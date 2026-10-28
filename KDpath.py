import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import io
import math
import queue
import re
import threading
import time
import tkinter as tk
from dataclasses import dataclass
from tkinter import messagebox

import requests
from PIL import Image, ImageTk, ImageFilter, ImageChops
from pyproj import Transformer

try:
    import gpsd
except ImportError:
    gpsd = None

WIDTH = 1100
HEIGHT = 720
MIRROR_X = True
AUTO_ROTATE_VIEW = True
GUIDANCE_WIDTH_M = 3.0
WARNING_THRESHOLD_M = 0.05
R = 6378137.0

ORTHO_WMS = "https://mapy.geoportal.gov.pl/wss/service/PZGIK/ORTO/WMS/HighResolution"
ORTHO_FALLBACK_WMS = "https://mapy.geoportal.gov.pl/wss/service/PZGIK/ORTO/WMS/StandardResolution"
PARCELS_WMS = "https://integracja.gugik.gov.pl/cgi-bin/KrajowaIntegracjaEwidencjiGruntow"
ULDK = "https://uldk.gugik.gov.pl/"

# Neutral boundary styling: lighter EGiB (county) vs darker LPIS (supplement).
# Contrasting thin outlines preserve readability on GRID and aerial photographs.
EGIB_COLOR = (192, 203, 215)     # Light cool gray
EGIB_HALO = (57, 65, 75)        # Thin graphite edge
LPIS_COLOR = (99, 108, 119)     # Darker neutral gray
LPIS_HALO = (241, 245, 249)     # Pale edge over aerial imagery
NUMBER_COLOR = (39, 47, 57)     # Dark labels, drawn above both boundaries
NUMBER_HALO = (255, 255, 255)
WMS_IMAGE_SIZE = 1400


# always_xy=True ensures lon,lat even with EPSG:4326 / WMS version variations.
TO_2180 = Transformer.from_crs("EPSG:4326", "EPSG:2180", always_xy=True)
# Keeping image requests in EPSG:2180 also avoids WMS 1.3.0 axis-order traps.


def parse_wkt_rings(wkt):
    """Extract exterior/interior polygon rings from POLYGON or MULTIPOLYGON WKT.

    The rings are used to DRAW boundaries, not to infer legal parcel extents.
    Expects lon/lat WKT requested with srid=4326 from ULDK.
    """
    if not isinstance(wkt, str) or not re.search(r'\b(?:MULTIPOLYGON|POLYGON)\b', wkt, re.I):
        raise ValueError("ULDK did not return a POLYGON/MULTIPOLYGON geometry")
    rings = []
    for data in re.findall(r'\(([^()]*)\)', wkt):
        pts = []
        for token in data.split(','):
            cols = token.strip().split()
            if len(cols) < 2:
                continue
            try:
                pts.append((float(cols[0]), float(cols[1])))
            except ValueError:
                pass
        if len(pts) >= 3:
            rings.append(pts)
    if not rings:
        raise ValueError("No polygon vertices in ULDK response")
    return rings


def parse_uldk_response(response):
    """Parse ULDK text with `result=id,geom_wkt` (status + data rows)."""
    lines = [x.strip() for x in response.strip().splitlines() if x.strip()]
    for line in lines:
        m = re.search(r'\b(?:MULTIPOLYGON|POLYGON)(?:\s+Z|\s+M|\s+ZM)?\s*\(', line, re.I)
        if m:
            wkt = line[m.start():]
            part = line[:m.start()].rstrip('|; \t')
            parcel_id = part.split('|')[-1].strip() if part else 'SELECTED PARCEL'
            return parcel_id, parse_wkt_rings(wkt)
    detail = ' '.join(lines[:2])[:150]
    raise ValueError(f"ULDK returned no parcel geometry: {detail or 'empty response'}")


def fetch_wms(url, layers, bbox, size=1400, transparent=False, output="image/png"):
    """Get one geo-referenced WMS image; use 1.1.1, XY order EPSG:2180."""
    x0, y0, x1, y1 = bbox
    params = {
        'SERVICE': 'WMS', 'REQUEST': 'GetMap', 'VERSION': '1.1.1',
        'SRS': 'EPSG:2180', 'BBOX': ','.join(f'{v:.3f}' for v in bbox),
        'LAYERS': layers, 'STYLES': '', 'FORMAT': output,
        'TRANSPARENT': 'TRUE' if transparent else 'FALSE',
        'WIDTH': size, 'HEIGHT': size,
        'EXCEPTIONS': 'application/vnd.ogc.se_xml',
    }
    resp = requests.get(url, params=params, timeout=(5, 18), headers={
        'User-Agent': 'KDpath-RaspberryPi/1.0 (GUGiK WMS educational integration)'
    })
    resp.raise_for_status()
    # The image decoder also catches OGC XML exceptions from the server.
    if not resp.content.startswith((b'\x89PNG', b'\xff\xd8', b'GIF8', b'RIFF')):
        snippet = resp.text[:180] if 'text' in resp.headers.get('content-type', '') or b'xml' in resp.content[:200].lower() else 'not an image'
        raise RuntimeError(f"WMS returned {snippet}")
    im = Image.open(io.BytesIO(resp.content))
    im.load()
    if im.size != (size, size):
        raise ValueError(f"WMS image size mismatch: {im.size}")
    return im.convert('RGBA')


def tint_wms_layer(im, ink_rgb, halo_rgb, halo_strength=0.85):
    """Recolor WMS pixels without shifting boundaries or altering geometry.

    Input can contain anti-aliased semi-transparent pixels. A small halo
    makes light EGiB and darker LPIS readable on ORTHO and GRID alike.
    Work is done once per map download, off the Tkinter thread.
    """
    im = im.convert('RGBA')
    alpha = im.getchannel('A')

    # Some upstream WMS endpoints ignore TRANSPARENT=TRUE and return a white
    # opaque backdrop. Treat only near-white as empty in THAT special case.
    # The normal transparent GetMap response is left completely untouched.
    if alpha.getextrema() == (255, 255):
        top_left = im.getpixel((0, 0))[:3]
        if all(channel >= 246 for channel in top_left):
            diff = ImageChops.difference(im.convert('RGB'),
                                         Image.new('RGB', im.size, (255, 255, 255)))
            # Any non-white drawing becomes an opacity mask.
            alpha = diff.convert('L').point(lambda v: min(255, v * 4))

    halo_alpha = alpha.filter(ImageFilter.MaxFilter(3))
    halo_alpha = halo_alpha.point(lambda v: round(v * halo_strength))
    halo = Image.new('RGBA', im.size, halo_rgb + (0,))
    halo.putalpha(halo_alpha)
    ink = Image.new('RGBA', im.size, ink_rgb + (0,))
    ink.putalpha(alpha)
    return Image.alpha_composite(halo, ink)


def combine_parcels_layers(layers):
    """Compose independent KIEG requests, in LPIS→EGiB→labels order.

    Draw BOTH official boundary sources, even when they do not align.
    The LPIS supplemental geometry is not snapped to county boundaries.
    """
    first = next(iter(layers.values()))
    composite = Image.new('RGBA', first.size, (0, 0, 0, 0))
    styles = (
        ('lpis', LPIS_COLOR, LPIS_HALO, 0.90),
        ('egib', EGIB_COLOR, EGIB_HALO, 0.88),
        ('numbers', NUMBER_COLOR, NUMBER_HALO, 0.95),
    )
    for key, fg, border, strength in styles:
        layer = layers.get(key)
        if layer is not None:
            composite = Image.alpha_composite(
                composite, tint_wms_layer(layer, fg, border, strength))
    return composite


@dataclass
class Raster:
    image: Image.Image
    bbox: tuple
    center: tuple
    zoom: float
    lat: float
    lon: float


class GeoportalClient:
    """Background network worker; UI and Tk photo objects stay in main thread."""
    def __init__(self):
        self.result_queue = queue.Queue()
        self.rasters = {}
        self.pending = set()
        self.last_attempt = {}
        self.errors = {}
        self.lock = threading.Lock()
        self.parcel_pending = False

    def raster_current_enough(self, kind, lat, lon, zoom, viewport):
        item = self.rasters.get(kind)
        if item is None:
            return False
        px, py = TO_2180.transform(lon, lat)
        radius = (item.bbox[2] - item.bbox[0]) / 2
        return (math.hypot(px-item.center[0], py-item.center[1]) < radius * 0.26
                and 0.73 < zoom / item.zoom < 1.4)

    def ensure(self, kind, lat, lon, zoom, viewport):
        if self.raster_current_enough(kind, lat, lon, zoom, viewport):
            return
        with self.lock:
            if kind in self.pending or time.monotonic() - self.last_attempt.get(kind, -1e10) < 14:
                return
            self.pending.add(kind)
            self.last_attempt[kind] = time.monotonic()
        w, h = viewport
        px, py = TO_2180.transform(lon, lat)
        radius = max(45.0, math.hypot(w, h) / max(0.35, zoom) * 0.66)
        bbox = (px-radius, py-radius, px+radius, py+radius)
        thread = threading.Thread(target=self._fetch_raster,
                                  args=(kind, bbox, (px, py), zoom, lat, lon), daemon=True)
        thread.start()

    def _fetch_raster(self, kind, bbox, center, zoom, lat, lon):
        try:
            if kind == 'ortho':
                failures = []
                # High-res WMS has historically advertised 'Raster' and '3,2,1';
                # attempt both, then standard orthophoto if necessary.
                variants = [(ORTHO_WMS, 'Raster'), (ORTHO_WMS, '3,2,1'),
                            (ORTHO_FALLBACK_WMS, 'Raster')]
                image = None
                for url, layers in variants:
                    try:
                        image = fetch_wms(url, layers, bbox, 1400, False, 'image/jpeg')
                        break
                    except Exception as exc:
                        failures.append(str(exc)[:100])
                if image is None:
                    raise RuntimeError('; '.join(failures))
            else:
                # Keep the county boundary, supplementary LPIS boundary and
                # county number labels separate. KIEG intentionally styles
                # them differently; tinting a *merged* PNG could not do this.
                requests_by_name = {
                    'egib': 'dzialki',
                    'lpis': 'geoportal',
                    'numbers': 'numery_dzialek',
                }
                received = {}
                failed = {}
                # Three independent requests share one bbox. Networking runs
                # in background; final raster remains ONE image in Tkinter.
                with ThreadPoolExecutor(max_workers=3) as pool:
                    futures = {
                        pool.submit(fetch_wms, PARCELS_WMS, layer, bbox,
                                    WMS_IMAGE_SIZE, True, 'image/png'): key
                        for key, layer in requests_by_name.items()
                    }
                    for future in as_completed(futures):
                        key = futures[future]
                        try:
                            received[key] = future.result()
                        except Exception as exc:
                            failed[key] = str(exc)[:90]
                if not received:
                    raise RuntimeError('KIEG: all three WMS layers failed: ' +
                                       '; '.join(f'{key}: {err}'
                                                 for key, err in failed.items()))
                image = combine_parcels_layers(received)
            self.result_queue.put(('raster', kind, Raster(image, bbox, center, zoom, lat, lon)))
            if kind == 'parcels' and failed:
                self.result_queue.put(('warning', kind,
                    'PARTIAL KIEG: ' + ', '.join(sorted(failed)) +
                    ' unavailable; remaining layers are displayed'))
        except Exception as exc:
            self.result_queue.put(('error', kind, str(exc)[:210]))

    def get_parcel_at(self, lat, lon):
        with self.lock:
            if self.parcel_pending:
                return False
            self.parcel_pending = True
        threading.Thread(target=self._fetch_parcel, args=(lat, lon), daemon=True).start()
        return True

    def _fetch_parcel(self, lat, lon):
        try:
            # The XY input explicitly specifies EPSG:4326; output vertices likewise.
            r = requests.get(ULDK, params={
                'request': 'GetParcelByXY',
                'xy': f'{lon:.9f},{lat:.9f},4326',
                'result': 'id,geom_wkt', 'srid': '4326',
            }, timeout=(5, 20))
            r.raise_for_status()
            r.encoding = 'utf-8'
            parcel_id, rings = parse_uldk_response(r.text)
            self.result_queue.put(('parcel', parcel_id, rings))
        except Exception as exc:
            self.result_queue.put(('error', 'outline', str(exc)[:230]))

    def collect(self, app):
        while True:
            try:
                typ, name, data = self.result_queue.get_nowait()
            except queue.Empty:
                break
            if typ == 'raster':
                self.rasters[name] = data
                self.errors.pop(name, None)
                with self.lock:
                    self.pending.discard(name)
            elif typ == 'warning':
                self.errors[name] = data
                app.notice = data
            elif typ == 'parcel':
                app.selected_parcel_id = name
                app.selected_parcel_rings = data
                app.outline_var.set(True)
                app._refresh_map_toolbar()
                app.notice = f'PARCEL {name} SELECTED'
                with self.lock:
                    self.parcel_pending = False
            elif typ == 'error':
                self.errors[name] = data
                app.notice = f'{name.upper()} ERROR: {data}'
                with self.lock:
                    self.pending.discard(name)
                    if name == 'outline':
                        self.parcel_pending = False


class KDpathApp:
    def __init__(self, root, args):
        self.root = root
        self.args = args
        self.zoom = 5.0
        self.tractor_scale = 1.0
        self.tractor_reverse = False
        self.points = []
        self.point_a = None
        self.point_b = None
        self.origin_lat = None
        self.origin_lon = None
        self.current_xy = None
        self.last_xy = None
        self.current_latlon = None
        self.paths = []
        self.active_path_index = 0
        self.blink_state = True
        self.background_var = tk.StringVar(value='GRID')
        self.parcels_var = tk.BooleanVar(value=False)
        self.outline_var = tk.BooleanVar(value=False)
        self.selected_parcel_id = None
        self.selected_parcel_rings = []
        self.pick_parcel_mode = False
        self.notice = ''
        self.gps_error = ''
        self.map_client = GeoportalClient()
        self.warp_cache_key = None
        self.warp_cache = None
        self.warp_photo = None
        self.parcel_photo = None
        self.parcel_warp_key = None
        self.parcel_warp = None
        self._last_size = (WIDTH, HEIGHT)
        self._gps_connected = False
        self._last_connect = 0
        self.demo_lat = args.lat
        self.demo_lon = args.lon
        self._build_ui()
        if args.demo:
            self._position_update(self.demo_lat, self.demo_lon)
            self.notice = 'DEMO: use arrow keys to move; A and B work normally'
            root.bind('<Up>', lambda e: self.demo_move(0, 0.6))
            root.bind('<Down>', lambda e: self.demo_move(0, -0.6))
            root.bind('<Left>', lambda e: self.demo_move(-0.6, 0))
            root.bind('<Right>', lambda e: self.demo_move(0.6, 0))
            # Ctrl+arrows permit faster test movement.
            root.bind('<Control-Up>', lambda e: self.demo_move(0, 4))
            root.bind('<Control-Down>', lambda e: self.demo_move(0, -4))
            root.bind('<Control-Left>', lambda e: self.demo_move(-4, 0))
            root.bind('<Control-Right>', lambda e: self.demo_move(4, 0))
        self.update()

    def _build_ui(self):
        self.root.title('KDpath')
        self.root.configure(bg='#101820')
        # Leave room for the desktop title bar/panel on the 1280x720 display.
        screen_w, screen_h = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
        self.root.geometry(f'{min(1280, screen_w - 8)}x{min(700, max(610, screen_h - 65))}')
        self.root.minsize(970, 610)

        # A horizontal MAP toolbar is independent from the guidance workspace.
        # It occupies the old 70px map header; all map settings are now here.
        self.toolbar = tk.Frame(self.root, height=68, bg='#111827')
        self.toolbar.pack(side='top', fill='x')
        self.toolbar.pack_propagate(False)

        self._build_map_toolbar()

        # Keep only original guidance controls on the right.  They fit inside
        # the remaining height of a 1280x720 Raspberry Pi touchscreen.
        self.panel = tk.Frame(self.root, width=182, bg='#101820')
        self.panel.pack(side='right', fill='y')
        self.panel.pack_propagate(False)

        self.canvas = tk.Canvas(self.root, width=WIDTH, height=HEIGHT, bg='#f7f9fb',
                                highlightthickness=0)
        self.canvas.pack(side='left', fill='both', expand=True)
        self.canvas.bind('<Configure>', self._on_resize)
        self.canvas.bind('<Button-1>', self.select_parcel_by_click)

        self._section('VIEW')
        self._btn('ZOOM +', self.zoom_in, '#2563eb')
        self._btn('ZOOM -', self.zoom_out, '#2563eb')
        self._btn('ICON +', self.tractor_bigger, '#0f766e')
        self._btn('ICON -', self.tractor_smaller, '#0f766e')
        self._btn('DIRECTION', self.toggle_direction, '#be123c')
        self._section('POINTS A-B')
        self._btn('SET A', self.set_a, '#16a34a')
        self._btn('SET B', self.set_b, '#0284c7')
        self._section('SPACE [cm]')
        self.spacing_entry = tk.Entry(self.panel, font=('Arial', 14, 'bold'), justify='center',
                                      bg='#e5e7eb', relief='flat', bd=0)
        self.spacing_entry.insert(0, '300')
        self.spacing_entry.pack(fill='x', padx=9, pady=3, ipady=4)
        self._btn('+ LEFT', self.add_left_path, '#7c3aed')
        self._btn('+ RIGHT', self.add_right_path, '#7c3aed')
        self._section('ACTIVE PATH')
        self._btn('◀ PREVIOUS', self.prev_path, '#f97316')
        self._btn('NEXT ▶', self.next_path, '#f97316')
        self._btn('RESET A/B', self.reset_ab, '#dc2626')

    def _build_map_toolbar(self):
        def group(label, padx=4):
            frame = tk.Frame(self.toolbar, bg='#111827')
            frame.pack(side='left', padx=padx, pady=(3, 2))
            tk.Label(frame, text=label, bg='#111827', fg='#94a3b8',
                     font=('Arial', 8, 'bold'), anchor='w').pack(anchor='w', pady=(0, 2))
            return frame

        background_group = group('BACKGROUND', 7)
        bg_row = tk.Frame(background_group, bg='#111827')
        bg_row.pack(fill='x')
        self.bg_buttons = {}
        for name in ('GRID', 'ORTHO'):
            button = tk.Button(bg_row, text=name,
                               command=lambda mode=name: self.set_map_background(mode),
                               bg='#334155', fg='white', activebackground='#1d4ed8',
                               activeforeground='white', relief='flat', bd=0,
                               font=('Arial', 10, 'bold'), padx=10, pady=7,
                               highlightthickness=0)
            button.pack(side='left', padx=1)
            self.bg_buttons[name] = button

        parcel_group = group('PARCELS', 7)
        self.parcels_button = tk.Button(parcel_group, text='OFF',
                                        command=self.switch_parcels_toolbar,
                                        bg='#334155', fg='white', relief='flat',
                                        activeforeground='white', bd=0,
                                        font=('Arial', 10, 'bold'), width=7,
                                        pady=7, highlightthickness=0)
        self.parcels_button.pack()

        outline_group = group('OUTLINE', 7)
        self.outline_button = tk.Button(outline_group, text='OFF',
                                        command=self.switch_outline_toolbar,
                                        bg='#334155', fg='white', relief='flat',
                                        activeforeground='white', bd=0,
                                        font=('Arial', 10, 'bold'), width=7,
                                        pady=7, highlightthickness=0)
        self.outline_button.pack()

        actions = (
            ('SELECT GPS PARCEL', 'SELECT GPS\nPARCEL', self.select_gps_parcel, '#0f766e', 95),
            ('PICK PARCEL', 'PICK\nPARCEL', self.start_parcel_pick, '#0f766e', 79),
            ('CLEAR SELECTION', 'CLEAR\nSELECTION', self.clear_selected_parcel, '#475569', 87),
        )
        for tooltip, title, callback, color, min_width in actions:
            frame = tk.Frame(self.toolbar, bg='#111827')
            frame.pack(side='left', padx=3, pady=7)
            button = tk.Button(frame, text=title, command=callback, bg=color,
                               fg='white', activebackground=color, activeforeground='white',
                               font=('Arial', 9, 'bold'), relief='flat', bd=0,
                               width=max(8, min_width//9), height=2,
                               highlightthickness=0)
            button.pack(fill='y')

        # STATUS receives all status text; the map no longer has a black status
        # overlay.  Guidance deviation/path info is preserved here as well.
        status_frame = tk.Frame(self.toolbar, bg='#111827')
        status_frame.pack(side='left', fill='both', expand=True, padx=(12, 7), pady=(5, 3))
        tk.Label(status_frame, text='STATUS', bg='#111827', fg='#94a3b8',
                 font=('Arial', 8, 'bold'), anchor='w').pack(fill='x')
        self.status_label = tk.Label(status_frame, text='Waiting for GNSS',
                                      bg='#111827', fg='#e2e8f0',
                                      font=('Arial', 9, 'bold'), anchor='w',
                                      justify='left')
        self.status_label.pack(fill='x', pady=(1, 0))
        self.guidance_label = tk.Label(status_frame, text='',
                                        bg='#111827', fg='#facc15',
                                        font=('Arial', 9, 'bold'), anchor='w',
                                        justify='left')
        self.guidance_label.pack(fill='x', pady=(2, 0))
        self._refresh_map_toolbar()

    def _refresh_map_toolbar(self):
        for name, button in self.bg_buttons.items():
            selected = self.background_var.get() == name
            button.configure(bg='#2563eb' if selected else '#334155',
                             activebackground='#1d4ed8' if selected else '#475569')
        for button, var in ((self.parcels_button, self.parcels_var),
                            (self.outline_button, self.outline_var)):
            selected = var.get()
            button.configure(text='ON' if selected else 'OFF',
                             bg='#0f766e' if selected else '#334155',
                             activebackground='#115e59' if selected else '#475569')

    def set_map_background(self, background):
        self.background_var.set(background)
        self.switch_background()
        self._refresh_map_toolbar()

    def switch_parcels_toolbar(self):
        self.parcels_var.set(not self.parcels_var.get())
        self.toggle_parcels()
        self._refresh_map_toolbar()

    def switch_outline_toolbar(self):
        self.outline_var.set(not self.outline_var.get())
        self.toggle_outline()
        self._refresh_map_toolbar()

    def _section(self, name):
        tk.Label(self.panel, text=name, bg='#101820', fg='#94a3b8',
                 font=('Arial', 9, 'bold')).pack(pady=(8, 2))

    def _btn(self, label, handler, bg='#2563eb', font_size=11):
        button = tk.Button(self.panel, text=label, command=handler, bg=bg, fg='white',
                           activebackground=bg, activeforeground='white', relief='flat',
                           bd=0, font=('Arial', font_size, 'bold'), padx=3, pady=4)
        button.pack(fill='x', padx=9, pady=2)
        return button

    def _on_resize(self, event):
        self._last_size = (max(1, event.width), max(1, event.height))
        self.warp_cache_key = None
        self.parcel_warp_key = None

    def dimensions(self):
        return self._last_size

    # --------------------- ORIGINAL POSITION/GUIDANCE MATH ---------------------
    def latlon_to_meters(self, lat, lon):
        if self.origin_lat is None:
            self.origin_lat = lat
            self.origin_lon = lon
        lat0 = math.radians(self.origin_lat)
        x = math.radians(lon-self.origin_lon)*R*math.cos(lat0)
        y = math.radians(lat-self.origin_lat)*R
        return x, y

    def meters_to_latlon(self, x, y):
        lat = self.origin_lat + math.degrees(y/R)
        lon = self.origin_lon + math.degrees(x/(R*math.cos(math.radians(self.origin_lat))))
        return lat, lon

    def ab_unit_vectors(self):
        if self.point_a is None or self.point_b is None:
            return None
        ax, ay = self.point_a
        bx, by = self.point_b
        dx, dy = bx-ax, by-ay
        length = math.hypot(dx, dy)
        if length == 0:
            return None
        ux, uy = dx/length, dy/length
        return ux, uy, -uy, ux

    def world_to_view(self, dx, dy):
        vectors = self.ab_unit_vectors()
        if AUTO_ROTATE_VIEW and vectors is not None:
            ux, uy, nx, ny = vectors
            sx, sy = dx*nx + dy*ny, dx*ux + dy*uy
        else:
            sx, sy = dx, dy
        if MIRROR_X:
            sx = -sx
        return sx, sy

    def screen_to_world_delta(self, sx, sy):
        vx, vy = sx/self.zoom, -sy/self.zoom
        if MIRROR_X:
            vx = -vx
        vectors = self.ab_unit_vectors()
        if AUTO_ROTATE_VIEW and vectors is not None:
            ux, uy, nx, ny = vectors
            return vx*nx + vy*ux, vx*ny + vy*uy
        return vx, vy

    def to_screen(self, x, y):
        w, h = self.dimensions()
        if self.current_xy is None:
            return w/2, h/2
        cx, cy = self.current_xy
        vx, vy = self.world_to_view(x-cx, y-cy)
        return w/2 + vx*self.zoom, h/2 - vy*self.zoom

    def screen_to_latlon(self, screen_x, screen_y):
        if self.current_xy is None:
            raise ValueError('No GPS position available')
        w, h = self.dimensions()
        dx, dy = self.screen_to_world_delta(screen_x-w/2, screen_y-h/2)
        return self.meters_to_latlon(self.current_xy[0]+dx, self.current_xy[1]+dy)

    def get_spacing_m(self):
        try:
            value = float(self.spacing_entry.get().replace(',', '.')) / 100.0
            return value if value > 0 else 3.0
        except ValueError:
            return 3.0

    def set_a(self):
        if self.current_xy is not None:
            self.point_a = self.current_xy
            print('Point A is set')

    def set_b(self):
        if self.current_xy is not None:
            self.point_b = self.current_xy
            self.paths = [0.0]
            self.active_path_index = 0
            print('Point B is set')

    def zoom_in(self):
        self.zoom = min(self.zoom*1.35, 80.0)

    def zoom_out(self):
        self.zoom = max(self.zoom/1.35, 0.35)

    def tractor_bigger(self):
        self.tractor_scale = min(self.tractor_scale*1.2, 5)

    def tractor_smaller(self):
        self.tractor_scale = max(self.tractor_scale/1.2, .25)

    def toggle_direction(self):
        self.tractor_reverse = not self.tractor_reverse

    def reset_ab(self):
        self.point_a = self.point_b = None
        self.paths = []
        self.active_path_index = 0

    def add_left_path(self):
        if self.ab_unit_vectors() is None:
            return
        spacing = self.get_spacing_m()
        if not self.paths:
            self.paths = [0.0]
        new_offset = (max(self.paths)+spacing if MIRROR_X else min(self.paths)-spacing)
        self.paths.append(new_offset)
        self.paths.sort()
        self.active_path_index = self.paths.index(new_offset)

    def add_right_path(self):
        if self.ab_unit_vectors() is None:
            return
        spacing = self.get_spacing_m()
        if not self.paths:
            self.paths = [0.0]
        new_offset = (min(self.paths)-spacing if MIRROR_X else max(self.paths)+spacing)
        self.paths.append(new_offset)
        self.paths.sort()
        self.active_path_index = self.paths.index(new_offset)

    def prev_path(self):
        if self.paths:
            self.active_path_index = (min(len(self.paths)-1, self.active_path_index+1)
                                      if MIRROR_X else max(0, self.active_path_index-1))

    def next_path(self):
        if self.paths:
            self.active_path_index = (max(0, self.active_path_index-1)
                                      if MIRROR_X else min(len(self.paths)-1, self.active_path_index+1))

    def active_offset(self):
        return self.paths[self.active_path_index] if self.paths else None

    def distance_to_base_line(self, px, py):
        vectors = self.ab_unit_vectors()
        if vectors is None:
            return None
        ax, ay = self.point_a
        ux, uy, nx, ny = vectors
        return (px-ax)*nx + (py-ay)*ny

    def distance_to_active_path(self, px, py):
        dist = self.distance_to_base_line(px, py)
        off = self.active_offset()
        return None if dist is None or off is None else dist-off

    def path_endpoints(self, offset):
        vectors = self.ab_unit_vectors()
        if vectors is None:
            return None
        ax, ay = self.point_a
        bx, by = self.point_b
        ux, uy, nx, ny = vectors
        extension = 10000
        return (ax+nx*offset-ux*extension, ay+ny*offset-uy*extension,
                bx+nx*offset+ux*extension, by+ny*offset+uy*extension)

    # ------------------------------ MAP CONTROLS -------------------------------
    def switch_background(self):
        self.warp_cache_key = None
        self.notice = ''

    def toggle_parcels(self):
        self.parcel_warp_key = None
        self.notice = ''

    def toggle_outline(self):
        if self.outline_var.get() and not self.selected_parcel_rings:
            self.select_gps_parcel()

    def start_parcel_pick(self):
        if self.current_xy is None:
            self.notice = 'WAIT FOR GPS BEFORE SELECTING A PARCEL'
            return
        self.pick_parcel_mode = True
        self.notice = 'TAP THE PARCEL ON THE MAP TO SELECT IT'

    def select_gps_parcel(self):
        if not self.current_latlon:
            self.notice = 'WAITING FOR GPS TO SELECT PARCEL'
            return
        if self.map_client.get_parcel_at(*self.current_latlon):
            self.notice = 'LOADING PARCEL FROM ULDK...'

    def select_parcel_by_click(self, event):
        # Pick mode prevents accidental selections from touching the map.
        if not self.pick_parcel_mode or self.current_xy is None:
            return
        self.pick_parcel_mode = False
        try:
            lat, lon = self.screen_to_latlon(event.x, event.y)
            if self.map_client.get_parcel_at(lat, lon):
                self.notice = 'SEARCHING FOR PARCEL AT MAP CLICK...'
        except Exception as exc:
            self.notice = str(exc)[:100]

    def clear_selected_parcel(self):
        self.pick_parcel_mode = False
        self.selected_parcel_id = None
        self.selected_parcel_rings = []
        self.outline_var.set(False)
        self._refresh_map_toolbar()
        self.notice = 'PARCEL SELECTION CLEARED'

    def ensure_layers(self):
        if self.current_latlon is None:
            return
        lat, lon = self.current_latlon
        if self.background_var.get() == 'ORTHO':
            self.map_client.ensure('ortho', lat, lon, self.zoom, self.dimensions())
        if self.parcels_var.get():
            self.map_client.ensure('parcels', lat, lon, self.zoom, self.dimensions())

    def _projected_xy(self, x, y):
        lat, lon = self.meters_to_latlon(x, y)
        return TO_2180.transform(lon, lat)

    def _affine_for_raster(self, raster):
        # Pillow needs: source_pixel = Affine(target_screen_pixel).
        # Calibrate the inverse on three neighboring screen points. The map is
        # locally affine at agricultural field scale; guidance math is unchanged.
        w, h = self.dimensions()
        cx, cy = self.current_xy
        proj0 = self._projected_xy(cx, cy)
        xdx, xdy = self.screen_to_world_delta(1.0, 0.0)
        ydx, ydy = self.screen_to_world_delta(0.0, 1.0)
        projx = self._projected_xy(cx+xdx, cy+xdy)
        projy = self._projected_xy(cx+ydx, cy+ydy)
        bx0, by0, bx1, by1 = raster.bbox
        iw, ih = raster.image.size
        def image_px(p):
            return ((p[0]-bx0)*iw/(bx1-bx0), (by1-p[1])*ih/(by1-by0))
        u0, v0 = image_px(proj0)
        ux, vx = image_px(projx)
        uy, vy = image_px(projy)
        a, b, d, e = ux-u0, uy-u0, vx-v0, vy-v0
        return (a, b, u0-a*w/2-b*h/2, d, e, v0-d*w/2-e*h/2)

    def _display_raster(self, kind):
        raster = self.map_client.rasters.get(kind)
        if raster is None or self.current_xy is None:
            return
        w, h = self.dimensions()
        # Reuse PIL transform / PhotoImage unless position or view changes.
        cache_key = (kind, id(raster), w, h, self.zoom, self.current_xy,
                     self.point_a, self.point_b, MIRROR_X, AUTO_ROTATE_VIEW)
        if kind == 'ortho' and self.warp_cache_key == cache_key:
            photo = self.warp_photo
        elif kind == 'parcels' and self.parcel_warp_key == cache_key:
            photo = self.parcel_photo
        else:
            matrix = self._affine_for_raster(raster)
            fill = (247, 249, 251, 255) if kind == 'ortho' else (0, 0, 0, 0)
            im = raster.image.transform((w, h), Image.Transform.AFFINE, matrix,
                                        resample=Image.Resampling.BILINEAR,
                                        fillcolor=fill)
            photo = ImageTk.PhotoImage(im)
            if kind == 'ortho':
                self.warp_cache_key, self.warp_photo = cache_key, photo
            else:
                self.parcel_warp_key, self.parcel_photo = cache_key, photo
        self.canvas.create_image(0, 0, image=photo, anchor='nw')

    # -------------------------------- DRAWING ---------------------------------
    def draw_grid(self):
        w, h = self.dimensions()
        step_m = 10
        step_px = max(40, int(step_m*self.zoom))
        if self.current_xy is None:
            offset_x = offset_y = 0
        else:
            vx, vy = self.world_to_view(self.current_xy[0], self.current_xy[1])
            offset_x = (vx*self.zoom) % step_px
            offset_y = (vy*self.zoom) % step_px
        for x in range(-step_px, w+step_px, step_px):
            self.canvas.create_line(x-offset_x, 0, x-offset_x, h, fill='#e5e7eb')
        for y in range(-step_px, h+step_px, step_px):
            self.canvas.create_line(0, y+offset_y, w, y+offset_y, fill='#e5e7eb')

    def draw_parcels_legend(self):
        """A compact source legend: pale gray county, darker gray LPIS."""
        if not self.parcels_var.get():
            return
        _, h = self.dimensions()
        y = h - 24
        self.canvas.create_rectangle(8, y - 17, 293, y + 16,
                                     fill='#111827', outline='#475569', width=1)
        for x, rgb, halo, label in (
                (18, EGIB_COLOR, EGIB_HALO, 'EGiB (POWIAT)'),
                (160, LPIS_COLOR, LPIS_HALO, 'LPIS')):
            color = '#%02x%02x%02x' % rgb
            halo_color = '#%02x%02x%02x' % halo
            self.canvas.create_line(x, y, x + 21, y, fill=halo_color, width=6)
            self.canvas.create_line(x, y, x + 21, y, fill=color, width=4)
            self.canvas.create_text(x + 26, y, anchor='w', fill='#f8fafc',
                                    text=label, font=('Arial', 9, 'bold'))

    def draw_selected_outline(self):
        if not self.outline_var.get() or not self.selected_parcel_rings:
            return
        # Draw WGS84 vertices as strokes; not derived from screen-pixel segmentation.
        for ring in self.selected_parcel_rings:
            flat = []
            for lon, lat in ring:
                x, y = self.latlon_to_meters(lat, lon)
                sx, sy = self.to_screen(x, y)
                flat.extend([sx, sy])
            if len(flat) >= 6:
                self.canvas.create_line(*flat, fill='#0f172a', width=7, joinstyle='round')
                self.canvas.create_line(*flat, fill='#facc15', width=4, joinstyle='round')
        if self.selected_parcel_id:
            self.canvas.create_text(14, self.dimensions()[1]-(64 if self.parcels_var.get() else 36),
                                    anchor='w', text=f'SELECTED: {self.selected_parcel_id}',
                                    font=('Arial', 11, 'bold'), fill='#eab308')

    def draw_paths(self):
        if self.ab_unit_vectors() is None or not self.paths:
            self.draw_ab_points()
            return
        active = self.active_offset()
        for offset in self.paths:
            x1, y1, x2, y2 = self.path_endpoints(offset)
            sx1, sy1 = self.to_screen(x1, y1)
            sx2, sy2 = self.to_screen(x2, y2)
            if offset == active:
                self.canvas.create_line(sx1, sy1, sx2, sy2, fill='#052e16', width=11)
                self.canvas.create_line(sx1, sy1, sx2, sy2, fill='#16a34a', width=8)
            else:
                self.canvas.create_line(sx1, sy1, sx2, sy2, fill='#334155', width=5)
                self.canvas.create_line(sx1, sy1, sx2, sy2, fill='#cbd5e1', width=3)
        self.draw_ab_points()

    def draw_ab_points(self):
        for label, point, color in [('A', self.point_a, '#15803d'),
                                    ('B', self.point_b, '#0369a1')]:
            if point is None:
                continue
            sx, sy = self.to_screen(*point)
            self.canvas.create_oval(sx-12, sy-12, sx+12, sy+12,
                                    fill=color, outline='white', width=3)
            self.canvas.create_text(sx+25, sy-19, text=label,
                                    font=('Arial', 18, 'bold'), fill='white')
            self.canvas.create_text(sx+24, sy-20, text=label,
                                    font=('Arial', 18, 'bold'), fill=color)

    def draw_track(self):
        if len(self.points) < 2:
            return
        coords = []
        for x, y in self.points[-5000:]:
            coords.extend(self.to_screen(x, y))
        if len(coords) > 3:
            self.canvas.create_line(*coords, fill='white', width=4)
            self.canvas.create_line(*coords, fill='#2563eb', width=2)

    def _rotated_polygon(self, cx, cy, coords, angle, fill, outline='', width=1):
        ca, sa = math.cos(angle), math.sin(angle)
        flat = []
        for x, y in coords:
            flat.extend([cx + x*ca-y*sa, cy+x*sa+y*ca])
        self.canvas.create_polygon(*flat, fill=fill, outline=outline, width=width,
                                   joinstyle='round')

    def draw_position(self):
        if self.current_xy is None:
            return
        w, h = self.dimensions()
        cx, cy = w/2, h/2
        if self.ab_unit_vectors() is None:
            radius = max(14, 20*self.tractor_scale)
            self.canvas.create_oval(cx-radius*1.85, cy-radius*1.85,
                                    cx+radius*1.85, cy+radius*1.85,
                                    fill='#60a5fa', outline='', stipple='gray75')
            self.canvas.create_oval(cx-radius-3, cy-radius-3, cx+radius+3, cy+radius+3,
                                    fill='#ffffff', outline='#0f172a', width=2)
            self.canvas.create_oval(cx-radius+2, cy-radius+2, cx+radius-2, cy+radius-2,
                                    fill='#2563eb', outline='white', width=2)
            self.canvas.create_oval(cx-4, cy-4, cx+4, cy+4, fill='#bfdbfe', outline='')
            return
        base = max(42, int(GUIDANCE_WIDTH_M*self.zoom))
        s = base*self.tractor_scale
        angle = math.pi if self.tractor_reverse else 0.0
        triangle = [(0, -s*.95), (-s*.55, s*.55), (0, s*.25), (s*.55, s*.55)]
        shadow = [(x+3, y+5) for x,y in triangle]
        self._rotated_polygon(cx, cy, shadow, angle, '#0f172a')
        self._rotated_polygon(cx, cy, triangle, angle, '#ef4444', 'white', 4)
        inner = [(0,-s*.55), (-s*.22,s*.15), (0,s*.02), (s*.22,s*.15)]
        self._rotated_polygon(cx, cy, inner, angle, '#facc15', '#854d0e', 2)

    def draw_warning_arrows(self, deviation):
        if deviation is None:
            return
        self.blink_state = not self.blink_state
        if abs(deviation) < WARNING_THRESHOLD_M or not self.blink_state:
            return
        w, h = self.dimensions()
        corrected_deviation = -deviation if MIRROR_X else deviation
        if corrected_deviation > 0:
            x, symbol = 85, '⬅'
        else:
            x, symbol = w-85, '➡'
        self.canvas.create_text(x, h/2, text=symbol, fill='#dc2626',
                                font=('Arial', 80, 'bold'))

    def draw_attribution(self):
        # Copyright/attribution must stay visible when using GUGiK imagery.
        if (self.background_var.get() == 'ORTHO' or self.parcels_var.get()
                or self.outline_var.get()):
            w, h = self.dimensions()
            self.canvas.create_text(w-8, h-8, anchor='se',
                                    text='Map: GUGiK / Geoportal.gov.pl | EGiB + LPIS: KIEG / ULDK',
                                    fill='#101820' if self.background_var.get() == 'GRID'
                                    else '#ffffff', font=('Arial', 9, 'bold'))

    def draw(self):
        self.canvas.delete('all')
        if self.background_var.get() == 'ORTHO' and 'ortho' in self.map_client.rasters:
            self._display_raster('ortho')
        else:
            self.canvas.configure(bg='#f7f9fb')
            self.draw_grid()
        if self.parcels_var.get():
            self._display_raster('parcels')
        self.draw_selected_outline()
        self.draw_paths()
        self.draw_track()
        self.draw_position()
        deviation = None
        if self.current_xy is not None:
            deviation = self.distance_to_active_path(*self.current_xy)
        self.draw_warning_arrows(deviation)
        self.draw_parcels_legend()
        self.draw_attribution()
        if self.current_xy is None:
            w, h = self.dimensions()
            self.canvas.create_text(w/2, h/2+80, text='WAITING FOR GNSS / gpsd',
                                    fill='#dc2626', font=('Arial', 20, 'bold'))
        if self.background_var.get() == 'ORTHO' and 'ortho' not in self.map_client.rasters:
            w, h = self.dimensions()
            self.canvas.create_text(w/2, h-55, text='LOADING ORTHO / using GRID until ready',
                                    fill='#b45309', font=('Arial', 12, 'bold'))

    # --------------------------------- GNSS -----------------------------------
    def _position_update(self, lat, lon):
        if not (-90<=lat<=90 and -180<=lon<=180 and math.isfinite(lat) and math.isfinite(lon)):
            raise ValueError('Invalid GNSS coordinates')
        new_xy = self.latlon_to_meters(lat, lon)
        self.last_xy = self.current_xy
        self.current_xy = new_xy
        self.current_latlon = (lat, lon)
        if not self.points or math.hypot(new_xy[0]-self.points[-1][0],
                                         new_xy[1]-self.points[-1][1]) > .015:
            self.points.append(new_xy)
        self.gps_error = ''

    def demo_move(self, dx, dy):
        if self.current_xy is None:
            return
        lat, lon = self.meters_to_latlon(self.current_xy[0]+dx, self.current_xy[1]+dy)
        self._position_update(lat, lon)

    def _poll_gps(self):
        if gpsd is None:
            self.gps_error = 'gpsd-py3 package missing'
            return
        if not self._gps_connected:
            if time.monotonic()-self._last_connect < 5:
                return
            self._last_connect = time.monotonic()
            try:
                gpsd.connect()
                self._gps_connected = True
            except Exception as exc:
                self.gps_error = str(exc)[:120]
                return
        try:
            packet = gpsd.get_current()
            if packet.mode >= 2:
                self._position_update(float(packet.lat), float(packet.lon))
            else:
                self.gps_error = 'No GNSS fix yet'
        except Exception as exc:
            self.gps_error = str(exc)[:120]
            self._gps_connected = False

    def update(self):
        try:
            if not self.args.demo:
                self._poll_gps()
            self.map_client.collect(self)
            self.ensure_layers()
            self.draw()
            status = self.notice or self.gps_error or (
                'GNSS ONLINE' if self.current_xy else 'Waiting for GNSS')
            if self.selected_parcel_id and not self.notice:
                status = f'PARCEL: {self.selected_parcel_id}'
            # Keep the entire toolbar on one row even with long WMS errors.
            self.status_label.configure(text=status.replace('\n', ' | ')[:76])
            if self.current_xy is not None:
                deviation = self.distance_to_active_path(*self.current_xy)
            else:
                deviation = None
            if deviation is not None:
                self.guidance_label.configure(
                    text=f'DEVIATION {deviation:+.2f} m  •  PATH {self.active_path_index + 1}/{len(self.paths)}')
            else:
                self.guidance_label.configure(text='')
        except Exception as exc:
            self.notice = f'DISPLAY ERROR: {exc}'
            print(self.notice)
        finally:
            self.root.after(300, self.update)


def self_test():
    assert len(parse_wkt_rings('POLYGON ((21 52,22 52,22 53,21 52))')) == 1
    assert len(parse_wkt_rings('MULTIPOLYGON (((21 52,22 52,22 53,21 52)),((23 54,24 54,24 55,23 54)))')) == 2
    name, rings = parse_uldk_response('0\n141201_1.0001.6509|POLYGON((21 52,22 52,22 53,21 52))')
    assert name == '141201_1.0001.6509' and len(rings) == 1
    e, n = TO_2180.transform(21.0122, 52.2297)
    assert math.isfinite(e) and math.isfinite(n)
    blank = Image.new('RGBA', (15, 15), (0, 0, 0, 0))
    county = blank.copy()
    county.putpixel((7, 7), (64, 160, 255, 255))
    lpis = blank.copy()
    lpis.putpixel((2, 10), (128, 128, 128, 255))
    out = combine_parcels_layers({'egib': county, 'lpis': lpis})
    assert out.getpixel((7, 7))[:3] == EGIB_COLOR
    assert out.getpixel((2, 10))[:3] == LPIS_COLOR
    assert out.getpixel((14, 14))[3] == 0
    print('KDpath self-tests: PASS (WKT, ULDK, EPSG:2180, EGiB/LPIS styling)')


def main():
    parser = argparse.ArgumentParser(description='KDpath Geoportal / GNSS RTK guidance')
    parser.add_argument('--demo', action='store_true', help='simulate GNSS without hardware')
    parser.add_argument('--lat', type=float, default=52.2297, help='demo latitude')
    parser.add_argument('--lon', type=float, default=21.0122, help='demo longitude')
    parser.add_argument('--self-test', action='store_true', help='run parser/projection tests, no GUI')
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return
    root = tk.Tk()
    KDpathApp(root, args)
    root.mainloop()


if __name__ == '__main__':
    main()
