# -*- coding: utf-8 -*-
"""
Win32 Layered Window — per-pixel alpha 显示 Live2D 帧

WndProc 只做最小工作：
  - WM_NCHITTEST：查 alpha 掩码，命中角色返回 HTCLIENT，否则 HTTRANSPARENT
  - 鼠标消息：只把事件 push 到队列，不调 Python 回调，不改任何外部状态
主程序通过 poll_events() 在 tk 主循环里安全消费事件。
"""
import ctypes
from ctypes import wintypes
import threading
import collections
import numpy as np

user32 = ctypes.WinDLL('user32', use_last_error=True)
gdi32 = ctypes.WinDLL('gdi32', use_last_error=True)
kernel32 = ctypes.WinDLL('kernel32', use_last_error=True)

WS_EX_LAYERED   = 0x00080000
WS_EX_TOOLWINDOW = 0x00000080
WS_EX_TOPMOST   = 0x00000008
WS_EX_NOACTIVATE = 0x08000000
WS_EX_TRANSPARENT = 0x00000020
WS_POPUP        = 0x80000000
SW_SHOWNOACTIVATE = 4
SW_HIDE         = 0
SWP_NOMOVE      = 0x0002
SWP_NOSIZE      = 0x0001
SWP_NOACTIVATE  = 0x0010
SWP_FRAMECHANGED = 0x0020
GWL_EXSTYLE     = -20
ULW_ALPHA       = 0x00000002
AC_SRC_OVER     = 0x00
AC_SRC_ALPHA    = 0x01

WM_NCHITTEST    = 0x0084
WM_LBUTTONDOWN  = 0x0201
WM_LBUTTONUP    = 0x0202
WM_MOUSEMOVE    = 0x0200
WM_RBUTTONUP    = 0x0205
WM_CAPTURECHANGED = 0x0215
WM_HOTKEY       = 0x0312
HTCLIENT        = 1
HTTRANSPARENT   = -1

MOD_CONTROL = 0x0002
MOD_SHIFT  = 0x0004

HIT_THRESHOLD = 24

class POINT(ctypes.Structure):
    _fields_ = [('x', ctypes.c_long), ('y', ctypes.c_long)]

class SIZE(ctypes.Structure):
    _fields_ = [('cx', ctypes.c_long), ('cy', ctypes.c_long)]

class BLENDFUNCTION(ctypes.Structure):
    _fields_ = [
        ('BlendOp', ctypes.c_byte),
        ('BlendFlags', ctypes.c_byte),
        ('SourceConstantAlpha', ctypes.c_byte),
        ('AlphaFormat', ctypes.c_byte),
    ]

class BITMAPINFOHEADER(ctypes.Structure):
    _fields_ = [
        ('biSize', ctypes.c_uint32),
        ('biWidth', ctypes.c_long),
        ('biHeight', ctypes.c_long),
        ('biPlanes', ctypes.c_uint16),
        ('biBitCount', ctypes.c_uint16),
        ('biCompression', ctypes.c_uint32),
        ('biSizeImage', ctypes.c_uint32),
        ('biXPelsPerMeter', ctypes.c_long),
        ('biYPelsPerMeter', ctypes.c_long),
        ('biClrUsed', ctypes.c_uint32),
        ('biClrImportant', ctypes.c_uint32),
    ]

class BITMAPINFO(ctypes.Structure):
    _fields_ = [('bmiHeader', BITMAPINFOHEADER), ('bmiColors', ctypes.c_uint32 * 3)]

class WNDCLASS(ctypes.Structure):
    _fields_ = [
        ('style', ctypes.c_uint),
        ('lpfnWndProc', ctypes.c_void_p),
        ('cbClsExtra', ctypes.c_int),
        ('cbWndExtra', ctypes.c_int),
        ('hInstance', wintypes.HINSTANCE),
        ('hIcon', wintypes.HICON),
        ('hCursor', wintypes.HANDLE),
        ('hbrBackground', wintypes.HBRUSH),
        ('lpszMenuName', wintypes.LPCWSTR),
        ('lpszClassName', wintypes.LPCWSTR),
    ]

WNDPROCTYPE = ctypes.WINFUNCTYPE(ctypes.c_long, wintypes.HWND, ctypes.c_uint, wintypes.WPARAM, wintypes.LPARAM)

user32.CreateWindowExW.restype = wintypes.HWND
user32.CreateWindowExW.argtypes = [ctypes.c_uint, wintypes.LPCWSTR, wintypes.LPCWSTR,
    ctypes.c_uint, ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int,
    wintypes.HWND, wintypes.HMENU, wintypes.HINSTANCE, wintypes.LPVOID]
user32.DefWindowProcW.restype = ctypes.c_long
user32.DefWindowProcW.argtypes = [wintypes.HWND, ctypes.c_uint, wintypes.WPARAM, wintypes.LPARAM]
user32.UpdateLayeredWindow.argtypes = [
    wintypes.HWND, wintypes.HDC, ctypes.POINTER(POINT), ctypes.POINTER(SIZE),
    wintypes.HDC, ctypes.POINTER(POINT), ctypes.c_uint,
    ctypes.POINTER(BLENDFUNCTION), ctypes.c_uint
]
user32.UpdateLayeredWindow.restype = wintypes.BOOL
user32.SetCapture.restype = wintypes.HWND
user32.SetCapture.argtypes = [wintypes.HWND]
user32.ReleaseCapture.restype = wintypes.BOOL
user32.GetCursorPos.argtypes = [ctypes.POINTER(POINT)]
user32.GetCursorPos.restype = wintypes.BOOL
user32.RegisterHotKey.restype = wintypes.BOOL
user32.RegisterHotKey.argtypes = [wintypes.HWND, ctypes.c_int, ctypes.c_uint, ctypes.c_uint]
user32.UnregisterHotKey.restype = wintypes.BOOL
user32.UnregisterHotKey.argtypes = [wintypes.HWND, ctypes.c_int]
user32.SetWindowLongW.restype = ctypes.c_long
user32.SetWindowLongW.argtypes = [wintypes.HWND, ctypes.c_int, ctypes.c_long]
user32.SetWindowPos.restype = wintypes.BOOL
user32.SetWindowPos.argtypes = [wintypes.HWND, wintypes.HWND, ctypes.c_int, ctypes.c_int,
    ctypes.c_int, ctypes.c_int, ctypes.c_uint]

gdi32.CreateCompatibleDC.restype = wintypes.HDC
gdi32.CreateCompatibleDC.argtypes = [wintypes.HDC]
gdi32.CreateDIBSection.restype = wintypes.HBITMAP
gdi32.CreateDIBSection.argtypes = [
    wintypes.HDC, ctypes.POINTER(BITMAPINFO), ctypes.c_uint,
    ctypes.POINTER(ctypes.c_void_p), wintypes.HANDLE, ctypes.c_uint
]
gdi32.SelectObject.restype = wintypes.HGDIOBJ
gdi32.SelectObject.argtypes = [wintypes.HDC, wintypes.HGDIOBJ]
# 下面三个不声明 argtypes 时，64 位句柄会被当成 int 传参而溢出报错，
# 导致 destroy() 半途中止（DC/DIB 泄漏，且异常被上层 except 吞掉）
gdi32.DeleteDC.restype = wintypes.BOOL
gdi32.DeleteDC.argtypes = [wintypes.HDC]
gdi32.DeleteObject.restype = wintypes.BOOL
gdi32.DeleteObject.argtypes = [wintypes.HGDIOBJ]
user32.GetDC.restype = wintypes.HDC
user32.GetDC.argtypes = [wintypes.HWND]
user32.ReleaseDC.restype = ctypes.c_int
user32.ReleaseDC.argtypes = [wintypes.HWND, wintypes.HDC]
user32.DestroyWindow.restype = wintypes.BOOL
user32.DestroyWindow.argtypes = [wintypes.HWND]
user32.ShowWindow.restype = wintypes.BOOL
user32.ShowWindow.argtypes = [wintypes.HWND, ctypes.c_int]
user32.GetWindowRect.restype = wintypes.BOOL
user32.GetWindowRect.argtypes = [wintypes.HWND, ctypes.POINTER(wintypes.RECT)]


_class_registered = False
_class_name = 'ViviLayeredWnd'
_kept_wndproc = None
_hwnd_to_inst = {}


def _wndproc(hwnd, msg, wparam, lparam):
    try:
        inst = _hwnd_to_inst.get(hwnd)
        if inst is None:
            return user32.DefWindowProcW(hwnd, msg, wparam, lparam)

        if msg == WM_NCHITTEST:
            sx = ctypes.c_int16(lparam & 0xFFFF).value
            sy = ctypes.c_int16((lparam >> 16) & 0xFFFF).value
            mask = inst._hit_mask
            with inst._mask_lock:
                if mask is None:
                    return HTTRANSPARENT
                cx = sx - inst._x
                cy = sy - inst._y
                h, w = mask.shape
                if 0 <= cx < w and 0 <= cy < h and bool(mask[cy, cx]):
                    return HTCLIENT
            return HTTRANSPARENT

        if msg == WM_HOTKEY:
            inst._events.append(('hotkey',))
            return 0

        if msg == WM_LBUTTONDOWN:
            sx = ctypes.c_int16(lparam & 0xFFFF).value + inst._x
            sy = ctypes.c_int16((lparam >> 16) & 0xFFFF).value + inst._y
            inst._dragging = True
            user32.SetCapture(hwnd)
            inst._events.append(('press', sx, sy))
            return 0

        if msg == WM_MOUSEMOVE and inst._dragging:
            pt = POINT()
            user32.GetCursorPos(ctypes.byref(pt))
            inst._events.append(('drag', pt.x, pt.y))
            return 0

        if msg == WM_LBUTTONUP and inst._dragging:
            inst._dragging = False
            user32.ReleaseCapture()
            pt = POINT()
            user32.GetCursorPos(ctypes.byref(pt))
            inst._events.append(('release', pt.x, pt.y))
            return 0

        if msg == WM_CAPTURECHANGED:
            # 系统取消了捕获，安全清理拖拽状态
            inst._dragging = False
            return 0

        if msg == WM_RBUTTONUP:
            pt = POINT()
            user32.GetCursorPos(ctypes.byref(pt))
            inst._events.append(('right', pt.x, pt.y))
            return 0

        return user32.DefWindowProcW(hwnd, msg, wparam, lparam)
    except Exception:
        # 任何 Python 异常都不能让出到 native，否则 ctypes 回调会崩进程
        try:
            return user32.DefWindowProcW(hwnd, msg, wparam, lparam)
        except Exception:
            return 0


def _register_class():
    global _class_registered, _kept_wndproc
    if _class_registered:
        return
    hinst = kernel32.GetModuleHandleW(None)
    _kept_wndproc = WNDPROCTYPE(_wndproc)
    wc = WNDCLASS()
    wc.style = 0
    wc.lpfnWndProc = ctypes.cast(_kept_wndproc, ctypes.c_void_p)
    wc.cbClsExtra = 0
    wc.cbWndExtra = 0
    wc.hInstance = hinst
    wc.hIcon = 0
    wc.hCursor = user32.LoadCursorW(None, 32512)
    wc.hbrBackground = 0
    wc.lpszMenuName = None
    wc.lpszClassName = _class_name
    user32.RegisterClassW(ctypes.byref(wc))
    _class_registered = True


class LayeredImageWindow:
    def __init__(self, width, height):
        _register_class()
        self.width = width
        self.height = height
        self._dragging = False
        self._hit_mask = None
        self._mask_lock = threading.Lock()
        self._update_lock = threading.Lock()
        self._events = collections.deque()
        self._alive = True

        ex_style = WS_EX_LAYERED | WS_EX_TOOLWINDOW | WS_EX_TOPMOST | WS_EX_NOACTIVATE
        self._base_ex_style = ex_style
        hinst = kernel32.GetModuleHandleW(None)
        self.hwnd = user32.CreateWindowExW(
            ex_style, _class_name, 'ViviLive2D', WS_POPUP,
            0, 0, width, height, None, None, hinst, None
        )
        if not self.hwnd:
            raise ctypes.WinError(ctypes.get_last_error())
        _hwnd_to_inst[self.hwnd] = self

        # 注册全局热键 Ctrl+Shift+G
        result = user32.RegisterHotKey(self.hwnd, 1, MOD_CONTROL | MOD_SHIFT, ord('G'))
        if not result:
            import logging
            logging.getLogger(__name__).warning(f"RegisterHotKey 失败: {ctypes.get_last_error()}")

        screen_dc = user32.GetDC(0)
        self.mem_dc = gdi32.CreateCompatibleDC(screen_dc)
        bmi = BITMAPINFO()
        bmi.bmiHeader.biSize = ctypes.sizeof(BITMAPINFOHEADER)
        bmi.bmiHeader.biWidth = width
        bmi.bmiHeader.biHeight = -height
        bmi.bmiHeader.biPlanes = 1
        bmi.bmiHeader.biBitCount = 32
        bmi.bmiHeader.biCompression = 0
        bmi.bmiHeader.biSizeImage = width * height * 4
        self._pixels = ctypes.c_void_p()
        self.hbm = gdi32.CreateDIBSection(
            self.mem_dc, ctypes.byref(bmi), 0, ctypes.byref(self._pixels), None, 0
        )
        gdi32.SelectObject(self.mem_dc, self.hbm)
        user32.ReleaseDC(0, screen_dc)

        self._screen_dc = user32.GetDC(0)
        self._x = 0
        self._y = 0
        self._buffer_size = width * height * 4

    def show(self):
        user32.ShowWindow(self.hwnd, SW_SHOWNOACTIVATE)

    def hide(self):
        user32.ShowWindow(self.hwnd, SW_HIDE)

    def update_rgba(self, rgba_bytes, x, y):
        # 与 destroy() 互斥：destroy 后（_alive=False）的帧直接丢弃，
        # 避免渲染线程对已销毁的 HWND/DC 调用 UpdateLayeredWindow 导致 access violation
        if len(rgba_bytes) != self._buffer_size or not self._alive:
            return
        with self._update_lock:
            if not self._alive:
                return
            arr = np.frombuffer(rgba_bytes, np.uint8).reshape(self.height, self.width, 4)

            new_mask = np.ascontiguousarray(arr[..., 3] >= HIT_THRESHOLD)
            with self._mask_lock:
                self._hit_mask = new_mask

            # 帧是预乘 alpha，只需 RGBA → BGRA 通道换序（预乘由渲染端一次性给出，
            # 这里再乘一遍会变成"二次预乘"导致边缘发暗）
            bgra = np.ascontiguousarray(arr[..., [2, 1, 0, 3]])
            ctypes.memmove(self._pixels, bgra.tobytes(), self._buffer_size)

            self._x, self._y = int(x), int(y)
            size = SIZE(self.width, self.height)
            src_pt = POINT(0, 0)
            dst_pt = POINT(self._x, self._y)
            blend = BLENDFUNCTION(AC_SRC_OVER, 0, 255, AC_SRC_ALPHA)
            user32.UpdateLayeredWindow(
                self.hwnd, self._screen_dc, ctypes.byref(dst_pt), ctypes.byref(size),
                self.mem_dc, ctypes.byref(src_pt), 0,
                ctypes.byref(blend), ULW_ALPHA
            )

    def poll_events(self):
        """返回自上次调用以来累积的事件列表 (kind, sx, sy)。"""
        out = []
        while self._events:
            try:
                out.append(self._events.popleft())
            except IndexError:
                break
        return out

    def set_bypass(self, enabled):
        """切换 WS_EX_TRANSPARENT：开启后窗口对鼠标完全不可见（穿透移动+点击）"""
        if not self._alive:
            return
        if enabled:
            new_style = self._base_ex_style | WS_EX_TRANSPARENT
        else:
            new_style = self._base_ex_style
        user32.SetWindowLongW(self.hwnd, GWL_EXSTYLE, new_style)
        user32.SetWindowPos(self.hwnd, 0, 0, 0, 0, 0,
                           SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE | SWP_FRAMECHANGED)

    def destroy(self):
        # 与 update_rgba 互斥：销毁期间渲染线程可能正在写像素/调 UpdateLayeredWindow
        with self._update_lock:
            if not self._alive:
                return
            self._alive = False
            if self.hwnd:
                user32.UnregisterHotKey(self.hwnd, 1)
                _hwnd_to_inst.pop(self.hwnd, None)
                user32.DestroyWindow(self.hwnd); self.hwnd = None
            if self.mem_dc:
                gdi32.DeleteDC(self.mem_dc); self.mem_dc = None
            if self.hbm:
                gdi32.DeleteObject(self.hbm); self.hbm = None
            if self._screen_dc:
                user32.ReleaseDC(0, self._screen_dc); self._screen_dc = None
