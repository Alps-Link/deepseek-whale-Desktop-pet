"""浏览器媒体控制：读"浏览器里在放什么"、控它的播放/暂停/上下首/进度。

用户 10/22 的口径："把浏览器的控制也加回来吧，让浏览器担任音乐播放"。
**只控浏览器**（Edge/Chrome/Firefox 这类注册了系统媒体会话的），不碰桌面播放器、不碰别的程序。
走 SMTC（`winsdk`），读到的就是浏览器的媒体会话。
"""
import asyncio

AVAILABLE = False
try:
    from winsdk.windows.media.control import (
        GlobalSystemMediaTransportControlsSessionManager as _Mgr,
    )
    AVAILABLE = True
except Exception:
    _Mgr = None

BROWSER_HINTS = ("msedge", "chrome", "firefox", "brave", "opera", "vivaldi", "edge")


def _status_name(st):
    return str(st).split(".")[-1].lower() if st is not None else "unknown"


def _is_browser(app):
    a = (app or "").lower()
    return any(k in a for k in BROWSER_HINTS)


async def _collect():
    mgr = await _Mgr.request_async()
    out = []
    for s in mgr.get_sessions():
        try:
            app = s.source_app_user_model_id or ""
            if not _is_browser(app):
                continue
            info = s.get_playback_info()
            tl = s.get_timeline_properties()
            title = artist = ""
            try:
                pm = await s.try_get_media_properties_async()
                title = (pm.title or "").strip()
                artist = (pm.artist or "").strip()
            except Exception:
                pass
            out.append({
                "app": app, "title": title, "artist": artist,
                "status": _status_name(info.playback_status),
                "position": round(tl.position.total_seconds(), 1) if tl else -1,
                "duration": round(tl.end_time.total_seconds(), 1) if tl else -1,
                "can_next": bool(info.controls.is_next_enabled),
                "can_prev": bool(info.controls.is_previous_enabled),
                "_s": s,
            })
        except Exception:
            continue
    return out


def status():
    """当前浏览器在放什么；没在放返回 None"""
    if not AVAILABLE:
        return None
    try:
        rows = asyncio.run(_collect())
    except Exception:
        return None
    for want in ("playing", "paused"):
        for r in rows:
            if r["status"] == want:
                return {k: v for k, v in r.items() if k != "_s"}
    return None


def control(action, seek_to=None):
    """控制浏览器：play / pause / toggle / next / prev / seek（seek_to: 0~1 比例或秒数）"""
    if not AVAILABLE:
        return False, "这台机器读不到浏览器的媒体会话（缺 winsdk）"
    try:
        return asyncio.run(_control(action, seek_to))
    except Exception as e:
        return False, "%s: %s" % (type(e).__name__, str(e)[:50])


async def _control(action, seek_to=None):
    rows = await _collect()
    target = None
    for want in ("playing", "paused"):
        for r in rows:
            if r["status"] == want:
                target = r["_s"]
                break
        if target:
            break
    if target is None:
        return False, "浏览器里没有在放东西"
    try:
        a = (action or "").lower()
        if a == "play":
            ok = await target.try_play_async()
        elif a == "pause":
            ok = await target.try_pause_async()
        elif a == "toggle":
            ok = await target.try_toggle_play_pause_async()
        elif a == "next":
            ok = await target.try_skip_next_async()
        elif a == "prev":
            ok = await target.try_skip_previous_async()
        elif a == "seek":
            tl = target.get_timeline_properties()
            total = tl.end_time.total_seconds() if tl else 0
            if total <= 0:
                return False, "拿不到时长，跳不了"
            pos = (seek_to * total) if (seek_to is not None and seek_to <= 1) else (seek_to or 0)
            import datetime
            ok = await target.try_change_playback_position_async(
                datetime.timedelta(seconds=max(0, min(pos, total))))
        else:
            return False, "不认识的动作: %s" % action
        if not ok:
            return False, "浏览器没响应这个操作"
        return True, ""
    except Exception as e:
        return False, "%s: %s" % (type(e).__name__, str(e)[:50])
