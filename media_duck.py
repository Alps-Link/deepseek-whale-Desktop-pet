"""TTS 压低外部声音：她说话时把浏览器/音乐播放器的音量临时压下去，说完恢复。

只剩这一件事（10/22 用户砍掉了整套播放器控制，只保留"压低"这个体验）。
不依赖 SMTC/winsdk，只用 pycaw 的按程序音量（音量合成器那套接口）。

规则（沿用用户 10/22 定的口径）：只认音乐播放器和浏览器，**游戏和别的程序一律不碰**；
优先挑"正在出声"的那个；找不到就什么都不压。
"""
import time

AVAILABLE = False
try:
    from pycaw.pycaw import AudioUtilities
    AVAILABLE = True
except Exception:
    AudioUtilities = None

# 允许被压低的进程关键字
MUSIC_PLAYERS = ("cloudmusic", "qqmusic", "netease", "spotify",
                 "kugou", "kuwo", "foobar2000", "musicbee", "aimp")
BROWSERS = ("msedge", "chrome", "firefox", "brave", "opera", "vivaldi")
ALLOWED = MUSIC_PLAYERS + BROWSERS

# 她自己（绝不能压自己的声音）
SELF_PROCS = ("python.exe", "dafeiyupet.exe", "pythonw.exe")


def _sessions():
    if not AVAILABLE:
        return []
    out = []
    try:
        for s in AudioUtilities.GetAllSessions():
            if s.Process is None:
                continue
            name = (s.Process.name() or "").lower()
            if not name or name in SELF_PROCS:
                continue
            if not any(k in name for k in ALLOWED):
                continue
            out.append((name, s))
    except Exception:
        return []
    return out


def pick(target_proc=None):
    """挑出要被压的那个会话：指定优先，否则取"正在出声"的第一个白名单进程"""
    rows = _sessions()
    if target_proc:
        hint = target_proc.lower()
        for name, s in rows:
            if hint in name:
                return name, s
        return None, None
    for name, s in rows:
        try:
            if getattr(s, "State", 0) == 1:      # 1 = Active（在出声）
                return name, s
        except Exception:
            continue
    return None, None


def get_volume(proc=None):
    name, s = pick(proc)
    if s is None:
        return None
    try:
        return round(s.SimpleAudioVolume.GetMasterVolume() * 100)
    except Exception:
        return None


def set_volume(value, proc=None):
    name, s = pick(proc)
    if s is None:
        return False
    try:
        s.SimpleAudioVolume.SetMasterVolume(max(0.0, min(1.0, float(value) / 100.0)), None)
        return True
    except Exception:
        return False


def duck(ratio=0.25, seconds=0.35):
    """压低外部声音：返回 (进程名, 原音量) 供 restore 用；没在放或本来就够小则返回 None。

    10/23 修的两个坑：
    ①**绝不提高**——以前写死 fade(25)，用户音量本来就低于 25 时，她一说话反而把它调响；
       现在按"当前音量 × ratio"算，且目标不比当前大才动手。
    ②**记住是哪个进程**——以前 restore 又重新挑一次"谁在出声"，浏览器这时候已经不响了
       就会挑到别的程序，原来那个永远卡在压低后的音量。现在把进程名一起带回去。
    """
    name, s = pick()
    if s is None:
        return None
    cur = get_volume(name)
    if cur is None or cur <= 0:
        return None
    target = int(round(cur * ratio))
    if target >= cur:
        return None
    if not fade(target, seconds, proc=name):
        pass
    return (name, cur)


def restore(saved, seconds=0.7):
    """把 duck() 抓到的那个程序还原回原音量"""
    if not saved:
        return False
    name, cur = saved
    return fade(int(cur), seconds, proc=name) is not None


def fade(target, seconds=0.35, steps=12, proc=None):
    """把外部声音渐变到 target(%)"""
    cur = get_volume(proc)
    if cur is None:
        return None
    target = max(0, min(100, int(target)))
    if cur == target:
        return cur
    step_sleep = max(0.01, seconds / max(1, steps))
    for i in range(1, steps + 1):
        v = cur + (target - cur) * i / steps
        if not set_volume(v, proc):
            return cur
        time.sleep(step_sleep)
    return cur
