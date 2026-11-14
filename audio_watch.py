"""系统声音监听（WASAPI loopback）：把"听得见"变成几句能拼进提示词的事实。

为什么单独一个模块：音频和画面是两条独立输入，不共用环形缓冲。
音频每 0.5 秒就能压成几个数（响度/峰值/低频占比），20 秒只有 2 KB，
所以这里只留一个很长的特征环形（默认 5 分钟），不需要存原始波形。

判据来源（真机采过的量级，16 kHz mono）：
  · 安静房间 / 只开风扇：RMS 约 -55 ~ -45 dBFS
  · 有人说话 / 音乐：-35 ~ -25
  · 游戏枪战：-20 ~ -12，且短促峰值密集
"""
import collections
import threading
import time

import numpy as np

try:
    import soundcard as sc
except Exception:  # 没装就让调用方看到明确原因
    sc = None

SR = 16000


class AudioMeter:
    """后台线程采 loopback 音频，按窗口压成特征，供 describe() 出人话。"""

    def __init__(self, samplerate=SR, window=0.5, keep_seconds=300):
        self.sr = int(samplerate)
        self.window = float(window)
        self.keep = int(max(1, keep_seconds / self.window))
        self._frames = collections.deque(maxlen=self.keep)   # (ts, dict)
        self._stop = threading.Event()
        self._thread = None
        self._ok = False
        self._err = ""
        self._lock = threading.Lock()

    # ---------- 生命周期 ----------
    def start(self):
        if self._thread and self._thread.is_alive():
            return True
        if sc is None:
            self._err = "soundcard 未安装"
            return False
        self._stop.clear()
        self._thread = threading.Thread(target=self._loop, daemon=True, name="AudioMeter")
        self._thread.start()
        time.sleep(0.35)
        return self._ok

    def stop(self):
        self._stop.set()
        t = self._thread
        if t and t.is_alive():
            t.join(timeout=1.5)
        self._thread = None

    @property
    def error(self):
        return self._err

    # ---------- 采集 ----------
    def _pick_loopback(self):
        mics = sc.all_microphones(include_loopback=True)
        loops = [m for m in mics if getattr(m, "isloopback", False)]
        if not loops:
            raise RuntimeError("没有 loopback 设备")
        # 优先默认扬声器对应的那个（名字一致）
        try:
            name = sc.default_speaker().name
            for m in loops:
                if m.name == name:
                    return m
        except Exception:
            pass
        return loops[0]

    def _loop(self):
        try:
            mic = self._pick_loopback()
            chunk = int(self.sr * 0.25)
            need = max(2, int(round(self.window / 0.25)))
            with mic.recorder(samplerate=self.sr, channels=1) as rec:
                self._ok = True
                acc = []
                while not self._stop.is_set():
                    block = rec.record(numframes=chunk)
                    x = np.asarray(block, dtype=np.float32).reshape(-1)
                    if x.size == 0:
                        continue
                    acc.append(x)
                    if len(acc) >= need:
                        buf = np.concatenate(acc)
                        acc = []
                        feat = self._features(buf)
                        with self._lock:
                            self._frames.append((time.time(), feat))
        except Exception as e:
            self._ok = False
            self._err = str(e)
        finally:
            self._ok = False

    def _features(self, x):
        n = x.size
        if n < 64:
            return {"db": -90.0, "peak": 0.0, "low": 0.0, "high": 0.0, "trans": 0}
        rms = float(np.sqrt(np.mean(x * x)) + 1e-12)
        peak = float(np.max(np.abs(x)))
        db = 20.0 * float(np.log10(rms + 1e-12))
        spec = np.abs(np.fft.rfft(x * np.hanning(n)))
        freqs = np.fft.rfftfreq(n, 1.0 / self.sr)
        low = float(spec[(freqs >= 20) & (freqs < 200)].sum())
        mid = float(spec[(freqs >= 200) & (freqs < 2000)].sum())
        high = float(spec[freqs >= 2000].sum())
        tot = low + mid + high + 1e-12
        # 短促冲击：峰值远高于均方根（枪声、点击、爆炸的起手）
        trans = 1 if (peak > 0.12 and peak / (rms + 1e-9) > 4.0) else 0
        return {"db": db, "peak": peak, "low": low / tot, "high": high / tot, "trans": trans}

    # ---------- 读 ----------
    def recent(self, seconds=20.0):
        now = time.time()
        with self._lock:
            return [(t, f) for (t, f) in self._frames if now - t <= seconds]

    def describe(self, seconds=20.0):
        """把最近 N 秒的声音压成一句人话；没数据返回空串。"""
        rows = self.recent(seconds)
        if len(rows) < 3:
            return ""
        dbs = [f["db"] for _, f in rows]
        avg = float(np.mean(dbs))
        trans = sum(f["trans"] for _, f in rows)
        low = float(np.mean([f["low"] for _, f in rows]))
        # 前后半段对比：突然变吵 / 突然安静
        half = max(1, len(dbs) // 2)
        first, second = float(np.mean(dbs[:half])), float(np.mean(dbs[half:]))
        swing = second - first

        parts = []
        if avg < -50:
            parts.append("几乎没声音")
        elif avg < -38:
            parts.append("有一点底噪")
        elif avg < -28:
            parts.append("一直有声音")
        else:
            parts.append("挺吵的")

        if trans >= 1:
            parts.append("有 %d 下短促的响动（枪声/点击这类）" % trans)
        if low >= 0.55 and avg > -40:
            parts.append("低频很重（爆炸、引擎或重低音）")
        if swing >= 8:
            parts.append("比前几秒明显变吵")
        elif swing <= -8:
            parts.append("刚安静下来")
        return "声音（近 %d 秒）：%s。" % (int(seconds), "，".join(parts))


if __name__ == "__main__":
    import sys
    secs = float(sys.argv[1]) if len(sys.argv) > 1 else 20.0
    m = AudioMeter()
    ok = m.start()
    print("启动：", ok, m.error or "")
    if not ok:
        raise SystemExit(1)
    print("采样 %.0f 秒……" % secs)
    time.sleep(secs)
    rows = m.recent(secs)
    print("窗口数：", len(rows))
    if rows:
        dbs = [f["db"] for _, f in rows]
        print("响度 dBFS：min %.1f / 中位 %.1f / max %.1f" % (
            min(dbs), float(np.median(dbs)), max(dbs)))
        print("冲击：", sum(f["trans"] for _, f in rows), "次")
    print("描述：", m.describe(secs))
    m.stop()
