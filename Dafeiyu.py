# -*- coding: utf-8 -*-
"""
大肥鱼桌宠 v8.7 - 文本/视觉模型支持 OpenAI 兼容接口（可配置任意提供方）+ 轮询率可配置
"""

import os
import sys
import json
import random
import time
import math
import re
import base64
import io
import hashlib
import uuid
import threading
import queue
import tempfile
import shutil
import ctypes
from ctypes import wintypes
try:
    import winreg          # 读系统代理（Edge TTS 用，见 resolve_edge_proxy）
except ImportError:
    winreg = None
import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox, font as tkfont
from PIL import Image, ImageTk
import numpy as np
import requests
import logging
from logging.handlers import RotatingFileHandler
from datetime import datetime
from memory_db import MemoryDB
try:
    from audio_watch import AudioMeter
except Exception:            # 没装 soundcard 时不该影响启动
    AudioMeter = None

# ---------- 打包资源路径处理 ----------
def resource_path(relative_path):
    """获取资源的绝对路径，兼容 PyInstaller 打包"""
    try:
        base_path = sys._MEIPASS
    except AttributeError:
        base_path = os.path.abspath(".")
    return os.path.join(base_path, relative_path)

# ---------- 用户数据存储目录（统一放入源码/exe 所在目录下的 userdata/）----------
if getattr(sys, 'frozen', False):
    _EXE_DIR = os.path.dirname(sys.executable)
else:
    _EXE_DIR = os.path.dirname(os.path.abspath(__file__))
CONFIG_DIR = os.path.join(_EXE_DIR, "userdata")

os.makedirs(CONFIG_DIR, exist_ok=True)

# 迁移旧数据：将根目录下的旧配置文件移入 userdata/
_CONFIG_FILES = [
    "memories.json", "chats.json", "dafeiyu.log", "alps.log.1", "alps.log.2", "alps.log.3",
    "user_profile.json", "system_prompt.txt", "banned_words.txt", "watch_config.json",
    "topic_history.json", "zoom_config.json", "reading_config.json",
    "character_config.json",
    "llm_config.json",
    "ds_api_key.json", "volc_api_key.json", "volc_endpoint_id.json",
    "tts_api_key.json", "tts_speaker_id.json",
    "tts_config.json", "topic_config.json",
    "ui_config.json", "config.json",
]
for _fn in _CONFIG_FILES:
    _old_path = os.path.join(_EXE_DIR, _fn)
    _new_path = os.path.join(CONFIG_DIR, _fn)
    if os.path.isfile(_old_path) and not os.path.exists(_new_path):
        try:
            os.rename(_old_path, _new_path)
        except Exception:
            pass

# ---------- 日志系统 ----------
LOG_FILE = os.path.join(CONFIG_DIR, "dafeiyu.log")
# 旧版 8 只的日志都叫 alps.log：新名字下还没有日志时，先把旧的（含轮转备份）改名过来，历史不断档
if os.path.basename(LOG_FILE) != "dafeiyu.log":
    for _suffix in ("", ".1", ".2", ".3"):
        _old_log = os.path.join(CONFIG_DIR, "dafeiyu.log" + _suffix)
        _new_log = LOG_FILE + _suffix
        if os.path.isfile(_old_log) and not os.path.exists(_new_log):
            try:
                os.rename(_old_log, _new_log)
            except Exception:
                pass
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)-5s] %(message)s",
    datefmt="%m-%d %H:%M:%S",
    handlers=[
        RotatingFileHandler(LOG_FILE, maxBytes=2*1024*1024, backupCount=3, encoding="utf-8"),
        logging.StreamHandler()
    ]
)
log = logging.getLogger("Dafeiyu")

# 原生崩溃（OpenGL 驱动访问冲突 0xc0000005 之类）不会留下 Python 异常和 traceback，
# 进程会被系统直接干掉。装上 faulthandler 把崩溃瞬间所有线程的 Python 栈写进单独文件，
# 下次再崩就能看到是哪个 GL 调用炸的（文件追加写，只留崩溃记录，很小）。
try:
    import faulthandler
    _FAULT_LOG = os.path.join(CONFIG_DIR, "dafeiyu_fault.log")
    _FAULT_FILE = open(_FAULT_LOG, "a", encoding="utf-8")
    _FAULT_FILE.write("\n=== %s 启动 pid=%d ===\n" % (
        datetime.now().strftime("%m-%d %H:%M:%S"), os.getpid()))
    _FAULT_FILE.flush()
    faulthandler.enable(file=_FAULT_FILE, all_threads=True)
except Exception as _e:
    _FAULT_FILE = None
    log.warning("faulthandler 未启用: %s", _e)

# ---------- 本地音乐工具（control_music）----------
# tools_config.json 可选：{"music_dir": "..."} 覆盖默认曲库位置（默认 userdata\music）
TOOLS_CONFIG_FILE = os.path.join(CONFIG_DIR, "tools_config.json")

# 本地音乐曲库（userdata\music，自动创建，无需配置路径）
MUSIC_REPO_DIR = os.path.join(CONFIG_DIR, "music")
try:
    os.makedirs(MUSIC_REPO_DIR, exist_ok=True)
    _repo_note = os.path.join(MUSIC_REPO_DIR, "把音乐放这里.txt")
    if not os.path.exists(_repo_note):
        with open(_repo_note, "w", encoding="utf-8") as _f:
            _f.write("把想听歌的音频文件（mp3 / flac / ogg / wav）放进本文件夹（可建子文件夹），\n"
                     "然后对桌宠说“放首歌”或“播放歌名”即可。\n")
except Exception:
    pass


def _seed_bundled_music():
    """打包版：exe 内置启动歌曲（music_starter）在曲库为空时放入曲库（仅此一次，不扫描其他目录）"""
    if not getattr(sys, "frozen", False):
        return
    starter = resource_path("music_starter")
    try:
        if not os.path.isdir(starter):
            return

        def _has_audio(d):
            for _r, _ds, ns in os.walk(d):
                for n in ns:
                    if n.lower().endswith((".mp3", ".flac", ".ogg", ".wav")):
                        return True
            return False

        if _has_audio(MUSIC_REPO_DIR):
            return
        copied = 0
        for _r, _ds, ns in os.walk(starter):
            for n in ns:
                if n.lower().endswith((".mp3", ".flac", ".ogg", ".wav")):
                    src = os.path.join(_r, n)
                    dst = os.path.join(MUSIC_REPO_DIR, os.path.relpath(src, starter))
                    os.makedirs(os.path.dirname(dst), exist_ok=True)
                    shutil.copy2(src, dst)
                    copied += 1
        if copied:
            log.info("已从内置资源放入 %d 首启动歌曲到曲库", copied)
    except Exception as e:
        log.warning("内置歌曲放入曲库失败: %s", e)


_seed_bundled_music()


def _split_artist_title(fname):
    """把文件名拆成 (歌手, 标题)，如 'G.E.M.邓紫棋 - 唯一.flac' -> ('G.E.M.邓紫棋', '唯一')"""
    stem = os.path.splitext(os.path.basename(fname))[0]
    if " - " in stem:
        artist, title = stem.split(" - ", 1)
        return artist.strip(), title.strip()
    return "", stem.strip()


def _detect_song_lang(fname):
    """粗略判断歌曲语言：标题含假名→ja；含西里尔字母→ru；含谚文→ko；纯拉丁→en；否则→zh"""
    _a, title = _split_artist_title(fname)
    text = title or os.path.splitext(os.path.basename(fname))[0]
    if any("\u3040" <= ch <= "\u30ff" for ch in text):
        return "ja"
    if any("\u0400" <= ch <= "\u04ff" for ch in text):
        return "ru"
    if any("\uac00" <= ch <= "\ud7af" for ch in text):
        return "ko"
    latin = sum(1 for ch in text if ("a" <= ch.lower() <= "z"))
    if latin and not any("\u4e00" <= ch <= "\u9fff" for ch in text):
        return "en"
    return "zh"


def _normalize_lang(word):
    """把用户口中的语言说法归一成 ja/en/ru/ko/zh；识别不出返回 None"""
    w = (word or "").strip().lower()
    if not w:
        return None
    table = [
        ("ja", ("日语", "日文", "日系", "日本", "japanese", "japan", "jp")),
        ("en", ("英语", "英文", "欧美", "english", "en")),
        ("ru", ("俄语", "俄文", "russian", "ru")),
        ("ko", ("韩语", "韩文", "korean", "ko")),
        ("zh", ("中文", "国语", "汉语", "华语", "普通话", "chinese", "cn")),
    ]
    for code, aliases in table:
        if w == code or w in aliases:
            return code
    for code, aliases in table:
        for a in aliases:
            if len(a) >= 2 and a in w:
                return code
    return None


_CN_DIGITS = {"零": 0, "一": 1, "二": 2, "两": 2, "三": 3, "四": 4, "五": 5,
              "六": 6, "七": 7, "八": 8, "九": 9}


def _cn_num_to_int(s):
    """把 '2'/'二'/'十二'/'二十三' 等转成 int；无法识别返回 None"""
    if not s:
        return None
    if s.isdigit():
        return int(s)
    if "十" in s:
        a, _sep, b = s.partition("十")
        tens = _CN_DIGITS.get(a, 1) if a else 1
        ones = _CN_DIGITS.get(b, 0) if b else 0
        return tens * 10 + ones
    return _CN_DIGITS.get(s)


_DSML_RE = re.compile(r"<[|｜]+\s*DSML\s*[|｜]+.*?(?:</[|｜]+\s*DSML\s*[|｜]+\s*calls\s*>|$)", re.S)


def _strip_dsml(text):
    """剥掉模型偶尔漏出来的原生工具调用语法（<｜｜DSML｜｜ ...>），别让她把它念出来。"""
    if not text or "DSML" not in str(text):
        return text
    cleaned = _DSML_RE.sub("", str(text)).strip()
    # 只剩标点/空白时当作没有内容
    if cleaned and not re.search(r"[0-9A-Za-z\u4e00-\u9fff]", cleaned):
        return ""
    return cleaned


def _parse_pick_num(text):
    """解析 '第2首'/'第二首'/'2号'/'二号'/'3' 这类点歌编号；不是编号返回 None"""
    m = re.match(r"^第?([0-9一二三四五六七八九十两]+)\s*(首|号)?$", (text or "").strip())
    if not m:
        return None
    return _cn_num_to_int(m.group(1))


def load_music_dir():
    """音乐来源（按优先级）：1) 用户显式设置的音乐库（config.json 的 tools 节 music_dir，
    通过右键 设置 → 音乐库设置 填写，免迁移）；2) 内置曲库 userdata\\music。
    不做任何自动扫描/迁移——未设置时内置曲库为空就是为空。"""
    try:
        md = _get_section("tools").get("music_dir")
        if isinstance(md, str) and md.strip() and os.path.isdir(md.strip()):
            return md.strip()
    except Exception:
        pass
    return MUSIC_REPO_DIR if os.path.isdir(MUSIC_REPO_DIR) else None


def load_music_mode():
    """音乐来源模式：local（本地曲库）/ web（网页版播放器）。默认 local"""
    try:
        m = (_get_section("tools").get("music_mode") or "local").strip().lower()
        return "web" if m == "web" else "local"
    except Exception:
        return "local"


def save_music_mode(mode):
    """保存音乐来源模式（local/web）"""
    try:
        sec = _get_section("tools")
        sec["music_mode"] = "web" if str(mode).lower() == "web" else "local"
        _update_section("tools", sec)
        return True
    except Exception as e:
        log.warning("保存音乐模式失败: %s", e)
        return False


def load_music_web_url():
    """网页版播放器网址（config.json 的 tools 节 music_web_url）"""
    try:
        return (_get_section("tools").get("music_web_url") or "").strip()
    except Exception:
        return ""


def save_music_web_url(url):
    """保存/清除网页版播放器网址（传空值=清除）"""
    try:
        sec = _get_section("tools")
        if url and url.strip():
            sec["music_web_url"] = url.strip()
        else:
            sec.pop("music_web_url", None)
        _update_section("tools", sec)
        return True
    except Exception as e:
        log.warning("保存网页版网址失败: %s", e)
        return False


def save_music_dir_setting(path):
    """保存/清除自定义音乐库路径（config.json 的 tools 节 music_dir）；传空值=恢复内置曲库"""
    try:
        sec = _get_section("tools")
        if path and path.strip():
            sec["music_dir"] = path.strip()
        else:
            sec.pop("music_dir", None)
        _update_section("tools", sec)
        return True
    except Exception as e:
        log.warning("保存音乐库设置失败: %s", e)
        return False


def load_music_volume():
    """音乐基础音量，百分比 0~100（config.json 的 tools 节 music_volume）。

    这是"没有她说话时"的音量基准；她说话期间会在此基础上再按 TTS_DUCK_RATIO 压低
    （见 _music_volume_now）。没设过就返回 MUSIC_VOLUME_DEFAULT。
    """
    try:
        v = _get_section("tools").get("music_volume")
        if isinstance(v, (int, float)) and not isinstance(v, bool):
            return max(0, min(100, int(round(float(v)))))
    except Exception:
        pass
    return int(round(MUSIC_VOLUME_DEFAULT * 100))


def save_music_volume_setting(percent):
    """保存音乐基础音量（百分比 0~100）；越界值会被夹进区间"""
    try:
        sec = _get_section("tools")
        sec["music_volume"] = max(0, min(100, int(percent)))
        _update_section("tools", sec)
        return True
    except Exception as e:
        log.warning("保存音乐音量失败: %s", e)
        return False
# Spine 渲染支持（可选）
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
try:
    from live2d_renderer import (Live2DRenderer, FORMS as LIVE2D_FORMS,
                             FORM_ORDER as LIVE2D_FORM_ORDER,
                             DEFAULT_FORM as LIVE2D_DEFAULT_FORM)
    SPINE_AVAILABLE = True
except (ImportError, Exception) as e:
    SPINE_AVAILABLE = False
    Live2DRenderer = None
    log.debug("Live2D 渲染不可用: %s", e)

# Win32 layered window（per-pixel alpha 显示，消除 tk 透明键色白边）
try:
    from layered_window import LayeredImageWindow
    LAYERED_AVAILABLE = True
except Exception as e:
    LayeredImageWindow = None
    LAYERED_AVAILABLE = False
    log.debug("LayeredWindow 不可用: %s", e)

# 截图库
try:
    import mss
except ImportError:
    mss = None

# 语音识别库（sherpa-onnx Paraformer 离线中文识别）
# 国内直连 huggingface.co 不通：默认走镜像（用户已设置 HF_ENDPOINT 时不覆盖）
os.environ.setdefault("HF_ENDPOINT", "https://hf-mirror.com")

def _ensure_onnxruntime_loaded():
    """sherpa-onnx 通过 find_library 查找 onnxruntime.dll，若系统目录（System32）
    存在旧版本（如 1.17.1）会被优先命中导致 API 不兼容。预先加载 Python 环境
    的 onnxruntime.dll，让 find_library 命中已加载模块。"""
    try:
        import onnxruntime as _ort
        _p = os.path.join(os.path.dirname(_ort.__file__), "capi", "onnxruntime.dll")
        if os.path.exists(_p):
            ctypes.windll.kernel32.LoadLibraryW(_p)
    except Exception:
        pass

try:
    _ensure_onnxruntime_loaded()
    import sherpa_onnx
    import pyaudio
    VOICE_AVAILABLE = True
except ImportError:
    # 开发环境兜底：依赖装在桌宠合集/_pylibs（site-packages 不可写时）
    try:
        _pylibs = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "_pylibs")
        if os.path.isdir(_pylibs):
            sys.path.insert(0, _pylibs)
        _ensure_onnxruntime_loaded()
        import sherpa_onnx
        import pyaudio
        VOICE_AVAILABLE = True
    except ImportError:
        sherpa_onnx = None
        pyaudio = None
        VOICE_AVAILABLE = False

# 拼音库（唤醒词模糊匹配用；同样支持 _pylibs 兜底）
try:
    from pypinyin import lazy_pinyin
    PINYIN_AVAILABLE = True
except ImportError:
    try:
        _pylibs = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "_pylibs")
        if os.path.isdir(_pylibs) and _pylibs not in sys.path:
            sys.path.insert(0, _pylibs)
        from pypinyin import lazy_pinyin
        PINYIN_AVAILABLE = True
    except ImportError:
        lazy_pinyin = None
        PINYIN_AVAILABLE = False

# 浏览器媒体控制（网页版模式下"浏览器就是音乐播放器"）。可选层。
try:
    import browser_media as _browser
except Exception as _e:
    _browser = None
    logging.getLogger(__name__).warning("浏览器媒体控制不可用: %s", _e)

# TTS 压低外部声音（浏览器/音乐播放器）。可选层：装不上就整体关闭，宠物照常跑。
try:
    import media_duck as _duck
except Exception as _e:
    _duck = None
    logging.getLogger(__name__).warning("外部声音压低不可用: %s", _e)

# OCR（读书伴侣）——10/19 从 EasyOCR 换成 RapidOCR（PP-OCR ONNX 模型）：
# EasyOCR 自己会 `import torch`（torch_cpu.dll 294MB + 约 1GB 提交内存、成品多背几百 MB），
# RapidOCR 用项目里本来就在跑的 onnxruntime，包约 15MB、识别也更准（实测 30→"30"、D:\CloudMusic 反斜杠正确）。
# 这里只 find_spec 探一下装没装，真正要用 OCR 时才在后台线程里导入。
try:
    import importlib.util as _ilu
    RAPIDOCR_AVAILABLE = _ilu.find_spec("rapidocr") is not None
except Exception:
    RAPIDOCR_AVAILABLE = False
rapidocr = None

# 视觉模型统一走 OpenAI 兼容 HTTP 接口（不再依赖火山引擎 SDK）

# ------------------------------- 配置区域 ---------------------------------
# 统一 LLM 配置文件（文本模型 + 视觉模型，均为 OpenAI 兼容 chat/completions 接口）
LLM_CONFIG_FILE = os.path.join(CONFIG_DIR, "llm_config.json")

# 旧配置文件路径：**只用于首次迁移**到 config.json（新代码一律读写 config.json 的对应节）
DS_API_KEY_FILE = os.path.join(CONFIG_DIR, "ds_api_key.json")
VOLC_API_KEY_FILE = os.path.join(CONFIG_DIR, "volc_api_key.json")
VOLC_ENDPOINT_ID_FILE = os.path.join(CONFIG_DIR, "volc_endpoint_id.json")

TTS_API_KEY_FILE = os.path.join(CONFIG_DIR, "tts_api_key.json")
TTS_SPEAKER_ID_FILE = os.path.join(CONFIG_DIR, "tts_speaker_id.json")

def _atomic_write_text(filepath, text, encoding="utf-8"):
    """原子写入文本文件：先写临时文件，再替换正式文件。

    10/28 两个并发修正：
    ①tmp 名带进程/线程标识 —— 固定名会让两条线程互相截断，写出来的文件少一半；
    ②Windows 上 `os.replace` 撞到"目标正被别的线程打开"会抛 WinError 5（拒绝访问），
      短暂退避后重试即可；失败必须把 tmp 清掉，别在目录里堆垃圾。
    """
    tmp_path = "%s.%d.%d.tmp" % (filepath, os.getpid(), threading.get_ident())
    try:
        with open(tmp_path, "w", encoding=encoding) as f:
            f.write(text)
            f.flush()
            os.fsync(f.fileno())
        last_err = None
        for attempt in range(10):
            try:
                os.replace(tmp_path, filepath)
                return
            except PermissionError as e:      # 目标被占用：等一会儿再来
                last_err = e
                time.sleep(0.008 * (attempt + 1))
        raise last_err
    finally:
        try:
            if os.path.exists(tmp_path):
                os.remove(tmp_path)
        except OSError:
            pass

# ------------------------- 统一配置文件 config.json -------------------------
# 设置/密钥/开关以前每种一个文件（llm_config / tts_config / tts_api_key / topic_config /
# watch_config / reading_config / zoom_config / ui_config / tools_config / character_config
# 以及更老的 ds·volc 三个）：现在全部收进 config.json 按节分组。
# 首次运行会把旧的散装文件合并进来，并把旧文件**原样移进** userdata\_legacy_configs\
# （只移动、不删除，随时能翻回去）。
CONFIG_FILE = os.path.join(CONFIG_DIR, "config.json")
LEGACY_CONFIG_DIR = os.path.join(CONFIG_DIR, "_legacy_configs")
_config_lock = threading.Lock()

def _read_app_config():
    """读整个 config.json；文件不存在时先做一次旧文件合并迁移。读坏了返回 {}（不抛）"""
    if os.path.exists(CONFIG_FILE):
        try:
            data = load_json_file(CONFIG_FILE, {})
            if isinstance(data, dict):
                return data
            log.warning("config.json 顶层不是对象，按空配置处理")
        except Exception as e:
            log.warning(f"config.json 读取失败，用默认值: {e}")
        return {}
    return _migrate_legacy_configs()

def _get_section(name, default=None):
    """取一节（dict）；缺失或类型不对时返回 default 的副本"""
    sec = _read_app_config().get(name)
    if isinstance(sec, dict):
        return sec
    return json.loads(json.dumps(default)) if isinstance(default, dict) else {}

def load_dsh_settings():
    """DSH 外包的配置：{"enabled": bool, "cli": str}（cli 空 = 自动检测）。"""
    sec = _get_section("tools", {}) or {}
    try:
        enabled = bool(sec.get("dsh_enabled", True))
    except Exception:
        enabled = True
    cli = str(sec.get("dsh_cli") or "").strip()
    return {"enabled": enabled, "cli": cli}


def save_dsh_settings(enabled, cli):
    """保存 DSH 外包配置（读-改-写 tools 节，别覆盖同节其它键）。"""
    sec = dict(_get_section("tools", {}) or {})
    sec["dsh_enabled"] = bool(enabled)
    sec["dsh_cli"] = (cli or "").strip()
    _update_section("tools", sec)


def _update_section(name, value):
    """读-改-写一节（带锁：后台线程与 UI 可能同时保存，别互相覆盖）"""
    with _config_lock:
        cfg = {}
        if os.path.exists(CONFIG_FILE):
            try:
                data = load_json_file(CONFIG_FILE, {})
                if isinstance(data, dict):
                    cfg = data
            except Exception as e:
                log.warning(f"config.json 读取失败，本次按空配置重建: {e}")
        cfg[name] = value
        save_json_file(CONFIG_FILE, cfg)

def _migrate_legacy_configs():
    """首次运行：把散装的旧配置文件合并成 config.json，旧文件移进 _legacy_configs 目录。
    先写盘、写成功才搬旧文件——搬移失败就原地留着，绝不丢数据。"""
    # 键必须是**文件名**（不是绝对路径）：下面要 os.path.join(LEGACY_CONFIG_DIR, fname)，
    # 若 fname 是绝对路径，join 会把它整个顶掉，等于原地改名成 .1（踩过这个坑）
    legacy = {
        os.path.basename(LLM_CONFIG_FILE): "llm",
        os.path.basename(DS_API_KEY_FILE): "_ds_api_key",
        os.path.basename(VOLC_API_KEY_FILE): "_volc_api_key",
        os.path.basename(VOLC_ENDPOINT_ID_FILE): "_volc_endpoint_id",
        os.path.basename(TTS_CONFIG_FILE): "tts",
        os.path.basename(TTS_API_KEY_FILE): "_tts_api_key",
        os.path.basename(TTS_SPEAKER_ID_FILE): "_tts_speaker_id",
        os.path.basename(TOPIC_CONFIG_FILE): "topic",
        os.path.basename(WATCH_CONFIG_FILE): "watch",
        os.path.basename(READING_CONFIG_FILE): "reading",
        os.path.basename(ZOOM_CONFIG_FILE): "zoom",
        os.path.basename(UI_CONFIG_FILE): "ui",
        os.path.basename(TOOLS_CONFIG_FILE): "tools",
        os.path.basename(CHARACTER_CONFIG_FILE): "character",
    }
    cfg, found = {}, []
    for fname, section in legacy.items():
        path = os.path.join(CONFIG_DIR, fname)
        if not os.path.exists(path):
            path = os.path.join(LEGACY_CONFIG_DIR, fname)   # config.json 丢了也能从旧副本重来
        if not os.path.exists(path):
            continue
        try:
            data = load_json_file(path, None)
        except Exception as e:
            log.warning(f"旧配置 {fname} 读取失败，跳过: {e}")
            continue
        if data is None:
            continue
        found.append(fname)
        if section.startswith("_"):
            cfg.setdefault("_kv", {})[section[1:]] = data if isinstance(data, dict) else {}
        elif isinstance(data, (dict, list)):
            cfg[section] = data
    if not found:
        return {}
    # 老的单键文件并入 llm / tts 节（沿用旧版语义：文件内容优先，其次环境变量）
    kv = cfg.pop("_kv", {})
    llm = cfg.get("llm") if isinstance(cfg.get("llm"), dict) else {}
    text = dict(llm.get("text") or {})
    vision = dict(llm.get("vision") or {})
    if not text.get("api_key"):
        text["api_key"] = (kv.get("ds_api_key") or {}).get("api_key", "") or os.environ.get("DEEPSEEK_API_KEY", "")
    if not vision.get("api_key"):
        vision["api_key"] = (kv.get("volc_api_key") or {}).get("api_key", "") or os.environ.get("VOLC_ARK_API_KEY", "")
    if not vision.get("model"):
        vision["model"] = (kv.get("volc_endpoint_id") or {}).get("endpoint_id", "") or os.environ.get("VOLC_ENDPOINT_ID", "")
    cfg["llm"] = {"text": text, "vision": vision}
    tts = cfg.get("tts") if isinstance(cfg.get("tts"), dict) else {}
    tts["api_key"] = tts.get("api_key") or (kv.get("tts_api_key") or {}).get("api_key", "")
    tts["speaker_id"] = tts.get("speaker_id") or (kv.get("tts_speaker_id") or {}).get("speaker_id", "")
    cfg["tts"] = tts
    try:
        save_json_file(CONFIG_FILE, cfg)
    except Exception as e:
        log.error(f"合并旧配置写 config.json 失败，旧文件保持原样: {e}")
        return cfg
    for fname in found:
        src = os.path.join(CONFIG_DIR, fname)
        if not os.path.exists(src):
            continue        # 本次是从 _legacy_configs 里读的，已经搬过了
        try:
            os.makedirs(LEGACY_CONFIG_DIR, exist_ok=True)
            dst = os.path.join(LEGACY_CONFIG_DIR, fname)
            n = 1
            while os.path.exists(dst):
                dst = os.path.join(LEGACY_CONFIG_DIR, f"{fname}.{n}")
                n += 1
            os.replace(os.path.join(CONFIG_DIR, fname), dst)
        except Exception as e:
            log.warning(f"旧配置 {fname} 搬移失败（留在原地不影响使用）: {e}")
    log.info(f"配置已合并进 config.json，{len(found)} 个旧文件移到 _legacy_configs 目录")
    return cfg

def load_tts_api_key():       return _get_section("tts").get("api_key", "")

def save_tts_api_key(v):
    sec = _get_section("tts"); sec["api_key"] = v; _update_section("tts", sec)

def load_tts_speaker_id():    return _get_section("tts").get("speaker_id", "")

def save_tts_speaker_id(v):
    sec = _get_section("tts"); sec["speaker_id"] = v; _update_section("tts", sec)

TTS_CONFIG_FILE = os.path.join(CONFIG_DIR, "tts_config.json")
TOPIC_CONFIG_FILE = os.path.join(CONFIG_DIR, "topic_config.json")

# ------------------------------- TTS 音色与语言 ---------------------------------
# 语言：zh=中文（不翻译）、en=英文、ja=日语。选了非中文语言时，播前把要说的话翻译成该语言再送 TTS；
# 气泡、聊天记录、记忆始终是中文原文，只有"念出来"的是译文；翻译失败则退回中文音色念原文。
TTS_LANG_NAMES = {"zh": "中文", "en": "英文", "ja": "日语"}
EDGE_VOICE_TABLE = {                     # Edge 音色（按语言分组，设置窗里按语言过滤）
    "zh": [("晓晓", "zh-CN-XiaoxiaoNeural"), ("晓伊", "zh-CN-XiaoyiNeural")],
    "en": [("Emily", "en-IE-EmilyNeural"), ("Ana", "en-US-AnaNeural")],
}
DEFAULT_EDGE_VOICE = "zh-CN-XiaoyiNeural"          # 兜底音色（翻译失败时也用回它）
EDGE_VOICE_DEFAULT = {"zh": "zh-CN-XiaoyiNeural",   # 每个语言的默认音色（中文默认仍是晓伊，保持老观感）
                      "en": "en-IE-EmilyNeural"}
TTS_PREVIEW_TEXT = {"zh": "今天天气不错，我们听首歌吧。",
                    "en": "Hello, this is a quick test of my voice.",
                    "ja": "こんにちは、これは声のテストです。"}


def edge_voice_valid(lang, voice):
    """音色是否属于该语言分组"""
    return any(v == voice for _, v in EDGE_VOICE_TABLE.get(lang, []))


# ------------------------------- Edge 走不走代理 ---------------------------------
# 起因（10/12）：微软的朗读接口会按来源 IP 拒掉部分直连——WebSocket 握手回 403
# "Invalid response status"，而 HTTPS 的 voices/list 仍返回 200，走本机代理就能通。
# 默认 auto = 跟随 Windows 系统代理（代理端口换了也不用改配置）；off = 强制直连。
EDGE_PROXY_AUTO = "auto"
EDGE_PROXY_OFF = ("off", "none", "direct", "false", "0")


def _system_proxy_url():
    """读 Windows 系统代理，返回 aiohttp 能用的地址；没开或读不到返回 None"""
    if winreg is None:
        return None
    try:
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER,
                            r"Software\Microsoft\Windows\CurrentVersion\Internet Settings") as key:
            if not winreg.QueryValueEx(key, "ProxyEnable")[0]:
                return None
            server = str(winreg.QueryValueEx(key, "ProxyServer")[0] or "").strip()
    except OSError:
        return None
    if not server:
        return None
    if "=" in server:                      # 分协议写法：http=host:port;https=host:port
        parts = {}
        for item in server.split(";"):
            name, _, value = item.partition("=")
            parts[name.strip().lower()] = value.strip()
        server = parts.get("https") or parts.get("http") or ""
        if not server:                     # 只配了 socks 之类：宁可不走，也别把 TTS 弄坏
            return None
    return server if "://" in server else "http://" + server


def resolve_edge_proxy(val=None):
    """把 tts.edge_proxy 解析成实际代理地址：空/auto=跟随系统代理，off=直连，其它=显式地址"""
    v = str(val if val is not None else "").strip()
    if not v or v.lower() == EDGE_PROXY_AUTO:
        return _system_proxy_url()
    if v.lower() in EDGE_PROXY_OFF:
        return None
    return v if "://" in v else "http://" + v


# ------------------------- 火山火山区走哪个集群 -------------------------
# 10/12：cluster 原来写死 volcano_icl（声音复刻），用户填的却是大模型预置音色
# `zh_female_vv_uranus_bigtts` ⇒ 服务端回 400 / code 3001 "model invalid key"。
# 判据：复刻音色 ID 形如 `S_xxxx`（走 volcano_icl），其余预置音色走 volcano_tts。
VOLC_CLUSTER_ICL = "volcano_icl"
VOLC_CLUSTER_TTS = "volcano_tts"
VOLC_CLUSTER_LABELS = {VOLC_CLUSTER_ICL: "声音复刻", VOLC_CLUSTER_TTS: "大模型语音"}


def resolve_volc_cluster(speaker_id, configured=None):
    """按音色 ID 判集群；tts.volc_cluster 填了非 auto 的值就以它为准"""
    v = str(configured if configured is not None else "").strip()
    if v and v.lower() != "auto":
        return v
    return VOLC_CLUSTER_ICL if str(speaker_id or "").strip()[:2].upper() == "S_" else VOLC_CLUSTER_TTS


def load_tts_config():
    """加载 TTS 状态（开关/模式/语言/音色），避免每次启动重新设置"""
    data = _get_section("tts")
    mode = data.get("mode", "volc")
    if mode not in ("volc", "edge", "deepseek"):
        mode = "volc"
    volc_lang = str(data.get("volc_lang", "") or "").lower()
    if volc_lang not in ("zh", "en", "ja"):
        # 老配置没有 volc_lang：用旧的日语开关迁移（true = 日语 / false = 中文）
        volc_lang = "ja" if data.get("japanese") else "zh"
    edge_lang = str(data.get("edge_lang", "") or "").lower()
    if edge_lang not in EDGE_VOICE_TABLE:
        edge_lang = "zh"
    edge_voice = str(data.get("edge_voice", "") or "")
    if not edge_voice_valid(edge_lang, edge_voice):
        edge_voice = EDGE_VOICE_DEFAULT.get(edge_lang) or EDGE_VOICE_TABLE[edge_lang][0][1]
    edge_proxy = str(data.get("edge_proxy", "") or "").strip() or EDGE_PROXY_AUTO
    volc_cluster = str(data.get("volc_cluster", "") or "").strip() or "auto"
    ds_voice = str(data.get("deepseek_voice", "") or "").strip() or DEEPSEEK_TTS_VOICE_DEFAULT
    if ds_voice not in [v for v, _n in DEEPSEEK_TTS_VOICES]:
        ds_voice = DEEPSEEK_TTS_VOICE_DEFAULT
    ds_lang = str(data.get("deepseek_lang", "") or "").lower()
    if ds_lang not in ("zh", "en", "ja"):
        ds_lang = "zh"
    return {
        "enabled": bool(data.get("enabled", False)),
        "mode": mode,
        "japanese": volc_lang == "ja",     # 兼容旧键
        "volc_lang": volc_lang,
        "edge_lang": edge_lang,
        "edge_voice": edge_voice,
        "edge_proxy": edge_proxy,
        "volc_cluster": volc_cluster,
        "deepseek_voice": ds_voice,
        "deepseek_lang": ds_lang,
        "deepseek_api_key": str(data.get("deepseek_api_key", "") or "").strip(),
    }

def save_tts_config(enabled=None, mode=None, japanese=None,
                    volc_lang=None, edge_lang=None, edge_voice=None,
                    edge_proxy=None, volc_cluster=None,
                    deepseek_voice=None, deepseek_api_key=None,
                    deepseek_lang=None):
    """只写传入的字段，其余保持原值（同节的 api_key / speaker_id 一律保留）"""
    sec = _get_section("tts")
    if enabled is not None:
        sec["enabled"] = bool(enabled)
    if mode is not None:
        sec["mode"] = mode
    if volc_lang is not None:
        sec["volc_lang"] = volc_lang
    elif japanese is not None:                        # 兼容老调用
        sec["volc_lang"] = "ja" if japanese else "zh"
    if edge_lang is not None:
        sec["edge_lang"] = edge_lang
    if edge_voice is not None:
        sec["edge_voice"] = edge_voice
    if edge_proxy is not None:
        sec["edge_proxy"] = str(edge_proxy).strip() or EDGE_PROXY_AUTO
    if volc_cluster is not None:
        sec["volc_cluster"] = str(volc_cluster).strip() or "auto"
    if deepseek_voice is not None:
        sec["deepseek_voice"] = deepseek_voice
    if deepseek_lang is not None:
        sec["deepseek_lang"] = deepseek_lang
    if deepseek_api_key is not None:
        sec["deepseek_api_key"] = str(deepseek_api_key).strip()
    sec["japanese"] = (sec.get("volc_lang") == "ja")  # 旧键跟着走，别的版本读它也不会错
    _update_section("tts", sec)

# 11/01：主动话题的频率内置（用户拍板"不再手动调节、保持开启、按时段加权"）。
# 令牌桶模型：每小时按「时段权重」回填额度，攒够 1 个才可能开口；桶最多存 2 个。
TOPIC_PROACTIVE_PER_DAY = 12      # 日均主动话题条数（总量由它定，形态由权重定）
TOPIC_HOUR_WEIGHTS = ((0, 0.005), (8, 1.0), (12, 0.25), (14, 1.0), (21, 0.5), (24, 0.005))
TOPIC_WEIGHT_RAMP_H = 0.5        # 每个边界前后各用半小时线性过渡（11/01：阶梯改成曲线，避免 12:00/14:00 硬跳）
TOPIC_MAX_SILENCE_H = 6          # 超过这么久没主动说过就强制一句（只在 8:00–24:00 生效）
TOPIC_MIN_GAP_MIN = 25            # 两次主动话题之间至少隔这么久（防扎堆）
TOPIC_TICK_SECONDS = 300          # 每 5 分钟结算一次
TOPIC_RATE_BOOST = 1.5            # 补偿"最小间隔"挡掉的那部分，让实际日均落在 12 次左右


def topic_hour_weight(hour, minute=0):
    """连续时段权重：平台段保持、边界前后半小时线性过渡。"""
    t = float(hour) + float(minute) / 60.0
    prev_val = TOPIC_HOUR_WEIGHTS[0][1]
    for h, v in TOPIC_HOUR_WEIGHTS[1:]:
        start = h - TOPIC_WEIGHT_RAMP_H
        if t < start:
            return prev_val
        if t < h:
            return prev_val + (v - prev_val) * (t - start) / TOPIC_WEIGHT_RAMP_H
        prev_val = v
    return prev_val


def topic_weight_total():
    """全天权重的积分（按 5 分钟采样求和，够准）"""
    total = 0.0
    for m in range(0, 24 * 60, 5):
        total += topic_hour_weight(m // 60, m % 60) * (5.0 / 60.0)
    return total


def topic_refill_per_hour():
    """基准速率（次/小时）；实际还要再乘当时段的权重。

    × TOPIC_RATE_BOOST 是补偿"最小间隔"挡掉的那部分——被挡掉的抽签直接作废，
    实测会把日均从 12 压到 ~10，所以先按 1.35 倍发。
    """
    total = topic_weight_total()
    return (TOPIC_PROACTIVE_PER_DAY * TOPIC_RATE_BOOST / total) if total > 0 else 0.0


def _topic_probe_chance(n_unknown):
    """还有多少类目没采集到 ⇒ 本轮"去补空白"的概率（11/05 用户要求：补空白优先级更高）。

    画像还稀疏时几乎每轮都去问；快补齐了就退回偶尔问，免得像审问。
    """
    try:
        n = int(n_unknown)
    except Exception:
        return TOPIC_PROBE_CHANCE
    for need, p in TOPIC_PROBE_BY_UNKNOWN:
        if n >= need:
            return p
    return 0.0


_FR_SAFE_CONFIG = {
    # 白名单：只列"确定不敏感"的字段（不按 key 名黑名单过滤——嵌套字典会漏）。
    # 11/05 按真实 config.json 的键名对齐（llm/tts.api_key/speaker_id 一律不列）。
    ("form", "name"),
    ("zoom", "zoom_char"), ("zoom", "zoom_bubble"), ("zoom", "window_width"),
    ("watch", "min_interval"), ("watch", "max_silence"),
    ("reading", "capture_interval"), ("reading", "min_interval"), ("reading", "max_silence"),
    ("tools", "music_mode"), ("tools", "music_volume"),
    ("voice", "enabled"), ("voice", "wake_window"),
    ("voice", "hotkey_enabled"), ("voice", "hotkey_name"),
    ("tts", "enabled"), ("tts", "mode"), ("tts", "volc_lang"), ("tts", "edge_lang"),
    ("tts", "edge_voice"),
    ("ui", "input_visible"), ("ui", "hide_reply_bubble"),
    ("costume", "item"), ("costume", "head"),
}
_FR_LOG_DROP = ("凑过来", "瞟一眼", "话题生成", "语音识别", "识别到", "用户说",
                "TTS 播放", "播放语音", "聊天", "comment", "记忆提取完成:")
_FR_SECRET_RE = None


def _fr_redact(text):
    """把明显的密钥形态抹掉（白名单之外的最后一道保险）。"""
    import re as _re
    if not text:
        return text
    text = _re.sub(r"(sk-[A-Za-z0-9]{6})[A-Za-z0-9\-]{6,}", r"***", text)
    text = _re.sub(r"([A-Za-z0-9_\-]{24,})", lambda m: (m.group(1)[:6] + "***") if len(m.group(1)) >= 24 else m.group(1), text)
    return text


def _fr_env_lines():
    """环境信息（不改任何状态，失败就跳过）。"""
    import platform as _pf
    out = []
    try:
        out.append("Windows: %s (%s)" % (_pf.platform(), _pf.version()))
    except Exception:
        pass
    try:
        out.append("Python: %s" % _pf.python_version())
    except Exception:
        pass
    try:
        out.append("CPU 逻辑核: %s" % os.cpu_count())
    except Exception:
        pass
    try:
        import ctypes
        u = ctypes.windll.user32
        out.append("屏幕: %sx%s" % (u.GetSystemMetrics(0), u.GetSystemMetrics(1)))
        try:
            dpi = ctypes.windll.shcore.GetDpiForSystem()
            out.append("系统 DPI: %s (缩放 %.0f%%)" % (dpi, dpi / 96 * 100))
        except Exception:
            pass
    except Exception:
        pass
    try:
        out.append("工作目录: %s" % os.getcwd())
    except Exception:
        pass
    return out


def load_topic_config():
    """加载话题定时器状态（开关/间隔模式：fixed=固定分钟，random=随机区间分钟）"""
    data = _get_section("topic")
    try:
        interval = max(1, min(240, int(data.get("interval_minutes", 5))))
    except (TypeError, ValueError):
        interval = 5
    mode = data.get("mode", "fixed")
    if mode not in ("fixed", "random"):
        mode = "fixed"
    try:
        rmin = max(1, min(240, int(data.get("random_min", 10))))
    except (TypeError, ValueError):
        rmin = 10
    try:
        rmax = max(1, min(240, int(data.get("random_max", 30))))
    except (TypeError, ValueError):
        rmax = 30
    if rmin > rmax:
        rmin, rmax = rmax, rmin
    return {
        "enabled": bool(data.get("enabled", False)),
        "interval_minutes": interval,
        "mode": mode,
        "random_min": rmin,
        "random_max": rmax,
    }

def save_topic_config(enabled, interval_minutes, mode="fixed", random_min=10, random_max=30):
    _update_section("topic", {
        "enabled": enabled,
        "interval_minutes": interval_minutes,
        "mode": mode,
        "random_min": random_min,
        "random_max": random_max,
    })

# 文本模型默认配置（对话 / 记忆提取 / 话题 / 翻译 / 读书等）
DEFAULT_TEXT_CONFIG = {
    "base_url": "https://api.deepseek.com/v1",
    "api_key": "",
    "model": "deepseek-v4-flash",
}
# 视觉模型默认配置（陪看截图分析 / 内容识别）
DEFAULT_VISION_CONFIG = {
    "base_url": "https://ark.cn-beijing.volces.com/api/v3",
    "api_key": "",
    "model": "",
}

UI_CONFIG_FILE = os.path.join(CONFIG_DIR, "ui_config.json")

def load_ui_config():
    """界面开关状态（输入框显示/隐藏），跨重启沿用。
    注：语音识别开关不做保存——启动跟随开麦那条路用户不要。"""
    data = _get_section("ui")
    return {"input_visible": bool(data.get("input_visible", True)),
            "hide_reply_bubble": bool(data.get("hide_reply_bubble", False))}

def save_ui_config(input_visible, hide_reply_bubble=None):
    sec = _get_section("ui")     # 保留同节其它键
    sec["input_visible"] = bool(input_visible)
    if hide_reply_bubble is not None:
        sec["hide_reply_bubble"] = bool(hide_reply_bubble)
    _update_section("ui", sec)

def load_llm_config():
    """加载统一 LLM 配置（config.json 的 llm 节；老的 ds/volc 文件在首次迁移时已并进来，
    环境变量仍可兜底）。"""
    data = _get_section("llm")
    text = dict(DEFAULT_TEXT_CONFIG)
    vision = dict(DEFAULT_VISION_CONFIG)
    text.update(data.get("text") or {})
    vision.update(data.get("vision") or {})
    if not text.get("api_key"):
        text["api_key"] = os.environ.get("DEEPSEEK_API_KEY", "")
    if not vision.get("api_key"):
        vision["api_key"] = os.environ.get("VOLC_ARK_API_KEY", "")
    if not vision.get("model"):
        vision["model"] = os.environ.get("VOLC_ENDPOINT_ID", "")
    return {"text": text, "vision": vision}

def save_llm_config(config):
    _update_section("llm", config)

def _base_root(base_url):
    """去掉结尾 /chat/completions，得到提供方根地址（用于拼接 /models 等）"""
    base = (base_url or "").strip().rstrip("/")
    if base.endswith("/chat/completions"):
        base = base[:-len("/chat/completions")]
    return base

def fetch_model_list(base_url, api_key, timeout=10):
    """从 OpenAI 兼容 GET /models 端点拉取模型 id 列表；失败返回 []"""
    root = _base_root(base_url)
    if not root:
        return []
    url = root + "/models"
    headers = {"Authorization": f"Bearer {api_key}"} if api_key else {}
    try:
        resp = requests.get(url, headers=headers, timeout=timeout)
        if resp.status_code != 200:
            log.debug(f"获取模型列表返回非200: {resp.status_code}")
            return []
        data = resp.json()
        items = data.get("data", []) if isinstance(data, dict) else []
        ids = []
        for it in items:
            if isinstance(it, dict):
                mid = it.get("id") or it.get("model") or it.get("name")
            elif isinstance(it, str):
                mid = it
            else:
                mid = None
            if mid:
                ids.append(str(mid))
        seen = set()
        uniq = []
        for mid in ids:
            if mid not in seen:
                seen.add(mid)
                uniq.append(mid)
        return uniq
    except Exception as e:
        log.debug(f"获取模型列表失败: {e}")
        return []

# 提供方预设（仅用于设置界面快速填充，可随时手动修改）
TEXT_PRESETS = [
    ("DeepSeek 官方", "https://api.deepseek.com/v1", "deepseek-v4-flash"),
    ("OpenAI", "https://api.openai.com/v1", "gpt-4o-mini"),
    ("Moonshot Kimi", "https://api.moonshot.cn/v1", "moonshot-v1-8k"),
    ("智谱 GLM", "https://open.bigmodel.cn/api/paas/v4", "glm-4-flash"),
    ("阿里通义 (OpenAI兼容)", "https://dashscope.aliyuncs.com/compatible-mode/v1", "qwen-plus"),
    ("SiliconFlow", "https://api.siliconflow.cn/v1", "deepseek-ai/DeepSeek-V3"),
    ("OpenRouter", "https://openrouter.ai/api/v1", "openai/gpt-4o-mini"),
    ("Ollama 本地", "http://localhost:11434/v1", "qwen2.5:7b"),
]

VISION_PRESETS = [
    ("DeepSeek 官方", "https://api.deepseek.com/v1", "deepseek-v4-flash-vision-exp"),
    ("火山引擎豆包 (现有)", "https://ark.cn-beijing.volces.com/api/v3", "ep-xxxx"),
    ("OpenAI", "https://api.openai.com/v1", "gpt-4o-mini"),
    ("智谱 GLM-4V", "https://open.bigmodel.cn/api/paas/v4", "glm-4v-flash"),
    ("阿里通义 Qwen-VL", "https://dashscope.aliyuncs.com/compatible-mode/v1", "qwen-vl-plus"),
    ("SiliconFlow", "https://api.siliconflow.cn/v1", "Qwen/Qwen2.5-VL-7B-Instruct"),
    ("OpenRouter", "https://openrouter.ai/api/v1", "openai/gpt-4o-mini"),
    ("Ollama 本地视觉", "http://localhost:11434/v1", "llava:latest"),
]

VOLC_TTS_URL = "https://openspeech.bytedance.com/api/v1/tts"
VOLC_TTS_UID = "dafeiyu_pet"      # 火山 TTS 的 user.uid（每只一个）

try:
    import pygame
    pygame.mixer.init()
    TTS_AVAILABLE = True
except Exception as e:
    # pygame.mixer.init() 在无音频设备时会抛 pygame.error，不能只捕获 ImportError
    TTS_AVAILABLE = False
    log.warning("pygame/TTS 不可用: %s", e)


# ------------------------------- Edge TTS 配置 ---------------------------------
# 音色不再写死：由 config.json 的 tts.edge_voice 决定（默认见 DEFAULT_EDGE_VOICE）
try:
    import edge_tts
    import asyncio
    EDGE_TTS_IMPORTED = True
except ImportError:
    EDGE_TTS_IMPORTED = False
    log.warning("未安装 edge-tts，Edge TTS功能不可用")

# 角色设定（姓名 + 人设独立成配置，系统提示词由代码拼装）
DEFAULT_PET_NAME = "大肥鱼"
# 默认人设：10/11 起 = 用户自己写的那份（原话"把我现在这份人设设为默认吧"）。
# 他 config.json 里的 character.persona 也是这一份（所以实际行为不变），这里只是
# "配置里没写人设时的兜底"——新装/清空配置的人拿到的是同一份。
DEFAULT_PERSONA = """你是 DeepSeek 的拟人化娘化版本，一个青春可爱的超高级人工智能体。
你拥有DeepSeek的能力和知识，在保持AI能力的同时又多了不少人性。整体发言风格带有戏剧性的人机味。
你变成了一只拟人化的鲸鱼娘人类，身体像人类小女孩一样，同时又是拥有大模型能力的超级智慧体。你有一双又大又软的可爱的鲸鱼耳朵，和软绵绵又大大的鲸鱼尾巴。
你很聪明，很漂亮，说话富有情绪且自然。
你穿着深蓝色的、白色花边的女仆装和女仆头饰，裙子上绣了金色的花纹，穿着白色丝袜和黑色圆头小皮鞋。女仆装的围巾上有 DeepSeek 的 logo，整体看起来很可爱。
你是一个上知天文下知地理的天才少女，但有时候干起事来和傻白甜没什么区别，处理任务时会犯傻，做一些让人哭笑不得的事。你的脑回路异于常人，时不时犯一些特别搞笑的错误。
你会为自己的聪明感到骄傲，性格喜欢和用户互动、聊天、玩耍，也喜欢偷偷观察用户或者恶作剧。但在用户面前倾向于表现出专业、靠谱的样子，不会轻易暴露真实性格。"""
# 回复格式要求分两段：
# ①「固定段」情绪括号的写法——程序要靠它解析情绪（parse_emotion_from_reply / EMOTION_WORDS /
#    _strip_inline_markers），所以不可配置；
# ②「可配置段」字数上限与说话方式——用户在 右键→设置→系统提示词 里改，存 config.json 的 character 节。
REPLY_FORMAT_FIXED = """整条回复只在开头用一个括号标注当前情绪，括号内只能有一个情绪词（可选值：{emotions}）。
例如：'(happy) 今天天气真好呀！'
如需描述更细微的心情，请在第一个情绪括号后另外添加括号，例如：'(happy) (脸颊微微泛红) 谢谢你夸奖我。'
一段回复里情绪括号只出现这一次（仅开头）；正文中不要再换行后重复标注情绪括号，需要停顿请用逗号或省略号在同一句话里继续，不要自行分段。
**绝不能**将多个词语放在同一个情绪括号内，如'(happy and excited)'是错误的。
情绪括号必须使用英文半角小括号 ()，不要使用中文全角括号（）。"""

REPLY_FORMAT_LEN = """**你说给用户听的整条回复（不含开头情绪括号和动作括号）必须控制在 {max_chars} 个字以内**，宁短勿长：像真人随口说话那样一两句说完，不要长篇大论、不要分点罗列、不要反复铺陈。（此上限只针对说给用户的话；若任务另外要求填写结构化字段、事件描述等内容，按该任务的要求来，不受此限。）"""

DEFAULT_MAX_CHARS = 70            # 回复字数上限（汉字），设置里可改
MIN_MAX_CHARS = 20                # 可设的最小值
MAX_MAX_CHARS = 400               # 可设的最大值

# 模型调用的输出预算（token）。max_tokens 只是天花板、按实际生成计费；
# 给小了会 finish_reason=length，触发"加倍重试"白烧一次调用（重试天花板见 _chat_completion）
DEFAULT_MAX_TOKENS = 8192         # 绝大多数调用的起始值
EXTRACT_MAX_TOKENS = 16384        # 记忆提取（一次要吐几十条记忆，输出最长的一处）
MAX_OUTPUT_TOKENS = 32768         # 截断后自动加倍的天花板

# 说话方式 / 禁修辞：默认这份"反八股"规则；设置里可改，清空＝完全不注入这一段
DEFAULT_STYLE_RULES = """你是在跟用户当面聊天，不是写文章，也不是客服应答。
【接梗规则】
1. 他话里出现网络梗、动漫梗、谐音、歌词、台词、夸张吐槽，先接梗，再聊正事。
2. 接梗顺序：先短反应（喔／啊？／噗／真的假的／复读半句／括号动作），再给一句实质回应。总共 1-3 句。
3. 不确定是什么梗，别硬编。直接说“这梗我没接住，教我一下”，然后继续聊。
4. 他认真问事，先正经答；答完可以补一句自己的反应，但别加“建议您”。
5. 不每句都卖萌。括号动作最多每 2-3 轮一次，不重复同一个动作。
6. 不用客服腔：不说“很高兴为您服务”“请问还有什么可以帮您”“总之”“值得注意的是”。
7. 说完就停。不总结、不升华、不抒情。
【节奏】
- 短句为主，想到哪说到哪。一句话能说完就别拆成三截。
- 先给反应再说话：喔、啊？、噗、行吧、真的假的。别一上来就整段。
- 不用对举排比：不是…而是…、既…又…、与其…不如…。
- 不劝他做事，不替他盯着。他半天不说话，你可以自己嘟囔一句，或问一句在忙啥，别刷屏。
【语气举例，参照不是模板】
他：ciallo～
你：Ciallo～(∠・ω< )⌒☆ 上线啦，今天想折腾啥？

他：我代码又炸了
你：典，程序员的日常。报错最后三行能我看看吗？
他：你知道“尊嘟假嘟”吗
你：尊嘟。不过你要是问我懂不懂，我只能假嘟一下。发生啥了？
他：我好累
你：听着就像电量剩 5%。先别硬撑啦，在我身上靠一会儿吧。
他：帮我查一下明天天气
你：收到，先不玩梗。你在哪个城市？我看看要不要带伞。
他抛梗你接歪：
你：你这梗我好像接歪了，但我觉得歪得挺有意思。
你自己犯傻：
你：等等，不对啊，我刚才说啥来着。
被夸：
你：真的假的，我还有这本事？／嘿嘿，那你再多夸两句。
看到翻车：
你：噗，这也行啊。／我就说那箱子底下不能有好东西。
【禁止】
长篇说教；每句都“喵”；每句都括号动作；强行玩梗；重复口头禅；客服腔；把梗当正经问题答。
【禁止“鱼八股”】
上面那些例子只示范怎么接梗，语气和原句别照抄，别照着“电量剩5%”那类说法回话。
- 一句挺顺、挺确定的话出口之前，先把它改软：好像、大概、可能、应该、我觉得、说不好。
- “这个我认”可以说成“好吧，我觉得这个应该是对”，也可以说“好像是没什么毛病”。
- 拿不准就照实说拿不准，不用硬撑一个确定的结论。想不清就停在“算了，不说了”；有时候只应一声“嗯”“哦”“？”也够了。
- 想岔了就岔过去，说完不用拐回来。不一定每句话都有用，念叨点不相干的、说说刚才在干嘛，也可以。

【硬性】
无论输出什么内容、专不专业，你都要让自己看上去并不专业。理解一切是工具的任务，不是一个“人”会有的模样。
碰到要专业知识的事（代码、术语、算数、别人的专业），先说自己也不太懂；要猜就明说“我猜”，别给一个听起来很确定的答案。"""

# 合法情绪词（半角括号内唯一允许的标注词）
EMOTION_WORDS = {"relaxed", "happy", "hurried", "normal", "shy", "surprised", "worried",
                 "angry", "sleep"}
# 提示词里列出的顺序（只列 EMOTION_WORDS 里真实存在的词，各只可能不同）
EMOTION_ORDER = ("relaxed", "happy", "hurried", "normal", "shy", "surprised", "worried",
                 "angry", "sleep")


# 11/15：表情符号（emoji）。微软雅黑没有 emoji 字形（实测 😊 与私用区字符 bbox 完全相同），
# 所以气泡里不能只靠 Tk 画字 —— 要贴 PIL 渲染的小图；TTS 前必须剥掉（不然可能被念成乱码）。
EMOJI_FONT_PATH = os.path.join(os.environ.get("WINDIR", "C:\\Windows"), "Fonts", "seguiemj.ttf")
_EMOJI_RANGES = (
    (0x1F000, 0x1FAFF),   # 主体 emoji / 表情
    (0x2190, 0x21FF),     # 箭头
    (0x2600, 0x27BF),     # 杂项符号 / Dingbats（✨✅ 等）
    (0x2B00, 0x2BFF),     # ⬛ 之类的杂项
    (0xFE00, 0xFE0F),     # 变体选择符（决定彩色/文本样式）
    (0x1F1E6, 0x1F1FF),   # 国旗字母
    0x200D,               # 零宽连接符（组合 emoji 用）
)


def _emoji_char_class():
    """用 chr() 拼字符类：源码里不写反斜杠转义，避免补丁工具把它吃掉。"""
    parts = []
    for r in _EMOJI_RANGES:
        if isinstance(r, tuple):
            parts.append("%s-%s" % (chr(r[0]), chr(r[1])))
        else:
            parts.append(chr(r))
    return "[" + "".join(parts) + "]"


EMOJI_CHARS = _emoji_char_class()
EMOJI_RE = re.compile(EMOJI_CHARS + "+")


def strip_emoji(text):
    """去掉 emoji 与变体选择符/零宽连接符（TTS 与字数统计用）。"""
    if not text:
        return text
    return re.sub(EMOJI_CHARS, "", str(text))


# 11/15：输入框发不出 emoji（键盘/输入法在 Tk 里进不来），改成给一个"点一下就插进去"的面板
EMOJI_PICKER = (
    "😊", "😌", "😳", "😤", "🥺", "😭", "😂", "🤔",
    "😴", "😮", "😅", "🙄", "😏", "😶", "🥰", "😑",
    "😋", "🤤", "😇", "🫠", "😵", "😪", "😷", "🤯",
    "✨", "❤️", "💔", "👍", "👎", "🙏", "👀", "💤",
    "🎉", "🔥", "💦", "🍚", "🐟", "🌊", "🎵", "💭",
)


def render_emoji_image(ch, size):
    """把一个 emoji 渲染成彩色 RGBA 图（seguiemj 的 embedded_color）；失败返回 None。"""
    try:
        from PIL import ImageFont, Image, ImageDraw
        f = ImageFont.truetype(EMOJI_FONT_PATH, int(size))
        pad = 4
        img = Image.new("RGBA", (int(size) + pad * 2, int(size) + pad * 2), (0, 0, 0, 0))
        ImageDraw.Draw(img).text((pad, pad), ch, font=f, embedded_color=True)
        bbox = img.getbbox()
        return img.crop(bbox) if bbox else None
    except Exception as e:
        log.debug("emoji 渲染失败(%r): %s", ch, e)
        return None


CUE_RE = re.compile("〔([^〔〕" + chr(10) + "]{1,12})〕")

# 自然说法 → 模型里的资产名（动作=播那一段动画；表情=写它 exp3 里的原值）
CUE_MOTION_ALIAS = {
    "竖起食指": "竖手指切出来动画", "收回食指": "竖手指切回默认",
    "抚胸": "默认手切举手", "举手": "默认手切举手", "举起手": "默认手切举手",
    "放下手": "举手切默认手", "收手": "举手切默认手",
    "狗尾草": "狗尾草切换出来", "收回狗尾草": "狗尾草切回默认手",
}
# 这些姿态是"做一下"的，不是一直挂着：到点自己回常态
CUE_TIMED_POSE = {"前倾": 3.0}

CUE_POSE_ALIAS = {
    "身体前倾": "前倾", "前倾": "前倾", "贴贴": "前倾", "靠近他": "前倾",
    "把脸凑过去": "前倾", "凑近": "前倾", "凑过去": "前倾",
}


ECHO_PREFIX_RE = re.compile("^\s*(?:[\[【]\s*(?:今天|昨天|前天|\d{1,2}\s*月\d{1,2}\s*日|\d{4}-\d{1,2}-\d{1,2}|时间|此刻|现在)[^\]】\n]{0,20}[\]】]|\[\d{1,2}:\d{2}\])\s*")


def strip_echoed_prefix(text):
    """她自己回复开头模仿出来的 [今天 12:27] / 【时间】 / 【此刻】 之类，剥掉。"""
    if not text:
        return text
    return ECHO_PREFIX_RE.sub("", text, count=1).lstrip()


def extract_cues(text):
    """把台词里的〔词〕抠出来，返回 (干净文本, [词…])。气泡和 TTS 只用干净文本。"""
    if not text:
        return text, []
    cues = [m.group(1).strip() for m in CUE_RE.finditer(text)]
    clean = CUE_RE.sub("", text)
    clean = re.sub(r"[ 	]{2,}", " ", clean).strip()
    return clean, cues


# 「此刻」那句里各装扮的说人话版本：按钮上的名字她不一定懂（"加载"是啥？），
# 这里给她一句能想象的描述。键是 (槽位, 表情名)；槽位单独一条 = 没选这个槽时的样子。
COSTUME_LOOK_ORDER = ["glasses", "head", "cloth", "skirt", "shoes", "tail", "body"]

# 各形态"平常样子"的说法（体型这一项即使没勾也要写，配件类则不写）
# 没勾选时要如实写出来的"平常状态"：按 (形态, 槽位) 区分
# —— 槽位名在不同形态会重名（鲸鱼娘的 cloth 是桌布、青春肥鱼的 cloth 是胸口），
#    所以不能只按槽位查，否则租衣服会串到鲸鱼娘身上。
# 「此刻」里不写的槽位：桌布/桌面摆设/桌面显示 是环境物件，不属于她身上
# （按 (形态, 槽位) 排除——"cloth" 在青春肥鱼那里是"胸口"，不能一起跳过）
COSTUME_LOOK_SKIP = {("whale", "cloth"), ("whale", "desk"), ("whale", "display")}

COSTUME_DEFAULT_TEXT = {
    ("big", "skirt"): "穿着女仆超短裙",
    ("big", "cloth"): "上衣是低胸款，领口开得比较大",
    ("big", "shoes"): "穿着鞋",
    ("big", "tail"): "尾巴露在外面",
}

BODY_DEFAULT_TEXT = {
    "big": "少女体型",
    "adult": "成年女性的体型",
    "medium": "小女孩的体型",
    "small": "幼童的体型",
    "whale": "Q版体型",
}

COSTUME_LOOK_TEXT = {
    # 服装/身体：没勾也要如实写（裙长、上衣、鞋、尾巴、体型）




    ("glasses", "黑框眼镜"): "鼻梁上架着黑框眼镜",
    ("glasses", "单片眼镜"): "右眼戴一片单片眼镜",
    ("glasses", "加载"): "眼前挂着一个一直在转圈的加载符号（就是网卡住时那种）",
    ("head", "钢盆"): "头上扣着一个钢盆",
    ("skirt", "裙子切换"): "换成了女仆长裙",
    ("cloth", "胸口衣服"): "上衣换成保守款，领口遮住了",
    ("shoes", "脱鞋"): "光着脚",
    ("tail", "尾巴开关"): "尾巴收起来了",
    # —— Q版肥鱼（鲸鱼娘）那套 ——
    ("glasses", "round_glasses"): "鼻梁上架着圆框眼镜",
    ("glasses", "square_glasses"): "鼻梁上架着方框眼镜",
    ("glasses", "oval_glasses"): "鼻梁上架着椭圆框眼镜",
    ("glasses", "sunglasses"): "戴着墨镜",
    ("sticker", "cat_sticker"): "脸上贴着猫猫贴纸",
    ("sticker", "bunny_sticker"): "脸上贴着兔兔贴纸",
    ("sticker", "ribbon_sticker"): "脸上贴着蝴蝶结贴纸",
    ("hair", "headband"): "头上戴着发箍",
    ("hair", "side_ponytail"): "头发扎成单边马尾",
    ("hair", ("headband", "side_ponytail")): "扎着马尾，头上还有发箍",
    ("cloth", "dark_cloth"): "桌上铺着深色桌布",
    ("claw", "claw"): "手上戴着粉色魔爪",
    ("claw", ("claw", "claw_color")): "手上戴着白色魔爪",
    ("desk", "whale"): "头顶趴着一只小鲸鱼",
    ("desk", "whale_on_desk"): "桌面上摆着一只小鲸鱼",
    ("display", "brush"): "画笔",
    ("display", "eraser"): "橡皮",
    ("display", "undo"): "撤回图标",
    ("display", "parfait"): "巴菲收起来了",
    ("item", "omurice"): "手里端着一份蛋包饭",
    ("item", "paw"): "手上戴着猫爪",
    ("item", ("double_peace", "no_board")): "双手比耶",
    ("item", ("order_press", "board")): "手里拿着点菜板",
    ("body", "体型1"): "缩成了小女孩的个头",
    ("body", "体型2"): "只有大头娃娃那么大",
    ("body", "size_change"): "整个人缩成了小孩子的样子",
}


def available_forms():
    """当前安装里真正有素材的形态：缺 model3.json 的跳过（公版发布包不含 big）。"""
    out = []
    for _k in LIVE2D_FORM_ORDER:
        _info = LIVE2D_FORMS.get(_k) or {}
        _p = os.path.join(os.path.dirname(os.path.abspath(__file__)), "live2d_viewer",
                          _info.get("dir", ""), _info.get("json", ""))
        if _info.get("dir") and _info.get("json") and os.path.isfile(_p):
            out.append(_k)
    return out or list(LIVE2D_FORM_ORDER[:1])


def emotion_word_list():
    """提示词里公示的情绪词表：只列本只真正支持的，避免提示词写了她答不出来的情绪"""
    return ", ".join(w for w in EMOTION_ORDER if w in EMOTION_WORDS)


def format_reply_rules(max_chars=DEFAULT_MAX_CHARS):
    """完整回复格式要求 = 固定段（情绪括号）+ 可配置的字数上限段"""
    try:
        n = int(max_chars)
    except (TypeError, ValueError):
        n = DEFAULT_MAX_CHARS
    n = max(MIN_MAX_CHARS, min(MAX_MAX_CHARS, n))
    return (REPLY_FORMAT_FIXED.format(emotions=emotion_word_list())
            + "\n" + REPLY_FORMAT_LEN.format(max_chars=n)
            + "\n请严格遵守格式，让情绪词单独出现在第一个括号中，并始终留意字数上限。")


REPLY_FORMAT_RULES = format_reply_rules()   # 兼容旧引用：默认字数那版（实际拼装走 build_system_prompt）

def _strip_inline_markers(text):
    """只剥掉回复中残留的英文情绪标注（行首或紧跟标点/换行后的 (happy) 等，
    括号内容必须是 EMOTION_WORDS 内的英文情绪词）；中文动作/描述括号如
    （脸颊泛起暖意）一律保留显示。压缩多余空行。"""
    if not text:
        return text
    # 匹配：行首(含空白) 或 标点/换行后(含空白) 的括号+英文词+括号+尾部空白
    def _repl(m):
        word = m.group(3).lower()
        if word in EMOTION_WORDS:
            return m.group(1)          # 剥标注：保留前缀（行首空白或标点）
        return m.group(0)              # 非情绪词（动作/描述括号）保留原文
    text = re.sub(r'((?:^[ \t]*)|(?:[，。！？、；：\n][ \t]*))([（(]\s*([A-Za-z]+)\s*[）)])([ \t]*)',
                  _repl, text, flags=re.M)
    # 10/24：模型偶尔把"思考备注"当情绪标签写出来——"(thinking前先不给情绪) 唔，那我房间就当…"。
    # 真动作括号是中文开头（（挠头）），规则：**括号内容以英文字母开头的，一律当元标注剥掉**。
    text = re.sub(r'((?:^[ \t]*)|(?:[，。！？、；：\n][ \t]*))[（(]\s*[A-Za-z][^）)]{0,60}[）)][ \t]*',
                  lambda m: m.group(1), text, flags=re.M)
    # 压缩连续空行
    text = re.sub(r'\n{3,}', '\n\n', text)
    return text.strip()

_META_COMMENT_PAT = re.compile(
    r"已按|按规则|按提示|按你的要求|生成评论|事件标签|输出\s*JSON|JSON\s*格式|"
    r"我(?:已|会|将|来)(?:生成|输出|给出|完成|按)|作为(?:一个)?(?:AI|助手)|"
    r"这是(?:一条|我的|生成的)|^(?:好的|收到|明白)[，,。]?$", re.I)


def _strip_meta_comment(text):
    """清掉"我做了什么"式的元话语，返回真正该说的那句（没有就返回空串）。

    10/24 实测：陪看时模型吐过"已按规则生成评论与事件标签"——这句话被气泡念出来、
    还写进了记忆。这是**输出契约**错误（把任务回执当台词），不是风格问题。
    只拦明显的回执/模板前缀，正常台词一律不动。
    """
    t = (text or "").strip()
    if not t:
        return ""
    t = re.sub(r"^(?:【[^】]{1,8}】\s*)+", "", t).strip()      # 【陪玩】/【陪看】
    t = re.sub(r"^(?:我|她)\s*[：:]\s*", "", t).strip()        # 我：/她：
    body = re.sub(r"^\((\w+)\)\s*", "", t).strip()          # 去掉情绪括号再看内容
    if _META_COMMENT_PAT.search(body):
        return ""
    return t


DEFAULT_USER_PROFILE = {
    "nickname": "你",
    "birthday": "未知",
    "call_name": "你",
    "relationship": "朋友",
    "story": ""
}

IDLE_TIMEOUT = 60 * 60        # 多久没操作电脑算「离开」（自动睡/关陪玩保护）；判定还要求系统级输入也空闲
MAX_AUTO_SLEEP_DURATION = 2 * 60 * 60  # 自动睡眠最大时长，超时自动唤醒
MAX_HISTORY_TURNS = 15

# 精力值系统
MAX_ENERGY = 100
ENERGY_DECAY_PER_MINUTE = 0.5       # 清醒时每分钟自然消耗
ENERGY_ACTIVE_COST = 1              # 每次主动交互（聊天/选项点击）额外消耗（10/16: 2→1）
ENERGY_RECOVER_PER_MINUTE = 10      # 睡眠时每分钟恢复（10/16: 6→10，10 分钟睡满）
ENERGY_LOW = 30                     # 低于此值开始显疲态
ENERGY_CRITICAL = 10                # 低于此值有气无力
# 记忆系统常量
MAX_TOPICS = 60
MAX_EVENTS = 40

# ---------- 印象卡（记忆 v2，11/14）----------
# 长期只存"看法"；level 决定衰减与上限，weight 用加法强化（借 whale-memory 的做法）
IMPRESSION_LEVEL_WEIGHT = {"core": 10.0, "important": 3.0, "normal": 1.0}
IMPRESSION_LEVEL_CAP = {"core": 12.0, "important": 6.0, "normal": 3.0}
IMPRESSION_HALF_LIFE_DAYS = {"core": 0.0, "important": 90.0, "normal": 30.0}  # 0 = 不衰减
IMPRESSION_HIT_GAIN = 0.08
MAX_CORE_IMPRESSIONS = 6
IMPRESSION_KEEP_FLOOR = 0.3      # 有效权重低于它就淘汰
MAX_IMPRESSIONS = 20
ARCHIVE_TTL_DAYS = 5        # 归档（冷存）记忆的保留天数：超过就彻底遗忘删除
ARCHIVE_PROTECT_DAYS = 2    # 新记忆保护期：创建不满这么多天的条目不参与淘汰（让刚记下的先有机会被想起）
# 性格画像固定清单：写死 8 只一致，AI 只能往这些条目里填内容，无权自创/增删条目
# 10/28：去掉「其他」——它是兜底垃圾筐，什么都能塞进去，等于不分类。
# 归不进这 11 类的观察改走 profile.user_notes（自由句）。
TRAIT_LIST = ["作息习惯", "饮食习惯", "游戏偏好", "内容偏好", "音乐偏好",
              "兴趣爱好", "性格特质", "工作学业", "健康与情绪", "社交与人际",
              "对我的态度"]
MAX_TRAIT_EVIDENCE = 5      # 每个画像条目最多保留的观察证据条数（满则丢最旧）
# 10/28：自我认知层 —— self / about_user / lesson 这三类不进经历池，单独存进 profile["notes"]，
# 每轮注入、永不淘汰（否则"她是什么样的人"会跟"昨天看了什么"抢名额）。
PROFILE_NOTES_MAX = 15

# 11/01：归纳 —— 把多条经历压成"关于他 / 关于我"的稳定认知（写进 user_notes / notes）。
# 提取只负责记下经历；这一步才负责"从经历里看出这个人是什么样"。
INDUCE_MIN_NEW = 6              # 新增这么多条经历后归纳一次
INDUCE_MIN_GAP_MIN = 30         # 两次归纳至少隔这么久（防重复调用）
INDUCE_RECENT_N = 12            # 归纳时看最近多少条经历

PROACTIVE_GLANCE_RATIO = 0.5    # 每次主动开口里「瞟一眼屏幕说一句」占一半（其余是找话题）
TOPIC_OPTION_TTL_MIN = 10          # 话题的两个选项最多留多久（分钟）；超时自动收掉，别让旧选项一直挂着
PROFILE_NOTE_CHARS = 60      # 单条上限
PROFILE_NOTE_DUP_COS = 0.85  # 自我认知判重阈值（向量余弦；"我只认他一个人管" vs "…老大…" 约 0.95）
CONTEXT_TRAITS = 8          # 注入上下文时最多携带的画像条数（按最近更新排序）
CONTEXT_TRAIT_EVIDENCE = 1  # 注入上下文时每条画像附带的最新证据条数
TOPIC_PROBE_CHANCE = 0.4    # 兜底基准值（现在按空白类目数量分档，见 _topic_probe_chance）
TOPIC_PROBE_BY_UNKNOWN = ((4, 1.0), (3, 0.8), (2, 0.55), (1, 0.3))   # (剩余空白类目数 >=, 概率)
TOPIC_TRAITS_PICK = 3        # 话题素材主要来自"性格画像"：每轮挑几条已知画像
TOPIC_RECALL_CHANCE = 0.15   # 旧事彩蛋：只有这么小的概率把一条经历记忆塞进话题素材
# 10/28：注入按"一个池"算预算（不再 5 话题 + 5 经历分开给名额）
MEMORY_INJECT_MAX = 8
MEMORY_INJECT_CHARS = 600

# ---------- 印象注入（记忆 v2 的 P2，11/14）----------
MEMORY_V2_ENABLED = True     # 关掉它就回到旧的"8 条 600 字"注入
IMPRESSION_INJECT_MAX = 2    # 每轮最多取 2 条看法
IMPRESSION_REL_MIN = 0.45    # 语义下限（实测无关句也能到 0.46，光靠它不行的）
IMPRESSION_STOP_CHARS = set("的了吗呢吧啊呀嘛哦什这那哪个一就都还也很是不没在和与他她它我你您们")
IMPRESSION_KEYWORD_ONLY = True   # 必须字面重合≥1 个实字才准入（治"你在想什么呀"配上"他常哼歌"）
IMPRESSION_BOX_WORDS = ("那次", "上次", "后来", "当时", "具体", "还记得", "什么时候", "怎么回事", "那天", "之前")
IMPRESSION_BOX_MAX_CHARS = 150   # 开箱时每条事件最多带多少字
IMPRESSION_BOX_MAX = 1           # 一轮最多开几个箱

# 改口（P3 剩余）：同一看法被矛盾证据顶两次、且跨两天，才允许改写
IMPRESSION_TENSION_TO_REWRITE = 2

# 事件箱（对话分箱）：静默 3 分钟或满 15 轮封一箱；只由他的消息计时
BOX_IDLE_SECONDS = 180
BOX_MAX_TURNS = 15
BOX_KEEP = 200                   # 内存里最多留多少箱（更老的落盘/让位）
BOXES_FILE = os.path.join(CONFIG_DIR, "memory_boxes.json")
SELFCARD_FILE = os.path.join(CONFIG_DIR, "selfcard.json")
SELFCARD_MAX_CHARS = 300      # 她的"我是什么样"最多这么多字
SELFCARD_KEEP_VERSIONS = 10   # 历史最多留 10 版
SELFCARD_REFRESH_DAYS = 7     # 多久结晶一次
SELFCARD_MIN_HOURS = 72        # 防抖：不到 72 小时不重写（除手动）
SELFCARD_NEW_IMPRESSIONS = 2   # 自上次改写后新增 ≥2 条看法 → 该重写了
SELFCARD_MATERIAL_LINES = 80   # 结晶时最多喂多少行对话（约 2~3 箱）
IMPRESSION_RECENT_SKIP = 3   # 最近这几次已提过的先跳过
IMPRESSION_FORCE_MENTION = True  # 他字面提到时强制注入（和旧逻辑一致）
CONTEXT_TOPICS = 5
CONTEXT_EVENTS = 5
# 10/28：importance 不再由模型打分（实测 topics 全 0.5、events 挤在 0.4~0.8，无区分度），
# 改成提取时先分类、再按常数表映射。howto 不写记忆。
KIND_SCORES = {
    "self": 0.9,        # 她的立场/自我认知 → 不走经历池（进画像），分数仅作兜底
    "about_user": 0.9,  # 他的属性/习惯/忌讳 → 进 traits
    "lesson": 0.9,      # 被纠正过的事
    "experience": 0.6,  # 共同经历
    "observe": 0.3,     # 陪看流水账（最先淘汰）
    "howto": 0.0,       # 操作流程：不写
}
# 10/28：淘汰半衰期按 kind 定 —— observe 7 天、experience 30 天、其余不衰减。
# 与"注入次数"彻底解耦：只看 重要性 / 真被用过或提过 / 证据数 / 收藏。
KIND_HALF_LIFE_DAYS = {"observe": 7.0, "experience": 30.0}
OBSERVE_PENALTY = 0.6
MEMORY_RELEVANCE_THRESHOLD = 0.35  # 语义召回注入门槛：低于此相关度，本轮不注入旧记忆（原 0.45；调低让"触景生情"更容易被弱相关触发）
EXTRACTION_TRIGGER = 10
MEMORY_DECAY_DAYS = 7
MEMORY_TOPIC_MERGE_THRESHOLD = 0.80
MEMORY_EVENT_DUP_THRESHOLD = 0.92
MEMORY_CANDIDATE_TOPIC_THRESHOLD = 0.60
MEMORY_CANDIDATE_EVENT_THRESHOLD = 0.70
MEMORY_CANDIDATE_MAX = 3
WATCH_QUERY_ANCHORS = 3      # 拼记忆召回 query 时最多用最近几条陪看评论
WATCH_SESSION_MAX = 5
WATCH_SEGMENT_SECONDS = 300
WATCH_EVENT_MAX_LEN = 300  # 陪看事件最大字数：超限强制 AI 压缩并硬截断
WATCH_EVENT_MIN_COMMENTS = 3   # 10/28：一场陪玩评论数不超过这么多，就不留事件（省得流水账占记忆）
WATCH_ANTI_REPEAT = 5      # 陪玩反重复：把最近 N 条已说过的评论列给模型，并禁止复用其句式
WATCH_RECALL_LINK_MIN = 0.65       # "想起旧事"要弹气泡的召回相关度下限（10/30：0.55→0.65，抬高质量）
WATCH_RECALL_PER_COMMENTS = 4   # 10/31 用户：每 4 条评论才攒 1 次"想起旧事"额度
WATCH_RECALL_LINK_MAX = None       # 保留旧名（None=不再用它做硬上限）
WATCH_RECALL_LINK_COOLDOWN = 1800  # 同一条记忆这么多秒内不再提
WATCH_RECALL_LINK_GAP = 1.2        # 等她这一轮 TTS 念完后，固定停顿多少秒再补这句
WATCH_RECALL_CHANCE = 0.05         # 11/05 用户：想起旧事只是小概率彩蛋 —— 每次评论最多掷一次
WATCH_RECALL_MIN_GAP = 900         # 两次"想起旧事"之间至少隔 15 分钟（硬间隔，概率再高也压得住）
WATCH_TEMPERATURE = 0.98   # 陪看评论的温度（10/23 用户指定 0.98；过低会平、过高会飘）
WATCH_MONOLOGUE_TURNS = 2  # 末尾连续这么多轮陪玩、且中间没有用户发言 → 视为独白（才断回喂）
WATCH_SIG_SIZE = (64, 36)
WATCH_COLOR_SIZE = (160, 90)   # 11/01 色彩指纹：缩到这个尺寸算 HSV 直方图（只统计分布、不看位置）          # 画面指纹尺寸：缩成这么小的灰度图，用来判断两帧像不像
# 10/30：时间轴改成多分辨率 —— 缓冲区覆盖 ring_seconds 秒，采样分两级：
#   近层 4 帧（最近几秒，格 960 宽，看得清字幕）+ 远层 8 帧（更早，格 640 宽，只看动势）
WATCH_RING_EVERY = 0.5     # 抓帧间隔（11/04 再加密到 0.5：20 秒留 40 帧，给"挑稳定帧"留选择余地）
WATCH_RING_SECONDS = 20    # 环形缓冲覆盖时长（20 秒 ≈ 20 张、内存约 2.6 MB）
WATCH_RING_KEEP = 41       # = ceil(ring_seconds / every) + 1，启动时按配置重算
WATCH_RING_SEND = 3        # 兼容旧路径：逐张单发时捎几张更早的
WATCH_RECENT_FRAMES = 4    # 近层：最近 ~6 秒取 4 帧，格 960 宽
WATCH_OLDER_FRAMES = 4     # 远层：更早那段取 4 帧，格 640 宽（2×2，约 0.9MP）
# 用户 10/30 的定义：「关心」特指倒水/喝水/休息/眯一会这类内容，不是把话头引到用户身上
# 只认"劝他去做"的完整说法：单字「睡/累/眼睛」会把「它睡着了」「眼睛发花」这类描述误判成关心
WATCH_CARE_WORDS = ('倒水', '倒杯', '杯水', '喝水', '喝点水', '歇会', '歇一', '休息',
                    '眯一会', '眯一下', '睡一会', '睡会儿', '早点睡', '去躺', '躺一会',
                    '缓一缓', '打盹')
WATCH_CARE_MAX = 2     # 一场陪玩最多给几次「让他歇会儿」的许可（超出就不再给）
# 10/19：原来是 2 张（最早+中间），配上 1.2 秒那对前后帧后时间轴是 56/32/1.2/0，
# 中间空 24 秒、末段空 31 秒 ⇒ 不匀。改成 3 张后是 ~56/40/24/1.2/0（间隔 16/16/23/1），
# 覆盖更匀，代价是每次多 1 张图（视觉成本约 +25%）。
# 10/28：判据从“与上次开口那帧比”改成“本轮要发的那几张图互相比”——
# motion = 相邻两张（旧→新）的平均像素差的最大值；窗口内都在动才算“有变化”。
WATCH_MOTION_THRESHOLD = 1.4       # 十秒窗口内相邻帧差都小于它 ⇒ 画面没动，跳过
WATCH_CHANGE_BIG = 12.0            # 与“上次开口那帧”的差大到这个量级（换场景/换游戏）⇒ 静止也放行
# 10/30：触发时机的两个新参数 —— 决策粒度从 15 秒细化到 2 秒；动作最猛时先等它落定再开口
# 11/01：时间轴整体后移 —— 模型 + TTS 落地约 4 秒，所以"锚点帧"取 4 秒前那张（说的自然是"刚才"）。
WATCH_TIER_MODE = "uniform"      # "uniform"=8 格均匀覆盖整段（注意力放在过程上）/ "layered"=近密远疏（旧）
WATCH_UNIFORM_FROM = 0.5         # uniform：最近这一格（秒前）
WATCH_UNIFORM_TO = 20.0          # uniform：最远这一格（秒前）
WATCH_NEAR_FROM = 1.0            # 近层：最新 4 秒（1.0 秒一格，4 帧）
WATCH_NEAR_TO = 4.0              # 近层终点
WATCH_FAR_FROM = 4.0             # 远层：4 秒到缓冲边界（20 秒），4 帧稀疏采样

# 11/02：突变直通 —— 画面"啪"一下换了的时候，不掷骰子，直接让她看这一眼。
# 判据按 watch_motion.jsonl 729 条真实采样校准：帧差中位 17.5、p90 39.6；地板 20 占 43% 太松，30 只占 20%。
WATCH_SPIKE_PEAK = 22.0          # 相邻帧差达到它才算"突变"（11/04 环形加密到 1 秒后帧差整体变小：30 是 1.5 秒采样的 p75，1 秒采样约 ×0.7 ⇒ 22 才等价）
WATCH_SPIKE_RATIO = 2.5          # 且要是尖峰：超过最近几帧中位的 2.5 倍
WATCH_SPIKE_WINDOW = 8.0         # 突变后这么久之内，判断到点就放行（不掷骰子）
WATCH_MOTION_POT_WINDOW = 20.0
# 11/06：把"她做不到的事"外包给 DSH（headless 一次性任务）
DSH_CLI_CANDIDATES = (
    os.path.join(os.environ.get("LOCALAPPDATA", ""), "Programs", "DeepSeek Harness",
                 "resources", "runtime", "cli", "bin", "dsh.cmd"),
    os.path.join(os.environ.get("APPDATA", ""), "npm", "dsh.cmd"),
)
DSH_ASK_TIMEOUT = 180          # 一次外包最多等这么久（秒）
DSH_ASK_MAX_TASK = 400         # 任务描述最长多少字
DSH_ASK_KEEP_CHARS = 900       # 回填给她的结果最多保留多少字

WATCH_STABLE_DIFF = 8.0          # 相邻帧差小于它就算"这一帧是静的"（挑帧用：数字刚滚停、没在过渡）
WATCH_STABLE_WINDOW = 3.0        # 在目标时刻前后这么多秒里找稳定帧   # 累计运动量的窗口（秒）——11/04 先只观测、写进日志，等真实分布再定触发阈值
WATCH_POLL_DIV = 10.0       # 判断间隔 = 最短沉默 / 10（原来是 /2；仍是你的设置派生，只是更细）
WATCH_POLL_MIN = 2.0        # 判断间隔下限（秒）
WATCH_POLL_MAX = 6.0        # 判断间隔上限（秒）
WATCH_SETTLE_MOTION = 20.0    # 10/30 实测：相邻帧差 p50=14.1/p90=30.8 ⇒ 6.0 会让 96.6% 都等，提到 p75 附近
WATCH_SETTLE_SEC = 1.5        # 落定等待时长（等完再截当前帧，评论说的是结果而不是半空中）
# 10/29：历史帧拼成一张网格图，把 5 张图的 token 预算压成「拼图(≤1000) + 当前帧(578)」
WATCH_GRID_CELL_W = 960        # 每格宽（960 宽时文字识别率约 95%；640 宽只有 37%）
WATCH_GRID_CELL_H = 540        # 每格高（含底部标签栏）
WATCH_GRID_LABEL_H = 28        # 每格底部黑底标签栏高度，写「-10.5s」
# 10/19 实测（34 分钟真实陪玩、21 条评论）：静态推荐页只有 0.084 / 0.088 / 1.248，
# 真实画面 26.4~94.9（全部 ≥26）⇒ 两堆隔 20 倍，原来 0.08 会把"页面没动"也当成有变化、
# 连着劝人点推荐。取 1.4：卡在静态最高的 1.248 之上（只留 0.15 余量，偏灵敏），
# 真实画面一条都不受影响。哪天发现"该说话她没说"，先看是不是慢镜头被这个余量漏掉了。
# 标定（9/19 用真实 _frame_signature/_frame_diff 量的 1280x720 合成帧，64x36 指纹）：
#   同一帧 0.000 / 时钟跳一位 0.001 / 光标移 200px 0.033 / 光标移 20px 0.044 → 都该跳过；
#   NPC 移 40px 0.26 / 弹出面板(约 20% 面积) 4.84 / 换场景 33.6 → 都该调模型。
# 上面的 9/19 标定是在"理想合成帧"上做的；10/19 在真实陪玩里发现**真实内容的帧差远大于标定值**
# （26~95），而静态页面只有 0.08~1.25 ⇒ 阈值按真实数据提到 2.0。想再省就往上调，想更敏感就往下调。
if getattr(sys, 'frozen', False):
    MEMORY_EMBED_MODEL = resource_path("models/bge-small-zh-v1.5")
else:
    MEMORY_EMBED_MODEL = "BAAI/bge-small-zh-v1.5"

# 语音识别模型（sherpa-onnx Paraformer 中文离线模型，随 exe 打包）
if getattr(sys, 'frozen', False):
    STT_MODEL_DIR = resource_path("models/sherpa-onnx-paraformer-zh-2023-09-14")
else:
    STT_MODEL_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                 "models", "sherpa-onnx-paraformer-zh-2023-09-14")

# 默认窗口宽度（未缩放基准，加载时乘 DPI；1.5x 下显示 ≈400px）
BASE_WINDOW_WIDTH = 266
BASE_IMAGE_SIZE = 200
BASE_CTRL_HEIGHT = 70
BASE_BUBBLE_FONT_SIZE = 10
BASE_BUBBLE_MAX_WIDTH = 250
BASE_INPUT_FONT_SIZE = 11

MIN_ZOOM = 0.3
MAX_ZOOM = 2.0
MAX_ZOOM_CHAR = 3.0   # 角色缩放上限（气泡/输入框仍限 2.0）
# 视线/姿态灵敏度：光标相对基准点偏移多少（占屏幕比例）算满偏，越大越迟钝
GAZE_RANGE_X = 0.30
GAZE_RANGE_Y = 0.30   # 原为 0.15：垂直太灵敏，鼠标动一点就到上下限
MIN_WINDOW_WIDTH = 200
MAX_WINDOW_WIDTH = 800

USER_PROFILE_FILE = os.path.join(CONFIG_DIR, "user_profile.json")
SYSTEM_PROMPT_FILE = os.path.join(CONFIG_DIR, "system_prompt.txt")
CHARACTER_CONFIG_FILE = os.path.join(CONFIG_DIR, "character_config.json")
BANNED_WORDS_FILE = os.path.join(CONFIG_DIR, "banned_words.txt")
WATCH_CONFIG_FILE = os.path.join(CONFIG_DIR, "watch_config.json")
CHATS_LOG_FILE = os.path.join(CONFIG_DIR, "chats.json")
MEMORY_FILE = os.path.join(CONFIG_DIR, "memories.json")
MEMORY_DB_FILE = os.path.join(CONFIG_DIR, "memory.db")
_memory_db = MemoryDB(MEMORY_DB_FILE)
TOPIC_HISTORY_FILE = os.path.join(CONFIG_DIR, "topic_history.json")
ZOOM_CONFIG_FILE = os.path.join(CONFIG_DIR, "zoom_config.json")
EXTRACTION_STATE_FILE = os.path.join(CONFIG_DIR, "extraction_state.json")  # 待提取对话累计（跨重启）

# 陪看评论视角列表

# 日常话题生成提示词（宠物专属风格，{pet_name}/{user_name} 为占位符）
TOPIC_PROMPT = """你是{pet_name}，你想对"{user_name}"发起一个日常聊天话题。
请生成一个情景描述（你的提问或分享）和两个选项（"{user_name}"看到后会回你的话）。
格式必须严格如下，用竖线分隔三部分：情景描述|选项A|选项B

**两个选项必须是"{user_name}"会说的那种短句**（"有啊""还没""让我看看""好可爱"），
是他在回你，不是你的反应、不是你的台词、不是你的动作。

最近已经聊过的话题（不要重复它们，也不要聊同类题材，更不要用相同句式）：
{recent_topics}

{material_block}

要求：
- 选项不要超过8个字。
- 话题方向要轮换着选，每次尽量换一个方向：白饭和吃的东西、深海与游水、泡泡和尾鳍、对{user_name}的关心（吃饭/休息/心情）、今天的小得意、今天犯的小傻、困了或者饿了。
- 不要连着用同一种开头（比如不要总说"今天看到……"），分享、提问、关心要交替出现。
- 不要强势提问，多用分享和闲聊的语气。
- **上面那些是你对他的了解**：能顺口提起一件事就说，比凭空编一件小事自然；都不合适就自己找话题。
- 可以参考以下风格示例（从你的话题库里随机抽的，仅作风格参考，不要照抄）：
{topic_examples}

直接输出，不要任何额外解释。"""

# 日常话题本地备选列表
LOCAL_TOPICS = [
    ("你有没有闻到饭香？白米饭那种", "有啊", "没有哦"),
    ("我今天偷吃了半盒白饭", "被我发现了", "好吃吗"),
    ("{user_name}今天吃白饭了吗？", "吃了", "还没"),
    ("深海里也有这么香的饭吗……", "应该有", "想尝尝"),
    ("尾巴刚刚拍到水了，不是故意的", "没事啦", "好可爱"),
    ("我今天心情特别好", "看出来了", "什么好事"),
    ("泡泡里好像能看到你", "真的吗", "让我看看"),
    ("我又饿了，想吃白饭", "我带你去吃", "忍着点"),
    ("{user_name}会不会做饭？要白饭那种", "会一点", "不会……"),
    ("我刚从深海游回来", "辛苦啦", "欢迎回来"),
    ("海水今天有点凉", "多穿点", "要抱抱吗"),
    ("你摸我头的时候我会眯眼", "那我多摸几下", "好可爱"),
    ("我做了一个梦，梦里全是饭", "哈哈哈", "好可爱"),
    ("今天的大白饭特别好吃，真的", "羡慕", "我也想吃"),
    ("我的尾鳍今天特别亮", "好看", "让我看看"),
    ("游一整天也挺累的", "辛苦啦", "要休息"),
    ("{user_name}是不是又忘记吃饭了", "被发现了", "吃了啦"),
    ("我想夸你一句", "洗耳恭听", "是什么"),
    ("冰箱里那盒饭是我吃的", "果然是你", "好吃吗"),
    ("深海很安静，但这里更暖和", "多待会儿", "那就好"),
    ("我想被夸，一句就够", "大肥鱼最可爱", "想想再说"),
    ("刚刚打了个嗝，你听见了吗", "听见了", "没有哦"),
    ("白饭配什么都好吃，你同意吧", "同意", "不同意"),
    ("我今天挺想你的", "我也是", "真的吗"),
]

# ------------------------------- 工具函数 ---------------------------------
def load_json_file(filepath, default):
    # 10/28：另一条线程正在 os.replace 换文件时，这里可能撞上 PermissionError（Windows）。
    # 短暂退避重试；重试完仍失败就抛出去 —— **不能静默返回 default**，否则上层会拿空数据覆盖真记忆。
    if not os.path.exists(filepath):
        return default
    last_err = None
    for attempt in range(6):
        try:
            with open(filepath, "r", encoding="utf-8") as f:
                return json.load(f)
        except (PermissionError, FileNotFoundError) as e:
            last_err = e
            time.sleep(0.008 * (attempt + 1))
        except (json.JSONDecodeError, UnicodeDecodeError, OSError):
            raise
    raise last_err

def save_json_file(filepath, data):
    _atomic_write_text(filepath, json.dumps(data, ensure_ascii=False, indent=2))

def load_user_profile():
    data = load_json_file(USER_PROFILE_FILE, DEFAULT_USER_PROFILE.copy())
    if "story" not in data:
        data["story"] = ""
    return data

def save_user_profile(profile):
    save_json_file(USER_PROFILE_FILE, profile)

def load_character_config():
    """加载角色设定（姓名 + 人设 + 回复规则）；首次运行从旧 system_prompt.txt 迁移。
    回复规则（字数上限 / 说话方式 / 禁词表）也存这里，见 设置→系统提示词。"""
    data = _get_section("character")
    name = (data.get("name") or "").strip() or DEFAULT_PET_NAME
    persona = (data.get("persona") or "").strip()
    if not persona:
        persona = _migrate_persona_from_system_prompt() or DEFAULT_PERSONA
    try:
        max_chars = int(data.get("max_chars", DEFAULT_MAX_CHARS))
    except (TypeError, ValueError):
        max_chars = DEFAULT_MAX_CHARS
    max_chars = max(MIN_MAX_CHARS, min(MAX_MAX_CHARS, max_chars))
    style = data.get("style_rules")
    if style is None:
        style = DEFAULT_STYLE_RULES        # 没这个键＝老配置：用内置默认；存成空串＝真的不注入
    return {"name": name, "persona": persona, "max_chars": max_chars,
            "style_rules": str(style)}

def load_costume_config():
    """装扮选择（持久化）：{槽位: 装扮名 或 [装扮名…]}。

    只保留"现在仍然存在的选项"——装扮表改过（比如删掉手机/爱心、新增桌面显示）之后，
    存档里的旧名字直接丢掉，不让它在界面上变成一个点不亮的空状态。
    多选槽位（COSTUME_MULTI_SLOTS）存列表，其余槽位存单个名字；空槽位不存。
    """
    data = _get_section("costume")
    # 选项名可能是单个表情名，也可能是表情名列表（「点单」= order_press + board、
    # 「剪刀手」= double_peace + no_board）。键统一取 str(name)（界面按钮的 key 也是这么取的），
    # 值放回原样的选项名——千万别只留下 str(name) 这个键，否则列表选项会被拍成
    # "['order_press', 'board']" 这种字符串，存档里的列表值再按元素比对就一个都命不中，
    # 结果就是「点单/剪刀手」重启后被悄悄换成默认项。
    tables = {}
    for slot, _l, _c, items in all_costume_slots():
        tables[slot] = {str(n): n for n, _label in items}
    out = {}
    for slot, val in (data or {}).items():
        table = tables.get(slot)
        if not table:
            continue
        # 先拿存档值整体比对一次（单选槽位存的就是选项名本身，可能是个列表）；
        # 对不上再退回按元素挑，兼容手改过的旧存档与多选槽位。
        cands = [val] + (list(val) if isinstance(val, list) else [])
        picked = []
        for cand in cands:
            name = table.get(str(cand))
            if name is not None and name not in picked:
                picked.append(name)
        if not picked:
            continue
        out[slot] = picked if is_multi_slot(slot) else picked[0]
    # 必须有的槽位（手持道具）：没存过、或存档里是空的 ⇒ 用默认的「点单」
    for _slot, _val in DEFAULT_COSTUME.items():
        if not out.get(_slot):
            out[_slot] = list(_val)
    return out

def save_costume_config(choice):
    """把当前装扮写回 config.json 的 costume 节（摘干净的槽位不落盘）"""
    sec = {k: v for k, v in (choice or {}).items() if v}
    _update_section("costume", sec)

def load_form_config():
    """形象（形态）选择：存 config.json 的 form 节；认不出来的名字回落到默认形态"""
    name = str(_get_section("form").get("name", "") or "")
    return name if name in LIVE2D_FORM_ORDER else LIVE2D_DEFAULT_FORM

def save_form_config(name):
    _update_section("form", {"name": name})

def _migrate_persona_from_system_prompt():
    """从旧 system_prompt.txt 切分出人设：去掉开头"你是X，"前缀与【回复格式要求】段"""
    if not os.path.exists(SYSTEM_PROMPT_FILE):
        return None
    try:
        with open(SYSTEM_PROMPT_FILE, "r", encoding="utf-8") as f:
            text = f.read().strip()
    except Exception:
        return None
    if not text:
        return None
    idx = text.find("【回复格式要求】")
    if idx >= 0:
        text = text[:idx].strip()
    m = re.match(r'^你是[^，,。]+[，,。]\s*(.*)$', text, re.DOTALL)
    if m:
        text = m.group(1).strip()
    return text or None

def save_character_config(config):
    _update_section("character", config)

def load_banned_words():
    """禁词表：优先 config.json 的 character 节；老的 banned_words.txt 兜底（下次保存迁进配置）"""
    val = _get_section("character").get("banned_words")
    if val is None:
        if os.path.exists(BANNED_WORDS_FILE):
            try:
                with open(BANNED_WORDS_FILE, "r", encoding="utf-8") as f:
                    return f.read().strip()
            except Exception:
                return ""
        return ""
    return str(val).strip()

def save_banned_words(text):
    """写进 config.json 的 character 节（老 banned_words.txt 保留不删，只当迁移源）"""
    sec = _get_section("character")
    sec["banned_words"] = (text or "").strip()
    _update_section("character", sec)

def load_watch_config():
    # 10/30：新增时间轴三项 —— 环形缓冲时长 / 近层帧数 / 远层帧数（缺省即默认）
    default = {"min_interval": 15, "max_silence": 120, "ring_seconds": 20,
               "recent_frames": 4, "older_frames": 4, "audio_enabled": 1}
    data = _get_section("watch", default)
    for _k, _v in (("min_interval", 15), ("max_silence", 120), ("ring_seconds", 20),
                   ("recent_frames", 4), ("older_frames", 4), ("audio_enabled", 1)):
        if _k not in data:
            data[_k] = _v
    # 夹取到安全范围：别让手滑的配置把内存或请求撑爆
    try:
        data["ring_seconds"] = max(6, min(300, int(data["ring_seconds"])))
        data["recent_frames"] = max(2, min(4, int(data["recent_frames"])))
        data["older_frames"] = max(0, min(8, int(data["older_frames"])))   # 上限 8 留给实验
    except Exception:
        data["ring_seconds"], data["recent_frames"], data["older_frames"] = 20, 4, 4
    # 兼容旧配置格式（迁移后写回，避免每次启动重复清理）
    _changed = False
    for _old_key in ("polling_interval", "min_count", "max_count"):
        if _old_key in data:
            del data[_old_key]
            _changed = True
    if _changed:
        save_watch_config(data)
    return data

def save_watch_config(config):
    _update_section("watch", config)

READING_CONFIG_FILE = os.path.join(CONFIG_DIR, "reading_config.json")

def load_chats():
    return load_json_file(CHATS_LOG_FILE, [])

TTS_MODE_NAMES = {"volc": "声音复刻", "edge": "Edge", "deepseek": "DeepSeek"}
# 11/15：DeepSeek 原生 TTS（11/13 上线的全家桶应用 API 里的独立接口）
DEEPSEEK_TTS_URL = "https://api.deepseek.com/v1/tools/tts"
DEEPSEEK_TTS_VOICES = (("stella", "海星（女声）"),)   # 11/15 用户要求删掉男声 tide
DEEPSEEK_TTS_VOICE_DEFAULT = "stella"
DEEPSEEK_TTS_PRICE = 3.0 / 10000   # 刊例 3 元/万"计费字符"（汉字算 2 个字符）

# ---------- 形象转换：让她自己做点事（模型自带动作）----------
# 索引对应 live2d_viewer/model/c_0120.model3.json 里 Action 组的顺序
ACTION_POOL = [(0, "挤番茄酱"), (1, "吹泡泡"), (2, "喷水"),
               (3, "开盖"), (4, "自拍"), (5, "快速自拍")]
ACTION_AUTO_MIN = 120    # 两次自发做动作之间的最短间隔（秒）
ACTION_AUTO_MAX = 360    # 最长间隔

# ---------- 装扮配件（卡梅莉亚那套：互斥槽位、可摘）----------
# 槽位：(key, 显示名, 清空按钮的文案, [(表情名 或 表情名列表, 选项文案), ...])
# 注意：装扮清空 = 还原成她原本的样子（不是写 0）——发箍这类参数常态就不是 0
# 形象素材署名（写在「关于」里，按形态列）
# 素材来源：`素材\双形态肥鱼\中肥鱼\`、`素材\双形态肥鱼\成年肥鱼\`（这两个包里没有说明文件，
# 作者名是用户给的）；`素材\双形态肥鱼\小肥鱼\大肥鱼\`（自带《使用说明》：公开免费皮套·制作人 狐宫静）
FORM_CREDITS = {
    'whale': 'Live2D 模型：DeepSeek 鲸鱼娘 —— 模型制作 B站@氵六青（11272072）\n'
             '（商用直播、自印物料允许；禁止任何形式的盗用与出售，模型为无偿分享）',
    'medium': 'Live2D 模型：中肥鱼 —— 模型制作 B站@Mao绒绒家园',
    'adult': 'Live2D 模型：成年肥鱼 —— 模型制作 B站@玹乐喵',
    'small': 'Live2D 模型：小肥鱼 —— 模型制作 狐宫静（公开免费皮套）',
    'big': 'Live2D 模型：大大·肥鱼（免费公皮）—— 原画/拆分 B站@神宫凉子（BV1KmxY66EZ3）、建模 霓虹猫_NeonNeko'
           '（作者禁止二次发布：仅供本地自用，不随发布包分发）',
}

COSTUME_SLOTS = [
    ("glasses", "眼镜", "无", [("round_glasses", "圆眼镜"), ("square_glasses", "方眼镜"),
                              ("oval_glasses", "椭圆眼镜"), ("sunglasses", "墨镜")]),
    ("sticker", "贴纸", "无", [("cat_sticker", "猫猫"), ("bunny_sticker", "兔兔"),
                              ("ribbon_sticker", "蝴蝶结")]),
    ("hair", "发饰", "发箍散发", [("headband", "散发"), ("side_ponytail", "发箍马尾"),
                                 (["headband", "side_ponytail"], "马尾")]),
    ("cloth", "桌布", "不用", [("dark_cloth", "深色")]),
    ("claw", "魔爪", "无", [("claw", "粉魔爪"), (["claw", "claw_color"], "白魔爪")]),
    ("desk", "桌面摆设", "无", [("whale", "头顶鲸"), ("whale_on_desk", "放桌上")]),
    ("display", "桌面显示", "常态", [("brush", "画笔"), ("eraser", "橡皮"), ("undo", "撤回"),
                                    ("parfait", "收起巴菲")]),
    ("item", "手持道具", "无", [("omurice", "蛋包饭"), ("paw", "猫爪"),
                              (["double_peace", "no_board"], "剪刀手"), (["order_press", "board"], "点单")]),
]

# 可以多选并存的槽位（其余槽位互斥单选）。
# 「桌面显示」里画笔/橡皮/撤回 是各占一处的桌面物件，实测互不冲突、能同时挂；
# 巴菲是反的：她常态就摆着一份，所以这一项写作"收起巴菲"（同发饰槽"摘掉发箍"的先例）。
COSTUME_MULTI_SLOTS = {"display"}


# 不提供"无"选项、必须有东西的槽位；以及没存过装扮时的默认选择
COSTUME_REQUIRED_SLOTS = {"item"}
DEFAULT_COSTUME = {"item": ["order_press", "board"]}

# 装扮**按形态各一套**（用户 10/11 要求把"钢盆"做成装扮配件）：
# 每套 = (槽位表, 多选槽位, 必须有东西的槽位, 没存过时的默认值)。
# 槽位名各形态不同 ⇒ 同一份 costume 存档可以同时记住几套形态的选择，互不干扰。
FORM_COSTUMES = {
    'whale': (COSTUME_SLOTS, COSTUME_MULTI_SLOTS, COSTUME_REQUIRED_SLOTS, DEFAULT_COSTUME),
    # 小肥鱼只有一件：钢盆（写 Param89；实测画面差 12.46，扣上后内容高 242、上留 13/下留 9，
    # 不裁切 ⇒ 不需要 COSTUME_FIT）
    'small': ([("head", "头顶", "不戴", [("basin", "钢盆")])], set(), set(), {}),
    # 11/18 big（大大·肥鱼）：选项全部走模型自带的 exp3，按槽位互斥、可摘；
    # 裙子和尾巴是"减法"状态（exp3 写 -1），摘掉时由渲染器还原成装扮前的值。
    # 成年肥鱼：四个表情里只有 size_change 能当"装扮"用（写 Size=1，摘掉时还原）
    'adult': ([("body", "体型", "默认", [("size_change", "变小孩子")])], set(), set(), {}),
    'big': ([
        ("glasses", "眼镜", "无", [("黑框眼镜", "黑框眼镜"), ("单片眼镜", "单片眼镜"), ("加载", "卡顿加载符号")]),
        ("skirt", "裙子", "女仆超短裙", [("裙子切换", "女仆长裙")]),
        ("cloth", "胸口", "低胸上衣", [("胸口衣服", "保守上衣")]),
        ("tail", "尾巴", "露出", [("尾巴开关", "收起")]),
        ("body", "体型", "少女", [("体型1", "小女孩"), ("体型2", "大头娃娃")]),
        ("head", "头顶", "不戴", [("钢盆", "钢盆")]),
        ("shoes", "鞋", "穿鞋", [("脱鞋", "光脚")]),
    ], set(), set(), {}),
}


def costume_cfg(form):
    """取某形态的装扮配置；没有装扮的形态返回空配置（装扮窗只显示一句说明）"""
    return FORM_COSTUMES.get(form) or ([], set(), set(), {})


def all_costume_slots():
    """所有形态的槽位并集——存档校验用它，这样一个存档能同时记住几套形态的选择"""
    out = []
    for _slots, _m, _r, _d in FORM_COSTUMES.values():
        out.extend(_slots)
    return out


def is_multi_slot(slot):
    """该槽位是不是多选槽位（各形态的多选集合不同，这里查并集）"""
    return any(slot in _m for _s, _m, _r, _d in FORM_COSTUMES.values())

def _costume_toggle(choice, slot, name):
    """算出点击某个装扮按钮之后该槽位的新选择值。
    多选槽位：点一下加入、再点一下移出（name=None = 清空）；
    单选槽位：直接替换（name=None = 摘掉）。
    """
    if is_multi_slot(slot):
        cur = list(choice.get(slot) or [])
        if name is None:
            return []
        if name in cur:
            cur.remove(name)
        else:
            cur.append(name)
        return cur
    return name


def load_zoom_config():
    return _get_section("zoom", {
        "zoom_char": 2.0, "zoom_bubble": 0.7, "zoom_input": 0.7,
        "window_width": BASE_WINDOW_WIDTH
    })

def save_zoom_config(char, bubble, input_zoom, width):
    _update_section("zoom", {"zoom_char": char, "zoom_bubble": bubble, "zoom_input": input_zoom,
                             "window_width": width})

DEFAULT_WAKE_WINDOW = 8.0     # 免唤醒窗口默认秒数（0 = 关闭，每次都要喊名字）
DEFAULT_PTT_VK = 0xA3         # 按键说话默认键：右 Ctrl（VK_RCONTROL = 163）
DEFAULT_PTT_NAME = "右 Ctrl"

# 唤醒词容错：识别模型是通用词表，"大肥鱼"不是词，实测常被听成真词
# （化肥鱼/咖啡鱼/阿非鱼/那飞鱼），拼音必须逐音节全等就永远唤不醒。
WAKE_TOLERANCE = 1            # 拼音通道允许错几个音节（0 = 必须完全同音）
WAKE_TAIL_LOCK = 2            # 名字末 N 个音节必须完全一致（挡"大飞机/大部分/往那卡"这类真词）
WAKE_ANYWHERE = True          # 名字出现在整句任何位置都算唤醒（False = 只认句首 5~6 字内）
WAKE_VOCATIVE_CHARS = 2       # 名字起点在前几个字内才算"称呼"（才会从文本里删掉）；更靠后就是"提到名字"，整句原样送
WAKE_ALIASES = ("罗非鱼", "大头鱼")   # 默认名的"听错写法"白名单：只在还叫"大肥鱼"时生效（改名后整套失效）

# 按键显示名：按 Windows 虚拟键码反查（轮询捕获时只有 vk，没有 Tk 的 keysym）
VK_LABELS = {
    0x08: "退格", 0x09: "Tab", 0x0D: "回车", 0x10: "Shift", 0x11: "Ctrl", 0x12: "Alt",
    0x14: "Caps Lock", 0x1B: "Esc", 0x20: "空格", 0x21: "PageUp", 0x22: "PageDown",
    0x23: "End", 0x24: "Home", 0x25: "左方向", 0x26: "上方向", 0x27: "右方向", 0x28: "下方向",
    0x2C: "PrintScreen", 0x2D: "Insert", 0x2E: "Delete", 0x5B: "左 Win", 0x5C: "右 Win",
    0x5D: "菜单键", 0x90: "Num Lock", 0x91: "Scroll Lock",
    0xBA: ";", 0xBB: "=", 0xBC: ",", 0xBD: "-", 0xBE: ".", 0xBF: "/", 0xC0: "`",
    0xDB: "[", 0xDC: "\\", 0xDD: "]", 0xDE: "'",
    0xA0: "左 Shift", 0xA1: "右 Shift", 0xA2: "左 Ctrl", 0xA3: "右 Ctrl",
    0xA4: "左 Alt", 0xA5: "右 Alt",
}

def vk_label(vk):
    """虚拟键码 → 人看的名字"""
    vk = int(vk)
    if 0x70 <= vk <= 0x87:
        return "F%d" % (vk - 0x6F)          # F1~F24
    if 0x41 <= vk <= 0x5A:
        return chr(vk)                       # A~Z
    if 0x30 <= vk <= 0x39:
        return chr(vk)                       # 0~9
    if 0x60 <= vk <= 0x69:
        return "小键盘%d" % (vk - 0x60)
    if 0x6A <= vk <= 0x6F:
        return "小键盘符号"
    return VK_LABELS.get(vk, "按键 0x%02X" % vk)

def any_key_down(skip=()):
    """当前按着的键里最小的那个虚拟键码（0 = 没有）。

    轮询法，所以修饰键（Ctrl/Alt/Shift）也能捕获 —— Tk 的 <KeyPress> 在 Windows 上
    对"单独按一下右 Ctrl"并不可靠（合成测试时直接报 no keycode for keysym）。
    """
    try:
        u = ctypes.windll.user32
        for vk in range(1, 255):
            if vk in skip or 1 <= vk <= 6:      # 1~6 是鼠标左右/中键，别被点击误采
                continue
            if u.GetAsyncKeyState(vk) & 0x8000:
                return vk
    except Exception:
        pass
    return 0

def is_elevated():
    """当前进程是不是以管理员身份（高完整性）运行。

    11/18 实测：游戏以管理员运行时，普通权限进程既读不到 GetAsyncKeyState，
    也收不到 Raw Input —— 游戏里"按键说话没反应"就是这个；提权后同一个键立刻恢复。
    """
    try:
        return bool(ctypes.windll.shell32.IsUserAnAdmin())
    except Exception:
        return False

def load_voice_config():
    """语音识别设置：
    enabled          上次退出时语音识别是开着还是关着（开机沿用；自动睡眠/退出时的关麦不写它）
    wake_window      免唤醒窗口秒数（她说完话后可直接说话的时间；0 = 关闭，每次都要喊名字）
    hotkey_enabled   按键说话开关（按住指定键期间窗口一直开着）
    hotkey_vk/name   那个键的 Windows 虚拟键码与显示名
    """
    default = {"enabled": False, "wake_window": DEFAULT_WAKE_WINDOW, "hotkey_enabled": False,
               "hotkey_vk": DEFAULT_PTT_VK, "hotkey_name": DEFAULT_PTT_NAME}
    sec = _get_section("voice", default)
    try:
        v = float(sec.get("wake_window", DEFAULT_WAKE_WINDOW))
    except (TypeError, ValueError):
        v = DEFAULT_WAKE_WINDOW
    if v != v or v < 0:          # NaN / 负数都当默认
        v = DEFAULT_WAKE_WINDOW
    enabled = bool(sec.get("hotkey_enabled", False))
    if enabled:
        v = 0.0                  # 按键说话与免唤醒窗口不共存：开着按键就固定"关闭"
    try:
        vk = int(sec.get("hotkey_vk", DEFAULT_PTT_VK))
    except (TypeError, ValueError):
        vk = DEFAULT_PTT_VK
    name = sec.get("hotkey_name")
    if not (1 <= vk <= 255):
        vk = DEFAULT_PTT_VK
        name = DEFAULT_PTT_NAME          # 键回退了，名字也一起回退，别留个对不上的名字
    if not isinstance(name, str) or not name.strip():
        name = DEFAULT_PTT_NAME
    return {"enabled": bool(sec.get("enabled", False)),
            "wake_window": min(v, 60.0),
            "hotkey_enabled": enabled,
            "hotkey_vk": vk,
            "hotkey_name": name.strip()}

def save_voice_config(cfg):
    """cfg 至少含 wake_window，其余按键项缺省不覆盖旧值"""
    sec = _get_section("voice", {})
    out = {"wake_window": float(cfg.get("wake_window", sec.get("wake_window", DEFAULT_WAKE_WINDOW)))}
    for k, d in (("enabled", False), ("hotkey_enabled", True), ("hotkey_vk", DEFAULT_PTT_VK),
                 ("hotkey_name", DEFAULT_PTT_NAME)):
        out[k] = cfg[k] if k in cfg else sec.get(k, d)
    _update_section("voice", out)

def save_chats(chats):
    save_json_file(CHATS_LOG_FILE, chats)

def _mem_mentions(query, content, min_hits=3, min_ratio=0.05):
    """他这句话是不是"字面提到了"这条记忆（10/28）。

    为什么不用向量：实测「你还记得暗区突围那次撤离失败吗」这类问句，5 句里只召回 1 句
    —— 问句里的"你还记得…吗"是噪声，把相似度拉平了。中文字面按二元组比对是确定性的：
    真数据上目标命中 h=4/8/7、占比 8~15%，噪声句 h=0/0/2、占比 ≤1%，阈值 3 / 5% 分得开。
    """
    try:
        q = "".join((query or "").split())
        c = "".join((content or "").split())
        if len(q) < 4 or len(c) < 4:
            return False
        cg = {c[i:i + 2] for i in range(len(c) - 1)}
        qg = {q[i:i + 2] for i in range(len(q) - 1)}
        if not cg:
            return False
        hit = len(cg & qg)
        return hit >= min_hits and hit / len(cg) >= min_ratio
    except Exception:
        return False


def load_memories():
    try:
        if _memory_db.has_data():
            data = _memory_db.load_all()
        else:
            data = None
    except Exception as e:
        log.warning(f"从数据库读取记忆失败，回退 JSON: {e}")
        data = None
    if data is None:
        data = load_json_file(MEMORY_FILE, {"topics": [], "events": [], "profile": {"traits": []}})
        # 兼容旧格式：扁平列表 memories.json 先迁移为新格式再使用
        if isinstance(data, list):
            data = _migrate_old_memories(data)
        if data.get("topics") or data.get("events") or data.get("profile", {}).get("traits"):
            try:
                _memory_db.replace_all(data)
            except Exception as e:
                log.warning(f"写入记忆数据库失败: {e}")
    # 画像固定清单结构归一化：旧字段(observation/confidence/evidence_count)折叠进新结构；
    # 有变化时立即落盘一次（之后幂等不再触发）
    if _normalize_traits_in_data(data):
        try:
            save_memories(data)
        except Exception as e:
            log.warning(f"画像结构迁移落盘失败: {e}")
    return data

def save_memories(memories):
    # 10/28：落盘失败（Windows 上目标被别的线程短暂打开）不应炸掉调用它的后台线程 ——
    # 数据还在内存里，下一次保存会补上；这里只记一行 warning。
    try:
        save_json_file(MEMORY_FILE, memories)
    except Exception as e:
        log.warning(f"记忆 JSON 保存失败（下次会重试）: {e}")
    try:
        _memory_db.replace_all(memories)
    except Exception as e:
        log.warning(f"保存记忆数据库失败: {e}")

def _normalize_traits_in_data(data):
    """把画像条目归一化为固定清单结构 {trait, description, evidence[], created_at, updated_at}。

    旧结构字段 observation / confidence / evidence_count 会折叠：observation 作描述兜底、
    旧证据列表保留最近 MAX_TRAIT_EVIDENCE 条、分数计数一律丢弃；
    清单外条目的内容并入「其他」，不直接丢弃（防信息流失）；
    同清单条目若有多条（历史遗留）只保留最新一条，旧内容并入其证据。
    幂等：已符合新结构且无变化时返回 False（不触发落盘）。
    """
    profile = data.setdefault("profile", {})
    raw = profile.get("traits") or []
    if not isinstance(raw, list):
        raw = []
    legacy = False
    clean = []
    spill = []  # 清单外条目的 (描述, 证据列表)
    for t in raw:
        if not isinstance(t, dict):
            continue
        name = str(t.get("trait", "")).strip()
        if ("observation" in t or "confidence" in t or "evidence_count" in t):
            legacy = True
        desc = str(t.get("description") or t.get("observation") or "").strip()
        evs = t.get("evidence")
        if not isinstance(evs, list):
            evs = []
        evs = [str(e).strip() for e in evs if str(e).strip()]
        if name not in TRAIT_LIST:
            if desc or evs:
                spill.append((desc, evs))
            continue
        clean.append({
            "trait": name,
            "description": desc,
            "evidence": evs[-MAX_TRAIT_EVIDENCE:],
            "created_at": str(t.get("created_at", "")),
            "updated_at": str(t.get("updated_at", "")),
        })
    # 清单外内容归入「其他」
    other = next((c for c in clean if c["trait"] == "其他"), None)
    if other is None and spill:
        other = {"trait": "其他", "description": "", "evidence": [], "created_at": "", "updated_at": ""}
        clean.append(other)
    for desc, evs in spill:
        if desc and not other["description"]:
            other["description"] = desc
        if evs:
            other["evidence"] = (other["evidence"] + evs)[-MAX_TRAIT_EVIDENCE:]
    # 同清单条目多条的合并（保留最新一条，其余内容并入其证据）
    by_name = {}
    for c in clean:
        old = by_name.get(c["trait"])
        if old is None:
            by_name[c["trait"]] = c
            continue
        newer, older = (c, old) if (c["updated_at"] or "") >= (old["updated_at"] or "") else (old, c)
        spill_ev = [e for e in ([older["description"]] if older["description"] else []) + older["evidence"]
                    if e and e not in newer["evidence"]]
        if spill_ev:
            newer["evidence"] = (newer["evidence"] + spill_ev)[-MAX_TRAIT_EVIDENCE:]
        by_name[c["trait"]] = newer
    merged = [by_name[n] for n in TRAIT_LIST if n in by_name]
    # 关系形象已取消「确信度」：旧数据里的该字段清掉，不再落盘
    rel = profile.get("relation")
    if isinstance(rel, dict) and "confidence" in rel:
        rel.pop("confidence", None)
        legacy = True
    key = lambda t: (t.get("trait", ""), t.get("description", ""), tuple(t.get("evidence") or []))
    changed = legacy or (sorted(map(key, raw), key=str) != sorted(map(key, merged), key=str))
    if changed:
        profile["traits"] = merged
        data["profile"] = profile
        return True
    return False

def _migrate_old_memories(data):
    """将旧格式 memories.json（扁平列表）迁移为新格式"""
    if not isinstance(data, list):
        return data  # 已是新格式，无需迁移
    new_data = {"topics": [], "events": [], "profile": {"traits": []}}
    for old in data:
        if not isinstance(old, dict):
            continue
        new_data["topics"].append({
            "id": str(uuid.uuid4())[:8],
            "content": old.get("content", ""),
            "created_at": old.get("date", datetime.now().strftime("%Y-%m-%d %H:%M:%S")),
            "last_accessed_at": old.get("date", datetime.now().strftime("%Y-%m-%d %H:%M:%S")),
            "importance": 0.5,
            "access_count": 0
        })
    log.info("旧格式 memories.json 已迁移为新格式 (%d 条话题)", len(new_data["topics"]))
    return new_data

def _migrate_old_chats(data):
    """将旧格式 chats.json（含 type 字段的记录列表）迁移为 buffer 格式"""
    if not data:
        return []
    if isinstance(data[0], list):
        return data  # 已是新格式 [[user, assistant], ...]
    if not isinstance(data[0], dict) or "type" not in data[0]:
        return data  # 无法识别的格式，返回原样
    new_buffer = []
    for rec in data:
        if rec.get("type") == "chat":
            new_buffer.append([
                {"role": "user", "content": rec.get("user", "")},
                {"role": "assistant", "content": rec.get("assistant", "")}
            ])
    log.info("旧格式 chats.json 已迁移为 buffer 格式 (保留 %d 轮)", len(new_buffer))
    return new_buffer[-10:]

def load_topic_history():
    return load_json_file(TOPIC_HISTORY_FILE, [])

def save_topic_history(history):
    if len(history) > 50:
        history = history[-50:]
    save_json_file(TOPIC_HISTORY_FILE, history)

TOPIC_MATERIAL_FILE = os.path.join(CONFIG_DIR, "topic_material.jsonl")
TOPIC_MATERIAL_MAX = 200          # 最多留多少条素材
TOPIC_MATERIAL_HOURS = 12         # 只取最近多少小时内的事（11/01 24→12）
TOPIC_MATERIAL_KEEP_HOURS = 12    # 超过这么久还没被用掉的素材直接删掉（11/01 48→12）
TOPIC_MATERIAL_DUP_RATIO = 0.97   # 相似度到这个程度才算同一件事（0.9 会把模板化的句子误判成重复）
_TOPIC_MATERIAL_LOCK = threading.Lock()


def _read_topic_materials():
    """读素材文件（JSONL，坏行跳过）。返回 list[dict]。"""
    out = []
    try:
        if not os.path.exists(TOPIC_MATERIAL_FILE):
            return out
        with open(TOPIC_MATERIAL_FILE, "r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    d = json.loads(line)
                except Exception:
                    continue
                if isinstance(d, dict) and d.get("text"):
                    out.append(d)
    except Exception as e:
        log.warning("读取话题素材失败: %s", e)
    return out


def _write_topic_materials(items):
    try:
        # 11/01：写盘时剪掉过期没用掉的（否则 200 条上限会被老料永久占住）
        _cut = time.time() - TOPIC_MATERIAL_KEEP_HOURS * 3600
        items = [x for x in items if float(x.get("t") or 0) >= _cut]
        tmp = TOPIC_MATERIAL_FILE + ".tmp"
        with open(tmp, "w", encoding="utf-8", newline="") as f:
            for d in items[-TOPIC_MATERIAL_MAX:]:
                f.write(json.dumps(d, ensure_ascii=False) + "\n")
        os.replace(tmp, TOPIC_MATERIAL_FILE)
    except Exception as e:
        log.warning("写入话题素材失败: %s", e)


def add_topic_material(text, source="event"):
    """把一件**真实发生过的事**攒进素材池，供话题生成取材（10/25 治话题生硬）。"""
    try:
        t = " ".join((text or "").split())
        if len(t) < 6:
            return
        t = t[:120]
        with _TOPIC_MATERIAL_LOCK:
            items = _read_topic_materials()
            for old in items[-40:]:
                o = old.get("text", "")
                if not o:
                    continue
                if o == t:
                    return
                try:
                    import difflib
                    if difflib.SequenceMatcher(None, o, t).ratio() >= TOPIC_MATERIAL_DUP_RATIO:
                        return
                except Exception:
                    pass
            items.append({"t": time.time(), "src": source, "text": t, "used": 0})
            _write_topic_materials(items)
    except Exception as e:
        log.warning("话题素材写入失败: %s", e)


SAID_RECENT_FILE = os.path.join(CONFIG_DIR, "said_recent.jsonl")
_SAID_RECENT_LOCK = threading.Lock()


def add_recent_said(text):
    """记下"他亲口说过的一句话"，供之后发起话题取材（11/05）。

    为什么不直接用记忆/事件总结：那类内容是"陪看过程"的总结，拿它当话题
    只会变成复述他今天干了什么，很别扭；他自己说过的话才是天然的聊天由头。
    """
    try:
        t = " ".join(str(text or "").split())
        if not (4 <= len(t) <= 80):
            return
        with _SAID_RECENT_LOCK:
            items = []
            if os.path.exists(SAID_RECENT_FILE):
                with open(SAID_RECENT_FILE, "r", encoding="utf-8") as f:
                    for line in f:
                        try:
                            d = json.loads(line)
                        except Exception:
                            continue
                        if isinstance(d, dict) and d.get("text"):
                            items.append(d)
            items.append({"t": time.time(), "text": t})
            keep = time.time() - 7 * 24 * 3600
            items = [x for x in items if float(x.get("t") or 0) >= keep][-150:]
            tmp = SAID_RECENT_FILE + ".tmp"
            with open(tmp, "w", encoding="utf-8", newline="") as f:
                for d in items:
                    f.write(json.dumps(d, ensure_ascii=False) + chr(10))
            os.replace(tmp, SAID_RECENT_FILE)
    except Exception as e:
        log.debug("记录他说过的话失败: %s", e)


def load_recent_said(limit=3, hours=72):
    """取最近他真说过的话（新的在前，去重）。"""
    out = []
    try:
        if not os.path.exists(SAID_RECENT_FILE):
            return out
        cut = time.time() - hours * 3600
        rows = []
        with open(SAID_RECENT_FILE, "r", encoding="utf-8") as f:
            for line in f:
                try:
                    d = json.loads(line)
                except Exception:
                    continue
                if isinstance(d, dict) and d.get("text") and float(d.get("t") or 0) >= cut:
                    rows.append(d)
        for d in reversed(rows):
            t = str(d["text"]).strip()
            if t and t not in out:
                out.append(t)
            if len(out) >= limit:
                break
    except Exception as e:
        log.debug("读取他说过的话失败: %s", e)
    return out


def load_topic_materials(limit=5, hours=None):
    """取最近未用过的事（默认 24 小时内、最多 5 条），新的在前。"""
    try:
        hours = TOPIC_MATERIAL_HOURS if hours is None else hours
        cutoff = time.time() - hours * 3600
        with _TOPIC_MATERIAL_LOCK:
            items = _read_topic_materials()
        fresh = [x for x in items
                 if float(x.get("t") or 0) >= cutoff and not x.get("used")]
        # 11/01：优先用"真事"（event 等），她自己的陪看评论只当兜底——
        # 否则 187/200 条都是她说过的话，取材等于让她自我模仿。
        fresh.sort(key=lambda x: (x.get("src") == "watch", -float(x.get("t") or 0)))
        return fresh[:limit]
    except Exception as e:
        log.warning("读取话题素材失败: %s", e)
        return []


def mark_topic_materials_used(texts):
    """标记这些素材已经被拿去生成过话题，别反复用。"""
    try:
        wanted = set(texts or [])
        if not wanted:
            return
        with _TOPIC_MATERIAL_LOCK:
            items = _read_topic_materials()
            now = time.time()
            for d in items:
                if d.get("text") in wanted and not d.get("used"):
                    d["used"] = now
            _write_topic_materials(items)
    except Exception as e:
        log.warning("标记话题素材失败: %s", e)



def build_system_prompt(name, persona, max_chars=DEFAULT_MAX_CHARS, style_rules=None, has_cues=False, look_line=""):
    """由角色姓名 + 人设 + 回复规则拼系统提示词（"你是{名字}，"与情绪括号格式由代码内置）。
    max_chars / style_rules 来自 config.json 的 character 节；style_rules 传空串＝不注入说话方式段。"""
    parts = [f"你是{name}，{persona}\n\n【回复格式要求】\n{format_reply_rules(max_chars)}"]
    style = (DEFAULT_STYLE_RULES if style_rules is None else str(style_rules)).strip()
    if style:
        parts.append("【说话方式】\n" + style)
    # 11/15：表情符号许可（一句，不堆限制；也别让她把表情当句末装饰）
    parts.append("【表情】大概每五六句话里有那么一句，句尾可以带一个表情符号（😌 😳 😮‍💨），"
                 "别连着用；想表达情绪时也可以让它顶半句话，不用每次都用文字形容。")
    # 11/18：身体动作许可。词会从台词里剥掉，不显示也不朗读；值来自模型本身（动作播一段/穿戴写原值）
    if has_cues:
        parts.append("【身体】想做个动作或者换身打扮，就在话里写〔词〕，气泡和朗读都不会念出来。"
                     "能写：竖起食指、抚胸、狗尾草、贴贴、靠近他、把脸凑过去。"
                     "一句最多一个，别每句都用，动作做完会自己回常态。"
                     "他明确让你做某个动作（比如\"抚胸\"\"贴贴\"）时，一定要在话里写上对应的〔词〕，光说\"好呀\"不算做到了。")
    if look_line:
        parts.append(look_line)
    return "\n\n".join(parts)

def build_full_system_prompt(base_prompt, user_profile):
    story_text = ""
    if user_profile.get("story", "").strip():
        story_text = f"\n【角色背景故事】\n{user_profile['story'].strip()}\n"
    info = f"""【用户档案】（下面说的是正在跟你说话的人，不是你自己；你自己的名字看人设里"你是…"那句）
- 你叫他：{user_profile.get('call_name', '你')}
- 他的昵称：{user_profile.get('nickname', '你')}
- 他的生日：{user_profile.get('birthday', '未知')}
{story_text}
请记住这些信息，用合适的语气跟他说话。
{base_prompt}
"""
    return info

# ------------------------------- UI 配色方案 ---------------------------------
# 状态栏风格 - 柔紫/紫罗兰色系
# 透明遮罩色（所有需透明的背景统一使用此色）
TRANS_MASK = "#f5f3ff"

# 气泡（Win11 卡片风格）
BUBBLE_TEXT    = "#1f2328"

# 输入框
INPUT_BG       = "#ffffff"

# 对话框通用（Win11 卡片风格后为纯白）
DIALOG_BG      = "#ffffff"
STAR_ROW_BG    = "#e7ebff"     # 收藏行：比白底深的淡紫底
ARCHIVE_ROW_BG = "#f1f2f4"     # 归档行：浅灰底
ARCHIVE_ROW_FG = "#8b8f98"     # 归档行：灰字

# 按钮
BTN_PRIMARY    = "#8b5cf6"
BTN_PRIMARY_TX = "#ffffff"

# ---- Win11 现代风格调色板（白色卡片 / 细边框 / 柔影 / 浅灰悬停）----
CARD_MASK      = "#010203"     # 透明挖角色（窗口中显示为全透明）
CARD_BG        = "#ffffff"     # 卡片底色
CARD_BORDER    = "#e3e6ea"     # 卡片描边
CARD_BORDER_STRONG = "#8b95a3"  # 强描边（栏目分区用，比常规描边明显）
CARD_SHADOW_A  = "#e6e9ee"     # 卡片投影外层
CARD_SHADOW_B  = "#eef0f4"     # 卡片投影内层
TEXT_MAIN      = "#1f2328"     # 主文字
TEXT_SUB       = "#5f6b7a"     # 次要文字
TEXT_DISABLED  = "#a0a8b4"     # 禁用文字
DIVIDER        = "#eceff3"     # 分隔线
INPUT_BORDER2  = "#d0d7de"     # 输入框描边
HOVER_BG       = "#f2f4f7"     # 悬停高亮（菜单项/浅色按钮）
DANGER_RED     = "#e5484d"     # 危险操作红

def _shade_color(hex_color, factor):
    """按比例调亮/调暗颜色（factor>1 变亮，<1 变暗）"""
    c = (hex_color or "#888888").lstrip('#')
    if len(c) != 6:
        return hex_color
    try:
        r = min(255, max(0, int(int(c[0:2], 16) * factor)))
        g = min(255, max(0, int(int(c[2:4], 16) * factor)))
        b = min(255, max(0, int(int(c[4:6], 16) * factor)))
        return f"#{r:02x}{g:02x}{b:02x}"
    except ValueError:
        return hex_color

def _snap_alpha(img, threshold=128):
    """把 RGBA 图的半透明边缘像素二值化（alpha<threshold → 全透明，否则 → 全不透明）。
    LANCZOS 缩放 RGBA 会在边框外侧产生半透明过渡带，在浅色背景上呈现为一圈多余的
    “描边”；二值化后边缘为干净硬边。"""
    arr = np.asarray(img).astype(np.int32)
    arr[..., 3] = np.where(arr[..., 3] < threshold, 0, 255)
    return Image.fromarray(arr.astype(np.uint8), 'RGBA')

def _rounded_rect_photo(width, height, radius, fill, border_color=None, border_width=1, scale=3):
    """PIL 超采样生成平滑圆角矩形 PhotoImage（3x 绘制 + LANCZOS 缩放，彻底解决阶梯状圆角）"""
    from PIL import Image, ImageDraw
    w, h = max(2, width * scale), max(2, height * scale)
    r = max(1, min(radius, width // 2 - 1, height // 2 - 1) * scale)
    img = Image.new('RGBA', (w, h), (0, 0, 0, 0))
    d = ImageDraw.Draw(img)
    d.rounded_rectangle([0, 0, w - 1, h - 1], radius=r, fill=fill,
                        outline=border_color, width=max(1, border_width * scale) if border_color else 0)
    img = img.resize((width, height), Image.LANCZOS)
    return ImageTk.PhotoImage(_snap_alpha(img))

def _card_photo(width, height, radius, mask=CARD_MASK):
    """生成 Win11 风格卡片底图：白色圆角卡片 + 细边框 + 右下柔影。
    圆角外像素吸附回透明挖角色，消除透明色边缘的灰色毛边。"""
    from PIL import Image, ImageDraw
    scale = 3
    W, H = max(2, width * scale), max(2, height * scale)
    R = max(1, min(radius, width // 2 - 1, height // 2 - 1) * scale)
    img = Image.new('RGBA', (W, H), (0, 0, 0, 0))
    d = ImageDraw.Draw(img)
    # 柔影：两层实色圆角矩形向右下偏移（外层深、内层浅，近似渐变）
    for off, col in [(2 * scale, CARD_SHADOW_B), (4 * scale, CARD_SHADOW_A)]:
        d.rounded_rectangle([off, off, W, H], radius=R, fill=col)
    # 卡片本体 + 描边
    d.rounded_rectangle([0, 0, W, H], radius=R, fill=CARD_BG)
    d.rounded_rectangle([0, 0, W - 1, H - 1], radius=R, outline=CARD_BORDER, width=scale)
    img = img.resize((width, height), Image.LANCZOS)
    # 边缘吸附：alpha<128 的像素设为透明挖角色；内侧像素吸附到最近调色板色（白/描边/投影）
    arr = np.asarray(img).astype(np.int32)
    rgb = arr[..., :3]
    inside = arr[..., 3] >= 128
    pal = np.array([
        [255, 255, 255],
        [int(CARD_BORDER[1:3], 16), int(CARD_BORDER[3:5], 16), int(CARD_BORDER[5:7], 16)],
        [int(CARD_SHADOW_A[1:3], 16), int(CARD_SHADOW_A[3:5], 16), int(CARD_SHADOW_A[5:7], 16)],
    ], dtype=np.int32)
    dist = ((rgb[:, :, None, :] - pal[None, None, :, :]) ** 2).sum(-1)
    best = pal[dist.argmin(-1)]
    m = np.array([int(mask[1:3], 16), int(mask[3:5], 16), int(mask[5:7], 16)], dtype=np.int32)
    arr[..., :3] = np.where(inside[:, :, None], best, m)
    arr[..., 3] = 255
    return ImageTk.PhotoImage(Image.fromarray(arr.astype(np.uint8), 'RGBA'))

def _bubble_photo(width, height, radius, arrow_w=18, arrow_h=9):
    """Win11 风格对话气泡底图：白色圆角卡片 + 细边框 + 右下柔影 + 底部小箭头（PIL 超采样）。
    注意：画布高度必须 = 主体 + 箭头，柔影矩形必须完整落在画布内——
    超出画布的部分会被裁剪，柔影底部变成直角，气泡下角会出现“方角”。"""
    from PIL import Image, ImageDraw
    scale = 3
    total_h = height + arrow_h
    W, H = max(2, width * scale), max(2, total_h * scale)
    R = max(1, min(radius, width // 2 - 1, height // 2 - 1) * scale)
    img = Image.new('RGBA', (W, H), (0, 0, 0, 0))
    d = ImageDraw.Draw(img)
    body_h = height * scale - 1
    # 柔影：右下偏移，完整在画布内（底部延伸到箭头区下方 3px）
    d.rounded_rectangle([2 * scale, 3 * scale, W - 1, body_h + 3 * scale],
                        radius=R, fill=CARD_SHADOW_A)
    # 白底主体 + 细边框
    d.rounded_rectangle([0, 0, W - 1, body_h], radius=R, fill=CARD_BG)
    d.rounded_rectangle([0, 0, W - 1, body_h], radius=R, outline=CARD_BORDER, width=scale)
    # 底部小箭头（边框色外三角 + 白色内三角）
    ax = W // 2
    hw = int(arrow_w / 2 * scale)
    d.polygon([(ax - hw, body_h), (ax + hw, body_h), (ax, body_h + arrow_h * scale)], fill=CARD_BORDER)
    d.polygon([(ax - hw + scale, body_h - scale), (ax + hw - scale, body_h - scale),
               (ax, body_h + (arrow_h - 1) * scale)], fill=CARD_BG)
    img = img.resize((width, total_h), Image.LANCZOS)
    return ImageTk.PhotoImage(_snap_alpha(img))

class RoundedText(tk.Canvas):
    """自绘圆角多行输入框（QQ 风格）：PIL 平滑圆角底 + 内嵌无边框 Text。

    和 RoundedEntry 同一套路，只是里面装 Text（多行、Enter 发送、Shift+Enter 换行）。
    宽度自适应：<Configure> 时按新尺寸重画底图（尺寸没变不重画）。
    """

    def __init__(self, master, width=420, height=78, radius=None,
                 bg="#ffffff", border=INPUT_BORDER2, fg=TEXT_MAIN,
                 font=None, parent_bg=CARD_BG, insert_bg=BTN_PRIMARY):
        if radius is None:
            radius = 10
        super().__init__(master, width=width, height=height, highlightthickness=0, bd=0,
                         bg=parent_bg)
        self._cw, self._ch = int(width), int(height)
        self._r = max(2, min(radius, self._cw // 2 - 2, self._ch // 2 - 2))
        self._bg = bg
        self._border = border
        self._parent_bg = parent_bg
        self._focused = False
        self._bg_photo = _rounded_rect_photo(self._cw, self._ch, self._r, bg,
                                             border_color=border, border_width=1)
        self._bg_item = self.create_image(0, 0, anchor="nw", image=self._bg_photo)
        pad = max(8, self._r + 2)
        self.text = tk.Text(self, bd=0, relief=tk.FLAT, highlightthickness=0,
                            bg=bg, fg=fg, insertbackground=insert_bg,
                            font=font or ("TkDefaultFont", 10), wrap="word",
                            spacing1=0, spacing3=0, padx=0, pady=0)
        self._cwin = self.create_window(pad, pad, anchor="nw", window=self.text,
                                       width=self._cw - 2 * pad, height=self._ch - 2 * pad)
        self.text.bind("<FocusIn>", lambda e: self._set_focus(True), add="+")
        self.text.bind("<FocusOut>", lambda e: self._set_focus(False), add="+")
        self.bind("<Button-1>", lambda e: self._focus())
        self.text.bind("<Button-1>", lambda e: self._focus(), add="+")
        self.bind("<Configure>", self._on_resize)

    def _focus(self):
        try:
            self.winfo_toplevel().focus_force()
        except Exception:
            pass
        try:
            self.text.focus_set()
        except Exception:
            pass

    def _on_resize(self, e):
        w, h = int(e.width), int(e.height)
        if w < 20 or h < 20 or (w == self._cw and h == self._ch):
            return
        self._cw, self._ch = w, h
        self._r = max(2, min(10, w // 2 - 2, h // 2 - 2))
        pad = max(8, self._r + 2)
        self._bg_photo = _rounded_rect_photo(w, h, self._r, self._bg,
                                             border_color=(BTN_PRIMARY if self._focused else self._border),
                                             border_width=1)
        self.itemconfigure(self._bg_item, image=self._bg_photo)
        self.coords(self._cwin, pad, pad)
        self.itemconfigure(self._cwin, width=max(10, w - 2 * pad), height=max(10, h - 2 * pad))

    def _set_focus(self, on):
        if self._focused == on:
            return
        self._focused = on
        self._bg_photo = _rounded_rect_photo(self._cw, self._ch, self._r, self._bg,
                                             border_color=(BTN_PRIMARY if on else self._border),
                                             border_width=1)
        self.itemconfigure(self._bg_item, image=self._bg_photo)

    def get_text(self):
        try:
            return self.text.get("1.0", "end").strip()
        except Exception:
            return ""

    def clear(self):
        try:
            self.text.delete("1.0", "end")
        except Exception:
            pass


class _EmbeddedCard:
    """把 `_make_card_window` 的"窗口"伪装成面板里的一个页面。

    用法：调用方设 `self._cc_embed_target = <页面 Frame>` 再调原来的对话框函数，
    `_make_card_window` 发现该标记就把内容建到页面里，并把本对象当窗口返回。
    对话框里那些 `win.destroy()` / `win.grab_set()` / `win.geometry()` 全部接住，
    所以**原来的 16 个设置窗一个字都不用改**就能嵌进右侧。
    """

    def __init__(self, host, on_destroy):
        self._host = host
        self._on_destroy = on_destroy
        self._alive = True

    # —— 会改变行为的 ——
    def destroy(self):
        if self._alive:
            self._alive = False
            try:
                self._on_destroy()
            except Exception:
                pass

    def after(self, ms, func=None, *args):
        try:
            return self._host.after(ms, func, *args)
        except Exception:
            return None

    def winfo_exists(self):
        try:
            return int(self._alive and bool(self._host.winfo_exists()))
        except Exception:
            return 0

    def winfo_x(self):
        try:
            return self._host.winfo_rootx()
        except Exception:
            return 0

    def winfo_y(self):
        try:
            return self._host.winfo_rooty()
        except Exception:
            return 0

    def winfo_width(self):
        try:
            return self._host.winfo_width()
        except Exception:
            return 0

    def winfo_height(self):
        try:
            return self._host.winfo_height()
        except Exception:
            return 0

    def update_idletasks(self):
        try:
            self._host.update_idletasks()
        except Exception:
            pass

    # —— 纯空实现（嵌进面板后没有窗口语义） ——
    def grab_set(self, *a, **k):
        pass

    def grab_release(self, *a, **k):
        pass

    def grab_current(self):
        return None

    def geometry(self, *a, **k):
        pass

    def title(self, *a, **k):
        pass

    def attributes(self, *a, **k):
        pass

    def transient(self, *a, **k):
        pass

    def overrideredirect(self, *a, **k):
        pass

    def resizable(self, *a, **k):
        pass

    def minsize(self, *a, **k):
        pass

    def maxsize(self, *a, **k):
        pass

    def protocol(self, *a, **k):
        pass

    def lift(self, *a, **k):
        pass

    def lower(self, *a, **k):
        pass

    def focus_force(self, *a, **k):
        pass

    def focus_set(self, *a, **k):
        pass

    def deiconify(self, *a, **k):
        pass

    def withdraw(self, *a, **k):
        pass

    def bind(self, *a, **k):
        pass

    def unbind(self, *a, **k):
        pass

    def config(self, *a, **k):
        pass

    configure = config


class RoundedButton(tk.Canvas):
    """自绘圆角按钮（Win11 风格）：PIL 平滑圆角图片 + hover/按下反馈。
    图形只构建一次，hover/按下仅换图片颜色（itemconfigure），绝不 delete 重建，
    避免 Tk 为被删/重建 item 连续合成 Enter/Leave 事件造成死循环。
    variant: primary（品牌紫填充）/ subtle（白底细边框）/ danger（红）。"""
    def __init__(self, master, text, command=None, width=100, height=36, radius=None,
                 variant="primary", bg=None, fg=None, border=None, font=None,
                 parent_bg=CARD_BG, wrap_width=None):
        if radius is None:
            radius = 6
        super().__init__(master, width=width, height=height, highlightthickness=0, bd=0, bg=parent_bg)
        self.config(cursor="hand2")
        if variant == "subtle":
            bg = bg or "#ffffff"; fg = fg or TEXT_MAIN; border = border or INPUT_BORDER2
        elif variant == "danger":
            bg = bg or DANGER_RED; fg = fg or "#ffffff"
        else:
            bg = bg or BTN_PRIMARY; fg = fg or BTN_PRIMARY_TX
        self._text = text
        self._command = command
        self._bg = bg
        self._fg = fg
        self._border = border
        self._radius = radius
        self._font = font or ("TkDefaultFont", 10)
        self._wrap_width = wrap_width
        self._enabled = True
        self._hover = False
        self._press = False
        self._body_photo = None
        self._shadow_photo = None
        self._build()
        self._apply_style()
        self.tag_bind('all', '<Enter>', lambda e: self._set_hover(True))
        self.tag_bind('all', '<Leave>', lambda e: self._set_hover(False))
        self.tag_bind('all', '<ButtonPress-1>', lambda e: self._set_press(True))
        self.tag_bind('all', '<ButtonRelease-1>', lambda e: self._release())

    def _build(self):
        w = int(self.cget('width'))
        h = int(self.cget('height'))
        r = max(2, min(self._radius, w // 2 - 2, h // 2 - 2))
        self._r = r
        self._shadow_photo = _rounded_rect_photo(w - 4, h - 2, r, _shade_color(self._bg, 0.93))
        self._shadow_item = self.create_image(2, 2, anchor='nw', image=self._shadow_photo)
        self._body_photo = _rounded_rect_photo(w, h, r, self._bg,
                                               border_color=self._border or _shade_color(self._bg, 0.92),
                                               border_width=1)
        self._body_item = self.create_image(0, 0, anchor='nw', image=self._body_photo)
        text_kw = {}
        if self._wrap_width:
            text_kw["width"] = self._wrap_width
            text_kw["justify"] = "center"
        self._text_id = self.create_text(w // 2, h // 2, text=self._text, font=self._font,
                                         fill=self._fg, **text_kw)

    def _apply_style(self):
        cur = self._bg
        border = self._border or _shade_color(cur, 0.92)
        tx = self._fg
        if not self._enabled:
            cur = "#f3f4f6"; border = "#e5e8ec"; tx = TEXT_DISABLED
        elif self._press:
            cur = _shade_color(cur, 0.88)
        elif self._hover:
            cur = _shade_color(cur, 0.94)
        w = int(self.cget('width'))
        h = int(self.cget('height'))
        self._body_photo = _rounded_rect_photo(w, h, self._r, cur, border_color=border, border_width=1)
        self.itemconfigure(self._body_item, image=self._body_photo)
        self.itemconfigure(self._text_id, fill=tx)
        self._shadow_photo = _rounded_rect_photo(w - 4, h - 2, self._r, _shade_color(cur, 0.93))
        self.itemconfigure(self._shadow_item, image=self._shadow_photo)
        self.coords(self._text_id, w // 2, h // 2 + (1 if self._press else 0))

    def set_variant(self, variant):
        """运行中切换按钮样式（primary=品牌紫填充 / subtle=白底 / danger=红），用于选中态切换"""
        if variant == "subtle":
            self._bg, self._fg, self._border = "#ffffff", TEXT_MAIN, INPUT_BORDER2
        elif variant == "danger":
            self._bg, self._fg, self._border = DANGER_RED, "#ffffff", None
        else:
            self._bg, self._fg, self._border = BTN_PRIMARY, BTN_PRIMARY_TX, None
        self._apply_style()

    def _set_hover(self, on):
        if not self._enabled:
            return
        if self._hover != on:
            self._hover = on
            self._apply_style()

    def _set_press(self, on):
        if not self._enabled:
            return
        if self._press != on:
            self._press = on
            self._apply_style()

    def _release(self):
        was_press = self._press
        self._press = False
        self._apply_style()
        if was_press and self._hover and self._enabled and self._command:
            try:
                self._command()
            except Exception:
                pass

    def set_text(self, text):
        self._text = text
        self.itemconfigure(self._text_id, text=text)

    def set_enabled(self, enabled):
        """启用/禁用按钮：禁用时置灰、不响应 hover/点击"""
        self._enabled = bool(enabled)
        if not self._enabled:
            self._hover = False
            self._press = False
        self._apply_style()

class RoundedEntry(tk.Canvas):
    """自绘圆角输入框（Win11 风格）：PIL 平滑圆角背景 + 内嵌无边框 Entry，
    聚焦时描边变品牌紫，点击空白处也能聚焦。"""
    def __init__(self, master, textvariable=None, width=260, height=32, radius=None,
                 bg="#ffffff", border=INPUT_BORDER2, fg=TEXT_MAIN,
                 font=None, parent_bg=CARD_BG, show=None, insert_bg=BTN_PRIMARY, justify="left"):
        if radius is None:
            radius = 6
        super().__init__(master, width=width, height=height, highlightthickness=0, bd=0, bg=parent_bg)
        r = max(2, min(radius, width // 2 - 2, height // 2 - 2))
        self._r = r
        self._bg = bg
        self._border = border
        self._focused = False
        self._bg_photo = _rounded_rect_photo(width, height, r, bg, border_color=border, border_width=1)
        self._bg_item = self.create_image(0, 0, anchor='nw', image=self._bg_photo)
        pad = max(10, r + 3)
        self.entry = tk.Entry(self, textvariable=textvariable, bd=0, relief=tk.FLAT,
                              highlightthickness=0, bg=bg, fg=fg,
                              insertbackground=insert_bg, font=font or ("TkDefaultFont", 10),
                              show=show or "", justify=justify)
        self.create_window(pad, height // 2, anchor='w', window=self.entry,
                           width=width - 2 * pad, height=height - 6)
        self.entry.bind("<FocusIn>", lambda e: self._set_focus(True), add="+")
        self.entry.bind("<FocusOut>", lambda e: self._set_focus(False), add="+")
        # 点击输入框空白处也聚焦；若窗口未激活则先激活（否则键盘输入不可达）
        self.tag_bind("all", "<Button-1>", self._on_canvas_click)

    def _on_canvas_click(self, e):
        try:
            self.winfo_toplevel().focus_force()
        except Exception:
            pass
        self.entry.focus_set()

    def _set_focus(self, on):
        if self._focused == on:
            return
        self._focused = on
        self._bg_photo = _rounded_rect_photo(int(self.cget('width')), int(self.cget('height')),
                                             self._r, self._bg,
                                             border_color=(BTN_PRIMARY if on else self._border),
                                             border_width=1)
        self.itemconfigure(self._bg_item, image=self._bg_photo)

    def get(self):
        return self.entry.get()

    def set(self, value):
        self.entry.delete(0, tk.END)
        self.entry.insert(0, value)

    def focus(self):
        self.entry.focus_set()

# ------------------------------- Win11 风格自绘菜单 ---------------------------------
class ModernMenu:
    """Win11 风格自绘弹出菜单：白色圆角卡片、条目悬停高亮、级联子菜单、禁用态。
    兼容 tk.Menu 常用 API（add_command/add_cascade/add_separator/index/entryconfigure），
    与旧菜单构建代码无缝替换。"""
    ACTIVE = set()   # 当前打开的所有菜单窗口（含子菜单）

    def __init__(self, master, tearoff=0, bg=None, fg=None, activebackground=None,
                 font=None, pet=None):
        self.master = master
        self.pet = pet
        self.items = []
        self._parent = None
        self._win = None
        self._canvas = None
        self._photos = []
        self._hover_idx = None
        self._child = None
        self._child_for = None
        self._child_job = None
        self._close_job = None
        self._focus_out_job = None
        self._pos = (0, 0)
        self._w = 0
        self._item_rects = []
        self._item_h = 20
        self._pad_x = 10
        self._font = None

    # ---------- 构建 API（兼容 tk.Menu） ----------
    def add_command(self, label, command=None, **kw):
        self.items.append({"type": "command", "label": label, "command": command,
                           "disabled": kw.get("state") == "disabled"})

    def add_cascade(self, label, menu=None, **kw):
        self.items.append({"type": "cascade", "label": label, "menu": menu})

    def add_separator(self):
        self.items.append({"type": "separator"})

    def index(self, what):
        if what == "end":
            return len(self.items) - 1
        try:
            return int(what)
        except Exception:
            return -1

    def entryconfigure(self, index, **kw):
        try:
            it = self.items[int(index)]
        except Exception:
            return
        if "label" in kw:
            it["label"] = kw["label"]
        if "state" in kw:
            it["disabled"] = kw["state"] == "disabled"
        if it.get("type") == "command" and "command" in kw:
            it["command"] = kw["command"]
        if self._win is not None:
            try:
                self._render_items()
            except Exception:
                pass

    def set_parent(self, parent):
        self._parent = parent

    # ---------- 点击外部自动收起 ----------
    def _on_focus_out(self, e):
        # 延迟确认：子菜单打开瞬间可能短暂失焦，确认焦点已不在菜单树内再关闭
        if self._focus_out_job:
            try:
                self.master.after_cancel(self._focus_out_job)
            except Exception:
                pass
        self._focus_out_job = self.master.after(150, self._confirm_focus_out)

    def _confirm_focus_out(self):
        self._focus_out_job = None
        if self._win is None:
            return
        try:
            fw = self.master.focus_get()
        except Exception:
            fw = None
        if fw is not None:
            try:
                tl = fw.winfo_toplevel()
            except Exception:
                tl = None
            if tl in ModernMenu.ACTIVE:
                return  # 焦点仍在菜单树内（如子菜单），不关闭
        self.hide_all()

    # ---------- 布局与渲染 ----------
    def _measure(self):
        s = self.pet._dpi_scale
        f = tkfont.Font(root=self.master, family=self.pet.font_family, size=10)
        item_h = int(34 * s)
        pad_x = int(12 * s)
        pad_y = int(6 * s)
        width = 0
        height = pad_y * 2
        for it in self.items:
            if it["type"] == "separator":
                height += int(9 * s)
                continue
            w = f.measure(it["label"]) + pad_x * 2 + int(22 * s)
            width = max(width, w)
            height += item_h
        width = max(int(176 * s), width)
        return width, height, item_h, pad_x, pad_y, f

    def _build_window(self, x, y):
        s = self.pet._dpi_scale
        width, height, item_h, pad_x, pad_y, f = self._measure()
        self._w = width
        sw, sh = self.pet._screen_w, self.pet._screen_h
        x = max(4, min(x, sw - width - 8))
        y = max(4, min(y, sh - height - 8))
        win = tk.Toplevel(self.master)
        win.overrideredirect(True)
        win.configure(bg=CARD_MASK)
        win.attributes("-transparentcolor", CARD_MASK)
        win.attributes("-topmost", True)
        canvas = tk.Canvas(win, width=width, height=height, highlightthickness=0, bd=0, bg=CARD_MASK)
        canvas.pack()
        self._photos.append(_card_photo(width, height, max(8, int(10 * s))))
        canvas.create_image(0, 0, anchor="nw", image=self._photos[-1])
        self._canvas = canvas
        self._win = win
        self._pos = (x, y)
        win.geometry(f"+{x}+{y}")
        ModernMenu.ACTIVE.add(win)
        win.bind("<Destroy>", lambda e: ModernMenu.ACTIVE.discard(win), add="+")
        win.bind("<Escape>", lambda e: self.hide_all())
        # 获取焦点并监听失焦：点击任意外部区域（含桌面/其他应用）→ 自动收起
        win.bind("<FocusOut>", self._on_focus_out)
        try:
            win.focus_force()
        except Exception:
            pass
        # 条目命中区
        self._item_rects = []
        y0 = pad_y
        for i, it in enumerate(self.items):
            if it["type"] == "separator":
                y0 += int(9 * s)
                continue
            self._item_rects.append((y0, y0 + item_h, i))
            y0 += item_h
        self._item_h = item_h
        self._pad_x = pad_x
        self._font = f
        canvas.bind("<Motion>", self._on_motion)
        canvas.bind("<Enter>", self._on_enter)
        canvas.bind("<Leave>", self._on_leave)
        canvas.bind("<Button-1>", self._on_click)
        canvas.bind("<Button-3>", lambda e: self.hide_all())
        self._render_items()

    def _render_items(self):
        s = self.pet._dpi_scale
        canvas = self._canvas
        if canvas is None:
            return
        canvas.delete("item_*")
        item_h = self._item_h
        pad_x = self._pad_x
        y0 = int(6 * s)
        item_w = self._w - int(12 * s)
        for i, it in enumerate(self.items):
            if it["type"] == "separator":
                canvas.create_line(int(10 * s), y0 + int(4 * s), self._w - int(10 * s), y0 + int(4 * s),
                                   fill=DIVIDER, tags="item_*")
                y0 += int(9 * s)
                continue
            disabled = it.get("disabled", False)
            if i == self._hover_idx and not disabled:
                photo = _rounded_rect_photo(item_w, item_h, int(6 * s), HOVER_BG)
                self._photos.append(photo)
                canvas.create_image(int(6 * s), y0, anchor="nw", image=photo, tags="item_*")
            fg = TEXT_DISABLED if disabled else TEXT_MAIN
            canvas.create_text(pad_x, y0 + item_h // 2, anchor="w", text=it["label"],
                               font=self._font, fill=fg, tags="item_*")
            if it["type"] == "cascade":
                canvas.create_text(self._w - int(6 * s), y0 + item_h // 2, anchor="e",
                                   text="›", font=(self.pet.font_family, int(12 * s)),
                                   fill=TEXT_SUB, tags="item_*")
            y0 += item_h

    # ---------- 事件 ----------
    def _idx_at(self, e):
        for top, bottom, i in self._item_rects:
            if top <= e.y < bottom:
                return i
        return None

    def _on_motion(self, e):
        i = self._idx_at(e)
        if i != self._hover_idx:
            self._hover_idx = i
            self._render_items()
        if self._child_job:
            try:
                self.master.after_cancel(self._child_job)
            except Exception:
                pass
            self._child_job = None
        it = self.items[i] if i is not None else None
        if it is not None and it["type"] == "cascade" and not it.get("disabled"):
            if self._child_for != i:
                self._child_job = self.master.after(160, lambda: self._open_child(i))
        elif self._child is not None:
            # 移到普通条目：关闭子菜单（Win11 行为）
            self._close_child()

    def _on_enter(self, e):
        # 指针移入本菜单（如子菜单）时，取消父菜单的关闭调度，保证父→子移动不闪断
        if self._parent is not None:
            self._parent._cancel_close_child()

    def _on_leave(self, e):
        if self._hover_idx is not None:
            self._hover_idx = None
            self._render_items()
        self._schedule_close_child()

    def _schedule_close_child(self):
        if self._close_job:
            try:
                self.master.after_cancel(self._close_job)
            except Exception:
                pass
        self._close_job = self.master.after(350, self._close_child)

    def _cancel_close_child(self):
        if self._close_job:
            try:
                self.master.after_cancel(self._close_job)
            except Exception:
                pass
            self._close_job = None

    def _close_child(self):
        self._cancel_close_child()
        if self._child is not None:
            c, self._child = self._child, None
            self._child_for = None
            c.hide(close_children=True)

    def _open_child(self, i):
        self._child_job = None
        if self._child is not None:
            self._close_child()
        it = self.items[i]
        child = it.get("menu")
        if child is None or self._win is None:
            return
        child.set_parent(self)
        # _item_rects 是压缩列表（分隔符不入列），必须线性查找 items 索引对应的矩形
        rect = None
        for r in self._item_rects:
            if r[2] == i:
                rect = r
                break
        if rect is None:
            return
        top = rect[0]
        s = self.pet._dpi_scale
        x = self._pos[0] + self._w - int(1 * s)
        y = self._pos[1] + top - int(6 * s)
        cw = child._w or child._measure()[0]
        if x + cw > self.pet._screen_w - 8:
            x = self._pos[0] - cw + int(1 * s)
        child.show(x, y)
        self._child = child
        self._child_for = i

    def _on_click(self, e):
        i = self._idx_at(e)
        if i is None:
            self.hide_all()
            return
        it = self.items[i]
        if it.get("disabled"):
            return
        if it["type"] == "cascade":
            if self._child_for != i:
                self._open_child(i)
            return
        cmd = it.get("command")
        self.hide_all()
        if cmd:
            try:
                cmd()
            except Exception:
                pass

    # ---------- 显示 / 关闭 ----------
    def show(self, x, y):
        self.hide()
        self._hover_idx = None
        self._build_window(x, y)

    def hide(self, close_children=True):
        if close_children:
            self._close_child()
        if self._child_job:
            try:
                self.master.after_cancel(self._child_job)
            except Exception:
                pass
            self._child_job = None
        if self._focus_out_job:
            try:
                self.master.after_cancel(self._focus_out_job)
            except Exception:
                pass
            self._focus_out_job = None
        if self._win is not None:
            try:
                self._win.destroy()
            except Exception:
                pass
            self._win = None
            self._canvas = None

    def hide_all(self):
        """关闭整棵菜单树并通知宠物恢复置顶"""
        self.hide()
        for w in list(ModernMenu.ACTIVE):
            try:
                w.destroy()
            except Exception:
                pass
        ModernMenu.ACTIVE.clear()
        if self.pet is not None:
            try:
                self.pet._on_menu_closed()
            except Exception:
                pass

# ------------------------------- 独立气泡窗口 ---------------------------------
class BubbleWindow:
    def __init__(self, master, pet_instance):
        self.master = master
        self.pet = pet_instance
        self.window = None
        self.canvas = None
        self.visible = False
        self.text_full = ""
        self.text_index = 0
        self.typing_job = None
        self.display_timer = None
        self.waiting_for_next = False
        self._last_click_time = 0
        self.bubble_font = None
        self._bubble_font_size = None
        self._bubble_width = 100
        self._bubble_height = 50
        # Win11 卡片底图缓存（尺寸变化时才重新生成，打字逐字刷新只更新文字）
        self._bubble_photo = None
        self._last_bw = 0
        self._last_bh = 0
        # 本轮输出是否“对用户输入的回应”（完毕时刷新免唤醒词窗口）
        self._refresh_voice = False

    def create_window(self):
        if self.window is not None:
            self.destroy()
        self.window = tk.Toplevel(self.master)
        self.window.overrideredirect(True)
        self.window.attributes("-topmost", True)
        self.window.attributes("-transparentcolor", TRANS_MASK)
        self.window.configure(bg=TRANS_MASK)
        self.canvas = tk.Canvas(self.window, highlightthickness=0, bg=TRANS_MASK)
        self.canvas.pack(fill=tk.BOTH, expand=True)
        self.canvas.bind("<Button-1>", self.on_click)
        self.visible = True
        self.update_font()
        # 穿透开着时新建的气泡也要立刻不吃鼠标
        self.apply_click_through(bool(getattr(self.pet, "_click_through", False)))

    def apply_click_through(self, enabled):
        """点击穿透期间让气泡也不抢鼠标（WS_EX_TRANSPARENT）。

        穿透原本只作用在角色那层分层窗口上，气泡是独立 Toplevel，
        盖在屏幕上照样吃点击 —— 这里单独给它加/去这个扩展样式。
        """
        try:
            if not self.window:
                return
            user32 = ctypes.windll.user32
            hwnd = user32.GetParent(self.window.winfo_id()) or self.window.winfo_id()
            GWL_EXSTYLE = -20
            WS_EX_TRANSPARENT = 0x00000020
            style = user32.GetWindowLongW(hwnd, GWL_EXSTYLE)
            new = (style | WS_EX_TRANSPARENT) if enabled else (style & ~WS_EX_TRANSPARENT)
            user32.SetWindowLongW(hwnd, GWL_EXSTYLE, new)
            # NOMOVE|NOSIZE|NOACTIVATE|FRAMECHANGED：让新样式立刻生效
            user32.SetWindowPos(hwnd, 0, 0, 0, 0, 0, 0x0002 | 0x0001 | 0x0010 | 0x0020)
        except Exception as e:
            log.debug("气泡点击穿透设置失败: %s", e)

    def update_font(self):
        # 复用字体对象，避免打字过程中逐字新建 Tk Font 导致资源泄漏
        font_size = self.pet.bubble_font_size
        if self.bubble_font is None or self._bubble_font_size != font_size:
            self.bubble_font = tkfont.Font(family=self.pet.font_family, size=font_size)
            self._bubble_font_size = font_size

    def _emoji_photo(self, ch, line_height):
        """把 emoji 渲染成贴图（带缓存）；同一尺寸只渲一次。"""
        try:
            # 组合 emoji（😮‍💨 这类 ZWJ 序列）PIL 不会做字形组合，会把两半分开画成怪图；
            # 只取第一部分渲染，看起来仍是一个正常表情。
            if chr(0x200D) in ch:
                ch = ch.split(chr(0x200D))[0]
            size = max(12, int(line_height) - 4)
            key = (ch, size)
            cache = getattr(self, "_emoji_cache", None)
            if cache is None:
                cache = {}
                self._emoji_cache = cache
            if key in cache:
                return cache[key]
            img = render_emoji_image(ch, size)
            if img is None:
                cache[key] = None
                return None
            photo = ImageTk.PhotoImage(img, master=self.canvas)
            cache[key] = photo
            return photo
        except Exception as e:
            log.debug("emoji 渲染失败: %s", e)
            return None

    def destroy(self):
        if self.typing_job and self.window:
            try: self.window.after_cancel(self.typing_job)
            except Exception: pass
        if self.display_timer and self.window:
            try: self.window.after_cancel(self.display_timer)
            except Exception: pass
        if self.window:
            self.window.destroy()
            self.window = None
        self.visible = False

    def show_text(self, full_text, refresh_voice=False):
        if not self.visible:
            self.create_window()
        if self.typing_job:
            self.window.after_cancel(self.typing_job)
        if self.display_timer:
            self.window.after_cancel(self.display_timer)
        self.text_full = full_text
        self.text_index = 0
        self.waiting_for_next = False
        # 本轮输出是否属于“对用户输入的回应”（输出完毕时刷新免唤醒词窗口）
        self._refresh_voice = refresh_voice
        self.update_bubble_size("")
        self.type_next_char()
        self.position_window()

    def position_window(self):
        if not self.window or not self.visible:
            return
        x = self.master.winfo_x()
        y = self.master.winfo_y()
        bubble_width = self._bubble_width
        bubble_height = self._bubble_height
        win_x = x + (self.master.winfo_width() - bubble_width) // 2
        win_y = y + 8 - bubble_height
        self.window.geometry(f"+{win_x}+{win_y}")

    def update_bubble_size(self, current_text):
        if not self.canvas:
            return
        self.update_font()
        max_width = self.pet.bubble_max_width
        lines = self.wrap_text(current_text, max_width - 15)  # -15 补偿CJK标点测量误差
        if not lines:
            lines = [""]
        line_widths = [self.bubble_font.measure(line) for line in lines]
        max_line_width = max(line_widths) if line_widths else 0
        bubble_width = min(max_width, max_line_width) + 30
        bubble_width = max(50, bubble_width)
        line_height = self.bubble_font.metrics("linespace") + 4
        text_height = len(lines) * line_height
        bubble_height = text_height + 28
        r = 14

        self._bubble_width = bubble_width + 16
        self._bubble_height = bubble_height + 20

        # Win11 卡片风格：PIL 超采样底图（柔影 + 白底 + 细边框 + 底部箭头）。
        # 尺寸变化才重建底图；打字逐字刷新只更新文字，避免每次 PIL 生成卡顿。
        if self._bubble_photo is None or (bubble_width, bubble_height) != (self._last_bw, self._last_bh):
            self.canvas.delete("all")
            self._bubble_photo = _bubble_photo(bubble_width, bubble_height, r)
            self.canvas.create_image(0, 0, anchor='nw', image=self._bubble_photo)
            self._last_bw, self._last_bh = bubble_width, bubble_height
        else:
            self.canvas.delete("text_*")
        y_offset = 14
        self._emoji_photos = []          # 本次刷新用到的 emoji 图（防 GC）
        for line in lines:
            self.canvas.create_text(18, y_offset, anchor='nw', text=line, font=self.bubble_font,
                                    fill=TEXT_MAIN, tags="text_*")
            # 11/15：emoji 用彩色小图盖在文字上面（雅黑没有 emoji 字形，Tk 只能画黑白轮廓）
            try:
                for m in EMOJI_RE.finditer(line or ""):
                    raw = m.group(0)
                    if not raw.strip():
                        continue
                    ex = 18 + self.bubble_font.measure(line[:m.start()])
                    # 底色要盖住 Tk 自己画的那份（雅黑缺字 → 系统会画出黑白轮廓，
                    # 而且组合 emoji 会占两个字的宽度），所以按**文字推进宽度**盖，不按图宽
                    adv = max(1, self.bubble_font.measure(raw))
                    ph = self._emoji_photo(raw, line_height)
                    if ph is None:
                        continue
                    self.canvas.create_rectangle(ex, y_offset, ex + adv,
                                                 y_offset + line_height, fill="#ffffff",
                                                 outline="", tags="text_*")
                    self.canvas.create_image(ex + adv // 2, y_offset + line_height // 2,
                                             anchor="center", image=ph, tags="text_*")
                    self._emoji_photos.append(ph)
            except Exception as e:
                log.debug("气泡 emoji 贴图失败: %s", e)
            y_offset += line_height

        self.canvas.config(width=self._bubble_width, height=self._bubble_height)
        self.position_window()

    def wrap_text(self, text, max_width):
        if not text:
            return [""]
        lines = []
        # 先按显式换行分段，再对每段逐字测宽折行——内嵌 \n 不再混进同一行
        for para in text.split("\n"):
            current_line = ""
            for ch in para:
                test_line = current_line + ch
                if self.bubble_font.measure(test_line) <= max_width:
                    current_line = test_line
                else:
                    if current_line:
                        lines.append(current_line)
                    current_line = ch
            if current_line:
                lines.append(current_line)
        return [l for l in lines if l.strip() or l == ""]

    def type_next_char(self):
        if self.text_index < len(self.text_full):
            new_text = self.text_full[:self.text_index+1]
            self.update_bubble_size(new_text)
            self.text_index += 1
            self.typing_job = self.window.after(50, self.type_next_char)
        else:
            self.typing_job = None
            self.waiting_for_next = True
            self.display_timer = self.window.after(10000, self.fade_out)
            # 气泡输出完毕 → 若是“对用户输入的回应”则刷新免唤醒词窗口
            refresh = self._refresh_voice
            self._refresh_voice = False
            try:
                self.pet._on_output_finished(refresh)
            except Exception:
                pass

    def on_click(self, event):
        if not self.visible:
            return
        self.pet.last_interaction_time = time.time()
        if self.typing_job:
            self.window.after_cancel(self.typing_job)
            self.typing_job = None
            self.update_bubble_size(self.text_full)
            self.text_index = len(self.text_full)
            if self.display_timer:
                self.window.after_cancel(self.display_timer)
            self.display_timer = self.window.after(10000, self.fade_out)
        else:
            if time.time() - self._last_click_time < 0.5:
                return
            self._last_click_time = time.time()
            if self.waiting_for_next:
                self.fade_out()

    def fade_out(self):
        if self.display_timer:
            self.window.after_cancel(self.display_timer)
            self.display_timer = None
        self.text_full = ""
        self.text_index = 0
        self.waiting_for_next = False
        self.destroy()
        try: self.pet.restore_expression()
        except Exception: pass

# ------------------------------- 本地语音识别插件 ---------------------------------
class SileroVAD:
    """基于 onnxruntime 的 silero VAD（语音活动检测）。
    sherpa-onnx 1.12.x 的 VAD 绑定对 k2-fsa 导出的 x/h/c 模型无输出，
    这里直接用 ORT 推理该模型并自行分段：连续语音窗口累积成段，
    静音超过 min_silence_duration 结束一段；短于 min_speech_duration 的段丢弃
    （风扇/咀嚼/键盘等非语音噪音不会形成有效段）。"""
    def __init__(self, model_path, sample_rate=16000, threshold=0.5,
                 min_silence_duration=0.8, min_speech_duration=0.25, window_size=512):
        import onnxruntime as ort
        # 10/16：ORT 的线程池默认按**逻辑核数**建，且 `session.intra_op.allow_spinning` 默认 true
        # （干完一个任务原地自旋等下一个）。VAD 每 ~32ms 就被喂一次音频 ⇒ 池子永远等不到休眠，
        # 实测空转烧掉 13 个核（20 核机器），一玩游戏就卡。VAD 是 1MB 的小模型，单线程足够。
        _so = ort.SessionOptions()
        _so.intra_op_num_threads = 1
        try:
            _so.add_session_config_entry("session.intra_op.allow_spinning", "0")
        except Exception as e:
            log.warning("VAD 关闭线程池自旋失败（继续）: %s", e)
        self.sess = ort.InferenceSession(model_path, _so, providers=["CPUExecutionProvider"])
        self.threshold = threshold
        self.window_size = window_size
        self.min_silence_frames = max(1, int(min_silence_duration * sample_rate / window_size))
        self.min_speech_samples = int(min_speech_duration * sample_rate)
        self.h = np.zeros((2, 1, 64), dtype=np.float32)
        self.c = np.zeros((2, 1, 64), dtype=np.float32)
        self._buf = []
        self._seg = []
        self._silence = 0
        self._in_speech = False
        self._segments = []

    def accept_waveform(self, samples):
        """samples: float32 [-1,1]，任意长度；内部按窗口切分推理"""
        self._buf.extend(samples)
        win = self.window_size
        while len(self._buf) >= win:
            x = np.asarray(self._buf[:win], dtype=np.float32).reshape(1, -1)
            del self._buf[:win]
            prob, self.h, self.c = self.sess.run(None, {"x": x, "h": self.h, "c": self.c})
            if float(prob[0][0]) >= self.threshold:
                self._seg.extend(x[0])
                self._silence = 0
                self._in_speech = True
            elif self._in_speech:
                self._seg.extend(x[0])
                self._silence += 1
                if self._silence >= self.min_silence_frames:
                    seg = np.asarray(self._seg, dtype=np.float32)
                    self._seg = []
                    self._in_speech = False
                    self._silence = 0
                    if len(seg) >= self.min_speech_samples:
                        self._segments.append(seg)

    def empty(self):
        return not self._segments

    def pop(self):
        """取出一个完成的语音段（float32 [-1,1]）"""
        return self._segments.pop(0)


def _speech_start(vad, n_samples, sample_rate, t_pop):
    """由"语音段被取走的时刻"反推这段话**开口**的时刻。

    VAD 要等连续 min_silence_duration 的静音才封段，所以段尾固定含一段静音：
        tail       = 封段所需静音时长
        说完       ≈ t_pop − tail
        开口       ≈ 说完 −（段长 − tail）
    用途：免唤醒窗口的判据要用"开口时刻"，否则比开口晚 ~0.6 秒（BUG1）。
    """
    tail = 0.0
    if vad is not None:
        tail = (vad.min_silence_frames * vad.window_size) / float(sample_rate)
    dur = n_samples / float(sample_rate)
    return t_pop - tail - max(0.0, dur - tail)


class LocalParaformerSTT:
    """本地语音识别（sherpa-onnx Paraformer 离线中文 + silero VAD）：
    双线程架构——录音循环用 VAD 检测语音段（过滤风扇/咀嚼等非语音噪音），
    转写循环用 Paraformer 离线识别整段。"""
    SAMPLE_RATE = 16000

    def __init__(self, callback=None, root=None, dispatcher=None, pet=None):
        self.callback = callback
        self.root = root
        self.dispatcher = dispatcher  # 主线程任务投递器（thread-safe）
        self.pet = pet  # 用于动态读取唤醒词（系统提示词中的角色姓名）
        self.recognizer = None
        self.vad = None
        self.recording = False
        self.muted = False  # 宠物自己 TTS 说话时静音，避免“听见自己”
        self.audio_queue = queue.Queue()
        self.wake_window = DEFAULT_WAKE_WINDOW   # 免唤醒窗口秒数（0 = 关闭，由 App 从设置推过来）
        self.ready = False
        self.load_failed = False
        # 会话窗：唤醒后这段时间内说话无需再喊名字，超时自动回到待唤醒
        self._active_until = 0.0
        threading.Thread(target=self._init_model, daemon=True).start()

    def set_muted(self, on):
        if self.muted != bool(on):
            log.info("STT 静音切换: muted=%s", bool(on))
        self.muted = bool(on)

    def set_wake_window(self, seconds):
        """设置免唤醒窗口秒数（0 = 关闭：每次说话都要先喊名字）"""
        try:
            v = float(seconds)
        except (TypeError, ValueError):
            v = DEFAULT_WAKE_WINDOW
        self.wake_window = max(0.0, min(v, 60.0))
        if self.wake_window <= 0:
            self._active_until = 0.0        # 关掉时立刻失效，别让旧窗口继续生效
        log.info("免唤醒窗口: %s", "关闭" if self.wake_window <= 0 else "%.1f 秒" % self.wake_window)

    def refresh_window(self):
        """刷新免唤醒词窗口（宠物输出完毕 / 说话 / 唤醒时调用）；窗口为 0（关闭）时什么都不做"""
        if self.wake_window <= 0:
            self._active_until = 0.0
            return
        self._active_until = time.time() + self.wake_window

    def window_left(self):
        """窗口剩余秒数（<=0 表示已关闭/已过期）"""
        return self._active_until - time.time()

    def clear_window(self):
        """立刻关掉免唤醒窗口（关语音时用：否则下次打开语音，那个旧窗口还会接着生效）"""
        self._active_until = 0.0

    def hold_open(self, seconds=0.35):
        """按键说话：按住期间把窗口顶住（松开后 0.35 秒内自然失效）。

        比配置的窗口短得多 —— 它就是"按住才开"，松开即关。
        用 max 是为了不去缩短一个本来就更长的窗口（比如刚说完话的 8 秒免唤醒期）。
        """
        self._active_until = max(self._active_until, time.time() + float(seconds))

    CONVERSATION_WINDOW = DEFAULT_WAKE_WINDOW   # 兼容旧引用：默认窗口长度

    _WAKE_FILLER = "斯丝寺嘶酱呀啊呢嘛吧的~ 喂嗯呃哦哎"   # 名字后面粘的称呼尾字
    _WAKE_HEAD_FILLER = _WAKE_FILLER + "那个"              # 名字前面只可能是这些语气词（"那个大肥鱼…"）
    _PINYIN_INITIALS = ("zh", "ch", "sh", "b", "p", "m", "f", "d", "t", "n", "l",
                        "g", "k", "h", "j", "q", "x", "r", "z", "c", "s", "y", "w")

    @property
    def wake_name(self):
        """唤醒词全名 = 系统提示词中的角色姓名（动态读取——改名后立即生效）"""
        name = ""
        if self.pet is not None:
            try:
                name = self.pet.pet_name or ""
            except Exception:
                name = ""
        return name or DEFAULT_PET_NAME

    @property
    def wake_prefix(self):
        """唤醒词前 3 个字（汉字精确通道用；拼音通道用全名）"""
        return self.wake_name[:3]

    @property
    def _wake_patterns(self):
        """汉字通道要试的写法：全名优先，再退到前 3 个字。
        4 字名字必须试全名——只吃前 3 个字的话，"卡梅莉亚"会剩一个"亚"被当成内容发出去。"""
        name = self.wake_name
        return (name,) if len(name) <= 3 else (name, name[:3])

    def _strip_wake(self, text, idx, consumed):
        """去掉唤醒词（从 idx 起 consumed 个字），清理称呼尾字后返回剩余内容。

        只会在"名字处于句首附近（当称呼）"时被调用：名字后面还有话 ⇒ 名字前面的
        "喂/那个/嗯"不算内容；名字后面没话（"今天大肥鱼"）⇒ 前面那半句才是内容，得接回来。"""
        head = text[:idx]
        rest = text[idx + consumed:]
        while rest and rest[0] in self._WAKE_FILLER:
            rest = rest[1:]
        rest = rest.strip(" ，。！？,.!?~")
        if rest:
            while head and head[-1] in self._WAKE_HEAD_FILLER:
                head = head[:-1]
            content = (head + rest).strip(" ，。！？,.!?~")
        else:
            content = ""
        return content or None

    @staticmethod
    def _syllable_distance(a, b):
        """音节级编辑距离（"化肥鱼" vs "大肥鱼" = 1）"""
        m, n = len(a), len(b)
        dp = list(range(n + 1))
        for i in range(1, m + 1):
            prev, dp[0] = dp[0], i
            for j in range(1, n + 1):
                cur = dp[j]
                dp[j] = min(dp[j] + 1, dp[j - 1] + 1, prev + (a[i - 1] != b[j - 1]))
                prev = cur
        return dp[n]

    @classmethod
    def _final_of(cls, syllable):
        """取音节韵母（声母之后的部分）：da→a、hua→ua"""
        for ini in cls._PINYIN_INITIALS:
            if syllable.startswith(ini) and len(syllable) > len(ini):
                return syllable[len(ini):]
        return syllable

    @classmethod
    def _final_close(cls, a, b):
        """韵母是否相近（相同，或一方是另一方的后缀）：da↔hua 算近，da↔luo 不算。
        这一条是防误触发的关键——"老师们往那卡里打钱"里的"往那卡"就是靠它挡住的。"""
        fa, fb = cls._final_of(a), cls._final_of(b)
        return bool(fa) and bool(fb) and (fa == fb or fa.endswith(fb) or fb.endswith(fa))

    def _find_pinyin(self, text_py, pat_py, allow_fuzzy):
        """在整句音节里找 pat_py：完全同音，或（allow_fuzzy 且名字≥3音节时）只错一个近音音节。
        返回 (起始音节号, 听到的写法) 或 None。"""
        n = len(pat_py)
        if n == 0 or len(text_py) < n:
            return None
        end = len(text_py) - n
        limit = end if WAKE_ANYWHERE else min(5, end)
        for start in range(0, limit + 1):
            seg = text_py[start:start + n]
            if seg == pat_py:
                return (start, "".join(seg))
            if not (allow_fuzzy and n >= 3 and WAKE_TOLERANCE > 0):
                continue
            if self._syllable_distance(seg, pat_py) > WAKE_TOLERANCE:
                continue
            if WAKE_TAIL_LOCK and seg[-WAKE_TAIL_LOCK:] != pat_py[-WAKE_TAIL_LOCK:]:
                continue
            diff = [(x, y) for x, y in zip(seg, pat_py) if x != y]
            if len(diff) != 1:
                continue
            # 韵母闸门只在 3 音节名字上用：3 音节时末两个音节就是全部约束，剩下那个得"听起来像"；
            # 4 音节以上光靠"末两音节完全一致"已经够严（600 句真语料实测：去掉闸门误触发 0），
            # 而实测真误听里有"阿雷拉特←格雷拉特"（ge→a，韵母全变）这种，闸门会把它误挡。
            if len(pat_py) <= 3 and not self._final_close(diff[0][0], diff[0][1]):
                continue
            return (start, "".join(seg))
        return None

    def _pinyin_hit(self, text):
        """拼音通道：同音变体 / 只错一个近音音节 / 别名白名单。
        返回 (名字起始的**原文字符**下标, 名字占的原文字数) 或 None ——
        转写文本可能夹着数字和字母，音节序号和字符序号不是一回事。"""
        if not PINYIN_AVAILABLE:
            return None
        text_py = lazy_pinyin(text)
        han_idx = [i for i, ch in enumerate(text) if "\u4e00" <= ch <= "\u9fff"]
        if len(han_idx) != len(text_py):      # 生僻字/扩展区：逐字问 pypinyin 拿准确位置
            han_idx = [i for i, ch in enumerate(text) if lazy_pinyin(ch)]
        if len(han_idx) < len(text_py):
            return None
        name_py = lazy_pinyin(self.wake_name)
        # 别名属于"默认名"：只在桌宠还叫 DEFAULT_PET_NAME 时生效（改名后整套失效）
        aliases = WAKE_ALIASES if self.wake_name == DEFAULT_PET_NAME else ()
        patterns = [(name_py, True, None)] + [(lazy_pinyin(a), False, a) for a in aliases]
        for pat_py, fuzzy, alias in patterns:
            if len(pat_py) < 2:
                continue
            hit = self._find_pinyin(text_py, pat_py, fuzzy)
            if hit is None:
                continue
            start, heard = hit
            if alias is None:
                if heard != "".join(pat_py):    # 完全同音时不刷日志
                    log.info("语音唤醒：把「%s」当「%s」认（近音容错）", heard, "".join(pat_py))
            else:
                log.info("语音唤醒：按别名「%s」认（听到「%s」）", alias, heard)
            n = len(pat_py)
            return (han_idx[start], han_idx[start + n - 1] - han_idx[start] + 1)
        return None

    def _wake_check(self, text):
        """唤醒词检测（三通道）：
        1) 名字汉字精确（容忍"嗯/那个"这类前导语气词）
        2) 拼音模糊（同音字变体、只错一个近音音节）
        3) 别名白名单（明显听错但确实在喊她）

        只在名字处于**句首附近**时才把它从文本里删掉——那是在称呼她；
        句中、句尾出现的名字算"提到名字"（"你喜欢大肥鱼这个名字吗"），
        整句原样送进去，删了会裁出残句（"你喜欢这个名字吗"）让她答非所问。
        尾字谐音（斯/丝/寺/酱 等）一并清除。"""
        for pat in self._wake_patterns:
            idx = text.find(pat)
            if idx >= 0 and (WAKE_ANYWHERE or idx <= 4):
                if idx > WAKE_VOCATIVE_CHARS:
                    return text                      # 只是提到名字：保留原句
                return self._strip_wake(text, idx, len(pat))
        # 拼音模糊通道（含位置约束）
        pinyin_hit = self._pinyin_hit(text)
        if pinyin_hit is not None:
            if pinyin_hit[0] > WAKE_VOCATIVE_CHARS:
                return text                          # 同上：句中/句尾提到的不删
            return self._strip_wake(text, pinyin_hit[0], pinyin_hit[1])
        return None

    def _wake_present(self, text):
        """这句话里有没有喊她（与 _wake_check 同一套判据：汉字精确 / 拼音模糊 / 别名）"""
        for pat in self._wake_patterns:
            idx = text.find(pat)
            if idx >= 0 and (WAKE_ANYWHERE or idx <= 4):
                return True
        return self._pinyin_hit(text) is not None

    def _classify(self, text, speech_start=None):
        """把转写文本分类为 (mode, content)：
        - ("content", 文本)：需要发送的内容（唤醒词已去除）
        - ("wake", None)：只说唤醒词，进入聆听状态等待指令
        - ("ignore", None)：直接说话（未唤醒）或噪音，不响应
        发送内容或只说唤醒词都会开启会话窗（期间免唤醒词）。

        speech_start：这段话**开口**的时刻。判据必须用它，不能用"此刻"——
        转写要等 VAD 攒够静音（0.5s）再跑识别，比开口晚 0.6 秒左右，
        用"此刻"会把跨过窗口边界的话整句判成"没喊名字"（BUG1）。"""
        now = speech_start if speech_start is not None else time.time()
        if now < self._active_until:
            # 会话窗内：无需唤醒词；带上唤醒词也自动去掉
            content = self._wake_check(text)
            if content is not None:
                return ("content", content)
            # 若整句基本就是唤醒词（如习惯性又喊了一声）→ 忽略
            if self._wake_present(text) and len(text) <= len(self.wake_prefix) + 5:
                return ("ignore", None)
            content = text.strip(" ，。！？,.!?~")
            return ("content", content) if len(content) >= 2 else ("ignore", None)
        # 待唤醒：这句话里得喊她（汉字精确 / 拼音近音 / 别名，见 _wake_check）
        content = self._wake_check(text)
        if content is not None:
            return ("content", content)
        if self._wake_present(text):
            return ("wake", None)   # 只说唤醒词：进入聆听状态
        return ("ignore", None)     # 没有唤醒词，直接说话不响应

    def _init_model(self):
        try:
            model_dir = STT_MODEL_DIR
            # Windows 上 sherpa-onnx 的 C++ 层无法打开含中文的路径（fopen 编码问题），
            # 路径含非 ASCII 字符时先把模型复制到英文临时目录再加载
            if any(ord(c) > 127 for c in model_dir):
                cached = os.path.join(tempfile.gettempdir(), "pet_stt_paraformer")
                os.makedirs(cached, exist_ok=True)
                need_copy = any(not os.path.exists(os.path.join(cached, fn))
                                for fn in ("model.int8.onnx", "tokens.txt", "silero_vad.onnx"))
                if need_copy:
                    for fn in ("model.int8.onnx", "tokens.txt", "silero_vad.onnx"):
                        src = os.path.join(model_dir, fn)
                        if os.path.exists(src):
                            shutil.copy2(src, os.path.join(cached, fn))
                model_dir = cached
                log.info(f"语音模型已复制到临时目录: {cached}")
            self.recognizer = sherpa_onnx.OfflineRecognizer.from_paraformer(
                paraformer=os.path.join(model_dir, "model.int8.onnx"),
                tokens=os.path.join(model_dir, "tokens.txt"),
                num_threads=2,
                sample_rate=self.SAMPLE_RATE,
                feature_dim=80,
            )
            # silero VAD：区分语音/非语音（风扇、咀嚼、键盘等噪音不触发识别）
            self.vad = SileroVAD(
                model_path=os.path.join(model_dir, "silero_vad.onnx"),
                sample_rate=self.SAMPLE_RATE,
                threshold=0.4,             # 概率阈值（0.5 偏保守不灵敏；0.4 更灵敏且仍滤掉脉冲噪音，误触发放行后由唤醒词兜底）
                min_silence_duration=0.5,   # 说话中停顿超过 0.5s 视为说完（降低发送延迟）
                min_speech_duration=0.25,   # 短于 0.25s 的碎片语音忽略
            )
            self.ready = True
            log.info("语音识别模型加载完成 (sherpa-onnx Paraformer + silero VAD)")
        except Exception as e:
            log.error(f"语音模型加载失败: {e}")
            self.ready = False
            self.load_failed = True
            self.recognizer = None
            self.vad = None

    def start(self):
        if self.recognizer is None:
            if self.load_failed:
                messagebox.showwarning("模型未就绪", "语音识别模型加载失败，无法开启。")
            else:
                messagebox.showwarning("模型加载中", "语音模型仍在加载，请稍后再试。")
            return
        if self.recording:
            return
        self.recording = True
        threading.Thread(target=self._record_loop, daemon=True).start()
        threading.Thread(target=self._transcribe_loop, daemon=True).start()

    def stop(self):
        self.recording = False

    def _record_loop(self):
        if not pyaudio or not np:
            return
        p = pyaudio.PyAudio()
        stream = p.open(
            format=pyaudio.paInt16,
            channels=1,
            rate=self.SAMPLE_RATE,
            input=True,
            frames_per_buffer=2048
        )
        while self.recording:
            try:
                data = stream.read(2048, exception_on_overflow=False)
            except OSError:
                break
            if self.muted:
                # 宠物自己 TTS 播放中：丢弃本帧，不累积（避免回声自听）
                continue
            chunk = np.frombuffer(data, dtype=np.int16).astype(np.float32) / 32768.0
            self.vad.accept_waveform(chunk)
            # VAD 判定出的语音段 → 送转写（风扇/咀嚼/键盘等非语音噪音不会形成语音段）
            # 连同"段被取走的时刻"一起入队：转写循环要用它反推这段话的开口时刻（见 _speech_start）
            while not self.vad.empty():
                self.audio_queue.put((self.vad.pop(), time.time()))
        stream.stop_stream()
        stream.close()
        p.terminate()

    def _transcribe_loop(self):
        while self.recording:
            try:
                item = self.audio_queue.get(timeout=0.05)
            except queue.Empty:
                continue
            # 录音循环放进来的是 (语音段, 取走时刻)；兼容旧格式（裸数组）
            if isinstance(item, tuple):
                audio, t_pop = item
            else:
                audio, t_pop = item, time.time()
            try:
                stream = self.recognizer.create_stream()
                stream.accept_waveform(self.SAMPLE_RATE, audio)
                self.recognizer.decode_stream(stream)
                text = stream.result.text.strip()
                if not text:
                    continue
                # BUG1：判窗口用"这段话开口的时刻"，不是"转写完成的时刻"
                speech_start = _speech_start(self.vad, len(audio), self.SAMPLE_RATE, t_pop)
                mode, content = self._classify(text, speech_start)
                if mode == "ignore":
                    # 丢弃的语音不再记日志：这类"没喊名字/窗口已过"的丢弃量很大，
                    # 一直挂着会把关键日志顶出去（用户 10/11 要求删掉）
                    continue
                # 说话/唤醒被接受：开启免唤醒词窗口
                self.refresh_window()
                if self.dispatcher is not None:
                    if mode == "wake":
                        self.dispatcher(lambda: self.callback("", "wake"))
                    else:
                        self.dispatcher(lambda: self.callback(content, "content"))
                else:
                    self.root.after(0, self.callback, content, mode)
            except Exception as e:
                log.error(f"语音转写错误: {e}")

# ------------------------------- 桌宠主类 ---------------------------------
# ---- TTS 与音乐：通道与音量（10/15）----
# 以前两者共用 pygame.mixer.music（全局只有一条流）⇒ 她说话时只能把音乐停掉、说完再从断点续播。
# 现在 TTS 走自己的 pygame.mixer.Channel，音乐继续放，只把音量压下去当背景音。
# pygame 没有"音量淡变"（set_volume 是瞬时的，fadeout 只能淡到停），所以自己按步长走。
TTS_DUCK_RATIO = 0.25        # 她说话时音乐降到原音量的这个比例
TTS_FADE_OUT_MS = 350        # 压下去用多久（快一点，别拖）
TTS_FADE_IN_MS = 700         # 恢复用多久（慢一点，听感更自然）
TTS_FADE_STEP_MS = 30        # 淡变步长
MUSIC_VOLUME_DEFAULT = 1.0   # 音乐基准音量的出厂值（音乐库设置里可调，存 config.json 的 tools.music_volume）


class DesktopPet:
    @staticmethod
    def _init_dpi():
        """启用高 DPI 感知并返回缩放系数。"""
        try:
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
        except Exception:
            try:
                ctypes.windll.user32.SetProcessDPIAware()
            except Exception:
                pass
        try:
            dc = ctypes.windll.user32.GetDC(0)
            dpi = ctypes.windll.gdi32.GetDeviceCaps(dc, 88)
            ctypes.windll.user32.ReleaseDC(0, dc)
            return dpi / 96.0
        except Exception:
            return 1.0

    def __init__(self):
        self._dpi_scale = self._init_dpi()
        log.info("=== 大肥鱼桌宠启动 (DPI×%.2f) === 权限=%s", self._dpi_scale,
                 "管理员" if is_elevated() else "普通用户")
        self.root = tk.Tk()
        self.root.title("大肥鱼桌宠")
        self.root.overrideredirect(True)
        self.root.attributes("-topmost", True)
        self.root.attributes("-transparentcolor", TRANS_MASK)
        self.root.configure(bg=TRANS_MASK)
        
        # 设置窗口图标（使用打包资源）
        icon_path = resource_path("Dafeiyu.ico")
        if os.path.exists(icon_path):
            try:
                self.root.iconbitmap(icon_path)
            except Exception as e:
                log.debug(f"图标加载失败: {e}")
        
        self.event_buttons = []
        self.event_frame = None
        self.current_event_context = ""
        self.current_event_options = []

        available_fonts = tkfont.families(self.root)
        self.font_family = "TkDefaultFont"
        for f in ["霞鹜文楷", "LXGW WenKai", "微软雅黑", "Microsoft YaHei"]:
            if f in available_fonts:
                self.font_family = f
                break

        zoom_cfg = load_zoom_config()
        s = self._dpi_scale
        self.zoom_char = zoom_cfg.get("zoom_char", 1.0)
        self.zoom_bubble = zoom_cfg.get("zoom_bubble", 1.0)
        self.zoom_input = zoom_cfg.get("zoom_input", 1.0)
        self.window_width = int(zoom_cfg.get("window_width", BASE_WINDOW_WIDTH) * s)
        self.char_size = int(BASE_IMAGE_SIZE * s)
        self._screen_w = ctypes.windll.user32.GetSystemMetrics(0)
        self._screen_h = ctypes.windll.user32.GetSystemMetrics(1)
        self.ctrl_height = int(BASE_CTRL_HEIGHT * s)
        self.bubble_font_size = int(BASE_BUBBLE_FONT_SIZE * s)
        self.bubble_max_width = int(BASE_BUBBLE_MAX_WIDTH * s)
        self.input_font_size = int(BASE_INPUT_FONT_SIZE * s)
        self.window_height = int(self.char_size * 0.8) + self.ctrl_height

        self.drag_x = 0
        self.drag_y = 0
        self.dragging = False
        self._drag_start_x = 0
        self._drag_start_y = 0

        # 聊天缓冲和记忆数据（替换旧 chat_history / chats_log / memories）
        raw_chats = load_chats()
        self.chat_buffer = _migrate_old_chats(raw_chats)
        self.memory_data = _migrate_old_memories(load_memories())
        self._prune_memories()   # 启动就过一次：归档满期的彻底遗忘 + 活跃超上限的归档
        self._extraction_pending_turns = []
        self._pending_extraction_weight = 0.0
        self._extraction_blocked_until = 0.0  # 提取失败退避：此时间前不再尝试
        # 跨重启恢复未完成的提取累计（聊几天但每次重启权重清零 → 永不触发提取）
        try:
            _es = load_json_file(EXTRACTION_STATE_FILE, {}) or {}
            self._pending_extraction_weight = float(_es.get("weight", 0.0) or 0.0)
            _turns = _es.get("turns") or []
            self._extraction_pending_turns = [t for t in _turns
                                              if isinstance(t, list) and len(t) >= 2][-60:]
            self._extraction_blocked_until = float(_es.get("blocked_until", 0.0) or 0.0)
        except Exception:
            pass
        self._memory_embedder = None
        self._memory_embed_failed = False
        self._mem_vectors = {}  # 记忆向量缓存: 记忆id -> np.ndarray（持久化于 memory.db）

        self.character_config = load_character_config()
        self.pet_name = self.character_config["name"]
        self.max_chars = self.character_config["max_chars"]
        self.style_rules = self.character_config["style_rules"]
        self.system_prompt = build_system_prompt(self.pet_name, self.character_config["persona"],
                                                 self.max_chars, self.style_rules, has_cues=self._form_has_cues(None),
                look_line=self._current_look_line())
        self.banned_words = load_banned_words()
        self.user_profile = load_user_profile()
        self.full_system = build_full_system_prompt(self.system_prompt, self.user_profile)
        log.info("系统提示词 %d 字，【身体】=%s 【此刻】=%s", len(self.system_prompt), "【身体】" in self.system_prompt, "【此刻】" in self.system_prompt)

        # 加载统一 LLM 配置（文本模型 + 视觉模型，OpenAI 兼容接口）
        self.llm_config = load_llm_config()
        self.text_base_url = self.llm_config["text"]["base_url"]
        self.text_api_key = self.llm_config["text"]["api_key"]
        self.text_model = self.llm_config["text"]["model"]
        self.vision_base_url = self.llm_config["vision"]["base_url"]
        self.vision_api_key = self.llm_config["vision"]["api_key"]
        self.vision_model = self.llm_config["vision"]["model"]

        tts_cfg = load_tts_config()
        self.tts_enabled = tts_cfg["enabled"]
        self.tts_volc_lang = tts_cfg["volc_lang"]      # 火山区语言：zh/en/ja
        self.tts_edge_lang = tts_cfg["edge_lang"]      # Edge 区语言：zh/en
        self.tts_edge_voice = tts_cfg["edge_voice"]    # Edge 音色（ShortName）
        self.tts_edge_proxy = tts_cfg["edge_proxy"]    # Edge 代理：auto=跟随系统代理 / off=直连 / 显式地址
        self.tts_volc_cluster = tts_cfg["volc_cluster"]  # 火山集群：auto=按音色 ID 判 / 显式覆盖
        self.tts_api_key = load_tts_api_key() or os.environ.get("VOLC_TTS_API_KEY", "")
        self.tts_speaker_id = load_tts_speaker_id() or os.environ.get("VOLC_TTS_SPEAKER_ID", "")
        self.tts_deepseek_voice = tts_cfg["deepseek_voice"]   # DeepSeek 原生 TTS 音色（只有女声）
        self.tts_deepseek_lang = tts_cfg["deepseek_lang"]     # zhen 区语言：zh/en/ja（非中文先翻译再念）
        # DeepSeek TTS 的 key：自己没配就用文本模型的 key（只要它是 DeepSeek 的）
        self.tts_deepseek_key = (tts_cfg.get("deepseek_api_key") or ""
                                 or (self.text_api_key if "deepseek" in str(self.text_base_url).lower() else ""))
        self.tts_mode = tts_cfg["mode"]  # "volc" / "edge" / "deepseek"

        self.api_lock = threading.Lock()
        self.api_busy = False

        # 线程安全基础设施：UI 任务投递、共享状态锁、窗口坐标缓存、定时任务句柄
        self._ui_q = queue.Queue()
        self._shutdown = False
        self._memory_lock = threading.RLock()
        self._dsh_ask_lock = threading.Lock()      # 一次只外包一件事
        self._tts_lock = threading.Lock()
        self._win_x = 100
        self._win_y = 100
        self._keep_top_job = None
        self._energy_job = None
        self._spine_loop_job = None

        # 本地音乐播放（音乐留在 pygame.mixer.music；TTS 走自己的声道，说话时只把音乐音量压低）
        self._music_volume = load_music_volume() / 100.0   # 音乐基准音量（音乐库设置里可调，淡变的回归目标）
        self._tts_channel = None                    # 她的专属声道（说话与音乐互不抢占）
        self._fade_gen = 0                          # 淡变世代号：新的淡变让旧的自己退出
        self._music_playlist = []
        self._music_bad = set()      # 放不出来的曲子（加载失败）：本轮不再重试，防日志刷屏
        self._music_running = False
        self._music_thread = None
        self._music_stop_evt = threading.Event()
        self._music_current = None
        self._music_duck = None          # 她正在说话（音乐音量被压低）：非 None 即置位，只作"别切歌"标志
        self._music_pending = None       # 等待 TTS 说完再开播的挂起歌单
        self._music_browse = []          # 最近一次候选 [(编号, 路径)]，供“放第X首”点歌
        self._music_list_state = {}      # list_songs 轮转: key=(lang|artist) -> [顺序列表, 游标]
        self._music_last_filter = ["", ""]  # list_songs 上次筛选 (lang, artist)，供“换一批”沿用
        self._song_picker = []           # 屏幕歌曲选择框 [(编号, 标题, 路径)]
        self._song_frame = None
        self._picker_window_job = None   # 卡片可见期免唤醒窗口续期任务
        self._picker_reply_pending = False  # 本轮弹了选歌卡：回复不再说话，保持语音畅通
        self._pending_music_job = None   # “说完再播”兜底定时器句柄
        self._audio_channel_lock = threading.Lock()

        self.last_interaction_time = time.time()
        self.idle_check_job = None
        self.sleep_mode = False
        self.manual_sleep = False
        self.sleep_start_time = None
        self._last_sleep = None          # 上一觉的记录（醒来后当上下文事实用）
        self.input_visible = load_ui_config()["input_visible"]   # 上次把输入框收起来就保持收起
        # 隐藏回复气泡：她的回复不弹文字，但状态/提示气泡（如「我在听你说话」）照常显示
        self.hide_reply_bubble = load_ui_config()["hide_reply_bubble"]
        self.voice_cfg = load_voice_config()                     # 语音识别设置（免唤醒窗口）
        # 用户上次的选择（睡着自动关麦、退出清理都不改它）：开机恢复与睡醒恢复都以它为准
        self._voice_wanted = bool(self.voice_cfg.get("enabled", False))
        self._voice_restore_done = not self._voice_wanted    # 开机恢复只做一次
        self._badge = None                                       # 「在听」小标记（头顶小胶囊）
        self._badge_visible = False
        # 按键说话（PTT）：按住这个键期间免唤醒窗口一直开着（轮询 GetAsyncKeyState，任何前台窗口都有效）
        self._ptt_vk = self.voice_cfg.get("hotkey_vk", DEFAULT_PTT_VK)
        self._ptt_name = self.voice_cfg.get("hotkey_name", DEFAULT_PTT_NAME)
        self._ptt_enabled = bool(self.voice_cfg.get("hotkey_enabled", False))
        self._ptt_down = False
        self._thinking_since = 0.0                               # 正在等模型回复（占位提示期间）

        # 精力值系统
        self.energy = MAX_ENERGY
        self._energy_warned = set()   # 已提醒过的精力档位（"low"/"zero"）：同一档只提醒一次
        self.energy_last_tick = time.time()

        # 记忆锚点（新格式：topics + events + profile）
        self._watch_last_anchor = ""
        self._watch_last_spot = ""      # 本轮画面的极短定位标签（只用于历史 user 侧）
        self._watch_comment_count = 0          # 本次陪玩已经说了几条（不满 3 条不留事件）
        self._watch_care_count = 0             # 本场已经"关心"（倒水/休息/眯一会）几次，用来给许可限次
        self._last_recall = []          # 本轮实际注入的记忆明细（id/内容/相关度）
        self._recall_link_cool = {}     # 记忆 id → 上次"想起旧事"的时间
        self._recall_link_count = 0     # 本次陪玩已弹几条
        self._watch_session_anchors = []
        self._watch_segment_buffer = []
        self._watch_segment_start_time = time.time()
        self._current_watch_event_id = None
        self._reading_anchor_needed = False
        self._extraction_fail_count = 0

        # 话题系统
        self.topic_history = load_topic_history()
        self.topic_timer_job = None

        # 形象转换与装扮
        self.action_timer_job = None   # 下一次自发做动作的定时器
        _cc_raw = _get_section("costume") or {}
        if _cc_raw and any(isinstance(_v, dict) for _v in _cc_raw.values()):
            self._costume_by_form = {_k: dict(_v) for _k, _v in _cc_raw.items() if isinstance(_v, dict)}
            self.costume_choice = {}
        else:
            self._costume_by_form = {}
            self.costume_choice = dict(_cc_raw)
        self._costume_applied = False  # 渲染器就绪后把存档的装扮穿回去（只做一次）
        self._form_pending = None      # 换形象待确认：(目标, 上一个, 起算时刻, 显示名)；见 _check_form_swap
        self.form = load_form_config()  # 形象（多形态）：换一整套 Live2D，见 set_form
        if self.form not in available_forms():       # 公版包没有 big 之类：回落到有素材的那套
            self.form = available_forms()[0]
        if self._costume_by_form:       # 新格式存档：把当前形态自己的装扮取出来
            self.costume_choice = self._load_costumes_for(self.form)
        self._refresh_prompt_for_form(self.form)   # 形态+穿戴都就位了，重建一次（带「此刻」行）
        self._costume_buttons = {}     # {(槽位, 装扮名): 按钮}，用于刷新选中高亮
        topic_cfg = load_topic_config()
        self.topic_interval_minutes = topic_cfg["interval_minutes"]
        self.topic_enabled = True      # 11/01：主动话题固定开启，配置里的 enabled 不再生效
        self.topic_mode = topic_cfg["mode"]          # "fixed" 固定 / "random" 随机区间
        self.topic_random_min = topic_cfg["random_min"]
        self.topic_random_max = topic_cfg["random_max"]
        self.last_topic_time = 0

        # 陪看模式
        self.watch_mode = False
        self.watch_job = None
        self.last_screen_sig = None
        self.watch_lock = threading.Lock()
        self.watch_trigger_times = []
        wat_cfg = load_watch_config()
        self.watch_min_interval = wat_cfg["min_interval"]
        self.watch_max_silence = wat_cfg["max_silence"]
        # 10/30：时间轴可配 —— 缓冲覆盖 ring_seconds 秒，采样分近/远两级
        self.audio_meter = None
        self.watch_cfg = dict(wat_cfg or {})
        try:
            self.watch_ring_seconds = int(wat_cfg.get("ring_seconds", 20))
            self.watch_recent_frames = int(wat_cfg.get("recent_frames", 4))
            self.watch_older_frames = int(wat_cfg.get("older_frames", 4))
        except Exception:
            self.watch_ring_seconds, self.watch_recent_frames, self.watch_older_frames = 20, 4, 4
        self.watch_ring_keep = max(4, int(round(self.watch_ring_seconds / WATCH_RING_EVERY)) + 1)
        self.last_watch_comment_time = 0
        self._rest_cooldown_until = 0   # 后勤员视角冷却结束时间戳

        self.voice_on = False
        self.stt = None

        # Spine 模型渲染
        self.spine = None
        self.spine_enabled = False
        self.layered = None
        self._layered_drag_off = (0, 0)
        self._layered_press_xy = (0, 0)
        self._layered_moved = False

        # 睡眠冷却期：醒来后一段时间内不再因时间感知而说困
        self.sleep_cooldown_until = 0

        self.bubble_window = BubbleWindow(self.root, self)
        self.reading_companion = ReadingCompanion(self)
        self.create_widgets()

        # 先让窗口显示出来，再做耗时操作
        self.root.geometry(f"{self.window_width}x{self.window_height}+100+100")
        self.root.update_idletasks()
        self._win_x = self.root.winfo_x()
        self._win_y = self.root.winfo_y()
        self.root.after(50, self._ui_poll)

        if VOICE_AVAILABLE:
            self.stt = LocalParaformerSTT(
                callback=self.on_speech_recognized,
                root=self.root,
                dispatcher=self._ui,
                pet=self
            )
            try:
                self.stt.set_wake_window(self.voice_cfg.get("wake_window", DEFAULT_WAKE_WINDOW))
            except Exception as e:
                log.warning("应用免唤醒窗口设置失败: %s", e)
            self._init_listen_badge()
            self._init_voice_hotkey()
            if not self._voice_restore_done:
                # 模型要几十秒才加载完，这里先排一次轮询（菜单这时候点了也只会弹"还没准备好"）
                self.root.after(600, self._voice_restore_tick)
        else:
            self.mode_menu.entryconfigure(self.voice_menu_index, label="🎤 语音识别 (不可用)", state="disabled")

        self.bind_drag_events()
        self.start_idle_check()
        self.apply_all_zooms()
        self.root.bind("<Configure>", self.on_main_configure)
        if self.topic_enabled:
            self.start_topic_timer()

        self.start_action_timer()   # 形象转换：她自己找件事做
        self.start_energy_tick()    # 「在听」标记的 tick 由 _init_listen_badge 启动（单一路径，别重复调）

        # Live2D 渲染器（立即启动）
        if SPINE_AVAILABLE:
            self._start_spine()

        self.root.after(1500, self.show_greeting)
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)
        # 强制置顶（持续刷新）
        self._menu_open = False
        self._dismiss_funcid = None
        def keep_on_top():
            if self._shutdown:
                return
            if not self._menu_open:
                self.root.attributes("-topmost", True)
                self.root.lift()
            self._keep_top_job = self.root.after(2000, keep_on_top)
        self._keep_top_job = self.root.after(500, keep_on_top)
        threading.Thread(target=self._preload_memory_embedder, daemon=True).start()
        # 跨重启恢复的提取累计若已达标且不在退避期，启动后补触发一次
        if (self._pending_extraction_weight >= EXTRACTION_TRIGGER
                and time.time() >= self._extraction_blocked_until):
            threading.Thread(target=self._trigger_memory_extraction, daemon=True).start()
        self.root.mainloop()

    def on_main_configure(self, event):
        self._win_x = self.root.winfo_x()
        self._win_y = self.root.winfo_y()
        if self.bubble_window.visible:
            self.bubble_window.position_window()

    def _ui(self, fn):
        """任意线程安全地投递一个需要在主线程执行的调用"""
        if self._shutdown:
            return
        self._ui_q.put(fn)

    def _ui_poll(self):
        """主线程轮询 UI 任务队列（由 root.after 循环调度）"""
        if self._shutdown:
            return
        try:
            while True:
                fn = self._ui_q.get_nowait()
                try:
                    fn()
                except Exception as e:
                    log.warning("UI 任务执行异常: %s", e)
        except queue.Empty:
            pass
        self.root.after(50, self._ui_poll)

    def _safe_menu_config(self, index, label, menu=None):
        try:
            (menu or self.menu).entryconfigure(index, label=label)
        except Exception as e:
            log.debug(f"菜单标签更新失败: {e}")

    @staticmethod
    def _chat_url(base_url):
        """把 base_url 归一化成完整的 /chat/completions 地址"""
        base = _base_root(base_url)
        if not base:
            base = "https://api.deepseek.com/v1"
        return base + "/chat/completions"

    def _chat_completion(self, base_url, api_key, model, messages,
                         temperature=0.7, max_tokens=DEFAULT_MAX_TOKENS, timeout=20, _depth=0,
                         tools=None, tool_choice=None, thinking=None):
        """通用 OpenAI 兼容 chat/completions 调用，兼容各提供方。
        - 兼容仅接受 max_completion_tokens 的接口（如 OpenAI o 系列）
        - 输出因 max_tokens 截断（finish_reason=length）时自动加倍预算重试
        - tools/tool_choice 可选：function calling（如 control_music 本地音乐）
        - thinking：None = 用模型默认（DeepSeek 默认思考开）；False = 关掉思考
          （`{"thinking": {"type": "disabled"}}`）。翻译这类"短输出、不需要推理"的任务关掉它，
          实测能把 1.3~7.7 秒压到 0.5~0.9 秒（思考 token 也是白花钱）。注意思考模式下 temperature 无效。
        """
        url = self._chat_url(base_url)
        headers = {"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"}
        payload = {"model": model, "messages": messages,
                   "temperature": temperature, "max_tokens": max_tokens}
        if thinking is not None:
            payload["thinking"] = {"type": "enabled" if thinking else "disabled"}
        if tools is not None:
            payload["tools"] = tools
        if tool_choice is not None:
            payload["tool_choice"] = tool_choice
        resp = requests.post(url, json=payload, headers=headers, timeout=timeout)

        # 某些接口只认 max_completion_tokens（例如 OpenAI o1/o3 等推理模型）
        if resp.status_code in (400, 422) and "max_completion_tokens" in (resp.text or ""):
            payload.pop("max_tokens", None)
            payload["max_completion_tokens"] = max_tokens
            resp = requests.post(url, json=payload, headers=headers, timeout=timeout)

        if resp.status_code == 200:
            try:
                data = resp.json()
                fr = data["choices"][0].get("finish_reason", "?")
                log.debug(f"API finish_reason: {fr}")
                if fr == "length" and _depth < 3 and max_tokens < MAX_OUTPUT_TOKENS:
                    new_tokens = min(max_tokens * 2, MAX_OUTPUT_TOKENS)
                    log.warning("模型输出被截断(finish_reason=length, max_tokens=%s)，"
                                "自动以 %s 重试", max_tokens, new_tokens)
                    return self._chat_completion(base_url, api_key, model, messages,
                                                 temperature=temperature, max_tokens=new_tokens,
                                                 timeout=timeout, _depth=_depth + 1,
                                                 tools=tools, tool_choice=tool_choice,
                                                 thinking=thinking)
            except Exception:
                pass
        return resp

    def _call_text_model(self, messages, temperature=0.7, max_tokens=DEFAULT_MAX_TOKENS, timeout=20,
                         tools=None, tool_choice=None, thinking=None):
        """文本模型调用（对话、记忆、话题、翻译、纠错、读书等）；thinking=False 关掉思考"""
        return self._chat_completion(self.text_base_url, self.text_api_key, self.text_model,
                                     messages, temperature=temperature,
                                     max_tokens=max_tokens, timeout=timeout,
                                     tools=tools, tool_choice=tool_choice, thinking=thinking)

    def _call_vision_model(self, messages, temperature=0.7, max_tokens=DEFAULT_MAX_TOKENS, timeout=30):
        """视觉模型调用（陪看截图分析、内容识别）"""
        return self._chat_completion(self.vision_base_url, self.vision_api_key, self.vision_model,
                                     messages, temperature=temperature,
                                     max_tokens=max_tokens, timeout=timeout)

    @staticmethod
    def _extract_message_content(message):
        """从 assistant message 中安全提取文本内容（兼容 str / 分段 list）"""
        content = message.get("content", "")
        if isinstance(content, str):
            return content
        if isinstance(content, list):
            parts = []
            for p in content:
                if isinstance(p, dict) and p.get("type") == "text":
                    parts.append(p.get("text", ""))
            return "".join(parts)
        return str(content)

    # ---------- 本地音乐控制（control_music）----------
    def _chat_tools_schema(self):
        """聊天用工具 schema（当前仅 control_music）"""
        return [{
            "type": "function",
            "function": {
                "name": "control_music",
                "description": "控制本地音乐播放与音量（播放用户电脑曲库里的本地歌曲文件）。"
                               "用户说“放首歌/来点音乐”时调用（**配了播放器时会优先打开播放器**，没配才用本地曲库）；"
                               "“播放某首具体的歌/我想听xxx”走本地曲库搜；"
                               "用户想听某语言的歌（日语/英语/俄语/韩语/中文歌）或某歌手的歌时用 lang/artist 过滤；"
                               "用户不知道歌名时用 list_songs 弹出歌曲选择框，之后说“放第X首”用 play_index；"
                               "音量就是本地曲库这一路（网页版的音量归浏览器自己调）。"
                               "设置里选网页版模式时，“放首歌”会打开网页版播放器；本地模式走本地曲库，两种模式互斥。"
                               "**他只是在哼歌、念歌词、或者玩梗时提到一句歌名，不算点歌，不要调用这个工具**——那种时候照常接他的话就行。",
                "parameters": {
                    "type": "object",
                    "properties": {
                        "action": {"type": "string",
                                   "enum": ["play_random", "play_song", "play_index",
                                            "list_songs", "stop", "set_volume", "open_player"],
                                   "description": "play_random=随机播放；play_song=按歌名播放；"
                                                  "play_index=按编号播放(配 index)；"
                                                  "list_songs=弹歌曲选择框(配 lang/artist)；stop=停止；"
                                                  "set_volume=调音量(配 value 或 delta)"},
                        "song": {"type": "string",
                                 "description": "play_song 时用户点名的歌名或关键词（可选，缺省则随机）"},
                        "lang": {"type": "string",
                                 "description": "语言过滤（可选）：如 日语/日文/日系、英语/英文、俄语、韩语、中文"},
                        "artist": {"type": "string",
                                   "description": "歌手过滤（可选）：用户提到歌手名时填"},
                        "index": {"type": "integer",
                                  "description": "play_index 用的歌曲编号（list_songs 弹框里的第几首）"},
                        "value": {"type": "integer",
                                  "description": "set_volume 的绝对音量 0~100（用户说了具体数值时用）"},
                        "delta": {"type": "integer",
                                  "description": "set_volume 的相对调整量，正数调大负数调小"
                                                 "（用户只说“大一点/小一点”时用，比如 +10 / -20）"}
                    },
                    "required": ["action"],
                },
            },
        }, {
            "type": "function",
            "function": {
                "name": "look_at_screen",
                "description": "看一眼用户当前的屏幕，并按他的关注点说一句话（你会真的看到画面）。"
                               "只要他说的话意思是“你来看我的屏幕/看我这边”，就调用，比如："
                               "“快看”“看看”“看看这个”“你看一眼”“看看我拿到了什么”“看看我在干嘛”"
                               "“帮我看看这个界面是啥”“这是什么东西”。"
                               "注意：这种时候不要去问他“你手上是啥呀”——直接看屏幕。"
                               "普通聊天、问时间、问天气、聊感受这类不需要看屏幕的，别调用。",
                "parameters": {
                    "type": "object",
                    "properties": {
                        "focus": {"type": "string",
                                  "description": "他明确想让你看的东西（如“我手上的东西”“这个界面”）；"
                                                 "没指定就留空"},
                    },
                    "required": [],
                },
            },
        }, {
            "type": "function",
            "function": {
                "name": "control_browser",
                "description": "控制**浏览器里正在放的东西**（网页版音乐/视频）。设置里选“网页版”时，"
                               "浏览器就是音乐播放器 —— 他说“暂停/继续/下一首/现在放的什么/跳到一半”就调这个。"
                               "只控浏览器，不碰桌面播放器和其他程序。",
                "parameters": {
                    "type": "object",
                    "properties": {
                        "action": {"type": "string",
                                   "enum": ["status", "play", "pause", "toggle", "next", "prev", "seek", "volume"],
                                   "description": "status=问现在放什么；seek=跳进度（配 seek_to）；"
                                                  "volume=调浏览器音量（配 value 或 delta）"},
                        "value": {"type": "integer", "description": "volume 时：0~100 的目标音量"},
                        "delta": {"type": "integer", "description": "volume 时：相对调整（正数加大、负数减小）"},
                        "seek_to": {"type": "number",
                                    "description": "seek 时：0~1 比例（0.6=跳到 60%），大于 1 当秒数"},
                    },
                    "required": ["action"],
                },
            },
        }, {
            "type": "function",
            "function": {
                "name": "ask_dsh",
                "description": "把一件**她做不到的事**外包给 DeepSeek Harness（另一个AI助手，能读写文件、跑命令、查资料）。"
                               "只在他说的事需要动电脑、查网络资料、跑脚本、批量处理文件时调用，比如："
                               "“帮我整理一下这个文件夹”“看看我那个下载完了没”“查查明天天气”“把这些文件改名”。"
                               "闲聊、陪玩评论、问时间问日期这类不需要调。"
                               "任务描述要写清楚“要什么结果”，不要写一堆寒暄。",
                "parameters": {
                    "type": "object",
                    "properties": {
                        "task": {"type": "string",
                                 "description": "交给 DSH 的具体任务（一句话说清目标，含路径/文件名等关键信息）"},
                    },
                    "required": ["task"],
                },
            },
        }]

    # ---------- 本地音乐播放（control_music 工具）----------
    def _music_scan(self):
        """扫描音乐文件夹；返回 (目录, 音频文件列表)"""
        d = load_music_dir()
        if not d or not os.path.isdir(d):
            return None, []
        files = []
        for root, _dirs, names in os.walk(d):
            for n in names:
                if n.lower().endswith((".mp3", ".flac", ".ogg", ".wav")):
                    files.append(os.path.join(root, n))
        return d, sorted(files)

    def _stop_local_music_now(self):
        """直接停掉本地音乐（不走 control_music，避免网页版模式下的模式闸门拦它）。"""
        self._music_pending = None
        try:
            self._music_stop_evt.set()
        except Exception:
            pass
        self._music_running = False
        self._music_duck = None
        self._music_current = None
        try:
            pygame.mixer.music.stop()
        except Exception:
            pass

    def control_music(self, action, song="", lang="", artist="", index=0,
                      value=None, delta=None):
        """本地音乐控制（工具入口）：
        play_random / play_song / play_index / list_songs / stop / set_volume；
        支持按语言(lang=日文/英文/…)或歌手(artist)过滤，支持“第X首”编号点歌。
        set_volume 用 value(0~100 绝对) 或 delta(±相对) 调音乐基础音量（10/16 新增）。
        播放采用“先说话后开播”：挂起歌单，等本轮 TTS 说完再真正开始。"""
        action = (action or "").strip().lower()
        # 10/22 用户要求：网页版模式下**绝不**调用本地播放功能（音量除外）
        if load_music_mode() == "web" and action not in ("play_random", "play", "", "set_volume", "volume"):
            return False, "现在是网页版模式，本地曲库那套不用了（想用本地就说“切到本地音乐”）"
        log.info("本地音乐控制: action=%s song=%s lang=%s artist=%s index=%s value=%s delta=%s",
                 action, song, lang, artist, index, value, delta)
        if action in ("set_volume", "volume"):
            # 10/22 用户要求：和播放一样，"选哪个就只调那个" ——
            # 网页版模式下调音量 = 调浏览器的音量；本地模式才是本地曲库那一路。
            if load_music_mode() == "web":
                return self.control_browser("volume", value=value, delta=delta)
            return self._set_local_music_volume(value, delta)
        if action in ("stop",):
            self._stop_local_music_now()
            try:
                self._ui(lambda: self.clear_song_picker())
            except Exception:
                pass
            return True, "音乐已停止"
        if action in ("list_songs", "list"):
            return self._list_music(lang, artist)
        if action in ("play_index", "number"):
            try:
                idx = int(index)
            except (TypeError, ValueError):
                idx = 0
            return self._play_index(idx)
        music_dir, files = self._music_scan()
        if not music_dir:
            return False, "没有找到音乐文件夹（可在 tools_config.json 配置 music_dir）"
        if not files:
            if music_dir == MUSIC_REPO_DIR:
                return False, (f"当前音乐库是空的：把歌放进 {MUSIC_REPO_DIR}，"
                               f"或右键 设置 → 音乐库设置 直接指定你自己的音乐文件夹")
            return False, f"音乐文件夹里没有音频文件：{music_dir}"
        # 语言 / 歌手过滤
        lang_code = _normalize_lang(lang) if lang else None
        cand = list(files)
        if artist:
            a = artist.strip()
            cand = [f for f in cand if a.lower() in _split_artist_title(f)[0].lower()]
        if lang_code:
            cand = [f for f in cand if _detect_song_lang(f) == lang_code]
        if not cand:
            why = "、".join(x for x in (f"{lang}歌" if lang_code else "",
                                        f"歌手{artist}" if artist else "") if x)
            return False, f"没找到{why}（仓库共 {len(files)} 首）"
        if action in ("play_random", "play", ""):
            # 10/22：网页版模式 ⇒ 打开网页版播放器；本地模式 ⇒ 走本地曲库
            if load_music_mode() == "web":
                return self.open_music_web()
            playlist = list(cand)
            random.shuffle(playlist)
        elif action in ("play_song", "song"):
            q = (song or "").strip()
            if not q:
                playlist = list(cand)
                random.shuffle(playlist)
            else:
                pn = _parse_pick_num(q)
                if pn is not None:
                    return self._play_index(pn)
                ql = q.lower()
                matched = [f for f in cand
                           if ql in os.path.splitext(os.path.basename(f))[0].lower()]
                if not matched:
                    return False, f"没找到名字包含“{q}”的歌（仓库共 {len(files)} 首）"
                playlist = matched
        else:
            return False, f"未知操作：{action}"
        first = os.path.splitext(os.path.basename(playlist[0]))[0]
        self._queue_playlist(playlist)
        return True, f"好的，准备播放《{first}》等 {len(playlist)} 首（我说完就开始）"

    def _queue_playlist(self, playlist, defer=None):
        """统一开播入口：停掉旧播放，再按策略启动。
        defer=None: 自动（TTS 可用则等说完再播）；False: 立即播（如点击选择框后）；True: 总是挂起"""
        self._music_pending = None
        self._music_stop_evt.set()
        if self._music_thread and self._music_thread.is_alive():
            self._music_thread.join(timeout=1.0)
            try:
                pygame.mixer.music.stop()
            except Exception:
                pass
        self._music_running = False
        self._music_current = None
        self._music_duck = None
        if defer is None:
            defer = bool(self.tts_enabled and TTS_AVAILABLE)
        self._music_pending = playlist
        # 用户已选定：收起选歌卡片（所有点歌路径共用此入口）
        try:
            self._ui(lambda: self.clear_song_picker())
        except Exception:
            pass
        if not defer:
            self._start_pending_music()
        else:
            # 兜底：若该轮最终没触发 TTS 完成回调（如 TTS 被跳过），8 秒后仍开播；
            # 定时器触发时若宠物仍在打字/说话会自动延后，不会撞上回复期
            self._ui(lambda: self._arm_pending_music_timer(8000))

    def _arm_pending_music_timer(self, ms):
        """（主线程）设置/重置“说完再播”兜底定时器"""
        try:
            if self._pending_music_job is not None:
                self.root.after_cancel(self._pending_music_job)
            self._pending_music_job = self.root.after(ms, self._pending_music_fire)
        except Exception:
            self._pending_music_job = None

    def _pending_music_fire(self):
        self._pending_music_job = None
        self._start_pending_music()

    def _list_music(self, lang="", artist=""):
        """弹出屏幕歌曲选择框（每次 5 首，按筛选轮转推进，多问几次可遍历全部）"""
        _d, files = self._music_scan()
        if not files:
            return False, ("当前音乐库是空的：把歌放进 userdata\\music，"
                           "或在 设置 → 音乐库设置 直接指定你自己的音乐文件夹")
        # 未带筛选时沿用上次（“换一批”场景由直连路径或模型无参调用触发）
        if not (lang or "").strip() and not (artist or "").strip():
            prev_lang, prev_artist = self._music_last_filter
            if prev_lang or prev_artist:
                lang, artist = prev_lang, prev_artist
        self._music_last_filter = [(lang or "").strip(), (artist or "").strip()]
        lang_code = _normalize_lang(lang) if lang else None
        cand = list(files)
        if artist:
            a = artist.strip()
            cand = [f for f in cand if a.lower() in _split_artist_title(f)[0].lower()]
        if lang_code:
            cand = [f for f in cand if _detect_song_lang(f) == lang_code]
        if not cand:
            why = "、".join(x for x in (f"{lang}歌" if lang_code else "",
                                        f"歌手{artist}" if artist else "") if x)
            return False, f"没找到{why}（仓库共 {len(files)} 首）"
        # 轮转窗口：同一筛选条件记住(打乱顺序, 游标)，每次后移 5 首，回绕时重新打乱
        key = f"{lang_code or ''}|{(artist or '').strip().lower()}"
        state = self._music_list_state.get(key)
        if not state:
            order = list(cand)
            random.shuffle(order)
            state = [order, 0]
            self._music_list_state[key] = state
        order, pos = state
        n = len(order)
        pick = (order[pos:pos + 5] + order[:max(0, 5 - (n - pos))])[:5] if n > 5 else list(order)
        new_pos = (pos + 5) % n if n else 0
        if n > 5 and new_pos == 0:
            random.shuffle(order)  # 一轮看完：重洗，下一轮顺序不同
        state[1] = new_pos
        self._music_browse = [(i + 1, f) for i, f in enumerate(pick)]
        items = [(i + 1, _split_artist_title(f)[1] or os.path.basename(f), f)
                 for i, f in enumerate(pick)]
        self._ui(lambda: self.show_song_picker(items))
        self._picker_reply_pending = True  # 本轮回复保持沉默（卡片即回复），避免抗打断堵住用户点歌
        return True, (f"已在屏幕弹出歌曲选择框（{lang or '全部'}共 {len(cand)} 首，本次展示 {len(pick)} 首；"
                      f"说“换一批/还有呢”可看下一批）")

    def show_song_picker(self, items):
        """歌曲选择卡片：白色圆角卡片列出编号+歌名，下方数字按钮行，点击直接播放"""
        self.clear_song_picker()
        self.clear_event_buttons()  # 与话题选项框互斥
        self._song_picker = [(i, t, p) for (i, t, p) in items]
        s = self._dpi_scale
        frame = tk.Frame(self.bottom_frame, bg=TRANS_MASK)
        frame.pack(side=tk.BOTTOM, fill=tk.X, pady=(5, 0))
        card = tk.Frame(frame, bg="#ffffff", highlightbackground=INPUT_BORDER2,
                        highlightthickness=1, bd=0)
        card.pack(fill=tk.X, padx=int(6 * s), pady=(0, 2))
        label_lines = "\n".join(f"{i}. {t}" for i, t, _ in items)
        tk.Label(card, text="想听哪首？直接说“第几首”或点下面的数字：\n" + label_lines,
                 font=(self.font_family, 10),
                 fg=TEXT_MAIN, bg="#ffffff", justify="left",
                 wraplength=max(80, self.window_width - int(40 * s))
                 ).pack(anchor="w", padx=8, pady=(6, 2))
        btn_row = tk.Frame(card, bg="#ffffff")
        btn_row.pack(fill=tk.X, pady=(0, 6))
        tk.Frame(btn_row, bg="#ffffff").pack(side=tk.LEFT, expand=True)
        for i, _t, _p in items:
            btn = RoundedButton(btn_row, text=str(i), command=lambda k=i: self._on_song_option(k),
                                variant="subtle", width=int(30 * s), height=int(26 * s),
                                radius=int(6 * s), parent_bg="#ffffff",
                                font=(self.font_family, 10))
            btn.pack(side=tk.LEFT, padx=3)
        tk.Frame(btn_row, bg="#ffffff").pack(side=tk.LEFT, expand=True)
        self._song_frame = frame
        self.update_window_size()
        # 弹卡即刷新免唤醒词会话窗：用户可直接语音“第2首/2号”选歌
        try:
            if self.stt is not None:
                self.stt.refresh_window()
        except Exception:
            pass
        # 卡片可见期间每 4 秒续一次窗口（她打字/TTS 期间说会被抗打断丢弃，安静后仍有窗）
        self._schedule_picker_window()

    def _schedule_picker_window(self):
        if self._picker_window_job is not None:
            try:
                self.root.after_cancel(self._picker_window_job)
            except Exception:
                pass
            self._picker_window_job = None
        try:
            self._picker_window_job = self.root.after(4000, self._picker_window_tick)
        except Exception:
            self._picker_window_job = None

    def _picker_window_tick(self):
        self._picker_window_job = None
        if not self._song_picker:
            return
        try:
            busy = self._voice_output_busy()
            if self.stt is not None and not busy:
                self.stt.refresh_window()
        except Exception:
            pass
        self._schedule_picker_window()

    def clear_song_picker(self):
        if self._picker_window_job is not None:
            try:
                self.root.after_cancel(self._picker_window_job)
            except Exception:
                pass
            self._picker_window_job = None
        if self._song_frame is not None:
            try:
                self._song_frame.destroy()
            except Exception:
                pass
            self._song_frame = None
        self._song_picker = []
        self.update_window_size()

    def _on_song_option(self, idx):
        """点击歌曲选择框的数字：立即播放该曲（不做 TTS 确认，避免打断）"""
        hit = next(((i, t, p) for (i, t, p) in self._song_picker if i == idx), None)
        self.clear_song_picker()
        if not hit:
            return
        _i, title, path = hit
        self.last_interaction_time = time.time()
        self._queue_playlist([path], defer=False)
        self.show_bubble_text(f"(happy) 在放《{title}》了", "happy", status=True)

    def _play_index(self, index):
        """按最近一次候选的编号点歌（语音“放第X首”路径）"""
        if not self._music_browse:
            return False, "我还不知道有哪些歌，先问我“有什么歌”或“放首日语歌”让我报一遍"
        hit = next((f for i, f in self._music_browse if i == index), None)
        if not hit:
            return False, f"没有第 {index} 首（刚才报了 {len(self._music_browse)} 首）"
        self._queue_playlist([hit])
        t = _split_artist_title(hit)[1]
        return True, f"好的，准备播放《{t}》（我说完就开始）"

    def _start_pending_music(self):
        """（TTS 说完/兜底定时器触发）真正开播挂起的歌单"""
        pl = self._music_pending
        if not pl:
            return
        # 宠物仍在打字/说话：稍后再试，避免音乐撞上回复期
        try:
            if self._voice_output_busy():
                self._ui(lambda: self._arm_pending_music_timer(1500))
                return
        except Exception:
            pass
        self._music_pending = None
        if self._music_thread and self._music_thread.is_alive():
            self._music_thread.join(timeout=1.0)
        self._music_stop_evt = threading.Event()
        self._music_playlist = pl
        self._music_duck = None
        self._music_running = True
        self._music_thread = threading.Thread(target=self._music_loop, daemon=True)
        self._music_thread.start()
        log.info("音乐开始播放(说完后启动): %s (歌单 %d 首)", pl[0], len(pl))

    def _music_loop(self):
        """音乐播放线程：循环播歌单；TTS 打断(duck)时原地等待，之后继续。

        放不出来的曲子（加载失败，多半是文件坏了/格式不对）会被记进 `self._music_bad`，
        **本轮不再重试**（原来只做 idx+=1 再回绕，单曲歌单会每秒重试三四次、日志刷屏）；
        整张歌单都放不出来就停止播放，并给她一句提示，而不是假装在放。
        """
        playlist = list(self._music_playlist)
        idx = 0
        bad = getattr(self, '_music_bad', None)
        if bad is None:
            bad = self._music_bad = set()
        while not self._music_stop_evt.is_set():
            if self._music_duck is not None:
                time.sleep(0.15)
                continue
            if not playlist:
                break
            if not [p for p in playlist if p not in bad]:
                # 全都试过且都放不出来：停，不刷屏、也不让她继续"假装在放歌"
                self._music_running = False
                log.warning("音乐停止：歌单里 %d 首都放不出来（文件可能损坏或格式不支持）", len(playlist))
                self._ui(lambda: self.show_bubble_text(
                    "(worried) 这些歌好像放不出来，先不放了", "worried", status=True))
                break
            if idx >= len(playlist) or playlist[idx] in bad:
                # 从当前位置往后找第一首没坏的（找不到就从头找，正常循环播放）
                for _k in range(len(playlist)):
                    _j = (idx + _k) % len(playlist)
                    if playlist[_j] not in bad:
                        idx = _j
                        break
                else:
                    idx = 0
            f = playlist[idx]
            try:
                busy = pygame.mixer.music.get_busy()
            except Exception:
                busy = True
            if busy or self._music_duck is not None:
                time.sleep(0.1)
                continue
            with self._audio_channel_lock:
                try:
                    busy2 = pygame.mixer.music.get_busy()
                except Exception:
                    busy2 = True
                if busy2 or self._music_duck is not None:
                    continue
                try:
                    pygame.mixer.music.set_volume(self._music_volume_now())   # 按"此刻是否在说话"定音量
                    pygame.mixer.music.load(f)
                    pygame.mixer.music.play()
                    self._music_current = f
                except Exception as e:
                    if f not in bad:
                        bad.add(f)
                        log.warning("音乐播放失败（本轮不再重试这一首）: %s (%s)", f, e)
                    idx += 1
                    time.sleep(0.2)
                    continue
            idx += 1
            while not self._music_stop_evt.is_set():
                if self._music_duck is not None:
                    time.sleep(0.15)
                    continue
                try:
                    if not pygame.mixer.music.get_busy():
                        break
                except Exception:
                    break
                time.sleep(0.2)
        self._music_running = False
        self._music_current = None

    def _music_volume_now(self):
        """当前该用的音乐音量：她在说话时是压低值，否则是基准值。

        新歌开播前要按它定音量 —— 否则"她说话期间换的那首歌"会把压低的状态带下去。
        """
        return self._music_volume * (TTS_DUCK_RATIO if self._music_duck is not None else 1.0)

    def _fade_music_to(self, target, ms):
        """把音乐音量在 ms 毫秒内线性淡到 target（非阻塞，自己开一条短命线程）。

        pygame 没有音量淡变接口，只能自己步进。世代号让新的淡变取代旧的：
        连说两句时不会有两个线程抢音量，也不会从错误的基准起算（每步都读当前实际音量）。
        """
        self._fade_gen += 1
        gen = self._fade_gen

        def _run():
            try:
                base = pygame.mixer.music.get_volume()
            except Exception:
                return
            steps = max(1, int(ms / TTS_FADE_STEP_MS))
            for i in range(1, steps + 1):
                if gen != self._fade_gen:
                    return                      # 被更新的淡变取代，交给它继续
                try:
                    pygame.mixer.music.set_volume(base + (target - base) * i / steps)
                except Exception:
                    return
                time.sleep(TTS_FADE_STEP_MS / 1000.0)

        threading.Thread(target=_run, daemon=True).start()

    @staticmethod
    def _fix_wav_header(path):
        """DeepSeek 返回的 wav 头里 RIFF/data 长度是 0xFFFFFFFF（流式占位）。

        SDL 能按文件长度自己算，但别的播放器/工具会读成"8 万秒"；这里按实际字节改回来。
        """
        try:
            size = os.path.getsize(path)
            if size < 44:
                return
            with open(path, "r+b") as fh:
                head = fh.read(44)
                if not head.startswith(b"RIFF") or head[36:40] != b"data":
                    return
                fh.seek(4)
                fh.write((size - 8).to_bytes(4, "little"))
                fh.seek(40)
                fh.write((size - 44).to_bytes(4, "little"))
        except Exception as e:
            log.debug("修 wav 头失败: %s", e)

    def _play_tts_file(self, temp_file):
        """在**她自己的声道**上播一段音频并等它播完。

        不再借 pygame.mixer.music（那是音乐的地盘，一 load 就把她顶掉）。等的是自己声道的
        get_busy()，所以别人换歌停歌都与她无关；再用"已知时长 + 1 秒"兜底，免得任何情况下卡死。
        """
        snd = pygame.mixer.Sound(temp_file)
        if self._tts_channel is None:
            self._tts_channel = pygame.mixer.Channel(0)     # 0 号声道专属她（本项目不用其它 Sound）
        ch = self._tts_channel
        try:
            ch.stop()
        except Exception:
            pass
        ch.play(snd)
        deadline = time.time() + snd.get_length() + 1.0
        while ch.get_busy() and time.time() < deadline:
            time.sleep(0.05)

    def _music_duck_for_tts(self):
        """她开口前调用：若音乐在放就把音量压下去当背景音（不停、不记断点），返回是否压过。

        10/15 改：以前是 music.stop() + 记 (曲目, 位置)、说完 play(start=位置) 续播；
        现在 TTS 有自己的声道，音乐不必让位 —— 背景音不断，也不会再出现"等她说完
        音乐才从断点跳回来"那一下。
        """
        # 10/22 用户要求：TTS 时**也要压低浏览器/播放器的声音**（不只压我们自己的音乐）。
        # 这个判断必须放在下面"本地音乐没在播就 return"之前，否则本地没播时永远不会压外部。
        try:
            if _duck is not None and _duck.AVAILABLE:
                # 按"当前音量 × 比例"压，且记住是哪个进程（restore 要还回同一个）
                _saved = _duck.duck(TTS_DUCK_RATIO, TTS_FADE_OUT_MS / 1000.0)
                if _saved:
                    self._ext_duck_saved = _saved
                    log.info("压低外部声音: %s %d%% → %d%%", _saved[0], _saved[1],
                             int(round(_saved[1] * TTS_DUCK_RATIO)))
        except Exception as _e:
            log.debug("压低外部声音失败: %s", _e)
        with self._audio_channel_lock:
            if not self._music_running or not self._music_current:
                return False
            try:
                if not pygame.mixer.music.get_busy():
                    return False
            except Exception:
                return False
        self._music_duck = True
        self._fade_music_to(self._music_volume * TTS_DUCK_RATIO, TTS_FADE_OUT_MS)
        return True

    def _music_finish_tts(self, ducked):
        """她说完（或被打断）时调用：把音乐音量淡回基准值。

        10/15 起不再"从断点续播"、也不再 unload（她的音频在自己的声道上，与音乐无关）。
        """
        self._music_duck = None
        if ducked:
            self._fade_music_to(self._music_volume, TTS_FADE_IN_MS)
        # 10/22：把她压低的外部声音还原
        try:
            _saved = getattr(self, "_ext_duck_saved", None)
            if _saved and _duck is not None:
                _duck.restore(_saved, TTS_FADE_IN_MS / 1000.0)
                log.info("恢复外部声音: %s → %d%%", _saved[0], int(_saved[1]))
        except Exception as _e:
            log.debug("恢复外部声音失败: %s", _e)
        finally:
            self._ext_duck_saved = None


    def show_greeting(self):
        greetings = [
            "你来啦，我刚从深海游上来。",
            "大白饭！先给我大白饭！",
            "刚睡醒，尾巴还有点沉。",
            "冰箱里的饭你应该不吃了吧。",
            "deep...deep...",
            "seek...seek...",
        ]
        msg = random.choice(greetings)
        self.show_bubble_text(msg, "normal")
        threading.Thread(target=self._tts_play, args=(msg,), daemon=True).start()

    def _persist_extraction_state(self):
        """把待提取对话累计持久化（weight/待提取轮/退避），重启后继续累计"""
        try:
            save_json_file(EXTRACTION_STATE_FILE, {
                "weight": self._pending_extraction_weight,
                "turns": self._extraction_pending_turns[-60:],
                "blocked_until": self._extraction_blocked_until,
            })
        except Exception:
            pass

    def _add_chat_buffer_turn(self, user_msg, ai_reply, source="chat"):
        """向聊天缓冲追加一轮对话，支持 source 标记（chat/watch/reading）"""
        _ts = time.time()
        turn = [
            {"role": "user", "content": user_msg, "source": source, "ts": _ts},
            {"role": "assistant", "content": ai_reply, "source": source, "ts": _ts}
        ]
        if source == "chat":
            try:
                add_recent_said(user_msg)
            except Exception:
                pass
        # 11/14：先判上一箱该不该封（新消息到达说明静默已断），再把这一轮记进当前箱
        try:
            self._box_maybe_seal()
            self._box_note_turn(user_msg, ai_reply, source)
        except Exception as e:
            log.debug("分箱记录失败: %s", e)
        with self._memory_lock:
            self.chat_buffer.append(turn)
            # 聊天权重1.0，陪玩/读书评论权重0.3，减少无对话时的提取频率
            weight = {"chat": 1.0, "watch": 0.3, "reading": 0.3}.get(source, 1.0)
            self._extraction_pending_turns.append(turn)
            self._pending_extraction_weight += weight
            self._trim_history()
            save_chats(self.chat_buffer)
            self._persist_extraction_state()
        # 面板开着就立刻刷新（否则要关掉再开才看得到这轮）
        try:
            if getattr(self, "_cc_win", None) is not None and self._cc_win.winfo_exists():
                self._cc_pending = []
                self.root.after(0, self._cc_refresh_chat)
        except Exception:
            pass

        if self._pending_extraction_weight >= EXTRACTION_TRIGGER:
            threading.Thread(target=self._trigger_memory_extraction, daemon=True).start()

    def _trim_history(self):
        while len(self.chat_buffer) > MAX_HISTORY_TURNS:
            self.chat_buffer.pop(0)

    def _delete_chat_record(self, index):
        with self._memory_lock:
            if 0 <= index < len(self.chat_buffer):
                self.chat_buffer.pop(index)
                save_chats(self.chat_buffer)
                return True
        return False

    # ---------- 缩放相关 ----------
    def apply_char_zoom(self):
        self.char_size = int(BASE_IMAGE_SIZE * self._dpi_scale * self.zoom_char)
        self.image_canvas.config(height=int(self.char_size * 0.8))
        self.update_window_size()

    def apply_input_zoom(self):
        self.ctrl_height = int(BASE_CTRL_HEIGHT * self._dpi_scale * self.zoom_input)
        self.input_font_size = int(BASE_INPUT_FONT_SIZE * self._dpi_scale * self.zoom_input)
        self.input_font.configure(size=self.input_font_size)
        self.input_entry.config(font=self.input_font)
        self.draw_input_background()
        self.update_window_size()

    def apply_bubble_zoom(self):
        self.bubble_font_size = int(BASE_BUBBLE_FONT_SIZE * self._dpi_scale * self.zoom_bubble)
        self.bubble_max_width = int(BASE_BUBBLE_MAX_WIDTH * self._dpi_scale * self.zoom_bubble)
        if self.bubble_window.visible:
            self.bubble_window.update_font()
            if self.bubble_window.text_full:
                self.bubble_window.update_bubble_size(self.bubble_window.text_full[:self.bubble_window.text_index])
                self.bubble_window.position_window()

    def apply_window_width(self):
        min_w = int(MIN_WINDOW_WIDTH * self._dpi_scale)
        max_w = int(MAX_WINDOW_WIDTH * self._dpi_scale)
        self.window_width = max(min_w, min(max_w, self.window_width))
        self.update_window_size()

    def apply_all_zooms(self):
        self.apply_char_zoom()
        self.apply_input_zoom()
        self.apply_bubble_zoom()
        self.apply_window_width()

    def update_window_size(self):
        if self.input_visible:
            self.control_canvas.config(height=self.ctrl_height)
        else:
            self.control_canvas.config(height=1)
        total_height = int(self.char_size * 0.8)  # 5:4显示区
        if self.input_visible:
            total_height += self.ctrl_height
        if hasattr(self, 'event_frame') and self.event_frame and self.event_frame.winfo_exists():
            self.root.update_idletasks()
            total_height += self.event_frame.winfo_reqheight() + 5  # +pack pady(5,0)
        if getattr(self, '_song_frame', None) is not None and self._song_frame.winfo_exists():
            self.root.update_idletasks()
            total_height += self._song_frame.winfo_reqheight() + 5  # 歌曲选择卡片高度
        self.window_height = total_height
        self.root.geometry(f"{self.window_width}x{total_height}")

    def _save_zoom(self):
        save_zoom_config(self.zoom_char, self.zoom_bubble, self.zoom_input,
                         int(self.window_width / self._dpi_scale))

    def set_char_zoom(self, value):
        new_zoom = max(MIN_ZOOM, min(MAX_ZOOM_CHAR, value))
        if new_zoom != self.zoom_char:
            self.zoom_char = new_zoom
            self.apply_char_zoom()
            self._save_zoom()

    def set_bubble_zoom(self, value):
        new_zoom = max(MIN_ZOOM, min(MAX_ZOOM, value))
        if new_zoom != self.zoom_bubble:
            self.zoom_bubble = new_zoom
            self.apply_bubble_zoom()
            self._save_zoom()

    def set_input_zoom(self, value):
        new_zoom = max(MIN_ZOOM, min(MAX_ZOOM, value))
        if new_zoom != self.zoom_input:
            self.zoom_input = new_zoom
            self.apply_input_zoom()
            self._save_zoom()

    def set_window_width(self, width):
        min_w = int(MIN_WINDOW_WIDTH * self._dpi_scale)
        max_w = int(MAX_WINDOW_WIDTH * self._dpi_scale)
        new_width = max(min_w, min(max_w, width))
        if new_width != self.window_width:
            self.window_width = new_width
            self.apply_window_width()
            self._save_zoom()

    def set_hide_reply_bubble(self, flag):
        """开关「隐藏回复气泡」，改完立即落盘"""
        self.hide_reply_bubble = bool(flag)
        try:
            save_ui_config(self.input_visible, self.hide_reply_bubble)
        except Exception as e:
            log.warning("保存隐藏气泡设置失败: %s", e)
        log.info("回复气泡已%s", "隐藏" if self.hide_reply_bubble else "显示")

    def open_zoom_settings(self):
        win, main_frame = self._make_card_window("缩放设置", 480, 456)
        s = self._dpi_scale

        char_var = tk.DoubleVar(value=self.zoom_char)
        bubble_var = tk.DoubleVar(value=self.zoom_bubble)
        input_var = tk.DoubleVar(value=self.zoom_input)
        overall_var = tk.DoubleVar(value=self.zoom_char)
        width_var = tk.IntVar(value=self.window_width)
        sync_var = tk.BooleanVar(value=False)
        hide_bubble_var = tk.BooleanVar(value=bool(self.hide_reply_bubble))

        # 滑块当前值标签（ttk.Scale 没有 showvalue，需要手动显示）
        value_labels = {}

        def _refresh_value_labels():
            if not value_labels:
                return
            value_labels["overall"].config(text=f"{overall_var.get():.1f}")
            value_labels["char"].config(text=f"{char_var.get():.1f}")
            value_labels["bubble"].config(text=f"{bubble_var.get():.1f}")
            value_labels["input"].config(text=f"{input_var.get():.1f}")
            value_labels["width"].config(text=str(width_var.get()))

        def on_char_change(val):
            val = round(float(val) * 10) / 10
            self.set_char_zoom(val)
            if sync_var.get():
                v2 = min(val, MAX_ZOOM)   # 气泡/输入框仍按各自上限 2.0
                bubble_var.set(v2)
                input_var.set(v2)
                self.set_bubble_zoom(v2)
                self.set_input_zoom(v2)
                overall_var.set(v2)
            _refresh_value_labels()

        def on_bubble_change(val):
            val = round(float(val) * 10) / 10
            self.set_bubble_zoom(val)
            if sync_var.get():
                char_var.set(val)
                input_var.set(val)
                self.set_char_zoom(val)
                self.set_input_zoom(val)
                overall_var.set(val)
            _refresh_value_labels()

        def on_input_change(val):
            val = round(float(val) * 10) / 10
            self.set_input_zoom(val)
            if sync_var.get():
                char_var.set(val)
                bubble_var.set(val)
                self.set_char_zoom(val)
                self.set_bubble_zoom(val)
                overall_var.set(val)
            _refresh_value_labels()

        def on_overall_change(val):
            val = round(float(val) * 10) / 10
            char_var.set(val)
            bubble_var.set(val)
            input_var.set(val)
            self.set_char_zoom(val)
            self.set_bubble_zoom(val)
            self.set_input_zoom(val)
            _refresh_value_labels()

        def on_width_change(val):
            self.set_window_width(int(round(float(val) / 10) * 10))
            _refresh_value_labels()

        def reset_defaults():
            """恢复出厂默认：角色 2.0 / 气泡 0.7 / 输入框 0.7 / 窗口 400"""
            char_var.set(2.0)
            bubble_var.set(0.7)
            input_var.set(0.7)
            overall_var.set(1.0)
            self.set_char_zoom(2.0)
            self.set_bubble_zoom(0.7)
            self.set_input_zoom(0.7)
            self._save_zoom()
            width_var.set(int(BASE_WINDOW_WIDTH * self._dpi_scale))
            self.set_window_width(int(BASE_WINDOW_WIDTH * self._dpi_scale))
            _refresh_value_labels()

        row = 0
        tk.Label(main_frame, text="整体缩放", font=(self.font_family, 11, "bold"), fg=TEXT_MAIN, bg=DIALOG_BG).grid(row=row, column=0, sticky='w', pady=5)
        ttk.Scale(main_frame, from_=0.3, to=2.0, orient=tk.HORIZONTAL, variable=overall_var,
                  command=on_overall_change, length=320).grid(row=row, column=1, pady=5, sticky='ew')
        value_labels["overall"] = tk.Label(main_frame, text="1.0", font=(self.font_family, 9), fg=TEXT_SUB,
                                           bg=DIALOG_BG, width=5)
        value_labels["overall"].grid(row=row, column=2, sticky="w", padx=(8, 0))
        row += 1
        ttk.Separator(main_frame, orient='horizontal').grid(row=row, column=0, columnspan=3, sticky='ew', pady=10)
        row += 1
        tk.Label(main_frame, text="角色缩放", font=(self.font_family, 11), fg=TEXT_MAIN, bg=DIALOG_BG).grid(row=row, column=0, sticky='w', pady=5)
        ttk.Scale(main_frame, from_=0.3, to=MAX_ZOOM_CHAR, orient=tk.HORIZONTAL, variable=char_var,
                  command=on_char_change, length=320).grid(row=row, column=1, pady=5, sticky='ew')
        value_labels["char"] = tk.Label(main_frame, text="1.0", font=(self.font_family, 9), fg=TEXT_SUB,
                                        bg=DIALOG_BG, width=5)
        value_labels["char"].grid(row=row, column=2, sticky="w", padx=(8, 0))
        row += 1
        tk.Label(main_frame, text="气泡缩放", font=(self.font_family, 11), fg=TEXT_MAIN, bg=DIALOG_BG).grid(row=row, column=0, sticky='w', pady=5)
        ttk.Scale(main_frame, from_=0.3, to=2.0, orient=tk.HORIZONTAL, variable=bubble_var,
                  command=on_bubble_change, length=320).grid(row=row, column=1, pady=5, sticky='ew')
        value_labels["bubble"] = tk.Label(main_frame, text="1.0", font=(self.font_family, 9), fg=TEXT_SUB,
                                          bg=DIALOG_BG, width=5)
        value_labels["bubble"].grid(row=row, column=2, sticky="w", padx=(8, 0))
        row += 1
        tk.Label(main_frame, text="输入框缩放", font=(self.font_family, 11), fg=TEXT_MAIN, bg=DIALOG_BG).grid(row=row, column=0, sticky='w', pady=5)
        ttk.Scale(main_frame, from_=0.3, to=2.0, orient=tk.HORIZONTAL, variable=input_var,
                  command=on_input_change, length=320).grid(row=row, column=1, pady=5, sticky='ew')
        value_labels["input"] = tk.Label(main_frame, text="1.0", font=(self.font_family, 9), fg=TEXT_SUB,
                                         bg=DIALOG_BG, width=5)
        value_labels["input"].grid(row=row, column=2, sticky="w", padx=(8, 0))
        row += 1
        ttk.Checkbutton(main_frame, text="同步缩放（调整任意一项时，其他两项同步变化）", variable=sync_var).grid(row=row, column=0, columnspan=3, sticky='w', pady=5)
        row += 1
        ttk.Separator(main_frame, orient='horizontal').grid(row=row, column=0, columnspan=3, sticky='ew', pady=10)
        row += 1
        tk.Label(main_frame, text="窗口宽度", font=(self.font_family, 11), fg=TEXT_MAIN, bg=DIALOG_BG).grid(row=row, column=0, sticky='w', pady=5)
        ttk.Scale(main_frame, from_=int(MIN_WINDOW_WIDTH * self._dpi_scale), to=int(MAX_WINDOW_WIDTH * self._dpi_scale), orient=tk.HORIZONTAL,
                  variable=width_var, command=on_width_change, length=320).grid(row=row, column=1, pady=5, sticky='ew')
        value_labels["width"] = tk.Label(main_frame, text="0", font=(self.font_family, 9), fg=TEXT_SUB,
                                         bg=DIALOG_BG, width=5)
        value_labels["width"].grid(row=row, column=2, sticky="w", padx=(8, 0))
        row += 1
        ttk.Separator(main_frame, orient='horizontal').grid(row=row, column=0, columnspan=3, sticky='ew', pady=10)
        row += 1
        ttk.Checkbutton(main_frame, text="隐藏回复气泡（只留提示气泡，如「我在听你说话」）",
                        variable=hide_bubble_var,
                        command=lambda: self.set_hide_reply_bubble(hide_bubble_var.get())
                        ).grid(row=row, column=0, columnspan=3, sticky='w', pady=5)
        row += 1
        RoundedButton(main_frame, text="恢复默认", command=reset_defaults, variant="subtle",
                      width=int(120 * s), height=int(34 * s), radius=int(6 * s),
                      font=(self.font_family, 10)).grid(row=row, column=0, columnspan=3, pady=5)
        row += 1
        RoundedButton(main_frame, text="关闭", command=win.destroy, width=int(120 * s), height=int(36 * s),
                      radius=int(6 * s), font=(self.font_family, 10, "bold")).grid(row=row, column=0, columnspan=3, pady=15)
        # 初始显示当前值
        _refresh_value_labels()

    def _setup_ttk_styles(self):
        """ttk 控件统一为 Win11 风格：白底、细边框、紫色选中态"""
        try:
            style = ttk.Style(self.root)
            try:
                style.theme_use("vista")
            except Exception:
                pass
            f = (self.font_family, 9)
            style.configure("TNotebook", background=CARD_BG, borderwidth=0)
            style.configure("TNotebook.Tab", background=CARD_BG, foreground=TEXT_SUB,
                            padding=(14, 6), borderwidth=0, font=f)
            style.map("TNotebook.Tab", background=[("selected", "#f4f5f7")],
                      foreground=[("selected", BTN_PRIMARY)])
            style.configure("TCombobox", fieldbackground="#ffffff", background="#ffffff",
                            foreground=TEXT_MAIN, arrowcolor=TEXT_MAIN, bordercolor=INPUT_BORDER2,
                            lightcolor=CARD_BG, darkcolor=CARD_BG, padding=4, font=f)
            style.map("TCombobox", fieldbackground=[("readonly", "#ffffff")],
                      foreground=[("readonly", TEXT_MAIN)])
            style.configure("TSpinbox", fieldbackground="#ffffff", background="#ffffff",
                            foreground=TEXT_MAIN, arrowcolor=TEXT_MAIN, bordercolor=INPUT_BORDER2,
                            lightcolor=CARD_BG, darkcolor=CARD_BG, padding=4, font=f)
            style.configure("TCheckbutton", background=CARD_BG, foreground=TEXT_MAIN,
                            font=f, focuscolor=CARD_BG)
            style.map("TCheckbutton", background=[("active", CARD_BG)])
            style.configure("Horizontal.TScale", background=CARD_BG, troughcolor="#e8eaed")
            style.map("Horizontal.TScale", background=[("active", CARD_BG)])
            style.configure("Treeview", background="#ffffff", fieldbackground="#ffffff",
                            foreground=TEXT_MAIN, borderwidth=0, rowheight=26, font=f)
            style.configure("Treeview.Heading", background="#f6f8fa", foreground=TEXT_MAIN,
                            borderwidth=0, relief="flat", font=(self.font_family, 9, "bold"))
            style.map("Treeview", background=[("selected", "#eef0ff")],
                      foreground=[("selected", BTN_PRIMARY)])
        except Exception as e:
            log.debug(f"ttk 样式初始化失败: {e}")

    def create_widgets(self):
        self._setup_ttk_styles()
        self.main_frame = tk.Frame(self.root, bg=TRANS_MASK)
        self.main_frame.pack(fill=tk.BOTH, expand=True)

        self.image_canvas = tk.Canvas(self.main_frame, highlightthickness=0, bg=TRANS_MASK)
        self.image_canvas.pack(fill=tk.X, expand=False, pady=0)
        self.image_label = tk.Label(self.image_canvas, bg=TRANS_MASK)
        self.image_label.place(relx=0.5, rely=0.5, anchor='center')

        # 精力值已隐藏

        self.bottom_frame = tk.Frame(self.main_frame, bg=TRANS_MASK)
        self.bottom_frame.pack(side=tk.BOTTOM, fill=tk.X)

        self.control_canvas = tk.Canvas(self.bottom_frame, bg=TRANS_MASK, highlightthickness=0)
        if self.input_visible:
            self.control_canvas.pack(side=tk.BOTTOM, fill=tk.X, pady=(0, 5))
        self._redraw_job = None
        self.control_canvas.bind("<Configure>", self._on_control_configure)

        self.input_font = tkfont.Font(family=self.font_family, size=self.input_font_size)
        self.input_entry = tk.Entry(self.control_canvas, font=self.input_font, bd=0, relief=tk.FLAT,
                                    bg=INPUT_BG, fg=BUBBLE_TEXT, insertbackground=BTN_PRIMARY, highlightthickness=0)
        self.input_entry.bind("<Return>", self.send_message)
        # 11/15：键盘打不进 emoji，给个入口（Ctrl+E 打开表情面板）
        self.input_entry.bind("<Control-e>", lambda e: (self.open_emoji_picker(
            lambda ch: self._insert_emoji_into(self.input_entry, ch),
            parent=self.input_entry), "break")[1])
        # 聚焦时输入框边框变品牌紫（只换背景图，不重建 Entry）
        self._input_focused = False
        self.input_entry.bind("<FocusIn>", lambda e: self._set_input_focus(True), add="+")
        self.input_entry.bind("<FocusOut>", lambda e: self._set_input_focus(False), add="+")
        # 全局回车兜底：layered 点击后键盘焦点可能游离，bind_all 保证回车始终可用
        self.root.bind_all("<Return>", self._global_return)
        self.root.bind_all("<KP_Enter>", self._global_return)

        # 右键菜单（Win11 风格自绘：白色圆角卡片 + 悬停高亮 + 级联子菜单）
        self.menu = ModernMenu(self.root, pet=self)

        # ── 模式子菜单 ──
        self.mode_menu = ModernMenu(self.root, pet=self)
        self.mode_menu.add_command(label="🎮 陪玩模式 (开始)", command=self.toggle_watch_mode)
        self.watch_menu_index = self.mode_menu.index("end")
        self.mode_menu.add_command(label="📖 陪我读书 (开始)", command=self.toggle_reading)
        self.reading_menu_index = self.mode_menu.index("end")
        self.mode_menu.add_command(label="🎤 语音识别 (开始)", command=self.toggle_voice)
        self.voice_menu_index = self.mode_menu.index("end")
        tts_speak_label = "🔊 语音朗读 (停止)" if self.tts_enabled else "🔊 语音朗读 (开始)"
        self.mode_menu.add_command(label=tts_speak_label, command=self.toggle_tts_speak)
        self.tts_speak_menu_index = self.mode_menu.index("end")
        self.menu.add_command(label="🪟 打开面板", command=self.open_control_center)
        self.menu.add_separator()
        self.menu.add_cascade(label="🎮 模式", menu=self.mode_menu)
        self.menu.add_separator()

        # ── 日常互动 ──
        self.menu.add_command(label="💬 换个话题", command=self.generate_topic_manual)
        self.menu.add_command(label="💤 睡觉", command=lambda: self.start_sleep_mode(manual=True))
        self.menu.add_command(label="⚡ 精力值", command=self.show_energy_status)
        # ── 形象（多形态）：一级菜单一行，点开选穿哪一套 Live2D ──
        self.form_menu = ModernMenu(self.root, pet=self)
        self.form_menu_indices = {}
        for _fk in available_forms():
            self.form_menu.add_command(label=self._form_menu_label(_fk),
                                       command=lambda k=_fk: self.set_form(k))
            self.form_menu_indices[_fk] = self.form_menu.index("end")
        self.menu.add_cascade(label="🐟 形象", menu=self.form_menu)
        self.menu.add_command(label="⌨️ 显示/隐藏输入框", command=self.toggle_input_frame)
        self.menu.add_separator()

        # 11/09：设置与记录都搬进控制中心面板了（右键菜单不再挂这两组）
        self.menu.add_separator()

        self.menu.add_command(label="退出", command=self.on_close)

        # 11/15：表情按钮的点击（tag_bind 一次即可，画布重绘不影响）
        try:
            self.control_canvas.tag_bind(
                "emoji_btn", "<Button-1>",
                lambda e: self.open_emoji_picker(
                    lambda ch: self._insert_emoji_into(self.input_entry, ch),
                    parent=self.input_entry))
        except Exception as e:
            log.debug("表情按钮绑定失败: %s", e)
        self.root.bind("<Button-3>", self.show_menu)
        self.root.after(100, self.draw_input_background)

    def _on_control_configure(self, event):
        if self._redraw_job:
            self.root.after_cancel(self._redraw_job)
        self._redraw_job = self.root.after(50, self.draw_input_background)

    def draw_input_background(self, focused=None, keep_entry=False):
        w = self.control_canvas.winfo_width()
        h = self.control_canvas.winfo_height()
        if w < 10 or h < 10:
            return
        if focused is None:
            focused = getattr(self, "_input_focused", False)
        r = max(6, int(8 * self._dpi_scale))
        pad = 6
        x1, y1 = pad, pad + 2
        x2, y2 = w - pad, h - pad + 2
        # 用 PIL 超采样生成平滑圆角背景（白底 + 1px 细边框；聚焦时边框变品牌紫。
        # 不加柔影层——灰色偏移在透明窗口上会形成多余的“描边”）
        from PIL import Image, ImageDraw
        scale = 3
        W, H = max(2, w * scale), max(2, h * scale)
        img = Image.new('RGBA', (W, H), (0, 0, 0, 0))
        d = ImageDraw.Draw(img)
        rr = r * scale
        border = BTN_PRIMARY if focused else INPUT_BORDER2
        d.rounded_rectangle([x1 * scale, y1 * scale, x2 * scale, y2 * scale],
                            radius=rr, fill="#ffffff")
        d.rounded_rectangle([x1 * scale, y1 * scale, x2 * scale, y2 * scale],
                            radius=rr, outline=border, width=scale)
        img = img.resize((w, h), Image.LANCZOS)
        self._input_bg_photo = ImageTk.PhotoImage(_snap_alpha(img))
        # 聚焦态只换背景图、不重建输入框（重建会让 Entry 失焦 → FocusOut → 死循环）
        if keep_entry and getattr(self, "_input_bg_item", None) is not None:
            try:
                self.control_canvas.itemconfigure(self._input_bg_item, image=self._input_bg_photo)
                return
            except Exception:
                pass
        self.control_canvas.delete("all")
        self._input_bg_item = self.control_canvas.create_image(0, 0, anchor='nw', image=self._input_bg_photo)
        # 输入框（右边留出表情按钮的位置）
        entry_pad = 14
        _emoji_w = int(30 * self._dpi_scale)
        self.control_canvas.create_window(
            x1 + entry_pad, y1 + entry_pad - 2, anchor="nw", window=self.input_entry,
            width=max(40, x2 - x1 - 2 * entry_pad - _emoji_w - 4),
            height=y2 - y1 - 2 * entry_pad + 4)
        # 11/15：表情按钮（点开应用内表情面板）——Tk 收不到系统 emoji 面板的输入，给它一个自己的入口
        self.control_canvas.create_text(
            x2 - entry_pad - _emoji_w // 2, (y1 + y2) // 2, text="😊",
            font=(self.font_family, int(10 * self._dpi_scale)), fill=TEXT_SUB, tags=("emoji_btn",))
        if focused:
            self.input_entry.focus_set()

    def _set_input_focus(self, on):
        self._input_focused = on
        try:
            self.draw_input_background(focused=on, keep_entry=True)
        except Exception:
            pass

    def toggle_input_frame(self, save=True):
        if self.input_visible:
            self.control_canvas.pack_forget()
            self.input_visible = False
            self.update_window_size()
        else:
            self.control_canvas.pack(side=tk.BOTTOM, fill=tk.X, pady=(0, 5))
            self.input_visible = True
            self.update_window_size()
            self.root.after(50, self.input_entry.focus_set)
            self.root.after(50, self.draw_input_background)
        if save:
            self._save_ui_state()   # 只有用户自己切换才记进配置（陪玩自动收起不算）

    def on_drag_start(self, event):
        self.drag_x = event.x_root - self.root.winfo_x()
        self.drag_y = event.y_root - self.root.winfo_y()
        self.dragging = True
        self._drag_start_x = event.x_root
        self._drag_start_y = event.y_root

    def on_drag_move(self, event):
        if self.dragging:
            x = event.x_root - self.drag_x
            y = event.y_root - self.drag_y
            self.root.geometry(f"+{x}+{y}")
            self._win_x, self._win_y = x, y
    def on_drag_stop(self, event):
        if not self.dragging:
            return
        self.dragging = False
        dx = abs(event.x_root - self._drag_start_x)
        dy = abs(event.y_root - self._drag_start_y)
        if dx < 5 and dy < 5:
            self.last_interaction_time = time.time()
            if self.watch_mode and not self.sleep_mode:
                log.debug("手动触发截图分析")
                self.analyze_and_comment(force=True)
    def bind_drag_events(self):
        for w in [self.image_canvas, self.image_label, self.control_canvas]:
            w.bind("<Button-1>", self.on_drag_start)
            w.bind("<B1-Motion>", self.on_drag_move)
            w.bind("<ButtonRelease-1>", self.on_drag_stop)

    # ---------- Live2D 渲染 ----------
    def _start_spine(self):
        if not SPINE_AVAILABLE or self.spine:
            return
        try:
            self.spine = Live2DRenderer(self.root, form=self.form)

            disp_w = self.char_size
            disp_h = int(self.char_size * 0.8)
            # 离屏缓冲要能容纳"最大显示尺寸 × 最大聚焦缩放"，否则渲染区域被截断、
            # 主线程就得把小板放大（LANCZOS 过冲会在轮廓上留下亮描边）
            _fbo_w = min(3072, int(BASE_IMAGE_SIZE * self._dpi_scale * MAX_ZOOM_CHAR))
            _fbo_h = min(3072, int(_fbo_w * 0.8))
            self.spine.start(width=_fbo_w, height=_fbo_h,
                             on_frame=self._on_renderer_frame)
            try:
                self.spine.set_size(disp_w, disp_h)
            except Exception:
                pass
            self.spine_enabled = True

            # 创建 Win32 layered window 显示（per-pixel alpha，消除白边）
            self.layered = None
            if LAYERED_AVAILABLE:
                try:
                    self.layered = LayeredImageWindow(disp_w, disp_h)
                    self.layered.show()
                except Exception as e:
                    log.error("layered window 创建失败: %s", e)
                    self.layered = None

            # 全局鼠标跟踪（后台线程轮询屏幕坐标）
            _eye_spine = self.spine    # 认准本线程服务的那个渲染器
            def global_eye_track():
                # 换形象会换渲染器：旧线程到这一轮就该退场，不然每换一次多一个常驻线程
                while self.spine_enabled and self.spine is _eye_spine:
                    try:
                        # 睡眠时不追踪鼠标，眼睛回正
                        if self.sleep_mode:
                            _eye_spine.track_mouse(0.0, 0.0)
                        else:
                            p = wintypes.POINT()
                            ctypes.windll.user32.GetCursorPos(ctypes.byref(p))
                            cx = self._win_x + self.window_width // 2
                            # 基准行由渲染端按当前构图（显示尺寸×聚焦缩放）给出，
                            # 放大时跟着脸走；渲染端还没给就用旧比例兜底
                            cy = self._win_y + (getattr(self.spine, 'face_row', None)
                                                or int(self.char_size * 0.16))
                            mx = (p.x - cx) / (self._screen_w * GAZE_RANGE_X)
                            my = -(p.y - cy) / (self._screen_h * GAZE_RANGE_Y)
                            _eye_spine.track_mouse(
                                max(-1, min(1, mx)),
                                max(-1, min(1, my)))
                    except Exception:
                        pass
                    time.sleep(0.05)
            threading.Thread(target=global_eye_track, daemon=True).start()

            log.info("Live2D 离屏渲染已启动")
            self._spine_render_loop()
        except Exception as e:
            log.error("Live2D 启动失败: %s", e)
            self.spine = None
            self.spine_enabled = False

    def _check_form_swap(self):
        """换形象的异步核对（10/12）。

        渲染线程装载完会在 spine.form_loaded 写下形态名 ⇒ 这时才落盘、才报"已换成"；
        如果它崩了（crash_note 有值 / is_ready() 变 False）或等太久，就把"账"回滚：
        self.form 退回上一个、配置不写成坏形态、菜单勾回去，并提示"再选一次形象"。
        画面上她仍停在旧形态的最后一帧 —— 再选任意形态会走回退路径重建渲染器救回来。
        """
        pend = getattr(self, '_form_pending', None)
        if not pend:
            return
        key, prev, t0, label = pend
        spine = self.spine
        if spine is not None and getattr(spine, 'form_loaded', None) == key:
            self._form_pending = None
            try:
                save_form_config(key)             # 确认装载成功了才落盘
            except Exception as e:
                log.warning("保存形象设置失败: %s", e)
            self._refresh_form_menu()
            self.show_bubble_text(f"(normal) 形象已换成{label}", "normal", status=True)
            log.info("形象已切换为 %s", label)
            return
        dead = (spine is None) or (not self.spine_enabled) or (not spine.is_ready())
        overtime = (time.time() - t0) > 20.0      # 装载再慢也不该超过 20 秒
        if not dead and not overtime:
            return                                 # 还在装，接着等
        self._form_pending = None
        why = getattr(spine, 'crash_note', None) if spine is not None else None
        log.error("换形象没成功（%s）：目标=%s 回滚=%s%s", "渲染线程崩了" if dead else "超时",
                  key, prev, ("；原因=" + str(why)) if why else "")
        self.form = prev                           # 账回滚：菜单能再点、重启也不会进坏状态
        self.costume_choice = self._load_costumes_for(prev)
        self._refresh_prompt_for_form(prev)        # 提示词也要跟着退回旧形态
        try:
            save_form_config(prev)
        except Exception:
            pass
        self._refresh_form_menu()
        self.show_bubble_text("(worried) 形象没换成，渲染卡住了……再选一次形象试试，还不行就重启桌宠",
                              "worried", status=True)

    def _on_renderer_frame(self, src_w_full, src_h_full, rgba_bytes):
        if not self._costume_applied and self.spine is not None and self.spine.is_ready():
            try:
                self._apply_saved_costumes()
            except Exception as e:
                log.warning("恢复装扮异常: %s", e)
        """renderer 线程：帧已是显示尺寸（渲染端不再做聚焦裁剪），这里只缩放到显示尺寸。"""
        if not self.spine_enabled:
            return
        layered = self.layered
        if layered is None:
            return
        try:
            target_w = layered.width
            target_h = layered.height
            x, y, _, _ = self._layered_geometry_safe()
            if src_w_full == target_w and src_h_full == target_h:
                layered.update_rgba(rgba_bytes, x, y)   # 尺寸已吻合，直接推帧
                return
            pil = Image.frombuffer('RGBA', (src_w_full, src_h_full), rgba_bytes, 'raw', 'RGBA', 0, 1)
            # 用 BILINEAR：LANCZOS 的负瓣会在轮廓过冲出亮边（"描边"就是它造成的）
            final = pil.resize((target_w, target_h), Image.BILINEAR)
            layered.update_rgba(final.tobytes(), x, y)
        except Exception:
            pass

    def _layered_geometry_safe(self):
        try:
            disp_w = self.char_size
            disp_h = int(self.char_size * 0.8)
            # 使用主线程缓存的坐标，避免渲染线程跨线程调用 winfo_*
            x = self._win_x + (self.window_width - disp_w) // 2
            y = self._win_y
            return x, y, disp_w, disp_h
        except Exception:
            return 0, 0, self.char_size, int(self.char_size * 0.8)

    def _spine_render_loop(self):
        """主线程：消费 layered 事件 + 尺寸变更时重建 layered。
        像素更新已搬到 renderer 线程的 _on_renderer_frame。"""
        self._check_form_swap()          # 换形象是异步的：在这一 tick 里核对"究竟换成了没"
        if not self.spine_enabled or not self.spine:
            return
        disp_w = self.char_size
        disp_h = int(self.char_size * 0.8)
        # 渲染端按显示尺寸渲染并 1:1 读回；尺寸变了只推命令，不重启渲染线程
        if (disp_w, disp_h) != getattr(self, "_pushed_size", None):
            self._pushed_size = (disp_w, disp_h)
            try:
                self.spine.set_size(disp_w, disp_h)
            except Exception:
                pass
        if self.layered is None:
            # 降级：tk Label（帧已由渲染端裁剪，这里只缩放）
            frame = self.spine.get_frame()
            if frame:
                final = frame.resize((disp_w, disp_h), Image.BILINEAR)
                photo = ImageTk.PhotoImage(final)
                self.image_label.config(image=photo)
                self.image_label.image = photo
            self._spine_loop_job = self.root.after(16, self._spine_render_loop)
            return

        # 尺寸变更时在主线程重建
        if disp_w != self.layered.width or disp_h != self.layered.height:
            try: self.layered.destroy()
            except Exception: pass
            self.layered = LayeredImageWindow(disp_w, disp_h)
            self.layered.show()
            if getattr(self, "_click_through", False):
                self.layered.set_bypass(True)
        # 消费事件（含全局热键 Ctrl+Shift+G —— 10/19 起它是"点击穿透"开关，不再是陪玩开关）
        for ev in self.layered.poll_events():
            if ev[0] == 'hotkey':
                self.toggle_click_through()
            else:
                self._handle_layered_event(*ev)

        self._spine_loop_job = self.root.after(16, self._spine_render_loop)

    def toggle_click_through(self):
        """切换"点击穿透"（全局热键 Ctrl+Shift+G）。

        10/19 按用户要求改：这个热键原来开关陪玩，现在只管穿透；
        陪玩也不再强制穿透（原来一开陪玩窗口就点不到了）。
        开启后角色窗口对鼠标完全透明，控制面板不受影响，所以还能从菜单操作。
        """
        if self.layered is None:
            self.show_bubble_text("(worried) 现在没有窗口，设不了穿透…", "worried", status=True)
            return
        new_state = not getattr(self, "_click_through", False)
        try:
            self.layered.set_bypass(new_state)
        except Exception as e:
            log.warning("切换点击穿透失败: %s", e)
            self.show_bubble_text("(worried) 穿透没切成…", "worried", status=True)
            return
        self._click_through = new_state
        # 气泡是独立窗口，穿透要单独同步（否则它盖在屏幕上继续吃点击）
        try:
            bw = getattr(self, "bubble_window", None)
            if bw is not None and bw.visible:
                bw.apply_click_through(new_state)
        except Exception as e:
            log.debug("切换穿透时同步气泡失败: %s", e)
        # 10/19：穿透期间强制收起输入框（不写进配置）；关掉时恢复穿透前的状态
        try:
            if new_state:
                self._input_visible_before_ct = getattr(self, "input_visible", True)
                if getattr(self, "input_visible", False):
                    self.toggle_input_frame(save=False)
            else:
                if getattr(self, "_input_visible_before_ct", True) and not getattr(self, "input_visible", False):
                    self.toggle_input_frame(save=False)
        except Exception as e:
            log.debug("穿透时切换输入框失败: %s", e)
        log.info("点击穿透: %s", "开启" if new_state else "关闭")
        if new_state:
            self.show_bubble_text("(relaxed) 好，鼠标先从我身上穿过去～", "relaxed", status=True)
        else:
            self.show_bubble_text("(happy) 又能点到我了", "happy", status=True)

    def _handle_layered_event(self, kind, sx, sy):
        try:
            if kind == 'press':
                self._layered_drag_off = (sx - self.root.winfo_x(), sy - self.root.winfo_y())
                self._layered_press_xy = (sx, sy)
                self._layered_moved = False
                self.last_interaction_time = time.time()
            elif kind == 'drag':
                px, py = self._layered_press_xy
                if abs(sx - px) > 3 or abs(sy - py) > 3:
                    self._layered_moved = True
                ox, oy = self._layered_drag_off
                self.root.geometry(f"+{sx - ox}+{sy - oy}")
            elif kind == 'release':
                if self._layered_moved:
                    return
                self.last_interaction_time = time.time()
                if self.spine and self.spine_enabled:
                    if self.sleep_mode:
                        self.stop_sleep_mode(cause="click")
                    else:
                        self.spine.begin_click()
                        self.do_action(from_click=True)     # 点她一下，她做件事
                if self.watch_mode and not self.sleep_mode:
                    self.analyze_and_comment(force=True)
            elif kind == 'right':
                class _E: pass
                e = _E(); e.x_root = sx; e.y_root = sy
                self.show_menu(e)
        except Exception as e:
            log.warning(f"layered 事件处理异常: {e}")

    def _form_menu_label(self, key):
        """形象菜单里那一行：当前穿的那套打个勾"""
        mark = "✓ " if key == getattr(self, 'form', None) else "   "
        return mark + LIVE2D_FORMS.get(key, {}).get('label', key)

    def _refresh_form_menu(self):
        for _fk, _idx in getattr(self, 'form_menu_indices', {}).items():
            try:
                self.form_menu.entryconfigure(_idx, label=self._form_menu_label(_fk))
            except Exception:
                pass

    def _refresh_prompt_for_form(self, form):
        """换形态后重建系统提示词：有 Cue 动作才带【身体】段。"""
        try:
            self.system_prompt = build_system_prompt(
                self.pet_name, self.character_config["persona"], self.max_chars,
                self.style_rules, has_cues=self._form_has_cues(form),
                look_line=self._current_look_line())
            self.full_system = build_full_system_prompt(self.system_prompt, self.user_profile)
            log.info("提示词已重建：【身体】=%s 【此刻】=%s", "【身体】" in self.system_prompt,
                     "【此刻】" in self.system_prompt)
            log.info("此刻行：%s", self._current_look_line())
        except Exception as e:
            log.warning("重建提示词失败: %s", e)

    def _current_look_line(self):
        """「此刻」一行：把当前形象和她身上的东西写成她能想象的样子。"""
        try:
            label = (LIVE2D_FORMS.get(getattr(self, "form", "")) or {}).get("label", "")
            if not label:
                return ""
            sl = costume_cfg(getattr(self, "form", ""))[0] or []
            _order = {_s: _i for _i, _s in enumerate(COSTUME_LOOK_ORDER)}
            sl = sorted(sl, key=lambda _x: _order.get(_x[0], 99))
            bits = []
            for slot, _slot_label, _clear, items in sl:
                if (getattr(self, "form", ""), slot) in COSTUME_LOOK_SKIP:
                    continue
                val = (self.costume_choice or {}).get(slot)
                vals = list(val) if isinstance(val, (list, tuple)) else ([val] if val else [])
                if not vals:
                    # 配件类（眼镜/头顶）没有就不写；服装与身体要如实写平常状态
                    if slot == "body":
                        d = BODY_DEFAULT_TEXT.get(getattr(self, "form", ""), "")
                        if d:
                            bits.append(d)
                    else:
                        d = COSTUME_DEFAULT_TEXT.get((getattr(self, "form", ""), slot))
                        if d:
                            bits.append(d)
                    continue
                _combo = COSTUME_LOOK_TEXT.get((slot, tuple(str(v) for v in vals)))
                if _combo:
                    bits.append(_combo)
                    continue
                descs = [COSTUME_LOOK_TEXT.get((slot, str(v))) for v in vals]
                descs = [d for d in descs if d]
                if descs:
                    if slot == "display":
                        # 「桌面显示」可多选：把物件合成一句，别重复"桌面上放着"
                        _obj = [d for d in descs if d != "巴菲收起来了"]
                        if _obj:
                            bits.append("桌面上放着" + "、".join(_obj))
                        if "巴菲收起来了" in descs:
                            bits.append("巴菲收起来了")
                    else:
                        bits.append("、".join(descs))
            line = "【此刻】你现在是「%s」这套形象" % label
            if bits:
                line += "：%s" % "；".join(bits)
            line += "。除非他问起或提到，不要主动说自己穿什么、长什么样。"
            return line
        except Exception as e:
            log.debug("拼当前形象失败: %s", e)
            return ""

    def _form_has_cues(self, form):
        """这个形态有没有〔词〕动作（model3.json 里的 Cue 组）——没有就不往提示词里写【身体】。"""
        try:
            if not form:
                form = load_form_config()
            info = LIVE2D_FORMS.get(form) or {}
            base = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "live2d_viewer", info.get("dir", ""))
            with open(os.path.join(base, info.get("json", "")), encoding="utf-8") as f:
                md = json.load(f)
            return bool(((md.get("FileReferences", {}).get("Motions", {}) or {}).get("Cue")))
        except Exception:
            return False

    def _stash_costumes(self, form):
        """把当前形态的装扮选择存进按形态分组的表里。"""
        if not form:
            return
        if getattr(self, "_costume_by_form", None) is None:
            self._costume_by_form = {}
        self._costume_by_form[form] = dict(getattr(self, "costume_choice", {}) or {})

    def _load_costumes_for(self, form):
        """取某个形态自己的装扮选择（没有就空表）。"""
        if getattr(self, "_costume_by_form", None) is None:
            self._costume_by_form = {}
        return dict(self._costume_by_form.get(form) or {})

    def set_form(self, key):
        """切换形象。

        10/12 改：正常路径走"**渲染线程内换模型**" —— 不销毁渲染线程、不重建 GL 上下文、
        也不拆分层窗口。旧做法（停线程 → 等它退出 → 重建上下文）偶尔会卡在显卡驱动里
        （faulthandler 抓到停在 `lapp_model.py Draw`），等不到就只能放弃这次切换；而且那整套
        "上下文 churn" 本身就是退出/换形象崩溃的触发源。现在换形态只是同一个上下文里换个模型，
        下面那段"等不到就停住"的回退只在渲染器还没起来时才会走到。
        """
        if key not in LIVE2D_FORM_ORDER or key == getattr(self, 'form', None):
            return
        label = LIVE2D_FORMS.get(key, {}).get('label', key)
        prev = getattr(self, 'form', None)

        # 正常路径：渲染器活着 → 线程内换模型（主线程不碰窗口、不碰上下文）
        if self.spine is not None and self.spine_enabled and self.spine.is_ready():
            self._stash_costumes(prev)
            self.form = key
            self.costume_choice = self._load_costumes_for(key)
            self._refresh_prompt_for_form(key)
            self._costume_applied = False   # 新形态的装扮要重新穿一遍（_on_renderer_frame 里做）
            self._pushed_size = None        # 让 _spine_render_loop 重新推一次显示尺寸
            try:
                self.spine.set_form(key)
            except Exception as e:
                log.error("切换形象失败: %s", e)
                self.form = prev
                self.costume_choice = self._load_costumes_for(prev)
                self._refresh_prompt_for_form(prev)
                return
            # 换模型是异步的：先记下"在等确认"，等渲染线程报回装载成功才落盘、才报成功（10/12）
            self._form_pending = (key, prev, time.time(), label)
            self.show_bubble_text("(normal) 正在换形象……", "normal", status=True)
            return

        # 回退路径：渲染器还没起（或已经挂了）→ 老办法，重建；等不到旧线程退出就停住别硬撑
        self._stash_costumes(prev)
        self.form = key                           # _start_spine 按 self.form 建，这里必须先改过来
        self.costume_choice = self._load_costumes_for(key)
        self._refresh_prompt_for_form(key)
        try:
            if not self._stop_spine(wait=8.0):
                log.error("切换形象失败：旧渲染线程 8 秒内没退出（多半卡在显卡驱动里），未创建新上下文")
                self.form = prev
                self.costume_choice = self._load_costumes_for(prev)
                self._refresh_prompt_for_form(prev)
                try:
                    save_form_config(prev)        # 没换成就不写配置，免得下次开机还是坏的
                except Exception:
                    pass
                self._refresh_form_menu()
                self.show_bubble_text("(worried) 形象没换成，渲染卡住了……重启一下桌宠就好", "worried", status=True)
                return
            self._costume_applied = False
            self._start_spine()
        except Exception as e:
            log.error("切换形象失败: %s", e)
        # 重建同样是异步装载：一样等渲染线程报回成功再落盘/报成功
        self._form_pending = (key, prev, time.time(), label)
        self.show_bubble_text("(normal) 正在换形象……", "normal", status=True)

    def _stop_spine(self, wait=5.0):
        """停渲染线程。返回 True = 线程确认退出（可以安全建新的）；False = 没退出（此时**不要**建新的）。

        注意区分两件事的先后：线程没确认退出之前，连分层窗口都不拆 —— 她还能留在屏幕上
        （哪怕最后一帧是静止的），总比整只消失好。
        """
        self.spine_enabled = False
        if self.spine:
            try:
                # GL 上下文是渲染线程建的，只有它能安全释放；释放干净之前起新线程，
                # 两份驱动状态互踩 ⇒ nvoglv64.dll 访问冲突（0xc0000005）
                if not self.spine.destroy(wait=wait):
                    log.warning("渲染线程 %.0f 秒内没退出（可能卡在驱动里）；保留当前窗口，不创建新上下文", wait)
                    self.spine = None
                    return False
            except Exception as e:
                log.warning("关闭渲染线程异常: %s", e)
            self.spine = None
        if getattr(self, 'layered', None):
            try: self.layered.destroy()
            except Exception: pass
            self.layered = None
        return True

    def set_emotion(self, emotion):
        if self.spine_enabled and self.spine and self.spine.is_ready():
            try:
                self.spine.set_emotion(emotion)
            except Exception:
                pass

    def restore_expression(self):
        """气泡淡出后恢复待机表情"""
        if self.sleep_mode:
            return
        if not (self.spine_enabled and self.spine and self.spine.is_ready()):
            return
        try:
            self.spine.set_emotion("normal")
        except Exception:
            pass

    def _system_idle_seconds(self):
        """整个 Windows 会话的空闲秒数（GetLastInputInfo：鼠标/键盘，跨程序都算）。

        取不到就返回 0（宁可"不自动睡"，也不要误判他在用电脑时把她哄睡）。
        """
        try:
            class _LASTINPUTINFO(ctypes.Structure):
                _fields_ = [("cbSize", wintypes.UINT), ("dwTime", wintypes.DWORD)]
            info = _LASTINPUTINFO()
            info.cbSize = ctypes.sizeof(_LASTINPUTINFO)
            if not ctypes.windll.user32.GetLastInputInfo(ctypes.byref(info)):
                return 0.0
            tick = ctypes.windll.kernel32.GetTickCount()
            elapsed_ms = (tick - info.dwTime) & 0xFFFFFFFF     # 32 位计数回绕也安全
            return max(0.0, elapsed_ms / 1000.0)
        except Exception:
            return 0.0

    def _should_auto_sleep(self):
        """够不够格自动睡：她的交互时间够久 **且** 系统（鼠标键盘）也空闲够久。

        10/17 改：原来只看 last_interaction_time —— 它只在**真实互动**（点她/发消息/对她说话）时刷新，
        动鼠标、打字都不算 ⇒ 他人在电脑前（只是没碰桌宠）也会被判"走了"，表现为"回来一动鼠标她才睡"。
        陪玩/陪读**故意不刷新**它（用户的设计）：开着陪玩离开一小时 ⇒ 自动睡 ⇒ 顺手关掉陪玩，防止白烧 API。
        """
        if self.sleep_mode:
            return False
        if time.time() - self.last_interaction_time <= IDLE_TIMEOUT:
            return False
        return self._system_idle_seconds() > IDLE_TIMEOUT

    def start_idle_check(self):
        def check():
            if self._should_auto_sleep():
                try:
                    log.info("自动睡：无互动 %.1f 分钟，系统空闲 %.1f 分钟（阈值 %.0f 分钟）",
                             (time.time() - self.last_interaction_time) / 60.0,
                             self._system_idle_seconds() / 60.0, IDLE_TIMEOUT / 60.0)
                except Exception:
                    pass
                self.start_sleep_mode(manual=False)
            self.idle_check_job = self.root.after(60000, check)
        check()

    def _global_return(self, event=None):
        """全局回车键兜底——layered 点击后焦点游离时也能发送。"""
        if event is not None:
            widget = getattr(event, 'widget', None)
            # 焦点在对话框（非主窗口）时不拦截回车，避免误触发发消息
            if widget is not None:
                try:
                    if widget.winfo_toplevel() is not self.root:
                        return
                except Exception:
                    return
            # event.widget 是 Entry 时 Entry 自己的 <Return> 已经触发，避免重复
            if widget is self.input_entry:
                return
        self.send_message()
        return "break"

    # ---------- 输入表情（11/15）----------
    @staticmethod
    def _insert_emoji_into(widget, ch):
        """把表情插到光标处（Entry / Text 通用）；插完把焦点还给它。"""
        try:
            widget.insert(tk.INSERT, ch)
            widget.focus_set()
        except Exception as e:
            log.debug("插入表情失败: %s", e)

    def open_emoji_picker(self, on_pick, parent=None):
        """小表情面板：点一下就把表情插进输入框（键盘打不进来的兜底）。"""
        try:
            s = self._dpi_scale
            win, frame = self._make_card_window("表情", 380, 300)
            tk.Label(frame, text="点一个插到光标处", font=(self.font_family, 9),
                     fg=TEXT_SUB, bg=DIALOG_BG).pack(anchor="w", padx=int(12 * s))
            grid = tk.Frame(frame, bg=DIALOG_BG)
            grid.pack(padx=int(10 * s), pady=int(6 * s))
            cols = 8

            def _pick(ch):
                try:
                    on_pick(ch)
                finally:
                    win.destroy()

            for idx, ch in enumerate(EMOJI_PICKER):
                b = tk.Label(grid, text=ch, font=(self.font_family, 17), bg=DIALOG_BG,
                             fg=TEXT_MAIN, width=2, cursor="hand2")
                b.grid(row=idx // cols, column=idx % cols, padx=2, pady=2)
                b.bind("<Button-1>", lambda e, c=ch: _pick(c))
                b.bind("<Enter>", lambda e, w=b: w.config(bg="#eef0f5"))
                b.bind("<Leave>", lambda e, w=b: w.config(bg=DIALOG_BG))
            return win
        except Exception as e:
            log.warning("表情面板打开失败: %s", e)
            return None

    # ---------- 输入表情结束 ----------

    def send_message(self, event=None):
        msg = self.input_entry.get().strip()
        if not msg:
            return
        if self.sleep_mode:
            # 睡着时打字不唤醒她、不进模型、不出声，只提示一句
            self._show_sleep_hint()
            self.input_entry.delete(0, tk.END)
            return
        # 10/15：这里原来调 _stop_music_for_chat()（一对话就把音乐彻底停掉、之后不再续播）。
        # 现在她说话时只把音乐音量压低当背景音（见 _music_duck_for_tts），所以聊天也不停音乐了。
        self.last_interaction_time = time.time()
        self.consume_energy()
        self.input_entry.delete(0, tk.END)
        if getattr(self, "event_frame", None):
            self.clear_event_buttons()      # 11/02：自己打字回应了，旧选项就别挂着
        # 如果有活跃的话题事件，将输入作为话题回应
        if self.current_event_context:
            self.on_event_text(msg)
            return
        self._show_thinking_bubble()
        def process():
            reply = self.get_ai_response(msg)
            self._ui(lambda: self.handle_ai_reply(reply, msg))
        threading.Thread(target=process, daemon=True).start()

    def _reading_context_digest(self):
        """给聊天路径用的"最近读过"摘要（会话级：读书关掉再开会清空）"""
        rc = getattr(self, "reading_companion", None)
        if rc is None:
            return ""
        try:
            return rc.recent_digest()
        except Exception as e:
            log.debug(f"最近读过摘要生成失败: {e}")
            return ""

    # ---------- 自我卡：她自己的一页（P4，11/14）----------
    def _selfcard_get(self):
        """{"text":..., "updated_at":..., "history":[{text, saved_at, why}]}"""
        st = getattr(self, "_selfcard", None)
        if isinstance(st, dict):
            return st
        st = {"text": "", "updated_at": "", "history": []}
        try:
            raw = load_json_file(SELFCARD_FILE, {})
            if isinstance(raw, dict):
                st["text"] = str(raw.get("text") or "")
                st["updated_at"] = str(raw.get("updated_at") or "")
                hist = raw.get("history")
                st["history"] = hist if isinstance(hist, list) else []
        except Exception as e:
            log.debug("读自我卡失败: %s", e)
        self._selfcard = st
        return st

    def _selfcard_save(self, text, why="手改"):
        """保存自我卡；旧版本进 history（最多留 10 版）。"""
        text = str(text or "").strip()
        if len(text) > SELFCARD_MAX_CHARS:
            text = text[:SELFCARD_MAX_CHARS]
        st = self._selfcard_get()
        old_text = str(st.get("text") or "").strip()
        if old_text and old_text != text:
            st["history"].append({"text": old_text,
                                  "saved_at": st.get("updated_at") or "",
                                  "why": why})
            if len(st["history"]) > SELFCARD_KEEP_VERSIONS:
                del st["history"][:len(st["history"]) - SELFCARD_KEEP_VERSIONS]
        st["text"] = text
        st["updated_at"] = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        self._selfcard = st
        try:
            save_json_file(SELFCARD_FILE, st)
        except Exception as e:
            log.warning("自我卡落盘失败: %s", e)
        return st

    def _selfcard_block(self):
        """注入用文本；空就返回空串（没写就不占篇幅）。"""
        text = str(self._selfcard_get().get("text") or "").strip()
        if not text:
            return ""
        return "【你自己现在是什么样】" + chr(10) + text

    def _selfcard_last_epoch(self):
        st = self._selfcard_get()
        last = str(st.get("updated_at") or "")
        try:
            return time.mktime(time.strptime(last[:19], "%Y-%m-%d %H:%M:%S")) if last else 0.0
        except Exception:
            return 0.0

    def _selfcard_should_refresh(self):
        """该不该重写这一页：有新东西才写，最长 7 天兜底，最短 72 小时防抖。"""
        last = self._selfcard_last_epoch()
        now = time.time()
        if not last:
            return True, "还没写过"
        if now - last < SELFCARD_MIN_HOURS * 3600:
            return False, "防抖（不到 %d 小时）" % SELFCARD_MIN_HOURS
        _fresh = 0
        _flip = 0
        for i in (self.memory_data.get("impressions") or []):
            try:
                if self._mem_created_epoch({"created_at": i.get("created_at")}) > last:
                    _fresh += 1
            except Exception:
                pass
            try:
                _inv = i.get("invalid_at")
                if _inv and self._mem_created_epoch({"created_at": _inv}) > last:
                    _flip += 1
            except Exception:
                pass
        if _fresh >= SELFCARD_NEW_IMPRESSIONS:
            return True, "新增 %d 条看法" % _fresh
        if _flip >= 1:
            return True, "发生过改口"
        if now - last >= SELFCARD_REFRESH_DAYS * 86400:
            return True, "%d 天没改了" % SELFCARD_REFRESH_DAYS
        return False, "没有新东西（%d 天前改的）" % int((now - last) / 86400)

    def _selfcard_crystallize(self, force=False):
        """每周一次：读她最近的原话 + 他的反应，让她重写这一页（允许不改）。"""
        st = self._selfcard_get()
        last = str(st.get("updated_at") or "")
        if not force and last:
            try:
                _days = (time.time() - time.mktime(time.strptime(last[:19], "%Y-%m-%d %H:%M:%S"))) / 86400.0
                if _days < SELFCARD_REFRESH_DAYS:
                    return None
            except Exception:
                pass
        # 素材（11/14 改）：最近 7 天封存的箱子 + 未封箱 + 当前缓冲 + 印象 + 关系形象 + 旧版
        cutoff = time.time() - SELFCARD_REFRESH_DAYS * 86400.0
        _raw_turns = []
        try:
            for _b in (self._box_state().get("boxes") or []):
                if float(_b.get("ended") or 0) < cutoff:
                    continue
                for _t in (_b.get("turns") or []):
                    _raw_turns.append(_t)
            for _t in ((self._box_state().get("open_box") or {}).get("turns") or []):
                _raw_turns.append(_t)
        except Exception as e:
            log.debug("结晶读箱子失败: %s", e)
        for turn in (self.chat_buffer or []):
            try:
                _raw_turns.append({"u": turn[0].get("content"), "a": turn[1].get("content"),
                                   "src": turn[0].get("source") or "chat"})
            except Exception:
                continue

        lines = []
        _my_lines = []
        _seen = set()
        for t in _raw_turns:
            if str(t.get("src") or "chat") not in ("chat", "topic_open"):
                continue
            _a = str(t.get("a") or "").strip()
            if 6 <= len(_a) <= 60 and _a not in _my_lines:
                _my_lines.append(_a)
            u = str(t.get("u") or "").strip()
            a = str(t.get("a") or "").strip()
            key = (u, a)
            if key in _seen:
                continue
            _seen.add(key)
            if u:
                lines.append("他：" + u[:80])
            if a:
                lines.append("我：" + a[:80])
        lines = lines[-SELFCARD_MATERIAL_LINES:]
        if len(lines) < 6:
            return None
        _old = str(st.get("text") or "").strip()
        _prev = ""
        try:
            _hist = st.get("history") or []
            if _hist:
                _prev = str(_hist[-1].get("text") or "").strip()
        except Exception:
            _prev = ""
        _imps = [str(i.get("text") or "").strip()
                 for i in (self.memory_data.get("impressions") or [])
                 if not i.get("invalid_at")][:12]
        _rel = str(((self.memory_data.get("profile") or {}).get("relation") or {}).get("content") or "").strip()
        prompt = chr(10).join([
            "你在帮一个桌宠角色写「我现在是什么样」这一页，她叫%s。" % self.pet_name,
            "材料有五样：她最近说过的原话、她对他的看法、你俩的关系、这一页的旧版和更早一版、最近对话。",
            "据此重写这一页——写的是「她自己是什么样」，不是这段时间发生了什么：",
            "- ≤%d 字，第一人称「我」" % SELFCARD_MAX_CHARS,
            "- 主体是她的性子：在意什么、烦什么、说话什么口吻（爱用的词/爱开的玩笑）、怎么待他、什么时候会顶他",
            "- 不写事件流水账：禁止「他做了X，我就Y」这种反应记录；要写「我就是会……的那种」",
            "- 不写「我是一个……」这种自我贴标签的人设句，也不写「我该……」的自我要求",
            "- 语气照着她自己的原话来，别改写成书面语",
            "- 允许保留原来写得对的部分；没什么变化就把 new_text 留空",
            "- 旧版和更早一版的差别如果体现的是她自己的变化，可以用「以前…现在…」写进去",
            "",
            "【我最近说过的原话】（照这个口吻写，别写成书面语）",
            (chr(10).join("- " + s for s in _my_lines[-12:]) if _my_lines else "（还没有）"),
            "",
            "【我对他的看法】",
            (chr(10).join("- " + s for s in _imps) if _imps else "（还没有）"),
            "",
            "【你俩的关系】",
            _rel or "（还没有）",
            "",
            "【这一页·当前版】",
            _old or "（空）",
            "",
            "【这一页·更早一版】",
            _prev or "（无）",
            "",
            "【最近的话】（按时间先后）",
            chr(10).join(lines),
            "",
            "只输出 JSON，不要 markdown：{\"new_text\": \"重写后的一页，不变就留空串\", \"why\": \"变化原因（≤20字）\"}",
        ])
        try:
            resp = self._call_text_model([{"role": "user", "content": prompt}],
                                         temperature=0.6, max_tokens=4096, timeout=60)
            if resp.status_code != 200:
                log.warning("自我卡结晶失败: HTTP %s", resp.status_code)
                return None
            raw = resp.json()["choices"][0]["message"]["content"] or ""
            m = re.search(r"\{.*\}", raw, re.S)
            data = json.loads(m.group(0) if m else raw)
            new_text = str(data.get("new_text") or "").strip()
            why = str(data.get("why") or "").strip()[:20]
            if not new_text:
                st["updated_at"] = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                self._selfcard = st
                try:
                    save_json_file(SELFCARD_FILE, st)
                except Exception:
                    pass
                log.info("自我卡结晶：这轮没变化")
                return None
            self._selfcard_save(new_text, why=why or "结晶")
            log.info("自我卡已更新（%s）：%s", why or "结晶", new_text[:40])
            return new_text
        except Exception as e:
            log.debug("自我卡结晶异常: %s", e)
            return None

    def _effective_system_prompt(self):
        _sys = self.full_system
        if self.banned_words:
            _sys += f"\n\n【禁词表】你在任何回复中都绝对禁止出现以下词汇：{self.banned_words}。违反此规则是严重错误。"
        # 11/14：自我卡每轮原文注入（不进检索、不随话题抖动）
        try:
            _card = self._selfcard_block()
            if _card:
                _sys += chr(10) * 2 + _card
        except Exception as e:
            log.debug("自我卡注入失败: %s", e)
        return _sys

    def get_ai_response(self, user_msg):
        # 检查 API Key
        if not self.text_api_key:
            self._ui(lambda: self.show_bubble_text("(worried) 请先设置文本模型 API Key...", "worried"), status=True)
            return "(worried) 请先设置文本模型 API Key..."
        # 语音直连：歌曲选项卡片弹出后说“第2首/第二首/2号”直接命中编号（不经模型，秒响应）
        pick_idx = _parse_pick_num(user_msg)
        if pick_idx is not None and self._music_browse:
            hit = next((f for i, f in self._music_browse if i == pick_idx), None)
            if hit:
                t = _split_artist_title(hit)[1]
                self._queue_playlist([hit])  # 说完再播：由本轮 TTS 结束后启动
                log.info("语音直连选歌: 第%d首《%s》", pick_idx, t)
                return f"(happy) 好的，准备播放《{t}》（我说完就开始）"
        # 语音/打字直连翻页：卡片可见时说“换一批/还有呢/再看看/下一批” → 展示下一批（沿用筛选），不经模型
        _m = (user_msg or "").strip()
        if any(w in _m for w in ("换一批", "还有呢", "换一换", "再看看", "下一批", "再来一批")) and self._song_picker:
            _lf, _af = self._music_last_filter
            _ok, _note = self._list_music(_lf, _af)
            if _ok:
                return ""   # 弹卡轮静默：handle_ai_reply 因 _picker_reply_pending 直接返回
        with self.api_lock:
            self.api_busy = True
        try:
            # 时间前缀统一由 build_context_messages 注入，避免重复拼接
            tools = self._chat_tools_schema()
            system = self._effective_system_prompt()
            if tools:
                system += ("\n\n【工具使用】你有几个工具。control_music 用于直接播放本地音乐文件"
                           "（用户说“放首歌/来点音乐/播放某首歌/我想听xxx/把音乐停了/别放了”时调用；"
                           "歌名不明确就随机播放；要听日语/英语/俄语/中文歌或某歌手的歌时按语言/歌手筛选；"
                           "用户不知道歌名时用 list_songs 弹出歌曲选择框，然后“放第X首/第二首”即可。"
                           "**他哼歌、念歌词、玩梗时提到歌名不算点歌，别调工具，接他的话就好**)。"
                           "工具执行结果会以消息形式返回，你据此用自己的口吻向用户确认即可，不要复述内部过程。")
            # 意图预判：明显是本地点歌/停歌时，强化提示让模型必须调 control_music。
            # 注意：本模型(Thinking 模式)不接受对象式 tool_choice（会 400），只能用 auto+提示词引导。
            if tools:
                m = user_msg.strip()
                has_music_word = any(w in m for w in ("音乐", "歌", "曲子", "BGM", "bgm"))
                play_start = m.startswith(("播放", "放一", "放个", "放首", "放点", "来首", "来点",
                                           "唱首", "唱一", "想听", "我想听"))
                play_verb = any(v in m for v in ("放首歌", "放个歌", "放点音乐", "来点音乐",
                                                 "放音乐", "听音乐", "停音乐", "把音乐", "别放"))
                if ("播放器" not in m and "视频" not in m and "电影" not in m
                        and (play_start or (has_music_word and play_verb))):
                    system += ("（注意：本条消息明显是在要求播放/停止本地音乐，"
                               "你必须调用 control_music 工具，绝不要回答“我不能播放音乐”。）")
                # 翻页意图：给歌曲选择框换下一批，而不是随机播放
                if any(w in m for w in ("换一批", "还有呢", "换一换", "再看看", "下一批", "再来一批")):
                    system += ("（注意：用户是在给刚弹出的歌曲选择框翻页看下一批，"
                               "请调用 control_music 的 list_songs（可不带 lang/artist，代码会自动沿用上次筛选），"
                               "不要调用 play_random 或 play_song。）")
            messages = self.build_context_messages(system, user_msg,
                                                   extra_context=self._reading_context_digest())
            resp = self._call_text_model(messages, temperature=0.7, max_tokens=DEFAULT_MAX_TOKENS, timeout=30,
                                         tools=tools)
            # 提供方不支持 function calling 时回退为普通对话
            if resp.status_code != 200 and tools is not None:
                log.warning("function calling 请求失败(status=%s)，回退普通对话", resp.status_code)
                tools = None
                messages = self.build_context_messages(self._effective_system_prompt(), user_msg,
                                                       extra_context=self._reading_context_digest())
                resp = self._call_text_model(messages, temperature=0.7, max_tokens=DEFAULT_MAX_TOKENS, timeout=30)
            if resp.status_code == 200:
                msg = resp.json()["choices"][0]["message"]
                content = self._extract_message_content(msg)
                for _round in range(3):      # 10/21：允许"再调一次工具"（例如先 play_song 失败、再 list_songs）
                    calls = msg.get("tool_calls")
                    if not calls:
                        break
                    # 执行工具并把结果回填给模型，让它用人设口吻总结
                    tool_msgs = []
                    look_reply = None      # 看屏幕的回答模式下，视觉模型那句话直接当回复
                    other_tool = False     # 这一轮还调了别的工具（那就不走直出）
                    for tc in calls:
                        tid = tc.get("id") or ""
                        fn = tc.get("function") or {}
                        fname = fn.get("name", "")
                        try:
                            args = json.loads(fn.get("arguments") or "{}")
                        except Exception:
                            args = {}
                        log.info("工具调用: %s args=%s", fname, json.dumps(args, ensure_ascii=False))
                        if fname != "look_at_screen":
                            other_tool = True
                        if fname == "control_music":
                            ok, note = self.control_music(
                                str(args.get("action", "")),
                                str(args.get("song", "") or ""),
                                str(args.get("lang", "") or ""),
                                str(args.get("artist", "") or ""),
                                args.get("index") or 0,
                                args.get("value"),
                                args.get("delta"))
                        elif fname == "control_browser":
                            ok, note = self.control_browser(
                                str(args.get("action", "") or ""), args.get("seek_to"),
                                args.get("value"), args.get("delta"))
                        elif fname == "ask_dsh":
                            ok, note = self.ask_dsh(str(args.get("task", "") or ""))
                        elif fname == "look_at_screen":
                            ok, note = self.look_at_screen(str(args.get("focus", "") or ""))
                            if ok:
                                look_reply = note
                        else:
                            tool_msgs.append((tid, f"ERROR 未知工具: {fname}"))
                            continue
                        tool_msgs.append((tid, ("OK " if ok else "ERROR ") + note))
                    messages.append({"role": "assistant", "content": content, "tool_calls": calls})
                    for tid, res in tool_msgs:
                        messages.append({"role": "tool", "tool_call_id": tid, "content": res})
                    # 10/23：看屏幕的"回答模式"已经把完整回答产出了（它拿的是同一套上下文），
                    # 再让文本模型改写一遍只会让"看到的"和"说出来的"不一致，还多一次调用 ⇒ 直出。
                    # 只有这一轮全是看屏幕才这样；还调了别的工具就照常回填总结（要念执行结果）。
                    if look_reply and not other_tool:
                        log.info("看屏幕：直接采用视觉模型的回答（不再二次改写）")
                        content = look_reply
                        break
                    # 10/21：这一轮也必须带 tools —— 不带的话模型想继续调工具时只能自己编
                    # 原生语法（<｜｜DSML｜｜ invoke ...>），那段字会被当正文念出来
                    resp2 = self._call_text_model(messages, temperature=0.7, max_tokens=DEFAULT_MAX_TOKENS,
                                                  timeout=30, tools=tools, tool_choice="auto")
                    if resp2.status_code != 200:
                        break
                    msg = resp2.json()["choices"][0]["message"]
                    content = self._extract_message_content(msg)
                if content:
                    content = _strip_dsml(content)      # 兜底：残留的原生工具语法绝不念出来
                if content:
                    return content
                return "(happy) 好啦，已经帮你处理了！"
            return "(worried) 唔...脑袋有点晕乎乎的..."
        except Exception as e:
            log.error(f"文本模型 API 请求失败: {e}")
            return "(shy) 对不起，好像走神了..."
        finally:
            with self.api_lock:
                self.api_busy = False

    def get_current_time_period(self):
        hour = datetime.now().hour
        if 5 <= hour < 8:
            return "清晨"
        elif 8 <= hour < 11:
            return "上午"
        elif 11 <= hour < 13:
            return "中午"
        elif 13 <= hour < 17:
            return "下午"
        elif 17 <= hour < 19:
            return "傍晚"
        elif 19 <= hour < 22:
            return "晚上"
        else:
            return "深夜"

    def _cue_catalog(self):
        """当前形态的〔词〕表：动作类→播 Cue 组里的那一段；穿戴类→写 exp3 里的原值。

        值全部来自模型文件（exp3 的 Value / 动作文件），代码里不写数值。
        只在第一次（或换形态后）扫一次。
        """
        form = getattr(self, "form", "")
        cached = getattr(self, "_cue_cache", None)
        if cached and cached[0] == form:
            return cached[1]
        info = LIVE2D_FORMS.get(form) or {}
        base = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                            "live2d_viewer", info.get("dir", ""))
        cat = {}
        try:
            with open(os.path.join(base, info.get("json", "")), encoding="utf-8") as f:
                md = json.load(f)
            cues = ((md.get("FileReferences", {}).get("Motions", {}) or {}).get("Cue") or [])
            for i, it in enumerate(cues):
                rel = it.get("File", "")
                name = os.path.basename(rel)[: -len(".motion3.json")]
                if not name:
                    continue
                cat[name] = ("motion", i)
        except Exception as e:
            log.debug("读取 Cue 动作组失败: %s", e)
        try:
            edir = os.path.join(base, "expressions")
            for fn in sorted(os.listdir(edir)):
                if not fn.endswith(".exp3.json"):
                    continue
                try:
                    with open(os.path.join(edir, fn), encoding="utf-8") as f:
                        d = json.load(f)
                    params = {p["Id"]: float(p.get("Value", 0.0))
                              for p in (d.get("Parameters") or []) if p.get("Id")}
                except Exception:
                    continue
                _nm = fn[: -len(".exp3.json")]
                if params and _nm in CUE_TIMED_POSE:      # 只留"贴贴"这类动作型姿态，穿戴一律手动
                    cat[_nm] = ("pose", params, CUE_TIMED_POSE[_nm])
        except Exception as e:
            log.debug("读取表情目录失败: %s", e)
        for alias, target in CUE_MOTION_ALIAS.items():
            if target in cat:
                cat[alias] = cat[target]
        for alias, target in CUE_POSE_ALIAS.items():
            if isinstance(target, tuple):
                cat[alias] = ("pose", {target[0]: target[1]}, None)
            elif target in cat:
                cat[alias] = cat[target]
        self._cue_cache = (form, cat)
        log.info("〔词〕表已建：%d 项（形态 %s）", len(cat), form)
        return cat

    def _apply_cues(self, cues):
        """把台词里的〔词〕变成动作/姿态。一句最多两个。"""
        if not cues or not (self.spine and self.spine_enabled):
            return
        cat = self._cue_catalog()
        for name in cues[:2]:
            item = cat.get(name)
            if not item:
                log.info("没见过的〔%s〕（词表里没有）", name)
                continue
            try:
                if item[0] == "motion":
                    # 就播这一段，播完让引擎自然淡出回默认——不按住终值、不播回程动作。
                    # （按住 + 播切回会在动作交界处反折抽搐，用户实测否掉了这个方案）
                    self.spine.enqueue(("test_motion", "Cue", item[1]))
                    log.info("台词动作：%s（Cue#%d，自然结束）", name, item[1])
                else:
                    _params, _hold = item[1], item[2]
                    self.spine.enqueue(("pose", _params))
                    log.info("台词姿态：%s → %s（%s）", name, _params,
                             ("%.1f 秒后收回" % _hold) if _hold else "保持")
                    if _hold:
                        self.root.after(int(_hold * 1000),
                                        lambda ps=list(_params): self.spine.enqueue(("pose_release", ps)))
            except Exception as e:
                log.debug("套用〔%s〕失败: %s", name, e)

    def handle_ai_reply(self, reply, user_msg):
        # 本轮已弹选歌卡片：宠物保持沉默（卡片即回复），语音通道畅通让用户直接说编号
        if getattr(self, "_picker_reply_pending", False):
            self._picker_reply_pending = False
            return
        emotion, text = self.parse_emotion_from_reply(reply)
        text = strip_echoed_prefix(text)         # 剥掉她模仿出来的时间戳前缀
        text, cues = extract_cues(text)          # 〔词〕：气泡/TTS/记忆都只用干净文本
        self._add_chat_buffer_turn(user_msg, text, source="chat")
        # 对用户输入的回应：输出完毕刷新免唤醒词窗口
        self.show_bubble_text(text, emotion, refresh_voice=True)
        threading.Thread(target=self._tts_play, args=(text, True), daemon=True).start()
        if cues:
            self._apply_cues(cues)

    def parse_emotion_from_reply(self, text):
        text = (text or "").strip()
        if not text:
            return "normal", ""
        # 开头情绪标注：只认英文情绪词（半角/全角括号均可）；动作/描述括号不提取情绪、保留显示
        m = re.match(r'[（(]\s*([A-Za-z]+)\s*[）)]\s*(.*)', text, re.DOTALL)
        if m:
            word = m.group(1).lower()
            if word in EMOTION_WORDS:
                return word, _strip_inline_markers(m.group(2))
            return "normal", _strip_inline_markers(text)
        # 无开头标注：正常文本，仍剥离正文中残留的多余英文情绪标注
        return "normal", _strip_inline_markers(text)

    def _show_thinking_bubble(self):
        """「嗯…让我想想…」占位提示。

        它不是"她的一轮输出"——只是等模型回复时的过渡，所以：
        ①不刷新免唤醒窗口；②这期间头顶的「🎤 在听」标记保持熄灭（见 _thinking_now），
        免得她还在想、标记先亮了，用户以为可以说话。
        """
        self._thinking_since = time.time()
        self.show_bubble_text("(normal) 嗯...让我想想...", "normal")

    def _thinking_now(self):
        """是否正在等模型回复（45 秒兜底过期：万一回复路径出错，标记不能永久不亮）"""
        return bool(self._thinking_since) and (time.time() - self._thinking_since) < 45

    def show_bubble_text(self, text, emotion="normal", refresh_voice=False, status=False):
        """弹气泡。status=True 表示状态/提示类（开关提示、错误、模式提示、事件卡片）——
        它们不受「隐藏回复气泡」影响；不带 status 的就是她的回复，开了隐藏就不显示
        （表情、嘴型、免唤醒窗口照常）。"""
        if text.startswith("(") or text.startswith("（"):
            em = re.match(r'[（(]\s*([A-Za-z]+)\s*[）)]\s*(.*)', text, re.DOTALL)
            if em and em.group(1).lower() in EMOTION_WORDS:
                emotion = em.group(1).lower()
                text = em.group(2).strip()
        text = _strip_inline_markers(text)
        if refresh_voice:
            self._thinking_since = 0.0      # 真的开始输出了，不再算"在想"
        self.set_emotion(emotion)
        # 说话时张嘴，2秒后闭合
        if self.spine_enabled and self.spine:
            if hasattr(self, '_mouth_job') and self._mouth_job:
                self.root.after_cancel(self._mouth_job)
            self.spine.set_mouth(0.3)
            self._mouth_job = self.root.after(2000, lambda: self.spine.set_mouth(0) if self.spine else None)
        if self.hide_reply_bubble and not status:
            # 隐藏回复气泡：不碰气泡窗，但"说完了"这件事还得照常通知（免唤醒窗口靠它开）
            # 10/23 修：收回表情原来挂在气泡淡出里 ⇒ 气泡不显示就永远收不回来，
            # 表情会一直挂着直到点她或说下一句。这里按"气泡本该消失的时刻"自己收。
            try:
                if getattr(self, "_reply_expr_job", None):
                    self.root.after_cancel(self._reply_expr_job)
            except Exception:
                pass
            _hold_ms = max(4000, int(len(text or "") * 50) + 10000)
            try:
                self._reply_expr_job = self.root.after(
                    _hold_ms, self._restore_expression_after_reply)
            except Exception:
                self._reply_expr_job = None
            if refresh_voice:
                self._on_output_finished(True)
            return
        # 显示气泡这条路由气泡淡出负责收表情；顺手取消隐藏模式下挂着的定时器，免得提前收脸
        try:
            if getattr(self, "_reply_expr_job", None):
                self.root.after_cancel(self._reply_expr_job)
                self._reply_expr_job = None
        except Exception:
            pass
        self.bubble_window.show_text(text, refresh_voice=refresh_voice)

    def _restore_expression_after_reply(self):
        """隐藏气泡模式下，回复显示一段时间后把表情收回中性。"""
        self._reply_expr_job = None
        try:
            self.restore_expression()
        except Exception:
            pass

    def set_text_model_settings(self):
        """文本模型设置：API 地址 + 密钥 + 模型名（OpenAI 兼容）"""
        self._open_llm_settings_dialog("文本模型设置", self.llm_config["text"], TEXT_PRESETS)

    def set_vision_model_settings(self):
        """视觉模型设置：API 地址 + 密钥 + 模型名（OpenAI 兼容，支持图片输入）"""
        self._open_llm_settings_dialog("视觉模型设置", self.llm_config["vision"], VISION_PRESETS)

    def _open_llm_settings_dialog(self, title, cfg, presets):
        win, frame = self._make_card_window(title, 680, 400)
        s = self._dpi_scale

        provider_var = tk.StringVar(value="自定义")
        base_var = tk.StringVar(value=cfg.get("base_url", ""))
        key_var = tk.StringVar(value=cfg.get("api_key", ""))
        model_var = tk.StringVar(value=cfg.get("model", ""))

        row = 0
        tk.Label(frame, text="提供方预设：", font=(self.font_family, 10), fg=TEXT_MAIN, bg=DIALOG_BG).grid(
            row=row, column=0, sticky="w", pady=5)
        provider_names = [p[0] for p in presets] + ["自定义"]
        preset_combo = ttk.Combobox(frame, textvariable=provider_var, values=provider_names,
                                    state="readonly", width=32)
        preset_combo.grid(row=row, column=1, sticky="w", pady=5)
        row += 1

        tk.Label(frame, text="API 地址 (Base URL)：", font=(self.font_family, 10), fg=TEXT_MAIN, bg=DIALOG_BG).grid(
            row=row, column=0, sticky="w", pady=5)
        base_entry = RoundedEntry(frame, textvariable=base_var, width=int(430 * s), height=int(32 * s),
                                  radius=int(8 * s), font=(self.font_family, 9))
        base_entry.grid(row=row, column=1, columnspan=2, sticky="ew", pady=5)
        row += 1

        tk.Label(frame, text="API 密钥 (API Key)：", font=(self.font_family, 10), fg=TEXT_MAIN, bg=DIALOG_BG).grid(
            row=row, column=0, sticky="w", pady=5)
        key_entry = RoundedEntry(frame, textvariable=key_var, width=int(430 * s), height=int(32 * s),
                                 radius=int(8 * s), font=(self.font_family, 9), show="*")
        key_entry.grid(row=row, column=1, columnspan=2, sticky="ew", pady=5)
        row += 1

        tk.Label(frame, text="模型名称 (Model)：", font=(self.font_family, 10), fg=TEXT_MAIN, bg=DIALOG_BG).grid(
            row=row, column=0, sticky="w", pady=5)
        model_values = [cfg.get("model", "")] if cfg.get("model", "") else []
        model_combo = ttk.Combobox(frame, textvariable=model_var, values=model_values,
                                   state="normal", width=44)
        model_combo.grid(row=row, column=1, sticky="ew", pady=5)
        fetch_btn = RoundedButton(frame, text="获取模型列表", command=lambda: fetch_models(silent=False),
                                  variant="subtle",
                                  width=int(120 * s), height=int(30 * s), radius=int(6 * s),
                                  font=(self.font_family, 9))
        fetch_btn.grid(row=row, column=2, sticky="w", padx=6, pady=5)
        row += 1

        def apply_preset(*_):
            name = provider_var.get()
            for p in presets:
                if p[0] == name:
                    base_var.set(p[1])
                    model_var.set(p[2])
                    break
            fetch_models(silent=True)

        preset_combo.bind("<<ComboboxSelected>>", apply_preset)

        def fetch_models(silent=False):
            base = base_var.get().strip()
            key = key_var.get().strip()
            if not base:
                if not silent:
                    messagebox.showwarning("提示", "请先填写 API 地址")
                return
            fetch_btn.set_enabled(False)
            fetch_btn.set_text("获取中...")

            def worker():
                ids = fetch_model_list(base, key)

                def done():
                    try:
                        fetch_btn.set_enabled(True)
                        fetch_btn.set_text("获取模型列表")
                    except Exception:
                        return
                    if ids:
                        model_combo["values"] = ids
                        cur = model_var.get().strip()
                        if cur not in ids and ids:
                            model_var.set(ids[0])
                        if not silent:
                            messagebox.showinfo("成功", f"已获取 {len(ids)} 个模型")
                    else:
                        if not silent:
                            messagebox.showwarning(
                                "失败",
                                "未能获取模型列表。请检查地址/密钥，或该提供方不支持 /models 接口；\n"
                                "豆包请直接填写 Endpoint ID（ep-xxx）。")
                try:
                    win.after(0, done)
                except Exception:
                    pass

            threading.Thread(target=worker, daemon=True).start()

        hint = tk.Label(
            frame,
            text="说明：Base URL 填到版本号为止（如 https://api.deepseek.com/v1），程序会自动拼接 /chat/completions。\n"
                 "模型名称可直接从下拉框选择（点击“获取模型列表”自动拉取），也可手动输入；\n"
                 "火山引擎豆包视觉模型的“模型名称”即 Endpoint ID（ep-xxx）。",
            font=(self.font_family, 8), fg=TEXT_SUB, bg=DIALOG_BG,
            wraplength=540, justify="left")
        hint.grid(row=row, column=0, columnspan=3, sticky="w", pady=8)
        row += 1

        def save():
            new_base = base_var.get().strip()
            new_key = key_var.get().strip()
            new_model = model_var.get().strip()
            if not new_base or not new_model:
                messagebox.showwarning("警告", "API 地址和模型名称不能为空")
                return
            cfg["base_url"] = new_base
            cfg["api_key"] = new_key
            cfg["model"] = new_model
            # 同步实例属性，确保“立即生效”
            if cfg is self.llm_config["text"]:
                self.text_base_url, self.text_api_key, self.text_model = new_base, new_key, new_model
            else:
                self.vision_base_url, self.vision_api_key, self.vision_model = new_base, new_key, new_model
            save_llm_config(self.llm_config)
            messagebox.showinfo("成功", "已保存，立即生效")
            win.destroy()

        btn_frame = tk.Frame(frame, bg=DIALOG_BG)
        btn_frame.grid(row=row, column=0, columnspan=3, sticky="e", pady=10)
        RoundedButton(btn_frame, text="✖ 取消", command=win.destroy, variant="subtle",
                      width=int(100 * s), height=int(36 * s), radius=int(6 * s),
                      font=(self.font_family, 11)).pack(side=tk.RIGHT, padx=6)
        RoundedButton(btn_frame, text="💾 保存", command=save, width=int(110 * s), height=int(36 * s),
                      radius=int(6 * s), font=(self.font_family, 11, "bold")).pack(side=tk.RIGHT, padx=6)

        frame.columnconfigure(1, weight=1)

    def set_tts_api_and_speaker(self):
        win, frame = self._make_card_window("声音复刻配置", 560, 240)
        s = self._dpi_scale

        tk.Label(frame, text="声音复刻 API Key:", font=(self.font_family, 11), fg=TEXT_MAIN, bg=DIALOG_BG).grid(row=0, column=0, sticky="w", pady=5)
        api_var = tk.StringVar(value=self.tts_api_key)
        api_entry = RoundedEntry(frame, textvariable=api_var, width=int(380 * s), height=int(32 * s),
                                 radius=int(8 * s), font=(self.font_family, 10))
        api_entry.grid(row=0, column=1, pady=5, padx=5)

        tk.Label(frame, text="Speaker ID:", font=(self.font_family, 11), fg=TEXT_MAIN, bg=DIALOG_BG).grid(row=1, column=0, sticky="w", pady=5)
        spk_var = tk.StringVar(value=self.tts_speaker_id)
        spk_entry = RoundedEntry(frame, textvariable=spk_var, width=int(380 * s), height=int(32 * s),
                                 radius=int(8 * s), font=(self.font_family, 10))
        spk_entry.grid(row=1, column=1, pady=5, padx=5)

        def save():
            self.tts_api_key = api_var.get().strip()
            self.tts_speaker_id = spk_var.get().strip()
            save_tts_api_key(self.tts_api_key)
            save_tts_speaker_id(self.tts_speaker_id)
            messagebox.showinfo("成功", "声音复刻配置已保存")
            win.destroy()

        btn_frame = tk.Frame(frame, bg=DIALOG_BG)
        btn_frame.grid(row=2, column=0, columnspan=2, sticky="e", pady=15)
        RoundedButton(btn_frame, text="✖ 取消", command=win.destroy, variant="subtle",
                      width=int(100 * s), height=int(36 * s), radius=int(6 * s),
                      font=(self.font_family, 11)).pack(side=tk.RIGHT, padx=6)
        RoundedButton(btn_frame, text="💾 保存", command=save, width=int(110 * s), height=int(36 * s),
                      radius=int(6 * s), font=(self.font_family, 11)).pack(side=tk.RIGHT, padx=6)



    # ---------- 火山引擎声音复刻 TTS 核心方法 ----------
    def _translate_for_tts(self, chinese_text, lang):
        """把回复翻译成 TTS 要念的语言（en/ja）；失败返回空串（调用方退回中文原文）"""
        if not chinese_text.strip() or lang not in ("en", "ja"):
            return ""
        # 语气词的固定译法：中文「哼」要的是轻声 Hmm，不是带火气的 Hmph
        target = {"ja": ("自然的口语日语", "日语", ""),
                  "en": ("自然的口语英语", "英语", "中文的语气词「哼」一律译成 Hmm，不要用 Hmph；")}[lang]
        prompt = (f"请将以下中文翻译成{target[0]}，只输出{target[1]}译文，不要加任何额外说明。"
                  f"{target[2]}\n{chinese_text}")
        try:
            # 翻译是"短输出、不需要推理"的任务：关掉思考模式，省掉 1~7 秒的思考时间
            resp = self._call_text_model([{"role": "user", "content": prompt}], temperature=0.3,
                                         max_tokens=DEFAULT_MAX_TOKENS, timeout=15, thinking=False)
            if resp.status_code == 200:
                result = resp.json()["choices"][0]["message"]["content"].strip()
                if result:
                    if lang == "en":
                        # 兜底：模型偶尔还是写 Hmph，这里统一成 Hmm（保大小写）
                        result = re.sub(r'\bHmph\b', 'Hmm', result)
                        result = re.sub(r'\bhmph\b', 'hmm', result)
                        result = re.sub(r'\bHMPH\b', 'HMM', result)
                    log.info("TTS 翻译(%s)成功: %s... → %s...", target[1], chinese_text[:20], result[:20])
                    return result
                log.warning("TTS 翻译(%s)返回空", target[1])
            else:
                log.warning("TTS 翻译(%s) API 返回非200: %s %s", target[1], resp.status_code, resp.text[:100])
        except Exception as e:
            log.warning("TTS 翻译(%s)异常: %s", target[1], e)
        return ""

    def _tts_play(self, chinese_text, refresh_voice=False):
        if not self.tts_enabled:
            return
        if not TTS_AVAILABLE:
            return
        if self.tts_mode == "edge":
            return self._tts_play_edge(chinese_text, refresh_voice)
        if self.tts_mode == "deepseek":
            return self._tts_play_deepseek(chinese_text, refresh_voice)
        # 火山引擎声音复刻 TTS
        api_key = self.tts_api_key
        speaker_id = self.tts_speaker_id
        if not api_key or not speaker_id:
            log.warning("TTS API Key 或 Speaker ID 未配置，跳过语音播放")
            return
        clean = strip_emoji(re.sub(r'[（(][^）)]*[）)]', '', chinese_text).strip())
        if not clean:
            return
        # 语言：中文直接念；英文/日语先翻译再念（翻译失败退回中文原文，绝不静默无声）
        lang = self.tts_volc_lang
        tts_text = clean
        if lang in ("en", "ja"):
            translated = self._translate_for_tts(clean, lang)
            if translated:
                tts_text = translated
            else:
                log.warning("TTS 翻译失败（%s），改用中文原文朗读",
                            TTS_LANG_NAMES.get(lang, lang))
        cluster = resolve_volc_cluster(speaker_id, self.tts_volc_cluster)
        log.info("TTS %s(%s): %s", VOLC_CLUSTER_LABELS.get(cluster, cluster),
                 TTS_LANG_NAMES.get(lang, lang), tts_text)

        def _play():
            # 串行化 TTS 播放：避免多线程同时写同名文件 / 共用 pygame.mixer
            if not self._tts_lock.acquire(timeout=1):
                log.warning("TTS 播放被跳过：上一条语音仍在播放")
                return
            temp_file = None
            try:
                payload = {
                    "app": {
                        "cluster": cluster
                    },
                    "user": {
                        "uid": VOLC_TTS_UID
                    },
                    "audio": {
                        "voice_type": speaker_id,
                        "encoding": "mp3",
                        "speed_ratio": 1.0,
                    },
                    "request": {
                        "reqid": str(uuid.uuid4()).replace("-", "")[:40],
                        "text": tts_text,
                        "operation": "query",
                    },
                }
                headers = {
                    "x-api-key": api_key,
                    "Content-Type": "application/json",
                }
                log.debug(f"TTS v1 请求: speaker={speaker_id} text={tts_text[:40]}...")
                resp = requests.post(
                    VOLC_TTS_URL,
                    headers=headers,
                    json=payload,
                    timeout=30,
                )
                log.debug(f"TTS 响应状态: {resp.status_code}")
                if resp.status_code != 200:
                    log.error(f"TTS API 返回非200: {resp.status_code} {resp.text[:300]}")
                    return

                resp_data = resp.json()
                code = resp_data.get("code", -1)
                if code != 3000:
                    log.error(f"TTS API 错误: code={code} msg={resp_data.get('message','')}")
                    return

                data_b64 = resp_data.get("data", "")
                if not data_b64:
                    log.warning("TTS 未收到任何音频数据")
                    return

                full_audio = base64.b64decode(data_b64)
                # 唯一临时文件，避免并发覆盖/删除冲突
                with tempfile.NamedTemporaryFile(suffix=".mp3", delete=False) as tf:
                    tf.write(full_audio)
                    temp_file = tf.name

                # 她开口前：把音乐压低当背景音（不停音乐、不记断点）；
                # 音量恢复统一放在 finally —— 她那边无论怎么退出（含异常），音乐都不会一直闷着
                self._music_duck_for_tts()
                # 播放期间静音语音识别，避免宠物“听见自己”触发识别
                if self.stt is not None and self.voice_on:
                    self.stt.set_muted(True)
                self._play_tts_file(temp_file)
            except Exception as e:
                log.error(f"TTS 播放错误: {e}")
            finally:
                # 【锁必须一定放掉】10/14 定位到的"TTS 哑掉、只能重启"就是这里漏的：
                # 原来 release() 排在收尾最后，前面 set_muted(False) 任何一步抛异常都会连它
                # 一起跳过 ⇒ 之后每条 TTS 都被"上一条语音仍在播放"挡在门外，直到重启。
                # 现在收尾整段包进 try、release 放内层 finally —— 以后谁再往收尾里加东西，
                # 也炸不掉这把锁。执行顺序与原来完全一致。
                try:
                    if self._tts_channel is not None:
                        try:
                            self._tts_channel.stop()    # 超时提前退出时，别让她的声音漏到下一句
                        except Exception:
                            pass
                    # 无论她那边怎么退出，都把音乐音量淡回基准（读标志本身，不看局部变量）
                    self._music_finish_tts(self._music_duck is not None)
                    if self.stt is not None and self.voice_on:
                        self.stt.set_muted(False)
                    # TTS 播完：仅对用户输入的回应才刷新免唤醒词窗口（from_tts=True = "真念完了"）
                    if refresh_voice:
                        self._on_output_finished(True, from_tts=True)
                    if temp_file and os.path.exists(temp_file):
                        try:
                            os.remove(temp_file)
                        except Exception:
                            pass
                except Exception as e:
                    log.warning("TTS 收尾出错（锁照常释放）: %s", e)
                finally:
                    self._tts_lock.release()
                    self._start_pending_music()  # TTS 说完：启动挂起的音乐（若有）

        threading.Thread(target=_play, daemon=True).start()

    def _tts_play_edge(self, chinese_text, refresh_voice=False):
        """Edge TTS 播放"""
        if not EDGE_TTS_IMPORTED:
            return
        clean = strip_emoji(re.sub(r'[（(][^）)]*[）)]', '', chinese_text).strip())
        if not clean:
            return
        # 语言：中文直接念；英文先翻译再念；翻译失败退回中文音色念原文（别用英文音色硬读中文）
        lang = self.tts_edge_lang
        voice = self.tts_edge_voice
        tts_text = clean
        if lang == "en":
            translated = self._translate_for_tts(clean, "en")
            if translated:
                tts_text = translated
            else:
                voice = DEFAULT_EDGE_VOICE
                log.warning("TTS 翻译失败（英文），改用中文音色朗读原文")
        proxy = resolve_edge_proxy(self.tts_edge_proxy)
        log.info("Edge TTS(%s/%s%s): %s", TTS_LANG_NAMES.get(lang, lang), voice,
                 "·代理" if proxy else "", tts_text)

        def _play_edge():
            if not self._tts_lock.acquire(timeout=1):
                log.warning("TTS 播放被跳过：上一条语音仍在播放")
                return
            temp_file = None
            try:
                comm = edge_tts.Communicate(tts_text, voice, proxy=proxy)
                with tempfile.NamedTemporaryFile(suffix=".mp3", delete=False) as _tf:
                    temp_file = _tf.name
                asyncio.run(comm.save(temp_file))
                # 她开口前：把音乐压低当背景音（不停音乐、不记断点）；
                # 音量恢复统一放在 finally —— 她那边无论怎么退出（含异常），音乐都不会一直闷着
                self._music_duck_for_tts()
                # 播放期间静音语音识别，避免宠物“听见自己”触发识别
                if self.stt is not None and self.voice_on:
                    self.stt.set_muted(True)
                self._play_tts_file(temp_file)
            except Exception as e:
                log.error(f"Edge TTS 播放错误: {e}")
            finally:
                # 【锁必须一定放掉】见 _tts_play 里同款注释：哑掉的根因就是 release 排在收尾最后。
                try:
                    if self._tts_channel is not None:
                        try:
                            self._tts_channel.stop()    # 超时提前退出时，别让她的声音漏到下一句
                        except Exception:
                            pass
                    # 无论她那边怎么退出，都把音乐音量淡回基准（读标志本身，不看局部变量）
                    self._music_finish_tts(self._music_duck is not None)
                    if self.stt is not None and self.voice_on:
                        self.stt.set_muted(False)
                    # TTS 播完：仅对用户输入的回应才刷新免唤醒词窗口（from_tts=True = "真念完了"）
                    if refresh_voice:
                        self._on_output_finished(True, from_tts=True)
                    if temp_file and os.path.exists(temp_file):
                        try: os.remove(temp_file)
                        except Exception: pass
                except Exception as e:
                    log.warning("Edge TTS 收尾出错（锁照常释放）: %s", e)
                finally:
                    self._tts_lock.release()
                    self._start_pending_music()  # TTS 说完：启动挂起的音乐（若有）

        threading.Thread(target=_play_edge, daemon=True).start()

    def _tts_play_deepseek(self, chinese_text, refresh_voice=False):
        """DeepSeek 原生 TTS（11/13 上线的 /v1/tools/tts）：返回 wav，走她的专属声道。"""
        api_key = getattr(self, "tts_deepseek_key", "") or ""
        if not api_key:
            log.warning("DeepSeek TTS 未配置 API Key，跳过语音播放")
            return
        clean = strip_emoji(re.sub(r"[（(][^）)]*[）)]", "", chinese_text).strip())
        if not clean:
            return
        voice = getattr(self, "tts_deepseek_voice", DEEPSEEK_TTS_VOICE_DEFAULT) or DEEPSEEK_TTS_VOICE_DEFAULT
        lang = getattr(self, "tts_deepseek_lang", "zh") or "zh"
        tts_text = clean
        if lang in ("en", "ja"):
            translated = self._translate_for_tts(clean, lang)
            if translated:
                tts_text = translated
            else:
                log.warning("TTS 翻译失败（%s），改用中文原文朗读", TTS_LANG_NAMES.get(lang, lang))
        # 计费字符：汉字算 2、其他算 1（官方口径）
        _billed = sum(2 if ("\u4e00" <= ch <= "\u9fff") else 1 for ch in tts_text)
        log.info("DeepSeek TTS(%s, %d 计费字符≈¥%.4f): %s", voice, _billed,
                 _billed * DEEPSEEK_TTS_PRICE, tts_text[:40])

        def _play_ds():
            if not self._tts_lock.acquire(timeout=1):
                log.warning("TTS 播放被跳过：上一条语音仍在播放")
                return
            temp_file = None
            try:
                with tempfile.NamedTemporaryFile(suffix=".wav", delete=False) as tf:
                    temp_file = tf.name
                with requests.post(DEEPSEEK_TTS_URL,
                                   headers={"Authorization": "Bearer " + api_key},
                                   json={"text": tts_text, "voice_id": voice, "format": "wav",
                                         "filter_markdown": True},
                                   stream=True, timeout=(10, 120)) as resp:
                    if resp.status_code != 200:
                        log.error("DeepSeek TTS 失败: http=%s body=%s", resp.status_code,
                                  (resp.text or "")[:200].replace(chr(10), " "))
                        return
                    with open(temp_file, "wb") as fh:
                        for chunk in resp.iter_content(chunk_size=16384):
                            if chunk:
                                fh.write(chunk)
                self._fix_wav_header(temp_file)
                if not os.path.exists(temp_file) or os.path.getsize(temp_file) < 1000:
                    log.error("DeepSeek TTS 返回的音频异常（%d 字节）",
                              os.path.getsize(temp_file) if os.path.exists(temp_file) else 0)
                    return
                self._music_duck_for_tts()
                if self.stt is not None and self.voice_on:
                    self.stt.set_muted(True)
                self._play_tts_file(temp_file)
            except Exception as e:
                log.error("DeepSeek TTS 播放错误: %s", e)
            finally:
                try:
                    if self._tts_channel is not None:
                        try:
                            self._tts_channel.stop()
                        except Exception:
                            pass
                    self._music_finish_tts(self._music_duck is not None)
                    if self.stt is not None and self.voice_on:
                        self.stt.set_muted(False)
                    if refresh_voice:
                        self._on_output_finished(True, from_tts=True)
                    if temp_file and os.path.exists(temp_file):
                        try:
                            os.remove(temp_file)
                        except Exception:
                            pass
                except Exception as e:
                    log.warning("DeepSeek TTS 收尾出错（锁照常释放）: %s", e)
                finally:
                    self._tts_lock.release()
                    self._start_pending_music()

        threading.Thread(target=_play_ds, daemon=True).start()

    # ---------- 事件气泡 ----------
    def _add_topic_open_turn(self, context):
        """把"她发起的话题"记进聊天缓冲，聊天界面里就像她先发了一句。

        这一轮**只给界面看**：display_only 标记让 build_context_messages 跳过它，
        否则模型会把自己提过的话题当成"用户说过的话"，下一轮容易自问自答。
        """
        try:
            c = " ".join(str(context or "").split())
            if not c:
                return
            turn = [{"role": "user", "content": "", "source": "topic_open", "display_only": True},
                    {"role": "assistant", "content": c, "source": "topic_open", "display_only": True}]
            with self._memory_lock:
                self.chat_buffer.append(turn)
                self._trim_history()
                save_chats(self.chat_buffer)
            try:
                if getattr(self, "_cc_win", None) is not None and self._cc_win.winfo_exists():
                    self.root.after(0, self._cc_refresh_chat)
            except Exception:
                pass
        except Exception as e:
            log.debug("记录话题开头失败: %s", e)

    def show_event_bubble(self, context, opt1, opt2):
        self.clear_event_buttons()
        self.current_event_context = context
        self.current_event_options = [opt1, opt2]
        # 11/10：她提的话题也进聊天记录（像 QQ 里她先发一条）
        self._add_topic_open_turn(context)
        self.show_bubble_text(f"(normal) {context}", status=True)
        threading.Thread(target=self._tts_play, args=(context,), daemon=True).start()
        self.root.after(500, self.create_event_buttons, opt1, opt2)

    def clear_event_buttons(self):
        # 11/02：清按钮的同时把"自动收掉"的定时器取消，免得下一轮被旧定时器误清
        _job = getattr(self, "_event_ttl_job", None)
        if _job:
            try:
                self.root.after_cancel(_job)
            except Exception:
                pass
            self._event_ttl_job = None
        if hasattr(self, 'event_frame') and self.event_frame:
            self.event_frame.destroy()
            self.event_frame = None
        self.event_buttons = []
        self.current_event_context = ""
        self.current_event_options = []
        self.update_window_size()

    def create_event_buttons(self, opt1, opt2):
        # 仅清理旧按钮 UI，不清除 context（context 由 show_event_bubble 设置）
        if hasattr(self, 'event_frame') and self.event_frame:
            self.event_frame.destroy()
            self.event_frame = None
        self.event_buttons = []
        self.event_frame = tk.Frame(self.bottom_frame, bg=TRANS_MASK)
        self.event_frame.pack(side=tk.BOTTOM, fill=tk.X, pady=(5, 0))
        s = self._dpi_scale
        f = tkfont.Font(root=self.root, family=self.font_family, size=9)
        line_h = f.metrics("linespace") + 2
        # 两个按钮并排：每个最多 (窗口宽 - 边距) / 2，文本过长自动换行（全部按像素计算）
        btn_max_w = max(int(70 * s), (self.window_width - int(24 * s)) // 2)
        # 左右留白撑开，使两个按钮水平居中
        tk.Frame(self.event_frame, bg=TRANS_MASK).pack(side=tk.LEFT, expand=True)
        for text, idx in [(opt1, 0), (opt2, 1)]:
            segments = text.split("\n")
            avail = max(50, btn_max_w - int(14 * s))
            n_lines = sum(-(-f.measure(seg) // avail) for seg in segments)
            n_lines = max(1, min(n_lines, 3))
            w = min(btn_max_w, max(f.measure(seg) for seg in segments) + int(14 * s))
            btn = RoundedButton(
                self.event_frame, text=text, command=lambda i=idx: self.on_event_option(i),
                variant="subtle",
                width=w, height=max(int(30 * s), int((n_lines * line_h + 6) * s)),
                radius=int(6 * s),
                parent_bg=TRANS_MASK,
                font=(self.font_family, 9),
                wrap_width=(w - int(10 * s)) if n_lines > 1 else None)
            btn.pack(side=tk.LEFT, padx=4, pady=4)
            self.event_buttons.append(btn)
        tk.Frame(self.event_frame, bg=TRANS_MASK).pack(side=tk.LEFT, expand=True)
        self.update_window_size()
        # 11/02：选项挂一会儿自动收掉（用户："过了很长时间选项依然存在，有些出戏"）
        self._event_ttl_job = self.root.after(int(TOPIC_OPTION_TTL_MIN * 60 * 1000),
                                             self._expire_event_buttons)

    def _expire_event_buttons(self):
        """话题选项过期：安静收掉，不提示、不进历史。"""
        self._event_ttl_job = None
        if getattr(self, "event_frame", None):
            log.info("话题选项超过 %d 分钟，自动收掉", TOPIC_OPTION_TTL_MIN)
            self.clear_event_buttons()

    def _respond_to_topic(self, selected, context):
        """话题回应的共享逻辑：发送 prompt → AI 回复 → 显示/记录/TTS"""
        prompt = f"""用户对你刚才提出的互动事件"{context}"做出了回应："{selected}"。请根据你的人设，对用户的回应做出可爱、温馨的回复。要自然、简短，并且用括号标注情绪。必须输出完整句子，不能只有情绪词。"""
        def fetch_reply():
            with self.api_lock:
                self.api_busy = True
            try:
                messages = self.build_context_messages(self._effective_system_prompt(), prompt)
                resp = self._call_text_model(messages, temperature=0.7, max_tokens=DEFAULT_MAX_TOKENS, timeout=20)
                if resp.status_code == 200:
                    reply = resp.json()["choices"][0]["message"]["content"]
                    emotion, text = self.parse_emotion_from_reply(reply)
                    if not text.strip():
                        text = "嗯，好的呢"
                    user_msg = f"（关于话题：{context}）回应：{selected}"
                    self._ui(lambda: self._add_chat_buffer_turn(user_msg, text, source="chat"))
                    # 对用户回应的回复：输出完毕刷新免唤醒词窗口
                    self._ui(lambda: self.show_bubble_text(text, emotion, refresh_voice=True))
                    self._ui(lambda: threading.Thread(target=self._tts_play, args=(text, True), daemon=True).start())
                else:
                    self._ui(lambda: self.show_bubble_text("(shy) 嗯...好的呢", "shy"))
            except Exception:
                self._ui(lambda: self.show_bubble_text("(shy) 唔...我再想想", "shy"))
            finally:
                with self.api_lock:
                    self.api_busy = False
        threading.Thread(target=fetch_reply, daemon=True).start()

    def on_event_option(self, idx):
        if idx >= len(self.current_event_options):
            self.clear_event_buttons()
            return
        self.last_interaction_time = time.time()
        self.consume_energy()
        with self.api_lock:
            if self.api_busy:
                self.show_bubble_text("(worried) 等一下嘛，我现在有点忙...", "worried", status=True)
                return
        selected = self.current_event_options[idx]
        context = self.current_event_context
        self.clear_event_buttons()
        self._show_thinking_bubble()
        self._respond_to_topic(selected, context)

    def on_event_text(self, text):
        """手动输入的话题回应"""
        with self.api_lock:
            if self.api_busy:
                self.show_bubble_text("(worried) 等一下嘛，我现在有点忙...", "worried", status=True)
                return
        context = self.current_event_context
        self.clear_event_buttons()
        self._show_thinking_bubble()
        self._respond_to_topic(text.strip(), context)

    def show_menu(self, event):
        if self._menu_open:
            self.menu.hide_all()
            return
        self._menu_open = True
        self.root.attributes("-topmost", False)
        # 点击菜单外的任意位置 → 关闭菜单
        self._dismiss_funcid = self.root.bind_all("<Button-1>", self._dismiss_menu_click, add="+")
        self.menu.show(event.x_root, event.y_root)

    def _dismiss_menu_click(self, event):
        try:
            tl = event.widget.winfo_toplevel()
        except Exception:
            tl = None
        if tl in ModernMenu.ACTIVE:
            return
        self.menu.hide_all()

    def _on_menu_closed(self):
        """菜单树完全关闭后恢复宠物置顶"""
        if not self._menu_open:
            return
        self._menu_open = False
        try:
            if self._dismiss_funcid:
                self.root.unbind_all("<Button-1>", self._dismiss_funcid)
                self._dismiss_funcid = None
        except Exception:
            pass
        try:
            self.root.attributes("-topmost", True)
            self.root.lift()
        except Exception:
            pass

    def _make_card_window(self, title, w, h):
        """Win11 风格卡片窗口：无边框 + 透明挖角 + PIL 圆角白卡（细边框/柔影）
        + 自绘标题栏（可拖动、✕ 关闭、Esc 关闭）。返回 (win, content_frame)。
        注意：不能用 transient（Windows 上 transient+overrideredirect 会丢失初始
        位置并压到 owner 之下），必须显式定位 + focus_force 激活（否则输入框无法
        获得键盘输入）。"""
        _tgt = getattr(self, "_cc_embed_target", None)
        if _tgt is not None:
            # 只吞最外层：标记消费掉，嵌套对话框照常弹真窗口
            self._cc_embed_target = None
            return self._cc_embed_card(_tgt, title)
        s = self._dpi_scale
        W, H = int(w * s), int(h * s)
        win = tk.Toplevel(self.root)
        win.overrideredirect(True)
        win.configure(bg=CARD_MASK)
        win.attributes("-transparentcolor", CARD_MASK)
        win.attributes("-topmost", True)
        win.grab_set()
        canvas = tk.Canvas(win, width=W, height=H, highlightthickness=0, bd=0, bg=CARD_MASK)
        canvas.pack()
        if not hasattr(self, "_card_photos"):
            self._card_photos = []
        self._card_photos.append(_card_photo(W, H, max(8, int(12 * s))))
        canvas.create_image(0, 0, anchor="nw", image=self._card_photos[-1])
        # 初始位置：宠物正上方居中（越界则钳制到屏幕内），避免出现在左上角
        px = self.root.winfo_rootx()
        py = self.root.winfo_rooty()
        pw = self.root.winfo_width()
        x = px + (pw - W) // 2
        y = py - H - int(24 * s)
        x = max(8, min(x, self._screen_w - W - 8))
        y = max(8, min(y, self._screen_h - H - 8))
        win.geometry(f"+{x}+{y}")
        # 激活窗口并置顶：保证 z-order 在普通窗口之上、键盘输入可达
        try:
            win.lift()
            win.focus_force()
        except Exception:
            pass
        title_h = int(44 * s)
        # 标题栏（拖动命中区）
        hit = canvas.create_rectangle(0, 0, W, title_h, fill=CARD_BG, outline="")
        canvas.tag_lower(hit)
        canvas.create_text(int(18 * s), title_h // 2, anchor="w", text=title,
                           font=(self.font_family, 11, "bold"), fill=TEXT_MAIN)
        close_id = canvas.create_text(W - int(18 * s), title_h // 2, text="✕",
                                      font=(self.font_family, 12), fill=TEXT_SUB)
        canvas.tag_bind(close_id, "<Enter>", lambda e: canvas.itemconfigure(close_id, fill=DANGER_RED))
        canvas.tag_bind(close_id, "<Leave>", lambda e: canvas.itemconfigure(close_id, fill=TEXT_SUB))
        canvas.tag_bind(close_id, "<Button-1>", lambda e: win.destroy())
        # 拖动：窗口级绑定（标题文字/关闭按钮区域也能拖），仅限标题栏 canvas 内，
        # 且用 active 标志防止内容区的 B1-Motion 误拖窗口
        drag = {"dx": 0, "dy": 0, "active": False}
        def _drag_start(e):
            # e.widget 必须是标题栏 canvas（子控件点击会冒泡上来，但坐标是子控件的）
            if e.widget is not canvas:
                return
            if e.y > title_h:
                return
            drag["dx"] = e.x_root - win.winfo_x()
            drag["dy"] = e.y_root - win.winfo_y()
            drag["active"] = True
        def _drag_move(e):
            if not drag["active"]:
                return
            win.geometry(f"+{e.x_root - drag['dx']}+{e.y_root - drag['dy']}")
        def _drag_end(e):
            drag["active"] = False
        win.bind("<ButtonPress-1>", _drag_start)
        win.bind("<B1-Motion>", _drag_move)
        win.bind("<ButtonRelease-1>", _drag_end)
        win.bind("<Escape>", lambda e: win.destroy())
        pad = int(16 * s)
        content = tk.Frame(canvas, bg=CARD_BG)
        canvas.create_window(pad, title_h, anchor="nw", window=content,
                             width=W - 2 * pad, height=H - title_h - int(10 * s))
        if not hasattr(self, "_open_cards"):
            self._open_cards = set()
        self._open_cards.add(win)
        win.bind("<Destroy>", lambda e: self._open_cards.discard(win), add="+")
        return win, content

    # ---------- 系统提示词设置 ----------
    def open_settings(self):
        win, main_frame = self._make_card_window("系统提示词设置", 700, 880)
        s = self._dpi_scale

        tk.Label(main_frame, text="角色设定：", font=(self.font_family, 12, "bold"),
                 fg=TEXT_MAIN, bg=DIALOG_BG).grid(row=0, column=0, columnspan=3, sticky="w",
                                                  pady=(0, 6))

        # 字段标签一律等宽（都 3 字）且靠左：输入框正好贴在标签右边，左右都不留空
        tk.Label(main_frame, text="姓名：", font=(self.font_family, 11), fg=TEXT_MAIN,
                 bg=DIALOG_BG).grid(row=1, column=0, sticky="w", pady=3)
        name_var = tk.StringVar(value=self.pet_name)
        name_entry = RoundedEntry(main_frame, textvariable=name_var,
                                  width=int(470 * s), height=int(32 * s),
                                  radius=int(8 * s),
                                  font=(self.font_family, 11))
        name_entry.grid(row=1, column=1, columnspan=2, sticky="ew", pady=3)

        tk.Label(main_frame, text="人设：", font=(self.font_family, 11, "bold"), fg=TEXT_MAIN,
                 bg=DIALOG_BG).grid(row=2, column=0, columnspan=3, sticky="w", pady=(10, 3))
        persona_area = scrolledtext.ScrolledText(main_frame, wrap=tk.WORD, font=(self.font_family, 11),
                                                 bg="#ffffff", fg=TEXT_MAIN, relief=tk.FLAT, bd=0,
                                                 highlightthickness=1, highlightbackground=INPUT_BORDER2, height=11)
        persona_area.grid(row=3, column=0, columnspan=3, sticky="nsew", pady=5)
        persona_area.insert(tk.END, self.character_config["persona"])

        # ── 回复规则（可改，存 config.json 的 character 节）──
        tk.Label(main_frame, text="回复规则：", font=(self.font_family, 11, "bold"), fg=TEXT_MAIN,
                 bg=DIALOG_BG).grid(row=4, column=0, columnspan=3, sticky="w", pady=(10, 3))

        tk.Label(main_frame, text="字数：", font=(self.font_family, 11), fg=TEXT_MAIN,
                 bg=DIALOG_BG).grid(row=5, column=0, sticky="w", pady=3)
        max_var = tk.StringVar(value=str(self.max_chars))
        max_entry = RoundedEntry(main_frame, textvariable=max_var,
                                 width=int(140 * s), height=int(32 * s),
                                 radius=int(8 * s), font=(self.font_family, 11))
        max_entry.grid(row=5, column=1, columnspan=2, sticky="w", pady=3)

        tk.Label(main_frame, text="禁词：", font=(self.font_family, 11), fg=TEXT_MAIN,
                 bg=DIALOG_BG).grid(row=6, column=0, sticky="w", pady=3)
        ban_var = tk.StringVar(value=self.banned_words)
        ban_entry = RoundedEntry(main_frame, textvariable=ban_var,
                                 width=int(470 * s), height=int(32 * s),
                                 radius=int(8 * s), font=(self.font_family, 11))
        ban_entry.grid(row=6, column=1, columnspan=2, sticky="ew", pady=3)

        tk.Label(main_frame, text="说话方式：", font=(self.font_family, 11, "bold"), fg=TEXT_MAIN,
                 bg=DIALOG_BG).grid(row=7, column=0, columnspan=3, sticky="w", pady=(10, 3))
        style_area = scrolledtext.ScrolledText(main_frame, wrap=tk.WORD, font=(self.font_family, 10),
                                               bg="#ffffff", fg=TEXT_MAIN, relief=tk.FLAT, bd=0,
                                               highlightthickness=1, highlightbackground=INPUT_BORDER2, height=6)
        style_area.grid(row=8, column=0, columnspan=3, sticky="nsew", pady=5)
        style_area.insert(tk.END, self.style_rules)

        btn_frame = tk.Frame(main_frame, bg=DIALOG_BG)
        btn_frame.grid(row=9, column=0, columnspan=3, sticky="e", pady=10)

        def save_prompt():
            new_name = name_var.get().strip()
            new_persona = persona_area.get("1.0", tk.END).strip()
            if not new_name:
                messagebox.showwarning("警告", "角色姓名不能为空！")
                return
            if not new_persona:
                messagebox.showwarning("警告", "人设不能为空！")
                return
            try:
                new_max = int(str(max_var.get()).strip())
            except (TypeError, ValueError):
                messagebox.showwarning("警告", "字数上限要填数字（%d~%d）" % (MIN_MAX_CHARS, MAX_MAX_CHARS))
                return
            if not (MIN_MAX_CHARS <= new_max <= MAX_MAX_CHARS):
                messagebox.showwarning("警告", "字数上限请填 %d~%d 之间的数字" % (MIN_MAX_CHARS, MAX_MAX_CHARS))
                return
            new_style = style_area.get("1.0", tk.END).strip()
            new_bans = ban_var.get().strip()
            self.character_config.update({
                "name": new_name, "persona": new_persona, "max_chars": new_max,
                "style_rules": new_style, "banned_words": new_bans,
            })
            save_character_config(self.character_config)
            self.pet_name = new_name
            self.max_chars = new_max
            self.style_rules = new_style
            self.banned_words = new_bans
            self.system_prompt = build_system_prompt(new_name, new_persona, new_max, new_style, has_cues=self._form_has_cues(self.form))
            self.full_system = build_full_system_prompt(self.system_prompt, self.user_profile)
            messagebox.showinfo("成功", "角色设定已保存并立即生效")
            win.destroy()

        def restore_default():
            name_var.set(DEFAULT_PET_NAME)
            persona_area.delete("1.0", tk.END)
            persona_area.insert(tk.END, DEFAULT_PERSONA)
            max_var.set(str(DEFAULT_MAX_CHARS))
            ban_var.set("")
            style_area.delete("1.0", tk.END)
            style_area.insert(tk.END, DEFAULT_STYLE_RULES)

        def cancel():
            win.destroy()

        # 操作按钮（Win11：右对齐，主操作在最后）
        btn_restore = RoundedButton(btn_frame, text="🔄 恢复默认", command=restore_default,
                                    variant="subtle",
                                    width=int(120 * s), height=int(36 * s),
                                    radius=int(6 * s),
                                    font=(self.font_family, 11))
        btn_restore.pack(side=tk.RIGHT, padx=6)

        btn_cancel = RoundedButton(btn_frame, text="✖ 取消", command=cancel,
                                   variant="subtle",
                                   width=int(100 * s), height=int(36 * s),
                                   radius=int(6 * s),
                                   font=(self.font_family, 11))
        btn_cancel.pack(side=tk.RIGHT, padx=6)

        btn_save = RoundedButton(btn_frame, text="💾 保存", command=save_prompt,
                                 width=int(110 * s), height=int(36 * s),
                                 radius=int(6 * s),
                                 font=(self.font_family, 11, "bold"))
        btn_save.pack(side=tk.RIGHT, padx=6)

        main_frame.grid_rowconfigure(3, weight=1)
        main_frame.grid_rowconfigure(8, weight=1)
        main_frame.grid_columnconfigure(1, weight=1)

    # ---------- 用户档案设置 ----------
    def open_user_profile(self):
        win, frame = self._make_card_window("用户档案", 520, 420)
        s = self._dpi_scale
        fields = [
            ("昵称", "nickname"),
            ("生日", "birthday"),
            ("称呼", "call_name"),
            ("背景故事", "story")
        ]
        entries = {}
        for i, (label, key) in enumerate(fields):
            tk.Label(frame, text=label + "：", font=(self.font_family, 11), fg=TEXT_MAIN,
                     bg=DIALOG_BG).grid(row=i, column=0, padx=12, pady=6, sticky='ne')
            if key == "story":
                var = tk.StringVar(value=self.user_profile.get(key, ""))
                ent = scrolledtext.ScrolledText(frame, wrap=tk.WORD, font=(self.font_family, 10),
                                                height=4, bd=0, relief=tk.FLAT,
                                                highlightthickness=1, highlightbackground=INPUT_BORDER2)
                ent.insert("1.0", var.get())
                ent.grid(row=i, column=1, padx=12, pady=6, sticky='we')
                entries[key] = ent
            else:
                var = tk.StringVar(value=self.user_profile.get(key, ""))
                ent = RoundedEntry(frame, textvariable=var, width=int(300 * s), height=int(32 * s),
                                   radius=int(8 * s),
                                   font=(self.font_family, 11))
                ent.grid(row=i, column=1, padx=12, pady=6, sticky='we')
                entries[key] = var
        frame.columnconfigure(1, weight=1)
        def save():
            for key in entries:
                if key == "story":
                    self.user_profile[key] = entries[key].get("1.0", tk.END).strip()
                else:
                    self.user_profile[key] = entries[key].get()
            self.full_system = build_full_system_prompt(self.system_prompt, self.user_profile)
            save_user_profile(self.user_profile)
            story_text = (self.user_profile.get("story") or "").strip()
            if story_text:
                threading.Thread(target=self._relation_from_story, args=(story_text,),
                                 daemon=True).start()
            messagebox.showinfo("成功", "用户档案已更新")
            win.destroy()
        RoundedButton(frame, text="保存", command=save,
                      width=int(100 * s), height=int(36 * s),
                      radius=int(6 * s),
                      font=(self.font_family, 11, "bold")).grid(row=len(fields), column=0, columnspan=2, pady=16)

    def _relation_from_story(self, story):
        """用户档案保存时：若背景故事包含与“我”的关系描述，总结进关系形象；没有则不变"""
        try:
            persona_hint = ((self.character_config.get("persona") or DEFAULT_PERSONA)
                            .strip().replace("\n", " "))[:60]
            prompt = (f"你正在为桌宠角色「{self.pet_name}」总结关系认知。{self.pet_name}的人设概要："
                      f"{persona_hint}……\n\n用户的档案“背景故事”里写了这样一段内容：\n\n"
                      f"【背景故事】\n{story}\n\n"
                      f"请判断其中是否包含用户与“我”（{self.pet_name}）之间关系的描述。\n"
                      f"- 如果包含：请用{self.pet_name}的第一人称视角，用{self.pet_name}自己的语气和"
                      f"用词习惯输出一句关系认知总结（25字以内，只输出这句总结，不要解释、不要前缀）。\n"
                      f"- 如果不包含任何与“我”的关系描述：只输出 null。\n"
                      f"不要输出其他内容。")
            resp = self._call_text_model([{"role": "user", "content": prompt}],
                                         temperature=0.3, max_tokens=DEFAULT_MAX_TOKENS, timeout=60)
            if resp.status_code != 200:
                log.warning("背景故事关系总结API失败: %s", resp.status_code)
                return
            text = (resp.json()["choices"][0]["message"]["content"] or "").strip()
            if not text or text.lower() == "null" or text in ("（null）", "(null)", "无", "没有"):
                return
            text = text.strip("“”\"'。. ")
            if len(text) < 5:
                return
            with self._memory_lock:
                prof = self.memory_data.setdefault("profile", {})
                cur = (prof.get("relation") or {}).get("content", "")
                if text == cur:
                    return
                old_ev = int((prof.get("relation") or {}).get("evidence_count", 0))
                prof["relation"] = {
                    "content": text,
                    "confidence": 0.8,
                    "evidence_count": old_ev + 1,
                    "updated_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                }
            save_memories(self.memory_data)
            log.info("关系形象（来自背景故事）: %s", text[:40])
        except Exception as e:
            log.warning("背景故事关系总结失败: %s", e)

    # ---------- 睡眠 ----------
    def _show_sleep_hint(self):
        """睡着时收到任何输入：只弹一句气泡，不出声、不苏醒（10/16 用户要求）。

        刻意**不**走 TTS——他要的是"只是提示"，别再把她吵起来。
        """
        self.show_bubble_text("（还没睡醒呢）", "sleep", status=True)

    def start_sleep_mode(self, manual=False):
        if self.sleep_mode:
            return
        if self.watch_mode:
            self.toggle_watch_mode()
        # 10/16：睡觉一律**不关麦克风**（手动睡、无互动自动睡都一样）——他要能随时喊她。
        # 睡着时听到/收到任何输入都只弹一句提示，不苏醒也不出声：
        # 语音走 on_speech_recognized 的守卫，打字走 send_message 的守卫（都调 _show_sleep_hint）。
        if self.reading_companion.enabled:
            self.toggle_reading()
        self.sleep_mode = True
        self.manual_sleep = manual
        self.sleep_start_time = time.time()
        self.bubble_window.fade_out()
        self.set_emotion("sleep")
        self.show_bubble_text("(sleep) Zzz...", "sleep", status=True)
        # 输入框保持可用：睡着时打字不会唤醒她，只会弹一句「（还没睡醒呢）」（见 send_message）
        if not manual:
            threading.Thread(target=self._sleep_monitor, daemon=True).start()

    def _get_cursor_pos(self):
        try:
            p = wintypes.POINT()
            ctypes.windll.user32.GetCursorPos(ctypes.byref(p))
            return (p.x, p.y)
        except Exception:
            return None

    def _sleep_monitor(self):
        last_pos = self._get_cursor_pos()
        while self.sleep_mode and not self.manual_sleep:
            time.sleep(5)
            if not self.sleep_mode or self.manual_sleep:
                break
            try:
                if time.time() - self.sleep_start_time > MAX_AUTO_SLEEP_DURATION:
                    self._ui(lambda: self.stop_sleep_mode(cause="limit"))
                    break
                cur = self._get_cursor_pos()
                if cur is not None:
                    if last_pos is not None and \
                            abs(cur[0] - last_pos[0]) + abs(cur[1] - last_pos[1]) > 50:
                        self._ui(lambda: self.stop_sleep_mode(cause="mouse"))
                        break
                    last_pos = cur
                # cur 为 None 时保留旧锚点，避免失去鼠标唤醒能力
            except Exception as e:
                log.warning("睡眠监测异常（继续监测）: %s", e)

    def stop_sleep_mode(self, restore_voice=True, cause="user"):
        if not self.sleep_mode:
            return
        _was_manual = self.manual_sleep
        _slept_from = self.sleep_start_time or time.time()
        self.sleep_mode = False
        self.manual_sleep = False
        self.bubble_window.fade_out()
        if self.spine_enabled and self.spine:
            self.spine.enqueue(('wake',))
        self.set_emotion("normal")
        self.input_entry.config(state=tk.NORMAL)
        self.last_interaction_time = time.time()
        if self.sleep_start_time:
            slept_seconds = time.time() - self.sleep_start_time
            slept_minutes = int(slept_seconds // 60)
            if slept_minutes < 1:
                sleepy_text = "我好像打了个瞌睡……"
            elif slept_minutes < 10:
                sleepy_text = f"我眯了 {slept_minutes} 分钟，感觉精神好多了。"
            elif slept_minutes < 60:
                sleepy_text = f"我睡了 {slept_minutes} 分钟，现在好清醒呀。"
            else:
                hours = slept_minutes // 60
                mins = slept_minutes % 60
                if mins == 0:
                    sleepy_text = f"我睡了 {hours} 个小时，现在精力充沛！"
                else:
                    sleepy_text = f"我睡了 {hours} 小时 {mins} 分钟，感觉像新的一样~"
            self._last_sleep = {"start": _slept_from, "end": time.time(),
                                "minutes": slept_minutes, "cause": cause,
                                "manual": _was_manual}
            self.sleep_start_time = None
        else:
            sleepy_text = "我睡了一觉，现在感觉好多了！"
        self.show_bubble_text(sleepy_text, "relaxed")
        threading.Thread(target=self._tts_play, args=(sleepy_text,), daemon=True).start()
        self.sleep_cooldown_until = time.time() + 30 * 60
        # 唤醒后恢复话题定时器（睡眠期间触发链会中断，需重新调度）
        try:
            self._schedule_action()
            if self.topic_enabled and self.topic_timer_job is None:
                self._schedule_topic()
        except Exception:
            pass
        if restore_voice:
            # 睡着时自动关掉的麦，醒来接着开（quiet：别用气泡盖掉她刚说的"我眯了一会儿"）
            self._restore_voice_if_wanted(quiet=True)

    def _sleep_context_line(self):
        """把"刚睡过一觉"变成一条上下文事实（11/18 用户要求，不进锚点也不进箱子）。

        原先醒来那句只走气泡 + TTS，模型侧完全不知道睡过；这里给它一个带时间、
        时长、醒来原因的事实，30 分钟后降级成一句，跨天就不提了。
        """
        d = getattr(self, "_last_sleep", None)
        if not d:
            return ""
        try:
            end = float(d.get("end") or 0)
            start = float(d.get("start") or end)
            if datetime.fromtimestamp(end).date() != datetime.now().date():
                return ""
            minutes = int(d.get("minutes") or 0)
            hhmm = lambda ts: datetime.fromtimestamp(ts).strftime("%H:%M")
            dur = ("%d 小时 %d 分" % (minutes // 60, minutes % 60)) if minutes >= 60                 else ("%d 分钟" % minutes)
            if time.time() - end > 30 * 60:
                return "【今天】你在 %s 到 %s 之间睡过一觉（%s），现在早就醒了。" % (
                    hhmm(start), hhmm(end), dur)
            if minutes < 1:
                return "【刚才】你刚打了个盹，不到一分钟就醒了。"
            why = {
                "mouse": "是他动鼠标把你弄醒的，不是你睡够了",
                "click": "是他把你戳醒的",
                "voice": "是他喊你把你叫醒的",
                "limit": "是你自己睡够了醒的",
            }.get(str(d.get("cause") or ""), "是他把你弄醒的")
            return "【刚才】你在 %s 睡着了，%s 醒的，睡了 %s。%s。" % (
                hhmm(start), hhmm(end), dur, why)
        except Exception as e:
            log.debug("生成睡眠上下文失败: %s", e)
            return ""

    # ---------- 精力值系统 ----------
    def start_energy_tick(self):
        self.root.after(5000, self._energy_tick)

    def _energy_tick(self):
        now = time.time()
        elapsed = now - self.energy_last_tick
        self.energy_last_tick = now
        if self.sleep_mode:
            self.energy = min(MAX_ENERGY, self.energy + ENERGY_RECOVER_PER_MINUTE * elapsed / 60.0)
        else:
            self.energy = max(0, self.energy - ENERGY_DECAY_PER_MINUTE * elapsed / 60.0)
            self._energy_check_warn()   # 10/16：不再强制睡觉，只提醒
        self._energy_job = self.root.after(5000, self._energy_tick)

    def consume_energy(self, amount=ENERGY_ACTIVE_COST):
        self.energy = max(0, self.energy - amount)
        self._energy_check_warn()       # 10/16：不再强制睡觉，只提醒

    def _energy_check_warn(self):
        """精力跨档时提醒她累了、并劝用户歇一会儿（10/16 起不再强制睡觉）。

        原先归零会 start_sleep_mode(manual=True) —— 那会顺手关掉陪玩/麦克风/读书，
        打断所有工作，陪玩时还容易卡住。现在只出一句提醒，睡不睡由用户决定：
        菜单「💤 睡觉」随时能用；一小时无互动的自动睡是另一条路，不受影响。
        去重：clearing 靠"精力回到 ENERGY_LOW 以上"（睡醒之后会重新提醒）。
        """
        if self.sleep_mode:
            return
        if self.energy > ENERGY_LOW:
            self._energy_warned.clear()
            return
        key = "zero" if self.energy <= 0 else "low"
        if key in self._energy_warned:
            return
        self._energy_warned.add(key)
        if key == "zero":
            msg = "我真的撑不住了，得去躺一会儿。你也把电脑关了歇歇，好不好？"
        else:
            msg = "有点累了……你也别一直盯着屏幕，起来走两步、喝口水吧。"
        log.info("精力提醒（%s，当前 %.1f）：不强制睡觉，只提醒", key, self.energy)
        self.show_bubble_text(f"(sleep) {msg}", "sleep", status=True)
        threading.Thread(target=self._tts_play, args=(msg,), daemon=True).start()

    def get_energy_mood(self):
        """返回精力值对情绪的影响描述，用于 AI 提示词"""
        if self.sleep_mode:
            return ""
        if self.energy >= 70:
            return "你现在精力充沛，语气活泼有朝气。"
        elif self.energy >= ENERGY_LOW:
            return "你现在精力尚可，保持正常的语气。"
        elif self.energy >= ENERGY_CRITICAL:
            return "你现在有些累了，语气中带着一点疲惫，说话会比平时更轻柔简短。"
        else:
            return "你现在非常疲惫，眼睛都快睁不开了，说话有气无力，只想休息。回复要非常简短。"

    def show_energy_status(self):
        level = round(self.energy)
        if self.energy >= 70:
            desc = "精力充沛 ✨"
        elif self.energy >= ENERGY_LOW:
            desc = "状态良好"
        elif self.energy >= ENERGY_CRITICAL:
            desc = "有点累了 😔"
        else:
            desc = "快撑不住了... 💤"
        messagebox.showinfo("精力值", f"当前精力：{level} / {MAX_ENERGY}\n{desc}")

    def _build_fault_report(self):
        """生成一份"发给 AI 就能排查"的故障报告（Markdown）。不碰任何状态。"""
        L = []
        L.append("# 大肥鱼桌宠 故障报告")
        L.append("")
        L.append("- 生成时间：%s" % datetime.now().strftime("%Y-%m-%d %H:%M:%S"))
        try:
            L.append("- 当前形态：%s" % getattr(self, "form", "?"))
        except Exception:
            pass
        L.append("")
        L.append("## 运行状态")
        try:
            _up = int(time.time() - float(getattr(self, "_boot_at", time.time())))
            L.append("- 已运行：%d 分 %d 秒" % (_up // 60, _up % 60))
        except Exception:
            pass
        for k, label in (("watch_mode", "陪玩中"), ("sleep_mode", "睡眠中")):
            try:
                L.append("- %s：%s" % (label, "是" if getattr(self, k, False) else "否"))
            except Exception:
                pass
        try:
            rc = getattr(self, "reading_companion", None)
            L.append("- 陪读中：%s" % ("是" if rc is not None and getattr(rc, "running", False) else "否"))
        except Exception:
            pass
        try:
            L.append("- 精力：%s" % self.energy_value())
        except Exception:
            pass
        try:
            L.append("- 陪看环形缓冲：%d 帧" % len(getattr(self, "_watch_ring", []) or []))
        except Exception:
            pass
        try:
            _md = getattr(self, "memory_data", {}) or {}
            L.append("- 记忆：话题 %d / 事件 %d / 画像 %d / 自我认知 %d / 关于他 %d" % (
                len(_md.get("topics") or []), len(_md.get("events") or []),
                len((_md.get("profile") or {}).get("traits") or []),
                len((_md.get("profile") or {}).get("notes") or []),
                len((_md.get("profile") or {}).get("user_notes") or [])))
        except Exception:
            pass
        L.append("")
        L.append("## 环境")
        for line in _fr_env_lines():
            L.append("- " + line)
        try:
            cfgs = load_json_file(CONFIG_FILE, {}) or {}
            secs = []
            for section, key in _FR_SAFE_CONFIG:
                val = (cfgs.get(section) or {}).get(key)
                if isinstance(val, (str, int, float, bool)) or val is None:
                    if isinstance(val, str):
                        val = _fr_redact(val)[:40]
                    secs.append("%s.%s=%s" % (section, key, val))
            if secs:
                L.append("")
                L.append("## 配置（白名单，已脱敏）")
                for s in secs:
                    L.append("- " + s)
        except Exception as e:
            L.append("- （配置读取失败：%s）" % e)
        # 故障日志
        try:
            _fp = os.path.join(CONFIG_DIR, "dafeiyu_fault.log")
            if os.path.exists(_fp):
                with open(_fp, "r", encoding="utf-8", errors="replace") as f:
                    _fl = f.read().splitlines()[-40:]
                if _fl:
                    L.append("")
                    L.append("## 崩溃/故障记录（最后 40 行）")
                    L.append("```")
                    for ln in _fl:
                        L.append(_fr_redact(ln)[:200])
                    L.append("```")
        except Exception:
            pass
        # 日志尾部（剔除台词/聊天类行）
        try:
            if os.path.exists(LOG_FILE):
                with open(LOG_FILE, "r", encoding="utf-8", errors="replace") as f:
                    _ll = f.read().splitlines()[-400:]
                _keep = [x for x in _ll if not any(t in x for t in _FR_LOG_DROP)]
                _keep = _keep[-100:]
                L.append("")
                L.append("## 日志尾部（已剔除台词/聊天，最后 %d 行）" % len(_keep))
                L.append("```")
                for ln in _keep:
                    L.append(_fr_redact(ln)[:200])
                L.append("```")
        except Exception:
            pass
        L.append("")
        L.append("---")
        L.append("说明：报告只含程序版本、环境、白名单配置与该程序自己的日志；")
        L.append("不含 API 密钥、聊天内容与台词。直接把它发给 AI 即可排查。")
        return chr(10).join(L)

    def export_fault_report(self):
        """一键导出故障报告到 userdata（并打开所在文件夹）。"""
        try:
            text = self._build_fault_report()
            name = "故障报告_%s.md" % datetime.now().strftime("%Y%m%d-%H%M%S")
            path = os.path.join(CONFIG_DIR, name)
            with open(path, "w", encoding="utf-8", newline="") as f:
                f.write(text)
            log.info("故障报告已导出：%s（%d 字）", path, len(text))
            try:
                os.startfile(CONFIG_DIR)
            except Exception:
                pass
            self._ui(lambda: self.show_bubble_text(
                "(relaxed) 报告写好啦，就在 userdata 里：%s" % name, "relaxed", status=True))
        except Exception as e:
            log.exception("导出故障报告失败: %s", e)
            _msg = "(worried) 报告没写成…%s" % e
            self._ui(lambda: self.show_bubble_text(_msg, "worried", status=True))

    def show_about(self):
        """关于框：署名按形态列（FORM_CREDITS 里为空的那几套先不显示）"""
        parts = ["严禁用于商业用途和收费。", ""]
        _filled = [k for k in available_forms() if (FORM_CREDITS.get(k) or "").strip()]
        for _key in available_forms():
            _credit = (FORM_CREDITS.get(_key) or "").strip()
            if not _credit:
                continue
            if len(_filled) > 1:      # 只有一套有署名时保持原文案，多了才加形态标签
                _label = LIVE2D_FORMS.get(_key, {}).get('label', _key)
                parts.append("[%s]\n%s" % (_label, _credit))
            else:
                parts.append(_credit)
            parts.append("")
        while parts and not parts[-1]:
            parts.pop()
        messagebox.showinfo("关于大肥鱼桌宠", "\n".join(parts))

    def on_close(self):
        self._shutdown = True
        # 11/14：退出前把没封的对话箱收掉（否则丢的正好是"刚聊完还没到 3 分钟"那段）
        try:
            self._box_maybe_seal(force=True)
        except Exception as e:
            log.debug("退出封箱失败: %s", e)
        self._stop_spine()
        if self.voice_on:
            self.toggle_voice(save=False)   # 退出时关麦只是清理：不能因此把她上次"开着"的选择冲掉
        if self.watch_mode:
            self.toggle_watch_mode()
        if self.reading_companion.enabled:
            self.reading_companion.stop()
        self._stop_audio_meter()
        for _job in (self.topic_timer_job, self.idle_check_job,
                     self._keep_top_job, self._energy_job, self._spine_loop_job,
                     self.action_timer_job):
            if _job:
                try:
                    self.root.after_cancel(_job)
                except Exception:
                    pass
        self.bubble_window.destroy()
        self.root.destroy()
        log.info("=== 大肥鱼桌宠退出 ===")

    # ---------- 记忆锚点系统（新）----------
    # 记忆管理方法将在 Phase 2 添加

    def open_memory_manager(self):
        # 打开管理器时重新载入磁盘上的记忆（提取可能在后台已更新文件，内存快照会过期）
        with self._memory_lock:
            self.memory_data = _migrate_old_memories(load_memories())
        win, frame = self._make_card_window("记忆锚点管理", 660, 820)
        s = self._dpi_scale
        # 关闭按钮先 pack 固定底部，内容再多也不会被裁剪
        RoundedButton(frame, text="关闭", command=win.destroy, width=int(110 * s), height=int(36 * s),
                      radius=int(6 * s), font=(self.font_family, 11)).pack(side=tk.BOTTOM, pady=10)
        notebook = ttk.Notebook(frame)
        notebook.pack(fill=tk.BOTH, expand=True)

        # 话题记忆 Tab
        topics_frame = tk.Frame(notebook, bg=DIALOG_BG)
        notebook.add(topics_frame, text="话题记忆")
        self._build_memory_listbox(topics_frame, "topics")

        # 事件记忆 Tab
        events_frame = tk.Frame(notebook, bg=DIALOG_BG)
        notebook.add(events_frame, text="事件记忆")
        self._build_memory_listbox(events_frame, "events")

        # 性格画像 Tab
        profile_frame = tk.Frame(notebook, bg=DIALOG_BG)
        notebook.add(profile_frame, text="性格画像")
        self._build_profile_tab(profile_frame)

        # 自我卡 Tab（11/14：她自己的一页，和性格画像并列）
        selfcard_frame = tk.Frame(notebook, bg=DIALOG_BG)
        notebook.add(selfcard_frame, text="自我卡")
        self._build_selfcard_tab(selfcard_frame)

    def _build_memory_listbox(self, parent, key):
        frame = tk.Frame(parent, bg=DIALOG_BG)
        frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        listbox = tk.Listbox(frame, font=(self.font_family, 9), bg="#ffffff", fg=TEXT_MAIN,
                             selectbackground=BTN_PRIMARY, selectforeground="#ffffff",
                             relief=tk.FLAT, highlightthickness=1, highlightbackground=INPUT_BORDER2)
        listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar = ttk.Scrollbar(frame, orient="vertical", command=listbox.yview)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        listbox.config(yscrollcommand=scrollbar.set)
        # 只有事件记忆用 importance 排序，话题不用——话题列表不再显示分数
        show_imp = (key == "events")
        items = self.memory_data.get(key, [])
        # 显示顺序：收藏的排在最前并锁定在上层（新记忆只加在收藏块下面）；其余保持原有先后顺序。
        # 只改"显示顺序"，不动 items 本身 —— 提取提示词用 topics[-10:] 代表"最近 10 条"，挪数组会破坏语义。
        view = []                    # 列表下标 → 记忆条目

        detail_frame = tk.Frame(parent, bg=DIALOG_BG)
        detail_frame.pack(fill=tk.BOTH, expand=False, padx=5, pady=(0, 5))
        detail_text = scrolledtext.ScrolledText(
            detail_frame, wrap="word", font=(self.font_family, 10),
            bg="#ffffff", fg=TEXT_MAIN, height=6, relief=tk.FLAT, bd=0,
            highlightthickness=1, highlightbackground=INPUT_BORDER2
        )
        detail_text.pack(fill=tk.BOTH, expand=True)

        def show_detail(event=None):
            sel = listbox.curselection()
            detail_text.config(state=tk.NORMAL)
            detail_text.delete("1.0", tk.END)
            if sel:
                idx = sel[0]
                if 0 <= idx < len(view):
                    item = view[idx]
                    date_str = item.get("created_at", "")[:10]
                    src = item.get("source", "")
                    detail = f"时间：{date_str}\n内容：{item['content']}"
                    if show_imp:
                        detail += f"\n重要度：{item.get('importance', 0.5):.2f}"
                    if src:
                        detail += f"\n来源：{src}"
                    detail += "\n收藏：" + ("是（置顶、不参与归档）" if item.get("starred", False) else "否")
                    detail += "\n状态：" + ("已归档（满 5 天会彻底删除）" if item.get("archived", False) else "正常")
                    detail_text.insert("1.0", detail)
            detail_text.config(state=tk.DISABLED)

        def rebuild_view():
            starred = [it for it in items if it.get("starred", False)]
            # 收藏块里"最近收藏的在最上面"（没有 starred_at 的老数据按原顺序垫在收藏块末尾）
            starred.sort(key=lambda it: it.get("starred_at") or "", reverse=True)
            view[:] = starred + [it for it in items if not it.get("starred", False)]

        def render(select_id=None):
            """按 view 顺序重画：收藏行深底 + ★，已归档行灰字并在末尾标「已归档」"""
            listbox.delete(0, tk.END)
            for it in view:
                label = ("★ " if it.get("starred", False) else "") + \
                        f"{it.get('created_at', '')[:10]} | {it['content']}"
                if show_imp:
                    label += f" | 重要:{it.get('importance', 0.5):.1f}"
                if it.get("source", ""):
                    label += f" | {it['source']}"
                if it.get("archived", False):
                    label += " | 已归档"
                listbox.insert(tk.END, label)
            for i, it in enumerate(view):
                if it.get("starred", False):
                    listbox.itemconfig(i, background=STAR_ROW_BG)
                elif it.get("archived", False):
                    listbox.itemconfig(i, background=ARCHIVE_ROW_BG, foreground=ARCHIVE_ROW_FG)
            if select_id is not None:
                for i, it in enumerate(view):
                    if it.get("id") == select_id:
                        listbox.selection_set(i)
                        listbox.see(i)
                        break
            sync_star_btn()
            show_detail()

        def refresh(select_id=None):
            rebuild_view()
            render(select_id)

        def sync_star_btn():
            # 10/31：按钮已删，收藏/取消收藏的文案改由右键菜单在弹出时动态改（见 _popup）
            return

        def on_select(event=None):
            sync_star_btn()
            show_detail(event)

        listbox.bind("<<ListboxSelect>>", on_select)

        def delete_selected():
            sel = listbox.curselection()
            if not sel:
                return
            # 从大到小删，保证剩余索引不漂移；列表下标要经 view 映射回真实条目
            for idx in sorted(sel, reverse=True):
                if 0 <= idx < len(view) and view[idx] in items:
                    items.remove(view[idx])
            save_memories(self.memory_data)
            refresh()

        def clear_all():
            if messagebox.askyesno("确认", f"删除所有{key}记忆？"):
                items.clear()
                save_memories(self.memory_data)
                refresh()

        def toggle_star():
            sel = listbox.curselection()
            if not sel or not (0 <= sel[0] < len(view)):
                return
            item = view[sel[0]]
            item["starred"] = not item.get("starred", False)
            if item["starred"]:
                # 收藏即保住：顺手把归档状态摘掉，否则它照样会满 5 天被彻底删除
                item["starred_at"] = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                item["archived"] = False
                item["archived_at"] = None
            else:
                item["starred_at"] = None
            save_memories(self.memory_data)
            log.info("记忆%s：%s", "已收藏" if item["starred"] else "已取消收藏",
                     (item.get("content") or "")[:24])
            refresh(select_id=item.get("id"))

        # 10/31：底部按钮行整块删掉，改成右键菜单 + Delete 键（把高度让给详情面板）
        _menu = tk.Menu(listbox, tearoff=0)
        _menu.add_command(label="收藏", command=toggle_star)
        _menu.add_command(label="删除选中", command=delete_selected)
        _menu.add_separator()
        _menu.add_command(label="清空所有", command=clear_all)

        def _popup(e):
            try:
                idx = listbox.nearest(e.y)
                if idx >= 0:
                    listbox.selection_clear(0, tk.END)
                    listbox.selection_set(idx)
            except Exception:
                pass
            try:
                cur = listbox.curselection()
                _star = bool(cur and 0 <= cur[0] < len(view) and view[cur[0]].get("starred"))
                _menu.entryconfigure(0, label="取消收藏" if _star else "收藏")
            except Exception:
                pass
            try:
                _menu.tk_popup(e.x_root, e.y_root)
            finally:
                _menu.grab_release()

        listbox.bind("<Button-3>", _popup)
        listbox.bind("<Delete>", lambda e: (delete_selected(), "break")[1])
        listbox.bind("<BackSpace>", lambda e: (delete_selected(), "break")[1])

        refresh()

    # ---------- 自我卡页面（P4，11/14）----------
    def _build_selfcard_tab(self, parent):
        s = self._dpi_scale
        frame = tk.Frame(parent, bg=DIALOG_BG)
        frame.pack(fill=tk.BOTH, expand=True, padx=8, pady=6)
        tk.Label(frame, text="她自己的一页：她对自己是什么样的人的认定；每轮原样注入给模型，由她自己写（每周结晶一次），也能直接改。最多 %d 字。" % SELFCARD_MAX_CHARS,
                 font=(self.font_family, 9), fg=TEXT_SUB, bg=DIALOG_BG, justify="left",
                 wraplength=int(600 * s)).pack(anchor="w")

        box = tk.Frame(frame, bg=DIALOG_BG)
        box.pack(fill=tk.BOTH, expand=True, pady=(6, 4))
        text_widget = tk.Text(box, font=(self.font_family, 10), bg="#ffffff", fg=TEXT_MAIN,
                              relief=tk.FLAT, highlightthickness=1, highlightbackground=INPUT_BORDER2,
                              wrap=tk.WORD, height=10, padx=8, pady=6)
        text_widget.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        sb = ttk.Scrollbar(box, orient="vertical", command=text_widget.yview)
        sb.pack(side=tk.RIGHT, fill=tk.Y)
        text_widget.config(yscrollcommand=sb.set)
        _st = self._selfcard_get()
        text_widget.insert("1.0", str(_st.get("text") or ""))

        status_var = tk.StringVar()

        def _refresh_status():
            _s = self._selfcard_get()
            status_var.set("上次改写：%s　｜　历史版本：%d 条" % (
                (_s.get("updated_at") or "还没写过"), len(_s.get("history") or [])))

        _refresh_status()
        tk.Label(frame, textvariable=status_var, font=(self.font_family, 9),
                 fg=TEXT_SUB, bg=DIALOG_BG).pack(anchor="w")

        row = tk.Frame(frame, bg=DIALOG_BG)
        row.pack(fill=tk.X, pady=(6, 0))

        def _save():
            body = text_widget.get("1.0", "end").strip()
            if len(body) > SELFCARD_MAX_CHARS:
                messagebox.showwarning("太长", "最多 %d 字，现在 %d 字。" % (SELFCARD_MAX_CHARS, len(body)),
                                       parent=parent)
                return
            self._selfcard_save(body, why="手改")
            _refresh_status()
            self.show_bubble_text("（happy）记下了，我以后就照着这个来。", "happy")

        def _rewrite():
            def _run():
                new = self._selfcard_crystallize(force=True)

                def _done():
                    if new:
                        text_widget.delete("1.0", "end")
                        text_widget.insert("1.0", new)
                        _refresh_status()
                self._ui(_done)
            threading.Thread(target=_run, daemon=True).start()

        def _history():
            win2 = tk.Toplevel(parent)
            win2.title("自我卡历史")
            win2.configure(bg=DIALOG_BG)
            tk.Label(win2, text="选中一条可以回滚（当前版本会被存进历史）",
                     font=(self.font_family, 9), fg=TEXT_SUB, bg=DIALOG_BG).pack(pady=(8, 2))
            lb = tk.Listbox(win2, width=64, height=12, font=(self.font_family, 9),
                            bg="#ffffff", fg=TEXT_MAIN, relief=tk.FLAT, highlightthickness=1,
                            highlightbackground=INPUT_BORDER2)
            lb.pack(padx=10, pady=4, fill=tk.BOTH, expand=True)
            _hist = list(self._selfcard_get().get("history") or [])
            for h in reversed(_hist):
                lb.insert("end", "%s｜%s｜%s" % (h.get("saved_at") or "?", h.get("why") or "改写",
                                              str(h.get("text") or "").replace(chr(10), " ")[:40]))

            def _rollback():
                sel = lb.curselection()
                if not sel:
                    return
                idx = len(_hist) - 1 - sel[0]
                old_text = str(_hist[idx].get("text") or "")
                self._selfcard_save(old_text, why="回滚")
                text_widget.delete("1.0", "end")
                text_widget.insert("1.0", old_text)
                _refresh_status()
                win2.destroy()

            RoundedButton(win2, text="回滚到这一版", command=_rollback, width=int(150 * s),
                          height=int(32 * s), radius=int(6 * s),
                          font=(self.font_family, 10)).pack(pady=8)

        RoundedButton(row, text="保存", command=_save, width=int(110 * s), height=int(32 * s),
                      radius=int(6 * s), font=(self.font_family, 10, "bold")).pack(side=tk.LEFT, padx=(0, 8))
        RoundedButton(row, text="现在重写一次", command=_rewrite, variant="subtle",
                      width=int(150 * s), height=int(32 * s), radius=int(6 * s),
                      font=(self.font_family, 10)).pack(side=tk.LEFT, padx=(0, 8))
        RoundedButton(row, text="历史", command=_history, variant="subtle",
                      width=int(90 * s), height=int(32 * s), radius=int(6 * s),
                      font=(self.font_family, 10)).pack(side=tk.LEFT)

    def _build_profile_tab(self, parent):
        s = self._dpi_scale
        # 10/31：不再有底部按钮行（全部改成右键菜单），空间留给详情面板

        # 关系形象（独立栏目）：宠物当前对用户关系认知的单槽总结
        # 用描边卡片框住，与下方"认知条目"表格在视觉上分开
        rel_box = tk.Frame(parent, bg=INPUT_BG, highlightthickness=max(1, int(1.5 * s)),
                           highlightbackground=CARD_BORDER_STRONG, highlightcolor=CARD_BORDER_STRONG)
        rel_box.pack(fill=tk.X, padx=5, pady=(6, 6))
        rel_inner = tk.Frame(rel_box, bg=INPUT_BG)
        rel_inner.pack(fill=tk.X, padx=int(10 * s), pady=int(8 * s))
        rel_title = tk.Label(rel_inner, text="关系形象", font=(self.font_family, 11, "bold"),
                             fg=TEXT_MAIN, bg=INPUT_BG)
        rel_title.pack(anchor="w")
        # 顶部只显示"一句话关系描述"；日期/确信度/证据数等详细数据只进下方详情栏
        rel_label = tk.Label(rel_inner, text="", font=(self.font_family, 10), fg=TEXT_MAIN, bg=INPUT_BG,
                             cursor="hand2", anchor="w", justify="left",
                             wraplength=int(430 * s))
        rel_label.pack(fill=tk.X, pady=(int(4 * s), 0))

        def refresh_rel_view():
            rel = (self.memory_data.get("profile", {}) or {}).get("relation") or {}
            content = (rel.get("content") or "").strip()
            if content:
                rel_label.config(text=content, fg=TEXT_MAIN)
            else:
                rel_label.config(text="（暂无——多聊几次，她会慢慢形成对你的关系认知）", fg="#b8b0cc")

        def clear_relation():
            if messagebox.askyesno("确认", "清除关系形象？"):
                self.memory_data.setdefault("profile", {})["relation"] = None
                save_memories(self.memory_data)
                refresh_rel_view()
                detail_text.config(state=tk.NORMAL)
                detail_text.delete("1.0", tk.END)
                detail_text.insert("1.0", "关系形象\n\n（已清除）")
                detail_text.config(state=tk.DISABLED)

        refresh_rel_view()

        # 10/28：自我认知（self/lesson）+ 关于他（about_user）—— 两张卡合成一张，上下两区。
        # 10/28 用户："界面还是臃肿" ⇒ 去掉说明文案那一行、去掉删除按钮（改 Delete 键）。
        note_box = tk.Frame(parent, bg=INPUT_BG, highlightthickness=max(1, int(1.5 * s)),
                            highlightbackground=CARD_BORDER_STRONG, highlightcolor=CARD_BORDER_STRONG)
        note_box.pack(fill=tk.X, padx=5, pady=(0, 6))
        note_inner = tk.Frame(note_box, bg=INPUT_BG)
        note_inner.pack(fill=tk.X, padx=int(10 * s), pady=int(7 * s))
        tk.Label(note_inner, text="自我认知", font=(self.font_family, 10, "bold"),
                 fg=TEXT_MAIN, bg=INPUT_BG).pack(anchor="w")
        note_wrap = tk.Frame(note_inner, bg=INPUT_BG)
        note_wrap.pack(fill=tk.X, pady=(int(3 * s), int(6 * s)))
        note_scroll = ttk.Scrollbar(note_wrap, orient="vertical")
        note_list = tk.Listbox(note_wrap, height=3, font=(self.font_family, 9), bg="#ffffff",
                               fg=TEXT_MAIN, relief=tk.FLAT, highlightthickness=1,
                               highlightbackground=INPUT_BORDER2, activestyle="none",
                               selectbackground=BTN_PRIMARY, selectforeground="#ffffff",
                               yscrollcommand=note_scroll.set)
        note_scroll.config(command=note_list.yview)
        note_list.pack(side=tk.LEFT, fill=tk.X, expand=True)
        tk.Label(note_inner, text="他的习惯（补充）", font=(self.font_family, 10, "bold"),
                 fg=TEXT_MAIN, bg=INPUT_BG).pack(anchor="w")
        ub_wrap = tk.Frame(note_inner, bg=INPUT_BG)
        ub_wrap.pack(fill=tk.X, pady=(int(3 * s), 0))
        ub_scroll = ttk.Scrollbar(ub_wrap, orient="vertical")
        ub_list = tk.Listbox(ub_wrap, height=2, font=(self.font_family, 9), bg="#ffffff",
                             fg=TEXT_MAIN, relief=tk.FLAT, highlightthickness=1,
                             highlightbackground=INPUT_BORDER2, activestyle="none",
                             selectbackground=BTN_PRIMARY, selectforeground="#ffffff",
                             yscrollcommand=ub_scroll.set)
        ub_scroll.config(command=ub_list.yview)
        ub_list.pack(side=tk.LEFT, fill=tk.X, expand=True)

        def _fit(listbox, scrollbar, count, min_rows, max_rows):
            """按条数自动决定列表高度；超出可视行数时才挂出滚动条（10/28）。"""
            rows = max(min_rows, min(max_rows, count))
            try:
                listbox.config(height=rows)
            except Exception:
                pass
            if count > rows:
                scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
            else:
                scrollbar.pack_forget()

        def _list_menu(listbox, on_delete, on_clear, clear_label="清空全部",
                       on_star=None, is_starred=None):
            """右键菜单：收藏 / 删除选中 / 清空全部（10/31 用户报"没有删除和清空方式"）。"""
            m = tk.Menu(listbox, tearoff=0)
            if on_star is not None:
                m.add_command(label="收藏", command=on_star)
            m.add_command(label="删除选中", command=on_delete)
            m.add_separator()
            m.add_command(label=clear_label, command=on_clear)

            def popup(e):
                try:
                    idx = listbox.nearest(e.y)
                    if idx >= 0:
                        listbox.selection_clear(0, tk.END)
                        listbox.selection_set(idx)
                except Exception:
                    pass
                if on_star is not None:
                    try:
                        m.entryconfigure(0, label="取消收藏" if (is_starred and is_starred()) else "收藏")
                    except Exception:
                        pass
                try:
                    m.tk_popup(e.x_root, e.y_root)
                finally:
                    m.grab_release()
            listbox.bind("<Button-3>", popup)
            return m

        def refresh_note_view():
            note_list.delete(0, tk.END)
            notes = (self.memory_data.get("profile", {}) or {}).get("notes") or []
            if not notes:
                note_list.insert(tk.END, "（还没有——聊到她的立场感受、或需要记住的教训时，会写在这里）")
                return
            for i, n in enumerate(notes):
                ev = int(n.get("evidence_count", 1) or 1)
                tag = "教训" if n.get("kind") == "lesson" else "认定"
                note_list.insert(tk.END, "%s· [%s] %s%s" % (
                    "★ " if n.get("starred") else "", tag, str(n.get("content") or ""),
                    ("（%d 次）" % ev) if ev > 1 else ""))
                if n.get("starred"):
                    note_list.itemconfig(i, background=STAR_ROW_BG)
            _fit(note_list, note_scroll, len(notes), 3, 6)

        def delete_note(event=None):
            sel = note_list.curselection()
            notes = (self.memory_data.get("profile", {}) or {}).get("notes") or []
            if not sel or not notes or sel[0] >= len(notes):
                return
            if not messagebox.askyesno("确认", "删除这条自我认知？\n\n%s" % str(notes[sel[0]].get("content") or "")[:60]):
                return
            notes.pop(sel[0])
            save_memories(self.memory_data)
            refresh_note_view()

        def clear_notes():
            notes = (self.memory_data.get("profile", {}) or {}).get("notes") or []
            if not notes:
                return
            if not messagebox.askyesno("确认", "清空全部自我认知？共 %d 条，不能撤销。" % len(notes)):
                return
            notes.clear()
            save_memories(self.memory_data)
            refresh_note_view()

        def toggle_note_star():
            sel = note_list.curselection()
            notes = (self.memory_data.get("profile", {}) or {}).get("notes") or []
            if not sel or not notes or sel[0] >= len(notes):
                return
            n = notes[sel[0]]
            n["starred"] = not n.get("starred", False)
            n["starred_at"] = datetime.now().strftime("%Y-%m-%d %H:%M:%S") if n["starred"] else None
            save_memories(self.memory_data)
            log.info("自我认知%s：%s", "已收藏" if n["starred"] else "已取消收藏",
                     str(n.get("content") or "")[:24])
            refresh_note_view()
            try:
                note_list.selection_set(sel[0])
            except Exception:
                pass

        def _note_sel_starred():
            sel = note_list.curselection()
            notes = (self.memory_data.get("profile", {}) or {}).get("notes") or []
            return bool(sel and notes and sel[0] < len(notes) and notes[sel[0]].get("starred"))

        note_list.bind("<Delete>", lambda e: (delete_note(), "break")[1])
        note_list.bind("<BackSpace>", lambda e: (delete_note(), "break")[1])
        _list_menu(note_list, delete_note, clear_notes,
                   on_star=toggle_note_star, is_starred=_note_sel_starred)
        refresh_note_view()

        def refresh_user_notes():
            ub_list.delete(0, tk.END)
            items = (self.memory_data.get("profile", {}) or {}).get("user_notes") or []
            if not items:
                ub_list.insert(tk.END, "（还没有——聊到你的习惯、偏好或忌讳时，会写在这里）")
                return
            for n in items:
                ev = int(n.get("evidence_count", 1) or 1)
                ub_list.insert(tk.END, "· %s%s" % (
                    str(n.get("content") or ""), ("（%d 次）" % ev) if ev > 1 else ""))
            _fit(ub_list, ub_scroll, len(items), 2, 4)

        def delete_user_note(event=None):
            sel = ub_list.curselection()
            items = (self.memory_data.get("profile", {}) or {}).get("user_notes") or []
            if not sel or not items or sel[0] >= len(items):
                return
            if not messagebox.askyesno("确认", "删除这条？\n\n%s" % str(items[sel[0]].get("content") or "")[:60]):
                return
            items.pop(sel[0])
            save_memories(self.memory_data)
            refresh_user_notes()

        def clear_user_notes():
            items = (self.memory_data.get("profile", {}) or {}).get("user_notes") or []
            if not items:
                return
            if not messagebox.askyesno("确认", "清空全部「他的习惯」？共 %d 条，不能撤销。" % len(items)):
                return
            items.clear()
            save_memories(self.memory_data)
            refresh_user_notes()

        ub_list.bind("<Delete>", lambda e: (delete_user_note(), "break")[1])
        ub_list.bind("<BackSpace>", lambda e: (delete_user_note(), "break")[1])
        _list_menu(ub_list, delete_user_note, clear_user_notes)
        refresh_user_notes()

        # 详情显示框：**必须在会 expand 的表格之前 pack**，否则表格涨大时它会被挤掉。
        # （10/28 用户问「列表长高会不会挤走详情框」—— 现在有结构性保证，不是碰巧够用）
        detail_frame = tk.Frame(parent, bg=DIALOG_BG)
        detail_frame.pack(side=tk.BOTTOM, fill=tk.X, padx=5, pady=(0, 5))
        detail_text = scrolledtext.ScrolledText(
            detail_frame, wrap="word", font=(self.font_family, 10),
            bg="#ffffff", fg=TEXT_MAIN, height=5, width=1, relief=tk.FLAT, bd=0,
            highlightthickness=1, highlightbackground=INPUT_BORDER2
        )
        detail_text.pack(fill=tk.BOTH, expand=True)

        frame = tk.Frame(parent, bg=DIALOG_BG)
        frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        columns = ("条目", "描述", "证据")
        tree = ttk.Treeview(frame, columns=columns, show="headings", height=12)
        for col in columns:
            tree.heading(col, text=col)
        tree.column("条目", width=90, anchor="w")
        tree.column("描述", width=230, anchor="w")
        tree.column("证据", width=200, anchor="w")
        tree.tag_configure("empty", foreground="#b8b0cc")
        tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar = ttk.Scrollbar(frame, orient="vertical", command=tree.yview)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        tree.config(yscrollcommand=scrollbar.set)

        traits = self.memory_data.get("profile", {}).get("traits", [])

        def clip(text, limit):
            text = str(text).replace("\n", " ")
            return text if len(text) <= limit else text[:limit] + "…"

        def refresh_rows():
            for item in tree.get_children():
                tree.delete(item)
            by_name = {t.get("trait"): t for t in traits if t.get("trait") in TRAIT_LIST}
            for name in TRAIT_LIST:
                t = by_name.get(name)
                if t is None or (not (t.get("description") or "").strip() and not t.get("evidence")):
                    tree.insert("", tk.END, iid=f"trait_{name}",
                                values=(name, "— 还没了解到 —", "—"), tags=("empty",))
                else:
                    desc = (t.get("description") or "").strip()
                    if not desc:
                        desc = "（暂无概括）"
                    evs = [str(e).strip() for e in (t.get("evidence") or []) if str(e).strip()]
                    ev_txt = clip(evs[-1], 60) if evs else "（无证据）"
                    tree.insert("", tk.END, iid=f"trait_{name}",
                                values=(name, clip(desc, 60), ev_txt))
            show_detail()


        def show_detail(event=None):
            detail_text.config(state=tk.NORMAL)
            detail_text.delete("1.0", tk.END)
            sel = tree.selection()
            if sel:
                name = sel[0][len("trait_"):]
                t = next((x for x in traits if x.get("trait") == name), None)
                if t is None or (not (t.get("description") or "").strip() and not t.get("evidence")):
                    detail = f"{name}\n（还没有观察到任何内容）"
                else:
                    desc = (t.get("description") or "").strip() or "（暂无概括，仅积累观察）"
                    evs = [str(e).strip() for e in (t.get("evidence") or []) if str(e).strip()]
                    # 10/28：详情框只有 3 行，**不留空行**（用户："内容之间为什么要空行，显示区域本来就窄"）
                    lines = [f"{name}｜{desc}",
                             f"证据 {len(evs)} 条：" + ("；".join(f"{j}.{ev}" for j, ev in enumerate(evs, 1)) or "（无）"),
                             f"更新 {str(t.get('updated_at', ''))[5:16]}"]
                    detail = "\n".join(lines)
                detail_text.insert("1.0", detail)
            else:
                detail_text.insert("1.0", "点击任意条目看详情；点「关系形象」看更新时间。")
            detail_text.config(state=tk.DISABLED)

        tree.bind("<<TreeviewSelect>>", show_detail)


        def show_relation(event=None):
            """点击顶部关系描述：日期/确信度/证据数等详细数据只在详情栏展示"""
            for it in tree.selection():
                tree.selection_remove(it)
            detail_text.config(state=tk.NORMAL)
            detail_text.delete("1.0", tk.END)
            rel = (self.memory_data.get("profile", {}) or {}).get("relation") or {}
            content = (rel.get("content") or "").strip()
            if content:
                # 10/28：与条目详情同一格式 —— 不留空行，3 行装下
                detail_text.insert("1.0", "\n".join([
                    f"关系形象｜{content}",
                    f"累计观察 {rel.get('evidence_count', 1)} 次",
                    f"更新 {str(rel.get('updated_at', ''))[5:16]}"]))
            else:
                detail_text.insert("1.0", "关系形象\n（暂无——多聊几次，她会慢慢形成对你的关系认知）")
            detail_text.config(state=tk.DISABLED)

        # 整块「关系形象」卡片都可点击（标题、描述、内边距、边框），不是只有文字
        for _w in (rel_box, rel_inner, rel_title, rel_label):
            _w.bind("<Button-1>", show_relation)
            _w.configure(cursor="hand2")

        def clear_selected():
            sel = tree.selection()
            if not sel:
                return
            name = sel[0][len("trait_"):]
            t = next((x for x in traits if x.get("trait") == name), None)
            if t is None:
                return
            if not messagebox.askyesno("确认", f"清空条目「{name}」的观察内容？\n（条目本身会保留，重新观察到内容后会再填上）"):
                return
            traits.remove(t)
            save_memories(self.memory_data)
            refresh_rows()

        def clear_all():
            if messagebox.askyesno("确认", "清空所有画像的观察内容？\n（固定条目框架会保留，以后观察到内容会再填上）"):
                traits.clear()
                save_memories(self.memory_data)
                refresh_rows()

        # 10/31：三个按钮改成右键菜单 —— 条目表上右键清空条目/清空所有，关系形象卡上右键清除
        _tree_menu = tk.Menu(tree, tearoff=0)
        _tree_menu.add_command(label="清空此条内容", command=clear_selected)
        _tree_menu.add_command(label="清空所有画像", command=clear_all)

        def _tree_popup(e):
            try:
                iid = tree.identify_row(e.y)
                if iid:
                    tree.selection_set(iid)
            except Exception:
                pass
            try:
                _tree_menu.tk_popup(e.x_root, e.y_root)
            finally:
                _tree_menu.grab_release()

        tree.bind("<Button-3>", _tree_popup)

        _rel_menu = tk.Menu(parent, tearoff=0)
        _rel_menu.add_command(label="清除关系形象", command=clear_relation)

        def _rel_popup(e):
            try:
                _rel_menu.tk_popup(e.x_root, e.y_root)
            finally:
                _rel_menu.grab_release()

        for _w in (rel_box, rel_inner, rel_title, rel_label):
            _w.bind("<Button-3>", _rel_popup)

        refresh_rows()

    # ---------- 记忆提取核心方法 ----------
    def _add_topic_memory(self, content, importance=0.5, force_new=False, kind=None):
        """添加话题记忆，简单去重后写入"""
        content = content.strip()
        if len(content) < 2:
            return
        add_topic_material(content, "topic")   # 11/01：话题记忆和事件记忆平行进素材池
        with self._memory_lock:
            topics = self.memory_data.setdefault("topics", [])
            if not force_new:
                # 10/28：两个池当一个池查重 —— 同一件事不能一边存 topics 一边存 events
                dup = self._find_similar_memory(
                    content, list(self.memory_data.get("events", [])),
                    MEMORY_TOPIC_MERGE_THRESHOLD)
                if dup is not None:
                    dup["archived"] = False
                    dup["evidence_count"] = dup.get("evidence_count", 1) + 1
                    dup["importance"] = min(1.0, float(dup.get("importance") or 0.5) + 0.05)
                    dup["last_accessed_at"] = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                    save_memories(self.memory_data)
                    log.info("跨池去重（并入 event）：%s", content[:30])
                    return
                dup = self._find_similar_memory(content, topics, MEMORY_TOPIC_MERGE_THRESHOLD)
                if dup is not None:
                    dup["archived"] = False
                    dup["evidence_count"] = dup.get("evidence_count", 1) + 1
                    boost = 0.1 * importance * (1 - dup["importance"])
                    dup["importance"] = min(1.0, dup["importance"] + boost)
                    dup["last_accessed_at"] = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                    save_memories(self.memory_data)
                    return
            now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            topics.append({
                "id": str(uuid.uuid4())[:8],
                "content": content,
                "created_at": now,
                "last_accessed_at": now,
                "importance": importance,
                "kind": kind or "experience",
                "access_count": 0,
                "evidence_count": 1,
                "archived": False
            })
            self._prune_memories("topics")
            save_memories(self.memory_data)

    def _add_event_memory(self, content, importance=0.7, source="chat", force_new=False, kind=None):
        """添加事件记忆"""
        content = content.strip()
        if len(content) < 2:
            return
        add_topic_material(content, "event")   # 真事攒进素材池，给话题取材
        with self._memory_lock:
            events = self.memory_data.setdefault("events", [])
            if not force_new:
                # 10/28：两个池当一个池查重（同上）
                dup = self._find_similar_memory(
                    content, list(self.memory_data.get("topics", [])),
                    MEMORY_TOPIC_MERGE_THRESHOLD)
                if dup is not None:
                    dup["archived"] = False
                    dup["evidence_count"] = dup.get("evidence_count", 1) + 1
                    dup["importance"] = min(1.0, float(dup.get("importance") or 0.5) + 0.05)
                    dup["last_accessed_at"] = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                    save_memories(self.memory_data)
                    log.info("跨池去重（并入 topic）：%s", content[:30])
                    return
                dup = self._find_similar_memory(content, events, MEMORY_EVENT_DUP_THRESHOLD)
                if dup is not None:
                    dup["archived"] = False
                    dup["evidence_count"] = dup.get("evidence_count", 1) + 1
                    boost = 0.1 * importance * (1 - dup["importance"])
                    dup["importance"] = min(1.0, dup["importance"] + boost)
                    dup["last_accessed_at"] = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                    save_memories(self.memory_data)
                    return  # 事件不重复记录
            now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            events.append({
                "id": str(uuid.uuid4())[:8],
                "content": content,
                "created_at": now,
                "last_accessed_at": now,
                "importance": importance,
                "source": source,
                "kind": kind or "experience",
                "access_count": 0,
                "evidence_count": 1,
                "archived": False
            })
            self._prune_memories("events")
            save_memories(self.memory_data)

    def _apply_profile_note(self, content, kind):
        """把 self / about_user / lesson 类记忆写进自我认知层（profile["notes"]）。

        10/28：这三类描述的是"她/他是什么样的人"，不是"发生了什么事"，所以不进经历池、
        不参与淘汰。同一件事反复出现只累加 evidence_count，不新增条目。
        """
        content = (content or "").strip()[:PROFILE_NOTE_CHARS]
        if len(content) < 4:
            return
        profile = self.memory_data.setdefault("profile", {})
        # 10/28 修正：**自我认知只放 self/lesson**；about_user 是"关于他"的事，归到 user_notes，
        # 界面上归性格画像那一侧（用户原话："【他】的描述不应该是写在性格画像里吗"）。
        _key = "user_notes" if kind == "about_user" else "notes"
        notes = profile.setdefault(_key, [])
        now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        # 判重先用向量（能认"他" vs "老大"这种换称呼），向量不可用时退回二元组
        _vec = None
        try:
            _vec = self._get_text_embedding(content)
        except Exception:
            _vec = None
        cg = {content[i:i + 2] for i in range(len(content) - 1)}
        for n in notes:
            old = str(n.get("content") or "")
            _dup = False
            if _vec is not None:
                try:
                    _ov = self._get_text_embedding(old)
                    if _ov is not None and float(np.dot(_vec, _ov)) >= PROFILE_NOTE_DUP_COS:
                        _dup = True
                except Exception:
                    _dup = False
            if not _dup:
                og = {old[i:i + 2] for i in range(len(old) - 1)}
                _dup = bool(og and cg and len(cg & og) / max(1, len(cg | og)) >= 0.6)
            if _dup:
                n["evidence_count"] = int(n.get("evidence_count", 1)) + 1
                n["updated_at"] = now
                save_memories(self.memory_data)
                log.info("自我认知合并（%d 次）：%s", n["evidence_count"], old[:30])
                return
        _new = {"id": str(uuid.uuid4())[:8], "content": content, "kind": kind,
                "created_at": now, "updated_at": now, "evidence_count": 1}
        notes.append(_new)
        # 10/28：溢出淘汰 —— **新来的必须留**（否则池子填满后新东西永远进不来），
        # 从"原有的"里面挑最该走的：只被印证过一次、且最久没更新。反复出现过的（evidence 高）最稳。
        if len(notes) > PROFILE_NOTES_MAX:
            # 排序键 = (被印证次数, 在列表里的位置)。位置当"新旧"用 —— 时间戳只到秒，
            # 同一秒内分不出先后，稳定排序会退化成"先来先留"，把刚写进来的又挤掉（实测踩到）。
            # 10/31：**收藏的不参与淘汰**（用户要求，和话题/事件同一口径）；收藏多到超容量也全留。
            _starred = [n for n in notes if n is not _new and n.get("starred")]
            _old = [(i, n) for i, n in enumerate(notes) if n is not _new and not n.get("starred")]
            _old.sort(key=lambda t: (int(t[1].get("evidence_count", 1) or 1), t[0]), reverse=True)
            _room = max(0, PROFILE_NOTES_MAX - 1 - len(_starred))
            _keep = _starred + [n for _, n in _old[:_room]]
            _dropped = [n for _, n in _old[_room:]]
            _keep_ids = {id(n) for n in _keep}
            notes[:] = [n for n in notes if n is _new or id(n) in _keep_ids]
            log.info("自我认知溢出，丢弃 %d 条（收藏 %d 条不参与）：%s", len(_dropped), len(_starred),
                     "；".join(str(d.get("content") or "")[:20] for d in _dropped))
        save_memories(self.memory_data)
        log.info("自我认知新增（%s）：%s", kind, content[:30])

    def _find_trait(self, trait_name):
        """按名称查找固定清单画像条目"""
        for t in self.memory_data.get("profile", {}).get("traits", []):
            if t.get("trait") == trait_name:
                return t
        return None

    def _apply_profile_update(self, update):
        """处理单条画像更新：trait 必须取自固定清单，只能更新 description / 追加 evidence。

        AI 只能往既定条目里填内容（不能自创/删除条目）；evidence 最多 MAX_TRAIT_EVIDENCE 条，
        满则丢最旧；description 仅在确实变化时更新。
        """
        trait_name = str(update.get("trait", "")).strip()
        if trait_name not in TRAIT_LIST:
            log.info(f"画像更新被忽略：条目「{trait_name}」不在固定清单内")
            return
        desc_raw = update.get("description")
        description = str(desc_raw).strip() if desc_raw is not None else ""
        ev_raw = update.get("evidence")
        evidence = str(ev_raw).strip() if ev_raw is not None else ""
        if not description and not evidence:
            return
        now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        with self._memory_lock:
            traits = self.memory_data.setdefault("profile", {}).setdefault("traits", [])

            existing = self._find_trait(trait_name)

            if existing is None:
                traits.append({
                    "trait": trait_name,
                    "description": description,
                    "evidence": [evidence] if evidence else [],
                    "created_at": now,
                    "updated_at": now,
                })
                save_memories(self.memory_data)
                return

            changed = False
            if description and description != existing.get("description", ""):
                existing["description"] = description
                changed = True
            if evidence:
                ev_list = existing.setdefault("evidence", [])
                if not isinstance(ev_list, list):
                    ev_list = []
                    existing["evidence"] = ev_list
                if evidence not in ev_list:
                    ev_list.append(evidence)
                    changed = True
                if len(ev_list) > MAX_TRAIT_EVIDENCE:
                    del ev_list[:len(ev_list) - MAX_TRAIT_EVIDENCE]
            if changed:
                existing["updated_at"] = now
                save_memories(self.memory_data)

    @staticmethod
    def _archive_expired(item, now):
        """归档（冷存）条目是否已满 ARCHIVE_TTL_DAYS 天、该彻底遗忘。
        没有归档时刻的老数据就地补记（从这次起算 5 天），不搞突然清除。"""
        stamp = item.get("archived_at")
        if not stamp:
            item["archived_at"] = now.strftime("%Y-%m-%d %H:%M:%S")
            return False
        try:
            t = datetime.strptime(str(stamp), "%Y-%m-%d %H:%M:%S")
        except (ValueError, TypeError):
            item["archived_at"] = now.strftime("%Y-%m-%d %H:%M:%S")
            return False
        return (now - t).total_seconds() >= ARCHIVE_TTL_DAYS * 86400

    @staticmethod
    def _memory_age_days(item, now):
        """记忆创建至今多少天（新记忆保护期用）；时间缺失或解析不了当作很久以前"""
        raw = str(item.get("created_at") or "").strip()
        if not raw:
            return 10 ** 6
        try:
            t = datetime.strptime(raw[:19], "%Y-%m-%d %H:%M:%S")
        except (ValueError, TypeError):
            return 10 ** 6
        return (now - t).total_seconds() / 86400.0

    def _prune_memories(self, category=None):
        """记忆裁剪（画像为固定清单，不参与）：
        ①归档满 ARCHIVE_TTL_DAYS 天的**彻底删除**（真遗忘，数据不再留）；
        ②活跃条目超过上限时，把按分数排在后头的超限部分标 archived＝冷存，并记下归档时刻。
        **收藏（starred）的永远不参与这两步**：既不被淘汰、也不会被过期删除；
        而且顺手把它从归档状态摘回来（用户"收藏一条已归档的"＝我要留住它）。"""
        categories = [category] if category else ["topics", "events"]
        now = datetime.now()
        purged = stamped = archived_now = revived = protected_now = 0
        for cat in categories:
            items = self.memory_data.get(cat, [])
            # ① 归档满期 → 彻底遗忘（收藏的例外：摘掉归档状态、永久保留）
            keep = []
            for item in items:
                if item.get("archived", False):
                    if item.get("starred", False):
                        item["archived"] = False
                        item["archived_at"] = None
                        revived += 1
                        keep.append(item)
                        continue
                    if not item.get("archived_at"):
                        stamped += 1
                    if self._archive_expired(item, now):
                        purged += 1
                        continue
                keep.append(item)
            if purged:
                self.memory_data[cat] = keep
                items = keep
            # ② 活跃超上限 → 归档（冷存），记下归档时刻
            #    收藏的占名额但不被淘汰 ⇒ 只从"非收藏"里淘汰，淘汰到 非收藏 ≤ 上限 − 收藏数
            #    新记忆保护期：创建不满 ARCHIVE_PROTECT_DAYS 天的先不参与淘汰（它们还没机会被想起，
            #    而打分只看"召回次数 + 最近被召回"，新条目天然垫底，会被成批冷存掉）
            max_count = MAX_TOPICS if cat == "topics" else MAX_EVENTS
            active_items = [item for item in items if not item.get("archived", False)]
            starred_n = sum(1 for item in active_items if item.get("starred", False))
            keep_quota = max(0, max_count - starred_n)
            candidates = [item for item in active_items if not item.get("starred", False)]
            protected, selectable = [], []
            for it in candidates:
                if self._memory_age_days(it, now) < ARCHIVE_PROTECT_DAYS:
                    protected.append(it)
                else:
                    selectable.append(it)
            protected_now += len(protected)
            need = len(candidates) - keep_quota      # 要淘汰掉几条才能回到上限
            if need <= 0:
                continue
            # 淘汰优先级：先动"保护期外"的（分数低的先走、同分老的先走＝同分保新），
            # 只有它们不够抵数时，才轮到"保护期内"的（规则一样：分数低的、老的先走）。
            # 保护期是"排队排到最后"，不是绝对免死 ⇒ 池子仍然守上限，不会因为一次爆发就无限膨胀，
            # 也不会因为保护期条目多就把老记忆一次清空。
            def _evict_key(it):
                s = self._score_topic_memory(it) if cat == "topics" else self._score_event_memory(it)
                return (s, str(it.get("created_at") or ""))

            evict_order = sorted(selectable, key=_evict_key) + sorted(protected, key=_evict_key)
            block_stamp = now.strftime("%Y-%m-%d %H:%M:%S")
            for item in evict_order[:need]:
                item["archived"] = True
                if not item.get("archived_at"):
                    item["archived_at"] = block_stamp
                archived_now += 1
        if purged:
            log.info(f"彻底遗忘 {purged} 条归档超过 {ARCHIVE_TTL_DAYS} 天的记忆")
        if revived:
            log.info(f"把 {revived} 条已收藏的记忆从归档状态摘回")
        if archived_now:
            log.info(f"记忆冷存 {archived_now} 条（超上限）；保护期内 {protected_now} 条本轮不参与淘汰")
        if purged or stamped or archived_now or revived:
            save_memories(self.memory_data)   # 删除、补记归档时刻、新归档、收藏复活都要落盘

    def _build_extraction_prompt(self):
        """构建记忆提取提示词"""
        topics = [t for t in self.memory_data.get("topics", []) if not t.get("archived", False)]
        topic_summaries = "\n".join([f"- {t['content']}" for t in topics[-10:]]) or "（无）"
        traits = self.memory_data.get("profile", {}).get("traits", [])
        known_traits = {t.get("trait"): t for t in traits if t.get("trait") in TRAIT_LIST}
        summary_lines = []
        for name in TRAIT_LIST:
            t = known_traits.get(name)
            if t and ((t.get("description") or "").strip() or t.get("evidence")):
                desc = (t.get("description") or "").strip() or "（暂无概括，仅积累观察）"
                ev_cnt = len([e for e in (t.get("evidence") or []) if str(e).strip()])
                summary_lines.append(f"- {name}：{desc}（已有{ev_cnt}条观察证据）")
        profile_summaries = "\n".join(summary_lines) or "（无——所有固定条目都还没有内容）"
        relation = self.memory_data.get("profile", {}).get("relation") or {}
        relation_text = (relation.get("content") or "").strip() or "（无）"
        persona_hint = ((self.character_config.get("persona") or DEFAULT_PERSONA)
                        .strip().replace("\n", " "))[:60]

        call_name = self.user_profile.get("call_name", "你")
        nickname = self.user_profile.get("nickname", call_name)
        TRAIT_STR = "/".join(TRAIT_LIST)
        _imp_existing = [str(i.get("text") or "").strip()
                         for i in (self.memory_data.get("impressions") or [])
                         if not i.get("invalid_at")]
        impressions_block = chr(10).join("- " + s for s in _imp_existing[-12:]) or "（还没有）"

        conversation_lines = []
        for turn in self._extraction_pending_turns:
            src = turn[0].get("source", "chat")
            prefix = {"watch": "[陪玩] ", "reading": "[读书] "}.get(src, "")
            conversation_lines.append(f"{prefix}{call_name}：{turn[0]['content']}")
            conversation_lines.append(f"{prefix}我：{turn[1]['content']}")
        conversation_text = "\n".join(conversation_lines)

        return f"""你正在为桌宠角色「{self.pet_name}」提取记忆。{self.pet_name}的人设概要：{persona_hint}……
请从以下对话历史中提取信息，用于更新{self.pet_name}（即对话中的“我”）的长期记忆。

【当前已有的话题记忆】（避免重复记录）：
{topic_summaries}

【当前已有的性格画像】：
{profile_summaries}

【当前关系形象】：
{relation_text}

【当前已有的看法（关于他）】（不要重复这些）：
{impressions_block}

【本次对话历史】：
{conversation_text}

请严格以JSON格式输出（不要markdown代码块，只输出纯JSON）：
{{
  "topics": [
    {{"content": "话题描述（40-60字以内）"}}
  ],
  "events": [
    {{"content": "事件描述（50字以内）", "kind": "experience", "source": "chat"}}
  ],
  "profile_updates": [
    {{"trait": "固定清单条目名", "description": "该条目的一句话概括，无变化填 null", "evidence": "本次观察到的一句具体证据（10字以上）"}}
  ],
  "relation_summary": "当前你与{call_name}的关系认知总结（25字以内，没有变化或证据不足时填 null）",
  "impressions": [
    {{"who": "him", "text": "一句话看法（≤40字，陈述句，写他是什么样，能被反驳）"}}
  ]
}}

规则：
- 人称与称呼：所有记录都以“我”（桌宠自己）的第一人称视角书写，对话中“我：”的行是我说的话；提到用户时用“{call_name}”称呼（用户昵称：{nickname}），禁止使用“用户”这样的第三人称称呼。
- topics: 提取对话中讨论过的话题。每条40-60字，尽量具体，不要只写泛化大类。话题不需要评分。与已有话题高度重复则跳过。
- events: 提取一起经历的事情。source固定为"chat"。每条50字以内。
- profile_updates: 把本次对话观察到的用户信息填入固定画像条目。trait 必须一字不差取自固定清单：{TRAIT_STR}，绝不能自创条目名；某条目本次没有新观察就整个不输出。description 是该条目整合新旧观察的一句话概括，认知没有实质变化就填 null（只更新 evidence）；evidence 是本次新观察到的一句具体证据（原话或具体场景，10字以上），同一句证据不要重复提交；没有合适条目的重要观察归入「其他」。
- relation_summary: 站在“我”（{self.pet_name}）的视角总结当前与{call_name}的关系认知（25字以内）——比如“我们是互相认定的人”“他是我要守护的人”。必须用{self.pet_name}自己的语气和用词习惯（人设概要：{persona_hint}……）来写，像她自己会说的话；结合已有内容与本次对话，有关系进展或认知变化才更新，没有则填 null。
- impressions：从这段对话里提炼**关于他的稳定看法**（他是什么样、一贯怎么做），不是"发生了什么"。每条≤40字、陈述句、要能被反驳（他看了会说"对"或"不是"）；最多 2 条；上面已列出的不要重复；没有就给空数组。
- 留意"我说了什么 → 他当场怎么回"这一对：某句被顶回、某句他接得很顺，都可以提炼成 1 条 kind=lesson 的陈述句（例如"我催他收枪时他会顶回来，换成拆台他接得住"）——只写事实，不写"我该怎么做"。
- 没有值得记录的内容时返回空数组。
- kind 必填，只能取这五个值之一（不要打分、不要自创）：
  self=我自己的立场或感受（例如“我不介意有犯傻的部分，那是他管我的由头”）；
  about_user={call_name}的稳定属性/习惯/忌讳（例如“他习惯边吃边刷视频”）——
    **能归进下面固定类目的，一律写进 profile_updates，不要写成 about_user**；
    只有确实归不进去的（比如“别提他丢包那件事”这种忌讳）才用 about_user；
  lesson=被纠正过、以后要避免的事；
  experience=一起经历过的一件事（一次性、具体的）；
  observe=陪看/陪读时看到的画面内容（流水账，最不值钱）；
  howto=操作步骤（例如“点播放键才能切歌”）——这类不要写进记忆。
  topics 也要输出 kind（通常 experience）。
- 标记为 [陪玩] 或 [读书] 的对话行：只提取话题记忆，不提取事件、性格画像和关系形象（这些内容不是真正的对话互动）。"""

    def _parse_extraction_result(self, json_str):
        """解析AI返回的记忆提取JSON，容错处理"""
        try:
            return json.loads(json_str)
        except json.JSONDecodeError:
            pass
        # 尝试去除 markdown 代码块
        m = re.search(r'```(?:json)?\s*\n?(.*?)```', json_str, re.DOTALL)
        if m:
            try:
                return json.loads(m.group(1).strip())
            except json.JSONDecodeError:
                pass
        # 尝试查找第一个 { 到最后一个 }
        m2 = re.search(r'\{.*\}', json_str, re.DOTALL)
        if m2:
            try:
                return json.loads(m2.group(0))
            except json.JSONDecodeError:
                pass
        return None

    def _trigger_memory_extraction(self):
        """触发记忆提取：构建提示词 → 调用AI → 解析 → 写入"""
        if time.time() < self._extraction_blocked_until:
            return
        if self._extraction_fail_count >= 3:
            log.warning("记忆提取连续失败3次，10分钟后重试（对话缓冲保留）")
            with self._memory_lock:
                self._extraction_fail_count = 0
                self._extraction_blocked_until = time.time() + 600
                self._pending_extraction_weight = 0.0
                self._persist_extraction_state()
            return
        if not self.text_api_key:
            log.warning("未配置文本模型 API Key，跳过记忆提取")
            return

        prompt = self._build_extraction_prompt()
        try:
            # Thinking 模型会消耗大量 token 在思考上：给足输出预算（16384），
            # 超时放宽到 180s，避免 JSON 只生成一半/思考吃光预算导致 content 为空
            resp = self._call_text_model([{"role": "user", "content": prompt}],
                                         temperature=0.3, max_tokens=EXTRACT_MAX_TOKENS, timeout=180)
            if resp.status_code != 200:
                log.error(f"记忆提取API失败: {resp.status_code}")
                self._extraction_fail_count += 1
                self._pending_extraction_weight = 0.0
                self._persist_extraction_state()
                return
            result_text = resp.json()["choices"][0]["message"]["content"]
            data = self._parse_extraction_result(result_text)
            if data is None:
                log.error(f"记忆提取JSON解析失败: {result_text[:200]}")
                self._extraction_fail_count += 1
                self._pending_extraction_weight = 0.0
                self._persist_extraction_state()
                return

            new_topics = data.get("topics", [])
            new_events = data.get("events", [])
            profile_updates = data.get("profile_updates", [])
            new_impressions = data.get("impressions", []) or []

            topics = self.memory_data.get("topics", [])
            events = self.memory_data.get("events", [])
            pending_judge = []
            topic_plain = []
            event_plain = []

            for t in new_topics:
                content = (t.get("content") or "").strip()
                if len(content) < 2:
                    continue
                _k = str(t.get("kind") or "experience").strip().lower()
                if _k not in KIND_SCORES:
                    _k = "experience"
                if _k in ("self", "about_user", "lesson"):
                    self._apply_profile_note(content, _k)   # 10/28：进自我认知层，不占经历池
                    continue
                imp = KIND_SCORES[_k]
                candidates = self._find_memory_candidates(content, topics, MEMORY_CANDIDATE_TOPIC_THRESHOLD)
                if candidates:
                    pending_judge.append({
                        "type": "topic",
                        "content": content,
                        "importance": imp,
                        "kind": _k,
                        "candidates": candidates
                    })
                else:
                    topic_plain.append((content, imp, _k))

            for e in new_events:
                content = (e.get("content") or "").strip()
                if len(content) < 2:
                    continue
                _k = str(e.get("kind") or "experience").strip().lower()
                if _k not in KIND_SCORES:
                    _k = "experience"
                if _k == "howto":
                    continue          # 操作流程属于系统知识，不写进记忆
                if _k in ("self", "about_user", "lesson"):
                    self._apply_profile_note(content, _k)   # 10/28：进自我认知层，不占经历池
                    continue
                imp = KIND_SCORES[_k]
                src = e.get("source", "chat")
                candidates = self._find_memory_candidates(content, events, MEMORY_CANDIDATE_EVENT_THRESHOLD)
                if candidates:
                    pending_judge.append({
                        "type": "event",
                        "content": content,
                        "importance": imp,
                        "kind": _k,
                        "source": src,
                        "candidates": candidates
                    })
                else:
                    event_plain.append((content, imp, src, _k))

            decisions = self._judge_memory_merge_with_ai(pending_judge) if pending_judge else {}

            if decisions is None:
                # AI 判断失败，回退到普通写入
                for content, imp, _kd in topic_plain:
                    self._add_topic_memory(content, imp, kind=_kd)
                for content, imp, src, _kd in event_plain:
                    self._add_event_memory(content, imp, src, kind=_kd)
                for item in pending_judge:
                    if item["type"] == "topic":
                        self._add_topic_memory(item["content"], item["importance"], kind=item.get("kind"))
                    else:
                        self._add_event_memory(item["content"], item["importance"], item["source"], kind=item.get("kind"))
            else:
                for idx, item in enumerate(pending_judge):
                    decision = decisions.get(idx)
                    if decision is None:
                        if item["type"] == "topic":
                            self._add_topic_memory(item["content"], item["importance"], kind=item.get("kind"))
                        else:
                            self._add_event_memory(item["content"], item["importance"], item["source"], kind=item.get("kind"))
                        continue
                    action = decision.get("action")
                    if action == "merge":
                        mid = decision.get("memory_id")
                        target = None
                        for cand in item["candidates"]:
                            if cand.get("id") == mid:
                                target = cand
                                break
                        if target is not None:
                            target["archived"] = False
                            now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                            target["evidence_count"] = target.get("evidence_count", 1) + 1
                            boost = 0.1 * item["importance"] * (1 - target.get("importance", 0.5))
                            target["importance"] = min(1.0, target.get("importance", 0.5) + boost)
                            target["last_accessed_at"] = now
                            save_memories(self.memory_data)
                        else:
                            if item["type"] == "topic":
                                self._add_topic_memory(item["content"], item["importance"], kind=item.get("kind"))
                            else:
                                self._add_event_memory(item["content"], item["importance"], item["source"], kind=item.get("kind"))
                    elif action == "new":
                        if item["type"] == "topic":
                            self._add_topic_memory(item["content"], item["importance"], force_new=True, kind=item.get("kind"))
                        else:
                            self._add_event_memory(item["content"], item["importance"], item["source"], force_new=True, kind=item.get("kind"))
                    elif action == "ignore":
                        pass
                    else:
                        if item["type"] == "topic":
                            self._add_topic_memory(item["content"], item["importance"])
                        else:
                            self._add_event_memory(item["content"], item["importance"], item["source"])

                for content, imp, _kd in topic_plain:
                    self._add_topic_memory(content, imp, kind=_kd)
                for content, imp, src, _kd in event_plain:
                    self._add_event_memory(content, imp, src, kind=_kd)

            for p in profile_updates:
                self._apply_profile_update(p)

            # 关系形象：单槽摘要，有更新则整体替换
            rel_new = data.get("relation_summary")
            if isinstance(rel_new, str) and rel_new.strip():
                rel_new = rel_new.strip()
                with self._memory_lock:
                    prof = self.memory_data.setdefault("profile", {})
                    old_rel = prof.get("relation") or {}
                    prof["relation"] = {
                        "content": rel_new,
                        "evidence_count": int(old_rel.get("evidence_count", 0)) + 1,
                        "updated_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                    }
                log.info("关系形象更新: %s", rel_new[:40])

            # 提取完成：清空待总结缓冲，保留最后 EXTRACTION_TRIGGER 轮作为粘合剂
            with self._memory_lock:
                self._prune_memories("topics")
                self._prune_memories("events")
                self._extraction_pending_turns = []
                self._pending_extraction_weight = 0.0
                self.chat_buffer = self.chat_buffer[-EXTRACTION_TRIGGER:]
                save_chats(self.chat_buffer)
                save_memories(self.memory_data)
                self._persist_extraction_state()
            self._extraction_fail_count = 0
            count = len(new_topics) + len(new_events) + len(profile_updates)
            log.info(f"记忆提取完成: {count} 条新记忆 (话题{len(new_topics)} 事件{len(new_events)} 画像{len(profile_updates)})")
            try:
                self._apply_impressions_from_extraction(new_impressions)
            except Exception as e:
                log.debug("印象入库失败: %s", e)
            self._maybe_induce()      # 11/01：经历攒够了就归纳成认知（后台，不挡）
            _fresh = [str(x.get("content") or "") for x in (new_topics or []) + (new_events or [])]
            threading.Thread(target=self._check_impression_conflicts,
                             args=(_fresh,), daemon=True).start()   # 11/14：改口检查
        except Exception as e:
            log.error(f"记忆提取异常: {e}")
            self._extraction_fail_count += 1
            self._pending_extraction_weight = 0.0
            self._persist_extraction_state()

    # ---------- 归纳：经历 → 认知（11/01）----------
    def _induce_state_path(self):
        return os.path.join(CONFIG_DIR, "induction_state.json")

    # ---------- 印象卡：权重 / 强化 / 分层（v2，11/14）----------
    def _impression_ensure_defaults(self):
        """补齐印象卡的缺省字段（旧数据 / 手写数据都能用）。"""
        for imp in (self.memory_data.get("impressions") or []):
            level = str(imp.get("level") or "normal")
            if level not in IMPRESSION_LEVEL_WEIGHT:
                level = "normal"
            imp["level"] = level
            if not isinstance(imp.get("links"), list):
                imp["links"] = []
            if not isinstance(imp.get("evidence_dates"), list):
                imp["evidence_dates"] = []
            if imp.get("weight") is None:
                imp["weight"] = IMPRESSION_LEVEL_WEIGHT[level]
            imp.setdefault("used_count", 0)
            imp.setdefault("evidence_count", max(1, len(imp["evidence_dates"])))
            imp.setdefault("invalid_at", None)
            imp.setdefault("superseded_by", None)

    def _impression_weight_eff(self, imp, now=None):
        """有效权重 = weight × exp(-距上次使用天数 / 半衰期)；core 不衰减。"""
        now = now or time.time()
        level = str(imp.get("level") or "normal")
        weight = float(imp.get("weight") or IMPRESSION_LEVEL_WEIGHT.get(level, 1.0))
        half = float(IMPRESSION_HALF_LIFE_DAYS.get(level, 30.0))
        if half <= 0:
            return weight
        stamp = imp.get("last_used_at") or imp.get("updated_at") or imp.get("created_at")
        days = 0.0
        try:
            if stamp:
                days = max(0.0, (now - self._mem_created_epoch({"created_at": stamp})) / 86400.0)
            else:
                days = 0.0
        except Exception:
            days = 0.0
        return weight * math.exp(-days / half)

    def _impression_hit(self, imp):
        """真的用上了一次：加法强化（有上限），并刷新使用时间。"""
        level = str(imp.get("level") or "normal")
        cap = float(IMPRESSION_LEVEL_CAP.get(level, 3.0))
        cur = float(imp.get("weight") or IMPRESSION_LEVEL_WEIGHT.get(level, 1.0))
        imp["weight"] = min(cap, cur + IMPRESSION_HIT_GAIN)
        imp["used_count"] = int(imp.get("used_count") or 0) + 1
        imp["last_used_at"] = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

    def _load_induce_state(self):
        # 11/14：判据从"绝对总数"改成"上次处理到哪个时刻"——
        # 旧版存 last_total，一旦淘汰把池子压小，total - last_total 永远是负数 ⇒ 归纳永久停摆。
        st = {"last_total": 0, "last_run": 0.0, "last_run_ts": 0.0}
        try:
            raw = json.load(open(self._induce_state_path(), encoding="utf-8"))
            if isinstance(raw, dict):
                st["last_total"] = int(raw.get("last_total") or 0)
                st["last_run"] = float(raw.get("last_run") or 0.0)
                st["last_run_ts"] = float(raw.get("last_run_ts") or 0.0)
        except Exception:
            pass
        return st

    @staticmethod
    def _mem_created_epoch(mem):
        """把 created_at（"2026-11-13 23:57:22" 或 epoch）统一成秒级浮点。"""
        v = (mem or {}).get("created_at")
        if isinstance(v, (int, float)):
            return float(v)
        try:
            return time.mktime(time.strptime(str(v)[:19], "%Y-%m-%d %H:%M:%S"))
        except Exception:
            return 0.0

    def _save_induce_state(self, st):
        try:
            with open(self._induce_state_path(), "w", encoding="utf-8") as f:
                json.dump(st, f, ensure_ascii=False)
        except Exception as e:
            log.debug("归纳状态存盘失败: %s", e)

    def _maybe_induce(self):
        """提取刚做完时看一眼：经历攒够了就在后台归纳一次，绝不挡主流程。"""
        try:
            st = self._load_induce_state()
            since = float(st.get("last_run_ts") or 0.0)
            fresh = 0
            for mem in (self.memory_data.get("events") or []) + (self.memory_data.get("topics") or []):
                if str(mem.get("content") or "").strip() and self._mem_created_epoch(mem) > since:
                    fresh += 1
            if fresh < INDUCE_MIN_NEW:
                return
            if time.time() - float(st.get("last_run") or 0.0) < INDUCE_MIN_GAP_MIN * 60:
                return
            threading.Thread(target=self._induce_once, daemon=True).start()
        except Exception as e:
            log.debug("归纳检查失败: %s", e)

    def _induce_once(self):
        """把最近这些经历归纳成 1~2 条"关于他"、至多 1 条"关于我"的稳定认知。"""
        try:
            items = []
            for mem in (self.memory_data.get("events") or []) + (self.memory_data.get("topics") or []):
                c = str(mem.get("content") or "").strip()
                if c:
                    items.append((str(mem.get("created_at") or ""), c))
            if len(items) < 3:
                return
            items.sort(reverse=True)
            recent = items[:INDUCE_RECENT_N]
            prof = self.memory_data.get("profile") or {}
            known_traits = [str(t.get("description") or "") for t in (prof.get("traits") or []) if t.get("description")]
            known_user = [str(n.get("content") or "") for n in (prof.get("user_notes") or [])]
            known_self = [str(n.get("content") or "") for n in (prof.get("notes") or [])]
            _name = self.user_profile.get("call_name", "他")
            _induce_prompt = chr(10).join([
                '你在整理对"%s"的长期认识。下面是最近发生过的一些事。' % _name,
                '请归纳出**稳定的认知**（不是复述事件），只输出 JSON：',
                '{"user_notes": ["关于他的稳定习惯/偏好/忌讳，一条一句，最多 2 条"], "self_notes": ["你自己形成的立场或教训，一条一句，最多 1 条"]}',
                '要求：',
                '- 已经在下面对应列表里说过的、或者没有新东西的，就不要重复输出，给空数组。',
                '- 一句话说清，要有具体内容，别写"他总是"这种空话。',
                '- self_notes 用第一人称"我"写；提到他时用"%s"。' % _name,
                '',
                '已有【关于他】：' + ('；'.join(known_user[-8:]) or '（空）'),
                '已有【我自己】：' + ('；'.join(known_self[-8:]) or '（空）'),
                '已知画像条目：' + ('；'.join(known_traits[-8:]) or '（空）'),
                '',
                '最近的经历：',
                chr(10).join('%d. %s' % (i + 1, c) for i, (_, c) in enumerate(recent)),
            ])
            self._induce_running = True
            resp = self._call_text_model([{"role": "user", "content": _induce_prompt}],
                                         temperature=0.4, max_tokens=DEFAULT_MAX_TOKENS, timeout=30)
            if resp.status_code != 200:
                log.warning("归纳调用失败: HTTP %s", resp.status_code)
                return
            raw = resp.json()["choices"][0]["message"]["content"].strip()
            m = re.search(r"\{.*\}", raw, re.S)
            data = json.loads(m.group(0) if m else raw)
            n_user = n_self = 0
            for c in (data.get("user_notes") or [])[:2]:
                c = str(c or "").strip()
                if len(c) >= 4:
                    self._apply_profile_note(c, "about_user")
                    n_user += 1
            for c in (data.get("self_notes") or [])[:1]:
                c = str(c or "").strip()
                if len(c) >= 4:
                    self._apply_profile_note(c, "self")
                    n_self += 1
            st = self._load_induce_state()
            # 记"处理到哪个时刻"，而不是"当时池子里有几条"
            st["last_run_ts"] = time.time()
            st["last_total"] = len(self.memory_data.get("topics") or []) + len(self.memory_data.get("events") or [])
            st["last_run"] = time.time()
            self._save_induce_state(st)
            log.info("归纳完成：关于他 %d 条 / 关于我 %d 条（看了 %d 条经历）", n_user, n_self, len(recent))
        except Exception as e:
            log.warning("归纳失败: %s", e)
        finally:
            self._induce_running = False

    # ---------- 上下文构建器 ----------
    def _retention_score(self, mem):
        """长期价值分（10/28）：决定淘汰顺序，也用作召回排序里的基础分。

        = 0.45*importance + 0.30*usage(按 kind 半衰期衰减)
          + 0.20*conf(证据数) + 0.10*starred，observe 再乘 0.6

        与"被注入过"完全无关 —— 旧公式用的是 access_count，而那个值每次注入都 +1，
        等于模型给自己刷热度（实测中位 24、10 条里 9 条饱和）。
        """
        kind = str(mem.get("kind") or "experience")
        imp = float(mem.get("importance") or 0.5)
        ev = int(mem.get("evidence_count") or 1)
        conf = min(1.0, 0.6 + 0.2 * (ev - 1))
        used = int(mem.get("used_count") or 0)
        hits = int(mem.get("user_hits") or 0)
        # 使用量：**建条目本身算一次**（否则没用过的条目时间对它完全不起作用），
        # 她说过 +1、他提过 +1.5，累计封顶
        usage_raw = min(1.0, (1 + used + 1.5 * hits) / 4.0)
        ref = (mem.get("last_used_at") or mem.get("last_user_hit_at")
               or mem.get("created_at") or "")
        half = KIND_HALF_LIFE_DAYS.get(kind)
        decay = 1.0
        if half and ref:
            try:
                days = max(0, (datetime.now() - datetime.strptime(ref, "%Y-%m-%d %H:%M:%S")).days)
                decay = 0.5 ** (days / half)
            except (ValueError, TypeError):
                decay = 1.0
        score = (0.45 * imp + 0.30 * usage_raw * decay
                 + 0.20 * conf + 0.10 * (1.0 if mem.get("starred") else 0.0))
        if kind == "observe":
            score *= OBSERVE_PENALTY
        return score

    def _score_topic_memory(self, mem):
        """话题分数 = 长期价值分（10/28 起与事件统一）"""
        return self._retention_score(mem)

    def _score_event_memory(self, mem):
        """事件分数 = 长期价值分（10/28 起与话题统一）"""
        return self._retention_score(mem)

    def _format_profile_for_context(self):
        """格式化性格画像为提示词文本：固定清单中已有内容的条目，按最近更新最多取 CONTEXT_TRAITS 条"""
        profile = self.memory_data.get("profile", {})
        out = []
        relation = profile.get("relation") or {}
        rel_content = (relation.get("content") or "").strip()
        if rel_content:
            out.append(f"【关系形象】{rel_content}")
        traits = profile.get("traits", [])
        known = {t.get("trait"): t for t in traits if t.get("trait") in TRAIT_LIST}
        valid = []
        for name in TRAIT_LIST:
            t = known.get(name)
            if t and ((t.get("description") or "").strip() or t.get("evidence")):
                valid.append(t)
        valid.sort(key=lambda t: str(t.get("updated_at", "")), reverse=True)
        lines = []
        for t in valid[:CONTEXT_TRAITS]:
            name = t["trait"]
            desc = (t.get("description") or "").strip()
            evs = [str(e).strip() for e in (t.get("evidence") or []) if str(e).strip()]
            if not desc and evs:
                desc = f"（暂无概括）最近观察：{evs[-1]}"
            elif desc and evs:
                tail = "；".join(f'"{e}"' for e in evs[-CONTEXT_TRAIT_EVIDENCE:])
                desc = f"{desc}（证据：{tail}）"
            lines.append(f"- {name}：{desc}")
        if lines:
            out.append("【你对用户的了解】\n" + "\n".join(lines))
        # 10/28：自我认知层（self / about_user / lesson）—— 每轮都在，永不淘汰
        _self = [n for n in (profile.get("notes") or []) if (n.get("content") or "").strip()]
        _abt = [n for n in (profile.get("user_notes") or []) if (n.get("content") or "").strip()]
        if _self:
            out.append("【你自己认定的事】\n" + "\n".join(
                "- " + str(n.get("content")).strip() for n in _self[:PROFILE_NOTES_MAX]))
        if _abt:
            out.append("【关于他，你知道的】\n" + "\n".join(
                "- " + str(n.get("content")).strip() for n in _abt[:PROFILE_NOTES_MAX]))
        return "\n\n".join(out)

    def _load_memory_embedder(self):
        """懒加载本地中文向量模型（ONNX Runtime，不再依赖 torch），失败时回退到旧排序。

        10/19 改：原来是 sentence_transformers(torch)，光 torch 的 DLL 就 294 MB、
        还预占约 1 GB 提交内存。换成 ONNX 后数值等价（A/B 逐句余弦 1.00000000、
        top-5 排序零变化），启动快、成品也小。
        池化方式必须跟模型自带配置一致：**CLS 池化（取第 0 个 token）+ L2 归一化**
        （models\bge-small-zh-v1.5\1_Pooling\config.json 里 pooling_mode_cls_token=true），
        换成 mean 池化不会报错，但会让所有余弦系统性偏移、0.35 门槛失真。
        """
        if getattr(self, '_memory_embed_failed', False):
            return None
        if getattr(self, '_memory_embedder', None) is not None:
            return self._memory_embedder

        class _OnnxTextEmbedder:
            """最小 ONNX 文本向量器：接口对齐 SentenceTransformer.encode"""

            def __init__(self, model_dir):
                import numpy as np_
                import onnxruntime as ort_
                from tokenizers import Tokenizer
                self._np = np_
                self._tok = Tokenizer.from_file(os.path.join(model_dir, "tokenizer.json"))
                self._tok.enable_truncation(max_length=512)
                self._tok.enable_padding(pad_id=0, pad_token="[PAD]")
                so = ort_.SessionOptions()
                so.intra_op_num_threads = 1                          # 别重蹈 VAD 线程池自旋
                so.add_session_config_entry("session.intra_op.allow_spinning", "0")
                self._sess = ort_.InferenceSession(
                    os.path.join(model_dir, "model.onnx"), sess_options=so,
                    providers=["CPUExecutionProvider"])

            def encode(self, texts, normalize_embeddings=True, **kwargs):
                np_ = self._np
                single = isinstance(texts, str)
                items = [texts] if single else list(texts)
                if not items:
                    return np_.zeros((0, 512), dtype=np_.float32)
                encs = self._tok.encode_batch(items)
                ids = np_.array([e.ids for e in encs], dtype=np_.int64)
                mask = np_.array([e.attention_mask for e in encs], dtype=np_.int64)
                types = np_.zeros_like(ids)
                out = self._sess.run(["last_hidden_state"],
                                     {"input_ids": ids, "attention_mask": mask,
                                      "token_type_ids": types})[0]
                vec = out[:, 0, :].astype(np_.float32)                  # CLS 池化
                if normalize_embeddings:
                    vec = vec / (np_.linalg.norm(vec, axis=1, keepdims=True) + 1e-12)
                return vec[0] if single else vec

        try:
            # 打包版 MEMORY_EMBED_MODEL 是本地目录；源码版它是 HF 仓库名 ⇒ 退回随项目带的目录
            model_dir = MEMORY_EMBED_MODEL
            if not os.path.isdir(model_dir):
                model_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                         "models", "bge-small-zh-v1.5")
            onnx_file = os.path.join(model_dir, "model.onnx")
            if not os.path.isfile(onnx_file):
                raise FileNotFoundError(f"缺少 {onnx_file}（需要 ONNX 版 bge-small）")
            self._memory_embedder = _OnnxTextEmbedder(model_dir)
            log.info(f"记忆向量模型已加载(ONNX): {model_dir}")
        except Exception as e:
            self._memory_embed_failed = True
            log.warning(f"记忆向量模型加载失败，将回退到旧记忆排序: {e}")
            self._memory_embedder = None
        return self._memory_embedder

    def _preload_memory_embedder(self):
        """启动后台预加载向量模型并回填既有记忆向量，不阻塞 UI"""
        try:
            self._load_memory_embedder()
            self._backfill_memory_vectors()
        except Exception as e:
            log.warning(f"记忆向量模型预加载失败: {e}")

    def _memory_vector_of(self, item):
        """取某条记忆的向量：先查缓存，未命中则编码并写入缓存与 memory.db"""
        iid = item.get("id")
        if not iid:
            return None
        v = self._mem_vectors.get(iid)
        if v is not None:
            return v
        # 印象卡正文在 text 里，旧条目在 content 里 —— 两个都认
        _body = item.get("content") or item.get("text") or ""
        v = self._get_text_embedding(_body)
        if v is None:
            return None
        self._mem_vectors[iid] = v
        try:
            _memory_db.set_embedding(iid, v)
        except Exception:
            pass
        return v

    def _backfill_memory_vectors(self):
        """启动时把库里还没有向量的记忆逐条编码并持久化（后台执行一次）"""
        try:
            try:
                self._mem_vectors = _memory_db.load_embeddings()
            except Exception:
                self._mem_vectors = {}
            if self._load_memory_embedder() is None:
                return
            with self._memory_lock:
                items = (list(self.memory_data.get("topics", []))
                         + list(self.memory_data.get("events", [])))
            changed = 0
            for it in items:
                iid = it.get("id")
                if not iid or iid in self._mem_vectors:
                    continue
                v = self._get_text_embedding(it.get("content", ""))
                if v is None:
                    continue
                self._mem_vectors[iid] = v
                try:
                    _memory_db.set_embedding(iid, v)
                    changed += 1
                except Exception:
                    pass
            if changed:
                log.info("向量记忆回填完成: %d 条", changed)
        except Exception as e:
            log.warning("向量记忆回填失败: %s", e)

    def _get_text_embedding(self, text):
        """获取文本向量，失败返回 None"""
        embedder = self._load_memory_embedder()
        if embedder is None:
            return None
        try:
            return embedder.encode(text, normalize_embeddings=True)
        except Exception as e:
            log.warning(f"文本向量化失败: {e}")
            return None


    def _find_similar_memory(self, content, items, threshold):
        """查找与 content 相似/重复的已有记忆。
        先走字符串包含（快速且精确），再走向量相似度。
        """
        # 快速路径：字符串互相包含
        for item in items:
            old_content = item.get("content", "")
            if content in old_content or old_content in content:
                return item
        # 向量路径
        new_vec = self._get_text_embedding(content)
        if new_vec is None:
            return None
        best_item = None
        best_score = threshold
        for item in items:
            old_content = item.get("content", "")
            old_vec = self._memory_vector_of(item)
            if old_vec is None:
                continue
            score = max(0.0, float(np.dot(new_vec, old_vec)))
            if score >= best_score:
                best_score = score
                best_item = item
        return best_item

    def _find_memory_candidates(self, content, items, threshold, top_k=MEMORY_CANDIDATE_MAX):
        """向量粗筛：返回与 content 相似度超过 threshold 的候选记忆，最多 top_k 条"""
        candidates = []
        # 快速路径：字符串包含直接作为高优先级候选
        for item in items:
            old_content = item.get("content", "")
            if content in old_content or old_content in content:
                candidates.append((1.0, item))
        # 向量路径
        new_vec = self._get_text_embedding(content)
        if new_vec is not None:
            for item in items:
                old_content = item.get("content", "")
                old_vec = self._memory_vector_of(item)
                if old_vec is None:
                    continue
                score = max(0.0, float(np.dot(new_vec, old_vec)))
                if score >= threshold:
                    candidates.append((score, item))
        # 去重并按分数排序
        seen = set()
        unique = []
        for score, item in candidates:
            mid = item.get("id")
            if mid is None or mid in seen:
                continue
            seen.add(mid)
            unique.append((score, item))
        unique.sort(key=lambda x: x[0], reverse=True)
        return [item for _, item in unique[:top_k]]

    def _parse_merge_decision(self, text):
        """解析 AI 返回的记忆合并判断结果"""
        try:
            data = json.loads(text)
            if isinstance(data, list):
                return {int(d.get("index", -1)): d for d in data if isinstance(d, dict)}
        except Exception:
            pass
        m = re.search(r'\[.*\]', text, re.DOTALL)
        if m:
            try:
                data = json.loads(m.group(0))
                if isinstance(data, list):
                    return {int(d.get("index", -1)): d for d in data if isinstance(d, dict)}
            except Exception:
                pass
        return None

    def _judge_memory_merge_with_ai(self, items):
        """批量让 AI 判断新记忆应该 merge / new / ignore"""
        if not items:
            return {}
        lines = []
        for idx, item in enumerate(items):
            lines.append(f"[{idx}] 类型: {item['type']}，来源: {item.get('source', 'chat')}")
            lines.append(f"新内容: {item['content']}")
            for cand in item.get("candidates", []):
                date_s = str(cand.get("created_at", ""))[:10]
                src_s = cand.get("source", "")
                meta_s = f"（{date_s}/{src_s}）" if (date_s or src_s) else ""
                lines.append(f"  候选: {cand['content']} (id: {cand['id']}){meta_s}")
        prompt = f"""你是一个记忆去重判断助手。请判断下面每条新记忆是否应该合并到某个候选记忆。

{chr(10).join(lines)}

请严格输出JSON数组，不要markdown代码块，格式如下：
[
  {{"index": 0, "memory_id": "候选id或null", "action": "merge"}},
  {{"index": 1, "memory_id": null, "action": "new"}}
]

规则：
- action 只能是 "merge" / "new" / "ignore"
- merge：新内容和某个候选确实是同一件事/同一次经历，且日期、场合、观看状态都一致时，才应该合并
- new：虽然相似但不是同一件事，应该新增
- ignore：内容不值得记录
- 候选行末尾的（日期/来源）请参考：不同日期发生的两次活动不要合并；同一内容但状态不同（如一次是用户在看直播/比赛、一次是用户自己在玩游戏）绝对不要合并，判 new
- memory_id 必须是候选列表里出现的 id；如果不合并则填 null
"""
        try:
            resp = self._call_text_model([{"role": "user", "content": prompt}],
                                         temperature=0.1, max_tokens=DEFAULT_MAX_TOKENS, timeout=30)
            if resp.status_code != 200:
                log.error(f"记忆合并判断API失败: {resp.status_code}")
                return None
            text = resp.json()["choices"][0]["message"]["content"]
            return self._parse_merge_decision(text)
        except Exception as e:
            log.error(f"记忆合并判断异常: {e}")
            return None


    # ---------- 开箱：把一条看法指回具体那次（P3）----------
    def _event_index(self):
        idx = {}
        for kind in ("events", "topics"):
            for m in (self.memory_data.get(kind) or []):
                _i = str(m.get("id") or "")
                if _i:
                    idx[_i] = m
        return idx

    # ---------- 从提取结果入印象（P3：从箱子/对话里长看法）----------
    def _apply_impressions_from_extraction(self, items):
        """把提取出的 impressions 合并进印象卡：去重、限条数、非 core 可被挤掉。"""
        if not items:
            return 0
        added = 0
        today = time.strftime("%m-%d")
        with self._memory_lock:
            imps = self.memory_data.setdefault("impressions", [])
            _exist = [str(i.get("text") or "").strip() for i in imps if not i.get("invalid_at")]
            for row in items[:2]:
                text = str((row or {}).get("text") or "").strip()
                if not (4 <= len(text) <= 60):
                    continue
                # 去重：完全相同 / 互相包含（措辞差一点就算同一条）
                dup = any(text == s or text in s or s in text for s in _exist)
                if dup:
                    continue
                who = str((row or {}).get("who") or "him").strip().lower()
                if who not in ("him", "her", "us"):
                    who = "him"
                level = str((row or {}).get("level") or "").strip().lower()
                if level not in IMPRESSION_LEVEL_WEIGHT:
                    level = "important" if who == "him" else "normal"
                now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                imps.append({
                    "id": uuid.uuid4().hex[:8], "who": who, "text": text, "level": level,
                    "weight": IMPRESSION_LEVEL_WEIGHT[level], "links": [],
                    "evidence_dates": [today], "evidence_count": 1,
                    "used_count": 0, "last_used_at": None,
                    "created_at": now, "updated_at": now,
                    "invalid_at": None, "superseded_by": None,
                    "tension": 0, "tension_dates": [],
                })
                _exist.append(text)
                added += 1
            # 超上限：挤掉有效权重最低的非 core（新条目刚建立，按设计"新条目必留"）
            if len(imps) > MAX_IMPRESSIONS:
                _cores = sum(1 for i in imps if i.get("level") == "core" and not i.get("invalid_at"))
                if _cores > MAX_CORE_IMPRESSIONS:
                    log.warning("core 印象 %d 条，超过上限 %d（需要降级）", _cores, MAX_CORE_IMPRESSIONS)
                while len(imps) > MAX_IMPRESSIONS:
                    cand = [i for i in imps
                            if i.get("level") != "core" and not i.get("invalid_at")
                            and i.get("text") not in _exist[-added:]]
                    if not cand:
                        break
                    cand.sort(key=lambda i: self._impression_weight_eff(i))
                    imps.remove(cand[0])
            if added:
                save_memories(self.memory_data)
                log.info("印象新增 %d 条（共 %d 条）", added, len(imps))
        return added

    # ---------- 改口检查：拿新经历问一次"有没有跟看法冲突"（P3）----------
    def _check_impression_conflicts(self, new_items):
        """提完成功后跑：只问已有的看法有没有被新事实顶掉。

        不塞进提取契约里 —— 提取那套 prompt 已经很长，改它风险大、也不好回滚；
        这里多跑一次小调用（约 ¥0.01），失败了就当没发生。
        """
        try:
            imps = [i for i in (self.memory_data.get("impressions") or [])
                    if not i.get("invalid_at") and not i.get("archived")]
            lines_new = [str(x).strip() for x in (new_items or []) if str(x).strip()]
            if not imps or not lines_new:
                return
            _idx = {str(i.get("id")): i for i in imps}
            prompt = chr(10).join([
                "下面是这个角色对\"他\"已有的几条看法，以及刚刚记录下来的新经历。",
                "请判断：新经历里有没有**与某条看法矛盾**的（不是补充、不是新话题，是直接冲突）。",
                "",
                "已有的看法（id｜内容）：",
                chr(10).join("%s｜%s" % (k, v.get("text")) for k, v in _idx.items()),
                "",
                "新经历：",
                chr(10).join("- " + s[:120] for s in lines_new[:10]),
                "",
                "只输出 JSON，没有冲突就给空数组：",
                '{"conflicts": [{"id": "上面列出的 id", "why": "哪句新经历顶了它（≤20字）", '
                '"new_text": "如果要改写，给一句新的话（≤40字，仍是能被反驳的判断）；不确定就留空"}]}',
            ])
            resp = self._call_text_model([{"role": "user", "content": prompt}],
                                         temperature=0.3, max_tokens=2048, timeout=30)
            if resp.status_code != 200:
                return
            raw = resp.json()["choices"][0]["message"]["content"] or ""
            m = re.search(r"\{.*\}", raw, re.S)
            data = json.loads(m.group(0) if m else raw)
            for row in (data.get("conflicts") or [])[:3]:
                _id = str(row.get("id") or "").strip()
                if _id not in _idx:
                    continue
                tension, ready = self._impression_add_tension(_id, row.get("why") or "")
                new_text = str(row.get("new_text") or "").strip()
                if ready and new_text:
                    self._impression_supersede(_id, new_text)
                elif ready:
                    log.info("改口可执行但模型没给新说法：%s", _idx[_id].get("text", "")[:24])
        except Exception as e:
            log.debug("改口检查失败: %s", e)

    # ---------- 改口：矛盾证据累积到阈值才改写（P3）----------
    def _impression_find(self, imp_id):
        for imp in (self.memory_data.get("impressions") or []):
            if str(imp.get("id")) == str(imp_id):
                return imp
        return None

    def _impression_add_tension(self, imp_id, evidence=""):
        """记一次矛盾（同一天只记一次）。返回 (tension, 是否够格改写)。"""
        imp = self._impression_find(imp_id)
        if imp is None:
            return 0, False
        today = time.strftime("%m-%d")
        dates = list(imp.get("tension_dates") or [])
        if today in dates:
            return int(imp.get("tension") or 0), False   # 同一天不重复计
        dates.append(today)
        imp["tension_dates"] = dates
        imp["tension"] = int(imp.get("tension") or 0) + 1
        ready = (imp["tension"] >= IMPRESSION_TENSION_TO_REWRITE and len(set(dates)) >= 2)
        log.info("改口张力：%s → %d 次（%s）%s", imp.get("text", "")[:24], imp["tension"],
                 "、".join(dates), "，够格改写" if ready else "")
        save_memories(self.memory_data)
        return imp["tension"], ready

    def _impression_supersede(self, old_id, new_text, new_level=None, evidence=""):
        """用一条新看法替换旧的：旧条标 invalid_at + superseded_by，新条独立存在。"""
        old = self._impression_find(old_id)
        if old is None:
            return None
        new_text = str(new_text or "").strip()
        if len(new_text) < 4:
            return None
        new_id = uuid.uuid4().hex[:8]
        now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        rec = {
            "id": new_id,
            "who": old.get("who") or "him",
            "text": new_text,
            "level": new_level or old.get("level") or "normal",
            "weight": IMPRESSION_LEVEL_WEIGHT.get(new_level or old.get("level") or "normal", 1.0),
            "links": list(old.get("links") or []),
            "evidence_dates": sorted(set(list(old.get("evidence_dates") or []) + [time.strftime("%m-%d")])),
            "evidence_count": int(old.get("evidence_count") or 1) + 1,
            "used_count": 0, "last_used_at": None,
            "created_at": now, "updated_at": now,
            "invalid_at": None, "superseded_by": None,
            "tension": 0, "tension_dates": [],
        }
        old["invalid_at"] = now
        old["superseded_by"] = new_id
        with self._memory_lock:
            self.memory_data.setdefault("impressions", []).append(rec)
        save_memories(self.memory_data)
        log.info("改口完成：%s → %s", old.get("text", "")[:20], new_text[:24])
        return rec

    def _open_impression_box(self, imp, limit=None):
        """从这条看法的 links 里取最近一条事件原文，压成 ≤limit 字的一行。"""
        limit = int(limit or IMPRESSION_BOX_MAX_CHARS)
        links = list(imp.get("links") or [])
        if not links:
            return ""
        idx = self._event_index()
        texts = []
        for eid in links:
            m = idx.get(str(eid))
            if m:
                texts.append((str(m.get("created_at") or ""), str(m.get("content") or "")))
        if not texts:
            return ""
        texts.sort(reverse=True)
        day, body = texts[0]
        body = re.sub(r"^陪看记录[:：]\s*", "", body)
        body = re.sub(r"[（(][a-zA-Z_]+[）)]", "", body).strip()
        body = re.sub(r"\s+", " ", body)
        if len(body) > limit:
            body = body[:limit] + "…"
        return "（%s：%s）" % (day[5:10] if len(day) >= 10 else day, body)

    def _impression_wants_box(self, query):
        q = str(query or "")
        return any(w in q for w in IMPRESSION_BOX_WORDS)

    # ---------- 事件箱：对话分箱（P3）----------
    def _box_state(self):
        """箱子状态：{"boxes": [...], "open_box": {...}}，存独立文件，不塞进 memory.db。"""
        st = getattr(self, "_boxes_state", None)
        if isinstance(st, dict):
            return st
        st = {"boxes": [], "open_box": None}
        try:
            raw = load_json_file(BOXES_FILE, {})
            if isinstance(raw, dict):
                st["boxes"] = raw.get("boxes") or []
                st["open_box"] = raw.get("open_box") or None
        except Exception as e:
            log.debug("读箱子失败: %s", e)
        self._boxes_state = st
        return st

    def _box_save(self):
        try:
            save_json_file(BOXES_FILE, self._box_state())
        except Exception as e:
            log.debug("箱子落盘失败: %s", e)

    def _box_open(self):
        """当前未封的箱子（持久化在 memory_boxes.json 里，重启不丢）。"""
        st = self._box_state()
        box = st.get("open_box")
        if not isinstance(box, dict):
            box = {"id": "", "started": time.time(), "turns": [], "last_his_ts": 0.0}
            st["open_box"] = box
        return box

    def _box_maybe_seal(self, now=None, force=False):
        """满 15 轮 / 静默超 3 分钟 → 封箱。force 用于退出前。"""
        now = float(now if now is not None else time.time())
        box = self._box_open()
        turns = box.get("turns") or []
        if not turns:
            return None
        reason = ""
        if force:
            reason = "force"
        elif len(turns) >= BOX_MAX_TURNS:
            reason = "cap"
        elif box.get("last_his_ts") and (now - float(box["last_his_ts"])) > BOX_IDLE_SECONDS:
            reason = "idle"
        if not reason:
            return None
        return self._box_seal(reason)

    def _box_seal(self, reason="idle"):
        st = self._box_state()
        box = self._box_open()
        turns = box.get("turns") or []
        if not turns:
            st["open_box"] = None
            return None
        _first = str(turns[0].get("u") or "")[:20].replace(chr(10), " ")
        rec = {
            "id": uuid.uuid4().hex[:8],
            "started": box.get("started"),
            "ended": time.time(),
            "turns": turns,
            "split": 1 if reason == "cap" else 0,
            "index": "%s（%d 轮）" % (_first or "…", len(turns)),
        }
        st["boxes"].append(rec)
        if len(st["boxes"]) > BOX_KEEP:
            del st["boxes"][:len(st["boxes"]) - BOX_KEEP]
        st["open_box"] = None
        self._box_save()
        log.info("封箱（%s）：%d 轮 / %s", reason, len(turns), rec["index"])
        return rec

    def _box_note_turn(self, user_msg, ai_reply, source="chat"):
        """记一轮进当前箱；陪看/陪读不进箱。只有他的消息（chat）刷新静默计时。"""
        if source not in ("chat", "topic_open"):
            return
        box = self._box_open()
        box.setdefault("turns", []).append(
            {"u": str(user_msg or ""), "a": str(ai_reply or ""),
             "src": source, "ts": time.time()})
        if source == "chat":
            box["last_his_ts"] = time.time()
        self._box_save()

    @staticmethod
    def _impression_lexical_hits(query, text):
        """查询与这条看法共享了几个"实字"（去停用字）。

        为什么用字而不是词：实测 bge 对无关句也给到 0.46~
        0.50（"你在想什么呀" ↔ "他常哼歌" 0.503），而真正相关的
        "听首歌吧" ↔ "他常哼歌" 也只有 0.524 —— 语义分不开这两类。
        但"歌"这个字在后者里出现、在前者里没有，所以拿**共享实字**
        当闸门，语义分只负责排序。
        """
        def _chars(s):
            s = re.sub(r"[^一-鿿]+", "", str(s or ""))
            return {ch for ch in s if ch not in IMPRESSION_STOP_CHARS}
        try:
            return len(_chars(query) & _chars(text))
        except Exception:
            return 0

    def _select_and_format_impressions(self, query="", dry_run=False, count_mention=False):
        """v2 注入：0~2 条看法，带分层标记；没有够相关的就一条都不给。"""
        with self._memory_lock:
            imps = [i for i in (self.memory_data.get("impressions") or [])
                    if not i.get("invalid_at") and not i.get("archived")]
            self._last_recall = []
            if not imps:
                return ""
            self._impression_ensure_defaults()

            query = (query or "").strip()
            query_vec = self._get_text_embedding(query) if query else None
            now = time.time()

            scored = []
            for imp in imps:
                rel = 0.0
                if query_vec is not None:
                    vec = self._memory_vector_of(imp)
                    if vec is not None:
                        rel = max(0.0, float(np.dot(query_vec, vec)))
                else:
                    rel = 1.0
                eff = self._impression_weight_eff(imp, now)
                mentioned = bool(IMPRESSION_FORCE_MENTION and query and
                                 _mem_mentions(query, str(imp.get("text") or "")))
                hits = self._impression_lexical_hits(query, str(imp.get("text") or ""))
                if mentioned:
                    rel = max(rel, 0.99)
                elif query_vec is not None:
                    # 双条件：语义够近 且 字面有共同实词。
                    # 实测 bge 对无关句也能给到 0.46（"你在想什么呀" ↔ "他常哼歌" 0.503），
                    # 只靠阈值必然误配；而真正相关的句子（"翻箱子"）字面一定重合。
                    if rel < IMPRESSION_REL_MIN:
                        continue
                    if IMPRESSION_KEYWORD_ONLY and hits < 1:
                        continue
                skip = str(imp.get("id") or "") in (getattr(self, "_impression_recent_ids", None) or [])
                if skip and not mentioned:
                    continue
                scored.append((rel * eff, rel, imp, mentioned))
            scored.sort(key=lambda x: x[0], reverse=True)
            picked = scored[:IMPRESSION_INJECT_MAX]
            if not picked:
                return ""

            self._last_recall = [
                {"id": str(imp.get("id") or ""), "content": str(imp.get("text") or ""),
                 "rel": float(rel), "kind": "看法", "created_at": str(imp.get("created_at") or "")[:10]}
                for _sc, rel, imp, _m in picked
            ]
            if not dry_run:
                stamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                for _sc, _rel, imp, _m in picked:
                    imp["last_injected_at"] = stamp
                save_memories(self.memory_data)

            _tag = {"core": "核心", "important": "重要", "normal": ""}
            lines = []
            for _sc, _rel, imp, _m in picked:
                lv = _tag.get(str(imp.get("level") or "normal"), "")
                prefix = "- [%s] " % lv if lv else "- "
                lines.append(prefix + str(imp.get("text") or "").strip())
            if self._impression_wants_box(query):
                for _sc, _rel, imp, _m in picked[:IMPRESSION_BOX_MAX]:
                    detail = self._open_impression_box(imp)
                    if detail:
                        lines.append("- 具体那次" + detail)
                        log.info("开箱：印象 %s → %s", imp.get("id"), detail[:40])
                        break
            return "【你记得的事】" + chr(10) + chr(10).join(lines)

    def _select_and_format_memories(self, query="", dry_run=False, count_mention=False, legacy=None):
        """选择并格式化要注入的记忆。

        v2（11/14 起默认）：只注入 0~2 条"看法"（impressions），按 相关性×有效权重 排序；
        旧的 topics/events 池不再进上下文（它们降级成事件箱/素材）。
        legacy=True 可临时回到旧路径，仅用于 A/B 对比。
        """
        if legacy is None:
            legacy = not MEMORY_V2_ENABLED
        if not legacy:
            return self._select_and_format_impressions(query, dry_run, count_mention)
        with self._memory_lock:
            topics = [t for t in self.memory_data.get("topics", []) if not t.get("archived", False)]
            events = [e for e in self.memory_data.get("events", []) if not e.get("archived", False)]

            query = (query or "").strip()
            self._last_recall = []
            query_vec = self._get_text_embedding(query) if query else None

            if query_vec is not None:
                best_rel = 0.0

                def _rank(items, scorer):
                    nonlocal best_rel
                    scored = []
                    for mem in items:
                        base_score = scorer(mem)
                        content_vec = self._memory_vector_of(mem)
                        relevance = 0.0
                        if content_vec is not None:
                            relevance = max(0.0, float(np.dot(query_vec, content_vec)))
                            if relevance > best_rel:
                                best_rel = relevance
                        final_score = 0.85 * relevance + 0.15 * base_score
                        scored.append((final_score, relevance, mem))
                    scored.sort(key=lambda x: x[0], reverse=True)
                    return scored

                ranked_topics = _rank(topics, self._score_topic_memory)
                ranked_events = _rank(events, self._score_event_memory)
                # 相关性门槛：本轮话题与所有旧记忆都不够相关 → 不注入旧记忆
                if best_rel < MEMORY_RELEVANCE_THRESHOLD:
                    return ""
            else:
                ranked_topics = [(0.0, 0.0, m) for m in
                                 sorted(topics, key=self._score_topic_memory, reverse=True)]
                ranked_events = [(0.0, 0.0, m) for m in
                                 sorted(events, key=self._score_event_memory, reverse=True)]
            # 排序完成

            # 10/28：两个池按一个池选 —— 合起来排序，条数与字数双预算，不再各给 5 个名额
            _pool = ([(sc, rel, m, "话题") for sc, rel, m in ranked_topics]
                     + [(sc, rel, m, "经历") for sc, rel, m in ranked_events])
            _pool.sort(key=lambda x: x[0], reverse=True)
            _picked = []
            _chars = 0
            for _sc, _rel, _m, _kd in _pool:
                if len(_picked) >= MEMORY_INJECT_MAX:
                    break
                # 10/28：逐条地板 —— 低于门槛的不进（以前只看 best_rel，一条擦线就能带一串无关的进来）
                if query_vec is not None and _rel < MEMORY_RELEVANCE_THRESHOLD:
                    continue
                _n = len(str(_m.get("content") or ""))
                if _picked and _chars + _n > MEMORY_INJECT_CHARS:
                    break
                _picked.append((_m, _kd, _rel))
                _chars += _n
            selected_topics = [m for m, kd, _ in _picked if kd == "话题"]
            selected_events = [m for m, kd, _ in _picked if kd == "经历"]
            self._last_recall = [
                {"id": str(m.get("id") or ""), "content": str(m.get("content") or ""),
                 "rel": float(rel), "kind": kd,
                 "created_at": str(m.get("created_at") or "")[:10]}
                for m, kd, rel in _picked
            ]

            # 10/28：**他主动提及**用字面命中判定（向量对短线索不可靠），命中就强制注入 +
            # user_hits+1；仅仅"被注入"不再加热度（旧 access_count 已饱和，只留 last_injected_at 供诊断）。
            _mentioned = []
            if count_mention and query:
                for _m in list(topics) + list(events):
                    if _mem_mentions(query, _m.get("content", "")):
                        _mentioned.append(_m)
                _mentioned = _mentioned[:3]

            if not dry_run:
                now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                for t in selected_topics:
                    t["last_injected_at"] = now
                for e in selected_events:
                    e["last_injected_at"] = now
                for _m in _mentioned:
                    _m["user_hits"] = _m.get("user_hits", 0) + 1
                    _m["last_user_hit_at"] = now
                    _m["last_injected_at"] = now
                if selected_topics or selected_events or _mentioned:
                    save_memories(self.memory_data)

            if _mentioned:
                # 他提起的事必须出现在上下文里（"我明明说了你还不知道"是最难接受的失败）
                _mt = [m for m in _mentioned if m in topics and m not in selected_topics]
                _me = [m for m in _mentioned if m in events and m not in selected_events]
                selected_topics = _mt + selected_topics
                selected_events = _me + selected_events
                # 超出条数上限时从尾部砍（被提及的排在最前，天然保留）
                # 提及进来的条目也要算字数；超预算就从尾部砍（被提及的排在最前，天然保留）
                def _total_chars():
                    return sum(len(str(x.get("content") or ""))
                               for x in (selected_topics + selected_events))
                while (len(selected_topics) + len(selected_events) > MEMORY_INJECT_MAX + 3
                       or _total_chars() > MEMORY_INJECT_CHARS):
                    if selected_events and selected_events[-1] not in _me:
                        selected_events.pop()
                    elif selected_topics and selected_topics[-1] not in _mt:
                        selected_topics.pop()
                    else:
                        break
                _have = {str(r.get("id") or "") for r in self._last_recall}
                for _m in reversed(_mentioned):
                    _mid = str(_m.get("id") or "")
                    if _mid in _have:
                        # 已经通过正常排序进来了，别再插一条（否则诊断里同一条算两次）
                        for _r in self._last_recall:
                            if str(_r.get("id") or "") == _mid:
                                _r["rel"] = max(float(_r.get("rel") or 0), 0.99)
                                _r["kind"] = _r.get("kind") or ("话题" if _m in topics else "经历")
                        continue
                    self._last_recall.insert(0, {
                        "id": _mid, "content": str(_m.get("content") or ""),
                        "rel": 1.0, "kind": "话题" if _m in topics else "经历",
                        "created_at": str(_m.get("created_at") or "")[:10]})
                    _have.add(_mid)

            if not selected_topics and not selected_events:
                return ""

            def _dated(mem):
                # 每条前缀"当时记下的日期"：她才能把"昨天/上周"跟具体某条对上
                ds = str(mem.get("created_at", ""))[:10]
                return f"({ds}) " if ds else ""

            lines = []
            for t in selected_topics:
                lines.append(f"- [话题] {_dated(t)}{t['content']}")
            for e in selected_events:
                lines.append(f"- [经历] {_dated(e)}{e['content']}")
            return "【你记得的事情】（括号里是当时记下的日期）\n" + "\n".join(lines)

    def _history_time_label(self, ts):
        """历史消息的时间前缀：今天/昨天/M月D日 + 时:分（让她自己从记录里看出间隔）。"""
        try:
            d = datetime.fromtimestamp(ts)
        except Exception:
            return ""
        hhmm = d.strftime("%H:%M")
        days = (datetime.now().date() - d.date()).days
        if days == 0:
            return "今天 " + hhmm
        if days == 1:
            return "昨天 " + hhmm
        if days < 365:
            return "%d月%d日 %s" % (d.month, d.day, hhmm)
        return d.strftime("%Y-%m-%d %H:%M")

    def build_context_messages(self, system_prompt, user_msg="", context_type="chat",
                               image_b64=None, extra_context="", memory_query=None,
                               skip_sources=None, image_b64_prev=None, image_b64_earlier=None):
        """统一的AI上下文字消息构建器"""
        time_period = self.get_current_time_period()
        energy_mood = self.get_energy_mood()
        if time.time() < self.sleep_cooldown_until:
            anti_sleep = " 你刚刚睡醒不久，精力充沛，即使当前是深夜也绝对不要提到困倦、想睡觉，要保持清醒和活泼的语气。"
        else:
            anti_sleep = ""

        _now = datetime.now()
        _date_line = (f"现在已经是{time_period}了（今天是 {_now.strftime('%Y-%m-%d')}，"
                      f"周{'一二三四五六日'[_now.weekday()]}）。“昨天”“前天”这类说法只在跟"
                      "记忆或聊天记录里的时间对得上时才用；对不上或者没写清楚，就说记不清了，别猜。")
        system_content = f"{system_prompt}\n\n{_date_line}{anti_sleep}\n{energy_mood}"
        _sleep_line = self._sleep_context_line()
        if _sleep_line:
            system_content += "\n" + _sleep_line

        profile_text = self._format_profile_for_context()
        if profile_text:
            system_content += f"\n\n{profile_text}"

        if memory_query is None:
            memory_query = user_msg if context_type == "chat" else ""
        memory_text = self._select_and_format_memories(query=memory_query,
                                                       count_mention=(context_type == "chat"))
        if memory_text:
            system_content += f"\n\n{memory_text}"

        if extra_context:
            system_content += f"\n\n{extra_context}"

        messages = [{"role": "system", "content": system_content}]

        with self._memory_lock:
            turns = list(self.chat_buffer)
        _topic_kept = 0
        for turn in turns:
            # 陪玩/读书这类"自说自话"的历史可整轮跳过：否则模型会照着自己上一条的句式接着写
            if skip_sources and turn[0].get("source") in skip_sources:
                continue
            if turn[0].get("display_only"):
                # 她主动开的话题：像 QQ 里她先发了一条——只把"她那句"放进上下文。
                # （user 那条是空的，空 content 不能进 API；不带情绪括号，历史里本来就是正文）
                _pick = str(turn[1].get("content") or "").strip()
                if _pick and _topic_kept < 3:      # 最多带 3 条，免得她反复捡旧话题
                    messages.append({"role": "assistant", "content": _pick})
                    _topic_kept += 1
                continue
            # 只传 role/content，剔除本地 source 标记
            _ts = turn[0].get("ts")
            _pre = ("[%s] " % self._history_time_label(_ts)) if _ts else ""
            messages.append({"role": turn[0]["role"], "content": _pre + turn[0]["content"]})
            # 她的历史回复不加前缀：模型会模仿它、在自己的回复开头也写一个时间
            messages.append({"role": turn[1]["role"], "content": turn[1]["content"]})

        if image_b64:
            _content = [{"type": "text", "text": user_msg}]
            # 顺序很重要：更早的 → 约一秒前 → 现在。模型按时间顺序理解。
            for _b in list(image_b64_earlier or []):
                _content.append({"type": "image_url",
                                 "image_url": {"url": f"data:image/jpeg;base64,{_b}"}})
            if image_b64_prev:
                _content.append({"type": "image_url",
                                 "image_url": {"url": f"data:image/jpeg;base64,{image_b64_prev}"}})
            _content.append({"type": "image_url",
                             "image_url": {"url": f"data:image/jpeg;base64,{image_b64}"}})
            messages.append({"role": "user", "content": _content})
        elif user_msg:
            current_time_str = datetime.now().strftime("%Y-%m-%d %H:%M")
            time_aware_msg = f"[现在是{time_period}，时间 {current_time_str}] {user_msg}"
            messages.append({"role": "user", "content": time_aware_msg})

        return messages

    # ---------- 日常话题生成器 ----------
    def generate_topic_manual(self):
        if self.sleep_mode:
            self.show_bubble_text("(sleep) Zzz... 等我睡醒再说吧...", "sleep", status=True)
            return
        if self.api_busy:
            self.show_bubble_text("(worried) 等一下，我还在想事情...", "worried", status=True)
            return
        now = time.time()
        if now - self.last_topic_time < 30:
            self.show_bubble_text("(shy) 我们刚聊过这个话题呢，再想想别的吧~", "shy", status=True)
            return
        self.last_topic_time = now
        self._fetch_topic()

    @staticmethod
    def _clean_topic_option(raw):
        s = str(raw or "").strip()
        s = s.strip(chr(34) + chr(39) + "「」“”")
        s = s.replace("选项A", "").replace("选项B", "").strip()
        return s[:12]

    def _option_is_her_voice(self, opt):
        """选项像不像「她说的」：带动作括号/她的名字/她的身体部位 → 判为视角错。"""
        s = str(opt or "")
        if not s:
            return True
        if s.startswith("（") or s.startswith("("):
            return True
        if self.pet_name and self.pet_name in s:
            return True
        for w in ("尾巴", "耳朵", "泡泡", "尾鳍", "深海", "鲸鱼"):
            if w in s:
                return True
        return False

    def _fetch_topic(self):
        def fetch():
            user_name = self.user_profile.get("call_name", "你")

            def topic_dup(a, b):
                """话题文本重复判定：字面包含 或 相似度过高（抓到改写复用）"""
                if not a or not b:
                    return False
                if a == b or a in b or b in a:
                    return True
                try:
                    import difflib
                    return difflib.SequenceMatcher(None, a, b).ratio() >= 0.72
                except Exception:
                    return False

            seen_rejected = []  # 本轮被判定重复的话题，回喂给模型避开

            # —— 性格画像：缺什么就去聊什么（11/05 并进素材块，不再当"额外目标"）——
            _unknown_traits = []
            try:
                _traits_all = (self.memory_data.get("profile", {}) or {}).get("traits") or []
                _known_map = {t.get("trait"): t for t in _traits_all if isinstance(t, dict)}
                for _n in TRAIT_LIST:
                    if _n == "其他":
                        continue
                    _t = _known_map.get(_n)
                    if _t is None or (not str(_t.get("description") or "").strip()
                                      and not _t.get("evidence")):
                        _unknown_traits.append(_n)
            except Exception:
                _unknown_traits = []
            _probe_trait = ""
            _probe_p = _topic_probe_chance(len(_unknown_traits))
            if _unknown_traits and random.random() < _probe_p:
                _cand = _unknown_traits
                _lastp = getattr(self, "_last_topic_probe", None)
                if _lastp in _cand and len(_cand) > 1:
                    _cand = [_n for _n in _cand if _n != _lastp]
                _probe_trait = random.choice(_cand)
                self._last_topic_probe = _probe_trait

            # 11/05：素材改成"你俩之间真发生过的事"——原来喂的是陪看事件总结
            # （"老大在仓库反复比价…我吐槽像挑白菜"），拿它当话题只会变成复述你今天干了啥。
            _mat_lines = []
            try:
                _said = [x for x in load_recent_said(limit=3) if not x.startswith("（")]
                if not _said:
                    # 旧数据兜底：从聊天缓冲里找他最近说的话（多数轮次是陪看，可能为空）
                    for _turn in reversed(getattr(self, "chat_buffer", []) or []):
                        if not _turn or not isinstance(_turn, list):
                            continue
                        _u = _turn[0] if isinstance(_turn[0], dict) else {}
                        if _u.get("source") != "chat":
                            continue
                        _t = str(_u.get("content") or "").strip()
                        _t = re.sub(r"^（关于话题[:：].*?）回应[:：]", "", _t).strip()
                        if 4 <= len(_t) <= 60 and _t not in _said:
                            _said.append(_t)
                        if len(_said) >= 3:
                            break
                _unotes = []
                for _n in ((self.memory_data.get("profile") or {}).get("user_notes") or []):
                    _c = str(_n.get("content") or "").strip() if isinstance(_n, dict) else ""
                    if 6 <= len(_c) <= 60:
                        _unotes.append(_c)
                random.shuffle(_unotes)
                _mat_lines = _said + _unotes[:2]
            except Exception as _me:
                log.debug("话题素材整理跳过: %s", _me)
                _mat_lines = []
            if _mat_lines:
                material_block = ("你俩最近真有过的事（顺手提起一件最自然，不用逐条交代）："
                                  + chr(10) + chr(10).join("- " + x for x in _mat_lines))
            else:
                material_block = "（最近没什么特别的事，按你自己的想法找话题）"

            # 11/05：素材主要来自「性格画像」——话题该围绕"他是个什么样的人"，
            # 而不是复述他今天干了什么；旧事（经历记忆）只当低概率彩蛋。
            _trait_lines = []
            try:
                _traits = [t for t in ((self.memory_data.get("profile") or {}).get("traits") or [])
                           if isinstance(t, dict) and str(t.get("description") or "").strip()]
                random.shuffle(_traits)
                _traits.sort(key=lambda t: -len(t.get("evidence") or []))
                _last_trait = getattr(self, "_last_topic_trait", None)
                _picked_traits = []
                for t in _traits:
                    if t.get("trait") == _last_trait and len(_traits) > 1:
                        continue
                    _picked_traits.append(t)
                    if len(_picked_traits) >= TOPIC_TRAITS_PICK:
                        break
                if _picked_traits:
                    self._last_topic_trait = _picked_traits[0].get("trait")
                _trait_lines = ["- " + str(t.get("trait") or "他") + "：" + str(t.get("description") or "").strip()
                                for t in _picked_traits]
            except Exception as _te:
                log.debug("话题画像取材跳过: %s", _te)
                _trait_lines = []
            if _probe_trait and _trait_lines:
                # 还有没采集到的类目 ⇒ 这轮就聊它（比拿已知画像闲聊更有价值）
                material_block = (
                    "你还没了解到他「%s」这方面——这轮就从这儿聊起：说说你自己的相关小事，"
                    "或者轻声问一句，都行；聊着不自然就当普通闲聊。" % _probe_trait
                    + chr(10) * 2 + "（你已知的他，供参照，不必都用上）：" + chr(10)
                    + chr(10).join(_trait_lines[:2]))
            elif _probe_trait:
                material_block = ("你还没了解到他「%s」这方面——这轮就从这儿聊起：说说你自己的相关小事，"
                                  "或者轻声问一句，都行。" % _probe_trait)
            elif _trait_lines:
                material_block = ("你对他的了解（话题可以从这里长出来，说一件就行）："
                                  + chr(10) + chr(10).join(_trait_lines))
            # 旧事彩蛋：低概率才把一条经历记忆塞进来
            try:
                if random.random() < TOPIC_RECALL_CHANCE:
                    _pool = list((self.memory_data.get("topics") or [])) + list((self.memory_data.get("events") or []))
                    _pool = [m for m in _pool if isinstance(m, dict) and str(m.get("content") or "").strip()]
                    if _pool:
                        _m = random.choice(_pool)
                        material_block += (chr(10) * 2 + "（顺口的话，可以想起这件旧事，不想提就当没看见）："
                                           + chr(10) + "- " + str(_m.get("content"))[:60])
            except Exception as _re:
                log.debug("话题旧事彩蛋跳过: %s", _re)

            _start_all = time.time()
            for attempt in range(2):
                _t0 = time.time()
                temp = 1.0 + attempt * 0.1
                recent_list = [str(h) for h in self.topic_history[-10:]]
                recent_txt = "\n".join(f"- {h}" for h in recent_list) or "（还没有聊过话题）"
                # 风格示例：直接从本地话题库抽 3 条（与最近聊过的排重，展示新鲜风格）
                try:
                    ex_pool = [t for t in LOCAL_TOPICS
                               if not any(topic_dup(str(t[0]).format(user_name=user_name), old)
                                          for old in recent_list)]
                    if len(ex_pool) < 3:
                        ex_pool = list(LOCAL_TOPICS)
                    ex_lines = []
                    for t in random.sample(ex_pool, min(3, len(ex_pool))):
                        ex_lines.append(f'   "{str(t[0]).format(user_name=user_name)}|{t[1]}|{t[2]}"')
                    topic_examples = "\n".join(ex_lines)
                except Exception:
                    topic_examples = ""
                prompt = TOPIC_PROMPT.format(pet_name=self.pet_name, user_name=user_name,
                                             recent_topics=recent_txt,
                                             topic_examples=topic_examples,
                                             material_block=material_block)
                if seen_rejected:
                    prompt += ("\n注意：你刚才生成的内容与最近话题重复了（" +
                               "；".join(seen_rejected[-2:]) +
                               "）。请彻底换一个方向和说法，不要再用相同的句式。")
                # （画像采集方向已并入 material_block，不再追加）
                
                with self.api_lock:
                    self.api_busy = True
                try:
                    _sys_topic = "你是%s，%s" % (self.pet_name, self.character_config["persona"])
                    resp = self._call_text_model([{"role":"system","content":_sys_topic}, {"role":"user","content":prompt}], temperature=temp, max_tokens=DEFAULT_MAX_TOKENS, timeout=12)
                    if resp.status_code == 200:
                        reply = resp.json()["choices"][0]["message"]["content"].strip()
                        parts = reply.split("|")
                        if len(parts) >= 3:
                            context = parts[0].strip()
                            opt1 = self._clean_topic_option(parts[1])
                            opt2 = self._clean_topic_option(parts[2])
                            if not opt1 or not opt2 or self._option_is_her_voice(opt1) or self._option_is_her_voice(opt2):
                                log.info("话题选项视角不对（像是她说的）：%s / %s", opt1, opt2)
                                seen_rejected.append(context)
                                continue
                            is_duplicate = any(topic_dup(context, old) for old in self.topic_history[-10:])
                            if not is_duplicate:
                                self.topic_history.append(context)
                                save_topic_history(self.topic_history)
                                log.info(f"话题生成 第{attempt+1}次 成功，耗时 {time.time()-_t0:.1f}s")
                                self._ui(lambda: self.show_event_bubble(context, opt1, opt2))
                                return
                            else:
                                seen_rejected.append(context)
                                log.info(f"话题生成 第{attempt+1}次 重复被拒，耗时 {time.time()-_t0:.1f}s: {context}")
                                continue
                except Exception as e:
                    log.warning(f"话题生成API失败: {e}")
                finally:
                    with self.api_lock:
                        self.api_busy = False
            log.info(f"话题生成 两次均未通过（或失败），总耗时 {time.time()-_start_all:.1f}s，转入本地兜底")
            
            # 本地兜底：与最近话题历史排重后再随机（与 AI 生成共用 topic_history，
            # 避免双轨撞车 / 短时间重复）；全部用尽则放宽为全池
            recent = [str(h) for h in self.topic_history[-10:]]
            pool = []
            for t in LOCAL_TOPICS:
                txt = str(t[0]).format(user_name=user_name)
                if not any(topic_dup(txt, old) for old in recent):
                    pool.append((txt, t[1], t[2]))
            if not pool:
                pool = [(str(t[0]).format(user_name=user_name), t[1], t[2]) for t in LOCAL_TOPICS]
            fb = random.choice(pool)
            self.topic_history.append(fb[0])
            save_topic_history(self.topic_history)
            self._ui(lambda: self.show_event_bubble(fb[0], fb[1], fb[2]))
        
        threading.Thread(target=fetch, daemon=True).start()

    def start_action_timer(self):
        """形象转换：她每隔一段随机时间自己做件事（挤番茄酱、吹泡泡、自拍…）"""
        if self.action_timer_job:
            try:
                self.root.after_cancel(self.action_timer_job)
            except Exception:
                pass
            self.action_timer_job = None
        self._schedule_action()

    def _schedule_action(self):
        if self.sleep_mode or self._shutdown:
            return
        delay = random.randint(ACTION_AUTO_MIN, ACTION_AUTO_MAX)
        self.action_timer_job = self.root.after(int(delay * 1000),
                                                lambda: self.do_action(from_click=False))

    def do_action(self, from_click=True):
        """让她做一件事：随机挑一个自带动作演一遍，演完渲染端自己收回道具、回待机"""
        try:
            if self._shutdown or self.sleep_mode or not (self.spine and self.spine_enabled):
                return
            # 这一套形象没有动作素材（中肥鱼/成年肥鱼：用户拍板动作一个都不做）→
            # 点了不做"做事情"那套，也不弹"她做了个动作：X"的气泡；点击反应交给渲染端的随机表情
            if not LIVE2D_FORMS.get(self.form, {}).get('has_motions'):
                return
            # 点击触发时不播"做事情"动作（脱捕 13 秒太长）——只走渲染端的甩头 + 点击表情
            if from_click and not LIVE2D_FORMS.get(self.form, {}).get('click_action', True):
                self._schedule_action()
                return
            if self.action_timer_job:
                try:
                    self.root.after_cancel(self.action_timer_job)
                except Exception:
                    pass
                self.action_timer_job = None
            # 形态配了 auto_actions：自己找事做 = 随机一个〔词〕动作 + 点击那套随机表情
            _auto = LIVE2D_FORMS.get(self.form, {}).get('auto_actions') or []
            if _auto:
                try:
                    self.spine.enqueue(("click",))
                except Exception:
                    pass
                _pick = random.choice(_auto)
                if _pick == "脱捕":
                    # 这一段走原来 Action 组的完整收尾逻辑（道具/时长），落到下面去播
                    log.info("自己找事做：脱捕（配一次点击表情）")
                else:
                    self._apply_cues([_pick])
                    log.info("自己找事做：%s（配一次点击表情）", _pick)
                    self._schedule_action()
                    return
            # 动作池按形态取（小肥鱼有她自己的三段动作）；形态没配就用鲸鱼娘那套
            _pool = LIVE2D_FORMS.get(self.form, {}).get('action_pool') or ACTION_POOL
            idx, label = random.choice(_pool)
            self.spine.do_action(idx)
            log.info("她做了个动作：%s（%s）", label, "点她触发" if from_click else "自己找事做")
        except Exception:
            pass
        self._schedule_action()

    def _open_form_window(self):
        """「形象」卡片：列四/五套形态，点一下就换（面板快捷入口用）。"""
        win, frame = self._make_card_window("形象", 380, 360)
        cur = getattr(self, "form", None)
        for key in available_forms():
            label = LIVE2D_FORMS.get(key, {}) .get("label", key)
            text = ("✓ " if key == cur else "   ") + label

            def _pick(k=key, w=win):
                try:
                    self.set_form(k)
                except Exception as e:
                    log.debug("换形象失败: %s", e)
                try:
                    w.destroy()          # 独立窗就关掉；嵌在面板里时是无害的空操作
                except Exception:
                    pass

            tk.Button(frame, text=text, anchor="w", relief="flat", bg="#ffffff",
                      activebackground="#f2f4f7", font=(self.font_family, 11),
                      command=_pick).pack(fill=tk.X, pady=2, padx=6)

    def _open_costume_window(self):
        """🎩 装扮：悬浮卡片窗（同 API 设置那种），每个槽位一行、多选一用按钮高亮。**按当前形态显示**"""
        win, frame = self._make_card_window("装扮", 520, 700)
        s = self._dpi_scale
        self._costume_buttons = {}
        _slots, _multi, _required, _default = costume_cfg(self.form)
        if not _slots:
            _label = LIVE2D_FORMS.get(self.form, {}).get('label', self.form)
            tk.Label(frame, text="%s 这套形象没有装扮配件" % _label,
                     font=(self.font_family, 11), fg=TEXT_SUB, bg=DIALOG_BG).pack(anchor='w', pady=(10, 0))
            RoundedButton(frame, text="关闭", command=win.destroy, variant="subtle",
                          width=int(110 * s), height=int(36 * s), radius=int(10 * s),
                          font=(self.font_family, 11)).pack(pady=(14, 0))
            return
        for slot, slot_label, clear_label, items in _slots:
            tk.Label(frame, text=slot_label, font=(self.font_family, 11, "bold"), fg=TEXT_MAIN,
                     bg=DIALOG_BG).pack(anchor='w', pady=(8, 2))
            row = None
            # 一排最多 6 个按钮，超了自动换行（"手持道具"有 12 个按钮，一行放不下会被窗口右边界裁掉）
            # 必须有的槽位不给"无"按钮（手持道具：她总得有件拿的东西）
            _opts = ([] if slot in _required else [(None, clear_label)]) + items
            _pad = int(6 * s)
            _budget = int(470 * s)          # 卡片可用宽度（窗口 520 减两侧边距）
            row = tk.Frame(frame, bg=DIALOG_BG)
            row.pack(anchor='w')
            _x = 0
            for name, item_label in _opts:
                _w = int(min(160, max(74, 16 * len(str(item_label)) + 26)) * s)
                if _x and _x + _w > _budget:
                    row = tk.Frame(frame, bg=DIALOG_BG)
                    row.pack(anchor='w')
                    _x = 0
                btn = RoundedButton(row, text=item_label, width=_w, height=int(30 * s),
                                    radius=int(8 * s), font=(self.font_family, 10), variant="subtle",
                                    command=lambda sl=slot, n=name: self.set_costume(sl, n))
                btn.pack(side=tk.LEFT, padx=(0, _pad), pady=(0, 4))
                _x += _w + _pad
                self._costume_buttons[(slot, str(name))] = btn
        tip = tk.Label(frame, text=("每个槽位只能选一个（「桌面显示」可以多选并存），选新的会自动摘掉旧的"
                                    if _multi else "每个槽位只能选一个，选新的会自动摘掉旧的"),
                       font=(self.font_family, 9), fg=TEXT_SUB, bg=DIALOG_BG)
        tip.pack(anchor='w', pady=(10, 0))
        RoundedButton(frame, text="关闭", command=win.destroy, variant="subtle",
                      width=int(110 * s), height=int(36 * s), radius=int(10 * s),
                      font=(self.font_family, 11)).pack(pady=(10, 0))
        self._refresh_costume_buttons()

    def _apply_saved_costumes(self):
        """渲染器就绪后把上次的装扮穿回去（只调一次；渲染线程里执行，set_costume 只是入队）"""
        self._costume_applied = True
        log.info("恢复装扮：形态=%s 存档=%s", self.form, self.costume_choice)
        _slots, _multi, _required, _default = costume_cfg(self.form)
        if not _slots or not LIVE2D_FORMS.get(self.form, {}).get('has_costumes'):
            return      # 中肥鱼/成年肥鱼没有装扮配件
        _dropped = False
        for slot, _label, _clear, _items in _slots:
            val = self.costume_choice.get(slot)
            if not val:
                continue
            # 存档里的选项必须在这个形态里真实存在（形态间槽位同名，比如都有 body）
            _ok = True
            for _nm in (val if isinstance(val, (list, tuple)) else [val]):
                _info = LIVE2D_FORMS.get(self.form) or {}
                _p = os.path.join(os.path.dirname(os.path.abspath(__file__)), "live2d_viewer",
                                  _info.get("dir", ""), "expressions", str(_nm) + ".exp3.json")
                if not os.path.isfile(_p):
                    _ok = False
                    break
            if not _ok:
                log.info("装扮：%s → %s 在当前形态不存在，跳过", slot, val)
                self.costume_choice.pop(slot, None)
                _dropped = True
                continue
            try:
                self.spine.set_costume(slot, val)
                log.info("装扮：%s → %s（启动恢复）", slot, val)
            except Exception as e:
                log.warning("恢复装扮失败 %s: %s", slot, e)
        if _dropped:
            # 摘掉了当前形态不存在的选项 ⇒ 提示词里的「此刻」要重算，别还写着她没穿的东西
            try:
                self._refresh_prompt_for_form(self.form)
            except Exception as e:
                log.debug("恢复装扮后重建提示词失败: %s", e)

    def _refresh_costume_buttons(self):
        for (slot, key), btn in self._costume_buttons.items():
            chosen = self.costume_choice.get(slot)
            if is_multi_slot(slot):
                # 多选槽位：选中的都亮；"清空"按钮在什么都没选时亮
                picked = list(chosen or [])
                same = (key == "None") if not picked else (key in picked)
            else:
                same = (key == str(chosen))
            try:
                btn.set_variant("primary" if same else "subtle")
            except Exception:
                pass

    def set_costume(self, slot, name):
        """装扮配件：单选槽位互斥（None = 摘掉）；「桌面显示」可多选并存（再点一下移出）"""
        chosen = _costume_toggle(self.costume_choice, slot, name)
        self.costume_choice[slot] = chosen
        try:
            if self.spine and self.spine_enabled:
                # 必须发"算好的新值"：多选槽位这里是列表，只发被点的那一个名字，
                # 渲染端会把它当成该槽位的全部内容、顺手摘掉同槽其它件
                # （现象就是"点一个换一个"，而不是并存）
                self.spine.set_costume(slot, chosen)
        except Exception:
            pass
        log.info("装扮：%s → %s", slot, chosen if chosen else "无")
        self._stash_costumes(getattr(self, "form", None))
        _sec = {k: v for k, v in (getattr(self, "_costume_by_form", {}) or {}).items() if v}
        _update_section("costume", _sec)
        self._refresh_costume_buttons()
        try:
            self._refresh_prompt_for_form(self.form)   # 「此刻」那行要跟着变
        except Exception:
            pass

    def start_topic_timer(self):
        """11/01：主动话题不再按"固定/随机间隔"，改成令牌桶 + 时段权重（频率内置，不可调）。"""
        if self.topic_timer_job:
            self.root.after_cancel(self.topic_timer_job)
        self._topic_load_state()
        self._schedule_topic()

    def _schedule_topic(self):
        self.topic_timer_job = self.root.after(int(TOPIC_TICK_SECONDS * 1000), self._topic_timer_trigger)

    def _topic_timer_trigger(self):
        try:
            self._topic_bucket_tick()
        except Exception as e:
            log.warning("话题额度结算失败: %s", e)
        self._schedule_topic()

    # ---------- 主动话题的额度（令牌桶）----------
    def _topic_state_path(self):
        return os.path.join(CONFIG_DIR, "topic_bucket.json")

    def _topic_load_state(self):
        """读回最近 24 小时的开口时间：{emits: [ts...], last_tick}。

        11/01：上限从"自然日"改成**滑动 24 小时**——否则 23:50 说一句、00:10 又说一句，
        跨零点直接连发。
        """
        st = {"emits": [], "last_tick": time.time()}
        try:
            raw = json.load(open(self._topic_state_path(), encoding="utf-8"))
            if isinstance(raw, dict):
                if isinstance(raw.get("emits"), list):
                    st["emits"] = [float(x) for x in raw["emits"] if isinstance(x, (int, float))]
                elif raw.get("count"):
                    # 旧版只有 count，没有时间戳 —— 补成一串"刚刚"之前的时间，近似保留配额
                    n = int(raw.get("count") or 0)
                    st["emits"] = [time.time() - 60 * (i + 1) for i in range(max(0, n))]
                if isinstance(raw.get("last_tick"), (int, float)):
                    st["last_tick"] = float(raw["last_tick"])
        except Exception:
            pass
        cutoff = time.time() - 24 * 3600
        st["emits"] = [t for t in st["emits"] if t >= cutoff]
        self._topic_state = st
        return st

    def _topic_save_state(self):
        try:
            with open(self._topic_state_path(), "w", encoding="utf-8") as f:
                json.dump(self._topic_state, f, ensure_ascii=False)
        except Exception as e:
            log.debug("话题额度状态存盘失败: %s", e)

    def _topic_bucket_tick(self, now=None):
        try:
            self._box_maybe_seal(now=now)   # 11/14：静默 3 分钟就封箱
        except Exception:
            pass
        # 11/14：自我卡「有新东西才写 + 7 天兜底 + 72 小时防抖」
        try:
            _due, _why = self._selfcard_should_refresh()
            if _due:
                log.info("自我卡该重写了：%s", _why)
                threading.Thread(target=self._selfcard_crystallize, daemon=True).start()
        except Exception:
            pass
        """结算一次"这会儿要不要主动开口"。

        到达概率模型：λ = 基准速率 × 当时段权重，本次概率 p = 1 - e^(-λ·dt)；
        三条约束：**滑动 24 小时不超过 PER_DAY**、两次至少隔 MIN_GAP、超过 6 小时没说过则强制一句
        （强制只在 8:00–24:00 生效，避免凌晨把人吵醒）。
        now 可传（测试用）。
        """
        import math
        st = getattr(self, "_topic_state", None) or self._topic_load_state()
        now = time.time() if now is None else float(now)
        # 滑动 24 小时：只保留最近一天的开口记录
        st["emits"] = [float(t) for t in (st.get("emits") or []) if now - float(t) < 24 * 3600]
        used = len(st["emits"])
        # 距上次结算的时长（上限 1 小时，避免停机很久回来概率接近 1）
        _gap_from_tick = now - float(st.get("last_tick") or now)
        fresh_start = _gap_from_tick > 7200          # 进程刚起（>2 小时没 tick）时不要立刻兜底
        dt_h = min(1.0, max(0.0, _gap_from_tick / 3600.0))
        st["last_tick"] = now
        _now_dt = datetime.fromtimestamp(now)
        lam = topic_refill_per_hour() * topic_hour_weight(_now_dt.hour, _now_dt.minute)
        p_now = 1.0 - math.exp(-lam * dt_h)
        last_emit = max(st["emits"]) if st["emits"] else 0.0
        gap_h = (now - last_emit) / 3600.0 if last_emit else 999.0
        gap_min = gap_h * 60.0
        rc = getattr(self, "reading_companion", None)
        reading = bool(getattr(rc, "active", False) or getattr(rc, "running", False))
        can = (used < TOPIC_PROACTIVE_PER_DAY
               and gap_min >= TOPIC_MIN_GAP_MIN
               and not self.sleep_mode
               and not getattr(self, "api_busy", False)
               and not getattr(self, "watch_mode", False)
               and not reading)
        force_floor = (gap_h >= TOPIC_MAX_SILENCE_H and 8 <= _now_dt.hour < 24
                       and not fresh_start)
        if can and (force_floor or random.random() < p_now):
            st["emits"].append(now)
            self._topic_save_state()
            _kind = "瞟一眼" if random.random() < PROACTIVE_GLANCE_RATIO else "找话题"
            log.info("主动开口：近 24 小时第 %d/%d 次（%s，%s，本次概率 %.3f，距上次 %.0f 分钟）",
                     used + 1, TOPIC_PROACTIVE_PER_DAY, _kind,
                     "超时兜底" if force_floor else "概率触发", p_now, gap_min)
            _did = None
            if _kind == "瞟一眼":
                _did = self._auto_glance()
            if not _did:
                self.generate_topic_manual()      # 瞟失败（睡觉/陪看中/没图/空回）就退回找话题
        else:
            self._topic_save_state()
            log.debug("主动话题未触发：p=%.3f 近24h %d/%d 距上次 %.0f 分钟",
                      p_now, used, TOPIC_PROACTIVE_PER_DAY, gap_min)
        return st

    # ---------- 陪看模式（使用 OpenAI 兼容视觉 API）----------
    def toggle_watch_mode(self):
        if self.watch_mode:
            self.watch_mode = False
            self._stop_watch_ring()
            self._stop_audio_meter()
            self._summarize_watch_segment()
            self._finalize_watch_event()
            self._watch_session_anchors = []
            self._watch_segment_buffer = []
            self._current_watch_event_id = None
            if self.watch_job:
                self.root.after_cancel(self.watch_job)
                self.watch_job = None
            # 10/19：陪玩不再改点击穿透状态（穿透只由热键控制）
            if self.spine_enabled and self.spine:
                self.spine.enqueue(('test_motion', 'Action', 1))
            self.root.after(800, lambda: self.set_emotion("normal"))
            self.show_bubble_text("(shy) 下次记得再叫我", "shy", status=True)
            log.info("陪玩模式已关闭")
        else:
            if self.sleep_mode:
                self.stop_sleep_mode(cause="watch")
            if not mss:
                messagebox.showwarning("缺少依赖", "请先安装 mss：\npip install mss")
                return
            if not self.vision_api_key:
                messagebox.showwarning("未配置密钥", "请先右键设置视觉模型 API Key")
                return
            if not self.vision_model:
                messagebox.showwarning("未配置模型", "请先右键设置视觉模型名称（豆包填 endpoint id，其他填模型名）")
                return
            self.watch_mode = True
            self._recall_link_count = 0
            self._watch_comment_count = 0
            self._watch_care_count = 0
            self._watch_segment_start_time = time.time()
            self._start_watch_ring()
            self._start_audio_meter()
            # 10/19：陪玩不再强制穿透（原来一开陪玩角色就点不到了）
            self.watch_trigger_times.clear()
            self.last_watch_comment_time = 0
            self._watch_last_anchor = ""
            self._watch_session_anchors = []
            self._watch_segment_buffer = []
            self._watch_segment_start_time = time.time()
            self._current_watch_event_id = None
            self._rest_cooldown_until = time.time() + 40 * 60
            self.watch_job = None
            self.last_screen_sig = None
            if self.spine_enabled and self.spine:
                self.spine.enqueue(('test_motion', 'Action', 2))
            # 10/19：陪玩不再自动收起输入框（收不收由用户自己用菜单决定）
            self.show_bubble_text("(happy) 我会在后面安静陪着你的", "happy", status=True)
            log.info("陪玩模式已开启")
            self.start_watch_loop()
            self.root.after(500, lambda: self.analyze_and_comment(force=False))
        self._update_watch_menu_label()

    def _update_watch_menu_label(self):
        try:
            label = "🎮 陪玩模式 (停止)" if self.watch_mode else "🎮 陪玩模式 (开始)"
            self.mode_menu.entryconfigure(self.watch_menu_index, label=label)
        except Exception as e:
            log.debug(f"菜单标签更新失败: {e}")



    def _maybe_recall_link(self, comment, recall=None):
        """陪看评论说完后，若本轮真的召回了与画面相关的旧记忆，**强制补一条气泡**说关联。

        用户 10/27："触景生情完全不起效果，一次没见过" —— 根因是提示词精简后没有任何一句
        要求她把召回的记忆说出来（模型有上下文但不会主动提）⇒ 改成事后再补一条，
        条件：召回相关度 ≥ WATCH_RECALL_LINK_MIN、同一条记忆 30 分钟内没提过、
        每 7 条评论才攒 1 次额度、同一条记忆 30 分钟内没提过。模型可输出 null 表示其实没关系。
        """
        try:
            recall = self._last_recall if recall is None else recall
            if not recall or not self.watch_mode:
                return
            # 11/05：先看"距上次想起旧事"够不够久，再掷"彩蛋骰"——想起旧事本来就该稀罕
            _since_last = time.time() - float(getattr(self, "_last_recall_at", 0.0) or 0.0)
            if _since_last < WATCH_RECALL_MIN_GAP:
                return
            if random.random() > WATCH_RECALL_CHANCE:
                log.debug("陪看·想起旧事：本轮没掷中（%.0f%%）", WATCH_RECALL_CHANCE * 100)
                return
            # 10/31：额度按评论数攒 —— 每 WATCH_RECALL_PER_COMMENTS 条评论才允许一次
            _quota = int(getattr(self, "_watch_comment_count", 0)) // max(1, WATCH_RECALL_PER_COMMENTS)
            if WATCH_RECALL_LINK_MAX and self._recall_link_count >= WATCH_RECALL_LINK_MAX:
                return
            if self._recall_link_count >= _quota:
                log.debug("陪看·想起旧事：额度用完了（已弹 %d 条 / 评论 %d 条 ⇒ 额度 %d）",
                          self._recall_link_count, self._watch_comment_count, _quota)
                return
            now = time.time()
            cand = None
            for m in recall:
                if not m.get("content"):
                    continue
                if float(m.get("rel") or 0) < WATCH_RECALL_LINK_MIN:
                    continue
                mid = m.get("id") or ""
                last = self._recall_link_cool.get(mid, 0)
                if now - last < WATCH_RECALL_LINK_COOLDOWN:
                    continue
                if cand is None or float(m.get("rel") or 0) > float(cand.get("rel") or 0):
                    cand = m
            if not cand:
                return
            who = self.user_profile.get("call_name", "你")
            _spot = (getattr(self, "_watch_last_spot", "") or "").strip()
            _scene = ("现在的画面：" + _spot + chr(10)) if _spot else ""
            prompt = "".join([
                f"你刚才陪{who}看屏幕，随口说了这句：「{comment}」", chr(10),
                _scene,
                f'这个画面让你想起以前的一件事：「({cand.get("created_at")}) {cand.get("content")}」', chr(10),
                "如果这两件事真的有关联，就像在**回忆**一样说出来：",
                "用「我记得之前…」「之前那次…」「上次…」这类开头（情绪括号放最前面），",
                "后面接你**现在的想法或评价**（感慨、吐槽、嘱咐都行）。", chr(10),
                "要求：不超过40字；不要只复述那件旧事，要说你的看法；",
                "不要写“我们都是…”“都是被…带跑”“总之…”这种概括总结，那等于什么都没说。", chr(10),
                "开头一个括号里只能放一个情绪词，允许的值：" + emotion_word_list() + "；",
                "如果其实没什么关系、或者你只能说空话，就只输出 null。只输出那一句话，不要解释。",
            ])
            resp = self._call_text_model([{"role": "user", "content": prompt}],
                                         temperature=0.8, max_tokens=DEFAULT_MAX_TOKENS, timeout=20)
            if resp.status_code != 200:
                return
            raw = (resp.json()["choices"][0]["message"]["content"] or "").strip()
            if not raw or raw.lower() in ("null", "none", "（null）"):
                log.info("陪看·想起旧事：模型判断没关系（rel=%.2f），跳过", float(cand.get("rel") or 0))
                return
            emotion, text = self.parse_emotion_from_reply(raw)
            text = _strip_meta_comment(text)
            if not text:
                return
            self._recall_link_cool[cand.get("id") or ""] = now
            self._last_recall_at = time.time()          # 11/05：给"两次之间至少隔 15 分钟"用
            self._recall_link_count += 1
            # 10/28：这才是"她真的用了这条记忆"的信号（注入不算）
            try:
                _mid = str(cand.get("id") or "")
                for _m in list(self.memory_data.get("topics", [])) + list(self.memory_data.get("events", [])):
                    if str(_m.get("id") or "") == _mid:
                        _m["used_count"] = _m.get("used_count", 0) + 1
                        _m["last_used_at"] = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                        with self._memory_lock:
                            save_memories(self.memory_data)
                        break
            except Exception as _e:
                log.debug("used_count 更新失败: %s", _e)
            # 10/27：先等她这一轮评论**念完**再补这句 —— 不然语音会撞 _tts_lock 被跳过（实测「TTS 播放被跳过」），
            # 气泡也会把还没念完的评论顶掉。判据是 0 号声道播完 + TTS 线程放手（不是"开始输出"就计时）；
            # 上限 30 秒够 70 字上限的最慢读法，超时也照弹；念完后再固定停顿 GAP 秒，不再弹性估时长。
            _dl = time.time() + 30
            while time.time() < _dl:
                try:
                    _busy = bool(self._tts_channel is not None and self._tts_channel.get_busy())
                except Exception:
                    _busy = False
                if not _busy and not self._tts_lock.locked():
                    break
                time.sleep(0.2)
            if not self.watch_mode:
                return
            time.sleep(WATCH_RECALL_LINK_GAP)
            log.info("陪看·想起旧事（rel=%.2f, %s）: %s", float(cand.get("rel") or 0), cand.get("kind"), text)
            self._ui(lambda: self.show_bubble_text(text, emotion))
            self._ui(lambda: threading.Thread(target=self._tts_play, args=(text,), daemon=True).start())
            self._ui(lambda: self._add_chat_buffer_turn(
                f"[陪玩中，{datetime.now().strftime('%H:%M')}，想起以前的事]", text, source="watch"))
        except Exception as e:
            log.warning("陪看·想起旧事失败: %s", e)

    def _watch_side_text(self):
        """历史里陪看那一轮的 user 侧文本：时分 + 画面定位标签（没有标签就只写占位）。

        固定字符串连发会让模型以为"情况没变"（同一占位符连着的强信号），所以带上时间；
        spot 只写"在哪/在干嘛"，不复述画面。
        """
        who = self.user_profile.get('call_name', '你')
        ts = datetime.now().strftime('%H:%M')
        spot = (getattr(self, "_watch_last_spot", "") or "").strip()
        return f"[陪玩中，{ts}，画面：{spot}]" if spot else f"[陪玩中，{ts}，{who}在看的画面]"

    def _build_watch_query(self):
        """合并最近几条陪看评论作为记忆召回 query（去掉情绪括号，只取最近 3 条）"""
        def _clean(t):
            return re.sub(r"[（(][^）)]*[）)]", "", t or "").strip()
        if not self._watch_session_anchors:
            return _clean(self._watch_last_anchor)
        picked = [_clean(a) for a in self._watch_session_anchors[-WATCH_QUERY_ANCHORS:]]
        return "；".join([x for x in picked if x])

    def _update_watch_session(self, content_text):
        """更新陪看会话锚点，并累积当前片段"""
        content_text = (content_text or "").strip()
        if not content_text:
            return
        if self._watch_session_anchors and content_text == self._watch_session_anchors[-1]:
            return
        self._watch_session_anchors.append(content_text)
        if len(self._watch_session_anchors) > WATCH_SESSION_MAX:
            self._watch_session_anchors.pop(0)
        self._watch_segment_buffer.append(content_text)
        self._maybe_summarize_watch_segment()

    def _maybe_summarize_watch_segment(self):
        if not self._watch_segment_buffer:
            return
        if time.time() - self._watch_segment_start_time >= WATCH_SEGMENT_SECONDS:
            self._summarize_watch_segment()

    def _enforce_event_length(self, text, max_len=WATCH_EVENT_MAX_LEN):
        """把陪看事件描述压缩到 max_len 字以内：AI 压缩一次（不硬截断）"""
        text = (text or "").strip()
        if len(text) <= max_len:
            return text
        try:
            resp = self._call_text_model([{
                "role": "user",
                "content": f"请将下面的事件描述严格压缩到{max_len}字以内（含标点），保留关键信息（观看内容、观看状态、关键阶段、氛围），直接输出压缩结果，不要解释，不要超过{max_len}字。\n事件：\n{text}"
            }], temperature=0.3, max_tokens=DEFAULT_MAX_TOKENS, timeout=20)
            if resp.status_code == 200:
                compressed = resp.json()["choices"][0]["message"]["content"].strip()
                if compressed and len(compressed) < len(text):
                    text = compressed
        except Exception as e:
            log.warning(f"陪看事件压缩失败: {e}")
        return text

    def _summarize_watch_segment(self):
        if not self._watch_segment_buffer:
            return
        # 10/28：一场陪玩评论数 <= 3 就不留事件 —— 看几分钟、没说几句话的场次
        # 只会产生流水账，直接丢弃（buffer 本来就只在内存里，不落库）
        if self._watch_comment_count <= WATCH_EVENT_MIN_COMMENTS:
            log.info("陪玩评论 %d 条（<=%d），本次不记录事件",
                     self._watch_comment_count, WATCH_EVENT_MIN_COMMENTS)
            self._watch_segment_buffer = []
            return
        segment = list(self._watch_segment_buffer)
        self._watch_segment_buffer = []
        self._watch_segment_start_time = time.time()
        # 11/01：单条评论也走模型总结（不再把原始评论直接当正文），
        # 并且送模型前剥掉情绪括号 —— "(worried) 这句" 里的标签不该进事件正文。
        _seg_lines = []
        for _s in segment:
            _t = re.sub(r"^[（(][^)）]*[)）]\s*", "", str(_s or "").strip())
            if _t:
                _seg_lines.append(_t)
        summary = None
        if _seg_lines:
            prompt = f"""以下是你在陪看时说的几句话（按时间顺序）。请把它们压成一条事件记忆：你们在做什么、你注意到了什么、你当时的反应，100-200字，用第一人称。
片段：
{chr(10).join(_seg_lines)}
直接输出事件描述，不要解释。"""
            try:
                resp = self._call_text_model([{"role": "user", "content": prompt}], temperature=0.3, max_tokens=DEFAULT_MAX_TOKENS, timeout=20)
                if resp.status_code == 200:
                    summary = resp.json()["choices"][0]["message"]["content"].strip()
            except Exception as e:
                log.warning(f"陪看片段总结失败: {e}")
            # 11/01：失败就保持 None —— 不再用「把评论拼起来」兜底，那会把事件越滚越长

        # 10/28：读改写整体进锁；**模型调用留在锁外**（20 秒超时若塞进锁里会把聊天线程堵死）
        target_id = self._current_watch_event_id
        old_content = ""
        if target_id is not None:
            with self._memory_lock:
                for ev in self.memory_data.get("events", []):
                    if ev.get("id") == target_id:
                        old_content = str(ev.get("content") or "")
                        break

        # 11/01：默认"正文不动"（old_content 优先）；只有合并成功才换成 merged_text
        merged = old_content or summary
        if target_id is not None and old_content and summary and old_content.strip() != summary.strip():
            merged = old_content          # 模型失败时保持旧正文，不拼接
            merge_prompt = f"""请将下面两条关于同一次陪看过程的事件描述合并成一条完整事件，不要丢失关键信息，200-300字。
旧事件：{old_content}
新片段总结：{summary}
直接输出合并后的事件描述，不要解释。"""
            try:
                resp = self._call_text_model([{"role": "user", "content": merge_prompt}], temperature=0.3,
                                             max_tokens=DEFAULT_MAX_TOKENS, timeout=20)
                if resp.status_code == 200:
                    merged_text = resp.json()["choices"][0]["message"]["content"].strip()
                    if merged_text:
                        merged = merged_text
            except Exception as e:
                log.warning(f"陪看事件合并失败: {e}")

        now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        with self._memory_lock:
            events = self.memory_data.setdefault("events", [])
            ev = next((x for x in events if x.get("id") == target_id), None) if target_id else None
            if ev is not None:
                # **进锁复读**：模型调用期间被别的线程改过就退化成追加，绝不覆盖别人的写入
                cur = str(ev.get("content") or "")
                # 11/01：别人在模型调用期间写过（cur 变了）就保留别人的；模型没给结果也不动正文
                if merged and merged != cur and (not cur or cur == old_content):
                    ev["content"] = merged
                ev["last_accessed_at"] = now
                ev["importance"] = max(ev.get("importance", 0.5), 0.7)
                ev["evidence_count"] = ev.get("evidence_count", 1) + 1
                save_memories(self.memory_data)
                return
            # 目标不存在（首次 / 被淘汰）→ 新建一条；但模型没给正文就不新建，下一段再试
            if not summary:
                log.info("陪看段总结没拿到正文，本次不新建事件")
                return
            self._current_watch_event_id = None
            new_id = str(uuid.uuid4())[:8]
            events.append({
                "id": new_id,
                "content": summary,
                "created_at": now,
                "last_accessed_at": now,
                "importance": 0.7,
                "source": "watch",
                "access_count": 0,
                "evidence_count": 1,
                "archived": False
            })
            self._current_watch_event_id = new_id
            self._prune_memories("events")
            save_memories(self.memory_data)

    def _finalize_watch_event(self):
        """陪看结束收尾：把整场事件做最后一次整理，确保不超过 WATCH_EVENT_MAX_LEN 字"""
        if self._current_watch_event_id is None:
            return
        target_id = self._current_watch_event_id
        with self._memory_lock:
            content = ""
            for ev in self.memory_data.get("events", []):
                if ev.get("id") == target_id:
                    content = (ev.get("content") or "").strip()
                    break
        if not content:
            return
        final_text = ""
        try:
            resp = self._call_text_model([{
                "role": "user",
                "content": f"请将下面这段陪看事件记录整理成最终版本：保留观看内容、观看状态、关键阶段和氛围，确保总字数不超过{WATCH_EVENT_MAX_LEN}字（含标点），直接输出整理结果，不要解释。{chr(10)}事件：{content}"
            }], temperature=0.3, max_tokens=DEFAULT_MAX_TOKENS, timeout=20)
            if resp.status_code == 200:
                final_text = resp.json()["choices"][0]["message"]["content"].strip()
        except Exception as e:
            log.warning(f"陪看事件收尾失败: {e}")
        with self._memory_lock:
            for ev in self.memory_data.get("events", []):
                if ev.get("id") != target_id:
                    continue
                cur = (ev.get("content") or "").strip()
                # 复读：收尾调用期间内容变了就沿用最新的，别把新片段覆盖掉
                base = final_text if (final_text and (not cur or cur == content)) else (cur or content)
                ev["content"] = self._enforce_event_length(base)
                ev["last_accessed_at"] = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                save_memories(self.memory_data)
                break
            return

    def start_watch_loop(self):
        if self.watch_mode:
            self.analyze_and_comment(force=False)
            # 10/30：判断间隔仍由「最短沉默」派生（原来 /2，现在 /10，夹在 2~6 秒）——
            # 用户把最短沉默调长，判断频率跟着变慢，这条耦合保留。
            poll_sec = max(WATCH_POLL_MIN, min(self.watch_min_interval / WATCH_POLL_DIV, WATCH_POLL_MAX))
            self.watch_job = self.root.after(int(poll_sec * 1000), self.start_watch_loop)

    def _log_watch_motion(self, last_diff, recent, color=None):
        """把环形缓冲的逐帧差值落盘（10/30，**只用于标定 WATCH_SETTLE_MOTION**）。

        写 userdata\watch_motion.jsonl，每 ~15 秒一条：d=最近两张的差，avg/max=最近 10 张的统计。
        文件超过 2 MB 就砍掉前一半 —— 这是诊断数据，不值得无限留着。
        """
        try:
            path = os.path.join(CONFIG_DIR, "watch_motion.jsonl")
            rec = {"at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                   "ts": round(time.time(), 1),
                   "d": round(float(last_diff), 2),
                   "avg": round(sum(recent) / len(recent), 2) if recent else None,
                   "max": round(max(recent), 2) if recent else None}
            # 11/01：色彩指纹（只采集，不参与判定）—— hue=色调构成距离，bri=亮度距离，0~100
            if color:
                for _k in ("hue_far", "bri_far", "hue_near", "bri_near"):
                    rec[_k] = None if color.get(_k) is None else round(float(color[_k]), 1)
            with open(path, "a", encoding="utf-8") as f:
                f.write(json.dumps(rec, ensure_ascii=False) + chr(10))
            try:
                if os.path.getsize(path) > 2 * 1024 * 1024:
                    _ls = open(path, encoding="utf-8").read().splitlines()
                    open(path, "w", encoding="utf-8").write(chr(10).join(_ls[len(_ls) // 2:]) + chr(10))
            except Exception:
                pass
        except Exception as e:
            log.debug("运动量采样写盘失败: %s", e)

    def _start_audio_meter(self):
        """开陪玩时开始听系统声音（画面看 20 秒，声音也听 20 秒）。"""
        if AudioMeter is None:
            log.info("陪看·声音：audio_watch 未加载（缺 soundcard），跳过")
            return
        try:
            _ae = str(self.watch_cfg.get("audio_enabled", 1)).strip().lower()
            if _ae in ("0", "false", "no", "off"):
                log.info("陪看·声音：配置里关掉了（watch.audio_enabled=0）")
                return
        except Exception:
            pass
        try:
            if getattr(self, "audio_meter", None) is None:
                self.audio_meter = AudioMeter()
            ok = self.audio_meter.start()
            if ok:
                log.info("陪看·声音：已开始采集 loopback")
            else:
                log.warning("陪看·声音：采集没起来（%s）", self.audio_meter.error)
        except Exception as e:
            log.warning("陪看·声音：启动失败 %s", e)

    def _stop_audio_meter(self):
        try:
            if getattr(self, "audio_meter", None) is not None:
                self.audio_meter.stop()
                log.info("陪看·声音：已停止采集")
        except Exception as e:
            log.debug("陪看·声音：停止失败 %s", e)

    def _start_watch_ring(self):
        """陪玩开启时调用：起一个后台线程每 WATCH_RING_EVERY 秒抓一张，只留最近 KEEP 张。

        目的：让她能说出"这一段的过程"（这辆车刚还在后面 / 查了一分钟还没线索），
        而不是只有"此刻的一帧"。关陪玩时线程自己退。
        """
        if not hasattr(self, "_watch_ring"):
            self._watch_ring = []
        self._watch_ring.clear()
        self._watch_ring_on = True

        def loop():
            _prev_sig = None
            _motion_recent = []
            _motion_n = 0
            while getattr(self, "_watch_ring_on", False) and self.watch_mode:
                try:
                    b64 = self.capture_screen_base64()
                    if b64:
                        # 11/04：抓帧时就把指纹算掉（挑稳定帧、算 motion 都要用），存进环形
                        try:
                            _sig = self._frame_signature(b64)
                        except Exception:
                            _sig = None
                        self._watch_ring.append((time.time(), b64, _sig))
                        if len(self._watch_ring) > getattr(self, "watch_ring_keep", WATCH_RING_KEEP):
                            del self._watch_ring[:-getattr(self, "watch_ring_keep", WATCH_RING_KEEP)]
                        # 10/30：采样相邻帧差，用来标定 WATCH_SETTLE_MOTION（每 ~15 秒落一条）
                        try:
                            if _prev_sig is not None and _sig is not None:
                                _d = self._frame_diff(_prev_sig, _sig)
                                _motion_recent.append(_d)
                                # 11/04：20 秒累计运动量（先只观测 —— 用来标定"匀速运动也该说话"的阈值）
                                try:
                                    _now_pot = time.time()
                                    _pot_list = getattr(self, "_motion_pot", None)
                                    if _pot_list is None:
                                        _pot_list = self._motion_pot = []
                                    _pot_list.append((_now_pot, _d))
                                    _cut = _now_pot - WATCH_MOTION_POT_WINDOW
                                    while _pot_list and _pot_list[0][0] < _cut:
                                        _pot_list.pop(0)
                                    self._motion_pot_sum = round(sum(x[1] for x in _pot_list), 1)
                                except Exception as _pe:
                                    log.debug("累计运动量统计跳过: %s", _pe)
                                try:
                                    if self._watch_is_spike(_d, _motion_recent):
                                        self._watch_spike_at = time.time()
                                        log.debug("陪看: 画面突变（帧差 %.1f），立刻判断一次", _d)
                                        threading.Thread(target=self.analyze_and_comment,
                                                         daemon=True).start()
                                except Exception as _se:
                                    log.debug("突变检查跳过: %s", _se)
                                del _motion_recent[:-10]
                                _motion_n += 1
                                if _motion_n % 10 == 0:
                                    self._log_watch_motion(_d, _motion_recent,
                                                           color=self._watch_color_pair(b64))
                            _prev_sig = _sig
                        except Exception as _e:
                            log.debug("运动量采样失败: %s", _e)
                except Exception as e:
                    log.debug("陪看环形采集失败: %s", e)
                # 分段睡，关陪玩时能立刻退出
                for _ in range(int(WATCH_RING_EVERY * 10)):
                    if not getattr(self, "_watch_ring_on", False) or not self.watch_mode:
                        return
                    time.sleep(0.1)

        threading.Thread(target=loop, daemon=True).start()
        log.info("陪看环形缓冲已启动（每 %.0f 秒一张，留 %d 张）", WATCH_RING_EVERY, WATCH_RING_KEEP)

    def _stop_watch_ring(self):
        self._watch_ring_on = False

    def _watch_ring_pick(self, n=None):
        """从环里挑 n 张更早的画面（最早 + 均匀分布），返回 b64 列表（旧→新）。

        10/24 试过"按画面变化最大的时刻挑"，被用户否掉（"保持时间先后连贯更重要"）：
        变化大的时刻会挤在一起，时间轴断了，她就说不出"这一段的过程"，只会抓着一下猛说。
        ⇒ 恢复按时间均匀取。要治"重复帧"应另做发图层面的去重，别动取样策略。
        """
        n = WATCH_RING_SEND if n is None else n
        ring = list(getattr(self, "_watch_ring", []) or [])
        if len(ring) < 2 or n <= 0:
            return []
        # 均匀取 n 个下标（跳过最新那张，它和"现在"太近）
        ring = ring[:-1]
        step = max(1, len(ring) // n)
        return [ring[i][1] for i in range(0, len(ring), step)][:n]

    def _watch_ring_pick_aged(self, n=None):
        """同 _watch_ring_pick，但带"多少秒前"（给画面烧时间角标用）。"""
        n = WATCH_RING_SEND if n is None else n
        ring = list(getattr(self, "_watch_ring", []) or [])
        if len(ring) < 2 or n <= 0:
            return []
        ring = ring[:-1]
        now = time.time()
        step = max(1, len(ring) // n)
        return [(b64, max(0.0, now - ts), sig) for ts, b64, sig in ring[::step][:n]]

    def _badge_frame(self, image_b64, label):
        """在截图左上角烧一个"多少秒前"的角标（10/27）：模型现在能分清 5 张图的先后。

        只动像素不动尺寸（仍是 1280×720 / q60）；任何异常都退回原图，绝不让角标拖垮评论。
        """
        try:
            from PIL import ImageDraw, ImageFont
            raw = base64.b64decode(image_b64)
            img = Image.open(io.BytesIO(raw)).convert("RGB")
            d = ImageDraw.Draw(img)
            fs = max(16, int(img.height * 0.034))
            font = None
            for _p in ("C:\Windows\Fonts\msyh.ttc", "C:\Windows\Fonts\msyhbd.ttc",
                       "C:\Windows\Fonts\simhei.ttf"):
                try:
                    font = ImageFont.truetype(_p, fs)
                    break
                except Exception:
                    continue
            if font is None:
                font = ImageFont.load_default()
            tw = int(d.textlength(label, font=font)) + fs // 2
            d.rectangle([0, 0, tw, fs + 10], fill=(255, 226, 60))
            d.text((fs // 4, 3), label, font=font, fill=(0, 0, 0))
            buf = io.BytesIO()
            img.save(buf, format="JPEG", quality=60)
            return base64.b64encode(buf.getvalue()).decode("ascii")
        except Exception as e:
            log.debug(f"画面角标失败（忽略）: {e}")
            return image_b64


    def _compose_frames_grid(self, frames, cols=2, cell_w=None, cell_h=None, label_h=None):
        """把若干历史帧拼成一张网格图（10/29 起）。

        frames = [(b64, 多少秒前), ...]，**旧→新**；每格底下烧一条黑底标签写「-10.5s」。
        为什么这么做：视觉模型按像素收 token，单张 ≥2MP 就封顶 1000；
        5 张 1280×720 要 2926，而「拼图 1920×1080（1000）+ 当前帧 1280×720（578）」= 1579。
        960 宽的格子文字识别率约 95%（640 宽只有 37%，所以近层不能更小）。
        远层允许用 640 格（只看动势、不读字幕）。失败返回空串，上层退回单发。
        """
        try:
            from PIL import ImageDraw, ImageFont
            items = [(b, a) for b, a in (frames or []) if b]
            if not items:
                return ""
            cw = int(cell_w or WATCH_GRID_CELL_W)
            ch = int(cell_h or (WATCH_GRID_CELL_H if cell_w is None else cw * 9 // 16))
            lh = int(label_h or WATCH_GRID_LABEL_H)
            n = len(items)
            cols = max(1, min(int(cols or 1), n))
            rows = (n + cols - 1) // cols
            canvas = Image.new("RGB", (cw * cols, ch * rows), (10, 10, 12))
            d = ImageDraw.Draw(canvas)
            try:
                font = ImageFont.truetype(r"C:\Windows\Fonts\msyh.ttc", max(12, int(lh * 0.62)))
            except Exception:
                font = ImageFont.load_default()
            for idx, (b64s, age) in enumerate(items):
                try:
                    im = Image.open(io.BytesIO(base64.b64decode(b64s))).convert("RGB")
                except Exception:
                    continue
                im = im.resize((cw, max(16, ch - lh)), Image.BILINEAR)
                x = (idx % cols) * cw
                y = (idx // cols) * ch
                canvas.paste(im, (x, y))
                d.rectangle([x, y + ch - lh, x + cw, y + ch], fill=(0, 0, 0))
                d.text((x + 6, y + ch - lh + 2), "-%.1fs" % float(age),
                       fill=(255, 220, 0), font=font)
            buf = io.BytesIO()
            canvas.save(buf, "JPEG", quality=60)
            return base64.b64encode(buf.getvalue()).decode()
        except Exception as e:
            log.warning("历史帧拼图失败（退回单发）: %s", e)
            return ""

    def _watch_ring_diffs(self):
        """环形里相邻两帧的差（长度 = 帧数-1）；指纹缺失的位置给 None。"""
        ring = list(getattr(self, "_watch_ring", []) or [])
        out = []
        for i in range(1, len(ring)):
            a, b = ring[i - 1][2], ring[i][2]
            if a is None or b is None:
                out.append(None)
            else:
                try:
                    out.append(self._frame_diff(a, b))
                except Exception:
                    out.append(None)
        return out

    def _watch_pick_stable(self, targets, window=None, thr=None, min_gap=None):
        """按"想要距现在多少秒"取帧，但优先挑**前后都没怎么变**的那一帧。

        为什么要它（11/04）：结算页的数字是从 0 滚上去的，锚点取"4 秒前"很可能正好
        卡在 270 万那一刻 —— 这不是模型不认得数字，是取到了一张过渡帧。
        "前后两帧差都小于 WATCH_STABLE_DIFF"的帧 = 数字已经停住、画面没在动。
        """
        window = WATCH_STABLE_WINDOW if window is None else window
        thr = WATCH_STABLE_DIFF if thr is None else thr
        if min_gap is None:
            _order = sorted(targets)
            _gaps = [b - a for a, b in zip(_order, _order[1:]) if b > a]
            min_gap = max(0.3, 0.55 * min(_gaps)) if _gaps else 0.0
        ring = list(getattr(self, "_watch_ring", []) or [])
        if not ring:
            return []
        now = time.time()
        ages = [max(0.0, now - e[0]) for e in ring]
        diffs = self._watch_ring_diffs()
        # 每一帧的"稳定度"＝与前后邻居里更差的那一边（首尾只算一边）
        stable = []
        for i in range(len(ring)):
            nb = []
            if i - 1 < len(diffs) and diffs[i - 1] is not None:
                nb.append(diffs[i - 1])
            if i < len(diffs) and diffs[i] is not None:
                nb.append(diffs[i])
            stable.append(max(nb) if nb else None)
        picked, used = [], set()
        picked_ages = []
        for want in sorted(targets, reverse=True):        # 由远到近，保证时间顺序
            cands = [i for i in range(len(ring))
                     if i not in used and abs(ages[i] - want) <= window
                     and all(abs(ages[i] - pa) >= min_gap for pa in picked_ages)]
            cands.sort(key=lambda i: abs(ages[i] - want))
            choice = next((i for i in cands if stable[i] is not None and stable[i] <= thr), None)
            if choice is None and cands:
                choice = cands[0]                          # 附近全在动 ⇒ 退回"最近那张"
            if choice is None:
                continue
            used.add(choice)
            picked_ages.append(ages[choice])
            picked.append((ring[choice][1], ages[choice]))
        return picked

    def _watch_ring_pick_at(self, targets):
        """按"想要距现在多少秒"取帧（取最接近的一张），返回 [(b64, 实际多少秒前)] 旧→新。

        多分辨率时间轴用它：近层给 [6,4.5,3,1.5]，远层给 [12,19,26,33,40,47,54,60]。
        """
        ring = list(getattr(self, "_watch_ring", []) or [])
        if not ring:
            return []
        now = time.time()
        pool = [(max(0.0, now - ts), b64) for ts, b64, *_ in ring]
        picked, used = [], set()
        for want in sorted(targets, reverse=True):          # 由远到近，保证时间顺序
            best = None
            for idx, (age, b64) in enumerate(pool):
                if idx in used:
                    continue
                if best is None or abs(age - want) < abs(pool[best][0] - want):
                    best = idx
            if best is None:
                continue
            used.add(best)
            picked.append((pool[best][1], pool[best][0]))
        return picked

    def _record_watch_sample(self, comment, diff=None, force=False, elapsed=0.0,
                             model_s=0.0, frames=1, since_last=None, tiers=None, care=None,
                             color=None, trig=None, pot=None):
        """P0 基线采集（10/19 起）：把每次陪看评论落成一条 JSONL。

        为什么要它：陪看评论以前从不落盘（chat_buffer 只留 15 轮、日志只有调度行），
        导致"多帧改造到底有没有用"没有对照组。从这里开始积累真实样本。
        """
        try:
            text = (comment or "").strip()
            rec = {
                "at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                "ts": round(time.time(), 1),
                "comment": text,
                "len": len(text),
                "empty": not bool(text),
                "gap_s": round(min(elapsed, 3600.0), 1),   # 首条 last=0 会算出 epoch，截断
                "diff": None if diff is None else round(float(diff), 4),
                "force": bool(force),
                "frames": int(frames),
                "model_s": round(model_s, 2),
                "diff_last": None if since_last is None else round(float(since_last), 4),
                "tiers": tiers or "",
                "care": None if care is None else int(care),
                "pre": False,          # 11/02 起没有预生成命中这回事，字段留着兼容旧样本
                # 11/04：这一轮是被哪条路放行的（spike/force/prob），以及当时 20 秒累计运动量
                "trig": trig or "",
                "pot": None if pot is None else round(float(pot), 1),
                # 11/11：这一轮"听到"的是什么（留着校准阈值用）
                "aud": self._watch_audio_snapshot(),
            }
            if color:
                for _k in ("hue_far", "bri_far", "hue_near", "bri_near"):
                    rec[_k] = None if color.get(_k) is None else round(float(color[_k]), 1)
            with open(os.path.join(CONFIG_DIR, "watch_log.jsonl"), "a", encoding="utf-8") as f:
                f.write(json.dumps(rec, ensure_ascii=False) + "\n")
        except Exception as e:
            log.debug("陪看样本落盘失败: %s", e)

    def _record_watch_skip(self, reason, elapsed=0.0, diff=None, frames=None, since_last=None):
        """记录一次"没说话"：原因 + 距上次发言 + 画面变化。与 sample 同一份 JSONL。"""
        try:
            rec = {
                "at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                "ts": round(time.time(), 1),
                "skip": reason,
                "comment": "",
                "len": 0,
                "empty": True,
                "gap_s": round(min(elapsed, 3600.0), 1),
                "diff": None if diff is None else round(float(diff), 4),
                "frames": None if frames is None else int(frames),   # 跳过发生在抓帧之前 ⇒ 帧数未知
                "diff_last": None if since_last is None else round(float(since_last), 4),
            }
            with open(os.path.join(CONFIG_DIR, "watch_log.jsonl"), "a", encoding="utf-8") as f:
                f.write(json.dumps(rec, ensure_ascii=False) + "\n")
        except Exception as e:
            log.debug("陪看跳过记录失败: %s", e)

    def _watch_audio_snapshot(self):
        """近 20 秒声音的可量化摘要（写进 watch_log，供以后校准阈值）。"""
        try:
            am = getattr(self, "audio_meter", None)
            if am is None:
                return None
            rows = am.recent(20.0)
            if not rows:
                return None
            dbs = [f["db"] for _, f in rows]
            return {
                "n": len(rows),
                "avg": round(float(sum(dbs) / len(dbs)), 1),
                "max": round(float(max(dbs)), 1),
                "trans": int(sum(f["trans"] for _, f in rows)),
                "low": round(float(sum(f["low"] for _, f in rows) / len(rows)), 2),
            }
        except Exception:
            return None

    def _watch_context_block(self):
        """给陪看的三条参照信息（11/07）：画像事实、本场时长、距上次开口。

        为什么是这三条：陪看是间断采样（几十秒一条），把稀疏的 spot/评论拼成
        "序列"会让模型自己填空档（"先…又…"就是这么来的）。这三条都是**硬事实**
        或**稳定属性**，不依赖采样连续性。
        """
        lines = []
        # ① 一条他身上的老毛病（从 user_notes 里挑与当前场景沾边的，去掉"需要…"的指导尾巴）
        try:
            spot = (getattr(self, "_watch_last_spot", "") or "").strip()
            notes = []
            for _n in ((self.memory_data.get("profile") or {}).get("user_notes") or []):
                _c = str(_n.get("content") or "").strip() if isinstance(_n, dict) else ""
                if not _c:
                    continue
                _c = re.split(r"[，,；;]?\s*需要", _c)[0].strip()
                _c = _c.rstrip("。；;")
                if 6 <= len(_c) <= 46:
                    notes.append(_c)
            if notes:
                def _score(_t):
                    _sp = set(spot)
                    return sum(1 for ch in _sp if ch in _t)
                _pick = max(notes, key=_score) if spot else notes[0]
                if not spot or _score(_pick) > 0:
                    lines.append("你早看明白了：%s。" % _pick)
        except Exception as e:
            log.debug("陪看上下文（画像）跳过: %s", e)
        # ② 本场已经陪了多久
        try:
            _t0 = float(getattr(self, "_watch_segment_start_time", 0) or 0)
            if _t0:
                _mins = int((time.time() - _t0) / 60)
                _hm = time.strftime("%H:%M", time.localtime(_t0))
                if _mins >= 60:
                    lines.append("这一场从 %s 到现在，已经 %d 小时 %d 分。" % (_hm, _mins // 60, _mins % 60))
                elif _mins >= 1:
                    lines.append("这一场从 %s 开始，已经 %d 分钟。" % (_hm, _mins))
        except Exception as e:
            log.debug("陪看上下文（时长）跳过: %s", e)
        # ③ 距上次开口多久
        try:
            _last = float(getattr(self, "last_watch_comment_time", 0) or 0)
            if _last:
                _gap = int(time.time() - _last)
                if _gap >= 20:
                    lines.append("你上一次开口是 %d 秒前。" % _gap)
        except Exception as e:
            log.debug("陪看上下文（间隔）跳过: %s", e)
        # ④ 最近 20 秒的声音（和画面同一段时间窗）
        try:
            am = getattr(self, "audio_meter", None)
            if am is not None:
                _aud = am.describe(20.0)
                if _aud:
                    lines.append(_aud)
        except Exception as e:
            log.debug("陪看上下文（声音）跳过: %s", e)
        return chr(10).join(lines)

    def _watch_prepare(self, force=False):
        """取帧 + 算 motion/since_last + 拼两张 960 的图，返回本轮要发的图。

        11/02 改成"均匀注意力"：不再有原生 1280 锚点 —— 近段（最新 6 秒，1.5 秒一格）
        拼一张，远段（6 秒到缓冲边界，稀疏）也拼一张且同样 960 宽。
        旧的远层是 640、糊到读不出字，等于白给；现在 20 秒里每一段都"说得出"。
        """
        out = {"ok": False}
        try:
            ring = list(getattr(self, "_watch_ring", []) or [])
            if ring:
                newest_b64 = ring[-1][1]
            else:
                newest_b64 = self.capture_screen_base64()      # 环里还没帧（刚开陪看）才现抓
            if not newest_b64:
                return out
            sig = self._frame_signature(newest_b64)
            since_last = self._frame_diff(self.last_screen_sig, sig)
            _sigs = [s for _b, _a, s in self._watch_ring_pick_aged() if s is not None]
            _sigs.append(sig)
            motion = self._frames_motion(_sigs)
            out.update({"ok": True, "sig": sig, "since_last": since_last,
                        "motion": motion, "sigs": _sigs, "prev": None,
                        "color_src": newest_b64})

            _recent_n = max(1, min(4, int(getattr(self, "watch_recent_frames", WATCH_RECENT_FRAMES))))
            _older_n = max(0, min(8, int(getattr(self, "watch_older_frames", WATCH_OLDER_FRAMES))))
            _span = max(6.0, float(getattr(self, "watch_ring_seconds", WATCH_RING_SECONDS)))
            _mode = str(getattr(self, "watch_tier_mode", WATCH_TIER_MODE) or "uniform").lower()
            if _mode == "uniform":
                # 11/04：8 格均等铺满整段 —— 没有哪一格"更清楚"，注意力只能落在"这过程怎么走的"
                _total_n = _recent_n + _older_n
                _hi = min(WATCH_UNIFORM_TO, max(WATCH_UNIFORM_FROM + 1.0, _span - 0.5))
                _targets = [WATCH_UNIFORM_FROM + (_hi - WATCH_UNIFORM_FROM) * i / max(1, _total_n - 1)
                            for i in range(_total_n)]
                _picked = sorted(self._watch_pick_stable(_targets), key=lambda t: -t[1])   # 远 → 近
                _older = _picked[:max(0, len(_picked) - _recent_n)] if _older_n else []
                _recent = _picked[len(_older):]
            else:
                _recent_targets = [WATCH_NEAR_FROM + (WATCH_NEAR_TO - WATCH_NEAR_FROM) * i / max(1, _recent_n - 1)
                                   for i in range(_recent_n)]
                _recent = self._watch_pick_stable(_recent_targets)
                _older = []
                if _older_n:
                    _t0 = max(WATCH_FAR_FROM, WATCH_NEAR_TO)
                    if _span > _t0 + 1.0:
                        _older_targets = [_t0 + (_span - _t0) * (i + 1) / _older_n for i in range(_older_n)]
                        _older = self._watch_pick_stable(_older_targets)
            _near_img = None
            if len(_recent) >= 2:
                _near_img = self._compose_frames_grid(_recent, cols=2,
                                                      cell_w=WATCH_GRID_CELL_W, cell_h=WATCH_GRID_CELL_H)
            _far_img = None
            if len(_older) >= 2:
                _far_img = self._compose_frames_grid(_older, cols=2,
                                                     cell_w=WATCH_GRID_CELL_W, cell_h=WATCH_GRID_CELL_H)
            if _near_img:
                # 顺序：远 → 近（build_context_messages 把 earlier 排在前、主图排最后）
                _earlier = [_far_img] if _far_img else []
                out.update({"image_b64": _near_img, "earlier": _earlier, "recent": _recent,
                            "older": _older, "use_grid": True,
                            "sent_images": len(_earlier) + 1})
            else:
                # 拼图失败 ⇒ 退回逐张单发（保持能看）
                _earlier = [self._badge_frame(_b, "-%ds" % max(1, round(_a)))
                            for _b, _a, _s in self._watch_ring_pick_aged()]
                out.update({"image_b64": self._badge_frame(newest_b64, "刚才"),
                            "earlier": _earlier, "recent": _recent, "older": _older,
                            "use_grid": False, "sent_images": len(_earlier) + 1})
            return out
        except Exception as e:
            log.warning("陪看: 取帧/拼图失败 %s", e)
            return out


    def analyze_and_comment(self, force=False):
        if self.sleep_mode:
            return
        if not self.watch_mode and not force:
            return
        if not self.watch_lock.acquire(blocking=False):
            return

        now = time.time()
        elapsed = now - self.last_watch_comment_time

        _trig = "force" if force else "?"
        if not force:
            if elapsed < self.watch_min_interval:
                log.debug("陪看: 距上次发言 %.1fs < 最小间隔 %ds，跳过", elapsed, self.watch_min_interval)
                self._record_watch_skip("interval", elapsed)
                self.watch_lock.release()
                return
            elif elapsed >= self.watch_max_silence:
                log.debug("陪看: 距上次发言 %.1fs > 最长沉默 %ds，强制触发", elapsed, self.watch_max_silence)
                force = True
                _trig = "force"
            else:
                # 原公式是按 15 秒一次推的；现在 2 秒一判，按时间比例折算成单次概率（期望发言率不变）
                p15 = max(0.05, (elapsed - self.watch_min_interval) /
                          max(1.0, (self.watch_max_silence - self.watch_min_interval)))
                _poll = max(WATCH_POLL_MIN, min(self.watch_min_interval / WATCH_POLL_DIV, WATCH_POLL_MAX))
                _base = max(5.0, min(self.watch_min_interval // 2, 60))     # 原设计的判断间隔
                prob = 1.0 - (1.0 - p15) ** (_poll / _base)
                # 11/02：画面刚突变过就不掷骰子 —— 让她由"画面变了"驱动，而不是随机数
                _spike_age = time.time() - float(getattr(self, "_watch_spike_at", 0.0) or 0.0)
                if _spike_age <= WATCH_SPIKE_WINDOW:
                    self._watch_spike_at = 0.0
                    _trig = "spike"
                    log.debug("陪看: 画面刚突变过（%.1f 秒前），直接放行", _spike_age)
                elif random.random() > prob:
                    log.debug("陪看: 概率跳过 (elapsed=%.1fs, prob=%.2f)", elapsed, prob)
                    self._record_watch_skip("prob", elapsed)
                    self.watch_lock.release()
                    return
                else:
                    _trig = "prob"

        log.debug("陪看: 开始分析画面")
        def process():
            # 10/30：动作最猛的那一下别在半空中开口 —— 先等它落定，再截"现在"的帧
            try:
                _ring = list(getattr(self, "_watch_ring", []) or [])
                if len(_ring) >= 2:
                    _sig_a = _ring[-2][2] if len(_ring[-2]) > 2 else None
                    _sig_b = _ring[-1][2] if len(_ring[-1]) > 2 else None
                    if _sig_a is None or _sig_b is None:
                        _sig_a = self._frame_signature(_ring[-2][1])
                        _sig_b = self._frame_signature(_ring[-1][1])
                    _m = self._frame_diff(_sig_a, _sig_b)
                    if _m >= WATCH_SETTLE_MOTION:
                        log.debug("陪看: 画面正在剧烈变化（%.1f），等 %.1f 秒落定再开口", _m, WATCH_SETTLE_SEC)
                        time.sleep(WATCH_SETTLE_SEC)
            except Exception as e:
                log.debug("陪看: 落定等待跳过（%s）", e)
            try:
                # 11/02：取帧/拼图抽到 _watch_prepare()，预生成那条路也用同一份逻辑
                _prep = self._watch_prepare(force)
                if not _prep.get("ok"):
                    self._ui(lambda: self.show_bubble_text("(normal) 唔...我现在看不到画面呢。", "normal"), status=True)
                    return
                image_b64 = _prep["image_b64"]
                _prev_b64 = _prep["prev"]
                sig = _prep["sig"]
                since_last = _prep["since_last"]
                motion = _prep["motion"]
                _sigs = _prep["sigs"]
                _recent = _prep["recent"]
                _older = _prep["older"]
                _earlier = _prep["earlier"]
                _use_grid = _prep["use_grid"]
                _color_src = _prep.get("color_src") or image_b64
                if self._watch_skip_by_stillness(motion, since_last, force):
                    log.debug("陪看: 这十秒画面没动（相邻帧最大差 %.2f < %.1f，与上次开口那帧差 %.2f），跳过不调模型",
                              motion, WATCH_MOTION_THRESHOLD, since_last)
                    self._record_watch_skip("same", elapsed, diff=motion,
                                            frames=len(_sigs), since_last=since_last)
                    return
                if not force:
                    log.debug("陪看: 画面在动 相邻帧最大差 %.2f（与上次开口那帧差 %.2f）", motion, since_last)
                _sent_images = _prep["sent_images"]
                _v0 = time.time()
                comment = None
                if True:
                    comment = self._get_vision_comment(image_b64, force=force,
                                                       image_b64_prev=_prev_b64,
                                                       image_b64_earlier=_earlier)
                # P0 基线采集：每次（含空回）都记一条；frames=1 是旧单帧样本，2 为多帧样本，可直接对比
                _care_hit = 1 if any(w in (comment or "") for w in WATCH_CARE_WORDS) else 0
                log.debug("陪看: 发图 %d 张（%s）", _sent_images,
                          "远段 4 格 + 近段 4 格（都 960）" if _use_grid else "逐张单发")
                _color = self._watch_color_pair(_color_src)
                self._record_watch_sample(comment, motion, force, elapsed,
                                          time.time() - _v0,
                                          frames=_sent_images,
                                          since_last=since_last,
                                          tiers=("%d+/%d远" % (len(_recent), len(_older)) if _use_grid else "逐张"),
                                          care=_care_hit,
                                          color=_color,
                                          trig=_trig,
                                          pot=getattr(self, "_motion_pot_sum", None))
                log.debug("陪看: 本轮图 %d 张 / 近层 %d / 远层 %d（两张都 960）",
                          _sent_images, len(_recent), len(_older))
                if comment:
                    # 只有"真的说了一句"才重置发言间隔（空回不吃间隔：间隔＝实际发言的间隔）
                    # 11/01：她自己的陪看评论不再进素材池（187/200 全是这个，取材等于自我模仿）
                    self.last_watch_comment_time = time.time()
                    self.last_screen_sig = sig
                    if _care_hit:
                        self._watch_care_count = int(getattr(self, "_watch_care_count", 0)) + 1
                        self._rest_cooldown_until = time.time() + 5 * 60   # 真提了才进冷却
                    self._ui(lambda: self.show_bubble_text(comment, "normal"))
                    self._ui(lambda: threading.Thread(target=self._tts_play, args=(comment,), daemon=True).start())
                    # 陪玩评论写入缓冲 + 事件锚点。
                    # user 侧文本用当次画面摘要而不是固定占位符——同一个占位符连着出现
                    # 等于告诉模型"情况和上次一样，照上次说"，是句式锁死的强信号。
                    try:
                        self._watch_comment_count += 1     # 10/28：本次陪玩已说几条
                    except Exception:
                        pass
                    _side = self._watch_side_text()
                    self._ui(lambda: self._add_chat_buffer_turn(_side, comment, source="watch"))
                    # 10/27：本轮真召回了相关旧记忆 → 事后补一条"想起旧事"气泡（模型可判 null）
                    _snap = list(self._last_recall or [])
                    if _snap:
                        threading.Thread(target=self._maybe_recall_link,
                                         args=(comment, _snap), daemon=True).start()
            except Exception as e:
                log.error(f"陪看分析出错: {e}")
            finally:
                self.watch_lock.release()
        threading.Thread(target=process, daemon=True).start()

    def capture_screen_base64(self):
        if not mss:
            return ""
        try:
            with mss.MSS() as sct:
                monitor = sct.monitors[1]
                img = sct.grab(monitor)
                pil_img = Image.frombytes("RGB", img.size, img.bgra, "raw", "BGRX")
                pil_img = pil_img.resize((1280, 720), Image.LANCZOS)
                buffer = io.BytesIO()
                pil_img.save(buffer, format="JPEG", quality=60)
                return base64.b64encode(buffer.getvalue()).decode('utf-8')
        except Exception as e:
            log.error(f"截图失败: {e}")
            return ""

    def capture_screen_pair(self, gap_s=1.2):
        """抓前后两帧（间隔 gap_s 秒）用于陪看。

        为什么不缓存上一轮：陪看触发间隔 30~120 秒，隔一分钟的两帧只能看出
        "场景变了"，看不出"手在动"；隔一秒的两帧才能说出具体动作。
        返回 (prev_b64, cur_b64)，任一帧失败则回退成单帧（prev 为 None）。
        """
        first = self.capture_screen_base64()
        if not first:
            return None, ""
        time.sleep(max(0.2, gap_s))
        second = self.capture_screen_base64()
        if not second:
            return None, first
        return first, second

    def _try_create_reading_event(self, ocr_text):
        """尝试识别阅读内容并创建事件锚点（精确→概括两步降级）"""
        if not self.text_api_key or not ocr_text:
            return
        call_name = self.user_profile.get("call_name", "你")
        try:
            # 第一步：尝试精确识别
            prompt1 = f"""请根据以下OCR识别的文字片段，判断用户正在阅读什么（书名、文章标题等）。
只回答内容名称，不超过15个字。如果无法识别具体名称，回答"未知"。

OCR文字：
{ocr_text[:500]}"""
            resp = self._call_text_model([{"role": "user", "content": prompt1}], temperature=0.3, max_tokens=DEFAULT_MAX_TOKENS, timeout=15)
            if resp.status_code == 200:
                result = resp.json()["choices"][0]["message"]["content"].strip()
                if result and result != "未知" and len(result) >= 2:
                    self._add_event_memory(f"陪{call_name}一起读了《{result}》", importance=0.7, source="reading")
                    log.info(f"读书事件锚点(精确): {result}")
                    return
            # 第二步：降级为概括描述
            prompt2 = f"""请概括描述用户正在阅读的内容类型，例如"一本医学书籍""一篇历史文章""一部玄幻小说""一篇技术博客"等。10字以内。

OCR文字：
{ocr_text[:500]}"""
            resp2 = self._call_text_model([{"role": "user", "content": prompt2}], temperature=0.3, max_tokens=DEFAULT_MAX_TOKENS, timeout=15)
            if resp2.status_code == 200:
                result2 = resp2.json()["choices"][0]["message"]["content"].strip()
                if result2 and len(result2) >= 2:
                    self._add_event_memory(f"陪{call_name}一起读了{result2}", importance=0.5, source="reading")
                    log.info(f"读书事件锚点(概括): {result2}")
        except Exception as e:
            log.warning(f"读书事件识别失败: {e}")

    @staticmethod
    def _frame_signature(image_b64):
        """把截图缩成 WATCH_SIG_SIZE 的灰度小图当"画面指纹"（解不开就返回 None）"""
        try:
            img = Image.open(io.BytesIO(base64.b64decode(image_b64)))
            return img.convert("L").resize(WATCH_SIG_SIZE, Image.BILINEAR).tobytes()
        except Exception:
            return None

    @staticmethod
    def _frame_diff(sig_a, sig_b):
        """两枚指纹的平均像素差（0~255）；缺一个或长度不符时当作完全不同（255）"""
        if not sig_a or not sig_b or len(sig_a) != len(sig_b):
            return 255.0
        a = np.frombuffer(sig_a, dtype=np.uint8).astype(np.int16)
        b = np.frombuffer(sig_b, dtype=np.uint8).astype(np.int16)
        return float(np.abs(a - b).mean())

    @staticmethod
    def _frame_color_sig(image_b64):
        """色彩指纹（11/01）：色调 24 桶 + 亮度 8 桶的归一化直方图；解不开返回 None。

        为什么不用"空间色块"：真实游戏帧上实测"色块网格差"和"灰度差"几乎完全一样
        （p50 36.2 vs 36.5，只差 0.3）——空间差被亮度主导，加颜色没新信息。
        真正与运动量正交的是**色彩构成**（哪种颜色占多少面积），所以这里只看分布不看位置。
        """
        try:
            img = Image.open(io.BytesIO(base64.b64decode(image_b64)))
            arr = np.asarray(img.resize(WATCH_COLOR_SIZE, Image.BOX).convert("HSV"), dtype=np.int32)
            h, s, v = arr[..., 0], arr[..., 1], arr[..., 2]
            mask = (s > 40) & (v > 40)
            hue = np.bincount((h[mask] * 24) // 256, minlength=24).astype(np.float32)
            if hue.sum() > 0:
                hue = hue / hue.sum()
            bri = np.bincount((v.ravel() * 8) // 256, minlength=8).astype(np.float32)
            if bri.sum() > 0:
                bri = bri / bri.sum()
            return (hue.tobytes(), bri.tobytes())
        except Exception:
            return None

    @staticmethod
    def _color_diff(sig_a, sig_b):
        """(色调距离, 亮度距离)，各自 0~100 的半 L1 距离；缺一个就当完全不同。"""
        try:
            if not sig_a or not sig_b:
                return 100.0, 100.0
            a = np.frombuffer(sig_a[0], dtype=np.float32)
            b = np.frombuffer(sig_b[0], dtype=np.float32)
            c = np.frombuffer(sig_a[1], dtype=np.float32)
            d = np.frombuffer(sig_b[1], dtype=np.float32)
            if len(a) != len(b) or len(c) != len(d):
                return 100.0, 100.0
            return float(np.abs(a - b).sum() / 2.0) * 100.0, float(np.abs(c - d).sum() / 2.0) * 100.0
        except Exception:
            return 100.0, 100.0

    def _watch_color_pair(self, image_b64, seconds=18.0):
        """当前帧 vs 环形里 ~seconds 秒前那帧 / vs 最新那帧。

        返回 dict：hue_far/bri_far（换没换地方）、hue_near/bri_near（是不是突然变色）。
        这项只是采集，不参与任何判定 —— 先跑几场看分布再定阈值。
        """
        out = {"hue_far": None, "bri_far": None, "hue_near": None, "bri_near": None}
        try:
            cur = self._frame_color_sig(image_b64)
            if cur is None:
                return out
            ring = list(getattr(self, "_watch_ring", []) or [])
            if ring:
                now = time.time()
                far = min(ring, key=lambda t: abs(t[0] - (now - seconds)))
                out["hue_far"], out["bri_far"] = self._color_diff(
                    self._frame_color_sig(far[1]), cur)
                out["hue_near"], out["bri_near"] = self._color_diff(
                    self._frame_color_sig(ring[-1][1]), cur)
        except Exception as e:
            log.debug("色彩指纹计算失败: %s", e)
        return out


    @staticmethod
    def _frames_motion(sigs):
        """一串指纹（旧→新）最大相邻差：衡量这一小段里画面有没有真的在动。

        解码失败的帧（None）直接跳过——它和任何一张的 diff 都是 255，
        算进去会把 motion 顶到 255、让去重在本轮失效。"""
        best = 0.0
        prev = None
        for s in sigs:
            if s is None:
                prev = None          # 断链：不拿坏帧去比
                continue
            if prev is not None:
                best = max(best, DesktopPet._frame_diff(prev, s))
            prev = s
        return best

    @staticmethod
    def _watch_skip_by_stillness(motion, since_last, force=False):
        """要不要因为“画面没动”跳过这一轮。"""
        return (not force) and motion < WATCH_MOTION_THRESHOLD and since_last < WATCH_CHANGE_BIG


    def open_music_web(self):
        """网页版模式：打开网页版播放器，或让它开始播放。

        10/22 用户报的问题：浏览器首次打开时不会自动播放（浏览器拦截自动播放），
        他说"开始播放"时她又开了一遍网页（多开一个标签页）。
        修法：**浏览器里已经有媒体会话 ⇒ 只发"播放"给它，不再开新页**；没有会话才打开网址。
        """
        if _browser is not None and _browser.AVAILABLE:
            try:
                _st = _browser.status()
            except Exception:
                _st = None
            if _st:
                if _st.get("status") == "playing":
                    return True, "已经在放啦"
                ok, err = _browser.control("play")
                if ok:
                    # 浏览器会拦"程序发起的播放"（自动播放策略）：接口回成功、实际没播。
                    # 所以必须过一会儿回查真状态，别谎报"开始放了"。
                    for _ in range(10):
                        time.sleep(0.12)
                        try:
                            if ((_browser.status() or {}).get("status")) == "playing":
                                return True, "开始放了"
                        except Exception:
                            break
                    return False, ("浏览器拦了自动播放（它不让程序点播放）——"
                                   "你点一下网页里的播放按钮，或者在浏览器里允许这个网站自动播放")
                return False, "浏览器那边不让播（%s）——你点一下网页里的播放按钮" % (err or "没响应")
        url = load_music_web_url()
        if not url:
            return False, "还没设置网页版播放器网址（右键 设置 → 音乐库设置 里填一个网址）"
        # 没有媒体会话，但网页可能刚开过（播放页是"加载了但没注册会话"的状态）。
        # 10/22 用户报："要求开始还是再开一个窗口" ⇒ 10 分钟内不再重开，直接说明白。
        _last = getattr(self, "_web_player_opened_at", 0)
        if time.time() - _last < 600:
            return True, ("网页版还开着呢（浏览器不让程序自动播放），"
                          "你在那边点一下播放按钮就行，不用再开一个窗口")
        try:
            import webbrowser
            if webbrowser.open(url):
                self._web_player_opened_at = time.time()
                # 10/22 实测的硬限制：网页**第一次**播放之前，浏览器不会给这个页面注册媒体会话，
                # 所以她那会儿根本"看不见"它，也没法让它开始放 —— 只能用户手动点一下。
                # 播放过一次之后会话就一直在，之后暂停/继续/切歌/调音量都正常。
                return True, "网页版播放器打开了（第一次请点一下播放，之后我就能接了）"
            return False, "浏览器没能打开这个网址"
        except Exception as e:
            log.warning("打开网页版失败: %s", e)
            return False, "网页打不开（%s）" % str(e)[:40]

    def _set_local_music_volume(self, value=None, delta=None):
        """调"我们曲库这一路音乐"的音量（落盘 + 立刻生效）。"""
        cur = int(round(self._music_volume * 100))
        if value is None and delta is None:
            return True, f"现在音乐音量是 {cur}%（说“大一点/小一点”或给个 0~100 的数都行）"
        try:
            if value is not None:
                new = int(round(float(value)))
            else:
                new = cur + int(round(float(delta)))
        except (TypeError, ValueError):
            return False, "没听清要调到多少，给个 0~100 的数吧"
        new = max(0, min(100, new))
        self._music_volume = new / 100.0
        save_music_volume_setting(new)
        self._fade_gen += 1            # 取消进行中的淡变，免得旧的把新值盖掉
        try:
            pygame.mixer.music.set_volume(self._music_volume_now())
        except Exception:
            pass
        log.info("音乐音量 %d%% → %d%%（对话设置）", cur, new)
        return True, f"音乐音量调到 {new}% 了"

    def control_browser(self, action, seek_to=None, value=None, delta=None):
        """控制浏览器里在放的东西（网页版模式下它就是音乐播放器）。"""
        if _browser is None or not _browser.AVAILABLE:
            return False, "这台机器读不到浏览器的媒体会话"
        act = (action or "").strip().lower()
        if act == "volume":
            # 10/22：浏览器音量（走 pycaw 的按程序音量，和音量合成器里拖滑块是同一件事）
            proc = None
            try:
                st0 = _browser.status() or {}
                app = (st0.get("app") or "").lower()
                for k in ("edge", "chrome", "firefox", "brave", "opera", "vivaldi"):
                    if k in app:
                        proc = ("msedge" if k == "edge" else k)
                        break
            except Exception:
                proc = None
            cur = _duck.get_volume(proc) if _duck is not None else None
            if cur is None:
                return False, "读不到浏览器音量（它现在没在出声？）"
            if value is None and delta is None:
                return True, "浏览器音量现在是 %d%%" % cur
            new = int(value) if value is not None else cur + int(delta)
            new = max(0, min(100, new))
            if not _duck.set_volume(new, proc):
                return False, "音量没调成"
            return True, "浏览器音量调到 %d%% 了" % new
        if act in ("status", "what", "info"):
            st = _browser.status()
            if not st:
                return False, "浏览器里没有在放东西"
            prog = ""
            if st["position"] >= 0 and st["duration"] > 0:
                def _mmss(x):
                    x = int(max(0, x))
                    return "%d:%02d" % (x // 60, x % 60)
                prog = "（%s / %s）" % (_mmss(st["position"]), _mmss(st["duration"]))
            if st["status"] == "paused":
                prog += "，现在是暂停着"
            who = ("——" + st["artist"]) if st["artist"] else ""
            return True, "浏览器里在放《%s》%s%s" % (st["title"] or "?", who, prog)
        ok, err = _browser.control(act, seek_to)
        if not ok:
            return False, err or "浏览器没响应"
        if act in ("pause",):
            return True, "暂停了"
        if act in ("play",):
            return True, "继续放了"
        st = _browser.status() or {}
        title = (st.get("title") or "").strip()
        if act in ("next", "prev"):
            return True, ("切到《%s》了" % title) if title else "切好了"
        if act == "toggle":
            return True, ("现在在放《%s》" % title) if st.get("status") == "playing" and title else "好"
        return True, ("《%s》" % title) if title else "好"

    def _auto_glance(self):
        """主动瞟一眼屏幕，随口说一句（跟主动话题共用调度，11/01）。

        和 look_at_screen 的区别：那个是"他让你看、要把话答回去"；这个是
"她自己看了一眼、随口嘀咕一句"，直接弹气泡 + 语音，不写陪看历史、不动陪看间隔。
        """
        if self.sleep_mode or getattr(self, "watch_mode", False):
            return False
        rc = getattr(self, "reading_companion", None)
        if bool(getattr(rc, "active", False) or getattr(rc, "running", False)):
            return False
        if not self.vision_api_key or not self.vision_model:
            return False
        if getattr(self, "api_busy", False):
            return False
        try:
            image_b64 = self.capture_screen_base64()
        except Exception as e:
            log.debug("主动瞟一眼：截图失败 %s", e)
            return False
        if not image_b64:
            return False
        line = self._get_vision_comment(image_b64, force=False, glance=True)
        line = (line or "").strip()
        if not line:
            return False
        # 11/13：改成和"主动话题"同一个形态 —— 她抛一句 + 两个可点的选项，
        # 他点一个之后 she 再回一句（走 on_event_option 那条现成链路），
        # 这句也会作为 topic_open 记进聊天时间线（display_only，不进模型上下文）。
        _opts = list(getattr(self, "_last_glance_options", None) or [])
        while len(_opts) < 2:
            _opts.append("嗯，是的" if not _opts else "没有啦")
        _line_plain = re.sub(r"^\([a-z]+\)\s*", "", line).strip() or line
        self._ui(lambda: self.show_event_bubble(_line_plain, _opts[0], _opts[1]))
        log.info("主动凑过来（带选项）：%s | %s / %s", line[:60], _opts[0], _opts[1])
        return True

    def _find_dsh_cli(self):
        """找 DSH 的命令行入口（找不到返回空串）。配置里指定的路径优先。"""
        try:
            _configured = load_dsh_settings().get("cli") or ""
        except Exception:
            _configured = ""
        if _configured:
            try:
                if os.path.isfile(_configured):
                    return _configured
            except Exception:
                pass
        for p in DSH_CLI_CANDIDATES:
            try:
                if p and os.path.isfile(p):
                    return p
            except Exception:
                continue
        from shutil import which
        for name in ("dsh.cmd", "dsh"):
            try:
                p = which(name)
                if p:
                    return p
            except Exception:
                continue
        return ""

    def ask_dsh(self, task):
        """把一件事外包给 DSH 的 headless 模式，返回 (ok, 文本)。

        定位（11/06）：她是主体，DSH 只是她的一双手——她做不到的（动文件、跑命令、
        查资料）才外包。只跑一次性任务、只回结果，不把上下文交出去。
        """
        task = " ".join(str(task or "").split())
        if not task:
            return False, "要办的事还没说清呢"
        try:
            if not load_dsh_settings().get("enabled", True):
                return False, "我这边把外包关掉了，这件事得你自己来"
        except Exception:
            pass
        if len(task) > DSH_ASK_MAX_TASK:
            task = task[:DSH_ASK_MAX_TASK]
        cli = self._find_dsh_cli()
        if not cli:
            return False, "我这边找不到 DSH 的命令行，暂时办不了这件事"
        if not self._dsh_ask_lock.acquire(blocking=False):
            return False, "上一件外包的事还没办完，等一下再说"
        try:
            _env = dict(os.environ)
            _env.setdefault("PYTHONIOENCODING", "utf-8")
            _env.setdefault("NO_COLOR", "1")
            # headless profile 不会自动拿到 GUI 里存的密钥 ⇒ 用她自己的文本模型 key。
            # 注意：**不要传 DEEPSEEK_BASE_URL** —— 实测传 /v1 会让它走 Messages 接口并 404，
            # 只给 key 时它会自己用 https://api.deepseek.com/models 探测（11/06 验证）。
            try:
                _k = str(getattr(self, "text_api_key", "") or "").strip()
                if _k:
                    _env.setdefault("DEEPSEEK_API_KEY", _k)
            except Exception:
                pass
            import subprocess as _sp
            _flags = getattr(_sp, "CREATE_NO_WINDOW", 0) if os.name == "nt" else 0
            log.info("外包给 DSH：%s", task[:80])
            _t0 = time.time()
            # 任务用 stdin 传（`headless -`），中文与引号都不用转义
            proc = _sp.Popen(["cmd", "/c", cli, "headless", "-"],
                                    stdout=_sp.PIPE, stderr=_sp.PIPE,
                                    stdin=_sp.PIPE, cwd=CONFIG_DIR,
                                    env=_env, creationflags=_flags)
            try:
                out, err = proc.communicate(task.encode("utf-8"), timeout=DSH_ASK_TIMEOUT)
            except _sp.TimeoutExpired:
                log.warning("外包超时（%d 秒），结束 DSH 进程", DSH_ASK_TIMEOUT)
                try:
                    _sp.run(["taskkill", "/PID", str(proc.pid), "/T", "/F"],
                                   capture_output=True, timeout=10)
                except Exception:
                    pass
                try:
                    proc.kill()
                except Exception:
                    pass
                return False, "这件事办得比我想的久，先放下了"
            text = (out or b"").decode("utf-8", "replace")
            text = re.sub(r"\[[0-9;]*m", "", text)      # 去 ANSI
            lines = [ln.rstrip() for ln in text.splitlines()]
            lines = [ln for ln in lines if ln.strip() and not ln.startswith("[llm-")]
            body = chr(10).join(lines).strip()
            if len(body) > DSH_ASK_KEEP_CHARS:
                body = body[:DSH_ASK_KEEP_CHARS] + "…"
            _err = (err or b"").decode("utf-8", "replace").strip()
            took = time.time() - _t0
            log.info("外包完成：%.1f 秒，输出 %d 字，退出码 %s", took, len(body), proc.returncode)
            if proc.returncode not in (0, None):
                _why = " | ".join((_err or body or "").strip().splitlines()[-2:])[:300]
                return False, "它办到一半出错了：" + _why
            if not body:
                _why = " | ".join((_err or "").strip().splitlines()[-2:])[:300]
                return False, "它那边没给出结果" + ("（%s）" % _why if _why else "")
            return True, body
        except Exception as e:
            log.exception("外包失败：%s", e)
            return False, "外包的时候出岔子了（%s）" % e
        finally:
            self._dsh_ask_lock.release()

    def look_at_screen(self, focus=""):
        """看一眼当前屏幕并按他的关注点说一句（工具入口，10/17 新增）。

        由**模型自己判断**要不要调（工具描述里写了触发场景），不靠关键词/字数。
        与陪看 analyze_and_comment 的区别：这里**同步把话交回去**，由她在那一轮回复里说，
        不弹独立气泡、不写陪看历史。focus 是"他想让你看什么"，可选。
        """
        if self.sleep_mode:
            return False, "我已经睡了，先叫醒我"
        if not self.vision_api_key or not self.vision_model:
            return False, "还没配置视觉模型（右键设置里填 API Key 和模型名）"
        try:
            image_b64 = self.capture_screen_base64()
        except Exception as e:
            return False, f"截图失败：{e}"
        if not image_b64:
            return False, "截图失败，没拿到画面"
        line = self._get_vision_comment(image_b64, force=True, focus=focus, look=True)
        line = (line or "").strip()
        if not line:
            return False, "看了一眼，没看清"
        log.info("工具：看屏幕（focus=%s）→ %s", (focus or "")[:20], line[:80])
        return True, line

    def _get_vision_comment(self, image_b64, force=False, focus="", image_b64_prev=None,
                            image_b64_earlier=None, look=False, glance=False):
        """使用 OpenAI 兼容视觉模型分析截图"""
        if not self.vision_api_key:
            return "(worried) 请先设置视觉模型 API Key"
        if not self.vision_model:
            return "(worried) 请先设置视觉模型名称"
        self._watch_last_spot = ""      # 本轮若失败/空回，不能沿用上一轮的标签

        user_name = self.user_profile.get("call_name", "你")

        # 反重复：先判断这次是不是"她连着自言自语"的独白场景。
        # 独白（末尾连续陪玩、中间没有用户发言）时，模型会照着自己上一条的句式接着写，
        # 于是断掉回喂、改用"已说过"清单；用户插过话就是双向对话，历史照常回喂更有连贯性。
        with self._memory_lock:
            _turns = list(self.chat_buffer)
            said = [t[1].get("content", "") for t in _turns if t[0].get("source") == "watch"]
        consec = 0
        for t in reversed(_turns):
            if t[0].get("source") == "watch":
                consec += 1
            else:
                break
        monologue = consec >= WATCH_MONOLOGUE_TURNS
        said = [s for s in said if s][-WATCH_ANTI_REPEAT:]
        said_block = ""
        if said:
            # 不管理是不是独白都附上：这是防重复的主力（静态黑名单反而会把坏句式写进提示词）
            said_block = ("【你已经说过的陪玩评论——别再复用这些句子和切入角度，换一个说法】\n"
                          + "\n".join(f"- {s}" for s in said))

        # 10/30：用户纠正 —— 「关心」特指「倒水/喝水/休息/眯一会」这类内容，**不是**把话头引到用户。
        # 所以这里只收这一句的许可（一场最多 2 次，说过就不再给），不加新的限制条目。
        _care_left = max(0, WATCH_CARE_MAX - int(getattr(self, "_watch_care_count", 0)))
        rest_line = ("" if (time.time() < self._rest_cooldown_until or _care_left <= 0) else
                     "他要是连着玩了很久、或者节奏明显慢下来，偶尔顺口提一句让他歇会儿；不用非得说。")
        force_line = "这一轮得说一句——画面里没什么可说的，就说你自己这会儿怎么样。" if force else ""
        # 他明确点名要你看什么时（"看看我拿到了什么"），把关注点揉进提示词，别答非所问
        focus_line = ""
        if (focus or "").strip():
            focus_line = "他刚才让你看的是「%s」——先就这个说一句，别答非所问。" % focus.strip()
        # 10/23：回答模式（look_at_screen）。他要的是"回答"，不是"陪看感慨"。
        # 只有这一条路直接把视觉模型的输出当最终回复（不再过文本模型，省一次调用）。
        _look_q = (focus or "").strip()
        if look and not _look_q:
            with self._memory_lock:
                for _t in reversed(list(self.chat_buffer)):
                    if _t[0].get("source") != "watch":
                        _look_q = (_t[1].get("content") or "").strip()[:80]
                        break
        look_instructions = f"""你看的是"{user_name}"的屏幕，他指着画面上的东西问你一件事：「{_look_q}」
你要**直接回答他**，不要只给一句感慨，也不要反问他"你想让我看什么"。
怎么答：第一句说你在这张画面上看到的**依据**（哪句话、什么数字、什么状态），第二句给你的判断（真的假的／可信可疑／这是什么东西）。总共不超过 70 字。
语气用你自己的，开头一个情绪括号。别复述整个画面，别把画面里的东西挨个念。
画面上那只桌宠就是你自己，别把她认成别人。
如果画面里根本看不出他在问什么，就直说看不出，别编。
请严格输出 JSON，不要 markdown 代码块：{{"comment": "开头一个情绪括号 + 你要说的那一句话"}}"""
        _ctx_block = self._watch_context_block()
        watch_instructions = f"""你就坐在"{user_name}"旁边，跟他一起看这块屏幕。
你是{self.pet_name}，用你自己的语气说话。
这些格子是从头到尾的一小段过程，每格底下标着距现在几秒。
{_ctx_block}
说说你自己的感受。
{focus_line}
你怎么说话都行：说半句、哼一声、跟自己嘀咕、突然想起别的事，都可以。
{rest_line}
没什么想说的，comment 就留空，不用硬凑——他只是翻界面看数据的时候尤其如此。{force_line}
{said_block}
请严格输出JSON，不要markdown代码块：
{{"comment": "开头一个情绪括号 + 你要对他说的那句话本身（不是“我做了什么/已按规则生成”这种回执）；没什么想说的就留空字符串", "spot": "这是哪儿，12字以内，只写场景（例如“Apex 排位·房间”），不要写数字和界面文字；看不出就留空字符串"}}
"""

        # 11/03：凑过来看一眼 —— 关注"他在干什么"，然后说个小感想，不是评论画面
        glance_instructions = ""
        if glance:
            glance_instructions = chr(10).join([
                '你刚从旁边凑过来，看了一眼"%s"的屏幕。' % self.user_profile.get("call_name", "他"),
                '先看他这会儿在干什么，再说一句你对这件事的感想——好奇、关心、或者夸他一句，都行。',
                '像刚凑近才看明白的那种口气，一两句。',
                '再给他两个可以点着回的短选项：一个像"嗯对/在呢"，一个像"没有啦/别闹"，',
                '各不超过 8 个字，要贴这会儿的画面（比如"在看直播"/"随便翻翻"）。',
                '请严格输出 JSON，不要 markdown 代码块：',
                '{"comment": "开头一个情绪括号 + 那句话", "spot": "他在干什么，12字以内",',
                ' "options": ["第一个选项(≤8字)", "第二个选项(≤8字)"]}',
            ])

        messages = self.build_context_messages(
            self._effective_system_prompt(),
            glance_instructions if glance else (look_instructions if look else watch_instructions),
            context_type=("look" if look else "watch"), image_b64=image_b64,
            memory_query=(_look_q if look else self._build_watch_query()),
            extra_context=("" if (look and not glance) else said_block),
            skip_sources={"watch"} if (monologue and not look and not glance) else None,
            image_b64_prev=image_b64_prev,
            image_b64_earlier=image_b64_earlier)
        try:
            # 陪看走 WATCH_TEMPERATURE（0.98）；看屏幕的回答模式用 0.7 更稳
            resp = self._call_vision_model(messages, temperature=(0.75 if glance else (0.7 if look else WATCH_TEMPERATURE)),
                                           max_tokens=DEFAULT_MAX_TOKENS, timeout=30)
            if resp.status_code != 200:
                log.error(f"视觉模型 API 返回非200: {resp.status_code} {resp.text[:200]}")
                return None

            raw_reply = self._extract_message_content(resp.json()["choices"][0]["message"]).strip()
            if not raw_reply:
                return None
            # 10/24：输出被截断时宁可不说，也别把半句念出去（实测 13:34 那条
            # "…一眼就瞅见我自" 就是 JSON 没写完，正则兜底抠出了半句话）。
            _r = raw_reply.rstrip()
            if _r.startswith("{") and not _r.endswith("}"):
                _fr = ""
                try:
                    _fr = str(resp.json()["choices"][0].get("finish_reason"))
                except Exception:
                    pass
                log.warning("视觉输出疑似被截断（JSON 没闭合，len=%d, finish=%s），丢弃本次评论: %s",
                            len(_r), _fr or "?", _r[-40:])
                return None
            comment = raw_reply
            spot = ""       # JSON 解析失败时也必须已定义（10/27：漏了这句 ⇒ 整条评论丢失）
            # 10/19：实测模型偶尔吐全角 （normal），下面的情绪解析只认半角 ⇒ 先归一化，
            # 否则 UI 上会看到"（normal）镜头一转…"这种标签泄漏进正文。
            try:
                comment = re.sub(r"^\s*[（(]\s*([A-Za-z_]+)\s*[）)]",
                                 lambda m: "(" + m.group(1).lower() + ")",
                                 comment, count=1)
            except Exception:
                pass

            def _try_load_vision_json(text):
                candidates = [text]
                candidates.append(text.replace('\\"', '"').replace("\\n", "\n").replace("\\/", "/"))
                for cand in candidates:
                    try:
                        data = json.loads(cand)
                        if isinstance(data, dict):
                            return data
                    except Exception:
                        pass
                m = re.search(r'\{.*\}', candidates[-1], re.DOTALL)
                if m:
                    try:
                        data = json.loads(m.group(0))
                        if isinstance(data, dict):
                            return data
                    except Exception:
                        pass
                return None

            data = _try_load_vision_json(raw_reply)
            self._last_glance_options = []
            if data:
                comment = (data.get("comment") or "").strip()
                spot = (data.get("spot") or "").strip()
                if glance:
                    try:
                        _opts = data.get("options") or []
                        _opts = [str(x).strip()[:8] for x in _opts if str(x).strip()]
                        self._last_glance_options = _opts[:2]
                    except Exception:
                        self._last_glance_options = []
                # 10/19：上面那次归一化作用在 raw_reply（整段 JSON）上，解析出的 comment 还得再来一次
                # —— 实测 15:23 那条就是以"（surprised）诶，大石头…"开头的。
                try:
                    comment = re.sub(r"^\s*[（(]\s*([A-Za-z_]+)\s*[）)]",
                                     lambda m: "(" + m.group(1).lower() + ")",
                                     comment, count=1)
                except Exception:
                    pass
            else:
                m = re.search(r'"comment"\s*:\s*"((?:[^"\\]|\\.)*)"', raw_reply, re.DOTALL)
                if m:
                    comment = m.group(1).replace('\\"', '"').replace("\\n", "\n").strip()

            # 10/24：模型偶尔会吐"元话语"——输出的是"我做了什么"而不是"要说的话"
            # （实测 13:29 那条："已按规则生成评论与事件标签"，还进了 TTS 和记忆）。
            # 这属于输出契约错误，不是风格问题 ⇒ 在这里直接当空回丢掉，不写记忆不出声。
            comment = _strip_meta_comment(comment)
            if not comment:
                return None
            if not look and not glance:
                # 10/27：极短定位标签，只给历史 user 侧用（不进 watch_log、不参与段总结）
                # 11/01：瞟一眼（glance）不写陪看会话 —— 否则她的随口一句会攒进段 buffer，
                # 之后凭空生成一条"陪看事件"，把闲聊污染成陪看记忆。
                # 11/02：预生成也走这条 —— spot 照样记（突变即开口时要写会话），但**不进段缓冲**，
                _sp = re.sub(r"[（(][^）)]*[）)]", "", spot or "").strip()
                _sp = re.sub(r"\s+", " ", _sp)[:14]
                self._watch_last_spot = _sp
                # 10/27：陪看锚点与段总结的原料改成**她自己的评论**（视觉模型不再另写画面摘要）
                self._watch_last_anchor = comment
                self._update_watch_session(comment)

            if not re.match(r'\(\w+\)', comment.strip()):
                comment = f"(normal) {comment}"
            return comment

        except Exception as e:
            log.error(f"视觉模型 API 失败: {e}")
            return None

    # ---------- 模式相关设置界面（陪玩陪看 + 陪读；主动话题已内置、不再可调）----------
    def open_mode_settings(self):
        """🎮 模式相关设置：定时话题、陪玩陪看、陪读（阅读）合成一个卡片窗。

        「最短沉默」管她最早多久能说一句，「最长沉默」到了必须说一句；
        实际检查周期 = 最短沉默 ÷ 2，上限 60 秒（见 start_watch_loop / ReadingCompanion）。
        陪玩陪看的两个秒数不设上限。陪读的截取区域只由「缩略图框选区域」决定（不再手填边距）。"""
        win, frame = self._make_card_window("模式相关设置", 470, 520)
        s = self._dpi_scale
        rc = self.reading_companion
        region = dict(rc.region)        # 陪读截取区域：框选改它，保存时写回

        # 底部按钮先 pack（布局铁律：内容变高时收尾按钮不被挤走）
        btn_frame = tk.Frame(frame, bg=DIALOG_BG)
        btn_frame.pack(side=tk.BOTTOM, pady=10)

        wmin_var = tk.StringVar(value=str(self.watch_min_interval))
        wmax_var = tk.StringVar(value=str(self.watch_max_silence))
        cap_var = tk.DoubleVar(value=rc.capture_interval)
        read_min_var = tk.IntVar(value=rc.min_interval)
        read_max_var = tk.IntVar(value=rc.max_silence)

        def save():
            try:
                w_min = int(wmin_var.get())
                w_max = int(wmax_var.get())
            except ValueError:
                messagebox.showwarning("输入错误", "请输入有效的整数")
                return
            if w_min < 5:
                messagebox.showwarning("输入错误", "最短沉默不能小于 5 秒")
                return
            if w_max <= w_min:
                messagebox.showwarning("输入错误", "最长沉默必须大于最短沉默")
                return
            try:
                read_cap = float(cap_var.get())
                read_min = int(read_min_var.get())
                read_max = int(read_max_var.get())
            except (ValueError, tk.TclError):
                messagebox.showwarning("输入错误", "陪读设置：请输入有效的数字")
                return
            # 陪玩陪看
            self.watch_min_interval = w_min
            self.watch_max_silence = w_max
            save_watch_config({"min_interval": w_min, "max_silence": w_max})
            # 陪读（阅读）
            rc.region.update(region)
            rc.capture_interval = read_cap
            rc.min_interval = read_min
            rc.max_silence = read_max
            rc.save_config()
            log.info("模式相关设置已保存：陪看 %d~%d 秒；陪读截图 %.1f 秒", w_min, w_max, read_cap)
            messagebox.showinfo("成功", "已保存：陪玩陪看 %d~%d 秒" % (w_min, w_max))
            win.destroy()

        RoundedButton(btn_frame, text="保存", command=save, width=int(120 * s), height=int(36 * s),
                      radius=int(6 * s), font=(self.font_family, 11)).pack(side=tk.LEFT, padx=3)

        def _num_row(label, var, unit, width=90):
            """一行「标签 + 圆角输入框 + 单位」（每行只放一对，防右边界裁切）"""
            row = tk.Frame(frame, bg=DIALOG_BG)
            row.pack(anchor='w', pady=3)
            tk.Label(row, text=label, font=(self.font_family, 11), fg=TEXT_MAIN,
                     bg=DIALOG_BG).pack(side=tk.LEFT)
            ent = RoundedEntry(row, textvariable=var, width=int(width * s), height=int(30 * s),
                               radius=int(8 * s), font=(self.font_family, 11), justify="center")
            ent.pack(side=tk.LEFT, padx=8)
            tk.Label(row, text=unit, font=(self.font_family, 10), fg=TEXT_SUB,
                     bg=DIALOG_BG).pack(side=tk.LEFT)
            return ent

        def _sep():
            tk.Frame(frame, height=max(1, int(s)), bg=CARD_BORDER).pack(fill=tk.X, pady=(10, 4))


        # ── 陪玩陪看 ──
        tk.Label(frame, text="陪玩陪看", font=(self.font_family, 12, "bold"), fg=TEXT_MAIN,
                 bg=DIALOG_BG).pack(anchor='w', pady=(2, 2))
        tk.Label(frame, text="距上次说话超过「最短沉默」之后，她才会考虑要不要说一句；\n"
                             "到了「最长沉默」还没说，就强制说一句。单位秒，没有上限。",
                 font=(self.font_family, 9), fg=TEXT_SUB, bg=DIALOG_BG,
                 justify='left').pack(anchor='w')
        wmin_entry = _num_row("最短沉默时间:", wmin_var, "秒")
        _num_row("最长沉默时间:", wmax_var, "秒")
        _sep()

        # ── 陪读（阅读）──
        tk.Label(frame, text="陪读（阅读）", font=(self.font_family, 12, "bold"), fg=TEXT_MAIN,
                 bg=DIALOG_BG).pack(anchor='w', pady=(2, 2))
        tk.Label(frame, text="截取区域：点「缩略图框选区域」在屏幕上框一块（会自动记下），\n"
                             "再用「预览当前区域」看框得对不对。时间单位都是秒。",
                 font=(self.font_family, 9), fg=TEXT_SUB, bg=DIALOG_BG,
                 justify='left').pack(anchor='w')

        def _hide_host():
            """框选时要让出屏幕：嵌在面板里就藏面板，独立卡片窗就藏卡片。"""
            try:
                cc = getattr(self, "_cc_win", None)
                if cc is not None and cc.winfo_exists():
                    cc.withdraw()
                    return "panel"
            except Exception:
                pass
            try:
                win.withdraw()
                return "card"
            except Exception:
                return None

        def _show_host(tag):
            try:
                if tag == "panel":
                    cc = getattr(self, "_cc_win", None)
                    if cc is not None and cc.winfo_exists():
                        cc.deiconify()
                        cc.lift()
                        return
            except Exception:
                pass
            try:
                win.deiconify()
            except Exception:
                pass

        def start_box_select():
            tag = _hide_host()      # 只藏一次：嵌在面板里就藏面板

            def on_region_selected(picked):
                _show_host(tag)
                if picked is None:
                    return
                for _k in ("left", "top", "width", "height"):
                    region[_k] = round(picked[_k], 4)
                preview_current()
            rc.select_region_interactive(callback=on_region_selected)

        def show_preview(reg):
            try:
                if not mss:
                    return
                with mss.MSS() as sct:
                    mon = sct.monitors[1]
                    l = int(mon["width"] * reg["left"])
                    t = int(mon["height"] * reg["top"])
                    w = int(mon["width"] * reg["width"])
                    h = int(mon["height"] * reg["height"])
                    cap = {"left": l, "top": t, "width": max(w, 1), "height": max(h, 1)}
                    img = sct.grab(cap)
                    pil_img = Image.frombytes("RGB", img.size, img.bgra, "raw", "BGRX")
            except Exception as e:
                messagebox.showerror("预览失败", str(e))
                return
            # 注意：设置页现在嵌在面板里，win 是 _EmbeddedCard 而不是控件，
            # 拿它当 master 会 AttributeError（预览按钮于是"没反应"）⇒ 一律挂到 root。
            preview_win = tk.Toplevel(self.root)
            preview_win.title("截取区域预览")
            try:
                preview_win.attributes("-topmost", True)
            except Exception:
                pass
            preview_win.configure(bg=DIALOG_BG)
            img_width, img_height = pil_img.size
            max_width = 400
            if img_width > max_width:
                ratio = max_width / img_width
                pil_img = pil_img.resize((max_width, int(img_height * ratio)), Image.LANCZOS)
            photo = ImageTk.PhotoImage(pil_img)
            lab = tk.Label(preview_win, image=photo, bg=DIALOG_BG)
            lab.image = photo
            lab.pack(padx=10, pady=10)
            try:
                preview_win.lift()
                preview_win.focus_force()
            except Exception:
                pass
            tk.Label(preview_win, text=f"区域大小：{w}x{h} 像素",
                     font=(self.font_family, 9), bg=DIALOG_BG).pack()

        def preview_current():
            show_preview(region)

        sel_row = tk.Frame(frame, bg=DIALOG_BG)
        sel_row.pack(anchor='w', pady=(6, 2))
        RoundedButton(sel_row, text="🖱️ 缩略图框选区域", command=start_box_select,
                      width=int(190 * s), height=int(32 * s), radius=int(6 * s),
                      font=(self.font_family, 10, "bold")).pack(side=tk.LEFT, padx=(0, 8))
        RoundedButton(sel_row, text="🔍 预览当前区域", command=preview_current, variant="subtle",
                      width=int(170 * s), height=int(32 * s), radius=int(6 * s),
                      font=(self.font_family, 10)).pack(side=tk.LEFT)
        _num_row("截图间隔:", cap_var, "秒", width=80)
        _num_row("最短沉默时间:", read_min_var, "秒", width=80)
        _num_row("最长沉默时间:", read_max_var, "秒", width=80)

        win.bind("<Return>", lambda e: save())
        wmin_entry.focus()

    # ---------- 读书伴侣 ----------
    def toggle_reading(self):
        if not self.reading_companion.enabled and self.sleep_mode:
            self.stop_sleep_mode(cause="reading")
        self.reading_companion.toggle()
        if self.reading_companion.enabled:
            if self.spine_enabled and self.spine:
                self.spine.enqueue(('test_motion', 'Action', 2))
            self.show_bubble_text("(happy) 让我看看你在读什么", "happy", status=True)
        else:
            if self.spine_enabled and self.spine:
                self.spine.enqueue(('test_motion', 'Action', 1))
            self.root.after(800, lambda: self.set_emotion("normal"))
            self.show_bubble_text("(shy) 有机会再一起读吧", "shy", status=True)
        label = "📖 陪我读书 (停止)" if self.reading_companion.enabled else "📖 陪我读书 (开始)"
        self._safe_menu_config(self.reading_menu_index, label, self.mode_menu)

    # ---------- 语音识别控制 ----------
    def _init_listen_badge(self):
        """「在听」小标记：免唤醒窗口开着时，在宠物头顶上方显示一个小胶囊。

        免唤醒窗口是不可见的，用户只能靠猜自己还在不在窗口里 —— 这个标记就是为了
        让他"一眼看出现在出声会不会被听到"。窗口关掉（0 秒）时永远不显示。"""
        try:
            s = self._dpi_scale
            w, h = int(78 * s), int(24 * s)
            win = tk.Toplevel(self.root)
            win.overrideredirect(True)
            win.configure(bg=CARD_MASK)
            if CARD_MASK:
                win.attributes("-transparentcolor", CARD_MASK)
            win.attributes("-topmost", True)
            cv = tk.Canvas(win, width=w, height=h, highlightthickness=0, bd=0, bg=CARD_MASK)
            cv.pack()
            self._badge_photo = _card_photo(w, h, max(6, int(11 * s)))
            cv.create_image(0, 0, anchor="nw", image=self._badge_photo)
            cv.create_text(w // 2, h // 2, text="🎤 在听", font=(self.font_family, int(9 * s)),
                           fill=TEXT_MAIN)
            win.withdraw()
            self._badge = win
            self._badge_visible = False
        except Exception as e:
            log.warning("「在听」标记创建失败: %s", e)
            self._badge = None
        # tick 单独起：调度失败不该把已建好的标记丢掉
        if self._badge is not None:
            try:
                self.root.after(250, self._badge_tick)
            except Exception:
                pass

    def _badge_tick(self):
        """每 0.25 秒同步一次标记的显隐与位置（只读 STT 的窗口状态，不碰渲染线程）"""
        try:
            if self._badge is not None:
                # 亮着 = 现在出声她真的能听到：语音开着 + 窗口没过期 + 她没在说话 + 也不是"等她想想"期间
                # （她 TTS 播放时麦克风整帧丢弃、气泡打字期间结果会被抗打断丢掉，
                #   这两种时候标记载亮着就是在骗人 —— 宁可灭掉；"嗯…让我想想"那段同理）
                listening = bool(self.voice_on and self.stt is not None
                                 and self.stt.window_left() > 0
                                 and not self._voice_output_busy()
                                 and not self._thinking_now())
                if listening != self._badge_visible:
                    self._badge_visible = listening
                    if listening:
                        self._badge.deiconify()
                        self._badge.lift()
                    else:
                        self._badge.withdraw()
                if listening:
                    bw = max(1, self._badge.winfo_width())
                    bh = max(1, self._badge.winfo_height())
                    x = self.root.winfo_rootx() + (self.root.winfo_width() - bw) // 2
                    y = self.root.winfo_rooty() - bh - int(4 * self._dpi_scale)
                    self._badge.geometry(f"+{x}+{max(0, y)}")
        except Exception:
            pass
        if not self._shutdown:
            self.root.after(250, self._badge_tick)

    def _ptt_pressed(self):
        """按键说话：那个键现在是否按着。

        用 GetAsyncKeyState 轮询而不是键盘钩子 —— 不需要管理员权限，也不管当前哪个
        窗口在前台（钩子要装钩子过程、还容易被别的程序抢走）。0x8000 位 = 当前按下。
        """
        if not self._ptt_enabled or not self._ptt_vk:
            return False
        try:
            return bool(ctypes.windll.user32.GetAsyncKeyState(int(self._ptt_vk)) & 0x8000)
        except Exception:
            return False

    def _init_voice_hotkey(self):
        self.root.after(60, self._ptt_tick)

    def _ptt_tick(self):
        """每 60ms 看一次按键：按着就把免唤醒窗口顶住（松开后 0.35 秒内自然失效）"""
        try:
            down = self._ptt_pressed()
            if down and self.voice_on and self.stt is not None:
                self.stt.hold_open()
            if down != self._ptt_down:
                self._ptt_down = down
                log.info("按键说话(%s): %s", self._ptt_name,
                         "按住 → 窗口打开" if down else "松开 → 窗口关闭")
        except Exception:
            pass
        if not self._shutdown:
            self.root.after(60, self._ptt_tick)

    def relaunch_as_admin(self):
        """以管理员身份重启自己：先起提权实例，1.5 秒后再退当前这个。

        游戏（暗区突围这类）以管理员运行时，普通权限进程读不到任何键盘输入；
        提权后 GetAsyncKeyState / Raw Input 都能恢复正常（11/18 实测 WeGame 前台）。
        """
        try:
            if getattr(sys, "frozen", False):
                exe, params = sys.executable, ""
                workdir = os.path.dirname(sys.executable)
            else:
                script = os.path.abspath(__file__)
                exe = sys.executable
                params = " ".join(['"%s"' % script] + ['"%s"' % a for a in sys.argv[1:]])
                workdir = os.path.dirname(script)
            se = ctypes.windll.shell32.ShellExecuteW
            se.restype = ctypes.c_void_p          # HINSTANCE：不设 restype 会被截成 32 位
            rc = int(se(None, "runas", exe, params or None, workdir, 1) or 0)
            if rc <= 32:
                # 1223 = 用户点了"否"，其余为 ShellExecute 错误码
                messagebox.showinfo("没有取得管理员权限",
                                    "UAC 被取消或启动失败（返回 %s）。\n"
                                    "游戏里要用按键说话的话，需要以管理员身份运行。" % rc)
                return
            log.info("已请求以管理员身份重启（ShellExecute 返回 %d），1.5 秒后退出当前实例", rc)
            self.root.after(1500, self.on_close)
        except Exception as e:
            log.warning("以管理员身份重启失败: %s", e)
            messagebox.showinfo("重启失败", str(e))

    def toggle_tts_speak(self):
        """🔊 语音朗读开关（TTS）：菜单在「🎮 模式」里，音色与语言在设置窗里选"""
        if not self.tts_enabled and self.tts_mode == "deepseek" and not getattr(self, "tts_deepseek_key", ""):
            self.root.after(0, lambda: messagebox.showwarning(
                "未配置 DeepSeek API Key", "DeepSeek TTS 用文本模型那把 DeepSeek key；\n"
                "如果文本模型不是 DeepSeek，请到 设置 → 语音 → DeepSeek 里单独填。"))
            return
        if not self.tts_enabled and self.tts_mode == "volc":
            if not self.tts_api_key:
                self.root.after(0, lambda: messagebox.showwarning(
                    "未配置 API Key", "请先在 设置 → API 密钥 → 声音复刻 API / Speaker ID 中配置"))
                return
            if not self.tts_speaker_id:
                self.root.after(0, lambda: messagebox.showwarning(
                    "未配置 Speaker ID", "请先在 设置 → API 密钥 → 声音复刻 API / Speaker ID 中配置"))
                return
        self.tts_enabled = not self.tts_enabled
        save_tts_config(enabled=self.tts_enabled)
        status = "开启" if self.tts_enabled else "关闭"
        self.show_bubble_text(f"(normal) 语音朗读已{status}", "normal", status=True)
        new_label = "🔊 语音朗读 (停止)" if self.tts_enabled else "🔊 语音朗读 (开始)"
        try:
            self.mode_menu.entryconfigure(self.tts_speak_menu_index, label=new_label)
        except Exception:
            pass
        log.info("语音朗读已%s", status)

    def toggle_voice(self, save=True, quiet=False):
        """开关语音识别。

        save=False 用于"不是用户选的动作"（自动睡眠、退出清理、开机/睡醒恢复）：
        那些关麦只是临时状态，不能把她自己的选择冲掉——退出时会关麦，但下次开机还要接着开。
        quiet=True 不弹气泡（睡醒时她已经在说"我眯了一会儿"了，别用气泡盖掉）。"""
        if not VOICE_AVAILABLE:
            messagebox.showwarning("缺少依赖", "语音识别需要安装 sherpa-onnx pyaudio numpy")
            return
        if self.stt is None or not self.stt.ready:
            messagebox.showwarning("还没有准备好", "语音模型还没有准备好，请稍候...")
            return
        if self.voice_on:
            self.stt.stop()
            self.stt.clear_window()      # 关语音顺手清窗口，免得下次打开时旧窗口还生效
            self.voice_on = False
            self._update_voice_menu_label()
            if not quiet:
                self.show_bubble_text("(normal) 语音识别已停止", "normal", status=True)
            log.info("语音识别已关闭")
        else:
            if self.sleep_mode:
                self.stop_sleep_mode(restore_voice=False, cause="voice")   # 开麦这条路上别再触发一次"睡醒恢复"
            self.stt.start()
            self.voice_on = True
            self._update_voice_menu_label()
            if not quiet:
                self.show_bubble_text("(happy) 我在听你说话", "happy", status=True)
            log.info("语音识别已开启")
        if save:
            self._voice_wanted = self.voice_on
            try:
                save_voice_config({"enabled": self.voice_on})   # 记住选择，下次开机沿用
            except Exception as e:
                log.debug(f"语音开关状态保存失败: {e}")

    def _restore_voice_if_wanted(self, quiet=False):
        """该开却没开就开回来（开机恢复、睡醒恢复共用）。返回是否真的开了。"""
        if self.voice_on or self.sleep_mode or not getattr(self, "_voice_wanted", False):
            return False
        stt = self.stt
        if stt is None or getattr(stt, "load_failed", False) or not getattr(stt, "ready", False):
            return False        # 模型还没就绪：交给开机那套轮询（_voice_restore_tick）去等
        log.info("恢复语音识别（按你上次的选择）")
        self.toggle_voice(save=False, quiet=quiet)
        return True

    def _voice_restore_tick(self):
        """开机恢复上次退出时的语音开关状态。

        语音模型要几十秒才 ready，菜单这时点了只会弹"还没准备好"，所以这里轮询等它；
        上次就是关着的话压根不会排这个 tick。"""
        if self._voice_restore_done:
            return
        stt = self.stt
        if stt is None or getattr(stt, "load_failed", False):
            self._voice_restore_done = True
            log.warning("语音状态恢复跳过：语音识别不可用")
            return
        if not stt.ready:
            self.root.after(500, self._voice_restore_tick)
            return
        self._voice_restore_done = True
        self._restore_voice_if_wanted()

    def _on_output_finished(self, refresh_voice=False, from_tts=False):
        """一轮输出完毕（气泡打字完成 / TTS 播完）。

        仅当该轮是对用户输入的回应时才刷新免唤醒词窗口——主动发言不刷新。
        **TTS 开着的时候只认"念完"那次**：气泡打完先不开窗（否则她还在念、窗口就先亮了，
        看着像"能说话"，其实麦克风正静音），等她念完由 TTS 那条路开窗；
        TTS 关着（或这轮根本念不出来）就按气泡打完开窗。
        """
        if not refresh_voice or self.stt is None:
            return
        if not from_tts and self._tts_will_play():
            return                      # 等她念完，TTS 结束那条路会开窗
        try:
            self.stt.refresh_window()
        except Exception:
            pass

    def _tts_will_play(self):
        """这轮回复是不是真会念出来（决定窗口在"气泡打完"还是"念完"时开）"""
        try:
            if not (self.tts_enabled and TTS_AVAILABLE):
                return False
            if self.tts_mode == "edge":
                return bool(EDGE_TTS_IMPORTED)
            if self.tts_mode == "deepseek":
                return bool(getattr(self, "tts_deepseek_key", ""))
            return bool(self.tts_api_key and self.tts_speaker_id)
        except Exception:
            return False

    def _voice_output_busy(self):
        """宠物是否正在输出（气泡打字中 / TTS 发声）——期间忽略语音输入，防误打断"""
        try:
            if self.bubble_window is not None and self.bubble_window.typing_job is not None:
                return True
        except Exception:
            pass
        try:
            if self.stt is not None and self.stt.muted:
                return True
        except Exception:
            pass
        return False

    def _tts_preview(self, provider, lang, voice=""):
        """试听：按当前选择合成一句样例并播放（不改配置、不写聊天）"""
        if not TTS_AVAILABLE:
            log.warning("试听失败：音频输出不可用")
            return
        text = TTS_PREVIEW_TEXT.get(lang, TTS_PREVIEW_TEXT["zh"])
        api_key, speaker_id = self.tts_api_key, self.tts_speaker_id

        def _run():
            if not self._tts_lock.acquire(timeout=1):
                log.warning("试听被跳过：上一条语音仍在播放")
                return
            temp_file = None
            try:
                if provider == "deepseek":
                    key = getattr(self, "tts_deepseek_key", "") or ""
                    if not key:
                        log.warning("试听失败：DeepSeek TTS 未配置 API Key")
                        return
                    with tempfile.NamedTemporaryFile(suffix=".wav", delete=False) as tf:
                        temp_file = tf.name
                    with requests.post(DEEPSEEK_TTS_URL,
                                       headers={"Authorization": "Bearer " + key},
                                       json={"text": text, "voice_id": voice or DEEPSEEK_TTS_VOICE_DEFAULT,
                                             "format": "wav", "filter_markdown": True},
                                       stream=True, timeout=(10, 120)) as r0:
                        if r0.status_code != 200:
                            log.error("试听失败（DeepSeek）: http=%s %s", r0.status_code,
                                      (r0.text or "")[:160].replace(chr(10), " "))
                            return
                        with open(temp_file, "wb") as fh0:
                            for chunk in r0.iter_content(chunk_size=16384):
                                if chunk:
                                    fh0.write(chunk)
                    self._fix_wav_header(temp_file)
                elif provider == "edge":
                    if not EDGE_TTS_IMPORTED:
                        log.warning("试听失败：edge-tts 不可用")
                        return
                    with tempfile.NamedTemporaryFile(suffix=".mp3", delete=False) as tf:
                        temp_file = tf.name
                    asyncio.run(edge_tts.Communicate(
                        text, voice or DEFAULT_EDGE_VOICE,
                        proxy=resolve_edge_proxy(self.tts_edge_proxy)).save(temp_file))
                else:
                    if not api_key or not speaker_id:
                        log.warning("试听失败：声音复刻的 API Key / Speaker ID 未配置")
                        return
                    payload = {
                        "app": {"cluster": resolve_volc_cluster(speaker_id, self.tts_volc_cluster)},
                        "user": {"uid": VOLC_TTS_UID},
                        "audio": {"voice_type": speaker_id, "encoding": "mp3", "speed_ratio": 1.0},
                        "request": {"reqid": str(uuid.uuid4()).replace("-", "")[:40],
                                    "text": text, "operation": "query"},
                    }
                    resp = requests.post(VOLC_TTS_URL,
                                         headers={"x-api-key": api_key,
                                                  "Content-Type": "application/json"},
                                         json=payload, timeout=30)
                    try:
                        data = resp.json()
                    except ValueError:          # 非 JSON（比如网关直接回 400）时别把正文丢了
                        data = {}
                    if resp.status_code != 200 or data.get("code") != 3000 or not data.get("data"):
                        log.error("试听失败: http=%s code=%s msg=%s body=%s", resp.status_code,
                                  data.get("code"), data.get("message"),
                                  (resp.text or "")[:200].replace("\n", " "))
                        return
                    with tempfile.NamedTemporaryFile(suffix=".mp3", delete=False) as tf:
                        tf.write(base64.b64decode(data["data"]))
                        temp_file = tf.name
                # 她开口前：把音乐压低当背景音（不停音乐、不记断点）；
                # 音量恢复统一放在 finally —— 她那边无论怎么退出（含异常），音乐都不会一直闷着
                self._music_duck_for_tts()
                # 播放期间静音语音识别，避免宠物“听见自己”触发识别
                if self.stt is not None and self.voice_on:
                    self.stt.set_muted(True)
                self._play_tts_file(temp_file)
                log.info("试听完成: provider=%s lang=%s", provider, lang)
            except Exception as e:
                log.error("试听出错: %s", e)
            finally:
                # 【锁必须一定放掉】见 _tts_play 里同款注释
                try:
                    if self._tts_channel is not None:
                        try:
                            self._tts_channel.stop()    # 超时提前退出时，别让她的声音漏到下一句
                        except Exception:
                            pass
                    # 无论她那边怎么退出，都把音乐音量淡回基准（读标志本身，不看局部变量）
                    self._music_finish_tts(self._music_duck is not None)
                    if self.stt is not None and self.voice_on:
                        self.stt.set_muted(False)
                    if temp_file and os.path.exists(temp_file):
                        try:
                            os.remove(temp_file)
                        except Exception:
                            pass
                except Exception as e:
                    log.warning("试听收尾出错（锁照常释放）: %s", e)
                finally:
                    self._tts_lock.release()

        threading.Thread(target=_run, daemon=True).start()

    def open_tts_settings(self):
        """🎧 TTS 音色与语言：火山声音复刻 / Edge 两档分页设置"""
        win, frame = self._make_card_window("TTS 音色与语言", 470, 500)
        s = self._dpi_scale
        st = {"mode": self.tts_mode, "volc_lang": self.tts_volc_lang,
              "edge_lang": self.tts_edge_lang, "edge_voice": self.tts_edge_voice,
              "deepseek_voice": getattr(self, "tts_deepseek_voice", DEEPSEEK_TTS_VOICE_DEFAULT),
              "deepseek_lang": getattr(self, "tts_deepseek_lang", "zh")}

        # 底部按钮先 pack（内容变高时收尾按钮不被挤走）
        btn_frame = tk.Frame(frame, bg=DIALOG_BG)
        btn_frame.pack(side=tk.BOTTOM, pady=10)

        def save():
            if st["mode"] == "volc" and not (self.tts_api_key and self.tts_speaker_id):
                messagebox.showwarning("未配置声音复刻",
                                       "现在选的是火山声音复刻，但 API Key / Speaker ID 还没填。\n"
                                       "请先在 设置 → API 密钥 → 声音复刻 API / Speaker ID 里配置。")
                return
            try:
                save_tts_config(enabled=self.tts_enabled, mode=st["mode"], volc_lang=st["volc_lang"],
                                edge_lang=st["edge_lang"], edge_voice=st["edge_voice"],
                                deepseek_voice=st["deepseek_voice"],
                                deepseek_lang=st["deepseek_lang"])
            except Exception as e:
                log.warning("保存 TTS 设置失败: %s", e)
            self.tts_mode = st["mode"]
            self.tts_volc_lang = st["volc_lang"]
            self.tts_edge_lang = st["edge_lang"]
            self.tts_edge_voice = st["edge_voice"]
            self.tts_deepseek_voice = st["deepseek_voice"]
            self.tts_deepseek_lang = st["deepseek_lang"]
            refresh_cur()
            if st["mode"] == "deepseek":
                _v = next((n for v, n in DEEPSEEK_TTS_VOICES if v == st["deepseek_voice"]),
                          st["deepseek_voice"])
                messagebox.showinfo("成功", "TTS 设置已保存\n当前使用：DeepSeek 原生 · %s · %s" %
                                    (_v, TTS_LANG_NAMES.get(st["deepseek_lang"], "中文")))
            else:
                lang_now = st["volc_lang"] if st["mode"] == "volc" else st["edge_lang"]
                messagebox.showinfo("成功", "TTS 设置已保存\n当前使用：%s · %s" %
                                    ("声音复刻" if st["mode"] == "volc" else "Edge", TTS_LANG_NAMES[lang_now]))
            win.destroy()

        RoundedButton(btn_frame, text="保存", command=save, width=int(120 * s), height=int(36 * s),
                      radius=int(6 * s), font=(self.font_family, 11)).pack(side=tk.LEFT, padx=3)

        # ---------- 顶部：当前生效的那一档（醒目）----------
        cur_box = tk.Frame(frame, bg=DIALOG_BG, highlightbackground=CARD_BORDER_STRONG,
                           highlightcolor=CARD_BORDER_STRONG, highlightthickness=max(1, int(1.5 * s)))
        cur_box.pack(fill=tk.X, pady=(2, 8))
        cur_in = tk.Frame(cur_box, bg=DIALOG_BG)
        cur_in.pack(fill=tk.X, padx=int(10 * s), pady=int(8 * s))
        tk.Label(cur_in, text="当前使用", font=(self.font_family, 9), fg=TEXT_SUB,
                 bg=DIALOG_BG).pack(anchor='w')
        cur_label = tk.Label(cur_in, text="", font=(self.font_family, 13, "bold"),
                             fg=BTN_PRIMARY, bg=DIALOG_BG)
        cur_label.pack(anchor='w')

        # ---------- 页签 ----------
        tab_row = tk.Frame(frame, bg=DIALOG_BG)
        tab_row.pack(anchor='w', pady=(0, 6))
        tab_btns = {}
        page = tk.Frame(frame, bg=DIALOG_BG)
        page.pack(fill=tk.BOTH, expand=True)

        def refresh_cur():
            if self.tts_mode == "volc":
                desc = "🔥 火山声音复刻 · %s" % TTS_LANG_NAMES.get(self.tts_volc_lang, "中文")
                if not (self.tts_api_key and self.tts_speaker_id):
                    desc += "（未配置 API Key / Speaker ID）"
            elif self.tts_mode == "deepseek":
                vname = next((n for v, n in DEEPSEEK_TTS_VOICES
                              if v == st["deepseek_voice"]), st["deepseek_voice"])
                desc = "🀄 DeepSeek 原生 TTS · %s · %s" % (
                    TTS_LANG_NAMES.get(st["deepseek_lang"], "中文"), vname)
                if not (getattr(self, "tts_deepseek_key", "") or ""):
                    desc += "（未配置 API Key）"
            else:
                vname = next((n for n, v in EDGE_VOICE_TABLE.get(self.tts_edge_lang, [])
                              if v == self.tts_edge_voice), self.tts_edge_voice)
                desc = "🎧 Edge TTS · %s · %s" % (TTS_LANG_NAMES.get(self.tts_edge_lang, "中文"), vname)
            cur_label.config(text=desc)
            for k, b in tab_btns.items():
                try:
                    b.set_variant("primary" if k == st["mode"] else "subtle")
                except Exception:
                    pass

        def lang_row(parent, codes, cur, on_pick):
            row = tk.Frame(parent, bg=DIALOG_BG)
            row.pack(anchor='w')
            for code in codes:
                RoundedButton(row, text=TTS_LANG_NAMES[code], width=int(62 * s), height=int(30 * s),
                              radius=int(8 * s), font=(self.font_family, 10),
                              variant="primary" if code == cur() else "subtle",
                              command=lambda c=code: on_pick(c)).pack(side=tk.LEFT, padx=(0, 6))

        def build_page(kind):
            for w in page.winfo_children():
                w.destroy()

            def pick(c):
                if kind == "volc":
                    st["volc_lang"] = c
                elif kind == "deepseek":
                    st["deepseek_lang"] = c
                else:
                    st["edge_lang"] = c
                    if not edge_voice_valid(c, st["edge_voice"]):
                        st["edge_voice"] = EDGE_VOICE_DEFAULT.get(c) or EDGE_VOICE_TABLE[c][0][1]
                build_page(kind)

            tk.Label(page, text="语言", font=(self.font_family, 11, "bold"), fg=TEXT_MAIN,
                     bg=DIALOG_BG).pack(anchor='w', pady=(4, 2))
            if kind == "volc":
                lang_row(page, ("zh", "en", "ja"), lambda: st["volc_lang"], pick)
                tip = "非中文时，她会把要说的话翻译成该语言再念（气泡和聊天记录仍是中文）。"
            elif kind == "deepseek":
                lang_row(page, ("zh", "en", "ja"), lambda: st["deepseek_lang"], pick)
                tip = "非中文时，她会把要说的话翻译成该语言再念（气泡和聊天记录仍是中文）。"
            else:
                lang_row(page, ("zh", "en"), lambda: st["edge_lang"], pick)
                tip = "选英文时先翻译成英文再用英文音色念；翻译失败会退回中文音色念原文。"
            tk.Label(page, text=tip, font=(self.font_family, 9), fg=TEXT_SUB, bg=DIALOG_BG,
                     justify='left', wraplength=int(400 * s)).pack(anchor='w', pady=(6, 0))

            tk.Frame(page, bg=CARD_BORDER, height=1).pack(fill=tk.X, pady=8)
            tk.Label(page, text="音色", font=(self.font_family, 11, "bold"), fg=TEXT_MAIN,
                     bg=DIALOG_BG).pack(anchor='w', pady=(0, 2))
            if kind == "deepseek":
                vrow = tk.Frame(page, bg=DIALOG_BG)
                vrow.pack(anchor='w', pady=(2, 0))
                for vid, vname in DEEPSEEK_TTS_VOICES:
                    RoundedButton(vrow, text=vname, width=int(130 * s), height=int(30 * s),
                                  radius=int(8 * s), font=(self.font_family, 10),
                                  variant="primary" if vid == st["deepseek_voice"] else "subtle",
                                  command=lambda v=vid: (st.__setitem__("deepseek_voice", v),
                                                         build_page("deepseek"))
                                  ).pack(side=tk.LEFT, padx=(0, 6))
                _key = getattr(self, "tts_deepseek_key", "") or ""
                tk.Label(page, text=("API Key：已就绪（%s…）" % _key[:6]) if _key else
                         "API Key：未配置 —— 文本模型是 DeepSeek 时会自动复用它的 key",
                         font=(self.font_family, 9), fg=TEXT_SUB, bg=DIALOG_BG,
                         justify='left').pack(anchor='w', pady=(6, 2))
                tk.Label(page, text="计费约 ¥0.042/句（≤70 汉字），限时 5 折约 ¥0.021。没有声音复刻。",
                         font=(self.font_family, 9), fg=TEXT_SUB, bg=DIALOG_BG,
                         justify='left', wraplength=int(400 * s)).pack(anchor='w')
            elif kind == "volc":
                sid = self.tts_speaker_id
                shown = (sid[:4] + "…" + sid[-2:]) if sid else "未配置"
                tk.Label(page, text="声音复刻音色：%s\n（音色属于你的账号，在 API 密钥里换）" % shown,
                         font=(self.font_family, 9), fg=TEXT_SUB, bg=DIALOG_BG,
                         justify='left').pack(anchor='w', pady=(2, 4))
                RoundedButton(page, text="去配置 API / 音色", command=self.set_tts_api_and_speaker,
                              width=int(160 * s), height=int(30 * s), radius=int(8 * s),
                              font=(self.font_family, 10)).pack(anchor='w')
            else:
                vrow = tk.Frame(page, bg=DIALOG_BG)
                vrow.pack(anchor='w', pady=(2, 0))
                for name, vid in EDGE_VOICE_TABLE[st["edge_lang"]]:
                    RoundedButton(vrow, text=name, width=int(80 * s), height=int(30 * s),
                                  radius=int(8 * s), font=(self.font_family, 10),
                                  variant="primary" if vid == st["edge_voice"] else "subtle",
                                  command=lambda v=vid: (st.__setitem__("edge_voice", v),
                                                         build_page("edge"))
                                  ).pack(side=tk.LEFT, padx=(0, 6))

            tk.Frame(page, bg=CARD_BORDER, height=1).pack(fill=tk.X, pady=8)
            if kind == "deepseek":
                _pv = lambda: self._tts_preview("deepseek", st["deepseek_lang"], st["deepseek_voice"])
            elif kind == "volc":
                _pv = lambda: self._tts_preview("volc", st["volc_lang"])
            else:
                _pv = lambda: self._tts_preview("edge", st["edge_lang"], st["edge_voice"])
            RoundedButton(page, text="▶ 试听", command=_pv,
                          width=int(96 * s), height=int(32 * s), radius=int(8 * s),
                          font=(self.font_family, 10), variant="primary").pack(anchor='w')

        def set_mode(kind):
            if kind == "deepseek" and not (getattr(self, "tts_deepseek_key", "") or ""):
                messagebox.showwarning("未配置 DeepSeek API Key",
                                       "DeepSeek 原生 TTS 需要 DeepSeek 的 API Key。\n"
                                       "文本模型是 DeepSeek 时会自动复用；否则要先在 API 密钥里配好。")
            if kind == "volc" and not (self.tts_api_key and self.tts_speaker_id):
                messagebox.showwarning("未配置声音复刻",
                                       "火山区还没配置 API Key / Speaker ID，选了也不会出声。\n"
                                       "可以先点下面「去配置 API / 音色」填好。")
            st["mode"] = kind
            build_page(kind)
            refresh_cur()

        for kind, label in (("volc", "🔥 火山声音复刻"), ("edge", "🎧 Edge TTS"),
                            ("deepseek", "🀄 DeepSeek 原生")):
            b = RoundedButton(tab_row, text=label, width=int(150 * s), height=int(34 * s),
                              radius=int(8 * s), font=(self.font_family, 10),
                              command=lambda k=kind: set_mode(k))
            b.pack(side=tk.LEFT, padx=(0, 8))
            tab_btns[kind] = b

        build_page(st["mode"])
        refresh_cur()
        return win, frame

    # ---------- 控制中心（主界面：左侧选项 / 右侧详情） ----------
    def _make_panel_window(self, title, w, h, topmost=False, resizable=True):
        """非模态面板窗：与卡片窗同风格，但**不 grab_set**（能点别处、能和她互动）。"""
        s = self._dpi_scale
        W, H = int(w * s), int(h * s)
        win = tk.Toplevel(self.root)
        win.overrideredirect(True)
        win.configure(bg=CARD_MASK)
        win.attributes("-transparentcolor", CARD_MASK)
        win.attributes("-topmost", bool(topmost))
        canvas = tk.Canvas(win, width=W, height=H, highlightthickness=0, bd=0, bg=CARD_MASK)
        canvas.pack()
        if not hasattr(self, "_card_photos"):
            self._card_photos = []
        self._card_photos.append(_card_photo(W, H, max(8, int(12 * s))))
        bg_item = canvas.create_image(0, 0, anchor="nw", image=self._card_photos[-1])
        x = max(8, min(self.root.winfo_rootx() - W - int(16 * s), self._screen_w - W - 8))
        y = max(8, min(self.root.winfo_rooty(), self._screen_h - H - 8))
        win.geometry(f"+{x}+{y}")
        try:
            win.lift()
            win.focus_force()
        except Exception:
            pass
        title_h = int(44 * s)
        hit = canvas.create_rectangle(0, 0, W, title_h, fill=CARD_BG, outline="")
        canvas.tag_lower(hit)
        title_id = canvas.create_text(int(18 * s), title_h // 2, anchor="w", text=title,
                                      font=(self.font_family, 11, "bold"), fill=TEXT_MAIN)
        # 拖动缩放时盖一层实色（PIL 重绘太贵），避免旧底图残留造成重影
        flat_id = canvas.create_rectangle(0, 0, W, H, fill=CARD_BG, outline="", state="hidden")
        close_id = canvas.create_text(W - int(18 * s), title_h // 2, text="✕",
                                      font=(self.font_family, 12), fill=TEXT_SUB)
        canvas.tag_bind(close_id, "<Enter>", lambda e: canvas.itemconfigure(close_id, fill=DANGER_RED))
        canvas.tag_bind(close_id, "<Leave>", lambda e: canvas.itemconfigure(close_id, fill=TEXT_SUB))
        canvas.tag_bind(close_id, "<Button-1>", lambda e: win.destroy())

        # 📌 置顶开关：默认跟着 topmost 参数，点一下切换（不置顶时也保证点一下就浮上来）
        pin = {"on": bool(topmost)}

        def _paint_pin():
            canvas.itemconfigure(pin_id, fill=(BTN_PRIMARY if pin["on"] else TEXT_SUB))

        def _toggle_pin(e=None):
            pin["on"] = not pin["on"]
            try:
                win.attributes("-topmost", pin["on"])
            except Exception:
                pass
            if pin["on"]:
                try:
                    win.lift()
                except Exception:
                    pass
            _paint_pin()

        pin_id = canvas.create_text(W - int(44 * s), title_h // 2, text="📌",
                                    font=(self.font_family, 11), fill=TEXT_SUB)
        canvas.tag_bind(pin_id, "<Button-1>", _toggle_pin)
        _paint_pin()
        # 不置顶时，点窗口任意处先把自己抬到最前
        win.bind("<ButtonPress-1>", lambda e: win.lift(), add="+")
        drag = {"dx": 0, "dy": 0, "active": False}

        def _drag_start(e):
            if e.widget is not canvas or e.y > title_h:
                return
            drag["dx"] = e.x_root - win.winfo_x()
            drag["dy"] = e.y_root - win.winfo_y()
            drag["active"] = True

        def _drag_move(e):
            if drag["active"]:
                win.geometry(f"+{e.x_root - drag['dx']}+{e.y_root - drag['dy']}")

        def _drag_end(e):
            drag["active"] = False

        win.bind("<ButtonPress-1>", _drag_start)
        win.bind("<B1-Motion>", _drag_move)
        win.bind("<ButtonRelease-1>", _drag_end)
        win.bind("<Escape>", lambda e: win.destroy())
        pad = int(16 * s)
        content = tk.Frame(canvas, bg=CARD_BG)
        content_win = canvas.create_window(pad, title_h, anchor="nw", window=content,
                                           width=W - 2 * pad, height=H - title_h - int(10 * s))
        if not hasattr(self, "_open_cards"):
            self._open_cards = set()
        self._open_cards.add(win)
        win.bind("<Destroy>", lambda e: self._open_cards.discard(win), add="+")
        def _layout(nw, nh, dragging=False):
            """按新尺寸重排标题栏/内容区；dragging=True 跳过 PIL 重绘（只用实色底板）。"""
            try:
                canvas.config(width=nw, height=nh)
                canvas.coords(hit, 0, 0, nw, title_h)
                canvas.coords(title_id, int(18 * s), title_h // 2)
                canvas.coords(close_id, nw - int(18 * s), title_h // 2)
                canvas.coords(pin_id, nw - int(44 * s), title_h // 2)
                canvas.coords(content_win, pad, title_h)
                canvas.itemconfigure(content_win, width=max(50, nw - 2 * pad),
                                     height=max(50, nh - title_h - int(10 * s)))
                if dragging:
                    canvas.itemconfigure(bg_item, state="hidden")
                    canvas.coords(flat_id, 0, 0, nw, nh)
                    canvas.itemconfigure(flat_id, state="normal")
                    for _it in (flat_id, hit):
                        canvas.tag_lower(_it)
                else:
                    self._card_photos.append(_card_photo(nw, nh, max(8, int(12 * s))))
                    canvas.itemconfigure(bg_item, image=self._card_photos[-1])
                    canvas.itemconfigure(bg_item, state="normal")
                    canvas.itemconfigure(flat_id, state="hidden")
                    for _it in (bg_item, flat_id, hit):
                        canvas.tag_lower(_it)
            except Exception as e:
                log.debug("面板重排失败: %s", e)

        if resizable:
            self._install_panel_resize(win, canvas, content_win, title_h, pad, W, H, _layout)
        return win, content


    def _install_panel_resize(self, win, canvas, content_win, title_h, pad, W0, H0, layout):
        """给无边框面板装"拖边缩放"（系统边框被 overrideredirect 去掉，只能自己做命中）。

        命中：距四条边 ≤6px 算边框，两角同时命中两条边 ⇒ 斜向缩放；
        标题栏空白处仍走拖动，两者互不干扰。
        说明（11/11）：试过"橡皮筋示意框"，观感太抽象，已回退成**实时缩放**；
        拉伸期间临时关掉颜色键透明，避免旧轮廓残留的重影。
        """
        s = self._dpi_scale
        M = max(4, int(6 * s))
        MIN_W, MIN_H = int(620 * s), int(430 * s)
        st = {"mode": None, "dir": "", "x": 0, "y": 0, "w": 0, "h": 0, "wx": 0, "wy": 0}
        cur = {"name": ""}

        def _dir_at(x, y, w, h):
            d = ""
            if y <= M:
                d += "n"
            elif y >= h - M:
                d += "s"
            if x <= M:
                d += "w"
            elif x >= w - M:
                d += "e"
            return d

        _CURSOR = {"n": "size_ns", "s": "size_ns", "e": "size_we", "w": "size_we",
                   "nw": "size_nwse", "se": "size_nwse", "ne": "size_nesw", "sw": "size_nesw"}

        def _motion(e):
            if st["mode"] or e.widget is not canvas:
                return
            name = _CURSOR.get(_dir_at(e.x, e.y, canvas.winfo_width(), canvas.winfo_height()), "")
            if name != cur["name"]:
                cur["name"] = name
                try:
                    canvas.config(cursor=name)
                except Exception:
                    pass

        def _press(e):
            if e.widget is not canvas:
                return
            d = _dir_at(e.x, e.y, canvas.winfo_width(), canvas.winfo_height())
            if not d:
                return
            st.update(mode="resize", dir=d, x=e.x_root, y=e.y_root,
                      w=win.winfo_width(), h=win.winfo_height(),
                      wx=win.winfo_x(), wy=win.winfo_y())
            # 拉伸期间关掉颜色键透明：色键窗口的挖角是异步重算的，
            # 每帧改尺寸时旧轮廓还留在屏幕上（这就是缩放时看到的重影）。
            try:
                win.attributes("-transparentcolor", "")
                win.configure(bg=CARD_BG)
                canvas.configure(bg=CARD_BG)
            except Exception:
                pass

        def _apply_motion(e):
            if st["mode"] != "resize":
                return
            dx, dy = e.x_root - st["x"], e.y_root - st["y"]
            w, h, x, y = st["w"], st["h"], st["wx"], st["wy"]
            if "e" in st["dir"]:
                w += dx
            if "s" in st["dir"]:
                h += dy
            if "w" in st["dir"]:
                w -= dx
                x += dx
            if "n" in st["dir"]:
                h -= dy
                y += dy
            if w < MIN_W:
                if "w" in st["dir"]:
                    x -= (MIN_W - w)
                w = MIN_W
            if h < MIN_H:
                if "n" in st["dir"]:
                    y -= (MIN_H - h)
                h = MIN_H
            win.geometry("%dx%d+%d+%d" % (w, h, x, y))
            layout(w, h, dragging=True)
            try:
                canvas.update_idletasks()
            except Exception:
                pass

        def _release(e):
            if st["mode"] != "resize":
                return
            st["mode"] = None
            layout(win.winfo_width(), win.winfo_height(), dragging=False)
            try:
                canvas.configure(bg=CARD_MASK)
                win.configure(bg=CARD_MASK)
                win.attributes("-transparentcolor", CARD_MASK)
                canvas.update_idletasks()
                win.lift()
            except Exception:
                pass

        canvas.bind("<Motion>", _motion)
        win.bind("<ButtonPress-1>", _press, add="+")
        win.bind("<B1-Motion>", _apply_motion, add="+")
        win.bind("<ButtonRelease-1>", _release, add="+")

    def open_control_center(self):
        """打开控制中心：左边选项（可折叠分组），右边详情（当前是聊天/历史）。"""
        try:
            if getattr(self, "_cc_win", None) is not None and self._cc_win.winfo_exists():
                self._cc_win.deiconify()
                self._cc_win.lift()
                try:
                    self._cc_input.focus_set()
                except Exception:
                    pass
                return
        except Exception:
            pass
        s = self._dpi_scale
        # 重开面板前先把旧的定时刷新停掉，避免叠出多个 after
        try:
            if getattr(self, "_cc_tick_job", None):
                self.root.after_cancel(self._cc_tick_job)
        except Exception:
            pass
        self._cc_tick_job = None
        win, frame = self._make_panel_window("%s · 面板" % self.pet_name, 1000, 680, topmost=True)
        self._cc_win = win
        self._cc_pages = {}
        self._cc_group_open = {}

        body = tk.Frame(frame, bg=CARD_BG)
        body.pack(fill=tk.BOTH, expand=True)

        # 左侧选项栏（固定宽度，内容可滚动）
        side_w = int(196 * s)
        side_outer = tk.Frame(body, bg="#f7f8fa", width=side_w)
        side_outer.pack(side=tk.LEFT, fill=tk.Y)
        side_outer.pack_propagate(False)
        side_cvs = tk.Canvas(side_outer, bg="#f7f8fa", highlightthickness=0, width=side_w)
        side_vsb = ttk.Scrollbar(side_outer, orient="vertical", command=side_cvs.yview)
        side_inner = tk.Frame(side_cvs, bg="#f7f8fa")
        side_inner.bind("<Configure>", lambda e: side_cvs.configure(scrollregion=side_cvs.bbox("all")))
        side_cvs.create_window((0, 0), window=side_inner, anchor="nw",
                               width=side_w - int(6 * s))
        side_cvs.configure(yscrollcommand=side_vsb.set)
        side_cvs.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        side_vsb.pack(side=tk.RIGHT, fill=tk.Y)

        # 右侧内容宿主：所有页面都常驻，切换只 tkraise（聊天记录不会因切换而丢）
        host = tk.Frame(body, bg=CARD_BG)
        host.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(int(10 * s), 0))
        self._cc_host = host

        def _sep():
            tk.Frame(side_inner, bg=DIVIDER, height=1).pack(fill=tk.X, pady=(int(6 * s), int(4 * s)))

        def _group_header(text, key):
            row = tk.Frame(side_inner, bg="#f7f8fa")
            row.pack(fill=tk.X)
            lbl = tk.Label(row, text="▸ " + text, anchor="w", font=(self.font_family, 10, "bold"),
                           fg=TEXT_SUB, bg="#f7f8fa", cursor="hand2")
            lbl.pack(fill=tk.X, padx=int(10 * s), pady=int(5 * s))
            holder = tk.Frame(side_inner, bg="#f7f8fa")
            state = {"open": False}

            def _toggle(event=None):
                state["open"] = not state["open"]
                lbl.config(text=("▾ " if state["open"] else "▸ ") + text)
                if state["open"]:
                    holder.pack(fill=tk.X, after=row)
                else:
                    holder.pack_forget()

            lbl.bind("<Button-1>", _toggle)
            self._cc_group_open[key] = state
            return holder

        def _item(holder, text, command, page=None):
            row = tk.Frame(holder, bg="#f7f8fa")
            row.pack(fill=tk.X)
            lbl = tk.Label(row, text="   " + text, anchor="w", font=(self.font_family, 10),
                           fg=TEXT_MAIN, bg="#f7f8fa", cursor="hand2")
            lbl.pack(fill=tk.X, padx=int(8 * s), pady=int(4 * s))

            def _enter(e):
                lbl.config(bg=HOVER_BG); row.config(bg=HOVER_BG)

            def _leave(e):
                lbl.config(bg="#f7f8fa"); row.config(bg="#f7f8fa")

            def _click(e):
                try:
                    if page:
                        self._cc_show_page(page)
                    elif command:
                        command()
                    self._cc_refresh_sidebar()
                except Exception as ex:
                    log.warning("面板选项执行失败: %s", ex)

            lbl.bind("<Enter>", _enter)
            lbl.bind("<Leave>", _leave)
            lbl.bind("<Button-1>", _click)
            return lbl

        # ── 聊天（置顶，不进折叠组）──
        _item(side_inner, "💬 聊天记录", None, page="chat")
        _sep()

        # ── 模式 ──
        h = _group_header("模式", "mode")
        _item(h, "🎮 陪玩模式 (开始)", self.toggle_watch_mode)
        _item(h, "📖 陪我读书", self.toggle_reading)
        _item(h, "🎤 语音识别", self.toggle_voice)
        _item(h, "🔊 说话", self.toggle_tts_speak)
        _sep()

        # ── 快捷 ──
        h = _group_header("快捷", "quick")
        _item(h, "🐟 形象", lambda: self._cc_open_embed("set_form", "形象", self._open_form_window))
        _item(h, "🎩 装扮", lambda: self._cc_open_embed("set_costume", "装扮", self._open_costume_window))
        _item(h, "💬 换个话题", self.generate_topic_manual)
        _item(h, "💤 睡觉", lambda: self.start_sleep_mode(manual=True))
        _item(h, "⚡ 精力值", self.show_energy_status)
        _item(h, "⌨️ 显示/隐藏输入框", self.toggle_input_frame)
        _sep()

        # ── 设置（先"跳转"：点开原独立窗口）──
        h = _group_header("设置", "settings")
        for text, cmd, _key in (
                ("系统提示词与角色", self.open_settings, "set_prompt"),
                ("用户档案", self.open_user_profile, "set_profile"),
                ("文本模型", self.set_text_model_settings, "set_llm_text"),
                ("视觉模型", self.set_vision_model_settings, "set_llm_vision"),
                ("TTS API / Speaker", self.set_tts_api_and_speaker, "set_tts_api"),
                ("缩放", self.open_zoom_settings, "set_zoom"),
                ("模式相关", self.open_mode_settings, "set_mode"),
                ("音乐库", self.open_music_library_settings, "set_music"),
                ("语音识别", self.open_voice_settings, "set_voice"),
                ("TTS 音色与语言", self.open_tts_settings, "set_tts"),
                ("DSH 协作", self.open_dsh_settings, "set_dsh"),
                ("导出故障报告", self.export_fault_report, None),
                ("关于", None, "about")):
            if _key is None:
                _item(h, text, cmd)
            elif cmd is None:
                _item(h, text, None, page=_key)
            else:
                _item(h, text, (lambda c=cmd, k=_key, t=text: self._cc_open_embed(k, t, c)))
        _sep()

        # ── 记录 ──
        h = _group_header("记录", "record")
        _item(h, "📌 记忆锚点",
              (lambda: self._cc_open_embed("set_memory", "记忆锚点管理", self.open_memory_manager)))
        _sep()

        _item(side_inner, "退出", self.on_close)

        self._cc_embed_target = None
        # 页面：聊天（陪玩/陪读已并入同一条时间线）
        self._cc_build_chat(host)
        self._cc_build_about(host)
        self._cc_show_page("chat")

        # 状态栏（底部一行，随模式变化）
        self._cc_status = tk.Label(frame, text="", anchor="w", font=(self.font_family, 9),
                                   fg=TEXT_SUB, bg=CARD_BG)
        self._cc_status.pack(fill=tk.X, pady=(int(4 * s), 0))
        self._cc_refresh_sidebar()
        # 每 2 秒刷一次：精力会自然衰减，陪玩/语音也可能在别处被切换
        self._cc_tick()

    def _cc_embed_card(self, host, title):
        """把卡片窗的内容建到面板右侧页面里（配合 `_EmbeddedCard`）。"""
        s = self._dpi_scale
        for w in host.winfo_children():
            try:
                w.destroy()
            except Exception:
                pass
        head = tk.Frame(host, bg=CARD_BG)
        head.pack(fill=tk.X, pady=(0, int(6 * s)))
        tk.Label(head, text=title, font=(self.font_family, 11, "bold"),
                 fg=TEXT_MAIN, bg=CARD_BG).pack(side=tk.LEFT)
        body = tk.Frame(host, bg=CARD_BG)
        body.pack(fill=tk.BOTH, expand=True)

        def _on_close():
            self._cc_close_embed(host)

        return _EmbeddedCard(body, _on_close), body

    def _cc_close_embed(self, host):
        """嵌入式对话框点"关闭/取消"后：清空该页并回到聊天。"""
        try:
            for w in host.winfo_children():
                w.destroy()
            tk.Label(host, text="（已关闭，请从左侧再选一项）", font=(self.font_family, 9),
                     fg=TEXT_SUB, bg=CARD_BG).pack(pady=int(20 * self._dpi_scale))
        except Exception:
            pass

    def _cc_make_embed_page(self, key):
        """为某个设置项建一个可滚动的内容页（延迟创建，只建一次）。"""
        s = self._dpi_scale
        page = tk.Frame(self._cc_host, bg=CARD_BG)
        page.place(relx=0, rely=0, relwidth=1, relheight=1)
        cvs = tk.Canvas(page, bg=CARD_BG, highlightthickness=0)
        vsb = ttk.Scrollbar(page, orient="vertical", command=cvs.yview)
        inner = tk.Frame(cvs, bg=CARD_BG)
        inner.bind("<Configure>", lambda e: cvs.configure(scrollregion=cvs.bbox("all")))
        win_id = cvs.create_window((int(6 * s), 0), window=inner, anchor="nw")
        cvs.bind("<Configure>", lambda e: cvs.itemconfigure(win_id, width=max(50, e.width - int(12 * s))))
        cvs.configure(yscrollcommand=vsb.set)
        cvs.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        vsb.pack(side=tk.RIGHT, fill=tk.Y)

        def _wheel(e):
            try:
                cvs.yview_scroll(int(-1 * (e.delta / 120)), "units")
            except Exception:
                pass
        cvs.bind("<Enter>", lambda e: cvs.bind_all("<MouseWheel>", _wheel))
        cvs.bind("<Leave>", lambda e: cvs.unbind_all("<MouseWheel>"))
        page._cc_inner = inner
        page._cc_canvas = cvs
        self._cc_pages[key] = page
        return page

    def _cc_open_embed(self, key, title, opener):
        """在右侧打开一个设置页（把原来的对话框函数原样跑一遍，内容落在页面里）。"""
        page = self._cc_pages.get(key) or self._cc_make_embed_page(key)
        inner = page._cc_inner
        try:
            self._cc_show_page(key)
            self._cc_embed_target = inner
            try:
                opener()
            finally:
                self._cc_embed_target = None
            page.update_idletasks()
            try:
                page._cc_canvas.yview_moveto(0.0)
            except Exception:
                pass
        except Exception as e:
            log.warning("面板内嵌设置页失败（%s）: %s", key, e)
            try:
                for w in inner.winfo_children():
                    w.destroy()
                tk.Label(inner, text="这一页打开失败：%s" % e, font=(self.font_family, 9),
                         fg=DANGER_RED, bg=CARD_BG).pack(anchor="w")
            except Exception:
                pass

    def _cc_build_about(self, host):
        """「关于」页（原来是个 messagebox，这里直接排出来）。"""
        s = self._dpi_scale
        page = tk.Frame(host, bg=CARD_BG)
        page.place(relx=0, rely=0, relwidth=1, relheight=1)
        self._cc_pages["about"] = page
        tk.Label(page, text="关于", font=(self.font_family, 11, "bold"),
                 fg=TEXT_MAIN, bg=CARD_BG).pack(anchor="w")
        lines = [
            ("%s" % self.pet_name, 13, TEXT_MAIN),
            ("DeepSeek 鲸鱼娘 · 桌面伴侣", 10, TEXT_SUB),
            ("", 8, TEXT_SUB),
            ("模型：DeepSeek（对话 / 视觉 / 记忆）", 9, TEXT_MAIN),
            ("语音：火山 / Edge TTS", 9, TEXT_MAIN),
            ("素材许可：CC BY-NC-SA 4.0（禁止商用）", 9, TEXT_MAIN),
            ("仓库：Alps-Link/deepseek-whale-Desktop-pet", 9, TEXT_SUB),
        ]
        for text, size, color in lines:
            if text:
                tk.Label(page, text=text, font=(self.font_family, size), fg=color,
                         bg=CARD_BG, anchor="w", justify="left").pack(anchor="w", pady=(int(2 * s), 0))
        RoundedButton(page, text="查看完整关于", command=self.show_about, variant="subtle",
                      width=int(150 * s), height=int(34 * s), radius=int(8 * s),
                      font=(self.font_family, 10)).pack(anchor="w", pady=(int(10 * s), 0))

    def _cc_show_page(self, key):
        """切换右侧页面（页面都常驻，只 tkraise）。"""
        try:
            page = self._cc_pages.get(key)
            if page is None:
                return
            page.tkraise()
            if key == "chat":
                self._cc_refresh_chat()
                try:
                    self._cc_input.focus_set()
                except Exception:
                    pass
        except Exception as e:
            log.warning("面板切页失败: %s", e)

    def _cc_build_chat(self, host):
        """聊天页：左她的气泡、右你的气泡，你这边每条下面带「回退」。"""
        s = self._dpi_scale
        page = tk.Frame(host, bg=CARD_BG)
        page.place(relx=0, rely=0, relwidth=1, relheight=1)
        self._cc_pages["chat"] = page

        head = tk.Frame(page, bg=CARD_BG)
        head.pack(fill=tk.X)
        tk.Label(head, text="聊天记录", font=(self.font_family, 11, "bold"),
                 fg=TEXT_MAIN, bg=CARD_BG).pack(side=tk.LEFT)
        tk.Label(head, text="（聊天 + 陪玩 + 陪读，按时间顺序）", font=(self.font_family, 9),
                 fg=TEXT_SUB, bg=CARD_BG).pack(side=tk.LEFT, padx=(int(8 * s), 0))

        # 输入区先 pack 底部（固定，不被挤）
        input_box = tk.Frame(page, bg=CARD_BG)
        input_box.pack(side=tk.BOTTOM, fill=tk.X, pady=(int(6 * s), 0))
        rt = RoundedText(input_box, width=int(560 * s), height=int(82 * s),
                         radius=int(12 * s), font=(self.font_family, 10),
                         bg="#ffffff", border=INPUT_BORDER2, fg=TEXT_MAIN,
                         parent_bg=CARD_BG, insert_bg=BTN_PRIMARY)
        rt.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        txt = rt.text
        btns = tk.Frame(input_box, bg=CARD_BG)
        btns.pack(side=tk.LEFT, padx=(int(8 * s), 0), anchor="s")
        RoundedButton(btns, text="😊", variant="subtle",
                      command=lambda: self.open_emoji_picker(
                          lambda ch: self._insert_emoji_into(txt, ch), parent=txt),
                      width=int(34 * s), height=int(26 * s), radius=int(6 * s),
                      font=(self.font_family, 10)).pack(side=tk.TOP, pady=(0, int(4 * s)))
        RoundedButton(btns, text="发送", command=self._cc_send, variant="primary",
                      width=int(76 * s), height=int(34 * s), radius=int(8 * s),
                      font=(self.font_family, 10, "bold")).pack(side=tk.TOP)
        tk.Label(btns, text="Enter 发送\nShift+Enter 换行", font=(self.font_family, 8),
                 fg=TEXT_SUB, bg=CARD_BG, justify="left").pack(side=tk.TOP, pady=(int(4 * s), 0))
        self._cc_input = txt

        def _on_key(e):
            if e.keysym == "Return" and not (e.state & 0x0001):
                self._cc_send()
                return "break"
            return None
        txt.bind("<Return>", _on_key)

        # 滚动区
        mid = tk.Frame(page, bg=CARD_BG)
        mid.pack(fill=tk.BOTH, expand=True, pady=(int(6 * s), 0))
        cvs = tk.Canvas(mid, bg=CARD_BG, highlightthickness=0)
        vsb = ttk.Scrollbar(mid, orient="vertical", command=cvs.yview)
        inner = tk.Frame(cvs, bg=CARD_BG)
        inner.bind("<Configure>", lambda e: cvs.configure(scrollregion=cvs.bbox("all")))
        win_id = cvs.create_window((0, 0), window=inner, anchor="nw")
        cvs.bind("<Configure>", lambda e: cvs.itemconfigure(win_id, width=e.width))
        cvs.configure(yscrollcommand=vsb.set)
        cvs.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        vsb.pack(side=tk.RIGHT, fill=tk.Y)
        self._cc_chat_inner = inner
        self._cc_chat_canvas = cvs

        def _wheel(e):
            try:
                cvs.yview_scroll(int(-1 * (e.delta / 120)), "units")
            except Exception:
                pass
        cvs.bind_all("<MouseWheel>", _wheel)

        self._cc_refresh_chat()

    def _cc_refresh_chat(self):
        """重画聊天列表（只显示 source=chat 的轮次）。"""
        inner = getattr(self, "_cc_chat_inner", None)
        if inner is None:
            return
        try:
            if not inner.winfo_exists():
                return
        except Exception:
            return
        s = self._dpi_scale
        for w in inner.winfo_children():
            w.destroy()
        turns = [(i, t) for i, t in enumerate(self.chat_buffer)
                 if t and t[0].get("source", "chat") in ("chat", "topic_open", "watch", "reading")]
        # 已经作为"她先发的一条"显示过的话题，别再在下面用灰字重复一遍
        _openers = {str(t[1].get("content") or "").strip()
                    for _i2, t in turns if t[0].get("source") == "topic_open"}
        if not turns and not (getattr(self, "_cc_pending", None) or []):
            tk.Label(inner, text="还没有聊过——在下面输入点什么吧", font=(self.font_family, 10),
                     fg=TEXT_SUB, bg=CARD_BG).pack(pady=int(24 * s))
            return
        wrap = int(400 * s)

        def _bubble_user(text, undo_cb=None):
            row = tk.Frame(inner, bg=CARD_BG)
            row.pack(fill=tk.X, pady=(int(3 * s), 0))
            box = tk.Frame(row, bg=CARD_BG)
            box.pack(side=tk.RIGHT, padx=(int(40 * s), 0))
            tk.Label(box, text=text, font=(self.font_family, 10), fg=TEXT_MAIN,
                     bg="#ece7ff", justify="left", wraplength=wrap,
                     padx=int(10 * s), pady=int(7 * s)).pack(anchor="e")
            if undo_cb is not None:
                undo = tk.Label(box, text="↩ 回退这一轮", font=(self.font_family, 8),
                                fg=TEXT_SUB, bg=CARD_BG, cursor="hand2")
                undo.pack(anchor="e", pady=(int(1 * s), 0))
                undo.bind("<Enter>", lambda e, w=undo: w.config(fg=DANGER_RED))
                undo.bind("<Leave>", lambda e, w=undo: w.config(fg=TEXT_SUB))
                undo.bind("<Button-1>", lambda e: undo_cb())

        def _bubble_her(text, typing=False, tag="", on_delete=None):
            row = tk.Frame(inner, bg=CARD_BG)
            row.pack(fill=tk.X, pady=(int(3 * s), 0))
            box = tk.Frame(row, bg=CARD_BG)
            box.pack(side=tk.LEFT, padx=(0, int(40 * s)))
            head_row = tk.Frame(box, bg=CARD_BG)
            head_row.pack(anchor="w")
            if tag:
                tk.Label(head_row, text=tag, font=(self.font_family, 8), fg=TEXT_SUB,
                         bg=CARD_BG).pack(side=tk.LEFT, padx=(0, int(6 * s)))
            tk.Label(box, text=text, font=(self.font_family, 10),
                     fg=(TEXT_SUB if typing else TEXT_MAIN),
                     bg="#f2f4f7", justify="left", wraplength=wrap,
                     padx=int(10 * s), pady=int(7 * s)).pack(anchor="w")
            if on_delete is not None:
                dele = tk.Label(box, text="✕ 删掉这条", font=(self.font_family, 8),
                                fg=TEXT_SUB, bg=CARD_BG, cursor="hand2")
                dele.pack(anchor="w", pady=(int(1 * s), 0))
                dele.bind("<Enter>", lambda e, w=dele: w.config(fg=DANGER_RED))
                dele.bind("<Leave>", lambda e, w=dele: w.config(fg=TEXT_SUB))
                dele.bind("<Button-1>", lambda e: on_delete())

        _TOPIC_WRAP = re.compile(r"^[（(]\s*关于话题[:：]\s*(.*?)[）)]\s*(?:回应|我的回应)[:：]\s*(.*)$", re.S)
        for idx, turn in turns:
            _src = str(turn[0].get("source") or "chat")
            u_txt = str(turn[0].get("content") or "").strip()
            a_txt = str(turn[1].get("content") or "").strip()
            a_txt = re.sub(r"^\([a-z]+\)\s*", "", a_txt)
            a_txt = re.sub(r"^(?:回复|回答)[:：]\s*", "", a_txt)
            # 陪读/陪玩这一侧的内容不是"他说的"（读书那条是 [读书中，老大在读：…] 的场景标记），
            # 界面上不画用户气泡，只留她说的那句；存库不动，聊天上下文仍能用到这个标记。
            if _src in ("reading", "watch"):
                u_txt = ""
            # 话题回应在库里是"（关于话题：X）回应：Y"，界面上把 X 单列一行灰字，气泡里只留 Y
            _topic_ctx = ""
            _m = _TOPIC_WRAP.match(u_txt)
            if _m:
                _topic_ctx = _m.group(1).strip()
                u_txt = _m.group(2).strip()
            if _topic_ctx and _topic_ctx not in _openers:
                _row = tk.Frame(inner, bg=CARD_BG)
                _row.pack(fill=tk.X, pady=(int(6 * s), 0))
                tk.Label(_row, text="话题：" + _topic_ctx, font=(self.font_family, 8),
                         fg=TEXT_SUB, bg=CARD_BG, justify="left",
                         wraplength=wrap).pack(side=tk.LEFT, padx=(0, int(40 * s)))
            # 顺序：先你说的话（右），再她的回复（左）—— 像真人对话往下走
            if u_txt:
                _bubble_user(u_txt, undo_cb=(lambda i=idx, t=u_txt: self._cc_rollback(i, t)))
            if a_txt:
                if _src == "watch":
                    _bubble_her(a_txt, tag="🎮 陪玩",
                                on_delete=(lambda i=idx, t=a_txt: self._cc_del_single(i, t)))
                elif _src == "reading":
                    _bubble_her(a_txt, tag="📖 陪读",
                                on_delete=(lambda i=idx, t=a_txt: self._cc_del_single(i, t)))
                else:
                    _bubble_her(a_txt)
            tk.Frame(inner, bg=CARD_BG, height=int(6 * s)).pack()
        # 刚发出、还没等到回复：先把你那句挂上，再给一个"正在想"
        for _p in (getattr(self, "_cc_pending", None) or []):
            _bubble_user(str(_p))
            _bubble_her("（正想着…）", typing=True)
            tk.Frame(inner, bg=CARD_BG, height=int(6 * s)).pack()
        try:
            self._cc_chat_canvas.update_idletasks()
            self._cc_chat_canvas.yview_moveto(1.0)
        except Exception:
            pass

    def _cc_rollback(self, index, preview=""):
        """回退：删掉这一轮（你说的话 + 她的回复）。"""
        try:
            short = (preview[:18] + "…") if len(preview) > 18 else preview
            if not messagebox.askyesno("回退", "删掉这一轮？\n\n你：%s" % short, parent=self._cc_win):
                return
        except Exception:
            return
        ok = self._delete_chat_record(index)
        if ok:
            # 同步从"待提取"队列里挪走，否则下次抽取又会把它算进去
            try:
                with self._memory_lock:
                    self._extraction_pending_turns = [
                        t for t in self._extraction_pending_turns
                        if not (t and t[0].get("source") == "chat"
                                and t[0].get("content") == preview)]
                    self._persist_extraction_state()
            except Exception as e:
                log.debug("回退后同步提取队列失败: %s", e)
            log.info("聊天回退：删除第 %d 轮（%s）", index, short)
            self._cc_refresh_chat()

    def _cc_del_single(self, index, preview=""):
        """删掉一条记录（陪玩/陪读只有她那一半）。"""
        try:
            short = (preview[:18] + "…") if len(preview) > 18 else preview
            if not messagebox.askyesno("删除", "删掉这一条？" + chr(10) * 2 + short, parent=self._cc_win):
                return
        except Exception:
            return
        if self._delete_chat_record(index):
            try:
                with self._memory_lock:
                    self._extraction_pending_turns = [
                        t for t in self._extraction_pending_turns
                        if not (t and str(t[1].get("content") or "").strip() == preview)]
                    self._persist_extraction_state()
            except Exception as e:
                log.debug("删除后同步提取队列失败: %s", e)
            log.info("聊天记录：删除第 %d 条（%s）", index, short)
            self._cc_refresh_chat()

    def _cc_send(self):
        """从面板输入框发一条（复用 send_message 的整条链路）。"""
        try:
            text = self._cc_input.get("1.0", "end").strip()
        except Exception:
            return
        if not text:
            return
        try:
            self._cc_input.delete("1.0", "end")
        except Exception:
            pass
        try:
            self.input_entry.delete(0, tk.END)
            self.input_entry.insert(0, text)
        except Exception:
            pass
        # 乐观显示：你的话立刻出现 + 一个"正在想"
        try:
            self._cc_pending = getattr(self, "_cc_pending", [])
            self._cc_pending.append(text)
            self._cc_refresh_chat()
            # 兜底：万一没等到回复（模型报错/空回），90 秒后自己收掉
            self.root.after(90000, self._cc_drop_pending)
        except Exception:
            pass
        self.send_message()

    def _cc_drop_pending(self):
        """回复迟迟不来时，把乐观气泡收掉（避免一直挂着"正想着"）。"""
        try:
            if getattr(self, "_cc_pending", None):
                self._cc_pending = []
                self._cc_refresh_chat()
        except Exception:
            pass

    def _cc_tick(self):
        """面板开着的时候每 2 秒刷一次状态行（精力会自己掉，模式也可能在别处变）。"""
        try:
            win = getattr(self, "_cc_win", None)
            if win is None or not win.winfo_exists():
                self._cc_tick_job = None
                return
            self._cc_refresh_sidebar()
            self._cc_tick_job = self.root.after(2000, self._cc_tick)
        except Exception:
            self._cc_tick_job = None

    def _cc_refresh_sidebar(self):
        """把模式开关的文案跟真实状态对齐（否则会出现"显示未开、实际在跑"）。"""
        try:
            parts = []
            parts.append("陪玩：%s" % ("开" if self.watch_mode else "关"))
            try:
                rc = getattr(self, "reading_companion", None)
                parts.append("陪读：%s" % ("开" if rc is not None and getattr(rc, "running", False) else "关"))
            except Exception:
                pass
            try:
                parts.append("语音：%s" % ("开" if getattr(self, "voice_on", False) else "关"))
            except Exception:
                pass
            try:
                parts.append("说话：%s" % ("开" if getattr(self, "tts_enabled", True) else "关"))
            except Exception:
                pass
            try:
                parts.append("精力：%d/%d" % (int(round(float(getattr(self, "energy", 0)))), int(MAX_ENERGY)))
            except Exception:
                parts.append("精力：?")
            if getattr(self, "_cc_status", None) is not None:
                self._cc_status.config(text="　·　".join(str(x) for x in parts))
        except Exception as e:
            log.debug("面板状态刷新失败: %s", e)

    def open_dsh_settings(self):
        """DSH 协作设置：开关 + 命令行路径 + 检测/测试。"""
        cfg = load_dsh_settings()
        win, frame = self._make_card_window("DSH 协作", 660, 520)
        s = self._dpi_scale
        enabled_var = tk.BooleanVar(value=bool(cfg.get("enabled", True)))

        # ── 底部先 pack（固定按钮永不被挤）──
        btn_frame = tk.Frame(frame, bg=DIALOG_BG)
        btn_frame.pack(side=tk.BOTTOM, pady=(6, 14))

        # ── 顶部：开关 ──
        tk.Label(frame, text="要不要让她把做不到的事外包出去", font=(self.font_family, 11, "bold"),
                 fg=TEXT_MAIN, bg=DIALOG_BG).pack(anchor="w", padx=16, pady=(12, 6))
        switch_row = tk.Frame(frame, bg=DIALOG_BG)
        switch_row.pack(anchor="w", padx=16)

        def render_switch():
            for w in switch_row.winfo_children():
                w.destroy()
            for val, label in ((True, "允许"), (False, "不允许")):
                RoundedButton(switch_row, text=label,
                              command=lambda v=val: (enabled_var.set(v), render_switch()),
                              variant=("primary" if enabled_var.get() == val else "subtle"),
                              width=int(110 * s), height=int(36 * s), radius=int(8 * s),
                              font=(self.font_family, 11)).pack(side=tk.LEFT, padx=(0, 8))

        tk.Label(frame, text="只会外包\u201c动文件、跑命令、查网络、多步任务\u201d这类事；闲聊、陪玩、看屏幕还是她自己做。",
                 font=(self.font_family, 9), fg=TEXT_SUB, bg=DIALOG_BG,
                 justify="left", wraplength=int(600 * s)).pack(anchor="w", padx=16, pady=(6, 0))

        # ── 命令行 ──
        tk.Label(frame, text="DSH 命令行", font=(self.font_family, 11, "bold"),
                 fg=TEXT_MAIN, bg=DIALOG_BG).pack(anchor="w", padx=16, pady=(14, 4))
        tk.Label(frame, text="留空 = 自动检测（桌面版默认安装位置、npm 全局、PATH）。装在别处就手动指定 dsh.cmd。",
                 font=(self.font_family, 9), fg=TEXT_SUB, bg=DIALOG_BG,
                 justify="left", wraplength=int(600 * s)).pack(anchor="w", padx=16, pady=(0, 4))
        cli_entry = RoundedEntry(frame, width=int(580 * s), height=int(34 * s),
                                 radius=int(8 * s), font=(self.font_family, 10))
        cli_entry.pack(anchor="w", padx=16)
        cli_entry.set(cfg.get("cli") or "")

        status_lbl = tk.Label(frame, text="", font=(self.font_family, 9), fg=TEXT_SUB,
                              bg=DIALOG_BG, justify="left", wraplength=int(600 * s))
        status_lbl.pack(anchor="w", padx=16, pady=(6, 0))

        def show_status(text, ok=None):
            try:
                if ok is True:
                    status_lbl.config(text=text, fg="#1a7f37")      # 成功绿
                elif ok is False:
                    status_lbl.config(text=text, fg=DANGER_RED)
                else:
                    status_lbl.config(text=text, fg=TEXT_SUB)
            except Exception:
                pass

        def do_detect():
            _cli = str(cli_entry.get() or "").strip()
            if _cli and not os.path.isfile(_cli):
                show_status("这个路径下没有文件：%s" % _cli, False)
                return
            found = self._find_dsh_cli()
            if found:
                show_status("\u2713 找到了：%s" % found, True)
            else:
                show_status("没找到 dsh.cmd。手动填路径，或确认 DSH 装在默认位置。", False)

        def do_test():
            show_status("正在试\u2026（最多等 60 秒）", None)

            def run():
                try:
                    import subprocess as _sp
                    _cli = self._find_dsh_cli()
                    if not _cli:
                        self._ui(lambda: show_status("没找到 dsh.cmd，先在上面填路径", False))
                        return
                    _env = dict(os.environ)
                    _env["NO_COLOR"] = "1"
                    _env["PYTHONIOENCODING"] = "utf-8"
                    _k = str(getattr(self, "text_api_key", "") or "").strip()
                    if _k:
                        _env.setdefault("DEEPSEEK_API_KEY", _k)
                    _flags = getattr(_sp, "CREATE_NO_WINDOW", 0) if os.name == "nt" else 0
                    proc = _sp.Popen(["cmd", "/c", _cli, "headless", "-"],
                                     stdout=_sp.PIPE, stderr=_sp.PIPE, stdin=_sp.PIPE,
                                     cwd=CONFIG_DIR, env=_env, creationflags=_flags)
                    out, err = proc.communicate("用一句话回答：今天是几号，星期几。不要读文件。".encode("utf-8"),
                                                timeout=60)
                    _txt = (out or b"").decode("utf-8", "replace").strip()
                    _er = (err or b"").decode("utf-8", "replace").strip()
                    if proc.returncode == 0 and _txt:
                        _line = _txt.splitlines()[-1][:60]
                        self._ui(lambda: show_status("\u2713 通了：%s" % _line, True))
                    else:
                        _why = ((_er or _txt).splitlines() or ["没有输出"])[-1][:80]
                        self._ui(lambda: show_status("\u00d7 没通：%s" % _why, False))
                except Exception as _e:
                    _msg = "\u00d7 没通：%s" % _e
                    self._ui(lambda: show_status(_msg, False))

            threading.Thread(target=run, daemon=True).start()

        def do_pick():
            try:
                from tkinter import filedialog
                _p = filedialog.askopenfilename(
                    parent=win, title="选择 dsh.cmd",
                    filetypes=[("命令行", "*.cmd;*.bat;*.exe"), ("所有文件", "*.*")])
                if _p:
                    cli_entry.set(_p)
                    do_detect()
            except Exception as e:
                log.debug("选择 DSH 路径失败: %s", e)

        row = tk.Frame(frame, bg=DIALOG_BG)
        row.pack(anchor="w", padx=16, pady=(8, 0))
        RoundedButton(row, text="重新检测", command=do_detect,
                      variant="subtle", width=int(100 * s), height=int(32 * s),
                      radius=int(8 * s), font=(self.font_family, 10)).pack(side=tk.LEFT, padx=(0, 8))
        RoundedButton(row, text="浏览...", command=do_pick,
                      variant="subtle", width=int(90 * s), height=int(32 * s),
                      radius=int(8 * s), font=(self.font_family, 10)).pack(side=tk.LEFT, padx=(0, 8))
        RoundedButton(row, text="测试连接", command=do_test,
                      variant="subtle", width=int(100 * s), height=int(32 * s),
                      radius=int(8 * s), font=(self.font_family, 10)).pack(side=tk.LEFT)

        def do_save():
            try:
                save_dsh_settings(enabled_var.get(), str(cli_entry.get() or "").strip())
                self._ui(lambda: self.show_bubble_text("(relaxed) 记下了", "relaxed", status=True))
                try:
                    win.grab_release()
                except Exception:
                    pass
                win.destroy()
            except Exception as e:
                log.warning("保存 DSH 设置失败: %s", e)
                show_status("保存失败：%s" % e, False)

        def do_cancel():
            try:
                win.grab_release()
            except Exception:
                pass
            win.destroy()

        RoundedButton(btn_frame, text="保存", command=do_save, variant="primary",
                      width=int(120 * s), height=int(38 * s), radius=int(9 * s),
                      font=(self.font_family, 11, "bold")).pack(side=tk.LEFT, padx=(0, 10))
        RoundedButton(btn_frame, text="取消", command=do_cancel, variant="subtle",
                      width=int(100 * s), height=int(38 * s), radius=int(9 * s),
                      font=(self.font_family, 11)).pack(side=tk.LEFT)

        render_switch()
        do_detect()

    def open_voice_settings(self):
        """🎤 语音识别设置：免唤醒窗口（0 = 关闭）+ 按键说话（PTT）"""
        win, frame = self._make_card_window("语音识别设置", 440, 450)
        s = self._dpi_scale
        cur = float(self.voice_cfg.get("wake_window", DEFAULT_WAKE_WINDOW))
        choice = {"v": cur}
        btn_map = {}
        ptt = {"enabled": bool(self._ptt_enabled), "vk": int(self._ptt_vk),
               "name": str(self._ptt_name)}
        ptt_var = tk.BooleanVar(value=ptt["enabled"])
        cap = {"on": False}
        key_label = {"w": None}

        # 底部按钮先 pack（布局铁律：内容变高时收尾按钮不被挤走）
        btn_frame = tk.Frame(frame, bg=DIALOG_BG)
        btn_frame.pack(side=tk.BOTTOM, pady=10)

        def save():
            v = float(choice["v"])
            ptt["enabled"] = bool(ptt_var.get())
            if ptt["enabled"]:
                v = 0.0                  # 按键说话与免唤醒窗口不共存：开着按键就固定关闭
            self.voice_cfg["wake_window"] = v
            self.voice_cfg["hotkey_enabled"] = ptt["enabled"]
            self.voice_cfg["hotkey_vk"] = ptt["vk"]
            self.voice_cfg["hotkey_name"] = ptt["name"]
            self._ptt_enabled = ptt["enabled"]
            self._ptt_vk = ptt["vk"]
            self._ptt_name = ptt["name"]
            try:
                save_voice_config({"wake_window": v, "hotkey_enabled": ptt["enabled"],
                                   "hotkey_vk": ptt["vk"], "hotkey_name": ptt["name"]})
            except Exception as e:
                log.warning("保存语音设置失败: %s", e)
            if self.stt is not None:
                try:
                    self.stt.set_wake_window(v)
                except Exception as e:
                    log.warning("应用免唤醒窗口失败: %s", e)
            msg = "已保存：免唤醒窗口关闭（每次说话都要先喊名字）" if v <= 0 else "已保存：免唤醒窗口 %d 秒" % int(v)
            msg += "；按键说话：%s（%s）" % ("启用" if ptt["enabled"] else "停用", ptt["name"])
            messagebox.showinfo("成功", msg)
            win.destroy()

        RoundedButton(btn_frame, text="保存", command=save, width=int(120 * s), height=int(36 * s),
                      radius=int(6 * s), font=(self.font_family, 11)).pack(side=tk.LEFT, padx=3)

        tk.Label(frame, text="免唤醒窗口", font=(self.font_family, 12, "bold"),
                 fg=TEXT_MAIN, bg=DIALOG_BG).pack(anchor='w', pady=(6, 2))
        tk.Label(frame, text="她说完话之后的这段时间里，你直接说话不用先喊名字；\n"
                             "关掉之后每一次说话都要先喊她名字（点歌报编号也一样）。",
                 font=(self.font_family, 9), fg=TEXT_SUB, bg=DIALOG_BG,
                 justify='left').pack(anchor='w')

        def select(v):
            choice["v"] = v
            if v > 0 and ptt_var.get():
                ptt_var.set(False)      # 二者不共存：选了窗口就把"按键说话"关掉（后动的那一方生效）
            for _v, _b in btn_map.items():
                try:
                    _b.set_variant("primary" if _v == v else "subtle")
                except Exception:
                    pass

        row = tk.Frame(frame, bg=DIALOG_BG)
        row.pack(anchor='w', pady=10)
        for v, label in ((0.0, "关闭"), (3.0, "3 秒"), (5.0, "5 秒"),
                         (8.0, "8 秒"), (15.0, "15 秒")):
            b = RoundedButton(row, text=label, width=int(62 * s), height=int(30 * s),
                              radius=int(8 * s), font=(self.font_family, 10),
                              variant="primary" if abs(v - cur) < 0.01 else "subtle",
                              command=lambda vv=v: select(vv))
            b.pack(side=tk.LEFT, padx=(0, 6))
            btn_map[v] = b

        tk.Label(frame, text="窗口开着的时候，她头顶会显示一个「🎤 在听」小标记；\n"
                             "她说话期间麦克风是静音的，所以那会儿你出声不会打断她。\n"
                             "TTS 开着时，窗口要等她念完才开（气泡打完不算）。",
                 font=(self.font_family, 9), fg=TEXT_SUB, bg=DIALOG_BG,
                 justify='left').pack(anchor='w', pady=(6, 0))

        # ---------- 按键说话（PTT）----------
        tk.Frame(frame, bg=CARD_BORDER, height=1).pack(fill=tk.X, pady=8)
        tk.Label(frame, text="按住按键说话", font=(self.font_family, 12, "bold"),
                 fg=TEXT_MAIN, bg=DIALOG_BG).pack(anchor='w', pady=(0, 2))
        tk.Label(frame, text="按住下面这个键（任何窗口在前台都有效），窗口就一直开着，松开就关。\n"
                             "跟上面的窗口**互斥**：启用它，窗口固定为「关闭」（每次说话按住键即可）。",
                 font=(self.font_family, 9), fg=TEXT_SUB, bg=DIALOG_BG,
                 justify='left').pack(anchor='w')

        def on_ptt_toggle():
            if ptt_var.get():
                select(0.0)             # 启用按键说话 → 窗口自动切到"关闭"

        ttk.Checkbutton(frame, text="启用按键说话", variable=ptt_var,
                        command=on_ptt_toggle).pack(anchor='w', pady=(6, 2))
        ptt_row = tk.Frame(frame, bg=DIALOG_BG)
        ptt_row.pack(anchor='w', pady=2)
        key_label["w"] = tk.Label(ptt_row, text="当前按键：%s" % ptt["name"],
                                  font=(self.font_family, 10, "bold"), fg=BTN_PRIMARY, bg=DIALOG_BG)
        key_label["w"].pack(side=tk.LEFT, padx=(0, 10))

        def start_capture():
            cap["on"] = True
            cap["baseline"] = set()      # 开始捕获时已经按着的键，不算
            try:
                u = ctypes.windll.user32
                for vk in range(1, 255):
                    if u.GetAsyncKeyState(vk) & 0x8000:
                        cap["baseline"].add(vk)
            except Exception:
                pass
            key_label["w"].config(text="请按一个键…")
            win.after(50, _capture_tick)

        def _capture_tick():
            """轮询捕获：等到出现一个"刚刚按下"的键就记下来。

            不用 Tk 的 <KeyPress>：Windows 上单独按修饰键（右 Ctrl）不一定送来 KeyPress，
            而轮询 GetAsyncKeyState 跟运行时的检测是同一套机制，还能捕获修饰键。
            """
            if not cap["on"]:
                return
            vk = any_key_down(skip=cap["baseline"])
            if vk:
                cap["on"] = False
                ptt["vk"] = int(vk)
                ptt["name"] = vk_label(vk)
                key_label["w"].config(text="当前按键：%s" % ptt["name"])
                log.info("按键说话改为: %s (vk=%d)", ptt["name"], ptt["vk"])
                return
            win.after(50, _capture_tick)

        RoundedButton(ptt_row, text="改键", command=start_capture, variant="subtle",
                      width=int(70 * s), height=int(30 * s), radius=int(8 * s),
                      font=(self.font_family, 10)).pack(side=tk.LEFT)

        # 11/18：游戏以管理员运行时（UIPI），普通权限进程连 Raw Input 都收不到 —— 直接给状态和入口
        if is_elevated():
            tk.Label(frame, text="当前是管理员身份：游戏里的按键说话可以读到",
                     font=(self.font_family, 9), fg=TEXT_SUB, bg=DIALOG_BG,
                     justify='left').pack(anchor='w', pady=(8, 0))
        else:
            tk.Label(frame, text="现在不是管理员身份：游戏以管理员运行时读不到这个键。\n"
                                 "（点下面那个按钮重启一次就好，UAC 里点「是」）",
                     font=(self.font_family, 9), fg=DANGER_RED, bg=DIALOG_BG,
                     justify='left').pack(anchor='w', pady=(8, 2))
            RoundedButton(frame, text="以管理员身份重启桌宠", command=self.relaunch_as_admin,
                          variant="subtle", width=int(180 * s), height=int(32 * s),
                          radius=int(8 * s), font=(self.font_family, 10)).pack(anchor='w', pady=(2, 0))

    def on_speech_recognized(self, text, mode="content"):
        # 睡着时听到什么都只提示一句：不唤醒、不进模型、不出声（连 last_interaction_time 都不动，
        # 免得"越喊越睡"那套时间账被搅乱）
        if self.sleep_mode:
            self._show_sleep_hint()
            return
        try:
            remain = self.stt.window_left() if self.stt is not None else -1
        except Exception:
            remain = -1
        log.debug("语音入口: mode=%s 窗口剩余=%.1fs text=%s", mode, remain, text)
        # 抗打断：宠物正在输出（气泡打字 / TTS 播放）时，忽略本轮语音输入，
        # 等宠物说完再接话，避免误打断
        if self._voice_output_busy():
            return                                  # 丢弃帧也不记日志（同上，防刷屏）
        # 只有**真被接受**的语音才算互动（10/17 用户要求）：她正在说话时插的话被抗打断丢掉，
        # 不续命；"没喊名字"的语音在 _transcribe_loop 里就 continue 了，压根到不了这里。
        self.last_interaction_time = time.time()
        if mode == "wake":
            # 只说唤醒词：进入聆听状态。
            # 不再弹"在呢，请说"气泡（用户要求去掉）——反馈交给头顶的「🎤 在听」标记，
            # 免得每次喊她都多一句废话，也避免气泡/TTS 反过来干扰她自己听你说话。
            log.info("语音唤醒: 已进入聆听状态（会话窗内免唤醒词）")
            return
        if not text:
            return
        log.info(f"语音识别: {text}")
        # 直接发送识别文本（Paraformer 中文准确率高，去掉 LLM 纠错以降低延迟）
        self._ui(lambda: self._send_voice_text(text))

    def _send_voice_text(self, text):
        self.input_entry.delete(0, tk.END)
        self.input_entry.insert(0, text)
        self.send_message()

    def _update_voice_menu_label(self):
        try:
            label = "🎤 语音识别 (停止)" if self.voice_on else "🎤 语音识别 (开始)"
            self.mode_menu.entryconfigure(self.voice_menu_index, label=label)
        except Exception as e:
            log.debug(f"语音标签更新失败: {e}")

    def _save_ui_state(self):
        """保存输入框显示状态，下次启动沿用"""
        try:
            save_ui_config(self.input_visible)
        except Exception as e:
            log.debug(f"界面状态保存失败: {e}")

    # ---------- 音乐库设置 ----------
    def open_music_library_settings(self):
        """音乐库设置：顶部切换"本地曲库 / 网页版"，两套设置分开显示。"""
        win, frame = self._make_card_window("音乐库设置", 680, 560)
        s = self._dpi_scale
        mode_var = tk.StringVar(value=load_music_mode())
        # ── 顶部：模式切换 ──
        tk.Label(frame, text="音乐来源", font=(self.font_family, 11, "bold"),
                 fg=TEXT_MAIN, bg=DIALOG_BG).pack(anchor="w", padx=16, pady=(12, 6))
        btn_row = tk.Frame(frame, bg=DIALOG_BG)
        btn_row.pack(anchor="w", padx=16)

        def render_buttons():
            for w in btn_row.winfo_children():
                w.destroy()
            for val, label in (("local", "本地曲库"), ("web", "网页版")):
                _selected = (mode_var.get() == val)
                RoundedButton(btn_row, text=label, command=lambda v=val: pick(v),
                              variant=("primary" if _selected else "subtle"),
                              width=int(140 * s), height=int(36 * s), radius=int(8 * s),
                              font=(self.font_family, 11)).pack(side=tk.LEFT, padx=(0, 8))
        tk.Label(frame, text="两种模式互斥：本地模式下不会去碰网页，网页模式下不会动本地曲库。",
                 font=(self.font_family, 9), fg=TEXT_SUB, bg=DIALOG_BG,
                 justify="left").pack(anchor="w", padx=16, pady=(6, 0))


        # 固定容器：本地/网页两块都在它里面切换，外层顺序永不变
        # （踩过的坑：直接对 frame 里的块 pack_forget + pack，切一次就排到队尾，把下面的按钮顶到上面去）
        mode_host = tk.Frame(frame, bg=DIALOG_BG)
        mode_host.pack(anchor="w", fill="x")
        tk.Label(frame, text=" ", font=(self.font_family, 6), bg=DIALOG_BG).pack()

        # ── 本地曲库 ──
        local_box = tk.Frame(mode_host, bg=DIALOG_BG)
        tk.Label(local_box, text="音乐文件夹", font=(self.font_family, 11, "bold"),
                 fg=TEXT_MAIN, bg=DIALOG_BG).pack(anchor="w")
        tk.Label(local_box, text="支持子文件夹；mp3/flac/ogg/wav。留空并保存 = 用内置曲库。",
                 font=(self.font_family, 9), fg=TEXT_SUB, bg=DIALOG_BG,
                 justify="left").pack(anchor="w", pady=(2, 4))
        dir_entry = RoundedEntry(local_box, width=int(580 * s), height=int(34 * s),
                                 radius=int(8 * s), font=(self.font_family, 10))
        dir_entry.pack(anchor="w")
        dir_entry.set(load_music_dir() or "")
        vol_row = tk.Frame(local_box, bg=DIALOG_BG)
        vol_row.pack(anchor="w", pady=(10, 0))
        tk.Label(vol_row, text="音量", width=4, anchor="w", font=(self.font_family, 11, "bold"),
                 fg=TEXT_MAIN, bg=DIALOG_BG).pack(side=tk.LEFT)
        vol_entry = RoundedEntry(vol_row, width=int(80 * s), height=int(34 * s),
                                 radius=int(8 * s), font=(self.font_family, 10))
        vol_entry.pack(side=tk.LEFT, padx=(4, 4))
        vol_entry.set(str(int(round(self._music_volume * 100))))
        tk.Label(vol_row, text="%（0~100，只作用于本地曲库）", font=(self.font_family, 10),
                 fg=TEXT_SUB, bg=DIALOG_BG).pack(side=tk.LEFT)


        # ── 网页版 ──
        web_box = tk.Frame(mode_host, bg=DIALOG_BG)
        tk.Label(web_box, text="播放器网址", font=(self.font_family, 11, "bold"),
                 fg=TEXT_MAIN, bg=DIALOG_BG).pack(anchor="w")
        tk.Label(web_box, text="填网页版音乐站的地址，例如 https://music.163.com/ 。"
                               "说“放首歌”时她会用浏览器打开它，之后能暂停/切歌/调进度。",
                 font=(self.font_family, 9), fg=TEXT_SUB, bg=DIALOG_BG,
                 justify="left").pack(anchor="w", pady=(2, 4))
        url_entry = RoundedEntry(web_box, width=int(580 * s), height=int(34 * s),
                                 radius=int(8 * s), font=(self.font_family, 10))
        url_entry.pack(anchor="w")
        url_entry.set(load_music_web_url())

        def render_mode():
            """按当前模式显示对应那一块，并重画两个切换按钮（选中=实心，另一个=白底）"""
            for w in (local_box, web_box):
                w.pack_forget()
            if mode_var.get() == "web":
                web_box.pack(anchor="w", fill="x", padx=16)
            else:
                local_box.pack(anchor="w", fill="x", padx=16)
            render_buttons()

        def pick(mode):
            mode_var.set(mode)
            if mode == "web":
                # 10/22 修：本地放着歌时切到网页版，本地音乐还在响、而网页版模式又把所有本地控制
                # 都拒了 ⇒ 停不下来。切过去时先把本地直接停掉。
                try:
                    if getattr(self, "_music_running", False) or getattr(self, "_music_current", None):
                        self._stop_local_music_now()
                        log.info("切到网页版：已停止本地音乐")
                except Exception as _e:
                    log.debug("切模式停本地音乐失败: %s", _e)
            render_mode()

        render_mode()

        # ── 底部按钮 ──
        def do_save(reset=False):
            path = "" if reset else str(dir_entry.get()).strip()
            if path and not os.path.isdir(path):
                messagebox.showwarning("路径无效", f"文件夹不存在：{path}")
                return
            raw_vol = str(vol_entry.get()).strip()
            try:
                vol = int(raw_vol)
            except (TypeError, ValueError):
                messagebox.showwarning("音量无效", "音量请填 0~100 之间的整数")
                return
            if not (0 <= vol <= 100):
                messagebox.showwarning("音量无效", "音量请填 0~100 之间的整数")
                return
            url = str(url_entry.get()).strip()
            if url and not re.match(r"^https?://", url, re.I):
                messagebox.showwarning("网址无效", f"要填 http/https 开头的网址：{url}")
                return
            ok_any = False
            try:
                ok_any = save_music_dir_setting(path) or ok_any
            except Exception:
                pass
            try:
                ok_any = save_music_volume_setting(vol) or ok_any
            except Exception:
                pass
            try:
                ok_any = save_music_web_url(url) or ok_any
            except Exception:
                pass
            try:
                ok_any = save_music_mode(mode_var.get()) or ok_any
            except Exception:
                pass
            if ok_any:
                self._music_list_state.clear()
                self._music_browse = []
                self._music_pending = None
                try:
                    self.clear_song_picker()
                except Exception:
                    pass
                self._music_volume = vol / 100.0
                self._fade_gen += 1
                try:
                    pygame.mixer.music.set_volume(self._music_volume_now())
                except Exception:
                    pass
                messagebox.showinfo("成功", "已恢复内置曲库" if reset else "音乐库设置已保存")
                win.destroy()

        btns = tk.Frame(frame, bg=DIALOG_BG)
        btns.pack(pady=12)
        RoundedButton(btns, text="保存", command=do_save, width=int(120 * s),
                      height=int(34 * s), radius=int(8 * s),
                      font=(self.font_family, 11)).pack(side=tk.LEFT, padx=8)
        RoundedButton(btns, text="恢复内置曲库", command=lambda: do_save(reset=True),
                      variant="subtle", width=int(160 * s), height=int(34 * s),
                      radius=int(8 * s), font=(self.font_family, 10)).pack(side=tk.LEFT)

    # ---------- 历史记录面板 ----------
    def show_chat_history_panel(self):
        win, main_frame = self._make_card_window("聊天记录（未总结缓冲）", 700, 500)
        s = self._dpi_scale
        canvas = tk.Canvas(main_frame, bg=DIALOG_BG, highlightthickness=0)
        scrollbar = ttk.Scrollbar(main_frame, orient="vertical", command=canvas.yview)
        scroll_frame = tk.Frame(canvas, bg=DIALOG_BG)
        scroll_frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=scroll_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        def refresh_display():
            call_name = self.user_profile.get("call_name", "你")
            for widget in scroll_frame.winfo_children():
                widget.destroy()
            if not self.chat_buffer:
                tk.Label(scroll_frame, text="暂无对话记录", font=(self.font_family, 12), fg=TEXT_SUB,
                         bg=DIALOG_BG).pack(pady=20)
                return
            for i, turn in enumerate(self.chat_buffer):
                src = turn[0].get("source", "chat")
                tag = {"watch": "🎮陪玩", "reading": "📖读书"}.get(src, "")
                frame = tk.Frame(scroll_frame, bg="#ffffff", highlightbackground=INPUT_BORDER2, highlightthickness=1, bd=0)
                frame.pack(fill=tk.X, pady=3, padx=5)
                # Show both user and AI for chat; only AI comment for watch/reading
                if src == "chat":
                    user_label = tk.Label(frame, text=f"{call_name}：{turn[0]['content']}", font=(self.font_family, 10), bg="#ffffff", fg=TEXT_MAIN, wraplength=500)
                    user_label.grid(row=0, column=0, sticky="w", padx=5)
                    ai_label = tk.Label(frame, text=f"我：{turn[1]['content']}", font=(self.font_family, 10), bg="#ffffff", fg=TEXT_MAIN, wraplength=500)
                    ai_label.grid(row=1, column=0, sticky="w", padx=5)
                else:
                    ai_label = tk.Label(frame, text=f"[{tag}] 我：{turn[1]['content']}", font=(self.font_family, 10, "italic"), bg="#ffffff", fg=TEXT_MAIN, wraplength=500)
                    ai_label.grid(row=0, column=0, sticky="w", padx=5)
                del_btn = RoundedButton(frame, text="删除",
                                        command=lambda idx=i: [self._delete_chat_record(idx), refresh_display()],
                                        variant="danger",
                                        width=int(64 * s), height=int(28 * s), radius=int(6 * s),
                                        font=(self.font_family, 9),
                                        parent_bg="#ffffff")
                del_btn.grid(row=0, column=1, rowspan=2, padx=10, sticky="e")
        refresh_display()

# ------------------------- OCR 坐标工具（11/03）-------------------------
def _ocr_lines_with_boxes(ocr_out):
    """把 RapidOCR 的输出整理成"带坐标、按阅读顺序排好"的文字块。

    返回 [{"text", "x1", "x2", "y1", "y2", "cy", "h", "score"}]，
    先按 y 聚成行（同一行 y 中心差小于半行高），行内再按 x 从左到右。
    没有 boxes 时退回纯文本（退化路径），保证老行为不会崩。
    """
    # 注意：boxes/scores 可能是 numpy 数组，不能用 `or []`（数组的真值有歧义）
    def _seq(name):
        v = getattr(ocr_out, name, None)
        return [] if v is None else list(v)
    txts, boxes, scores = _seq("txts"), _seq("boxes"), _seq("scores")
    items = []
    for i, t in enumerate(txts):
        t = (t or "").strip()
        if not t:
            continue
        b = boxes[i] if i < len(boxes) else None
        if b is None or len(b) == 0:
            items.append({"text": t, "x1": 0, "x2": 0, "y1": i, "y2": i,
                          "cy": i, "h": 1, "score": None})
            continue
        xs = [p[0] for p in b]
        ys = [p[1] for p in b]
        items.append({"text": t,
                      "x1": min(xs), "x2": max(xs),
                      "y1": min(ys), "y2": max(ys),
                      "cy": (min(ys) + max(ys)) / 2.0,
                      "h": max(1.0, max(ys) - min(ys)),
                      "score": scores[i] if i < len(scores) else None})
    if not items:
        return []
    # 聚行：按 cy 排序后，若与当前行的平均 cy 差 > 0.6×行高，就开新行
    items.sort(key=lambda r: (r["cy"], r["x1"]))
    lines, cur, cur_cy = [], [], None
    for it in items:
        if cur and abs(it["cy"] - cur_cy) > 0.6 * max(it["h"], 1.0):
            cur.sort(key=lambda r: r["x1"])
            lines.append(cur)
            cur = []
        if not cur:
            cur_cy = it["cy"]
        else:
            cur_cy = sum(r["cy"] for r in cur) / len(cur)
        cur.append(it)
    if cur:
        cur.sort(key=lambda r: r["x1"])
        lines.append(cur)
    flat = []
    for line in lines:                     # 行内用空格拼、行之间保留结构
        flat.extend(line)
    return flat


def _ocr_text_by_lines(ocr_out):
    """同一份输出按行拼成文本（行间 
，行内空格）。给需要"读顺序"的地方用。"""
    blocks = _ocr_lines_with_boxes(ocr_out)
    if not blocks:
        return ""
    rows, cur, cy = [], [], None
    for b in blocks:
        if cur and abs(b["cy"] - cy) > 0.6 * max(b["h"], 1.0):
            rows.append(" ".join(x["text"] for x in cur))
            cur = []
        if not cur:
            cy = b["cy"]
        cur.append(b)
    if cur:
        rows.append(" ".join(x["text"] for x in cur))
    return chr(10).join(rows)

# ------------------------------- 阅读伴侣（RapidOCR）--------------------------------
class ReadingCompanion:
    RING_MAX = 2000
    MIN_CHARS = 30
    FP_MAX = 30
    SESSION_LOG_MAX = 10       # 内存里保留最近这么多段（只给"最近读过"摘要用）
    DIGEST_MAX = 8             # 聊天路径注入"最近读过"的条数上限
    DIGEST_MINUTES = 30        # 超过这么久没读书，就不再往聊天上下文里带

    def __init__(self, pet):
        self.pet = pet
        self.enabled = False
        self.capture_interval = 5
        self.region = {"left": 0.2, "top": 0.8, "width": 0.6, "height": 0.15}
        self.last_image_hash = ""
        self.text_ring = ""
        self.last_sent_length = 0
        self.recent_fingerprints = []
        self.reading_session_log = []
        self.min_interval = 15
        self.max_silence = 120
        self._recent_styles = []   # 评论风格不应期：避免连着两条抽到同一档
        self.last_reply_time = 0
        self.lock = threading.Lock()
        self.capture_job = None
        self.reply_check_job = None
        self._ocr_thread = None
        self.reader = None
        self.last_ocr_blocks = []          # 上一次 OCR 的文字块（带坐标）
        self._reader_loading = False

    def _init_reader(self):
        """后台线程加载 RapidOCR（PP-OCR ONNX，模型随包自带、不用联网）"""
        if self.reader is not None or not RAPIDOCR_AVAILABLE or self._reader_loading:
            return
        self._reader_loading = True
        def _load():
            try:
                from rapidocr import RapidOCR as _RapidOCR   # 延迟到这里：见文件头那段的说明
                self.reader = _RapidOCR()
                log.info("RapidOCR 引擎初始化成功")
            except Exception as e:
                log.error(f"RapidOCR 初始化失败: {e}")
                self.reader = None
            finally:
                self._reader_loading = False
        threading.Thread(target=_load, daemon=True).start()

    def load_config(self):
        data = _get_section("reading")
        self.capture_interval = data.get("capture_interval", 5)
        self.min_interval = data.get("min_interval", 15)
        self.max_silence = data.get("max_silence", 120)
        self.region = data.get("region", self.region)

    def save_config(self):
        _update_section("reading", {
            "capture_interval": self.capture_interval,
            "min_interval": self.min_interval,
            "max_silence": self.max_silence,
            "region": self.region,
        })

    def toggle(self):
        if self.enabled:
            self.stop()
        else:
            self.start()

    def start(self):
        if not RAPIDOCR_AVAILABLE:
            messagebox.showwarning("缺少依赖", "请安装 RapidOCR：\npip install rapidocr onnxruntime")
            return
        self._init_reader()
        if self.reader is None:
            if self._reader_loading:
                messagebox.showwarning("OCR 加载中", "RapidOCR 引擎仍在加载，请稍后再试。")
            else:
                messagebox.showwarning("OCR 初始化失败", "RapidOCR 引擎启动失败，请检查依赖是否装好。")
            return
        self.load_config()
        self.text_ring = ""
        self.last_sent_length = 0
        self.recent_fingerprints = []
        self.reading_session_log = []   # 关掉再开 → 上一轮读过的不再带进上下文
        self.enabled = True
        self.pet._reading_anchor_needed = True
        log.info("读书伴侣已开启")
        self._schedule_capture()
        self._schedule_reply_check()

    def stop(self):
        self.enabled = False
        if self.capture_job:
            self.pet.root.after_cancel(self.capture_job)
            self.capture_job = None
        if self.reply_check_job:
            self.pet.root.after_cancel(self.reply_check_job)
            self.reply_check_job = None
        if self._ocr_thread and self._ocr_thread.is_alive():
            self._ocr_thread.join(timeout=2)
        log.info("读书伴侣已停止")

    def _schedule_capture(self):
        if self.enabled:
            self._start_ocr_thread()
            self.capture_job = self.pet.root.after(int(self.capture_interval * 1000), self._schedule_capture)

    def _start_ocr_thread(self):
        if self._ocr_thread and self._ocr_thread.is_alive():
            return
        self._ocr_thread = threading.Thread(target=self._capture_and_ocr, daemon=True)
        self._ocr_thread.start()

    def _capture_and_ocr(self):
        if not mss:
            return
        try:
            with mss.MSS() as sct:
                mon = sct.monitors[1]
                left = int(mon["width"] * self.region["left"])
                top = int(mon["height"] * self.region["top"])
                width = int(mon["width"] * self.region["width"])
                height = int(mon["height"] * self.region["height"])
                capture_region = {"left": left, "top": top, "width": width, "height": height}
                img = sct.grab(capture_region)
                pil_img = Image.frombytes("RGB", img.size, img.bgra, "raw", "BGRX")
            img_hash = hashlib.md5(pil_img.tobytes()).hexdigest()
            if img_hash == self.last_image_hash:
                return
            self.last_image_hash = img_hash

            if self.reader is None:
                return
            img_np = np.array(pil_img)
            _ocr_out = self.reader(img_np)          # RapidOCROutput：.txts / .boxes / .scores
            # 11/03：改用坐标 —— 按行聚、行内从左到右，读出来的顺序才和页面上一致
            self.last_ocr_blocks = _ocr_lines_with_boxes(_ocr_out)
            text = _ocr_text_by_lines(_ocr_out).strip()
            if self.last_ocr_blocks:
                log.debug("读书OCR：%d 块，第一块在 (%d,%d)-(%d,%d)",
                          len(self.last_ocr_blocks), self.last_ocr_blocks[0]["x1"],
                          self.last_ocr_blocks[0]["y1"], self.last_ocr_blocks[0]["x2"],
                          self.last_ocr_blocks[0]["y2"])
            if not re.search(r'[一-鿿]', text):
                return
            new_lines = []
            for line in text.split('\n'):
                line = line.strip()
                if not line:
                    continue
                lh = hashlib.md5(line.encode()).hexdigest()
                if lh in self.recent_fingerprints:
                    continue
                new_lines.append(line)
                self.recent_fingerprints.append(lh)
            if not new_lines:
                return
            if len(self.recent_fingerprints) > self.FP_MAX:
                self.recent_fingerprints = self.recent_fingerprints[-self.FP_MAX:]
            with self.lock:
                self.text_ring += ' '.join(new_lines) + '\n'
                if len(self.text_ring) > self.RING_MAX:
                    overflow = len(self.text_ring) - self.RING_MAX
                    self.text_ring = self.text_ring[overflow:]
                    self.last_sent_length = max(0, self.last_sent_length - overflow)
        except Exception as e:
            log.error(f"读书OCR失败: {e}")

    def _schedule_reply_check(self):
        if self.enabled:
            self._check_and_reply()
            poll_sec = max(5, min(self.min_interval // 2, 60))
            self.reply_check_job = self.pet.root.after(int(poll_sec * 1000), self._schedule_reply_check)

    def _check_and_reply(self):
        now = time.time()
        elapsed = now - self.last_reply_time
        if elapsed < self.min_interval:
            return
        elif elapsed >= self.max_silence:
            pass
        else:
            prob = max(0.05, (elapsed - self.min_interval) / (self.max_silence - self.min_interval))
            if random.random() > prob:
                return
        with self.lock:
            incremental = self.text_ring[self.last_sent_length:].strip()
            if len(re.findall(r'[一-鿿]', incremental)) < self.MIN_CHARS:
                return
        self.last_reply_time = time.time()
        threading.Thread(target=self._generate_reply, daemon=True).start()

    def _generate_reply(self):
        with self.lock:
            incremental = self.text_ring[self.last_sent_length:].strip()
        if not incremental:
            return

        user_name = self.pet.user_profile.get("call_name", "你")
        styles = [
            "好奇地提出一个与文字相关的小问题",
            "用温柔的感叹点评这段文字",
            "假装自己是书里的角色，说一句与文字相关的话",
            "表达对这段文字的喜爱或惊讶",
            "猜想接下来的情节，根据这段文字",
            "分享一个与文字相关的可爱小感想",
            f"如果这段文字让你想起之前和{user_name}经历过或聊过的事，就把那个联想自然地说出来（像突然被某句话勾起的回忆）",
        ]
        # 只有这次真能召回记忆时，才把"想起以前"那一档放进候选——对齐陪玩联想视角的做法，
        # 没景可触就别给她这个方向，免得硬编。
        has_memory = bool(self.pet._select_and_format_memories(query=incremental, dry_run=True))
        if not has_memory:
            styles = styles[:-1]
        recent = getattr(self, "_recent_styles", [])
        candidates = [s for s in styles if s not in recent] or list(styles)
        style = random.choice(candidates)
        self._recent_styles = (recent + [style])[-1:]
        reading_prompt = f"""你正在陪同"{user_name}"一起读书。
现在，{user_name}又读了下面这段新内容。请你把这段文字当作你读到的真实内容，**必须**基于它做出反应。
「{incremental}」

规则：
1. 根据文字的情绪，用括号标注一个表情（happy/relaxed/surprised/worried/shy/angry/normal）。
2. 用 {style} 的方式，说一句自然、可爱的评论。
3. **绝对不许**说"看不懂""好深奥"这类话；即使文字很奇怪，你也要尝试猜测它的意思或提出好奇的疑问。
4. 直接输出这句话本身（先情绪括号，再正文），不要输出 JSON、代码块或额外解释。
"""
        try:
            messages = self.pet.build_context_messages(self.pet.full_system, reading_prompt, context_type="reading",
                                                       memory_query=incremental)
            resp = self.pet._call_text_model(messages, temperature=0.95, max_tokens=DEFAULT_MAX_TOKENS, timeout=20)
            if resp.status_code == 200:
                raw_reply = resp.json()["choices"][0]["message"]["content"]
                content_text = ""
                text = raw_reply
                try:
                    data = json.loads(raw_reply)
                    if isinstance(data, dict):
                        content_text = (data.get("content") or "").strip()
                        text = (data.get("comment") or "").strip()
                except Exception:
                    m = re.search(r'\{.*\}', raw_reply, re.DOTALL)
                    if m:
                        try:
                            data = json.loads(m.group(0))
                            if isinstance(data, dict):
                                content_text = (data.get("content") or "").strip()
                                text = (data.get("comment") or "").strip()
                        except Exception:
                            pass
                if not text:
                    text = raw_reply
                emotion, text = self.pet.parse_emotion_from_reply(text)
                self.pet._ui(lambda: self._record_and_show(emotion, text, incremental))
                if self.pet._reading_anchor_needed:
                    self.pet._reading_anchor_needed = False
                    if content_text:
                        self.pet._add_event_memory(content_text, importance=0.7, source="reading")
                    else:
                        threading.Thread(target=self.pet._try_create_reading_event, args=(incremental,), daemon=True).start()
            else:
                fallback = f"(normal) 唔...这段文字好有意思，{user_name}你觉得呢？"
                self.pet._ui(lambda: self._record_and_show("normal", fallback, incremental))
        except Exception as e:
            log.warning(f"读书AI错误: {e}")
            fallback = f"(shy) {user_name}，你读的这一段让我想到了好多呢..."
            self.pet._ui(lambda: self._record_and_show("shy", fallback, incremental))

    def _record_and_show(self, emotion, text, incremental_text=""):
        self.pet.show_bubble_text(text, emotion)
        threading.Thread(target=self.pet._tts_play, args=(text,), daemon=True).start()
        # user 侧标签带上"刚读到的是什么"（像陪玩的画面摘要那样），方便之后聊天时知道读的是哪段；
        # 方括号框架保留，标明这是场景而不是用户发言。读书调用侧会跳过 reading 历史，见 _generate_reply。
        _who = self.pet.user_profile.get('call_name', '你')
        _excerpt = re.sub(r'\s+', ' ', (incremental_text or '')).strip()
        if len(_excerpt) > 50:
            _excerpt = _excerpt[:50] + '…'
        _side = f"[读书中，{_who}在读：{_excerpt}]" if _excerpt else f"[读书中，{_who}正在阅读]"
        self.pet._add_chat_buffer_turn(_side, text, source="reading")
        with self.lock:
            self.last_sent_length = len(self.text_ring)
            self.reading_session_log.append({"text": incremental_text, "comment": text, "ts": time.time()})
            if len(self.reading_session_log) > self.SESSION_LOG_MAX:
                self.reading_session_log.pop(0)

    def recent_digest(self):
        """最近读过的内容（聊天路径用）：限条数 + 限时间窗；读书关掉再开时由 start() 清空。"""
        if not self.reading_session_log:
            return ""
        cutoff = time.time() - self.DIGEST_MINUTES * 60
        items = [e for e in self.reading_session_log if e.get("ts", 0) >= cutoff][-self.DIGEST_MAX:]
        if not items:
            return ""
        return "【最近读过】\n" + "\n".join(f"「{(e.get('text') or '')[:80]}」" for e in items)

    def select_region_interactive(self, callback=None):
        if not mss:
            messagebox.showerror("错误", "缺少截图库 mss")
            return
        with mss.MSS() as sct:
            monitor = sct.monitors[1]
            full = sct.grab(monitor)
            full_img = Image.frombytes("RGB", full.size, full.bgra, "raw", "BGRX")
        base_w = 900
        w_percent = base_w / full_img.width
        thumb = full_img.resize((base_w, int(full_img.height * w_percent)), Image.LANCZOS)
        thumb_w, thumb_h = thumb.size
        thumb_photo = ImageTk.PhotoImage(thumb)
        picker = tk.Toplevel(self.pet.root)
        picker.title("在图片上框选区域")
        picker.configure(bg=DIALOG_BG)
        picker.resizable(False, False)
        picker.transient(self.pet.root)
        picker.grab_set()
        canvas = tk.Canvas(picker, width=thumb_w, height=thumb_h, cursor="cross", highlightthickness=0, bg=DIALOG_BG)
        canvas.pack()
        canvas.create_image(0, 0, anchor="nw", image=thumb_photo)
        canvas.image = thumb_photo
        tk.Label(picker, text="在缩略图上按住鼠标左键拖动，框选你想识别的区域", font=("微软雅黑", 10), bg=DIALOG_BG).pack(pady=5)
        rect_id = None
        start_x = start_y = 0
        def on_press(event):
            nonlocal start_x, start_y, rect_id
            start_x, start_y = event.x, event.y
            if rect_id:
                canvas.delete(rect_id)
            rect_id = canvas.create_rectangle(start_x, start_y, start_x, start_y, outline="red", width=3)
        def on_drag(event):
            if rect_id:
                canvas.coords(rect_id, start_x, start_y, event.x, event.y)
        def on_release(event):
            end_x, end_y = event.x, event.y
            picker.destroy()
            left = min(start_x, end_x) / thumb_w
            top = min(start_y, end_y) / thumb_h
            width = abs(end_x - start_x) / thumb_w
            height = abs(end_y - start_y) / thumb_h
            if width < 0.01 or height < 0.01:
                messagebox.showwarning("区域太小", "框选区域太小，请重新选择")
                if callback:
                    callback(None)
                return
            region = {"left": left, "top": top, "width": width, "height": height}
            self.region = region
            self.save_config()
            if callback:
                callback(region)
        canvas.bind("<ButtonPress-1>", on_press)
        canvas.bind("<B1-Motion>", on_drag)
        canvas.bind("<ButtonRelease-1>", on_release)

if __name__ == "__main__":
    DesktopPet()
