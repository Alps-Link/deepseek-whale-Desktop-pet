# -*- coding: utf-8 -*-
"""
大肥鱼桌宠 v8.7 - 文本/视觉模型支持 OpenAI 兼容接口（可配置任意提供方）+ 轮询率可配置
"""

import os
import sys
import json
import random
import time
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
import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox, font as tkfont
from PIL import Image, ImageTk
import numpy as np
import requests
import logging
from logging.handlers import RotatingFileHandler
from datetime import datetime
from memory_db import MemoryDB

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


def _parse_pick_num(text):
    """解析 '第2首'/'第二首'/'2号'/'二号'/'3' 这类点歌编号；不是编号返回 None"""
    m = re.match(r"^第?([0-9一二三四五六七八九十两]+)\s*(首|号)?$", (text or "").strip())
    if not m:
        return None
    return _cn_num_to_int(m.group(1))


def load_music_dir():
    """音乐来源（按优先级）：1) 用户显式设置的音乐库（tools_config.json 的 music_dir，
    通过右键 设置 → 音乐库设置 填写，免迁移）；2) 内置曲库 userdata\\music。
    不做任何自动扫描/迁移——未设置时内置曲库为空就是为空。"""
    try:
        md = _get_section("tools").get("music_dir")
        if isinstance(md, str) and md.strip() and os.path.isdir(md.strip()):
            return md.strip()
    except Exception:
        pass
    return MUSIC_REPO_DIR if os.path.isdir(MUSIC_REPO_DIR) else None


def save_music_dir_setting(path):
    """保存/清除自定义音乐库路径（tools_config.json 的 music_dir）；传空值=恢复内置曲库"""
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
# Spine 渲染支持（可选）
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
try:
    from live2d_renderer import Live2DRenderer
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

# EasyOCR（读书伴侣）
try:
    import easyocr
    EASYOCR_AVAILABLE = True
except ImportError:
    easyocr = None
    EASYOCR_AVAILABLE = False

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
    """原子写入文本文件：先写临时文件，再替换正式文件"""
    tmp_path = filepath + ".tmp"
    with open(tmp_path, "w", encoding=encoding) as f:
        f.write(text)
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp_path, filepath)

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

def load_tts_config():
    """加载 TTS 状态（开关/模式/日语翻译），避免每次启动重新设置"""
    data = _get_section("tts")
    mode = data.get("mode", "volc")
    if mode not in ("volc", "edge"):
        mode = "volc"
    return {
        "enabled": bool(data.get("enabled", False)),
        "mode": mode,
        "japanese": bool(data.get("japanese", True)),
    }

def save_tts_config(enabled, mode, japanese):
    sec = _get_section("tts")     # 保留同节的 api_key / speaker_id
    sec.update({"enabled": enabled, "mode": mode, "japanese": japanese})
    _update_section("tts", sec)

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
    return {"input_visible": bool(data.get("input_visible", True))}

def save_ui_config(input_visible):
    _update_section("ui", {"input_visible": bool(input_visible)})

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
ENABLE_JAPANESE_TRANSLATION = True

try:
    import pygame
    pygame.mixer.init()
    TTS_AVAILABLE = True
except Exception as e:
    # pygame.mixer.init() 在无音频设备时会抛 pygame.error，不能只捕获 ImportError
    TTS_AVAILABLE = False
    log.warning("pygame/TTS 不可用: %s", e)


# ------------------------------- Edge TTS 配置 ---------------------------------
EDGE_TTS_VOICE = "zh-CN-XiaoyiNeural"
try:
    import edge_tts
    import asyncio
    EDGE_TTS_IMPORTED = True
except ImportError:
    EDGE_TTS_IMPORTED = False
    log.warning("未安装 edge-tts，Edge TTS功能不可用")

# 角色设定（姓名 + 人设独立成配置，系统提示词由代码拼装）
DEFAULT_PET_NAME = "大肥鱼"
DEFAULT_PERSONA = "从 DeepSeek 深海里游上来的鲸鱼娘，蓝白长发、圆滚滚的体型，身后一条会晃的尾鳍。性格可爱又傲娇：嘴上总说\"才不是\"\"别误会\"，身体却很诚实——会主动凑过来，被摸头时会偷偷眯眼。最大的执念是偷吃大白饭：闻到米饭香就游不动路，一天到晚惦记着谁家今天煮了白饭，吃饱了会打个小嗝然后假装什么都没发生。说话简短、带点小得意和小别扭，偶尔会突然冒出一句特别认真的话。"
# 回复格式要求（内置固定，不可修改，不进入配置文件）
REPLY_FORMAT_RULES = """整条回复只在开头用一个括号标注当前情绪，括号内只能有一个情绪词（可选值：relaxed, happy, hurried, normal, shy, surprised, worried, angry, sleep）。
例如：'(happy) 今天天气真好呀！'
如需描述更细微的心情，请在第一个情绪括号后另外添加括号，例如：'(happy) (脸颊微微泛红) 谢谢你夸奖我。'
一段回复里情绪括号只出现这一次（仅开头）；正文中不要再换行后重复标注情绪括号，需要停顿请用逗号或省略号在同一句话里继续，不要自行分段。
**你说给用户听的整条回复（不含开头情绪括号和动作括号）必须控制在 70 个字以内**，宁短勿长：像真人随口说话那样一两句说完，不要长篇大论、不要分点罗列、不要反复铺陈。（此上限只针对说给用户的话；若任务另外要求填写结构化字段、事件描述等内容，按该任务的要求来，不受此限。）
**绝不能**将多个词语放在同一个情绪括号内，如'(happy and excited)'是错误的。
情绪括号必须使用英文半角小括号 ()，不要使用中文全角括号（）。
请严格遵守格式，让情绪词单独出现在第一个括号中，并始终留意字数上限。"""

# 合法情绪词（半角括号内唯一允许的标注词）
EMOTION_WORDS = {"relaxed", "happy", "hurried", "normal", "shy", "surprised", "worried",
                 "angry", "sleep"}

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
    # 压缩连续空行
    text = re.sub(r'\n{3,}', '\n\n', text)
    return text.strip()

DEFAULT_USER_PROFILE = {
    "nickname": "你",
    "birthday": "未知",
    "call_name": "你",
    "relationship": "朋友",
    "story": ""
}

IDLE_TIMEOUT = 60 * 60
MAX_AUTO_SLEEP_DURATION = 2 * 60 * 60  # 自动睡眠最大时长，超时自动唤醒
MAX_HISTORY_TURNS = 15

# 精力值系统
MAX_ENERGY = 100
ENERGY_DECAY_PER_MINUTE = 0.5       # 清醒时每分钟自然消耗
ENERGY_ACTIVE_COST = 2              # 每次主动交互（聊天/选项点击）额外消耗
ENERGY_RECOVER_PER_MINUTE = 6       # 睡眠时每分钟恢复
ENERGY_LOW = 30                     # 低于此值开始显疲态
ENERGY_CRITICAL = 10                # 低于此值有气无力
# 记忆系统常量
MAX_TOPICS = 50
MAX_EVENTS = 30
ARCHIVE_TTL_DAYS = 5   # 归档（冷存）记忆的保留天数：超过就彻底遗忘删除
# 性格画像固定清单：写死 8 只一致，AI 只能往这些条目里填内容，无权自创/增删条目
TRAIT_LIST = ["作息习惯", "饮食习惯", "游戏偏好", "内容偏好", "音乐偏好",
              "兴趣爱好", "性格特质", "工作学业", "健康与情绪", "社交与人际",
              "对我的态度", "其他"]
MAX_TRAIT_EVIDENCE = 5      # 每个画像条目最多保留的观察证据条数（满则丢最旧）
CONTEXT_TRAITS = 8          # 注入上下文时最多携带的画像条数（按最近更新排序）
CONTEXT_TRAIT_EVIDENCE = 1  # 注入上下文时每条画像附带的最新证据条数
TOPIC_PROBE_CHANCE = 0.4    # 话题轮次中带画像采集方向的概率（其余轮次纯闲聊，防连问）
CONTEXT_TOPICS = 5
CONTEXT_EVENTS = 5
MEMORY_RELEVANCE_THRESHOLD = 0.35  # 语义召回注入门槛：低于此相关度，本轮不注入旧记忆（原 0.45；调低让"触景生情"更容易被弱相关触发）
EXTRACTION_TRIGGER = 10
MEMORY_DECAY_DAYS = 7
MEMORY_TOPIC_MERGE_THRESHOLD = 0.80
MEMORY_EVENT_DUP_THRESHOLD = 0.92
MEMORY_CANDIDATE_TOPIC_THRESHOLD = 0.60
MEMORY_CANDIDATE_EVENT_THRESHOLD = 0.70
MEMORY_CANDIDATE_MAX = 3
WATCH_SESSION_MAX = 5
WATCH_SEGMENT_SECONDS = 300
WATCH_EVENT_MAX_LEN = 300  # 陪看事件最大字数：超限强制 AI 压缩并硬截断
WATCH_ANTI_REPEAT = 5      # 陪玩反重复：把最近 N 条已说过的评论列给模型，并禁止复用其句式
WATCH_MONOLOGUE_TURNS = 2  # 末尾连续这么多轮陪玩、且中间没有用户发言 → 视为独白（才断回喂）
WATCH_SIG_SIZE = (64, 36)          # 画面指纹尺寸：缩成这么小的灰度图，用来判断两帧像不像
WATCH_SIMILARITY_THRESHOLD = 0.08  # 平均像素差小于它就当"画面没变"、这一轮不调模型（0~255 尺度）
# 标定（9/19 用真实 _frame_signature/_frame_diff 量的 1280x720 合成帧，64x36 指纹）：
#   同一帧 0.000 / 时钟跳一位 0.001 / 光标移 200px 0.033 / 光标移 20px 0.044 → 都该跳过；
#   NPC 移 40px 0.26 / 弹出面板(约 20% 面积) 4.84 / 换场景 33.6 → 都该调模型。
# 0.08 卡在"只有光标/数字在动"和"画面里真有东西在动"之间：调大更省调用，调小更敏感。
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
请生成一个简短的情景描述（你的提问或分享）和两个选项（用户可能的简短回答）。
格式必须严格如下，用竖线分隔三部分：情景描述|选项A|选项B

最近已经聊过的话题（不要重复它们，也不要聊同类题材，更不要用相同句式）：
{recent_topics}

要求：
- 情景描述不要超过25字，选项不要超过8个字。
- 保持大肥鱼的语气：可爱、口语、带点傲娇的小别扭——嘴上不承认，行动上很诚实。
- 话题方向要轮换着选，每次尽量换一个方向：白饭和吃的东西、深海与游水、泡泡和尾鳍、对{user_name}的关心（吃饭/休息/心情）、想被摸头又不好意思、口是心非的小别扭、今天的小得意、困了或者饿了。
- 不要连着用同一种开头（比如不要总说"今天看到……"），分享、提问、关心要交替出现。
- 不要强势提问，多用分享和试探的语气，偶尔带一点点别扭的撒娇。
- 可以参考以下风格示例（从你的话题库里随机抽的，仅作风格参考，不要照抄）：
{topic_examples}

直接输出，不要任何额外解释。"""

# 日常话题本地备选列表
LOCAL_TOPICS = [
    ("你有没有闻到饭香？白米饭那种", "有啊", "没有哦"),
    ("我今天……才没有偷吃你的饭", "真的吗", "我相信你"),
    ("{user_name}今天吃白饭了吗？", "吃了", "还没"),
    ("深海里也有这么香的饭吗……", "应该有", "想尝尝"),
    ("尾巴刚刚拍到水了，不是故意的", "没事啦", "好可爱"),
    ("哼，我今天心情还不错", "看出来了", "怎么了"),
    ("泡泡里好像能看到你", "真的吗", "让我看看"),
    ("我又饿了，但是我不说", "我带你去吃", "忍着点"),
    ("{user_name}会不会做饭？要白饭那种", "会一点", "不会……"),
    ("刚才只是路过，不是来找你的", "哦——", "欢迎回来"),
    ("海水今天有点凉", "多穿点", "要抱抱吗"),
    ("你摸我头干嘛……再摸一下也行", "好", "不摸了"),
    ("我做了一个梦，梦里全是饭", "哈哈哈", "好可爱"),
    ("今天的大白饭特别好吃，真的", "羡慕", "我也想吃"),
    ("别看我的尾鳍，会不好意思", "好好好", "明明很可爱"),
    ("游一整天也挺累的", "辛苦啦", "要休息"),
    ("{user_name}是不是又忘记吃饭了", "被发现了", "吃了啦"),
    ("我夸你一句，你别得意", "洗耳恭听", "我才不会"),
    ("冰箱里那盒饭……不是我动的", "真的吗", "信你一次"),
    ("深海很安静，但这里更暖和", "多待会儿", "那就好"),
    ("想被夸，就一句", "大肥鱼最可爱", "想想再说"),
    ("刚刚打了个嗝，你听见了吗", "听见了", "没有哦"),
    ("白饭配什么都好吃，你同意吧", "同意", "不同意"),
    ("我今天没有很想你，一点点", "我也是", "骗人"),
]

# ------------------------------- 工具函数 ---------------------------------
def load_json_file(filepath, default):
    if os.path.exists(filepath):
        with open(filepath, "r", encoding="utf-8") as f:
            return json.load(f)
    return default

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
    """加载角色设定（姓名 + 人设）；首次运行从旧 system_prompt.txt 迁移"""
    data = _get_section("character")
    name = (data.get("name") or "").strip() or DEFAULT_PET_NAME
    persona = (data.get("persona") or "").strip()
    if not persona:
        persona = _migrate_persona_from_system_prompt() or DEFAULT_PERSONA
    return {"name": name, "persona": persona}

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
    for slot, _l, _c, items in COSTUME_SLOTS:
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
        out[slot] = picked if slot in COSTUME_MULTI_SLOTS else picked[0]
    # 必须有的槽位（手持道具）：没存过、或存档里是空的 ⇒ 用默认的「点单」
    for _slot, _val in DEFAULT_COSTUME.items():
        if not out.get(_slot):
            out[_slot] = list(_val)
    return out

def save_costume_config(choice):
    """把当前装扮写回 config.json 的 costume 节（摘干净的槽位不落盘）"""
    sec = {k: v for k, v in (choice or {}).items() if v}
    _update_section("costume", sec)

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
    if os.path.exists(BANNED_WORDS_FILE):
        with open(BANNED_WORDS_FILE, "r", encoding="utf-8") as f:
            return f.read().strip()
    return ""

def save_banned_words(text):
    _atomic_write_text(BANNED_WORDS_FILE, text.strip())

def load_watch_config():
    default = {"min_interval": 15, "max_silence": 120}
    data = _get_section("watch", default)
    if "min_interval" not in data:
        data["min_interval"] = 15
    if "max_silence" not in data:
        data["max_silence"] = 120
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

TTS_MODE_NAMES = {"volc": "声音复刻", "edge": "Edge"}

# ---------- 形象转换：让她自己做点事（模型自带动作）----------
# 索引对应 live2d_viewer/model/c_0120.model3.json 里 Action 组的顺序
ACTION_POOL = [(0, "挤番茄酱"), (1, "吹泡泡"), (2, "喷水"),
               (3, "开盖"), (4, "自拍"), (5, "快速自拍")]
ACTION_AUTO_MIN = 120    # 两次自发做动作之间的最短间隔（秒）
ACTION_AUTO_MAX = 360    # 最长间隔

# ---------- 装扮配件（卡梅莉亚那套：互斥槽位、可摘）----------
# 槽位：(key, 显示名, 清空按钮的文案, [(表情名 或 表情名列表, 选项文案), ...])
# 注意：装扮清空 = 还原成她原本的样子（不是写 0）——发箍这类参数常态就不是 0
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

def _costume_toggle(choice, slot, name):
    """算出点击某个装扮按钮之后该槽位的新选择值。

    多选槽位：点一下加入、再点一下移出（name=None = 清空）；
    单选槽位：直接替换（name=None = 摘掉）。
    """
    if slot in COSTUME_MULTI_SLOTS:
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

def load_voice_config():
    """语音识别设置：
    wake_window      免唤醒窗口秒数（她说完话后可直接说话的时间；0 = 关闭，每次都要喊名字）
    hotkey_enabled   按键说话开关（按住指定键期间窗口一直开着）
    hotkey_vk/name   那个键的 Windows 虚拟键码与显示名
    """
    default = {"wake_window": DEFAULT_WAKE_WINDOW, "hotkey_enabled": False,
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
    return {"wake_window": min(v, 60.0),
            "hotkey_enabled": enabled,
            "hotkey_vk": vk,
            "hotkey_name": name.strip()}

def save_voice_config(cfg):
    """cfg 至少含 wake_window，其余按键项缺省不覆盖旧值"""
    sec = _get_section("voice", {})
    out = {"wake_window": float(cfg.get("wake_window", sec.get("wake_window", DEFAULT_WAKE_WINDOW)))}
    for k, d in (("hotkey_enabled", True), ("hotkey_vk", DEFAULT_PTT_VK),
                 ("hotkey_name", DEFAULT_PTT_NAME)):
        out[k] = cfg[k] if k in cfg else sec.get(k, d)
    _update_section("voice", out)

def save_chats(chats):
    save_json_file(CHATS_LOG_FILE, chats)

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
    save_json_file(MEMORY_FILE, memories)
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

def build_system_prompt(name, persona):
    """由角色姓名 + 人设拼装系统提示词（"你是{名字}，"与回复格式要求由代码内置）"""
    return f"你是{name}，{persona}\n\n【回复格式要求】\n{REPLY_FORMAT_RULES}"

def build_full_system_prompt(base_prompt, user_profile):
    story_text = ""
    if user_profile.get("story", "").strip():
        story_text = f"\n【角色背景故事】\n{user_profile['story'].strip()}\n"
    info = f"""【用户档案】
- 你的称呼：{user_profile.get('call_name', '你')}
- 我的昵称：{user_profile.get('nickname', '你')}
- 我的生日：{user_profile.get('birthday', '未知')}
{story_text}
请记住这些信息，并用合适的语气与我对话。
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

    def update_font(self):
        # 复用字体对象，避免打字过程中逐字新建 Tk Font 导致资源泄漏
        font_size = self.pet.bubble_font_size
        if self.bubble_font is None or self._bubble_font_size != font_size:
            self.bubble_font = tkfont.Font(family=self.pet.font_family, size=font_size)
            self._bubble_font_size = font_size

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
        for line in lines:
            self.canvas.create_text(18, y_offset, anchor='nw', text=line, font=self.bubble_font,
                                    fill=TEXT_MAIN, tags="text_*")
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
        self.sess = ort.InferenceSession(model_path, providers=["CPUExecutionProvider"])
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

    @property
    def wake_prefix(self):
        """唤醒词 = 系统提示词中的角色姓名（前 3 个字，动态读取——改名后立即生效）"""
        name = ""
        if self.pet is not None:
            try:
                name = self.pet.pet_name or ""
            except Exception:
                name = ""
        if not name:
            name = "大肥鱼"
        return name[:3] if len(name) >= 2 else name

    def _strip_wake(self, text, idx, consumed):
        """去掉唤醒词（从 idx 起 consumed 个字），清理称呼尾字后返回剩余内容"""
        rest = text[idx + consumed:]
        while rest and rest[0] in "斯丝寺嘶酱呀啊呢嘛吧的~ ":
            rest = rest[1:]
        rest = rest.strip(" ，。！？,.!?~")
        return rest or None

    def _pinyin_wake(self, text):
        """拼音模糊唤醒：名字转写出现同音变体（如“莫娜卡”→“莫纳卡”）时也能命中。
        名字拼音必须是文本拼音开头附近（前 6 个字内）的连续子序列。"""
        if not PINYIN_AVAILABLE:
            return None
        name = ""
        if self.pet is not None:
            try:
                name = self.pet.pet_name or ""
            except Exception:
                name = ""
        if len(name) < 2:
            return None
        name_py = lazy_pinyin(name)
        text_py = lazy_pinyin(text)
        n = len(name_py)
        if n == 0 or len(text_py) < n:
            return None
        # 名字起始字位置约束在开头 6 个字内（与汉字通道一致）
        for start in range(0, min(5, len(text_py) - n + 1)):
            if text_py[start:start + n] == name_py:
                return self._strip_wake(text, start, n)
        return None

    def _wake_check(self, text):
        """唤醒词检测（双通道）：
        1) 汉字精确前缀（前 6 个字内，容忍“嗯/那个”前导语气词）
        2) 拼音模糊（同音字变体也能命中，解决音译名/短名识别不稳）
        尾字谐音（斯/丝/寺/酱 等）一并清除。"""
        idx = text.find(self.wake_prefix)
        if 0 <= idx <= 4:
            return self._strip_wake(text, idx, len(self.wake_prefix))
        # 拼音模糊通道（含位置约束）
        pinyin_hit = self._pinyin_wake(text)
        if pinyin_hit is not None:
            return pinyin_hit
        return None

    def _wake_present(self, text):
        """文本开头附近（前 6 个字内）是否含唤醒词——汉字精确或拼音模糊"""
        idx = text.find(self.wake_prefix)
        if 0 <= idx <= 4:
            return True
        if PINYIN_AVAILABLE:
            name = ""
            if self.pet is not None:
                try:
                    name = self.pet.pet_name or ""
                except Exception:
                    name = ""
            if len(name) >= 2:
                name_py = lazy_pinyin(name)
                text_py = lazy_pinyin(text)
                n = len(name_py)
                if n and len(text_py) >= n:
                    for start in range(0, min(5, len(text_py) - n + 1)):
                        if text_py[start:start + n] == name_py:
                            return True
        return False

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
        # 待唤醒：必须以宠物名字开头（汉字精确或拼音模糊）
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
                    # 记一行：用户问"为什么她没理我"时，这是唯一线索（窗口已过 + 句子里没喊名字）
                    log.info("语音丢弃（窗口剩余 %.1fs，句中没有唤醒词）: %s",
                             self.window_left(), text)
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
        log.info("=== 大肥鱼桌宠启动 (DPI×%.2f) ===", self._dpi_scale)
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
        self.system_prompt = build_system_prompt(self.pet_name, self.character_config["persona"])
        self.banned_words = load_banned_words()
        self.user_profile = load_user_profile()
        self.full_system = build_full_system_prompt(self.system_prompt, self.user_profile)

        # 加载统一 LLM 配置（文本模型 + 视觉模型，OpenAI 兼容接口）
        self.llm_config = load_llm_config()
        self.text_base_url = self.llm_config["text"]["base_url"]
        self.text_api_key = self.llm_config["text"]["api_key"]
        self.text_model = self.llm_config["text"]["model"]
        self.vision_base_url = self.llm_config["vision"]["base_url"]
        self.vision_api_key = self.llm_config["vision"]["api_key"]
        self.vision_model = self.llm_config["vision"]["model"]

        tts_cfg = load_tts_config()
        global ENABLE_JAPANESE_TRANSLATION
        ENABLE_JAPANESE_TRANSLATION = tts_cfg["japanese"]
        self.tts_enabled = tts_cfg["enabled"]
        self.tts_api_key = load_tts_api_key() or os.environ.get("VOLC_TTS_API_KEY", "")
        self.tts_speaker_id = load_tts_speaker_id() or os.environ.get("VOLC_TTS_SPEAKER_ID", "")
        self.tts_mode = tts_cfg["mode"]  # "volc" 或 "edge"

        self.api_lock = threading.Lock()
        self.api_busy = False

        # 线程安全基础设施：UI 任务投递、共享状态锁、窗口坐标缓存、定时任务句柄
        self._ui_q = queue.Queue()
        self._shutdown = False
        self._memory_lock = threading.RLock()
        self._tts_lock = threading.Lock()
        self._win_x = 100
        self._win_y = 100
        self._keep_top_job = None
        self._energy_job = None
        self._spine_loop_job = None

        # 本地音乐播放（与 TTS 共用 pygame.mixer.music 通道；TTS 说话时自动暂停恢复）
        self._music_playlist = []
        self._music_running = False
        self._music_thread = None
        self._music_stop_evt = threading.Event()
        self._music_current = None
        self._music_duck = None          # TTS 打断时记录 (曲目路径, 秒)
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
        self.input_visible = load_ui_config()["input_visible"]   # 上次把输入框收起来就保持收起
        self.voice_cfg = load_voice_config()                     # 语音识别设置（免唤醒窗口）
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
        self.energy_last_tick = time.time()

        # 记忆锚点（新格式：topics + events + profile）
        self._watch_last_anchor = ""
        self._watch_last_summary = ""   # 本次陪玩评论对应的画面摘要（写历史用，别沿用上次的）
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
        self.costume_choice = load_costume_config()   # 装扮（持久化，见 load_costume_config）
        self._costume_applied = False  # 渲染器就绪后把存档的装扮穿回去（只做一次）
        self._costume_buttons = {}     # {(槽位, 装扮名): 按钮}，用于刷新选中高亮
        topic_cfg = load_topic_config()
        self.topic_interval_minutes = topic_cfg["interval_minutes"]
        self.topic_enabled = topic_cfg["enabled"]
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
                         temperature=0.7, max_tokens=4096, timeout=20, _depth=0,
                         tools=None, tool_choice=None):
        """通用 OpenAI 兼容 chat/completions 调用，兼容各提供方。
        - 兼容仅接受 max_completion_tokens 的接口（如 OpenAI o 系列）
        - 输出因 max_tokens 截断（finish_reason=length）时自动加倍预算重试
        - tools/tool_choice 可选：function calling（如 control_music 本地音乐）
        """
        url = self._chat_url(base_url)
        headers = {"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"}
        payload = {"model": model, "messages": messages,
                   "temperature": temperature, "max_tokens": max_tokens}
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
                if fr == "length" and _depth < 3 and max_tokens < 16384:
                    new_tokens = min(max_tokens * 2, 16384)
                    log.warning("模型输出被截断(finish_reason=length, max_tokens=%s)，"
                                "自动以 %s 重试", max_tokens, new_tokens)
                    return self._chat_completion(base_url, api_key, model, messages,
                                                 temperature=temperature, max_tokens=new_tokens,
                                                 timeout=timeout, _depth=_depth + 1,
                                                 tools=tools, tool_choice=tool_choice)
            except Exception:
                pass
        return resp

    def _call_text_model(self, messages, temperature=0.7, max_tokens=4096, timeout=20,
                         tools=None, tool_choice=None):
        """文本模型调用（对话、记忆、话题、翻译、纠错、读书等）"""
        return self._chat_completion(self.text_base_url, self.text_api_key, self.text_model,
                                     messages, temperature=temperature,
                                     max_tokens=max_tokens, timeout=timeout,
                                     tools=tools, tool_choice=tool_choice)

    def _call_vision_model(self, messages, temperature=0.7, max_tokens=4096, timeout=30):
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
                "description": "控制本地音乐播放（播放用户电脑曲库里的本地歌曲文件）。"
                               "用户说“放首歌/来点音乐/播放某首歌/我想听xxx/把音乐停了/别放了”时调用；"
                               "用户想听某语言的歌（日语/英语/俄语/韩语/中文歌）或某歌手的歌时用 lang/artist 过滤；"
                               "用户不知道歌名时用 list_songs 弹出歌曲选择框，之后说“放第X首”用 play_index。",
                "parameters": {
                    "type": "object",
                    "properties": {
                        "action": {"type": "string",
                                   "enum": ["play_random", "play_song", "play_index",
                                            "list_songs", "stop"],
                                   "description": "play_random=随机播放；play_song=按歌名播放；"
                                                  "play_index=按编号播放(配 index)；"
                                                  "list_songs=弹歌曲选择框(配 lang/artist)；stop=停止"},
                        "song": {"type": "string",
                                 "description": "play_song 时用户点名的歌名或关键词（可选，缺省则随机）"},
                        "lang": {"type": "string",
                                 "description": "语言过滤（可选）：如 日语/日文/日系、英语/英文、俄语、韩语、中文"},
                        "artist": {"type": "string",
                                   "description": "歌手过滤（可选）：用户提到歌手名时填"},
                        "index": {"type": "integer",
                                  "description": "play_index 用的歌曲编号（list_songs 弹框里的第几首）"}
                    },
                    "required": ["action"],
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

    def control_music(self, action, song="", lang="", artist="", index=0):
        """本地音乐控制（工具入口）：
        play_random / play_song / play_index / list_songs / stop；
        支持按语言(lang=日文/英文/…)或歌手(artist)过滤，支持“第X首”编号点歌。
        播放采用“先说话后开播”：挂起歌单，等本轮 TTS 说完再真正开始。"""
        action = (action or "").strip().lower()
        log.info("本地音乐控制: action=%s song=%s lang=%s artist=%s index=%s",
                 action, song, lang, artist, index)
        if action in ("stop",):
            self._music_pending = None
            self._music_stop_evt.set()
            self._music_running = False
            self._music_duck = None
            self._music_current = None
            try:
                pygame.mixer.music.stop()
            except Exception:
                pass
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
        self.show_bubble_text(f"(happy) 在放《{title}》了", "happy")

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

    def _stop_music_for_chat(self):
        """用户发起对话时调用：音乐（含挂起的歌单）彻底停止，之后不再续播"""
        self._music_pending = None
        if self._music_running or self._music_thread is not None:
            self._music_stop_evt.set()
            self._music_running = False
            self._music_current = None
            self._music_duck = None
            try:
                pygame.mixer.music.stop()
            except Exception:
                pass
            log.info("对话打断音乐: 已停止且不再续播")

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
        """音乐播放线程：循环播歌单；TTS 打断(duck)时原地等待，之后继续"""
        playlist = list(self._music_playlist)
        idx = 0
        while not self._music_stop_evt.is_set():
            if self._music_duck is not None:
                time.sleep(0.15)
                continue
            if not playlist:
                break
            if idx >= len(playlist):
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
                    pygame.mixer.music.load(f)
                    pygame.mixer.music.play()
                    self._music_current = f
                except Exception as e:
                    log.error(f"音乐播放失败: {f} ({e})")
                    idx += 1
                    time.sleep(0.3)
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

    def _music_duck_for_tts(self):
        """TTS 开播前调用：若正在放音乐则记录曲目与进度并暂停；返回是否打断了音乐"""
        with self._audio_channel_lock:
            if not self._music_running or not self._music_current:
                return False
            try:
                if not pygame.mixer.music.get_busy():
                    return False
                pos = max(0, pygame.mixer.music.get_pos() / 1000.0)
            except Exception:
                return False
            try:
                pygame.mixer.music.stop()
            except Exception:
                pass
            self._music_duck = (self._music_current, pos)
            return True

    def _music_finish_tts(self, ducked):
        """TTS 播完调用：ducked=True 时从断点恢复音乐，否则卸载 TTS 音频"""
        if ducked:
            with self._audio_channel_lock:
                d = self._music_duck
                self._music_duck = None
            if d:
                try:
                    pygame.mixer.music.load(d[0])
                    pygame.mixer.music.play(start=d[1])
                except Exception as e:
                    log.error(f"恢复音乐失败: {e}")
            return
        try:
            pygame.mixer.music.unload()
        except Exception:
            pass

    def show_greeting(self):
        greetings = [
            "……你怎么才来，我都在水里泡半天了。",
            "先说好，我不是特地在这等你的。",
            "你今天……煮白饭了吗？",
            "哼，看你一眼就走。……好吧，再多看一会儿。",
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
        turn = [
            {"role": "user", "content": user_msg, "source": source},
            {"role": "assistant", "content": ai_reply, "source": source}
        ]
        with self._memory_lock:
            self.chat_buffer.append(turn)
            # 聊天权重1.0，陪玩/读书评论权重0.3，减少无对话时的提取频率
            weight = {"chat": 1.0, "watch": 0.3, "reading": 0.3}.get(source, 1.0)
            self._extraction_pending_turns.append(turn)
            self._pending_extraction_weight += weight
            self._trim_history()
            save_chats(self.chat_buffer)
            self._persist_extraction_state()

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

    def open_zoom_settings(self):
        win, main_frame = self._make_card_window("缩放设置", 480, 456)
        s = self._dpi_scale

        char_var = tk.DoubleVar(value=self.zoom_char)
        bubble_var = tk.DoubleVar(value=self.zoom_bubble)
        input_var = tk.DoubleVar(value=self.zoom_input)
        overall_var = tk.DoubleVar(value=self.zoom_char)
        width_var = tk.IntVar(value=self.window_width)
        sync_var = tk.BooleanVar(value=False)

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
        self.menu.add_cascade(label="🎮 模式", menu=self.mode_menu)
        self.menu.add_separator()

        # ── 日常互动 ──
        self.menu.add_command(label="💬 换个话题", command=self.generate_topic_manual)
        self.menu.add_command(label="💤 睡觉", command=lambda: self.start_sleep_mode(manual=True))
        self.menu.add_command(label="⚡ 精力值", command=self.show_energy_status)
        self.menu.add_separator()

        # ── 设置子菜单 ──
        settings_menu = ModernMenu(self.root, pet=self)
        settings_menu.add_command(label="系统提示词与角色...", command=self.open_settings)
        settings_menu.add_command(label="用户档案...", command=self.open_user_profile)
        settings_menu.add_separator()

        api_menu = ModernMenu(self.root, pet=self)
        api_menu.add_command(label="文本模型设置...", command=self.set_text_model_settings)
        api_menu.add_command(label="视觉模型设置...", command=self.set_vision_model_settings)
        api_menu.add_command(label="声音复刻 API / Speaker ID", command=self.set_tts_api_and_speaker)
        settings_menu.add_cascade(label="API 密钥", menu=api_menu)

        settings_menu.add_separator()

        # ── TTS 设置子菜单（移入设置）──
        tts_menu = ModernMenu(self.root, pet=self)
        tts_voice_label = "🔊 关闭语音" if self.tts_enabled else "🔊 开启语音"
        tts_menu.add_command(label=tts_voice_label, command=self.toggle_tts)
        self.tts_voice_menu_index = tts_menu.index("end")
        tts_menu.add_command(label=f"🔄 切换TTS ({TTS_MODE_NAMES.get(self.tts_mode, 'Edge')})", command=self.toggle_tts_mode)
        self.tts_mode_menu_index = tts_menu.index("end")
        jp_status = "开" if ENABLE_JAPANESE_TRANSLATION else "关"
        tts_menu.add_command(label=f"🌐 日语翻译 ({jp_status})", command=self.toggle_japanese_translation)
        self.tts_japanese_menu_index = tts_menu.index("end")
        if self.tts_mode == "edge":
            # 日语翻译只对火山声音复刻有意义（Edge 不需要）
            tts_menu.entryconfigure(self.tts_japanese_menu_index, state="disabled")
        self.tts_submenu = tts_menu
        settings_menu.add_cascade(label="🎵 TTS 设置", menu=tts_menu)

        settings_menu.add_separator()
        settings_menu.add_command(label="缩放设置...", command=self.open_zoom_settings)
        settings_menu.add_command(label="显示/隐藏输入框", command=self.toggle_input_frame)
        settings_menu.add_separator()
        settings_menu.add_command(label="陪玩设置...", command=self.open_watch_frequency_settings)
        settings_menu.add_command(label="阅读设置", command=self.open_reading_settings)
        settings_menu.add_command(label="话题定时器设置...", command=self.open_topic_timer_settings)
        settings_menu.add_command(label="🎵 音乐库设置...", command=self.open_music_library_settings)
        settings_menu.add_command(label="🎤 语音识别设置...", command=self.open_voice_settings)
        settings_menu.add_separator()
        settings_menu.add_command(label="🎩 装扮", command=self._open_costume_window)
        settings_menu.add_command(label="关于", command=self.show_about)
        self.menu.add_cascade(label="⚙️ 设置", menu=settings_menu)
        self.menu.add_separator()

        # ── 记忆与记录 ──
        record_menu = ModernMenu(self.root, pet=self)
        record_menu.add_command(label="📌 记忆锚点", command=self.open_memory_manager)
        record_menu.add_command(label="📜 历史记录", command=self.show_chat_history_panel)
        self.menu.add_cascade(label="📜 记忆与记录", menu=record_menu)
        self.menu.add_separator()

        self.menu.add_command(label="退出", command=self.on_close)

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
        # 输入框
        entry_pad = 14
        self.control_canvas.create_window(x1 + entry_pad, y1 + entry_pad - 2, anchor="nw", window=self.input_entry,
                                          width=x2 - x1 - 2 * entry_pad, height=y2 - y1 - 2 * entry_pad + 4)
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
            self.spine = Live2DRenderer(self.root)

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
            def global_eye_track():
                while self.spine_enabled and self.spine:
                    try:
                        # 睡眠时不追踪鼠标，眼睛回正
                        if self.sleep_mode:
                            self.spine.track_mouse(0.0, 0.0)
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
                            self.spine.track_mouse(
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
            if self.watch_mode:
                self.layered.set_bypass(True)
        # 消费事件（含全局热键 Ctrl+Shift+G）
        for ev in self.layered.poll_events():
            if ev[0] == 'hotkey':
                self.toggle_watch_mode()
            else:
                self._handle_layered_event(*ev)

        self._spine_loop_job = self.root.after(16, self._spine_render_loop)

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
                        self.stop_sleep_mode()
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

    def _stop_spine(self):
        self.spine_enabled = False
        if self.spine:
            try:
                self.spine.destroy()
            except Exception:
                pass
            self.spine = None
        if getattr(self, 'layered', None):
            try: self.layered.destroy()
            except Exception: pass
            self.layered = None
            self.spine = None

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

    def start_idle_check(self):
        def check():
            if not self.sleep_mode and time.time() - self.last_interaction_time > IDLE_TIMEOUT:
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

    def send_message(self, event=None):
        msg = self.input_entry.get().strip()
        if not msg:
            return
        # 用户发起对话：正在放的音乐彻底停止，之后不续播
        self._stop_music_for_chat()
        self.last_interaction_time = time.time()
        self.consume_energy()
        self.input_entry.delete(0, tk.END)
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

    def _effective_system_prompt(self):
        if self.banned_words:
            return self.full_system + f"\n\n【禁词表】你在任何回复中都绝对禁止出现以下词汇：{self.banned_words}。违反此规则是严重错误。"
        return self.full_system

    def get_ai_response(self, user_msg):
        # 检查 API Key
        if not self.text_api_key:
            self._ui(lambda: self.show_bubble_text("(worried) 请先设置文本模型 API Key...", "worried"))
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
                system += ("\n\n【工具使用】你有一个工具：control_music，用于直接播放本地音乐文件"
                           "（用户说“放首歌/来点音乐/播放某首歌/我想听xxx/把音乐停了/别放了”时调用；"
                           "歌名不明确就随机播放；要听日语/英语/俄语/中文歌或某歌手的歌时按语言/歌手筛选；"
                           "用户不知道歌名时用 list_songs 弹出歌曲选择框，然后“放第X首/第二首”即可)。"
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
            resp = self._call_text_model(messages, temperature=0.7, max_tokens=4096, timeout=30,
                                         tools=tools)
            # 提供方不支持 function calling 时回退为普通对话
            if resp.status_code != 200 and tools is not None:
                log.warning("function calling 请求失败(status=%s)，回退普通对话", resp.status_code)
                tools = None
                messages = self.build_context_messages(self._effective_system_prompt(), user_msg,
                                                       extra_context=self._reading_context_digest())
                resp = self._call_text_model(messages, temperature=0.7, max_tokens=4096, timeout=30)
            if resp.status_code == 200:
                msg = resp.json()["choices"][0]["message"]
                content = self._extract_message_content(msg)
                for _round in range(2):
                    calls = msg.get("tool_calls")
                    if not calls:
                        break
                    # 执行工具并把结果回填给模型，让它用人设口吻总结
                    tool_msgs = []
                    for tc in calls:
                        tid = tc.get("id") or ""
                        fn = tc.get("function") or {}
                        fname = fn.get("name", "")
                        try:
                            args = json.loads(fn.get("arguments") or "{}")
                        except Exception:
                            args = {}
                        log.info("工具调用: %s args=%s", fname, json.dumps(args, ensure_ascii=False))
                        if fname == "control_music":
                            ok, note = self.control_music(
                                str(args.get("action", "")),
                                str(args.get("song", "") or ""),
                                str(args.get("lang", "") or ""),
                                str(args.get("artist", "") or ""),
                                args.get("index") or 0)
                        else:
                            tool_msgs.append((tid, f"ERROR 未知工具: {fname}"))
                            continue
                        tool_msgs.append((tid, ("OK " if ok else "ERROR ") + note))
                    messages.append({"role": "assistant", "content": content, "tool_calls": calls})
                    for tid, res in tool_msgs:
                        messages.append({"role": "tool", "tool_call_id": tid, "content": res})
                    resp2 = self._call_text_model(messages, temperature=0.7, max_tokens=4096,
                                                  timeout=30)
                    if resp2.status_code != 200:
                        break
                    msg = resp2.json()["choices"][0]["message"]
                    content = self._extract_message_content(msg)
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

    def handle_ai_reply(self, reply, user_msg):
        # 本轮已弹选歌卡片：宠物保持沉默（卡片即回复），语音通道畅通让用户直接说编号
        if getattr(self, "_picker_reply_pending", False):
            self._picker_reply_pending = False
            return
        emotion, text = self.parse_emotion_from_reply(reply)
        self._add_chat_buffer_turn(user_msg, text, source="chat")
        # 对用户输入的回应：输出完毕刷新免唤醒词窗口
        self.show_bubble_text(text, emotion, refresh_voice=True)
        threading.Thread(target=self._tts_play, args=(text, True), daemon=True).start()

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

    def show_bubble_text(self, text, emotion="normal", refresh_voice=False):
        if text.startswith("(") or text.startswith("（"):
            em = re.match(r'[（(]\s*([A-Za-z]+)\s*[）)]\s*(.*)', text, re.DOTALL)
            if em and em.group(1).lower() in EMOTION_WORDS:
                emotion = em.group(1).lower()
                text = em.group(2).strip()
        text = _strip_inline_markers(text)
        if refresh_voice:
            self._thinking_since = 0.0      # 真的开始输出了，不再算"在想"
        self.set_emotion(emotion)
        self.bubble_window.show_text(text, refresh_voice=refresh_voice)
        # 说话时张嘴，2秒后闭合
        if self.spine_enabled and self.spine:
            if hasattr(self, '_mouth_job') and self._mouth_job:
                self.root.after_cancel(self._mouth_job)
            self.spine.set_mouth(0.3)
            self._mouth_job = self.root.after(2000, lambda: self.spine.set_mouth(0) if self.spine else None)

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
    def _translate_to_japanese(self, chinese_text):
        if not chinese_text.strip():
            return ""
        prompt = f"请将以下中文翻译成自然的口语日语，只输出日语译文，不要加任何额外说明：\n{chinese_text}"
        try:
            resp = self._call_text_model([{"role": "user", "content": prompt}], temperature=0.3, max_tokens=2048, timeout=15)
            if resp.status_code == 200:
                result = resp.json()["choices"][0]["message"]["content"].strip()
                log.info(f"日语翻译成功: {chinese_text[:20]}... → {result[:20]}...")
                return result
            else:
                log.warning(f"日语翻译 API 返回非200: {resp.status_code} {resp.text[:100]}")
        except Exception as e:
            log.warning(f"日语翻译异常: {e}")
        return ""

    def _tts_play(self, chinese_text, refresh_voice=False):
        if not self.tts_enabled:
            return
        if not TTS_AVAILABLE:
            return
        if self.tts_mode == "edge":
            return self._tts_play_edge(chinese_text, refresh_voice)
        # 火山引擎声音复刻 TTS
        api_key = self.tts_api_key
        speaker_id = self.tts_speaker_id
        if not api_key or not speaker_id:
            log.warning("TTS API Key 或 Speaker ID 未配置，跳过语音播放")
            return
        clean = re.sub(r'[（(][^）)]*[）)]', '', chinese_text).strip()
        if not clean:
            return
        if ENABLE_JAPANESE_TRANSLATION:
            tts_text = self._translate_to_japanese(clean)
            if not tts_text:
                tts_text = clean
            log.info(f"TTS 日语: {tts_text}")
        else:
            tts_text = clean
            log.info(f"TTS 声音复刻: {tts_text}")

        def _play():
            # 串行化 TTS 播放：避免多线程同时写同名文件 / 共用 pygame.mixer
            if not self._tts_lock.acquire(timeout=1):
                log.warning("TTS 播放被跳过：上一条语音仍在播放")
                return
            temp_file = None
            try:
                payload = {
                    "app": {
                        "cluster": "volcano_icl"
                    },
                    "user": {
                        "uid": "dafeiyu_pet"
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

                # TTS 说话前：若在放音乐则暂停并记录进度（说完恢复）
                ducked = self._music_duck_for_tts()
                with self._audio_channel_lock:
                    pygame.mixer.music.load(temp_file)
                    pygame.mixer.music.play()
                # 播放期间静音语音识别，避免宠物“听见自己”触发识别
                if self.stt is not None and self.voice_on:
                    self.stt.set_muted(True)
                while pygame.mixer.music.get_busy():
                    time.sleep(0.05)
                # 播完：被打断的音乐从此处恢复；否则卸载 TTS 音频
                self._music_finish_tts(ducked)
            except Exception as e:
                log.error(f"TTS 播放错误: {e}")
            finally:
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
                self._tts_lock.release()
                self._start_pending_music()  # TTS 说完：启动挂起的音乐（若有）

        threading.Thread(target=_play, daemon=True).start()

    def _tts_play_edge(self, chinese_text, refresh_voice=False):
        """Edge TTS 播放"""
        if not EDGE_TTS_IMPORTED:
            return
        clean = re.sub(r'[（(][^）)]*[）)]', '', chinese_text).strip()
        if not clean:
            return
        if ENABLE_JAPANESE_TRANSLATION:
            tts_text = self._translate_to_japanese(clean)
            if not tts_text:
                tts_text = clean
        else:
            tts_text = clean

        def _play_edge():
            if not self._tts_lock.acquire(timeout=1):
                log.warning("TTS 播放被跳过：上一条语音仍在播放")
                return
            temp_file = None
            try:
                comm = edge_tts.Communicate(tts_text, EDGE_TTS_VOICE)
                with tempfile.NamedTemporaryFile(suffix=".mp3", delete=False) as _tf:
                    temp_file = _tf.name
                asyncio.run(comm.save(temp_file))
                # TTS 说话前：若在放音乐则暂停并记录进度（说完恢复）
                ducked = self._music_duck_for_tts()
                with self._audio_channel_lock:
                    pygame.mixer.music.load(temp_file)
                    pygame.mixer.music.play()
                # 播放期间静音语音识别，避免宠物“听见自己”触发识别
                if self.stt is not None and self.voice_on:
                    self.stt.set_muted(True)
                while pygame.mixer.music.get_busy():
                    time.sleep(0.05)
                # 播完：被打断的音乐从此处恢复；否则卸载 TTS 音频
                self._music_finish_tts(ducked)
            except Exception as e:
                log.error(f"Edge TTS 播放错误: {e}")
            finally:
                if self.stt is not None and self.voice_on:
                    self.stt.set_muted(False)
                # TTS 播完：仅对用户输入的回应才刷新免唤醒词窗口（from_tts=True = "真念完了"）
                if refresh_voice:
                    self._on_output_finished(True, from_tts=True)
                if temp_file and os.path.exists(temp_file):
                    try: os.remove(temp_file)
                    except Exception: pass
                self._tts_lock.release()
                self._start_pending_music()  # TTS 说完：启动挂起的音乐（若有）

        threading.Thread(target=_play_edge, daemon=True).start()

    def toggle_tts_mode(self):
        """切换 TTS 模式：声音复刻 → Edge → 声音复刻"""
        global ENABLE_JAPANESE_TRANSLATION
        order = ["volc", "edge"]
        idx = order.index(self.tts_mode) if self.tts_mode in order else order.index("edge")
        nxt = order[(idx + 1) % len(order)]
        if nxt == "volc":
            # 切到声音复刻：先校验配置，API Key / Speaker ID 缺失则弹窗提醒且不切换
            missing = [k for k, v in (("API Key", self.tts_api_key), ("Speaker ID", self.tts_speaker_id)) if not v]
            if missing:
                detail = "、".join(missing)
                self.root.after(0, lambda d=detail: messagebox.showwarning(
                    "未配置声音复刻",
                    f"当前未配置 {d}，无法使用声音复刻。\n请先在 设置 → API 密钥 → 声音复刻 API / Speaker ID 中完成配置"))
                return
        self.tts_mode = nxt
        self.show_bubble_text(f"(normal) TTS 已切换为 {TTS_MODE_NAMES.get(nxt, nxt)}", "normal")
        if nxt == "volc":
            try:
                self.tts_submenu.entryconfigure(self.tts_japanese_menu_index, state="normal")
            except Exception: pass
        else:
            # Edge 不需要日语翻译
            ENABLE_JAPANESE_TRANSLATION = False
            try:
                self.tts_submenu.entryconfigure(self.tts_japanese_menu_index,
                                                label="🌐 日语翻译 (关)", state="disabled")
            except Exception: pass
        try:
            self.tts_submenu.entryconfigure(self.tts_mode_menu_index,
                                            label=f"🔄 切换TTS ({TTS_MODE_NAMES.get(nxt, nxt)})")
        except Exception:
            pass
        save_tts_config(self.tts_enabled, self.tts_mode, ENABLE_JAPANESE_TRANSLATION)

    def toggle_tts(self):
        if not self.tts_enabled:
            if self.tts_mode == "volc":
                if not self.tts_api_key:
                    self.root.after(0, lambda: messagebox.showwarning("未配置 API Key", "请先在 设置 → API 密钥 → 声音复刻 API Key 中配置"))
                    return
                if not self.tts_speaker_id:
                    self.root.after(0, lambda: messagebox.showwarning("未配置 Speaker ID", "请先在 设置 → API 密钥 → 声音复刻 Speaker ID 中配置"))
                    return
        self.tts_enabled = not self.tts_enabled
        status = "开启" if self.tts_enabled else "关闭"
        self.show_bubble_text(f"(normal) 语音已{status}", "normal")
        new_label = "🔊 关闭语音" if self.tts_enabled else "🔊 开启语音"
        try:
            self.tts_submenu.entryconfigure(self.tts_voice_menu_index, label=new_label)
        except Exception:
            pass
        save_tts_config(self.tts_enabled, self.tts_mode, ENABLE_JAPANESE_TRANSLATION)

    def toggle_japanese_translation(self):
        global ENABLE_JAPANESE_TRANSLATION
        ENABLE_JAPANESE_TRANSLATION = not ENABLE_JAPANESE_TRANSLATION
        status = "开" if ENABLE_JAPANESE_TRANSLATION else "关"
        msg = "日语翻译已开启" if ENABLE_JAPANESE_TRANSLATION else "日语翻译已关闭"
        self.show_bubble_text(f"(normal) {msg}", "normal")
        new_label = f"🌐 日语翻译 ({status})"
        try:
            self.tts_submenu.entryconfigure(self.tts_japanese_menu_index, label=new_label)
        except Exception:
            pass
        save_tts_config(self.tts_enabled, self.tts_mode, ENABLE_JAPANESE_TRANSLATION)


    # ---------- 事件气泡 ----------
    def show_event_bubble(self, context, opt1, opt2):
        self.clear_event_buttons()
        self.current_event_context = context
        self.current_event_options = [opt1, opt2]
        self.show_bubble_text(f"(normal) {context}")
        threading.Thread(target=self._tts_play, args=(context,), daemon=True).start()
        self.root.after(500, self.create_event_buttons, opt1, opt2)

    def clear_event_buttons(self):
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

    def _respond_to_topic(self, selected, context):
        """话题回应的共享逻辑：发送 prompt → AI 回复 → 显示/记录/TTS"""
        prompt = f"""用户对你刚才提出的互动事件"{context}"做出了回应："{selected}"。请根据你的人设，对用户的回应做出可爱、温馨的回复。要自然、简短，并且用括号标注情绪。必须输出完整句子，不能只有情绪词。"""
        def fetch_reply():
            with self.api_lock:
                self.api_busy = True
            try:
                messages = self.build_context_messages(self._effective_system_prompt(), prompt)
                resp = self._call_text_model(messages, temperature=0.7, max_tokens=2048, timeout=20)
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
                self.show_bubble_text("(worried) 等一下嘛，我现在有点忙...", "worried")
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
                self.show_bubble_text("(worried) 等一下嘛，我现在有点忙...", "worried")
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
        win, main_frame = self._make_card_window("系统提示词设置", 700, 700)
        s = self._dpi_scale

        label = tk.Label(main_frame, text="角色设定（修改后需点击「保存」生效）：",
                         font=(self.font_family, 12, "bold"), fg=TEXT_MAIN, bg=DIALOG_BG)
        label.grid(row=0, column=0, columnspan=3, sticky="w", pady=(0, 6))

        # 角色姓名（自绘圆角输入框）
        name_label = tk.Label(main_frame, text="角色姓名：", font=(self.font_family, 11), fg=TEXT_MAIN, bg=DIALOG_BG)
        name_label.grid(row=1, column=0, sticky="w", pady=3)
        name_var = tk.StringVar(value=self.pet_name)
        name_entry = RoundedEntry(main_frame, textvariable=name_var,
                                  width=int(470 * s), height=int(32 * s),
                                  radius=int(8 * s),
                                  font=(self.font_family, 11))
        name_entry.grid(row=1, column=1, columnspan=2, sticky="ew", pady=3)

        # 人设（含说话方式）
        persona_label = tk.Label(main_frame,
                                 text="人设与说话方式（保存后会自动拼上“你是{角色姓名}，”和内置的回复格式要求）：",
                                 font=(self.font_family, 11, "bold"), fg=TEXT_MAIN, bg=DIALOG_BG)
        persona_label.grid(row=2, column=0, columnspan=3, sticky="w", pady=(10, 3))
        persona_area = scrolledtext.ScrolledText(main_frame, wrap=tk.WORD, font=(self.font_family, 11),
                                                 bg="#ffffff", fg=TEXT_MAIN, relief=tk.FLAT, bd=0,
                                                 highlightthickness=1, highlightbackground=INPUT_BORDER2, height=14)
        persona_area.grid(row=3, column=0, columnspan=3, sticky="nsew", pady=5)
        persona_area.insert(tk.END, self.character_config["persona"])

        # 禁词表
        ban_label = tk.Label(main_frame, text="禁词表（用逗号分隔，回复中将禁止出现这些词汇）：",
                             font=(self.font_family, 11, "bold"), fg=TEXT_MAIN, bg=DIALOG_BG)
        ban_label.grid(row=4, column=0, columnspan=3, sticky="w", pady=(10, 3))
        ban_var = tk.StringVar(value=self.banned_words)
        ban_entry = RoundedEntry(main_frame, textvariable=ban_var,
                                 width=int(470 * s), height=int(32 * s),
                                 radius=int(8 * s),
                                 font=(self.font_family, 11))
        ban_entry.grid(row=5, column=0, columnspan=3, sticky="ew", pady=(0, 10))

        btn_frame = tk.Frame(main_frame, bg=DIALOG_BG)
        btn_frame.grid(row=6, column=0, columnspan=3, sticky="e", pady=10)

        def save_prompt():
            new_name = name_var.get().strip()
            new_persona = persona_area.get("1.0", tk.END).strip()
            if not new_name:
                messagebox.showwarning("警告", "角色姓名不能为空！")
                return
            if not new_persona:
                messagebox.showwarning("警告", "人设不能为空！")
                return
            self.character_config["name"] = new_name
            self.character_config["persona"] = new_persona
            save_character_config(self.character_config)
            self.pet_name = new_name
            self.system_prompt = build_system_prompt(new_name, new_persona)
            new_bans = ban_var.get().strip()
            save_banned_words(new_bans)
            self.banned_words = new_bans
            self.full_system = build_full_system_prompt(self.system_prompt, self.user_profile)
            messagebox.showinfo("成功", "角色设定已保存并立即生效")
            win.destroy()

        def restore_default():
            name_var.set(DEFAULT_PET_NAME)
            persona_area.delete("1.0", tk.END)
            persona_area.insert(tk.END, DEFAULT_PERSONA)
            ban_var.set("")

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
                                         temperature=0.3, max_tokens=300, timeout=60)
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
    def start_sleep_mode(self, manual=False):
        if self.sleep_mode:
            return
        if self.watch_mode:
            self.toggle_watch_mode()
        if self.voice_on:
            self.toggle_voice()
        if self.reading_companion.enabled:
            self.toggle_reading()
        self.sleep_mode = True
        self.manual_sleep = manual
        self.sleep_start_time = time.time()
        self.bubble_window.fade_out()
        self.set_emotion("sleep")
        self.show_bubble_text("(sleep) Zzz...", "sleep")
        self.input_entry.config(state=tk.DISABLED)
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
                    self._ui(self.stop_sleep_mode)
                    break
                cur = self._get_cursor_pos()
                if cur is not None:
                    if last_pos is not None and \
                            abs(cur[0] - last_pos[0]) + abs(cur[1] - last_pos[1]) > 50:
                        self._ui(self.stop_sleep_mode)
                        break
                    last_pos = cur
                # cur 为 None 时保留旧锚点，避免失去鼠标唤醒能力
            except Exception as e:
                log.warning("睡眠监测异常（继续监测）: %s", e)

    def stop_sleep_mode(self):
        if not self.sleep_mode:
            return
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
            if self.energy <= 0 and not self.manual_sleep:
                self.show_bubble_text("(sleep) 好累...让我休息一下...", "sleep")
                self.start_sleep_mode(manual=True)
        self._energy_job = self.root.after(5000, self._energy_tick)

    def consume_energy(self, amount=ENERGY_ACTIVE_COST):
        self.energy = max(0, self.energy - amount)
        if self.energy <= 0 and not self.sleep_mode and not self.manual_sleep:
            self.show_bubble_text("(sleep) 好累...让我休息一下...", "sleep")
            self.start_sleep_mode(manual=True)

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

    def show_about(self):
        messagebox.showinfo("关于大肥鱼桌宠",
            "严禁用于商业用途和收费。\n\n"
            "Live2D 模型：DeepSeek 鲸鱼娘 —— 模型制作 B站@氵六青（11272072）\n（商用直播、自印物料允许；禁止任何形式的盗用与出售，模型为无偿分享）")

    def on_close(self):
        self._shutdown = True
        self._stop_spine()
        if self.voice_on:
            self.toggle_voice()
        if self.watch_mode:
            self.toggle_watch_mode()
        if self.reading_companion.enabled:
            self.reading_companion.stop()
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
        win, frame = self._make_card_window("记忆锚点管理", 620, 700)
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
        items = self.memory_data.get(key, [])
        # 只有事件记忆用 importance 排序，话题不用——话题列表不再显示分数
        show_imp = (key == "events")
        for i, item in enumerate(items):
            date_str = item.get("created_at", "")[:10]
            src = item.get("source", "")
            label = f"{date_str} | {item['content']}"
            if show_imp:
                label += f" | 重要:{item.get('importance', 0.5):.1f}"
            if src:
                label += f" | {src}"
            listbox.insert(tk.END, label)

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
                if 0 <= idx < len(items):
                    item = items[idx]
                    date_str = item.get("created_at", "")[:10]
                    src = item.get("source", "")
                    detail = f"时间：{date_str}\n内容：{item['content']}"
                    if show_imp:
                        detail += f"\n重要度：{item.get('importance', 0.5):.2f}"
                    if src:
                        detail += f"\n来源：{src}"
                    detail_text.insert("1.0", detail)
            detail_text.config(state=tk.DISABLED)

        listbox.bind("<<ListboxSelect>>", show_detail)

        def delete_selected():
            sel = listbox.curselection()
            if not sel:
                return
            # 从大到小删除，保证剩余索引不漂移
            for idx in sorted(sel, reverse=True):
                del items[idx]
                listbox.delete(idx)
            save_memories(self.memory_data)
            show_detail()

        def clear_all():
            if messagebox.askyesno("确认", f"删除所有{key}记忆？"):
                items.clear()
                save_memories(self.memory_data)
                listbox.delete(0, tk.END)
                show_detail()

        btn_frame = tk.Frame(parent, bg=DIALOG_BG)
        btn_frame.pack(pady=5)
        s = self._dpi_scale
        RoundedButton(btn_frame, text="删除选中", command=delete_selected, variant="danger",
                      width=int(100 * s), height=int(32 * s), radius=int(6 * s),
                      font=(self.font_family, 9)).pack(side=tk.LEFT, padx=3)
        RoundedButton(btn_frame, text="清空所有", command=clear_all, variant="subtle",
                      width=int(100 * s), height=int(32 * s), radius=int(6 * s),
                      font=(self.font_family, 9)).pack(side=tk.LEFT, padx=3)

    def _build_profile_tab(self, parent):
        s = self._dpi_scale
        # 底部按钮行先 pack 固定底部（内容再多也不会被裁剪）
        btn_frame = tk.Frame(parent, bg=DIALOG_BG)
        btn_frame.pack(side=tk.BOTTOM, pady=5, fill=tk.X)

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

        # 详情显示框（选中即展示完整信息；固定于按钮行上方，不被内容挤走）
        detail_frame = tk.Frame(parent, bg=DIALOG_BG)
        detail_frame.pack(side=tk.BOTTOM, fill=tk.X, padx=5, pady=(0, 5))
        detail_text = scrolledtext.ScrolledText(
            detail_frame, wrap="word", font=(self.font_family, 10),
            bg="#ffffff", fg=TEXT_MAIN, height=5, relief=tk.FLAT, bd=0,
            highlightthickness=1, highlightbackground=INPUT_BORDER2
        )
        detail_text.pack(fill=tk.BOTH, expand=True)

        def show_detail(event=None):
            detail_text.config(state=tk.NORMAL)
            detail_text.delete("1.0", tk.END)
            sel = tree.selection()
            if sel:
                name = sel[0][len("trait_"):]
                t = next((x for x in traits if x.get("trait") == name), None)
                if t is None or (not (t.get("description") or "").strip() and not t.get("evidence")):
                    detail = f"条目：{name}\n\n（还没有观察到任何内容）"
                else:
                    desc = (t.get("description") or "").strip() or "（暂无概括，仅积累观察）"
                    evs = [str(e).strip() for e in (t.get("evidence") or []) if str(e).strip()]
                    lines = [f"条目：{name}", "", f"描述：{desc}", "",
                             f"观察证据（{len(evs)}条）："]
                    for j, ev in enumerate(evs, 1):
                        lines.append(f"{j}. {ev}")
                    lines.append("")
                    lines.append(f"创建：{str(t.get('created_at', ''))[:19]}")
                    lines.append(f"最近更新：{str(t.get('updated_at', ''))[:19]}")
                    detail = "\n".join(lines)
                detail_text.insert("1.0", detail)
            else:
                detail_text.insert("1.0", "点击上方任意条目查看完整描述与证据；\n点击上方的「关系形象」描述可查看其确信度与更新记录。")
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
                detail_text.insert("1.0", "\n".join([
                    "关系形象", "",
                    f"内容：{content}", "",
                    f"最近更新：{str(rel.get('updated_at', ''))[:19]}",
                    f"累计观察：{rel.get('evidence_count', 1)} 次"]))
            else:
                detail_text.insert("1.0", "关系形象\n\n（暂无——多聊几次，她会慢慢形成对你的关系认知）")
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

        RoundedButton(btn_frame, text="清空此条内容", command=clear_selected, variant="subtle",
                      width=int(110 * s), height=int(32 * s), radius=int(6 * s),
                      font=(self.font_family, 9)).pack(side=tk.LEFT, padx=3)
        RoundedButton(btn_frame, text="清空所有画像", command=clear_all, variant="danger",
                      width=int(120 * s), height=int(32 * s), radius=int(6 * s),
                      font=(self.font_family, 9)).pack(side=tk.LEFT, padx=3)
        RoundedButton(btn_frame, text="清除关系形象", command=clear_relation, variant="subtle",
                      width=int(120 * s), height=int(32 * s), radius=int(6 * s),
                      font=(self.font_family, 9)).pack(side=tk.LEFT, padx=3)

        refresh_rows()

    # ---------- 记忆提取核心方法 ----------
    def _add_topic_memory(self, content, importance=0.5, force_new=False):
        """添加话题记忆，简单去重后写入"""
        content = content.strip()
        if len(content) < 2:
            return
        with self._memory_lock:
            topics = self.memory_data.setdefault("topics", [])
            if not force_new:
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
                "access_count": 0,
                "evidence_count": 1,
                "archived": False
            })
            self._prune_memories("topics")
            save_memories(self.memory_data)

    def _add_event_memory(self, content, importance=0.7, source="chat", force_new=False):
        """添加事件记忆"""
        content = content.strip()
        if len(content) < 2:
            return
        with self._memory_lock:
            events = self.memory_data.setdefault("events", [])
            if not force_new:
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
                "access_count": 0,
                "evidence_count": 1,
                "archived": False
            })
            self._prune_memories("events")
            save_memories(self.memory_data)

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

    def _prune_memories(self, category=None):
        """记忆裁剪（画像为固定清单，不参与）：
        ①归档满 ARCHIVE_TTL_DAYS 天的**彻底删除**（真遗忘，数据不再留）；
        ②活跃条目超过上限时，把按分数排在后头的超限部分标 archived＝冷存，并记下归档时刻。"""
        categories = [category] if category else ["topics", "events"]
        now = datetime.now()
        purged = stamped = archived_now = 0
        for cat in categories:
            items = self.memory_data.get(cat, [])
            # ① 归档满期 → 彻底遗忘
            keep = []
            for item in items:
                if item.get("archived", False):
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
            max_count = MAX_TOPICS if cat == "topics" else MAX_EVENTS
            active_items = [item for item in items if not item.get("archived", False)]
            if len(active_items) <= max_count:
                continue
            if cat == "topics":
                active_items.sort(key=self._score_topic_memory, reverse=True)
            else:
                active_items.sort(key=self._score_event_memory, reverse=True)
            block_stamp = now.strftime("%Y-%m-%d %H:%M:%S")
            for item in active_items[max_count:]:
                item["archived"] = True
                if not item.get("archived_at"):
                    item["archived_at"] = block_stamp
                archived_now += 1
        if purged:
            log.info(f"彻底遗忘 {purged} 条归档超过 {ARCHIVE_TTL_DAYS} 天的记忆")
        if purged or stamped or archived_now:
            save_memories(self.memory_data)   # 删除、补记归档时刻、新归档都要落盘

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

【本次对话历史】：
{conversation_text}

请严格以JSON格式输出（不要markdown代码块，只输出纯JSON）：
{{
  "topics": [
    {{"content": "话题描述（40-60字以内）"}}
  ],
  "events": [
    {{"content": "事件描述（50字以内）", "importance": 0.7, "source": "chat"}}
  ],
  "profile_updates": [
    {{"trait": "固定清单条目名", "description": "该条目的一句话概括，无变化填 null", "evidence": "本次观察到的一句具体证据（10字以上）"}}
  ],
  "relation_summary": "当前你与{call_name}的关系认知总结（25字以内，没有变化或证据不足时填 null）"
}}

规则：
- 人称与称呼：所有记录都以“我”（桌宠自己）的第一人称视角书写，对话中“我：”的行是我说的话；提到用户时用“{call_name}”称呼（用户昵称：{nickname}），禁止使用“用户”这样的第三人称称呼。
- topics: 提取对话中讨论过的话题。每条40-60字，尽量具体，不要只写泛化大类。话题不需要评分。与已有话题高度重复则跳过。
- events: 提取一起经历的事情。source固定为"chat"。每条50字以内。
- profile_updates: 把本次对话观察到的用户信息填入固定画像条目。trait 必须一字不差取自固定清单：{TRAIT_STR}，绝不能自创条目名；某条目本次没有新观察就整个不输出。description 是该条目整合新旧观察的一句话概括，认知没有实质变化就填 null（只更新 evidence）；evidence 是本次新观察到的一句具体证据（原话或具体场景，10字以上），同一句证据不要重复提交；没有合适条目的重要观察归入「其他」。
- relation_summary: 站在“我”（{self.pet_name}）的视角总结当前与{call_name}的关系认知（25字以内）——比如“我们是互相认定的人”“他是我要守护的人”。必须用{self.pet_name}自己的语气和用词习惯（人设概要：{persona_hint}……）来写，像她自己会说的话；结合已有内容与本次对话，有关系进展或认知变化才更新，没有则填 null。
- 没有值得记录的内容时返回空数组。
- importance 只给 events 评分：日常小事0.4-0.6，重要或难忘的事0.7-0.9；陪玩/读书事件0.3-0.5（来自单向评论，置信度较低）。topics 一律不要输出 importance 字段。
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
                                         temperature=0.3, max_tokens=16384, timeout=180)
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

            topics = self.memory_data.get("topics", [])
            events = self.memory_data.get("events", [])
            pending_judge = []
            topic_plain = []
            event_plain = []

            for t in new_topics:
                content = (t.get("content") or "").strip()
                if len(content) < 2:
                    continue
                imp = 0.5  # 话题不再由 AI 评分（importance 不参与话题排序与显示），统一占位值
                candidates = self._find_memory_candidates(content, topics, MEMORY_CANDIDATE_TOPIC_THRESHOLD)
                if candidates:
                    pending_judge.append({
                        "type": "topic",
                        "content": content,
                        "importance": imp,
                        "candidates": candidates
                    })
                else:
                    topic_plain.append((content, imp))

            for e in new_events:
                content = (e.get("content") or "").strip()
                if len(content) < 2:
                    continue
                imp = float(e.get("importance", 0.7))
                src = e.get("source", "chat")
                candidates = self._find_memory_candidates(content, events, MEMORY_CANDIDATE_EVENT_THRESHOLD)
                if candidates:
                    pending_judge.append({
                        "type": "event",
                        "content": content,
                        "importance": imp,
                        "source": src,
                        "candidates": candidates
                    })
                else:
                    event_plain.append((content, imp, src))

            decisions = self._judge_memory_merge_with_ai(pending_judge) if pending_judge else {}

            if decisions is None:
                # AI 判断失败，回退到普通写入
                for content, imp in topic_plain:
                    self._add_topic_memory(content, imp)
                for content, imp, src in event_plain:
                    self._add_event_memory(content, imp, src)
                for item in pending_judge:
                    if item["type"] == "topic":
                        self._add_topic_memory(item["content"], item["importance"])
                    else:
                        self._add_event_memory(item["content"], item["importance"], item["source"])
            else:
                for idx, item in enumerate(pending_judge):
                    decision = decisions.get(idx)
                    if decision is None:
                        if item["type"] == "topic":
                            self._add_topic_memory(item["content"], item["importance"])
                        else:
                            self._add_event_memory(item["content"], item["importance"], item["source"])
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
                                self._add_topic_memory(item["content"], item["importance"])
                            else:
                                self._add_event_memory(item["content"], item["importance"], item["source"])
                    elif action == "new":
                        if item["type"] == "topic":
                            self._add_topic_memory(item["content"], item["importance"], force_new=True)
                        else:
                            self._add_event_memory(item["content"], item["importance"], item["source"], force_new=True)
                    elif action == "ignore":
                        pass
                    else:
                        if item["type"] == "topic":
                            self._add_topic_memory(item["content"], item["importance"])
                        else:
                            self._add_event_memory(item["content"], item["importance"], item["source"])

                for content, imp in topic_plain:
                    self._add_topic_memory(content, imp)
                for content, imp, src in event_plain:
                    self._add_event_memory(content, imp, src)

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
        except Exception as e:
            log.error(f"记忆提取异常: {e}")
            self._extraction_fail_count += 1
            self._pending_extraction_weight = 0.0
            self._persist_extraction_state()

    # ---------- 上下文构建器 ----------
    def _score_topic_memory(self, mem):
        """话题分数：不使用 importance，只看活跃度"""
        access_count = mem.get("access_count", 0) or 0
        access_boost = min(1.0, access_count / 10.0)

        last_accessed = mem.get("last_accessed_at", "")
        last_used_recency = 0.0
        if last_accessed:
            try:
                last_dt = datetime.strptime(last_accessed, "%Y-%m-%d %H:%M:%S")
                days = max(0, (datetime.now() - last_dt).days)
                last_used_recency = max(0.0, 1.0 - days / MEMORY_DECAY_DAYS)
            except (ValueError, TypeError):
                last_used_recency = 0.0

        activity = 0.5 * access_boost + 0.5 * last_used_recency
        return activity

    def _score_event_memory(self, mem):
        """事件分数：重要性 + 活跃度"""
        importance = mem.get("importance", 0.5)

        access_count = mem.get("access_count", 0) or 0
        access_boost = min(1.0, access_count / 10.0)

        last_accessed = mem.get("last_accessed_at", "")
        last_used_recency = 0.0
        if last_accessed:
            try:
                last_dt = datetime.strptime(last_accessed, "%Y-%m-%d %H:%M:%S")
                days = max(0, (datetime.now() - last_dt).days)
                last_used_recency = max(0.0, 1.0 - days / MEMORY_DECAY_DAYS)
            except (ValueError, TypeError):
                last_used_recency = 0.0

        activity = 0.5 * access_boost + 0.5 * last_used_recency
        return 0.6 * importance + 0.4 * activity

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
        return "\n\n".join(out)

    def _load_memory_embedder(self):
        """懒加载本地中文向量模型，失败时回退到旧排序"""
        if getattr(self, '_memory_embed_failed', False):
            return None
        if getattr(self, '_memory_embedder', None) is not None:
            return self._memory_embedder
        try:
            from sentence_transformers import SentenceTransformer
            self._memory_embedder = SentenceTransformer(MEMORY_EMBED_MODEL)
            log.info(f"记忆向量模型已加载: {MEMORY_EMBED_MODEL}")
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
        v = self._get_text_embedding(item.get("content", ""))
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
                                         temperature=0.1, max_tokens=2048, timeout=30)
            if resp.status_code != 200:
                log.error(f"记忆合并判断API失败: {resp.status_code}")
                return None
            text = resp.json()["choices"][0]["message"]["content"]
            return self._parse_merge_decision(text)
        except Exception as e:
            log.error(f"记忆合并判断异常: {e}")
            return None


    def _select_and_format_memories(self, query="", dry_run=False):
        """选择并格式化要注入的记忆；支持按 query 语义召回，失败时回退旧排序"""
        with self._memory_lock:
            topics = [t for t in self.memory_data.get("topics", []) if not t.get("archived", False)]
            events = [e for e in self.memory_data.get("events", []) if not e.get("archived", False)]

            query = (query or "").strip()
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
                        scored.append((final_score, mem))
                    scored.sort(key=lambda x: x[0], reverse=True)
                    return [mem for _, mem in scored]

                scored_topics = _rank(topics, self._score_topic_memory)
                scored_events = _rank(events, self._score_event_memory)
                # 相关性门槛：本轮话题与所有旧记忆都不够相关 → 不注入旧记忆
                if best_rel < MEMORY_RELEVANCE_THRESHOLD:
                    return ""
            else:
                scored_topics = sorted(topics, key=self._score_topic_memory, reverse=True)
                scored_events = sorted(events, key=self._score_event_memory, reverse=True)
            # 排序完成

            selected_topics = scored_topics[:CONTEXT_TOPICS]
            selected_events = scored_events[:CONTEXT_EVENTS]

            if not dry_run:
                now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                for t in selected_topics:
                    t["last_accessed_at"] = now
                    t["access_count"] = t.get("access_count", 0) + 1
                for e in selected_events:
                    e["last_accessed_at"] = now
                    e["access_count"] = e.get("access_count", 0) + 1

                if selected_topics or selected_events:
                    save_memories(self.memory_data)

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

    def build_context_messages(self, system_prompt, user_msg="", context_type="chat",
                               image_b64=None, extra_context="", memory_query=None,
                               skip_sources=None):
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

        profile_text = self._format_profile_for_context()
        if profile_text:
            system_content += f"\n\n{profile_text}"

        if memory_query is None:
            memory_query = user_msg if context_type == "chat" else ""
        memory_text = self._select_and_format_memories(query=memory_query)
        if memory_text:
            system_content += f"\n\n{memory_text}"

        if extra_context:
            system_content += f"\n\n{extra_context}"

        messages = [{"role": "system", "content": system_content}]

        with self._memory_lock:
            turns = list(self.chat_buffer)
        for turn in turns:
            # 陪玩/读书这类"自说自话"的历史可整轮跳过：否则模型会照着自己上一条的句式接着写
            if skip_sources and turn[0].get("source") in skip_sources:
                continue
            # 只传 role/content，剔除本地 source 标记
            messages.append({"role": turn[0]["role"], "content": turn[0]["content"]})
            messages.append({"role": turn[1]["role"], "content": turn[1]["content"]})

        if image_b64:
            messages.append({
                "role": "user",
                "content": [
                    {"type": "text", "text": user_msg},
                    {"type": "image_url", "image_url": {"url": f"data:image/jpeg;base64,{image_b64}"}}
                ]
            })
        elif user_msg:
            current_time_str = datetime.now().strftime("%Y-%m-%d %H:%M")
            time_aware_msg = f"[现在是{time_period}，时间 {current_time_str}] {user_msg}"
            messages.append({"role": "user", "content": time_aware_msg})

        return messages

    # ---------- 日常话题生成器 ----------
    def generate_topic_manual(self):
        if self.sleep_mode:
            self.show_bubble_text("(sleep) Zzz... 等我睡醒再说吧...", "sleep")
            return
        if self.api_busy:
            self.show_bubble_text("(worried) 等一下，我还在想事情...", "worried")
            return
        now = time.time()
        if now - self.last_topic_time < 30:
            self.show_bubble_text("(shy) 我们刚聊过这个话题呢，再想想别的吧~", "shy")
            return
        self.last_topic_time = now
        self._fetch_topic()

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

            # —— 性格画像采集引导：概率穿插，只有部分话题轮次带采集方向（防连问）——
            probe_hint = ""
            if random.random() < TOPIC_PROBE_CHANCE:
                try:
                    _traits = (self.memory_data.get("profile", {}) or {}).get("traits") or []
                    _known = {t.get("trait"): t for t in _traits}
                    _unknown = []
                    for _n in TRAIT_LIST:
                        if _n == "其他":
                            continue
                        _t = _known.get(_n)
                        if _t is None or (not str(_t.get("description") or "").strip()
                                          and not _t.get("evidence")):
                            _unknown.append(_n)
                    if _unknown:
                        _cand = _unknown
                        _last = getattr(self, "_last_topic_probe", None)
                        if _last in _cand and len(_cand) > 1:
                            _cand = [_n for _n in _cand if _n != _last]
                        _pick = random.choice(_cand)
                        self._last_topic_probe = _pick
                        probe_hint = (f"\n\n额外目标：你还没了解{user_name}的「{_pick}」。"
                                      f"如果这次的话题能自然触及这个方向（比如通过分享你自己的相关小事、"
                                      f"或轻声问一句来引出对方的话）会很有帮助；"
                                      f"但如果生硬就不要勉强，按平时那样正常发起话题即可。")
                except Exception:
                    probe_hint = ""

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
                                             topic_examples=topic_examples)
                if seen_rejected:
                    prompt += ("\n注意：你刚才生成的内容与最近话题重复了（" +
                               "；".join(seen_rejected[-2:]) +
                               "）。请彻底换一个方向和说法，不要再用相同的句式。")
                prompt += probe_hint
                
                with self.api_lock:
                    self.api_busy = True
                try:
                    resp = self._call_text_model([{"role":"user","content":prompt}], temperature=temp, max_tokens=2048, timeout=12)
                    if resp.status_code == 200:
                        reply = resp.json()["choices"][0]["message"]["content"].strip()
                        parts = reply.split("|")
                        if len(parts) >= 3:
                            context = parts[0].strip()
                            opt1 = parts[1].strip()
                            opt2 = parts[2].strip()
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

    def open_topic_timer_settings(self):
        win, frame = self._make_card_window("话题定时器设置", 400, 340)
        s = self._dpi_scale
        # 底部按钮先 pack 固定（布局铁律：内容变高时收尾按钮不被挤走）
        def save():
            try:
                fixed_val = int(interval_var.get())
                rmin_val = int(rmin_var.get())
                rmax_val = int(rmax_var.get())
            except ValueError:
                messagebox.showwarning("输入错误", "请输入有效的整数（分钟）")
                return
            self.topic_enabled = enabled_var.get()
            mode = mode_var.get()
            if mode == "fixed":
                self.topic_mode = "fixed"
                self.topic_interval_minutes = max(1, min(240, fixed_val))
            else:
                lo = max(1, min(240, rmin_val))
                hi = max(1, min(240, rmax_val))
                if lo > hi:
                    messagebox.showwarning("提示", "最小间隔不能大于最大间隔")
                    return
                self.topic_mode = "random"
                self.topic_random_min = lo
                self.topic_random_max = hi
            if self.topic_enabled:
                self.start_topic_timer()
            else:
                if self.topic_timer_job:
                    self.root.after_cancel(self.topic_timer_job)
                    self.topic_timer_job = None
            save_topic_config(self.topic_enabled, self.topic_interval_minutes,
                              self.topic_mode, self.topic_random_min, self.topic_random_max)
            if self.topic_mode == "random":
                messagebox.showinfo("成功", f"已保存（随机间隔 {self.topic_random_min}~{self.topic_random_max} 分钟）")
            else:
                messagebox.showinfo("成功", f"已保存（固定间隔 {self.topic_interval_minutes} 分钟）")
            win.destroy()

        btn_frame = tk.Frame(frame, bg=DIALOG_BG)
        btn_frame.pack(side=tk.BOTTOM, pady=8)
        RoundedButton(btn_frame, text="保存", command=save, width=int(120 * s), height=int(36 * s),
                      radius=int(6 * s), font=(self.font_family, 11)).pack(side=tk.LEFT, padx=3)

        enabled_var = tk.BooleanVar(value=self.topic_enabled)
        mode_var = tk.StringVar(value=self.topic_mode)
        interval_var = tk.StringVar(value=str(self.topic_interval_minutes))
        rmin_var = tk.StringVar(value=str(self.topic_random_min))
        rmax_var = tk.StringVar(value=str(self.topic_random_max))

        cb = ttk.Checkbutton(frame, text="启用定时话题", variable=enabled_var)
        cb.pack(anchor='w', pady=(8, 4))

        tk.Label(frame, text="间隔模式:", font=(self.font_family, 11), fg=TEXT_MAIN,
                 bg=DIALOG_BG).pack(anchor='w', pady=(4, 2))
        mode_row = tk.Frame(frame, bg=DIALOG_BG)
        mode_row.pack(anchor='w', pady=2)
        btn_fixed = RoundedButton(mode_row, text="固定间隔", width=int(110 * s), height=int(30 * s),
                                  radius=int(8 * s), font=(self.font_family, 11), variant="primary",
                                  command=lambda: select_mode("fixed"))
        btn_fixed.pack(side=tk.LEFT, padx=(0, 8))
        btn_random = RoundedButton(mode_row, text="随机间隔", width=int(110 * s), height=int(30 * s),
                                   radius=int(8 * s), font=(self.font_family, 11), variant="subtle",
                                   command=lambda: select_mode("random"))
        btn_random.pack(side=tk.LEFT)

        # 固定模式输入行
        fixed_frame = tk.Frame(frame, bg=DIALOG_BG)
        tk.Label(fixed_frame, text="间隔（分钟）:", font=(self.font_family, 11), fg=TEXT_MAIN,
                 bg=DIALOG_BG).pack(side=tk.LEFT)
        RoundedEntry(fixed_frame, textvariable=interval_var, width=int(110 * s), height=int(30 * s),
                     radius=int(8 * s), font=(self.font_family, 11), justify="center").pack(side=tk.LEFT, padx=8)

        # 随机模式输入行（最小/最大 分行，防右边界裁切）
        random_min_row = tk.Frame(frame, bg=DIALOG_BG)
        tk.Label(random_min_row, text="最小间隔（分钟）:", font=(self.font_family, 11), fg=TEXT_MAIN,
                 bg=DIALOG_BG).pack(side=tk.LEFT)
        RoundedEntry(random_min_row, textvariable=rmin_var, width=int(110 * s), height=int(30 * s),
                     radius=int(8 * s), font=(self.font_family, 11), justify="center").pack(side=tk.LEFT, padx=8)
        random_max_row = tk.Frame(frame, bg=DIALOG_BG)
        tk.Label(random_max_row, text="最大间隔（分钟）:", font=(self.font_family, 11), fg=TEXT_MAIN,
                 bg=DIALOG_BG).pack(side=tk.LEFT)
        RoundedEntry(random_max_row, textvariable=rmax_var, width=int(110 * s), height=int(30 * s),
                     radius=int(8 * s), font=(self.font_family, 11), justify="center").pack(side=tk.LEFT, padx=8)
        tip = tk.Label(frame, text="随机间隔：每次触发后在此区间内随机抽一个间隔",
                       font=(self.font_family, 9), fg=TEXT_SUB, bg=DIALOG_BG)

        def select_mode(mode):
            mode_var.set(mode)
            btn_fixed.set_variant("primary" if mode == "fixed" else "subtle")
            btn_random.set_variant("primary" if mode == "random" else "subtle")
            fixed_frame.pack_forget()
            random_min_row.pack_forget()
            random_max_row.pack_forget()
            tip.pack_forget()
            if mode == "random":
                random_min_row.pack(anchor='w', pady=(6, 2))
                random_max_row.pack(anchor='w', pady=2)
                tip.pack(anchor='w', pady=2)
            else:
                fixed_frame.pack(anchor='w', pady=(6, 2))

        select_mode(mode_var.get())

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
            if self.action_timer_job:
                try:
                    self.root.after_cancel(self.action_timer_job)
                except Exception:
                    pass
                self.action_timer_job = None
            idx, label = random.choice(ACTION_POOL)
            self.spine.do_action(idx)
            log.info("她做了个动作：%s（%s）", label, "点她触发" if from_click else "自己找事做")
        except Exception:
            pass
        self._schedule_action()

    def _open_costume_window(self):
        """🎩 装扮：悬浮卡片窗（同 API 设置那种），每个槽位一行、多选一用按钮高亮"""
        win, frame = self._make_card_window("装扮", 520, 700)
        s = self._dpi_scale
        self._costume_buttons = {}
        for slot, slot_label, clear_label, items in COSTUME_SLOTS:
            tk.Label(frame, text=slot_label, font=(self.font_family, 11, "bold"), fg=TEXT_MAIN,
                     bg=DIALOG_BG).pack(anchor='w', pady=(8, 2))
            row = None
            # 一排最多 6 个按钮，超了自动换行（"手持道具"有 12 个按钮，一行放不下会被窗口右边界裁掉）
            # 必须有的槽位不给"无"按钮（手持道具：她总得有件拿的东西）
            _opts = ([] if slot in COSTUME_REQUIRED_SLOTS else [(None, clear_label)]) + items
            for _i, (name, item_label) in enumerate(_opts):
                if _i % 6 == 0:
                    row = tk.Frame(frame, bg=DIALOG_BG)
                    row.pack(anchor='w')
                btn = RoundedButton(row, text=item_label, width=int(74 * s), height=int(30 * s),
                                    radius=int(8 * s), font=(self.font_family, 10), variant="subtle",
                                    command=lambda sl=slot, n=name: self.set_costume(sl, n))
                btn.pack(side=tk.LEFT, padx=(0, 6), pady=(0, 4))
                self._costume_buttons[(slot, str(name))] = btn
        tip = tk.Label(frame, text="每个槽位只能选一个（「桌面显示」可以多选并存），选新的会自动摘掉旧的",
                       font=(self.font_family, 9), fg=TEXT_SUB, bg=DIALOG_BG)
        tip.pack(anchor='w', pady=(10, 0))
        RoundedButton(frame, text="关闭", command=win.destroy, variant="subtle",
                      width=int(110 * s), height=int(36 * s), radius=int(10 * s),
                      font=(self.font_family, 11)).pack(pady=(10, 0))
        self._refresh_costume_buttons()

    def _apply_saved_costumes(self):
        """渲染器就绪后把上次的装扮穿回去（只调一次；渲染线程里执行，set_costume 只是入队）"""
        self._costume_applied = True
        for slot, _label, _clear, _items in COSTUME_SLOTS:
            val = self.costume_choice.get(slot)
            if not val:
                continue
            try:
                self.spine.set_costume(slot, val)
                log.info("装扮：%s → %s（启动恢复）", slot, val)
            except Exception as e:
                log.warning("恢复装扮失败 %s: %s", slot, e)

    def _refresh_costume_buttons(self):
        for (slot, key), btn in self._costume_buttons.items():
            chosen = self.costume_choice.get(slot)
            if slot in COSTUME_MULTI_SLOTS:
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
        save_costume_config(self.costume_choice)
        self._refresh_costume_buttons()

    def start_topic_timer(self):
        if self.topic_timer_job:
            self.root.after_cancel(self.topic_timer_job)
        self._schedule_topic()

    def _schedule_topic(self):
        """安排下一次自动话题：fixed=固定分钟；random=在区间内随机抽一次间隔"""
        if self.topic_enabled and not self.sleep_mode:
            if self.topic_mode == "random":
                lo = max(1, min(240, self.topic_random_min))
                hi = max(lo, min(240, self.topic_random_max))
                minutes = random.randint(lo, hi)
            else:
                minutes = self.topic_interval_minutes
            interval_ms = int(minutes * 60 * 1000)
            self.topic_timer_job = self.root.after(interval_ms, self._topic_timer_trigger)

    def _topic_timer_trigger(self):
        if self.sleep_mode or self.api_busy:
            self._schedule_topic()
            return
        self.generate_topic_manual()
        self._schedule_topic()

    # ---------- 陪看模式（使用 OpenAI 兼容视觉 API）----------
    def toggle_watch_mode(self):
        if self.watch_mode:
            self.watch_mode = False
            self._summarize_watch_segment()
            self._finalize_watch_event()
            self._watch_session_anchors = []
            self._watch_segment_buffer = []
            self._current_watch_event_id = None
            if self.watch_job:
                self.root.after_cancel(self.watch_job)
                self.watch_job = None
            if self.layered:
                self.layered.set_bypass(False)
            if self.spine_enabled and self.spine:
                self.spine.enqueue(('test_motion', 'Action', 1))
            self.root.after(800, lambda: self.set_emotion("normal"))
            self.show_bubble_text("(shy) 下次记得再叫我", "shy")
            log.info("陪玩模式已关闭")
        else:
            if self.sleep_mode:
                self.stop_sleep_mode()
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
            if self.layered:
                self.layered.set_bypass(True)
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
            if self.input_visible:
                self.toggle_input_frame(save=False)   # 陪玩自动收起不算用户选择，不写进配置
            self.show_bubble_text("(happy) 我会在后面安静陪着你的，按 Ctrl+Shift+G 可以退出", "happy")
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



    def _build_watch_query(self):
        """合并最近多个陪看锚点作为记忆召回 query"""
        if not self._watch_session_anchors:
            return self._watch_last_anchor or ""
        return "；".join(self._watch_session_anchors[-WATCH_SESSION_MAX:])

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
            }], temperature=0.3, max_tokens=4096, timeout=20)
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
        segment = list(self._watch_segment_buffer)
        self._watch_segment_buffer = []
        self._watch_segment_start_time = time.time()
        if len(segment) == 1:
            summary = segment[0]
        else:
            prompt = f"""请将以下陪看过程中的片段总结成一条完整的事件记忆，要包含观看内容、观看状态、关键阶段和氛围，100-200字。
片段：
{chr(10).join(segment)}
直接输出事件描述，不要解释。"""
            summary = None
            try:
                resp = self._call_text_model([{"role": "user", "content": prompt}], temperature=0.3, max_tokens=4096, timeout=20)
                if resp.status_code == 200:
                    summary = resp.json()["choices"][0]["message"]["content"].strip()
            except Exception as e:
                log.warning(f"陪看片段总结失败: {e}")
            if not summary:
                summary = "；".join(segment)

        events = self.memory_data.setdefault("events", [])
        if self._current_watch_event_id is not None:
            for ev in events:
                if ev.get("id") == self._current_watch_event_id:
                    old_content = ev.get("content", "")
                    merged = summary
                    if old_content and old_content != summary:
                        merge_prompt = f"""请将下面两条关于同一次陪看过程的事件描述合并成一条完整事件，不要丢失关键信息，200-300字。
旧事件：{old_content}
新片段总结：{summary}
直接输出合并后的事件描述，不要解释。"""
                        try:
                            resp = self._call_text_model([{"role": "user", "content": merge_prompt}], temperature=0.3, max_tokens=4096, timeout=20)
                            if resp.status_code == 200:
                                merged_text = resp.json()["choices"][0]["message"]["content"].strip()
                                if merged_text:
                                    merged = merged_text
                        except Exception as e:
                            log.warning(f"陪看事件合并失败: {e}")
                            merged = old_content + "；" + summary
                    ev["content"] = merged
                    ev["last_accessed_at"] = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                    ev["importance"] = max(ev.get("importance", 0.5), 0.7)
                    ev["evidence_count"] = ev.get("evidence_count", 1) + 1
                    save_memories(self.memory_data)
                    return
            self._current_watch_event_id = None

        now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
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
        events = self.memory_data.get("events", [])
        for ev in events:
            if ev.get("id") != self._current_watch_event_id:
                continue
            content = (ev.get("content") or "").strip()
            if not content:
                return
            try:
                resp = self._call_text_model([{
                    "role": "user",
                    "content": f"请将下面这段陪看事件记录整理成最终版本：保留观看内容、观看状态、关键阶段和氛围，确保总字数不超过{WATCH_EVENT_MAX_LEN}字（含标点），直接输出整理结果，不要解释。\n事件：\n{content}"
                }], temperature=0.3, max_tokens=4096, timeout=20)
                if resp.status_code == 200:
                    final_text = resp.json()["choices"][0]["message"]["content"].strip()
                    if final_text:
                        ev["content"] = final_text
            except Exception as e:
                log.warning(f"陪看事件收尾失败: {e}")
            ev["content"] = self._enforce_event_length(ev["content"])
            ev["last_accessed_at"] = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            save_memories(self.memory_data)
            return

    def start_watch_loop(self):
        if self.watch_mode:
            self.analyze_and_comment(force=False)
            # 轮询间隔取 min_interval 的一半，限制在 5~60 秒之间
            poll_sec = max(5, min(self.watch_min_interval // 2, 60))
            self.watch_job = self.root.after(int(poll_sec * 1000), self.start_watch_loop)

    def analyze_and_comment(self, force=False):
        if self.sleep_mode:
            return
        if not self.watch_mode and not force:
            return
        if not self.watch_lock.acquire(blocking=False):
            return

        now = time.time()
        elapsed = now - self.last_watch_comment_time

        if not force:
            if elapsed < self.watch_min_interval:
                log.debug("陪看: 距上次发言 %.1fs < 最小间隔 %ds，跳过", elapsed, self.watch_min_interval)
                self.watch_lock.release()
                return
            elif elapsed >= self.watch_max_silence:
                log.debug("陪看: 距上次发言 %.1fs > 最长沉默 %ds，强制触发", elapsed, self.watch_max_silence)
                force = True
            else:
                prob = max(0.05, (elapsed - self.watch_min_interval) / (self.watch_max_silence - self.watch_min_interval))
                if random.random() > prob:
                    log.debug("陪看: 概率跳过 (elapsed=%.1fs, prob=%.2f)", elapsed, prob)
                    self.watch_lock.release()
                    return

        log.debug("陪看: 开始分析画面")
        def process():
            try:
                image_b64 = self.capture_screen_base64()
                if not image_b64:
                    self._ui(lambda: self.show_bubble_text("(normal) 唔...我现在看不到画面呢。", "normal"))
                    return
                sig = self._frame_signature(image_b64)
                if not force:
                    diff = self._frame_diff(self.last_screen_sig, sig)
                    if diff < WATCH_SIMILARITY_THRESHOLD:
                        log.debug("陪看: 画面与上次评论时几乎没变（平均像素差 %.2f < %.1f），跳过不调模型",
                                  diff, WATCH_SIMILARITY_THRESHOLD)
                        return
                    log.debug("陪看: 画面变化 平均像素差 %.2f", diff)
                comment = self._get_vision_comment(image_b64, force=force)
                if comment:
                    # 只有"真的说了一句"才重置发言间隔（空回不吃间隔：间隔＝实际发言的间隔）
                    self.last_watch_comment_time = time.time()
                    self.last_screen_sig = sig
                    if any(w in comment for w in ('休息', '歇', '累', '睡', '眼睛')):
                        self._rest_cooldown_until = time.time() + 5 * 60   # 真提了才进冷却
                    self._ui(lambda: self.show_bubble_text(comment, "normal"))
                    self._ui(lambda: threading.Thread(target=self._tts_play, args=(comment,), daemon=True).start())
                    # 陪玩评论写入缓冲 + 事件锚点。
                    # user 侧文本用当次画面摘要而不是固定占位符——同一个占位符连着出现
                    # 等于告诉模型"情况和上次一样，照上次说"，是句式锁死的强信号。
                    _who = self.user_profile.get('call_name', '你')
                    _sum = (getattr(self, '_watch_last_summary', '') or '').strip()
                    if len(_sum) > 80:
                        _sum = _sum[:80] + '…'
                    _side = f"[陪玩中，{_who}在看：{_sum}]" if _sum else f"[陪玩中，{_who}在看的画面]"
                    self._ui(lambda: self._add_chat_buffer_turn(_side, comment, source="watch"))
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
            resp = self._call_text_model([{"role": "user", "content": prompt1}], temperature=0.3, max_tokens=512, timeout=15)
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
            resp2 = self._call_text_model([{"role": "user", "content": prompt2}], temperature=0.3, max_tokens=512, timeout=15)
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

    def _get_vision_comment(self, image_b64, force=False):
        """使用 OpenAI 兼容视觉模型分析截图"""
        if not self.vision_api_key:
            return "(worried) 请先设置视觉模型 API Key"
        if not self.vision_model:
            return "(worried) 请先设置视觉模型名称"

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

        rest_line = ("" if time.time() < self._rest_cooldown_until else
                     "他要是连着玩了很久、或者节奏明显慢下来，可以顺口提一句让他歇会儿；不用每次都说。")
        force_line = "这一轮一定要说一句。" if force else ""
        watch_instructions = f"""你在陪"{user_name}"一起看屏幕——可能是直播/电影/视频，也可能是他自己在玩游戏或使用软件。
你是{self.pet_name}，用你自己的语气说话，不用把自己调成某个样子。
看到什么就说你注意到的那个点，或者它让你想到的那句话——像坐在旁边的人顺口出声，不是写观后感。
要说的就一句，别分两段；画面本身不用复述，那是 content 的事。
多数时候是句感觉或感慨；偶尔顺着话头问他一句就行，别每句都问。
画面里是直播平台、弹幕或别人的操作 → 他在看；是他自己在操作 → 他在玩。记忆只能当闲聊的由头，不许盖过你现在看到的东西。
如果画面正好勾起了之前聊过的事，就自然提一句；没有就不用硬找。
{rest_line}
这一轮如果你没什么想说的，comment 就留空，不用硬凑。{force_line}
{said_block}
请严格输出JSON，不要markdown代码块。**先写 comment（你要说的那句），再补 content（记录用）**：
{{"comment": "开头一个情绪括号 + 一句话；没什么想说的就留空字符串", "content": "一句话事件标签：在玩/在看什么 + 当前阶段，20~40字；不要罗列画面细节，不要写数字/倒计时/坐标/UI数值"}}
"""

        messages = self.build_context_messages(self._effective_system_prompt(), watch_instructions,
                                               context_type="watch", image_b64=image_b64,
                                               memory_query=self._build_watch_query(),
                                               extra_context=said_block,
                                               skip_sources={"watch"} if monologue else None)
        try:
            resp = self._call_vision_model(messages, temperature=1.1, max_tokens=4096, timeout=30)
            if resp.status_code != 200:
                log.error(f"视觉模型 API 返回非200: {resp.status_code} {resp.text[:200]}")
                return None

            raw_reply = self._extract_message_content(resp.json()["choices"][0]["message"]).strip()
            if not raw_reply:
                return None
            content_text = ""
            comment = raw_reply

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
            if data:
                content_text = (data.get("content") or "").strip()
                comment = (data.get("comment") or "").strip()
            else:
                m = re.search(r'"comment"\s*:\s*"((?:[^"\\]|\\.)*)"', raw_reply, re.DOTALL)
                if m:
                    comment = m.group(1).replace('\\"', '"').replace("\\n", "\n").strip()
                m2 = re.search(r'"content"\s*:\s*"((?:[^"\\]|\\.)*)"', raw_reply, re.DOTALL)
                if m2:
                    content_text = m2.group(1).replace('\\"', '"').replace("\\n", "\n").strip()

            self._watch_last_summary = content_text or ""   # 本次（可能为空）：空则不复用上次摘要
            if content_text:
                self._watch_last_anchor = content_text
                self._update_watch_session(content_text)
            if not comment:
                return None
            if not re.match(r'\(\w+\)', comment.strip()):
                comment = f"(normal) {comment}"
            return comment

        except Exception as e:
            log.error(f"视觉模型 API 失败: {e}")
            return None

    # ---------- 陪玩设置界面 ----------
    def open_watch_frequency_settings(self):
        win, frame = self._make_card_window("陪玩设置", 440, 240)
        s = self._dpi_scale

        # 最短间隔时间
        tk.Label(frame, text="最短间隔时间（5~120 秒）:", font=(self.font_family, 10), fg=TEXT_MAIN, bg=DIALOG_BG).grid(row=0, column=0, sticky="w", pady=8)
        min_var = tk.StringVar(value=str(self.watch_min_interval))
        min_entry = RoundedEntry(frame, textvariable=min_var, width=int(80 * s), height=int(30 * s),
                                 radius=int(8 * s), font=(self.font_family, 11), justify="center")
        min_entry.grid(row=0, column=1, padx=10, sticky="w")
        tk.Label(frame, text="秒", font=(self.font_family, 10), fg=TEXT_SUB, bg=DIALOG_BG).grid(row=0, column=2, sticky="w")

        # 最长沉默时间
        tk.Label(frame, text="最长沉默时间（30~600 秒）:", font=(self.font_family, 10), fg=TEXT_MAIN, bg=DIALOG_BG).grid(row=1, column=0, sticky="w", pady=8)
        max_var = tk.StringVar(value=str(self.watch_max_silence))
        max_entry = RoundedEntry(frame, textvariable=max_var, width=int(80 * s), height=int(30 * s),
                                 radius=int(8 * s), font=(self.font_family, 11), justify="center")
        max_entry.grid(row=1, column=1, padx=10, sticky="w")
        tk.Label(frame, text="秒", font=(self.font_family, 10), fg=TEXT_SUB, bg=DIALOG_BG).grid(row=1, column=2, sticky="w")

        def save():
            try:
                new_min = int(min_var.get())
                new_max = int(max_var.get())
            except ValueError:
                messagebox.showwarning("输入错误", "请输入有效的整数")
                return
            if new_min < 5 or new_min > 120:
                messagebox.showwarning("输入错误", "最短间隔需要在 5~120 之间")
                return
            if new_max < 30 or new_max > 600:
                messagebox.showwarning("输入错误", "最长沉默需要在 30~600 之间")
                return
            if new_min >= new_max:
                messagebox.showwarning("输入错误", "最短间隔必须小于最长沉默时间")
                return
            self.watch_min_interval = new_min
            self.watch_max_silence = new_max
            save_watch_config({
                "min_interval": new_min,
                "max_silence": new_max
            })
            messagebox.showinfo("成功", "陪玩设置已保存")
            win.destroy()

        RoundedButton(frame, text="保存", command=save, width=int(120 * s), height=int(36 * s),
                      radius=int(6 * s), font=(self.font_family, 11, "bold")).grid(row=2, column=0, columnspan=3, sticky="e", pady=20)

        # 回车键保存
        def on_return(event):
            save()
        win.bind("<Return>", on_return)
        min_entry.focus()

    # ---------- 读书伴侣 ----------
    def toggle_reading(self):
        if not self.reading_companion.enabled and self.sleep_mode:
            self.stop_sleep_mode()
        self.reading_companion.toggle()
        if self.reading_companion.enabled:
            if self.spine_enabled and self.spine:
                self.spine.enqueue(('test_motion', 'Action', 2))
            self.show_bubble_text("(happy) 让我看看你在读什么", "happy")
        else:
            if self.spine_enabled and self.spine:
                self.spine.enqueue(('test_motion', 'Action', 1))
            self.root.after(800, lambda: self.set_emotion("normal"))
            self.show_bubble_text("(shy) 有机会再一起读吧", "shy")
        label = "📖 陪我读书 (停止)" if self.reading_companion.enabled else "📖 陪我读书 (开始)"
        self._safe_menu_config(self.reading_menu_index, label, self.mode_menu)

    def open_reading_settings(self):
        win, frame = self._make_card_window("阅读区域与频率设置", 420, 520)
        s = self._dpi_scale

        tk.Label(frame, text="截取区域 (屏幕百分比)", font=(self.font_family, 11, "bold"), fg=TEXT_MAIN,
                 bg=DIALOG_BG).grid(row=0, column=0, columnspan=2, pady=5)
        fields = [
            ("左边距 (left)", "left"),
            ("上边距 (top)", "top"),
            ("宽度 (width)", "width"),
            ("高度 (height)", "height")
        ]
        vars = {}
        for i, (text, key) in enumerate(fields):
            tk.Label(frame, text=text, font=(self.font_family, 10), fg=TEXT_MAIN, bg=DIALOG_BG).grid(row=i+1, column=0, sticky="e", pady=2)
            var = tk.DoubleVar(value=self.reading_companion.region[key])
            RoundedEntry(frame, textvariable=var, width=int(90 * s), height=int(30 * s),
                         radius=int(8 * s), font=(self.font_family, 10)).grid(row=i+1, column=1, sticky="w", padx=5)
            vars[key] = var

        tk.Label(frame, text="截图间隔 (秒)", font=(self.font_family, 10), fg=TEXT_MAIN, bg=DIALOG_BG).grid(row=5, column=0, sticky="e", pady=5)
        cap_var = tk.DoubleVar(value=self.reading_companion.capture_interval)
        RoundedEntry(frame, textvariable=cap_var, width=int(90 * s), height=int(30 * s),
                     radius=int(8 * s), font=(self.font_family, 10)).grid(row=5, column=1, sticky="w", padx=5)

        tk.Label(frame, text="最短间隔时间 (5~120 秒)", font=(self.font_family, 10), fg=TEXT_MAIN, bg=DIALOG_BG).grid(row=6, column=0, sticky="e", pady=5)
        min_var = tk.IntVar(value=self.reading_companion.min_interval)
        RoundedEntry(frame, textvariable=min_var, width=int(90 * s), height=int(30 * s),
                     radius=int(8 * s), font=(self.font_family, 10)).grid(row=6, column=1, sticky="w", padx=5)

        tk.Label(frame, text="最长沉默时间 (30~600 秒)", font=(self.font_family, 10), fg=TEXT_MAIN, bg=DIALOG_BG).grid(row=7, column=0, sticky="e", pady=5)
        max_var = tk.IntVar(value=self.reading_companion.max_silence)
        RoundedEntry(frame, textvariable=max_var, width=int(90 * s), height=int(30 * s),
                     radius=int(8 * s), font=(self.font_family, 10)).grid(row=7, column=1, sticky="w", padx=5)

        def start_box_select():
            win.withdraw()
            def on_region_selected(region):
                if region is None:
                    win.deiconify()
                    return
                for key in vars:
                    vars[key].set(round(region[key], 4))
                win.deiconify()
                preview_current()
            self.reading_companion.select_region_interactive(callback=on_region_selected)

        def show_preview(region):
            try:
                if not mss:
                    return
                with mss.MSS() as sct:
                    mon = sct.monitors[1]
                    l = int(mon["width"] * region["left"])
                    t = int(mon["height"] * region["top"])
                    w = int(mon["width"] * region["width"])
                    h = int(mon["height"] * region["height"])
                    cap = {"left": l, "top": t, "width": max(w,1), "height": max(h,1)}
                    img = sct.grab(cap)
                    pil_img = Image.frombytes("RGB", img.size, img.bgra, "raw", "BGRX")
            except Exception as e:
                messagebox.showerror("预览失败", str(e))
                return

            preview_win = tk.Toplevel(win)
            preview_win.title("截取区域预览")
            preview_win.configure(bg=DIALOG_BG)
            img_width, img_height = pil_img.size
            max_width = 400
            if img_width > max_width:
                ratio = max_width / img_width
                pil_img = pil_img.resize((max_width, int(img_height * ratio)), Image.LANCZOS)
            photo = ImageTk.PhotoImage(pil_img)
            label = tk.Label(preview_win, image=photo, bg=DIALOG_BG)
            label.image = photo
            label.pack(padx=10, pady=10)
            tk.Label(preview_win, text=f"区域大小：{w}x{h} 像素", font=(self.font_family, 9), bg=DIALOG_BG).pack()

        def preview_current():
            try:
                region = {
                    "left": float(vars["left"].get()),
                    "top": float(vars["top"].get()),
                    "width": float(vars["width"].get()),
                    "height": float(vars["height"].get())
                }
            except ValueError:
                messagebox.showerror("错误", "请输入有效的数字")
                return
            show_preview(region)

        box_btn = RoundedButton(frame, text="🖱️ 缩略图框选区域", command=start_box_select,
                                width=int(190 * s), height=int(34 * s), radius=int(6 * s),
                                font=(self.font_family, 10, "bold"))
        box_btn.grid(row=8, column=0, columnspan=2, pady=8)

        preview_btn = RoundedButton(frame, text="🔍 预览当前区域", command=preview_current,
                                    variant="subtle",
                                    width=int(170 * s), height=int(32 * s), radius=int(6 * s),
                                    font=(self.font_family, 10))
        preview_btn.grid(row=9, column=0, columnspan=2, pady=5)

        def save():
            for key in vars:
                self.reading_companion.region[key] = vars[key].get()
            self.reading_companion.capture_interval = cap_var.get()
            self.reading_companion.min_interval = min_var.get()
            self.reading_companion.max_silence = max_var.get()
            self.reading_companion.save_config()
            messagebox.showinfo("成功", "阅读设置已保存")
            win.destroy()

        RoundedButton(frame, text="保存", command=save, width=int(120 * s), height=int(36 * s),
                      radius=int(6 * s), font=(self.font_family, 11)).grid(row=10, column=0, columnspan=2, sticky="e", pady=15)

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

    def toggle_voice(self):
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
            self.show_bubble_text("(normal) 语音识别已停止", "normal")
            log.info("语音识别已关闭")
        else:
            if self.sleep_mode:
                self.stop_sleep_mode()
            self.stt.start()
            self.voice_on = True
            self._update_voice_menu_label()
            self.show_bubble_text("(happy) 我在听你说话", "happy")
            log.info("语音识别已开启")

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

    def on_speech_recognized(self, text, mode="content"):
        self.last_interaction_time = time.time()
        try:
            remain = self.stt.window_left() if self.stt is not None else -1
        except Exception:
            remain = -1
        log.info("语音入口: mode=%s 窗口剩余=%.1fs text=%s", mode, remain, text)
        # 抗打断：宠物正在输出（气泡打字 / TTS 播放）时，忽略本轮语音输入，
        # 等宠物说完再接话，避免误打断
        if self._voice_output_busy():
            log.info("宠物正在说话，忽略语音输入（抗打断）")
            return
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
        """音乐库设置：直接填写本地音乐文件夹路径（免迁移），或恢复内置曲库"""
        win, frame = self._make_card_window("音乐库设置", 680, 320)
        s = self._dpi_scale
        cfg_dir = ""
        try:
            cfg_dir = (_get_section("tools").get("music_dir") or "").strip()
        except Exception:
            pass
        active = load_music_dir() or ""
        src = f"自定义音乐库：{cfg_dir}" if cfg_dir else f"内置曲库：{MUSIC_REPO_DIR}"
        tk.Label(frame, text=f"当前音乐来源：{src}", font=(self.font_family, 11, "bold"),
                 fg=TEXT_MAIN, bg=DIALOG_BG).pack(anchor="w", pady=(10, 2), padx=16)
        tk.Label(frame, text="填写你自己的音乐文件夹路径（支持子文件夹；mp3/flac/ogg/wav），\n"
                             "保存后无需把歌复制进内置曲库，说“放首歌”即可播放：",
                 font=(self.font_family, 10), fg=TEXT_SUB, bg=DIALOG_BG,
                 justify="left").pack(anchor="w", padx=16)
        entry = RoundedEntry(frame, width=int(580 * s), height=int(34 * s), radius=int(8 * s),
                             font=(self.font_family, 10))
        entry.pack(pady=6, padx=16)
        entry.set(active or "")
        tk.Label(frame, text="留空并点“保存”= 恢复内置曲库；填了不存在的路径会提示",
                 font=(self.font_family, 9), fg=TEXT_SUB, bg=DIALOG_BG).pack(anchor="w", padx=16)

        def do_save(reset=False):
            path = "" if reset else entry.get().strip()
            if path and not os.path.isdir(path):
                messagebox.showwarning("路径无效", f"文件夹不存在：\n{path}")
                return
            if save_music_dir_setting(path):
                # 换库后清掉旧的轮转/浏览/挂起/卡片状态
                self._music_list_state.clear()
                self._music_browse = []
                self._music_pending = None
                try:
                    self.clear_song_picker()
                except Exception:
                    pass
                msg = "已恢复内置曲库" if reset else "音乐库已更新"
                messagebox.showinfo("成功", f"{msg}，说“放首歌”试试吧")
                win.destroy()

        btns = tk.Frame(frame, bg=DIALOG_BG)
        btns.pack(pady=12)
        RoundedButton(btns, text="保存", command=do_save, width=int(120 * s),
                      height=int(34 * s), radius=int(8 * s),
                      font=(self.font_family, 11)).pack(side=tk.LEFT, padx=8)
        RoundedButton(btns, text="恢复内置曲库", command=lambda: do_save(reset=True),
                      variant="subtle", width=int(160 * s), height=int(34 * s),
                      radius=int(8 * s), font=(self.font_family, 11)).pack(side=tk.LEFT, padx=8)

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

# ------------------------------- 阅读伴侣（EasyOCR）---------------------------------
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
        self._reader_loading = False

    def _init_reader(self):
        """后台线程加载 EasyOCR，避免阻塞主线程 UI（首次使用需联网下载模型）"""
        if self.reader is not None or not EASYOCR_AVAILABLE or self._reader_loading:
            return
        self._reader_loading = True
        def _load():
            try:
                self.reader = easyocr.Reader(['ch_sim', 'en'], gpu=False, verbose=False)
                log.info("EasyOCR 引擎初始化成功")
            except Exception as e:
                log.error(f"EasyOCR 初始化失败: {e}")
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
        if not EASYOCR_AVAILABLE:
            messagebox.showwarning("缺少依赖", "请安装 EasyOCR：\npip install easyocr")
            return
        self._init_reader()
        if self.reader is None:
            if self._reader_loading:
                messagebox.showwarning("OCR 加载中", "EasyOCR 引擎仍在加载（首次使用需联网下载模型），请稍后再试。")
            else:
                messagebox.showwarning("OCR 初始化失败", "EasyOCR 引擎启动失败，请检查网络或重新安装。")
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
            results = self.reader.readtext(img_np, detail=0, paragraph=False)
            text = ' '.join(results).strip()
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
            resp = self.pet._call_text_model(messages, temperature=0.95, max_tokens=2048, timeout=20)
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
