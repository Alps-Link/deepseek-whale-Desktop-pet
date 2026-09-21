"""
Live2D 离屏渲染
"""
import os, time, json, threading, sys, random
import numpy as np
from PIL import Image
import pygame
from pygame.locals import *
from OpenGL.GL import *
import live2d.v3 as live2d

def _get_base_dir():
    try:
        return sys._MEIPASS
    except AttributeError:
        return os.path.dirname(os.path.abspath(__file__))

MODEL_DIR = os.path.join(_get_base_dir(), 'live2d_viewer', 'model')

# 反预乘查表：_UNPREMUL[a] = round(255 * 65536 / a)（定点 16.16），a=0 时为 0。
# 帧数据保持预乘 alpha（Windows 分层窗口本就要求预乘），
# 只有 tk Label 降级路径需要直通 alpha，才用它换算。
_UNPREMUL = np.zeros(256, dtype=np.uint32)
for _i in range(1, 256):
    _UNPREMUL[_i] = round(255 * 65536 / _i)


def _unpremultiply(img):
    """预乘 alpha → 直通 alpha（仅降级用 Label 显示时调用）"""
    arr = np.array(img, copy=True)
    a = arr[..., 3]
    m = a > 0
    if m.any():
        sub = arr[..., :3][m].astype(np.uint32)
        sub *= _UNPREMUL[a[m]][:, None]
        sub >>= 16
        np.minimum(sub, 255, out=sub)
        arr[..., :3][m] = sub.astype(np.uint8)
    return Image.fromarray(arr, 'RGBA')

# 眼睛在模型画布（800×640，中心为原点）里的纵向位置：自画布顶部往下约 20 单位（≈画面高的 13%）。
# 用于把"注视基准行"随渲染构图一起换算 —— 放大（聚焦缩放）时基准线才会跟着脸走。
# 旧实现是按 char_size 的固定 16%（≈画面高 20%，落在脖子/上胸），偏高。
EYE_ROW_IN_CANVAS = 20.5
# 跟随鼠标的幅度：这只模型的角度响应比家族其它只大得多（同一输入摆幅约为阿尔卑斯的两倍），
# 所以把家族那套 (1.2, 1.0) 收敛下来。实测换算：系数每 0.1 ≈ 7.4° 摆幅
# （1.0 时 AngleX 摆幅约 74°，会被 ±30 的上限夹住；0.5 ≈ 37°）。嫌大继续调小。
DRAG_SCALE_X = 0.5
DRAG_SCALE_Y = 0.5
# 形象定位纠正（实测，只有本模型需要）：她按家族同一套自适应画出来只占显示高的 78%
# （内容高 188/240）、下边缘离输入框 31px；阿尔卑斯是占满高度(239)、底部留白 0。
# 注意：glScalef/glTranslatef 对它无效——model.Draw() 用模型自己的矩阵，会覆盖 GL 变换，
# 所以只能用模型 API（SetScale/SetOffset，绝对值语义、设一次即持久）。
FIT_SCALE = 1.277      # = 240/188，放大到占满显示高度
FIT_OFFSET_Y = -0.053  # 下移 6.4px（单位=显示高的一半），让下边缘贴住窗口底
# 装扮会把"内容有多高"改掉：兔耳 +9px、头顶鲸 +2、单边马尾 +1（把画面缩到 S=1.0 保证不裁边后
# 量出的 bbox 高：常态 188 → 197 / 190 / 189）。而上面这套构图是按"常态内容占满显示高度"定的，
# 于是头顶多出来的部分会被上边界截掉（兔耳实测被裁约 11px）。
# 下表 = "挂着这件装扮时改用哪套缩放/偏移"，实测得来：
#   缩放 = 让该装扮也刚好占满显示高度；
#   偏移 = 缩放后把内容底边重新贴回下边界（复测 bbox 顶边 y=1、底边 y=239，不越界）。
# 没列出的装扮不改变内容高度（猫猫/蝴蝶结/发箍/三副眼镜/墨爪/桌上鲸/深色桌布逐一量过 = 188），
# 沿用基准构图，画面一点不动。
# "手里拿着的东西"所在的槽位：动画（点她 / 主动做动作）播放期间，这些参数要让位，
# 否则它们会一直压着动画自带的手和道具 —— 实测：装猫爪时点她，自拍的手机完全不出现、
# 挤番茄酱的双手一直维持猫爪（`maoshou=1` 写满全程，而 8 段动画里没有一段会去改它）。
# 桌面显示槽（画笔/橡皮/撤回/收起巴菲）不让位：巴菲是"写 1 才收起"的反向开关，
# 停写会让它每次点她都弹回来；那几件也不跟动画抢参数。
# 默认收起的手部道具参数：模型出厂时她手里拿着一块点菜板（point=1），用户要求取消这个常态。
# 这里每帧写 0 把它收起来；只有挤番茄酱 Action_0/Touch_1 会主动把 point 压成 0，其余动作不碰它，
# 所以不冲突。想恢复出厂样子，把这一行删掉即可。
DEFAULT_OFF_PARAMS = {'point': 0.0}

HAND_SLOTS = {'item'}
# 说明：只有**手持道具**槽（猫爪/蛋包饭/剪刀手/点单）参与让位 ——
# 「魔爪」是**桌面摆件**、「桌面显示」槽（画笔/橡皮/撤回/收起巴菲）是**桌布上的图标**，
# 它们都不是手里拿的东西，动画期间照常显示（巴菲还额外是"写 1 才收起"的反向开关）。
# 判断"这段动画用不用手"的参数名：动画曲线里出现任意一个，就说明它要靠手演东西
# （实测：挤番茄酱/开盖/自拍/快速自拍 有；吹泡泡/喷水/入场/待机 一个都没有）。
# 用不到手的动画就**不该**碰她的配件——用户原话："吹泡泡糖用不到手，为什么动作期间手会变成原始常态"。
HAND_PARAMS = {'phone', 'phone2', 'phone3', 'phone4', 'phone5', 'phone6', 'phone7', 'shouji',
               'ji', 'danbaoX', 'danbaoY', 'danbaofan', 'danbaoz', 'point', 'pointZ',
               'keyboard', 'xbox', 'aixing', 'maoshou'}
COSTUME_FIT = {
    'bunny_sticker': (1.213, -0.100),   # 兔耳
    'whale':         (1.258, -0.075),   # 头顶鲸
    'side_ponytail': (1.265, -0.067),   # 单边马尾
}


# 脸部残留修复：触摸动作播完后这些参数会定格在末帧——实测阿尔卑斯 EyeLift 1.00→0.00、
# 希雅拉 EyeSmile 0→0.97 且 Mouth_Smile 0→1.00、洛洛 BrowLY/RY 0→0.50 且 Toungue 0→0.32、
# 莫娜卡 EyeSoft 1.00→0.00，全是永久挂着不回。Idling 只驱动角度/手臂、自动眨眼只写眼开合，
# 嘴由 App 拥有、部件开关由装扮逻辑管，所以脸这层没人管，得显式还原。
# 还原目标 = 下面这份"日常状态值" NORMAL_FACE：她入场播完、静置下来的样子。9/18 用探针跑真实渲染
# 循环实测得来（入场+1.5~2s 与入场+8~14s 两个窗口的中位数完全一致，说明早就稳了），只写死参数值、
# 不写死观感；没列出来的脸参数一律按 0 还原。
NORMAL_FACE = {
    # 实测日常状态值（入场+1.5~2.0s 与 入场+8~14s 两窗口中位数一致，41 个脸参数里只有这三项非零）
    "ParamEyeLOpen": 1.0,
    "ParamEyeROpen": 1.0,
    "ParamMouthForm": -0.5,
}
FACE_TOKENS = ('ParamEye', 'Param_EYE', 'ParamBrow', 'ParamMouth', 'ParamParm', 'ParamSay',
               'ParamFace', 'ParamSmile', 'ParamTear', 'ParamCheek', 'ParamTeeth', 'ParamToungue',
               'ParamSweat', 'ParamBlueFace', 'ParamBlush', 'ParamDrool')

# 情绪 → 表情池：每个情绪随机挑一个，且不跟上一个连抽同一个（同一情绪连着两次也有不同表情）。
# 池子里只放"脸部"表情（exp3 只写 Param*）：眼镜/贴纸/发箍归装扮，道具类（画笔/手机/蛋包饭…）
# 归「手持道具」装扮槽 —— 情绪挂着道具会很怪。
# 表情名 = expressions/<名>.exp3.json 的文件名（也是 model3.json 里注册的 Id）。
EMOTION_POOLS = {
    'happy':     ['excited', 'star_eyes', 'flowers', 'heartbeat'],
    'relaxed':   ['blank_eyes', 'playful', 'tongue'],
    'shy':       ['blush', 'love_eyes'],
    'surprised': ['exclaim', 'question', 'dizzy'],
    'worried':   ['sad', 'cry'],
    'hurried':   ['sweat', 'soul_out'],
    'angry':     ['angry', 'gloomy'],
    'sleep':     ['drool'],          # 睡眠固定这一个：它同时负责"闭眼口水"的观感
}
# 自己会写眼睛开合的表情：挂着期间必须关掉自动眨眼，否则眨眼在 Update 里每帧把它盖掉
# （"墨镜遮眼被眨眼盖过"就是这个毛病，装扮里写眼睛的也归这条规则管）
EYE_OWNING_EXPRESSIONS = {'excited', 'playful', 'dizzy', 'sunglasses'}


def _parse_curve(segments):
    """把 motion3 的 Segments 解析成 [(t, v), ...] 关键帧。

    格式是 [t0, v0, 类型, 段..., 类型, 段...]：
      类型 0（线性/阶梯）= 两个数 [t, v]；
      类型 1（贝塞尔）  = 六个数 [c1x, c1y, c2x, c2y, t, v]（只取终点 t/v）。
    早先我按"时间必须递增"来猜段长，结果把 duration（如 5）当成值读进来、再被参数上限夹住，
    于是 `point` 没能归零 —— 这就是"挤番茄酱多出两只手"的根因。
    """
    if not segments or len(segments) < 2:
        return []
    keys = [(float(segments[0]), float(segments[1]))]
    i = 2
    while i < len(segments):
        typ = int(segments[i])
        i += 1
        if typ == 1 and i + 5 < len(segments):
            t, v = float(segments[i + 4]), float(segments[i + 5])
            i += 6
        elif i + 1 < len(segments):
            t, v = float(segments[i]), float(segments[i + 1])
            i += 2
        else:
            break
        keys.append((t, v))
    return keys


def _curve_value(keys, t):
    """按关键帧线性插值取值（超出范围取端点）"""
    if not keys:
        return 0.0
    if t <= keys[0][0]:
        return keys[0][1]
    for (t0, v0), (t1, v1) in zip(keys, keys[1:]):
        if t <= t1:
            if t1 <= t0:
                return v1
            k = (t - t0) / (t1 - t0)
            return v0 + (v1 - v0) * k
    return keys[-1][1]


def _hand_active_until(curves):
    """手部参数"还在用"的截止时刻（秒）。

    按**偏离动作起始值**算，不能按"非零"算：phone / danbaofan / aixing 这类参数整段恒定
    （phone 甚至恒为常态值 1.0），按非零算会把让位窗口拖到最后一帧，于是动作自带的
    "回到默认手形"那一段收尾会露着手演 —— 用户看到的就是"手机手 → 变成握笔 → 配件才回来"。
    实测三个手机动作：真正的手机手 phone2~phone7 在 79%~89% 处就归零了。
    """
    last = 0.0
    for _p, _ks in (curves or {}).items():
        if _p not in HAND_PARAMS or not _ks:
            continue
        _base = _ks[0][1]
        for _t, _v in _ks:
            if abs(_v - _base) > 0.5:
                last = max(last, _t)
    return last


def _face_param_ids(param_ids, mouth_param):
    """挑出"脸"这一层的参数：眼/眉/嘴型/说话口型/脸型/泪/脸颊/牙/舌/汗/发青/脸红/口水。"""
    return [p for p in param_ids
            if p.startswith(FACE_TOKENS) and p not in ('ParamEyeBallX', 'ParamEyeBallY')
            and p != mouth_param]


class Live2DRenderer:
    def __init__(self, tk_root):
        self._thread = None
        self._cmd_q = []
        self._q_lock = threading.Lock()
        self._ready = False
        self._frame = None
        self._frame_lock = threading.Lock()
        self._on_frame = None
        self.face_row = None      # 注视基准行（渲染线程按当前构图更新，主线程读）

    def enqueue(self, cmd):
        """线程安全地追加渲染命令"""
        with self._q_lock:
            self._cmd_q.append(cmd)

    def start(self, width=600, height=480, on_frame=None):
        self._cmd_q = []
        self._on_frame = on_frame
        def run(): _render_offscreen(self, width, height)
        self._thread = threading.Thread(target=run, daemon=True)
        self._thread.start()
        self._ready = True

    def get_frame(self):
        with self._frame_lock:
            if self._frame is None: return None
            w, h, data = self._frame
        # 帧是预乘 alpha（分层窗口直接用）；tk Label 需要直通 alpha，这里换算
        return _unpremultiply(Image.frombuffer('RGBA', (w, h), data, 'raw', 'RGBA', 0, 1))

    def set_emotion(self, emotion):
        self.enqueue(('emotion', emotion))

    def set_mouth(self, val):
        self.enqueue(('mouth', val))

    def do_action(self, idx):
        """做一个动作（形象转换）：播一次模型自带动作，到点收道具、回待机。"""
        self.enqueue(('action', int(idx)))

    def set_costume(self, slot, name):
        """装扮配件：按槽位互斥，name=None 表示摘掉（该槽位参数写回 0）。"""
        self.enqueue(('costume', slot, name))

    def set_size(self, w, h):
        """显示尺寸：渲染区域按它 ×（聚焦缩放）推算，读回裁剪后仍是它 —— 放大也 1:1"""
        self.enqueue(('size', int(w), int(h)))

    def begin_click(self):
        self.enqueue(('click',))

    def track_mouse(self, mx, my):
        self.enqueue(('mouse', mx, my))

    def destroy(self):
        self._ready = False
        self.enqueue(('quit',))

    def is_ready(self):
        return self._ready


def _render_offscreen(bridge, width, height):
    os.environ['SDL_VIDEO_WINDOW_POS'] = '-9999,-9999'
    pygame.init()
    pygame.display.set_mode((width, height), DOUBLEBUF | OPENGL | HIDDEN)

    live2d.init()
    live2d.glInit()
    model = live2d.LAppModel()
    model.LoadModelJson(os.path.join(MODEL_DIR, 'c_0120.model3.json'))

    model.SetAutoBreathEnable(True)
    model.SetAutoBlinkEnable(True)

    # 嘴部参数名因模型而异（部分模型导出为 ParamParmOpenY），探测实际存在的名字
    try:
        _param_ids = list(model.GetParamIds())
    except Exception:
        _param_ids = []
    MOUTH_PARAM = next((p for p in ('ParamMouthOpenY', 'ParamParmOpenY') if p in _param_ids), None)

    fbo = glGenFramebuffers(1); tex = glGenTextures(1)
    glBindFramebuffer(GL_FRAMEBUFFER, fbo)
    glBindTexture(GL_TEXTURE_2D, tex)
    glTexImage2D(GL_TEXTURE_2D, 0, GL_RGBA, width, height, 0, GL_RGBA, GL_UNSIGNED_BYTE, None)
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR)
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_LINEAR)
    glFramebufferTexture2D(GL_FRAMEBUFFER, GL_COLOR_ATTACHMENT0, GL_TEXTURE_2D, tex, 0)
    # Live2D 的遮罩(clipping mask)依赖模板缓冲：离屏 FBO 必须挂 depth-stencil，
    # 否则被遮罩裁掉的部分（描边/阴影网格）会露出来，放大后尤其明显
    rbo = glGenRenderbuffers(1)
    glBindRenderbuffer(GL_RENDERBUFFER, rbo)
    glRenderbufferStorage(GL_RENDERBUFFER, GL_DEPTH24_STENCIL8, width, height)
    glFramebufferRenderbuffer(GL_FRAMEBUFFER, GL_DEPTH_STENCIL_ATTACHMENT, GL_RENDERBUFFER, rbo)
    glBindFramebuffer(GL_FRAMEBUFFER, 0)

    glClearStencil(0)
    glViewport(0, 0, width, height)
    glMatrixMode(GL_PROJECTION); glLoadIdentity(); glOrtho(0, width, height, 0, -1, 1)
    glMatrixMode(GL_MODELVIEW); glLoadIdentity()
    clock = pygame.time.Clock()
    cmd_idx = 0; mouse_x, mouse_y = 0.0, 0.0
    disp_w, disp_h = width, height   # 显示尺寸（主线程推送）
    act_w, act_h = width, height     # 活动渲染区域（FBO 分配尺寸为上限）

    cur_fit_scale = FIT_SCALE      # 当前生效的构图（装扮会临时改小，见 COSTUME_FIT）
    cur_fit_offset = FIT_OFFSET_Y

    def apply_area():
        """按 显示尺寸 × 聚焦缩放 设定渲染区域；上限是 FBO 分配尺寸。
        这样任何缩放档位读回的都是显示尺寸的真实像素（不是把小块放大）。"""
        nonlocal act_w, act_h
        act_w = max(1, min(int(disp_w), width))
        act_h = max(1, min(int(disp_h), height))
        glViewport(0, 0, act_w, act_h)
        glEnable(GL_SCISSOR_TEST)
        glScissor(0, 0, act_w, act_h)          # 只清活动区域，别白清整个大缓冲
        glMatrixMode(GL_PROJECTION); glLoadIdentity()
        glOrtho(0, act_w, act_h, 0, -1, 1)
        glMatrixMode(GL_MODELVIEW); glLoadIdentity()
        # 注视基准行（画面像素，自窗口顶往下）：画布顶部 + 眼睛在画布里的偏移
        _sc = min(act_w / 800.0, act_h / 640.0) * 0.78
        # 注视基准行要在"未被纠正"的坐标里算，再套同一套 SetScale/SetOffset 变换
        _row = act_h * 0.5 - _sc * 320 + EYE_ROW_IN_CANVAS * _sc
        _row = (_row - act_h * 0.5) * cur_fit_scale + act_h * 0.5 + cur_fit_offset * act_h * 0.5
        bridge.face_row = int(_row)
    active_scene = None
    expression_active = None   # 表情（场景）是否还挂着
    last_emo_expr = None       # 最近一次随机挑中的情绪表情（用于"不连抽同一个"）
    blink_off = False          # 当前是否已关掉自动眨眼（眼睛归表情/装扮/睡眠所有时）
    sleep_eyes = False         # 睡眠时每帧强制闭眼（她没有 Sleep 动作）：挂着期间嘴归表情所有，App 说话值不得覆盖
    costume_slots = {}         # 装扮：{槽位: {参数: 值}}，每帧强制写入（动作会把参数顶掉）
    costume_rest = {}          # 装扮：{槽位: {参数: 原本的值}}，摘掉时还原成它
    costume_params = {}        # 上面各槽位合并后的写入表
    costume_names = {}         # 装扮：{槽位: [表情名…]}，用于按装扮重算构图
    hand_rest = {}             # 手里拿的东西：{参数: 原本的值}，动画期间淡出到它＝先放下
    hand_yield = 0.0           # 让位程度 0~1：渐变而不是瞬间切换（瞬间跳会"闪一下"）
    need_hand_yield = False    # 当前这段动画到底用不用手（用不到就不碰配件）
    hand_busy_until = 0.0      # 本段动画手部参数还在用的截止时刻（到点配件就回来）

    action_props = {}          # 本动作涉及的道具参数 → 动作结束时要还原成的值（动作前快照）
    action_start = 0.0         # 动作开始时间（用于按 elapsed 插值道具曲线）
    _idx_now = -1              # 当前动作索引（对应 action_curves）
    action_until = 0.0         # 动作预计结束时间
    # 平滑过渡（进入与退出）
    trans_start = 0; trans_dur = 0.5
    trans_dur_return = 0.8  # 回归常态的过渡时长（太短会显得被拽回去，太长像僵住）
    trans_from = {}; trans_to = {}
    face_restore_at = 0.0    # 触摸动作播完、开始还原的时刻
    normal_face = {}         # 脸的还原目标 = 模型脸参数 × NORMAL_FACE（首次用到时按模型现状建）
    trans_return = False      # 是否处于回归中性的过渡中
    # 预加载Scene参数（从 model3.json 读取，兼容命名文件）
    scene_params = {}
    m3_path = os.path.join(MODEL_DIR, 'c_0120.model3.json')
    with open(m3_path, 'r', encoding='utf-8') as _f:
        _md = json.load(_f)
    scene_files = _md['FileReferences']['Motions']['Scene']
    for i, sc in enumerate(scene_files):
        fpath = os.path.join(MODEL_DIR, sc['File'])
        try:
            with open(fpath,'r') as f:
                md = json.load(f)
            scene_params[i] = {c['Id']: c['Segments'][1] for c in md['Curves']}
        except: pass
    # Touch 组各动作时长（点击/唤醒随机播放后，循环点前收尾）+ 是否用到手
    touch_durations, touch_needs_hands, touch_hand_until = [], [], []
    try:
        for _it in (_md.get('FileReferences', {}).get('Motions', {}).get('Touch', []) or []):
            with open(os.path.join(MODEL_DIR, _it['File']), 'r', encoding='utf-8') as _f:
                _mo = json.load(_f)
            touch_durations.append(_mo.get('Meta', {}).get('Duration', 0) or 0)
            touch_needs_hands.append(
                any(_c.get('Id') in HAND_PARAMS for _c in _mo.get('Curves', [])))
            _tc = {}
            for _c in _mo.get('Curves', []):
                if _c.get('Id') in HAND_PARAMS:
                    _ks = _parse_curve(_c.get('Segments', []))
                    if _ks:
                        _tc[_c['Id']] = _ks
            touch_hand_until.append(_hand_active_until(_tc))
    except Exception:
        pass
    # Action 组（形象转换用的"做事情"动作）：时长 + 道具参数曲线
    # 实测：引擎播这些动作时只驱动姿态/脸，道具参数一律不动（曲线/参数都在也不动）——
    # 所以道具由渲染端自己按关键帧插值写入（同装扮那套写法），播完写回 0。
    action_durations, action_curves, action_needs_hands = [], [], []
    action_hand_until = []     # 每段动作：手部参数偏离起始值的最后时刻（秒）
    try:
        for _it in (_md.get('FileReferences', {}).get('Motions', {}).get('Action', []) or []):
            with open(os.path.join(MODEL_DIR, _it['File']), 'r', encoding='utf-8') as _f:
                _mo = json.load(_f)
            action_durations.append(_mo.get('Meta', {}).get('Duration', 0) or 0)
            _curves = {}
            for _c in _mo.get('Curves', []):
                _pid = _c['Id']
                if _pid.startswith(FACE_TOKENS):
                    continue
                if _pid.startswith(('ParamAngle', 'ParamBodyAngle', 'ParamBreath', 'ParamEyeBall')):
                    continue
                _keys = _parse_curve(_c.get('Segments', []))
                if _keys:
                    _curves[_pid] = _keys
            action_curves.append(_curves)
            # action_curves 里已经滤掉了脸/角度，剩下的基本就是道具参数 → 用不用手一眼可判
            action_needs_hands.append(any(_p in HAND_PARAMS for _p in _curves))
            action_hand_until.append(_hand_active_until(_curves))
    except Exception:
        pass

    # 模型默认参数即中性：所有动作/表情结束后的统一回归目标
    defaults = {pid: model.GetParameterValue(i) for i, pid in enumerate(model.GetParamIds())}
    mouth_level = 0.0   # 嘴部开合目标（App 的 mouth 命令推送）
    mouth_disp = 0.0    # 实际写入值（速率限制 0.25/帧，避免闭嘴时一跳）
    try:
        # 形象定位纠正（见 FIT_SCALE/FIT_OFFSET_Y 注释）
        model.SetScale(cur_fit_scale)
        model.SetOffset(0.0, cur_fit_offset)
    except Exception:
        pass
    model.StartMotion('FirstImpression', 0, 3)
    first_impression_end = time.time() + 4.767  # FirstImpression 3.817s：自然播完（Loop=false）后切待机

    try:
        while bridge._ready:
            clock.tick(60)

            while cmd_idx < len(bridge._cmd_q):
                cmd = bridge._cmd_q[cmd_idx]; cmd_idx += 1
                if cmd[0] == 'quit': bridge._ready = False; break
                elif cmd[0] == 'emotion':
                    # 这只模型的表情是 .exp3.json（原生表达式，Add 混合，Update 时叠加一层）
                    # → 不再走"Scene 动作参数插值"，直接 SetExpression；不需要动用参数过渡
                    if cmd[1] == 'sleep':
                        # 她没有 Sleep 动作：表情 + 每帧强制闭眼当睡着
                        # （自动眨眼由下面"眼睛归属"统一关；醒来收到 normal 时走 else 分支复位）
                        active_scene = None
                        expression_active = None
                        trans_to = {}
                        trans_return = False
                        sleep_eyes = True
                        last_emo_expr = EMOTION_POOLS['sleep'][0]
                        model.SetExpression(last_emo_expr)
                    elif cmd[1] in EMOTION_POOLS:
                        _pool = EMOTION_POOLS[cmd[1]]
                        _cands = [e for e in _pool if e != last_emo_expr] or _pool
                        last_emo_expr = random.choice(_cands)
                        sleep_eyes = False
                        model.SetExpression(last_emo_expr)
                    else:
                        # 表情结束：从当前值平滑回归中性（模型默认参数）
                        trans_from = {pid: model.GetParameterValue(i)
                            for i, pid in enumerate(model.GetParamIds())}
                        trans_to = dict(defaults)
                        if MOUTH_PARAM:
                            # 嘴归 App 管（不说话恒为 0），但模型默认嘴是张开的（实测希雅拉默认 ParamMouthOpenY=1.0）：
                            # 直接回归默认会把嘴推到 1.0，0.8s 后过渡结束又被逐帧写入拉回 0 —— 看着就是"张一下又闭上"
                            trans_to[MOUTH_PARAM] = 0.0
                        if not normal_face:
                            normal_face = {p: NORMAL_FACE.get(p, 0.0)
                                           for p in _face_param_ids(_param_ids, MOUTH_PARAM)}
                        trans_to.update(normal_face)     # 脸回"日常状态"，其余照旧回默认值
                        trans_start = time.time()
                        trans_return = True
                        active_scene = None
                        expression_active = None
                        sleep_eyes = False
                        last_emo_expr = None
                        model.ResetExpressions()
                        model.StartRandomMotion('Idling', 1)
                elif cmd[0] == 'action':
                    # 做动作（形象转换）：播一次，到点收回道具参数并回待机。
                    # 换新动作前先把上一个动作的道具还原——否则旧的蛋包饭/番茄酱/手柄会留在她身上
                    # 跟新动作叠在一起（"挤番茄酱出现四只手"就是这么来的，同装扮叠加一个道理）
                    for _ap, _av in action_props.items():
                        model.SetParameterValue(_ap, _av)
                    action_props = {}
                    action_until = 0.0
                    _idx = int(cmd[1])
                    if 0 <= _idx < len(action_durations):
                        active_scene = None
                        expression_active = None
                        trans_to = {}          # 动作期间不跑脸部回归过渡，交给它自己演
                        trans_return = False
                        model.StopAllMotions()
                        model.StartMotion('Action', _idx, 5)   # 必须高于待机的 4，否则被挂起
                        action_start = time.time()
                        _idx_now = _idx
                        action_until = action_start + action_durations[_idx] + 0.1
                        need_hand_yield = (_idx < len(action_needs_hands)
                                           and action_needs_hands[_idx])
                        hand_busy_until = (action_start + action_hand_until[_idx]
                                           if _idx < len(action_hand_until) else 0.0)
                        # 动作前快照：演完还原成"她原本的样子"（这些道具参数没有别的所有者，
                        # 一律写 0 会把常态值改掉——例如 point 常态就是 1.0）
                        action_props = {}
                        for _p in (action_curves[_idx] if _idx < len(action_curves) else {}):
                            if _p in _param_ids:
                                action_props[_p] = model.GetParameterValue(_param_ids.index(_p))
                elif cmd[0] == 'costume':
                    # 装扮配件（按槽位互斥）：换的时候先把该槽位旧参数写回 0，再写新装扮；
                    # 然后每帧强制写入——动作会把这些参数顶掉（卡梅莉亚那套同理）
                    _slot = cmd[1]
                    _names = cmd[2] if isinstance(cmd[2], (list, tuple)) else ([cmd[2]] if cmd[2] else [])
                    _new_params = {}
                    for _nm in _names:
                        try:
                            with open(os.path.join(MODEL_DIR, 'expressions', _nm + '.exp3.json'),
                                      encoding='utf-8') as _f:
                                for _it in json.load(_f)['Parameters']:
                                    _new_params[_it['Id']] = _it['Value']
                        except Exception:
                            pass
                    # 记下"她原本的值"：有些装扮参数常态就不是 0（发箍 ParamCheek38 常态 3.0），
                    # 摘掉时写 0 反而会把常态的东西弄没——所以摘掉要还原成原本的值
                    _rest = costume_rest.setdefault(_slot, {})
                    # 正在播动画时不能拿"当前值"当原本的值：动作可能正把这个参数顶在别的值上
                    # （挤番茄酱会把 danbaofan 顶起来），记下来就会让蛋包饭之类一直粘着不走。
                    # 这种时候用模型默认值兜底 —— 装扮参数只被装扮和动画改过，默认值就是它原本的值。
                    _busy_now = bool((action_until and time.time() < action_until)
                                     or (face_restore_at and time.time() < face_restore_at))
                    for _p in set(_new_params) | set(costume_slots.get(_slot) or {}):
                        if _p not in _rest and _p in _param_ids:
                            if _busy_now:
                                _rest[_p] = defaults.get(_p, model.GetParameterValue(
                                    _param_ids.index(_p)))
                            else:
                                _rest[_p] = model.GetParameterValue(_param_ids.index(_p))
                    # 先把这个槽位"用过的参数"全部还原成原本的值，再叠上新装扮 ——
                    # 少了这一步，同槽位换装扮（圆眼镜→方眼镜）会两个都亮着（只剩"无"能全清）
                    _slot_params = {_p: _v for _p, _v in _rest.items()}
                    if _names:
                        _slot_params.update(_new_params)
                    costume_slots[_slot] = _slot_params
                    costume_params = {}
                    for _sp in costume_slots.values():
                        costume_params.update(_sp)
                    costume_names[_slot] = list(_names)
                    # 手里拿的东西 → 它们"原本的值"（放下时写回它）
                    hand_rest = {_p: costume_rest.get(_sl, {}).get(_p, 0.0)
                                 for _sl, _ps in costume_slots.items() if _sl in HAND_SLOTS
                                 for _p in _ps}
                    # 装扮会改内容高度（兔耳最明显）→ 重算构图，否则头顶多出来的会被上边界裁掉。
                    # 多件同时挂时取"缩得最狠的那件"的一套（它自带对应的偏移）。
                    _fits = [COSTUME_FIT[_n] for _sl in costume_names.values()
                             for _n in _sl if _n in COSTUME_FIT]
                    if _fits:
                        cur_fit_scale, cur_fit_offset = min(_fits, key=lambda _f: _f[0])
                    else:
                        cur_fit_scale, cur_fit_offset = FIT_SCALE, FIT_OFFSET_Y
                    model.SetScale(cur_fit_scale)
                    model.SetOffset(0.0, cur_fit_offset)
                    apply_area()      # 注视基准行要跟着新构图一起重算
                elif cmd[0] == 'test_motion':
                    model.StartMotion(cmd[1], cmd[2], 5)
                elif cmd[0] == 'wake':
                    # 苏醒：播随机触摸动画；同时把 Idling 以更低优先级排队，
                    # 动画播完由 Cubism 自己交叉淡入接管（不硬停、不动参数）
                    active_scene = None
                    expression_active = None   # 触摸/唤醒接管面部，表情不再拥有嘴
                    trans_to = {}
                    trans_return = False
                    # 先清掉当前动作（否则新一轮触摸会因优先级不高于它而被拒），再播触摸动作
                    model.StopAllMotions()
                    if touch_durations:
                        _ti = random.randint(0, len(touch_durations) - 1)
                        model.StartMotion('Touch', _ti, 3)
                        _touch_dur = touch_durations[_ti]
                        need_hand_yield = (_ti < len(touch_needs_hands)
                                           and touch_needs_hands[_ti])
                        hand_busy_until = (time.time() + touch_hand_until[_ti]
                                           if _ti < len(touch_hand_until) else 0.0)
                    else:
                        model.StartRandomMotion('Touch', 3)
                        _touch_dur = 0.0
                        need_hand_yield = False
                    # 脸会在动作末帧定格：记下动作时长，播完把脸还原回她的日常状态（NORMAL_FACE）
                    face_restore_at = time.time() + (_touch_dur or 1.0)
                elif cmd[0] == 'click':
                    # 触摸：播随机触摸动画（优先级 5 立刻插入），并把 Idling 以更低优先级
                    # 排队 —— Touch 播完后由 Cubism 用动作自身的淡入淡出接管呼吸，
                    # 全程不 StopAllMotions、不写回参数：于是既没有呼吸瞬跳，
                    # 也不会在鼠标拖到极限时因"剥离 drag"算错基准位而前冲。
                    active_scene = None
                    expression_active = None   # 触摸/唤醒接管面部，表情不再拥有嘴
                    trans_to = {}
                    trans_return = False
                    # 先清掉当前动作（否则新一轮触摸会因优先级不高于它而被拒），再播触摸动作
                    model.StopAllMotions()
                    if touch_durations:
                        _ti = random.randint(0, len(touch_durations) - 1)
                        model.StartMotion('Touch', _ti, 3)
                        _touch_dur = touch_durations[_ti]
                        need_hand_yield = (_ti < len(touch_needs_hands)
                                           and touch_needs_hands[_ti])
                        hand_busy_until = (time.time() + touch_hand_until[_ti]
                                           if _ti < len(touch_hand_until) else 0.0)
                    else:
                        model.StartRandomMotion('Touch', 3)
                        _touch_dur = 0.0
                        need_hand_yield = False
                    # 脸会在动作末帧定格：记下动作时长，播完把脸还原回她的日常状态（NORMAL_FACE）
                    face_restore_at = time.time() + (_touch_dur or 1.0)
                elif cmd[0] == 'mouth':
                    mouth_level = float(cmd[1])  # 只记录，由每帧写入（见渲染循环）
                elif cmd[0] == 'mouse':
                    mouse_x, mouse_y = cmd[1], cmd[2]
                elif cmd[0] == 'size':
                    disp_w = max(1, min(int(cmd[1]), width))
                    disp_h = max(1, min(int(cmd[2]), height))
                    apply_area()
            with bridge._q_lock:
                bridge._cmd_q = bridge._cmd_q[cmd_idx:]
                cmd_idx = 0

            for event in pygame.event.get(): pass

            if first_impression_end and time.time() > first_impression_end:
                first_impression_end = 0
                model.StopAllMotions()  # 停掉循环的入场动作，Idling 接管
                model.StartRandomMotion('Idling', 4)
                # 入场末帧不是她的日常状态（实测莫娜卡/艾丽卡右眼停在 0.78、卡梅莉亚左眼停在 0.81
                # 就是大小眼），所以入场一结束就用同一套回归过渡把脸收回到 NORMAL_FACE，再由 Idling 接管
                if not normal_face:
                    normal_face = {p: NORMAL_FACE.get(p, 0.0)
                                   for p in _face_param_ids(_param_ids, MOUTH_PARAM)}
                trans_from = {p: model.GetParameterValue(_param_ids.index(p)) for p in normal_face}
                trans_to = dict(normal_face)
                trans_start = time.time()
                trans_return = True
                active_scene = None

            # 脸部还原：触摸动作播完 → 借回归过渡把脸插值回常态（姿态/呼吸/视线/嘴/部件不碰）
            if face_restore_at and time.time() >= face_restore_at:
                face_restore_at = 0.0
                if not trans_return:      # 正好有表情回归在跑，就让给它
                    if not normal_face:
                        normal_face = {p: NORMAL_FACE.get(p, 0.0)
                                       for p in _face_param_ids(_param_ids, MOUTH_PARAM)}
                    trans_from = {p: model.GetParameterValue(_param_ids.index(p)) for p in normal_face}
                    trans_to = dict(normal_face)
                    trans_start = time.time()
                    trans_return = True
                    active_scene = None
            if trans_to and (active_scene is not None or trans_return):
                _tdur = trans_dur_return if trans_return else trans_dur
                t = min(1.0, (time.time() - trans_start) / _tdur)
                if not trans_return:
                    t = t * t * (3.0 - 2.0 * t)  # 表情进入 smoothstep
                else:
                    # 动作残姿回归用缓出：先快后慢收尾，避免末尾被拽一下
                    t = 1.0 - (1.0 - t) ** 3
                for pid, target_val in trans_to.items():
                    if pid in ('ParamEyeBallX', 'ParamEyeBallY', 'ParamHat', 'ParamSunglass'):
                        continue  # 眼球/装扮参数由各自系统接管，不参与回归
                    if trans_return and pid == 'ParamBreath':
                        # 呼吸不参与回归：动作停止那一帧自动呼吸会突然加回来（实测单帧 +0.39），
                        # 强制拉回 0 再让 Idling 重启就会"泄气 + 顶一下"。交给 Idling 连续接管
                        continue
                    if trans_return and (pid.startswith('ParamAngle') or pid.startswith('ParamBodyAngle')):
                        # 姿态不参与回归：残姿留在动作末帧，鼠标 Drag 继续在其之上实时叠加
                        # （若把角度也拉回中性，drag 就只剩"标准位置"，动作残姿会被抹掉）
                        continue
                    if trans_return and pid == 'ParamSkirt':
                        continue  # 裙子交给物理，不拉回默认
                    cur = trans_from.get(pid, target_val)
                    model.SetParameterValue(pid, cur + (target_val - cur) * t)
                if t >= 1.0:
                    if trans_return:
                        trans_return = False
                    active_scene = None
                    trans_to = {}
            # 动作结束（接缝）：**什么都不做**。
            # 动作按引擎自己的淡入淡出收尾（硬停/排队/交叉淡入都会让自动呼吸单帧顶 +0.33~0.64）；
            # 角度/裙摆残姿由 drag 按绝对位置继续叠加；呼吸交给引擎自动呼吸；嘴由下方"嘴部"一行管。
            # 早期那套"全参数回归 + 重启待机"的收尾已整段删除：它等于又引入一份同样宽的所有权冲突。
            # 嘴部：每帧写一次（动作播放时其曲线会覆盖本写入，动作结束后回到 App 值
            # 而不是停在动作末帧，避免"点完她嘴一直张着"）
            # 嘴部：只在 App 正在说话/正在收嘴时才写；其余时候把嘴交给"接缝回归插值"或"表情场景"。
            # （无条件每帧写会把表情场景的张嘴一帧抹掉 —— 实测 happy 表情 0.5s 后 ParmOpenY 0.500→0.000；
            #   也会在回归待机瞬间把表情撑开的嘴一帧闭死 —— 实测薇薇 1.000→0.000、艾丽卡 0.992→0.000）
            # 嘴的归属：①表情挂着 → 完全交给表情；②表情回归过渡中且没在说话 → 交给过渡（平滑收嘴）；
            #            ③其余情况（含过渡中正在说话）→ 由这里每帧写，收回动作末帧残留 + 跟 App 说话值
            if MOUTH_PARAM and active_scene is None and expression_active is None \
                    and (not trans_return or mouth_level > 0 or mouth_disp > 0):
                _mt = mouth_level
                mouth_disp += max(-0.25, min(0.25, _mt - mouth_disp))
                model.SetParameterValue(MOUTH_PARAM, mouth_disp)
            # 自动眨眼的归属：睡眠 / 自己写眼睛的表情（excited、playful、dizzy）/ 写眼睛的装扮（墨镜）
            # 挂着时一律关掉眨眼 —— 眨眼在 Update 里每帧覆盖眼睛参数，不关就会把"闭眼/遮眼"盖掉。
            # 状态没变就不重复调用（这只是个开关，但没必要每帧设一次）。
            _eyes_owned = (sleep_eyes or last_emo_expr in EYE_OWNING_EXPRESSIONS
                           or 'ParamEyeLOpen' in costume_params or 'ParamEyeROpen' in costume_params)
            if _eyes_owned != blink_off:
                model.SetAutoBlinkEnable(not _eyes_owned)
                blink_off = _eyes_owned
            # 动画期间（点她 / 做动作）把"手里的东西"放下：朝它原本的值过渡，而不是直接写死——
            # 直接写会"闪一下"，不写又等于没放下（参数会保持上一个值）。所以做成 0.25 秒的淡出/淡回。
            _now = time.time()
            # ① 只有这段动画真的用手时才让位（吹泡泡/喷水/入场等一个手部参数都不动，配件该留着）
            # ② 提前 0.5 秒放行、0.12 秒过渡 ⇒ 动作还没演完配件就完全回来了。
            # 收尾时看到的就是"装备好的样子"，不会先露出底层手形（用户说的"右手先变回握笔"）
            # 让位只覆盖"手部参数真的在动"的那一段（hand_busy_until 由动作曲线算出），
            # 动作自带的"回到默认手形"收尾不再被盖住 ⇒ 不会再先露出握笔手形
            _busy = need_hand_yield and _now < hand_busy_until
            _target = 1.0 if _busy else 0.0
            if hand_yield != _target:
                _step = 1.0 / (0.12 * 60)          # 0.12 秒走完（要快：慢了会在动作收尾时露出底层手形）
                hand_yield = max(0.0, min(1.0, hand_yield +
                                          (_step if _target > hand_yield else -_step)))
            for _cp, _cv in costume_params.items():
                if hand_yield > 0.0 and _cp in hand_rest:
                    _rv = hand_rest[_cp]
                    model.SetParameterValue(_cp, _cv + (_rv - _cv) * hand_yield)
                    continue
                model.SetParameterValue(_cp, _cv)
            # 默认收起的东西（见 DEFAULT_OFF_PARAMS）：每帧写一次，装扮/动作有需要时会自己覆盖它
            for _dp, _dv in DEFAULT_OFF_PARAMS.items():
                model.SetParameterValue(_dp, _dv)
            if action_until:
                _el = time.time() - action_start
                if _el <= action_until - action_start:
                    _curves_now = action_curves[_idx_now] if 0 <= _idx_now < len(action_curves) else {}
                    for _ap in action_props:
                        model.SetParameterValue(_ap, _curve_value(_curves_now.get(_ap), _el))
                else:
                    # 演完：只把"动作自己插值写过的道具参数"还原成动作前的值；
                    # 姿势交给引擎自己的淡出 / 待机淡入接管 —— 硬停 + 把整套参数拉回去会让姿势瞬跳，
                    # 看起来就是"先跳回常态拿着笔和写字板、再变回猫爪"。
                    for _ap, _av in action_props.items():
                        model.SetParameterValue(_ap, _av)
                    action_props = {}
                    action_until = 0.0
            if sleep_eyes:
                model.SetParameterValue('ParamEyeLOpen', 0.0)
                model.SetParameterValue('ParamEyeROpen', 0.0)

            model.SetParameterValue('ParamEyeBallX', mouse_x)
            model.SetParameterValue('ParamEyeBallY', mouse_y)
            if active_scene is None:
                model.Drag(mouse_x * DRAG_SCALE_X, mouse_y * DRAG_SCALE_Y)
            model.Update()

            glBindFramebuffer(GL_FRAMEBUFFER, fbo)
            glClearColor(0.0, 0.0, 0.0, 0.0)
            glClear(GL_COLOR_BUFFER_BIT | GL_STENCIL_BUFFER_BIT)   # 模板也要清，遮罩才干净
            glLoadIdentity()
            s = min(act_w/800, act_h/640) * 0.78
            glTranslatef(act_w/2, act_h*0.50, 0); glScalef(s, s, 1)
            model.Draw()
            glFlush()

            # 读回：渲染区域恒等于显示尺寸（已去掉聚焦缩放），直接整块读
            crop_w, crop_h = act_w, act_h
            buf = glReadPixels(0, 0, crop_w, crop_h, GL_RGBA, GL_UNSIGNED_BYTE)
            arr = np.ascontiguousarray(
                np.frombuffer(buf, dtype=np.uint8).reshape(crop_h, crop_w, 4)[::-1])
            rgba = arr.tobytes()   # FBO 本身就是预乘 alpha，分层窗口要的正是这个
            with bridge._frame_lock:
                bridge._frame = (crop_w, crop_h, rgba)
            cb = bridge._on_frame
            if cb is not None:
                try: cb(crop_w, crop_h, rgba)
                except Exception: pass
            glBindFramebuffer(GL_FRAMEBUFFER, 0)

    except Exception as e:
        import traceback
        print(f'[Live2D] CRASH: {e}')
        traceback.print_exc()
    finally:
        glDeleteFramebuffers(1, [fbo]); glDeleteTextures([tex]); glDeleteRenderbuffers(1, [rbo])
        live2d.glRelease(); pygame.quit()
