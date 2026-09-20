# 从源码运行（详细版）

> **只是想用、不想改代码？** 直接下成品 exe（自包含，不用装 Python）：<https://pan.baidu.com/s/1SMvJiDkVZhNoARs75eDoZA>　提取码：`sgqg`

本仓库**不含** `models/`（语音识别模型 244MB）与 `userdata/`（运行期数据），
按下面几步补齐即可。已经跑起来的话看 [README](README.md) 就够了。

## 1. 环境

- Windows x64
- **Python 3.10**（本机验证 3.10.11）。`live2d-py` 的 Cubism native 与 `sherpa-onnx` 都是
  **cp310** 扩展，3.11/3.12 下 `import` 直接失败。

## 2. 依赖

```bat
python -m pip install -r requirements.txt
```

必需三件套（`pillow` / `numpy` / `requests`）缺了程序起不来；`easyocr` 最重（连带 torch），
只是「读书」功能用，不想装可以删掉那一行。

## 3. 模型文件

```bat
python tools/fetch_models.py              :: 语音识别模型（约 244MB，带 SHA256 校验）
python tools/fetch_models.py --with-bge   :: 再加 bge 向量模型（约 92MB，记忆召回更准）
python tools/fetch_models.py --check-only :: 只核对已下好的文件
```

下到本仓库根目录的 `models/` 下；走 hf-mirror，中断了重跑即可（已存在且校验通过会跳过）。
**不下会怎样**：程序照常运行，只是「语音识别」会提示模型未就绪；再下 bge 之前记忆召回走旧排序。

## 4. 音乐（可选）

`music_starter/`（内置启动曲）**不随仓库分发**。没有它只是曲库为空——
右键菜单 → 音乐设置里指定你自己放歌的目录就行。

## 5. 跑

```bat
run.bat
:: 或者
python Dafeiyu.py
```

首次启动要加载模型（记忆向量模型约十几秒），窗口出现得稍慢是正常的。
启动后 **右键点她 → ⚙️ 设置 → API 密钥 → 文本模型设置…** 填上你自己的 Key。

## 常见问题

- **她不回话**：八成是没填 API Key（见上一步）；看 `userdata/dafeiyu.log` 里最后一次请求的报错。
- **提示「语音识别需要安装 sherpa-onnx pyaudio numpy」**：`pip install -r requirements.txt` 没装全。
- **没有画面 / 黑屏**：`pygame`、`PyOpenGL`、`live2d-py` 三件没装好；日志里会有 import 报错。
- **窗口图标不对、或者路径里有中文**：把仓库放到**纯英文路径**下最稳（sherpa 的部分底层库对中文路径敏感）。
