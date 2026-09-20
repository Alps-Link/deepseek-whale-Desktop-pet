#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""一键下载桌宠「从源码运行」需要的模型文件，下完自动核对 SHA256。

默认只下**语音模型那 3 个文件**（源码运行必需，成品 exe 里已内置、不需要跑这个脚本）：

    python tools/fetch_models.py                # 下到本仓库根目录的 models/（244MB）
    python tools/fetch_models.py --with-bge     # 连 bge 向量模型一起下（记忆向量召回用）
    python tools/fetch_models.py --check-only   # 只核对已有文件，不下载
    python tools/fetch_models.py --out D:\\tmp   # 指定输出目录

设计说明：
- 不依赖任何第三方库（只用标准库），所以 **pip install 之前也能跑**；hf-mirror 会返回 308 跳转，
  而 Python 3.10 的 urllib 不认 308，这里自己补了处理器（`hf download` CLI 实测走镜像会失败，别用）。
- 幂等：文件已存在且 SHA256 对得上就跳过，中断后重跑不会重复下载。
- 下完必校验，不符就删掉并报错——避免半截文件被当成"下好了"。
"""

import argparse
import hashlib
import os
import shutil
import sys
import time
import urllib.error
import urllib.request

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PETS_DIR = os.path.join(ROOT, '桌宠合集')
DEFAULT_PET = '阿尔卑斯桌宠自用'

HF = 'https://hf-mirror.com'
HF_ALT = 'https://huggingface.co'
PARA_REPO = 'csukuangfj/sherpa-onnx-paraformer-zh-2023-09-14'
BGE_REPO = 'BAAI/bge-small-zh-v1.5'
VOICE_DIR = 'models/sherpa-onnx-paraformer-zh-2023-09-14'
BGE_DIR = 'models/bge-small-zh-v1.5'

# (相对路径, 字节数, SHA256, [候选下载地址…])  —— 哈希来自本机既有文件，且实测从这些地址下回来一致
VOICE_FILES = [
    (VOICE_DIR + '/model.int8.onnx', 243371218,
     'f36a0433bcf096bd6d6f11b80a3ac8bed110bdca632fe0d731df8d1a84475945',
     [f'{HF}/{PARA_REPO}/resolve/main/model.int8.onnx',
      f'{HF_ALT}/{PARA_REPO}/resolve/main/model.int8.onnx']),
    (VOICE_DIR + '/tokens.txt', 75756,
     '59aba8873a2ed1e122c25fee421e25f283b63290efbde85c1f01a853d83cb6e6',
     [f'{HF}/{PARA_REPO}/resolve/main/tokens.txt',
      f'{HF_ALT}/{PARA_REPO}/resolve/main/tokens.txt']),
    (VOICE_DIR + '/silero_vad.onnx', 643854,
     '9e2449e1087496d8d4caba907f23e0bd3f78d91fa552479bb9c23ac09cbb1fd6',
     ['https://github.com/k2-fsa/sherpa-onnx/releases/download/asr-models/silero_vad.onnx']),
]

BGE_FILES = [
    (BGE_DIR + '/model.safetensors', 95827648,
     '354763b9b1357bc9c44f62c6be2276321081ed2567773608c0d0785b61d5a026',
     [f'{HF}/{BGE_REPO}/resolve/main/model.safetensors',
      f'{HF_ALT}/{BGE_REPO}/resolve/main/model.safetensors']),
    (BGE_DIR + '/tokenizer.json', 439125,
     '48cea5d44424912a6fd1ea647bf4fe50b55ab8b1e5879c3275f80e339e8fae26',
     [f'{HF}/{BGE_REPO}/resolve/main/tokenizer.json']),
    (BGE_DIR + '/vocab.txt', 109540,
     '45bbac6b341c319adc98a532532882e91a9cefc0329aa57bac9ae761c27b291c',
     [f'{HF}/{BGE_REPO}/resolve/main/vocab.txt']),
    (BGE_DIR + '/config.json', 776,
     '3853a7979202c348751b753e36f579c41d8da7d36af617d3d907e1fc9b441f2a',
     [f'{HF}/{BGE_REPO}/resolve/main/config.json']),
    (BGE_DIR + '/config_sentence_transformers.json', 124,
     '940d5f50db195fa6e5e6a4f122c095f77880de259d74b14a65779ed48bdd7c56',
     [f'{HF}/{BGE_REPO}/resolve/main/config_sentence_transformers.json']),
    (BGE_DIR + '/modules.json', 349,
     '84e40c8e006c9b1d6c122e02cba9b02458120b5fb0c87b746c41e0207cf642cf',
     [f'{HF}/{BGE_REPO}/resolve/main/modules.json']),
    (BGE_DIR + '/sentence_bert_config.json', 52,
     '84e39fda68ccbff05bfa723ae9c0e70e23e2ec373b76e0f8c6e71af72a693cbf',
     [f'{HF}/{BGE_REPO}/resolve/main/sentence_bert_config.json']),
    (BGE_DIR + '/special_tokens_map.json', 125,
     'b6d346be366a7d1d48332dbc9fdf3bf8960b5d879522b7799ddba59e76237ee3',
     [f'{HF}/{BGE_REPO}/resolve/main/special_tokens_map.json']),
    (BGE_DIR + '/tokenizer_config.json', 367,
     'e6f3b96db926a37d4039995fbf5ad17de158dfb8f6343d607e4dbaad18d75f5a',
     [f'{HF}/{BGE_REPO}/resolve/main/tokenizer_config.json']),
    (BGE_DIR + '/1_Pooling/config.json', 190,
     'aaa8861589f80c961a03cc86c7eeaef7605c1676b9ab55329d33a304738769c6',
     [f'{HF}/{BGE_REPO}/resolve/main/1_Pooling/config.json']),
]

PETS = [d for d in sorted(os.listdir(PETS_DIR))
        if d.endswith('桌宠自用') and os.path.isdir(os.path.join(PETS_DIR, d))] if os.path.isdir(PETS_DIR) else []


class _Redirect308(urllib.request.HTTPRedirectHandler):
    """Python 3.10 的 urllib 不认 308（hf-mirror 会返回 308），补上。"""

    def http_error_308(self, req, fp, code, msg, headers):
        return self.http_error_301(req, fp, 301, msg, headers)


_opener = urllib.request.build_opener(_Redirect308)


def fmt_size(n):
    return f'{n / 1048576:.1f} MB' if n >= 1048576 else f'{n / 1024:.0f} KB'


def short(path):
    """显示用的短路径：在仓库内显示相对路径，在仓库外（--out）显示绝对路径。"""
    rel = os.path.relpath(path, ROOT)
    return rel if not rel.startswith('..') else path


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(4 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def download(url, dest):
    """流式下载，边下边打印进度。成功返回 True。"""
    tmp = dest + '.part'
    req = urllib.request.Request(url, headers={'User-Agent': 'Mozilla/5.0 (pet-fetch-models)'})
    try:
        with _opener.open(req, timeout=60) as r, open(tmp, 'wb') as f:
            total = int(r.headers.get('Content-Length') or 0)
            got = 0
            t0 = time.time()
            last = 0.0
            while True:
                chunk = r.read(1 << 20)
                if not chunk:
                    break
                f.write(chunk)
                got += len(chunk)
                now = time.time()
                if now - last > 0.5:
                    last = now
                    speed = got / max(now - t0, 0.001) / 1048576
                    if total:
                        print(f'\r    {got * 100 / total:5.1f}%  {fmt_size(got)}/{fmt_size(total)}  {speed:.1f} MB/s',
                              end='', flush=True)
                    else:
                        print(f'\r    {fmt_size(got)}  {speed:.1f} MB/s', end='', flush=True)
        print()
        shutil.move(tmp, dest)
        return True
    except (urllib.error.URLError, OSError, TimeoutError) as e:
        print(f'\n    ✗ {type(e).__name__}: {e}')
        if os.path.exists(tmp):
            os.remove(tmp)
        return False


def fetch_one(path, size, want_hash, urls, check_only=False):
    """返回 'ok'（已存在且正确）/ 'done'（刚下好）/ 'fail'。"""
    if os.path.exists(path):
        got = sha256_file(path)
        if got == want_hash:
            print(f'  ✓ 已存在  {short(path)}')
            return 'ok'
        print(f'  ! 已存在但校验不符，重新下载  {short(path)}')
    elif check_only:
        print(f'  ✗ 缺失  {short(path)}')
        return 'fail'
    if check_only:
        return 'fail'

    print(f'  ↓ {short(path)}  ({fmt_size(size)})')
    for i, url in enumerate(urls):
        if i:
            print(f'    换个源重试：{url}')
        if download(url, path):
            got = sha256_file(path)
            if got == want_hash:
                print(f'  ✓ 校验通过  {got[:16]}…')
                return 'done'
            print(f'  ✗ 校验不符（期望 {want_hash[:16]}…，实得 {got[:16]}…），已删除')
            os.remove(path)
    return 'fail'


def resolve_pets(names):
    """支持短名（阿尔卑斯）、目录名（阿尔卑斯桌宠自用）。"""
    out = []
    for n in names:
        full = n if n.endswith('桌宠自用') else n + '桌宠自用'
        if full not in PETS:
            sys.exit(f'[x] 找不到桌宠「{n}」，可用的：' + '、'.join(p[:-4] for p in PETS))
        out.append(full)
    return out


def main():
    ap = argparse.ArgumentParser(description='一键下载桌宠源码运行所需的模型文件（带 SHA256 校验）')
    ap.add_argument('pets', nargs='*', help='桌宠短名或目录名，默认 阿尔卑斯')
    ap.add_argument('--all', action='store_true', help='8 只全下')
    ap.add_argument('--with-bge', action='store_true', help='连 bge 向量模型一起下（打包 exe 需要）')
    ap.add_argument('--check-only', action='store_true', help='只核对已有文件，不下载')
    ap.add_argument('--out', help='直接指定输出目录（此时忽略桌宠参数）')
    args = ap.parse_args()

    files = list(VOICE_FILES) + (list(BGE_FILES) if args.with_bge else [])

    if args.out:
        targets = [(args.out, '（--out 指定）')]
    else:
        targets = [(ROOT, '大肥鱼桌宠（本仓库根目录）')]

    if not files:
        sys.exit('[x] 没有要下载的文件')

    total_bytes = sum(f[1] for f in files) * len(targets)
    print(f'准备下载 {len(files)} 个文件 × {len(targets)} 只桌宠，总计 {fmt_size(total_bytes)}')
    if args.with_bge:
        print('（含 bge 向量模型；只跑源码的话其实不需要它，它是给打包 exe 用的）')
    print()

    stats = {'ok': 0, 'done': 0, 'fail': 0}
    t0 = time.time()
    for out_dir, label in targets:
        print(f'== {label} ==')
        for rel, size, h, urls in files:
            dest = os.path.join(out_dir, rel.replace('/', os.sep))
            os.makedirs(os.path.dirname(dest), exist_ok=True)
            stats[fetch_one(dest, size, h, urls, args.check_only)] += 1
        print()

    print(f'完成：已存在 {stats["ok"]}，新下载 {stats["done"]}，失败 {stats["fail"]}'
          f'（{time.time() - t0:.0f} 秒）')
    if stats['fail']:
        print('有失败项：先确认网络（hf-mirror 不通时可挂代理），再重跑本脚本；已下好的会跳过。')
        return 1
    print('语音模型就绪：点菜单里的「🎤 语音识别 (开始)」即可用（不用重启也行，重新点一次即可）。')
    return 0


if __name__ == '__main__':
    sys.exit(main())
