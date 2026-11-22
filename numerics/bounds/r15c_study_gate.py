#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r15c_study_gate.py — R15C B5 解析本体预研件验收门（G1–G6 ＋ NC1/NC2/NC3）.

任务书口径（r15c-b5core-study，D61 裁决 4）：零 Lean 件入库、零求解、纯 notes
产出——notes/b5-core-study.md 五节结构与证据链一致性门。本门为纯 python3 文本
检查（零 Lean 编译、零数值计算）；不验数学内容（预研件职责＝方向确定性，
数学正确性由书面推导＋后续轮次本体件承担）。

检查面（全部确定性；seed 20261017 按惯例记档，本门无随机路径）：
  G1 件在位：notes/b5-core-study.md 存在且非空
  G2 五节结构齐：§1 步骤逐条数学复述／§2 Mathlib 可用性映射／§3 缺口清单／
     §4 工程量分档／§5 建议切分与排期 五个二级标题逐节在档
  G3 已跑声明日志在盘：件内全部 /tmp/… 路径逐一存在（每条『已跑』声明必须
     带可核验日志——诚实纪律的机器面）；零 /tmp 路径引用即 fail（件必须含
     实跑证据）
  G4 grep 缺位证据在档（两条）：hessian 探针段与 polar 探针段的原样命令行
     字符串逐字在档（与 /tmp/r15c_grep_{hessian,polar}.log 头部一致）
  G5 越权陈述零命中：『已证』『已 Lean 化』『已形式化』『证明已完成』
     『本体已完成』『已证毕』六模式 regex 全文件零命中（预研件不得宣称
     证明完成；R14 常数层属既往事实的表述已用『已入 Lean 件』口径隔离）
  G6 零求解声明锚：『零求解』声明段在档（heavySolves = 0 字面）
  NC1（负对照）/tmp 篡改：副本将首条 /tmp 日志路径替换为不存在的路径
      ⇒ G3 检查逻辑必须拦（exit 1）
  NC2（负对照）节删改：副本删去 §4 标题 ⇒ G2 必须拦
  NC3（负对照）越权注入：副本追加『已证毕』行 ⇒ G5 必须拦
  （NC 全部作用于临时目录副本，不动真件；三门自测后对真件跑 G1–G6）

用法：
  python3 numerics/bounds/r15c_study_gate.py              # 全门（exit 0 = 过）
  python3 numerics/bounds/r15c_study_gate.py --file PATH  # 对副本跑门
  python3 numerics/bounds/r15c_study_gate.py --no-nc      # 跳过 NC
CWD 无关：全部路径经 __file__ 解析。
"""
from __future__ import annotations

import argparse
import re
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
STUDY_DEFAULT = REPO / "notes" / "b5-core-study.md"

SEED_GATE = 20261017                     # 惯例记档；本门无随机路径（确定性）

SECTIONS = [
    "§1 步骤逐条数学复述",
    "§2 Mathlib 可用性映射",
    "§3 缺口清单",
    "§4 工程量分档",
    "§5 建议切分与排期",
]

# G4：与 /tmp/r15c_grep_hessian.log / /tmp/r15c_grep_polar.log 内命令行逐字一致
GREP_EVIDENCE_ANCHORS = [
    "== [B] hessian: case-insensitive content grep over Mathlib/Analysis ==",
    "== [F] polar decomposition identifiers: Matrix.polar / polarDecomp / "
    "Matrix.IsHermitian.polar in whole Mathlib ==",
]

# G5：越权陈述模式（预研件禁止宣称证明完成／本体入 Lean）
OVERREACH_PATTERNS = [
    r"已证",
    r"已\s*Lean\s*化",
    r"已形式化",
    r"证明已完成",
    r"本体已完成",
    r"已证毕",
]

TMP_PATH_RE = re.compile(r"/tmp/[A-Za-z0-9_][A-Za-z0-9_.\-]*")


class GateFail(Exception):
    pass


def log(msg: str) -> None:
    print(msg, flush=True)


def check_g1(path: Path) -> str:
    if not path.is_file():
        raise GateFail(f"G1 FAIL：预研件不在位：{path}")
    text = path.read_text(encoding="utf-8")
    if len(text.strip()) < 5000:
        raise GateFail(f"G1 FAIL：预研件过短（{len(text)} 字符 < 5000，疑似占位）")
    return f"G1 件在位：{path.relative_to(REPO) if path.is_relative_to(REPO) else path}（{len(text)} 字符）"


def check_g2(text: str) -> str:
    missing = [s for s in SECTIONS if f"## {s}" not in text]
    if missing:
        raise GateFail(f"G2 FAIL：五节结构缺：{missing}")
    return "G2 五节结构齐：§1–§5 逐节在档 ✓"


def check_g3(text: str) -> str:
    paths = sorted(set(TMP_PATH_RE.findall(text)))
    if not paths:
        raise GateFail("G3 FAIL：件内零 /tmp 路径——『已跑』声明无机器可核验面")
    missing = [p for p in paths if not Path(p).is_file()]
    if missing:
        raise GateFail(f"G3 FAIL：/tmp 日志缺位（已跑声明不可核验）：{missing}")
    return f"G3 已跑声明日志在盘：{len(paths)} 条 /tmp 路径逐一存在 ✓（{'、'.join(p.split('/')[-1] for p in paths[:3])}… 等）"


def check_g4(text: str) -> str:
    miss = [a for a in GREP_EVIDENCE_ANCHORS if a not in text]
    if miss:
        raise GateFail(f"G4 FAIL：grep 缺位证据串不在档：{miss}")
    return "G4 grep 缺位证据在档：hessian [B] 段＋polar [F] 段两条逐字 ✓"


def check_g5(text: str) -> str:
    for pat in OVERREACH_PATTERNS:
        hits = re.findall(pat, text)
        if hits:
            raise GateFail(
                f"G5 FAIL：越权陈述命中：模式 {pat!r} ×{len(hits)}（预研件不得宣称证明完成）")
    return "G5 越权陈述零命中：六模式全文件零命中 ✓"


def check_g6(text: str) -> str:
    if "零求解" not in text:
        raise GateFail("G6 FAIL：零求解声明缺位")
    if not re.search(r"heavySolves\s*=\s*0", text):
        raise GateFail("G6 FAIL：heavySolves = 0 字面锚缺位")
    return "G6 零求解声明锚在档（heavySolves = 0）✓"


def run_core_checks(path: Path) -> None:
    """G1–G6 全跑（对 path 指向的件）；任一 FAIL 即抛 GateFail。"""
    log(check_g1(path))
    text = path.read_text(encoding="utf-8")
    log(check_g2(text))
    log(check_g3(text))
    log(check_g4(text))
    log(check_g5(text))
    log(check_g6(text))


def run_negative_controls(study: Path) -> None:
    text = study.read_text(encoding="utf-8")
    with tempfile.TemporaryDirectory(prefix="r15c_nc_") as td:
        tmp = Path(td)
        # NC1：/tmp 篡改——首条日志路径换成不存在的路径，G3 必须拦
        paths = sorted(set(TMP_PATH_RE.findall(text)))
        bogus = "/tmp/r15c_NONEXISTENT_9x7.log"
        nc1_text = text.replace(paths[0], bogus, 1)
        nc1 = tmp / "nc1_tampered.md"
        nc1.write_text(nc1_text, encoding="utf-8")
        try:
            check_g3(nc1_text)
            raise GateFail("NC1 FAIL：/tmp 篡副本未被 G3 拦（负对照失效）")
        except GateFail as e:
            if "NC1 FAIL" in str(e):
                raise
            log(f"NC1 /tmp 篡副本被拦 ✓（{e}）")
        # NC2：节删改——删 §4 标题，G2 必须拦
        nc2_text = text.replace(f"## {SECTIONS[3]}", "##（已删）", 1)
        try:
            check_g2(nc2_text)
            raise GateFail("NC2 FAIL：节删副本未被 G2 拦（负对照失效）")
        except GateFail as e:
            if "NC2 FAIL" in str(e):
                raise
            log("NC2 节删副本被拦 ✓")
        # NC3：越权注入——追加『已证毕』行，G5 必须拦
        nc3_text = text + "\n（注入测试行）d_P 定理已证毕。\n"
        try:
            check_g5(nc3_text)
            raise GateFail("NC3 FAIL：越权注入副本未被 G5 拦（负对照失效）")
        except GateFail as e:
            if "NC3 FAIL" in str(e):
                raise
            log("NC3 越权注入副本被拦 ✓")


def main() -> None:
    ap = argparse.ArgumentParser(description="R15C B5 预研件验收门（纯文本检查）")
    ap.add_argument("--file", default=str(STUDY_DEFAULT),
                    help="预研件路径（默认仓内 notes/b5-core-study.md）")
    ap.add_argument("--no-nc", action="store_true", help="跳过负对照")
    args = ap.parse_args()
    study = Path(args.file).resolve()

    log(f"[gate] r15c_study_gate（seed {SEED_GATE}，CWD 无关，纯 python3 零 Lean 编译）")
    log(f"[gate] 预研件：{study}")
    try:
        if not args.no_nc:
            if not study.is_file():
                raise GateFail(f"NC SKIP：真件不在位，无从做副本（{study}）")
            run_negative_controls(study)
        run_core_checks(study)
    except GateFail as e:
        log(f"[gate] FAIL——{e}")
        sys.exit(1)
    log("[gate] PASS——G1–G6 全过"
        + ("＋NC1/NC2/NC3 负对照全触发" if not args.no_nc else "（--no-nc）")
        + "——exit 0")


if __name__ == "__main__":
    main()
