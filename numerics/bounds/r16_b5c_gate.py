#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r16_b5c_gate.py — R16B B5c 谱夹逼三件零入库并行探针件验收门（G1–G7＋NC1–NC4）.

任务书口径（b5c-spectral-probe，D67 裁决 2）：零 Lean 件入库、零求解、纯 notes
产出——notes/b5c-spectral-probe.md 五探针节结构、证据链一致性与零入库守卫。
本门为纯 python3 文本＋git 状态检查（零 Lean 编译、零数值计算）；不验数学内容
（探针件职责＝方向确定性，数学正确性由书面推导＋后续轮次本体件承担）。

检查面（全部确定性；seed 20261017 按惯例记档，本门无随机路径）：
  G1 件在位：notes/b5c-spectral-probe.md 存在且非空
  G2 五探针节结构齐：§P1–§P5 五个二级标题逐节在档（R15C 五节门同款）
  G3 已跑声明日志在盘：件内全部 /tmp/… 路径逐一存在（每条『已跑』声明必须
     带可核验日志——诚实纪律的机器面）；零 /tmp 路径引用即 fail
  G4 grep 证据锚在档（四条）：P1/P2/P3/P5 各一条 grep 段头——须同时在
     预研件内逐字转录 AND 对应 /tmp grep 日志内逐字在档（双面锚）
  G5 越权陈述零命中：『已证』『已 Lean 化』『已形式化』『证明已完成』
     『本体已完成』『已证毕』六模式 regex 全文件零命中（探针≠证明；
     R15C 同款六模式）
  G6 零求解声明锚：『零求解』声明段在档（heavySolves = 0 字面）
  G7 零入库守卫：git status --porcelain＋git diff HEAD --name-only 中
     formal/ 下无任何新增/改动，唯 r16 家族放行层（R16A TableB5Core 族
     在途件，D67 并行纪律＋decisions.md 执行裁决留痕）例外——本任务
     自身零 formal/lean/ThomsonN9/ 写入的机器面
  NC1（负对照）/tmp 篡改：副本将首条 /tmp 日志路径替换为不存在的路径
      ⇒ G3 检查逻辑必须拦（exit 1）
  NC2（负对照）节删改：副本删去 §P4 标题 ⇒ G2 必须拦
  NC3（负对照）越权注入：副本追加『已证毕』行 ⇒ G5 必须拦
  NC4（负对照）模拟入库：临时 git 仓库的 formal 树副本造新文件（非家族
      放行面）⇒ G7 必须拦（NC 全部作用于临时目录副本，不动真件）
  （四门自测后对真件跑 G1–G7）

用法：
  python3 numerics/bounds/r16_b5c_gate.py              # 全门（exit 0 = 过）
  python3 numerics/bounds/r16_b5c_gate.py --file PATH  # 对副本跑门（G7 仍对真仓）
  python3 numerics/bounds/r16_b5c_gate.py --no-nc      # 跳过 NC
CWD 无关：全部路径经 __file__ 解析。
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
STUDY_DEFAULT = REPO / "notes" / "b5c-spectral-probe.md"

SEED_GATE = 20261017                     # 惯例记档；本门无随机路径（确定性）

SECTIONS = [
    "§P1 探针",
    "§P2 探针",
    "§P3 探针",
    "§P4 探针",
    "§P5 探针",
]

# G4：双面锚——(锚串, 对应 /tmp grep 日志路径)；须同时出现在预研件与日志内
GREP_EVIDENCE_ANCHORS = [
    ("== [B] P1: 'sqrt' theorem/def declarations in CFC dir "
     "(grep -n 'theorem\\|lemma\\|def' lines containing sqrt) ==",
     "/tmp/r16b_grep_cfc.log"),
    ("== [B] P2: Rayleigh anywhere in Mathlib (content, case-insensitive) ==",
     "/tmp/r16b_grep_opnorm.log"),
    ("== [A] P3: 'eigenvalues_le'-named declarations anywhere in Mathlib ==",
     "/tmp/r16b_grep_eigmono.log"),
    ("== [F] P5: Gershgorin.lean full declaration outline ==",
     "/tmp/r16b_grep_gershgorin.log"),
]

# G5：越权陈述模式（探针件禁止宣称证明完成／本体入 Lean；R15C 同款）
OVERREACH_PATTERNS = [
    r"已证",
    r"已\s*Lean\s*化",
    r"已形式化",
    r"证明已完成",
    r"本体已完成",
    r"已证毕",
]

TMP_PATH_RE = re.compile(r"/tmp/[A-Za-z0-9_][A-Za-z0-9_.\-]*")

# G7：r16 家族放行层（R16A 在途件；D67 并行纪律＋thomson-n9/notes/decisions.md
# 本轮执行裁决『家族放行面』留痕）。前缀匹配；本任务自身四件不在此层。
PARALLEL_FAMILY_PREFIXES = [
    "formal/lean/ThomsonN9/TableB5Core",   # R16A TableB5Core 族 Lean 件（D67 裁决 1 主攻件）
    "formal/lean/ThomsonN9.lean",          # R16A 根 import 文件追加面（TableB5Core 挂载）
]


class GateFail(Exception):
    pass


def log(msg: str) -> None:
    print(msg, flush=True)


def check_g1(path: Path) -> str:
    if not path.is_file():
        raise GateFail(f"G1 FAIL：探针件不在位：{path}")
    text = path.read_text(encoding="utf-8")
    if len(text.strip()) < 5000:
        raise GateFail(f"G1 FAIL：探针件过短（{len(text)} 字符 < 5000，疑似占位）")
    return f"G1 件在位：{path.relative_to(REPO) if path.is_relative_to(REPO) else path}（{len(text)} 字符）"


def check_g2(text: str) -> str:
    missing = [s for s in SECTIONS if f"## {s}" not in text]
    if missing:
        raise GateFail(f"G2 FAIL：五探针节结构缺：{missing}")
    return "G2 五探针节结构齐：§P1–§P5 逐节在档 ✓"


def check_g3(text: str) -> str:
    paths = sorted(set(TMP_PATH_RE.findall(text)))
    if not paths:
        raise GateFail("G3 FAIL：件内零 /tmp 路径——『已跑』声明无机器可核验面")
    missing = [p for p in paths if not Path(p).is_file()]
    if missing:
        raise GateFail(f"G3 FAIL：/tmp 日志缺位（已跑声明不可核验）：{missing}")
    return (f"G3 已跑声明日志在盘：{len(paths)} 条 /tmp 路径逐一存在 ✓"
            f"（{'、'.join(p.split('/')[-1] for p in paths[:3])}… 等）")


def check_g4(text: str) -> str:
    miss_md = [a for a, _ in GREP_EVIDENCE_ANCHORS if a not in text]
    if miss_md:
        raise GateFail(f"G4 FAIL：grep 证据锚未在探针件内逐字转录：{miss_md}")
    miss_log = []
    for anchor, logpath in GREP_EVIDENCE_ANCHORS:
        lp = Path(logpath)
        if not lp.is_file() or anchor not in lp.read_text(encoding="utf-8", errors="replace"):
            miss_log.append(logpath)
    if miss_log:
        raise GateFail(f"G4 FAIL：grep 证据锚不在对应 /tmp 日志内（双面锚破坏）：{miss_log}")
    return "G4 grep 证据锚双面在档：P1/P2/P3/P5 四条段头（件内转录＋/tmp 日志）逐字 ✓"


def check_g5(text: str) -> str:
    for pat in OVERREACH_PATTERNS:
        hits = re.findall(pat, text)
        if hits:
            raise GateFail(
                f"G5 FAIL：越权陈述命中：模式 {pat!r} ×{len(hits)}（探针件不得宣称证明完成）")
    return "G5 越权陈述零命中：六模式全文件零命中 ✓"


def check_g6(text: str) -> str:
    if "零求解" not in text:
        raise GateFail("G6 FAIL：零求解声明缺位")
    if not re.search(r"heavySolves\s*=\s*0", text):
        raise GateFail("G6 FAIL：heavySolves = 0 字面锚缺位")
    return "G6 零求解声明锚在档（heavySolves = 0）✓"


def _git(repo: Path, *args: str) -> str:
    proc = subprocess.run(["git", "-C", str(repo), *args],
                          capture_output=True, text=True, timeout=60)
    if proc.returncode != 0:
        raise GateFail(f"G7 FAIL：git {' '.join(args)} 退出码 {proc.returncode}：{proc.stderr.strip()[:200]}")
    return proc.stdout


def check_g7(repo: Path = REPO) -> str:
    if not (repo / ".git").exists():
        raise GateFail(f"G7 FAIL：{repo} 不是 git 仓库——零入库守卫无从执行")
    changed: set[str] = set()
    for line in _git(repo, "status", "--porcelain").splitlines():
        line = line.strip()
        if not line:
            continue
        changed.add(line[3:].strip('"'))
    for line in _git(repo, "diff", "HEAD", "--name-only").splitlines():
        if line.strip():
            changed.add(line.strip())
    violated = [p for p in sorted(changed)
                if p.startswith("formal/") and not any(
                    p.startswith(pre) for pre in PARALLEL_FAMILY_PREFIXES)]
    if violated:
        raise GateFail(
            f"G7 FAIL：formal/ 树下出现非家族放行面的新增/改动（零入库守卫拦截）：{violated}")
    n_family = len([p for p in changed if p.startswith("formal/")])
    return ("G7 零入库守卫：formal/ 树零非放行改动 ✓"
            f"（r16 家族放行层在途 {n_family} 件按 D67 并行纪律放行；"
            f"本任务自有四件均在 formal/ 之外）")


def run_core_checks(path: Path) -> None:
    """G1–G7 全跑（对 path 指向的件；G7 恒对真仓）；任一 FAIL 即抛 GateFail。"""
    log(check_g1(path))
    text = path.read_text(encoding="utf-8")
    log(check_g2(text))
    log(check_g3(text))
    log(check_g4(text))
    log(check_g5(text))
    log(check_g6(text))
    log(check_g7())


def run_negative_controls(study: Path) -> None:
    text = study.read_text(encoding="utf-8")
    with tempfile.TemporaryDirectory(prefix="r16b_nc_") as td:
        tmp = Path(td)
        # NC1：/tmp 篡改——首条日志路径换成不存在的路径，G3 必须拦
        paths = sorted(set(TMP_PATH_RE.findall(text)))
        bogus = "/tmp/r16b_NONEXISTENT_7z3.log"
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
        # NC2：节删改——删 §P4 标题，G2 必须拦
        nc2_text = text.replace(f"## {SECTIONS[3]}", "##（已删）", 1)
        try:
            check_g2(nc2_text)
            raise GateFail("NC2 FAIL：节删副本未被 G2 拦（负对照失效）")
        except GateFail as e:
            if "NC2 FAIL" in str(e):
                raise
            log("NC2 节删副本被拦 ✓")
        # NC3：越权注入——追加『已证毕』行，G5 必须拦
        nc3_text = text + "\n（注入测试行）谱夹逼定理已证毕。\n"
        try:
            check_g5(nc3_text)
            raise GateFail("NC3 FAIL：越权注入副本未被 G5 拦（负对照失效）")
        except GateFail as e:
            if "NC3 FAIL" in str(e):
                raise
            log("NC3 越权注入副本被拦 ✓")
    # NC4：模拟入库——临时 git 仓库的 formal 树副本造非家族新文件，G7 必须拦
    with tempfile.TemporaryDirectory(prefix="r16b_nc4_") as td:
        fake = Path(td)
        (fake / "base.md").write_text("base\n", encoding="utf-8")
        _git_ok_or_die(fake, "init", "-q")
        _git_ok_or_die(fake, "-c", "user.email=nc4@gate", "-c", "user.name=nc4",
                       "add", "base.md")
        _git_ok_or_die(fake, "-c", "user.email=nc4@gate", "-c", "user.name=nc4",
                       "commit", "-q", "-m", "base")
        ingest = fake / "formal" / "lean" / "ThomsonN9"
        ingest.mkdir(parents=True)
        (ingest / "BogusIngest.lean").write_text("import Mathlib\n", encoding="utf-8")
        try:
            check_g7(fake)
            raise GateFail("NC4 FAIL：模拟入库副本未被 G7 拦（负对照失效）")
        except GateFail as e:
            if "NC4 FAIL" in str(e):
                raise
            log("NC4 模拟入库副本被拦 ✓（formal/ 树临时副本＋非家族新文件）")


def _git_ok_or_die(repo: Path, *args: str) -> None:
    proc = subprocess.run(["git", "-C", str(repo), *args],
                          capture_output=True, text=True, timeout=60)
    if proc.returncode != 0:
        raise GateFail(f"NC4 环境失败：git {' '.join(args)}：{proc.stderr.strip()[:200]}")


def main() -> None:
    ap = argparse.ArgumentParser(description="R16B B5c 探针件验收门（纯文本＋git 状态检查）")
    ap.add_argument("--file", default=str(STUDY_DEFAULT),
                    help="探针件路径（默认仓内 notes/b5c-spectral-probe.md）")
    ap.add_argument("--no-nc", action="store_true", help="跳过负对照")
    args = ap.parse_args()
    study = Path(args.file).resolve()

    log(f"[gate] r16_b5c_gate（seed {SEED_GATE}，CWD 无关，纯 python3 零 Lean 编译）")
    log(f"[gate] 探针件：{study}")
    try:
        if not args.no_nc:
            if not study.is_file():
                raise GateFail(f"NC SKIP：真件不在位，无从做副本（{study}）")
            run_negative_controls(study)
        run_core_checks(study)
    except GateFail as e:
        log(f"[gate] FAIL——{e}")
        sys.exit(1)
    log("[gate] PASS——G1–G7 全过"
        + ("＋NC1/NC2/NC3/NC4 负对照全触发" if not args.no_nc else "（--no-nc）")
        + "——exit 0")


if __name__ == "__main__":
    main()
