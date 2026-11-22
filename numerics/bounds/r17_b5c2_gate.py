#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r17_b5c2_gate.py — R17B B5c 前置探针补全四件零入库并行探针件验收门（G1–G7＋NC1–NC3）.

任务书口径（r17b-b5c-assembly-probe，D72 裁决 2）：零 Lean 件入库、零求解、纯
notes 产出——notes/b5c-assembly-probe.md 四探针节（§Q1–§Q4）结构、三档判定、
heavySolves=0 字面、/tmp 证据链在盘、零账本触碰声明与零入库守卫。
本门为纯 python3 文本＋git 状态检查（零 Lean 编译、零数值计算）；不验数学内容
（探针件职责＝方向确定性，数学正确性由书面推导＋后续轮次本体件承担）。

检查面（全部确定性；seed 20261017 按惯例记档，本门无随机路径）：
  G1 件在位（所有权）：notes/b5c-assembly-probe.md 存在且非空（≥5000 字符，
     疑似占位拦截）
  G2 notes 结构锚：§Q1–§Q4 四个二级标题逐节在档＋『三档判定』标记＋
     heavySolves = 0 字面＋/tmp 日志路径在文＋四条 grep 段头双面锚
     （须同时在探针件内逐字转录 AND 对应 /tmp grep 日志内逐字在档）
  G3 已跑声明日志在盘：件内全部 /tmp/… 路径逐一存在且非零字节（每条『已跑』
     声明必须带可核验日志——诚实纪律的机器面）；零 /tmp 路径引用即 fail
  G4 门源码 SEED_GATE 锚：本门源码内含字面 `SEED_GATE = 20261017`
     （模板拷贝时种子漂移的机器面拦截）
  G5 零求解声明锚：『零求解』声明段在档（heavySolves = 0 字面）＋越权陈述
     零命中（『已证』『已 Lean 化』『已形式化』『证明已完成』『本体已完成』
     『已证毕』六模式 regex 全文件零命中——探针≠证明；R15C/R16B 同款）
  G6 零账本触碰声明锚：『四账本』『endgame.json 零触碰』『certificates/ 零触碰』
     『typed_ladder rungs 零追加』四字面在档
  G7 零入库守卫：git status --porcelain＋git diff HEAD --name-only 中
     formal/ 下无任何新增/改动，唯 r17 家族放行层（R17A TableB5Trace 族在途件
     ＋根 import 追加面，D72 并行纪律＋decisions.md D74 执行裁决留痕）例外
     ——本任务自身零 formal/lean/ThomsonN9/ 写入的机器面
  NC1（负对照）节删改：副本删去 §Q3 标题 ⇒ G2 必须拦（exit 1）
  NC2（负对照）假日志路径：副本将首条 /tmp 日志路径替换为不存在的路径
      ⇒ G3 检查逻辑必须拦
  NC3（负对照）模拟入库：临时 git 仓库的 formal 树副本造新文件（非家族
      放行面）⇒ G7 必须拦（NC 全部作用于临时目录副本，不动真件）
  （三门自测后对真件跑 G1–G7）

用法：
  python3 numerics/bounds/r17_b5c2_gate.py              # 全门（exit 0 = 过）
  python3 numerics/bounds/r17_b5c2_gate.py --file PATH  # 对副本跑门（G7 仍对真仓）
  python3 numerics/bounds/r17_b5c2_gate.py --no-nc      # 跳过 NC
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
STUDY_DEFAULT = REPO / "notes" / "b5c-assembly-probe.md"

SEED_GATE = 20261017                     # 惯例记档；本门无随机路径（确定性）

SECTIONS = [
    "§Q1 探针",
    "§Q2 探针",
    "§Q3 探针",
    "§Q4 探针",
]

# G2：grep 证据双面锚——(锚串, 对应 /tmp grep 日志路径)；须同时出现在探针件与日志内
GREP_EVIDENCE_ANCHORS = [
    ("== [A] Q1: posSemidef dotProduct-mulVec bridge declarations (PosDef.lean) ==",
     "/tmp/r17b_grep_psdbridge.log"),
    ("== [A] Q2: roots_charpoly_eq_eigenvalues + charpoly_cfc_eq signatures ==",
     "/tmp/r17b_grep_cfc2.log"),
    ("== [A] Q3: orthogonalGroup membership API (UnitaryGroup.lean) ==",
     "/tmp/r17b_grep_orth.log"),
    ("== [D] Q4: squared CS candidate lemmas (sum_sq / card_mul / inner Finset) ==",
     "/tmp/r17b_grep_rowsum.log"),
]

# G5：越权陈述模式（探针件禁止宣称证明完成／本体入 Lean；R15C/R16B 同款）
OVERREACH_PATTERNS = [
    r"已证",
    r"已\s*Lean\s*化",
    r"已形式化",
    r"证明已完成",
    r"本体已完成",
    r"已证毕",
]

# G6：零账本触碰声明锚（四字面）
LEDGER_UNTOUCHED_ANCHORS = [
    "四账本",
    "endgame.json 零触碰",
    "certificates/ 零触碰",
    "typed_ladder rungs 零追加",
]

TMP_PATH_RE = re.compile(r"/tmp/[A-Za-z0-9_][A-Za-z0-9_.\-]*")

# G7：r17 家族放行层（R17A 在途件；D72 并行纪律＋thomson-n9/notes/decisions.md
# D74 执行裁决『家族放行面』留痕）。前缀匹配；本任务自身四件不在此层。
PARALLEL_FAMILY_PREFIXES = [
    "formal/lean/ThomsonN9/TableB5Trace",  # R17A B5b trace 族 Lean 件（D72 裁决 1 主攻件）
    "formal/lean/ThomsonN9.lean",          # R17A 根 import 文件追加面（TableB5Trace 挂载）
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
    return f"G1 件在位（所有权）：{path.relative_to(REPO) if path.is_relative_to(REPO) else path}（{len(text)} 字符）"


def check_g2(text: str) -> str:
    missing = [s for s in SECTIONS if f"## {s}" not in text]
    if missing:
        raise GateFail(f"G2 FAIL：四探针节结构缺：{missing}")
    for anchor in ("三档判定",):
        if anchor not in text:
            raise GateFail(f"G2 FAIL：结构锚缺位：{anchor!r}")
    if not re.search(r"heavySolves\s*=\s*0", text):
        raise GateFail("G2 FAIL：heavySolves = 0 字面锚缺位")
    if not TMP_PATH_RE.search(text):
        raise GateFail("G2 FAIL：件内零 /tmp 路径引用（证据链声明缺面）")
    miss_md = [a for a, _ in GREP_EVIDENCE_ANCHORS if a not in text]
    if miss_md:
        raise GateFail(f"G2 FAIL：grep 证据锚未在探针件内逐字转录：{miss_md}")
    miss_log = []
    for anchor, logpath in GREP_EVIDENCE_ANCHORS:
        lp = Path(logpath)
        if not lp.is_file() or anchor not in lp.read_text(encoding="utf-8", errors="replace"):
            miss_log.append(logpath)
    if miss_log:
        raise GateFail(f"G2 FAIL：grep 证据锚不在对应 /tmp 日志内（双面锚破坏）：{miss_log}")
    return ("G2 notes 结构锚：§Q1–§Q4 四节＋三档判定＋heavySolves = 0 字面＋"
            "/tmp 路径在文＋Q1/Q2/Q3/Q4 四条 grep 段头双面锚 ✓")


def check_g3(text: str) -> str:
    paths = sorted(set(TMP_PATH_RE.findall(text)))
    if not paths:
        raise GateFail("G3 FAIL：件内零 /tmp 路径——『已跑』声明无机器可核验面")
    missing = [p for p in paths if not (Path(p).is_file() and Path(p).stat().st_size > 0)]
    if missing:
        raise GateFail(f"G3 FAIL：/tmp 日志缺位或零字节（已跑声明不可核验）：{missing}")
    return (f"G3 已跑声明日志在盘非零字节：{len(paths)} 条 /tmp 路径逐一存在 ✓"
            f"（{'、'.join(p.split('/')[-1] for p in paths[:3])}… 等）")


def check_g4(gate_source: str) -> str:
    if "SEED_GATE = 20261017" not in gate_source:
        raise GateFail("G4 FAIL：门源码 SEED_GATE = 20261017 字面锚缺位（模板拷贝种子漂移？）")
    return "G4 门源码 SEED_GATE = 20261017 锚在档 ✓"


def check_g5(text: str) -> str:
    if "零求解" not in text:
        raise GateFail("G5 FAIL：零求解声明缺位")
    if not re.search(r"heavySolves\s*=\s*0", text):
        raise GateFail("G5 FAIL：heavySolves = 0 字面锚缺位")
    for pat in OVERREACH_PATTERNS:
        hits = re.findall(pat, text)
        if hits:
            raise GateFail(
                f"G5 FAIL：越权陈述命中：模式 {pat!r} ×{len(hits)}（探针件不得宣称证明完成）")
    return "G5 零求解声明锚（heavySolves = 0）＋越权陈述六模式零命中 ✓"


def check_g6(text: str) -> str:
    missing = [a for a in LEDGER_UNTOUCHED_ANCHORS if a not in text]
    if missing:
        raise GateFail(f"G6 FAIL：零账本触碰声明锚缺位：{missing}")
    return "G6 零账本触碰声明锚：四账本/endgame.json/certificates/typed_ladder 四字面在档 ✓"


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
            f"（r17 家族放行层在途 {n_family} 件按 D72 并行纪律放行；"
            f"本任务自有四件均在 formal/ 之外）")


def run_core_checks(path: Path) -> None:
    """G1–G7 全跑（对 path 指向的件；G7 恒对真仓）；任一 FAIL 即抛 GateFail。"""
    log(check_g1(path))
    text = path.read_text(encoding="utf-8")
    log(check_g2(text))
    log(check_g3(text))
    log(check_g4(Path(__file__).resolve().read_text(encoding="utf-8")))
    log(check_g5(text))
    log(check_g6(text))
    log(check_g7())


def run_negative_controls(study: Path) -> None:
    text = study.read_text(encoding="utf-8")
    with tempfile.TemporaryDirectory(prefix="r17b_nc_") as td:
        tmp = Path(td)
        # NC1：节删改——删 §Q3 标题，G2 必须拦
        nc1_text = text.replace(f"## {SECTIONS[2]}", "##（已删）", 1)
        try:
            check_g2(nc1_text)
            raise GateFail("NC1 FAIL：节删副本未被 G2 拦（负对照失效）")
        except GateFail as e:
            if "NC1 FAIL" in str(e):
                raise
            log("NC1 节删副本被拦 ✓")
        # NC2：假日志路径——首条日志路径换成不存在的路径，G3 必须拦
        paths = sorted(set(TMP_PATH_RE.findall(text)))
        bogus = "/tmp/r17b_NONEXISTENT_9q4.log"
        nc2_text = text.replace(paths[0], bogus, 1)
        try:
            check_g3(nc2_text)
            raise GateFail("NC2 FAIL：假日志路径副本未被 G3 拦（负对照失效）")
        except GateFail as e:
            if "NC2 FAIL" in str(e):
                raise
            log(f"NC2 假日志路径副本被拦 ✓（{e}）")
    # NC3：模拟入库——临时 git 仓库的 formal 树副本造非家族新文件，G7 必须拦
    with tempfile.TemporaryDirectory(prefix="r17b_nc3_") as td:
        fake = Path(td)
        (fake / "base.md").write_text("base\n", encoding="utf-8")
        _git_ok_or_die(fake, "init", "-q")
        _git_ok_or_die(fake, "-c", "user.email=nc3@gate", "-c", "user.name=nc3",
                       "add", "base.md")
        _git_ok_or_die(fake, "-c", "user.email=nc3@gate", "-c", "user.name=nc3",
                       "commit", "-q", "-m", "base")
        ingest = fake / "formal" / "lean" / "ThomsonN9"
        ingest.mkdir(parents=True)
        (ingest / "BogusIngestR17.lean").write_text("import Mathlib\n", encoding="utf-8")
        try:
            check_g7(fake)
            raise GateFail("NC3 FAIL：模拟入库副本未被 G7 拦（负对照失效）")
        except GateFail as e:
            if "NC3 FAIL" in str(e):
                raise
            log("NC3 模拟入库副本被拦 ✓（formal/ 树临时副本＋非家族新文件）")


def _git_ok_or_die(repo: Path, *args: str) -> None:
    proc = subprocess.run(["git", "-C", str(repo), *args],
                          capture_output=True, text=True, timeout=60)
    if proc.returncode != 0:
        raise GateFail(f"NC3 环境失败：git {' '.join(args)}：{proc.stderr.strip()[:200]}")


def main() -> None:
    ap = argparse.ArgumentParser(description="R17B B5c 四件探针验收门（纯文本＋git 状态检查）")
    ap.add_argument("--file", default=str(STUDY_DEFAULT),
                    help="探针件路径（默认仓内 notes/b5c-assembly-probe.md）")
    ap.add_argument("--no-nc", action="store_true", help="跳过负对照")
    args = ap.parse_args()
    study = Path(args.file).resolve()

    log(f"[gate] r17_b5c2_gate（seed {SEED_GATE}，CWD 无关，纯 python3 零 Lean 编译）")
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
        + ("＋NC1/NC2/NC3 负对照全触发" if not args.no_nc else "（--no-nc）")
        + "——exit 0")


if __name__ == "__main__":
    main()
