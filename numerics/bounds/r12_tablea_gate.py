#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r12_tablea_gate.py — R12 r12b 表 A 首两件（A5/A2′）Lean 化验收门（G1–G5＋负对照 NC1/NC2）.

任务书口径（r12b-tablea-lean，D49 裁决 2）：Stage B 结构定理层表 A（notes/stageb-scope.md §2）
首两件 Lean 化——A5 L2 强制恒等式（l2_eps_forcing_identity，四 ℚ 字面量取自
numerics/bounds/results/l2_rigorous.json：E_star / certified_recomputed / R2max_exact /
eps_forcing.exact，恒等式 (1+R2max)·(E*−certified)=ε_forcing）＋A2′ 引理 4.1 正性件
（dfactorialOdd 递归定义、phiDeriv m t = (2m−1)!!/√((2−2t)^(2m+1))、
hasDerivAt_phiDeriv＋phiDeriv_pos）。产出件 formal/lean/ThomsonN9/TableA.lean 仅
import Mathlib，不 import 仓内解件、不被其 import，不触 Solution.lean/check.sh/lakefile
（与 r12a M1 Lean 全链并行、文件面零交叠）。本门全确定性检查（无随机路径），
seed 20261014 按惯例记档；PATH 自动前置 ~/.elan/bin（缺失即 FAIL 附信息）；
CWD 无关（全部路径自 __file__ 推导）。

检查面（对应任务书 G1–G5＋NC1/NC2）：
  G0 账本在场与受控字段（seed == 20261014、heavy_solves == 0、自有四件在账本清单）。
  G1 文件所有权守卫：git status --porcelain 与 git diff HEAD --name-only 相对 HEAD
     的全部改动路径 ⊆ 本任务自有四件（TableA.lean / 本门 / r12_tablea_ledger.json /
     tablea-lean.md）；冻结件（ComparatorChallenges/lakefile/manifest/toolchain/
     Solution.lean/check.sh 等）的任何改动都会因此被拒。
  G2 单文件 elaboration：子进程 `lake env lean ThomsonN9/TableA.lean`（CWD=formal/lean）
     exit 0 且输出无 error／无 sorry 警告——不整库 build，规避 r12a 并行在途态干扰。
  G3 公理：先将 TableA.lean 编译为 olean 落在 formal/lean/.lake/build/lib/lean/
     ThomsonN9/TableA.olean（gitignored 构建产物位，lake env 的 LEAN_PATH 原生可见），
     再生成 /tmp 检查件 import ThomsonN9.TableA 并 #print axioms 三定理
     （l2_eps_forcing_identity / hasDerivAt_phiDeriv / phiDeriv_pos）——
     公理集恰 ⊆ {propext, Classical.choice, Quot.sound}，无 sorryAx/ofReduceBool/
     ofReduceNat/trustCompiler。
  G4 语句 regex：源码 import 行恰 [import Mathlib]；两定理名＋命题形状锚
     （A5：`1 +`、双差、RHS 单分数的 ℚ 字面量结构；A2′：
     HasDerivAt (phiDeriv m) (phiDeriv (m+1) t) t 与 0 < phiDeriv m t）；
     dfactorialOdd/phiDeriv 定义在场；非交叠守卫（Solution.lean / ThomsonN9.lean /
     lakefile.toml / scripts/check.sh 源码不含 "TableA"）。
  G5 离线精确复核（stdlib Fraction，零外部依赖）：
     A5——自 l2_rigorous.json 重读四分数串重析 Fraction、重算恒等式
     (1+R2max)·(E*−certified)==ε_forcing（并核对 json identity_check.holds==true）；
     与 TableA.lean 源码 regex 抽取的 ℚ 字面量四分数逐分量（分子/分母整数）比对全等。
     A2′——平方化判据：(phiDeriv m t)² == df²·(2−2t)^(−(2m+1)) 于 m=0..8、t=−7/4
     精确成立；左端用源码字面量（解析 dfactorialOdd 递归基/步与 phiDeriv 分母的
     (2−2t)^(2m+1) 结构）自算，右端用独立实现的 (2m−1)!! 与 2−2t（与源码字面量比对）。
  NC1 注入 sorry 必被 G3 拦：/tmp 副本把 A5 证明改 sorry → 独立编译＋公理检查
     必现 sorryAx → G3 判定逻辑必 FAIL（未篡副本 sanity：公理检查 PASS）。
  NC2 篡字面量必被 G5 拦：/tmp 副本两处篡改——(a) A5 ε 分子末位数字＋1；
     (b) dfactorialOdd 递归基 1→2——G5 对应检查函数必 FAIL（原文件 sanity PASS）。

用法（CWD 无关）：
  python3 numerics/bounds/r12_tablea_gate.py     # 全门（exit 0 = 过）
  python3 thomson-n9/numerics/bounds/r12_tablea_gate.py
      # ↑ CWD＝仓库根时的验收命令命中同名 runpy 包装器（沿 R10A 0087eab 先例，
      #   thomson-n9/thomson-n9/… → 本真实门，exit code 原样传播；CWD＝campaign
      #   根时该相对路径直接命中本文件，包装器不参与）

自跑专用：R12 r12a/r12c 并行会话在途件未提交时，可设
  R12B_G1_ALLOW_FOREIGN=numerics/bounds/endgame_gate.py,... python3 ...
对 G1 显式放行这些非本任务路径（逐项响亮打印；验收/常规运行不设该变量，
G1 字面严格——提交后树净 ⇒ 恒过）。
"""
from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import sys
import time
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
REPO = HERE.parents[1]                 # thomson-n9/
LEAN_DIR = REPO / "formal" / "lean"

SEED_GATE = 20261014                   # 惯例记档；本门无随机路径（确定性）

TABLEA_REL = "formal/lean/ThomsonN9/TableA.lean"
GATE_REL = "numerics/bounds/r12_tablea_gate.py"
WRAPPER_REL = "thomson-n9/numerics/bounds/r12_tablea_gate.py"   # CWD 兼容包装器（沿 R10A 0087eab 先例）
LEDGER_REL = "numerics/bounds/results/r12_tablea_ledger.json"
NOTES_REL = "notes/tablea-lean.md"
OWNED = {TABLEA_REL, GATE_REL, WRAPPER_REL, LEDGER_REL, NOTES_REL}

L2_JSON = RESULTS / "l2_rigorous.json"
TABLEA = LEAN_DIR / "ThomsonN9" / "TableA.lean"
OLEAN_REL = ".lake/build/lib/lean/ThomsonN9/TableA.olean"
LEDGER = RESULTS / "r12_tablea_ledger.json"
TMP = Path("/tmp/r12_tablea_gate")

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN_AXIOMS = ("sorryAx", "ofReduceBool", "ofReduceNat", "trustCompiler")
THEOREMS = [
    "ThomsonN9.TableA.l2_eps_forcing_identity",
    "ThomsonN9.TableA.hasDerivAt_phiDeriv",
    "ThomsonN9.TableA.phiDeriv_pos",
]

# ---- 负对照 / G5 解析口径 ------------------------------------------------
A5_TAIL = "62308232016279826168812154155836080188260221347417966571668186047549261057992006380543153"
RE_Q_LITERAL = re.compile(r"\((\d+) : ℚ\)\s*/\s*(\d+)")
RE_DFAC_BASE = re.compile(r"\|\s*0\s*=>\s*(\d+)\s*$", re.M)
RE_DFAC_STEP = re.compile(r"\|\s*m \+ 1\s*=>\s*\((\d+) \* m \+ (\d+)\) \* dfactorialOdd m")
RE_PHIDERIV_DEN = re.compile(
    r"Real\.sqrt \(\(2 - 2 \* t\) \^ \(2 \* m \+ 1\)\)")


class GateFail(Exception):
    """单门失守（main 统一转 [gate][FAIL] ＋ exit 1；负对照捕获它作预期检出）。"""


def fail(msg: str) -> None:
    raise GateFail(msg)


def okmsg(msg: str) -> None:
    print(f"[gate][ok] {msg}", flush=True)


def sha256_of(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


# ------------------------------------------------------------------ env
def gate_env() -> dict:
    elan = Path.home() / ".elan" / "bin"
    env = dict(os.environ)
    env["PATH"] = str(elan) + os.pathsep + env.get("PATH", "")
    return env


def run(cmd, cwd: Path, timeout_s: int = 580):
    return subprocess.run(cmd, cwd=str(cwd), env=gate_env(), capture_output=True,
                          text=True, timeout=timeout_s)


def require_toolchain() -> None:
    probe = run(["lake", "--version"], LEAN_DIR)
    if probe.returncode != 0:
        fail(f"PATH 前置 ~/.elan/bin 后 lake 不可用：{probe.stderr.strip()[:300]}")


# ------------------------------------------------------------------ G0
def gate0_ledger():
    if not LEDGER.is_file():
        fail(f"G0 账本不在场：{LEDGER_REL}")
    led = json.loads(LEDGER.read_text())
    if led.get("seed") != SEED_GATE:
        fail(f"G0 账本 seed 失配：{led.get('seed')!r} != {SEED_GATE}")
    if led.get("heavy_solves") != 0:
        fail(f"G0 账本 heavy_solves 失配：{led.get('heavy_solves')!r} != 0")
    files = led.get("files", {})
    for rel in OWNED:
        if rel not in files:
            fail(f"G0 账本 files 缺自有件：{rel}")
    okmsg(f"G0 账本在场（seed={SEED_GATE}，heavy_solves=0，自有件{len(OWNED)}全在清单）")
    return led


# ------------------------------------------------------------------ G1
def porcelain_paths(out: str) -> list:
    paths = []
    for ln in out.splitlines():
        if not ln.strip():
            continue
        if ln.startswith("?? ") or ln.startswith("!! "):
            paths.append(ln[3:].strip().strip('"'))
        else:
            p = ln[3:].strip().strip('"')
            if " -> " in p:                      # rename：取新路径
                p = p.split(" -> ")[-1]
            paths.append(p)
    return paths


def gate1_ownership():
    # 自跑专用放行清单（默认关）：R12 r12a/r12c 并行会话的在途件可经环境变量
    # R12B_G1_ALLOW_FOREIGN=p1,p2 显式放行（逐项响亮打印）；验收/常规运行不设该变量，
    # G1 保持字面严格（提交后树净 ⇒ 全集为空 ⇒ 恒过）。
    allow_foreign = {p.strip() for p in
                     os.environ.get("R12B_G1_ALLOW_FOREIGN", "").split(",") if p.strip()}
    for cmd in (["git", "status", "--porcelain"], ["git", "diff", "HEAD", "--name-only"]):
        r = run(cmd, REPO)
        if r.returncode != 0:
            raise GateFail(f"G1 {cmd[1]} 失败：{r.stderr.strip()[:300]}")
        paths = porcelain_paths(r.stdout) if "--porcelain" in cmd else \
            [ln.strip().strip('"') for ln in r.stdout.splitlines() if ln.strip()]
        for p in paths:
            if p in OWNED:
                continue
            if p in allow_foreign:
                print(f"[gate][G1][自跑放行] 并行在途件（非本任务产物，显式放行）：{p}")
                continue
            raise GateFail(
                f"G1 树上出现非本任务自有件（{cmd[1]}）：{p!r}（自有集={sorted(OWNED)}；"
                f"自跑遇 r12a/r12c 并行在途件可设 R12B_G1_ALLOW_FOREIGN 显式放行）")
    okmsg("G1 文件所有权守卫：git status/diff 相对 HEAD 仅本任务自有件（或全净）"
          + (f"〔放行并行件 {sorted(allow_foreign)}〕" if allow_foreign else ""))


# ------------------------------------------------------------------ G2
def gate2_elaborate() -> float:
    t0 = time.time()
    r = run(["lake", "env", "lean", "ThomsonN9/TableA.lean"], LEAN_DIR)
    wall = time.time() - t0
    if r.returncode != 0:
        fail(f"G2 单文件 elaboration 失败（exit {r.returncode}）：\n{r.stdout[-800:]}\n{r.stderr[-800:]}")
    out = r.stdout + r.stderr
    if "error" in out or "sorry" in out:
        fail(f"G2 elaboration 输出含 error/sorry：\n{out[-800:]}")
    okmsg(f"G2 单文件 elaboration：lake env lean ThomsonN9/TableA.lean exit 0（{wall:.1f}s，输出无 error/sorry）")
    return wall


# ------------------------------------------------------------------ G3
def parse_axiom_lines(out: str) -> dict:
    ax = {}
    for line in out.splitlines():
        m = re.match(r"'([^']+)'\s+depends on axioms:\s*\[(.*)\]", line.strip())
        if m:
            ax[m.group(1)] = {a.strip() for a in m.group(2).split(",") if a.strip()}
    return ax


def check_axioms(ax: dict, ctx: str) -> None:
    for th in THEOREMS:
        if th not in ax:
            fail(f"{ctx}：公理输出缺定理 {th}（解析到：{sorted(ax)}）")
        bad = ax[th] - ALLOWED_AXIOMS
        if bad:
            fail(f"{ctx}：定理 {th} 依赖非标准公理 {sorted(bad)}")
        for f in FORBIDDEN_AXIOMS:
            if f in ax[th]:
                fail(f"{ctx}：定理 {th} 依赖 {f}")
    okmsg(f"{ctx}：三定理公理集 ⊆ {{propext, Classical.choice, Quot.sound}}"
          f"（实际 {sorted(set().union(*ax.values()))}）")


def gate3_axioms() -> None:
    olean = LEAN_DIR / OLEAN_REL
    olean.parent.mkdir(parents=True, exist_ok=True)
    r = run(["lake", "env", "lean", "-o", OLEAN_REL, "ThomsonN9/TableA.lean"], LEAN_DIR)
    if r.returncode != 0 or not olean.is_file():
        fail(f"G3 TableA.olean 编译失败（exit {r.returncode}）：\n{r.stdout[-500:]}\n{r.stderr[-500:]}")
    TMP.mkdir(parents=True, exist_ok=True)
    axfile = TMP / "axcheck.lean"
    axfile.write_text(
        "import ThomsonN9.TableA\n"
        + "".join(f"#print axioms {th}\n" for th in THEOREMS))
    r = run(["lake", "env", "lean", str(axfile)], LEAN_DIR)
    if r.returncode != 0:
        fail(f"G3 公理检查件编译失败（exit {r.returncode}）：\n{r.stdout[-500:]}\n{r.stderr[-500:]}")
    ax = parse_axiom_lines(r.stdout)
    check_axioms(ax, "G3 公理")


# ------------------------------------------------------------------ G4
def gate4_statement(src: str) -> None:
    imports = re.findall(r"^import\s+\S+", src, re.M)
    if imports != ["import Mathlib"]:
        fail(f"G4 import 行失配：{imports}（应恰为 [import Mathlib]）")
    anchors = [
        (r"theorem l2_eps_forcing_identity\s*:", "A5 定理名"),
        (r"1 \+ \(\d+ : ℚ\) / \d+", "A5 形状锚：1 + R2max"),
        (r"\*\s*\(\(\d+ : ℚ\) / \d+\s*-\s*\(\d+ : ℚ\) / \d+\)", "A5 形状锚：(E* − certified) 因子"),
        (r"=\s*\(\d+ : ℚ\) / \d+", "A5 形状锚：= ε_forcing"),
        (r"theorem hasDerivAt_phiDeriv\s*\(m : ℕ\) \(t : ℝ\)", "A2′ 定理签名"),
        (r"HasDerivAt \(phiDeriv m\) \(phiDeriv \(m \+ 1\) t\) t", "A2′ 命题形状锚"),
        (r"theorem phiDeriv_pos\s*\(m : ℕ\) \(t : ℝ\)", "A2′ 正性引理签名"),
        (r"0 < phiDeriv m t", "A2′ 正性命题锚"),
        (r"def dfactorialOdd : ℕ → ℚ", "dfactorialOdd 定义锚"),
        (r"noncomputable def phiDeriv \(m : ℕ\) \(t : ℝ\) : ℝ", "phiDeriv 定义锚"),
        (RE_PHIDERIV_DEN, "phiDeriv 分母结构锚 (2−2t)^(2m+1)"),
    ]
    for pat, name in anchors:
        if not re.search(pat, src):
            fail(f"G4 语句锚缺失：{name}（pattern {pat!r}）")
    # 非交叠守卫：冻结/解件面不含 TableA
    for rel in ("ThomsonN9/Solution.lean", "ThomsonN9.lean", "lakefile.toml",
                "scripts/check.sh"):
        p = LEAN_DIR / rel
        if p.is_file() and "TableA" in p.read_text():
            fail(f"G4 非交叠守卫：{rel} 含 'TableA'（本件必须不被 import／不被引用）")
    okmsg("G4 语句锚：import 恰 [Mathlib]；A5/A2′ 定理名＋命题形状锚＋定义锚全在；"
          "Solution.lean/根模块/lakefile/check.sh 零 TableA 引用（非交叠）")


# ------------------------------------------------------------------ G5
def parse_frac(s: str) -> Fraction:
    num, den = s.split("/")
    return Fraction(int(num), int(den))


def g5_a5(src: str, l2: dict) -> dict:
    fr = {
        "E_star": parse_frac(l2["E_star"]["value"]),
        "certified": parse_frac(l2["certificate_rebuild"]["certified_recomputed"]),
        "R2max": parse_frac(l2["certificate_rebuild"]["R2max_exact"]),
        "eps": parse_frac(l2["eps_forcing"]["exact"]),
    }
    if l2["eps_forcing"]["identity_check"]["holds"] is not True:
        fail("G5·A5 l2_rigorous.json identity_check.holds != true（Python 侧先证锚缺失）")
    if (1 + fr["R2max"]) * (fr["E_star"] - fr["certified"]) != fr["eps"]:
        fail("G5·A5 重算恒等式 (1+R2max)·(E*−certified) == ε_forcing 不成立（Fraction 精确）")
    lits = RE_Q_LITERAL.findall(src)
    if len(lits) != 4:
        fail(f"G5·A5 源码 ℚ 字面量抽取数 {len(lits)} != 4")
    got = [Fraction(int(n), int(d)) for n, d in lits]
    want = [fr["E_star"], fr["certified"], fr["R2max"], fr["eps"]]
    if sorted(got) != sorted(want):
        fail(f"G5·A5 源码 ℚ 字面量与 json 四分数失配：源码 {sorted(got)} vs json {sorted(want)}")
    # 逐分量（分子/分母整数）比对（sorted-by-Fraction 已等值；再钉字符串分量）
    lit_pairs = sorted((int(n), int(d)) for n, d in lits)
    json_pairs = sorted((f.numerator, f.denominator) for f in want)
    if lit_pairs != json_pairs:
        fail(f"G5·A5 逐分量比对失配：{lit_pairs} vs {json_pairs}")
    return {"identity_recomputed": True, "literals_match": True,
            "fractions": {k: f"{v.numerator}/{v.denominator}" for k, v in fr.items()}}


def dfac_std(m: int) -> int:
    """独立实现的 (2m−1)!! = 1·3·⋯·(2m−1)（m=0 → 1）——不读源码。"""
    out = 1
    for i in range(1, 2 * m, 2):
        out *= i
    return out


def g5_a2(src: str) -> dict:
    mb = RE_DFAC_BASE.search(src)
    if not mb:
        fail("G5·A2′ 源码缺 dfactorialOdd 递归基（pattern `| 0 => d`）")
    ms = RE_DFAC_STEP.search(src)
    if not ms:
        fail("G5·A2′ 源码缺 dfactorialOdd 递归步（pattern `| m + 1 => (c1 * m + c2) * dfactorialOdd m`）")
    if not RE_PHIDERIV_DEN.search(src):
        fail("G5·A2′ 源码缺 phiDeriv 分母结构 Real.sqrt ((2 - 2 * t) ^ (2 * m + 1))")
    base, c1, c2 = int(mb.group(1)), int(ms.group(1)), int(ms.group(2))
    # 源码字面量驱动的递归（不硬编码基/步常量——篡字面量将沿递归传导至下方判据被拦）
    df = [base]
    for m in range(1, 9):
        df.append((c1 * (m - 1) + c2) * df[m - 1])   # df(m) = (c1·m + c2)·df(m−1)（步进从 m−1）
    t = Fraction(-7, 4)
    u_src = Fraction(2, 1) - Fraction(2, 1) * t       # 源码字面量 (2 − 2·t)
    u_std = Fraction(11, 2)                           # 独立算：2 − 2·(−7/4) = 11/2
    if u_src != u_std:
        fail(f"G5·A2′ 源码内积 (2−2t) 于 t=−7/4 失配：{u_src} != {u_std}")
    for m in range(0, 9):
        if df[m] != dfac_std(m):
            fail(f"G5·A2′ 源码递归值 vs 独立 (2m−1)!! 失配于 m={m}：{df[m]} != {dfac_std(m)}")
        exp = 2 * m + 1                                # 源码指数结构 (2m+1)
        lhs = Fraction(df[m] ** 2, 1) * u_src ** (-exp)   # (phiDeriv m t)²（平方消去 √）
        rhs = Fraction(dfac_std(m) ** 2, 1) * u_std ** (-(2 * m + 1))
        if lhs != rhs:
            fail(f"G5·A2′ 平方化判据失配于 m={m}：{lhs} != {rhs}")
    okmsg("G5 离线精确复核：A5 四分数自 json 重读重算恒等式==源码 ℚ 字面量（4/4）；"
          "A2′ 平方化判据 (phiDeriv m t)²==df²·(2−2t)^(−(2m+1)) 于 m=0..8、t=−7/4 全过"
          "（源码字面量 vs 独立 (2m−1)!! 双侧）")
    return {"base": base, "c1": c1, "c2": c2,
            "df_values": df, "t": "-7/4", "u": "11/2"}


# ------------------------------------------------------------------ NC
def nc1_sorry_injection(src: str) -> None:
    tampered = src.replace("  norm_num\n", "  sorry\n", 1)
    if "sorry" not in tampered:
        fail("NC1 预置失败：未能在 /tmp 副本注入 sorry（源码缺 `  norm_num` 行）")
    d = TMP / "nc1"
    (d / "ThomsonN9").mkdir(parents=True, exist_ok=True)
    (d / "ThomsonN9" / "TableA.lean").write_text(tampered)
    lp = run(["lake", "env", "printenv", "LEAN_PATH"], LEAN_DIR).stdout.strip()
    env = gate_env()
    env["LEAN_PATH"] = f"{d}:{lp}"
    b = subprocess.run(["lean", "--root", str(d), "-o", str(d / "ThomsonN9" / "TableA.olean"),
                        str(d / "ThomsonN9" / "TableA.lean")],
                       cwd=str(LEAN_DIR), env=env, capture_output=True, text=True, timeout=580)
    if b.returncode != 0 or "declaration uses `sorry`" not in (b.stdout + b.stderr):
        fail(f"NC1 注入 sorry 后编译未产生 sorry 警告（exit {b.returncode}）：\n{(b.stdout + b.stderr)[-500:]}")
    axfile = d / "axcheck.lean"
    axfile.write_text("import ThomsonN9.TableA\n#print axioms ThomsonN9.TableA.l2_eps_forcing_identity\n")
    a = subprocess.run(["lean", str(axfile)], cwd=str(LEAN_DIR), env=env,
                       capture_output=True, text=True, timeout=580)
    ax = parse_axiom_lines(a.stdout)
    th = "ThomsonN9.TableA.l2_eps_forcing_identity"
    caught = th in ax and ("sorryAx" in ax[th] or (ax[th] - ALLOWED_AXIOMS))
    if not caught:
        fail(f"NC1 失守：注入 sorry 后公理检查未现 sorryAx（{ax}）")
    okmsg(f"NC1 注入 sorry 必被 G3 拦：篡件公理集 = {sorted(ax.get(th, set()))}（含 sorryAx → G3 FAIL）")


def nc2_literal_tamper(src: str, l2: dict) -> None:
    # (a) A5 ε 分子末位数字 +1
    bad_a5 = src.replace(A5_TAIL, A5_TAIL[:-1] + str(int(A5_TAIL[-1]) + 1), 1)
    if bad_a5 == src:
        raise GateFail("NC2(a) 预置失败：未篡到 A5 ε 分子字面量")
    try:
        g5_a5(bad_a5, l2)
        raise GateFail("NC2(a) 失守：篡 A5 ℚ 字面量后 G5·A5 未报错")
    except GateFail as e:
        if "失守" in str(e) or "预置" in str(e):
            raise
        print(f"[gate][NC2-a 检出] {e}")
    # (b) dfactorialOdd 递归基 1 → 2（"| 0 => 1" 在源码中唯一，见 G4 定义锚）
    bad_a2 = src.replace("| 0 => 1", "| 0 => 2", 1)
    if bad_a2 == src:
        raise GateFail("NC2(b) 预置失败：未篡到 dfactorialOdd 递归基")
    try:
        g5_a2(bad_a2)
        raise GateFail("NC2(b) 失守：篡递归基后 G5·A2′ 未报错")
    except GateFail as e:
        if "失守" in str(e) or "预置" in str(e):
            raise
        print(f"[gate][NC2-b 检出] {e}")
    # sanity：原文件双函数 PASS（此处重复调用不改变其确定性结论）
    g5_a5(src, l2)
    g5_a2(src)
    okmsg("NC2 篡字面量必被 G5 拦：A5 ε 分子末位＋1 与 dfactorialOdd 基 1→2 双篡均被检出；"
          "原文件双函数 sanity PASS")


# ------------------------------------------------------------------ main
def main() -> None:
    t0 = time.time()
    print(f"[gate] r12_tablea_gate.py seed={SEED_GATE}（确定性，无随机路径）")
    try:
        run_gate()
    except GateFail as e:
        print(f"[gate][FAIL] {e}", flush=True)
        sys.exit(1)
    wall = time.time() - t0
    print(f"[gate] PASS（{wall:.1f}s）——exit 0")
    print(f"[gate] heavySolves=0（本门零求解：仅 elaboration/公理/regex/Fraction 复核）")


def run_gate() -> None:
    t0 = time.time()
    require_toolchain()
    if not TABLEA.is_file():
        fail(f"TableA.lean 不在场：{TABLEA_REL}")
    if not L2_JSON.is_file():
        fail(f"l2_rigorous.json 不在场：{L2_JSON}")
    src = TABLEA.read_text()
    l2 = json.loads(L2_JSON.read_text())

    gate0_ledger()
    gate1_ownership()
    wall2 = gate2_elaborate()
    gate3_axioms()
    gate4_statement(src)
    g5_a5(src, l2)
    g5_a2(src)
    nc1_sorry_injection(src)
    nc2_literal_tamper(src, l2)
    print(f"[gate] G2 elaboration 墙钟 {wall2:.1f}s；全门 {time.time() - t0:.1f}s")


if __name__ == "__main__":
    main()
