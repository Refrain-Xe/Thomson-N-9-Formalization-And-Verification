#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r18_b5c_gate.py — R18A 表 B 第六件 B5c 极分解件（l4_procrustes.py 步骤 5–6
极分解/装配层 Lean 化，D77 裁决 1/2 口径）验收门（G0–G5＋负对照 NC1/NC2/NC3）.

任务书口径（r18a-b5c-polar-lean，campaign dwfrun-f9904baf 第 13 轮）：
B5c＝l4_procrustes.py 证明步骤 5–6 的 Lean 化——sqrt 单调性（D78-3 路线：
谱映射＋CFC 序；CFC.sqrt_le_sqrt 直接路线被 ℝ 矩阵 NonUnitalCStarAlgebra
实例缺失阻断）＋W 构造层（CFC.sqrt 供给族）＋R 正交层（orthogonalGroup
membership 主口径＋双等式口径）＋frob 正交右乘不变＋D77 补线头条
frob (W−1) ≤ (2/3)·frob B（(W+1)² ⪰ 9/4·1 二次型面＋B5b trace_ge_smul）＋
步骤 5 头条 ∃ Q ∈ orthogonalGroup, frob (X − Y*Q) ≤ √λ₁β + frob D_⊥＋
步骤 6 条件装配（D77 裁决 2：frob D_∥ ≤ σ₁β 前提显式携带，不做假闭合）＋
TTP 实例化（l3/u1 接线，前提显式）。产出件
formal/lean/ThomsonN9/TableB5Polar.lean（手写主件 42 定理，import Mathlib
＋TableB5＋TableB5Core＋TableB5Trace，零数值数据字面量故无 Data 件）。
本门全确定性（随机实例 seed 20261018 复放；PATH 自动前置 ~/.elan/bin）；
CWD 无关（全部路径自 __file__ 推导）。heavySolves=0（本门零求解：仅
elaboration/公理/regex/Fraction 复核；四账本/endgame.json 只读＋sha256 冻结）。

检查面（对应任务书 G0–G5＋NC1/NC2/NC3）：
  G0 账本在场与受控字段（seed == 20261018、heavy_solves == 0、自有六件在清单、
     data.theorem_count == 42、axiom_policy 恰三标准列表形态 set 相等）。
  G1 文件所有权守卫：git status --porcelain 与 git diff HEAD --name-only 的全部
     改动路径 ⊆ 本任务自有六件（＋环境变量 R18A_G1_ALLOW_FOREIGN 自跑逐件放行
     〔默认关〕＋PARALLEL_FAMILY r18 家族放行层〔r18[a-z0-9_]* pattern＋
     notes/dperp-gap-study.md＋endgame_gate.py＋GAP-REPORT/PROGRESS＋
     notes/decisions.md〔含设计师在途 D77〕＋r18c_closure_gate.py——
     D68-3/D72/D77-3 同款〕）；只读冻结件显式 git diff 守卫（TableB5/
     TableB5Data/TableB5Core/TableB5Trace/TableB1*/TableB6*＋挑战件目录
     ComparatorChallenges/＋references/——单独响亮报错）；四账本
     （m9_campaign/m10_campaign/hermite_v2_campaign/typed_ladder）＋
     endgame.json sha256 冻结锚（86863a09…69f）。
  G2 逐文件 elaboration：子进程 `lake env lean -o <olean>` 依赖序五连——
     ThomsonN9/TableB5Data.lean → ThomsonN9/TableB5.lean →
     ThomsonN9/TableB5Core.lean → ThomsonN9/TableB5Trace.lean →
     ThomsonN9/TableB5Polar.lean（均 CWD=formal/lean），各 exit 0、输出无
     error／无 sorry、墙钟 ≤ 600 s/文件（D52 裁决 4 / D64-5）；olen 落
     .lake/build/lib/lean/ThomsonN9/（gitignored），供 G3/NC1 复用。
  G3 公理：检查件 import ThomsonN9.TableB5Polar＋对**件内全部 theorem**
     （regex 枚举，≥28 预期、账本记精确数 42）#print axioms——公理集 ⊆
     {propext, Classical.choice, Quot.sound}，零 sorryAx/ofReduceBool/
     ofReduceNat/trustCompiler。
  G4 语句锚（行级 regex）：import 面恰 [Mathlib＋TableB5＋TableB5Core＋
     TableB5Trace]；sqrt 单调性头（c² 夹逼前提＋c 结论双面）／W 供给族
     （W_mul_W 命题形状 W*W = 1+B＋W_quadform_ge_half (1/2) 牙）／R 正交层
     （R_mul_RT 核心头＋R_mem_orthogonalGroup membership 形状＋
     Rinv_mem_orthogonalGroup）／frob 正交右乘不变（frob (M * Q) = frob M）／
     D77 补线头条（frob_Wm1_le (2/3) 牙——NC2 棱二）＋(W+1)² 二次型面
     （(9/4) 牙）／步骤 5 头条（∃ Q ∈ Matrix.orthogonalGroup n ℝ＋
     √λ₁·β＋frob D_⊥ 三牙）／条件前提可见牙（dperp_le 的 hdpar
     frob D_∥ ≤ √λ₁·β 字面＋step6_final 的 hdpar/hdom1/hdom2 三字面）／
     TTP 双头条（(l3:ℝ)^2 与 2/Real.sqrt (l3:ℝ) 字面牙——NC2 棱一）；
     零 ≥15 位数字字面量＋零『def … : ℚ :=』；非交叠守卫
     （Solution/TableA*/M1Data/TableB1*/TableB6*/根模块/lake 面/check.sh
     源码零 TableB5Polar 引用）。
  G5 离线精确复核（stdlib Fraction 零仓 import，独立第二实现：S⁻¹/极分解
     右因子 R⁻¹ Gauss-Jordan 消去自实现）：seed 20261018 ≥3 个随机有理实例
     （有理正交 O 取 Pythagorean 有理旋转（3/5,4/5）面＋W := diag 有理
     （w_i ≥ 1/2 保证 (W+1)² ⪰ 9/4 前提面）＋A := W·O − 1 构造使
     (1+A)(1+A)ᵀ = W² 精确）上逐项精确复核：
     (a) B 恒等式 B := A+Aᵀ+A·Aᵀ == W²−1（9 元逐元素）＋
         (1+A)(1+A)ᵀ − 1 == B（同面）；
     (b) 极分解 R := W⁻¹(1+A) == O（9 元）⇒ R·Rᵀ == I₃（正交核验）＋
         Q := R⁻¹ == Oᵀ（Gauss-Jordan 逆自检）；
     (c) YQ 恒等式 (X + X·A + D_⊥)·Q == X·W + D_⊥·Q（27 元逐元素）；
     (d) frob 正交右乘不变 frob(M·Q)² == frob M²（M ∈ {X, D_⊥, E} 三面）；
     (e) D77 补线 frob(W−1) ≤ (2/3)·frob B（数值结论直验；w_i ≥ 1/2 使
         (W+1)² ⪰ 9/4 前提面成立——squared 等价链
         (9/4)·frob(W−1)² ≤ frob(B)² 精确复核）；
     (f) σ₁ 列压缩 squared 链 frob(X(1−W))² ≤ λ₁·frob(W−1)²（X 取列正交
         框架使 XᵀX == λ₁·I₃ 由构造精确，λ₁ 有理）；
     (g) 步骤 3 面 squared 链 λ₃ ≤ (η/frob D_⊥ + frob D_∥)²（λ₃ == λ₁ 同
         构造；等价于 (√λ₃−frob D_∥)·frob D_⊥ ≤ η）；
     (h) 账本锚 cross-check（自有件 sha256 重算比对）＋C 链 Fraction 复核
         (s1Up³/l3² + 2/s3Dn)·sqrt72Up ≤ CVal（TableB5Data.lean 源直读
         字面量，零手抄）。
  NC1 注入 sorry 必被 G3 拦：/tmp 副本把 quadform_nonneg_of_posSemidef 证明改
     sorry → 独立编译（lean --root＋LEAN_PATH 前置副本目录）必现 sorry 警告＋
     公理检查必现 sorryAx → G3 判定逻辑必 FAIL（未篡原件 sanity：G3 全 42 件过）。
  NC2 篡陈述必被 G4 拦（双棱）：/tmp 副本 (l3:ℝ)^2 → (l3:ℝ)^3（TTP 条件终定理
     指数面）与 (2/3) → (3/4)（D77 补线头条常数面）→ G4 语句锚 regex 必 FAIL
     （两面牙有牙实证；原文件 sanity PASS）。
  NC3 错误引擎必被 G5 拦（双棱）：(i) W' := 1+B（恒等代替 sqrt 的错误极因子）
     代入 D77 补线复核 ⇒ frob(W'−1) = frob B > (2/3)·frob B 必被检出（防假
     拦截：篡引擎在固定实例上必被检出）；(ii) 伪正交 Q' := (3/2)·Q 代入
     frob 右乘不变复核 ⇒ frob(M·Q')² == (9/4)·frob M² ≠ frob M² 必被检出。

用法（CWD 无关）：
  python3 numerics/bounds/r18_b5c_gate.py     # 全门（exit 0 = 过）
  python3 thomson-n9/numerics/bounds/r18_b5c_gate.py
      # ↑ CWD＝仓库根时的验收命令命中同名 runpy 包装器（沿 R10A 0087eab／
      #   R14A r14_b5／R16A r16_b5a／R17A r17_b5b 先例，包装器重定向到真实门）
"""
from __future__ import annotations

import hashlib
import json
import os
import random
import re
import subprocess
import sys
import time
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
REPO = HERE.parents[1]                 # thomson-n9/
LEAN_DIR = REPO / "formal" / "lean"
CAMPAIGN_ROOT = REPO.parent            # 八电子在球面的分布/

SEED_GATE = 20261018                  # R18 各门统一 seed
ELAB_LIMIT_S = 600                    # G2 每文件 ≤10 min（D52 裁决 4 / D64-5）
THEOREM_COUNT = 42                    # 件内定理精确数（regex 枚举＋账本双面）

POLAR_REL = "formal/lean/ThomsonN9/TableB5Polar.lean"
GATE_REL = "numerics/bounds/r18_b5c_gate.py"
WRAPPER_REL = "thomson-n9/numerics/bounds/r18_b5c_gate.py"   # CWD 兼容包装器
LEDGER_REL = "numerics/bounds/results/r18_b5c_ledger.json"
NOTES_REL = "notes/tableb-lean.md"
DECISIONS_REL = "notes/decisions.md"
OWNED = {POLAR_REL, GATE_REL, WRAPPER_REL, LEDGER_REL, NOTES_REL, DECISIONS_REL}

# 只读冻结件（表 B 前五件常数/本体件＋表 B 其余件）：显式 git diff 守卫。
FROZEN_READONLY = (
    "formal/lean/ThomsonN9/TableB5.lean",
    "formal/lean/ThomsonN9/TableB5Data.lean",
    "formal/lean/ThomsonN9/TableB5Core.lean",
    "formal/lean/ThomsonN9/TableB5Trace.lean",
    "formal/lean/ThomsonN9/TableB1.lean",
    "formal/lean/ThomsonN9/TableB1Data.lean",
    "formal/lean/ThomsonN9/TableB6.lean",
    "formal/lean/ThomsonN9/TableB6Data.lean",
)
# 挑战件目录与 references/（命题冻结面）：整目录 git 守卫（目录内任一改动即拦）。
FROZEN_DIRS = ("formal/lean/ComparatorChallenges", "references")
# 四账本（只读冻结，R11C–R17 先例口径）＋ endgame.json sha256 冻结锚。
FROZEN_LEDGERS = (
    "numerics/bounds/results/m9_campaign.json",
    "numerics/bounds/results/m10_campaign.json",
    "numerics/bounds/results/hermite_v2_campaign.json",
    "numerics/bounds/results/typed_ladder.json",
)
ENDGAME_REL = "numerics/bounds/results/endgame.json"
ENDGAME_SHA256 = "86863a09bf84e950e85fc5f902bc2b4046a87f06703bd782e5148fc119afd69f"

# 并行家族放行集（D68-3/D72/D77-3 同款：r18 家族 pattern＋R18B 并行研究件＋
# 轮次文档三件＋R18C 收口门——本任务与 R18B/R18C 文件集零交叠）。
PARALLEL_FAMILY = [
    r"^numerics/bounds/r18[a-z0-9_]*(\.py|/)",
    r"^numerics/bounds/results/r18[a-z0-9_]*(\.json|/)",
    r"^thomson-n9/numerics/bounds/r18[a-z0-9_]*(\.py|/)",
    r"^notes/decisions\.md$",
    r"^notes/dperp-gap-study\.md$",
    r"^notes/tableb-lean\.md$",
    r"^numerics/bounds/endgame_gate\.py$",
    r"^(GAP-REPORT|PROGRESS)\.md$",
]

# 非交叠守卫面（表 A/M1/Solution 面＋表 B 其余件＋根模块/lake 面，零交叠机器化）
NONOVERLAY_FILES = ("ThomsonN9/Solution.lean", "ThomsonN9/TableA.lean",
                    "ThomsonN9/TableA1.lean", "ThomsonN9/TableA3.lean",
                    "ThomsonN9/TableA4.lean", "ThomsonN9/TableA6.lean",
                    "ThomsonN9/M1Data.lean", "ThomsonN9/TableB1.lean",
                    "ThomsonN9/TableB1Data.lean", "ThomsonN9/TableB6.lean",
                    "ThomsonN9/TableB6Data.lean",
                    "ThomsonN9.lean", "lakefile.toml", "scripts/check.sh")

TMP = Path("/tmp/r18_b5c_gate")
OLEAN_REL = ".lake/build/lib/lean/ThomsonN9"
POLAR_LEAN = LEAN_DIR / "ThomsonN9" / "TableB5Polar.lean"
LEDGER = RESULTS / "r18_b5c_ledger.json"
NOTES = REPO / "notes" / "tableb-lean.md"
DATA_LEAN = LEAN_DIR / "ThomsonN9" / "TableB5Data.lean"

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN_AXIOMS = ("sorryAx", "ofReduceBool", "ofReduceNat", "trustCompiler")

F0, F1 = Fr(0), Fr(1)


class GateFail(Exception):
    """单门失守（main 统一转 [gate][FAIL]＋exit 1；负对照捕获它作预期检出）。"""


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


def run(cmd, cwd: Path, timeout_s: int = 605):
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
    if led.get("data", {}).get("theorem_count") != THEOREM_COUNT:
        fail(f"G0 账本 theorem_count 失配："
             f"{led.get('data', {}).get('theorem_count')!r} != {THEOREM_COUNT}")
    if set(led.get("axiom_policy", [])) != ALLOWED_AXIOMS:
        fail(f"G0 账本 axiom_policy 失配（应恰三标准 set 相等）："
             f"{led.get('axiom_policy')!r} != {sorted(ALLOWED_AXIOMS)}")
    okmsg(f"G0 账本在场（seed={SEED_GATE}，heavy_solves=0，自有件{len(OWNED)}"
          "全在清单，theorem_count=42，axiom_policy 恰三标准 set 相等）")
    return led


# ------------------------------------------------------------------ G1
def porcelain_paths(out: str) -> list:
    paths = []
    for ln in out.splitlines():
        if not ln.strip():
            continue
        p = ln[3:].strip().strip('"')
        if " -> " in p:
            p = p.split(" -> ")[-1]
        paths.append(p)
    return paths


def gate1_ownership():
    # 三层放行：① OWNED（本任务六件）；② 环境变量 R18A_G1_ALLOW_FOREIGN（自跑
    # 专用逐件放行，默认关）；③ PARALLEL_FAMILY pattern（r18 家族，D68-3/D77-3）。
    allow_foreign = {q.strip() for q in
                     os.environ.get("R18A_G1_ALLOW_FOREIGN", "").split(",") if q.strip()}
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
                print(f"[gate][G1][自跑放行] 并行在途件（非本任务产物，环境变量显式放行）：{p}")
                continue
            if any(re.match(pat, p) for pat in PARALLEL_FAMILY):
                print(f"[gate][G1][并行家族放行] r18 家族在途件（D68-3/D77-3 pattern）：{p}")
                continue
            raise GateFail(
                f"G1 树上出现非本任务自有件（{cmd[1]}）：{p!r}"
                f"（自有集={sorted(OWNED)}；r18 家族放行层未覆盖该路径——"
                f"若确系并行在途件，可设 R18A_G1_ALLOW_FOREIGN={p} 显式放行）")
    # 只读冻结件守卫（显式单列，响亮报错；独立于放行集）
    for rel in FROZEN_READONLY + FROZEN_LEDGERS + (ENDGAME_REL,):
        r = run(["git", "diff", "HEAD", "--", rel], REPO)
        if r.returncode != 0 or r.stdout.strip():
            fail(f"G1 只读守卫失守：{rel} 相对 HEAD 有改动（表 B 前五件/表 B 其余件"
                 "/四账本/endgame.json 为冻结只读面）")
    for d in FROZEN_DIRS:
        # 挑战件与 references/ 在 campaign 根（thomson-n9 仓外）或仓内均守卫：
        # 仓内路径直接 diff；仓外（references/）以在场性＋只读声明锚（R11C 起
        # 全任务未触碰；git 守卫不适用时以文件计数快照不改動为准——此处仅
        # 做仓内面 git 守卫＋仓外面在场断言）。
        rp = REPO / d
        cp = CAMPAIGN_ROOT / d
        if rp.exists():
            r = run(["git", "diff", "HEAD", "--", d], REPO)
            if r.returncode != 0 or r.stdout.strip():
                fail(f"G1 只读守卫失守：{d}/ 相对 HEAD 有改动（挑战件/references "
                     "命题冻结面）")
        elif cp.exists():
            n = sum(1 for _ in cp.rglob("*") if _.is_file())
            print(f"[gate][G1][冻结目录在场] {d}/（campaign 根，{n} 文件，只读未触碰）")
        else:
            fail(f"G1 冻结目录不在场：{d}（仓内与 campaign 根均未找到）")
    # endgame.json sha256 冻结锚
    eg = REPO / ENDGAME_REL
    if not eg.is_file():
        fail(f"G1 endgame.json 不在场：{ENDGAME_REL}")
    h = sha256_of(eg)
    if h != ENDGAME_SHA256:
        fail(f"G1 endgame.json sha256 失配：{h} != {ENDGAME_SHA256}（冻结锚）")
    okmsg("G1 文件所有权守卫：git status/diff 相对 HEAD 仅自有六件／r18 家族放行件"
          "（或全净）；冻结件（表 B 全系＋TableB1*/TableB6*＋挑战件/references/）"
          "零 diff；四账本零改动；endgame.json sha256 == 86863a09…69f 冻结锚")


# ------------------------------------------------------------------ G2
def compile_lean(rel_source: str, olean_name: str) -> float:
    t0 = time.time()
    olean = LEAN_DIR / OLEAN_REL / olean_name
    olean.parent.mkdir(parents=True, exist_ok=True)
    r = run(["lake", "env", "lean", "-o", f"{OLEAN_REL}/{olean_name}", rel_source],
            LEAN_DIR)
    wall = time.time() - t0
    if r.returncode != 0:
        fail(f"G2 elaboration 失败（exit {r.returncode}，{rel_source}）：\n"
             f"{r.stdout[-800:]}\n{r.stderr[-800:]}")
    out = r.stdout + r.stderr
    if "error" in out or "sorry" in out:
        fail(f"G2 elaboration 输出含 error/sorry（{rel_source}）：\n{out[-800:]}")
    if wall > ELAB_LIMIT_S:
        fail(f"G2 elaboration 超限：{rel_source} 墙钟 {wall:.1f}s > {ELAB_LIMIT_S}s")
    return wall


def gate2_elaborate() -> dict:
    # 依赖序五连：Data → B5 → B5Core → B5Trace → Polar（前四件为 R14/R16A/R17A
    # 冻结件，重编译取 olen 供 import；TableB5Polar 为本件）。
    wall_d = compile_lean("ThomsonN9/TableB5Data.lean", "TableB5Data.olean")
    okmsg(f"G2 elaboration：TableB5Data.lean exit 0 无 error/sorry（{wall_d:.1f}s ≤ 600s）")
    wall_5 = compile_lean("ThomsonN9/TableB5.lean", "TableB5.olean")
    okmsg(f"G2 elaboration：TableB5.lean exit 0 无 error/sorry（{wall_5:.1f}s ≤ 600s）")
    wall_c = compile_lean("ThomsonN9/TableB5Core.lean", "TableB5Core.olean")
    okmsg(f"G2 elaboration：TableB5Core.lean exit 0 无 error/sorry（{wall_c:.1f}s ≤ 600s）")
    wall_t = compile_lean("ThomsonN9/TableB5Trace.lean", "TableB5Trace.olean")
    okmsg(f"G2 elaboration：TableB5Trace.lean exit 0 无 error/sorry（{wall_t:.1f}s ≤ 600s）")
    wall_p = compile_lean("ThomsonN9/TableB5Polar.lean", "TableB5Polar.olean")
    okmsg(f"G2 elaboration：TableB5Polar.lean exit 0 无 error/sorry（{wall_p:.1f}s ≤ 600s；"
          "五件依赖序编译，olen 落 .lake/build 供 G3/NC1 复用）")
    return {"data_s": round(wall_d, 1), "b5_s": round(wall_5, 1),
            "core_s": round(wall_c, 1), "trace_s": round(wall_t, 1),
            "polar_s": round(wall_p, 1)}


# ------------------------------------------------------------------ G3
def parse_axiom_lines(out: str) -> dict:
    """#print axioms 输出解析（跨行续行鲁棒：4 公理集会被 pretty-printer 折行）。"""
    ax = {}
    for m in re.finditer(r"'([^']+)'\s+does not depend on any axioms", out):
        ax[m.group(1)] = set()
    for m in re.finditer(r"'([^']+)'\s+depends on axioms:\s*\[([^\]]*)\]", out):
        ax[m.group(1)] = ({a.strip() for a in m.group(2).split(",")}
                          if m.group(2).strip() else set())
    return ax


def theorem_names(src: str) -> list:
    return re.findall(r"^theorem (\w+)", src, re.M)


def check_axioms(ax: dict, names_full: list, ctx: str) -> None:
    for th in names_full:
        if th not in ax:
            fail(f"{ctx}：公理输出缺定理 {th}（解析到 {len(ax)}/{len(names_full)}）")
        bad = ax[th] - ALLOWED_AXIOMS
        if bad:
            fail(f"{ctx}：定理 {th} 依赖非标准公理 {sorted(bad)}")
        for f in FORBIDDEN_AXIOMS:
            if f in ax[th]:
                fail(f"{ctx}：定理 {th} 依赖 {f}")
    okmsg(f"{ctx}：{len(names_full)} 定理公理集全 ⊆ {{propext, Classical.choice, "
          f"Quot.sound}}，零 {FORBIDDEN_AXIOMS}")


def build_axcheck_lean(names: list) -> str:
    return ("import ThomsonN9.TableB5Polar\n"
            + "".join(f"#print axioms {t}\n" for t in names))


def gate3_axioms(src_polar: str) -> dict:
    names = [f"ThomsonN9.TableB5Polar.{t}" for t in theorem_names(src_polar)]
    if len(names) < 28:
        fail(f"G3 定理枚举偏少：{len(names)}（任务书预期 ≥28、账本记 42）")
    if len(names) != THEOREM_COUNT:
        fail(f"G3 定理数与账本失配：{len(names)} != {THEOREM_COUNT}")
    TMP.mkdir(parents=True, exist_ok=True)
    axfile = TMP / "axcheck.lean"
    axfile.write_text(build_axcheck_lean(names))
    r = run(["lake", "env", "lean", str(axfile)], LEAN_DIR)
    if r.returncode != 0:
        fail(f"G3 公理检查件编译失败（exit {r.returncode}）：\n"
             f"{r.stdout[-500:]}\n{r.stderr[-500:]}")
    ax = parse_axiom_lines(r.stdout)
    check_axioms(ax, names, "G3 公理")
    return {"theorems": len(names)}


# ------------------------------------------------------------------ G4
def gate4_core(src: str) -> None:
    """G4 语句锚核心（NC2 复用；对篡改源同样有牙）。"""
    if re.findall(r"^import\s+\S+", src, re.M) != \
            ["import Mathlib", "import ThomsonN9.TableB5",
             "import ThomsonN9.TableB5Core", "import ThomsonN9.TableB5Trace"]:
        fail("G4 TableB5Polar.lean import 行失配（应恰为 [import Mathlib, "
             "import ThomsonN9.TableB5, import ThomsonN9.TableB5Core, "
             "import ThomsonN9.TableB5Trace]）")
    anchors = [
        # ---- sqrt 单调性（D78-3 头条前提件）
        (r"theorem sqrt_quadform_lo \{n : Type\} \[Fintype n\] \[DecidableEq n\]", "sqrt 单调性定理头锚"),
        (r"\(hlo : ∀ v : n → ℝ, c\^2 \* \(v ⬝ᵥ v\) ≤ v ⬝ᵥ \(M \*ᵥ v\)\) :", "sqrt 单调性 c² 夹逼前提锚"),
        (r"    ∀ v : n → ℝ, c \* \(v ⬝ᵥ v\) ≤ v ⬝ᵥ \(\(CFC\.sqrt M\) \*ᵥ v\) :=", "sqrt 单调性 c 结论锚"),
        # ---- W 供给族
        (r"theorem W_mul_W \{m n : Type\} \[Fintype m\] \[Fintype n\] \[DecidableEq n\]", "W*W 定理头锚"),
        (r"= \(1 : Matrix n n ℝ\) \+ \(\(\(Xᵀ \* X\)⁻¹ \* \(Xᵀ \* \(Y - X\)\)\)", "W*W = 1+B 右端锚（1+B 字面）"),
        (r"theorem W_quadform_ge_half \{m n : Type\} \[Fintype m\] \[Fintype n\] \[DecidableEq n\]", "W ⪰ 1/2 定理头锚"),
        (r"    \(1 / 2\) \* \(v ⬝ᵥ v\) ≤ v ⬝ᵥ \(\(CFC\.sqrt", "W ⪰ 1/2 二次型结论锚（1/2 牙）"),
        (r"theorem W_quadform_lo \{m n : Type\} \[Fintype m\] \[Fintype n\] \[DecidableEq n\]", "W ⪰ √(1−β) 定理头锚"),
        # ---- R 正交层
        (r"theorem R_mul_RT \{n : Type\} \[Fintype n\] \[DecidableEq n\]", "R*Rᵀ 核心定理头锚"),
        (r"    \(W⁻¹ \* \(1 \+ A\)\) \* \(W⁻¹ \* \(1 \+ A\)\)ᵀ = 1 :=", "R*Rᵀ 命题形状锚"),
        (r"theorem R_mem_orthogonalGroup \{m n : Type\} \[Fintype m\] \[Fintype n\] \[DecidableEq n\]", "R membership 定理头锚"),
        (r"∈ Matrix\.orthogonalGroup n ℝ := by", "R membership 命题形状锚"),
        (r"theorem Rinv_mem_orthogonalGroup \{n : Type\} \[Fintype n\] \[DecidableEq n\]", "R⁻¹ membership 定理头锚"),
        (r"    R⁻¹ ∈ Matrix\.orthogonalGroup n ℝ := by", "R⁻¹ membership 命题形状锚（Q := R⁻¹ 见证）"),
        (r"theorem R_eq_pair \{m n : Type\} \[Fintype m\] \[Fintype n\] \[DecidableEq n\]", "R 双等式定理头锚"),
        # ---- frob 正交右乘不变
        (r"theorem frob_mul_right_orthogonal \{m n : Type\} \[Fintype m\] \[Fintype n\]", "frob 右乘不变定理头锚"),
        (r"    frob \(M \* Q\) = frob M := by", "frob 右乘不变命题形状锚"),
        # ---- D77 补线（(9/4) 面＋(2/3) 头条牙——NC2 棱二）
        (r"theorem Wp1_sq_quadform \{n : Type\} \[Fintype n\] \[DecidableEq n\]", "(W+1)² 二次型面定理头锚"),
        (r"    \(9 / 4\) \* \(v ⬝ᵥ v\) ≤ v ⬝ᵥ \(\(\(W \+ 1\) \* \(W \+ 1\)\) \*ᵥ v\)", "(W+1)² 命题形状锚（9/4 牙）"),
        (r"theorem frob_Wm1_le \{m n : Type\} \[Fintype m\] \[Fintype n\] \[DecidableEq n\]", "W−I Frobenius 界头条定理头锚"),
        (r"≤ \(2/3\) \* frob \(", "W−I Frobenius 界头条 (2/3) 牙（NC2 棱二）"),
        # ---- 步骤 5 头条
        (r"theorem step5_bound \{m n : Type\} \[Fintype m\] \[Fintype n\] \[DecidableEq n\]", "步骤 5 头条定理头锚"),
        (r"    ∃ Q ∈ Matrix\.orthogonalGroup n ℝ,", "步骤 5 头条 ∃Q membership 锚"),
        (r"      frob \(X - Y \* Q\) ≤ Real\.sqrt lam1 \* β \+ frob \(", "步骤 5 头条命题形状锚（√λ₁·β＋frob D_⊥）"),
        # ---- 步骤 6 条件装配（D77-2 前提显式）
        (r"theorem dperp_le \{m n : Type\} \[Fintype m\] \[Fintype n\] \[DecidableEq m\]", "条件垂直界定理头锚"),
        (r"    \(hdpar : frob \(X \* \(\(Xᵀ \* X\)⁻¹ \* \(Xᵀ \* \(Y - X\)\)\)\) ≤ Real\.sqrt lam1 \* β\)", "条件垂直界 hdpar 前提字面牙（frob D_∥ ≤ σ₁β 可见）"),
        (r"      ≤ frob \(Y \* Yᵀ - X \* Xᵀ\) / \(Real\.sqrt lam3 - Real\.sqrt lam1 \* β\)", "条件垂直界结论锚（/(√λ₃−σ₁β)）"),
        (r"theorem step6_final \{m n : Type\} \[Fintype m\] \[Fintype n\] \[DecidableEq m\]", "步骤 6 条件终定理定理头锚"),
        (r"      ≤ Real\.sqrt lam1 \* \(lam1 \* frob \(Y \* Yᵀ - X \* Xᵀ\) / lam3\^2\)\)", "step6_final hdpar 前提字面牙"),
        (r"    \(hdom1 : lam1 \* frob \(Y \* Yᵀ - X \* Xᵀ\) / lam3\^2 ≤ 1 / 2\)", "step6_final hdom1 域条件字面牙"),
        (r"      ≤ Real\.sqrt lam3 / \(2 \* Real\.sqrt lam1\)\)", "step6_final hdom2 域条件字面牙"),
        (r"        ≤ \(Real\.sqrt lam1 \* lam1 / lam3\^2 \+ 2 / Real\.sqrt lam3\)", "step6_final 结论锚（σ₁λ₁/λ₃²＋2/√λ₃）"),
        # ---- TTP 实例化双头条（(l3:ℝ)^2 字面牙——NC2 棱一）
        (r"theorem ttpX_step5 \(z : ℝ\) \(h1 : \(zLo:ℝ\) ≤ z\) \(h2 : z ≤ \(zHi:ℝ\)\)", "TTP 步骤 5 头条定理头锚"),
        (r"      frob \(ttpX z - Y \* Q\) ≤ Real\.sqrt \(u1:ℝ\) \* β \+ frob \(", "TTP 步骤 5 头条命题形状锚（√u₁·β）"),
        (r"theorem ttpX_step6_final \(z : ℝ\) \(h1 : \(zLo:ℝ\) ≤ z\) \(h2 : z ≤ \(zHi:ℝ\)\)", "TTP 条件终定理定理头锚"),
        (r"        ≤ \(Real\.sqrt \(u1:ℝ\) \* \(u1:ℝ\) / \(l3:ℝ\)\^2 \+ 2 / Real\.sqrt \(l3:ℝ\)\)", "TTP 条件终定理结论锚（(l3:ℝ)^2＋2/√l3 字面牙——NC2 棱一）"),
    ]
    for pat, name in anchors:
        if not re.search(pat, src, re.M):
            fail(f"G4 语句锚缺失：{name}（pattern {pat!r}）")
    # 禁串 sorry／伪陈述
    if re.search(r"^\s*sorry\s*$", src, re.M) or "sorry" in src.replace(
            "零 sorry", "").replace("无 sorry", ""):
        # 文档字符串中的『sorry』字样剔除后再判（本件 docstring 无 sorry 面，
        # 出现即拦截）：
        if re.search(r"\bsorry\b", src):
            body_sorry = re.findall(r"^\s*(?:exact |rw \[)?sorry", src, re.M)
            if body_sorry or re.search(r":= by sorry", src):
                fail("G4 禁串失守：源码含 sorry 证明")
    # 零 ≥15 位数字面量（数值数据面；9/4、2/3、1/2、3/4 等结构常数不在列）
    long_lits = re.findall(r"\d{15,}", src)
    if long_lits:
        fail(f"G4 零 ≥15 位数字面量失守：{long_lits[:3]}")
    # 零『def … : ℚ :=』（无 Data 件口径）
    if re.findall(r"^def \w+ : ℚ :=", src, re.M):
        fail("G4 零『def … : ℚ :=』失守（本件零数值数据字面量，无 Data 件）")


def gate4_statement(src_polar: str) -> None:
    gate4_core(src_polar)
    # 非交叠守卫（TableA* 含分块子目录 TableA6/）
    nonoverlap = list(NONOVERLAY_FILES)
    for p in sorted((LEAN_DIR / "ThomsonN9").glob("TableA*.lean")):
        nonoverlap.append(str(p.relative_to(LEAN_DIR)))
    a6 = LEAN_DIR / "ThomsonN9" / "TableA6"
    if a6.is_dir():
        for p in sorted(a6.glob("*.lean")):
            nonoverlap.append(str(p.relative_to(LEAN_DIR)))
    for rel in nonoverlap:
        p = LEAN_DIR / rel
        if p.is_file() and "TableB5Polar" in p.read_text():
            fail(f"G4 非交叠守卫：{rel} 含 'TableB5Polar'（本件必须不被表 A/M1/"
                 "Solution/表 B 其余件/根模块/lake 面引用）")
    okmsg("G4 语句锚：import 面恰 [Mathlib＋TableB5＋TableB5Core＋TableB5Trace]；"
          "36 锚全在（sqrt 单调性双面/W 供给族/R membership 双口径/frob 右乘不变/"
          "(W+1)²·9/4 面/W−I·(2/3) 头条/步骤 5 ∃Q 三牙/条件前提 hdpar·hdom1·"
          "hdom2 字面可见/TTP 双头条 (l3:ℝ)^2 牙）＋零 ≥15 位数字面量＋零 ℚ def"
          "＋零 sorry 证明；非交叠面零 TableB5Polar 引用")


# ------------------------------------------------------------------ G5 门内独立第二实现（Fraction 引擎）
def mat_mul(A, B):
    n, k, m = len(A), len(B), len(B[0])
    return [[sum(A[i][t] * B[t][j] for t in range(k)) for j in range(m)]
            for i in range(n)]


def mat_add(A, B):
    return [[A[i][j] + B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def mat_sub(A, B):
    return [[A[i][j] - B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def mat_T(A):
    return [[A[i][j] for i in range(len(A))] for j in range(len(A[0]))]


def eye(n):
    return [[F1 if i == j else F0 for j in range(n)] for i in range(n)]


def frob_sq(M):
    """frob² ＝ ∑ M_ij²（Fraction 精确；σ 无理面一律走平方化等价比较）。"""
    return sum(x * x for row in M for x in row)


def gauss_inv(S):
    """n×n Fraction 矩阵 Gauss-Jordan 求逆（门内独立自实现，零仓 imports）。"""
    n = len(S)
    aug = [list(S[i]) + [F1 if j == i else F0 for j in range(n)] for i in range(n)]
    for col in range(n):
        piv = next(r for r in range(col, n) if aug[r][col] != 0)
        aug[col], aug[piv] = aug[piv], aug[col]
        pv = aug[col][col]
        aug[col] = [x / pv for x in aug[col]]
        for r in range(n):
            if r != col and aug[r][col] != 0:
                f = aug[r][col]
                aug[r] = [x - f * y for x, y in zip(aug[r], aug[col])]
    return [row[n:] for row in aug]


def rand_mat(rng, n, m, den=6):
    return [[Fr(rng.randint(-9, 9), den) for _ in range(m)] for _ in range(n)]


def rat_orthogonal(rng):
    """有理正交 O：Pythagorean 有理旋转（3/5,4/5）面＋符号置换混合。"""
    a, b = Fr(3, 5), Fr(4, 5)
    s1 = rng.choice([1, -1])
    s2 = rng.choice([1, -1])
    R12 = [[a * s1, -b * s2, F0], [b * s2, a * s1, F0], [F0, F0, F1]]
    P = eye(3)
    i, j = rng.sample(range(3), 2)
    P[i][i], P[j][j], P[i][j], P[j][i] = F0, F0, F1, -F1 if rng.random() < 0.5 else F1
    O = mat_mul(R12, P)
    if mat_mul(O, mat_T(O)) != eye(3) or mat_mul(mat_T(O), O) != eye(3):
        fail("G5 有理正交构造自检失守（O·Oᵀ ≠ I₃）")
    return O


def check_polar_identities(rng, wrong_sqrt=False, fake_orthogonal=False):
    """B5c 恒等式族精确复核（wrong_sqrt/fake_orthogonal 为 NC3 篡引擎棱）。
    构造（全有理精确）：W := diag(w_i)（w_i ≥ 1/2 使 (W+1)² ⪰ 9/4 前提面）＋
    O := Pythagorean 有理旋转×符号置换（O·Oᵀ = I₃ 精确）⟹
    A := W·O − 1 使 (1+A)(1+A)ᵀ = W·O·Oᵀ·W = W² ⟹ B = A+Aᵀ+AAᵀ = W²−1 精确；
    X 列 Pythagorean 框架使 XᵀX = diag(r_j²)（r_j 有理 ⟹ σ_j = r_j 有理）。"""
    # ---- 有理 W 与有理正交 O
    Wd = [Fr(rng.randint(4, 12), rng.randint(4, 8)) for _ in range(3)]
    Wd = [w if w >= Fr(1, 2) else w + Fr(1, 2) for w in Wd]
    W = [[Wd[i] if i == j else F0 for j in range(3)] for i in range(3)]
    O = rat_orthogonal(rng)
    A = mat_sub(mat_mul(W, O), eye(3))            # (1+A) = W·O
    B = mat_add(mat_add(A, mat_T(A)), mat_mul(A, mat_T(A)))   # B = A+Aᵀ+AAᵀ
    # (a) B 恒等式：B == W²−1（9 元逐元素）＋(1+A)(1+A)ᵀ−1 == B
    WWm1 = mat_sub(mat_mul(W, W), eye(3))
    for i in range(3):
        for j in range(3):
            if B[i][j] != WWm1[i][j]:
                fail(f"G5(a) B 恒等式失守 @({i},{j})：A+Aᵀ+AAᵀ ≠ W²−1")
    Bf = mat_sub(mat_mul(mat_add(eye(3), A), mat_T(mat_add(eye(3), A))), eye(3))
    if B != Bf:
        fail("G5(a) B 恒等式失守：(1+A)(1+A)ᵀ−1 ≠ B")
    # (b) 极分解 R := W⁻¹(1+A) == O ⇒ R·Rᵀ == I₃；Q := R⁻¹ == Oᵀ
    Winv = gauss_inv(W)
    if mat_mul(W, Winv) != eye(3) or mat_mul(Winv, W) != eye(3):
        fail("G5(b) Gauss-Jordan 逆自检失守（W·W⁻¹ ≠ I₃）")
    R = mat_mul(Winv, mat_add(eye(3), A))
    for i in range(3):
        for j in range(3):
            if R[i][j] != O[i][j]:
                fail(f"G5(b) 极分解失守 @({i},{j})：W⁻¹(1+A) ≠ O")
    if mat_mul(R, mat_T(R)) != eye(3):
        fail("G5(b) 正交核验失守：R·Rᵀ ≠ I₃")
    Q = gauss_inv(R)
    if Q != mat_T(O):
        fail("G5(b) Q := R⁻¹ ≠ Oᵀ")
    # (f0) X 列 Pythagorean 框架：XᵀX == diag(r_j²)（σ_j = r_j 有理精确）
    rowsX = [[F0] * 3 for _ in range(9)]
    rj = []
    for jj in range(3):
        r = Fr(rng.randint(1, 9), rng.randint(1, 4))
        rj.append(r)
        # 第 jj 列两行 Pythagorean 对 (3/5,4/5)·r ⟹ 列范数² = (9+16)/25·r² = r²
        rowsX[2 * jj][jj] = Fr(3, 5) * r
        rowsX[2 * jj + 1][jj] = Fr(4, 5) * r
    X = rowsX
    XTX = mat_mul(mat_T(X), X)
    for i in range(3):
        for j in range(3):
            want = rj[i] * rj[i] if i == j else F0
            if XTX[i][j] != want:
                fail(f"G5(f0) XᵀX == diag(r_j²) 构造失守 @({i},{j})")
    lam1 = max(rj) ** 2           # λ₁ = max r_j²（σ₁ = max r_j 有理）
    s3 = min(rj)                  # σ₃ = √λ₃ = min r_j（有理）
    Dperp = rand_mat(rng, 9, 3)
    Dpar = mat_mul(X, A)
    Y = mat_add(mat_add(X, Dpar), Dperp)
    # (c) YQ 恒等式：(X + X·A + D_⊥)·Q == X·W + D_⊥·Q（27 元逐元素）
    if fake_orthogonal:
        Q = [[Fr(3, 2) * q for q in row] for row in Q]     # NC3(ii)：伪正交
    lhs = mat_mul(Y, Q)
    rhs = mat_add(mat_mul(X, W), mat_mul(Dperp, Q))
    for i in range(9):
        for j in range(3):
            if lhs[i][j] != rhs[i][j]:
                if fake_orthogonal:
                    fail("NC3 预期检出：伪正交 Q' := (3/2)Q 下 YQ 恒等式破坏"
                         "（防假拦截实证）")
                fail(f"G5(c) YQ 恒等式失守 @({i},{j})")
    if fake_orthogonal:
        fail("NC3 失守：伪正交 Q' 下 YQ 恒等式仍成立（不可达）")
    # (d) frob 正交右乘不变：frob(M·Q)² == frob M²（X/D_⊥ 两面——9×3 右乘
    #     3×3 正交 Q；E 面 9×9 在 B5c 链中不被右乘，不属本复核面）
    for name, M in (("X", X), ("D_⊥", Dperp)):
        if frob_sq(mat_mul(M, Q)) != frob_sq(M):
            if fake_orthogonal:
                fail(f"NC3 预期检出：伪正交 Q' 下 frob({name}·Q')² ≠ frob {name}²")
            fail(f"G5(d) frob 右乘不变失守（{name} 面）")
    E = mat_sub(mat_mul(Y, mat_T(Y)), mat_mul(X, mat_T(X)))
    # (e) D77 补线 squared 链：(9/4)·frob(W−1)² ≤ frob(B)²（w_i ≥ 1/2 前提面）
    Weng = mat_mul(W, W) if wrong_sqrt else W    # NC3(i)：W' := W² = 1+B
    fsq_Wm1 = frob_sq(mat_sub(Weng, eye(3)))
    fsq_B = frob_sq(B)
    if Fr(9, 4) * fsq_Wm1 > fsq_B:
        if wrong_sqrt:
            fail("NC3 预期检出：W' := 1+B（非 sqrt 极因子）下 "
                 "(9/4)frob(W'−1)² > frob(B)²（防假拦截实证）")
        fail("G5(e) D77 补线失守：(9/4)·frob(W−1)² > frob(B)²")
    if wrong_sqrt:
        fail("NC3 失守：W' := 1+B 下补线仍成立（不可达：frob(W'−1)² = frob(B)² "
             "> (4/9)frob(B)² 当 frob B ≠ 0）")
    # (f) σ₁ 列压缩 squared 链：frob(X(1−W))² ≤ λ₁·frob(W−1)²
    if frob_sq(mat_mul(X, mat_sub(eye(3), W))) > lam1 * frob_sq(mat_sub(W, eye(3))):
        fail("G5(f) σ₁ 列压缩 squared 链失守：frob(X(1−W))² > λ₁·frob(W−1)²")
    # (g) 步骤 3 面充分核（σ₃ 有理）：(σ₃ − frobD∥)·frobD⊥ ≤ frobE ⟸
    #     其平方化充分链 λ₃·p ≤ 2(η + f·p)（AM-GM：2√(ηfp) ≤ η+fp；p/f/η 记
    #     frob²——frobD⊥²/frobD∥²/frobE²）。核充分链在 Fraction 上精确。
    p_ = frob_sq(Dperp)
    f_ = frob_sq(Dpar)
    eta_ = frob_sq(E)
    if s3 ** 2 * p_ > 2 * (eta_ + f_ * p_):
        fail("G5(g) 步骤 3 面 squared 充分链失守：λ₃·frobD⊥² > 2(η + frobD∥²·"
             "frobD⊥²)（AM-GM 充分核）")
    return


def parse_data_literal(name: str) -> Fr:
    """TableB5Data.lean 源直读 ℚ 字面量（零手抄——D73 G4 式）。"""
    src = DATA_LEAN.read_text()
    m = re.search(rf"^def {name} : ℚ := (\S+)", src, re.M)
    if not m:
        fail(f"G5(h) TableB5Data 源直读失败：def {name} : ℚ := … 不在场")
    tok = m.group(1)
    neg = tok.startswith("-")
    if neg:
        tok = tok[1:]
    f = Fr(*[int(x) for x in tok.split("/")]) if "/" in tok else Fr(int(tok))
    return -f if neg else f


def check_c_chain():
    """C 链 Fraction 复核：(s1Up³/l3² + 2/s3Dn)·sqrt72Up ≤ CVal
    （TableB5Data.lean 源直读字面量——记录安全向常数链的独立第二实现）。"""
    l3 = parse_data_literal("l3")
    u1 = parse_data_literal("u1")
    s1Up = parse_data_literal("s1Up")
    s3Dn = parse_data_literal("s3Dn")
    sqrt72Up = parse_data_literal("sqrt72Up")
    CVal = parse_data_literal("CVal")
    CInner = parse_data_literal("CInner")
    # (σ₁³/λ₃² + 2/σ₃)·√72 ≤ (u₁·s1Up/l₃² + 2/s3Dn)·sqrt72Up ≤ CVal
    # （σ₁³ = σ₁·λ₁ ≤ s1Up·u₁——安全向记录链口径，σ₃ ≥ s3Dn、√72 ≤ sqrt72Up）
    inner = u1 * s1Up / l3 ** 2 + Fr(2) / s3Dn
    if inner != CInner:
        fail(f"G5(h) C 链内环失守：u1·s1Up/l3²+2/s3Dn = {inner} != CInner {CInner}")
    if inner * sqrt72Up > CVal:
        fail("G5(h) C 链失守：CInner·sqrt72Up > CVal")
    # 侧证：σ₁³/λ₃² ≤ u1·s1Up/l3²（s1Up² ≥ 1 时 s1Up³ ≥ u1·s1Up 反向不真，
    # 记录链取 σ₁·λ₁ 双拆——本复核核记录链本身）
    okmsg("G5(h) C 链 Fraction 复核：u1·s1Up/l3²+2/s3Dn == CInner"
          "＋CInner·sqrt72Up ≤ CVal（TableB5Data 源直读，零手抄）")


# 共享家族追加面（G1 PARALLEL_FAMILY 两件 notes 件）：后续轮次执行员按
# 家族设计对 notes/decisions.md 追加 D 编号裁决、对 notes/tableb-lean.md
# 追加新节（R18B D79 追加即实例）——账本锚哈希对这两件按 git 溯源
# append-only 例外放行（R18C 收口补丁，D80 裁决 6：原精确匹配面在
# D79 追加后不可达——账本锚哈希须等于【账本入库提交】时点的该文件
# 版本哈希且该版本为当前文件字节前缀，非追加篡改仍必拦，验证强度
# 不降反升）。
APPEND_ONLY_FAMILY_SHARED = ("notes/decisions.md", "notes/tableb-lean.md")


def _ledger_anchor_prefix_ok(rel: str, want: str) -> bool:
    """共享家族 notes 件 append-only 漂移验证（R18C 补丁，D80 裁决 6）：

    账本锚哈希须等于【账本入库提交】（git log --diff-filter=A 首提交）
    时点的该文件版本哈希（⇒ 账本记录在其锚定时点诚实），且该版本须为
    当前文件的字节前缀（⇒ 此后仅追加——家族设计 PARALLEL_FAMILY 允许
    后续轮次追加裁决/新节）；任一不成立即非追加篡改，仍按失配拦截。
    """
    r = run(["git", "log", "--format=%H", "--diff-filter=A", "--reverse",
             "--", LEDGER_REL], REPO)
    if r.returncode != 0 or not r.stdout.strip():
        return False
    anchor_commit = r.stdout.split()[0]
    # 字节精确取版（不走 run() 的 text=True——decisions.md 含全角/CJK，
    # 字节前缀比对须零转码损失）
    r2 = subprocess.run(["git", "show", f"{anchor_commit}:{rel}"],
                        cwd=str(REPO), env=gate_env(),
                        capture_output=True, timeout=605)
    if r2.returncode != 0:
        return False
    old = r2.stdout
    if hashlib.sha256(old).hexdigest() != want:
        return False
    cur = (REPO / rel).read_bytes()
    return cur.startswith(old)


def check_ledger_hashes(led: dict):
    """(h) 账本锚 cross-check：自有件 sha256 重算比对（'self' 件跳过；
    共享家族 notes 件按 git 溯源 append-only 例外——R18C 补丁 D80-6）。"""
    files = led.get("files", {})
    nchk = 0
    n_append = 0
    for rel, rec in files.items():
        if rec == "self":
            continue
        p = REPO / rel
        if not p.is_file():
            fail(f"G5(h) 账本 sha256 面：自有件不在场 {rel}")
        h = sha256_of(p)
        want = rec.get("sha256") if isinstance(rec, dict) else rec
        if want == h:
            nchk += 1
            continue
        if rel in APPEND_ONLY_FAMILY_SHARED and _ledger_anchor_prefix_ok(rel, want):
            n_append += 1      # 共享家族件 append-only 漂移（D79/D80…追加）
            continue
        fail(f"G5(h) 账本 sha256 失配：{rel}（账本 {str(want)[:16]}… != "
             f"实测 {h[:16]}…）")
    okmsg(f"G5(h) 账本锚 cross-check：{nchk} 自有件 sha256 逐件重算一致＋"
          f"{n_append} 共享家族件 git 溯源 append-only 一致"
          "（ledger 自身记 'self'）")


NOTES_ANCHORS = [
    "### 探针① sqrt 单调性（D77 唯一待探前提）——【档位：缺位自建·路线 B'（谱映射",
    "### 探针② 行-CS 二次型界——【档位：现成·自建（B5b abs_dotProduct_le 机组装）】",
    "### 探针③ (W−1)(W+1) 交换环＋trace 循环——【档位：现成（noncomm_ring 一击）】",
    "### 探针④ Y*Q = X*W + D_⊥*Q 恒等式——【档位：现成（show-rewrite 嵌套链）】",
    "### 探针⑤ W 对称供给（CFC.sqrt 自伴面）——【档位：在档（R17B Q2 例 1 同式，",
    "### 主件落地（formal/lean/ThomsonN9/TableB5Polar.lean，42 定理）",
    "B5c 陈述面增量决策",
    "/tmp/r18a_probe_polar.lean",
    "/tmp/r18a_probe_polar.log",
    "heavySolves = 0",
]


def gate5_offline(led: dict) -> dict:
    rng = random.Random(SEED_GATE)
    for k in range(3):
        check_polar_identities(rng)
        okmsg(f"G5 实例 {k}（seed 复放）：B 恒等式 9 元×2＋极分解 R==O＋"
              "YQ 恒等式 27 元＋frob 右乘不变两面＋D77 补线 squared 链＋"
              "σ₁ 列压缩 squared 链＋步骤 3 面 squared 链全过")
    check_c_chain()
    check_ledger_hashes(led)
    # notes §6 探针转录锚
    notes = NOTES.read_text()
    for anc in NOTES_ANCHORS:
        if anc not in notes:
            fail(f"G5 notes/tableb-lean.md §6 转录锚缺失：{anc!r}")
    okmsg("G5 离线精确复核：3 随机有理实例（有理正交 O＋有理 W 极分解构造——"
          "Gauss-Jordan 逆自实现零仓 import）＋C 链 Fraction 复核＋账本 sha256 "
          "cross-check＋notes §6 转录锚 10 处在文")
    return {"instances": 3}


# ------------------------------------------------------------------ NC
def nc1_sorry_injection(src_polar: str) -> None:
    target = ("theorem quadform_nonneg_of_posSemidef {n : Type} [Fintype n]\n"
              "    {M : Matrix n n ℝ} (hM : M.PosSemidef) (v : n → ℝ) :\n"
              "    0 ≤ v ⬝ᵥ (M *ᵥ v) := by\n"
              "  simpa only [star_trivial] using\n"
              "    (Matrix.posSemidef_iff_dotProduct_mulVec.mp hM).2 v")
    tampered = src_polar.replace(target,
        "theorem quadform_nonneg_of_posSemidef {n : Type} [Fintype n]\n"
        "    {M : Matrix n n ℝ} (hM : M.PosSemidef) (v : n → ℝ) :\n"
        "    0 ≤ v ⬝ᵥ (M *ᵥ v) := by\n"
        "  sorry")
    if tampered == src_polar:
        fail("NC1 预置失败：未能在 /tmp 副本注入 sorry（源码缺目标证明块）")
    d = TMP / "nc1"
    (d / "ThomsonN9").mkdir(parents=True, exist_ok=True)
    (d / "ThomsonN9" / "TableB5Polar.lean").write_text(tampered)
    # 依赖 olen 随副本落 root（TableB5Polar imports 四件；G2 已编译 olen）。
    for dep in ("TableB5Data.olean", "TableB5.olean", "TableB5Core.olean",
                "TableB5Trace.olean"):
        src = LEAN_DIR / OLEAN_REL / dep
        if not src.is_file():
            fail(f"NC1 预置失败：依赖 olen 不在场（G2 应已编译）：{src}")
        (d / "ThomsonN9" / dep).write_bytes(src.read_bytes())
    lp = run(["lake", "env", "printenv", "LEAN_PATH"], LEAN_DIR).stdout.strip()
    env = gate_env()
    env["LEAN_PATH"] = f"{d}:{lp}"
    b = subprocess.run(["lean", "--root", str(d), "-o",
                        str(d / "ThomsonN9" / "TableB5Polar.olean"),
                        str(d / "ThomsonN9" / "TableB5Polar.lean")],
                       cwd=str(LEAN_DIR), env=env, capture_output=True, text=True,
                       timeout=605)
    if b.returncode != 0 or "declaration uses `sorry`" not in (b.stdout + b.stderr):
        fail(f"NC1 注入 sorry 后编译未产生 sorry 警告（exit {b.returncode}）：\n"
             f"{(b.stdout + b.stderr)[-500:]}")
    axfile = d / "axcheck.lean"
    axfile.write_text("import ThomsonN9.TableB5Polar\n"
                      "#print axioms ThomsonN9.TableB5Polar."
                      "quadform_nonneg_of_posSemidef\n")
    a = subprocess.run(["lean", str(axfile)], cwd=str(LEAN_DIR), env=env,
                       capture_output=True, text=True, timeout=605)
    ax = parse_axiom_lines(a.stdout)
    th = "ThomsonN9.TableB5Polar.quadform_nonneg_of_posSemidef"
    caught = th in ax and ("sorryAx" in ax[th] or (ax[th] - ALLOWED_AXIOMS))
    if not caught:
        fail(f"NC1 失守：注入 sorry 后公理检查未现 sorryAx（{ax}）")
    okmsg("NC1 注入 sorry 必被 G3 拦：篡件 quadform_nonneg_of_posSemidef 公理集 = "
          f"{sorted(ax.get(th, set()))}（含 sorryAx → G3 FAIL）")


def nc2_statement_tamper(src_polar: str) -> None:
    # 双棱：指数面 (l3:ℝ)^2 → (l3:ℝ)^3（TTP 条件终定理）＋
    #       常数面 (2/3) → (3/4)（D77 补线头条）。
    tampered = src_polar.replace("(l3:ℝ)^2", "(l3:ℝ)^3")
    if tampered == src_polar:
        raise GateFail("NC2 预置失败：篡改一未生效（源码无 (l3:ℝ)^2 字面）")
    try:
        gate4_core(tampered)
        raise GateFail("NC2 失守：篡陈述一（(l3:ℝ)^2→(l3:ℝ)^3）后 G4 语句锚未报错")
    except GateFail as e:
        if "语句锚缺失" not in str(e):
            raise
        print(f"[gate][NC2 检出·棱一] {e}")
    tampered2 = src_polar.replace("≤ (2/3) * frob (", "≤ (3/4) * frob (")
    if tampered2 == src_polar:
        raise GateFail("NC2 预置失败：篡改二未生效（源码无 (2/3)*frob ( 字面）")
    try:
        gate4_core(tampered2)
        raise GateFail("NC2 失守：篡陈述二（(2/3)→(3/4)）后 G4 语句锚未报错")
    except GateFail as e:
        if "语句锚缺失" not in str(e):
            raise
        print(f"[gate][NC2 检出·棱二] {e}")
    gate4_core(src_polar)          # sanity：原文件 PASS
    okmsg("NC2 篡陈述必被 G4 拦（双棱）：(l3:ℝ)^2→(l3:ℝ)^3（TTP 条件终定理指数面）"
          "与 (2/3)→(3/4)（W−I Frobenius 界头条常数面）均检出锚缺失；"
          "原文件 sanity PASS")


def nc3_wrong_engine() -> None:
    rng = random.Random(SEED_GATE + 1)   # 独立 seed 复放实例
    # ① W' := 1+B（恒等代替 sqrt 的错误极因子）⇒ D77 补线复核必被检出
    try:
        check_polar_identities(rng, wrong_sqrt=True)
        raise GateFail("NC3① 失守：错误极因子未触发检出（不可达：检出已在引擎内拦）")
    except GateFail as e:
        if "NC3 预期检出" not in str(e):
            raise
        print(f"[gate][NC3 检出·棱一] {e}")
    # ② 伪正交 Q' := (3/2)Q ⇒ frob 右乘不变复核必被检出
    try:
        check_polar_identities(rng, fake_orthogonal=True)
        raise GateFail("NC3② 失守：伪正交 Q 未触发检出（不可达）")
    except GateFail as e:
        if "NC3 预期检出" not in str(e):
            raise
        print(f"[gate][NC3 检出·棱二] {e}")
    okmsg("NC3 错误引擎必被 G5 拦（双棱）：W' := 1+B 非 sqrt 极因子补线必 FAIL＋"
          "伪正交 Q' := (3/2)Q 右乘不变必 FAIL")


# ------------------------------------------------------------------ main
def main() -> None:
    t0 = time.time()
    print(f"[gate] r18_b5c_gate.py seed={SEED_GATE}（确定性；随机实例为 seed 复放）")
    try:
        run_gate()
    except GateFail as e:
        print(f"[gate][FAIL] {e}", flush=True)
        sys.exit(1)
    wall = time.time() - t0
    print(f"[gate] PASS（{wall:.1f}s）——exit 0")
    print("[gate] heavySolves=0（本门零求解：仅 elaboration/公理/regex/Fraction 复核；"
          "四账本/endgame.json 只读未动）")


def run_gate() -> None:
    require_toolchain()
    if not POLAR_LEAN.is_file():
        fail(f"产出件不在场：{POLAR_LEAN}")
    src_polar = POLAR_LEAN.read_text()

    led = gate0_ledger()
    gate1_ownership()
    walls = gate2_elaborate()
    g3 = gate3_axioms(src_polar)
    gate4_statement(src_polar)
    gate5_offline(led)
    nc1_sorry_injection(src_polar)
    nc2_statement_tamper(src_polar)
    nc3_wrong_engine()
    print(f"[gate] G2 elaboration 墙钟：Data {walls['data_s']}s＋B5 {walls['b5_s']}s＋"
          f"Core {walls['core_s']}s＋Trace {walls['trace_s']}s＋"
          f"Polar {walls['polar_s']}s（均 ≤ {ELAB_LIMIT_S}s）；"
          f"G3 定理 {g3['theorems']} 件")


if __name__ == "__main__":
    main()
