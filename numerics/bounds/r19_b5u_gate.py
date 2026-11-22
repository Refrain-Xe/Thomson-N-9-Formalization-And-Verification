#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r19_b5u_gate.py — R19A 表 B 第七件 B5c 步骤 6 无条件化（D82 裁决 1/2/3
口径：路线 B 全域 ½-Hölder 档＋路线 A 窄域线性档合并单件）验收门
（G0–G5＋负对照 NC1/NC2/NC3）.

任务书口径（r19a-b5u-uncond-lean，campaign dwfrun-f9904baf 第 14 轮）：
B5c 步骤 6 无条件化＝新件 formal/lean/ThomsonN9/TableB5Uncond.lean（24 定理，
import Mathlib＋TableB5＋TableB5Core＋TableB5Trace＋TableB5Polar，零数值数据
字面量故无 Data 件——常数一律以 TableB5Data 既有 def 表达）——层 1 共享面
（块恒等式双例 E(1−P₀)=Y·D_⊥ᵀ／(1−P₀)E(1−P₀)=D_⊥D_⊥ᵀ〔R18B 探针 1 源转录
＋P₀ 桥在库六面免费复用〕＋op(1−P₀)≤1 二次型面＋trace-CS 面＋½-Hölder 面
t² ≤ √(Fintype.card m)·η）＋层 2 路线 B 头条（无条件·全域：前提仅 λ 夹逼＋
β := λ₁η/λ₃² ≤ 1/2〔无 hdpar〕，结论 ∃ Q, frob (X−Y*Q) ≤ √λ₁·β + √(3η)；
C_B·√δ 推论 β≤1/2 由 TableB5.delta_max_valid 内部导出）＋层 3 路线 A 链
（A2 frob 对称面／A4 行-CS／A6 算子面／A7 组装＋逆向三角／A8 ‖Y·D_⊥ᵀ‖≤η／
A9 λ₃(Y) 压缩／A10 闭环消歧〔域 η ≤ λ₃/24，c_lo := √(λ₃/2) 包络口径〕／
A11 线性头条 (√λ₁λ₁/λ₃² + 2√2/√λ₃)·η〔无 hdpar〕）＋层 4 TTP 实例化双头条
（(l3:ℝ)/(u1:ℝ) 字面接线）。R18A 条件层（TableB5Polar step6_final 三前提）
保留为中间件不动（D78-4 可回滚点）。本门全确定性（随机实例 seed 20261019
复放；PATH 自动前置 ~/.elan/bin）；CWD 无关（全部路径自 __file__ 推导）。
heavySolves=0（本门零求解：仅 elaboration/公理/regex/Fraction 复核；四账本/
endgame.json 只读＋sha256 冻结）。

检查面（对应任务书 G0–G5＋NC1/NC2/NC3）：
  G0 账本在场与受控字段（seed == 20261019、heavy_solves == 0、自有六件在清单、
     data.theorem_count == 24、axiom_policy 恰三标准列表形态 set 相等——
     r16a/r17/r18 新形态）。
  G1 文件所有权守卫：git status --porcelain 与 git diff HEAD --name-only 的全部
     改动路径 ⊆ 本任务自有六件（＋环境变量 R19A_G1_ALLOW_FOREIGN 自跑逐件放行
     〔默认关〕＋r19 家族放行层〔r19 pattern＋tableb-lean.md＋decisions.md＋
     endgame_gate.py＋GAP-REPORT/PROGRESS——D82 裁决 5〕）；只读冻结件显式
     git diff 守卫（TableB5/TableB5Data/TableB5Core/TableB5Trace/**TableB5Polar
     sha256 == d8c58f7d…8516**/TableB1*/TableB6*＋挑战件目录 Comparator
     Challenges/＋references/）；四账本＋endgame.json sha256 冻结锚
     （86863a09…69f）。
  G2 逐文件 elaboration：依赖序六连 Data → B5 → Core → Trace → Polar →
     Uncond（均 CWD=formal/lean），各 exit 0、输出无 error／无 sorry、
     墙钟 ≤ 600 s/文件（D52 裁决 4 / D64-5；外层编译型门 1200s 文档化例外
     D80-1 不适用于单文件限）。
  G3 公理：检查件 import ThomsonN9.TableB5Uncond＋对件内全部 24 theorem
     （regex 枚举，账本记精确数 24）#print axioms——公理集 ⊆
     {propext, Classical.choice, Quot.sound}，零 sorryAx/ofReduceBool/
     ofReduceNat/trustCompiler。
  G4 语句锚（行级 regex＋陈述跨度面）：
     (a) import 面恰 [Mathlib＋TableB5＋TableB5Core＋TableB5Trace＋TableB5Polar]；
     (b) 块恒等式双例形状（block_id1/block_id2 命题形状）；
     (c) op≤1 面（vecNorm ((1 - P0) *ᵥ u) ≤ vecNorm u）；
     (d) trace-CS 面（Fintype.card 牙：|M.trace| ≤ Real.sqrt (Fintype.card n)
         * frob M）；
     (e) 路线 B 头条（∃ Q ∈ Matrix.orthogonalGroup＋Real.sqrt (3 * 牙）；
     (f) 路线 A 线性头条（2 * Real.sqrt 2 牙＋√λ₁λ₁/λ₃² 牙）＋窄域牙
         （/ 24 域形）；
     (g) TTP 双头条 (l3:ℝ)/(u1:ℝ) 牙；
     (h) **无 hdpar 机器锚（D82 裁决 3 核心）**：两条无条件头条
         （step6_uncond_hoelder/step6_uncond_linear）＋TTP 实例
         （ttpX_step6_hoelder/ttpX_step6_linear）的**陈述跨度内**
         frob (X * ((Xᵀ * X)⁻¹ 与 frob (ttpX z * (((ttpX z)ᵀ * ttpX z)⁻¹
         模式零命中；
     (i) 零 sorry／零 ≥15 位数字字面量／零『def … : ℚ :=』；非交叠守卫
         （Solution/TableA*/M1Data/TableB1*/TableB6*/根模块/lake 面
         零 TableB5Uncond 引用）。
  G5 离线精确复核（stdlib Fraction 零仓 import，独立第二实现：S⁻¹ Gauss-Jordan
     自实现，sqrt 用整数 Newton 有理包〔l4_procrustes.py:94 同式〕；seed
     20261019）：stereographic 有理 X（行单位满秩）＋有理 A（frob B² ≤ 1/4
     域内）＋D_⊥ := M − X(S⁻¹(XᵀM)) ⟹ Y := X(1+A) + D_⊥ 上：
     (a) 块恒等式 E·(1−P₀) == Y·D_⊥ᵀ（81 元）＋(1−P₀)E(1−P₀) == D_⊥D_⊥ᵀ
         （81 元）逐位；
     (b) ‖E(1−P₀)‖²_F ≤ ‖E‖²_F（op ≤ 1 实例面）；
     (c) tr(D_⊥D_⊥ᵀ) == tr(E(1−P₀))（循环＋幂等）精确＋squared 口径
         (3η)² − tr² ≥ 0（≤ 3η 面）；
     (d) ‖Y·D_⊥ᵀ‖²_F == ‖E(1−P₀)‖²_F ≤ η²（A8 实例面）；
     (e) 闭环 39 点网格（t := t_hi·k/40 ⊂ [0, √(3η*)]，t_hi := √(3η*) 上包）
         域内无违例（t(c_lo−t) ≤ η* ⟹ t ≤ 2η*/c_lo 逆否形）＋出域 NC 反例
         复现（P2-NC：η := c_lo²/3 时 t := c_lo 违 t ≤ 2η/c——域条件实质）；
     (f) 常数链 Fraction 精确（常数 TableB5Data.lean 源直读零手抄）：
         k1 == s1Up*u1*sqrt72Up/l3²（Lean 字面形逐位）＋19 点网格
         k1·δ + √(3√72Up·δ) ≤ C_B·√δ（C_B := k1·√δmax + √(3·sqrt72Up)，
         δ ∈ (0, δmax]）＋C_A == sqrt72Up*(u1*s1Up/l3² + 2/c_lo)＋
         δ_A == (l3/24)/sqrt72Up（安全向 c_lo²/12 ≤ l3/24 复核）＋
         β ≤ 1/2 域面（sqrt72Up·deltaMax ≤ l3²/(2·u1) 精确）；
     (g) 账本 sha256 cross-check（共享家族件 decisions.md/tableb-lean.md 用
         **git 溯源 append-only 验证**——D80-6 口径自始内置 D82 裁决 5，
         不做当前哈希等值锚）。
  NC1 注入 sorry 必被 G3 拦：/tmp 副本把 vecNorm_one_sub_P0_le 证明改 sorry
     → 独立编译（lean --root＋LEAN_PATH 前置副本目录）必现 sorry 警告＋公理
     检查必现 sorryAx → G3 判定逻辑必 FAIL（未篡原件 sanity：G3 全 24 件过）。
  NC2 篡陈述必被 G4 拦（三棱）：(i) √(3* → √(4*（路线 B 头条常数面）；
     (ii) 2*Real.sqrt 2 → 3*Real.sqrt 2（路线 A 头条常数面）；
     (iii) **向无条件头条注入 hdpar 前提文本必被无 hdpar 锚拦**（D82 裁决 3
     核心：防『条件定理改名冒充』与『前提走私』双作弊面）——三棱 G4 语句锚
     regex／跨度锚必 FAIL（有牙实证；原件 sanity PASS）。
  NC3 错误引擎必被 G5 拦（双棱）：(i) D_⊥ 换未投影 M 代入块恒等式复核
     （E·(1−P₀) == Y·Mᵀ）必 FAIL；(ii) 常数链篡 3→4（√(4·sqrt72Up·δ)）
     必在 19 点网格上被检出。

用法（CWD 无关）：
  python3 numerics/bounds/r19_b5u_gate.py     # 全门（exit 0 = 过）
  python3 thomson-n9/numerics/bounds/r19_b5u_gate.py
      # ↑ CWD＝仓库根时的验收命令命中同名 runpy 包装器（沿 R10A 0087eab／
      #   R14A r14_b5／R16A r16_b5a／R17A r17_b5b／R18A r18_b5c 先例）
"""
from __future__ import annotations

import hashlib
import json
import math
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

SEED_GATE = 20261019                  # R19 各门统一 seed（任务书口径）
ELAB_LIMIT_S = 600                    # G2 每文件 ≤10 min（D52 裁决 4 / D64-5）
THEOREM_COUNT = 24                    # 件内定理精确数（regex 枚举＋账本双面）

UNCOND_REL = "formal/lean/ThomsonN9/TableB5Uncond.lean"
GATE_REL = "numerics/bounds/r19_b5u_gate.py"
WRAPPER_REL = "thomson-n9/numerics/bounds/r19_b5u_gate.py"   # CWD 兼容包装器
LEDGER_REL = "numerics/bounds/results/r19_b5u_ledger.json"
NOTES_REL = "notes/tableb-lean.md"
DECISIONS_REL = "notes/decisions.md"
OWNED = {UNCOND_REL, GATE_REL, WRAPPER_REL, LEDGER_REL, NOTES_REL, DECISIONS_REL}

# 只读冻结件（表 B 前六件常数/本体件含 R18A Polar——D82 裁决 2 冻结面
# ＋表 B 其余件）：显式 git diff 守卫；TableB5Polar 另加 sha256 冻结锚。
FROZEN_READONLY = (
    "formal/lean/ThomsonN9/TableB5.lean",
    "formal/lean/ThomsonN9/TableB5Data.lean",
    "formal/lean/ThomsonN9/TableB5Core.lean",
    "formal/lean/ThomsonN9/TableB5Trace.lean",
    "formal/lean/ThomsonN9/TableB5Polar.lean",
    "formal/lean/ThomsonN9/TableB1.lean",
    "formal/lean/ThomsonN9/TableB1Data.lean",
    "formal/lean/ThomsonN9/TableB6.lean",
    "formal/lean/ThomsonN9/TableB6Data.lean",
)
POLAR_SHA256 = "d8c58f7d2c56c39fbe1ae62d634fc6ea5bd585fa9f1c0b9c2e2fc909d4338516"
# 挑战件目录与 references/（命题冻结面）：整目录 git 守卫（目录内任一改动即拦）。
FROZEN_DIRS = ("formal/lean/ComparatorChallenges", "references")
# 四账本（只读冻结，R11C–R18 先例口径）＋ endgame.json sha256 冻结锚。
FROZEN_LEDGERS = (
    "numerics/bounds/results/m9_campaign.json",
    "numerics/bounds/results/m10_campaign.json",
    "numerics/bounds/results/hermite_v2_campaign.json",
    "numerics/bounds/results/typed_ladder.json",
)
ENDGAME_REL = "numerics/bounds/results/endgame.json"
ENDGAME_SHA256 = "86863a09bf84e950e85fc5f902bc2b4046a87f06703bd782e5148fc119afd69f"

# r19 家族放行集（D82 裁决 5：r19 pattern＋共享家族 notes 两件＋轮次文档
# ＋收口门 pattern——本任务与 R19B 收口文件集零交叠〔R19B 后续在途〕）。
PARALLEL_FAMILY = [
    r"^numerics/bounds/r19[a-z0-9_]*(\.py|/)",
    r"^numerics/bounds/results/r19[a-z0-9_]*(\.json|/)",
    r"^thomson-n9/numerics/bounds/r19[a-z0-9_]*(\.py|/)",
    r"^notes/decisions\.md$",
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

TMP = Path("/tmp/r19_b5u_gate")
OLEAN_REL = ".lake/build/lib/lean/ThomsonN9"
UNCOND_LEAN = LEAN_DIR / "ThomsonN9" / "TableB5Uncond.lean"
LEDGER = RESULTS / "r19_b5u_ledger.json"
NOTES = REPO / "notes" / "tableb-lean.md"
DATA_LEAN = LEAN_DIR / "ThomsonN9" / "TableB5Data.lean"

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN_AXIOMS = ("sorryAx", "ofReduceBool", "ofReduceNat", "trustCompiler")

F0, F1 = Fr(0), Fr(1)

# 无 hdpar 机器锚（D82-3）：四头条陈述跨度内的禁式（frob D_∥ 形前提走私面）。
HEADLINE_THEOREMS = ("step6_uncond_hoelder", "step6_uncond_linear",
                     "ttpX_step6_hoelder", "ttpX_step6_linear")
HDPAR_PATTERNS = (
    r"frob \(X \* \(\(Xᵀ \* X\)⁻¹",
    r"frob \(ttpX z \* \(\(\(ttpX z\)ᵀ \* ttpX z\)⁻¹",
)


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
          "全在清单，theorem_count=24，axiom_policy 恰三标准 set 相等）")
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
    # 三层放行：① OWNED（本任务六件）；② 环境变量 R19A_G1_ALLOW_FOREIGN（自跑
    # 专用逐件放行，默认关）；③ PARALLEL_FAMILY pattern（r19 家族，D82-5）。
    allow_foreign = {q.strip() for q in
                     os.environ.get("R19A_G1_ALLOW_FOREIGN", "").split(",") if q.strip()}
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
                print(f"[gate][G1][r19 家族放行] 在途件（D82 裁决 5 pattern）：{p}")
                continue
            raise GateFail(
                f"G1 树上出现非本任务自有件（{cmd[1]}）：{p!r}"
                f"（自有集={sorted(OWNED)}；r19 家族放行层未覆盖该路径——"
                f"若确系并行在途件，可设 R19A_G1_ALLOW_FOREIGN={p} 显式放行）")
    # 只读冻结件守卫（显式单列，响亮报错；独立于放行集）
    for rel in FROZEN_READONLY + FROZEN_LEDGERS + (ENDGAME_REL,):
        r = run(["git", "diff", "HEAD", "--", rel], REPO)
        if r.returncode != 0 or r.stdout.strip():
            fail(f"G1 只读守卫失守：{rel} 相对 HEAD 有改动（表 B 前六件〔含 R18A "
                 "Polar 冻结面 D82-2〕/表 B 其余件/四账本/endgame.json 为冻结只读面）")
    for d in FROZEN_DIRS:
        # 挑战件与 references/ 在 campaign 根（thomson-n9 仓外）或仓内均守卫：
        # 仓内路径直接 diff；仓外（references/）以在场性＋文件计数快照只读断言。
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
    # TableB5Polar sha256 冻结锚（D82 裁决 2：R19A 门将其增入冻结面）
    pol = REPO / "formal/lean/ThomsonN9/TableB5Polar.lean"
    hp = sha256_of(pol)
    if hp != POLAR_SHA256:
        fail(f"G1 TableB5Polar.lean sha256 失配：{hp} != {POLAR_SHA256}"
             "（D82-2 冻结锚——R18A 本体件零改动）")
    # endgame.json sha256 冻结锚
    eg = REPO / ENDGAME_REL
    if not eg.is_file():
        fail(f"G1 endgame.json 不在场：{ENDGAME_REL}")
    h = sha256_of(eg)
    if h != ENDGAME_SHA256:
        fail(f"G1 endgame.json sha256 失配：{h} != {ENDGAME_SHA256}（冻结锚）")
    okmsg("G1 文件所有权守卫：git status/diff 相对 HEAD 仅自有六件／r19 家族放行件"
          "（或全净）；冻结件（表 B 前六件〔TableB5Polar sha256 == d8c58f7d…8516"
          " D82-2〕＋TableB1*/TableB6*＋挑战件/references/）零 diff；四账本零改动；"
          "endgame.json sha256 == 86863a09…69f 冻结锚")


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
    # 依赖序六连：Data → B5 → Core → Trace → Polar → Uncond（前五件为
    # R14/R16A/R17A/R18A 冻结件，重编译取 olen 供 import；Uncond 为本件）。
    order = [("ThomsonN9/TableB5Data.lean", "TableB5Data.olean", "Data"),
             ("ThomsonN9/TableB5.lean", "TableB5.olean", "B5"),
             ("ThomsonN9/TableB5Core.lean", "TableB5Core.olean", "Core"),
             ("ThomsonN9/TableB5Trace.lean", "TableB5Trace.olean", "Trace"),
             ("ThomsonN9/TableB5Polar.lean", "TableB5Polar.olean", "Polar"),
             ("ThomsonN9/TableB5Uncond.lean", "TableB5Uncond.olean", "Uncond")]
    walls = {}
    for src, ol, tag in order:
        walls[tag.lower()] = round(compile_lean(src, ol), 1)
        okmsg(f"G2 elaboration：{src} exit 0 无 error/sorry"
              f"（{walls[tag.lower()]}s ≤ 600s）")
    okmsg("G2 依赖序六连完毕（Data→B5→Core→Trace→Polar→Uncond），"
          "olen 落 .lake/build 供 G3/NC1 复用")
    return walls


# ------------------------------------------------------------------ G3
def parse_axiom_lines(out: str) -> dict:
    """#print axioms 输出解析（跨行续行鲁棒）。"""
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
    return ("import ThomsonN9.TableB5Uncond\n"
            + "".join(f"#print axioms {t}\n" for t in names))


def gate3_axioms(src_uncond: str) -> dict:
    names = [f"ThomsonN9.TableB5Uncond.{t}" for t in theorem_names(src_uncond)]
    if len(names) < 20:
        fail(f"G3 定理枚举偏少：{len(names)}（任务书预期 ≥20、账本记 24）")
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
def statement_span(src: str, name: str) -> str:
    m = re.search(rf"theorem {name}\b.*?:=", src, re.S)
    if not m:
        return ""
    return m.group(0)


def gate4_core(src: str) -> None:
    """G4 语句锚核心（NC2 复用；对篡改源同样有牙）。"""
    if re.findall(r"^import\s+\S+", src, re.M) != \
            ["import Mathlib", "import ThomsonN9.TableB5",
             "import ThomsonN9.TableB5Core", "import ThomsonN9.TableB5Trace",
             "import ThomsonN9.TableB5Polar"]:
        fail("G4 TableB5Uncond.lean import 行失配（应恰为 [import Mathlib, "
             "import ThomsonN9.TableB5, import ThomsonN9.TableB5Core, "
             "import ThomsonN9.TableB5Trace, import ThomsonN9.TableB5Polar]）")
    anchors = [
        # ---- 层 1：块恒等式双例形状
        (r"theorem block_id1 \{m n : Type\} \[Fintype m\] \[Fintype n\] \[DecidableEq m\]", "块恒等式例 1 定理头锚"),
        (r"    \(Y \* Yᵀ - X \* Xᵀ\) \* \(1 - X \* \(Xᵀ \* X\)⁻¹ \* Xᵀ\)", "块恒等式例 1 命题形状锚（E*(1−P₀)）"),
        (r"      = Y \* \(\(Y - X\) - X \* \(\(Xᵀ \* X\)⁻¹ \* \(Xᵀ \* \(Y - X\)\)\)\)ᵀ", "块恒等式例 1 右端锚（Y*D_⊥ᵀ）"),
        (r"theorem block_id2 \{m n : Type\} \[Fintype m\] \[Fintype n\] \[DecidableEq m\]", "块恒等式例 2 定理头锚"),
        (r"    \(1 - X \* \(Xᵀ \* X\)⁻¹ \* Xᵀ\) \* \(Y \* Yᵀ - X \* Xᵀ\) \* \(1 - X \* \(Xᵀ \* X\)⁻¹ \* Xᵀ\)", "块恒等式例 2 命题形状锚（(1−P₀)E(1−P₀)）"),
        # ---- 层 1：op(1−P₀) ≤ 1 面
        (r"theorem vecNorm_one_sub_P0_le \{m : Type\} \[Fintype m\] \[DecidableEq m\]", "op≤1 面定理头锚"),
        (r"    vecNorm \(\(1 - P0\) \*ᵥ u\) ≤ vecNorm u :=", "op≤1 面命题形状锚"),
        # ---- 层 1：trace-CS 面（Fintype.card 牙）
        (r"theorem abs_trace_le_sqrt_card_frob \{n : Type\} \[Fintype n\] \[DecidableEq n\]", "trace-CS 定理头锚"),
        (r"    \|M\.trace\| ≤ Real\.sqrt \(Fintype\.card n\) \* frob M :=", "trace-CS 命题形状锚（Fintype.card 牙）"),
        # ---- 层 1：½-Hölder 面 9 行实例
        (r"      ≤ Real\.sqrt \(3 \* frob \(Y \* Yᵀ - X \* Xᵀ\)\) :=", "½-Hölder 9 行实例锚（√(3η)）"),
        # ---- 层 2：路线 B 头条（NC2 棱一）
        (r"theorem step6_uncond_hoelder \{n : Type\} \[Fintype n\] \[DecidableEq n\]", "路线 B 头条定理头锚"),
        (r"    ∃ Q ∈ Matrix\.orthogonalGroup n ℝ,", "路线 B 头条 ∃Q membership 锚"),
        (r"          \+ Real\.sqrt \(3 \* frob \(Y \* Yᵀ - X \* Xᵀ\)\) :=", "路线 B 头条 √(3η) 牙（NC2 棱一）"),
        # ---- 层 2：C_B·√δ 推论
        (r"theorem step6_hoelder_Cform \{n : Type\} \[Fintype n\] \[DecidableEq n\]", "C_B·√δ 推论定理头锚"),
        (r"        ≤ \(\(s1Up:ℝ\) \* \(u1:ℝ\) \* \(sqrt72Up:ℝ\) / \(l3:ℝ\)\^2 \* Real\.sqrt \(deltaMax:ℝ\)", "C_B 常数链锚（k1·√δ_max）"),
        # ---- 层 3：路线 A 线性头条（NC2 棱二）
        (r"theorem step6_uncond_linear \{n : Type\} \[Fintype n\] \[DecidableEq n\]", "路线 A 线性头条定理头锚"),
        (r"        ≤ \(Real\.sqrt lam1 \* lam1 / lam3\^2 \+ 2 \* Real\.sqrt 2 / Real\.sqrt lam3\)", "路线 A 线性头条常数链锚（2*Real.sqrt 2 牙——NC2 棱二）"),
        (r"    \(heta24 : frob \(Y \* Yᵀ - X \* Xᵀ\) ≤ lam3 / 24\) :", "路线 A 窄域牙（/ 24 域形）"),
        # ---- 层 3：A10 闭环消歧
        (r"theorem dperp_le_linear \{n : Type\} \[Fintype n\] \[DecidableEq n\]", "A10 闭环消歧定理头锚"),
        (r"      ≤ 2 \* Real\.sqrt 2 \* frob \(Y \* Yᵀ - X \* Xᵀ\) / Real\.sqrt lam3 :=", "A10 结论锚（2√2·η/√λ₃）"),
        # ---- 层 4：TTP 双头条（(l3:ℝ)/(u1:ℝ) 牙）
        (r"theorem ttpX_step6_hoelder \(z : ℝ\) \(h1 : \(zLo:ℝ\) ≤ z\) \(h2 : z ≤ \(zHi:ℝ\)\)", "TTP Hölder 头条定理头锚"),
        (r"        ≤ Real\.sqrt \(u1:ℝ\)", "TTP Hölder 头条 √u₁ 牙"),
        (r"          \+ Real\.sqrt \(3 \* frob \(Y \* Yᵀ - \(ttpX z\) \* \(ttpX z\)ᵀ\)\) :=", "TTP Hölder 头条 √(3η) 牙"),
        (r"theorem ttpX_step6_linear \(z : ℝ\) \(h1 : \(zLo:ℝ\) ≤ z\) \(h2 : z ≤ \(zHi:ℝ\)\)", "TTP 线性头条定理头锚"),
        (r"        ≤ \(Real\.sqrt \(u1:ℝ\) \* \(u1:ℝ\) / \(l3:ℝ\)\^2", "TTP 线性头条 √u₁u₁/l₃² 牙"),
        (r"    \(heta24 : frob \(Y \* Yᵀ - \(ttpX z\) \* \(ttpX z\)ᵀ\) ≤ \(l3:ℝ\) / 24\) :", "TTP 线性头条窄域牙（l3/24）"),
    ]
    for pat, name in anchors:
        if not re.search(pat, src, re.M):
            fail(f"G4 语句锚缺失：{name}（pattern {pat!r}）")
    # (h) 无 hdpar 机器锚（D82 裁决 3 核心）：四头条陈述跨度内 frob D_∥ 模式零命中
    for th in HEADLINE_THEOREMS:
        span = statement_span(src, th)
        if not span:
            fail(f"G4 无 hdpar 锚：头条 {th} 的陈述跨度未提取到")
        for pat in HDPAR_PATTERNS:
            if re.search(pat, span):
                fail(f"G4 无 hdpar 锚失守：{th} 陈述跨度内命中禁式 {pat!r}"
                     "（frob D_∥ 形前提走私——D82-3：两条无条件头条＋TTP 实例的"
                     "陈述不得携带 hdpar 型前提）")
    # 各头条跨度内的正向牙（跨度面防『改名冒充』：锚必须落在头条陈述内）
    span_teeth = {
        "step6_uncond_hoelder": ["∃ Q ∈ Matrix.orthogonalGroup n ℝ",
                                 "Real.sqrt (3 * frob (Y * Yᵀ - X * Xᵀ))",
                                 "lam1 * frob (Y * Yᵀ - X * Xᵀ) / lam3^2 ≤ 1 / 2"],
        "step6_uncond_linear": ["2 * Real.sqrt 2",
                                 "Real.sqrt lam1 * lam1 / lam3^2",
                                 "≤ lam3 / 24"],
        "ttpX_step6_hoelder": ["(u1:ℝ)", "(l3:ℝ)^2",
                               "Real.sqrt (3 * frob (Y * Yᵀ - (ttpX z) * (ttpX z)ᵀ))"],
        "ttpX_step6_linear": ["(u1:ℝ)", "(l3:ℝ)^2", "2 * Real.sqrt 2",
                              "≤ (l3:ℝ) / 24"],
    }
    for th, teeth in span_teeth.items():
        span = statement_span(src, th)
        for tooth in teeth:
            if tooth not in span:
                fail(f"G4 头条跨度正向牙缺失：{th} 陈述跨度内无 {tooth!r}")
    # 禁串 sorry／伪陈述
    if re.search(r"\bsorry\b", src):
        body_sorry = re.findall(r"^\s*(?:exact |rw \[)?sorry", src, re.M)
        if body_sorry or re.search(r":= by sorry", src):
            fail("G4 禁串失守：源码含 sorry 证明")
    # 零 ≥15 位数字面量（数值数据面；3/4、1/2、2、3 等结构常数不在列）
    long_lits = re.findall(r"\d{15,}", src)
    if long_lits:
        fail(f"G4 零 ≥15 位数字面量失守：{long_lits[:3]}")
    # 零『def … : ℚ :=』（无 Data 件口径）
    if re.findall(r"^def \w+ : ℚ :=", src, re.M):
        fail("G4 零『def … : ℚ :=』失守（本件零数值数据字面量，无 Data 件）")


def gate4_statement(src_uncond: str) -> None:
    gate4_core(src_uncond)
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
        if p.is_file() and "TableB5Uncond" in p.read_text():
            fail(f"G4 非交叠守卫：{rel} 含 'TableB5Uncond'（本件必须不被表 A/M1/"
                 "Solution/表 B 其余件/根模块/lake 面引用）")
    okmsg("G4 语句锚：import 面恰 [Mathlib＋TableB5＋TableB5Core＋TableB5Trace＋"
          "TableB5Polar]；26 锚全在（块恒等式双例形状/op≤1 面/trace-CS 面"
          "Fintype.card 牙/路线 B 头条 ∃Q＋√(3η) 牙/C_B 常数链/路线 A 线性头条"
          "2*Real.sqrt 2＋√λ₁λ₁/λ₃² 牙＋/24 窄域牙/A10 闭环 2√2 牙/TTP 双头条"
          "(l3:ℝ)/(u1:ℝ) 牙）＋**无 hdpar 机器锚（四头条陈述跨度 frob (X * "
          "((Xᵀ * X)⁻¹ 模式零命中＋跨度正向牙）**＋零 ≥15 位数字字面量＋零 ℚ def"
          "＋零 sorry 证明；非交叠面零 TableB5Uncond 引用")


# ------------------------------------------------------------------ G5 门内独立第二实现（Fraction 引擎）
def mat_mul(A, B):
    n, k, m = len(A), len(B), len(B[0])
    return [[sum((A[i][t] * B[t][j] for t in range(k)), F0) for j in range(m)]
            for i in range(n)]


def mat_add(A, B):
    return [[A[i][j] + B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def mat_sub(A, B):
    return [[A[i][j] - B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def mat_T(A):
    return [list(r) for r in zip(*A)]


def eye(n):
    return [[F1 if i == j else F0 for j in range(n)] for i in range(n)]


def frob_sq(M):
    """frob² ＝ ∑ M_ij²（Fraction 精确；σ 无理面一律走平方化等价比较）。"""
    return sum((sum((x * x for x in row), F0) for row in M), F0)


def trace(A):
    return sum((A[i][i] for i in range(len(A))), F0)


def mat_eq(A, B):
    return all(A[i][j] == B[i][j]
               for i in range(len(A)) for j in range(len(A[0])))


def gauss_inv(S):
    """n×n Fraction 矩阵 Gauss-Jordan 求逆（门内独立自实现，零仓 imports）。"""
    n = len(S)
    aug = [list(S[i]) + [F1 if j == i else F0 for j in range(n)] for i in range(n)]
    for col in range(n):
        piv = next((r for r in range(col, n) if aug[r][col] != 0), None)
        if piv is None:
            raise ValueError("singular")
        aug[col], aug[piv] = aug[piv], aug[col]
        pv = aug[col][col]
        aug[col] = [x / pv for x in aug[col]]
        for r in range(n):
            if r != col and aug[r][col] != 0:
                f = aug[r][col]
                aug[r] = [x - f * y for x, y in zip(aug[r], aug[col])]
    return [row[n:] for row in aug]


def sqrt_rat(q: Fr, side: str, bits: int = 200) -> Fr:
    """√q 的有理下/上包（整数 Newton，l4_procrustes.py:94 同式）。"""
    if q < 0:
        raise ValueError("sqrt of negative")
    if q == 0:
        return F0
    p = bits
    num, den = q.numerator, q.denominator
    if side == "lo":
        n = math.isqrt((num << (2 * p)) // den)
        return Fr(n, 1 << p)
    n = math.isqrt((num << (2 * p)) // den + 1) + 1
    return Fr(n, 1 << p)


def lcg(seed: int):
    x = seed
    while True:
        x = (1103515245 * x + 12345) % (1 << 31)
        yield x


def gen_stereographic_X(seed: int) -> list[list[Fr]]:
    """stereographic 有理 X：u,v ∈ ℚ ⟹ (2u, 2v, 1−u²−v²)/(1+u²+v²)
    行单位逐位精确；u ≠ 0 保证（首列坐标非零）。"""
    g = lcg(seed)
    rows = []
    for _ in range(9):
        while True:
            u = Fr(next(g) % 21 - 10, 10)
            v = Fr(next(g) % 21 - 10, 10)
            if u != 0:
                break
        d = F1 + u * u + v * v
        rows.append([2 * u / d, 2 * v / d, (F1 - u * u - v * v) / d])
    # 行单位自检（stereographic 精确性）
    for i, r in enumerate(rows):
        if sum((x * x for x in r), F0) != F1:
            fail(f"G5 stereographic 行单位自检失守 @row {i}")
    return rows


def check_uncond_identities(rng_seed: int, wrong_dperp: bool = False):
    """R19A 无条件面恒等式族精确复核（wrong_dperp 为 NC3 篡引擎棱一）。

    构造（全有理精确，seed 复放）：stereographic 有理 X（9×3 行单位满秩）＋
    随机有理 A（系数 /100 ⟹ frob B² ≤ 1/4 域内）＋D_⊥ := M − X·(S⁻¹·(Xᵀ·M))
    （S⁻¹ Gauss-Jordan 自实现；Xᵀ·D_⊥ == 0 精确）⟹ Y := X·(1+A) + D_⊥。
    NC3(i) wrong_dperp：块恒等式复核中 D_⊥ 换未投影 M（防假拦截实证）。
    """
    g = lcg(rng_seed)
    X = gen_stereographic_X(rng_seed)
    S = mat_mul(mat_T(X), X)
    Sinv = gauss_inv(S)
    if mat_mul(S, Sinv) != eye(3) or mat_mul(Sinv, S) != eye(3):
        fail("G5 Gauss-Jordan 逆自检失守（S·S⁻¹ ≠ I₃）")
    P0 = mat_mul(mat_mul(X, Sinv), mat_T(X))
    I9 = eye(9)
    One_m_P0 = mat_sub(I9, P0)
    # 随机有理 A：分母 100 的小系数 ⟹ frob B ≤ 1/2 域内（frob B² ≤ 1/4）
    A3 = [[Fr(next(g) % 7 - 3, 100) for _ in range(3)] for _ in range(3)]
    B3 = [[sum((A3[i][t] * A3[t][j] for t in range(3)), F0) for j in range(3)]
          for i in range(3)]
    B3 = [[A3[i][j] + A3[j][i] + B3[i][j] for j in range(3)] for i in range(3)]
    beta = frob_sq(B3)
    if beta > Fr(1, 4):
        fail(f"G5 实例 frob B > 1/2（域面，frob B² = {float(beta):.6f}）")
    M9 = [[Fr(next(g) % 11 - 5, 10) for _ in range(3)] for _ in range(9)]
    XD = mat_mul(mat_mul(X, Sinv), mat_mul(mat_T(X), M9))   # X·(S⁻¹·(XᵀM))
    Dperp = mat_sub(M9, XD)
    if not mat_eq(mat_mul(mat_T(X), Dperp), [[F0] * 3 for _ in range(3)]):
        fail("G5 Xᵀ·D_⊥ != 0（投影构造失败）")
    OneA = [[A3[i][j] + (F1 if i == j else F0) for j in range(3)] for i in range(3)]
    Y = [list(map(sum, zip(mat_mul(X, OneA)[i], Dperp[i]))) for i in range(9)]
    E = mat_sub(mat_mul(Y, mat_T(Y)), mat_mul(X, mat_T(X)))
    eta2 = frob_sq(E)
    # (a) 块恒等式 81 元×2（NC3(i)：D_⊥ 换未投影 M 必被检出）
    lhs1 = mat_mul(E, One_m_P0)
    tgt1 = mat_mul(Y, mat_T(M9 if wrong_dperp else Dperp))
    if not mat_eq(lhs1, tgt1):
        if wrong_dperp:
            fail("NC3 预期检出：未投影 M 代入块恒等式（E·(1−P₀) ≠ Y·Mᵀ）"
                 "（防假拦截实证）")
        fail("G5(a) 块恒等式失守：E·(1−P₀) != Y·D_⊥ᵀ")
    if wrong_dperp:
        fail("NC3 失守：未投影 M 下块恒等式仍成立（不可达：XᵀM ≠ 0 ⟹ "
             "E(1−P₀) = Y·D_⊥ᵀ ≠ Y·Mᵀ 当 D_⊥ ≠ M）")
    lhs2 = mat_mul(mat_mul(One_m_P0, E), One_m_P0)
    if not mat_eq(lhs2, mat_mul(Dperp, mat_T(Dperp))):
        fail("G5(a) 块恒等式失守：(1−P₀)·E·(1−P₀) != D_⊥·D_⊥ᵀ")
    # (b) op ≤ 1 实例面
    if not frob_sq(lhs1) <= eta2:
        fail("G5(b) ‖E(1−P₀)‖²_F > ‖E‖²_F")
    # (c) Hölder trace 面（≤ 3η squared 口径——真常数 3 恒定）
    trD = trace(mat_mul(Dperp, mat_T(Dperp)))
    trE1 = trace(mat_mul(E, One_m_P0))
    if trD != trE1:
        fail("G5(c) tr(D_⊥D_⊥ᵀ) != tr(E(1−P₀))（循环＋幂等面失败）")
    if 9 * eta2 - trE1 * trE1 < 0:
        fail("G5(c) |tr(E(1−P₀))| > 3‖E‖_F（Hölder 面失败）")
    # (d) A8 实例面
    YDt = mat_mul(Y, mat_T(Dperp))
    if frob_sq(YDt) != frob_sq(lhs1):
        fail("G5(d) ‖Y·D_⊥ᵀ‖² != ‖E(1−P₀)‖²")
    if frob_sq(YDt) > eta2:
        fail("G5(d) ‖Y·D_⊥ᵀ‖²_F > η²")


def parse_data_literal(name: str) -> Fr:
    """TableB5Data.lean 源直读 ℚ 字面量（零手抄——D73 G4 式）。"""
    src = DATA_LEAN.read_text()
    m = re.search(rf"^def {name} : ℚ := (\S+)", src, re.M)
    if not m:
        fail(f"G5(f) TableB5Data 源直读失败：def {name} : ℚ := … 不在场")
    tok = m.group(1)
    neg = tok.startswith("-")
    if neg:
        tok = tok[1:]
    f = Fr(*[int(x) for x in tok.split("/")]) if "/" in tok else Fr(int(tok))
    return -f if neg else f


def check_constants(const_tamper: int = 0):
    """(e) 闭环网格＋出域 NC 反例复现＋(f) 常数链 Fraction 精确
    （TableB5Data.lean 源直读零手抄；const_tamper 为 NC3(ii) 篡棱）。"""
    l3 = parse_data_literal("l3")
    u1 = parse_data_literal("u1")
    s1Up = parse_data_literal("s1Up")
    s3Dn = parse_data_literal("s3Dn")
    sqrt72Up = parse_data_literal("sqrt72Up")
    deltaMax = parse_data_literal("deltaMax")
    # (e) 闭环 39 点网格（域内无违例）：c_lo := √(l3/2) 下包，η* := c_lo²/12
    c_lo = sqrt_rat(l3 * Fr(1, 2), "lo")
    if c_lo * c_lo > l3 * Fr(1, 2):
        fail("G5(e) c_lo 下包自检失守（c_lo² > l3/2）")
    eta_A = c_lo * c_lo / 12
    if eta_A > l3 / 24:
        fail("G5(e) 包络口径自检失守（c_lo²/12 > l3/24）")
    t_hi = sqrt_rat(3 * eta_A, "hi")
    viol = 0
    for k in range(1, 40):
        t = t_hi * Fr(k, 40)
        if t * (c_lo - t) <= eta_A and t > 2 * eta_A / c_lo:
            viol += 1
    if viol:
        fail(f"G5(e) 闭环蕴含在网格上被违 {viol} 点（消歧推导错）")
    # 出域 NC 反例复现（P2-NC）：η := c_lo²/3 时 t := c_lo 违 t ≤ 2η/c
    eta_bad = c_lo * c_lo / 3
    t_bad = c_lo
    if not (t_bad * (c_lo - t_bad) <= eta_bad and t_bad > 2 * eta_bad / c_lo):
        fail("G5(e) 出域反例未按预期出现（P2-NC 复现失效）")
    if not eta_bad > c_lo * c_lo / 12:
        fail("G5(e) η_bad 未出域")
    # (f) 常数链：k1 == s1Up*u1*sqrt72Up/l3²（Lean 字面形逐位）
    k1 = s1Up * u1 * sqrt72Up / (l3 * l3)
    # 19 点网格 k1·δ + √(3√72Up·δ) ≤ C_B·√δ（C_B := k1·√δmax + √(3·sqrt72Up)
    # 恒用真常数 3；NC3(ii) 篡棱只动网格 lhs 的 Hölder 因子——篡引擎对真 C_B
    # 复核，2 > √3 的差在顶部格点必被检出）
    kfac = const_tamper if const_tamper else 3
    C_B = k1 * sqrt_rat(deltaMax, "hi") + sqrt_rat(3 * sqrt72Up, "hi")
    bad = 0
    for i in range(1, 20):
        d = deltaMax * Fr(i, 20)
        lhs = k1 * d + sqrt_rat(kfac * sqrt72Up * d, "hi")
        rhs = C_B * sqrt_rat(d, "lo")
        if lhs > rhs:
            bad += 1
    if bad and not const_tamper:
        fail(f"G5(f) Hölder 覆盖不等式在网格上被违 {bad} 点")
    if bad and const_tamper:
        fail(f"NC3 预期检出：常数链篡 3→{kfac} 后 19 点网格对真 C_B 被违 {bad} 点"
             "（防假拦截实证）")
    if not bad and const_tamper:
        fail(f"NC3 失守：常数链篡 3→{kfac} 后 19 点网格仍全过（不可达："
             f"2 > √3 在顶部格点必破坏）")
    # C_A == sqrt72Up*(u1*s1Up/l3² + 2/c_lo)＋δ_A == (l3/24)/sqrt72Up（安全向）
    C_A = sqrt72Up * (u1 * s1Up / (l3 * l3) + 2 / c_lo)
    delta_A = (l3 / 24) / sqrt72Up
    if not eta_A / sqrt72Up <= delta_A:
        fail("G5(f) δ_A 包络面失守（eta_A/sqrt72Up > (l3/24)/sqrt72Up）")
    # β ≤ 1/2 域面 Fraction 精确（记录域全体在路线 B 域内）
    if not sqrt72Up * deltaMax <= l3 * l3 / (2 * u1):
        fail("G5(f) 记录域内 β ≤ 1/2 不成立（路线 B 域面复核失败）")
    # 记录恒等式侧证（P1 同式）
    dom = s3Dn / (2 * s1Up)
    if not dom < Fr(1, 2):
        fail("G5(f) dom ≥ 1/2（与记录不符）")
    if sqrt72Up * deltaMax != dom * l3 * l3 / u1:
        fail("G5(f) 记录恒等式 sqrt72Up·deltaMax == dom·l3²/u1 失败")
    if not const_tamper:
        okmsg(f"G5(e) 闭环 39 点网格域内无违例（c_lo ≈ {float(c_lo):.6f}，"
              f"η* ≈ {float(eta_A):.6f}）＋出域 NC 反例复现（η := c_lo²/3 时 "
              f"t := c_lo 违 t ≤ 2η/c）✓")
        okmsg(f"G5(f) 常数链 Fraction 精确：k1 ≈ {float(k1):.6f}（Lean 字面形"
              f"逐位）；19 点网格 k1·δ+√(3√72Up·δ) ≤ C_B·√δ（C_B ≈ "
              f"{float(k1 * sqrt_rat(deltaMax, 'hi') + sqrt_rat(3 * sqrt72Up, 'hi')):.3f}）"
              f"全过；C_A ≈ {float(C_A):.3f}；δ_A ≈ {float(delta_A):.6f}"
              f"（安全向 eta_A/√72Up ≤ δ_A ✓）；β ≤ 1/2 域面＋记录恒等式 ✓")
    return


# 共享家族追加面（G1 PARALLEL_FAMILY 两件 notes 件）：D82 裁决 5 自始内置
# D80-6 口径——git 溯源 append-only 验证，不做当前哈希等值锚。
APPEND_ONLY_FAMILY_SHARED = ("notes/decisions.md", "notes/tableb-lean.md")


def _ledger_anchor_prefix_ok(rel: str, want: str) -> bool:
    """共享家族 notes 件 append-only 漂移验证（D80 裁决 6 / D82 裁决 5）：

    账本锚哈希须等于【账本入库提交】（git log --diff-filter=A 首提交）
    时点的该文件版本哈希（⇒ 账本记录在其锚定时点诚实），且该版本须为
    当前文件的字节前缀（⇒ 此后仅追加——家族设计允许后续轮次追加）；
    任一不成立即非追加篡改，仍按失配拦截。
    """
    r = run(["git", "log", "--format=%H", "--diff-filter=A", "--reverse",
             "--", LEDGER_REL], REPO)
    if r.returncode != 0 or not r.stdout.strip():
        return False
    anchor_commit = r.stdout.split()[0]
    # 字节精确取版（不走 text=True——notes 件含全角/CJK，字节前缀比对
    # 须零转码损失）
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
    """(g) 账本锚 cross-check：自有件 sha256 重算比对（'self' 件跳过；
    共享家族 notes 件按 git 溯源 append-only 例外——D80-6/D82-5）。"""
    files = led.get("files", {})
    nchk = 0
    n_append = 0
    for rel, rec in files.items():
        if rec == "self":
            continue
        p = REPO / rel
        if not p.is_file():
            fail(f"G5(g) 账本 sha256 面：自有件不在场 {rel}")
        h = sha256_of(p)
        want = rec.get("sha256") if isinstance(rec, dict) else rec
        if want == h:
            nchk += 1
            continue
        if rel in APPEND_ONLY_FAMILY_SHARED and _ledger_anchor_prefix_ok(rel, want):
            n_append += 1      # 共享家族件 append-only 漂移（后续轮次追加）
            continue
        fail(f"G5(g) 账本 sha256 失配：{rel}（账本 {str(want)[:16]}… != "
             f"实测 {h[:16]}…）")
    okmsg(f"G5(g) 账本锚 cross-check：{nchk} 自有件 sha256 逐件重算一致＋"
          f"{n_append} 共享家族件 git 溯源 append-only 一致"
          "（ledger 自身记 'self'）")


NOTES_ANCHORS = [
    "## §7 R19A B5Uncond 无条件化件（r19a-b5u-uncond-lean，2026-10-12）",
    "### 探针三档判定转录（R18B 三路线供件 → R19A 施工面）",
    "### 施工摩擦（亲历留档）",
    "### 陈述面决策（D83）",
    "heavySolves = 0",
    "无 hdpar",
]


def gate5_offline(led: dict) -> dict:
    check_uncond_identities(SEED_GATE)
    okmsg(f"G5(a)-(d) 实例（seed={SEED_GATE} 复放）：块恒等式 81 元×2 逐位＋"
          "‖E(1−P₀)‖² ≤ ‖E‖²＋tr(D_⊥D_⊥ᵀ) == tr(E(1−P₀)) 精确＋(3η)²−tr² ≥ 0＋"
          "‖Y·D_⊥ᵀ‖² == ‖E(1−P₀)‖² ≤ η² 全过（stereographic 有理 X＋有理 A"
          "＋D_⊥ := M−X(S⁻¹(XᵀM))，Gauss-Jordan S⁻¹ 自实现）")
    check_constants()
    check_ledger_hashes(led)
    # notes §7 转录锚
    notes = NOTES.read_text()
    for anc in NOTES_ANCHORS:
        if anc not in notes:
            fail(f"G5 notes/tableb-lean.md §7 转录锚缺失：{anc!r}")
    okmsg("G5 离线精确复核：Fraction 独立第二实现（零仓 import，Gauss-Jordan/"
          "Newton sqrt 自实现）＋常数链（TableB5Data 源直读零手抄）＋账本 sha256 "
          "cross-check（共享家族件 git 溯源 append-only——D82-5）＋notes §7 "
          "转录锚 6 处在文")
    return {"instances": 1}


# ------------------------------------------------------------------ NC
def nc1_sorry_injection(src_uncond: str) -> None:
    # 整证明块替换为 sorry（目标定理的 := by 至下一顶层声明前——保证篡件
    # 可独立 elaboration 出 sorry 警告，而非中途 no-goals 错误掩盖）。
    m = re.search(
        r"(theorem vecNorm_one_sub_P0_le \{m : Type\} \[Fintype m\] \[DecidableEq m\]\n"
        r"    \{P0 : Matrix m m ℝ\} \(hSym : P0ᵀ = P0\) \(hIdem : P0 \* P0 = P0\) \(u : m → ℝ\) :\n"
        r"    vecNorm \(\(1 - P0\) \*ᵥ u\) ≤ vecNorm u := by)\n"
        r".*?(?=\n(?:theorem |/-!))",
        src_uncond, re.S)
    if not m:
        fail("NC1 预置失败：目标定理证明块未定位（vecNorm_one_sub_P0_le）")
    tampered = src_uncond[:m.start()] + m.group(1) + "\n  sorry" + src_uncond[m.end():]
    if tampered == src_uncond:
        fail("NC1 预置失败：注入未生效")
    d = TMP / "nc1"
    (d / "ThomsonN9").mkdir(parents=True, exist_ok=True)
    (d / "ThomsonN9" / "TableB5Uncond.lean").write_text(tampered)
    # 依赖 olen 随副本落 root（TableB5Uncond imports 五件；G2 已编译 olen）。
    for dep in ("TableB5Data.olean", "TableB5.olean", "TableB5Core.olean",
                "TableB5Trace.olean", "TableB5Polar.olean"):
        src = LEAN_DIR / OLEAN_REL / dep
        if not src.is_file():
            fail(f"NC1 预置失败：依赖 olen 不在场（G2 应已编译）：{src}")
        (d / "ThomsonN9" / dep).write_bytes(src.read_bytes())
    lp = run(["lake", "env", "printenv", "LEAN_PATH"], LEAN_DIR).stdout.strip()
    env = gate_env()
    env["LEAN_PATH"] = f"{d}:{lp}"
    b = subprocess.run(["lean", "--root", str(d), "-o",
                        str(d / "ThomsonN9" / "TableB5Uncond.olean"),
                        str(d / "ThomsonN9" / "TableB5Uncond.lean")],
                       cwd=str(LEAN_DIR), env=env, capture_output=True, text=True,
                       timeout=605)
    if b.returncode != 0 or "declaration uses `sorry`" not in (b.stdout + b.stderr):
        fail(f"NC1 注入 sorry 后编译未产生 sorry 警告（exit {b.returncode}）：\n"
             f"{(b.stdout + b.stderr)[-500:]}")
    axfile = d / "axcheck.lean"
    axfile.write_text("import ThomsonN9.TableB5Uncond\n"
                      "#print axioms ThomsonN9.TableB5Uncond."
                      "vecNorm_one_sub_P0_le\n")
    a = subprocess.run(["lean", str(axfile)], cwd=str(LEAN_DIR), env=env,
                       capture_output=True, text=True, timeout=605)
    ax = parse_axiom_lines(a.stdout)
    th = "ThomsonN9.TableB5Uncond.vecNorm_one_sub_P0_le"
    caught = th in ax and ("sorryAx" in ax[th] or (ax[th] - ALLOWED_AXIOMS))
    if not caught:
        fail(f"NC1 失守：注入 sorry 后公理检查未现 sorryAx（{ax}）")
    okmsg("NC1 注入 sorry 必被 G3 拦：篡件 vecNorm_one_sub_P0_le 公理集 = "
          f"{sorted(ax.get(th, set()))}（含 sorryAx → G3 FAIL）")


def nc2_statement_tamper(src_uncond: str) -> None:
    # 三棱（D82 裁决 3 核心）：(i) √(3* → √(4*（路线 B 头条常数面）；
    # (ii) 2*Real.sqrt 2 → 3*Real.sqrt 2（路线 A 头条常数面）；
    # (iii) 向无条件头条注入 hdpar 前提文本（前提走私面）。
    tampered1 = src_uncond.replace("Real.sqrt (3 * frob (Y * Yᵀ - X * Xᵀ))",
                                   "Real.sqrt (4 * frob (Y * Yᵀ - X * Xᵀ))")
    if tampered1 == src_uncond:
        raise GateFail("NC2 预置失败：篡改一未生效（源码无 √(3*frob (Y*Yᵀ…) 字面）")
    try:
        gate4_core(tampered1)
        raise GateFail("NC2 失守：篡陈述一（√(3*→√(4*)）后 G4 语句锚未报错")
    except GateFail as e:
        if "语句锚缺失" not in str(e) and "正向牙缺失" not in str(e):
            raise
        print(f"[gate][NC2 检出·棱一] {e}")
    tampered2 = src_uncond.replace("2 * Real.sqrt 2", "3 * Real.sqrt 2")
    if tampered2 == src_uncond:
        raise GateFail("NC2 预置失败：篡改二未生效（源码无 2 * Real.sqrt 2 字面）")
    try:
        gate4_core(tampered2)
        raise GateFail("NC2 失守：篡陈述二（2√2→3√2）后 G4 语句锚未报错")
    except GateFail as e:
        if "语句锚缺失" not in str(e) and "正向牙缺失" not in str(e):
            raise
        print(f"[gate][NC2 检出·棱二] {e}")
    hdpar_premise = ("    (hdpar : frob (X * ((Xᵀ * X)⁻¹ * (Xᵀ * (Y - X))))\n"
                     "      ≤ Real.sqrt lam1 * (lam1 * frob (Y * Yᵀ - X * Xᵀ) / lam3^2))\n")
    anchor_line = ("    (hdom1 : lam1 * frob (Y * Yᵀ - X * Xᵀ) / lam3^2 ≤ 1 / 2) :\n"
                   "    ∃ Q ∈ Matrix.orthogonalGroup n ℝ,\n")
    if anchor_line not in src_uncond:
        raise GateFail("NC2 预置失败：篡改三注入点不在场（hdom1 行字面失配）")
    tampered3 = src_uncond.replace(
        anchor_line,
        ("    (hdom1 : lam1 * frob (Y * Yᵀ - X * Xᵀ) / lam3^2 ≤ 1 / 2)\n"
         + hdpar_premise
         + "    :\n    ∃ Q ∈ Matrix.orthogonalGroup n ℝ,\n"), 1)
    try:
        gate4_core(tampered3)
        raise GateFail("NC2 失守：注入 hdpar 前提后无 hdpar 机器锚未报错"
                       "（D82-3 核心面失效）")
    except GateFail as e:
        if "无 hdpar 锚失守" not in str(e):
            raise
        print(f"[gate][NC2 检出·棱三] {e}")
    gate4_core(src_uncond)          # sanity：原文件 PASS
    okmsg("NC2 篡陈述必被 G4 拦（三棱）：√(3*→√(4*)（路线 B 头条常数面）与"
          "2√2→3√2（路线 A 头条常数面）均检出锚缺失；**向无条件头条注入 hdpar"
          " 前提文本必被无 hdpar 锚拦（D82 裁决 3 核心：防『条件定理改名冒充』"
          "与『前提走私』）**；原文件 sanity PASS")


def nc3_wrong_engine() -> None:
    # ① D_⊥ 换未投影 M 代入块恒等式复核 ⇒ 必被检出
    try:
        check_uncond_identities(SEED_GATE + 1, wrong_dperp=True)
        raise GateFail("NC3① 失守：未投影 M 未触发检出（不可达）")
    except GateFail as e:
        if "NC3 预期检出" not in str(e):
            raise
        print(f"[gate][NC3 检出·棱一] {e}")
    # ② 常数链篡 3→4（trace-CS/Hölder 因子）⇒ 必被检出
    try:
        check_constants(const_tamper=4)
        raise GateFail("NC3② 失守：常数链篡 3→4 未触发检出（不可达）")
    except GateFail as e:
        if "NC3 预期检出" not in str(e):
            raise
        print(f"[gate][NC3 检出·棱二] {e}")
    okmsg("NC3 错误引擎必被 G5 拦（双棱）：D_⊥ 换未投影 M 的块恒等式复核必 FAIL＋"
          "常数链篡 3→4（网格 Hölder 因子 √(4√72Up·δ) 对真 C_B）必 FAIL")


# ------------------------------------------------------------------ main
def main() -> None:
    t0 = time.time()
    print(f"[gate] r19_b5u_gate.py seed={SEED_GATE}（确定性；随机实例为 seed 复放）")
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
    if not UNCOND_LEAN.is_file():
        fail(f"产出件不在场：{UNCOND_LEAN}")
    src_uncond = UNCOND_LEAN.read_text()

    led = gate0_ledger()
    gate1_ownership()
    walls = gate2_elaborate()
    g3 = gate3_axioms(src_uncond)
    gate4_statement(src_uncond)
    gate5_offline(led)
    nc1_sorry_injection(src_uncond)
    nc2_statement_tamper(src_uncond)
    nc3_wrong_engine()
    print(f"[gate] G2 elaboration 墙钟：Data {walls['data']}s＋B5 {walls['b5']}s＋"
          f"Core {walls['core']}s＋Trace {walls['trace']}s＋Polar {walls['polar']}s＋"
          f"Uncond {walls['uncond']}s（均 ≤ {ELAB_LIMIT_S}s）；"
          f"G3 定理 {g3['theorems']} 件")


if __name__ == "__main__":
    main()
