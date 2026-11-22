#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r16_b5a_gate.py — R16A 表 B 第四件 B5a（B5 解析本体步骤 1–2 纯代数层）验收门
（G0–G5＋负对照 NC1/NC2/NC3）.

任务书口径（r16a-tableb-b5a，D67 裁决 1；预研 notes/b5-core-study.md §5 切分）：
B5a＝l4_procrustes.py 证明步骤 1–2 的 Lean 化——E 三交叉分解＋对角恒 0＋
η ≤ √72·δ（步骤 1）＋投影分解＋P₀ 幂等/对称＋S 可逆前提桥＋TTP 实例化推论
（步骤 2）。步骤 3–6（trace/范数压缩/极分解/装配）不在件内（B5b/B5c 边界，
docstring 双侧声明）。开工前置三探针（§2.4 六项未跑 API 中 B5a 相关①②⑤，
D67 分叉裁决）已跑并转录 notes/tableb-lean.md §4（三档判定＋/tmp 日志留档）。
产出件 formal/lean/ThomsonN9/TableB5Core.lean（手写主件 16 定理，import
Mathlib＋ThomsonN9.TableB5，零数值数据字面量故无 Data 件）。本门全确定性
（随机实例 seed 20261017 复放；PATH 自动前置 ~/.elan/bin）；CWD 无关（全部
路径自 __file__ 推导）。heavySolves=0（本门零求解：仅 elaboration/公理/
regex/Fraction 复核）。

检查面（对应任务书 G0–G5＋NC1/NC2/NC3）：
  G0 账本在场与受控字段（seed == 20261017、heavy_solves == 0、自有六件在清单、
     theorem_count == 16、axiom_policy 恰三标准）。
  G1 文件所有权守卫：git status --porcelain 与 git diff HEAD --name-only 的全部
     改动路径 ⊆ 本任务自有六件（＋环境变量 R16A_G1_ALLOW_FOREIGN 自跑逐件放行
     〔默认关〕＋PARALLEL_FAMILY r16 家族放行层〔r16[a-z0-9_]* pattern＋
     notes/decisions.md＋notes/b5c-spectral-probe.md＋endgame_gate.py＋
     GAP-REPORT/PROGRESS——D61-5/D67 同款〕）；两读件
     formal/lean/ThomsonN9/TableB5.lean 与 TableB5Data.lean 显式 git diff 守卫
     （单独响亮报错）。
  G2 逐文件 elaboration：子进程 `lake env lean -o <olean>` 依赖序三连——
     ThomsonN9/TableB5Data.lean → ThomsonN9/TableB5.lean → ThomsonN9/TableB5Core.lean
     （均 CWD=formal/lean），各 exit 0、输出无 error／无 sorry、墙钟 ≤ 600 s/文件
     （D52 裁决 4：每个 lake 子命令 ≤10 min）；olen 落 .lake/build/lib/lean/
     ThomsonN9/（gitignored），供 G3/NC1 复用。
  G3 公理：检查件 import ThomsonN9.TableB5Core＋对**件内全部 theorem**（regex
     枚举，≥12 预期、账本记精确数）#print axioms——公理集 ⊆ {propext,
     Classical.choice, Quot.sound}，零 sorryAx/ofReduceBool/ofReduceNat/
     trustCompiler。
  G4 语句锚（行级 regex）：import 面恰 [Mathlib＋TableB5]；E 分解／E 对角恒 0／
     η ≤ √72·δ（抽象＋TTP 面两定理，√72 字面锚——NC2 的牙）／投影正交／P₀ 幂等
     ＋对称／夹逼⇒IsUnit 桥／TTP 矩阵 quadform 桥／TTP 可逆推论各定理头＋命题
     形状；ttpX/frob def 锚；零 ≥15 位数字面量＋零『def … : ℚ :=』；非交叠守卫
     （Solution/TableA*/M1Data/TableB1*/TableB6*/TableB5.lean/TableB5Data.lean/
     根模块 ThomsonN9.lean/lakefile.toml/scripts/check.sh 源码零 TableB5Core 引用）。
  G5 离线精确复核（stdlib Fraction 零仓 import，独立第二实现：S⁻¹ Gauss-Jordan
     消去自实现）：seed 20261017 ≥3 个随机有理 9×3 实例（有理单位球参数化
     (t,s)↦((1−t²−s²),2t,2s)/(1+t²+s²)——行单位精确成立）上三矩阵恒等式精确复核：
     (a) E 三交叉分解逐元素（81 元全查）＋对角恒 0；(b) XᵀD_⊥ == 0（9 元全零）；
     (c) P₀ 幂等＋对称（81 元全查）；(d) 72 == 81−9 计数＋η² ≤ 72·δ² 实例复核
     （δ=非对角 |E_ij| 的精确 max）；(e) notes/tableb-lean.md §4 三探针转录锚
     （三档判定标题＋陈述面三决策＋六 /tmp 日志路径在文）。
  NC1 注入 sorry 必被 G3 拦：/tmp 副本把 gram_transpose 证明改 sorry → 独立编译
     （lean --root＋LEAN_PATH 前置副本目录）必现 sorry 警告＋公理检查必现
     sorryAx → G3 判定逻辑必 FAIL（未篡原件 sanity：G3 全 16 件过）。
  NC2 篡陈述必被 G4 拦：/tmp 副本把 Real.sqrt 72 → Real.sqrt 71 → G4 语句锚
     regex 必 FAIL（√72 字面锚有牙实证；原文件 sanity PASS）。
  NC3 门内 Fraction 引擎换错误投影定义（A := Xᵀ*D 去 S⁻¹）⇒ 恒等式复核必 FAIL
     （防假拦截：篡引擎在固定实例上 XᵀD_⊥' ≠ 0 必被检出）。

用法（CWD 无关）：
  python3 numerics/bounds/r16_b5a_gate.py     # 全门（exit 0 = 过）
  python3 thomson-n9/numerics/bounds/r16_b5a_gate.py
      # ↑ CWD＝仓库根时的验收命令命中同名 runpy 包装器（沿 R10A 0087eab／
      #   R12B 5237fe5／R13C r13_a1／R14A r14_b5 先例，包装器重定向到真实门）
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

SEED_GATE = 20261017                  # R16 各门统一 seed（D67）
ELAB_LIMIT_S = 600                    # G2 每文件 ≤10 min（D52 裁决 4）

CORE_REL = "formal/lean/ThomsonN9/TableB5Core.lean"
GATE_REL = "numerics/bounds/r16_b5a_gate.py"
WRAPPER_REL = "thomson-n9/numerics/bounds/r16_b5a_gate.py"   # CWD 兼容包装器
LEDGER_REL = "numerics/bounds/results/r16_b5a_ledger.json"
NOTES_REL = "notes/tableb-lean.md"
DECISIONS_REL = "notes/decisions.md"
OWNED = {CORE_REL, GATE_REL, WRAPPER_REL, LEDGER_REL, NOTES_REL, DECISIONS_REL}

# 两只读件（R14 常数件）：显式 git diff 守卫（独立于放行层，单独响亮报错）
FROZEN_READONLY = ("formal/lean/ThomsonN9/TableB5.lean",
                   "formal/lean/ThomsonN9/TableB5Data.lean")

# 并行家族放行集（D61-5/D67 同款：r16 家族 pattern＋轮次文档三件＋收口门＋
# R16B 并行 notes 件——本任务与 R16B/R16C 文件集零交叠，D67 裁决 3）。
PARALLEL_FAMILY = [
    r"^numerics/bounds/r16[a-z0-9_]*(\.py|/)",
    r"^numerics/bounds/results/r16[a-z0-9_]*(\.json|/)",
    r"^thomson-n9/numerics/bounds/r16[a-z0-9_]*(\.py|/)",
    r"^notes/decisions\.md$",
    r"^notes/b5c-spectral-probe\.md$",
    r"^numerics/bounds/endgame_gate\.py$",
    r"^(GAP-REPORT|PROGRESS)\.md$",
]

# 非交叠守卫面（表 A/M1/Solution 面＋表 B 其余件＋根模块/lake 面，零交叠机器化）
NONOVERLAY_FILES = ("ThomsonN9/Solution.lean", "ThomsonN9/TableA.lean",
                    "ThomsonN9/TableA1.lean", "ThomsonN9/TableA3.lean",
                    "ThomsonN9/TableA4.lean", "ThomsonN9/TableA6.lean",
                    "ThomsonN9/M1Data.lean", "ThomsonN9/TableB1.lean",
                    "ThomsonN9/TableB1Data.lean", "ThomsonN9/TableB6.lean",
                    "ThomsonN9/TableB6Data.lean", "ThomsonN9/TableB5.lean",
                    "ThomsonN9/TableB5Data.lean", "ThomsonN9.lean",
                    "lakefile.toml", "scripts/check.sh")

TMP = Path("/tmp/r16_b5a_gate")
OLEAN_REL = ".lake/build/lib/lean/ThomsonN9"
CORE_LEAN = LEAN_DIR / "ThomsonN9" / "TableB5Core.lean"
LEDGER = RESULTS / "r16_b5a_ledger.json"
NOTES = REPO / "notes" / "tableb-lean.md"

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
    if led.get("data", {}).get("theorem_count") != 16:
        fail(f"G0 账本 theorem_count 失配："
             f"{led.get('data', {}).get('theorem_count')!r} != 16")
    if led.get("axiom_policy") != sorted(ALLOWED_AXIOMS):
        fail(f"G0 账本 axiom_policy 失配：{led.get('axiom_policy')!r} != "
             f"{sorted(ALLOWED_AXIOMS)}")
    okmsg(f"G0 账本在场（seed={SEED_GATE}，heavy_solves=0，自有件{len(OWNED)}"
          "全在清单，theorem_count=16，axiom_policy 恰三标准）")
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
    # 三层放行：① OWNED（本任务六件）；② 环境变量 R16A_G1_ALLOW_FOREIGN（自跑
    # 专用逐件放行，默认关）；③ PARALLEL_FAMILY pattern（r16 家族，D61-5/D67）。
    # 三层之外字面拦截。
    allow_foreign = {q.strip() for q in
                     os.environ.get("R16A_G1_ALLOW_FOREIGN", "").split(",") if q.strip()}
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
                print(f"[gate][G1][并行家族放行] r16 家族在途件（D61-5/D67 pattern）：{p}")
                continue
            raise GateFail(
                f"G1 树上出现非本任务自有件（{cmd[1]}）：{p!r}"
                f"（自有集={sorted(OWNED)}；r16 家族放行层未覆盖该路径——"
                f"若确系并行在途件，可设 R16A_G1_ALLOW_FOREIGN={p} 显式放行）")
    # 两只读件守卫（显式单列，响亮报错；独立于放行集）
    for rel in FROZEN_READONLY:
        r = run(["git", "diff", "HEAD", "--", rel], REPO)
        if r.returncode != 0 or r.stdout.strip():
            fail(f"G1 只读守卫失守：{rel} 相对 HEAD 有改动"
                 "（TableB5.lean/TableB5Data.lean 为 R14 常数件冻结只读面）")
    okmsg("G1 文件所有权守卫：git status/diff 相对 HEAD 仅自有六件／r16 家族放行件"
          "（或全净）；TableB5.lean 与 TableB5Data.lean 只读守卫空 diff")


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
    # 依赖序三连：TableB5Data → TableB5 → TableB5Core（前两件为 R14 冻结件，
    # 重编译取 olean 供 import；TableB5Core 为本件）。
    wall_d = compile_lean("ThomsonN9/TableB5Data.lean", "TableB5Data.olean")
    okmsg(f"G2 elaboration：TableB5Data.lean exit 0 无 error/sorry（{wall_d:.1f}s ≤ 600s）")
    wall_5 = compile_lean("ThomsonN9/TableB5.lean", "TableB5.olean")
    okmsg(f"G2 elaboration：TableB5.lean exit 0 无 error/sorry（{wall_5:.1f}s ≤ 600s）")
    wall_c = compile_lean("ThomsonN9/TableB5Core.lean", "TableB5Core.olean")
    okmsg(f"G2 elaboration：TableB5Core.lean exit 0 无 error/sorry（{wall_c:.1f}s ≤ 600s；"
          "三件依赖序编译，olen 落 .lake/build 供 G3/NC1 复用）")
    return {"data_s": round(wall_d, 1), "b5_s": round(wall_5, 1), "core_s": round(wall_c, 1)}


# ------------------------------------------------------------------ G3
def parse_axiom_lines(out: str) -> dict:
    ax = {}
    for line in out.splitlines():
        m = re.match(r"'([^']+)'\s+(?:does not depend on any axioms"
                     r"|depends on axioms:\s*\[(.*)\])", line.strip())
        if m:
            ax[m.group(1)] = ({a.strip() for a in m.group(2).split(",")}
                              if m.group(2) is not None else set())
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
    return ("import ThomsonN9.TableB5Core\n"
            + "".join(f"#print axioms {t}\n" for t in names))


def gate3_axioms(src_core: str) -> dict:
    names = [f"ThomsonN9.TableB5Core.{t}" for t in theorem_names(src_core)]
    if len(names) < 12:
        fail(f"G3 定理枚举偏少：{len(names)}（任务书预期 ≥12、账本记 16）")
    if len(names) != 16:
        fail(f"G3 定理数与账本失配：{len(names)} != 16")
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
            ["import Mathlib", "import ThomsonN9.TableB5"]:
        fail("G4 TableB5Core.lean import 行失配（应恰为 "
             "[import Mathlib, import ThomsonN9.TableB5]）")
    anchors = [
        # ---- def 锚
        (r"^noncomputable def frob \{m n : Type\} \[Fintype m\] \[Fintype n\]", "frob def 锚"),
        (r"^noncomputable def ttpX \(z : ℝ\) : Matrix \(Fin 9\) \(Fin 3\) ℝ :=", "ttpX def 锚（陈述面决策 1：Fin 9 × Fin 3）"),
        (r"^noncomputable def ttpRow \(z : ℝ\) : ℕ → Fin 3 → ℝ", "ttpRow def 锚"),
        # ---- 步骤 1
        (r"theorem E_decomp \{m n : Type\} \[Fintype m\] \[Fintype n\] \(X Y : Matrix m n ℝ\) :", "E 分解定理头锚"),
        (r"Y \* Yᵀ - X \* Xᵀ = X \* \(Y - X\)ᵀ \+ \(Y - X\) \* Xᵀ \+ \(Y - X\) \* \(Y - X\)ᵀ", "E 分解命题形状锚（三交叉恒等式）"),
        (r"theorem E_diag_zero \{m n : Type\} \[Fintype m\] \[Fintype n\] \(X Y : Matrix m n ℝ\)", "E 对角恒 0 定理头锚"),
        (r"\(Y \* Yᵀ - X \* Xᵀ\) i i = 0", "E 对角恒 0 命题形状锚"),
        (r"theorem frob_le_of_off_diag \(E : Matrix \(Fin 9\) \(Fin 9\) ℝ\) \(δ : ℝ\)", "η ≤ √72·δ 抽象版定理头锚"),
        (r"frob E ≤ Real\.sqrt 72 \* δ", "η ≤ √72·δ 抽象版命题形状锚（√72 字面）"),
        (r"theorem eta_le_sqrt72 \(X Y : Matrix \(Fin 9\) \(Fin 3\) ℝ\) \(δ : ℝ\)", "η ≤ √72·δ TTP 面定理头锚"),
        (r"frob \(Y \* Yᵀ - X \* Xᵀ\) ≤ Real\.sqrt 72 \* δ", "η ≤ √72·δ TTP 面命题形状锚（√72 字面——NC2 牙）"),
        # ---- 步骤 2
        (r"theorem proj_orth \(X D : Matrix \(Fin 9\) \(Fin 3\) ℝ\) \(hS : IsUnit \(Xᵀ \* X\)\) :", "投影正交定理头锚"),
        (r"Xᵀ \* \(D - X \* \(\(Xᵀ \* X\)⁻¹ \* Xᵀ \* D\)\) = 0", "投影正交命题形状锚（XᵀD_⊥=0）"),
        (r"theorem P0_mul_self \(X : Matrix \(Fin 9\) \(Fin 3\) ℝ\) \(hS : IsUnit \(Xᵀ \* X\)\) :", "P₀ 幂等定理头锚"),
        (r"\(X \* \(Xᵀ \* X\)⁻¹ \* Xᵀ\) \* \(X \* \(Xᵀ \* X\)⁻¹ \* Xᵀ\) = X \* \(Xᵀ \* X\)⁻¹ \* Xᵀ", "P₀ 幂等命题形状锚"),
        (r"theorem P0_transpose \(X : Matrix \(Fin 9\) \(Fin 3\) ℝ\) :", "P₀ 对称定理头锚"),
        (r"\(X \* \(Xᵀ \* X\)⁻¹ \* Xᵀ\)ᵀ = X \* \(Xᵀ \* X\)⁻¹ \* Xᵀ", "P₀ 对称命题形状锚"),
        (r"theorem sandwich_isUnit \{n : Type\} \[Fintype n\] \[DecidableEq n\] \{S : Matrix n n ℝ\}", "夹逼⇒IsUnit 桥定理头锚"),
        (r"\(h : ∀ v : n → ℝ, l \* \(v ⬝ᵥ v\) ≤ v ⬝ᵥ \(S \*ᵥ v\)\) :\n    IsUnit S", "夹逼⇒IsUnit 桥命题形状锚"),
        # ---- TTP 实例化
        (r"theorem ttpX_quadform \(z : ℝ\) \(v : Fin 3 → ℝ\) :", "TTP quadform 桥定理头锚"),
        (r"v ⬝ᵥ \(\(\(ttpX z\)ᵀ \* ttpX z\) \*ᵥ v\) = TableB5\.ttpQ z \(v 0\) \(v 1\) \(v 2\)", "TTP quadform 桥命题形状锚"),
        (r"theorem ttpX_isUnit \(z : ℝ\) \(h1 : \(zLo:ℝ\) ≤ z\) \(h2 : z ≤ \(zHi:ℝ\)\) :", "TTP 可逆推论定理头锚"),
        (r"IsUnit \(\(ttpX z\)ᵀ \* ttpX z\)", "TTP 可逆推论命题形状锚"),
    ]
    for pat, name in anchors:
        if not re.search(pat, src, re.M):
            fail(f"G4 语句锚缺失：{name}（pattern {pat!r}）")
    # 零 ≥15 位数字面量（数值数据面；Fin 9/Fin 3/72 等结构数不在列）
    long_lits = re.findall(r"\d{15,}", src)
    if long_lits:
        fail(f"G4 零 ≥15 位数字面量失守：{long_lits[:3]}")
    # 零『def … : ℚ :=』（无 Data 件口径）
    if re.findall(r"^def \w+ : ℚ :=", src, re.M):
        fail("G4 零『def … : ℚ :=』失守（本件零数值数据字面量，无 Data 件）")


def gate4_statement(src_core: str) -> None:
    gate4_core(src_core)
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
        if p.is_file() and "TableB5Core" in p.read_text():
            fail(f"G4 非交叠守卫：{rel} 含 'TableB5Core'（本件必须不被表 A/M1/"
                 "Solution/表 B 其余件/根模块/lake 面引用）")
    okmsg("G4 语句锚：import 面恰 [Mathlib＋TableB5]；23 锚全在（九定理族头＋命题"
          "形状，√72 双字面锚）＋3 def 锚；零 ≥15 位数字面量＋零 ℚ def；非交叠面"
          "（Solution/TableA*/M1Data/TableB1*/TableB6*/TableB5 双件/根模块/"
          "lakefile/check.sh）零 TableB5Core 引用")


# ------------------------------------------------------------------ G5 门内独立第二实现（Fraction 引擎）
def mat_mul(A, B):
    n, k, m = len(A), len(B), len(B[0])
    return [[sum(A[i][t] * B[t][j] for t in range(k)) for j in range(m)]
            for i in range(n)]


def mat_sub(A, B):
    return [[A[i][j] - B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def mat_T(A):
    return [[A[i][j] for i in range(len(A))] for j in range(len(A[0]))]


def mat_eq0(A):
    return all(x == 0 for row in A for x in row)


def mat_add(A, B):
    return [[A[i][j] + B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def gauss_inv3(S):
    """3×3 Fraction 矩阵 Gauss-Jordan 求逆（门内独立自实现，零仓 import）。"""
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


def unit_row(t, s):
    """有理单位球参数化：((1−t²−s²), 2t, 2s)/(1+t²+s²)——行单位精确成立。"""
    d = 1 + t * t + s * s
    return [(1 - t * t - s * s) / d, (2 * t) / d, (2 * s) / d]


def gen_instance(rng):
    """随机有理 9×3 双构型（X/Y 各 9 行，全部行单位精确）。"""
    def rows():
        return [unit_row(Fr(rng.randint(-12, 12), 8), Fr(rng.randint(-12, 12), 8))
                for _ in range(9)]
    return rows(), rows()


def check_identities(X, Y, wrong_projection=False):
    """三矩阵恒等式精确复核（wrong_projection=True 为 NC3 篡引擎：
    A := Xᵀ*D 去 S⁻¹——恒等式复核必 FAIL）。"""
    D = mat_sub(Y, X)
    XT, DT = mat_T(X), mat_T(D)
    E = mat_sub(mat_mul(Y, mat_T(Y)), mat_mul(X, XT))
    # (a) E 三交叉分解逐元素（81 元全查）＋对角恒 0：X·Dᵀ + D·Xᵀ + D·Dᵀ
    XD_T = mat_mul(X, DT)
    DX_T = mat_mul(D, XT)
    DD_T = mat_mul(D, DT)
    decomp = [[XD_T[i][j] + DX_T[i][j] + DD_T[i][j] for j in range(9)] for i in range(9)]
    for i in range(9):
        for j in range(9):
            if E[i][j] != decomp[i][j]:
                fail(f"G5(a) E 三交叉分解失守 @({i},{j})：{E[i][j]} != {decomp[i][j]}")
        if E[i][i] != 0:
            fail(f"G5(a) E 对角恒 0 失守 @({i},{i})：{E[i][i]}")
    # (d) η² ≤ 72·δ²（δ=非对角 |E_ij| 精确 max）
    delta = max(abs(E[i][j]) for i in range(9) for j in range(9) if i != j)
    eta_sq = sum(E[i][j] * E[i][j] for i in range(9) for j in range(9))
    if not eta_sq <= Fr(72) * delta * delta:
        fail(f"G5(d) η² ≤ 72·δ² 实例复核失守：{eta_sq} > 72·{delta}²")
    # (b) XᵀD_⊥ == 0（NC3 篡引擎：A := Xᵀ*D 去 S⁻¹ ⇒ XᵀD_⊥' ≠ 0 必被检出）
    S = mat_mul(XT, X)
    Sinv = gauss_inv3(S)
    eye = [[F1 if i == j else F0 for j in range(3)] for i in range(3)]
    if mat_mul(S, Sinv) != eye or mat_mul(Sinv, S) != eye:
        fail("G5(b) Gauss-Jordan 逆自检失守（S·S⁻¹ ≠ I 或 S⁻¹·S ≠ I）")
    A = (mat_mul(XT, D)) if wrong_projection else mat_mul(Sinv, mat_mul(XT, D))
    Dperp = mat_sub(D, mat_mul(X, A))
    XTDperp = mat_mul(XT, Dperp)
    if not mat_eq0(XTDperp):
        if wrong_projection:
            fail("NC3 预期检出：错误投影（A := XᵀD 去 S⁻¹）下 XᵀD_⊥' ≠ 0"
                 "（防假拦截实证——恒等式复核必 FAIL）")
        fail(f"G5(b) XᵀD_⊥ == 0 失守：{XTDperp}")
    if wrong_projection:
        fail("NC3 失守：错误投影定义（A := XᵀD 去 S⁻¹）下 XᵀD_⊥' 仍为 0"
             "（防假拦截断言失败）")
    # (c) P₀ 幂等＋对称（81 元全查）
    P0 = mat_mul(X, mat_mul(Sinv, XT))
    P0sq = mat_mul(P0, P0)
    P0T = mat_T(P0)
    for i in range(9):
        for j in range(9):
            if P0sq[i][j] != P0[i][j]:
                fail(f"G5(c) P₀ 幂等失守 @({i},{j})")
            if P0T[i][j] != P0[i][j]:
                fail(f"G5(c) P₀ 对称失守 @({i},{j})")


NOTES_ANCHORS = [
    "探针① posDef_iff_isUnit／posDef_iff_det_ne_zero 使用级——【档位：现成】",
    "探针② 二次型夹逼 ⇒ PosDef ⇒ IsUnit 桥——【档位：现成（预研『未定位』消解）】",
    "探针⑤ ‖M·Q‖_F = ‖M‖_F（Q 正交）直接引理——【档位：缺位（直接引理未定位）】",
    "B5a 全链陈述面三决策",
    "/tmp/r16a_probe1_posdef.log", "/tmp/r16a_probe2_bridge.log",
    "/tmp/r16a_probe5_orth.log", "/tmp/r16a_probe5_grep.log",
]


def gate5_offline() -> dict:
    rng = random.Random(SEED_GATE)
    # (d) 72 == 81 − 9 计数（9×9 元对角 9 个为零，非对角恰 72 个）
    if 81 - 9 != 72:
        fail("G5(d) 72 == 81−9 计数失守")
    off_diag_pairs = sum(1 for i in range(9) for j in range(9) if i != j)
    if off_diag_pairs != 72:
        fail(f"G5(d) 非对角元计数失守：{off_diag_pairs} != 72")
    for k in range(3):
        X, Y = gen_instance(rng)
        for name, M in (("X", X), ("Y", Y)):
            for i, row in enumerate(M):
                n2 = sum(c * c for c in row)
                if n2 != 1:
                    fail(f"G5 随机场构造失守：{name}[{i}] 行单位 ≠ 1（{n2}）")
        check_identities(X, Y)
        okmsg(f"G5 实例 {k}（seed 复放）：E 分解 81 元全对＋对角 0＋XᵀD_⊥==0＋"
              "P₀ 幂等/对称 81 元全对＋η² ≤ 72δ²")
    # (e) notes §4 三探针转录锚
    notes = NOTES.read_text()
    for anc in NOTES_ANCHORS:
        if anc not in notes:
            fail(f"G5(e) notes/tableb-lean.md §4 转录锚缺失：{anc!r}")
    okmsg("G5 离线精确复核：3 随机有理 9×3 实例（有理单位球参数化）三矩阵恒等式"
          "Fraction 精确复核全过（独立 Gauss-Jordan S⁻¹）＋72==81−9 计数＋"
          "notes §4 三探针转录锚 7 处在文")
    return {"instances": 3}


# ------------------------------------------------------------------ NC
def nc1_sorry_injection(src_core: str) -> None:
    target = "    (Xᵀ * X)ᵀ = Xᵀ * X := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]"
    tampered = src_core.replace(
        target,
        "    (Xᵀ * X)ᵀ = Xᵀ * X := by sorry")
    if tampered == src_core:
        fail(f"NC1 预置失败：未能在 /tmp 副本注入 sorry（源码缺目标行 {target!r}）")
    d = TMP / "nc1"
    (d / "ThomsonN9").mkdir(parents=True, exist_ok=True)
    (d / "ThomsonN9" / "TableB5Core.lean").write_text(tampered)
    # 依赖 olen 随副本落 root（TableB5Core imports ThomsonN9.TableB5 →
    # TableB5Data；--root 下 import 先查 root，无 olen 即报缺——G2 已编译
    # 这两个冻结件的 olen，拷入副本 root 使篡件可独立编译）
    for dep in ("TableB5Data.olean", "TableB5.olean"):
        src = LEAN_DIR / OLEAN_REL / dep
        if not src.is_file():
            fail(f"NC1 预置失败：依赖 olen 不在场（G2 应已编译）：{src}")
        (d / "ThomsonN9" / dep).write_bytes(src.read_bytes())
    lp = run(["lake", "env", "printenv", "LEAN_PATH"], LEAN_DIR).stdout.strip()
    env = gate_env()
    env["LEAN_PATH"] = f"{d}:{lp}"
    b = subprocess.run(["lean", "--root", str(d), "-o",
                        str(d / "ThomsonN9" / "TableB5Core.olean"),
                        str(d / "ThomsonN9" / "TableB5Core.lean")],
                       cwd=str(LEAN_DIR), env=env, capture_output=True, text=True,
                       timeout=605)
    if b.returncode != 0 or "declaration uses `sorry`" not in (b.stdout + b.stderr):
        fail(f"NC1 注入 sorry 后编译未产生 sorry 警告（exit {b.returncode}）：\n"
             f"{(b.stdout + b.stderr)[-500:]}")
    axfile = d / "axcheck.lean"
    axfile.write_text("import ThomsonN9.TableB5Core\n"
                      "#print axioms ThomsonN9.TableB5Core.gram_transpose\n")
    a = subprocess.run(["lean", str(axfile)], cwd=str(LEAN_DIR), env=env,
                       capture_output=True, text=True, timeout=605)
    ax = parse_axiom_lines(a.stdout)
    th = "ThomsonN9.TableB5Core.gram_transpose"
    caught = th in ax and ("sorryAx" in ax[th] or (ax[th] - ALLOWED_AXIOMS))
    if not caught:
        fail(f"NC1 失守：注入 sorry 后公理检查未现 sorryAx（{ax}）")
    okmsg(f"NC1 注入 sorry 必被 G3 拦：篡件 gram_transpose 公理集 = "
          f"{sorted(ax.get(th, set()))}（含 sorryAx → G3 FAIL）")


def nc2_statement_tamper(src_core: str) -> None:
    tampered = src_core.replace("Real.sqrt 72", "Real.sqrt 71")
    if tampered == src_core:
        raise GateFail("NC2 预置失败：篡改未生效（源码无 Real.sqrt 72 字面）")
    try:
        gate4_core(tampered)
        raise GateFail("NC2 失守：篡陈述（√72→√71）后 G4 语句锚未报错")
    except GateFail as e:
        if "语句锚缺失" not in str(e):
            raise
        print(f"[gate][NC2 检出] {e}")
    gate4_core(src_core)             # sanity：原文件 PASS
    okmsg("NC2 篡陈述（Real.sqrt 72 → Real.sqrt 71）必被 G4 拦：√72 双字面锚"
          "（抽象版＋TTP 面）检出缺失；原文件 sanity PASS")


def nc3_wrong_projection() -> None:
    rng = random.Random(SEED_GATE)   # 同 seed 复放实例 0
    X, Y = gen_instance(rng)
    try:
        check_identities(X, Y, wrong_projection=True)
        raise GateFail("NC3 失守：错误投影定义未触发检出（不可达：检出已在引擎内拦）")
    except GateFail as e:
        if "NC3 预期检出" not in str(e):
            raise
        print(f"[gate][NC3 检出] {e}")
    okmsg("NC3 门内 Fraction 引擎换错误投影定义（A 去 S⁻¹）⇒ XᵀD_⊥' ≠ 0 必被"
          "恒等式复核检出（防假拦截断言过）")


# ------------------------------------------------------------------ main
def main() -> None:
    t0 = time.time()
    print(f"[gate] r16_b5a_gate.py seed={SEED_GATE}（确定性；随机实例为 seed 复放）")
    try:
        run_gate()
    except GateFail as e:
        print(f"[gate][FAIL] {e}", flush=True)
        sys.exit(1)
    wall = time.time() - t0
    print(f"[gate] PASS（{wall:.1f}s）——exit 0")
    print("[gate] heavySolves=0（本门零求解：仅 elaboration/公理/regex/Fraction 复核）")


def run_gate() -> None:
    require_toolchain()
    if not CORE_LEAN.is_file():
        fail(f"产出件不在场：{CORE_LEAN}")
    src_core = CORE_LEAN.read_text()

    gate0_ledger()
    gate1_ownership()
    walls = gate2_elaborate()
    g3 = gate3_axioms(src_core)
    gate4_statement(src_core)
    gate5_offline()
    nc1_sorry_injection(src_core)
    nc2_statement_tamper(src_core)
    nc3_wrong_projection()
    print(f"[gate] G2 elaboration 墙钟：Data {walls['data_s']}s＋B5 {walls['b5_s']}s＋"
          f"Core {walls['core_s']}s（均 ≤ {ELAB_LIMIT_S}s）；G3 定理 {g3['theorems']} 件")


if __name__ == "__main__":
    main()
