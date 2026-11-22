#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r17_b5b_gate.py — R17A 表 B 第五件 B5b trace 件（l4_procrustes.py 步骤 3–4
trace/范数压缩层 Lean 化）验收门（G0–G5＋负对照 NC1/NC2/NC3）.

任务书口径（r17a-tableb-b5b，D72 裁决 1；预研 notes/b5-core-study.md §5 切分）：
B5b＝l4_procrustes.py 证明步骤 3–4 的 Lean 化——T1/T2 PSD trace 族＋
Frobenius↔trace 桥＋块分解恒等式＋Frobenius-Pythagoras＋头条一
`(√λ₃ − frob D_∥)·frob D_⊥ ≤ frob E`（步骤 3 收口）＋B 三恒等式＋逆压缩
（向量层 ‖S⁻¹v‖ ≤ ‖v‖/λ₃＋Frobenius 层 ‖S⁻¹MS⁻¹‖_F ≤ ‖M‖_F/λ₃²）＋头条二
`frob B ≤ λ₁·frob E/λ₃²`（步骤 4 收口＝β 口径）＋TTP 实例化四件。
步骤 1–2 在 TableB5Core（B5a 只读冻结件）；步骤 5–6 不在件内（B5c 边界，
docstring 双侧声明）。开工前置探针四组（D72 分叉裁决）已跑并转录
notes/tableb-lean.md §5（三档判定＋/tmp 日志留档；探针②三备选路线实测
判定采用路线 (a) 列压缩）。产出件 formal/lean/ThomsonN9/TableB5Trace.lean
（手写主件 44 定理＋vecNorm def，import Mathlib＋TableB5＋TableB5Core，
零数值数据字面量故无 Data 件）。本门全确定性（随机实例 seed 20261017 复放；
PATH 自动前置 ~/.elan/bin）；CWD 无关（全部路径自 __file__ 推导）。
heavySolves=0（本门零求解：仅 elaboration/公理/regex/Fraction 复核）。

检查面（对应任务书 G0–G5＋NC1/NC2/NC3）：
  G0 账本在场与受控字段（seed == 20261017、heavy_solves == 0、自有六件在清单、
     theorem_count == 44、axiom_policy 恰三标准列表形态 set 相等）。
  G1 文件所有权守卫：git status --porcelain 与 git diff HEAD --name-only 的全部
     改动路径 ⊆ 本任务自有六件（＋环境变量 R17A_G1_ALLOW_FOREIGN 自跑逐件放行
     〔默认关〕＋PARALLEL_FAMILY r17 家族放行层〔r17[a-z0-9_]* pattern＋
     notes/b5c-assembly-probe.md＋endgame_gate.py＋GAP-REPORT/PROGRESS＋
     notes/decisions.md——D68-3/D72 同款，覆盖 R17B/R17C 在途件〕）；三只读件
     TableB5.lean/TableB5Data.lean/TableB5Core.lean 显式 git diff 守卫
     （单独响亮报错）。
  G2 逐文件 elaboration：子进程 `lake env lean -o <olean>` 依赖序四连——
     ThomsonN9/TableB5Data.lean → ThomsonN9/TableB5.lean →
     ThomsonN9/TableB5Core.lean → ThomsonN9/TableB5Trace.lean
     （均 CWD=formal/lean），各 exit 0、输出无 error／无 sorry、墙钟 ≤ 600 s/文件
     （D52 裁决 4：每个 lake 子命令 ≤10 min）；olen 落 .lake/build/lib/lean/
     ThomsonN9/（gitignored），供 G3/NC1 复用。
  G3 公理：检查件 import ThomsonN9.TableB5Trace＋对**件内全部 theorem**（regex
     枚举，≥12 预期、账本记精确数 44）#print axioms——公理集 ⊆ {propext,
     Classical.choice, Quot.sound}，零 sorryAx/ofReduceBool/ofReduceNat/
     trustCompiler。
  G4 语句锚（行级 regex）：import 面恰 [Mathlib＋TableB5＋TableB5Core]；T1/T2
     trace 族（定理头＋命题形状）／Frobenius↔trace 桥（frob_sq_eq_trace＋
     X*D_ᵀ 面）／Frobenius-Pythagoras 双口径／块分解恒等式（P₀*E*(1−P₀) 形状）／
     头条一（√λ₃ 字面牙）／B 三恒等式／列压缩主件／逆压缩向量层（/λ₃ 牙）／
     逆压缩 Frobenius 层（/λ₃² 指数牙——NC2）／头条二（/λ₃² 指数牙——NC2）／
     TTP 双头条（(l3:ℝ)^2 字面牙——NC2 第二棱）；vecNorm def 锚；零 ≥15 位数字
     字面量＋零『def … : ℚ :=』；非交叠守卫（Solution/TableA*/M1Data/
     TableB1*/TableB6*/根模块 ThomsonN9.lean/lakefile.toml/scripts/check.sh
     源码零 TableB5Trace 引用）。
  G5 离线精确复核（stdlib Fraction 零仓 import，独立第二实现：S⁻¹ Gauss-Jordan
     消去自实现）：seed 20261017 ≥3 个随机有理实例（9×3 双构型有理单位球参数化
     (t,s)↦((1−t²−s²),2t,2s)/(1+t²+s²)）上逐项精确复核：
     (a) PSD 构造 A:=CᵀC（＋t•1 平移）复核 T1（0 ≤ tr(AₚBₚ)）与 T2
         （t*tr(B) ≤ tr(A*B)，A−t•1 = CᵀC 由构造 PSD）；
     (b) frob² == tr(M*Mᵀ) 精确（X/Y/E 三面）；
     (c) 块分解恒等式 P₀*E*(1−P₀) == X*D_⊥ᵀ + D_∥*D_⊥ᵀ 逐元素（81 元全查）；
     (d) Frobenius-Pythagoras（A:=X、B:=D_⊥ 满足 Xᵀ*D_⊥=0：
         frob(A+B)² == frob A²+frob B² 精确）；
     (e) B 三恒等式逐元素（B == (1+A)(1+A)ᵀ−1／XᵀEX == S*B*S／
         B == S⁻¹*(XᵀEX)*S⁻¹，各 9 元全查）；
     (f) 压缩不等式精确复核（S := l₃•1+CᵀC 构造使夹逼由构造成立
         〔vᵀSv − l₃(v⬝v) == ‖Cv‖² ≥ 0 逐向量精确〕、S⁻¹ Gauss-Jordan 自实现、
         无理 σ₃ 走平方化等价比较——‖S⁻¹v‖² ≤ ‖v‖²/λ₃² 与
         frob(S⁻¹MS⁻¹)² ≤ frob(M)²/λ₃⁴，特征值无关实例设计）；
     (g) notes/tableb-lean.md §5 探针转录锚（四节三档判定＋陈述面增量决策＋
         六 /tmp 日志路径在文）。
  NC1 注入 sorry 必被 G3 拦：/tmp 副本把 vecNorm_nonneg 证明改 sorry → 独立编译
     （lean --root＋LEAN_PATH 前置副本目录）必现 sorry 警告＋公理检查必现
     sorryAx → G3 判定逻辑必 FAIL（未篡原件 sanity：G3 全 44 件过）。
  NC2 篡陈述必被 G4 拦（指数面双棱）：/tmp 副本 lam3^2 → lam3^3（抽象面
     frob_inv_mul_inv_le＋step4_bound）与 (l3:ℝ)^2 → (l3:ℝ)^3（TTP 面
     ttpX_step4）→ G4 语句锚 regex 必 FAIL（指数牙有牙实证；原文件 sanity
     PASS）。
  NC3 错误引擎必被 G5 拦（双棱）：(i) A := Xᵀ*D 去 S⁻¹ 的错误投影代入块分解
     恒等式 ⇒ 81 元逐元素复核必 FAIL（防假拦截：篡引擎在固定实例上必被检出）；
     (ii) 单 PSD 前提冒充（A:=I₃ PSD＋B 不定元 diag(0,−1,0)）⇒ T1 复核
     tr(I₃*B) = −1 < 0 必被检出。

用法（CWD 无关）：
  python3 numerics/bounds/r17_b5b_gate.py     # 全门（exit 0 = 过）
  python3 thomson-n9/numerics/bounds/r17_b5b_gate.py
      # ↑ CWD＝仓库根时的验收命令命中同名 runpy 包装器（沿 R10A 0087eab／
      #   R12B 5237fe5／R13C r13_a1／R14A r14_b5／R16A r16_b5a 先例，包装器
      #   重定向到真实门）
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

SEED_GATE = 20261017                  # R17 各门统一 seed（D72/D74）
ELAB_LIMIT_S = 600                    # G2 每文件 ≤10 min（D52 裁决 4）
THEOREM_COUNT = 44                    # 件内定理精确数（regex 枚举＋账本双面）

TRACE_REL = "formal/lean/ThomsonN9/TableB5Trace.lean"
GATE_REL = "numerics/bounds/r17_b5b_gate.py"
WRAPPER_REL = "thomson-n9/numerics/bounds/r17_b5b_gate.py"   # CWD 兼容包装器
LEDGER_REL = "numerics/bounds/results/r17_b5b_ledger.json"
NOTES_REL = "notes/tableb-lean.md"
DECISIONS_REL = "notes/decisions.md"
OWNED = {TRACE_REL, GATE_REL, WRAPPER_REL, LEDGER_REL, NOTES_REL, DECISIONS_REL}

# 三只读冻结件（R14 常数件双件＋R16A B5a 件）：显式 git diff 守卫（独立于
# 放行层，单独响亮报错——D72 裁决 1：TableB5Core 转 R17A 的只读冻结面）。
FROZEN_READONLY = ("formal/lean/ThomsonN9/TableB5.lean",
                   "formal/lean/ThomsonN9/TableB5Data.lean",
                   "formal/lean/ThomsonN9/TableB5Core.lean")

# 并行家族放行集（D68-3/D72 同款：r17 家族 pattern＋轮次文档三件＋收口门＋
# R17B 并行 notes 件——本任务与 R17B/R17C 文件集零交叠，D72 裁决 3）。
PARALLEL_FAMILY = [
    r"^numerics/bounds/r17[a-z0-9_]*(\.py|/)",
    r"^numerics/bounds/results/r17[a-z0-9_]*(\.json|/)",
    r"^thomson-n9/numerics/bounds/r17[a-z0-9_]*(\.py|/)",
    r"^notes/decisions\.md$",
    r"^notes/b5c-assembly-probe\.md$",
    r"^numerics/bounds/endgame_gate\.py$",
    r"^(GAP-REPORT|PROGRESS)\.md$",
]

# 非交叠守卫面（表 A/M1/Solution 面＋表 B 其余件＋根模块/lake 面，零交叠机器化）
NONOVERLAY_FILES = ("ThomsonN9/Solution.lean", "ThomsonN9/TableA.lean",
                    "ThomsonN9/TableA1.lean", "ThomsonN9/TableA3.lean",
                    "ThomsonN9/TableA4.lean", "ThomsonN9/TableA6.lean",
                    "ThomsonN9/M1Data.lean", "ThomsonN9/TableB1.lean",
                    "ThomsonN9/TableB1Data.lean", "ThomsonN9/TableB6.lean",
                    "ThomsonN9/TableB6Data.lean", "ThomsonN9.lean",
                    "lakefile.toml", "scripts/check.sh")

TMP = Path("/tmp/r17_b5b_gate")
OLEAN_REL = ".lake/build/lib/lean/ThomsonN9"
TRACE_LEAN = LEAN_DIR / "ThomsonN9" / "TableB5Trace.lean"
LEDGER = RESULTS / "r17_b5b_ledger.json"
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
    if led.get("data", {}).get("theorem_count") != THEOREM_COUNT:
        fail(f"G0 账本 theorem_count 失配："
             f"{led.get('data', {}).get('theorem_count')!r} != {THEOREM_COUNT}")
    if set(led.get("axiom_policy", [])) != ALLOWED_AXIOMS:
        fail(f"G0 账本 axiom_policy 失配（应恰三标准 set 相等）："
             f"{led.get('axiom_policy')!r} != {sorted(ALLOWED_AXIOMS)}")
    okmsg(f"G0 账本在场（seed={SEED_GATE}，heavy_solves=0，自有件{len(OWNED)}"
          "全在清单，theorem_count=44，axiom_policy 恰三标准 set 相等）")
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
    # 三层放行：① OWNED（本任务六件）；② 环境变量 R17A_G1_ALLOW_FOREIGN（自跑
    # 专用逐件放行，默认关）；③ PARALLEL_FAMILY pattern（r17 家族，D68-3/D72）。
    # 三层之外字面拦截。
    allow_foreign = {q.strip() for q in
                     os.environ.get("R17A_G1_ALLOW_FOREIGN", "").split(",") if q.strip()}
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
                print(f"[gate][G1][并行家族放行] r17 家族在途件（D68-3/D72 pattern）：{p}")
                continue
            raise GateFail(
                f"G1 树上出现非本任务自有件（{cmd[1]}）：{p!r}"
                f"（自有集={sorted(OWNED)}；r17 家族放行层未覆盖该路径——"
                f"若确系并行在途件，可设 R17A_G1_ALLOW_FOREIGN={p} 显式放行）")
    # 三只读件守卫（显式单列，响亮报错；独立于放行集）
    for rel in FROZEN_READONLY:
        r = run(["git", "diff", "HEAD", "--", rel], REPO)
        if r.returncode != 0 or r.stdout.strip():
            fail(f"G1 只读守卫失守：{rel} 相对 HEAD 有改动"
                 "（TableB5/TableB5Data/TableB5Core 为 R14 常数件＋R16A B5a"
                 "冻结只读面）")
    okmsg("G1 文件所有权守卫：git status/diff 相对 HEAD 仅自有六件／r17 家族放行件"
          "（或全净）；TableB5/TableB5Data/TableB5Core 三件只读守卫空 diff")


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
    # 依赖序四连：TableB5Data → TableB5 → TableB5Core → TableB5Trace（前三件为
    # R14/R16A 冻结件，重编译取 olen 供 import；TableB5Trace 为本件）。
    wall_d = compile_lean("ThomsonN9/TableB5Data.lean", "TableB5Data.olean")
    okmsg(f"G2 elaboration：TableB5Data.lean exit 0 无 error/sorry（{wall_d:.1f}s ≤ 600s）")
    wall_5 = compile_lean("ThomsonN9/TableB5.lean", "TableB5.olean")
    okmsg(f"G2 elaboration：TableB5.lean exit 0 无 error/sorry（{wall_5:.1f}s ≤ 600s）")
    wall_c = compile_lean("ThomsonN9/TableB5Core.lean", "TableB5Core.olean")
    okmsg(f"G2 elaboration：TableB5Core.lean exit 0 无 error/sorry（{wall_c:.1f}s ≤ 600s）")
    wall_t = compile_lean("ThomsonN9/TableB5Trace.lean", "TableB5Trace.olean")
    okmsg(f"G2 elaboration：TableB5Trace.lean exit 0 无 error/sorry（{wall_t:.1f}s ≤ 600s；"
          "四件依赖序编译，olen 落 .lake/build 供 G3/NC1 复用）")
    return {"data_s": round(wall_d, 1), "b5_s": round(wall_5, 1),
            "core_s": round(wall_c, 1), "trace_s": round(wall_t, 1)}


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
    return ("import ThomsonN9.TableB5Trace\n"
            + "".join(f"#print axioms {t}\n" for t in names))


def gate3_axioms(src_trace: str) -> dict:
    names = [f"ThomsonN9.TableB5Trace.{t}" for t in theorem_names(src_trace)]
    if len(names) < 12:
        fail(f"G3 定理枚举偏少：{len(names)}（任务书预期 ≥12、账本记 44）")
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
             "import ThomsonN9.TableB5Core"]:
        fail("G4 TableB5Trace.lean import 行失配（应恰为 [import Mathlib, "
             "import ThomsonN9.TableB5, import ThomsonN9.TableB5Core]）")
    anchors = [
        # ---- def 锚（D72-③：vecNorm 自有 def）
        (r"^noncomputable def vecNorm \{n : Type\} \[Fintype n\] \(v : n → ℝ\) : ℝ :=", "vecNorm def 锚"),
        # ---- PSD trace 族（T1/T2——/tmp/r15c_probe3_trace.lean 照搬面）
        (r"theorem trace_mul_nonneg \{n : Type\} \[Fintype n\] \[DecidableEq n\]", "T1 定理头锚"),
        (r"\{A B : Matrix n n ℝ\} \(hA : A\.PosSemidef\) \(hB : B\.PosSemidef\) :\n    0 ≤ \(A \* B\)\.trace", "T1 命题形状锚（双 PSD 前提）"),
        (r"theorem trace_ge_smul \{n : Type\} \[Fintype n\] \[DecidableEq n\]", "T2 定理头锚"),
        (r"\(hA : \(A - t • \(1 : Matrix n n ℝ\)\)\.PosSemidef\) \(hB : B\.PosSemidef\) :\n    t \* B\.trace ≤ \(A \* B\)\.trace", "T2 命题形状锚"),
        # ---- Frobenius↔trace 桥（探针①照搬面）
        (r"theorem frob_sq_eq_trace \{m n : Type\} \[Fintype m\] \[Fintype n\] \(M : Matrix m n ℝ\) :", "frob↔trace 桥定理头锚"),
        (r"\(frob M\)\^2 = \(M \* Mᵀ\)\.trace := by", "frob↔trace 桥命题形状锚"),
        (r"theorem frob_sq_mul_transpose \{m n : Type\} \[Fintype m\] \[Fintype n\]", "X*Dᵀ 面定理头锚"),
        (r"\(frob \(X \* Mᵀ\)\)\^2 = \(\(Xᵀ \* X\) \* \(Mᵀ \* M\)\)\.trace", "X*Dᵀ 面命题形状锚（‖X*D_⊥ᵀ‖²_F = tr(S·D_⊥ᵀD_⊥)）"),
        # ---- Frobenius-Pythagoras 双口径
        (r"theorem frob_sq_add_of_trace \{m n : Type\}", "Pythagoras·trace 形定理头锚"),
        (r"theorem frob_sq_add_of_mul \{m n : Type\} \[Fintype m\] \[Fintype n\]", "Pythagoras·矩阵形定理头锚"),
        (r"\(A B : Matrix m n ℝ\) \(h : Aᵀ \* B = 0\) :\n    \(frob \(A \+ B\)\)\^2 = \(frob A\)\^2 \+ \(frob B\)\^2", "Pythagoras·矩阵形命题形状锚（任务书口径）"),
        # ---- 块分解恒等式（步骤 3）
        (r"theorem mixed_block \{m n : Type\} \[Fintype m\] \[Fintype n\] \[DecidableEq m\]", "块分解恒等式定理头锚"),
        (r"\(X \* \(Xᵀ \* X\)⁻¹ \* Xᵀ\) \* \(Y \* Yᵀ - X \* Xᵀ\) \* \(1 - X \* \(Xᵀ \* X\)⁻¹ \* Xᵀ\)", "块分解 P₀*E*(1−P₀) 命题形状锚"),
        # ---- 头条一（步骤 3 收口；√λ₃ 字面牙）
        (r"theorem step3_bound \{m n : Type\} \[Fintype m\] \[Fintype n\] \[DecidableEq m\]", "头条一定理头锚"),
        (r"\(hlo : ∀ v : n → ℝ, lam3 \* \(v ⬝ᵥ v\) ≤ v ⬝ᵥ \(\(Xᵀ \* X\) \*ᵥ v\)\) :\n    \(Real\.sqrt lam3 - frob \(X \* \(\(Xᵀ \* X\)⁻¹ \* \(Xᵀ \* \(Y - X\)\)\)\)\)", "头条一命题形状锚（√λ₃ 字面——σ₃ 口径牙）"),
        (r"      ≤ frob \(Y \* Yᵀ - X \* Xᵀ\) := by", "头条一右端命题形状锚"),
        # ---- B 三恒等式（步骤 4）
        (r"theorem B_eq_factor \{m n : Type\} \[Fintype m\] \[Fintype n\] \[DecidableEq n\]", "B 恒等式一定理头锚"),
        (r"\* \(1 \+ \(\(Xᵀ \* X\)⁻¹ \* \(Xᵀ \* \(Y - X\)\)\)\)ᵀ - 1 := by", "B 恒等式一命题形状锚（(1+A)(1+A)ᵀ−1）"),
        (r"theorem XTEX_eq_SBS \{m n : Type\} \[Fintype m\] \[Fintype n\] \[DecidableEq n\]", "B 恒等式二定理头锚"),
        (r"Xᵀ \* \(Y \* Yᵀ - X \* Xᵀ\) \* X\n      = \(Xᵀ \* X\) \*", "B 恒等式二命题形状锚（XᵀEX = S·B·S）"),
        (r"theorem B_eq_inv \{m n : Type\} \[Fintype m\] \[Fintype n\] \[DecidableEq n\]", "B 恒等式三定理头锚"),
        (r"      = \(Xᵀ \* X\)⁻¹ \* \(Xᵀ \* \(Y \* Yᵀ - X \* Xᵀ\) \* X\) \* \(Xᵀ \* X\)⁻¹ := by", "B 恒等式三命题形状锚（S⁻¹(XᵀEX)S⁻¹）"),
        # ---- 列压缩主件（路线 (a)）＋逆压缩向量层（λ₃ 牙）
        (r"theorem frob_mul_le_of_vecNorm \{m n k : Type\}", "列压缩主件定理头锚"),
        (r"frob \(M \* N\) ≤ c \* frob N := by", "列压缩主件命题形状锚"),
        (r"theorem vecNorm_inv_mulVec_le \{n : Type\} \[Fintype n\] \[DecidableEq n\]", "逆压缩向量层定理头锚"),
        (r"vecNorm \(S⁻¹ \*ᵥ v\) ≤ vecNorm v / lam3 := by", "逆压缩向量层命题形状锚（‖v‖/λ₃）"),
        # ---- 逆压缩 Frobenius 层＋头条二（λ₃² 指数牙——NC2 双棱之一）
        (r"theorem frob_inv_mul_inv_le \{n : Type\} \[Fintype n\] \[DecidableEq n\]", "逆压缩 Frobenius 层定理头锚"),
        (r"frob \(S⁻¹ \* M \* S⁻¹\) ≤ frob M / lam3\^2", "逆压缩 Frobenius 层命题形状锚（/λ₃² 指数牙）"),
        (r"theorem step4_bound \{m n : Type\} \[Fintype m\] \[Fintype n\] \[DecidableEq m\]", "头条二定理头锚"),
        (r"      ≤ lam1 \* frob \(Y \* Yᵀ - X \* Xᵀ\) / lam3\^2 := by", "头条二命题形状锚（β=λ₁η/λ₃² 指数牙）"),
        # ---- TTP 实例化双头条（(l3:ℝ)^2 字面牙——NC2 双棱之二）
        (r"theorem ttpX_step3 \(z : ℝ\) \(h1 : \(zLo:ℝ\) ≤ z\) \(h2 : z ≤ \(zHi:ℝ\)\)", "TTP 头条一定理头锚"),
        (r"\(Real\.sqrt \(l3:ℝ\) - frob \(ttpX z \* \(\(\(ttpX z\)ᵀ \* ttpX z\)⁻¹", "TTP 头条一命题形状锚（√l₃ 字面）"),
        (r"theorem ttpX_step4 \(z : ℝ\) \(h1 : \(zLo:ℝ\) ≤ z\) \(h2 : z ≤ \(zHi:ℝ\)\)", "TTP 头条二定理头锚"),
        (r"      ≤ \(u1:ℝ\) \* frob \(Y \* Yᵀ - \(ttpX z\) \* \(ttpX z\)ᵀ\) / \(l3:ℝ\)\^2 :=", "TTP 头条二命题形状锚（(l3:ℝ)^2 字面牙）"),
    ]
    for pat, name in anchors:
        if not re.search(pat, src, re.M):
            fail(f"G4 语句锚缺失：{name}（pattern {pat!r}）")
    # 零 ≥15 位数字面量（数值数据面；Fin 9/Fin 3/lam3^2 等结构数不在列）
    long_lits = re.findall(r"\d{15,}", src)
    if long_lits:
        fail(f"G4 零 ≥15 位数字面量失守：{long_lits[:3]}")
    # 零『def … : ℚ :=』（无 Data 件口径）
    if re.findall(r"^def \w+ : ℚ :=", src, re.M):
        fail("G4 零『def … : ℚ :=』失守（本件零数值数据字面量，无 Data 件）")


def gate4_statement(src_trace: str) -> None:
    gate4_core(src_trace)
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
        if p.is_file() and "TableB5Trace" in p.read_text():
            fail(f"G4 非交叠守卫：{rel} 含 'TableB5Trace'（本件必须不被表 A/M1/"
                 "Solution/表 B 其余件/根模块/lake 面引用）")
    okmsg("G4 语句锚：import 面恰 [Mathlib＋TableB5＋TableB5Core]；33 锚全在"
          "（T1/T2/桥/Pythagoras/块分解/两头条/B 三恒等式/压缩族/TTP 双头条，"
          "√λ₃·/λ₃·/λ₃²·(l3:ℝ)^2 四面字面牙）＋vecNorm def 锚；零 ≥15 位数字面量"
          "＋零 ℚ def；非交叠面（Solution/TableA*/M1Data/TableB1*/TableB6*/"
          "根模块/lakefile/check.sh）零 TableB5Trace 引用")


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


def mat_eq0(A):
    return all(x == 0 for row in A for x in row)


def eye(n):
    return [[F1 if i == j else F0 for j in range(n)] for i in range(n)]


def frob_sq(M):
    """frob² ＝ ∑ M_ij²（Fraction 精确；σ₃ 无理面走平方化等价比较）。"""
    return sum(x * x for row in M for x in row)


def trace(M):
    return sum(M[i][i] for i in range(len(M)))


def gauss_inv(S):
    """n×n Fraction 矩阵 Gauss-Jordan 求逆（门内独立自实现，零仓 import）。"""
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


def mat_vec(M, v):
    return [sum(M[i][j] * v[j] for j in range(len(v))) for i in range(len(M))]


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


def rand_mat(rng, n, m, den=6):
    return [[Fr(rng.randint(-9, 9), den) for _ in range(m)] for _ in range(n)]


def t1_trace_nonneg(A, B):
    """T1 复核核心：双 PSD ⇒ 0 ≤ tr(A*B)（NC3(ii) 冒充前提在此被检出）。"""
    if trace(mat_mul(A, B)) < 0:
        fail("G5(a) T1 复核失守：tr(A*B) < 0（PSD 构造或前提冒充检出）")
    return True


def check_step34_identities(X, Y, wrong_projection=False):
    """步骤 3/4 矩阵恒等式精确复核（wrong_projection=True 为 NC3(i) 篡引擎：
    A := Xᵀ*D 去 S⁻¹——块分解恒等式复核必 FAIL）。"""
    D = mat_sub(Y, X)
    XT, DT = mat_T(X), mat_T(D)
    E = mat_sub(mat_mul(Y, mat_T(Y)), mat_mul(X, XT))
    S = mat_mul(XT, X)
    Sinv = gauss_inv(S)
    if mat_mul(S, Sinv) != eye(3) or mat_mul(Sinv, S) != eye(3):
        fail("G5 Gauss-Jordan 逆自检失守（S·S⁻¹ ≠ I 或 S⁻¹·S ≠ I）")
    A = (mat_mul(XT, D)) if wrong_projection else mat_mul(Sinv, mat_mul(XT, D))
    Dpar = mat_mul(X, A)                      # D_∥
    Dperp = mat_sub(D, Dpar)                  # D_⊥
    # (c) 块分解恒等式 P₀*E*(1−P₀) == X*D_⊥ᵀ + D_∥*D_⊥ᵀ（81 元逐元素）
    P0 = mat_mul(X, mat_mul(Sinv, XT))
    Q = mat_sub(eye(9), P0)
    lhs = mat_mul(mat_mul(P0, E), Q)
    rhs = mat_add(mat_mul(X, mat_T(Dperp)), mat_mul(Dpar, mat_T(Dperp)))
    for i in range(9):
        for j in range(9):
            if lhs[i][j] != rhs[i][j]:
                if wrong_projection:
                    fail("NC3 预期检出：错误投影（A := XᵀD 去 S⁻¹）下"
                         "P₀E(1−P₀) ≠ X*D_⊥ᵀ + D_∥D_⊥ᵀ（防假拦截实证）")
                fail(f"G5(c) 块分解恒等式失守 @({i},{j})：{lhs[i][j]} != {rhs[i][j]}")
    if wrong_projection:
        fail("NC3 失守：错误投影定义（A := XᵀD 去 S⁻¹）下块分解恒等式仍成立"
             "（防假拦截断言失败——不可达：Xᵀ*D ≠ S*A' 时 D_⊥ 错位）")
    # (d) Frobenius-Pythagoras：Xᵀ*D_⊥ = 0（矩阵形前提）⇒ frob(X+D_⊥)² 分解
    if not mat_eq0(mat_mul(XT, Dperp)):
        fail("G5(d) Pythagoras 前提失守：Xᵀ*D_⊥ ≠ 0")
    if frob_sq(mat_add(X, Dperp)) != frob_sq(X) + frob_sq(Dperp):
        fail("G5(d) Frobenius-Pythagoras 失守：frob(X+D_⊥)² ≠ frob X² + frob D_⊥²")
    # (b) frob² == tr(M*Mᵀ)（X/Y/E 三面精确）
    for name, M in (("X", X), ("Y", Y), ("E", E)):
        if frob_sq(M) != trace(mat_mul(M, mat_T(M))):
            fail(f"G5(b) frob² == tr(M*Mᵀ) 失守（{name} 面）")
    # (e) B 三恒等式（9 元逐元素×3）
    B = mat_add(mat_add(A, mat_T(A)), mat_mul(A, mat_T(A)))      # B = A+Aᵀ+A*Aᵀ
    Bf = mat_sub(mat_mul(mat_add(eye(3), A), mat_T(mat_add(eye(3), A))), eye(3))
    XTEX = mat_mul(mat_mul(XT, E), X)
    SBS = mat_mul(mat_mul(S, B), S)
    Binv = mat_mul(mat_mul(Sinv, XTEX), Sinv)
    for i in range(3):
        for j in range(3):
            if B[i][j] != Bf[i][j]:
                fail(f"G5(e) B 恒等式一失守 @({i},{j})：B ≠ (1+A)(1+A)ᵀ−1")
            if XTEX[i][j] != SBS[i][j]:
                fail(f"G5(e) B 恒等式二失守 @({i},{j})：XᵀEX ≠ S*B*S")
            if B[i][j] != Binv[i][j]:
                fail(f"G5(e) B 恒等式三失守 @({i},{j})：B ≠ S⁻¹*(XᵀEX)*S⁻¹")
    return S, Sinv, E


def check_compression(rng):
    """(f) 压缩不等式精确复核：S := l₃•1 + CᵀC 夹逼由构造成立（特征值无关）；
    σ₃ 无理走平方化：‖S⁻¹v‖² ≤ ‖v‖²/λ₃² 与 frob(S⁻¹MS⁻¹)² ≤ frob M²/λ₃⁴。"""
    l3 = Fr(rng.randint(1, 5), 2)
    C = rand_mat(rng, 3, 3)
    CtC = mat_mul(mat_T(C), C)
    S = mat_add(mat_mul([[l3 if i == j else F0 for j in range(3)] for i in range(3)],
                        eye(3)), CtC)
    Sinv = gauss_inv(S)
    if mat_mul(S, Sinv) != eye(3) or mat_mul(Sinv, S) != eye(3):
        fail("G5(f) 压缩面 Gauss-Jordan 逆自检失守")
    # 夹逼由构造成立：vᵀSv − l₃(v⬝v) == ‖Cv‖² ≥ 0（逐向量精确，代数恒等）
    for _ in range(3):
        v = [Fr(rng.randint(-7, 7), 4) for _ in range(3)]
        Sv = mat_vec(S, v)
        lhs = sum(a * b for a, b in zip(v, Sv)) - l3 * sum(a * a for a in v)
        if lhs != sum(x * x for x in mat_vec(C, v)):
            fail("G5(f) 夹逼构造恒等失守：vᵀSv − λ₃‖v‖² ≠ ‖Cv‖²")
        if lhs < 0:
            fail("G5(f) 夹逼构造失守：vᵀSv − λ₃‖v‖² < 0")
    # 向量层平方化：‖S⁻¹v‖² ≤ ‖v‖²/λ₃²
    for _ in range(3):
        v = [Fr(rng.randint(-7, 7), 4) for _ in range(3)]
        w = mat_vec(Sinv, v)
        if sum(x * x for x in w) > sum(x * x for x in v) / (l3 * l3):
            fail("G5(f) 向量层压缩失守：‖S⁻¹v‖² > ‖v‖²/λ₃²")
    # Frobenius 层平方化：frob(S⁻¹MS⁻¹)² ≤ frob(M)²/λ₃⁴
    for _ in range(2):
        M = rand_mat(rng, 3, 3)
        if frob_sq(mat_mul(mat_mul(Sinv, M), Sinv)) > frob_sq(M) / (l3 ** 4):
            fail("G5(f) Frobenius 层压缩失守：frob(S⁻¹MS⁻¹)² > frob M²/λ₃⁴")
    return l3


NOTES_ANCHORS = [
    "### 探针① Frobenius↔trace 恒等式使用级——【档位：现成（自有 frob def 下 15 行闭）】",
    "### 探针② Frobenius↔L2op 比较件三路线（D72-②备选实测判定）——【档位：路线 (a) 现成·自建，采用】",
    "### 探针③ 向量 ℓ2 范数面——【档位：现成·自建（归探针 (a) a1/a2 内）】",
    "### 探针④ R15C trace 探针在盘复核＋照搬源新上下文重编——【档位：在档（D69-4 口径不重跑）】",
    "B5b 陈述面增量决策",
    "/tmp/r17a_probe1_frobtrace.log",
    "/tmp/r17a_probe2_frob_opnorm.log",
    "/tmp/r17a_probe2b_mathlibroute.log",
    "/tmp/r17a_probe2c_names.log",
    "/tmp/r17a_probe3_trace_step34.log",
    "/tmp/r15c_probe3_trace.lean",
]


def gate5_offline() -> dict:
    rng = random.Random(SEED_GATE)
    for k in range(3):
        # (a) PSD 构造 A:=CᵀC 复核 T1/T2（A − t•1 = CᵀC 由构造 PSD）
        C, Dm = rand_mat(rng, 3, 3), rand_mat(rng, 3, 3)
        t = Fr(rng.randint(1, 5), 3)
        Cpsd = mat_mul(mat_T(C), C)
        Dpsd = mat_mul(mat_T(Dm), Dm)
        t1_trace_nonneg(Cpsd, Dpsd)                       # T1：双 PSD
        A2 = mat_add(Cpsd, mat_mul([[t if i == j else F0 for j in range(3)]
                                    for i in range(3)], eye(3)))
        if trace(mat_mul(A2, Dpsd)) < t * trace(Dpsd):    # T2：t*tr(B) ≤ tr(A*B)
            fail("G5(a) T2 复核失守：t*tr(B) > tr(A*B)（A−t•1=CᵀC PSD 构造下）")
        # (b)–(e) 步骤 3/4 恒等式族（9×3 双构型）
        X, Y = gen_instance(rng)
        for name, M in (("X", X), ("Y", Y)):
            for i, row in enumerate(M):
                n2 = sum(c * c for c in row)
                if n2 != 1:
                    fail(f"G5 随机场构造失守：{name}[{i}] 行单位 ≠ 1（{n2}）")
        check_step34_identities(X, Y)
        # (f) 压缩不等式（特征值无关实例设计）
        check_compression(rng)
        okmsg(f"G5 实例 {k}（seed 复放）：T1/T2＋frob²==tr(MMᵀ) 三面＋块分解 81 元"
              "＋Pythagoras＋B 三恒等式 9 元×3＋压缩双面平方化全过")
    # (g) notes §5 探针转录锚
    notes = NOTES.read_text()
    for anc in NOTES_ANCHORS:
        if anc not in notes:
            fail(f"G5(g) notes/tableb-lean.md §5 转录锚缺失：{anc!r}")
    okmsg("G5 离线精确复核：3 随机有理实例（T1/T2 PSD 构造＋块分解＋Pythagoras＋"
          "B 三恒等式＋压缩双面平方化——Gauss-Jordan S⁻¹ 自实现零仓 import）＋"
          "notes §5 探针转录锚 11 处在文")
    return {"instances": 3}


# ------------------------------------------------------------------ NC
def nc1_sorry_injection(src_trace: str) -> None:
    target = ("theorem vecNorm_nonneg {n : Type} [Fintype n] (v : n → ℝ) : "
              "0 ≤ vecNorm v :=\n  Real.sqrt_nonneg _")
    tampered = src_trace.replace(
        target,
        "theorem vecNorm_nonneg {n : Type} [Fintype n] (v : n → ℝ) : "
        "0 ≤ vecNorm v :=\n  sorry")
    if tampered == src_trace:
        fail(f"NC1 预置失败：未能在 /tmp 副本注入 sorry（源码缺目标行 {target!r}）")
    d = TMP / "nc1"
    (d / "ThomsonN9").mkdir(parents=True, exist_ok=True)
    (d / "ThomsonN9" / "TableB5Trace.lean").write_text(tampered)
    # 依赖 olen 随副本落 root（TableB5Trace imports TableB5/TableB5Core →
    # TableB5Data；--root 下 import 先查 root，无 olen 即报缺——G2 已编译
    # 这三个冻结件的 olen，拷入副本 root 使篡件可独立编译）
    for dep in ("TableB5Data.olean", "TableB5.olean", "TableB5Core.olean"):
        src = LEAN_DIR / OLEAN_REL / dep
        if not src.is_file():
            fail(f"NC1 预置失败：依赖 olen 不在场（G2 应已编译）：{src}")
        (d / "ThomsonN9" / dep).write_bytes(src.read_bytes())
    lp = run(["lake", "env", "printenv", "LEAN_PATH"], LEAN_DIR).stdout.strip()
    env = gate_env()
    env["LEAN_PATH"] = f"{d}:{lp}"
    b = subprocess.run(["lean", "--root", str(d), "-o",
                        str(d / "ThomsonN9" / "TableB5Trace.olean"),
                        str(d / "ThomsonN9" / "TableB5Trace.lean")],
                       cwd=str(LEAN_DIR), env=env, capture_output=True, text=True,
                       timeout=605)
    if b.returncode != 0 or "declaration uses `sorry`" not in (b.stdout + b.stderr):
        fail(f"NC1 注入 sorry 后编译未产生 sorry 警告（exit {b.returncode}）：\n"
             f"{(b.stdout + b.stderr)[-500:]}")
    axfile = d / "axcheck.lean"
    axfile.write_text("import ThomsonN9.TableB5Trace\n"
                      "#print axioms ThomsonN9.TableB5Trace.vecNorm_nonneg\n")
    a = subprocess.run(["lean", str(axfile)], cwd=str(LEAN_DIR), env=env,
                       capture_output=True, text=True, timeout=605)
    ax = parse_axiom_lines(a.stdout)
    th = "ThomsonN9.TableB5Trace.vecNorm_nonneg"
    caught = th in ax and ("sorryAx" in ax[th] or (ax[th] - ALLOWED_AXIOMS))
    if not caught:
        fail(f"NC1 失守：注入 sorry 后公理检查未现 sorryAx（{ax}）")
    okmsg(f"NC1 注入 sorry 必被 G3 拦：篡件 vecNorm_nonneg 公理集 = "
          f"{sorted(ax.get(th, set()))}（含 sorryAx → G3 FAIL）")


def nc2_statement_tamper(src_trace: str) -> None:
    # 双棱（指数面）：抽象面 lam3^2 → lam3^3＋TTP 面 (l3:ℝ)^2 → (l3:ℝ)^3
    tampered = src_trace.replace("lam3^2", "lam3^3")
    if tampered == src_trace:
        raise GateFail("NC2 预置失败：篡改一未生效（源码无 lam3^2 字面）")
    try:
        gate4_core(tampered)
        raise GateFail("NC2 失守：篡陈述一（lam3^2→lam3^3）后 G4 语句锚未报错")
    except GateFail as e:
        if "语句锚缺失" not in str(e):
            raise
        print(f"[gate][NC2 检出·棱一] {e}")
    tampered2 = src_trace.replace("(l3:ℝ)^2", "(l3:ℝ)^3")
    if tampered2 == src_trace:
        raise GateFail("NC2 预置失败：篡改二未生效（源码无 (l3:ℝ)^2 字面）")
    try:
        gate4_core(tampered2)
        raise GateFail("NC2 失守：篡陈述二（(l3:ℝ)^2→(l3:ℝ)^3）后 G4 语句锚未报错")
    except GateFail as e:
        if "语句锚缺失" not in str(e):
            raise
        print(f"[gate][NC2 检出·棱二] {e}")
    gate4_core(src_trace)          # sanity：原文件 PASS
    okmsg("NC2 篡陈述必被 G4 拦（指数面双棱）：lam3^2→lam3^3（逆压缩 Frobenius 层"
          "＋头条二）与 (l3:ℝ)^2→(l3:ℝ)^3（TTP 头条二）均检出锚缺失；"
          "原文件 sanity PASS")


def nc3_wrong_engine() -> None:
    rng = random.Random(SEED_GATE)   # 同 seed 复放实例 0
    # ① A 去 S⁻¹ 的错误投影 ⇒ 块分解恒等式必被检出
    X, Y = gen_instance(rng)
    try:
        check_step34_identities(X, Y, wrong_projection=True)
        raise GateFail("NC3① 失守：错误投影未触发检出（不可达：检出已在引擎内拦）")
    except GateFail as e:
        if "NC3 预期检出" not in str(e):
            raise
        print(f"[gate][NC3 检出·棱一] {e}")
    # ② 单 PSD 前提冒充：A:=I₃（PSD）＋B 不定（负迹）⇒ T1 复核必被检出
    fakeB = [[F0, F0, F0], [F0, -F1, F0], [F0, F0, F0]]
    try:
        t1_trace_nonneg(eye(3), fakeB)
        raise GateFail("NC3② 失守：单 PSD 前提冒充未触发检出（tr(I*B) 应 < 0）")
    except GateFail as e:
        if "T1 复核失守" not in str(e):
            raise
        print(f"[gate][NC3 检出·棱二] {e}")
    okmsg("NC3 错误引擎必被 G5 拦（双棱）：A 去 S⁻¹ 投影错位块分解必 FAIL＋"
          "单 PSD 前提冒充 tr(I₃·diag(0,−1,0)) = −1 < 0 必被 T1 复核检出")


# ------------------------------------------------------------------ main
def main() -> None:
    t0 = time.time()
    print(f"[gate] r17_b5b_gate.py seed={SEED_GATE}（确定性；随机实例为 seed 复放）")
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
    if not TRACE_LEAN.is_file():
        fail(f"产出件不在场：{TRACE_LEAN}")
    src_trace = TRACE_LEAN.read_text()

    gate0_ledger()
    gate1_ownership()
    walls = gate2_elaborate()
    g3 = gate3_axioms(src_trace)
    gate4_statement(src_trace)
    gate5_offline()
    nc1_sorry_injection(src_trace)
    nc2_statement_tamper(src_trace)
    nc3_wrong_engine()
    print(f"[gate] G2 elaboration 墙钟：Data {walls['data_s']}s＋B5 {walls['b5_s']}s＋"
          f"Core {walls['core_s']}s＋Trace {walls['trace_s']}s（均 ≤ {ELAB_LIMIT_S}s）；"
          f"G3 定理 {g3['theorems']} 件")


if __name__ == "__main__":
    main()
