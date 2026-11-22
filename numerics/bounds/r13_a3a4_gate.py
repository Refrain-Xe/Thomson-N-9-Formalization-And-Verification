#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r13_a3a4_gate.py — R13 r13a 表 A 第 3/4 件（A3/A4）Lean 化验收门（G1–G5＋负对照 NC1/NC2）.

任务书口径（r13a-tablea-a3a4，D52 裁决）：Stage B 结构定理层表 A 清尾四件中 A3＋A4
两件 Lean 化（heavySolves=0，与 r13b/r13c 文件面零交叠）——

* **A3**（formal/lean/ThomsonN9/TableA3.lean，仅 import Mathlib）：
  (a) typed 组合计数恒等式：TYPES=(0,0,0,1,1,1,2,2,2) 的全部 C(9,3)=84 个三点组
      （严格递增指标三元组编码）按类型分桶（非降序类型三元组）恰为 AAA 轨道
      3 类×各 1 组、AAB 型 6 类×各 9 组、ABC 1 类×27 组
      （3·1+6·9+1·27=84），显式枚举表＋decide 计数引理落
      （card_allTriples / bucket_table / image_buckets / bucket_partition /
      orbit_totals / a3_typed_counting）；
  (b) ℓ₁ 归一化恒等式 3c_A+54c_B+27c_C−9·ΣF⁽⁰⁾−e == 0（a3_l1_normalization，
      norm_num）——五 ℚ 字面量取自 M9 证书 certificates/n9-stage-a4-typedcap-m0748_M9.json
      （blocks.c_A/c_B/c_C/e 与 9×9 blocks.F0 全 81 元素之和 ΣF⁽⁰⁾）。
* **A4**（formal/lean/ThomsonN9/TableA4.lean，仅 import Mathlib）：S₃ 商展开结构核——
  Q:ℕ→ℚ→ℚ→ℚ→ℚ 递推 def（Q₀=1、Q₁=t−u·v、
  Q_{j+2}=2(t−u·v)·Q_{j+1}−(1−u²−v²+u²v²)·Q_j）＋对称性定理 Q_symm
  （∀ m u v t, Q m u v t = Q m v u t）＋k≤5 显式形状引理（Q_zero…Q_five）＋
  Y 列计数 Σ_{k<6}(9−k)²=271（ycol_count，decide）＋stretch 一非平凡列
  K_col=−2(Y+Y^{(u,t,v)}+Y^{(v,t,u)}) 展开恒等式（Kcol_two_three_one，ring）。
  271 列全符号装配明确不在件（数值面由 r13c A1 实例＋Python 第二实现承担）。

本门全确定性检查（无随机路径），seed 20261015 按惯例记档；PATH 自动前置
~/.elan/bin（缺失即 FAIL 附信息）；CWD 无关（全部路径自 __file__ 推导）。

检查面（对应任务书 G1–G5＋NC1/NC2）：
  G0 账本在场与受控字段（seed == 20261015、heavy_solves == 0、自有件在账本清单）。
  G1 文件所有权守卫：git status --porcelain 与 git diff HEAD --name-only 的全部
     改动路径 ⊆ 本任务自有七件（TableA3/TableA4/本门/仓内嵌套包装器/账本/
     tablea-lean.md/decisions.md）∪ 并行家族放行集（D53-4：按 D52 任务切分
     的 r13b/r13c/r13d 交付件家族 pattern——TableA1(Data)/TableA6.lean、
     r13_a1*/r13_a6*/r13d* 门数据账本包装器、tablea* 笔记、GAP-REPORT/PROGRESS
     收口文档；逐项响亮打印）；家族外任何路径（冻结件/证书/参考仓/既有
     results 等）仍字面拦截。另对两份只读输入件显式 git diff HEAD 守卫
     （certificates/n9-stage-a4-typedcap-m0748_M9.json 与
     numerics/bounds/results/r9_s3_rederive.json 必须零改动——放行集不含
     certificates/ 与二者）。
  G2 逐文件 elaboration：子进程 `lake env lean ThomsonN9/TableA3.lean` 与
     `lake env lean ThomsonN9/TableA4.lean`（CWD=formal/lean）各 exit 0、输出无
     error／无 sorry、墙钟各 ≤ 600s（任务书 ≤10 min）——不整库 build。
  G3 公理：两文件各编译 olean 落 .lake/build/lib/lean/ThomsonN9/（gitignored
     构建产物位），再 /tmp 检查件 import 两模块并 #print axioms 全部 16 条定理
     ——公理集恰 ⊆ {propext, Classical.choice, Quot.sound}，无 sorryAx/
     ofReduceBool/ofReduceNat/trustCompiler。
  G4 语句锚：两文件 import 行恰 [import Mathlib]；定理名＋命题形状锚
     （A3：types/sort3/allTriples/bucket/bucketCount/classes 定义、
     [1, 9, 9, 9, 27, 9, 1, 9, 9, 1] 枚举表、3 * 1 + 6 * 9 + 1 * 27、= 84、
     a3_l1_normalization 五 ℚ 字面量结构；A4：Q 递推 def 三臂字面量、
     Q_symm 的 Q m u v t = Q m v u t、Q_zero…Q_five 定理名、
     Finset.range 6 的 (9 - k) ^ 2 = 271、Kcol 2 3 1）；非交叠守卫
     （Solution.lean/ThomsonN9.lean/M1Data.lean/lakefile.toml/scripts/check.sh/
     TableA.lean 零 "TableA3"/"TableA4" 引用）。
  G5 离线精确复核（stdlib Fraction，零外部依赖，零仓库 import）：
     A3——自 results/r9_s3_rederive.json 重读链（inputs.certificate 为唯一推
     导输入）→ 重读 M9 证书 → 重析 c_A/c_B/c_C/e 与 F0 81 元素重加得 ΣF⁽⁰⁾ →
     重算 3c_A+54c_B+27c_C−9·ΣF⁽⁰⁾−e == 0（Fraction 精确）→ 与 TableA3.lean
     源码 a3_l1_normalization 语句（空白归一后）逐字符模板比对（五字面量＋
     结构一并钉死）；r9 锚（sizes.class_counts 三轨道口径、sizes.Y_cols=271、
     structural_checks.Q_uv_symmetric_all_k/Y_cols_equals_271、
     normalization_residual 语句、inputs.certificate_is_sole_derivation_input）；
     84 分桶枚举独立复算（itertools.combinations＋types=i//d，d 自源码 regex
     析出）与源码 classes 列表／bucket_table 枚举表逐项比对，3·1+6·9+1·27=84。
     A4——多项式＝稀疏 dict {指数:Fraction} 的独立第二实现（ω 以 (1−u²)(1−v²)
     乘积形式独立构造，与源码 1-u*u-v*v+u*u*v*v 展开形不同路径）重算 Q_k
     （k≤5）；源码 def Q 字面量重构（regex 析出递推系数 m 与 ω 表达式文本，
     经内置 ℚ 表达式求值器（+,-,*,^,括号，变量 u/v/t）求值）在 5 个非对称
     有理点 ×k≤5 与独立实现逐点对拍；Q_zero…Q_five 语句 RHS 文本在同一批点
     求值对拍；ycol_count 形状锚＋独立复算 Σ_{k<6}(9−k)²=271；Kcol_two_three_one
     RHS 文本求值 vs 独立 Kcol（Y=u^a v^b Q_k、Y^{(u,t,v)}=u^a t^b Q_k(u,t,v)、
     Y^{(v,t,u)}=v^a t^b Q_k(v,t,u)、−2·三者和）对拍。
  NC1 注入 sorry 必被 G3 拦：/tmp 副本把 a3_l1_normalization 证明改 sorry →
     独立编译必现 "declaration uses `sorry`" ＋公理检查必现 sorryAx。
  NC2 篡字面量必被 G5 拦：/tmp 副本两处篡改——(a) c_B 分子 140609170236263 +1；
     (b) Q_two RHS 系数 4→5——G5 对应检查函数必 FAIL（原文件 sanity PASS）。

用法（CWD 无关）：
  python3 numerics/bounds/r13_a3a4_gate.py     # 全门（exit 0 = 过）
  python3 thomson-n9/numerics/bounds/r13_a3a4_gate.py
      # ↑ CWD＝仓库根时的验收命令命中同名 runpy 包装器（沿 R10A 0087eab／
      #   R12B 先例，thomson-n9/thomson-n9/… → 本真实门，exit code 原样传播；
      #   CWD＝campaign 根时该相对路径直接命中本文件，包装器不参与）

自跑/验收并行容错（D53-4）：G1 对 r13b/r13c/r13d 并行会话在途件按
  PARALLEL_FAMILY pattern 家族放行（逐项响亮打印；D52 任务切分的文件面），
  家族外路径仍字面拦截；如遇家族 pattern 未覆盖的正当在途件，可另设
  R13A_G1_ALLOW_FOREIGN=path1,path2 显式放行（同样响亮打印）。
  提交后树净 ⇒ 两层放行集皆空 ⇒ G1 等价字面严格。
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
from itertools import combinations
from pathlib import Path

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
REPO = HERE.parents[1]                 # thomson-n9/
LEAN_DIR = REPO / "formal" / "lean"

SEED_GATE = 20261015                   # 惯例记档；本门无随机路径（确定性）

TABLEA3_REL = "formal/lean/ThomsonN9/TableA3.lean"
TABLEA4_REL = "formal/lean/ThomsonN9/TableA4.lean"
GATE_REL = "numerics/bounds/r13_a3a4_gate.py"
WRAPPER_REL = "thomson-n9/numerics/bounds/r13_a3a4_gate.py"   # CWD 兼容包装器
LEDGER_REL = "numerics/bounds/results/r13_a3a4_ledger.json"
NOTES_REL = "notes/tablea-lean.md"
DECISIONS_REL = "notes/decisions.md"
OWNED = {TABLEA3_REL, TABLEA4_REL, GATE_REL, WRAPPER_REL, LEDGER_REL,
         NOTES_REL, DECISIONS_REL}
READONLY_INPUTS = [
    "certificates/n9-stage-a4-typedcap-m0748_M9.json",
    "numerics/bounds/results/r9_s3_rederive.json",
]
# 并行家族放行集（D53-4，2026-10-10 验收返工）：验收时点 r13b/r13c/r13d 并行
# 会话可能有未提交在途件（R13 实录：r13c TableA1.lean 在途致本门首验 G1 exit 1；
# r13b TableA6.lean/r13_a6_data.* 同期在途）。按 D52 任务切分把三线交付件家族
# pattern 化放行（逐项响亮打印，非静默）；家族外任何路径（冻结件/证书/参考仓/
# 既有 results·bounds 资产/Solution.lean/M1Data.lean/lakefile/toolchain 等）
# 仍字面拦截，只读输入件守卫不受放行集影响。
PARALLEL_FAMILY = [
    # r13b/r13c 形式层件（TableA1/Data、TableA6 含分块子模块目录——R13 实录
    # r13b 曾建 TableA6/ 目录拆块；TableA[0-9]… 不匹配 r12 冻结面 TableA.lean）
    r"^formal/lean/ThomsonN9/TableA[0-9][A-Za-z0-9_]*(\.lean|/)",
    r"^numerics/bounds/r13_a1[a-z0-9_]*(\.py|/)",           # r13c 门/数据件/工作目录
    r"^numerics/bounds/r13_a6[a-z0-9_]*(\.py|/)",           # r13b 门/数据件/工作目录
    r"^numerics/bounds/r13d[a-z0-9_]*(\.py|/)",             # r13d 收口门
    r"^numerics/bounds/results/r13_a1[a-z0-9_]*(\.json|/)", # r13c 账本/数据
    r"^numerics/bounds/results/r13_a6[a-z0-9_]*(\.json|/)", # r13b 账本/数据
    r"^numerics/bounds/results/r13d[a-z0-9_]*(\.json|/)",   # r13d 账本
    r"^thomson-n9/numerics/bounds/r13_a1[a-z0-9_]*(\.py|/)",   # r13c 嵌套包装器
    r"^thomson-n9/numerics/bounds/r13_a6[a-z0-9_]*(\.py|/)",   # r13b 嵌套包装器
    r"^thomson-n9/numerics/bounds/r13d[a-z0-9_]*(\.py|/)",     # r13d 嵌套包装器
    r"^notes/tablea[a-z0-9_\-]*\.md$",                      # r13b/c tablea 笔记族
    r"^(GAP-REPORT|PROGRESS)\.md$",                         # r13d 收口文档
]

R9_JSON = RESULTS / "r9_s3_rederive.json"
TABLEA3 = LEAN_DIR / "ThomsonN9" / "TableA3.lean"
TABLEA4 = LEAN_DIR / "ThomsonN9" / "TableA4.lean"
TMP = Path("/tmp/r13_a3a4_gate")

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN_AXIOMS = ("sorryAx", "ofReduceBool", "ofReduceNat", "trustCompiler")
THEOREMS_A3 = [
    "ThomsonN9.TableA3.card_allTriples",
    "ThomsonN9.TableA3.bucket_table",
    "ThomsonN9.TableA3.image_buckets",
    "ThomsonN9.TableA3.bucket_partition",
    "ThomsonN9.TableA3.orbit_totals",
    "ThomsonN9.TableA3.a3_typed_counting",
    "ThomsonN9.TableA3.a3_l1_normalization",
]
THEOREMS_A4 = [
    "ThomsonN9.TableA4.Q_symm",
    "ThomsonN9.TableA4.Q_zero",
    "ThomsonN9.TableA4.Q_one",
    "ThomsonN9.TableA4.Q_two",
    "ThomsonN9.TableA4.Q_three",
    "ThomsonN9.TableA4.Q_four",
    "ThomsonN9.TableA4.Q_five",
    "ThomsonN9.TableA4.ycol_count",
    "ThomsonN9.TableA4.Kcol_two_three_one",
]
THEOREMS = THEOREMS_A3 + THEOREMS_A4

# G5 采样点（非对称有理点，5 点；篡任一系数在 5 个 generic 点同时消失不可期）
SAMPLE_POINTS = [
    (Fraction(1, 3), Fraction(2, 5), Fraction(-1, 7)),
    (Fraction(-3, 2), Fraction(5, 7), Fraction(1, 5)),
    (Fraction(2, 1), Fraction(-1, 3), Fraction(3, 8)),
    (Fraction(7, 5), Fraction(-2, 1), Fraction(1, 2)),
    (Fraction(-1, 4), Fraction(-2, 5), Fraction(-7, 1)),
]


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
    if LEDGER.is_file():
        led = json.loads(LEDGER.read_text())
        if led.get("seed") != SEED_GATE:
            fail(f"G0 账本 seed 失配：{led.get('seed')!r} != {SEED_GATE}")
        if led.get("heavy_solves") != 0:
            fail(f"G0 账本 heavy_solves 失配：{led.get('heavy_solves')!r} != 0")
        files = led.get("files", {})
        missing = [rel for rel in OWNED if rel not in files]
        if missing:
            fail(f"G0 账本 files 缺自有件：{missing}")
        okmsg(f"G0 账本在场（seed={SEED_GATE}，heavy_solves=0，自有件{len(OWNED)}全在清单）")
        return led
    okmsg("G0 账本尚未落盘（首次自跑前奏；正式验收时必须在场）——跳过字段核验")
    return None


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
    # 三层放行：① OWNED（本任务七件）；② 环境变量 R13A_G1_ALLOW_FOREIGN（自跑
    # 专用逐件放行，默认关）；③ PARALLEL_FAMILY pattern（D53-4 验收返工——
    # r13b/r13c/r13d 并行在途件家族放行，逐项响亮打印）。三层之外字面拦截。
    allow_foreign = {p.strip() for p in
                     os.environ.get("R13A_G1_ALLOW_FOREIGN", "").split(",") if p.strip()}
    parallel_hits = set()
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
                parallel_hits.add(p)
                print(f"[gate][G1][并行家族放行] r13b/r13c/r13d 在途件（D53-4 pattern）：{p}")
                continue
            raise GateFail(
                f"G1 树上出现非本任务自有件（{cmd[1]}）：{p!r}（自有集={sorted(OWNED)}；"
                f"并行家族放行集 D53-4 未覆盖该路径——若确系 r13b/r13c/r13d 在途件，"
                f"可设 R13A_G1_ALLOW_FOREIGN={p} 显式放行）")
    # 两份只读输入件的显式 git diff 守卫（响亮打印，双保险；放行集不含此二者）
    r = run(["git", "diff", "HEAD", "--"] + READONLY_INPUTS, REPO)
    if r.returncode != 0:
        raise GateFail(f"G1 只读输入件 diff 守卫失败：{r.stderr.strip()[:300]}")
    if r.stdout.strip():
        raise GateFail(f"G1 只读输入件被改动：{'、'.join(READONLY_INPUTS)}（git diff HEAD 非空）")
    okmsg("G1 文件所有权守卫：git status/diff 相对 HEAD 仅本任务自有件／并行家族放行件"
          f"（或全净）；M9 证书与 r9_s3_rederive.json 只读 git diff 守卫空"
          + (f"〔并行家族放行 {sorted(parallel_hits)}〕" if parallel_hits else "")
          + (f"〔环境变量放行 {sorted(allow_foreign)}〕" if allow_foreign else ""))


# ------------------------------------------------------------------ G2
def gate2_elaborate() -> dict:
    walls = {}
    for rel, path in (("TableA3", TABLEA3), ("TableA4", TABLEA4)):
        t0 = time.time()
        r = run(["lake", "env", "lean", f"ThomsonN9/{rel}.lean"], LEAN_DIR)
        wall = time.time() - t0
        walls[rel] = round(wall, 1)
        if r.returncode != 0:
            fail(f"G2 {rel}.lean elaboration 失败（exit {r.returncode}）：\n"
                 f"{r.stdout[-800:]}\n{r.stderr[-800:]}")
        out = r.stdout + r.stderr
        if "error" in out or "sorry" in out:
            fail(f"G2 {rel}.lean elaboration 输出含 error/sorry：\n{out[-800:]}")
        if wall > 600.0:
            fail(f"G2 {rel}.lean elaboration 墙钟 {wall:.1f}s 超 10 分钟上限")
    okmsg(f"G2 逐文件 elaboration：TableA3.lean exit 0（{walls['TableA3']}s）＋"
          f"TableA4.lean exit 0（{walls['TableA4']}s），输出均无 error/sorry，各 ≤ 600s")
    return walls


# ------------------------------------------------------------------ G3
def parse_axiom_lines(out: str) -> dict:
    ax = {}
    for line in out.splitlines():
        m = re.match(r"'([^']+)'\s+depends on axioms:\s*\[(.*)\]", line.strip())
        if m:
            ax[m.group(1)] = {a.strip() for a in m.group(2).split(",") if a.strip()}
    return ax


def check_axioms(ax: dict, ctx: str, ths: list) -> None:
    for th in ths:
        if th not in ax:
            fail(f"{ctx}：公理输出缺定理 {th}（解析到：{sorted(ax)}）")
        bad = ax[th] - ALLOWED_AXIOMS
        if bad:
            fail(f"{ctx}：定理 {th} 依赖非标准公理 {sorted(bad)}")
        for f in FORBIDDEN_AXIOMS:
            if f in ax[th]:
                fail(f"{ctx}：定理 {th} 依赖 {f}")
    union = sorted(set().union(*ax.values())) if ax else []
    okmsg(f"{ctx}：{len(ths)} 条定理公理集 ⊆ {{propext, Classical.choice, Quot.sound}}"
          f"（实际并集 {union}）")


def gate3_axioms() -> dict:
    ax_union = set()
    for rel in ("TableA3", "TableA4"):
        olean_rel = f".lake/build/lib/lean/ThomsonN9/{rel}.olean"
        olean = LEAN_DIR / olean_rel
        olean.parent.mkdir(parents=True, exist_ok=True)
        r = run(["lake", "env", "lean", "-o", olean_rel, f"ThomsonN9/{rel}.lean"], LEAN_DIR)
        if r.returncode != 0 or not olean.is_file():
            fail(f"G3 {rel}.olean 编译失败（exit {r.returncode}）：\n"
                 f"{r.stdout[-500:]}\n{r.stderr[-500:]}")
    TMP.mkdir(parents=True, exist_ok=True)
    axfile = TMP / "axcheck.lean"
    axfile.write_text(
        "import ThomsonN9.TableA3\nimport ThomsonN9.TableA4\n"
        + "".join(f"#print axioms {th}\n" for th in THEOREMS))
    r = run(["lake", "env", "lean", str(axfile)], LEAN_DIR)
    if r.returncode != 0:
        fail(f"G3 公理检查件编译失败（exit {r.returncode}）：\n"
             f"{r.stdout[-500:]}\n{r.stderr[-500:]}")
    ax = parse_axiom_lines(r.stdout)
    if len(ax) != len(THEOREMS):
        fail(f"G3 公理输出解析数 {len(ax)} != 定理数 {len(THEOREMS)}（解析到 {sorted(ax)}）")
    check_axioms(ax, "G3 公理", THEOREMS)
    ax_union = set().union(*ax.values())
    return sorted(ax_union)


# ------------------------------------------------------------------ G4
A3_ANCHORS = [
    (r"^import\s+Mathlib\s*$", "A3 import 锚（两文件共用，见 gate4）"),
    (r"def types : Fin 9 → ℕ := fun i => i\.val / 3", "A3 types 定义锚（i/3 分型）"),
    (r"def sort3 \(a b c : ℕ\) : ℕ × ℕ × ℕ", "A3 sort3 定义锚"),
    (r"def allTriples : Finset \(Fin 9 × Fin 9 × Fin 9\)", "A3 allTriples 定义锚"),
    (r"def bucket \(p : Fin 9 × Fin 9 × Fin 9\) : ℕ × ℕ × ℕ", "A3 bucket 定义锚"),
    (r"def bucketCount \(b : ℕ × ℕ × ℕ\) : ℕ := \(allTriples\.filter fun p => bucket p = b\)\.card",
     "A3 bucketCount 定义锚"),
    (r"theorem card_allTriples : allTriples\.card = 84", "A3 card_allTriples 语句锚"),
    (r"theorem bucket_table :", "A3 bucket_table 定理名锚"),
    (r"bucketCount \(2, 2, 2\)\] = \[1, 9, 9, 9, 27, 9, 1, 9, 9, 1\]", "A3 枚举表字面量锚"),
    (r"theorem image_buckets : allTriples\.image bucket = classesSet", "A3 image_buckets 语句锚"),
    (r"theorem bucket_partition : ∑ b ∈ allTriples\.image bucket, bucketCount b = 84",
     "A3 bucket_partition 语句锚"),
    (r"theorem orbit_totals :", "A3 orbit_totals 定理名锚"),
    (r"= 6 \* 9 ∧", "A3 轨道小计锚（6·9）"),
    (r"theorem a3_typed_counting :", "A3 主定理名锚"),
    (r"3 \* 1 \+ 6 \* 9 \+ 1 \* 27 = 84", "A3 配平恒等式锚 3·1+6·9+1·27=84"),
    (r"theorem a3_l1_normalization :", "A3(b) 定理名锚"),
    (r"3 \* \(0 : ℚ\)", "A3(b) c_A=0 字面量锚"),
    (r"54 \* \(140609170236263 : ℚ\) / 281474976710656", "A3(b) c_B 字面量锚"),
    (r"27 \* \(20717 : ℚ\) / 7599824371187712", "A3(b) c_C 字面量锚"),
    (r"9 \* \(9503960072215 : ℚ\) / 70368744177664", "A3(b) ΣF⁽⁰⁾ 字面量锚"),
    (r"- \(7250752630179179 : ℚ\) / 281474976710656 = 0", "A3(b) e 字面量锚＋=0 收口"),
]

A4_ANCHORS = [
    (r"def Q : ℕ → ℚ → ℚ → ℚ → ℚ", "A4 Q 递推 def 签名锚"),
    (r"\| 0, _, _, _ => 1", "A4 Q₀=1 基锚"),
    (r"\| 1, u, v, t => t - u \* v", "A4 Q₁=t−u·v 基锚"),
    (r"\| j \+ 2, u, v, t =>", "A4 递推步臂锚"),
    (r"2 \* \(t - u \* v\) \* Q \(j \+ 1\) u v t", "A4 递推步 2(t−u·v)·Q_{j+1} 锚"),
    (r"\(1 - u \* u - v \* v \+ u \* u \* v \* v\) \* Q j u v t",
     "A4 递推步 (1−u²−v²+u²v²)·Q_j 锚"),
    (r"theorem Q_symm : ∀ \(m : ℕ\) \(u v t : ℚ\), Q m u v t = Q m v u t",
     "A4 对称性定理语句锚"),
    (r"theorem Q_zero \(u v t : ℚ\) : Q 0 u v t = 1", "A4 Q_zero 锚"),
    (r"theorem Q_one \(u v t : ℚ\) : Q 1 u v t = t - u \* v", "A4 Q_one 锚"),
    (r"theorem Q_two \(u v t : ℚ\) :", "A4 Q_two 定理名锚"),
    (r"theorem Q_three \(u v t : ℚ\) :", "A4 Q_three 定理名锚"),
    (r"theorem Q_four \(u v t : ℚ\) :", "A4 Q_four 定理名锚"),
    (r"theorem Q_five \(u v t : ℚ\) :", "A4 Q_five 定理名锚"),
    (r"theorem ycol_count : ∑ k ∈ Finset\.range 6, \(9 - k\) \^ 2 = 271",
     "A4 Y 列计数语句锚 Σ_{k<6}(9−k)²=271"),
    (r"def Ycol \(k a b : ℕ\) \(u v t : ℚ\) : ℚ := u \^ a \* v \^ b \* Q k u v t",
     "A4 Ycol 定义锚"),
    (r"def Kcol \(k a b : ℕ\) \(u v t : ℚ\) : ℚ :=", "A4 Kcol 定义锚"),
    (r"-2 \* \(Ycol k a b u v t \+ u \^ a \* t \^ b \* Q k u t v \+ v \^ a \* t \^ b \* Q k v t u\)",
     "A4 Kcol=−2(Y+Y^{(u,t,v)}+Y^{(v,t,u)}) 结构锚"),
    (r"theorem Kcol_two_three_one \(u v t : ℚ\) :", "A4 stretch 定理名锚"),
]


def gate4_statement(src3: str, src4: str) -> None:
    for name, src in (("TableA3", src3), ("TableA4", src4)):
        imports = re.findall(r"^import\s+\S+", src, re.M)
        if imports != ["import Mathlib"]:
            fail(f"G4 {name} import 行失配：{imports}（应恰为 [import Mathlib]）")
    anchors = [(p, n) for p, n in A3_ANCHORS if not n.startswith("A3 import")]
    anchors += A4_ANCHORS
    for pat, name in anchors:
        src = src3 if name.startswith("A3") else src4
        if not re.search(pat, src, re.M):
            fail(f"G4 语句锚缺失：{name}（pattern {pat!r}）")
    # 非交叠守卫：冻结/解件/先行件面不含 TableA3/TableA4
    for rel in ("ThomsonN9/Solution.lean", "ThomsonN9.lean", "ThomsonN9/M1Data.lean",
                "lakefile.toml", "scripts/check.sh", "ThomsonN9/TableA.lean"):
        p = LEAN_DIR / rel
        if p.is_file() and ("TableA3" in p.read_text() or "TableA4" in p.read_text()):
            fail(f"G4 非交叠守卫：{rel} 含 'TableA3'/'TableA4'（本件必须不被 import／不被引用）")
    okmsg("G4 语句锚：两文件 import 恰 [Mathlib]；A3 20 锚（定义/枚举表/配平/五字面量）＋"
          "A4 18 锚（递推三臂/对称性/形状/271/Kcol）全在；Solution.lean/根模块/M1Data.lean/"
          "lakefile/check.sh/TableA.lean 零 TableA3/TableA4 引用（非交叠）")


# ------------------------------------------------------------------ G5 helpers
def parse_frac(s: str) -> Fraction:
    s = s.strip()
    if "/" in s:
        num, den = s.split("/")
        return Fraction(int(num), int(den))
    return Fraction(int(s))          # 证书标量可为整数串（如 c_A = "0"）


# ---- 内置 ℚ 表达式求值器（+,-,*,^，括号，变量 u/v/t，非负整数指数） ----
def eval_q_expr(text: str, u: Fraction, v: Fraction, t: Fraction) -> Fraction:
    """求值 Lean 风格 ℚ 多项式表达式文本（仅 + - * ^、括号、u/v/t、非负整数指数）."""
    toks = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c.isspace():
            i += 1
        elif c.isdigit():
            j = i
            while j < n and text[j].isdigit():
                j += 1
            toks.append(("num", int(text[i:j])))
            i = j
        elif c.isalpha():
            if c not in "uvt":
                raise GateFail(f"G5 求值器：非法变量 {c!r}（表达式 {text[:60]!r}）")
            toks.append(("var", c))
            i += 1
        elif c in "+-*^()":
            toks.append((c, c))
            i += 1
        else:
            raise GateFail(f"G5 求值器：非法字符 {c!r}（表达式 {text[:60]!r}）")
    pos = [0]
    env = {"u": u, "v": v, "t": t}

    def peek():
        return toks[pos[0]] if pos[0] < len(toks) else (None, None)

    def eat(kind):
        if peek()[0] != kind:
            raise GateFail(f"G5 求值器：token 失配 期望 {kind} 实得 {peek()}（{text[:60]!r}）")
        tok = toks[pos[0]]
        pos[0] += 1
        return tok

    def parse_atom():
        kind, val = peek()
        if kind == "num":
            eat("num")
            return Fraction(val)
        if kind == "var":
            eat("var")
            return env[val]
        if kind == "(":
            eat("(")
            e = parse_sum()
            eat(")")
            return e
        raise GateFail(f"G5 求值器：原子失配 {peek()}（{text[:60]!r}）")

    def parse_pow():
        base = parse_atom()
        if peek()[0] == "^":
            eat("^")
            kind, val = peek()
            if kind != "num":
                raise GateFail(f"G5 求值器：指数须为非负整数字面量，得 {peek()}")
            eat("num")
            if val < 0 or val > 64:
                raise GateFail(f"G5 求值器：指数越界 {val}")
            return base ** val
        return base

    def parse_unary():
        if peek()[0] == "-":
            eat("-")
            return -parse_unary()
        if peek()[0] == "+":
            eat("+")
            return parse_unary()
        return parse_pow()

    def parse_prod():
        acc = parse_unary()
        while peek()[0] == "*":
            eat("*")
            acc *= parse_unary()
        return acc

    def parse_sum():
        acc = parse_prod()
        while peek()[0] in ("+", "-"):
            op = peek()[0]
            eat(op)
            rhs = parse_prod()
            acc = acc + rhs if op == "+" else acc - rhs
        return acc

    result = parse_sum()
    if pos[0] != len(toks):
        raise GateFail(f"G5 求值器：尾随 token {peek()}（{text[:60]!r}）")
    return result


# ---- 独立第二实现：Q_k 多项式（稀疏 dict，ω 用 (1−u²)(1−v²) 乘积形独立构造） ----
def poly_zero():
    return {}


def poly_add(a, b):
    r = dict(a)
    for k, val in b.items():
        r[k] = r.get(k, Fraction(0)) + val
        if r[k] == 0:
            del r[k]
    return r


def poly_mul(a, b):
    r = {}
    for (i1, j1, l1), v1 in a.items():
        for (i2, j2, l2), v2 in b.items():
            key = (i1 + i2, j1 + j2, l1 + l2)
            r[key] = r.get(key, Fraction(0)) + v1 * v2
    return {k: val for k, val in r.items() if val != 0}


def poly_sm(a, s):
    return {k: val * s for k, val in a.items() if val * s != 0}


def poly_sub(a, b):
    return poly_add(a, poly_sm(b, Fraction(-1)))


def poly_subst(p, perm):
    """perm[i] = 老变量 i（0=u,1=v,2=t）在新多项式中落到的位置."""
    r = {}
    for (i, j, l), c in p.items():
        e = [0, 0, 0]
        e[perm[0]] += i
        e[perm[1]] += j
        e[perm[2]] += l
        key = tuple(e)
        r[key] = r.get(key, Fraction(0)) + c
    return {k: val for k, val in r.items() if val != 0}


def poly_eval(p, u, v, t):
    return sum(c * u ** i * v ** j * t ** l for (i, j, l), c in p.items())


def mono(i, j, l, c=Fraction(1)):
    return {(i, j, l): c}


def independent_Q(kmax: int) -> list:
    """独立实现：Q₀=1、Q₁=t−uv、Q_{j+2}=2(t−uv)Q_{j+1}−(1−u²)(1−v²)Q_j."""
    tuv = poly_sub(mono(0, 0, 1), mono(1, 1, 0))                    # t − u·v
    om = poly_mul(poly_sub(mono(0, 0, 0), mono(2, 0, 0)),           # (1−u²)(1−v²)
                  poly_sub(mono(0, 0, 0), mono(0, 2, 0)))
    qs = [mono(0, 0, 0), tuv]
    while len(qs) < kmax + 1:
        qs.append(poly_sub(poly_mul(poly_sm(tuv, Fraction(2)), qs[-1]),
                           poly_mul(om, qs[-2])))
    return qs


def independent_Kcol(qs, k, a, b):
    """独立实现：−2·(u^a v^b Q_k(u,v,t) + u^a t^b Q_k(u,t,v) + v^a t^b Q_k(v,t,u))."""
    y1 = poly_mul(mono(a, b, 0), qs[k])
    y2 = poly_mul(mono(a, 0, b), poly_subst(qs[k], (0, 2, 1)))   # p ↦ p(u,t,v)
    y3 = poly_mul(mono(0, a, b), poly_subst(qs[k], (1, 2, 0)))   # p ↦ p(v,t,u)
    return poly_sm(poly_add(poly_add(y1, y2), y3), Fraction(-2))


# ---- A3 源码解析 ----
RE_TYPES_DIV = re.compile(r"def types : Fin 9 → ℕ := fun i => i\.val / (\d+)")
RE_CLASSES_LIST = re.compile(
    r"def classes : List \(ℕ × ℕ × ℕ\) :=\s*\n\s*\[((?:\(\d+, \d+, \d+\)(?:,\s*\n?\s*)?)+)\]",
    re.S)
RE_BUCKET_TABLE = re.compile(
    r"bucketCount \(2, 2, 2\)\] = \[(\d+(?:, \d+)+)\]")
RE_L1_STMT = re.compile(
    r"theorem a3_l1_normalization :\s*(.*?)\s*:= by", re.S)


def norm_ws(s: str) -> str:
    return re.sub(r"\s+", " ", s).strip()


def g5_a3(src: str, r9: dict) -> dict:
    # ---- 证书链重读（r9_s3_rederive.json → inputs.certificate → M9 证书）----
    if r9.get("inputs", {}).get("certificate_is_sole_derivation_input") is not True:
        fail("G5·A3 r9_s3_rederive.json inputs.certificate_is_sole_derivation_input != true")
    cert_path = Path(r9["inputs"]["certificate"])
    if not cert_path.is_file():
        cert_path = REPO / "certificates" / cert_path.name
    if not cert_path.is_file():
        fail(f"G5·A3 证书不在场：{r9['inputs']['certificate']}（回退 {cert_path} 亦缺）")
    cert = json.loads(cert_path.read_text())
    if cert.get("kind") != "n9-stage-a4-typedcap":
        fail(f"G5·A3 证书 kind 失配：{cert.get('kind')!r}")
    if cert["params"]["M"] != 9 or cert["params"]["K"] != 6:
        fail(f"G5·A3 证书 params.M/K 失配：{cert['params']}（应 M=9、K=6）")
    blocks = cert["blocks"]
    fr = {
        "c_A": parse_frac(blocks["c_A"][0]),
        "c_B": parse_frac(blocks["c_B"][0]),
        "c_C": parse_frac(blocks["c_C"][0]),
        "e": parse_frac(blocks["e"][0]),
    }
    F0 = blocks["F0"]
    if len(F0) != 9 or any(len(row) != 9 for row in F0):
        fail(f"G5·A3 证书 F0 非 9×9：{len(F0)}×{[len(r) for r in F0][:3]}…")
    sumF0 = Fraction(0)
    for row in F0:
        for x in row:
            sumF0 += parse_frac(x)
    fr["sumF0"] = sumF0
    residual = 3 * fr["c_A"] + 54 * fr["c_B"] + 27 * fr["c_C"] - 9 * sumF0 - fr["e"]
    if residual != 0:
        fail(f"G5·A3 重算归一化 3c_A+54c_B+27c_C−9·ΣF⁽⁰⁾−e = {residual} != 0（Fraction 精确）")
    nr = r9.get("normalization_residual", "")
    if "3c_A+54c_B+27c_C" not in nr or "== 0" not in nr:
        fail(f"G5·A3 r9_s3_rederive.json normalization_residual 锚失配：{nr!r}")
    # ---- 源码语句逐字符模板比对（空白归一）----
    m = RE_L1_STMT.search(src)
    if not m:
        fail("G5·A3 源码缺 a3_l1_normalization 语句（regex 失配）")
    stmt = norm_ws(m.group(1))
    expect = norm_ws(
        f"3 * (0 : ℚ) + 54 * ({fr['c_B'].numerator} : ℚ) / {fr['c_B'].denominator}"
        f" + 27 * ({fr['c_C'].numerator} : ℚ) / {fr['c_C'].denominator}"
        f" - 9 * ({sumF0.numerator} : ℚ) / {sumF0.denominator}"
        f" - ({fr['e'].numerator} : ℚ) / {fr['e'].denominator} = 0")
    if fr["c_A"] != 0:
        fail(f"G5·A3 证书 c_A != 0：{fr['c_A']}")
    if stmt != expect:
        fail(f"G5·A3 源码语句与证书重算模板逐字符失配：\n  源码 {stmt}\n  模板 {expect}")
    # ---- r9 json 结构锚（三轨道口径＋271＋对称）----
    cc = r9.get("sizes", {}).get("class_counts", {})
    if cc.get("AAA") != "3类×1" or cc.get("AAB") != "6类×9" or cc.get("ABC") != "1类×27":
        fail(f"G5·A3 r9 sizes.class_counts 失配：{cc}")
    if r9.get("sizes", {}).get("Y_cols") != 271:
        fail(f"G5·A3 r9 sizes.Y_cols 失配：{r9.get('sizes', {}).get('Y_cols')!r}")
    sc = r9.get("structural_checks", {})
    if sc.get("Q_uv_symmetric_all_k") is not True:
        fail("G5·A3/A4 r9 structural_checks.Q_uv_symmetric_all_k != true")
    if sc.get("Y_cols_equals_271") is not True:
        fail("G5·A3/A4 r9 structural_checks.Y_cols_equals_271 != true")
    # ---- 84 分桶枚举独立复算 ----
    md = RE_TYPES_DIV.search(src)
    if not md:
        fail("G5·A3 源码缺 types 定义（fun i => i.val / d）")
    d = int(md.group(1))
    types = [i // d for i in range(9)]
    if types != [0, 0, 0, 1, 1, 1, 2, 2, 2]:
        fail(f"G5·A3 源码 types 字面量（除数 {d}）≠ (0,0,0,1,1,1,2,2,2)：{types}")
    buckets = {}
    for i, j, k in combinations(range(9), 3):
        b = tuple(sorted((types[i], types[j], types[k])))
        buckets[b] = buckets.get(b, 0) + 1
    cls = sorted(buckets)
    counts = [buckets[c] for c in cls]
    if len(list(combinations(range(9), 3))) != 84 or sum(counts) != 84:
        fail(f"G5·A3 独立枚举总数 {sum(counts)} != C(9,3)=84")
    if counts != [1, 9, 9, 9, 27, 9, 1, 9, 9, 1]:
        fail(f"G5·A3 独立枚举计数表失配：{counts}（应 [1,9,9,9,27,9,1,9,9,1]）")
    if 3 * 1 + 6 * 9 + 1 * 27 != 84:
        fail("G5·A3 配平 3·1+6·9+1·27 != 84（内部一致性）")
    # 与源码 classes 列表逐项比对
    mc = RE_CLASSES_LIST.search(src)
    if not mc:
        fail("G5·A3 源码缺 classes 列表（regex 失配）")
    src_classes = [tuple(int(x) for x in tup) for tup in
                   re.findall(r"\((\d+), (\d+), (\d+)\)", mc.group(1))]
    if src_classes != cls:
        fail(f"G5·A3 源码 classes 列表与独立枚举类序失配：{src_classes} vs {cls}")
    # 与源码 bucket_table 枚举表逐项比对
    mt = RE_BUCKET_TABLE.search(src)
    if not mt:
        fail("G5·A3 源码缺 bucket_table 枚举表（regex 失配）")
    src_table = [int(x) for x in mt.group(1).split(",")]
    if src_table != counts:
        fail(f"G5·A3 源码枚举表与独立复算失配：{src_table} vs {counts}")
    okmsg("G5 离线精确复核·A3：证书链 r9_s3_rederive.json→M9 证书重读，五字面量"
          f"（c_A={fr['c_A']}、c_B={fr['c_B'].numerator}/{fr['c_B'].denominator}、"
          f"c_C、e、ΣF⁽⁰⁾={sumF0.numerator}/{sumF0.denominator}）重算归一化==0 且与"
          "源码语句逐字符模板全等；84 分桶独立复算 == 源码 classes/枚举表"
          "（3·1+6·9+1·27=84）；r9 锚（class_counts/Y_cols=271/Q_uv_symmetric）全过")
    return {"residual": "0", "fractions": {k: f"{v.numerator}/{v.denominator}"
                                            for k, v in fr.items()},
            "classes": [list(c) for c in cls], "counts": counts}


# ---- A4 源码解析与对拍 ----
RE_Q_DEF = re.compile(
    r"def Q : ℕ → ℚ → ℚ → ℚ → ℚ\n"
    r"\s*\| 0, _, _, _ => (\d+)\n"
    r"\s*\| 1, u, v, t => (t - u \* v)\n"
    r"\s*\| j \+ 2, u, v, t =>\n"
    r"\s*(\d+) \* \(t - u \* v\) \* Q \(j \+ 1\) u v t - \(([^)]+)\) \* Q j u v t\n")
RE_SHAPE = re.compile(
    r"theorem (Q_(?:zero|one|two|three|four|five)) \(u v t : ℚ\) :\s*\n?"
    r"\s*Q (\d) u v t = (.*?) :=", re.S)
RE_KCOL = re.compile(
    r"theorem Kcol_two_three_one \(u v t : ℚ\) :\s*\n?"
    r"\s*Kcol (\d) (\d) (\d) u v t =\s*(.*?) :=", re.S)


def g5_a4(src: str) -> dict:
    # ---- def Q 字面量重构对拍 ----
    m = RE_Q_DEF.search(src)
    if not m:
        fail("G5·A4 源码缺 def Q 递推三臂（regex 失配）")
    b0_txt, b1_txt, mult_txt, om_txt = m.group(1), m.group(2), m.group(3), m.group(4)
    qs = independent_Q(5)
    for (u, v, t) in SAMPLE_POINTS:
        qsrc = [eval_q_expr(b0_txt, u, v, t), eval_q_expr(b1_txt, u, v, t)]
        for j in range(0, 4):   # 重构 Q_{j+2}，j+2 ≤ 5
            qsrc.append(int(mult_txt) * eval_q_expr("t - u * v", u, v, t) * qsrc[j + 1]
                        - eval_q_expr(om_txt, u, v, t) * qsrc[j])
        for k in range(6):
            want = poly_eval(qs[k], u, v, t)
            if qsrc[k] != want:
                fail(f"G5·A4 def Q 重构对拍失配：k={k} 点=({u},{v},{t}) "
                     f"源码字面量重构 {qsrc[k]} != 独立实现 {want}")
    # ---- k≤5 形状引理 RHS 文本求值对拍 ----
    shapes = RE_SHAPE.findall(src)
    names = [s[0] for s in shapes]
    if names != ["Q_zero", "Q_one", "Q_two", "Q_three", "Q_four", "Q_five"]:
        fail(f"G5·A4 形状引理集失配：{names}（应 Q_zero…Q_five 六条齐且序正确）")
    for (th_name, k_txt, rhs) in shapes:
        k = int(k_txt)
        if f"Q {k} u v t" not in src:
            fail(f"G5·A4 形状引理 {th_name} 左端与 k={k} 失配")
        for (u, v, t) in SAMPLE_POINTS:
            got = eval_q_expr(rhs, u, v, t)
            want = poly_eval(qs[k], u, v, t)
            if got != want:
                fail(f"G5·A4 形状引理 {th_name} 对拍失配：点=({u},{v},{t}) "
                     f"RHS 求值 {got} != 独立 Q_{k} {want}")
    # ---- ycol_count 独立复算 ----
    if not re.search(r"∑ k ∈ Finset\.range 6, \(9 - k\) \^ 2 = 271", src):
        fail("G5·A4 ycol_count 语句形状锚（∑ k ∈ Finset.range 6, (9 - k) ^ 2 = 271）缺失")
    ysum = sum((9 - k) ** 2 for k in range(6))
    if ysum != 271:
        fail(f"G5·A4 Y 列计数独立复算 {ysum} != 271")
    sizes = [9 - k for k in range(6)]
    if sum(s * s for s in sizes) != 271:
        fail("G5·A4 Y 列尺寸表复算失配（内部一致性）")
    # ---- stretch：Kcol_two_three_one RHS 对拍 ----
    mk = RE_KCOL.search(src)
    if not mk:
        fail("G5·A4 源码缺 Kcol_two_three_one 语句（regex 失配）")
    k, a, b = int(mk.group(1)), int(mk.group(2)), int(mk.group(3))
    if (k, a, b) == (0, 0, 0):
        fail("G5·A4 stretch 列 (k,a,b) 为平凡 (0,0,0)（应非平凡列）")
    kcol = independent_Kcol(qs, k, a, b)
    for (u, v, t) in SAMPLE_POINTS:
        got = eval_q_expr(mk.group(4), u, v, t)
        want = poly_eval(kcol, u, v, t)
        if got != want:
            fail(f"G5·A4 Kcol_two_three_one 对拍失配：点=({u},{v},{t}) "
                 f"RHS 求值 {got} != 独立 Kcol {want}")
    okmsg("G5 离线精确复核·A4：def Q 递推三臂字面量重构 × 5 点 × k≤5 与独立第二实现"
          "（ω=(1−u²)(1−v²) 乘积形）逐点对拍全等；Q_zero…Q_five 六条 RHS 文本求值"
          "对拍全等；ycol_count Σ_{k<6}(9−k)² 独立复算==271；stretch Kcol(2,3,1)"
          " 展开恒等式 5 点对拍全等")
    return {"def_literals": {"Q0": b0_txt, "Q1": b1_txt, "mult": int(mult_txt),
                             "omega": norm_ws(om_txt)},
            "shape_theorems": names, "ycol_sizes": sizes, "ycol_total": ysum,
            "kcol_kab": [k, a, b]}


# ------------------------------------------------------------------ NC
def nc1_sorry_injection(src3: str) -> None:
    tampered = src3.replace("  norm_num\n", "  sorry\n", 1)
    if "sorry" not in tampered:
        fail("NC1 预置失败：未能在 /tmp 副本注入 sorry（源码缺 `  norm_num` 行）")
    d = TMP / "nc1"
    (d / "ThomsonN9").mkdir(parents=True, exist_ok=True)
    (d / "ThomsonN9" / "TableA3.lean").write_text(tampered)
    lp = run(["lake", "env", "printenv", "LEAN_PATH"], LEAN_DIR).stdout.strip()
    env = gate_env()
    env["LEAN_PATH"] = f"{d}:{lp}"
    b = subprocess.run(["lean", "--root", str(d),
                        "-o", str(d / "ThomsonN9" / "TableA3.olean"),
                        str(d / "ThomsonN9" / "TableA3.lean")],
                       cwd=str(LEAN_DIR), env=env, capture_output=True, text=True,
                       timeout=580)
    if b.returncode != 0 or "declaration uses `sorry`" not in (b.stdout + b.stderr):
        fail(f"NC1 注入 sorry 后编译未产生 sorry 警告（exit {b.returncode}）：\n"
             f"{(b.stdout + b.stderr)[-500:]}")
    axfile = d / "axcheck.lean"
    axfile.write_text(
        "import ThomsonN9.TableA3\n"
        "#print axioms ThomsonN9.TableA3.a3_l1_normalization\n")
    a = subprocess.run(["lean", str(axfile)], cwd=str(LEAN_DIR), env=env,
                       capture_output=True, text=True, timeout=580)
    ax = parse_axiom_lines(a.stdout)
    th = "ThomsonN9.TableA3.a3_l1_normalization"
    caught = th in ax and ("sorryAx" in ax[th] or (ax[th] - ALLOWED_AXIOMS))
    if not caught:
        fail(f"NC1 失守：注入 sorry 后公理检查未现 sorryAx（{ax}）")
    okmsg(f"NC1 注入 sorry 必被 G3 拦：篡件公理集 = {sorted(ax.get(th, set()))}"
          "（含 sorryAx → G3 FAIL）")


def nc2_literal_tamper(src3: str, src4: str, r9: dict) -> None:
    # (a) c_B 分子 +1（任务书指定负对照；锚定语句内带 ℚ 标注的唯一形态，
    #     避免误中模块 docstring 里的同数字面量）
    bad_a3 = src3.replace("54 * (140609170236263 : ℚ)",
                          "54 * (140609170236264 : ℚ)", 1)
    if bad_a3 == src3:
        raise GateFail("NC2(a) 预置失败：未篡到 c_B 分子字面量 140609170236263（语句形态）")
    try:
        g5_a3(bad_a3, r9)
        raise GateFail("NC2(a) 失守：篡 c_B 分子＋1 后 G5·A3 未报错")
    except GateFail as e:
        if "失守" in str(e) or "预置" in str(e):
            raise
        print(f"[gate][NC2-a 检出] {e}")
    # (b) Q_two RHS 系数 4 → 5（A4 面对拍负对照）
    bad_a4 = src4.replace("- 4 * u * v * t", "- 5 * u * v * t", 1)
    if bad_a4 == src4:
        raise GateFail("NC2(b) 预置失败：未篡到 Q_two RHS 系数（- 4 * u * v * t）")
    try:
        g5_a4(bad_a4)
        raise GateFail("NC2(b) 失守：篡 Q_two 系数 4→5 后 G5·A4 未报错")
    except GateFail as e:
        if "失守" in str(e) or "预置" in str(e):
            raise
        print(f"[gate][NC2-b 检出] {e}")
    # sanity：原文件双函数 PASS（确定性结论不因复跑改变）
    g5_a3(src3, r9)
    g5_a4(src4)
    okmsg("NC2 篡字面量必被 G5 拦：c_B 分子＋1 与 Q_two 系数 4→5 双篡均被检出；"
          "原文件双函数 sanity PASS")


# ------------------------------------------------------------------ main
LEDGER = RESULTS / "r13_a3a4_ledger.json"


def main() -> None:
    t0 = time.time()
    print(f"[gate] r13_a3a4_gate.py seed={SEED_GATE}（确定性，无随机路径）")
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
    for p in (TABLEA3, TABLEA4, R9_JSON):
        if not p.is_file():
            fail(f"必各件不在场：{p}")
    src3 = TABLEA3.read_text()
    src4 = TABLEA4.read_text()
    r9 = json.loads(R9_JSON.read_text())

    gate0_ledger()
    gate1_ownership()
    walls2 = gate2_elaborate()
    ax_union = gate3_axioms()
    gate4_statement(src3, src4)
    g5_a3(src3, r9)
    g5_a4(src4)
    nc1_sorry_injection(src3)
    nc2_literal_tamper(src3, src4, r9)
    print(f"[gate] G2 elaboration 墙钟 TableA3={walls2['TableA3']}s／"
          f"TableA4={walls2['TableA4']}s；全门 {time.time() - t0:.1f}s")


if __name__ == "__main__":
    main()
