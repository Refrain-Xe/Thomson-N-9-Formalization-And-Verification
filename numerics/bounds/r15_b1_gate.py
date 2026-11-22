#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r15_b1_gate.py — R15B 表 B 第三件 B1（l4_orbit (P5) 实现证书＋轨道配平）验收门
（G0–G5＋负对照 NC1/NC2/NC3）.

任务书口径（r15b-tableb-b1，D61 裁决 3）：B1 算术层 Lean 化——45 逐对 Gram
恒等式（模曲线 ring 证书，乘子＝发射器精确生成）＋分类桥＋六类边计数
6/6/3/3/6/12==36＋逐顶点轮廓＋Σ_y==2·mult 配平＋z 盒节点分离容器。
l4_orbit (P1)–(P4) 过滤枚举与『轨道维数/横截坐标』几何不在件内（边界如实，
docstring 双侧声明）。产出件 formal/lean/ThomsonN9/TableB1Data.lean（发射器
确定性生成，仅 import Mathlib）＋TableB1.lean（发射器确定性生成——r13_a1
emit_main_lean 先例，import Mathlib＋ThomsonN9.TableB1Data，零数值数据字面
量）。本门全确定性（无随机路径；抽查点 seed 20261017 复现为确定性重放），
PATH 自动前置 ~/.elan/bin（缺失即 FAIL 附信息）；CWD 无关（全部路径自
__file__ 推导）。heavySolves=0（本门零求解：仅 elaboration/公理/regex/
Fraction 复核）。

检查面（G0–G5＋NC1/NC2/NC3）：
  G0 账本在场与受控字段（seed == 20261017、heavy_solves == 0、自有八件在清单）。
  G1 文件所有权守卫：git status --porcelain 与 git diff HEAD --name-only 的全部
     改动路径 ⊆ 本任务自有八件（＋环境变量 R15B_G1_ALLOW_FOREIGN 自跑逐件放行
     〔默认关——预提交口径：notes/decisions.md 共享 append-only 件，B5 R14A
     先例〕＋PARALLEL_FAMILY r15 家族放行层〔D61-5：R15A TableB6 族/R15C 预研
     /R15D 收口 含 endgame_gate.py campaign-10 扩展面与 decisions.md 追加
     面——R15A 0cba187 已提交门同式放行 endgame_gate.py，对称收编；decisions.md
     为共享 append-only 裁决账（历轮收口均追加其裁决节，R14B D58/R14C D59 同源），
     G2–G5 不读该两件零削弱；本门自有八件仍严格 OWNED）；两只读输入件 results/local_min.json 与 results/
     l4_orbit.json 显式 git diff 守卫（单独响亮报错）。
  G2 逐文件 elaboration：子进程 `lake env lean -o <olean> ThomsonN9/TableB1Data.lean`
     然后 `… ThomsonN9/TableB1.lean`（依赖序；均 CWD=formal/lean），各 exit 0、
     输出无 error／无 sorry、墙钟 ≤ 600 s/文件（D52 裁决 4）。
  G3 公理：检查件 import 两模块＋对**两文件全部 theorem**（regex 枚举，≥80 件）
     #print axioms——公理集 ⊆ {propext, Classical.choice, Quot.sound}，零
     sorryAx/ofReduceBool/ofReduceNat/trustCompiler。
  G4 语句锚（行号 regex）＋零数值数据字面量守卫＋非交叠守卫：行原子 def 九件/
     ν 曲线六件/45 Gram 定理头/证书形状（M1·(s3R·s3R−3)+M2·(rhoR z·rhoR z+
     z^2−1)）/分类桥/对角归一 ∀ 包装/计数四件/轮廓两件/Σ_y/容器定理/节点链/
     两两分离/Data 不交链与端点事实/抽查三定理；主件零 `def … : ℚ :=` 与零
     ≥15 位数字面量；Solution/TableA*/M1Data/TableB5*/根模块/lake 面 零 TableB1
     引用。
  G5 离线精确复核（stdlib Fraction 零仓 import，独立于 r15_b1_data.py 的门内
     第二实现——行参数化取 l4_orbit.family_points_s3 ×2 整数表独立重导，
     符号元＝dict {(rdeg, sdeg): [z 次数系数表]}，与发射器 {(zdeg,rdeg,sdeg):
     Fr} 平面 dict 异构编码）：
     (a) z 盒三方：源码 zLo/zHi ↔ local_min.json zStarIntervalMpmath 逐位＋
         l4_orbit.json inputs.zBox 严格外扩（orb_lo < zLo < zHi < orb_hi）；
     (b) 36 条目分类三方：门内几何分类（曲线匹配）↔ 门内算术规则 ↔
         l4_orbit.json orbitBalance（六类计数/轮廓/Σ_y）；主件计数定理字面量
         （edgeMult/prismProf/capProf/2·mult/36）与门内重算对账；
     (c) 证书乘子对账：主件 45 key 语句的 M1/M2 文本 ↔ 门内归约再生成（渲染
         同一规范文法）逐字节；行/ν 定义文本 ↔ 门内表驱动渲染；
     (d) 容器三方：源码 25 ℚ def ↔ 门内重算（Newton ρ 包同族算法独立重写＋
         端点公式）↔ json 记录；五链不交复核；真值范围⊆外扩(1e-15) json 节点
         区间复核；抽查点 seed 复放（3 点 z/ρ 包/ν 容器包含性）。
  NC1 注入 sorry 必被 G3 拦：/tmp 副本把 zLo_pos 证明改 sorry → 独立编译必现
     sorry 警告＋公理检查必现 sorryAx（未篡原件 sanity：G3 全件过）。
  NC2 篡行坐标必被 G5 拦：/tmp 副本把 Data rowT1 的 z 坐标 z→1 硬编码 →
     G5(c) 行定义文本对账＋证书再生成对账必 FAIL（原文件 sanity PASS）。
  NC3 篡容器端点越隔离区间必被 G5 拦：/tmp 副本把 nu4Hi＋1/8（侵入 ν₅ 容器）
     → G5(d) 容器三方比对＋五链不交复核必 FAIL 且首错命题为容器失配
     （首错命题断言防假拦截，R13C 先例）。

用法（CWD 无关）：
  python3 numerics/bounds/r15_b1_gate.py     # 全门（exit 0 = 过）
  python3 thomson-n9/numerics/bounds/r15_b1_gate.py
      # ↑ CWD＝仓库根时的验收命令命中同名 runpy 包装器（沿 R10A 0087eab／
      #   R13C r13_a1／R14A r14_b5 先例，包装器重定向到真实门）
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

SEED_GATE = 20261017                   # R15B 统一 seed（任务书）
ELAB_LIMIT_S = 600                     # G2 每文件 ≤10 min（D52 裁决 4）
ZGRID = 1 << 40                        # 抽查 z 网格（与发射器同一文档化方案）
SQBITS = 200                           # 门内 Newton ρ 包精度（B5 同族）

DATA_REL = "formal/lean/ThomsonN9/TableB1Data.lean"
MAIN_REL = "formal/lean/ThomsonN9/TableB1.lean"
GATE_REL = "numerics/bounds/r15_b1_gate.py"
WRAPPER_REL = "thomson-n9/numerics/bounds/r15_b1_gate.py"   # CWD 兼容包装器
DATAPY_REL = "numerics/bounds/r15_b1_data.py"
DATAJSON_REL = "numerics/bounds/results/r15_b1_data.json"
LEDGER_REL = "numerics/bounds/results/r15_b1_ledger.json"
NOTES_REL = "notes/tableb-lean.md"
OWNED = {DATA_REL, MAIN_REL, GATE_REL, WRAPPER_REL, DATAPY_REL,
         DATAJSON_REL, LEDGER_REL, NOTES_REL}

LM_REL = "numerics/bounds/results/local_min.json"      # 只读输入（z 盒隔离源）
ORB_REL = "numerics/bounds/results/l4_orbit.json"      # 只读输入（记录面）
FROZEN_READONLY = (LM_REL, ORB_REL)

# 并行家族放行集（D61-5：R15A TableB6 族／R15C 预研／R15D 收口；家族外字面拦截）。
# endgame_gate.py＝R15D 收口件的 campaign-10 增补式扩展面（R14B 先例同源）——
# R15A 已提交门 r15_b6_gate.py:120 同式放行（0cba187），本门对称收编；本门的
# 数值被验面（G2–G5）不读该件，放行零削弱。r15 泛式 pattern＝R15A 同款
# （自有件先命中 OWNED 分支，不受影响）。
PARALLEL_FAMILY = [
    r"^numerics/bounds/r15[a-z0-9_]*(\.py|/)",
    r"^numerics/bounds/results/r15[a-z0-9_]*(\.json|/)",
    r"^thomson-n9/numerics/bounds/r15[a-z0-9_]*(\.py|/)",
    r"^formal/lean/ThomsonN9/TableB6[a-zA-Z0-9/]*",
    r"^numerics/bounds/endgame_gate\.py$",
    r"^notes/b5-core-study\.md$",
    r"^notes/decisions\.md$",
    r"^(GAP-REPORT|PROGRESS)\.md$",
]

# 非交叠守卫面（表 A/M1/Solution/B5 面＋根模块/lake 面，零交叠机器化）
NONOVERLAP_FILES = ("ThomsonN9/Solution.lean", "ThomsonN9/TableA.lean",
                    "ThomsonN9/TableA1.lean", "ThomsonN9/TableA3.lean",
                    "ThomsonN9/TableA4.lean", "ThomsonN9/TableA6.lean",
                    "ThomsonN9/M1Data.lean", "ThomsonN9/TableB5.lean",
                    "ThomsonN9/TableB5Data.lean", "ThomsonN9.lean",
                    "lakefile.toml", "scripts/check.sh")

TMP = Path("/tmp/r15_b1_gate")
OLEAN_REL = ".lake/build/lib/lean/ThomsonN9"
DATA_LEAN = LEAN_DIR / "ThomsonN9" / "TableB1Data.lean"
MAIN_LEAN = LEAN_DIR / "ThomsonN9" / "TableB1.lean"
LEDGER = RESULTS / "r15_b1_ledger.json"
LM_JSON = RESULTS / "local_min.json"
ORB_JSON = RESULTS / "l4_orbit.json"

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN_AXIOMS = ("sorryAx", "ofReduceBool", "ofReduceNat", "trustCompiler")

ROWS = ["T0", "T1", "T2", "B0", "B1", "B2", "C0", "C1", "C2"]
NU_NAMES = ["nu1", "nu2", "nu3", "nu4", "nu5", "nu6"]
MULTS = [6, 6, 3, 3, 6, 12]

F0, F1, FHALF = Fr(0), Fr(1), Fr(1, 2)


class GateFail(Exception):
    """单门失守（main 统一转 [gate][FAIL]＋exit 1；负对照捕获它作预期检出）。"""


def fail(msg: str) -> None:
    raise GateFail(msg)


def okmsg(msg: str) -> None:
    print(f"[gate][ok] {msg}", flush=True)


def sha256_of(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def fs(f: Fr) -> str:
    return f"{f.numerator}/{f.denominator}"


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
            if " -> " in p:
                p = p.split(" -> ")[-1]
            paths.append(p)
    return paths


def gate1_ownership():
    # 三层放行：① OWNED（本任务八件）；② 环境变量 R15B_G1_ALLOW_FOREIGN（自跑
    # 专用逐件放行，默认关——预提交口径：notes/decisions.md 共享 append-only 件，
    # R14A 先例）；③ PARALLEL_FAMILY pattern（D61-5 r15 家族放行层）。三层之外
    # 字面拦截。
    allow_foreign = {q.strip() for q in
                     os.environ.get("R15B_G1_ALLOW_FOREIGN", "").split(",") if q.strip()}
    for cmd in (["git", "status", "--porcelain"], ["git", "diff", "HEAD", "--name-only"]):
        r = run(cmd, REPO)
        if r.returncode != 0:
            raise GateFail(f"G1 {cmd[1]} 失败：{r.stderr.strip()[:300]}")
        paths = porcelain_paths(r.stdout) if "--porcelain" in cmd else \
            [ln.strip().strip('"') for ln in r.stdout.splitlines() if ln.strip()]
        for p in paths:
            if p in OWNED or p in allow_foreign:
                continue
            if any(re.match(pat, p) for pat in PARALLEL_FAMILY):
                print(f"[gate][G1][并行家族放行] r15 家族在途件（D61-5 pattern）：{p}")
                continue
            raise GateFail(
                f"G1 树上出现非本任务自有件（{cmd[1]}）：{p!r}"
                f"（自有集={sorted(OWNED)}；r15 家族放行集 D61-5 未覆盖该路径——"
                f"若确系 R15A/R15C/R15D 在途件，可设 R15B_G1_ALLOW_FOREIGN={p} 显式放行）")
    # 两只读输入件守卫（显式单列，响亮报错；独立于放行集）
    for rel in FROZEN_READONLY:
        r = run(["git", "diff", "HEAD", "--", rel], REPO)
        if r.returncode != 0 or r.stdout.strip():
            fail(f"G1 只读守卫失守：{rel} 相对 HEAD 有改动（local_min.json/l4_orbit.json 为冻结只读面）")
    okmsg("G1 文件所有权守卫：git status/diff 相对 HEAD 仅自有八件／r15 家族放行件"
          "（或全净）；local_min.json 与 l4_orbit.json 只读守卫空 diff")


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
    wall_data = compile_lean("ThomsonN9/TableB1Data.lean", "TableB1Data.olean")
    okmsg(f"G2 elaboration：TableB1Data.lean exit 0 无 error/sorry（{wall_data:.1f}s ≤ 600s）")
    wall_main = compile_lean("ThomsonN9/TableB1.lean", "TableB1.olean")
    okmsg(f"G2 elaboration：TableB1.lean exit 0 无 error/sorry（{wall_main:.1f}s ≤ 600s；"
          "两件依赖序编译，olen 落 .lake/build 供 G3/主件 import 复用）")
    return {"data_s": round(wall_data, 1), "main_s": round(wall_main, 1)}


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


def gate3_axioms(src_data: str, src_main: str) -> dict:
    names = ([f"ThomsonN9.TableB1Data.{t}" for t in theorem_names(src_data)]
             + [f"ThomsonN9.TableB1.{t}" for t in theorem_names(src_main)])
    if len(names) < 80:
        fail(f"G3 定理枚举异常偏少：{len(names)}（应 ≈88）")
    TMP.mkdir(parents=True, exist_ok=True)
    axfile = TMP / "axcheck.lean"
    axfile.write_text("import ThomsonN9.TableB1Data\nimport ThomsonN9.TableB1\n"
                      + "".join(f"#print axioms {t}\n" for t in names))
    r = run(["lake", "env", "lean", str(axfile)], LEAN_DIR)
    if r.returncode != 0:
        fail(f"G3 公理检查件编译失败（exit {r.returncode}）：\n"
             f"{r.stdout[-500:]}\n{r.stderr[-500:]}")
    ax = parse_axiom_lines(r.stdout)
    check_axioms(ax, names, "G3 公理")
    return {"theorems": len(names)}


# ------------------------------------------------------------------ G4
def gate4_statement(src_data: str, src_main: str) -> None:
    if re.findall(r"^import\s+\S+", src_data, re.M) != ["import Mathlib"]:
        fail("G4 TableB1Data.lean import 行失配（应恰为 [import Mathlib]）")
    if re.findall(r"^import\s+\S+", src_main, re.M) != \
            ["import Mathlib", "import ThomsonN9.TableB1Data"]:
        fail("G4 TableB1.lean import 行失配（应恰为 "
             "[import Mathlib, import ThomsonN9.TableB1Data]）")
    # 零数值数据字面量守卫（主件）：无 ℚ def、无 ≥15 位数字面量
    if re.findall(r"^def \w+ : ℚ :=", src_main, re.M):
        fail("G4 主件含 ℚ def（数值数据面必须全部锚定 Data 件）")
    if re.findall(r"\d{15,}", src_main):
        fail("G4 主件含 ≥15 位数字面量（数值数据面必须全部锚定 Data 件）")
    anchors = [
        # ---- Data 件：行原子 def（九件，坐标文本精确锚）
        (r"^noncomputable def rhoR \(z : ℝ\) : ℝ := Real\.sqrt \(1 - z\^2\)$", "rhoR 原子锚"),
        (r"^noncomputable def s3R : ℝ := Real\.sqrt 3$", "s3R 原子锚"),
        (r"^noncomputable def rowT0 \(z : ℝ\) : ℝ × ℝ × ℝ := \(rhoR z, 0, z\)$", "rowT0 锚"),
        (r"^noncomputable def rowT1 \(z : ℝ\) : ℝ × ℝ × ℝ := \(-\(rhoR z\)/2, s3R \* rhoR z / 2, z\)$", "rowT1 锚"),
        (r"^noncomputable def rowT2 \(z : ℝ\) : ℝ × ℝ × ℝ := \(-\(rhoR z\)/2, -\(s3R \* rhoR z / 2\), z\)$", "rowT2 锚"),
        (r"^noncomputable def rowB0 \(z : ℝ\) : ℝ × ℝ × ℝ := \(rhoR z, 0, -z\)$", "rowB0 锚"),
        (r"^noncomputable def rowB1 \(z : ℝ\) : ℝ × ℝ × ℝ := \(-\(rhoR z\)/2, s3R \* rhoR z / 2, -z\)$", "rowB1 锚"),
        (r"^noncomputable def rowB2 \(z : ℝ\) : ℝ × ℝ × ℝ := \(-\(rhoR z\)/2, -\(s3R \* rhoR z / 2\), -z\)$", "rowB2 锚"),
        (r"^noncomputable def rowC0 : ℝ × ℝ × ℝ := \(1/2, s3R/2, 0\)$", "rowC0 锚"),
        (r"^noncomputable def rowC1 : ℝ × ℝ × ℝ := \(-1, 0, 0\)$", "rowC1 锚"),
        (r"^noncomputable def rowC2 : ℝ × ℝ × ℝ := \(1/2, -s3R/2, 0\)$", "rowC2 锚"),
        # ---- Data 件：ν 曲线六件
        (r"^noncomputable def nu1 \(z : ℝ\) : ℝ := -\(1 \+ z\^2\)/2$", "nu1 曲线锚"),
        (r"^noncomputable def nu2 \(z : ℝ\) : ℝ := -\(rhoR z\)$", "nu2 曲线锚"),
        (r"^noncomputable def nu3 \(z : ℝ\) : ℝ := -1/2$", "nu3 曲线锚"),
        (r"^noncomputable def nu4 \(z : ℝ\) : ℝ := 1 - 2\*z\^2$", "nu4 曲线锚"),
        (r"^noncomputable def nu5 \(z : ℝ\) : ℝ := \(3\*z\^2 - 1\)/2$", "nu5 曲线锚"),
        (r"^noncomputable def nu6 \(z : ℝ\) : ℝ := rhoR z / 2$", "nu6 曲线锚"),
        # ---- Data 件：容器端点事实＋不交链＋ρ 包前提
        (r"theorem nu1Lo_eq : nu1Lo = -\(1 \+ zHi\^2\)/2", "ν₁ 端点事实锚"),
        (r"theorem nu4Hi_eq : nu4Hi = 1 - 2\*zLo\^2", "ν₄ 端点事实锚"),
        (r"theorem nu5Lo_eq : nu5Lo = \(3\*zLo\^2 - 1\)/2", "ν₅ 端点事实锚"),
        (r"theorem rhoDn_sq_le : rhoDn\^2 ≤ 1 - zHi\^2", "ρ 包前提①锚"),
        (r"theorem rhoUp_sq_ge : 1 - zLo\^2 ≤ rhoUp\^2", "ρ 包前提②锚"),
        (r"theorem nu_chain_disjoint :\n    nu1Hi < nu2Lo ∧ nu2Hi < nu3Lo ∧ nu3Hi < nu4Lo", "容器五链不交锚"),
        # ---- 主件：45 Gram 定理头与证书形状
        (r"theorem gram_T0_T1 \(z : ℝ\) \(hz : z\^2 ≤ 1\) :\n    dot3 \(rowT0 z\) \(rowT1 z\) = nu5 z", "gram_T0_T1 头锚"),
        (r"theorem gram_T1_T2 \(z : ℝ\) \(hz : z\^2 ≤ 1\) :\n    dot3 \(rowT1 z\) \(rowT2 z\) = nu5 z", "gram_T1_T2 头锚"),
        (r"theorem gram_diag_T0 \(z : ℝ\) \(hz : z\^2 ≤ 1\) :\n    dot3 \(rowT0 z\) \(rowT0 z\) = 1", "gram_diag_T0 头锚"),
        (r"\* \(s3R \* s3R - 3\)\n        \+ .*\* \(rhoR z \* rhoR z \+ z\^2 - 1\) := by", "证书两槽形状锚"),
        # ---- 主件：桥接＋对角归一
        (r"theorem gram_nodeOfN \(z : ℝ\) \(hz : z\^2 ≤ 1\) : ∀ k l : ℕ, k < 9 → l < 9 → k < l →", "分类桥定理头锚"),
        (r"    dot3 \(rowOfN k z\) \(rowOfN l z\) = nuOfN \(nodeOfN k l\) z := by", "分类桥命题形状锚"),
        (r"theorem diag_norm_all \(z : ℝ\) \(hz : z\^2 ≤ 1\) : ∀ k : ℕ, k < 9 →", "对角归一 ∀ 包装锚"),
        # ---- 主件：计数配平＋轮廓＋Σ_y
        (r"def edgeMult : ℕ → ℕ\n  \| 0 => 6 \| 1 => 6 \| 2 => 3 \| 3 => 3 \| 4 => 6 \| _ => 12", "edgeMult 六类计数锚"),
        (r"theorem edge_counts : ∀ c : Fin 6, \(Finset\.univ\.filter \(fun p : Fin 9 × Fin 9 =>", "六类边计数定理锚"),
        (r"theorem edge_total : \(Finset\.univ\.filter \(fun p : Fin 9 × Fin 9 =>\n    p\.1\.val < p\.2\.val\)\)\.card = 36 := by decide", "36 总数锚"),
        (r"def prismProf : ℕ → ℕ\n  \| 0 => 2 \| 1 => 1 \| 2 => 0 \| 3 => 1 \| 4 => 2 \| _ => 2", "棱顶轮廓锚"),
        (r"def capProf : ℕ → ℕ\n  \| 0 => 0 \| 1 => 2 \| 2 => 2 \| 3 => 0 \| 4 => 0 \| _ => 4", "帽顶轮廓锚"),
        (r"theorem prism_profile : ∀ \(v : Fin 9\) \(c : Fin 6\), v\.val < 6 →", "棱顶轮廓定理锚"),
        (r"theorem cap_profile : ∀ \(v : Fin 9\) \(c : Fin 6\), 6 ≤ v\.val →", "帽顶轮廓定理锚"),
        (r"theorem sigma_y_balance : ∀ c : Fin 6,", "Σ_y 配平定理头锚"),
        (r"    = 2 \* edgeMult c\.val := by decide", "Σ_y==2·mult 形状锚"),
        # ---- 主件：容器＋分离
        (r"theorem nu_containers \(z : ℝ\) \(h1 : \(zLo:ℝ\) ≤ z\) \(h2 : z ≤ \(zHi:ℝ\)\) :", "ν 容器定理头锚"),
        (r"theorem node_chain \(z : ℝ\) \(h1 : \(zLo:ℝ\) ≤ z\) \(h2 : z ≤ \(zHi:ℝ\)\) :\n    nu1 z < nu2 z", "节点链锚"),
        (r"theorem node_values_distinct \(z : ℝ\) \(h1 : \(zLo:ℝ\) ≤ z\) \(h2 : z ≤ \(zHi:ℝ\)\) :", "两两分离定理头锚"),
        (r"    ∀ k l : ℕ, k < 6 → l < 6 → k ≠ l → nuOfN k z ≠ nuOfN l z := by", "两两分离命题形状锚"),
        # ---- 主件：nodeOfN 分类函数
        (r"def nodeOfN : ℕ → ℕ → ℕ", "nodeOfN 分类函数锚"),
    ]
    both = src_data + "\n" + src_main
    for pat, name in anchors:
        if not re.search(pat, both, re.M):
            fail(f"G4 语句锚缺失：{name}（pattern {pat!r}）")
    spots = sorted(re.findall(r"^theorem spot(\d)_containers", src_data, re.M))
    if spots != ["0", "1", "2"]:
        fail(f"G4 抽查定理失配：spot_containers{spots}（应 0/1/2）")
    n_gram = len(re.findall(r"^theorem gram_", src_main, re.M))
    if n_gram != 46:                     # 45 逐对＋桥接 gram_nodeOfN
        fail(f"G4 主件 gram_* 定理数失配：{n_gram}（应 46=45 逐对＋1 桥接）")
    # 非交叠守卫（TableA* 含分块子目录 TableA6/）
    nonoverlap = list(NONOVERLAP_FILES)
    for p in sorted((LEAN_DIR / "ThomsonN9").glob("TableA*.lean")):
        nonoverlap.append(str(p.relative_to(LEAN_DIR)))
    for p in sorted((LEAN_DIR / "ThomsonN9" / "TableA6").glob("*.lean")) \
            if (LEAN_DIR / "ThomsonN9" / "TableA6").is_dir() else []:
        nonoverlap.append(str(p.relative_to(LEAN_DIR)))
    for rel in nonoverlap:
        p = LEAN_DIR / rel
        if p.is_file() and "TableB1" in p.read_text():
            fail(f"G4 非交叠守卫：{rel} 含 'TableB1'（本件必须不被表 A/M1/B5/Solution 面引用）")
    okmsg("G4 语句锚：import 面恰 [Mathlib]/[Mathlib＋TableB1Data]；43 锚＋3 抽查定理＋"
          "46 gram 定理数；主件零 ℚ def／零 ≥15 位字面量；Solution/TableA*/M1Data/"
          "TableB5*/根模块/lakefile/check.sh 零 TableB1 引用")


# ------------------------------------------------------------------ G5 门内独立第二实现
def sqrt_rat(q: Fr, side: str) -> Fr:
    """√q 有理包（门内独立重实现；上界 isqrt(⌊q·2^(2p)⌋+1)+1、下界 isqrt）。"""
    p = SQBITS
    num, den = q.numerator, q.denominator
    if side == "lo":
        return Fr(math.isqrt((num << (2 * p)) // den), 1 << p)
    return Fr(math.isqrt((num << (2 * p)) // den + 1) + 1, 1 << p)


class GateEngine:
    """门内独立符号引擎：元 = dict {(rdeg, sdeg): [z⁰, z¹, z², …]}（ℚ 系数表）。

    与发射器的平面 dict {(zdeg, rdeg, sdeg): Fr} 异构编码；行参数化取
    l4_orbit.family_points_s3 的 ×2 整数表（tri_cos/tri_sin/cap_cos/cap_sin）
    独立重导——与发射器的显式半系数模板不同代码路径。
    """

    TRICOS = [2, -1, -1]
    TRISIN = [0, 1, -1]
    CAPCOS = [1, -2, 1]
    CAPSIN = [1, 0, -1]

    def __init__(self):
        self.rows = self._rows()

    # -- 元构造：z 多项式系数表乘 (r^b s^c) --
    @staticmethod
    def el(coeffs, b=0, c=0):
        return {(b, c): list(coeffs)}

    ZERO = {}

    @staticmethod
    def const(q, b=0, c=0):
        return {(b, c): [Fr(q)]}

    @classmethod
    def _rows(cls):
        rows = []
        R = cls.const(1, b=1)                    # ρ
        S = cls.const(1, c=1)                    # √3
        RS = None
        for zsgn in (1, -1):
            zc = cls.el([F0, Fr(zsgn)])
            for k in range(3):
                # (ρ·tri_cos[k]/2, √3·ρ·tri_sin[k]/2, ±z)
                x = cls._scale(R, Fr(cls.TRICOS[k], 2))
                if cls.TRISIN[k] == 0:
                    y = cls.ZERO
                else:
                    y = cls._scale(cls._mul(R, S, None), Fr(cls.TRISIN[k], 2))
                rows.append([x, y, zc])
        for k in range(3):
            x = cls.const(Fr(cls.CAPCOS[k], 2))
            y = cls.ZERO if cls.CAPSIN[k] == 0 else cls._scale(S, Fr(cls.CAPSIN[k], 2))
            rows.append([x, y, cls.ZERO])
        return rows

    NU = None                                    # 类级惰子见 _nu()

    @classmethod
    def _nu(cls):
        z2 = cls.el([F0, F0, F1])
        one = cls.const(1)
        rho = cls.const(1, b=1)
        return [cls._add(cls._scale(one, -1), cls._scale(z2, -1)),   # 2ν₁
                cls._scale(rho, -2),                                  # 2ν₂
                cls.const(-2),                                        # 2ν₃
                cls._add(cls.const(2), cls._scale(z2, -4)),           # 2ν₄
                cls._add(cls._scale(z2, 3), cls.const(-1)),           # 2ν₅
                rho]                                                  # 2ν₆

    # -- 运算（r² = 1−z²、s² = 3 代入归约）--
    @staticmethod
    def _add(a, b):
        out = {}
        for k in set(a) | set(b):
            va, vb = a.get(k, [F0]), b.get(k, [F0])
            n = max(len(va), len(vb))
            v = [va[i] if i < len(va) else F0 for i in range(n)]
            for i, x in enumerate(vb):
                v[i] = v[i] + x
            v = [x for x in v if True]
            if any(x != 0 for x in v):
                out[k] = v
        return out

    @staticmethod
    def _zmul(x, y):
        out = [F0] * (len(x) + len(y) - 1)
        for i, cx in enumerate(x):
            if cx == 0:
                continue
            for j, cy in enumerate(y):
                out[i + j] += cx * cy
        return out

    @classmethod
    def _one_m_z2(cls):
        return [F1, F0, -F1]

    @classmethod
    def _mul(cls, a, b, _rs=None):
        out = {}
        for (b1, c1), x in a.items():
            for (b2, c2), y in b.items():
                bb, cc = b1 + b2, c1 + c2
                coef = cls._zmul(x, y)
                if cc >= 2:
                    cc -= 2
                    coef = [3 * t for t in coef]
                if bb >= 2:
                    bb -= 2
                    coef = cls._zmul(coef, cls._one_m_z2())
                key = (bb, cc)
                if key in out:
                    merged = cls._add({key: out[key]}, {key: coef})
                    out[key] = merged[key]
                else:
                    out[key] = coef
        return {k: v for k, v in out.items() if any(t != 0 for t in v)}

    @staticmethod
    def _scale(a, q):
        return {k: [t * q for t in v] for k, v in a.items()}

    @classmethod
    def dot(cls, i, j):
        acc = {}
        for x, y in zip(cls._rows_cache[0][i], cls._rows_cache[0][j]):
            acc = cls._add(acc, cls._mul(x, y, None))
        return acc


GateEngine._rows_cache = (None,)


def _ge_setup():
    if GateEngine._rows_cache[0] is None:
        eng = GateEngine()
        GateEngine._rows_cache = (eng.rows,)
        GateEngine.NU = GateEngine._nu()


# ---- 自由代数（无关系版，证书归约用）：复用 dict {(rdeg,sdeg): [z 表]} ----
def gfree_dot(eng_rows, i, j):
    """自由代数乘法（不做 ρ²/s² 归约）：返回 {(rdeg, sdeg): z 表}。"""
    out = {}
    for x, y in zip(eng_rows[i], eng_rows[j]):
        for (b1, c1), zx in x.items():
            for (b2, c2), zy in y.items():
                key = (b1 + b2, c1 + c2)
                prod = [F0] * (len(zx) + len(zy) - 1)
                for ii, cx in enumerate(zx):
                    if cx == 0:
                        continue
                    for jj, cy in enumerate(zy):
                        prod[ii + jj] += cx * cy
                if key in out:
                    cur = out[key]
                    n = max(len(cur), len(prod))
                    m = [cur[t] if t < len(cur) else F0 for t in range(n)]
                    for t, p_ in enumerate(prod):
                        m[t] += p_
                    out[key] = m
                else:
                    out[key] = prod
    return {k: v for k, v in out.items() if any(t != 0 for t in v)}


def gfree_nu(k):
    z2 = {(0, 0): [F0, F0, F1]}
    one = {(0, 0): [F1]}
    rho = {(1, 0): [F1]}
    return [
        _gscale(_gadd(one, z2), Fr(-1, 2)),          # ν₁ = −(1+z²)/2
        _gscale(rho, -1),                            # ν₂
        {(0, 0): [Fr(-1, 2)]},                       # ν₃
        _gadd(one, _gscale(z2, -2)),                 # ν₄
        _gscale(_gadd(_gscale(z2, 3), _gscale(one, -1)), FHALF),  # ν₅
        _gscale(rho, FHALF),                         # ν₆
    ][k]


def _gadd(a, b):
    out = {}
    for k in set(a) | set(b):
        va, vb = a.get(k, []), b.get(k, [])
        n = max(len(va), len(vb))
        v = [va[i] if i < len(va) else F0 for i in range(n)]
        for i, x in enumerate(vb):
            v[i] = v[i] + x
        if any(t != 0 for t in v):
            out[k] = v
    return out


def _gscale(a, q):
    return {k: [t * q for t in v] for k, v in a.items() if q != 0}


def _gzmul(x, y):
    out = [F0] * (len(x) + len(y) - 1)
    for i, cx in enumerate(x):
        if cx == 0:
            continue
        for j, cy in enumerate(y):
            out[i + j] += cx * cy
    return out


def gfree_reduce(D):
    """自由元归约：D == C1·(s²−3) + C2·(ρ²−(1−z²)) + D'，D' 的 rdeg/sdeg ≤ 1。

    返回 (C1, C2)（同为自由元）；D' == {} ⇔ 恒等式成立（调用方断言）。
    """
    C1, C2 = {}, {}
    D = {k: list(v) for k, v in D.items()}
    while True:
        offenders = [k for k, v in D.items() if any(t != 0 for t in v)
                     and (k[0] >= 2 or k[1] >= 2)]
        if not offenders:
            break
        k = max(offenders, key=lambda t: (t[1], t[0]))
        b, c = k
        coef = D[k]
        if c >= 2:
            step = {(b, c - 2): coef}
            C1 = _gadd(C1, step)
            D = _gadd(_gadd(D, {k: [-t for t in coef]}), _gscale(step, 3))
        else:
            step = {(b - 2, c): coef}
            C2 = _gadd(C2, step)
            D = _gadd(_gadd(D, {k: [-t for t in coef]}),
                      {(b - 2, c): _gzmul(coef, [F1, F0, -F1])})
    return C1, C2, D


# ---- 门内渲染器（与发射器同一规范文法、独立实现） --------------------------
def g_rat(c: Fr) -> str:
    if c.denominator == 1:
        return f"({c.numerator}:ℝ)"
    if c < 0:
        return f"(-({abs(c.numerator)}/{c.denominator}:ℝ))"
    return f"({c.numerator}/{c.denominator}:ℝ)"


def g_render(P) -> str:
    if not P or all(all(t == 0 for t in v) for v in P.values()):
        return "(0:ℝ)"
    flat = {}
    for (b, c), zs in P.items():
        for a, t in enumerate(zs):
            if t != 0:
                flat[(a, b, c)] = t
    if not flat:
        return "(0:ℝ)"
    terms = []
    for (a, b, c) in sorted(flat.keys()):
        v = flat[(a, b, c)]
        facs = []
        if a == 1:
            facs.append("z")
        elif a >= 2:
            facs.append(f"z^{a}")
        facs += ["rhoR z"] * b
        facs += ["s3R"] * c
        terms.append(g_rat(v) + (" * " + " * ".join(facs) if facs else ""))
    return " + ".join(terms)


def g_row_text(i) -> str:
    """门内表驱动行渲染（×2 整数表 → 规范坐标文本；i 为行号 0–8）。"""
    if i < 6:
        k = i % 3
        x = "rhoR z" if GateEngine.TRICOS[k] == 2 else "-(rhoR z)/2"
        if GateEngine.TRISIN[k] == 0:
            y = "0"
        else:
            y = ("s3R * rhoR z / 2" if GateEngine.TRISIN[k] == 1
                 else "-(s3R * rhoR z / 2)")
        zs = "z" if i < 3 else "-z"
        return f"({x}, {y}, {zs})"
    k = i - 6
    x = f"{GateEngine.CAPCOS[k]}/2" if GateEngine.CAPCOS[k] > 0 else "-1"
    if GateEngine.CAPSIN[k] == 0:
        y = "0"
    else:
        y = "s3R/2" if GateEngine.CAPSIN[k] == 1 else "-s3R/2"
    return f"({x}, {y}, 0)"


def g_row_arg(i):
    return f"(row{ROWS[i]} z)" if i < 6 else f"row{ROWS[i]}"


def g_node_rule(i, j):
    if i // 3 == j // 3:
        return 2 if i // 3 == 2 else 4
    if i // 3 == 2:
        return 1 if (i % 3 + 3 - j % 3) % 3 == 1 else 5
    if j // 3 == 2:
        return 1 if (j % 3 + 3 - i % 3) % 3 == 1 else 5
    return 3 if i % 3 == j % 3 else 0


def parse_data_defs(src: str) -> dict:
    out = {}
    for m in re.finditer(r"^def (\w+) : ℚ := (-?\d+/\d+)$", src, re.M):
        out[m.group(1)] = Fr(m.group(2))
    return out


def parse_certs(src_main: str) -> dict:
    """主件 45 key 语句的 (M1, M2) 原文抽取。"""
    out = {}
    for m in re.finditer(
            r"^theorem (gram_\w+) \(z : ℝ\) \(hz : z\^2 ≤ 1\) :\n"
            r"    dot3 (.*?) = (.*?) := by\n"
            r"(?:.*\n)*?"
            r"      = (.*?) \* \(s3R \* s3R - 3\)\n"
            r"        \+ (.*?) \* \(rhoR z \* rhoR z \+ z\^2 - 1\) := by",
            src_main, re.M):
        out[m.group(1)] = (m.group(2), m.group(3), m.group(4), m.group(5))
    return out


def g5_core(src_data: str, src_main: str) -> dict:
    """G5 主体（NC 复用；不改盘上件；src 可为篡改副本）。"""
    lm = json.loads(LM_JSON.read_text())
    orb = json.loads(ORB_JSON.read_text())
    parsed = parse_data_defs(src_data)
    need = {"zLo", "zHi", "rhoDn", "rhoUp"} | \
           {f"nu{k+1}{s}" for k in range(6) for s in ("Lo", "Hi")} | \
           {f"spotZ{k}" for k in range(3)} | \
           {f"spotRhoDn{k}" for k in range(3)} | {f"spotRhoUp{k}" for k in range(3)}
    if not need <= set(parsed):
        fail(f"G5 源码解析缺 def：缺 {sorted(need - set(parsed))}")

    # (a) z 盒三方：源码 ↔ local_min 逐位 ↔ l4_orbit zBox 严格外扩
    zl_s, zh_s = lm["zStarIntervalMpmath"].strip("[]").split(", ")
    lm_lo, lm_hi = Fr(zl_s.strip()), Fr(zh_s.strip())
    if parsed["zLo"] != lm_lo or parsed["zHi"] != lm_hi:
        fail("G5(a) z 盒三方失配：源码 zLo/zHi ≠ local_min zStarIntervalMpmath 端点")
    orb_lo, orb_hi = (Fr(s) for s in orb["inputs"]["zBox"])
    if not (orb_lo < parsed["zLo"] < parsed["zHi"] < orb_hi):
        fail("G5(a) z 盒三方失配：l4_orbit zBox 未严格外扩源码 z 盒")

    # (c1) 行/ν 定义文本 ↔ 门内表驱动渲染
    for i in range(9):
        if i < 6:
            pat = rf"^noncomputable def row{ROWS[i]} \(z : ℝ\) : ℝ × ℝ × ℝ := (.+)$"
        else:
            pat = rf"^noncomputable def row{ROWS[i]} : ℝ × ℝ × ℝ := (.+)$"
        m = re.search(pat, src_data, re.M)
        if not m:
            fail(f"G5(c) 行定义缺失：row{ROWS[i]}")
        if m.group(1).strip() != g_row_text(i):
            fail(f"G5(c) 行定义文本失配：row{ROWS[i]} 源码 {m.group(1).strip()!r} "
                 f"≠ 门内表驱动渲染 {g_row_text(i)!r}")
    nu_txt = ["-(1 + z^2)/2", "-(rhoR z)", "-1/2", "1 - 2*z^2",
              "(3*z^2 - 1)/2", "rhoR z / 2"]
    for k in range(6):
        m = re.search(rf"^noncomputable def {NU_NAMES[k]} \(z : ℝ\) : ℝ := (.+)$",
                      src_data, re.M)
        if not m or m.group(1).strip() != nu_txt[k]:
            fail(f"G5(c) ν 曲线定义文本失配：{NU_NAMES[k]}")

    # (c2) 证书乘子对账：门内归约再生成 ↔ 主件 key 文本逐字节
    _ge_setup()
    eng_rows = GateEngine._rows_cache[0]
    certs_txt = parse_certs(src_main)
    if len(certs_txt) != 45:
        fail(f"G5(c) 主件 key 语句解析数失配：{len(certs_txt)}（应 45）")
    cls_gate = {}
    for i in range(9):
        for j in range(i + 1, 9):
            D = gfree_dot(eng_rows, i, j)
            found = None
            for k in range(6):
                C1, C2, Dp = gfree_reduce(_gadd(D, _gscale(gfree_nu(k), -1)))
                if not Dp:
                    found = k
                    break
            if found is None:
                fail(f"G5(c) 门内几何分类失败：{ROWS[i]},{ROWS[j]} 无 ν 曲线匹配")
            cls_gate[(i, j)] = found
            name = f"gram_{ROWS[i]}_{ROWS[j]}"
            if name not in certs_txt:
                fail(f"G5(c) 主件缺 key 语句：{name}")
            lhs_dot, rhs, M1, M2 = certs_txt[name]
            if lhs_dot.strip() != f"{g_row_arg(i)} {g_row_arg(j)}" or \
                    rhs.strip() != f"{NU_NAMES[found]} z":
                fail(f"G5(c) {name} 定理头与门内分类失配（dot={lhs_dot}, rhs={rhs}）")
            if M1.strip() != g_render(C1) or M2.strip() != g_render(C2):
                fail(f"G5(c) {name} 证书乘子失配：M1 源码 {M1.strip()!r} ≠ 门内 "
                     f"{g_render(C1)!r}／M2 源码 {M2.strip()!r} ≠ 门内 {g_render(C2)!r}")
    for i in range(9):
        D = gfree_dot(eng_rows, i, i)
        C1, C2, Dp = gfree_reduce(_gadd(D, _gscale({(0, 0): [F1]}, -1)))
        if Dp:
            fail(f"G5(c) 门内对角归一失守：{ROWS[i]}")
        name = f"gram_diag_{ROWS[i]}"
        if name not in certs_txt:
            fail(f"G5(c) 主件缺 key 语句：{name}")
        lhs_dot, rhs, M1, M2 = certs_txt[name]
        if lhs_dot.strip() != f"{g_row_arg(i)} {g_row_arg(i)}" or rhs.strip() != "1":
            fail(f"G5(c) {name} 定理头失配")
        if M1.strip() != g_render(C1) or M2.strip() != g_render(C2):
            fail(f"G5(c) {name} 证书乘子失配（对角）")

    # (b) 分类三方＋计数配平：门内几何 ↔ 门内算术规则 ↔ l4_orbit.json
    mism = [(i, j) for (i, j), k in cls_gate.items() if g_node_rule(i, j) != k]
    if mism:
        fail(f"G5(b) 门内算术规则与几何分类失配：{mism}")
    counts = [sum(1 for k in cls_gate.values() if k == c) for c in range(6)]
    if counts != MULTS or list(orb["orbitBalance"]["tubeMults"]) != MULTS:
        fail(f"G5(b) 六类计数失配：门内 {counts} ≠ tubeMults {MULTS}")
    prof = {v: [0] * 6 for v in range(9)}
    for (i, j), c in cls_gate.items():
        prof[i][c] += 1
        prof[j][c] += 1
    if prof[0] != orb["orbitBalance"]["prismVertexProfile"] or \
            prof[6] != orb["orbitBalance"]["capVertexProfile"]:
        fail("G5(b) 逐顶点轮廓与 l4_orbit.json orbitBalance 失配")
    sigma = [sum(prof[v][c] for v in range(9)) for c in range(6)]
    if sigma != [2 * m for m in MULTS] or \
            sigma != list(orb["orbitBalance"]["perNodeSums_Sigma_y"]):
        fail("G5(b) Σ_y==2·mult 配平与门内重算/json 失配")
    # 主件计数定理字面量对账
    if "| 0 => 6 | 1 => 6 | 2 => 3 | 3 => 3 | 4 => 6 | _ => 12" not in src_main:
        fail("G5(b) 主件 edgeMult 字面量与门内计数失配")
    if "| 0 => 2 | 1 => 1 | 2 => 0 | 3 => 1 | 4 => 2 | _ => 2" not in src_main:
        fail("G5(b) 主件 prismProf 字面量与门内轮廓失配")
    if "| 0 => 0 | 1 => 2 | 2 => 2 | 3 => 0 | 4 => 0 | _ => 4" not in src_main:
        fail("G5(b) 主件 capProf 字面量与门内轮廓失配")

    # (d) 容器三方：源码 ↔ 门内重算 ↔ json 记录；五链不交；抽查复放
    z_lo, z_hi = parsed["zLo"], parsed["zHi"]
    z2_lo, z2_hi = z_lo * z_lo, z_hi * z_hi
    rhoDn = sqrt_rat(1 - z2_hi, "lo")
    rhoUp = sqrt_rat(1 - z2_lo, "hi")
    if parsed["rhoDn"] != rhoDn:
        fail("G5(d) rhoDn 失配：源码 ≠ 门内 Newton 重算")
    if parsed["rhoUp"] != rhoUp:
        fail("G5(d) rhoUp 失配：源码 ≠ 门内 Newton 重算")
    cont = [(-(1 + z2_hi) / 2, -(1 + z2_lo) / 2), (-rhoUp, -rhoDn),
            (Fr(-1, 2), Fr(-1, 2)), (1 - 2 * z2_hi, 1 - 2 * z2_lo),
            ((3 * z2_lo - 1) / 2, (3 * z2_hi - 1) / 2), (rhoDn / 2, rhoUp / 2)]
    for k in range(6):
        for s, nm in ((0, f"nu{k+1}Lo"), (1, f"nu{k+1}Hi")):
            if parsed[nm] != cont[k][s]:
                fail(f"G5(d) 容器三方失配：源码 {nm} ≠ 门内端点公式重算 {cont[k][s]}")
    for k in range(5):
        if not cont[k][1] < cont[k + 1][0]:
            fail(f"G5(d) 容器五链不交失守：ν{k+1}Hi ≮ ν{k+2}Lo（容器越分离区间）")
    json_iv = [[Fr(s) for s in pair] for pair in orb["nodes"]["intervals"]]
    TOL = Fr(1, 10 ** 15)
    exact_rng = {0: (-(1 + z2_hi) / 2, -(1 + z2_lo) / 2), 2: (Fr(-1, 2), Fr(-1, 2)),
                 3: (1 - 2 * z2_hi, 1 - 2 * z2_lo),
                 4: ((3 * z2_lo - 1) / 2, (3 * z2_hi - 1) / 2)}
    for k, (tlo, thi) in exact_rng.items():
        if not (json_iv[k][0] - TOL <= tlo and thi <= json_iv[k][1] + TOL):
            fail(f"G5(d) 真值范围 ⊄ 外扩 json 节点区间：ν{k+1}")
    if not ((1 - z2_lo) <= (-json_iv[1][0] + TOL) ** 2
            and (1 - z2_hi) >= (-json_iv[1][1] - TOL) ** 2):
        fail("G5(d) 真值范围 ⊄ 外扩 json 节点区间：ν₂")
    if not ((1 - z2_hi) >= (2 * json_iv[5][0] - TOL) ** 2
            and (1 - z2_lo) <= (2 * json_iv[5][1] + TOL) ** 2):
        fail("G5(d) 真值范围 ⊄ 外扩 json 节点区间：ν₆")
    # 抽查 seed 复放
    rng = random.Random(SEED_GATE)
    lo_i, hi_i = math.floor(z_lo * ZGRID), math.ceil(z_hi * ZGRID)
    for k in range(3):
        i = rng.randint(lo_i, hi_i)
        z = Fr(i, ZGRID)
        if not (z_lo <= z <= z_hi):
            fail(f"G5(d) 抽查 {k} 越盒：z={z}")
        if parsed[f"spotZ{k}"] != z:
            fail(f"G5(d) 抽查 {k} 点失配：源码 spotZ{k} ≠ seed 复放 {z}")
        dn = sqrt_rat(1 - z * z, "lo")
        up = sqrt_rat(1 - z * z, "hi")
        if parsed[f"spotRhoDn{k}"] != dn or parsed[f"spotRhoUp{k}"] != up:
            fail(f"G5(d) 抽查 {k} ρ 包失配：源码 ≠ 门内 Newton 复放")
        z2 = z * z
        vals = {0: -(1 + z2) / 2, 2: Fr(-1, 2), 3: 1 - 2 * z2, 4: (3 * z2 - 1) / 2}
        for c in range(6):
            lo, hi = cont[c]
            if c == 1:
                ok = lo <= -up and -dn <= hi
            elif c == 5:
                ok = lo <= dn / 2 and up / 2 <= hi
            else:
                ok = lo <= vals[c] <= hi
            if not ok:
                fail(f"G5(d) 抽查 {k} ν{c+1} 容器包含性失守（门内复算）")
        if f"theorem spot{k}_containers" not in src_data:
            fail(f"G5(d) 抽查定理缺场：spot{k}_containers")
    # 发射器 json 对账（第四面：r15_b1_data.json 的证书/容器/抽查记录）
    dj = json.loads((RESULTS / "r15_b1_data.json").read_text())
    for name, rec in dj["certificates"]["per_pair"].items():
        if name not in certs_txt:
            fail(f"G5 json 证书记录缺场：{name}")
        _, _, M1, M2 = certs_txt[name]
        if M1.strip() != rec["C1"] or M2.strip() != rec["C2"]:
            fail(f"G5 json 证书记录与主件文本失配：{name}")
    return dict(counts=counts, sigma=sigma, certs=len(certs_txt))


def gate5_offline(src_data: str, src_main: str) -> dict:
    out = g5_core(src_data, src_main)
    okmsg("G5 离线精确复核：z 盒三方（local_min 逐位＋l4_orbit zBox 严格外扩）＋"
          "行/ν 定义表驱动渲染对账＋45 证书乘子门内归约再生成逐字节＋36 条目分类"
          "三方（几何↔算术↔json）＋计数/轮廓/Σ_y＋容器三方（Newton 重算＋json）＋"
          "五链不交＋3 抽查点 seed 复放全过")
    return out


# ------------------------------------------------------------------ NC
def nc1_sorry_injection(src_data: str) -> None:
    target = "theorem zLo_pos : (0:ℚ) < zLo := by norm_num [zLo]"
    tampered = src_data.replace(target, "theorem zLo_pos : (0:ℚ) < zLo := by sorry", 1)
    if tampered == src_data or "sorry" not in tampered:
        fail(f"NC1 预置失败：未能在 /tmp 副本注入 sorry（源码缺目标行 {target!r}）")
    d = TMP / "nc1"
    (d / "ThomsonN9").mkdir(parents=True, exist_ok=True)
    (d / "ThomsonN9" / "TableB1Data.lean").write_text(tampered)
    lp = run(["lake", "env", "printenv", "LEAN_PATH"], LEAN_DIR).stdout.strip()
    env = gate_env()
    env["LEAN_PATH"] = f"{d}:{lp}"
    b = subprocess.run(["lean", "--root", str(d), "-o",
                        str(d / "ThomsonN9" / "TableB1Data.olean"),
                        str(d / "ThomsonN9" / "TableB1Data.lean")],
                       cwd=str(LEAN_DIR), env=env, capture_output=True, text=True,
                       timeout=605)
    if b.returncode != 0 or "declaration uses `sorry`" not in (b.stdout + b.stderr):
        fail(f"NC1 注入 sorry 后编译未产生 sorry 警告（exit {b.returncode}）：\n"
             f"{(b.stdout + b.stderr)[-500:]}")
    axfile = d / "axcheck.lean"
    axfile.write_text("import ThomsonN9.TableB1Data\n"
                      "#print axioms ThomsonN9.TableB1Data.zLo_pos\n")
    a = subprocess.run(["lean", str(axfile)], cwd=str(LEAN_DIR), env=env,
                       capture_output=True, text=True, timeout=605)
    ax = parse_axiom_lines(a.stdout)
    th = "ThomsonN9.TableB1Data.zLo_pos"
    caught = th in ax and ("sorryAx" in ax[th] or (ax[th] - ALLOWED_AXIOMS))
    if not caught:
        fail(f"NC1 失守：注入 sorry 后公理检查未现 sorryAx（{ax}）")
    okmsg(f"NC1 注入 sorry 必被 G3 拦：篡件 zLo_pos 公理集 = "
          f"{sorted(ax.get(th, set()))}（含 sorryAx → G3 FAIL）")


def nc2_row_tamper(src_data: str, src_main: str) -> None:
    target = ("noncomputable def rowT1 (z : ℝ) : ℝ × ℝ × ℝ := "
              "(-(rhoR z)/2, s3R * rhoR z / 2, z)")
    tampered = src_data.replace(
        target,
        "noncomputable def rowT1 (z : ℝ) : ℝ × ℝ × ℝ := "
        "(-(rhoR z)/2, s3R * rhoR z / 2, 1)", 1)      # z 坐标 → 1 硬编码
    if tampered == src_data:
        raise GateFail("NC2 预置失败：未找到 rowT1 定义行")
    try:
        g5_core(tampered, src_main)
        raise GateFail("NC2 失守：篡行坐标（rowT1 的 z 坐标→1）后 G5 未报错")
    except GateFail as e:
        if "预置" in str(e):
            raise
        print(f"[gate][NC2 检出] {e}")
    g5_core(src_data, src_main)        # sanity：原文件 PASS
    okmsg("NC2 篡行坐标（rowT1 的 z 坐标→1 硬编码）必被 G5 拦：行定义文本对账"
          "（门内表驱动渲染）首错即检出；原文件 sanity PASS")


def nc3_container_tamper(src_data: str, src_main: str) -> None:
    m = re.search(r"^def nu4Hi : ℚ := (\d+)/(\d+)$", src_data, re.M)
    if not m:
        raise GateFail("NC3 预置失败：未找到 nu4Hi 字面量")
    bad = Fr(int(m.group(1)), int(m.group(2))) + Fr(1, 8)   # 侵入 ν₅ 容器
    tampered = src_data.replace(f"def nu4Hi : ℚ := {m.group(1)}/{m.group(2)}",
                                f"def nu4Hi : ℚ := {fs(bad)}", 1)
    if tampered == src_data:
        raise GateFail("NC3 预置失败：篡改未生效")
    try:
        g5_core(tampered, src_main)
        raise GateFail("NC3 失守：篡容器端点后 G5 未报错")
    except GateFail as e:
        if "预置" in str(e) or "失守：篡" in str(e):
            raise
        if "容器" not in str(e):
            raise GateFail(f"NC3 首错命题断言失败：首错非容器失配（{e}）")
        print(f"[gate][NC3 检出] {e}")
    g5_core(src_data, src_main)        # sanity：原文件 PASS
    okmsg("NC3 篡容器端点（nu4Hi＋1/8 越过 ν₅ 隔离下端）必被 G5 拦：容器三方比对"
          "（源码≠门内端点公式重算）＋五链不交复核检出（防假拦截断言过）；"
          "原文件 sanity PASS")


# ------------------------------------------------------------------ main
def main() -> None:
    t0 = time.time()
    print(f"[gate] r15_b1_gate.py seed={SEED_GATE}（确定性；抽查点为 seed 复放）")
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
    for p in (DATA_LEAN, MAIN_LEAN, RESULTS / "r15_b1_data.json"):
        if not p.is_file():
            fail(f"产出件不在场：{p}")
    src_data = DATA_LEAN.read_text()
    src_main = MAIN_LEAN.read_text()

    gate0_ledger()
    gate1_ownership()
    walls = gate2_elaborate()
    g3 = gate3_axioms(src_data, src_main)
    gate4_statement(src_data, src_main)
    gate5_offline(src_data, src_main)
    nc1_sorry_injection(src_data)
    nc2_row_tamper(src_data, src_main)
    nc3_container_tamper(src_data, src_main)
    print(f"[gate] G2 elaboration 墙钟：Data {walls['data_s']}s＋Main {walls['main_s']}s"
          f"（均 ≤ {ELAB_LIMIT_S}s）；G3 定理 {g3['theorems']} 件")


if __name__ == "__main__":
    main()
