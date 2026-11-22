#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r14_b5_gate.py — R14A 表 B 首件 B5（Procrustes 刚性常数层）验收门
（G0–G5＋负对照 NC1/NC2/NC3）.

任务书口径（r14a-b5-procrustes-lean，D56 裁决 1/2/3）：B5 常数件 Lean 化——
TTP 族二次型对角化＋λ 夹逼（二次型口径免特征值 API）＋S 区间容器＋装配
恒等式四件（636-bit norm_num）＋sqrt 有理界四件＋C/δ_max 有效性定理。
d_P(X,Y)≤C·δ 解析本体不在件内（边界如实，docstring 双侧声明）。产出件
formal/lean/ThomsonN9/TableB5Data.lean（r14_b5_data.py 确定性发射，仅
import Mathlib）＋TableB5.lean（手写主件，import Mathlib＋
ThomsonN9.TableB5Data，零数值字面量）。本门全确定性（无随机路径；抽查点
seed 20261016 复现为确定性重放），PATH 自动前置 ~/.elan/bin（缺失即 FAIL
附信息）；CWD 无关（全部路径自 __file__ 推导）。heavySolves=0（本门零求解：
仅 elaboration/公理/regex/Fraction 复核）。

检查面（对应任务书 G0–G5＋NC1/NC2/NC3）：
  G0 账本在场与受控字段（seed == 20261016、heavy_solves == 0、自有八件在清单）。
  G1 文件所有权守卫：git status --porcelain 与 git diff HEAD --name-only 的全部
     改动路径 ⊆ 本任务自有八件（＋环境变量 R14A_G1_ALLOW_FOREIGN 自跑逐件放行
     〔默认关〕＋PARALLEL_FAMILY r14b 家族 pattern〔D53-4 对齐〕）；两只读输入件
     results/l4.json 与 results/local_min.json 显式 git diff 守卫（单独响亮报错）。
  G2 逐文件 elaboration：子进程 `lake env lean -o <olean> ThomsonN9/TableB5Data.lean`
     然后 `… ThomsonN9/TableB5.lean`（依赖序；均 CWD=formal/lean），各 exit 0、
     输出无 error／无 sorry、墙钟 ≤ 600 s/文件（D52 裁决 4：每个 lake 子命令
     ≤10 min）；olen 落 .lake/build/lib/lean/ThomsonN9/（gitignored），供 G3/主件
     import 复用。
  G3 公理：检查件 import 两模块＋对**两文件全部 theorem**（regex 枚举）#print
     axioms——公理集 ⊆ {propext, Classical.choice, Quot.sound}，零
     sorryAx/ofReduceBool/ofReduceNat/trustCompiler。
  G4 语句锚（行号 regex）：二次型恒等式（含 ring 证书形状）／λ 夹逼两向／装配
     四件／C 有效性／δ_max 有效性／sqrt 界四件／S 容器（主件定理＋Data 端点
     事实）＋抽查六定理＋import 面；非交叠守卫（Solution.lean/TableA*.lean/
     M1Data.lean/ThomsonN9.lean/lakefile.toml/scripts/check.sh 源码零 TableB5
     引用）。
  G5 离线精确复核（stdlib Fraction 零仓 import，独立于 r14_b5_data.py 的门内
     第二实现——Newton sqrt 包＋9 行构型 4-monomial 符号行展开重写）：
     (a) 常数三方逐位：TableB5Data.lean 源码 regex 解析的 23 个 ℚ 字面量 ↔
         l4.json 记录值 ↔ 门内独立重算（sqrt 包/装配四件）；
     (b) z 盒三方：源码 zLo/zHi ↔ local_min.json zStarIntervalMpmath ↔
         l4.json ttp_interval.z_box 逐位同源；
     (c) λ 支配＋sqrt 前提＋reg2<1/2＋S 容器端点（S22 端点==6z² 逐位、
         S00/S11 严格容器、非对角对称含 0）于解析字面量上复核；
     (d) 抽查点复放：seed 20261016 重放 3 有理点（2⁻⁴⁰ 网格 z＋/64 网格 v），
         期望值由门内行展开引擎独立算出，与 diagQ_spotN 定理字面量逐位对账
         ＋λ 夹逼数值复核。
  NC1 注入 sorry 必被 G3 拦：/tmp 副本把 zLo_pos 证明改 sorry → 独立编译
     （lean --root＋LEAN_PATH 前置副本目录）必现 sorry 警告＋公理检查必现
     sorryAx → G3 判定逻辑必 FAIL（未篡原件 sanity：G3 全 50 件过）。
  NC2 篡 C 装配分量必被 G5 拦：/tmp 副本把 CInner 分子＋1 → G5(a) 三方逐位
     比对必 FAIL（原文件 sanity PASS）。
  NC3 篡 z 盒必被 G5 拦：/tmp 副本把 zHi 越出 local_min 隔离区间（+1e-3）→
     G5(b) z 盒三方比对必 FAIL 且首错命题为 z 盒失配（首错命题断言防假拦截，
     R13C 先例）。

用法（CWD 无关）：
  python3 numerics/bounds/r14_b5_gate.py     # 全门（exit 0 = 过）
  python3 thomson-n9/numerics/bounds/r14_b5_gate.py
      # ↑ CWD＝仓库根时的验收命令命中同名 runpy 包装器（沿 R10A 0087eab／
      #   R12B 5237fe5／R13C r13_a1 先例，包装器重定向到真实门）
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

SEED_GATE = 20261016                   # R14 各门统一 seed（D56）
ELAB_LIMIT_S = 600                     # G2 每文件 ≤10 min（D52 裁决 4）
ZGRID = 1 << 40                        # 抽查 z 网格（与发射器同一文档化方案）

DATA_REL = "formal/lean/ThomsonN9/TableB5Data.lean"
MAIN_REL = "formal/lean/ThomsonN9/TableB5.lean"
GATE_REL = "numerics/bounds/r14_b5_gate.py"
WRAPPER_REL = "thomson-n9/numerics/bounds/r14_b5_gate.py"   # CWD 兼容包装器
DATAPY_REL = "numerics/bounds/r14_b5_data.py"
DATAJSON_REL = "numerics/bounds/results/r14_b5_data.json"
LEDGER_REL = "numerics/bounds/results/r14_b5_ledger.json"
NOTES_REL = "notes/tableb-lean.md"
OWNED = {DATA_REL, MAIN_REL, GATE_REL, WRAPPER_REL, DATAPY_REL,
         DATAJSON_REL, LEDGER_REL, NOTES_REL}

L4_REL = "numerics/bounds/results/l4.json"            # 只读输入（唯一记录源）
LM_REL = "numerics/bounds/results/local_min.json"     # 只读输入（z 盒隔离源）
FROZEN_READONLY = (L4_REL, LM_REL)

# 并行家族放行集（D53-4 对齐；R14 任务切分＝r14a 本件＋r14b 收口）：
# r14b 收口件的门/数据/账本/包装器/工作目录与 GAP-REPORT/PROGRESS 轮次文档。
# 家族外任何路径字面拦截；只读输入件守卫独立于放行集不受影响。
PARALLEL_FAMILY = [
    r"^numerics/bounds/r14b[a-z0-9_]*(\.py|/)",
    r"^numerics/bounds/results/r14b[a-z0-9_]*(\.json|/)",
    r"^thomson-n9/numerics/bounds/r14b[a-z0-9_]*(\.py|/)",
    r"^(GAP-REPORT|PROGRESS)\.md$",
]

# 非交叠守卫面（既有表 A/M1/Solution 面＋根模块/lake 面，零交叠机器化）
NONOVERLAP_FILES = ("ThomsonN9/Solution.lean", "ThomsonN9/TableA.lean",
                    "ThomsonN9/TableA1.lean", "ThomsonN9/TableA3.lean",
                    "ThomsonN9/TableA4.lean", "ThomsonN9/TableA6.lean",
                    "ThomsonN9/M1Data.lean", "ThomsonN9.lean",
                    "lakefile.toml", "scripts/check.sh")

TMP = Path("/tmp/r14_b5_gate")
OLEAN_REL = ".lake/build/lib/lean/ThomsonN9"
DATA_LEAN = LEAN_DIR / "ThomsonN9" / "TableB5Data.lean"
MAIN_LEAN = LEAN_DIR / "ThomsonN9" / "TableB5.lean"
LEDGER = RESULTS / "r14_b5_ledger.json"
L4_JSON = RESULTS / "l4.json"
LM_JSON = RESULTS / "local_min.json"

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN_AXIOMS = ("sorryAx", "ofReduceBool", "ofReduceNat", "trustCompiler")

F0, F1, FHALF = Fr(0), Fr(1), Fr(1, 2)


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
    # 三层放行：① OWNED（本任务八件）；② 环境变量 R14A_G1_ALLOW_FOREIGN（自跑
    # 专用逐件放行，默认关——预提交口径：notes/decisions.md 的 D57 留痕等共享
    # append-only 件，沿 R13C D-r13d-2 先例）；③ PARALLEL_FAMILY pattern
    # （D53-4 对齐，r14b 收口件家族）。三层之外字面拦截。
    allow_foreign = {q.strip() for q in
                     os.environ.get("R14A_G1_ALLOW_FOREIGN", "").split(",") if q.strip()}
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
                print(f"[gate][G1][并行家族放行] r14b 在途件（D53-4 pattern）：{p}")
                continue
            raise GateFail(
                f"G1 树上出现非本任务自有件（{cmd[1]}）：{p!r}"
                f"（自有集={sorted(OWNED)}；并行家族放行集 D53-4 未覆盖该路径——"
                f"若确系 r14b 在途件，可设 R14A_G1_ALLOW_FOREIGN={p} 显式放行）")
    # 两只读输入件守卫（显式单列，响亮报错；独立于放行集）
    for rel in FROZEN_READONLY:
        r = run(["git", "diff", "HEAD", "--", rel], REPO)
        if r.returncode != 0 or r.stdout.strip():
            fail(f"G1 只读守卫失守：{rel} 相对 HEAD 有改动（l4.json/local_min.json 为冻结只读面）")
    okmsg("G1 文件所有权守卫：git status/diff 相对 HEAD 仅自有八件／并行家族放行件"
          f"（或全净）；l4.json 与 local_min.json 只读守卫空 diff")


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
    wall_data = compile_lean("ThomsonN9/TableB5Data.lean", "TableB5Data.olean")
    okmsg(f"G2 elaboration：TableB5Data.lean exit 0 无 error/sorry（{wall_data:.1f}s ≤ 600s）")
    wall_main = compile_lean("ThomsonN9/TableB5.lean", "TableB5.olean")
    okmsg(f"G2 elaboration：TableB5.lean exit 0 无 error/sorry（{wall_main:.1f}s ≤ 600s；"
          "两件依赖序编译，olean 落 .lake/build 供 G3/主件 import 复用）")
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
    names = ([f"ThomsonN9.TableB5Data.{t}" for t in theorem_names(src_data)]
             + [f"ThomsonN9.TableB5.{t}" for t in theorem_names(src_main)])
    if len(names) < 40:
        fail(f"G3 定理枚举异常偏少：{len(names)}（应 ≈50）")
    TMP.mkdir(parents=True, exist_ok=True)
    axfile = TMP / "axcheck.lean"
    axfile.write_text("import ThomsonN9.TableB5Data\nimport ThomsonN9.TableB5\n"
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
        fail("G4 TableB5Data.lean import 行失配（应恰为 [import Mathlib]）")
    if re.findall(r"^import\s+\S+", src_main, re.M) != \
            ["import Mathlib", "import ThomsonN9.TableB5Data"]:
        fail("G4 TableB5.lean import 行失配（应恰为 "
             "[import Mathlib, import ThomsonN9.TableB5Data]）")
    anchors = [
        # ---- Data 件：字面量 def 锚
        (r"^def zLo : ℚ :=", "zLo 字面量锚"),
        (r"^def zHi : ℚ :=", "zHi 字面量锚"),
        (r"^def l3 : ℚ :=", "l3 字面量锚"),
        (r"^def u1 : ℚ :=", "u1 字面量锚"),
        (r"^def s1Up : ℚ :=", "s1Up 字面量锚"),
        (r"^def s3Dn : ℚ :=", "s3Dn 字面量锚"),
        (r"^def sqrt72Up : ℚ :=", "sqrt72Up 字面量锚"),
        (r"^def CInner : ℚ :=", "CInner 字面量锚"),
        (r"^def CVal : ℚ :=", "CVal 字面量锚"),
        (r"^def CChord : ℚ :=", "CChord 字面量锚"),
        (r"^def deltaMax : ℚ :=", "deltaMax 字面量锚"),
        (r"^def diagQ \(z v0 v1 v2 : ℚ\) : ℚ :=", "diagQ 对角二次型锚"),
        # ---- Data 件：装配四件
        (r"theorem C_inner_val : u1 \* s1Up / \(l3\*l3\) \+ 2/s3Dn = CInner", "装配① C_inner 锚"),
        (r"theorem C_val : sqrt72Up \* CInner = CVal", "装配② C 锚"),
        (r"theorem C_chord_val : 2 \* CVal = CChord", "装配③ C_chord 锚"),
        (r"theorem delta_max_val : \(s3Dn/\(2\*s1Up\)\) \* \(l3\*l3\) / \(sqrt72Up \* u1\) = deltaMax", "装配④ δ_max 锚"),
        # ---- Data 件：λ 支配＋sqrt 前提＋S 端点
        (r"theorem six_zLo_sq_ge_l3 : l3 ≤ 6 \* zLo\^2", "λ 支配下侧锚"),
        (r"theorem fourhalf_three_zLo_le_u1 : 9/2 - 3 \* zLo\^2 ≤ u1", "λ 支配上侧锚"),
        (r"theorem zHi_sq_lt_half : zHi\^2 < 1/2", "z_hi²<1/2 锚"),
        (r"theorem s1Up_sq_ge_u1 : u1 ≤ s1Up\^2", "sqrt 前提①锚"),
        (r"theorem s3Dn_sq_le_l3 : s3Dn\^2 ≤ l3", "sqrt 前提②锚"),
        (r"theorem sqrt72Up_sq_ge_72 : \(72:ℚ\) ≤ sqrt72Up\^2", "sqrt 前提③锚"),
        (r"theorem s3Dn_le_s1Up : s3Dn ≤ s1Up", "sqrt 前提④锚"),
        (r"theorem S22_lo_eq : S22lo = 6 \* zLo\^2", "S22 下端==6z_lo²锚"),
        (r"theorem S22_hi_eq : S22hi = 6 \* zHi\^2", "S22 上端==6z_hi²锚"),
        (r"theorem S00_container : S00lo < 9/2 - 3\*zHi\^2", "S00 严格容器锚"),
        (r"theorem S11_container : S11lo < 9/2 - 3\*zHi\^2", "S11 严格容器锚"),
        (r"theorem S01_sym : S01lo = -S01hi ∧ 0 < S01hi", "S01 对称锚"),
        # ---- 主件：二次型恒等式＋证书
        (r"theorem ttp_quadform \(z : ℝ\) \(hz : z\^2 ≤ 1\) \(v0 v1 v2 : ℝ\)", "二次型恒等式定理头锚"),
        (r"ttpQ z v0 v1 v2 = \(3\*\(1-z\^2\)\+3/2\)\*\(v0\^2\+v1\^2\) \+ 6\*z\^2\*v2\^2", "二次型恒等式命题形状锚"),
        (r"\(Real\.sqrt 3 \* Real\.sqrt 3 - 3\)", "ring 证书系数①锚"),
        (r"\+ \(Real\.sqrt \(1-z\^2\) \* Real\.sqrt \(1-z\^2\) \+ z\^2 - 1\) \* \(3\*\(v0\^2\+v1\^2\)\)", "ring 证书系数②锚"),
        # ---- 主件：Gram 对角/非对角
        (r"theorem ttpQ_e0 \(z : ℝ\) \(hz : z\^2 ≤ 1\) : ttpQ z 1 0 0 = 3\*\(1-z\^2\)\+3/2", "Gram S00 锚"),
        (r"theorem ttpQ_e2 \(z : ℝ\) \(hz : z\^2 ≤ 1\) : ttpQ z 0 0 1 = 6\*z\^2", "Gram S22 锚"),
        (r"theorem ttpQ_off01 \(z : ℝ\) \(hz : z\^2 ≤ 1\) :", "非对角混合差01锚"),
        (r"theorem ttpQ_off12 \(z : ℝ\) \(hz : z\^2 ≤ 1\) :", "非对角混合差12锚"),
        # ---- 主件：λ 夹逼两向
        (r"theorem ttp_sandwich_lo \(z v0 v1 v2 : ℝ\) \(h1 : \(zLo:ℝ\) ≤ z\) \(h2 : z ≤ \(zHi:ℝ\)\) :\n    \(l3:ℝ\)\*\(v0\^2\+v1\^2\+v2\^2\) ≤ ttpQ z v0 v1 v2", "λ 夹逼下侧命题锚"),
        (r"theorem ttp_sandwich_hi \(z v0 v1 v2 : ℝ\) \(h1 : \(zLo:ℝ\) ≤ z\) \(h2 : z ≤ \(zHi:ℝ\)\) :\n    ttpQ z v0 v1 v2 ≤ \(u1:ℝ\)\*\(v0\^2\+v1\^2\+v2\^2\)", "λ 夹逼上侧命题锚"),
        # ---- 主件：S 容器
        (r"theorem S_interval_container \(z : ℝ\) \(h1 : \(zLo:ℝ\) ≤ z\) \(h2 : z ≤ \(zHi:ℝ\)\)", "S 容器定理头锚"),
        (r"\(S22lo:ℝ\) ≤ 6\*z\^2 ∧ 6\*z\^2 ≤ \(S22hi:ℝ\)", "S 容器 S22 形状锚"),
        (r"\(S01lo:ℝ\) ≤ 0 ∧ 0 ≤ \(S01hi:ℝ\)", "S 容器非对角形状锚"),
        # ---- 主件：sqrt 界四件
        (r"theorem sqrt_u1_le_s1Up : Real\.sqrt \(u1:ℝ\) ≤ \(s1Up:ℝ\)", "sqrt 界①锚"),
        (r"theorem s3Dn_le_sqrt_l3 : \(s3Dn:ℝ\) ≤ Real\.sqrt \(l3:ℝ\)", "sqrt 界②锚"),
        (r"theorem sqrt72_le_sqrt72Up : Real\.sqrt 72 ≤ \(sqrt72Up:ℝ\)", "sqrt 界③锚"),
        (r"theorem sqrt_l3_le_s1Up : Real\.sqrt \(l3:ℝ\) ≤ \(s1Up:ℝ\)", "sqrt 界④锚"),
        # ---- 主件：有效性定理
        (r"theorem C_valid \(lam3 lam1 : ℝ\) \(h3 : \(l3:ℝ\) ≤ lam3\) \(h1 : lam1 ≤ \(u1:ℝ\)\)", "C 有效性定理头锚"),
        (r"Real\.sqrt 72 \* \(\(Real\.sqrt lam1\)\^3 / lam3\^2 \+ 2 / Real\.sqrt lam3\) ≤ \(CVal:ℝ\)", "C 有效性命题形状锚"),
        (r"theorem delta_max_valid \(lam3 lam1 eta delta : ℝ\) \(heta0 : \(0:ℝ\) ≤ eta\)", "δ_max 有效性定理头锚"),
        (r"lam1 \* eta / lam3\^2\n      ≤ min \(1/2\) \(Real\.sqrt lam3 / \(2 \* Real\.sqrt lam1\)\)", "δ_max 有效性命题形状锚"),
    ]
    for pat, name in anchors:
        if not re.search(pat, src_data + "\n" + src_main, re.M):
            fail(f"G4 语句锚缺失：{name}（pattern {pat!r}）")
    spots = re.findall(r"^theorem diagQ_spot(\d)", src_data, re.M)
    sw = re.findall(r"^theorem diagQ_sandwich_spot(\d)", src_data, re.M)
    if sorted(spots) != ["0", "1", "2"] or sorted(sw) != ["0", "1", "2"]:
        fail(f"G4 抽查定理失配：diagQ_spot{sorted(spots)}、"
             f"diagQ_sandwich_spot{sorted(sw)}（应各 0/1/2）")
    # 非交叠守卫（TableA* 含分块子目录 TableA6/）
    nonoverlap = list(NONOVERLAP_FILES)
    for p in sorted((LEAN_DIR / "ThomsonN9").glob("TableA*.lean")):
        nonoverlap.append(str(p.relative_to(LEAN_DIR)))
    for p in sorted((LEAN_DIR / "ThomsonN9" / "TableA6").glob("*.lean")) \
            if (LEAN_DIR / "ThomsonN9" / "TableA6").is_dir() else []:
        nonoverlap.append(str(p.relative_to(LEAN_DIR)))
    for rel in nonoverlap:
        p = LEAN_DIR / rel
        if p.is_file() and "TableB5" in p.read_text():
            fail(f"G4 非交叠守卫：{rel} 含 'TableB5'（本件必须不被表 A/M1/Solution 面引用）")
    okmsg("G4 语句锚：import 面恰 [Mathlib]/[Mathlib＋TableB5Data]；49 锚全在＋"
          "6 抽查定理；Solution/TableA*/M1Data/根模块/lakefile/check.sh 零 TableB5 引用")


# ------------------------------------------------------------------ G5 门内独立第二实现
def sqrt_rat(q: Fr, side: str) -> Fr:
    """√q 有理包（门内独立重实现；上界 isqrt(⌊q·2^(2p)⌋+1)+1、下界 isqrt）。"""
    p = 200
    num, den = q.numerator, q.denominator
    if side == "lo":
        return Fr(math.isqrt((num << (2 * p)) // den), 1 << p)
    return Fr(math.isqrt((num << (2 * p)) // den + 1) + 1, 1 << p)


def q_rows(z: Fr, v0: Fr, v1: Fr, v2: Fr) -> Fr:
    """Σᵢ(xᵢ·v)² 的门内独立行展开（4-monomial 系数四元组 (c, cρ, cs, cρs)，
    归约 ρ²=1−z²、s²=3；逐行求 dot 后平方求和——与发射器的 dict 引擎独立编码）。"""
    r2 = 1 - z * z
    MON = 4

    def padd(a, b):
        return tuple(x + y for x, y in zip(a, b))

    def pmul(a, b):
        out = [F0] * MON
        for i, ca in enumerate(a):
            if ca == 0:
                continue
            for j, cb in enumerate(b):
                if cb == 0:
                    continue
                er = (i % 2) + (j % 2)
                es = (i // 2) + (j // 2)
                c = ca * cb
                if es >= 2:
                    es -= 2
                    c *= 3
                if er >= 2:
                    er -= 2
                    c *= r2
                out[er + 2 * es] += c
        return tuple(out)

    def scal(a, c):
        return tuple(x * c for x in a)
    Z = (F0, F0, F0, F0)
    rho, s = (F0, F1, F0, F0), (F0, F0, F1, F0)
    rows = []
    for zs in (z, -z):
        zc = (zs, F0, F0, F0)
        rows.append([rho, Z, zc])
        rows.append([scal(rho, Fr(-1, 2)), scal(pmul(rho, s), FHALF), zc])
        rows.append([scal(rho, Fr(-1, 2)), scal(pmul(rho, s), -FHALF), zc])
    rows.append([(FHALF, F0, F0, F0), scal(s, FHALF), Z])
    rows.append([(-F1, F0, F0, F0), Z, Z])
    rows.append([(FHALF, F0, F0, F0), scal(s, -FHALF), Z])
    tot = Z
    for r in rows:
        dot = Z
        for c, vi in zip(r, (v0, v1, v2)):
            dot = padd(dot, pmul(c, (vi, F0, F0, F0)))
        tot = padd(tot, pmul(dot, dot))
    if tot[1:] != (F0, F0, F0):
        fail(f"G5 行展开 ρ/s 项非零（{tot[1:]}）")
    return tot[0]


def parse_data_defs(src: str) -> dict:
    out = {}
    for m in re.finditer(r"^def (\w+) : ℚ := (-?\d+/\d+)$", src, re.M):
        out[m.group(1)] = Fr(m.group(2))
    return out


def g5_constants_three_way(parsed: dict, l4: dict) -> dict:
    """G5(a)+(c)：源码字面量 ↔ l4.json ↔ 门内重算 三方逐位比对（篡改源可复用）。"""
    ti, co = l4["ttp_interval"], l4["constants"]
    # (a1) z 盒三方（源码 ↔ local_min ↔ l4.json）
    lm = json.loads(LM_JSON.read_text())
    zl_s, zh_s = lm["zStarIntervalMpmath"].strip("[]").split(", ")
    lm_lo, lm_hi = Fr(zl_s.strip()), Fr(zh_s.strip())
    l4_box = [Fr(x) for x in ti["z_box"]]
    if parsed["zLo"] != lm_lo or parsed["zHi"] != lm_hi:
        fail("G5(b) z 盒三方失配：源码 zLo/zHi ≠ local_min zStarIntervalMpmath 端点")
    if l4_box != [lm_lo, lm_hi]:
        fail("G5(b) z 盒三方失配：l4.json z_box ≠ local_min 隔离区间")
    # (a2) λ 界与 sqrt 包
    l3, u1 = parsed["l3"], parsed["u1"]
    if str(l3) != ti["lambda3_lower_exact"] or str(u1) != ti["lambda1_upper_exact"]:
        fail("G5(a) λ 界失配：源码 l3/u1 ≠ l4.json lambda3_lower/lambda1_upper")
    s1_up, s3_dn, sqrt72_up = parsed["s1Up"], parsed["s3Dn"], parsed["sqrt72Up"]
    if s1_up != sqrt_rat(u1, "hi") or str(s1_up) != ti["sigma1_upper"]:
        fail("G5(a) s1Up 失配：源码 ≠ 门内 Newton 重算 ≠ l4.json sigma1_upper")
    if s3_dn != sqrt_rat(l3, "lo") or str(s3_dn) != ti["sigma3_lower"]:
        fail("G5(a) s3Dn 失配：源码 ≠ 门内 Newton 重算 ≠ l4.json sigma3_lower")
    if sqrt72_up != sqrt_rat(Fr(72), "hi"):
        fail("G5(a) sqrt72Up 失配：源码 ≠ 门内 Newton 重算")
    # (a3) 装配四件三方
    C_inner = u1 * s1_up / (l3 * l3) + Fr(2) / s3_dn
    C_val = sqrt72_up * C_inner
    C_chord = 2 * C_val
    reg2 = s3_dn / (2 * s1_up)
    delta_max = min(FHALF, reg2) * l3 * l3 / (sqrt72_up * u1)
    for nm, mine, src_v, ref in (
            ("CInner", C_inner, parsed["CInner"], co["C_inner_Frobenius_exact"]),
            ("CVal", C_val, parsed["CVal"], co["C_exact"]),
            ("CChord", C_chord, parsed["CChord"], co["C_chord_distance_exact"]),
            ("deltaMax", delta_max, parsed["deltaMax"], co["delta_max_exact"])):
        if not (mine == src_v and str(src_v) == ref):
            fail(f"G5(a) 装配 {nm} 三方失配：重算={mine} 源码={src_v} l4.json={ref}")
    # (c) λ 支配＋sqrt 前提＋regime
    z_lo, z_hi = parsed["zLo"], parsed["zHi"]
    if not l3 <= 6 * z_lo * z_lo:
        fail("G5(c) λ 支配失守：l3 ≤ 6·zLo²")
    if not Fr(9, 2) - 3 * z_lo * z_lo <= u1:
        fail("G5(c) λ 支配失守：9/2 − 3·zLo² ≤ u1")
    if not z_hi * z_hi < FHALF:
        fail("G5(c) z_hi² < 1/2 失守")
    if not u1 <= s1_up * s1_up:
        fail("G5(c) sqrt 前提失守：u1 ≤ s1Up²")
    if not s3_dn * s3_dn <= l3:
        fail("G5(c) sqrt 前提失守：s3Dn² ≤ l3")
    if not Fr(72) <= sqrt72_up * sqrt72_up:
        fail("G5(c) sqrt 前提失守：72 ≤ sqrt72Up²")
    if not s3_dn <= s1_up:
        fail("G5(c) sqrt 前提失守：s3Dn ≤ s1Up")
    if not reg2 < FHALF:
        fail("G5(c) min 支路失守：reg2 = s3Dn/(2·s1Up) < 1/2")
    # (c2) S 区间容器端点（源码 ↔ l4.json ↔ 对角真值）
    S_iv = [[tuple(Fr(x) for x in c.strip("[]").split(",")) for c in row]
            for row in ti["S_interval"]]
    for nm, (i, j) in (("S00lo", (0, 0)), ("S00hi", (0, 0)),
                       ("S11lo", (1, 1)), ("S11hi", (1, 1)),
                       ("S22lo", (2, 2)), ("S22hi", (2, 2)),
                       ("S01lo", (0, 1)), ("S01hi", (0, 1)),
                       ("S02lo", (0, 2)), ("S02hi", (0, 2)),
                       ("S12lo", (1, 2)), ("S12hi", (1, 2))):
        if parsed[nm] != S_iv[i][j][0 if nm.endswith("lo") else 1]:
            fail(f"G5(c2) S 端点失配：源码 {nm} ≠ l4.json S_interval[{i}][{j}]")
    a_lo = 3 * (1 - z_hi * z_hi) + Fr(3, 2)
    a_hi = 3 * (1 - z_lo * z_lo) + Fr(3, 2)
    for nm in ("S00", "S11"):
        if not (parsed[nm + "lo"] < a_lo and a_hi < parsed[nm + "hi"]):
            fail(f"G5(c2) {nm} 非严格 ρ 外扩容器（应严格含 [a(zHi), a(zLo)]）")
    if (parsed["S22lo"], parsed["S22hi"]) != (6 * z_lo * z_lo, 6 * z_hi * z_hi):
        fail("G5(c2) S22 端点 ≠ 6·zLo²/6·zHi² 逐位")
    for nm in ("S01", "S02", "S12"):
        lo, hi = parsed[nm + "lo"], parsed[nm + "hi"]
        if lo != -hi or not (lo <= 0 <= hi):
            fail(f"G5(c2) {nm} 非对称含零区间")
    return dict(C_inner=str(C_inner), C=str(C_val), C_chord=str(C_chord),
                delta_max=str(delta_max), reg2_lt_half=True)


def g5_spots(src_data: str, parsed: dict) -> None:
    """G5(d)：抽查点 seed 复放＋期望值门内独立算出＋字面量对账＋夹逼复核。"""
    rng = random.Random(SEED_GATE)
    z_lo, z_hi = parsed["zLo"], parsed["zHi"]
    lo_i, hi_i = math.floor(z_lo * ZGRID), math.ceil(z_hi * ZGRID)
    for k in range(3):
        i = rng.randint(lo_i, hi_i)
        z = Fr(i, ZGRID)
        v = [Fr(rng.randint(-64, 64), 64) for _ in range(3)]
        if not (z_lo <= z <= z_hi):
            fail(f"G5(d) 抽查 {k} 越盒：z={z}")
        m = re.search(rf"theorem diagQ_spot{k} : diagQ \((-?\d+/\d+)\)"
                      rf" \((-?\d+/\d+)\) \((-?\d+/\d+)\) \((-?\d+/\d+)\)"
                      rf" = \((-?\d+)/(\d+)\)", src_data)
        if not m:
            fail(f"G5(d) diagQ_spot{k} 解析失败")
        zc = Fr(m.group(1))
        vc = [Fr(m.group(t)) for t in (2, 3, 4)]
        if (zc, vc) != (z, v):
            fail(f"G5(d) diagQ_spot{k} 点失配：源码 {(zc, vc)} ≠ seed 复放 {(z, v)}")
        want = Fr(int(m.group(5)), int(m.group(6)))
        q = q_rows(zc, *vc)
        if q != want:
            fail(f"G5(d) diagQ_spot{k} 期望值失配：门内行展开={q} ≠ 定理字面量={want}")
        n2 = sum(c * c for c in vc)
        if not (parsed["l3"] * n2 <= q <= parsed["u1"] * n2):
            fail(f"G5(d) diagQ_spot{k} λ 夹逼数值失守")
        if not re.search(rf"theorem diagQ_sandwich_spot{k} :", src_data):
            fail(f"G5(d) diagQ_sandwich_spot{k} 缺场")
    # 发射器 json 对账（三方第四面：r14_b5_data.json 的 spot 期望值）
    dj = json.loads((RESULTS / "r14_b5_data.json").read_text())
    for k, pt in enumerate(dj["spot_checks"]["points"]):
        if Fr(pt["q_symbolic"]) != q_rows(Fr(pt["z"]), *[Fr(x) for x in pt["v"]]):
            fail(f"G5(d) json spot {k} q_symbolic ≠ 门内行展开")


def gate5_offline(src_data: str) -> dict:
    l4 = json.loads(L4_JSON.read_text())
    parsed = parse_data_defs(src_data)
    need = {"zLo", "zHi", "l3", "u1", "s1Up", "s3Dn", "sqrt72Up", "CInner",
            "CVal", "CChord", "deltaMax", "S00lo", "S00hi", "S11lo", "S11hi",
            "S22lo", "S22hi", "S01lo", "S01hi", "S02lo", "S02hi", "S12lo", "S12hi"}
    if not need <= set(parsed):
        fail(f"G5 源码解析缺 def：缺 {sorted(need - set(parsed))}")
    out = g5_constants_three_way(parsed, l4)
    g5_spots(src_data, parsed)
    okmsg("G5 离线精确复核：23 字面量三方逐位（源码↔l4.json↔门内 Newton/装配重算）＋"
          "z 盒三方同源＋λ 支配/sqrt 前提/regime＋S 容器端点＋3 抽查点 seed 复放"
          "（期望值行展开独立算出）全过")
    return out


# ------------------------------------------------------------------ NC
def nc1_sorry_injection(src_data: str) -> None:
    target = "theorem zLo_pos : (0:ℚ) < zLo := by norm_num [zLo]"
    tampered = src_data.replace(target, "theorem zLo_pos : (0:ℚ) < zLo := by sorry", 1)
    if tampered == src_data or "sorry" not in tampered:
        fail(f"NC1 预置失败：未能在 /tmp 副本注入 sorry（源码缺目标行 {target!r}）")
    d = TMP / "nc1"
    (d / "ThomsonN9").mkdir(parents=True, exist_ok=True)
    (d / "ThomsonN9" / "TableB5Data.lean").write_text(tampered)
    lp = run(["lake", "env", "printenv", "LEAN_PATH"], LEAN_DIR).stdout.strip()
    env = gate_env()
    env["LEAN_PATH"] = f"{d}:{lp}"
    b = subprocess.run(["lean", "--root", str(d), "-o",
                        str(d / "ThomsonN9" / "TableB5Data.olean"),
                        str(d / "ThomsonN9" / "TableB5Data.lean")],
                       cwd=str(LEAN_DIR), env=env, capture_output=True, text=True,
                       timeout=605)
    if b.returncode != 0 or "declaration uses `sorry`" not in (b.stdout + b.stderr):
        fail(f"NC1 注入 sorry 后编译未产生 sorry 警告（exit {b.returncode}）：\n"
             f"{(b.stdout + b.stderr)[-500:]}")
    axfile = d / "axcheck.lean"
    axfile.write_text("import ThomsonN9.TableB5Data\n"
                      "#print axioms ThomsonN9.TableB5Data.zLo_pos\n")
    a = subprocess.run(["lean", str(axfile)], cwd=str(LEAN_DIR), env=env,
                       capture_output=True, text=True, timeout=605)
    ax = parse_axiom_lines(a.stdout)
    th = "ThomsonN9.TableB5Data.zLo_pos"
    caught = th in ax and ("sorryAx" in ax[th] or (ax[th] - ALLOWED_AXIOMS))
    if not caught:
        fail(f"NC1 失守：注入 sorry 后公理检查未现 sorryAx（{ax}）")
    okmsg(f"NC1 注入 sorry 必被 G3 拦：篡件 zLo_pos 公理集 = "
          f"{sorted(ax.get(th, set()))}（含 sorryAx → G3 FAIL）")


def nc2_assembly_tamper(src_data: str) -> None:
    m = re.search(r"^def CInner : ℚ := (\d+)/(\d+)$", src_data, re.M)
    if not m:
        raise GateFail("NC2 预置失败：未找到 CInner 字面量")
    bad_num = str(int(m.group(1)) + 1)
    tampered = src_data.replace(f"def CInner : ℚ := {m.group(1)}/{m.group(2)}",
                                f"def CInner : ℚ := {bad_num}/{m.group(2)}", 1)
    if tampered == src_data:
        raise GateFail("NC2 预置失败：篡改未生效")
    try:
        gate5_offline_core(tampered)
        raise GateFail("NC2 失守：篡 C 装配分量后 G5(a) 三方比对未报错")
    except GateFail as e:
        if "失守" in str(e) or "预置" in str(e):
            raise
        print(f"[gate][NC2 检出] {e}")
    gate5_offline_core(src_data)        # sanity：原文件 PASS
    okmsg("NC2 篡 C 装配分量（CInner 分子＋1）必被 G5 拦：三方逐位比对（重算≠"
          "源码≠l4.json）检出；原文件 sanity PASS")


def nc3_zbox_tamper(src_data: str) -> None:
    m = re.search(r"^def zHi : ℚ := (\d+)/(\d+)$", src_data, re.M)
    if not m:
        raise GateFail("NC3 预置失败：未找到 zHi 字面量")
    bad = Fr(int(m.group(1)), int(m.group(2))) + Fr(1, 1000)   # 越出隔离区间
    tampered = src_data.replace(f"def zHi : ℚ := {m.group(1)}/{m.group(2)}",
                                f"def zHi : ℚ := {fs(bad)}", 1)
    if tampered == src_data:
        raise GateFail("NC3 预置失败：篡改未生效")
    # 防假拦截（R13C 先例）：先独立断言篡值确已越出 local_min 隔离区间
    lm = json.loads(LM_JSON.read_text())
    zl_s, zh_s = lm["zStarIntervalMpmath"].strip("[]").split(", ")
    if not bad > Fr(zh_s.strip()):
        raise GateFail("NC3 预置失败：篡值未越出 local_min 隔离区间（假拦截风险）")
    try:
        gate5_offline_core(tampered)
        raise GateFail("NC3 失守：篡 z 盒后 G5(b) 三方比对未报错")
    except GateFail as e:
        if "失守" in str(e) or "预置" in str(e):
            raise
        if "z 盒" not in str(e):
            raise GateFail(f"NC3 首错命题断言失败：首错非 z 盒失配（{e}）")
        print(f"[gate][NC3 检出] {e}")
    okmsg("NC3 篡 z 盒（zHi＋1/1000 越出 local_min 隔离区间）必被 G5 拦：z 盒三方"
          "比对首错即命题失配（防假拦截断言过）；原文件 sanity PASS")


def gate5_offline_core(src_data: str) -> None:
    """G5 核心路径（NC 复用；不改盘上件）。"""
    l4 = json.loads(L4_JSON.read_text())
    parsed = parse_data_defs(src_data)
    g5_constants_three_way(parsed, l4)
    g5_spots(src_data, parsed)


def fs(f: Fr) -> str:
    return f"{f.numerator}/{f.denominator}"


# ------------------------------------------------------------------ main
def main() -> None:
    t0 = time.time()
    print(f"[gate] r14_b5_gate.py seed={SEED_GATE}（确定性；抽查点为 seed 复放）")
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
    for p in (DATA_LEAN, MAIN_LEAN, RESULTS / "r14_b5_data.json"):
        if not p.is_file():
            fail(f"产出件不在场：{p}")
    src_data = DATA_LEAN.read_text()
    src_main = MAIN_LEAN.read_text()

    gate0_ledger()
    gate1_ownership()
    walls = gate2_elaborate()
    g3 = gate3_axioms(src_data, src_main)
    gate4_statement(src_data, src_main)
    gate5_offline(src_data)
    nc1_sorry_injection(src_data)
    nc2_assembly_tamper(src_data)
    nc3_zbox_tamper(src_data)
    print(f"[gate] G2 elaboration 墙钟：Data {walls['data_s']}s＋Main {walls['main_s']}s"
          f"（均 ≤ {ELAB_LIMIT_S}s）；G3 定理 {g3['theorems']} 件")


if __name__ == "__main__":
    main()
