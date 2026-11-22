#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r15_b6_gate.py — R15A 表 B 第二件 B6（拼接端点/记录锚件算术层）验收门
（G0–G5＋负对照 NC1/NC2/NC3）.

任务书口径（r15a-tableb-b6，D61 裁决 2）：B6 记录锚件 Lean 化——12 分区无缝
覆盖（13 端点链＋Nat.find 最小命中指数法真证明，ℚ/ℝ 双版）＋记录装配
AR==min(12 分区 bound)（口径①：∀ i:Fin 12, AR ≤ bnds i ∧ bnds 10 == AR；
HP 片指标 10 字面取到）＋铁律 AR≤E*（更强版 margin>0＋ε 版）＋分片语义
（10 排除片 bound>E*＋2 片 TTP-covering bound≤E*+1e-6）。『区域 i 上
E≥b_i』的证书语义＝数值层职责（typed_ladder/hermite/hp 各证书 verifyCmd）
不在件内（docstring 双侧如实）。产出件 formal/lean/ThomsonN9/TableB6Data.lean
（r15_b6_data.py 确定性发射，仅 import Mathlib；28 ℚ def＋45 定理）＋
TableB6.lean（手写主件，import Mathlib＋ThomsonN9.TableB6Data，8 定理，
零数据值字面量——数值篡改面全落 Data 件）。本门全确定性（无随机路径；
抽查点 seed 20261017 复现为确定性重放），PATH 自动前置 ~/.elan/bin（缺失即
FAIL 附信息）；CWD 无关（全部路径自 __file__ 推导）。heavySolves=0（本门
零求解：仅 elaboration/公理/regex/Fraction 复核）。

检查面（对应任务书 G0–G5＋NC1/NC2/NC3）：
  G0 账本在场与受控字段（seed == 20261017、heavy_solves == 0、自有八件在清单）。
  G1 文件所有权守卫：git status --porcelain 与 git diff HEAD --name-only 的全部
     改动路径 ⊆ 本任务自有八件（＋环境变量 R15A_G1_ALLOW_FOREIGN 自跑逐件放行
     〔默认关〕＋PARALLEL_FAMILY r15 家族 pattern〔D53-4/D57 裁决 5 对齐〕）；
     只读输入面 results/endgame.json 与 certificates/ 显式 git diff 守卫（单独
     响亮报错）。
  G2 逐文件 elaboration：子进程 `lake env lean -o <olean> ThomsonN9/TableB6Data.lean`
     然后 `… ThomsonN9/TableB6.lean`（依赖序；均 CWD=formal/lean），各 exit 0、
     输出无 error／无 sorry、墙钟 ≤ 600 s/文件（D52 裁决 4）；olen 落
     .lake/build/lib/lean/ThomsonN9/（gitignored），供 G3/主件 import 复用。
  G3 公理：检查件 import 两模块＋对**两文件全部 theorem**（regex 枚举）#print
     axioms——公理集 ⊆ {propext, Classical.choice, Quot.sound}，零
     sorryAx/ofReduceBool/ofReduceNat/trustCompiler。
  G4 语句锚（行号 regex）：端点链 12 对／记录下侧 12 件／HP 字面等／铁律两版
     ／epsIron 正性／分片语义 12 件（10 排除＋2 covering）／覆盖 ℚ/ℝ 双版命题
     形状（Nat.find 法）／口径① min 陈述／记录取到／主件函数与 import 面
     ＋抽查三定理形状；主件零数据值字面量检查（剥注释后无 ℚ 分数/小数
     字面量——结构指标 10/11/12/13 不在此列）；非交叠守卫（Solution.lean/
     TableA*.lean/TableB5*.lean/M1Data.lean/ThomsonN9.lean/lakefile.toml/
     scripts/check.sh 源码零 TableB6 引用）。
  G5 离线精确复核（stdlib Fraction 零仓 import，独立于 r15_b6_data.py 的门内
     第二实现——region 字符串直析 Fraction 重导）：
     (a) endgame.json sha256 == 不变锚 86863a09…69f；
     (b) 28 字面量三方逐位：TableB6Data.lean 源码 regex 解析 ↔ endgame.json
         记录值（端点链/bounds/E*/AR）↔ 门内独立重导；epsIron == 1/1000000；
     (c) 端点链：单调＋与 json 分区 regions 无缝对账（13 端点逐位）＋e0=−1、
         e12=1；bounds：bᵢ == partition[i].bound 逐件＋citedCertificates
         claimed_bound 12/12 值一双射对账；
     (d) 记录/铁律/分片语义：AR==min＋逐件 AR≤bᵢ＋b10==AR＋AR≤E*＋AR<E
         （margin>0）＋AR≤E*+1e-6＋json coverPiece 分类逐片（exclusion→
         bᵢ>E*；covering→bᵢ≤E*+1e-6）＋计数 10/2＋covering 指标=={10,11}；
     (e) 抽查点复放：seed 20261017 重放 3 有理点（2⁻²⁰ 网格），最小命中指数法
         定位片，与 cover_spotN 定理字面量（片索引＋x 值）逐位对账＋区间包含
         复核；r15_b6_data.json 四面交叉（endpoints/bounds/aR/estar 与源码
         解析一致）。
  NC1 注入 sorry 必被 G3 拦：/tmp 副本把 e0_val 证明改 sorry（单行 rfl 锚
     定理整体替换）→ 独立编译（LEAN_PATH 前置副本目录）必现 sorry 警告＋
     公理检查必现 sorryAx → G3 判定逻辑必 FAIL（未篡原件 sanity：G3 全件过）。
  NC2 篡任一 bound 分子必被 G5 拦：/tmp 副本把 b0 分子＋1 → G5(c) bound↔json
     逐件对账必 FAIL（预断言篡值 ≠ json 记录值防假拦截；原文件 sanity PASS）。
  NC3 篡端点乱序必被 G5 拦：/tmp 副本交换 e5/e6 字面量（乱序）→ G5(c) 端点链
     单调必 FAIL 且首错命题为端点链失守（预断言交换后链确在 e5≤e6 处破序——
     首错命题断言防假拦截，R13C/R14A 先例；原文件 sanity PASS）。

用法（CWD 无关）：
  python3 numerics/bounds/r15_b6_gate.py     # 全门（exit 0 = 过）
  python3 thomson-n9/numerics/bounds/r15_b6_gate.py
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

SEED_GATE = 20261017                   # R15 各门统一 seed（D61）
ELAB_LIMIT_S = 600                     # G2 每文件 ≤10 min（D52 裁决 4）
XGRID = 1 << 20                        # 抽查 x 网格（与发射器同一文档化方案）
EG_SHA256 = "86863a09bf84e950e85fc5f902bc2b4046a87f06703bd782e5148fc119afd69f"

DATA_REL = "formal/lean/ThomsonN9/TableB6Data.lean"
MAIN_REL = "formal/lean/ThomsonN9/TableB6.lean"
GATE_REL = "numerics/bounds/r15_b6_gate.py"
WRAPPER_REL = "thomson-n9/numerics/bounds/r15_b6_gate.py"   # CWD 兼容包装器
DATAPY_REL = "numerics/bounds/r15_b6_data.py"
DATAJSON_REL = "numerics/bounds/results/r15_b6_data.json"
LEDGER_REL = "numerics/bounds/results/r15_b6_ledger.json"
NOTES_REL = "notes/tableb-lean.md"
OWNED = {DATA_REL, MAIN_REL, GATE_REL, WRAPPER_REL, DATAPY_REL,
         DATAJSON_REL, LEDGER_REL, NOTES_REL}

EG_REL = "numerics/bounds/results/endgame.json"        # 只读输入（唯一记录源）
CERTS_REL = "certificates"                             # 只读输入（证书目录）
FROZEN_READONLY = (EG_REL, CERTS_REL)

# 并行家族放行集（D53-4/D57 裁决 5 对齐；R15 任务切分＝r15a 本件＋r15b
# TableB1＋r15c 预研＋r15d 收口）：家族外任何路径字面拦截；只读输入件守卫
# 独立于放行集不受影响。r15b 自有件＝TableB1(Data).Lean＋r15_b1_* 门/数据/
# 账本/包装器（D61 裁决 1/3：R15A 与 R15B 文件集零交叠）；r15d 收口件＝
# endgame_gate.py（campaign-10 增补式扩展面，D61 裁决 5）＋r15d_closure_
# gate 家族（r15 前缀已覆盖）＋轮次文档三件套 GAP-REPORT/PROGRESS/
# decisions.md（共享 append-only，各轮各件留痕面——D57/D61 先例）。
PARALLEL_FAMILY = [
    r"^numerics/bounds/r15[a-z0-9_]*(\.py|/)",
    r"^numerics/bounds/results/r15[a-z0-9_]*(\.json|/)",
    r"^thomson-n9/numerics/bounds/r15[a-z0-9_]*(\.py|/)",
    r"^formal/lean/ThomsonN9/TableB1",
    r"^numerics/bounds/endgame_gate\.py$",
    r"^notes/b5-core-study\.md$",
    r"^notes/decisions\.md$",
    r"^(GAP-REPORT|PROGRESS)\.md$",
]

# 非交叠守卫面（既有表 A/M1/Solution/B5 面＋根模块/lake 面，零交叠机器化）
NONOVERLAP_FILES = ("ThomsonN9/Solution.lean", "ThomsonN9/TableA.lean",
                    "ThomsonN9/TableA1.lean", "ThomsonN9/TableA3.lean",
                    "ThomsonN9/TableA4.lean", "ThomsonN9/TableA6.lean",
                    "ThomsonN9/TableB5.lean", "ThomsonN9/TableB5Data.lean",
                    "ThomsonN9/M1Data.lean", "ThomsonN9.lean",
                    "lakefile.toml", "scripts/check.sh")

TMP = Path("/tmp/r15_b6_gate")
OLEAN_REL = ".lake/build/lib/lean/ThomsonN9"
DATA_LEAN = LEAN_DIR / "ThomsonN9" / "TableB6Data.lean"
MAIN_LEAN = LEAN_DIR / "ThomsonN9" / "TableB6.lean"
LEDGER = RESULTS / "r15_b6_ledger.json"
EG_JSON = RESULTS / "endgame.json"

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN_AXIOMS = ("sorryAx", "ofReduceBool", "ofReduceNat", "trustCompiler")

F0, F1 = Fr(0), Fr(1)
IRON_EPS = Fr(1, 10**6)


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
    # 三层放行：① OWNED（本任务八件）；② 环境变量 R15A_G1_ALLOW_FOREIGN（自跑
    # 专用逐件放行，默认关——预提交口径：notes/decisions.md 的 D61 留痕等共享
    # append-only 件，沿 R13C D-r13d-2／R14A D57 先例）；③ PARALLEL_FAMILY
    # pattern（D53-4/D57-5 对齐，r15b/r15c/r15d 家族）。三层之外字面拦截。
    allow_foreign = {q.strip() for q in
                     os.environ.get("R15A_G1_ALLOW_FOREIGN", "").split(",") if q.strip()}
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
                print(f"[gate][G1][并行家族放行] r15 在途件（D53-4/D57-5 pattern）：{p}")
                continue
            raise GateFail(
                f"G1 树上出现非本任务自有件（{cmd[1]}）：{p!r}"
                f"（自有集={sorted(OWNED)}；并行家族放行集 D53-4/D57-5 未覆盖该路径——"
                f"若确系 r15 家族在途件，可设 R15A_G1_ALLOW_FOREIGN={p} 显式放行）")
    # 只读输入面守卫（显式单列，响亮报错；独立于放行集）
    for rel in FROZEN_READONLY:
        r = run(["git", "diff", "HEAD", "--", rel], REPO)
        if r.returncode != 0 or r.stdout.strip():
            fail(f"G1 只读守卫失守：{rel} 相对 HEAD 有改动"
                 f"（endgame.json/certificates 为冻结只读面）")
    okmsg("G1 文件所有权守卫：git status/diff 相对 HEAD 仅自有八件／并行家族放行件"
          f"（或全净）；endgame.json 与 certificates/ 只读守卫空 diff")


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
    wall_data = compile_lean("ThomsonN9/TableB6Data.lean", "TableB6Data.olean")
    okmsg(f"G2 elaboration：TableB6Data.lean exit 0 无 error/sorry（{wall_data:.1f}s ≤ 600s）")
    wall_main = compile_lean("ThomsonN9/TableB6.lean", "TableB6.olean")
    okmsg(f"G2 elaboration：TableB6.lean exit 0 无 error/sorry（{wall_main:.1f}s ≤ 600s；"
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
    names = ([f"ThomsonN9.TableB6Data.{t}" for t in theorem_names(src_data)]
             + [f"ThomsonN9.TableB6.{t}" for t in theorem_names(src_main)])
    if len(names) < 40:
        fail(f"G3 定理枚举异常偏少：{len(names)}（应 ≈53）")
    TMP.mkdir(parents=True, exist_ok=True)
    axfile = TMP / "axcheck.lean"
    axfile.write_text("import ThomsonN9.TableB6Data\nimport ThomsonN9.TableB6\n"
                      + "".join(f"#print axioms {t}\n" for t in names))
    r = run(["lake", "env", "lean", str(axfile)], LEAN_DIR)
    if r.returncode != 0:
        fail(f"G3 公理检查件编译失败（exit {r.returncode}）：\n"
             f"{r.stdout[-500:]}\n{r.stderr[-500:]}")
    ax = parse_axiom_lines(r.stdout)
    check_axioms(ax, names, "G3 公理")
    return {"theorems": len(names)}


# ------------------------------------------------------------------ G4
def strip_lean_comments(src: str) -> str:
    """剥块注释（/- … -/，含 /-! 与 /-- 文档块，嵌套计数）与行注释（--）。"""
    out_lines, depth, i, n = [], 0, 0, len(src)
    for line in src.splitlines():
        res, j = [], 0
        while j < len(line):
            if depth == 0 and line[j:j + 2] == "--":
                break
            if line[j:j + 2] == "/-":
                depth += 1
                j += 2
                continue
            if depth > 0 and line[j:j + 2] == "-/":
                depth -= 1
                j += 2
                continue
            if depth == 0:
                res.append(line[j])
            j += 1
        out_lines.append("".join(res))
    return "\n".join(out_lines)


def gate4_statement(src_data: str, src_main: str) -> None:
    if re.findall(r"^import\s+\S+", src_data, re.M) != ["import Mathlib"]:
        fail("G4 TableB6Data.lean import 行失配（应恰为 [import Mathlib]）")
    if re.findall(r"^import\s+\S+", src_main, re.M) != \
            ["import Mathlib", "import ThomsonN9.TableB6Data"]:
        fail("G4 TableB6.lean import 行失配（应恰为 "
             "[import Mathlib, import ThomsonN9.TableB6Data]）")
    anchors = [
        # ---- Data 件：字面量 def 锚（28 件全枚举）
        *[(rf"^def e{k} : ℚ :=", f"e{k} 字面量锚") for k in range(13)],
        *[(rf"^def b{i} : ℚ :=", f"b{i} 字面量锚") for i in range(12)],
        (r"^def estar : ℚ :=", "estar 字面量锚"),
        (r"^def aR : ℚ :=", "aR 字面量锚"),
        (r"^def epsIron : ℚ :=", "epsIron 字面量锚"),
        # ---- Data 件：端点锚＋链 12 对
        (r"^theorem e0_val : e0 = -1/1 := rfl", "e0 字面 −1 锚"),
        (r"^theorem e12_val : e12 = 1/1 := rfl", "e12 字面 1 锚"),
        *[(rf"^theorem e{k}_le_e{k+1} : e{k} ≤ e{k+1}", f"链第 {k} 对锚") for k in range(12)],
        # ---- Data 件：记录下侧 12 件＋HP 字面等
        *[(rf"^theorem ar_le_b{i} : aR ≤ b{i}", f"记录下侧第 {i} 件锚") for i in range(12)],
        (r"^theorem b10_eq_ar : b10 = aR", "HP 片（指标 10）字面等锚"),
        # ---- Data 件：铁律两版＋eps 正性
        (r"^theorem iron_rule : aR ≤ estar", "铁律 AR≤E* 锚"),
        (r"^theorem margin_pos : aR < estar", "铁律严格版锚"),
        (r"^theorem epsIron_pos : \(0:ℚ\) < epsIron", "epsIron 正性锚"),
        # ---- Data 件：分片语义 12 件（10 排除＋2 covering）
        *[(rf"^theorem excl{i}_gt : estar < b{i}", f"排除片 {i} 铁律锚") for i in range(10)],
        (r"^theorem cover10_le_iron : b10 ≤ estar \+ epsIron", "HP 片铁律锚"),
        (r"^theorem cover11_le_iron : b11 ≤ estar \+ epsIron", "cap 片铁律锚"),
        # ---- 主件：函数＋覆盖双版（Nat.find 法）＋链聚合
        (r"^def endpointsQ : ℕ → ℚ", "端点函数锚"),
        (r"^def bndsQ : ℕ → ℚ", "bound 函数锚"),
        (r"^theorem endpoints_mono \(i : Fin 12\) : endpointsQ i\.val ≤ endpointsQ \(i\.val \+ 1\)",
         "链单调聚合锚"),
        (r"^theorem partition_cover_q \(x : ℚ\) \(hx0 : e0 ≤ x\) \(hx1 : x ≤ e12\) :",
         "覆盖 ℚ 定理头锚"),
        (r"∃ i : Fin 12, endpointsQ i\.val ≤ x ∧ x ≤ endpointsQ \(i\.val \+ 1\)",
         "覆盖 ℚ 命题形状锚"),
        (r"^theorem partition_cover \(x : ℝ\) \(hx0 : \(e0:ℝ\) ≤ x\) \(hx1 : x ≤ \(e12:ℝ\)\) :",
         "覆盖 ℝ 定理头锚"),
        (r"∃ i : Fin 12, \(endpointsQ i\.val : ℝ\) ≤ x ∧ x ≤ \(endpointsQ \(i\.val \+ 1\) : ℝ\)",
         "覆盖 ℝ 命题形状锚"),
        (r"Nat\.find_min hpred", "Nat.find 极小性锚"),
        # ---- 主件：记录装配（口径①）＋取到＋铁律 ε 版＋分片语义
        (r"^theorem ar_le_bnds \(i : Fin 12\) : aR ≤ bndsQ i\.val", "记录下侧聚合锚"),
        (r"^theorem record_is_min : ∀ i : Fin 12, aR ≤ bndsQ i\.val ∧ bndsQ 10 = aR",
         "口径① min 陈述锚（D61-2）"),
        (r"^theorem record_min_attained : ∃ i : Fin 12, bndsQ i\.val = aR", "记录取到锚"),
        (r"^theorem iron_rule_eps : aR ≤ estar \+ epsIron", "铁律 ε 版锚"),
        (r"^theorem piece_semantics \(i : Fin 12\) :", "分片语义定理头锚"),
        (r"estar < bndsQ i\.val ∨ bndsQ i\.val ≤ estar \+ epsIron", "分片语义命题形状锚"),
    ]
    for pat, name in anchors:
        if not re.search(pat, src_data + "\n" + src_main, re.M):
            fail(f"G4 语句锚缺失：{name}（pattern {pat!r}）")
    # 抽查三定理形状（片索引＋x 字面量）
    spots = re.findall(r"^theorem cover_spot(\d) : e(\d+) ≤ \((-?\d+/\d+):ℚ\) "
                       r"∧ \((-?\d+/\d+):ℚ\) ≤ e(\d+) :=", src_data, re.M)
    if sorted(s[0] for s in spots) != ["0", "1", "2"]:
        fail(f"G4 抽查定理失配：cover_spot{sorted(s[0] for s in spots)}（应 0/1/2）")
    # 主件零数据值字面量（剥注释后无 ℚ 分数/小数字面量；结构指标不在此列）
    code_main = strip_lean_comments(src_main)
    lits = re.findall(r"\d+/\d+|\d+\.\d+", code_main)
    if lits:
        fail(f"G4 主件数据值字面量残留（剥注释后）：{lits[:8]}（数值篡改面须全落 Data 件）")
    # 非交叠守卫（TableA* 含分块子目录 TableA6/）
    nonoverlap = list(NONOVERLAP_FILES)
    for p in sorted((LEAN_DIR / "ThomsonN9").glob("TableA*.lean")):
        nonoverlap.append(str(p.relative_to(LEAN_DIR)))
    a6 = LEAN_DIR / "ThomsonN9" / "TableA6"
    if a6.is_dir():
        for p in sorted(a6.glob("*.lean")):
            nonoverlap.append(str(p.relative_to(LEAN_DIR)))
    for rel in nonoverlap:
        p = LEAN_DIR / rel
        if p.is_file() and "TableB6" in p.read_text():
            fail(f"G4 非交叠守卫：{rel} 含 'TableB6'（本件必须不被表 A/B5/M1/Solution 面引用）")
    okmsg("G4 语句锚：import 面恰 [Mathlib]/[Mathlib＋TableB6Data]；"
          f"{len(anchors)} 锚全在＋3 抽查定理形状；主件剥注释零数据值字面量；"
          "Solution/TableA*/TableB5*/M1Data/根模块/lakefile/check.sh 零 TableB6 引用")


# ------------------------------------------------------------------ G5 门内独立第二实现
def parse_data_defs(src: str) -> dict:
    out = {}
    for m in re.finditer(r"^def (\w+) : ℚ := (-?\d+/\d+)$", src, re.M):
        out[m.group(1)] = Fr(m.group(2))
    return out


def g5_core(src_data: str) -> dict:
    """G5 (a)–(e)：门内独立第二实现（region 直析 Fraction 重导；NC 复用，
    不改盘上件；篡源可传入）。首错命题＝首个失守的命题（NC3 防假拦截依据）。"""
    # (a) endgame.json 不变锚
    if sha256_of(EG_JSON) != EG_SHA256:
        fail("G5(a) endgame.json sha256 失配（不变锚 86863a09…69f）——冻结面被动")
    eg = json.loads(EG_JSON.read_text())
    regions = eg["partition"]
    if len(regions) != 12:
        fail("G5(a) 分区数失配（≠12）")
    chain_json, bounds_json, pieces = [], [], []
    for r in regions:
        lo_s, hi_s = r["region"].strip("[]").split(",")
        lo, hi = Fr(lo_s.strip()), Fr(hi_s.strip())
        if chain_json and chain_json[-1] != lo:
            fail(f"G5(a) 分区无缝失守：region 下端 {lo} ≠ 前区上端 {chain_json[-1]}")
        if not chain_json:
            chain_json.append(lo)         # e0（首区下端）
        chain_json.append(hi)             # e_{i+1}（各区上端，与前区下端共享）
        bounds_json.append(Fr(r["bound"]))
        cp = r["coverPiece"]
        pieces.append("exclusion" if cp.startswith("exclusion") else "covering")
    if len(chain_json) != 13:
        fail(f"G5(a) 端点数失配：{len(chain_json)} ≠ 13")
    # (b) 28 字面量三方：源码 ↔ json 记录值
    parsed = parse_data_defs(src_data)
    need = ({f"e{k}" for k in range(13)} | {f"b{i}" for i in range(12)}
            | {"estar", "aR", "epsIron"})
    if not need <= set(parsed):
        fail(f"G5(b) 源码解析缺 def：缺 {sorted(need - set(parsed))}")
    for k in range(13):
        if parsed[f"e{k}"] != chain_json[k]:
            fail(f"G5(c) 端点链对账失配：源码 e{k}={parsed[f'e{k}']} ≠ json 端点 "
                 f"{chain_json[k]}（13 端点与分区 regions 无缝逐位）")
    for i in range(12):
        if parsed[f"b{i}"] != bounds_json[i]:
            fail(f"G5(c) 分区 bound 对账失配：源码 b{i}={parsed[f'b{i}']} ≠ json "
                 f"partition[{i}].bound={bounds_json[i]}（逐件）")
    if parsed["estar"] != Fr(eg["E_star"]["value"]):
        fail("G5(b) estar 失配：源码 ≠ json E_star.value")
    if parsed["aR"] != Fr(eg["assembledRecord"]["value"]):
        fail("G5(b) aR 失配：源码 ≠ json assembledRecord.value")
    if parsed["epsIron"] != IRON_EPS:
        fail("G5(b) epsIron 失配：源码 ≠ 1/1000000")
    # (c) 端点链单调＋端点锚（无缝已由 (b) 13 逐位对账覆盖）
    for k in range(12):
        if not parsed[f"e{k}"] <= parsed[f"e{k+1}"]:
            fail(f"G5(c) 端点链单调失守：e{k}={parsed[f'e{k}']} > e{k+1}={parsed[f'e{k+1}']}"
                 f"（乱序）")
    if parsed["e0"] != -1 or parsed["e12"] != 1:
        fail("G5(c) 端点锚失守：e0 ≠ −1 或 e12 ≠ 1")
    # (c2) certs 值一双射
    cert_bounds = [Fr(c["claimed_bound"]) for c in eg["citedCertificates"]]
    if len(cert_bounds) != 12 or len(set(cert_bounds)) != 12 \
            or set(cert_bounds) != {parsed[f"b{i}"] for i in range(12)}:
        fail("G5(c) citedCertificates 对账失守：claimed_bound 与 12 分区 bound 非"
             "值一双射（12/12 一一对应）")
    # (d) 记录/铁律/分片语义（源码字面量上复核）
    a_r, estar = parsed["aR"], parsed["estar"]
    for i in range(12):
        if not a_r <= parsed[f"b{i}"]:
            fail(f"G5(d) 记录装配失守：AR ≤ b{i} 不成立（源码字面量）")
    if a_r != min(parsed[f"b{i}"] for i in range(12)):
        fail("G5(d) 记录装配失守：AR ≠ min(12 分区 bound)（源码字面量）")
    if parsed["b10"] != a_r:
        fail("G5(d) HP 片失守：b10 ≠ AR（字面等，源码字面量）")
    if not a_r <= estar:
        fail("G5(d) 铁律失守：AR ≤ E* 不成立（源码字面量）")
    if not a_r < estar:
        fail("G5(d) 铁律严格版失守：AR < E* 不成立（margin ≤ 0）")
    if not a_r <= estar + parsed["epsIron"]:
        fail("G5(d) 铁律 ε 版失守：AR ≤ E*+1e-6 不成立（源码字面量）")
    if [i for i in range(12) if pieces[i] == "exclusion"] != list(range(10)) \
            or [i for i in range(12) if pieces[i] == "covering"] != [10, 11]:
        fail("G5(d) 分片语义分类失守：json coverPiece 非 10 排除（0–9）＋2 covering（10/11）")
    for i in range(12):
        if pieces[i] == "exclusion" and not estar < parsed[f"b{i}"]:
            fail(f"G5(d) 排除片铁律失守：b{i} ≤ E*（json coverPiece=exclusion 须 >E*）")
        if pieces[i] == "covering" and not parsed[f"b{i}"] <= estar + parsed["epsIron"]:
            fail(f"G5(d) TTP-covering 片铁律失守：b{i} > E*+1e-6")
    # (e) 抽查点复放（seed 20261017；最小命中指数法——门内独立重实现）
    rng = random.Random(SEED_GATE)
    for k in range(3):
        ii = rng.randint(-XGRID, XGRID)
        x = Fr(ii, XGRID)
        chain = [parsed[f"e{kk}"] for kk in range(13)]
        if not chain[0] <= x <= chain[12]:
            fail(f"G5(e) 抽查 {k} 越界：x={x}")
        j = next(jj for jj in range(13) if x <= chain[jj])
        iv = j - 1 if j >= 1 else 0
        m = re.search(rf"theorem cover_spot{k} : e(\d+) ≤ \((-?\d+/\d+):ℚ\) "
                      rf"∧ \((-?\d+/\d+):ℚ\) ≤ e(\d+) :=", src_data, re.M)
        if not m:
            fail(f"G5(e) cover_spot{k} 解析失败")
        i_lo, x_lo, x_hi, i_hi = (int(m.group(1)), Fr(m.group(2)),
                                  Fr(m.group(3)), int(m.group(4)))
        if x_lo != x or x_hi != x:
            fail(f"G5(e) cover_spot{k} x 字面量失配：源码 ≠ seed 复放")
        if i_lo != iv or i_hi != iv + 1:
            fail(f"G5(e) cover_spot{k} 片索引失配：源码 {i_lo}/{i_hi} ≠ "
                 f"最小命中指数复放 {iv}/{iv+1}")
        if not chain[i_lo] <= x <= chain[i_hi]:
            fail(f"G5(e) cover_spot{k} 区间包含失守")
    # (e2) 四面交叉：r15_b6_data.json 记录值 == 源码解析
    dj = json.loads((RESULTS / "r15_b6_data.json").read_text())
    if [Fr(s) for s in dj["partition"]["endpoints"]] != [parsed[f"e{k}"] for k in range(13)]:
        fail("G5(e2) 四面交叉失守：json endpoints ≠ 源码解析")
    if [Fr(s) for s in dj["partition"]["bounds"]] != [parsed[f"b{i}"] for i in range(12)]:
        fail("G5(e2) 四面交叉失守：json bounds ≠ 源码解析")
    if Fr(dj["record"]["aR"]) != a_r or Fr(dj["record"]["estar"]) != estar:
        fail("G5(e2) 四面交叉失守：json aR/estar ≠ 源码解析")
    return dict(aR=str(a_r), estar=str(estar))


def gate5_offline(src_data: str) -> dict:
    out = g5_core(src_data)
    okmsg("G5 离线精确复核：endgame.json 不变锚＋28 字面量三方逐位（源码↔json↔门内"
          "region 直析重导）＋端点链单调无缝＋certs 12/12 值一双射＋记录 AR==min/"
          "逐件 AR≤bᵢ/b10==AR＋铁律三式＋分片语义 10/2 逐片＋3 抽查点 seed 复放"
          "（最小命中指数法）＋json 四面交叉 全过")
    return out


# ------------------------------------------------------------------ NC
def nc1_sorry_injection(src_data: str) -> None:
    # 单行 rfl 定理整证明替换（B5 NC1 同式：B6 全 norm_num1 定理为多行 show
    # 形状，行内追加 sorry 会残留 show 致『No goals』伪错——rfl 锚定理单行可
    # 整体换 by sorry，篡后文件恰只多 sorry 警告）
    tampered, n = re.subn(r"^theorem e0_val : e0 = -1/1 := rfl$",
                          "theorem e0_val : e0 = -1/1 := by sorry",
                          src_data, count=1, flags=re.M)
    if n != 1 or "sorry" not in tampered:
        raise GateFail("NC1 预置失败：未能在 /tmp 副本注入 sorry（缺 e0_val rfl 目标行）")
    d = TMP / "nc1"
    (d / "ThomsonN9").mkdir(parents=True, exist_ok=True)
    (d / "ThomsonN9" / "TableB6Data.lean").write_text(tampered)
    lp = run(["lake", "env", "printenv", "LEAN_PATH"], LEAN_DIR).stdout.strip()
    env = gate_env()
    env["LEAN_PATH"] = f"{d}:{lp}"
    b = subprocess.run(["lean", "--root", str(d), "-o",
                        str(d / "ThomsonN9" / "TableB6Data.olean"),
                        str(d / "ThomsonN9" / "TableB6Data.lean")],
                       cwd=str(LEAN_DIR), env=env, capture_output=True, text=True,
                       timeout=605)
    if b.returncode != 0 or "declaration uses `sorry`" not in (b.stdout + b.stderr):
        fail(f"NC1 注入 sorry 后编译未产生 sorry 警告（exit {b.returncode}）：\n"
             f"{(b.stdout + b.stderr)[-500:]}")
    axfile = d / "axcheck.lean"
    axfile.write_text("import ThomsonN9.TableB6Data\n"
                      "#print axioms ThomsonN9.TableB6Data.e0_val\n")
    a = subprocess.run(["lean", str(axfile)], cwd=str(LEAN_DIR), env=env,
                       capture_output=True, text=True, timeout=605)
    ax = parse_axiom_lines(a.stdout)
    th = "ThomsonN9.TableB6Data.e0_val"
    caught = th in ax and ("sorryAx" in ax[th] or (ax[th] - ALLOWED_AXIOMS))
    if not caught:
        fail(f"NC1 失守：注入 sorry 后公理检查未现 sorryAx（{ax}）")
    okmsg(f"NC1 注入 sorry 必被 G3 拦：篡件 e0_val 公理集 = "
          f"{sorted(ax.get(th, set()))}（含 sorryAx → G3 FAIL）")


def nc2_bound_tamper(src_data: str) -> None:
    m = re.search(r"^def b0 : ℚ := (\d+)/(\d+)$", src_data, re.M)
    if not m:
        raise GateFail("NC2 预置失败：未找到 b0 字面量")
    bad_num = str(int(m.group(1)) + 1)
    tampered = src_data.replace(f"def b0 : ℚ := {m.group(1)}/{m.group(2)}",
                                f"def b0 : ℚ := {bad_num}/{m.group(2)}", 1)
    if tampered == src_data:
        raise GateFail("NC2 预置失败：篡改未生效")
    # 防假拦截预断言：篡值确 ≠ json 记录 bound（且仍为合法分数形状）
    eg = json.loads(EG_JSON.read_text())
    b0_json = Fr(eg["partition"][0]["bound"])
    if Fr(int(bad_num), int(m.group(2))) == b0_json:
        raise GateFail("NC2 预置失败：篡值==json 记录值（假拦截风险）")
    caught = None
    try:
        g5_core(tampered)
    except GateFail as e:
        caught = e
    if caught is None:
        raise GateFail("NC2 失守：篡 bound 分子后 G5 未报错")
    if "分区 bound 对账" not in str(caught):
        raise GateFail(f"NC2 首错命题断言失败：首错非 bound 对账失配（{caught}）")
    print(f"[gate][NC2 检出] {caught}")
    g5_core(src_data)        # sanity：原文件 PASS
    okmsg("NC2 篡 bound 分子（b0 分子＋1）必被 G5 拦：分区 bound 逐件对账首错即"
          "『源码 b0 ≠ json partition[0].bound』（防假拦截预断言过）；原文件 sanity PASS")


def nc3_endpoint_tamper(src_data: str) -> None:
    m5 = re.search(r"^def e5 : ℚ := (-?\d+)/(\d+)$", src_data, re.M)
    m6 = re.search(r"^def e6 : ℚ := (-?\d+)/(\d+)$", src_data, re.M)
    if not m5 or not m6:
        raise GateFail("NC3 预置失败：未找到 e5/e6 字面量")
    v5, v6 = f"{m5.group(1)}/{m5.group(2)}", f"{m6.group(1)}/{m6.group(2)}"
    tampered = src_data.replace(f"def e5 : ℚ := {v5}", f"def e5 : ℚ := {v6}", 1)
    tampered = tampered.replace(f"def e6 : ℚ := {v6}", f"def e6 : ℚ := {v5}", 1)
    if tampered == src_data:
        raise GateFail("NC3 预置失败：交换未生效")
    # 防假拦截预断言（R13C/R14A 先例）：交换后链确在 e5≤e6 处破序（Fraction 亲算）
    if Fr(v6) <= Fr(v5):
        raise GateFail("NC3 预置失败：交换后 e5≤e6 仍成立（未构成乱序，假拦截风险）")
    caught = None
    try:
        g5_core(tampered)
    except GateFail as e:
        caught = e
    if caught is None:
        raise GateFail("NC3 失守：篡端点乱序后 G5 未报错")
    if "端点" not in str(caught):
        raise GateFail(f"NC3 首错命题断言失败：首错非端点命题（{caught}）")
    print(f"[gate][NC3 检出] {caught}")
    g5_core(src_data)        # sanity：原文件 PASS
    okmsg("NC3 篡端点乱序（交换 e5/e6 字面量）必被 G5 拦：首错即端点命题"
          "（13 端点与 regions 无缝对账先拦；交换后 e5>e6 亲算预断言过——"
          "防假拦截）；原文件 sanity PASS")


# ------------------------------------------------------------------ main
def main() -> None:
    t0 = time.time()
    print(f"[gate] r15_b6_gate.py seed={SEED_GATE}（确定性；抽查点为 seed 复放）")
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
    for p in (DATA_LEAN, MAIN_LEAN, RESULTS / "r15_b6_data.json"):
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
    nc2_bound_tamper(src_data)
    nc3_endpoint_tamper(src_data)
    print(f"[gate] G2 elaboration 墙钟：Data {walls['data_s']}s＋Main {walls['main_s']}s"
          f"（均 ≤ {ELAB_LIMIT_S}s）；G3 定理 {g3['theorems']} 件")


if __name__ == "__main__":
    main()
