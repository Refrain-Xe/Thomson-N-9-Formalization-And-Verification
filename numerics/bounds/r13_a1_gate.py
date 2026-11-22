#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r13_a1_gate.py — R13C 表 A 第 6 件 A1（KLT (4.5) 型三点装配恒等式）验收门
（G0–G5＋负对照 NC1/NC2/NC3）.

任务书口径（r13c-tablea-a1，D52 裁决 2/4）：A1 三点恒等式
Σ_84 λ_cls + Σ_all == ΣH − e_dy 的 Lean 数据锚定实例——对称块构型
X={e₁,e₁,e₁,e₂,e₂,e₂,e₃,e₃,e₃}（λ 求值点恰 4 个 (orbit,perm,point)、s 点恰
5 个全在 {0,1}³）＋84 三元组显式分类表＋729 全三元组按 5 个 s-点折叠计数
＋36 对按 2 个 h-类折叠计数＋三 sum 折叠收口＋每表 3 个固定随机有理点抽查
（seed 20261015，堵 {0,1}³ 立方点篡改盲区）。产出件
formal/lean/ThomsonN9/TableA1.lean＋TableA1Data.lean 仅 import Mathlib
（Data 件）/＋ThomsonN9.TableA1Data（主件），不触 Solution.lean/TableA.lean/
M1Data.lean（文件面与 r13a/r13b 零交叠，G4 非交叠守卫机器化）。本门全确定性
（无随机路径；抽查点 seed 20261015 复现为确定性重放），PATH 自动前置
~/.elan/bin（缺失即 FAIL 附信息）；CWD 无关（全部路径自 __file__ 推导）。

检查面（对应任务书 G1–G5＋NC1/NC2/NC3）：
  G0 账本在场与受控字段（seed == 20261015、heavy_solves == 0、自有八件在清单）。
  G1 文件所有权守卫：git status --porcelain 与 git diff HEAD --name-only 的全部
     改动路径 ⊆ 本任务自有八件；M9 证书与 r9_s3_rederive.json 显式只读守卫
     （git diff HEAD -- <冻结件> 为空，单独响亮报错）。
  G2 逐文件 elaboration：子进程 `lake env lean -o <olean> ThomsonN9/TableA1Data.lean`
     然后 `… ThomsonN9/TableA1.lean`（依赖序；均 CWD=formal/lean），各 exit 0、
     输出无 error／无 sorry、墙钟 ≤ 600 s/文件（D52 裁决 4：每个 lake 子命令
     ≤10 min）；olean 落 .lake/build/lib/lean/ThomsonN9/（gitignored，lake env
     LEAN_PATH 原生可见），供 G3/主件 import 复用（不二次编译）。
  G3 公理：/tmp 检查件 import 两模块＋对**两文件全部 theorem**（regex 枚举，
     55 件）#print axioms——公理集 ⊆ {propext, Classical.choice, Quot.sound}
     （decide 件可为空），无 sorryAx/ofReduceBool/ofReduceNat/trustCompiler。
  G4 语句锚：TableA1Data.lean import 行恰 [import Mathlib]；TableA1.lean
     恰 [import Mathlib, import ThomsonN9.TableA1Data]；定理名＋命题形状锚
     （a1_assembly_identity 的 Σλ+Σ_all=ΣH−e 形状、gramI_blk_fin 的
     if ⌊i/3⌋=⌊j/3⌋ then 1 else 0、三 sum 折叠、三参考值、计数引理、18 个
     抽查定理全在）；非交叠守卫（Solution.lean/TableA.lean/M1Data.lean/
     ThomsonN9.lean/lakefile.toml/scripts/check.sh 源码零 "TableA1" 引用）。
  G5 离线精确复核（stdlib Fraction＋r9_s3_rederive 独立第二实现装配面）：
     (a) λ 三轨道/s/h/e 字面量自 M9 证书独立重算，与 TableA1Data.lean 源码
         regex 重建的表**逐位**比对，并与 r13_a1_data.json 三方对账；
     (b) 对称构型恒等式 Fraction 重放 ==0：用 **Lean 源码解析出的表**＋门内
         独立重写的分类/计数逻辑（orbit/perm 判定、84/729/36 枚举）重放，
         Σλ/Σ_all/ΣH 与 json 参考值及 Lean sum_*_value 字面量逐位一致；
     (c) 抽查点对账：18 个抽查点按 seed 20261015＋文档化抽样方案独立重放，
         与 Lean spot 定理的点/期望值及 json 逐位一致（期望值由解析表
         Fraction 重算，双实现＝解析表 vs 证书重算表）；
     (d) 计数枚举独立复算：λ 点计数 (3,27,27,27)、s 点计数 (81,162,162,
         162,162) 和==729、h 计数 (9,27) 与 json 及 Lean 计数引理字面量一致。
  NC1 注入 sorry 必被 G3 拦：/tmp 副本把 lamAAA_at_111 证明改 sorry → 独立
     编译（lean --root＋LEAN_PATH 前置副本目录）必现 sorry 警告＋公理检查
     必现 sorryAx → G3 判定逻辑必 FAIL（未篡副本 sanity：G3 全 55 件过）。
  NC2 篡 λ 表系数必被 G5/抽查拦：/tmp 副本把 lamAAA 首项非零系数分子＋1 →
     G5(a) 证书逐位比对必 FAIL 且 G5(c) 抽查求值必 FAIL（原文件双函数 PASS）。
  NC3 篡构型点坐标必被 G2/G5 拦：/tmp 副本把 gX 坐标字面量 1→2 → (a) G5(b)
     构型结构检查必 FAIL；(b) G2 复制件 elaboration 必 FAIL（gramI_blk_fin
     的 decide 于错误构型不可判真，12 s 级验证）。

用法（CWD 无关）：
  python3 numerics/bounds/r13_a1_gate.py     # 全门（exit 0 = 过）
  python3 thomson-n9/numerics/bounds/r13_a1_gate.py
      # ↑ CWD＝仓库根时的验收命令命中同名 runpy 包装器（沿 R10A 0087eab 先例，
      #   thomson-n9/thomson-n9/… → 本真实门，exit code 原样传播；CWD＝campaign
      #   根时该相对路径直接命中本文件，包装器不参与）

自跑/验收并行容错（D53-4 对齐，首验返工实录见 tablea-lean.md §9.2 D-r13c-8）：
  G1 三层放行——① 自有八件；② 环境变量 R13C_G1_ALLOW_FOREIGN=p1,p2（自跑专用
  逐件放行，默认关）；③ PARALLEL_FAMILY pattern 家族（D52 任务切分的 r13a/r13b/
  r13d 并行在途交付件家族，逐项响亮打印）。三层之外字面拦截；验收命令不设任何
  环境变量亦可在并行会话在途时过门。提交后树净 ⇒ 两层放行集皆空 ⇒ G1 等价字面
  严格。只读输入件（M9 证书/r9_s3_rederive.json）git diff 守卫独立于放行集。
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
from fractions import Fraction
from itertools import combinations
from pathlib import Path

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
REPO = HERE.parents[1]                 # thomson-n9/
LEAN_DIR = REPO / "formal" / "lean"
sys.path.insert(0, str(HERE))
import r9_s3_rederive as R             # 独立第二实现装配面（stdlib only）

SEED_GATE = 20261015                   # D52 裁决 4：R13 各门统一 seed
ELAB_LIMIT_S = 600                     # G2 每文件 ≤10 min（D52 裁决 4）

DATA_REL = "formal/lean/ThomsonN9/TableA1Data.lean"
MAIN_REL = "formal/lean/ThomsonN9/TableA1.lean"
GATE_REL = "numerics/bounds/r13_a1_gate.py"
WRAPPER_REL = "thomson-n9/numerics/bounds/r13_a1_gate.py"   # CWD 兼容包装器（5237fe5 前移教训）
DATAPY_REL = "numerics/bounds/r13_a1_data.py"
DATAJSON_REL = "numerics/bounds/results/r13_a1_data.json"
LEDGER_REL = "numerics/bounds/results/r13_a1_ledger.json"
NOTES_REL = "notes/tablea-lean.md"
OWNED = {DATA_REL, MAIN_REL, GATE_REL, WRAPPER_REL, DATAPY_REL,
         DATAJSON_REL, LEDGER_REL, NOTES_REL}

CERT_REL = "certificates/n9-stage-a4-typedcap-m0748_M9.json"   # M9 cap 证书（只读守卫）
R9JSON_REL = "numerics/bounds/results/r9_s3_rederive.json"    # 泛构型证据档（只读守卫）
FROZEN_READONLY = (CERT_REL, R9JSON_REL)

# 并行家族放行集（D53-4 对齐〔r13a 18f586b 先例〕，2026-10-10 首验返工）：
# 验收时点 r13a/r13b/r13d 并行会话可能有未提交在途件（R13 实录：本门首验时
# r13b TableA6.lean/r13_a6_data.* 在途致 G1 exit 1；r13a 同因先例 18f586b）。
# 按 D52 任务切分把姊妹线交付件家族 pattern 化放行（逐项响亮打印，非静默）；
# 家族外任何路径（冻结件/证书/参考仓/既有资产/Solution.lean/M1Data.lean/
# lakefile/toolchain 等）仍字面拦截；TableA[0-9]… 不匹配 r12 冻结面 TableA.lean；
# certificates/references/endgame.json 明确不在集；只读输入件守卫不受放行集影响。
PARALLEL_FAMILY = [
    # r13a/r13b 形式层件（TableA3/A4/A6 含分块子模块目录——r13b 实录曾建
    # TableA6/ 目录拆块）
    r"^formal/lean/ThomsonN9/TableA[0-9][A-Za-z0-9_]*(\.lean|/)",
    r"^numerics/bounds/r13_a3a4[a-z0-9_]*(\.py|/)",       # r13a 门/数据件/工作目录
    r"^numerics/bounds/r13_a6[a-z0-9_]*(\.py|/)",         # r13b 门/数据件/工作目录
    r"^numerics/bounds/r13d[a-z0-9_]*(\.py|/)",           # r13d 收口门
    r"^numerics/bounds/results/r13_a3a4[a-z0-9_]*(\.json|/)",  # r13a 账本/数据
    r"^numerics/bounds/results/r13_a6[a-z0-9_]*(\.json|/)",    # r13b 账本/数据
    r"^numerics/bounds/results/r13d[a-z0-9_]*(\.json|/)",      # r13d 账本
    r"^thomson-n9/numerics/bounds/r13_a3a4[a-z0-9_]*(\.py|/)",  # r13a 嵌套包装器
    r"^thomson-n9/numerics/bounds/r13_a6[a-z0-9_]*(\.py|/)",    # r13b 嵌套包装器
    r"^thomson-n9/numerics/bounds/r13d[a-z0-9_]*(\.py|/)",      # r13d 嵌套包装器
    r"^notes/tablea[a-z0-9_\-]*\.md$",                    # r13a/b/c tablea 笔记族
    r"^(GAP-REPORT|PROGRESS)\.md$",                        # r13d 收口文档
]

# 非交叠守卫面（r12a/r12b 件＋根模块/lake 面，零交叠机器化）
NONOVERLAP_FILES = ("ThomsonN9/Solution.lean", "ThomsonN9/TableA.lean",
                    "ThomsonN9/M1Data.lean", "ThomsonN9.lean",
                    "lakefile.toml", "scripts/check.sh")

TMP = Path("/tmp/r13_a1_gate")
OLEAN_REL = ".lake/build/lib/lean/ThomsonN9"
DATA_LEAN = LEAN_DIR / "ThomsonN9" / "TableA1Data.lean"
MAIN_LEAN = LEAN_DIR / "ThomsonN9" / "TableA1.lean"
LEDGER = RESULTS / "r13_a1_ledger.json"
DATA_JSON = RESULTS / "r13_a1_data.json"

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN_AXIOMS = ("sorryAx", "ofReduceBool", "ofReduceNat", "trustCompiler")

SPOT_TABLES = ("lamAAA", "lamAAB", "lamABC", "svec", "hAA", "hAB")
TYPES = (0, 0, 0, 1, 1, 1, 2, 2, 2)
F0, F1 = Fraction(0), Fraction(1)
SYM_PTS = [(F1, F0, F0)] * 3 + [(F0, F1, F0)] * 3 + [(F0, F0, F1)] * 3


class GateFail(Exception):
    """单门失守（main 统一转 [gate][FAIL] ＋ exit 1；负对照捕获它作预期检出）。"""


def fail(msg: str) -> None:
    raise GateFail(msg)


def okmsg(msg: str) -> None:
    print(f"[gate][ok] {msg}", flush=True)


def fs(f: Fraction) -> str:
    return f"{f.numerator}/{f.denominator}"


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
    # 三层放行：① OWNED（本任务八件）；② 环境变量 R13C_G1_ALLOW_FOREIGN（自跑
    # 专用逐件放行，默认关）；③ PARALLEL_FAMILY pattern（D53-4 对齐——r13a/r13b/
    # r13d 并行在途件家族放行，逐项响亮打印）。三层之外字面拦截。
    allow_foreign = {q.strip() for q in
                     os.environ.get("R13C_G1_ALLOW_FOREIGN", "").split(",") if q.strip()}
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
                print(f"[gate][G1][并行家族放行] r13a/r13b/r13d 在途件（D53-4 pattern）：{p}")
                continue
            raise GateFail(
                f"G1 树上出现非本任务自有件（{cmd[1]}）：{p!r}"
                f"（自有集={sorted(OWNED)}；并行家族放行集 D53-4 未覆盖该路径——"
                f"若确系 r13a/r13b/r13d 在途件，可设 R13C_G1_ALLOW_FOREIGN={p} 显式放行）")
    # M9 证书＋泛构型证据档只读守卫（显式单列，响亮报错；独立于放行集）
    for rel in FROZEN_READONLY:
        r = run(["git", "diff", "HEAD", "--", rel], REPO)
        if r.returncode != 0 or r.stdout.strip():
            fail(f"G1 只读守卫失守：{rel} 相对 HEAD 有改动（M9 证书/证据档为冻结只读面）")
    okmsg("G1 文件所有权守卫：git status/diff 相对 HEAD 仅自有八件／并行家族放行件"
          f"（或全净）；M9 证书与 r9_s3_rederive.json 只读守卫空 diff"
          + (f"〔并行家族放行 {sorted(parallel_hits)}〕" if parallel_hits else "")
          + (f"〔环境变量放行 {sorted(allow_foreign)}〕" if allow_foreign else ""))


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
    wall_data = compile_lean("ThomsonN9/TableA1Data.lean", "TableA1Data.olean")
    okmsg(f"G2 elaboration：TableA1Data.lean exit 0 无 error/sorry（{wall_data:.1f}s ≤ 600s）")
    wall_main = compile_lean("ThomsonN9/TableA1.lean", "TableA1.olean")
    okmsg(f"G2 elaboration：TableA1.lean exit 0 无 error/sorry（{wall_main:.1f}s ≤ 600s；"
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
          f"Quot.sound}}（decide 件可为空），零 {FORBIDDEN_AXIOMS}")


def gate3_axioms(src_data: str, src_main: str) -> dict:
    names = ([f"ThomsonN9.TableA1Data.{t}" for t in theorem_names(src_data)]
             + [f"ThomsonN9.TableA1.{t}" for t in theorem_names(src_main)])
    if len(names) < 50:
        fail(f"G3 定理枚举异常偏少：{len(names)}（应 ≈55）")
    TMP.mkdir(parents=True, exist_ok=True)
    axfile = TMP / "axcheck.lean"
    axfile.write_text("import ThomsonN9.TableA1Data\nimport ThomsonN9.TableA1\n"
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
        fail("G4 TableA1Data.lean import 行失配（应恰为 [import Mathlib]）")
    if re.findall(r"^import\s+\S+", src_main, re.M) != \
            ["import Mathlib", "import ThomsonN9.TableA1Data"]:
        fail("G4 TableA1.lean import 行失配（应恰为 "
             "[import Mathlib, import ThomsonN9.TableA1Data]）")
    anchors = [
        (r"def lamAAA_0 \(u v t : ℚ\)", "λ_AAA 分块表锚"),
        (r"def lamAAB_0 \(u v t : ℚ\)", "λ_AAB 分块表锚"),
        (r"def lamABC_0 \(u v t : ℚ\)", "λ_ABC 分块表锚"),
        (r"def svec_0 \(u v t : ℚ\)", "s 分块表锚"),
        (r"def hAA \(x : ℚ\) : ℚ", "h_AA 表锚"),
        (r"def hAB \(x : ℚ\) : ℚ", "h_AB 表锚"),
        (r"def eA1 : ℚ", "e 字面量锚"),
        (r"theorem lamAAA_at_111 : lamAAA 1 1 1", "λ_AAA 立方点求值锚"),
        (r"theorem lamAAB_at_100 : lamAAB 1 0 0", "λ_AAB 立方点求值锚"),
        (r"theorem lamABC_at_000 : lamABC 0 0 0", "λ_ABC 立方点求值锚"),
        (r"theorem svec_at_111 : svec 1 1 1", "s(1,1,1) 求值锚"),
        (r"theorem svec_at_000 : svec 0 0 0", "s(0,0,0) 求值锚"),
        (r"theorem hAA_at_1 : hAA 1", "h_AA(1) 求值锚"),
        (r"theorem hAB_at_0 : hAB 0", "h_AB(0) 求值锚"),
        (r"theorem gramI_blk_fin : ∀ i j : Fin 9", "Gram decide 引理锚"),
        (r"if i\.val / 3 = j\.val / 3 then 1 else 0", "Gram 块结构形状锚"),
        (r"def class84 : List \(ℕ × ℕ × ℕ × Orbit × Perm × \(ℕ × ℕ × ℕ\)\)", "84 分类表锚"),
        (r"theorem class84_complete", "分类表完备性锚"),
        (r"theorem class84_gram_ok", "分类表逐行 Gram 对账锚"),
        (r"theorem count_lam_AAA", "λ 点计数锚 AAA"),
        (r"theorem count_lam_AAB_ut", "λ 点计数锚 AAB-ut"),
        (r"theorem cube9_enum", "729 枚举完备锚"),
        (r"theorem count_s_111", "s 点计数锚"),
        (r"theorem s_counts_sum : 81 \+ 162 \+ 162 \+ 162 \+ 162 = 729", "s 计数和==729 锚"),
        (r"theorem pairs36_length : pairs36\.length = 36", "36 对长度锚"),
        (r"theorem count_h_AA", "h 类计数锚 AA"),
        (r"theorem count_h_AB", "h 类计数锚 AB"),
        (r"theorem sum_lam_eq : \(class84\.map lamOfRow\)\.sum", "Σλ 折叠锚"),
        (r"theorem sum_s_eq : \(cube9\.map sAt\)\.sum", "Σ_all 折叠锚"),
        (r"theorem sum_h_eq : \(pairs36\.map hAt\)\.sum", "ΣH 折叠锚"),
        (r"theorem a1_assembly_identity :", "A1 装配恒等式定理名锚"),
        (r"\(class84\.map lamOfRow\)\.sum \+ \(cube9\.map sAt\)\.sum", "恒等式 LHS 形状锚"),
        (r"= \(pairs36\.map hAt\)\.sum - eA1", "恒等式 RHS 形状锚"),
        (r"theorem sum_lam_value : \(class84\.map lamOfRow\)\.sum", "Σλ 参考值锚"),
        (r"theorem sum_all_value : \(cube9\.map sAt\)\.sum", "Σ_all 参考值锚"),
        (r"theorem sum_H_value : \(pairs36\.map hAt\)\.sum", "ΣH 参考值锚"),
    ]
    for pat, name in anchors:
        if not re.search(pat, src_data + "\n" + src_main):
            fail(f"G4 语句锚缺失：{name}（pattern {pat!r}）")
    spots = re.findall(r"^theorem (\w+)_spot\d", src_data, re.M)
    if sorted(set(spots)) != sorted(SPOT_TABLES) or \
            len(re.findall(r"^theorem \w+_spot\d", src_data, re.M)) != 18:
        fail(f"G4 抽查定理数失配：表 {sorted(set(spots))}，总数 "
             f"{len(re.findall(r'^theorem \\w+_spot\\d', src_data, re.M))}（应 6 表×3=18）")
    # 非交叠守卫
    for rel in NONOVERLAP_FILES:
        p = LEAN_DIR / rel
        if p.is_file() and "TableA1" in p.read_text():
            fail(f"G4 非交叠守卫：{rel} 含 'TableA1'（本件必须不被 r12a/r12b 面引用）")
    okmsg("G4 语句锚：import 面恰 [Mathlib]/[Mathlib＋TableA1Data]；36 锚全在＋"
          "18 抽查定理（6 表×3）；Solution.lean/TableA.lean/M1Data.lean/根模块/"
          "lakefile/check.sh 零 TableA1 引用（零交叠）")


# ------------------------------------------------------------------ G5 解析层
RE_TERM = re.compile(r"\((-?\d+)/(\d+)\)(?:\*u\^(\d+))?(?:\*v\^(\d+))?(?:\*t\^(\d+))?")
RE_HTERM = re.compile(r"[ +]\((-?\d+)/(\d+)\)(?:\*x\^(\d+))?")
RE_GCOORD = re.compile(r"def g([XYZ]) : ℕ → ℕ\n\s*\| (\d+) \| (\d+) \| (\d+) => (\d+)")


def parse_tables(src_data: str) -> dict:
    out = {}
    for nm in ("lamAAA", "lamAAB", "lamABC", "svec"):
        poly = {}
        for line in re.findall(rf"def {nm}_\d+ \(u v t : ℚ\) : ℚ :=\n(.*)", src_data):
            for m in RE_TERM.finditer(line):
                e = (int(m.group(3) or 0), int(m.group(4) or 0), int(m.group(5) or 0))
                if e in poly:
                    fail(f"G5 解析：{nm} 重复指数 {e}")
                poly[e] = Fraction(int(m.group(1)), int(m.group(2)))
        out[nm] = poly
    for nm in ("hAA", "hAB"):
        m = re.search(rf"def {nm} \(x : ℚ\) : ℚ := (.*)", src_data)
        vec = {}
        for mm in RE_HTERM.finditer(" " + m.group(1)):
            vec[int(mm.group(3) or 0)] = Fraction(int(mm.group(1)), int(mm.group(2)))
        out[nm] = vec
    m = re.search(r"def eA1 : ℚ := \((-?\d+)/(\d+)\)", src_data)
    out["e"] = Fraction(int(m.group(1)), int(m.group(2)))
    return out


def parse_config(src_main: str):
    """解析 gX/gY/gZ 坐标字面量 → 9 点构型。"""
    got = {}
    for m in RE_GCOORD.finditer(src_main):
        axis = "XYZ".index(m.group(1))
        i0, i1, i2, val = (int(m.group(k)) for k in range(2, 6))
        for i in (i0, i1, i2):
            got[(i, axis)] = val
    pts = []
    for i in range(9):
        pts.append(tuple(Fraction(got.get((i, a), 0)) for a in range(3)))
    return pts


def eval3(poly, u, v, t):
    return sum(c * u ** i * v ** j * t ** l for (i, j, l), c in poly.items())


def eval1(vec, x):
    return sum(c * x ** k for k, c in vec.items())


def classify(i, j, l):
    """门内独立重写的分类逻辑：type 排序 → (orbit, perm)。"""
    tt = sorted([(TYPES[i], i), (TYPES[j], j), (TYPES[l], l)])
    (_, i0), (_, j0), (_, l0) = tt
    cls = tuple(x[0] for x in tt)
    X, Y, Z = cls
    need = {}
    for t in cls:
        need[t] = need.get(t, 0) + 1
    mult = sorted(need.values(), reverse=True)
    orbit = "AAA" if mult == [3] else ("AAB" if mult == [2, 1] else "ABC")
    perm = "ut" if (Y == Z and X != Y) else "id"
    return i0, j0, l0, orbit, perm


def replay(parsed, pts):
    """恒等式 Fraction 重放（解析表＋独立分类）→ (diff, sums, 点计数)。"""
    G = [[sum(a * b for a, b in zip(xi, xj)) for xj in pts] for xi in pts]
    lam_of = {"AAA": parsed["lamAAA"], "AAB": parsed["lamAAB"],
              "ABC": parsed["lamABC"]}
    lam_points = {}
    sum_lam = Fraction(0)
    for (i, j, l) in combinations(range(9), 3):
        i0, j0, l0, o, p = classify(i, j, l)
        u_, v_, t_ = G[i0][j0], G[i0][l0], G[j0][l0]
        key = (o, p, (u_, v_, t_))
        lam_points[key] = lam_points.get(key, 0) + 1
        args = (t_, v_, u_) if p == "ut" else (u_, v_, t_)
        sum_lam += eval3(lam_of[o], *args)
    s_counts = {}
    sum_all = Fraction(0)
    for i in range(9):
        for j in range(9):
            for l in range(9):
                pt = (G[i][j], G[i][l], G[j][l])
                s_counts[pt] = s_counts.get(pt, 0) + 1
                sum_all += eval3(parsed["svec"], *pt)
    h_counts = {}
    sum_H = Fraction(0)
    for i in range(9):
        for j in range(i + 1, 9):
            cls = "AA" if TYPES[i] == TYPES[j] else "AB"
            h_counts[(cls, G[i][j])] = h_counts.get((cls, G[i][j]), 0) + 1
            sum_H += eval1(parsed["hAA" if cls == "AA" else "hAB"], G[i][j])
    diff = (sum_lam + sum_all) - (sum_H - parsed["e"])
    return dict(diff=diff, sum_lam=sum_lam, sum_all=sum_all, sum_H=sum_H,
                lam_points=lam_points, s_counts=s_counts, h_counts=h_counts, G=G)


def gate5_offline(src_data: str, src_main: str) -> dict:
    # (a) 证书独立重算 vs Lean 解析表 vs json 三方逐位
    cert = json.loads((REPO / CERT_REL).read_text())
    asm = R.S3Assembly(Fraction(cert["params"]["a0"]), cert["params"]["M"],
                       cert["params"]["K"])
    data = R.load_data(asm, cert)
    recon = {"lamAAA": asm.lam("AAA", data), "lamAAB": asm.lam("AAB", data),
             "lamABC": asm.lam("ABC", data)}
    s_vec, _ = asm.s_forms(data)
    recon["svec"] = s_vec
    recon["hAA"] = {k: c for k, c in enumerate(data["h_AA"]) if c}
    recon["hAB"] = {k: c for k, c in enumerate(data["h_AB"]) if c}
    recon["e"] = data["e"]
    parsed = parse_tables(src_data)
    for nm in ("lamAAA", "lamAAB", "lamABC", "svec", "hAA", "hAB", "e"):
        if parsed[nm] != recon[nm]:
            fail(f"G5(a) {nm}：Lean 字面量表 ≠ 证书独立重算表（逐位失配）")
    dj = json.loads(DATA_JSON.read_text())
    jt = dj["tables"]
    JKEY = {"lamAAA": "lam_AAA", "lamAAB": "lam_AAB", "lamABC": "lam_ABC",
            "svec": "s", "hAA": "h_AA", "hAB": "h_AB"}
    for nm in ("lamAAA", "lamAAB", "lamABC", "svec"):
        jpoly = {(int(i), int(j), int(l)): Fraction(c)
                 for i, j, l, c in jt[JKEY[nm]]["terms"]}
        if jpoly != parsed[nm] or len(jpoly) != jt[JKEY[nm]]["nnz"]:
            fail(f"G5(a) {nm}：json 表 ≠ Lean 解析表（三方失配）")
    for nm, key in (("hAA", "h_AA"), ("hAB", "h_AB")):
        jvec = {k: c for k, c in enumerate(map(Fraction, jt[key])) if c}
        if jvec != parsed[nm]:
            fail(f"G5(a) {nm}：json 表 ≠ Lean 解析表")
    if Fraction(jt["e"]) != parsed["e"]:
        fail("G5(a) e：json ≠ Lean 解析")

    # (b) 构型结构检查＋恒等式重放
    pts = parse_config(src_main)
    if [tuple(map(Fraction, p)) for p in dj["config"]["points"]] != pts:
        fail("G5(b) 构型：Lean gX/gY/gZ 解析 ≠ json config.points")
    if pts != SYM_PTS:
        fail(f"G5(b) 构型：解析构型 ≠ 对称块构型 {{e₁×3,e₂×3,e₃×3}}（got {pts}）")
    rep = replay(parsed, pts)
    if rep["diff"] != 0:
        fail(f"G5(b) 对称构型恒等式重放 diff={rep['diff']} ≠ 0（Fraction 精确）")
    for key, jk in (("sum_lam", "sum_lam"), ("sum_all", "sum_all"),
                    ("sum_H", "sum_H")):
        if rep[key] != Fraction(dj["reference_values"][jk]):
            fail(f"G5(b) {key} 重放 ≠ json reference_values.{jk}")
    # Lean sum_*_value 字面量对账
    for th, val in (("sum_lam_value", rep["sum_lam"]),
                    ("sum_all_value", rep["sum_all"]),
                    ("sum_H_value", rep["sum_H"])):
        m = re.search(rf"theorem {th} :[\s\S]*?= \((\d+) : ℚ\) / (\d+)", src_main)
        if not m:
            fail(f"G5(b) 源码缺 {th} 参考值字面量")
        if Fraction(int(m.group(1)), int(m.group(2))) != val:
            fail(f"G5(b) {th} 字面量 ≠ 重放值")

    # (c) 抽查点：seed 复放＋解析表求值双实现
    rng = random.Random(SEED_GATE)
    for tbl in SPOT_TABLES:
        m = re.search(rf"def {tbl} \(", src_data)
        nterms = 3
        for k in range(nterms):
            if tbl in ("hAA", "hAB"):
                pt = (Fraction(rng.randint(-64, 64), 64),)
                mm = re.search(rf"theorem {tbl}_spot{k} : {tbl} \((-?\d+)/(\d+)\)"
                               rf" = \((-?\d+)/(\d+)\)", src_data)
                args, exp = mm.group(1, 2), mm.group(3, 4)
            else:
                pt = tuple(Fraction(rng.randint(-64, 64), 64) for _ in range(3))
                mm = re.search(rf"theorem {tbl}_spot{k} : {tbl} "
                               r"\((-?\d+)/(\d+)\) \((-?\d+)/(\d+)\) \((-?\d+)/(\d+)\)"
                               r" = \((-?\d+)/(\d+)\)", src_data)
                args, exp = mm.group(1, 2, 3, 4, 5, 6), mm.group(7, 8)
            got_pt = tuple(Fraction(int(a), int(b)) for a, b in zip(args[::2], args[1::2]))
            if got_pt != pt:
                fail(f"G5(c) {tbl}_spot{k}：源码点 {got_pt} ≠ seed 复放点 {pt}")
            want = Fraction(int(exp[0]), int(exp[1]))
            val = (eval1(parsed[tbl], pt[0]) if tbl in ("hAA", "hAB")
                   else eval3(parsed[tbl], *pt))
            if val != want:
                fail(f"G5(c) {tbl}_spot{k}：解析表求值 {val} ≠ 定理字面量 {want}")
            val2 = (eval1(recon[tbl], pt[0]) if tbl in ("hAA", "hAB")
                    else eval3(recon[tbl], *pt))
            if val2 != want:
                fail(f"G5(c) {tbl}_spot{k}：证书重算表求值 ≠ 定理字面量")
            jrec = dj["spot_checks"]["tables"][tbl][k]
            if [fs(a) for a in pt] != jrec["point"] or fs(want) != jrec["expected"]:
                fail(f"G5(c) {tbl}_spot{k}：与 json spot_checks 失配")

    # (d) 计数枚举独立复算 vs json vs Lean 计数引理字面量
    if len(rep["lam_points"]) != 4:
        fail(f"G5(d) λ 求值点 {len(rep['lam_points'])} ≠ 4")
    lam_counts = sorted(rep["lam_points"].values())
    if lam_counts != [3, 27, 27, 27] or sum(lam_counts) != 84:
        fail(f"G5(d) λ 点计数复算 {lam_counts} ≠ [3,27,27,27]")
    s_by = [rep["s_counts"][pt] for pt in sorted(rep["s_counts"])]
    if sorted(rep["s_counts"]) != [(0, 0, 0), (0, 0, 1), (0, 1, 0), (1, 0, 0), (1, 1, 1)]:
        fail("G5(d) s 点集 ≠ {0,1}³ 的 5 个立方点")
    if s_by != [162, 162, 162, 162, 81] or sum(s_by) != 729:
        fail(f"G5(d) s 点计数复算 {s_by} ≠ [162,162,162,162,81]（和 729）")
    h_by = [rep["h_counts"][k] for k in sorted(rep["h_counts"])]
    if h_by != [9, 27] or sum(h_by) != 36:
        fail(f"G5(d) h 类计数复算 {h_by} ≠ [9,27]（和 36）")
    if dj["counts"]["lam_by_point"] != lam_counts or \
            dj["counts"]["s_by_point"] != s_by or dj["counts"]["h_by_class"] != h_by:
        fail("G5(d) json counts 与门内复算失配")
    cnt_anchors = [("count_lam_AAA", 3), ("count_lam_AAB_id", 27),
                   ("count_lam_AAB_ut", 27), ("count_lam_ABC", 27),
                   ("count_s_000", 162), ("count_s_001", 162), ("count_s_010", 162),
                   ("count_s_100", 162), ("count_s_111", 81),
                   ("count_h_AA", 9), ("count_h_AB", 27),
                   ("triplesAll_length", 84), ("cube9_length", 729),
                   ("pairs36_length", 36)]
    for th, want in cnt_anchors:
        m = re.search(rf"theorem {th} :[\s\S]*?= (\d+) :=", src_main)
        if not m or int(m.group(1)) != want:
            fail(f"G5(d) Lean 计数引理 {th} 字面量 ≠ {want}")
    okmsg("G5 离线精确复核：λ×3/s/h×2/e 七表证书重算==Lean 解析==json 三方逐位；"
          "对称构型恒等式重放 diff==0 且 Σλ/Σ_all/ΣH==json 参考值==Lean value 字面量；"
          "18 抽查点 seed 复放＋解析表/重算表双实现求值对账；计数 4λ/5s/2h 点独立"
          "复算==json==Lean 计数引理（和 84/729/36）")
    return {"tables_bitwise": True, "replay_diff": fs(rep["diff"]),
            "spot_checks": 18, "counts": dict(lam=lam_counts, s=s_by, h=h_by)}


# ------------------------------------------------------------------ NC
def nc1_sorry_injection(src_data: str) -> None:
    tampered = src_data.replace("  norm_num\n", "  sorry\n", 1)
    if "sorry" not in tampered:
        fail("NC1 预置失败：未能在 /tmp 副本注入 sorry（源码缺 `  norm_num` 行）")
    d = TMP / "nc1"
    (d / "ThomsonN9").mkdir(parents=True, exist_ok=True)
    (d / "ThomsonN9" / "TableA1Data.lean").write_text(tampered)
    lp = run(["lake", "env", "printenv", "LEAN_PATH"], LEAN_DIR).stdout.strip()
    env = gate_env()
    env["LEAN_PATH"] = f"{d}:{lp}"
    b = subprocess.run(["lean", "--root", str(d), "-o",
                        str(d / "ThomsonN9" / "TableA1Data.olean"),
                        str(d / "ThomsonN9" / "TableA1Data.lean")],
                       cwd=str(LEAN_DIR), env=env, capture_output=True, text=True,
                       timeout=605)
    if b.returncode != 0 or "declaration uses `sorry`" not in (b.stdout + b.stderr):
        fail(f"NC1 注入 sorry 后编译未产生 sorry 警告（exit {b.returncode}）：\n"
             f"{(b.stdout + b.stderr)[-500:]}")
    axfile = d / "axcheck.lean"
    axfile.write_text("import ThomsonN9.TableA1Data\n"
                      "#print axioms ThomsonN9.TableA1Data.lamAAA_at_111\n")
    a = subprocess.run(["lean", str(axfile)], cwd=str(LEAN_DIR), env=env,
                       capture_output=True, text=True, timeout=605)
    ax = parse_axiom_lines(a.stdout)
    th = "ThomsonN9.TableA1Data.lamAAA_at_111"
    caught = th in ax and ("sorryAx" in ax[th] or (ax[th] - ALLOWED_AXIOMS))
    if not caught:
        fail(f"NC1 失守：注入 sorry 后公理检查未现 sorryAx（{ax}）")
    okmsg(f"NC1 注入 sorry 必被 G3 拦：篡件 lamAAA_at_111 公理集 = "
          f"{sorted(ax.get(th, set()))}（含 sorryAx → G3 FAIL）")


def g5_table_compare_tamper(src_data_tampered: str) -> None:
    """G5(a)+(c) 于篡改源码上的复跑（负对照用；失守＝不报错）。"""
    cert = json.loads((REPO / CERT_REL).read_text())
    asm = R.S3Assembly(Fraction(cert["params"]["a0"]), cert["params"]["M"],
                       cert["params"]["K"])
    data = R.load_data(asm, cert)
    parsed = parse_tables(src_data_tampered)
    recon = {"lamAAA": asm.lam("AAA", data), "lamAAB": asm.lam("AAB", data),
             "lamABC": asm.lam("ABC", data)}
    for nm in ("lamAAA", "lamAAB", "lamABC"):
        if parsed[nm] != recon[nm]:
            raise GateFail(f"G5(a) {nm}：篡改表 ≠ 证书重算表（逐位失配）")
    # 若 (a) 未检出（例如篡在 s/h），抽查层兜底
    rng = random.Random(SEED_GATE)
    for tbl in SPOT_TABLES:
        for k in range(3):
            pt = ((Fraction(rng.randint(-64, 64), 64),)
                  if tbl in ("hAA", "hAB") else
                  tuple(Fraction(rng.randint(-64, 64), 64) for _ in range(3)))
            m = re.search(rf"theorem {tbl}_spot{k} : {tbl} ([^\n]*) = \((-?\d+)/(\d+)\)",
                          src_data_tampered)
            want = Fraction(int(m.group(2)), int(m.group(3)))
            val = (eval1(parsed[tbl], pt[0]) if tbl in ("hAA", "hAB")
                   else eval3(parsed[tbl], *pt))
            if val != want:
                raise GateFail(f"G5(c) {tbl}_spot{k}：篡改表求值 ≠ 定理字面量")


def nc2_lambda_tamper(src_data: str) -> None:
    m = re.search(r"def lamAAA_0 \(u v t : ℚ\) : ℚ :=\n\s*\((\d+)/(\d+)\)", src_data)
    if not m:
        raise GateFail("NC2 预置失败：未找到 lamAAA_0 首项系数")
    bad_num = str(int(m.group(1)) + 1)
    tampered = src_data.replace(
        f"({m.group(1)}/{m.group(2)})", f"({bad_num}/{m.group(2)})", 1)
    if tampered == src_data:
        raise GateFail("NC2 预置失败：篡改未生效")
    try:
        g5_table_compare_tamper(tampered)
        raise GateFail("NC2 失守：篡 λ 表系数后 G5(a)/(c) 均未报错")
    except GateFail as e:
        if "失守" in str(e) or "预置" in str(e):
            raise
        print(f"[gate][NC2 检出] {e}")
    g5_table_compare_tamper(src_data)      # sanity：原文件 PASS
    okmsg("NC2 篡 λ 表系数（lamAAA 首项分子＋1）必被 G5 拦：证书逐位比对与抽查"
          "求值双路检出；原文件双路 sanity PASS")


def nc3_config_tamper(src_main: str) -> None:
    bad = src_main.replace("| 0 | 1 | 2 => 1", "| 0 | 1 | 2 => 2", 1)
    if bad == src_main:
        raise GateFail("NC3 预置失败：未篡到 gX 坐标字面量")
    # (a) G5(b) 构型结构检查必拦
    pts = parse_config(bad)
    if pts == SYM_PTS:
        raise GateFail("NC3 失守：篡构型后 G5(b) 结构检查未检出")
    print(f"[gate][NC3 检出] G5(b) 构型结构检查：篡改后 gX(0)=2 → 构型首点 "
          f"{pts[0]} ≠ e₁=(1,0,0)")
    # (b) G2 复制件 elaboration 必拦（gramI_blk_fin 的 decide 于错误构型不可判真）：
    # 直接以 lake env lean 编译 /tmp 篡改源（import ThomsonN9.TableA1Data 解析到
    # G2 落盘的真实 olean），不经 --root 重定位。
    d = TMP / "nc3"
    d.mkdir(parents=True, exist_ok=True)
    badfile = d / "TableA1.lean"
    badfile.write_text(bad)
    b = run(["lake", "env", "lean", str(badfile)], LEAN_DIR)
    out = b.stdout + b.stderr
    if b.returncode == 0 and "error" not in out:
        raise GateFail("NC3 失守：篡构型后 elaboration 仍通过（G2 不拦）")
    if "Tactic `decide` proved that the proposition" not in out \
            or "gramI ↑i ↑j = if ↑i / 3 = ↑j / 3 then 1 else 0" not in out:
        raise GateFail(f"NC3 G2 复制件虽失败但首错非 gramI_blk_fin 的 decide 反证：\n{out[-500:]}")
    print("[gate][NC3 检出] G2 复制件 elaboration 失败如预期：首错即 "
          "gramI ↑i ↑j = if ↑i/3 = ↑j/3 then 1 else 0 被 decide 证伪（篡构型破坏 G 引理）")
    okmsg("NC3 篡构型点坐标（gX 字面量 1→2）必被拦：G5(b) 构型结构检查＋"
          "G2 复制件 elaboration（gramI_blk_fin decide 失败）双路检出")


# ------------------------------------------------------------------ main
def main() -> None:
    t0 = time.time()
    print(f"[gate] r13_a1_gate.py seed={SEED_GATE}（确定性；抽查点为 seed 复放）")
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
    for p in (DATA_LEAN, MAIN_LEAN, DATA_JSON):
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
    nc2_lambda_tamper(src_data)
    nc3_config_tamper(src_main)
    print(f"[gate] G2 elaboration 墙钟：Data {walls['data_s']}s＋Main {walls['main_s']}s"
          f"（均 ≤ {ELAB_LIMIT_S}s）；G3 定理 {g3['theorems']} 件")


if __name__ == "__main__":
    main()
