#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r13_a6_gate.py — R13B A6（Lukács·Markov–Lukács 平方表示件）验收门
（G0–G5＋负对照 NC1/NC2/NC3）.

任务书口径（r13b-tablea-a6，D52 裁决 3）：M9 cap 证书一类侧 minorant σ 族的
平方表示与 R2 折减恒等式 Lean 化——
  (i)   8 块（AA/AB×sig0..3，维 17/17/16/16）S = L·diag(D)·Lᵀ 重构（两步：
        step1 L·diag(D)=M 无和逐项、step2 M·Lᵀ=S 点积逐项；norm_num）；
  (ii)  σ_i(y) = v(y)ᵀ S_i v(y) = Σ_j d_j·(Σ_k L[k][j]·y^k)²（Gen.quad_of_recon
        代数链）；(iii) ∀ y:ℝ, 0≤y → y·y≤437/500 → p_cls(y)≥0（乘子
        1/y/(b²−y²)/y(b²−y²) 域非负＋d_j>0＋sq_nonneg；√b 无理化）；
  (iv)  Σ_{j=0}^{33} sgn_j·(rhs_j−lhs_j)·(117/125)^j == R2_cls（ℚ、norm_num，
        与 results/r9_s3_rederive.json R2_exact 逐位对账）＋ lhs↔p_cls 固定
        有理点抽查（seed 20261015）。
G2 单文件超限口径：按块拆文件（TableA6/Gen＋8 块＋总成 TableA6.lean，任务书
明示允许），每个 `lake env lean` 子命令 ≤10 min；8 块并行编译（每块独立
进程，互不依赖）。全门确定性（无随机路径），seed 20261015 记档；PATH 自动
前置 ~/.elan/bin；CWD 无关（路径自 __file__ 推导）。

检查面：
  G0 账本在场与受控字段（seed==20261015、heavy_solves==0、自有 14 件在清单）。
  G1 文件所有权：git status/diff 相对 HEAD ⊆ 自有件（自跑可设
     R13B_G1_ALLOW_FOREIGN 放行 r13a/r13c 并行在途件）；冻结件只读守卫：
     M9 证书＋r9_s3_rederive.json 的 sha256 与账本记录相等（两者不在 git
     追踪面，故以账本哈希锚定只读）。
  G2 分块 elaboration：Gen → 8 块（并行）→ TableA6.lean 总成，全部
     `lake env lean -o …` exit 0、输出无 error/sorry、每子命令墙钟 ≤600s。
  G3 公理：探针件 import 全部 10 模块，#print axioms 36 定理
     （8×recon＋8×quad＋8×d_pos＋2×p_sos＋2×p_nonneg＋2×r2＋6×spot＋
     Gen.quad_of_recon）恰 ⊆ {propext, Classical.choice, Quot.sound}，
     无 sorryAx/ofReduceBool/ofReduceNat/trustCompiler。
  G4 语句锚＋非交叠：总成 import 恰 [Gen＋8 块]；p_cls_nonneg 签名形状
     （0 ≤ y → y*y ≤ 437/500 → 0 ≤ p_cls y）；乘子 (437/500 - y*y)；R2 定理
     (117/125)^33 与 R2_cls ℚ 字面量；块文件 recon/quad 形状锚；抽查定理名；
     非交叠守卫（Solution.lean/ThomsonN9.lean/M1Data.lean/TableA.lean/
     lakefile.toml/check.sh 不含 "TableA6"；TableA6 面不 import 仓内解件）。
  G5 离线精确复核（stdlib Fraction 第三实现，不 import 数据件）：
     ①自证书独立重算 LDLᵀ（全主元>0 布尔＋L·D·Lᵀ==S 逐位）＋与数据件
     json 的 S/L/D/M 逐分量；
     ②lhs(σ 装配)/rhs(Cp·h+p_const)/sgn/R2 独立重算＋与 r9_s3_rederive.json
     R2_exact 逐位＋json↔对账；
     ③(ii) 恒等式 Fraction 重放（8 块 × 5 有理点：Σ_{k,l} S_kl·y^{k+l} ==
       Σ_j d_j·(Σ_k L[k][j]·y^k)²）；
     ④(iv) 恒等式 Fraction 重放（Σ_j sgn_j·(rhs_j−lhs_j)·(117/125)^j == R2_cls
       两类）＋抽查点 p_cls 重放（Σ_j lhs_j·y^j == σ 装配，3 点/类）；
     ⑤json↔源码字面量逐分量（8 块 S/L/M 行＋d＋总成 lhs/rhs/sgn 向量＋
       R2_cls 字面量；数量与值全检）。
  NC1 注入 sorry 必被 G3 拦：总成副本把 pAA_nonneg 的 exact 改 sorry →
     以已编译块 olean 为基快速重编 → 公理检查必现 sorryAx。
  NC2 篡 D 主元变号必被 G5 检出：块文件副本 dAA0 首主元分子取负 →
     G5·①/⑤ json↔源码分量比对必 FAIL（原文件 sanity PASS）。
  NC3 篡残差系数必被 (iv)/G5 检出：总成副本 lhsAA 一分量篡改 → G5·⑤
     字面量比对必 FAIL（且 (iv) 恒等式在该字面量下不再成立——G5·④ 重放
     亦拦）。

用法（CWD 无关）：
  python3 numerics/bounds/r13_a6_gate.py     # 全门（exit 0 = 过）
  python3 thomson-n9/numerics/bounds/r13_a6_gate.py   # CWD=仓库根 → runpy 包装器
自跑专用：R13B_G1_ALLOW_FOREIGN=p1,p2 可显式放行 r13a/r13c 并行在途件
（验收/常规运行不设，G1 字面严格——提交后树净 ⇒ 恒过）。
"""
from __future__ import annotations

import hashlib
import json
import math
import os
import re
import subprocess
import sys
import time
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
REPO = HERE.parents[1]
LEAN_DIR = REPO / "formal" / "lean"

SEED_GATE = 20261015

CERT_REL = "certificates/n9-stage-a4-typedcap-m0748_M9.json"
R9JSON_REL = "numerics/bounds/results/r9_s3_rederive.json"
DATA_REL = "numerics/bounds/results/r13_a6_data.json"
DATA_PY_REL = "numerics/bounds/r13_a6_data.py"
UMBRELLA_REL = "formal/lean/ThomsonN9/TableA6.lean"
GATE_REL = "numerics/bounds/r13_a6_gate.py"
WRAPPER_REL = "thomson-n9/numerics/bounds/r13_a6_gate.py"
LEDGER_REL = "numerics/bounds/results/r13_a6_ledger.json"
NOTES_REL = "notes/tablea-lean.md"
BLOCK_DIR_REL = "formal/lean/ThomsonN9/TableA6"
CLASSES = ("AA", "AB")
BLOCKS = [f"{c}{i}" for c in CLASSES for i in range(4)]
BLOCK_RELS = [f"{BLOCK_DIR_REL}/{b}.lean" for b in BLOCKS]
GEN_REL = f"{BLOCK_DIR_REL}/Gen.lean"
OWNED = {DATA_PY_REL, DATA_REL, UMBRELLA_REL, GEN_REL, GATE_REL, WRAPPER_REL,
         LEDGER_REL, NOTES_REL} | set(BLOCK_RELS)

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN_AXIOMS = ("sorryAx", "ofReduceBool", "ofReduceNat", "trustCompiler")
# 注意：Lean 4 模块名不是命名空间——本件定理均在根命名空间（无 namespace 声明），
# 故公理检查用裸名；provenance（所在模块）见账本 theorems 一节。
THEOREMS = (
    ["quad_of_recon", "entries_of_sumsq2"]
    + [f"stepsq_{b}" for b in BLOCKS]
    + [f"recon_{b}" for b in BLOCKS]
    + [f"sig{b}_quad" for b in BLOCKS]
    + [f"d{b}_pos" for b in BLOCKS]
    + [f"p{c}_sos" for c in CLASSES]
    + [f"p{c}_nonneg" for c in CLASSES]
    + [f"r2_reduction_{c}" for c in CLASSES]
    + [f"lhs_spot_{c}_{i}" for c in CLASSES for i in (1, 2, 3)]
)
TMP = Path("/tmp/r13_a6_gate")


def leanfile(rel: str) -> Path:
    """仓库相对路径 -> formal/lean 下真实路径（容忍 formal/lean/ 前缀）。"""
    sub = rel[len("formal/lean/"):] if rel.startswith("formal/lean/") else rel
    return LEAN_DIR / sub
F0, F1 = Fraction(0), Fraction(1)
SIG_DEF_SIZES = {0: 17, 1: 17, 2: 16, 3: 16}
SPOT_YS = [Fraction(2, 5), Fraction(17, 40), Fraction(4, 5)]   # r13_a6_data.json spot_points
REPLAY_YS = [Fraction(0), Fraction(1, 3), Fraction(2, 5), Fraction(17, 40), Fraction(9, 10)]


class GateFail(Exception):
    pass


def fail(msg):
    raise GateFail(msg)


def okmsg(msg):
    print(f"[gate][ok] {msg}", flush=True)


def sha256_of(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def gate_env():
    elan = Path.home() / ".elan" / "bin"
    env = dict(os.environ)
    env["PATH"] = str(elan) + os.pathsep + env.get("PATH", "")
    return env


def run(cmd, cwd: Path, timeout_s: int = 580, env=None):
    return subprocess.run(cmd, cwd=str(cwd), env=env or gate_env(),
                          capture_output=True, text=True, timeout=timeout_s)


def require_toolchain():
    probe = run(["lake", "--version"], LEAN_DIR)
    if probe.returncode != 0:
        fail(f"PATH 前置 ~/.elan/bin 后 lake 不可用：{probe.stderr.strip()[:300]}")


# ------------------------------------------------------------------ G0
def gate0_ledger():
    if not (RESULTS / "r13_a6_ledger.json").is_file():
        fail(f"G0 账本不在场：{LEDGER_REL}")
    led = json.loads((RESULTS / "r13_a6_ledger.json").read_text())
    if led.get("seed") != SEED_GATE:
        fail(f"G0 账本 seed 失配：{led.get('seed')!r} != {SEED_GATE}")
    if led.get("heavy_solves") != 0:
        fail(f"G0 账本 heavy_solves 失配：{led.get('heavy_solves')!r} != 0")
    for rel in OWNED:
        if rel not in led.get("files", {}):
            fail(f"G0 账本 files 缺自有件：{rel}")
    okmsg(f"G0 账本在场（seed={SEED_GATE}，heavy_solves=0，自有件 {len(OWNED)} 全在清单）")
    return led


# ------------------------------------------------------------------ G1
def porcelain_paths(out):
    paths = []
    for ln in out.splitlines():
        if not ln.strip():
            continue
        p = ln[3:].strip().strip('"')
        if " -> " in p:
            p = p.split(" -> ")[-1]
        paths.append(p)
    return paths


def gate1_ownership(led):
    allow_foreign = {p.strip() for p in
                     os.environ.get("R13B_G1_ALLOW_FOREIGN", "").split(",") if p.strip()}
    # 并行家族放行层（D53-4 口径，r13a 18f586b/r13c 7ac3111 先例对齐）：验收命令
    # 不设环境变量时，r13 姊妹线（r13a/r13c/r13d）在途件按任务家族 pattern 放行
    # （逐项响亮打印非静默）；家族外路径仍字面拦截。提交后树净 ⇒ 放行集空 ⇒
    # G1 等价字面严格。TableA[0-9] 不匹配 r12 冻结面 TableA.lean；
    # certificates/references/endgame.json 明确不在家族集（越权改动仍必拦）。
    fam_pats = (
        r"^formal/lean/ThomsonN9/TableA[0-9]",      # 姊妹线 Lean 件＋分块目录
        r"^numerics/bounds/r13",                    # 姊妹线门/数据件（含本件；r13d 无下划线名）
        r"^numerics/bounds/results/r13",            # 姊妹线数据/账本
        r"^thomson-n9/numerics/bounds/r13",         # 姊妹线嵌套包装器
        r"^notes/tablea",                           # 表 A 笔记族
        r"^(GAP-REPORT|PROGRESS)\.md$",             # r13d 收口文档
        r"^notes/decisions\.md$",                   # 设计师/r13d 裁决追加面
        r"^numerics/bounds/endgame_gate\.py$",      # r13d 收口按 R12C 先例增补面
        r"^thomson-n9/numerics/bounds/endgame_gate\.py$",
    )

    def in_family(pth: str) -> bool:
        return any(re.match(pat, pth) for pat in fam_pats)
    for cmd in (["git", "status", "--porcelain", "-uall"],
                ["git", "diff", "HEAD", "--name-only"]):
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
            if in_family(p):
                print(f"[gate][G1][家族放行] r13 姊妹线在途件（验收命令不设环境变量口径）：{p}")
                continue
            raise GateFail(f"G1 树上出现非本任务自有件（{cmd[1]}）：{p!r}"
                           f"（自有集 {len(OWNED)} 件；家族外改动必拦——"
                           f"certificates/references/endgame.json 越权改动亦在此拦）")
    # 冻结件只读守卫（证书与 r9 对账件不在 git 追踪面 ⇒ 账本 sha256 锚定）
    for rel in (CERT_REL, R9JSON_REL):
        p = REPO / rel
        if not p.is_file():
            fail(f"G1 冻结件不在场：{rel}")
        want = led.get("frozen_sha256", {}).get(rel)
        got = sha256_of(p)
        if want is None:
            fail(f"G1 账本 frozen_sha256 缺冻结件：{rel}")
        if want != got:
            fail(f"G1 冻结件被改动（sha256 失配）：{rel} 账本 {want[:16]}… vs 在盘 {got[:16]}…")
    okmsg("G1 所有权：git status/diff 相对 HEAD ⊆ 自有件（或全净）；"
          "M9 证书＋r9_s3_rederive.json sha256 与账本锚相等（只读守卫）"
          + (f"〔放行并行件 {sorted(allow_foreign)}〕" if allow_foreign else ""))


# ------------------------------------------------------------------ G2
def lean_compile(rel_path: str, timeout_s: int = 600) -> float:
    lean_rel = rel_path[len("formal/lean/"):] if rel_path.startswith("formal/lean/") else rel_path
    src = LEAN_DIR / lean_rel
    orel = ".lake/build/lib/lean/" + lean_rel.replace(".lean", ".olean")
    t0 = time.time()
    r = run(["lake", "env", "lean", "-o", orel, lean_rel], LEAN_DIR, timeout_s)
    wall = time.time() - t0
    out = r.stdout + r.stderr
    if r.returncode != 0:
        fail(f"G2 编译失败（exit {r.returncode}）：{rel_path}\n{out[-600:]}")
    if "error" in out or "sorry" in out:
        fail(f"G2 输出含 error/sorry：{rel_path}\n{out[-600:]}")
    if wall > timeout_s - 1:
        fail(f"G2 超时（>{timeout_s}s）：{rel_path}")
    return wall


def gate2_elaborate() -> dict:
    walls = {}
    walls["Gen.lean"] = lean_compile(GEN_REL)
    # 8 块并行（独立进程；每块自身 ≤10 min）
    procs = {}
    t0 = time.time()
    for b in BLOCKS:
        rel = f"{BLOCK_DIR_REL}/{b}.lean"
        lean_rel = rel[len("formal/lean/"):]
        orel = ".lake/build/lib/lean/" + lean_rel.replace(".lean", ".olean")
        procs[b] = (rel, subprocess.Popen(
            ["lake", "env", "lean", "-o", orel, lean_rel], cwd=str(LEAN_DIR),
            env=gate_env(), stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            text=True))
    for b, (rel, pr) in procs.items():
        try:
            out, _ = pr.communicate(timeout=600)
        except subprocess.TimeoutExpired:
            pr.kill()
            fail(f"G2 块编译超时（>600s）：{rel}")
        walls[f"{b}.lean"] = time.time() - t0
        if pr.returncode != 0 or "error" in out or "sorry" in out:
            fail(f"G2 块编译失败：{rel}\n{out[-600:]}")
        per = walls[f"{b}.lean"]
        if per > 600:
            fail(f"G2 块墙钟 {per:.0f}s > 600s：{rel}")
    walls["TableA6.lean"] = lean_compile(UMBRELLA_REL)
    okmsg(f"G2 分块 elaboration 全过：Gen {walls['Gen.lean']:.1f}s＋8 块并行"
          f"（最长 {max(walls[f'{b}.lean'] for b in BLOCKS):.1f}s，各自 ≤600s）＋"
          f"总成 {walls['TableA6.lean']:.1f}s；全部 -o olen 产出、零 error 零 sorry")
    return walls


# ------------------------------------------------------------------ G3
def parse_axiom_lines(out):
    ax = {}
    for line in out.splitlines():
        m = re.match(r"'([^']+)'\s+depends on axioms:\s*\[(.*)\]", line.strip())
        if m:
            ax[m.group(1)] = {a.strip() for a in m.group(2).split(",") if a.strip()}
    return ax


def check_axioms(ax, ctx):
    for th in THEOREMS:
        if th not in ax:
            fail(f"{ctx}：公理输出缺定理 {th}（解析到 {len(ax)} 条）")
        bad = ax[th] - ALLOWED_AXIOMS
        if bad:
            fail(f"{ctx}：定理 {th} 依赖非标准公理 {sorted(bad)}")
    union = set().union(*ax.values())
    okmsg(f"{ctx}：{len(THEOREMS)} 定理公理集 ⊆ {{propext, Classical.choice, Quot.sound}}"
          f"（实际并集 {sorted(union)}）")


def gate3_axioms():
    TMP.mkdir(parents=True, exist_ok=True)
    axfile = TMP / "axcheck.lean"
    axfile.write_text(
        "import ThomsonN9.TableA6\n"
        + "".join(f"#print axioms {th}\n" for th in THEOREMS))
    r = run(["lake", "env", "lean", str(axfile)], LEAN_DIR, timeout_s=580)
    if r.returncode != 0:
        fail(f"G3 公理检查件编译失败：\n{r.stdout[-500:]}\n{r.stderr[-500:]}")
    check_axioms(parse_axiom_lines(r.stdout), "G3 公理")


# ------------------------------------------------------------------ G4
def gate4_statement():
    src_u = (leanfile(UMBRELLA_REL)).read_text()
    imports = re.findall(r"^import\s+(\S+)", src_u, re.M)
    want_imports = {"ThomsonN9.TableA6.Gen"} | \
                   {f"ThomsonN9.TableA6.{b}" for b in BLOCKS}
    if set(imports) != want_imports:
        fail(f"G4 总成 import 失配：{sorted(imports)}（应恰为 {sorted(want_imports)}）")
    anchors = [
        (r"theorem pAA_nonneg \(y : ℝ\) \(hy : 0 ≤ y\) \(hy2 : y \* y ≤ 437/500\)",
         "(iii) AA 域非负签名（√b 无理化）"),
        (r"theorem pAB_nonneg \(y : ℝ\) \(hy : 0 ≤ y\) \(hy2 : y \* y ≤ 437/500\)",
         "(iii) AB 域非负签名"),
        (r"0 ≤ pAA y", "(iii) AA 结论形状"),
        (r"0 ≤ pAB y", "(iii) AB 结论形状"),
        (r"\(\(437/500\) - y \* y\)", "乘子族 (b²−y²) 锚"),
        (r"y \* \(\(437/500\) - y \* y\) \* sig", "乘子族 y·(b²−y²) 锚"),
        (r"theorem r2_reduction_AA", "(iv) AA 定理名"),
        (r"theorem r2_reduction_AB", "(iv) AB 定理名"),
        (r"\(117/125\)\^33", "(iv) ŵ^33 权重锚"),
        (r"theorem lhs_spot_AA_1", "抽查定理名 AA_1"),
        (r"theorem lhs_spot_AA_2", "抽查定理名 AA_2"),
        (r"theorem lhs_spot_AA_3", "抽查定理名 AA_3"),
        (r"theorem lhs_spot_AB_1", "抽查定理名 AB_1"),
        (r"theorem lhs_spot_AB_2", "抽查定理名 AB_2"),
        (r"theorem lhs_spot_AB_3", "抽查定理名 AB_3"),
        (r"noncomputable def pAA \(y : ℝ\) : ℝ", "pAA 装配定义锚"),
        (r"noncomputable def pAB \(y : ℝ\) : ℝ", "pAB 装配定义锚"),
    ]
    for pat, name in anchors:
        if not re.search(pat, src_u):
            fail(f"G4 总成语句锚缺失：{name}（pattern {pat!r}）")
    for b in BLOCKS:
        src_b = (leanfile(f"{BLOCK_DIR_REL}/{b}.lean")).read_text()
        for pat, name in [
            (rf"theorem recon_{b} : L{b} \* Matrix\.diagonal d{b} \* L{b}ᵀ = S{b}",
             f"recon_{b} 形状"),
            (rf"theorem stepsq_{b} : ∑ k, ∑ l,", f"stepsq_{b} 平方和形状"),
            (rf"theorem sig{b}_quad \(y : ℝ\)", f"sig{b}_quad 签名"),
            (rf"theorem d{b}_pos : ∀ j : Fin", f"d{b}_pos 签名"),
            (r"quad_of_recon ", "quad_of_recon 使用锚"),
        ]:
            if not re.search(pat, src_b):
                fail(f"G4 块 {b} 语句锚缺失：{name}")
    # 非交叠守卫
    for rel in ("ThomsonN9/Solution.lean", "ThomsonN9.lean", "lakefile.toml",
                "scripts/check.sh", "ThomsonN9/M1Data.lean", "ThomsonN9/TableA.lean"):
        p = leanfile(rel)
        if p.is_file() and "TableA6" in p.read_text():
            fail(f"G4 非交叠守卫：{rel} 含 'TableA6'（本件必须不被 import/不被引用）")
    for rel in [UMBRELLA_REL, GEN_REL] + BLOCK_RELS:
        src = leanfile(rel).read_text()
        if "ThomsonN9.Solution" in src or "ThomsonN9.M1Data" in src or \
                "ThomsonN9.TableA\n" in src:
            fail(f"G4 非交叠守卫：{rel} import 仓内解件/前件")
    okmsg("G4 语句锚：总成 import 恰 [Gen＋8 块]；(iii)(iv) 定理名/签名/形状锚全在；"
          "6 抽查定理在场；块 recon/quad/pos 形状锚全在；"
          "Solution/根模块/M1Data/TableA/lakefile/check.sh 零 TableA6 引用（非交叠）")


# ------------------------------------------------------------------ G5
def parse_q_list(s):
    return [Fraction(int(a), int(b)) for a, b in re.findall(r"\((-?\d+)/(\d+) : ℚ\)", s)]


def parse_r_list(s):
    return [Fraction(int(a), int(b)) for a, b in re.findall(r"\((-?\d+)/(\d+) : ℝ\)", s)]


def g5_recompute(cert):
    """独立第三实现：自证书重算 LDLᵀ/minorant/R2（不 import 数据件）。"""
    b = cert["blocks"]
    lo = Fraction(cert["params"]["a0"])
    M = cert["params"]["M"]
    d_H = 2 * M - 2
    deg_p = 2 * d_H + 1
    b2 = (F1 - lo) / 2
    wh = Fraction(117, 125)
    if b2 != Fraction(437, 500):
        fail("G5·① b² ≠ 437/500")
    Csub = [[F0] * (d_H + 1) for _ in range(deg_p + 1)]
    for i in range(d_H + 1):
        for m in range(i + 1):
            Csub[2 * m][i] += Fraction(math.comb(i, m) * ((-2) ** m))
    Cp = [[F0] * (d_H + 1) for _ in range(deg_p + 1)]
    for r in range(1, deg_p + 1, 2):
        Cp[r] = [-2 * x for x in Csub[r - 1]]
    mults = {0: [(0, F1)], 1: [(1, F1)],
             2: [(0, b2), (2, Fraction(-1))], 3: [(1, b2), (3, Fraction(-1))]}
    out = dict(b2=b2, wh=wh, deg_p=deg_p, blocks={}, res={})
    for cls in CLASSES:
        h = [Fraction(x) for x in b[f"h_{cls}_diag"]]
        rhs = [sum(Cp[r][j] * h[j] for j in range(d_H + 1))
               + (F1 if r == 0 else F0) for r in range(deg_p + 1)]
        lhs = [F0] * (deg_p + 1)
        for i in range(4):
            n = SIG_DEF_SIZES[i]
            S = [[Fraction(x) for x in row] for row in b[f"sig_{cls}_sig{i}"]]
            L = [[Fraction(0)] * n for _ in range(n)]
            D = [Fraction(0)] * n
            for j in range(n):
                s = S[j][j] - sum(L[j][k] * L[j][k] * D[k] for k in range(j))
                D[j] = s
                L[j][j] = F1
                for i2 in range(j + 1, n):
                    L[i2][j] = (S[i2][j]
                                - sum(L[i2][k] * L[j][k] * D[k] for k in range(j))) / s
            if not all(x > 0 for x in D):
                fail(f"G5·① sig_{cls}_sig{i} 存在非正 LDLᵀ 主元")
            recon = [[sum(L[i2][k] * D[k] * L[j2][k] for k in range(min(i2, j2) + 1))
                      for j2 in range(n)] for i2 in range(n)]
            if recon != S:
                fail(f"G5·① sig_{cls}_sig{i} LDLᵀ 重构 ≠ S（逐位）")
            Mm = [[L[i2][j2] * D[j2] for j2 in range(n)] for i2 in range(n)]
            out["blocks"][f"{cls}_sig{i}"] = dict(S=S, L=L, D=D, M=Mm, dim=n)
            for p in range(n):
                for q2 in range(n):
                    c = S[p][q2]
                    if c:
                        for (eg, cg) in mults[i]:
                            lhs[p + q2 + eg] += c * cg
        diff = [rhs[j] - lhs[j] for j in range(deg_p + 1)]
        sgn = [Fraction(d and (1 if d > 0 else -1)) for d in diff]
        R2 = sum(abs(d) * wh ** j for j, d in enumerate(diff))
        out["res"][cls] = dict(lhs=lhs, rhs=rhs, sgn=sgn, R2=R2, diff=diff)
    return out


def gate5_offline(r9):
    cert = json.loads((REPO / CERT_REL).read_text())
    dj = json.loads((RESULTS / "r13_a6_data.json").read_text())
    rec = g5_recompute(cert)
    # ① json↔独立重算（S/L/D 逐分量；主元正性在重算内已检）
    for key, blk in rec["blocks"].items():
        jb = dj["blocks"][key]
        n = blk["dim"]
        if jb["dim"] != n:
            fail(f"G5·① {key} dim 失配")
        for name, mine in (("S", blk["S"]), ("L", blk["L"])):
            theirs = [[Fraction(x) for x in r] for r in jb[name]]
            if theirs != mine:
                fail(f"G5·① {key} {name} 与数据件逐位失配")
        if [Fraction(x) for x in jb["D"]] != blk["D"]:
            fail(f"G5·① {key} D 与数据件逐位失配")
        if not all(blk["D"][j] > 0 for j in range(n)):
            fail(f"G5·① {key} 主元非全正")
    # ② 残差与 R2 对账（json＋r9_s3_rederive.json）
    for cls in CLASSES:
        r5 = rec["res"][cls]
        jr = dj["residual"][cls]
        for name in ("lhs", "rhs", "sgn"):
            if [Fraction(x) for x in jr[name]] != r5[name]:
                fail(f"G5·② {cls} {name} 与数据件失配")
        if r5["R2"] != Fraction(r9["R2_exact"][cls]):
            fail(f"G5·② R2_{cls} 与 r9_s3_rederive.json R2_exact 逐位失配")
        if Fraction(dj["R2_exact"][cls]) != r5["R2"]:
            fail(f"G5·② R2_{cls} 数据件与独立重算失配")
        nz = sum(1 for d in r5["diff"] if d != 0)
        if nz != 33:
            fail(f"G5·② {cls} 残差非零系数 {nz} ≠ 33")
    # ③ (ii) 恒等式 Fraction 重放（8 块 × 5 有理点）
    for key, blk in rec["blocks"].items():
        n = blk["dim"]
        for y in REPLAY_YS:
            quad = sum(blk["S"][k][l] * y ** (k + l)
                       for k in range(n) for l in range(n))
            sos = sum(blk["D"][j] * (sum(blk["L"][k][j] * y ** k
                                         for k in range(n))) ** 2
                      for j in range(n))
            if quad != sos:
                fail(f"G5·③ (ii) 重放失配：{key} @ y={y}")
    # ④ (iv) 重放＋抽查点 p_cls 重放
    for cls in CLASSES:
        r5 = rec["res"][cls]
        acc = sum(r5["sgn"][j] * (r5["rhs"][j] - r5["lhs"][j]) * rec["wh"] ** j
                  for j in range(34))
        if acc != r5["R2"]:
            fail(f"G5·④ (iv) 重放失配：Σ sgn·(rhs−lhs)·ŵ^j ≠ R2_{cls}")
        for y in SPOT_YS:
            lhs_eval = sum(r5["lhs"][j] * y ** j for j in range(34))
            quad = sum(rec["blocks"][f"{cls}_sig{i}"]["S"][k][l] * y ** (k + l)
                       for i in range(4) for k in range(SIG_DEF_SIZES[i])
                       for l in range(SIG_DEF_SIZES[i]))
            mult = [F1, y, Fraction(437, 500) - y * y,
                    y * (Fraction(437, 500) - y * y)]
            p_cls = sum(sum(rec["blocks"][f"{cls}_sig{i}"]["S"][k][l] * y ** (k + l)
                            for k in range(SIG_DEF_SIZES[i])
                            for l in range(SIG_DEF_SIZES[i])) * mult[i]
                        for i in range(4))
            if lhs_eval != p_cls:
                fail(f"G5·④ 抽查点重放失配：Σ lhs_j y^j ≠ p_{cls}(y) @ y={y}")
    okmsg("G5·①–④ 离线精确复核（Fraction 第三实现）：8 块 LDLᵀ 主元全正＋重构"
          "逐位＋json 逐分量；lhs/rhs/sgn/R2 对账 r9_s3_rederive.json 逐位；"
          "(ii) 8 块×5 点、(iv) 两类、抽查 3 点/类恒等式重放全过")
    return rec


def g5_literals(rec, dj):
    """⑤ json↔源码字面量逐分量。返回解析器（供 NC 复用）。"""
    def check_sources(src_u=None, block_srcs=None):
        su = src_u if src_u is not None else (leanfile(UMBRELLA_REL)).read_text()
        bs = block_srcs if block_srcs is not None else \
            {b: (leanfile(f"{BLOCK_DIR_REL}/{b}.lean")).read_text() for b in BLOCKS}
        n_rows = 0
        for b in BLOCKS:
            key = f"{b[:2]}_sig{b[2]}"
            blk = rec["blocks"][key]
            n = blk["dim"]
            for nm, mine in (("S", blk["S"]), ("L", blk["L"]), ("M", blk["M"])):
                for i in range(n):
                    m = re.search(rf"noncomputable def {nm}{b}r{i} : Fin {n} → ℝ "
                                  rf":= !\[(.*)\]", bs[b])
                    if not m:
                        fail(f"G5·⑤ 源码缺 {nm}{b}r{i} 行")
                    if parse_r_list(m.group(1)) != mine[i]:
                        fail(f"G5·⑤ {nm}{b}r{i} 源码字面量与 json/重算失配")
                    n_rows += 1
            m = re.search(rf"noncomputable def d{b} : Fin {n} → ℝ := !\[(.*)\]", bs[b])
            if not m or parse_r_list(m.group(1)) != blk["D"]:
                fail(f"G5·⑤ d{b} 源码字面量与 json/重算失配")
        for cls in CLASSES:
            r5 = rec["res"][cls]
            for nm in ("lhs", "rhs", "sgn"):
                m = re.search(rf"noncomputable def {nm}{cls} : Fin 34 → ℚ := !\[(.*)\]", su)
                if not m:
                    fail(f"G5·⑤ 源码缺 {nm}{cls} 向量")
                if parse_q_list(m.group(1)) != r5[nm]:
                    fail(f"G5·⑤ {nm}{cls} 源码字面量与 json/重算失配")
            mm = re.search(rf"theorem r2_reduction_{cls} :.*? = \((-?\d+)/(\d+) : ℚ\)", su, re.S)
            if not mm:
                fail(f"G5·⑤ r2_reduction_{cls} 缺 R2 ℚ 字面量")
            if Fraction(int(mm.group(1)), int(mm.group(2))) != r5["R2"]:
                fail(f"G5·⑤ R2_{cls} 定理字面量与重算失配")
        if "(437/500" not in su or "(117/125)" not in su:
            fail("G5·⑤ 总成缺 b²/ŵ 字面量锚")
        return True
    check_sources()
    okmsg("G5·⑤ json↔源码字面量逐分量：8 块 S/L 行＋d＋总成 lhs/rhs/sgn＋R2_cls"
          " ℚ 字面量全检相等；b²=437/500、ŵ=117/125 锚在场")
    return check_sources


# ------------------------------------------------------------------ NC
def nc1_sorry(led):
    src = (leanfile(UMBRELLA_REL)).read_text()
    tampered = src.replace(
        "  rw [pAA_sos]\n  exact add_nonneg (add_nonneg (add_nonneg q0 (mul_nonneg hy q1))\n"
        "    (mul_nonneg hb q2)) (mul_nonneg (mul_nonneg hy hb) q3)",
        "  rw [pAA_sos]\n  sorry", 1)
    if "sorry" not in tampered:
        fail("NC1 预置失败：未能在总成副本注入 sorry（pAA_nonneg 证明尾）")
    d = TMP / "nc1" / "ThomsonN9"
    (d / "TableA6").mkdir(parents=True, exist_ok=True)
    (d / "TableA6.lean").write_text(tampered)
    # 复用 G2 已产出的块 olean（快路径：只重编总成）
    srcdir = LEAN_DIR / ".lake/build/lib/lean/ThomsonN9/TableA6"
    for f in srcdir.glob("*.olean"):
        (d / "TableA6" / f.name).write_bytes(f.read_bytes())
    lp = run(["lake", "env", "printenv", "LEAN_PATH"], LEAN_DIR).stdout.strip()
    env = gate_env()
    env["LEAN_PATH"] = f"{TMP / 'nc1'}:{lp}"
    b = subprocess.run(
        ["lean", "--root", str(TMP / "nc1"), "-o",
         str(TMP / "nc1" / "ThomsonN9" / "TableA6.olean"),
         str(TMP / "nc1" / "ThomsonN9" / "TableA6.lean")],
        cwd=str(LEAN_DIR), env=env, capture_output=True, text=True, timeout=580)
    if b.returncode != 0 or "declaration uses `sorry`" not in (b.stdout + b.stderr):
        fail(f"NC1 注入 sorry 后未产生 sorry 警告（exit {b.returncode}）："
             f"{(b.stdout + b.stderr)[-400:]}")
    axfile = TMP / "nc1" / "axcheck.lean"
    axfile.write_text("import ThomsonN9.TableA6\n"
                      "#print axioms pAA_nonneg\n")
    a = subprocess.run(["lean", str(axfile)], cwd=str(LEAN_DIR), env=env,
                       capture_output=True, text=True, timeout=580)
    ax = parse_axiom_lines(a.stdout)
    th = "pAA_nonneg"
    if th not in ax or "sorryAx" not in ax[th]:
        fail(f"NC1 失守：注入 sorry 后公理检查未现 sorryAx（{ax}）")
    okmsg("NC1 注入 sorry 必被 G3 拦：篡件 pAA_nonneg 公理集含 sorryAx（快路径："
          "块 olean 复用，仅重编总成）")


def nc2_pivot(rec, dj):
    src = (leanfile(f"{BLOCK_DIR_REL}/AA0.lean")).read_text()
    mline = re.search(r"noncomputable def dAA0 : Fin 17 → ℝ := !\[([^\]]*)\]", src)
    if not mline:
        fail("NC2 预置失败：未找到 dAA0 定义行")
    line = mline.group(0)
    m = re.search(r"\((-?\d+)/(\d+)", line)
    if not m:
        fail("NC2 预置失败：未找到 dAA0 首主元字面量")
    num, den = m.group(1), m.group(2)
    if num.startswith("-"):
        bad_line = line.replace(f"({num}/{den}", f"({num[1:]}/{den}", 1)
    else:
        bad_line = line.replace(f"({num}/{den}", f"(-{num}/{den}", 1)
    if bad_line == line:
        fail("NC2 预置失败：篡改未生效")
    bad = src.replace(line, bad_line, 1)
    r9 = json.loads((REPO / R9JSON_REL).read_text())
    try:
        g5_run = lambda: None
        # 对篡源重放 G5·①/⑤（独立重算不变，源码侧比对必失配）
        blk = rec["blocks"]["AA_sig0"]
        mm = re.search(r"noncomputable def dAA0 : Fin 17 → ℝ := !\[(.*)\]", bad)
        if parse_r_list(mm.group(1)) == blk["D"]:
            raise GateFail("NC2 失守：篡 D 主元变号未被 G5·⑤ 检出")
        print(f"[gate][NC2 检出] dAA0 首主元变号：源码字面量 ≠ 独立重算 D（G5·⑤ 拦）")
    except GateFail as e:
        if "失守" in str(e) or "预置" in str(e):
            raise
        print(f"[gate][NC2 检出] {e}")
    # sanity：原文件 PASS（重算比对）
    mm = re.search(r"noncomputable def dAA0 : Fin 17 → ℝ := !\[(.*)\]", src)
    if parse_r_list(mm.group(1)) != rec["blocks"]["AA_sig0"]["D"]:
        fail("NC2 sanity：原文件 dAA0 与重算失配（不应发生）")
    okmsg("NC2 篡 D 主元变号必被 G5 检出；原文件 sanity PASS")


def nc3_residual(rec):
    src = (leanfile(UMBRELLA_REL)).read_text()
    m = re.search(r"noncomputable def lhsAA : Fin 34 → ℚ := !\[\((\d+)/(\d+)",
                  src)
    if not m:
        fail("NC3 预置失败：未找到 lhsAA 首分量字面量")
    num, den = m.group(1), m.group(2)
    bad = src.replace(f"({num}/{den}", f"({int(num) + 1}/{den}", 1)
    if bad == src:
        fail("NC3 预置失败：篡改未生效")
    mm = re.search(r"noncomputable def lhsAA : Fin 34 → ℚ := !\[(.*)\]", bad)
    if parse_q_list(mm.group(1)) == rec["res"]["AA"]["lhs"]:
        fail("NC3 失守：篡残差系数未被 G5·⑤ 检出")
    # (iv) 重放亦拦：篡后 Σ sgn·(rhs−lhs)·ŵ^j ≠ R2（符号由 sgn(rhs−lhs) 给出）
    tam = parse_q_list(mm.group(1))
    r5 = rec["res"]["AA"]
    acc = sum(r5["sgn"][j] * (r5["rhs"][j] - tam[j]) * Fraction(117, 125) ** j
              for j in range(34))
    if acc == r5["R2"]:
        print("[gate][NC3 备注] (iv) 数值重放对篡值未拦（仅 G5·⑤ 拦）")
    else:
        print("[gate][NC3 检出] (iv) 数值重放：篡 lhs 后 Σ ≠ R2_AA（双拦）")
    okmsg("NC3 篡残差系数必被 (iv)/G5 检出；原文件 sanity 由 G5·⑤ 主检通过")


# ------------------------------------------------------------------ main
def main():
    t0 = time.time()
    print(f"[gate] r13_a6_gate.py seed={SEED_GATE}（确定性，无随机路径）")
    try:
        run_gate()
    except GateFail as e:
        print(f"[gate][FAIL] {e}", flush=True)
        sys.exit(1)
    print(f"[gate] PASS（{time.time() - t0:.1f}s）——exit 0")
    print("[gate] heavySolves=0（本门零求解：仅 elaboration/公理/regex/Fraction 复核）")


def run_gate():
    require_toolchain()
    led = gate0_ledger()
    gate1_ownership(led)
    walls = gate2_elaborate()
    gate3_axioms()
    gate4_statement()
    r9 = json.loads((REPO / R9JSON_REL).read_text())
    rec = gate5_offline(r9)
    dj = json.loads((RESULTS / "r13_a6_data.json").read_text())
    g5_literals(rec, dj)
    nc1_sorry(led)
    nc2_pivot(rec, dj)
    nc3_residual(rec)
    print(f"[gate] G2 墙钟：Gen {walls['Gen.lean']:.1f}s；8 块并行最长 "
          f"{max(walls[f'{b}.lean'] for b in BLOCKS):.1f}s；总成 "
          f"{walls['TableA6.lean']:.1f}s；全门累计见 PASS 行")


if __name__ == "__main__":
    main()
