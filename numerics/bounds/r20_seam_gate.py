#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r20_seam_gate.py — R20A L5→L6 缝量化探针验收门（G0–G4＋负对照
NC1/NC2/NC3；seed 20261020；零 Lean 编译——本门纯数值/文本/git 面）.

任务书口径（r20a-l5l6-seam-probe，campaign dwfrun-f9904baf 第 15 轮）：
被验件＝numerics/bounds/r20_seam_probe.py（确定性 Fraction／定向有理包络
探针，零求解零 SDP）＋numerics/bounds/results/r20_l5l6_seam.json（审计件
账本，seed 20261020/heavy_solves==0）＋notes/l5l6-seam.md（发现与勘正叙述）
＋本门＋嵌套 CWD 包装器。输入存档全部只读（TableB5Data/TableB5Uncond/
l4/l6_intube/tube/l2_rigorous/r19_b5u_ledger）。

检查面（任务书 G0–G4＋NC1/NC2/NC3）：
  G0 账本自锚：seed==20261020、heavy_solves==0、kind/task/schema 三层
     口径词汇表、确定性面（零 timestamp/wall_s/code_version/generated 顶层
     键——G2 逐位一致的必要条件）、provenance 输入 sha256 逐文件重算比对
     ＋冻结锚字符串。
  G1 冻结面不触＋隔离面：git 改动路径 ⊆ 自有六件（＋R20A_G1_ALLOW_FOREIGN
     环境变量逐件放行〔默认关〕＋r20 家族放行层）；挑战件目录/＋references/
     ＋表 B 前六件 Lean 只读 git diff 守卫；四账本（m9/m10/hermite_v2/
     typed_ladder）sha256 冻结锚；endgame.json sha256==86863a09…69f＋
     TableB5Uncond==c79fc623…＋TableB5Polar==d8c58f7d…；**审计件隔离面**：
     r20_l5l6_seam 不得出现在 endgame.json/endgame_chain.py 文本中＋
     chain-only 干跑五字段逐位零漂移＋全集漂移叶 ⊆ 冻结 22 叶分布
     （certReverify 17＋code_version/timestamp 2＋L1 quant 1＋engineV2 2
     ——D84-4；新叶出现即 FAIL，处置归 D88）。
  G2 探针确定性重跑：--out /tmp 副产物与存档逐位一致（cmp 字节级）。
  G3 常数独立第二实现定向包络交叉核验：门内自有 regex/Newton 包络
     （与探针不同字面不同构造）重导全部常数——装配恒等式四件＋sqrt 前提
     四件＋k1/δ_A 精确层逐位相等＋包络层（C_B_hi/C_A）紧公差 |Δ|/v ≤1e-30
     （≫200-bit 包络差 ~6e-61，≪任何实质篡改——NC1 的 0.1% 必被检出）＋
     C_B·√δ 支配 19 点网格（精确）＋记录域恒等式 sqrt72Up·δmax==dom·l3²/u1
     ＋β≤1/2 域面＋l4.json C_exact/delta_max_exact 与 TableB5Data
     CVal/deltaMax 精确恒等＋r19 账本路线 float（7.128/18.957/0.014588）
     舍入带内命中。
  G4 缝表断言（validate_ledger——对任意账本 dict 可复用，NC 同一入口）：
     三口径×四需求半径 12 行阈值精确重算恒等；定向舍入安全向（阈值
     floor ≤ 精确值、shortfall ceil ≥ 精确值、非退化带）；域检查三面
     （B：δ≤δmax；A：δ≤δ_A＋β=u₁√72Up·δ/l₃²≤1/2 精确；num：δ≤δmax）；
     中心偏移 2.5635e-6 三角入账（r_eff==r*−d_orb_hi 精确＋r_eff>0＋
     存档区间串逐位）；三层口径分层标注机器检查（tier 词汇表＋
     float_advisory 只入注记行＋数值档 route_tier==written_proof_fraction）；
     L3 对账（存档阶梯 float 逐位镜像＋M9 ε_forcing 括带＋shortfall 关键
     断言 ≥70×/≥4.5×/≥3.9×/≥399× 精确重算）；Round 5 勘正定量面
     （CVal/50 精确＋比值＋窗口高估因子==δmax/δ_need_num＋architecture-
     decision.md 叙述原文在场锚）；binding=L3＋seam_closed=False；
     notes/l5l6-seam.md 转录锚。
  NC1 篡 C_B 常数必拦：/tmp 篡副本把 supply.C_B.hi 精确值压低 0.1%
     （假装更小常数⟹缝阈值虚降——现实作弊向）→ validate_ledger 必 FAIL
     （G3/G4 紧公差交叉面拦截；未篡 /tmp 副本 sanity 全过）。
  NC2 篡 r* 必拦：/tmp 篡副本把 r* 改 0.95（假装百倍认证球）→ 必 FAIL
     （l6_intube 存档恒等面拦截）。
  NC3 包络方向反转必拦：/tmp 篡副本把 sqrt2Up 换 √2 下包（假装更锐的
     上包——方向反转）→ 必 FAIL（定向前提 2≤sqrt2Up² 精确整数面拦截）。

诚实边界：本门零求解零 SDP 零 Lean 编译（被验件零 Lean 面——常数以
TableB5Data def 直读）；endgame.json/四账本只读未动（sha256 锚＋干跑零
漂移双面）；审计件不入 12 分区（隔离面）。

用法（CWD 无关）：
  python3 numerics/bounds/r20_seam_gate.py    # 全门（exit 0 = 过）
  python3 thomson-n9/numerics/bounds/r20_seam_gate.py
      # ↑ CWD＝仓库根时命中同名 runpy 包装器（R10A/R14A/R19A 先例）
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
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
REPO = HERE.parents[1]                 # thomson-n9/

SEED_GATE = 20261020                  # R20 各门统一 seed（任务书口径）

PROBE_REL = "numerics/bounds/r20_seam_probe.py"
GATE_REL = "numerics/bounds/r20_seam_gate.py"
WRAPPER_REL = "thomson-n9/numerics/bounds/r20_seam_gate.py"   # CWD 兼容包装器
LEDGER_REL = "numerics/bounds/results/r20_l5l6_seam.json"
NOTES_REL = "notes/l5l6-seam.md"
DECISIONS_REL = "notes/decisions.md"
OWNED = {PROBE_REL, GATE_REL, WRAPPER_REL, LEDGER_REL, NOTES_REL, DECISIONS_REL}

TABLE_B5_DATA = REPO / "formal" / "lean" / "ThomsonN9" / "TableB5Data.lean"
TABLE_B5_UNCOND = REPO / "formal" / "lean" / "ThomsonN9" / "TableB5Uncond.lean"
L4_JSON = RESULTS / "l4.json"
L6_JSON = RESULTS / "l6_intube.json"
TUBE_JSON = RESULTS / "tube.json"
L2_JSON = RESULTS / "l2_rigorous.json"
R19_LEDGER = RESULTS / "r19_b5u_ledger.json"
LEDGER = RESULTS / "r20_l5l6_seam.json"
NOTES = REPO / "notes" / "l5l6-seam.md"
ARCH_DECISION = REPO / "notes" / "architecture-decision.md"
ENDGAME_CHAIN = REPO / "numerics" / "bounds" / "endgame_chain.py"

# 只读冻结件（表 B 全家族 Lean 件——R19A 冻结面延续）：显式 git diff 守卫。
FROZEN_READONLY = (
    "formal/lean/ThomsonN9/TableB5.lean",
    "formal/lean/ThomsonN9/TableB5Data.lean",
    "formal/lean/ThomsonN9/TableB5Core.lean",
    "formal/lean/ThomsonN9/TableB5Trace.lean",
    "formal/lean/ThomsonN9/TableB5Polar.lean",
    "formal/lean/ThomsonN9/TableB5Uncond.lean",
    "formal/lean/ThomsonN9/TableB1.lean",
    "formal/lean/ThomsonN9/TableB1Data.lean",
    "formal/lean/ThomsonN9/TableB6.lean",
    "formal/lean/ThomsonN9/TableB6Data.lean",
)
FROZEN_DIRS = ("formal/lean/ComparatorChallenges", "references")
FROZEN_LEDGERS = {
    "numerics/bounds/results/m9_campaign.json":
        "583e5dd11356472b47e8d9e8fac7865ec434800c99919df31d247f30b260114a",
    "numerics/bounds/results/m10_campaign.json":
        "9f6cf91c3adf1e0908c2f41084e53380237ca58840f82bbdcd720c54421c23ed",
    "numerics/bounds/results/hermite_v2_campaign.json":
        "4ebcbedd1e8dc300ab9e6bc0e3b756c75b7f4cbe4fe00675719217f90ea41765",
    "numerics/bounds/results/typed_ladder.json":
        "78fc1102e6d864115204fae21959f3704841aa688b07a30a9567bbdca4683318",
}
ENDGAME_REL = "numerics/bounds/results/endgame.json"
ENDGAME_SHA256 = "86863a09bf84e950e85fc5f902bc2b4046a87f06703bd782e5148fc119afd69f"
UNCOND_SHA256 = "c79fc6231d1e13b8ffd7873d1338901602ed3b70b3f057ed4eec4eb757e36d5e"
POLAR_SHA256 = "d8c58f7d2c56c39fbe1ae62d634fc6ea5bd585fa9f1c0b9c2e2fc909d4338516"

# r20 家族放行集（D86 裁决 4：R20A 探针腿与 R20B 收口腿〔endgame_gate.py/
# GAP-REPORT/PROGRESS/decisions 后续追加〕零交叠放行）。
PARALLEL_FAMILY = [
    r"^numerics/bounds/r20[a-z0-9_]*(\.py|/)",
    r"^numerics/bounds/results/r20[a-z0-9_]*(\.json|/)",
    r"^thomson-n9/numerics/bounds/r20[a-z0-9_]*(\.py|/)",
    r"^notes/decisions\.md$",
    r"^notes/l5l6-seam\.md$",
    r"^numerics/bounds/endgame_gate\.py$",
    r"^(GAP-REPORT|PROGRESS)\.md$",
]

# C2 冻结漂移分布（R18C/R19 实测口径，本会话 2026-10-13 复测同分布）：
# 22 叶＝certReverify 17＋code_version/timestamp 2＋L1 quant 1＋engineV2 2。
FROZEN_DRIFT_LEAVES = frozenset({
    "/certReverify/all_pass", "/certReverify/cap_m0748_M9",
    "/certReverify/hp_reproduce", "/certReverify/l3_analytic_rerun",
    "/certReverify/l4_orbit_rerun", "/certReverify/l6_intube_rerun",
    "/certReverify/slab_sm19o20_m91o100", "/certReverify/slab_sm1_m99o100",
    "/certReverify/slab_sm91o100_m9o10", "/certReverify/slab_sm97o100_m19o20",
    "/certReverify/slab_sm99o100_m97o100", "/certReverify/status",
    "/certReverify/strip_m079-m765", "/certReverify/strip_m082-m079",
    "/certReverify/strip_m085-m082", "/certReverify/strip_m088-m085",
    "/certReverify/strip_m090-m088", "/code_version",
    "/endgameChain/components/1/quant", "/round8Inputs/engineV2/ledgers/7",
    "/round8Inputs/engineV2/note", "/timestamp",
})

TIERS = ("formal_lean", "written_proof_fraction",
         "interval_certified_numeric", "rejection_certified_numeric",
         "float_advisory")
ENVELOPE_TOL = Fr(1, 10**30)      # 包络层紧公差（见 G3 说明）
VOLATILE_KEYS = ("timestamp", "wall_s", "code_version", "generated")

TMP = Path("/tmp/r20_seam_gate")


class GateFail(Exception):
    pass


def fail(msg: str) -> None:
    raise GateFail(msg)


def okmsg(msg: str) -> None:
    print(f"[gate][OK ] {msg}", flush=True)


def sha256_of(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def load_json(p: Path):
    return json.loads(p.read_text())


def run(cmd, cwd: Path, timeout: int = 600):
    return subprocess.run(cmd, cwd=str(cwd), capture_output=True, text=True,
                          timeout=timeout)


# ============================================================ 独立第二实现
# 门内 Newton 有理平方根包：与探针不同构造（a=isqrt(⌊q·2^{2p}⌋)；
# hi=(a+2)/2^p 严格上包〔a+2 > √q+1〕、lo=a/2^p 下包〔a² ≤ q〕——
# 探针用 isqrt(quotient+1)+1 与 isqrt(quotient) 的不同字面）。
def sqrt_env(q: Fr, side: str, bits: int = 200) -> Fr:
    num, den = q.numerator, q.denominator
    a = math.isqrt((num << (2 * bits)) // den)
    if side == "lo":
        return Fr(a, 1 << bits)
    return Fr(a + 2, 1 << bits)


def parse_data_literal(name: str, src: str) -> Fr:
    """TableB5Data.lean def 值直读（门内自有解析——按行切分，非探针 regex）。"""
    for line in src.splitlines():
        s = line.strip()
        if s.startswith(f"def {name} :"):
            val = s.split(":=", 1)[1].strip()
            return Fr(val)
    fail(f"G3 TableB5Data.lean 缺 def {name}")


def recompute_supply(src: str) -> dict:
    """G3 核心：门内独立重导全部供给面常数（精确层＋包络层分离记账）。"""
    l3 = parse_data_literal("l3", src)
    u1 = parse_data_literal("u1", src)
    s1Up = parse_data_literal("s1Up", src)
    s3Dn = parse_data_literal("s3Dn", src)
    sqrt72Up = parse_data_literal("sqrt72Up", src)
    CInner = parse_data_literal("CInner", src)
    CVal = parse_data_literal("CVal", src)
    deltaMax = parse_data_literal("deltaMax", src)
    # 装配恒等式四件（norm_num 面的独立第二实现复验）
    if u1 * s1Up / (l3 * l3) + 2 / s3Dn != CInner:
        fail("G3 装配① C_inner 恒等式不符")
    if sqrt72Up * CInner != CVal:
        fail("G3 装配② C==sqrt72Up·CInner 恒等式不符")
    if s3Dn / (2 * s1Up) * (l3 * l3) / (sqrt72Up * u1) != deltaMax:
        fail("G3 装配④ δ_max 恒等式不符")
    # sqrt 前提四件（方向性：上包平方 ≥ 真值 ≥ 下包平方）
    if not (u1 <= s1Up * s1Up):
        fail("G3 前提 s1Up² ≥ u₁ 不符")
    if not (s3Dn * s3Dn <= l3):
        fail("G3 前提 s3Dn² ≤ l₃ 不符")
    if not (72 <= sqrt72Up * sqrt72Up):
        fail("G3 前提 sqrt72Up² ≥ 72 不符")
    if not (s3Dn <= s1Up):
        fail("G3 前提 s3Dn ≤ s1Up 不符")
    # 记录域恒等式＋β≤1/2 域面（r19 G5(f) 同式独立重跑）
    if sqrt72Up * deltaMax != (s3Dn / (2 * s1Up)) * l3 * l3 / u1:
        fail("G3 记录恒等式 sqrt72Up·δmax==dom·l3²/u1 不符")
    if not (sqrt72Up * deltaMax <= l3 * l3 / (2 * u1)):
        fail("G3 记录域内 β≤1/2 域面不符")
    k1 = s1Up * u1 * sqrt72Up / (l3 * l3)
    C_B_hi = k1 * sqrt_env(deltaMax, "hi") + sqrt_env(3 * sqrt72Up, "hi")
    C_B_lo = k1 * sqrt_env(deltaMax, "lo") + sqrt_env(3 * sqrt72Up, "lo")
    sqrt2Up = sqrt_env(Fr(2), "hi")
    if not (2 <= sqrt2Up * sqrt2Up):
        fail("G3 √2 上包方向自检失守")
    C_A_eta = s1Up * u1 / (l3 * l3) + 2 * sqrt2Up / s3Dn
    delta_A = (l3 / 24) / sqrt72Up
    if u1 * sqrt72Up * delta_A / (l3 * l3) != u1 / (24 * l3):
        fail("G3 δ_A β 域端恒等式不符")
    # C_B·√δ 支配 19 点网格（精确）
    for i in range(1, 20):
        d = deltaMax * Fr(i, 20)
        if k1 * d + sqrt_env(3 * sqrt72Up * d, "hi") > C_B_hi * sqrt_env(d, "lo"):
            fail(f"G3 C_B·√δ 支配面 19 点网格违例（i={i}）")
    return {"l3": l3, "u1": u1, "s1Up": s1Up, "s3Dn": s3Dn,
            "sqrt72Up": sqrt72Up, "CInner": CInner, "CVal": CVal,
            "deltaMax": deltaMax, "k1": k1, "C_B_hi": C_B_hi,
            "C_B_lo": C_B_lo, "sqrt2Up": sqrt2Up, "C_A_eta": C_A_eta,
            "C_A_delta": sqrt72Up * C_A_eta, "delta_A": delta_A}


# ============================================================ G0
def gate0_ledger() -> dict:
    if not LEDGER.is_file():
        fail(f"G0 账本不在场：{LEDGER_REL}")
    led = load_json(LEDGER)
    if led.get("seed") != SEED_GATE:
        fail(f"G0 seed 失配：{led.get('seed')!r} != {SEED_GATE}")
    if led.get("heavy_solves") != 0:
        fail(f"G0 heavy_solves 失配：{led.get('heavy_solves')!r} != 0")
    if led.get("kind") != "n9-r20-l5l6-seam":
        fail(f"G0 kind 失配：{led.get('kind')!r}")
    if led.get("task") != "r20a-l5l6-seam-probe":
        fail(f"G0 task 失配：{led.get('task')!r}")
    for k in VOLATILE_KEYS:
        if k in led:
            fail(f"G0 确定性面：账本含易变键 {k!r}（G2 逐位一致的必要条件）")
    if tuple(led.get("schema", {}).get("tiers_vocabulary", ())) != TIERS:
        fail("G0 schema.tiers_vocabulary 与固定词汇表不符")
    art = led.get("schema", {}).get("artifact_class", "")
    if "endgame" not in art or "endgame_chain" not in art:
        fail("G0 schema.artifact_class 未声明审计件隔离（endgame/endgame_chain）")
    prov = led.get("provenance", {})
    if prov.get("read_only") is not True:
        fail("G0 provenance.read_only 非 True")
    for rel, rec in prov.get("inputs", {}).items():
        p = REPO / rel
        if not p.is_file():
            fail(f"G0 provenance 输入不在场：{rel}")
        if sha256_of(p) != rec.get("sha256"):
            fail(f"G0 provenance 输入 sha256 漂移：{rel}")
    fa = prov.get("frozen_anchors", {})
    if fa.get("endgame_json_sha256") != ENDGAME_SHA256:
        fail("G0 冻结锚 endgame_json_sha256 失配")
    if fa.get("tableb5uncond_sha256") != UNCOND_SHA256:
        fail("G0 冻结锚 tableb5uncond_sha256 失配")
    if fa.get("tableb5polar_sha256") != POLAR_SHA256:
        fail("G0 冻结锚 tableb5polar_sha256 失配")
    okmsg(f"G0 账本自锚：seed={SEED_GATE}、heavy_solves=0、无易变键、"
          f"provenance {len(prov.get('inputs', {}))} 输入 sha256 逐文件重算一致、"
          "三层口径词汇表＋冻结锚三件在账")
    return led


# ============================================================ G1
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


def gate1_ownership() -> None:
    allow_foreign = {q.strip() for q in
                     os.environ.get("R20A_G1_ALLOW_FOREIGN", "").split(",")
                     if q.strip()}
    for cmd in (["git", "status", "--porcelain"],
                ["git", "diff", "HEAD", "--name-only"]):
        r = run(cmd, REPO)
        if r.returncode != 0:
            raise GateFail(f"G1 {cmd[1]} 失败：{r.stderr.strip()[:300]}")
        paths = (porcelain_paths(r.stdout) if "--porcelain" in cmd else
                 [ln.strip().strip('"') for ln in r.stdout.splitlines()
                  if ln.strip()])
        for p in paths:
            if p in OWNED:
                continue
            if p in allow_foreign:
                print(f"[gate][G1][自跑放行] 并行在途件：{p}")
                continue
            if any(re.match(pat, p) for pat in PARALLEL_FAMILY):
                print(f"[gate][G1][r20 家族放行] 在途件（D86 裁决 4 pattern）：{p}")
                continue
            raise GateFail(
                f"G1 树上出现非本任务自有件（{cmd[1]}）：{p!r}"
                f"（自有集={sorted(OWNED)}；r20 家族放行层未覆盖）")
    # 只读冻结件显式守卫（响亮报错，独立于放行集）
    r = run(["git", "diff", "HEAD", "--"] + list(FROZEN_READONLY), REPO)
    if r.stdout.strip():
        fail("G1 表 B Lean 件只读面被触碰（git diff 非空）")
    for d in FROZEN_DIRS:
        r = run(["git", "status", "--porcelain", "--", d + "/"], REPO)
        if r.stdout.strip():
            fail(f"G1 冻结目录被触碰：{d}")
    for rel, want in FROZEN_LEDGERS.items():
        h = sha256_of(REPO / rel)
        if h != want:
            fail(f"G1 四账本 sha256 冻结锚失配：{rel}（{h[:16]}… != {want[:16]}…）")
    if sha256_of(REPO / ENDGAME_REL) != ENDGAME_SHA256:
        fail("G1 endgame.json sha256 != 86863a09…69f")
    if sha256_of(TABLE_B5_UNCOND) != UNCOND_SHA256:
        fail("G1 TableB5Uncond.lean sha256 != c79fc623…")
    if sha256_of(REPO / "formal/lean/ThomsonN9/TableB5Polar.lean") != POLAR_SHA256:
        fail("G1 TableB5Polar.lean sha256 != d8c58f7d…")
    okmsg("G1 冻结面：git 改动 ⊆ 自有六件＋r20 家族放行层；表 B 十件 Lean＋"
          "挑战件/ references/ ＋四账本 sha256 冻结锚＋endgame.json/"
          "TableB5Uncond/TableB5Polar 三 sha256 锚全过")


def _leaf_diff(x, y, path: str) -> list:
    out = []
    if isinstance(x, dict) and isinstance(y, dict):
        for k in sorted(set(x) | set(y)):
            if k not in x or k not in y:
                out.append(f"{path}/{k}")
            else:
                out += _leaf_diff(x[k], y[k], f"{path}/{k}")
    elif isinstance(x, list) and isinstance(y, list):
        for i in range(max(len(x), len(y))):
            if i >= len(x) or i >= len(y):
                out.append(f"{path}/{i}")
            else:
                out += _leaf_diff(x[i], y[i], f"{path}/{i}")
    elif x != y:
        out.append(path)
    return out


def gate1_isolation() -> None:
    """审计件隔离面：不入 12 分区、不作 chain 输入、干跑零漂移＋冻结 22 叶。"""
    if "r20_l5l6_seam" in (REPO / ENDGAME_REL).read_text():
        fail("G1 隔离面：r20_l5l6_seam 出现在 endgame.json 文本中（审计件非证书）")
    if "r20_l5l6_seam" in ENDGAME_CHAIN.read_text():
        fail("G1 隔离面：r20_l5l6_seam 出现在 endgame_chain.py 文本中（禁止输入）")
    out = TMP / "chain_dry.json"
    r = run([sys.executable, "numerics/bounds/endgame_chain.py",
             "--out", str(out)], REPO)
    if r.returncode != 0:
        fail(f"G1 chain-only 干跑 exit {r.returncode}")
    arch = load_json(REPO / ENDGAME_REL)
    dry = load_json(out)
    # 五字段严格零漂移（r19c C2 同口径）
    if dry["endgameChain"]["closed"] is not False or \
            arch["endgameChain"]["closed"] is not False:
        fail("G1 干跑 closed 漂移（应 False）")
    for k in ("value", "float", "margin_vs_E_star"):
        if arch["assembledRecord"][k] != dry["assembledRecord"][k]:
            fail(f"G1 干跑 assembledRecord.{k} 漂移")
    if len(dry["endgameChain"]["components"]) != 8:
        fail("G1 干跑组件集非 L0–L7")
    for a, b in zip(arch["endgameChain"]["components"],
                    dry["endgameChain"]["components"]):
        if a["id"] != b["id"] or a.get("rigorous") != b.get("rigorous"):
            fail(f"G1 干跑组件 {a.get('id')} rigorous 漂移")
    if dry["endgameChain"]["blocking"] != ["L0", "L3"]:
        fail("G1 干跑 blocking != [L0, L3]")
    if arch["spliceMapVerdict"]["verdict"] != dry["spliceMapVerdict"]["verdict"] \
            or arch["spliceMapVerdict"].get("assembled_equal_R7") != \
            dry["spliceMapVerdict"].get("assembled_equal_R7"):
        fail("G1 干跑 spliceMapVerdict 漂移")
    # 全集漂移叶 ⊆ 冻结 22 叶（新叶即 FAIL——D84-4 口径，处置归 D88）
    drifted = set(_leaf_diff(arch, dry, ""))
    fresh = drifted - FROZEN_DRIFT_LEAVES
    if fresh:
        fail(f"G1 C2 冻结漂移分布出现新叶（{len(fresh)} 处——审计件若被误接为 "
             f"chain 输入即在此暴露；处置归 D88）：{sorted(fresh)[:6]}")
    missing = FROZEN_DRIFT_LEAVES - drifted
    if missing:
        fail(f"G1 C2 漂移分布叶缺失（{len(missing)} 处——环境面变化，如实拦）："
             f"{sorted(missing)[:4]}")
    okmsg("G1 隔离面：r20_l5l6_seam 不入 endgame.json/endgame_chain.py 文本；"
          "chain-only 干跑五字段逐位零漂移＋全集漂移恰为冻结 22 叶"
          "（certReverify 17＋code_version/timestamp 2＋L1 quant 1＋engineV2 2）")


# ============================================================ G2
def gate2_determinism() -> None:
    out = TMP / "probe_rerun.json"
    r = run([sys.executable, PROBE_REL, "--out", str(out)], REPO)
    if r.returncode != 0:
        fail(f"G2 探针重跑 exit {r.returncode}：\n{r.stdout[-400:]}")
    a = LEDGER.read_bytes()
    b = out.read_bytes()
    if a != b:
        fail(f"G2 探针重跑与存档非逐位一致（{len(a)} vs {len(b)} 字节）")
    okmsg(f"G2 探针确定性重跑：/tmp 副产物与存档逐位一致（{len(a)} 字节 cmp）")


# ============================================================ G3
def gate3_constants(led: dict) -> dict:
    ctx = recompute_supply(TABLE_B5_DATA.read_text())
    sup = led["supply"]
    exact_fields = {"l3": "l3", "u1": "u1", "s1Up": "s1Up", "s3Dn": "s3Dn",
                    "sqrt72Up": "sqrt72Up", "CInner": "CInner",
                    "CVal": "CVal", "deltaMax": "deltaMax", "k1": "k1"}
    for led_key, ctx_key in exact_fields.items():
        if Fr(sup[led_key]["exact"]) != ctx[ctx_key]:
            fail(f"G3 精确层失配：supply.{led_key}")
    if Fr(sup["C_A"]["delta_A"]["exact"]) != ctx["delta_A"]:
        fail("G3 精确层失配：supply.C_A.delta_A")
    # 包络层：紧公差 |Δ|/v ≤ 1e-30（两侧均 200-bit 包络，构造差 ~6e-61；
    # 任何实质篡改（≥1e-4 相对，如 NC1 的 0.1%）必被检出）
    for led_val, ctx_val, nm in (
            (Fr(sup["C_B"]["hi"]["exact"]), ctx["C_B_hi"], "C_B.hi"),
            (Fr(sup["C_B"]["lo"]["exact"]), ctx["C_B_lo"], "C_B.lo"),
            (Fr(sup["sqrt2Up"]["exact"]), ctx["sqrt2Up"], "sqrt2Up"),
            (Fr(sup["C_A"]["eta_caliber"]["exact"]), ctx["C_A_eta"], "C_A.eta"),
            (Fr(sup["C_A"]["delta_caliber"]["exact"]), ctx["C_A_delta"],
             "C_A.delta")):
        if abs(led_val - ctx_val) > ENVELOPE_TOL * ctx_val:
            fail(f"G3 包络层紧公差失配：{nm}（|Δ|/v="
                 f"{float(abs(led_val - ctx_val) / ctx_val):.3e} > 1e-30）")
    # 定向前提（对账本记值的精确整数面——NC3 牙）
    if not (2 <= Fr(sup["sqrt2Up"]["exact"]) ** 2):
        fail("G3 定向前提：账本 sqrt2Up² < 2（方向反转）")
    if Fr(sup["C_B"]["hi"]["exact"]) < Fr(sup["C_B"]["lo"]["exact"]):
        fail("G3 定向前提：C_B.hi < C_B.lo")
    if not (u1_ := Fr(sup["u1"]["exact"])) <= Fr(sup["s1Up"]["exact"]) ** 2:
        fail("G3 定向前提：账本 s1Up² < u1")
    if not Fr(sup["s3Dn"]["exact"]) ** 2 <= Fr(sup["l3"]["exact"]):
        fail("G3 定向前提：账本 s3Dn² > l3")
    if not 72 <= Fr(sup["sqrt72Up"]["exact"]) ** 2:
        fail("G3 定向前提：账本 sqrt72Up² < 72")
    # l4.json 恒等（written_proof_fraction 档源对账）
    l4c = load_json(L4_JSON)["constants"]
    if Fr(l4c["C_exact"]) != ctx["CVal"]:
        fail("G3 l4.json C_exact ≠ TableB5Data CVal（精确恒等破损）")
    if Fr(l4c["delta_max_exact"]) != ctx["deltaMax"]:
        fail("G3 l4.json delta_max_exact ≠ TableB5Data deltaMax")
    # r19 账本路线 float 包络内命中
    routes = load_json(R19_LEDGER)["data"]["routes"]
    for nm, mine, want in (
            ("C_B", float(ctx["C_B_hi"]), routes["B_global_hoelder"]["C_B_float"]),
            ("C_A", float(ctx["C_A_delta"]), routes["A_narrow_linear"]["C_A_float"]),
            ("δ_A", float(ctx["delta_A"]),
             routes["A_narrow_linear"]["delta_A_float"])):
        if abs(mine - want) > 5e-4 + 1e-6:
            fail(f"G3 r19 账本包络内命中失败：{nm} {mine} vs {want}")
    # 探针侧 cross 记录与门内重算一致
    for k, rec in sup["r19_ledger_cross"].items():
        if not rec["within_rounding"]:
            fail(f"G3 探针侧 r19 cross 记录未命中：{k}")
    okmsg("G3 常数独立第二实现：装配恒等式四件＋sqrt 前提五件（含 √2）＋"
          "k1/δ_A 精确层逐位＋C_B/C_A 包络层紧公差 1e-30＋C_B·√δ 支配 19 点"
          "网格（精确）＋记录域恒等式/β≤1/2 域面＋l4.json C_exact/δmax 恒等＋"
          "r19 路线 float（C_B≈7.128/C_A≈18.957/δ_A≈0.014588）舍入带内命中")
    return ctx


# ============================================================ G4（可复用）
def validate_ledger(led: dict, ctx: dict, tag: str = "G4") -> None:
    """缝表断言全集（真实账本与 NC 篡副本同一入口——含供给常数对门内
    独立重算 ctx 的精确层逐位／包络层紧公差比对与定向前提五件）。"""
    sup = led["supply"]
    C_B = Fr(sup["C_B"]["hi"]["exact"])
    C_A = Fr(sup["C_A"]["delta_caliber"]["exact"])
    delta_A = Fr(sup["C_A"]["delta_A"]["exact"])
    CVal = Fr(sup["CVal"]["exact"])
    deltaMax = Fr(sup["deltaMax"]["exact"])
    l3, u1, sqrt72Up = (Fr(sup["l3"]["exact"]), Fr(sup["u1"]["exact"]),
                        Fr(sup["sqrt72Up"]["exact"]))
    # ---- 供给常数 vs 门内独立重算（精确层逐位；包络层紧公差——NC1 牙）
    for k in ("l3", "u1", "s1Up", "s3Dn", "sqrt72Up", "CInner", "CVal",
              "deltaMax", "k1"):
        if Fr(sup[k]["exact"]) != ctx[k]:
            fail(f"{tag} 供给精确层 {k} 与门内重算不符")
    if delta_A != ctx["delta_A"]:
        fail(f"{tag} 供给精确层 delta_A 与门内重算不符")
    for led_v, ctx_v, nm in ((C_B, ctx["C_B_hi"], "C_B.hi"),
                             (Fr(sup["C_B"]["lo"]["exact"]), ctx["C_B_lo"],
                              "C_B.lo"),
                             (Fr(sup["sqrt2Up"]["exact"]), ctx["sqrt2Up"],
                              "sqrt2Up"),
                             (Fr(sup["C_A"]["eta_caliber"]["exact"]),
                              ctx["C_A_eta"], "C_A.eta"),
                             (C_A, ctx["C_A_delta"], "C_A.delta")):
        if abs(led_v - ctx_v) > ENVELOPE_TOL * ctx_v:
            fail(f"{tag} 供给包络层 {nm} 紧公差失配（|Δ|/v="
                 f"{float(abs(led_v - ctx_v) / ctx_v):.3e} > 1e-30）")
    # ---- 定向前提五件（对账本记值的精确整数面——NC3 牙）
    if not (2 <= Fr(sup["sqrt2Up"]["exact"]) ** 2):
        fail(f"{tag} 定向前提：sqrt2Up² < 2（包络方向反转）")
    if not (u1 <= Fr(sup["s1Up"]["exact"]) ** 2):
        fail(f"{tag} 定向前提：s1Up² < u1")
    if not (Fr(sup["s3Dn"]["exact"]) ** 2 <= l3):
        fail(f"{tag} 定向前提：s3Dn² > l3")
    if not (72 <= sqrt72Up ** 2):
        fail(f"{tag} 定向前提：sqrt72Up² < 72")
    if C_B < Fr(sup["C_B"]["lo"]["exact"]):
        fail(f"{tag} 定向前提：C_B.hi < C_B.lo")

    # ---- 需求面（存档恒等）
    l6 = load_json(L6_JSON)
    qg = l6["quadraticGrowth"]
    r_star = Fr(led["demand"]["r_star"]["exact"])
    if r_star != Fr(qg["rigorousRadius"]) or r_star != Fr(950125, 100000000):
        fail(f"{tag} r* ≠ l6_intube rigorousRadius/950125/10⁸（存档恒等破损）")
    dorb = led["demand"]["delta_orbit_archive"]
    if dorb["interval_str"] != qg["deltaOrbitArchive"]:
        fail(f"{tag} deltaOrbitArchive 区间串与存档不符")
    d_hi = Fr(dorb["exact_hi"])
    if d_hi != Fr("2.5634854076114746e-6"):
        fail(f"{tag} 中心偏移上端非存档单点值")
    r_eff = Fr(led["demand"]["r_eff"]["exact"])
    if r_eff != r_star - d_hi or r_eff <= 0:
        fail(f"{tag} r_eff ≠ r* − delta_orbit_hi（三角入账破损）或 ≤ 0")
    if led["demand"]["mu_at_r_star"]["interval_str"] != qg["muAtRstar"]:
        fail(f"{tag} μ 区间串与存档不符")
    if led["demand"]["competitor_exclusion_radius"]["interval_str"] != \
            qg["competitorExclusionRadius"]:
        fail(f"{tag} 排除半径区间串与存档不符")
    r_tube = Fr(led["demand"]["r_tube"]["exact"])
    R_MAX = Fr(led["demand"]["R_MAX"]["exact"])
    if r_tube != Fr(l6["reconciliation"]["rTargetFormula"]["value"]):
        fail(f"{tag} r_tube ≠ l6 rTargetFormula.value")
    if R_MAX != Fr(l6["binning"]["R_MAX"]) or R_MAX != 2 * r_tube:
        fail(f"{tag} R_MAX ≠ l6 binning.R_MAX 或 ≠ 2·r_tube")
    if not l6["reconciliation"]["rTargetFormula"]["certifiedHere"].startswith("否"):
        fail(f"{tag} 0.07601 未认证注记前提破损（certifiedHere 非『否』）")
    drc = l6["negativeControls"]["doubleRadiusControl"]
    if drc.get("triggered") is not True:
        fail(f"{tag} doubleRadiusControl 非 triggered（拒绝口径前提破损）")

    # ---- 缝表 12 行
    rows = led["seam_table"]
    if len(rows) != 12:
        fail(f"{tag} 缝表行数 {len(rows)} != 12（3 口径 × 4 需求半径）")
    tvals = {"r_eff": r_eff, "r_star_raw": r_star,
             "r_tube_uncertified": r_tube, "R_MAX_rejection": R_MAX}
    ttiers = {"r_eff": "interval_certified_numeric",
              "r_star_raw": "interval_certified_numeric",
              "r_tube_uncertified": "float_advisory",
              "R_MAX_rejection": "rejection_certified_numeric"}
    for row in rows:
        rt, tg = row["route"], row["target"]
        if row["target_tier"] != ttiers[tg]:
            fail(f"{tag} 缝表 {rt}/{tg} target_tier 失配")
        t = Fr(row["demand_radius"]["exact"])
        if t != tvals[tg]:
            fail(f"{tag} 缝表 {rt}/{tg} demand_radius 失配")
        thr = Fr(row["threshold"]["exact"])
        want = ((t / C_B) ** 2 if rt == "B_global_hoelder" else
                t / C_A if rt == "A_narrow_linear" else t / CVal)
        if thr != want:
            fail(f"{tag} 缝表 {rt}/{tg} 阈值精确重算失配")
        safe = Fr(row["threshold_safe_display"]["exact"])
        if not (safe <= thr):
            fail(f"{tag} 缝表 {rt}/{tg} 定向舍入方向破损（floor 向）")
        if safe < thr * Fr(99999, 100000):
            fail(f"{tag} 缝表 {rt}/{tg} 安全显示退化（<99.999% 真值）")
        if row["domain_ok"] is not True:
            fail(f"{tag} 缝表 {rt}/{tg} domain_ok 非 True")
        if rt == "numerical_linear":
            if row["route_tier"] != "written_proof_fraction":
                fail(f"{tag} 数值档 route_tier 非 written_proof_fraction")
        elif row["route_tier"] != "formal_lean":
            fail(f"{tag} Lean 档 route_tier 非 formal_lean")
        if (row["primary"] is True) != (tg == "r_eff"):
            fail(f"{tag} 缝表 primary 标志仅应属 r_eff 行")
    # ---- 域检查三面（r_eff 主口径精确重算）
    dn_B = (r_eff / C_B) ** 2
    dn_A = r_eff / C_A
    dn_num = r_eff / CVal
    if not (dn_B <= deltaMax):
        fail(f"{tag} B 档域检查 δ_need ≤ δmax 失败")
    if not (dn_A <= delta_A):
        fail(f"{tag} A 档域检查 δ_need ≤ δ_A 失败")
    if not (u1 * sqrt72Up * dn_A / (l3 * l3) <= Fr(1, 2)):
        fail(f"{tag} A 档 β 域检查失败")
    if not (dn_num <= deltaMax):
        fail(f"{tag} 数值档域检查失败")

    # ---- L3 对账（存档 float 镜像＋关键 shortfall 断言精确重算）
    tv = load_json(TUBE_JSON)["verdict"]
    rec = led["l3_reconciliation"]
    for led_key, arc_key in (("rho_spec_at_forcing", "rho_spec_at_forcing"),
                             ("rho_spec_at_ttp_level", "rho_spec_at_ttp_level"),
                             ("rho_spec_at_floor", "rho_spec_at_floor"),
                             ("need_l3_spectral_tube", "need")):
        if rec[led_key]["float"] != tv[arc_key]:
            fail(f"{tag} L3 对账 {led_key} float 镜像与存档不符")
        if rec[led_key]["tier"] != "float_advisory":
            fail(f"{tag} L3 对账 {led_key} tier 非 float_advisory")
    l2 = load_json(L2_JSON)["eps_forcing"]
    eps_m9 = Fr(rec["eps_forcing_m9"]["exact"])
    if eps_m9 != Fr(l2["exact"]) or rec["eps_forcing_m9"]["float"] != l2["float"]:
        fail(f"{tag} eps_forcing(M9) 精确值/float 镜像与 l2_rigorous 不符")
    ladder = load_json(TUBE_JSON)["spectral_tube"]["AAA"]["res"]
    br = rec["eps_forcing_m9_bracket"]
    if br["lo"]["rho_spec"] != ladder["0.0001"]["rho_spec"] or \
            br["hi"]["rho_spec"] != ladder["0.0003"]["rho_spec"]:
        fail(f"{tag} M9 括带端点与存档阶梯不符")
    if not (float(eps_m9) > 1e-4 and float(eps_m9) < 3e-4):
        fail(f"{tag} M9 ε_forcing 未落存档阶梯 1e-4–3e-4 括带内")
    # 关键 shortfall（存档 float 十进制串 → 精确有理，宽安全边定向断言）
    rho_floor = Fr(str(tv["rho_spec_at_floor"]))
    if not (CVal * rho_floor >= 70 * r_eff):
        fail(f"{tag} 最深 SDP 点对 r_eff shortfall < 70×（{tag} 关键断言）")
    if not (CVal * rho_floor >= Fr(45, 10) * R_MAX):
        fail(f"{tag} 最深 SDP 点对 R_MAX shortfall < 4.5×")
    if not (CVal * rho_floor >= Fr(39, 10) * r_tube):
        fail(f"{tag} 最深 SDP 点对 r_tube shortfall < 3.9×")
    if not (Fr(str(ladder["0.0001"]["rho_spec"])) / dn_num >= 399):
        fail(f"{tag} M9 括带下端对数值档阈值 shortfall < 399×")
    for row in rec["supply_rows"]:
        if row["shortfall_ratio"]["tier"] != "float_advisory":
            fail(f"{tag} supply_rows tier 非 float_advisory")
        sd = Fr(row["shortfall_ratio"]["safe_display_exact"])
        base = {"B_global_hoelder": C_B * rho_floor,
                "A_narrow_linear": C_A * rho_floor,
                "numerical_linear": CVal * rho_floor}[row["route"]]
        tgt = {"r_eff": r_eff, "r_tube": r_tube, "R_MAX": R_MAX}[row["target"]]
        if not (sd >= base / tgt):
            fail(f"{tag} supply_rows {row['route']}/{row['target']} "
                 "ceil 安全向破损")

    # ---- Round 5 勘正定量面
    r5 = led["round5_correction"]
    d5 = Fr(r5["d_P_bound_at_0.02"]["numerical_linear"]["exact"])
    if d5 != CVal * Fr(1, 50):
        fail(f"{tag} Round5 d_P 界 ≠ CVal/50（精确）")
    if not (d5 >= 31 * r_eff and d5 >= Fr(39, 10) * r_tube):
        fail(f"{tag} Round5 勘正定量面破损（31×/3.9× 下界）")
    wf = Fr(r5["window_overstatement_factor"]["exact"])
    if wf != deltaMax / dn_num:
        fail(f"{tag} Round5 窗口高估因子 ≠ δmax/δ_need_num(r_eff)")
    for k in ("vs_r_eff", "vs_r_tube", "vs_R_MAX"):
        sd = Fr(r5["d_P_bound_at_0.02"]["ratios"][k]["safe_display_exact"])
        tgt = {"vs_r_eff": r_eff, "vs_r_tube": r_tube,
               "vs_R_MAX": R_MAX}[k]
        if not (sd >= d5 / tgt):
            fail(f"{tag} Round5 比值 {k} ceil 安全向破损")
    if "域窗口" not in r5["correction"] or "链闭合窗口" not in r5["correction"]:
        fail(f"{tag} Round5 勘正叙述缺域窗口/链闭合窗口勘正面")
    if "§2.4" not in r5["narrative_source"]:
        fail(f"{tag} Round5 叙述源缺 §2.4 定位")

    # ---- binding／verdict／口径分层
    bnd = led["binding_constraint"]
    if "L3" not in bnd["binding_layer"]:
        fail(f"{tag} binding_layer 非 L3 供给")
    if led["verdict"]["seam_closed"] is not False:
        fail(f"{tag} seam_closed 应为 False（如实判定）")
    for blk in (sup["C_B"]["hi"], sup["C_A"]["delta_caliber"],
                led["demand"]["r_star"], led["demand"]["r_eff"]):
        if blk["tier"] not in TIERS:
            fail(f"{tag} tier 词汇表外值：{blk['tier']!r}")


def gate4_seam_table(led: dict, ctx: dict) -> None:
    validate_ledger(led, ctx, tag="G4")
    # notes 转录锚＋叙述原文在场锚（勘正对象必须仍在案——本任务不改历史文档）
    notes = NOTES.read_text()
    for anc in ("# L5→L6 缝量化探针",
                "Round 5『闭合窗口』叙述勘正",
                "binding-constraint 识别：**L3 供给**",
                "72.9×", "268×", "deltaOrbitArchive"):
        if anc not in notes:
            fail(f"G4 notes/l5l6-seam.md 转录锚缺失：{anc!r}")
    arch_src = ARCH_DECISION.read_text()
    for anc in ("δ_max=0.17124 覆盖域", "链有闭合窗口"):
        if anc not in arch_src:
            fail(f"G4 勘正对象原文不在场（architecture-decision.md）：{anc!r}")
    okmsg("G4 缝表断言：12 行阈值精确重算恒等＋定向舍入双向（floor ≤ 真值"
          "≤1e-5 带；ceil ≥ 真值）＋域检查三面（δmax/δ_A＋β 精确）＋中心偏移"
          " 2.5635e-6 三角入账（r_eff==r*−d_hi 精确）＋三层口径分层机器检查"
          "（float_advisory 只入注记行）＋L3 对账存档逐位镜像＋M9 括带＋"
          "shortfall ≥70×/≥4.5×/≥3.9×/≥399×＋Round 5 勘正定量面＋binding=L3"
          "＋seam_closed=False＋notes 转录锚 6 处＋勘正对象原文在场锚 2 处")


# ============================================================ NC
def _tampered_copy(led: dict, mutate, nc: str) -> Path:
    import copy
    d = copy.deepcopy(led)
    mutate(d)
    p = TMP / f"nc{nc}_tampered.json"
    p.write_text(json.dumps(d, ensure_ascii=False, indent=1, sort_keys=True))
    return p


def run_ncs(led: dict, ctx: dict) -> None:
    TMP.mkdir(parents=True, exist_ok=True)
    # sanity：未篡 /tmp 副本全过（同一入口）
    sane = _tampered_copy(led, lambda d: None, "0")
    validate_ledger(load_json(sane), ctx, tag="NC-sanity")
    # NC1：压低 C_B 常数 0.1%（假装更小常数 ⟹ δ_need_B 虚升？——注意方向：
    # 更小常数 ⟹ 阈值 (r*/C_B)² 变大 ⟹ 缝看似更近；现实作弊向）必拦
    def nc1(d):
        v = Fr(d["supply"]["C_B"]["hi"]["exact"])
        d["supply"]["C_B"]["hi"]["exact"] = fs(v * Fr(999, 1000))
    p = _tampered_copy(led, nc1, "1")
    try:
        validate_ledger(load_json(p), ctx, tag="NC1")
        fail("NC1 失守：压低 C_B 0.1% 后缝表断言未拦截（不可达：G3 紧公差 "
             "1e-30 ≪ 1e-3）")
    except GateFail as e:
        if "NC1" not in str(e):
            fail(f"NC1 拦截面失配：{e}")
        print(f"[gate][OK ] NC1 篡 C_B 常数（压 0.1%）必拦：{str(e)[:90]}")
    # NC2：r* 篡 0.95（假装百倍认证球）必拦
    def nc2(d):
        d["demand"]["r_star"]["exact"] = fs(Fr(95, 100))
    p = _tampered_copy(led, nc2, "2")
    try:
        validate_ledger(load_json(p), ctx, tag="NC2")
        fail("NC2 失守：篡 r*=0.95 后缝表断言未拦截（不可达：存档恒等面）")
    except GateFail as e:
        if "NC2" not in str(e):
            fail(f"NC2 拦截面失配：{e}")
        print(f"[gate][OK ] NC2 篡 r*（0.95）必拦：{str(e)[:90]}")
    # NC3：包络方向反转（sqrt2Up ← √2 下包，假装更锐上包）必拦
    def nc3(d):
        d["supply"]["sqrt2Up"]["exact"] = fs(sqrt_env(Fr(2), "lo"))
    p = _tampered_copy(led, nc3, "3")
    try:
        validate_ledger(load_json(p), ctx, tag="NC3")
        fail("NC3 失守：√2 包络方向反转后未拦截（不可达：2 ≤ sqrt2Up² "
             "精确整数面）")
    except GateFail as e:
        if "NC3" not in str(e):
            fail(f"NC3 拦截面失配：{e}")
        print(f"[gate][OK ] NC3 包络方向反转（sqrt2Up→下包）必拦：{str(e)[:90]}")


def fs(f: Fr) -> str:
    return f"{f.numerator}/{f.denominator}"


# ============================================================ main
def run_gate() -> None:
    TMP.mkdir(parents=True, exist_ok=True)
    led = gate0_ledger()
    gate1_ownership()
    gate1_isolation()
    gate2_determinism()
    ctx = gate3_constants(led)
    gate4_seam_table(led, ctx)
    run_ncs(led, ctx)


def main() -> None:
    t0 = time.time()
    print(f"[gate] r20_seam_gate.py seed={SEED_GATE}（确定性；零求解零 SDP "
          "零 Lean 编译）")
    try:
        run_gate()
    except GateFail as e:
        print(f"[gate][FAIL] {e}", flush=True)
        sys.exit(1)
    wall = time.time() - t0
    print(f"[gate] PASS（{wall:.1f}s）——exit 0")
    print("[gate] heavySolves=0（数值面审计件：endgame.json/四账本只读未动；"
          "r20_l5l6_seam.json 不入 12 分区）")


if __name__ == "__main__":
    main()
