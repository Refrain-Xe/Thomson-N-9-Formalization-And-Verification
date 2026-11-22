#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r21_chain_gate.py — R21A 链装配数值实例化探针验收门（G0–G4＋负对照
NC1/NC2/NC3；seed 20261021；零 Lean 编译——本门纯数值/文本/git 面；
CWD 无关）.

任务书口径（r21a-chain-assembly-probe，campaign dwfrun-f9904baf 第 16 轮，
D90 裁决 1/4）：被验件＝numerics/bounds/r21_chain_assembly_probe.py（确定
性 Fraction／定向有理包络探针，零求解零 SDP）＋numerics/bounds/results/
r21_chain_assembly.json（审计件账本，kind=n9-r21-chain-assembly、
seed 20261021、heavy_solves==0）＋notes/chain-assembly.md（四块数学内容
叙述）＋本门＋嵌套 CWD 包装器（thomson-n9/numerics/bounds/ 同名，D52-4
先例）＋会话根包装器（D7/D8/D9 先例，仓库外不入版本库）。输入存档全部
只读（r20_l5l6_seam/tube/l6_intube/endgame/l2_rigorous＋TableB5Data.lean
门内独立第二实现源）。

检查面（任务书 G0–G4＋NC1/NC2/NC3）：
  G0 账本自锚：seed==20261021、heavy_solves==0、kind/task、三层口径词汇
     表、确定性面（零 timestamp/wall_s/code_version/generated 顶层键——
     G2 逐位一致的必要条件）、provenance 输入 sha256 逐文件重算比对＋
     冻结锚三件字符串。
  G1 冻结面不触＋隔离面：git 双路由（git status --porcelain＋git diff
     HEAD --name-only）改动路径 ⊆ 自有六件（＋R21A_G1_ALLOW_FOREIGN
     环境变量逐件放行〔默认关〕＋r21 家族放行层——覆盖 r21a/r21b 在途
     自有件，D90 裁决 4 串行落盘）；挑战件目录/＋references/＋表 B 前十
     件 Lean 只读 git diff 守卫；四账本（m9/m10/hermite_v2/typed_ladder）
     sha256 冻结锚；endgame.json sha256==86863a09…69f＋TableB5Uncond==
     c79fc623…＋TableB5Polar==d8c58f7d…；**审计件隔离面**：
     r21_chain_assembly 不得出现在 endgame.json/endgame_chain.py 文本中
     ＋chain-only 干跑五字段逐位零漂移＋全集漂移叶 ⊆ 冻结 22 叶分布
     （certReverify 17＋code_version/timestamp 2＋L1 quant 1＋engineV2 2
     ——D84-4；新叶出现即 FAIL，处置归 D93）。
  G2 探针确定性重跑：--out /tmp 副产物与存档逐位一致（cmp 字节级）。
  G3 常数独立第二实现（D87-4 口径）：门内自有解析/Newton 包络（与探针
     不同构造——探针自 r20_l5l6_seam.json 直读、不读 Lean）重导全部供给
     常数：装配恒等式＋sqrt 前提＋k1/δ_A 精确层逐位相等＋包络层
     （C_B hi/lo、C_A eta/delta、√2Up）紧公差 |Δ|/v ≤1e-30（≫200-bit
     包络构造差 ~6e-61，≪任何实质篡改）；账本 supply 精确层 == r20 存档
     supply 精确层逐位（直读恒等）；**箱定律重导**：r_32==r*==
     950125/10⁸==R_MAX/16 精确 Fraction＋r_33=r*·2^{1/4} 双层有理平方根
     包络重导落存档 8 位有效舍入窗＋全 48 箱定律 8 位舍入带。
  G4 装配表断言（validate_ledger——对任意账本 dict 可复用，NC 同一入口）：
     复合阈值 6 行（三口径 × r_eff/r*）精确重算恒等（δ_need==R20 缝表
     行、δ_close==min(δ_ident,δ_need)、球门 binding、域检查三面、宽安全
     边 δ_need ≤ δ_ident/2）；辨识门 floor 比值 == tube.json
     verdict.ratio_at_floor（float 逐位）且 ≥2×；r20 缝表 12 行并列精确
     恒等；ε 链表 21 行（七阶梯点 × 三口径）d_P 界/双门比值/全败判定
     精确重算＋floor 行与 R20 supply_rows float 逐位对账＋M9 括带＋
     ≥2×/≥70×/≥399× 宽安全边断言；ε_need/α 外推 float 重算恒能；
     Ē 底座（区间恒等＋Ē_lo−E* 精确 2.69832e-10＋float64 Sterbenz 亲证
     ＋1e-6 容差 3706×＋wouldBe==E*＋γ²/(2μ_lo) 修正 <1e-15）；需求面
     零余量（r_32==r*＋相邻箱 μ 上端 ≤0＋1e-9 舍入带＋r_33 包络窗＋
     排除半径 ≪ r_eff）；定向舍入安全向＋float_advisory 分层机器检查
     （tier 词汇表＋advisory 只入宽安全边断言行）；chain_closed=False
     ＋binding=L3＋notes 转录锚。
  NC1 篡 δ_need 必拦：/tmp 篡副本把数值档 r_eff 口径 δ_need 精确值抬高
     0.1%（假装阈值更大⟹缝看似更近——现实作弊向）→ validate_ledger
     必 FAIL（复合行精确重算＋R20 并列恒等双面拦截）。
  NC2 篹 Ē_lo／r* 必拦：/tmp 篡副本（a）把 Ē_lo 抬到 25.76（假装更高
     能量底座）（b）把 r* 改 0.95（假装百倍认证球）→ 各必 FAIL
     （l6_intube 存档恒等面＋Ē_lo−E* 精确重算拦截）。
  NC3 辨识门方向反转必拦：/tmp 篡副本把 δ_ident 抬高 2×（假装辨识窗
     更宽——方向反转）→ 必 FAIL（δ_ident==tube.json half_gap/need 存档
     恒等面＋floor 比值逐位重算拦截）。

诚实边界：本门零求解零 SDP 零 Lean 编译（被验件零 Lean 面——供给常数
自 r20 账本直读，门内 TableB5Data.lean 重导系独立第二实现复验）；
endgame.json/四账本只读未动（sha256 锚＋干跑零漂移双面）；审计件不入
12 分区（隔离面）。

用法（CWD 无关）：
  python3 numerics/bounds/r21_chain_gate.py    # 全门（exit 0 = 过）
  python3 thomson-n9/numerics/bounds/r21_chain_gate.py
      # ↑ CWD＝仓库根时命中同名 runpy 包装器（R18A/R19A/R20A 先例）
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

SEED_GATE = 20261021                   # R21 各门统一 seed（D90 裁决 4）

PROBE_REL = "numerics/bounds/r21_chain_assembly_probe.py"
GATE_REL = "numerics/bounds/r21_chain_gate.py"
WRAPPER_REL = "thomson-n9/numerics/bounds/r21_chain_gate.py"   # CWD 兼容包装器
LEDGER_REL = "numerics/bounds/results/r21_chain_assembly.json"
NOTES_REL = "notes/chain-assembly.md"
DECISIONS_REL = "notes/decisions.md"
OWNED = {PROBE_REL, GATE_REL, WRAPPER_REL, LEDGER_REL, NOTES_REL,
         DECISIONS_REL}

TABLE_B5_DATA = REPO / "formal" / "lean" / "ThomsonN9" / "TableB5Data.lean"
TABLE_B5_UNCOND = REPO / "formal" / "lean" / "ThomsonN9" / "TableB5Uncond.lean"
R20_JSON = RESULTS / "r20_l5l6_seam.json"
TUBE_JSON = RESULTS / "tube.json"
L6_JSON = RESULTS / "l6_intube.json"
ENDGAME_JSON = RESULTS / "endgame.json"
L2_JSON = RESULTS / "l2_rigorous.json"
LEDGER = RESULTS / "r21_chain_assembly.json"
NOTES = REPO / "notes" / "chain-assembly.md"
ENDGAME_CHAIN = REPO / "numerics" / "bounds" / "endgame_chain.py"

# 只读冻结件（表 B 全家族 Lean 件——R19A/R20 冻结面延续）：显式 git diff 守卫。
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

# r21 家族放行集（D90 裁决 4：R21A 探针腿与 R21B 表 B 第八件腿
#〔TableB5Chain.lean/r21_b5chain_*＋notes〕及 R21C 收口腿〔endgame_gate.py/
# GAP-REPORT/PROGRESS/decisions 后续追加〕零交叠放行）。
PARALLEL_FAMILY = [
    r"^numerics/bounds/r21[a-z0-9_]*(\.py|/)",
    r"^numerics/bounds/results/r21[a-z0-9_]*(\.json|/)",
    r"^thomson-n9/numerics/bounds/r21[a-z0-9_]*(\.py|/)",
    r"^notes/decisions\.md$",
    r"^notes/chain-assembly\.md$",
    r"^formal/lean/ThomsonN9/TableB5Chain[a-zA-Z0-9_]*\.lean$",
    r"^notes/(b5chain|b5-chain|chain-formal|tableb5-chain)[a-z0-9.-]*\.md$",
    r"^numerics/bounds/endgame_gate\.py$",
    r"^(GAP-REPORT|PROGRESS)\.md$",
]

# C2 冻结漂移分布（R18C/R19/R20 实测口径，R20 会话复测同分布）：
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
ENVELOPE_TOL = Fr(1, 10**30)      # 包络层紧公差（D87-4 口径，见 G3 说明）
VOLATILE_KEYS = ("timestamp", "wall_s", "code_version", "generated")
E_STAR = Fr(25759986531, 10 ** 9)  # 九位参考 E*（thomson-workflow energies）

TMP = Path("/tmp/r21_chain_gate")


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


def fs(f: Fr) -> str:
    return f"{f.numerator}/{f.denominator}"


def parse_iv(s: str) -> list:
    return [Fr(x.strip()) for x in s.strip("[]").split(",")]


# ============================================================ 独立第二实现
# 门内 Newton 有理平方根包：与探针不同构造（a=isqrt(⌊q·2^{2p}⌋）；
# hi=(a+2)/2^p 严格上包〔a+2 > √q+1〕、lo=a/2^p 下包〔a² ≤ q〕——
# 探针用 isqrt(quotient+1)+1 与 isqrt(quotient) 的不同字面）。
def sqrt_env(q: Fr, side: str, bits: int = 200) -> Fr:
    num, den = q.numerator, q.denominator
    a = math.isqrt((num << (2 * bits)) // den)
    if side == "lo":
        return Fr(a, 1 << bits)
    return Fr(a + 2, 1 << bits)


def parse_data_literal(name: str, src: str) -> Fr:
    """TableB5Data.lean def 值直读（门内自有解析——按行切分）。"""
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
    # 装配恒等式（norm_num 面的独立第二实现复验）
    if u1 * s1Up / (l3 * l3) + 2 / s3Dn != CInner:
        fail("G3 装配① C_inner 恒等式不符")
    if sqrt72Up * CInner != CVal:
        fail("G3 装配② C==sqrt72Up·CInner 恒等式不符")
    if s3Dn / (2 * s1Up) * (l3 * l3) / (sqrt72Up * u1) != deltaMax:
        fail("G3 装配④ δ_max 恒等式不符")
    # sqrt 前提（方向性：上包平方 ≥ 真值 ≥ 下包平方）
    if not (u1 <= s1Up * s1Up):
        fail("G3 前提 s1Up² ≥ u₁ 不符")
    if not (s3Dn * s3Dn <= l3):
        fail("G3 前提 s3Dn² ≤ l₃ 不符")
    if not (72 <= sqrt72Up * sqrt72Up):
        fail("G3 前提 sqrt72Up² ≥ 72 不符")
    if not (s3Dn <= s1Up):
        fail("G3 前提 s3Dn ≤ s1Up 不符")
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
    if led.get("kind") != "n9-r21-chain-assembly":
        fail(f"G0 kind 失配：{led.get('kind')!r}")
    if led.get("task") != "r21a-chain-assembly-probe":
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
                     os.environ.get("R21A_G1_ALLOW_FOREIGN", "").split(",")
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
                print(f"[gate][G1][r21 家族放行] 在途件（D90 裁决 4 pattern）：{p}")
                continue
            raise GateFail(
                f"G1 树上出现非本任务自有件（{cmd[1]}）：{p!r}"
                f"（自有集={sorted(OWNED)}；r21 家族放行层未覆盖）")
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
    okmsg("G1 冻结面：git 双路由改动 ⊆ 自有六件＋r21 家族放行层；表 B 十件 "
          "Lean＋挑战件/ references/ ＋四账本 sha256 冻结锚＋endgame.json/"
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
    if "r21_chain_assembly" in (REPO / ENDGAME_REL).read_text():
        fail("G1 隔离面：r21_chain_assembly 出现在 endgame.json 文本中"
             "（审计件非证书）")
    if "r21_chain_assembly" in ENDGAME_CHAIN.read_text():
        fail("G1 隔离面：r21_chain_assembly 出现在 endgame_chain.py 文本中"
             "（禁止输入）")
    out = TMP / "chain_dry.json"
    r = run([sys.executable, "numerics/bounds/endgame_chain.py",
             "--out", str(out)], REPO)
    if r.returncode != 0:
        fail(f"G1 chain-only 干跑 exit {r.returncode}")
    arch = load_json(REPO / ENDGAME_REL)
    dry = load_json(out)
    # 五字段严格零漂移（r19c/r20 C2 同口径）
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
    # 全集漂移叶 ⊆ 冻结 22 叶（新叶即 FAIL——D84-4 口径，处置归 D93）
    drifted = set(_leaf_diff(arch, dry, ""))
    fresh = drifted - FROZEN_DRIFT_LEAVES
    if fresh:
        fail(f"G1 C2 冻结漂移分布出现新叶（{len(fresh)} 处——审计件若被误接为 "
             f"chain 输入即在此暴露；处置归 D93）：{sorted(fresh)[:6]}")
    missing = FROZEN_DRIFT_LEAVES - drifted
    if missing:
        fail(f"G1 C2 漂移分布叶缺失（{len(missing)} 处——环境面变化，如实拦）："
             f"{sorted(missing)[:4]}")
    okmsg("G1 隔离面：r21_chain_assembly 不入 endgame.json/endgame_chain.py "
          "文本；chain-only 干跑五字段逐位零漂移＋全集漂移恰为冻结 22 叶"
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
    r20sup = load_json(R20_JSON)["supply"]
    # 账本 supply 精确层 == r20 存档 supply 精确层逐位（直读恒等）
    for k in ("l3", "u1", "s1Up", "s3Dn", "sqrt72Up", "CInner", "CVal",
              "deltaMax", "k1"):
        if Fr(sup[k]["exact"]) != Fr(r20sup[k]["exact"]):
            fail(f"G3 直读恒等失配：supply.{k} ≠ r20 存档")
    for k in ("eta_caliber", "delta_caliber", "delta_A"):
        if Fr(sup["C_A"][k]["exact"]) != Fr(r20sup["C_A"][k]["exact"]):
            fail(f"G3 直读恒等失配：supply.C_A.{k} ≠ r20 存档")
    for k in ("hi", "lo"):
        if Fr(sup["C_B"][k]["exact"]) != Fr(r20sup["C_B"][k]["exact"]):
            fail(f"G3 直读恒等失配：supply.C_B.{k} ≠ r20 存档")
    # 门内独立重导（TableB5Data.lean）vs 账本：精确层逐位＋包络层紧公差
    exact_fields = {"l3": "l3", "u1": "u1", "s1Up": "s1Up", "s3Dn": "s3Dn",
                    "sqrt72Up": "sqrt72Up", "CInner": "CInner",
                    "CVal": "CVal", "deltaMax": "deltaMax", "k1": "k1"}
    for led_key, ctx_key in exact_fields.items():
        if Fr(sup[led_key]["exact"]) != ctx[ctx_key]:
            fail(f"G3 精确层失配：supply.{led_key}")
    if Fr(sup["C_A"]["delta_A"]["exact"]) != ctx["delta_A"]:
        fail("G3 精确层失配：supply.C_A.delta_A")
    # 包络层：紧公差 |Δ|/v ≤ 1e-30（两侧均 200-bit 包络，构造差 ~6e-61；
    # 任何实质篡改（≥1e-4 相对）必被检出）
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
    # 定向前提（对账本记值的精确整数面）
    if not (2 <= Fr(sup["sqrt2Up"]["exact"]) ** 2):
        fail("G3 定向前提：账本 sqrt2Up² < 2（方向反转）")
    if Fr(sup["C_B"]["hi"]["exact"]) < Fr(sup["C_B"]["lo"]["exact"]):
        fail("G3 定向前提：C_B.hi < C_B.lo")
    # l4.json 恒等（written_proof_fraction 档源对账）
    l4c = load_json(RESULTS / "l4.json")["constants"]
    if Fr(l4c["C_exact"]) != ctx["CVal"]:
        fail("G3 l4.json C_exact ≠ TableB5Data CVal（精确恒等破损）")
    if Fr(l4c["delta_max_exact"]) != ctx["deltaMax"]:
        fail("G3 l4.json delta_max_exact ≠ TableB5Data deltaMax")
    # ---- 箱定律重导（r_32==r*、r_33 精确 Fraction 包络）
    l6 = load_json(L6_JSON)
    R_MAX = Fr(l6["binning"]["R_MAX"])
    r_star = Fr(l6["quadraticGrowth"]["rigorousRadius"])
    r32 = R_MAX / 16
    if not (r32 == Fr(950125, 10 ** 8) == r_star == Fr(l6["bins"][31]["r"])):
        fail("G3 箱定律：r_32=R_MAX/16 ≠ 950125/10⁸ = r* = bins[31].r")
    s2_lo, s2_hi = sqrt_env(Fr(2), "lo"), sqrt_env(Fr(2), "hi")
    if not (s2_lo * s2_lo <= 2 <= s2_hi * s2_hi):
        fail("G3 √2 包络方向破损")
    b4_lo = sqrt_env(2 * s2_lo, "lo")
    b4_hi = sqrt_env(2 * s2_hi, "hi")
    if not (b4_lo * b4_lo <= 2 * s2_lo and 2 * s2_hi <= b4_hi * b4_hi):
        fail("G3 2^{3/4} 包络方向破损")
    r33_lo, r33_hi = R_MAX / (8 * b4_hi), R_MAX / (8 * b4_lo)
    arch33 = Fr(l6["bins"][32]["r"])
    if not (arch33 - Fr(5, 10 ** 10) <= r33_lo
            and r33_hi <= arch33 + Fr(5, 10 ** 10)):
        fail("G3 箱定律：r_33 包络未落存档 8 位有效舍入窗")
    for i, b in enumerate(l6["bins"]):
        k = i + 1
        v = float(b["r"])
        law = float(R_MAX) * 2.0 ** ((k - 48) / 4.0)
        if abs(v - law) > 5.1e-8 * abs(law) + 1e-15:
            fail(f"G3 箱定律：箱 {k} 半径偏离 8 位有效舍入带")
    okmsg("G3 常数独立第二实现（D87-4 口径）：账本 supply==r20 存档逐位＋"
          "TableB5Data.lean 重导装配恒等式＋sqrt 前提五件＋k1/δ_A 精确层逐位＋"
          "C_B/C_A 包络层紧公差 1e-30＋C_B·√δ 支配 19 点网格＋l4.json C_exact/"
          "δmax 恒等＋箱定律重导（r_32==r*==950125/10⁸==R_MAX/16 精确；r_33 "
          "双层包络落 8 位舍入窗；全 48 箱舍入带）")
    return ctx


# ============================================================ G4（可复用）
def validate_ledger(led: dict, ctx: dict, tag: str = "G4") -> None:
    """装配表断言全集（真实账本与 NC 篡副本同一入口——含供给常数对门内
    独立重算 ctx 的精确层逐位／包络层紧公差比对与定向前提）。"""
    sup = led["supply"]
    C_B = Fr(sup["C_B"]["hi"]["exact"])
    C_A = Fr(sup["C_A"]["delta_caliber"]["exact"])
    delta_A = Fr(sup["C_A"]["delta_A"]["exact"])
    CVal = Fr(sup["CVal"]["exact"])
    deltaMax = Fr(sup["deltaMax"]["exact"])
    l3, u1, sqrt72Up = (Fr(sup["l3"]["exact"]), Fr(sup["u1"]["exact"]),
                        Fr(sup["sqrt72Up"]["exact"]))
    # ---- 供给常数 vs 门内独立重算（精确层逐位；包络层紧公差——NC1 牙之一）
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

    # ---- 需求面（存档恒等——NC2 r* 牙）
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

    # ---- 双门复合阈值（(A) 块）
    tube = load_json(TUBE_JSON)
    half_gap = Fr(str(tube["ttp_spectrum"]["half_gap"]))
    if Fr(str(tube["verdict"]["need"])) != half_gap:
        fail(f"{tag} tube verdict.need ≠ half_gap（辨识门交叉锚破损）")
    dg = led["dual_gate"]
    if Fr(dg["identification_gate"]["value"]["exact"]) != half_gap:
        fail(f"{tag} δ_ident ≠ tube.json half_gap（存档恒等破损——NC3 牙）")
    if dg["identification_gate"]["value"]["tier"] != "float_advisory":
        fail(f"{tag} δ_ident tier 非 float_advisory")
    ident_floor = dg["identification_at_floor"]
    rho_floor = Fr(ident_floor["rho"]["exact"])
    if rho_floor != Fr(str(tube["verdict"]["rho_spec_at_floor"])):
        fail(f"{tag} ρ_floor ≠ tube.json verdict（存档恒等破损）")
    ri = rho_floor / half_gap
    if float(ri) != tube["verdict"]["ratio_at_floor"]:
        fail(f"{tag} 辨识门 floor 比值 ≠ verdict.ratio_at_floor（同数交叉"
             "验证失配）")
    if float(Fr(ident_floor["ratio"]["exact"])) != float(ri):
        fail(f"{tag} 辨识门 floor 比值重算失配")
    if not (rho_floor >= 2 * half_gap):
        fail(f"{tag} 辨识门 floor 违反 <2×（宽安全边断言破损）")
    if ident_floor["violated"] is not True:
        fail(f"{tag} identification_at_floor.violated 非 True")
    tvals = {"r_eff": (r_eff, "interval_certified_numeric", True),
             "r_star_raw": (r_star, "interval_certified_numeric", False)}
    rows = dg["composite_rows"]
    if len(rows) != 6:
        fail(f"{tag} 复合行数 {len(rows)} != 6（3 口径 × r_eff/r*）")
    seen = set()
    for row in rows:
        rt, tg = row["route"], row["target"]
        seen.add((rt, tg))
        t, ttier, primary = tvals[tg]
        if row["target_tier"] != ttier or (row["primary"] is True) != primary:
            fail(f"{tag} 复合行 {rt}/{tg} tier/primary 失配")
        dn_want = ((t / C_B) ** 2 if rt == "B_global_hoelder"
                   else t / C_A if rt == "A_narrow_linear" else t / CVal)
        dn = Fr(row["delta_need"]["exact"])
        if dn != dn_want:
            fail(f"{tag} 复合行 {rt}/{tg} δ_need 精确重算失配")
        dclose = Fr(row["delta_close"]["exact"])
        if dclose != min(half_gap, dn):
            fail(f"{tag} 复合行 {rt}/{tg} δ_close ≠ min(δ_ident, δ_need)")
        gap = Fr(row["ident_over_need"]["exact"])
        if gap != half_gap / dn or row["binding_gate"] != "demand（球门）":
            fail(f"{tag} 复合行 {rt}/{tg} 比值/binding 失配")
        if not (dn <= half_gap / 2):
            fail(f"{tag} 复合行 {rt}/{tg} 宽安全边断言 δ_need ≤ δ_ident/2 破损")
        # 域检查三面（复合阈值口径）
        if rt == "B_global_hoelder":
            if not dclose <= deltaMax:
                fail(f"{tag} B 档域检查失败（{tg}）")
        elif rt == "A_narrow_linear":
            if not (dclose <= delta_A
                    and u1 * sqrt72Up * dclose / (l3 * l3) <= Fr(1, 2)):
                fail(f"{tag} A 档域检查失败（{tg}）")
        else:
            if not dclose <= deltaMax:
                fail(f"{tag} 数值档域检查失败（{tg}）")
        if row["domain_ok"] is not True:
            fail(f"{tag} 复合行 {rt}/{tg} domain_ok 非 True")
        if rt == "numerical_linear":
            if row["route_tier"] != "written_proof_fraction":
                fail(f"{tag} 数值档 route_tier 非 written_proof_fraction")
        elif row["route_tier"] != "formal_lean":
            fail(f"{tag} Lean 档 route_tier 非 formal_lean")
    if seen != {(r, t) for r in ("B_global_hoelder", "A_narrow_linear",
                                 "numerical_linear")
                for t in ("r_eff", "r_star_raw")}:
        fail(f"{tag} 复合行覆盖面不完备：{sorted(seen)}")
    # r20 缝表 12 行并列（精确重算恒等＋与 r20 存档逐位）
    r20led = load_json(R20_JSON)
    par = dg["r20_seam_parallel"]["rows"]
    if len(par) != 12:
        fail(f"{tag} r20 并列行数 {len(par)} != 12")
    r20rows = {(r["route"], r["target"]): r for r in r20led["seam_table"]}
    for row in par:
        key = (row["route"], row["target"])
        if key not in r20rows:
            fail(f"{tag} r20 并列行 {key} 不在 r20 缝表")
        t = Fr(r20rows[key]["demand_radius"]["exact"])
        want = ((t / C_B) ** 2 if row["route"] == "B_global_hoelder"
                else t / C_A if row["route"] == "A_narrow_linear"
                else t / CVal)
        if Fr(row["recomputed_exact"]) != want:
            fail(f"{tag} r20 并列行 {key} 重算失配")
        if Fr(row["threshold_exact"]) != want or \
                Fr(r20rows[key]["threshold"]["exact"]) != want:
            fail(f"{tag} r20 并列行 {key} 与 r20 存档逐位失配")

    # ---- ε 空间链表（(B) 块）
    ec = led["epsilon_chain"]
    res = tube["spectral_tube"]["AAA"]["res"]
    keys_sorted = sorted(res, key=float)
    vals = [res[k]["rho_spec"] for k in keys_sorted]
    for a, b in zip(vals, vals[1:]):
        if a > b:
            fail(f"{tag} 存档阶梯非单调")
    if [p["eps"] for p in ec["ladder_points"]] != keys_sorted:
        fail(f"{tag} 阶梯点列与存档键序不符")
    if ec["monotone_ladder_verified"] is not True:
        fail(f"{tag} monotone_ladder_verified 非 True")
    table = ec["table"]
    if len(table) != 21:
        fail(f"{tag} ε 链表行数 {len(table)} != 21（7 点 × 3 口径）")
    tseen = set()
    for row in table:
        k, rt = row["eps"], row["route"]
        tseen.add((k, rt))
        rho = Fr(str(res[k]["rho_spec"]))
        if row["rho_spec"] != res[k]["rho_spec"]:
            fail(f"{tag} 链表 {k}/{rt} ρ 与存档失配")
        ri_want = rho / half_gap
        if Fr(row["ratio_ident"]["exact"]) != ri_want or \
                row["ratio_ident"]["pass"] is not False:
            fail(f"{tag} 链表 {k}/{rt} 辨识门比值/pass 失配")
        bound_want = (C_B * sqrt_env(rho, "hi") if rt == "B_global_hoelder"
                      else C_A * rho if rt == "A_narrow_linear"
                      else CVal * rho)
        if abs(Fr(row["d_P_bound"]["exact"]) - bound_want) > \
                ENVELOPE_TOL * bound_want:
            fail(f"{tag} 链表 {k}/{rt} d_P 界重算失配")
        rd_want = bound_want / r_eff
        if abs(Fr(row["ratio_demand"]["exact"]) - rd_want) > \
                ENVELOPE_TOL * rd_want:
            fail(f"{tag} 链表 {k}/{rt} 球门比值重算失配")
        if row["ratio_demand"]["pass"] is not False or \
                not row["composite"].startswith("fail"):
            fail(f"{tag} 链表 {k}/{rt} 全败判定失配")
        if not (ri_want >= 2 and rd_want >= 70):
            fail(f"{tag} 链表 {k}/{rt} 宽安全边断言（≥2×/≥70×）破损")
        if row["tier"] != "float_advisory":
            fail(f"{tag} 链表 {k}/{rt} tier 非 float_advisory")
    if tseen != {(k, r) for k in keys_sorted
                 for r in ("B_global_hoelder", "A_narrow_linear",
                           "numerical_linear")}:
        fail(f"{tag} 链表覆盖面不完备：{len(tseen)} 行")
    # floor 行与 R20 supply_rows float 逐位对账
    r20sup_rows = {(r["route"], r["target"]): r
                   for r in r20led["l3_reconciliation"]["supply_rows"]}
    for rt in ("B_global_hoelder", "A_narrow_linear", "numerical_linear"):
        mine = next(r for r in table
                    if r["eps"] == "1.5e-08" and r["route"] == rt)
        theirs = r20sup_rows[(rt, "r_eff")]
        if mine["d_P_bound"]["float"] != theirs["bound_at_floor"]["float"]:
            fail(f"{tag} floor 行 {rt} bound ≠ R20 supply_rows（float 逐位）")
        if mine["ratio_demand"]["float"] != theirs["shortfall_ratio"]["float"]:
            fail(f"{tag} floor 行 {rt} 比值 ≠ R20 supply_rows（float 逐位）")
    # M9 括带
    l2e = load_json(L2_JSON)["eps_forcing"]
    m9 = ec["m9_bracket"]
    eps_m9 = Fr(m9["eps_forcing_m9"]["exact"])
    if eps_m9 != Fr(l2e["exact"]) or m9["eps_forcing_m9"]["float"] != l2e["float"]:
        fail(f"{tag} eps_forcing(M9) 与 l2_rigorous 不符")
    if not (float(eps_m9) > 1e-4 and float(eps_m9) < 3e-4):
        fail(f"{tag} M9 ε_forcing 未落存档阶梯 1e-4–3e-4 括带内")
    rho_lo = Fr(str(res["0.0001"]["rho_spec"]))
    rho_hi = Fr(str(res["0.0003"]["rho_spec"]))
    if m9["rho_bracket"] != [float(rho_lo), float(rho_hi)]:
        fail(f"{tag} M9 ρ 括带端点与存档阶梯不符")
    if len(m9["rows"]) != 6 or \
            not all(r["composite"].startswith("fail") for r in m9["rows"]):
        fail(f"{tag} M9 括带行非全败或行数失配")
    if not (rho_lo / (r_eff / CVal) >= 399):
        fail(f"{tag} M9 括带下端对数值档阈值 shortfall < 399×")
    # ε_need 外推 float 重算恒能＋诚实标注在账
    ext = ec["eps_need_extrapolation"]
    al = math.log(float(rho_floor) / float(rho_lo)) / math.log(1.5e-8 / 1e-4)
    if abs(ext["alpha"]["float"] - al) > 1e-15:
        fail(f"{tag} α 外推重算失配")
    eps_need = 1.5e-8 * (float(r_eff / CVal) / float(rho_floor)) ** (1.0 / al)
    if abs(ext["eps_need"]["float"] - eps_need) > 1e-15 * abs(eps_need):
        fail(f"{tag} ε_need 外推重算失配")
    if not (1e-19 < eps_need < 1e-17):
        fail(f"{tag} ε_need 量级越界（预期 ~3.4e-18）")
    if ext["alpha"]["tier"] != "float_advisory" or \
            ext["eps_need"]["tier"] != "float_advisory":
        fail(f"{tag} ε_need/α tier 非 float_advisory")
    for anc in ("两点", "平台形状未知", "9.4e-9", "dead-at-(9,6)"):
        if anc not in ext["honest"]:
            fail(f"{tag} ε_need 诚实标注缺锚：{anc!r}")

    # ---- L6 能量底座复合（(C) 块）
    l6c = led["l6_composite"]
    eb = l6["Ebar"]
    if l6c["ebar"]["interval_str"] != eb["interval"]:
        fail(f"{tag} Ē 区间串与存档不符")
    eb_iv = parse_iv(eb["interval"])
    ebar_lo = eb_iv[0]
    if eb_iv[0] != eb_iv[1]:
        fail(f"{tag} Ē 区间非单点")
    diff = Fr(l6c["ebar_lo_minus_E_star"]["exact"])
    if diff != ebar_lo - E_STAR or diff <= 0 or diff >= Fr(1, 10 ** 6):
        fail(f"{tag} Ē_lo−E* 精确重算失配或越 1e-6 铁律容差")
    if abs(l6c["ebar_lo_minus_E_star"]["float_exact_decimal"]
           - float(diff)) > 0:
        fail(f"{tag} Ē_lo−E* float 镜像失配")
    if abs(l6c["ebar_lo_minus_E_star"]["float64_subtraction"]
           - (float(ebar_lo) - 25.759986531)) > 0:
        fail(f"{tag} Ē_lo−E* float64 Sterbenz 亲证值失配")
    if abs(Fr(1, 10 ** 6) / diff
           - l6c["ebar_lo_minus_E_star"]["rule_margin_factor"]) > 1e-6:
        fail(f"{tag} 铁律容差倍数重算失配")
    if abs(ebar_lo - Fr(eb["eStarHighPrecision"])) > Fr(eb["absDiffUpper"]):
        fail(f"{tag} |Ē−E*_hp| 十进制差 > absDiffUpper（存档自洽面破损）")
    mu_iv = parse_iv(qg["muAtRstar"])
    gam = parse_iv(qg["gammaLinear"])[0]
    cp = l6c["composite_proposition"]
    if Fr(cp["gamma"]["exact"]) != gam or Fr(cp["mu_lo"]["exact"]) != mu_iv[0]:
        fail(f"{tag} γ/μ_lo 与 l6_intube 存档不符")
    corr = gam * gam / (2 * mu_iv[0])
    if Fr(cp["quadratic_floor_correction"]["exact"]) != corr or \
            not corr < Fr(1, 10 ** 15):
        fail(f"{tag} γ²/(2μ_lo) 修正重算失配或 ≥1e-15")
    end = load_json(ENDGAME_JSON)
    wb = end["assembledRecord"]["wouldBe_if_chain_closed"]
    if cp["wouldBe_consistency"]["archived"] != wb or \
            Fr(wb["value"]) != E_STAR or cp["wouldBe_consistency"][
            "equals_E_star"] is not True or cp["wouldBe_consistency"][
            "composite_floor_above_reference"] is not True:
        fail(f"{tag} wouldBe 记账一致面失配（==E*＋复合底座高于参考）")
    # 需求面零余量
    dz = l6c["demand_face_zero_slack"]
    r32 = R_MAX / 16
    if fs(r32) != dz["r32_is_rstar"]["r32_exact"] or \
            r32 != Fr(950125, 10 ** 8) != r_star:
        fail(f"{tag} r_32==r*==950125/10⁸ 恒等失配")
    adj = Fr(l6["negativeControls"]["doubleRadiusControl"]["adjacentBinMuUpper"])
    mu33 = parse_iv(l6["bins"][32]["mu"])
    if dz["adjacent_bin"]["mu_upper_archived"] != \
            l6["negativeControls"]["doubleRadiusControl"]["adjacentBinMuUpper"]:
        fail(f"{tag} adjacentBinMuUpper 与存档不符")
    if not (adj <= 0 and mu33[1] <= 0):
        fail(f"{tag} 相邻箱 μ 上端 > 0（零余量前提破损）")
    if abs(adj - mu33[1]) > Fr(1, 10 ** 9):
        fail(f"{tag} adjacentBinMuUpper 9 位舍入带失配")
    if abs(Fr(dz["adjacent_bin"]["r33"]["archived"])
           - Fr(l6["bins"][32]["r"])) > 0:
        fail(f"{tag} r_33 存档串失配")
    s2_lo, s2_hi = sqrt_env(Fr(2), "lo"), sqrt_env(Fr(2), "hi")
    b4_lo, b4_hi = sqrt_env(2 * s2_lo, "lo"), sqrt_env(2 * s2_hi, "hi")
    r33_lo, r33_hi = R_MAX / (8 * b4_hi), R_MAX / (8 * b4_lo)
    arch33 = Fr(l6["bins"][32]["r"])
    if not (arch33 - Fr(5, 10 ** 10) <= r33_lo
            and r33_hi <= arch33 + Fr(5, 10 ** 10)):
        fail(f"{tag} r_33 包络未落存档 8 位有效舍入窗")
    if dz["adjacent_bin"]["mu_upper_leq_zero"] is not True:
        fail(f"{tag} mu_upper_leq_zero 非 True")
    dexcl = parse_iv(qg["competitorExclusionRadius"])
    if not (Fr(dexcl[1]) < r_eff / 10 ** 5):
        fail(f"{tag} 排除半径非 ≪ r_eff（比值前提破损）")

    # ---- 判定面
    v = led["verdict"]
    if v["chain_closed"] is not False:
        fail(f"{tag} chain_closed 应为 False（如实判定）")
    if "L3" not in v["binding"]:
        fail(f"{tag} binding 非 L3 供给")
    if v["consistency"]["r20_seam_closed"] is not False or \
            v["consistency"]["endgameChain_closed"] is not False or \
            v["consistency"]["endgameChain_blocking"] != ["L0", "L3"]:
        fail(f"{tag} 一致性面与存档判定失配")
    # 定向舍入安全向抽查（floor 行 safe_display ≥ 真值 ceil 性质）
    for row in table:
        sd = Fr(row["ratio_demand"]["safe_display_exact"])
        if not (sd >= Fr(row["ratio_demand"]["exact"])):
            fail(f"{tag} 链表 {row['eps']}/{row['route']} ceil 安全向破损")
    # tier 词汇表面（抽查关键块）
    for blk in (sup["C_B"]["hi"], sup["C_A"]["delta_caliber"],
                led["demand"]["r_star"], led["demand"]["r_eff"],
                l6c["ebar"]["lo"]):
        if blk["tier"] not in TIERS:
            fail(f"{tag} tier 词汇表外值：{blk['tier']!r}")


def gate4_assembly(led: dict, ctx: dict) -> None:
    validate_ledger(led, ctx, tag="G4")
    # notes 转录锚（四块数学内容叙述在场）
    notes = NOTES.read_text()
    for anc in ("# 链装配数值实例化探针",
                "双门复合阈值", "ε 空间链表", "L6 衔接",
                "0.01850609934999997", "2.5157", "3.37",
                "2.69832e-10", "950125/10⁸", "chain_closed=False"):
        if anc not in notes:
            fail(f"G4 notes/chain-assembly.md 转录锚缺失：{anc!r}")
    okmsg("G4 装配表断言：复合阈值 6 行精确重算恒等（δ_need==R20 缝表行＋"
          "δ_close==min＋球门 binding＋域检查三面＋宽安全边 δ_need≤δ_ident/2）"
          "＋辨识门 floor 同数交叉验证（==verdict.ratio_at_floor float 逐位）"
          "＋r20 缝表 12 行并列逐位＋ε 链表 21 行精确重算全败（≥2×/≥70× 宽"
          "安全边）＋floor 行 R20 对账＋M9 括带 ≥399×＋ε_need/α 重算恒能＋"
          "Ē 底座差 2.69832e-10（float64 Sterbenz 亲证＋3706× 容差）＋"
          "wouldBe==E*＋γ²/(2μ_lo)<1e-15＋需求面零余量（r_32==r*＋相邻箱 "
          "μ≤0＋r_33 包络窗）＋ceil 安全向＋分层机器检查＋chain_closed=False"
          "＋notes 转录锚 10 处")


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
    # NC1：把数值档 r_eff 口径 δ_need 抬高 0.1%（假装阈值更大⟹缝看似更近
    # ——现实作弊向）必拦（复合行精确重算＋R20 并列恒等双面）
    def nc1(d):
        row = next(r for r in d["dual_gate"]["composite_rows"]
                   if r["route"] == "numerical_linear"
                   and r["target"] == "r_eff")
        v = Fr(row["delta_need"]["exact"])
        row["delta_need"]["exact"] = fs(v * Fr(1001, 1000))
        row["delta_close"]["exact"] = fs(min(Fr(
            d["dual_gate"]["identification_gate"]["value"]["exact"]),
            v * Fr(1001, 1000)))
    p = _tampered_copy(led, nc1, "1")
    try:
        validate_ledger(load_json(p), ctx, tag="NC1")
        fail("NC1 失守：篡 δ_need（抬 0.1%）后装配表断言未拦截（不可达："
             "精确重算＋R20 并列恒等双面）")
    except GateFail as e:
        if "NC1" not in str(e):
            fail(f"NC1 拦截面失配：{e}")
        print(f"[gate][OK ] NC1 篡 δ_need（抬 0.1%）必拦：{str(e)[:90]}")
    # NC2a：Ē_lo 抬到 25.76（假装更高能量底座）必拦
    def nc2a(d):
        d["l6_composite"]["ebar"]["interval_str"] = \
            "[25.76, 25.76]"
        d["l6_composite"]["ebar"]["lo"]["exact"] = fs(Fr("25.76"))
    p = _tampered_copy(led, nc2a, "2a")
    try:
        validate_ledger(load_json(p), ctx, tag="NC2")
        fail("NC2 失守：篡 Ē_lo=25.76 后装配表断言未拦截（不可达：存档恒等面）")
    except GateFail as e:
        if "NC2" not in str(e):
            fail(f"NC2 拦截面失配：{e}")
        print(f"[gate][OK ] NC2a 篹 Ē_lo（25.76）必拦：{str(e)[:90]}")
    # NC2b：r* 改 0.95（假装百倍认证球）必拦
    def nc2b(d):
        d["demand"]["r_star"]["exact"] = fs(Fr(95, 100))
    p = _tampered_copy(led, nc2b, "2b")
    try:
        validate_ledger(load_json(p), ctx, tag="NC2")
        fail("NC2 失守：篡 r*=0.95 后装配表断言未拦截（不可达：存档恒等面）")
    except GateFail as e:
        if "NC2" not in str(e):
            fail(f"NC2 拦截面失配：{e}")
        print(f"[gate][OK ] NC2b 篹 r*（0.95）必拦：{str(e)[:90]}")
    # NC3：辨识门方向反转（δ_ident 抬高 2×——假装辨识窗更宽）必拦
    def nc3(d):
        v = Fr(d["dual_gate"]["identification_gate"]["value"]["exact"])
        d["dual_gate"]["identification_gate"]["value"]["exact"] = fs(v * 2)
        for r in d["dual_gate"]["composite_rows"]:
            r["delta_ident"]["exact"] = fs(v * 2)
    p = _tampered_copy(led, nc3, "3")
    try:
        validate_ledger(load_json(p), ctx, tag="NC3")
        fail("NC3 失守：δ_ident 抬 2× 后装配表断言未拦截（不可达：存档恒等"
             "面＋floor 比值逐位重算）")
    except GateFail as e:
        if "NC3" not in str(e):
            fail(f"NC3 拦截面失配：{e}")
        print(f"[gate][OK ] NC3 辨识门方向反转（δ_ident×2）必拦：{str(e)[:90]}")


# ============================================================ main
def run_gate() -> None:
    TMP.mkdir(parents=True, exist_ok=True)
    led = gate0_ledger()
    gate1_ownership()
    gate1_isolation()
    gate2_determinism()
    ctx = gate3_constants(led)
    gate4_assembly(led, ctx)
    run_ncs(led, ctx)


def main() -> None:
    t0 = time.time()
    print(f"[gate] r21_chain_gate.py seed={SEED_GATE}（确定性；零求解零 SDP "
          "零 Lean 编译；CWD 无关）")
    try:
        run_gate()
    except GateFail as e:
        print(f"[gate][FAIL] {e}", flush=True)
        sys.exit(1)
    wall = time.time() - t0
    print(f"[gate] PASS（{wall:.1f}s）——exit 0")
    print("[gate] heavySolves=0（数值面审计件：endgame.json/四账本只读未动；"
          "r21_chain_assembly.json 不入 12 分区）")


if __name__ == "__main__":
    main()
