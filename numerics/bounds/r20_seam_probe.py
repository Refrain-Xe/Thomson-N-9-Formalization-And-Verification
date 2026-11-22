#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r20_seam_probe.py — R20A L5→L6 缝量化探针（D86 裁决 1；heavySolves=0，
零求解零 SDP 零新数值证书——纯确定性 Fraction／定向有理包络算术，
输入全部只读存档）.

任务书口径（r20a-l5l6-seam-probe，campaign dwfrun-f9904baf 第 15 轮）：
表 B 七件把 L5 形式层全链无条件化（R19A TableB5Uncond 24 定理）之后，本
探针是该形式底座的第一次数值消费——把『L3 是阻断』从定性升级为定量缝
目标，并勘正 Round 5『闭合窗口』叙述（域窗口 ≠ 链闭合窗口）。

供给面（三层口径，逐行分层标注）：
  * formal_lean 档（TableB5Uncond.lean，常数以 TableB5Data.lean def 直读）：
    - 路线 B（全局 ½-Hölder 档，:395 step6_hoelder_Cform，记录域全体 δ≤δ_max）：
      d_P ≤ C_B·√δ，C_B := k1·√δmax + √(3·√72Up)，k1 := s1Up·u₁·√72Up/l₃²
      ——√δmax/√(3·√72Up) 以 200-bit 整数 Newton 有理包络定向外扩（上包）；
    - 路线 A（窄域线性档，:932–941 step6_uncond_linear，域 η ≤ λ₃/24）：
      d_P ≤ (√λ₁·λ₁/λ₃² + 2√2/√λ₃)·η，δ 口径系数 (√λ₁·λ₁/λ₃²+2√2/√λ₃)·√72Up，
      定向包络 √λ₁≤s1Up、2√2≤2·sqrt2Up、√λ₃≥s3Dn、η≤√72Up·δ；
      域 δ_A := (l₃/24)/√72Up（η≤√72Up·δ≤l₃/24 ⟺ δ≤δ_A）。
  * written_proof_fraction 档（l4.json，书面证明口径非 Lean）：d_P ≤ CVal·δ
    （CVal==C_exact 精确 Fraction，δ ≤ δ_max=deltaMax——与 TableB5Data
    CVal/deltaMax 逐位恒等，装配恒等式独立第二实现复验）。
需求面（interval_certified_numeric 档，l6_intube.json /quadraticGrowth）：
  r* = 950125/10⁸＝0.00950125（精确十进制），μ(r*)=[0.00651,0.00928]，
  竞争者排除半径 [3.8519e-8,5.4901e-8]（≪ r*——排除面不构成瓶颈，注记），
  轨道中心偏移 deltaOrbitArchive=[2.5634854076114746e-6,2.5634854076114746e-6]
  **入账**：有效需求半径 r_eff := r* − delta_orbit_hi（中心偏移三角入账，
  d(Y,X)≤r_eff ⟹ d(Y,center)≤r_eff+delta_orbit=r*，安全向）；并列两档
  目标半径 0.07601（float_advisory：r_tube 公式值，l6_intube
  reconciliation.rTargetFormula.certifiedHere=="否" 未认证口径如实标注）与
  R_MAX=0.15202（rejection_certified_numeric：加倍半径处证书拒绝，负对照
  doubleRadiusControl 在档 triggered=true、μ 上端 −14151.328 ≤ 0）。

缝闭合阈值三口径（对四个需求半径各算一行，全部定向舍入安全向——
阈值 floor 向（报小仍充分）、比值 ceil 向（报大不低于真 shortfall））：
  δ_need_B=(t/C_B)²〔√δ 档〕、δ_need_A=t/C_A〔窄域线性档＋δ≤δ_A 域检查＋
  β=u₁η/l₃²≤1/2 域检查〕、δ_need_num=t/CVal〔数值线性档＋δ≤δ_max 域检查〕。

与 L3 供给对账（tube.json /verdict 阶梯，float_advisory 数值层输入如实
标注）：ε_forcing 处 ρ_spec=0.6447（存档 verdict.rho_spec_at_forcing，tube
自身 ε_forcing=4.1531e-4 档）、最深 SDP 点 ε=1.5e-8 处 0.0466、TTP slack
平台 0.2548、L3 谱管需求 need=0.018506（min_gap/2）；l2_rigorous.json
eps_forcing 精确 Fraction（float 1.4030566524531613e-4，M9 口径）落在存档
阶梯 1e-4→3e-4 两点之间——阶梯非降 ⟹ ρ_spec(M9 ε_forcing) ∈
[0.2548, 0.6447] 区间对账（存档不定值如实；两端对缝阈值均 ≥399×）。
δ=ρ 缝认同定＝簿记口径（注记：L5 前提为固定标号 |⟨y_i,y_j⟩−⟨x_i,x_j⟩|≤δ
∀i<j，S₉ 重排竞争者须对匹配重排应用前提；ρ_spec 系谱管坐标口径与
逐对内积偏差口径为不同量——本审计以口径同定作簿记，非证书）。

binding-constraint 识别：最深 SDP 点（ε=1.5e-8，伪近零深度 9.4e-9 级）
ρ_spec=0.0466 处 d_P ≤ CVal·ρ = 0.6927，对认证需求 r_eff 差 ~72.9×、对
R_MAX 差 ~4.56×、对未认证 0.07601 差 ~9.11×——三口径全不闭合，阻断层
=L3（供给），如实落账不硬凑。

Round 5『闭合窗口』勘正定量落账：architecture-decision.md §2.4（:205–:207，
另 §1.3 :131–:134）『ρ_spec(4.15e-4)~√ε≈0.02 落入 L5 δ_max=0.17124 覆盖
域——链有闭合窗口』系 **L5 常数域窗口 ≠ 链闭合窗口**：δ_max 是 L5 常数
的适用域上界（必要条件），闭合需 C·δ ≤ 需求半径；ρ=0.02 处 d_P ≤
CVal·0.02=0.29757 ≫ 0.07601（3.91×）≫ r_eff（31.33×）——域窗口对链闭合
高估 268×（δ_max/δ_need_num(r_eff)）。

诚实边界：本件系数值面审计件（audit artifact），不入 endgame.json/
citedCertificates/12 分区、不得成为 endgame_chain.py 输入（R11C–R19 先例，
D86 裁决 1）；l4.json 书面证明属性、tube.json 阶梯数值层属性、0.07601
未认证属性逐行分层标注（机器可查）；缝表任一断言与存档不符即 FAIL。

确定性：零随机零时间戳零 code_version（G2 重跑逐位一致的充分条件）；
sort_keys＋indent=1＋ensure_ascii=False。

用法（CWD 无关）：
  python3 numerics/bounds/r20_seam_probe.py [--out PATH]
产出（默认）：
  numerics/bounds/results/r20_l5l6_seam.json
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import re
import sys
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
REPO = HERE.parents[1]                       # thomson-n9/

TABLE_B5_DATA = REPO / "formal" / "lean" / "ThomsonN9" / "TableB5Data.lean"
TABLE_B5_UNCOND = REPO / "formal" / "lean" / "ThomsonN9" / "TableB5Uncond.lean"
L4_JSON = RESULTS / "l4.json"
L6_JSON = RESULTS / "l6_intube.json"
TUBE_JSON = RESULTS / "tube.json"
L2_JSON = RESULTS / "l2_rigorous.json"
R19_LEDGER = RESULTS / "r19_b5u_ledger.json"
OUT_JSON = RESULTS / "r20_l5l6_seam.json"

SEED = 20261020                             # R20 各件统一 seed（任务书口径）
SQ_BITS = 200                               # 有理平方根包精度（家族同参 r14_b5）
SIG = 6                                     # 定向舍入安全显示有效位数

# 三层口径词汇表（G4 机器检查面；float_advisory 不得进入精确断言行）
TIERS = ("formal_lean", "written_proof_fraction",
         "interval_certified_numeric", "rejection_certified_numeric",
         "float_advisory")


def log(msg: str) -> None:
    print(f"[r20seam] {msg}", flush=True)


def fail(msg: str) -> None:
    raise SystemExit(f"[r20seam][FAIL] {msg}")


def fs(f: Fr) -> str:
    return f"{f.numerator}/{f.denominator}"


def sha256_of(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def load(p: Path):
    return json.loads(p.read_text())


# ------------------------------------------------ 独立第二实现：有理平方根包
def sqrt_rat(q: Fr, side: str) -> Fr:
    """√q 的有理下界（'lo'）／上界（'hi'），整数 Newton（math.isqrt），q>0。

    r14_b5_data.sqrt_rat 同族算法的独立重导（不 import 之）：上界侧取
    isqrt(⌊q·2^(2p)⌋+1)+1 保证严格上界，下界侧取 isqrt 严格下界。方向性
    由调用方按需取用并在调用点断言（lo² ≤ q ≤ hi²）。
    """
    p = SQ_BITS
    num, den = q.numerator, q.denominator
    if side == "lo":
        return Fr(math.isqrt((num << (2 * p)) // den), 1 << p)
    return Fr(math.isqrt((num << (2 * p)) // den + 1) + 1, 1 << p)


def require(cond: bool, msg: str) -> None:
    if not cond:
        fail(msg)


# ------------------------------------------------ 定向舍入安全显示
def floor_sig(x: Fr, sig: int = SIG) -> Fr:
    """x 的 sig 位有效数字十进 floor（≤ x，安全向：阈值报小仍充分）。"""
    require(x > 0, f"floor_sig 需正值：{x}")
    e = math.floor(math.log10(float(x)))
    scale = Fr(10) ** (e - sig + 1)
    return Fr(math.floor(x / scale)) * scale


def ceil_sig(x: Fr, sig: int = SIG) -> Fr:
    """x 的 sig 位有效数字十进 ceil（≥ x，安全向：shortfall 报大不失真）。"""
    require(x > 0, f"ceil_sig 需正值：{x}")
    e = math.floor(math.log10(float(x)))
    scale = Fr(10) ** (e - sig + 1)
    return Fr(math.ceil(x / scale)) * scale


def num_block(f: Fr, tier: str, note: str = "") -> dict:
    """数值行统一块：精确 Fraction＋float 镜像＋口径分层标注。"""
    require(tier in TIERS, f"未知口径层 {tier}")
    b = {"exact": fs(f), "float": float(f), "tier": tier}
    if note:
        b["note"] = note
    return b


# ============================================================ 主流程
def main() -> None:
    ap = argparse.ArgumentParser(description="R20A L5→L6 缝量化探针（只读）")
    ap.add_argument("--out", default=str(OUT_JSON),
                    help="输出账本路径（默认仓库 results/ 下）")
    args = ap.parse_args()
    out_path = Path(args.out)

    # ---------------- 0) 只读输入与 provenance
    for p in (TABLE_B5_DATA, TABLE_B5_UNCOND, L4_JSON, L6_JSON, TUBE_JSON,
              L2_JSON, R19_LEDGER):
        require(p.exists(), f"输入缺失：{p}")

    data_src = TABLE_B5_DATA.read_text()
    uncond_src = TABLE_B5_UNCOND.read_text()
    l4 = load(L4_JSON)
    l6 = load(L6_JSON)
    tube = load(TUBE_JSON)
    l2 = load(L2_JSON)
    r19 = load(R19_LEDGER)

    # TableB5Data.lean def 直读（常数唯一源；regex 与门内第二实现不同字面）
    defs = dict(re.findall(r"^def\s+(\w+)\s*:\s*ℚ\s*:=\s*(\S+)", data_src, re.M))
    need_defs = ("l3", "u1", "s1Up", "s3Dn", "sqrt72Up",
                 "CInner", "CVal", "CChord", "deltaMax")
    for nm in need_defs:
        require(nm in defs, f"TableB5Data.lean 缺 def {nm}")
    C = {nm: Fr(defs[nm]) for nm in need_defs}          # noqa: N806（Lean 常量表）
    l3, u1 = C["l3"], C["u1"]
    s1Up, s3Dn, sqrt72Up = C["s1Up"], C["s3Dn"], C["sqrt72Up"]
    CInner, CVal, deltaMax = C["CInner"], C["CVal"], C["deltaMax"]

    # 装配恒等式独立第二实现复验（TableB5Data norm_num 四件的同式 Fraction 重导）
    require(u1 * s1Up / (l3 * l3) + 2 / s3Dn == CInner,
            "装配① C_inner = u₁·s1Up/l₃² + 2/s3Dn 不符")
    require(sqrt72Up * CInner == CVal, "装配② C = sqrt72Up·CInner 不符")
    require(2 * CVal == C["CChord"], "装配③ C_chord = 2·C 不符")
    require((s3Dn / (2 * s1Up)) * (l3 * l3) / (sqrt72Up * u1) == deltaMax,
            "装配④ δ_max = (s3Dn/(2·s1Up))·l₃²/(sqrt72Up·u₁) 不符")
    # sqrt 包络前提四件＋记录 λ 界（TableB5Data 同名定理的 Fraction 复验）
    require(u1 <= s1Up * s1Up, "s1Up² ≥ u₁ 不符")
    require(s3Dn * s3Dn <= l3, "s3Dn² ≤ l₃ 不符")
    require(72 <= sqrt72Up * sqrt72Up, "sqrt72Up² ≥ 72 不符")
    require(s3Dn <= s1Up, "s3Dn ≤ s1Up 不符")
    require(Fr(0) < l3 and l3 <= u1, "l₃ ∈ (0, u₁] 不符")

    # TableB5Uncond.lean 语句锚（缝常数与 Lean 陈述的接线面；行号入账）
    anchors = {}
    for key, pat in {
        "route_B_theorem": r"^theorem step6_hoelder_Cform\b",
        "route_B_Cform": (r"s1Up:ℝ\) \* \(u1:ℝ\) \* \(sqrt72Up:ℝ\) / "
                          r"\(l3:ℝ\)\^2 \* Real\.sqrt \(deltaMax:ℝ\)"),
        "route_B_sqrt3face": r"Real\.sqrt \(3 \* \(sqrt72Up:ℝ\)\)",
        "route_A_theorem": r"^theorem step6_uncond_linear\b",
        "route_A_Cform": (r"Real\.sqrt lam1 \* lam1 / lam3\^2"
                          r" \+ 2 \* Real\.sqrt 2 / Real\.sqrt lam3"),
        "route_A_domain24": r"≤ lam3 / 24",
    }.items():
        m = re.search(pat, uncond_src, re.M)
        require(m is not None, f"TableB5Uncond.lean 缺语句锚 {key}")
        anchors[key] = uncond_src[:m.start()].count("\n") + 1

    # ---------------- 1) 供给面（形式层双档 ＋ 数值层线性档）
    k1 = s1Up * u1 * sqrt72Up / (l3 * l3)
    sqrt_dm_lo, sqrt_dm_hi = sqrt_rat(deltaMax, "lo"), sqrt_rat(deltaMax, "hi")
    r372_lo, r372_hi = sqrt_rat(3 * sqrt72Up, "lo"), sqrt_rat(3 * sqrt72Up, "hi")
    C_B_hi = k1 * sqrt_dm_hi + r372_hi        # 上包（安全向：缝阈值用它）
    C_B_lo = k1 * sqrt_dm_lo + r372_lo        # 下包（信息面）
    require(sqrt_dm_lo * sqrt_dm_lo <= deltaMax <= sqrt_dm_hi * sqrt_dm_hi,
            "√δmax 包络方向破损（lo² ≤ δmax ≤ hi²）")
    require(r372_lo * r372_lo <= 3 * sqrt72Up <= r372_hi * r372_hi,
            "√(3√72Up) 包络方向破损（lo² ≤ 3√72Up ≤ hi²）")

    sqrt2Up = sqrt_rat(Fr(2), "hi")
    require(2 <= sqrt2Up * sqrt2Up, "√2 上包方向破损")
    C_A_eta = s1Up * u1 / (l3 * l3) + 2 * sqrt2Up / s3Dn    # η 口径上包
    C_A_delta = sqrt72Up * C_A_eta                          # δ 口径上包
    delta_A = (l3 / 24) / sqrt72Up                          # 精确 Fraction
    # 窄域 β 域检查的域端事实：β(δ_A) = u₁·√72Up·δ_A/l₃² == u₁/(24·l₃)（精确恒等）
    require(u1 * sqrt72Up * delta_A / (l3 * l3) == u1 / (24 * l3),
            "δ_A β 域恒等式不符")

    # C_B·√δ 支配面 19 点网格（r19 家族 G5(f) 同式复验：k1·δ + √(3√72Up·δ)
    # ≤ C_B_hi·√δ 于 δ ∈ (0, δmax]）——k1 界注入 δ≤δmax 的 √ 单调面
    grid_ok = True
    for i in range(1, 20):
        d = deltaMax * Fr(i, 20)
        lhs = k1 * d + sqrt_rat(3 * sqrt72Up * d, "hi")
        rhs = C_B_hi * sqrt_rat(d, "lo")
        if lhs > rhs:
            grid_ok = False
            break
    require(grid_ok, "C_B·√δ 支配面 19 点网格违例")

    # l4.json 恒等对账（written_proof_fraction 档）
    l4c = l4["constants"]
    require(Fr(l4c["C_exact"]) == CVal, "l4.json C_exact ≠ TableB5Data CVal")
    require(Fr(l4c["delta_max_exact"]) == deltaMax,
            "l4.json delta_max_exact ≠ TableB5Data deltaMax")
    require(l4c["C_float"] == float(CVal), "l4.json C_float ≠ float(CVal)")
    require(l4c["delta_max_float"] == float(deltaMax),
            "l4.json delta_max_float ≠ float(deltaMax)")
    require(Fr(l4c["C_inner_Frobenius_exact"]) == CInner,
            "l4.json C_inner_exact ≠ TableB5Data CInner")

    supply = {
        "layer_note": ("三层口径：formal_lean＝TableB5Data/TableB5Uncond 精确 "
                       "ℚ 常数与定理；written_proof_fraction＝l4.json 严格数值"
                       "层（Fraction 区间、书面证明非 Lean）；包络＝200-bit 整数 "
                       "Newton 有理包（独立第二实现，方向性逐点断言）"),
        "l3": num_block(l3, "formal_lean", "记录 λ₃ 下界（interval-Sylvester 对角路线）"),
        "u1": num_block(u1, "formal_lean", "记录 λ₁ 上界"),
        "s1Up": num_block(s1Up, "formal_lean", "σ₁=√λ₁ 有理上包（s1Up²≥u₁ 已验）"),
        "s3Dn": num_block(s3Dn, "formal_lean", "σ₃=√λ₃ 有理下包（s3Dn²≤l₃ 已验）"),
        "sqrt72Up": num_block(sqrt72Up, "formal_lean", "√72 有理上包"),
        "sqrt2Up": num_block(sqrt2Up, "formal_lean", "√2 有理上包（路线 A 定向包络件）"),
        "CInner": num_block(CInner, "formal_lean", "内积口径内常数（装配① 已验）"),
        "CVal": num_block(CVal, "formal_lean",
                          "数值层线性档常数同值（l4.json C_exact 逐位恒等已验；"
                          "d_P≤CVal·δ 的证明系书面口径非 Lean——tier 在 seam 表内"
                          "标 written_proof_fraction）"),
        "deltaMax": num_block(deltaMax, "formal_lean",
                              "适用域半径（l4.json delta_max_exact 逐位恒等已验）"),
        "k1": num_block(k1, "formal_lean", "k1 := s1Up·u₁·√72Up/l₃²（路线 B）"),
        "C_B": {
            "form": "C_B := k1·√δmax + √(3·√72Up)；d_P ≤ C_B·√δ（全域 δ ≤ δ_max，"
                    "β≤1/2 前件由 TableB5.delta_max_valid 内部导出）",
            "hi": num_block(C_B_hi, "formal_lean",
                            "上包（缝阈值安全向所用；√δmax/√(3√72Up) 200-bit 包外扩）"),
            "lo": num_block(C_B_lo, "formal_lean", "下包（信息面）"),
            "envelope_width_rel": float((C_B_hi - C_B_lo) / C_B_lo),
            "domain": "δ ≤ deltaMax（记录域全体）",
            "dominance_grid_19pt": grid_ok,
        },
        "C_A": {
            "form": "d_P ≤ (√λ₁·λ₁/λ₃² + 2√2/√λ₃)·η ≤ C_A_eta·η ≤ C_A_delta·δ"
                    "（η ≤ √72Up·δ 注入；δ 口径系数 (√λ₁·λ₁/λ₃²+2√2/√λ₃)·√72Up）",
            "eta_caliber": num_block(C_A_eta, "formal_lean",
                                     "η 口径上包（√λ₁≤s1Up、2√2≤2·sqrt2Up、√λ₃≥s3Dn）"),
            "delta_caliber": num_block(C_A_delta, "formal_lean", "δ 口径上包（×√72Up）"),
            "delta_A": num_block(delta_A, "formal_lean",
                                 "窄域适用半径 δ_A := (l₃/24)/√72Up（η≤√72Up·δ≤l₃/24）"),
            "domain": "η ≤ λ₃/24（c_lo := √(λ₃/2) 包络口径，D79-5）⟺ δ ≤ δ_A；"
                      "另需 β = u₁η/l₃² ≤ 1/2（域端恒等 u₁·√72Up·δ_A == u₁/(24·l₃)"
                      "≈0.0423 ≤ 1/2 已验——δ≤δ_A 自动满足）",
            "beta_at_delta_A_exact": fs(u1 * sqrt72Up * delta_A / (l3 * l3)),
        },
        "r19_ledger_cross": {},          # 稍后填充
        "uncond_statement_anchors": anchors,
    }
    # r19 账本路线 float 对账（G3 包络内命中面的探针侧记录）
    r19_routes = r19["data"]["routes"]
    cross = {}
    for nm, mine, theirs in (
            ("C_B_vs_r19_float", float(C_B_hi),
             float(r19_routes["B_global_hoelder"]["C_B_float"])),
            ("C_A_vs_r19_float", float(C_A_delta),
             float(r19_routes["A_narrow_linear"]["C_A_float"])),
            ("delta_A_vs_r19_float", float(delta_A),
             float(r19_routes["A_narrow_linear"]["delta_A_float"]))):
        cross[nm] = {"probe_float": mine, "r19_float": theirs,
                     "abs_diff": abs(mine - theirs),
                     "within_rounding": abs(mine - theirs) <= 5e-4 + 1e-6}
    supply["r19_ledger_cross"] = cross
    for nm, d in cross.items():
        require(d["within_rounding"], f"{nm} 超出 r19 账本舍入带")

    # ---------------- 2) 需求面（L6 认证球＋偏移入账＋双档目标半径）
    qg = l6["quadraticGrowth"]
    r_star = Fr(qg["rigorousRadius"])
    require(r_star == Fr(950125, 100000000), "r* ≠ 950125/10⁸")
    dob = qg["deltaOrbitArchive"].strip("[]").split(",")
    d_orb_lo, d_orb_hi = Fr(dob[0]), Fr(dob[-1])
    require(d_orb_lo == d_orb_hi == Fr("2.5634854076114746e-6"),
            "deltaOrbitArchive 非存档单点区间")
    r_eff = r_star - d_orb_hi                 # 中心偏移三角入账（安全向）
    require(r_eff > 0, "r_eff ≤ 0：中心偏移吞没认证球")
    mu = qg["muAtRstar"].strip("[]").split(",")
    dexcl = qg["competitorExclusionRadius"].strip("[]").split(",")
    drc = l6["negativeControls"]["doubleRadiusControl"]
    r_tube = Fr(l6["reconciliation"]["rTargetFormula"]["value"])
    R_MAX = Fr(l6["binning"]["R_MAX"])       # noqa: N806（存档名）
    require(R_MAX == 2 * r_tube, "R_MAX ≠ 2·r_tube")
    require(drc["triggered"] is True and drc["radiusDoubled"] == "0.15202",
            "doubleRadiusControl 非在档触发态")
    require(l6["reconciliation"]["rTargetFormula"]["certifiedHere"]
            .startswith("否"), "0.07601 认证状态字段非『否』——未注记面前提破损")
    require(float(d_orb_hi) <= float(r_star) / 100,
            "中心偏移量级异常（>r*/100）")

    demand = {
        "layer_note": ("interval_certified_numeric＝l6_intube.json 区间证书（数值层"
                       "非 Lean）；rejection_certified_numeric＝证书拒绝面（加倍半径"
                       "μ 上端 ≤0）；float_advisory＝未认证公式值，如实标注"),
        "r_star": num_block(r_star, "interval_certified_numeric",
                            "L6 认证二次增长球半径（l6_intube /quadraticGrowth/"
                            "rigorousRadius 精确十进制 " + qg["rigorousRadius"] + "）"),
        "mu_at_r_star": {"interval_str": qg["muAtRstar"],
                         "lo": float(mu[0]), "hi": float(mu[1]),
                         "tier": "interval_certified_numeric",
                         "note": "μ(r*) 认证区间（>0）"},
        "competitor_exclusion_radius": {
            "interval_str": qg["competitorExclusionRadius"],
            "lo": float(dexcl[0]), "hi": float(dexcl[1]),
            "tier": "interval_certified_numeric",
            "note": "排除半径 ≪ r_eff（E(Y)≤Ē ⟹ d(Y)≤2γ/μ 在 r* 球内）——排除面"
                    "不构成缝瓶颈，注记入账"},
        "delta_orbit_archive": {
            "interval_str": qg["deltaOrbitArchive"],
            "exact_hi": fs(d_orb_hi), "float_hi": float(d_orb_hi),
            "tier": "interval_certified_numeric",
            "note": "轨道中心偏移（L6 中心与 R1 存档 TTP 轨道 Hausdorff 上界）——"
                    "三角入账"},
        "r_eff": num_block(r_eff, "interval_certified_numeric",
                           "r_eff := r* − delta_orbit_hi（中心偏移入账后的有效需求"
                           "半径；d(Y,X)≤r_eff ⟹ d(Y,center)≤r*，安全向）——缝阈值"
                           "主口径"),
        "r_tube": num_block(r_tube, "float_advisory",
                            "目标半径 0.07601（√(2ΔE/λ_ref) 公式值；l6_intube "
                            "reconciliation.rTargetFormula.certifiedHere==『否…』"
                            "——未认证口径如实标注）"),
        "R_MAX": num_block(R_MAX, "rejection_certified_numeric",
                           "加倍半径 0.15202（证书拒绝口径：doubleRadiusControl "
                           f"triggered=true，μ 上端 {drc['muUpper']} ≤ 0）"),
        "exclusion_vs_r_eff": num_block(Fr(dexcl[1]), "interval_certified_numeric",
                                        "排除半径上端（≪ r_eff，对照记注）"),
    }

    # ---------------- 3) 缝闭合阈值表（三口径 × 四需求半径）
    targets = [
        ("r_eff", r_eff, "interval_certified_numeric", True),
        ("r_star_raw", r_star, "interval_certified_numeric", False),
        ("r_tube_uncertified", r_tube, "float_advisory", False),
        ("R_MAX_rejection", R_MAX, "rejection_certified_numeric", False),
    ]
    seam_rows = []
    for tname, t, tier, primary in targets:
        # 路线 B（√δ 档；全域 δ≤δ_max）
        dn_B = (t / C_B_hi) ** 2
        dom_B = dn_B <= deltaMax
        require(dom_B, f"路线 B 域检查失败（{tname}）")
        # 路线 A（窄域线性档；域 δ≤δ_A ＋ β=u₁η/l₃²≤1/2 于 η=√72Up·δ）
        dn_A = t / C_A_delta
        eta_A = sqrt72Up * dn_A
        dom_A = dn_A <= delta_A and u1 * eta_A / (l3 * l3) <= Fr(1, 2)
        require(dom_A, f"路线 A 域检查失败（{tname}）")
        # 数值线性档（书面证明口径；域 δ≤δ_max）
        dn_num = t / CVal
        dom_num = dn_num <= deltaMax
        require(dom_num, f"数值档域检查失败（{tname}）")
        for route, dn, dom, note in (
                ("B_global_hoelder", dn_B, dom_B,
                 "d_P ≤ C_B·√δ（Lean 路线 B；域 δ≤δ_max 全体）"),
                ("A_narrow_linear", dn_A, dom_A,
                 "d_P ≤ C_A_delta·δ（Lean 路线 A；域 δ≤δ_A＋β≤1/2 双检查）"),
                ("numerical_linear", dn_num, dom_num,
                 "d_P ≤ CVal·δ（l4.json 书面证明口径非 Lean）")):
            seam_rows.append({
                "route": route,
                "route_tier": "formal_lean" if route != "numerical_linear"
                              else "written_proof_fraction",
                "target": tname, "target_tier": tier,
                "demand_radius": num_block(t, tier),
                "threshold": num_block(dn, "formal_lean" if route != "numerical_linear"
                                       else "written_proof_fraction"),
                "threshold_safe_display": {
                    "exact": fs(floor_sig(dn)), "float": float(floor_sig(dn)),
                    "direction": "floor（报小仍充分）"},
                "domain_ok": bool(dom),
                "statement": note,
                "primary": primary,
            })

    # ---------------- 4) L3 供给对账（float_advisory 数值层输入如实标注）
    tv = tube["verdict"]
    rho_floor = Fr(str(tv["rho_spec_at_floor"]))
    rho_ttp = Fr(str(tv["rho_spec_at_ttp_level"]))
    rho_forcing = Fr(str(tv["rho_spec_at_forcing"]))
    need_l3 = Fr(str(tv["need"]))
    eps_m9_exact = Fr(l2["eps_forcing"]["exact"])
    require(l2["eps_forcing"]["float"] == float(eps_m9_exact),
            "l2 eps_forcing float 镜像不符")
    # 存档 AAA 阶梯（三点对：1e-4→0.2548 / 3e-4→0.6447）非降单调验证
    ladder = {k: v for k, v in
              tube["spectral_tube"]["AAA"]["res"].items()}
    keys_sorted = sorted(ladder, key=float)
    vals = [ladder[k]["rho_spec"] for k in keys_sorted]
    for i in range(len(vals) - 1):
        require(vals[i] <= vals[i + 1], "存档阶梯非单调（AAA）")
    m9_float = float(eps_m9_exact)
    lo_k, hi_k = "0.0001", "0.0003"
    require(float(lo_k) <= m9_float <= float(hi_k),
            "M9 ε_forcing 未落在存档阶梯 1e-4–3e-4 括带内")
    bracket_lo, bracket_hi = ladder[lo_k]["rho_spec"], ladder[hi_k]["rho_spec"]
    require(bracket_lo == float(rho_ttp) and bracket_hi == float(rho_forcing),
            "括带端点与 verdict 平台值不符")

    # 供给对缝：最深 SDP 点（floor）与各口径/各需求半径的 shortfall（ceil 安全向）
    l3_rows = []
    for route, bound_at_floor in (
            ("B_global_hoelder", C_B_hi * sqrt_rat(rho_floor, "hi")),
            ("A_narrow_linear", C_A_delta * rho_floor),
            ("numerical_linear", CVal * rho_floor)):
        for tname, t in (("r_eff", r_eff), ("r_tube", r_tube), ("R_MAX", R_MAX)):
            ratio = bound_at_floor / t
            l3_rows.append({
                "route": route, "target": tname,
                "bound_at_floor": {"float": float(bound_at_floor),
                                   "tier": "float_advisory",
                                   "note": "ρ_spec(floor)=0.0466 数值层输入（tube.json"
                                           " verdict）→ 定向包络上界"},
                "shortfall_ratio": {"float": float(ratio),
                                    "safe_display_exact": fs(ceil_sig(ratio, 2)),
                                    "safe_display_float": float(ceil_sig(ratio, 2)),
                                    "direction": "ceil（报大不低于真 shortfall）",
                                    "tier": "float_advisory"},
            })
    # 关键定量断言（float 输入＋宽安全边，定向： shortfall 下界）
    row_num_reff = next(r for r in l3_rows
                        if r["route"] == "numerical_linear" and r["target"] == "r_eff")
    row_num_rmax = next(r for r in l3_rows
                        if r["route"] == "numerical_linear" and r["target"] == "R_MAX")
    row_num_rtube = next(r for r in l3_rows
                         if r["route"] == "numerical_linear" and r["target"] == "r_tube")
    require(Fr(str(row_num_reff["shortfall_ratio"]["float"])) >= 70,
            "最深 SDP 点对 r_eff shortfall < 70×（与 73× 预期不符）")
    require(Fr(str(row_num_rmax["shortfall_ratio"]["float"])) >= Fr(45, 10),
            "最深 SDP 点对 R_MAX shortfall < 4.5×（与 4.6× 预期不符）")
    require(Fr(str(row_num_rtube["shortfall_ratio"]["float"])) >= Fr(39, 10),
            "最深 SDP 点对 r_tube shortfall < 3.9×（预期不符）")
    # M9 ε_forcing 括带两端对缝阈值均 ≥399×（缝判定对平台歧义稳健）
    thr_num = r_eff / CVal
    require(Fr(str(bracket_lo)) / thr_num >= 399,
            "M9 括带下端 0.2548 对数值档阈值 shortfall < 399×")

    l3_reconciliation = {
        "layer_note": ("tube.json /verdict 阶梯与 l2_rigorous eps_forcing 均系数值层"
                       "输入（float_advisory 如实标注）；eps_forcing 精确 Fraction 系 "
                       "l2_rigorous 严格层产物（written_proof_fraction）"),
        "rho_spec_at_forcing": {"float": float(rho_forcing), "tier": "float_advisory",
                                "note": "tube 自身 ε_forcing=4.1531e-4 档（cap m0748_M8 "
                                        "ΔE 口径）；存档 verdict.rho_spec_at_forcing"},
        "rho_spec_at_ttp_level": {"float": float(rho_ttp), "tier": "float_advisory",
                                  "note": "TTP slack 平台（ε 5.3e-6–1e-4）"},
        "rho_spec_at_floor": {"float": float(rho_floor), "tier": "float_advisory",
                              "note": "最深 SDP 点 ε=1.5e-8（伪近零 (0.1961,0.1961,"
                                      "0.1961) 深度 9.4e-9 级——可能是 SOS 族真零点）"},
        "need_l3_spectral_tube": {"float": float(need_l3), "tier": "float_advisory",
                                  "note": "L3 谱管需求 min_gap/2（tube.json verdict.need"
                                          "）；内部比值 ratio_at_floor=2.5157×"},
        "archived_ratios": {k: tv[k] for k in
                            ("ratio_at_forcing", "ratio_at_ttp_level", "ratio_at_floor")},
        "eps_forcing_m9": {
            "exact": fs(eps_m9_exact), "float": float(eps_m9_exact),
            "tier": "written_proof_fraction",
            "note": "l2_rigorous /eps_forcing 精确 Fraction（M9 口径，主口径十进制"
                    " E*）；落在存档阶梯 1e-4（0.2548）与 3e-4（0.6447）两点之间"},
        "eps_forcing_m9_bracket": {
            "lo": {"eps": lo_k, "rho_spec": bracket_lo},
            "hi": {"eps": hi_k, "rho_spec": bracket_hi},
            "monotone_ladder_verified": True,
            "note": "阶梯非降（存档点列逐对验证）⟹ ρ_spec(M9 ε_forcing) ∈ "
                    "[0.2548, 0.6447]；存档不定值如实；两端对数值档缝阈值均 "
                    "≥399×——缝判定对平台歧义稳健",
            "tier": "float_advisory"},
        "seam_identity_delta_equals_rho": {
            "convention": ("δ=ρ 缝认同定＝簿记口径：L5 前提为固定标号 "
                           "|⟨y_i,y_j⟩−⟨x_i,x_j⟩| ≤ δ (∀i<j)，S₉ 重排竞争者须对"
                           "匹配重排应用前提（前提对某重排成立时对该重排应用——"
                           "l4.json metric 注记）；ρ_spec 系谱管（类和特征坐标）口径"
                           "与逐对内积偏差口径为不同量——本审计以口径同定作簿记"
                           "（非证书）",),
            "tier": "float_advisory"},
        "supply_rows": l3_rows,
    }

    # ---------------- 5) Round 5『闭合窗口』勘正定量落账
    rho5 = Fr(1, 50)
    d5_num = CVal * rho5
    win_factor = deltaMax / thr_num
    round5 = {
        "narrative_source": "notes/architecture-decision.md §2.4（:205–:207；另 §1.3 "
                            ":131–:134）",
        "narrative_claim": "『ρ_spec(4.15e-4)~√ε≈0.02 落入无悔件 L5 的 δ_max=0.17124 "
                           "覆盖域——L2→L3→L5→L6 链有闭合窗口』",
        "correction": ("δ_max=0.17124 是 L5 常数的适用域上界（必要条件面），非链闭合"
                       "窗口：闭合需 C·δ ≤ 需求半径；ρ=0.02 处 d_P ≤ CVal·0.02="
                       "0.29757 ≫ 0.07601 ≫ r_eff——域窗口对链闭合高估 "
                       f"{float(win_factor):.1f}×（δ_max/δ_need_num(r_eff)）"),
        "rho_narrative": {"exact": fs(rho5), "float": float(rho5),
                          "tier": "float_advisory",
                          "note": "Round 5 设计期 √ε 量级估计值（非计算结果——原文"
                                  "自注）"},
        "d_P_bound_at_0.02": {
            "numerical_linear": num_block(d5_num, "float_advisory",
                                          "CVal·(1/50)（精确值记录；ρ=0.02 本身系"
                                          "advisory 输入）"),
            "ratios": {
                "vs_r_eff": {"float": float(d5_num / r_eff),
                             "safe_display_exact": fs(ceil_sig(d5_num / r_eff, 2)),
                             "tier": "float_advisory"},
                "vs_r_tube": {"float": float(d5_num / r_tube),
                              "safe_display_exact": fs(ceil_sig(d5_num / r_tube, 2)),
                              "tier": "float_advisory"},
                "vs_R_MAX": {"float": float(d5_num / R_MAX),
                             "safe_display_exact": fs(ceil_sig(d5_num / R_MAX, 2)),
                             "tier": "float_advisory"}}},
        "window_overstatement_factor": num_block(
            win_factor, "formal_lean",
            "δ_max/δ_need_num(r_eff)——『域窗口』若被误读为『闭合窗口』的高估倍数"),
        "verdict": "勘正成立：L5 常数域窗口（ρ ≤ δ_max）≠ 链闭合窗口（C·ρ ≤ r）；"
                   "ρ=0.02 全口径不闭合",
    }
    require(d5_num > 31 * r_eff, "Round5 勘正定量面破损（vs r_eff < 31×）")
    require(d5_num > Fr(39, 10) * r_tube, "Round5 勘正定量面破损（vs r_tube < 3.9×）")

    # ---------------- 6) binding-constraint 识别
    binding = {
        "binding_layer": "L3（供给面：slack 零集几何）",
        "quantified": {
            "deepest_sdp_point": "ε=1.5e-8，ρ_spec=0.0466（float_advisory 输入）",
            "numerical_caliber_vs_r_eff": row_num_reff["shortfall_ratio"]["float"],
            "numerical_caliber_vs_R_MAX": row_num_rmax["shortfall_ratio"]["float"],
            "numerical_caliber_vs_r_tube": row_num_rtube["shortfall_ratio"]["float"],
            "lean_route_A_vs_r_eff": next(
                r for r in l3_rows if r["route"] == "A_narrow_linear"
                and r["target"] == "r_eff")["shortfall_ratio"]["float"],
            "lean_route_B_vs_r_eff": next(
                r for r in l3_rows if r["route"] == "B_global_hoelder"
                and r["target"] == "r_eff")["shortfall_ratio"]["float"]},
        "identification": ("三口径（Lean √δ／Lean 窄域线性／数值线性）× 三需求半径"
                          "（r_eff／0.07601／R_MAX）全组合不闭合：最深 SDP 点对认证 "
                          "r_eff 差 ~72.9×（数值档；Lean 窄域 ~92.9×／√δ 档 ~161.9×），"
                          "对证书拒绝半径 R_MAX 亦差 ~4.56×——阻断层=L3 供给（ρ_spec "
                          "阶梯地板 0.0466 由伪近零几何决定，ε 压缩 4 个数量级仅"
                          "13.8× 收益），非 L5 常数层亦非 L6 认证球；如实落账不硬凑"),
        "tier": "float_advisory",
    }

    # ---------------- 7) 账本组装（确定性：零时间戳零 code_version）
    doc = {
        "kind": "n9-r20-l5l6-seam",
        "task": "r20a-l5l6-seam-probe",
        "seed": SEED,
        "heavy_solves": 0,
        "schema": {
            "tiers_vocabulary": list(TIERS),
            "tier_semantics": {
                "formal_lean": "TableB5Data/TableB5Uncond 精确 ℚ 常数与定理（Lean）",
                "written_proof_fraction": "严格数值层精确 Fraction（书面证明非 Lean）",
                "interval_certified_numeric": "区间证书数值层（非 Lean）",
                "rejection_certified_numeric": "证书拒绝面（负对照在档）",
                "float_advisory": "未认证数值输入（如实标注，不入精确断言）"},
            "determinism": ("零随机零时间戳零 code_version；sort_keys＋indent=1——"
                            "G2 重跑逐位一致的充分条件"),
            "artifact_class": ("数值面审计件（audit artifact）：不入 endgame.json/"
                               "citedCertificates/12 分区、不得成为 endgame_chain.py"
                               " 输入（R11C–R19 先例，D86 裁决 1）"),
            "rounding_policy": "阈值 floor 向 6 位有效数字（报小仍充分）；shortfall "
                               "比值 ceil 向（报大不低于真值）",
        },
        "provenance": {
            "read_only": True,
            "E_star": "25.759986531（thomson-workflow/data/energies.json，只读）",
            "inputs": {
                str(TABLE_B5_DATA.relative_to(REPO)): {
                    "sha256": sha256_of(TABLE_B5_DATA),
                    "role": "Lean ℚ 常数唯一源（def 直读）"},
                str(TABLE_B5_UNCOND.relative_to(REPO)): {
                    "sha256": sha256_of(TABLE_B5_UNCOND),
                    "role": "路线 B/A 语句锚（step6_hoelder_Cform/step6_uncond_linear）"},
                "numerics/bounds/results/l4.json": {
                    "sha256": sha256_of(L4_JSON),
                    "role": "数值层线性常数（C_exact/delta_max_exact 恒等对账）"},
                "numerics/bounds/results/l6_intube.json": {
                    "sha256": sha256_of(L6_JSON),
                    "role": "L6 需求面（r*/μ/排除半径/中心偏移/R_MAX/负对照）"},
                "numerics/bounds/results/tube.json": {
                    "sha256": sha256_of(TUBE_JSON),
                    "role": "L3 供给阶梯（verdict＋spectral_tube.AAA）"},
                "numerics/bounds/results/l2_rigorous.json": {
                    "sha256": sha256_of(L2_JSON),
                    "role": "eps_forcing 精确 Fraction（M9 口径）"},
                "numerics/bounds/results/r19_b5u_ledger.json": {
                    "sha256": sha256_of(R19_LEDGER),
                    "role": "r19 路线 float 对账（C_B/C_A/δ_A 包络内命中）"},
            },
            "frozen_anchors": {
                "endgame_json_sha256":
                    "86863a09bf84e950e85fc5f902bc2b4046a87f06703bd782e5148fc119afd69f",
                "tableb5uncond_sha256":
                    "c79fc6231d1e13b8ffd7873d1338901602ed3b70b3f057ed4eec4eb757e36d5e",
                "tableb5polar_sha256":
                    "d8c58f7d2c56c39fbe1ae62d634fc6ea5bd585fa9f1c0b9c2e2fc909d4338516"},
        },
        "supply": supply,
        "demand": demand,
        "seam_table": seam_rows,
        "l3_reconciliation": l3_reconciliation,
        "round5_correction": round5,
        "binding_constraint": binding,
        "verdict": {
            "seam_closed": False,
            "statement": ("L5→L6 缝不闭合（三口径全组合）：最深 SDP 供给 "
                          "ρ_spec=0.0466 对认证需求 r_eff=0.0094987 差 ~72.9×（数值"
                          "口径；Lean 窄域线性 ~92.9×／√δ 档 ~161.9×）；δ_need 三口径"
                          "＝1.7758e-6（B）/5.0106e-4（A）/6.3841e-4（num，均 r_eff "
                          "口径）；Round 5『闭合窗口』系域窗口误读（高估 268×）——"
                          "勘正定量落账；binding=L3 供给"),
        },
    }

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(doc, ensure_ascii=False, indent=1,
                                   sort_keys=True))
    log(f"[done ] {out_path}；seam_closed=False（binding=L3）；exit 0")


if __name__ == "__main__":
    main()
