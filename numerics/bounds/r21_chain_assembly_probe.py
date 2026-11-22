#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r21_chain_assembly_probe.py — R21A 链装配数值实例化探针（D90 裁决 1；
heavySolves=0，零求解零 SDP 零新数值证书——纯确定性 Fraction／定向有理
包络算术，输入全部只读存档）.

任务书口径（r21a-chain-assembly-probe，campaign dwfrun-f9904baf 第 16 轮）：
R20A 缝探针（r20_l5l6_seam.json，单门会计：d_P ≤ C·δ ≤ r）把缝消费推进
到『L3 是阻断』的定量缝目标之后，本探针完成 R20 节下轮候选 1——
『d_P≤C·δ 装配数值实例化与 L6 管内二次增长衔接』：缝会计从单门升级
**双门**（辨识门＋球门），并把 L6 能量底座复合进链假设命题，端到端
实例化 L2→L3→L5→L6 的数值装配面。

四块数学内容：

  (A) 双门复合阈值。三口径 X∈{B(√δ 档,C_B=7.127939)、A(窄域线性,
      C_A=18.957127)、num(线性,CVal=14.878732)}——供给常数自
      r20_l5l6_seam.json supply 精确层直读（本探针不重读 Lean；门 G3
      以 TableB5Data.lean def 独立第二实现复验精确层逐位＋包络层
      1e-30 紧公差，D87-4 口径）。复合闭合条件
          δ_close_X := min(δ_ident, δ_need_X)，
      δ_ident = tube.json /ttp_spectrum/half_gap = 0.01850609934999997
      （float_advisory——存档无精确节点值包络，只入宽安全边 ≥2× 定向
      断言，分层标注同 R20 之 0.07601）；δ_need_X = R20 精确 Fraction
      （1.775821e-6／5.010615e-4／6.384070e-4，r_eff 主口径；r* 口径
      12 行并列——R20 缝表逐行精确重算恒等）。断言：三口径均
      δ_need_X ≤ δ_ident/2（2× 宽安全边定向断言）⟹ 复合阈值
      =δ_need_X（球门 binding）；精确比值 δ_ident/δ_need＝10421.2×
      （B，4.018 个数量级）／36.93×（A，1.567）／28.99×（num，1.462）
      ——任务书设计期粗记 4.2 个数量级以执行员重算 4.018 为准（不影响
      判定方向）。辨识门在供给 floor=0.04655635318160481 处独立违反
      2.5157×（== tube.json verdict.ratio_at_floor 同数 float 逐位
      交叉验证）——缝会计从单门升级双门。

  (B) ε 空间链表。存档阶梯逐点（tube.json spectral_tube.AAA.res 七点：
      1.5e-8→0.04655635、1e-7→0.10432877、5.3484317457756185e-06→
      0.25484932、2e-05→0.25484932、1e-4→0.25484932、3e-4→0.64472583、
      ε_forcing=4.153070184893437e-4→0.64472583；非降单调复验）×三口径：
      ρ → d_P≤C·ρ（B 档 C_B·√ρ 定向包络上界）→ 双门比值 → 复合判定
      全表（21 行全败）。M9 口径 eps_forcing=1.4030566524531613e-4
      （l2_rigorous 精确 Fraction）括带 [0.2548,0.6447]（存档阶梯非降
      ⟹ 存档不定值如实）。ε_need 外推（float_advisory 设计期估计，
      执行员重算为准）：两点对数斜率
          α = ln(ρ_floor/ρ_plat)/ln(ε_floor/ε_plat)，
      两点＝(ε_floor=1.5e-8, ρ_floor=0.04655635) 与 (ε_plat=1e-4,
      ρ_plat=0.25484932)（任务书 B 块点名阶梯点『1e-4→0.2548』；备选
      平台起点 5.3484317457756185e-06 的稳健性对照在账）；
      α = 0.19307587251730365（任务书设计期 ≈0.19308 命中）；
      ε_need = ε_floor·(δ_need_num/ρ_floor)^{1/α}
              = 3.3701515978167564e-18（任务书 ≈3.4e-18 命中）——比最深
      SDP 点 1.5e-8 低 9.648 个数量级。诚实标注：两点斜率外推、深部
      平台形状未知、伪近零地板 9.4e-9（tube.json verdict bottleneck：
      (0.1961,0.1961,0.1961) 深度 9.4e-9 级——可能是 SOS 族真零点）决定
      SDP 供给深度下界——dead-at-(9,6) 的算术面精确化，非新证书。

  (C) L6 衔接（能量底座复合）。l6_intube 直读 Ē 区间
      [25.759986531269832, 25.759986531269832]（interval_certified_numeric
      层）＋absDiffUpper=1.68436e-13（对 E*_hp=25.75998653127）。复合
      条件命题：链假设（∀ 次水平集构型 Y：d_P(Y) ≤ C_X·ρ）＋ C_X·ρ ≤
      r_eff ⟹ E(Y) ≥ Ē_lo − γ²/(2·μ_lo)（L6 二次增长证书
      E ≥ Ē − γ·d + (μ/2)d² 于 d ≤ r_eff 的极小化；精确修正
      γ²/(2μ_lo)=2.4526e-18 低于 Ē 的 float64 ulp ~3.55e-15 ⟹ float
      粒度命题 E ≥ Ē_lo 成立）——Ē_lo 超九位参考 E*=25.759986531 达
      2.69832e-10（十进制精确 Fraction；float64 减法 Sterbenz 精确亲证
      2.6983215661857685e-10），≪1e-6 铁律容差 3706× ⟹ 与
      wouldBe_if_chain_closed==E*（记账定义值 25759986531/10⁹，只读
      交叉）一致、不改账本（诚实注记：复合底座 Ē_lo 高于参考值，
      wouldBe 记账保守）。μ(r_eff) ≥ μ(r*)_lo=0.0065098053…（方向安全：
      r* 球证书 a fortiori 覆盖子球 r_eff=r*−δ_orb<r*；箱列 μ 随 r 降
      同向：箱 31 μ_lo=0.0313＞箱 32 μ_lo=0.0065＞箱 33 上端 −0.0206）。
      L6 需求面零余量：rigorousRadius 恰为箱 32 半径
      （r_32 = R_MAX/16 = 0.15202/16 == 950125/10⁸ 精确 Fraction 亲证，
      分箱定律 r_k = R_MAX·2^((k−48)/4)）；相邻箱 33 μ 上端
      adjacentBinMuUpper=−0.020623402 ≤ 0（== bins[32].mu 上端 9 位
      舍入）、r_33 = r*·2^{1/4} ≈ 0.0112989541（200-bit 双层有理平方根
      包络重导，存档 8 位有效数字串 '0.011298954' 舍入窗内）——需求
      半径不可经既有证书上松，闭合负担全在 L3 供给（R20 结论定量强化）；
      竞争者排除 [3.8519e-8,5.4901e-8] ≪ r_eff 维持注记。

  (D) 判定。全存档供给点（七阶梯点＋M9 括带）双门全败（辨识门比值
      ≥2.5157×、球门比值 ≥72.93×）⇒ chain_closed=False（与 R20
      seam_closed=False 一致——细化非反转）；binding=L3 供给双门。

诚实边界：本件系数值面审计件（audit artifact），不入 endgame.json/
citedCertificates/12 分区、不得成为 endgame_chain.py 输入（R11C–R20
先例，D86 裁决 1／D90 裁决 1）；供给/需求面 r20 账本直读的分层标注
（formal_lean／written_proof_fraction／interval_certified_numeric／
rejection_certified_numeric／float_advisory）逐行原样携带；δ_ident 与
ε_need 系 float_advisory 只入宽安全边 ≥2× 定向断言；装配表任一断言与
存档不符即 FAIL。

确定性：零随机零时间戳零 code_version（G2 重跑逐位一致的充分条件）；
sort_keys＋indent=1＋ensure_ascii=False。

用法（CWD 无关）：
  python3 numerics/bounds/r21_chain_assembly_probe.py [--out PATH]
产出（默认）：
  numerics/bounds/results/r21_chain_assembly.json
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
REPO = HERE.parents[1]                       # thomson-n9/

R20_JSON = RESULTS / "r20_l5l6_seam.json"
TUBE_JSON = RESULTS / "tube.json"
L6_JSON = RESULTS / "l6_intube.json"
ENDGAME_JSON = RESULTS / "endgame.json"
L2_JSON = RESULTS / "l2_rigorous.json"
OUT_JSON = RESULTS / "r21_chain_assembly.json"

SEED = 20261021                             # R21 各件统一 seed（D90 裁决 4）
SQ_BITS = 200                               # 有理平方根包精度（家族同参）
SIG = 6                                     # 定向舍入安全显示有效位数

TIERS = ("formal_lean", "written_proof_fraction",
         "interval_certified_numeric", "rejection_certified_numeric",
         "float_advisory")


def log(msg: str) -> None:
    print(f"[r21chain] {msg}", flush=True)


def fail(msg: str) -> None:
    raise SystemExit(f"[r21chain][FAIL] {msg}")


def require(cond: bool, msg: str) -> None:
    if not cond:
        fail(msg)


def fs(f: Fr) -> str:
    return f"{f.numerator}/{f.denominator}"


def sha256_of(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def load(p: Path):
    return json.loads(p.read_text())


def sqrt_rat(q: Fr, side: str) -> Fr:
    """√q 有理下界（'lo'）／上界（'hi'），整数 Newton（math.isqrt）。

    与 r20_seam_probe.sqrt_rat 同族同构造（isqrt(⌊q·2^{2p}⌋+1)+1 上包 /
    isqrt(⌊q·2^{2p}⌋) 下包）——保证与 R20 supply_rows bound_at_floor
    精确 Fraction 逐位可对账；门 G3 用不同字面（a+2）第二实现。
    """
    p = SQ_BITS
    num, den = q.numerator, q.denominator
    if side == "lo":
        return Fr(math.isqrt((num << (2 * p)) // den), 1 << p)
    return Fr(math.isqrt((num << (2 * p)) // den + 1) + 1, 1 << p)


def floor_sig(x: Fr, sig: int = SIG) -> Fr:
    """x 的 sig 位有效数字十进 floor（≤ x，安全向：阈值报小仍充分）。"""
    require(x > 0, f"floor_sig 需正值：{x}")
    e = math.floor(math.log10(float(x)))
    scale = Fr(10) ** (e - sig + 1)
    return Fr(math.floor(x / scale)) * scale


def ceil_sig(x: Fr, sig: int = SIG) -> Fr:
    """x 的 sig 位有效数字十进 ceil（≥ x，安全向：比值报大不失真）。"""
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


def parse_iv(s: str) -> list:
    """'[a, b]' 存档区间串 → [Fr(a), Fr(b)]。"""
    return [Fr(x.strip()) for x in s.strip("[]").split(",")]


# ============================================================ 主流程
def main() -> None:
    ap = argparse.ArgumentParser(description="R21A 链装配数值实例化探针（只读）")
    ap.add_argument("--out", default=str(OUT_JSON),
                    help="输出账本路径（默认仓库 results/ 下）")
    args = ap.parse_args()
    out_path = Path(args.out)

    # ---------------- 0) 只读输入与 provenance
    for p in (R20_JSON, TUBE_JSON, L6_JSON, ENDGAME_JSON, L2_JSON):
        require(p.exists(), f"输入缺失：{p}")
    r20 = load(R20_JSON)
    tube = load(TUBE_JSON)
    l6 = load(L6_JSON)
    end = load(ENDGAME_JSON)
    l2 = load(L2_JSON)
    require(r20.get("kind") == "n9-r20-l5l6-seam"
            and r20["verdict"]["seam_closed"] is False,
            "r20 缝账本 kind/verdict 前提破损")

    # ---------------- 1) 供给面：r20 账本 supply 精确层直读（G3 门内独立
    # 第二实现自 TableB5Data.lean 复验——D87-4 口径）
    sup = r20["supply"]
    C_B = Fr(sup["C_B"]["hi"]["exact"])       # noqa: N806（上包，安全向）
    C_B_lo = Fr(sup["C_B"]["lo"]["exact"])
    C_A = Fr(sup["C_A"]["delta_caliber"]["exact"])
    delta_A = Fr(sup["C_A"]["delta_A"]["exact"])
    CVal = Fr(sup["CVal"]["exact"])
    deltaMax = Fr(sup["deltaMax"]["exact"])
    l3, u1 = Fr(sup["l3"]["exact"]), Fr(sup["u1"]["exact"])
    s1Up, s3Dn = Fr(sup["s1Up"]["exact"]), Fr(sup["s3Dn"]["exact"])
    sqrt72Up = Fr(sup["sqrt72Up"]["exact"])
    # 直读面方向前提（精确整数面；包络构造复验在门 G3）
    require(C_B >= C_B_lo, "直读 C_B.hi < C_B.lo")
    require(u1 <= s1Up * s1Up, "直读 s1Up² < u₁")
    require(s3Dn * s3Dn <= l3, "直读 s3Dn² > l₃")
    require(72 <= sqrt72Up * sqrt72Up, "直读 sqrt72Up² < 72")
    supply = dict(sup)                        # r20 供给面原样携带（含分层标注）
    supply["source"] = ("r20_l5l6_seam.json /supply 精确层直读（R20A 定向包络"
                        "产物）；本探针不重读 Lean——TableB5Data.lean def 独立"
                        "第二实现复验在 r21_chain_gate G3（精确层逐位＋包络层 "
                        "1e-30 紧公差，D87-4 口径）")

    # ---------------- 2) 需求面：r20 账本 demand 直读 ＋ l6_intube 新鲜恒等
    dem = r20["demand"]
    r_star = Fr(dem["r_star"]["exact"])
    d_orb_hi = Fr(dem["delta_orbit_archive"]["exact_hi"])
    r_eff = Fr(dem["r_eff"]["exact"])
    r_tube = Fr(dem["r_tube"]["exact"])
    R_MAX = Fr(dem["R_MAX"]["exact"])
    require(r_eff == r_star - d_orb_hi and r_eff > 0,
            "r_eff ≠ r* − delta_orbit_hi（中心偏移三角入账破损）")
    qg = l6["quadraticGrowth"]
    require(r_star == Fr(qg["rigorousRadius"]) == Fr(950125, 100000000),
            "r* ≠ l6_intube rigorousRadius / 950125/10⁸")
    require(dem["mu_at_r_star"]["interval_str"] == qg["muAtRstar"],
            "μ(r*) 区间串与 l6_intube 不符")
    mu_iv = parse_iv(qg["muAtRstar"])
    mu_lo = mu_iv[0]
    gam = parse_iv(qg["gammaLinear"])[0]
    demand = dict(dem)                        # r20 需求面原样携带
    demand["source"] = ("r20_l5l6_seam.json /demand 直读；l6_intube 恒等面"
                        "（r*/μ/中心偏移）本探针新鲜复核（require 全过）")

    # ---------------- 3) (A) 双门复合阈值
    tv = tube["verdict"]
    half_gap = Fr(str(tube["ttp_spectrum"]["half_gap"]))
    require(Fr(str(tv["need"])) == half_gap,
            "tube.json verdict.need ≠ ttp_spectrum.half_gap（辨识门阈值存档"
            "交叉锚破损）")
    δ_ident = half_gap                        # noqa: N816（任务书记号 δ_ident）
    ident_block = {
        "value": {"exact": fs(δ_ident), "float": float(δ_ident),
                  "tier": "float_advisory",
                  "note": "tube.json /ttp_spectrum/half_gap（min_gap/2）——存档"
                          "无精确节点值包络，float_advisory：只入宽安全边 ≥2× "
                          "定向断言，分层标注同 R20 之 0.07601；verdict.need "
                          "同数（float 逐位）交叉锚"},
        "statement": "辨识门：ρ ≤ δ_ident（L3 谱管辨识前提——δ=ρ 簿记同定下，"
                     "供给内积偏差口径量小于谱隙半宽 min_gap/2）",
    }
    # 辨识门在 floor 处独立违反（与 verdict.ratio_at_floor 同数交叉验证）
    rho_floor = Fr(str(tv["rho_spec_at_floor"]))
    ratio_floor_ident = rho_floor / δ_ident
    require(float(ratio_floor_ident) == tv["ratio_at_floor"],
            "辨识门 floor 比值 ≠ tube.json verdict.ratio_at_floor（同数交叉"
            "验证失配）")
    require(rho_floor >= 2 * δ_ident,
            "辨识门 floor 违反 <2×（宽安全边定向断言破损——存档比值 2.5157×）")
    # 三口径 δ_need（R20 精确 Fraction 逐位）＋复合阈值
    tvals = {"r_eff": (r_eff, "interval_certified_numeric", True),
             "r_star_raw": (r_star, "interval_certified_numeric", False)}
    composite_rows = []
    for tname, (t, ttier, primary) in tvals.items():
        dn_B = (t / C_B) ** 2
        dn_A = t / C_A
        dn_num = t / CVal
        for route, dn, rtier in (
                ("B_global_hoelder", dn_B, "formal_lean"),
                ("A_narrow_linear", dn_A, "formal_lean"),
                ("numerical_linear", dn_num, "written_proof_fraction")):
            require(dn <= δ_ident / 2,
                    f"复合阈值宽安全边断言失守（{route}/{tname}）：δ_need > "
                    "δ_ident/2")
            dclose = min(δ_ident, dn)
            gap = δ_ident / dn
            # 域检查（复合阈值 ≤ δ_need ⟹ 域面 a fortiori；仍逐口径显式断言）
            if route == "B_global_hoelder":
                dom = dclose <= deltaMax
                dom_note = "δ_close ≤ δ_max（记录域全体）"
            elif route == "A_narrow_linear":
                beta = u1 * sqrt72Up * dclose / (l3 * l3)
                dom = dclose <= delta_A and beta <= Fr(1, 2)
                dom_note = "δ_close ≤ δ_A ＋ β=u₁√72Up·δ/l₃² ≤ 1/2（精确）"
            else:
                dom = dclose <= deltaMax
                dom_note = "δ_close ≤ δ_max（书面证明域）"
            require(dom, f"复合域检查失败（{route}/{tname}）")
            composite_rows.append({
                "route": route, "route_tier": rtier,
                "target": tname, "target_tier": ttier,
                "primary": primary,
                "delta_need": num_block(dn, rtier,
                                        "R20 缝表精确 Fraction（逐位对账见 "
                                        "r20_seam_parallel）"),
                "delta_ident": {"exact": fs(δ_ident), "float": float(δ_ident),
                                "tier": "float_advisory"},
                "delta_close": num_block(
                    dclose, rtier if rtier != "written_proof_fraction"
                    else "written_proof_fraction",
                    "δ_close := min(δ_ident, δ_need)——复合闭合阈值"),
                "ident_over_need": {
                    "exact": fs(gap), "float": float(gap),
                    "orders_of_magnitude": math.log10(float(gap)),
                    "note": "δ_ident/δ_need（>1 ⟹ 球门 binding；任务书设计期"
                            "粗记 B 档 4.2 个数量级——执行员重算 4.018 为准，"
                            "不影响判定方向）"},
                "binding_gate": "demand（球门）" if dn < δ_ident else
                                "identification（辨识门）",
                "domain_ok": bool(dom), "domain_note": dom_note,
            })
    # r* 口径 12 行并列：R20 缝表逐行精确重算恒等
    parallel = []
    for row in r20["seam_table"]:
        t = Fr(row["demand_radius"]["exact"])
        rt = row["route"]
        want = ((t / C_B) ** 2 if rt == "B_global_hoelder"
                else t / C_A if rt == "A_narrow_linear" else t / CVal)
        require(Fr(row["threshold"]["exact"]) == want,
                f"r20 缝表 {rt}/{row['target']} 阈值精确重算失配")
        parallel.append({"route": rt, "target": row["target"],
                         "threshold_exact": row["threshold"]["exact"],
                         "recomputed_exact": fs(want),
                         "exact_equal": True})
    require(len(parallel) == 12, "r20 缝表行数 ≠ 12")
    dual_gate = {
        "identification_gate": ident_block,
        "identification_at_floor": {
            "rho": {"exact": fs(rho_floor), "float": float(rho_floor),
                    "tier": "float_advisory"},
            "ratio": {"exact": fs(ratio_floor_ident),
                      "float": float(ratio_floor_ident),
                      "safe_display_exact": fs(ceil_sig(ratio_floor_ident, 2)),
                      "tier": "float_advisory",
                      "note": "ρ_floor/δ_ident——与 tube.json verdict."
                              "ratio_at_floor 同数（float 逐位）交叉验证"},
            "violated": True,
            "margin_assertion": "ρ_floor ≥ 2·δ_ident（≥2× 宽安全边定向断言）",
        },
        "composite_definition": "δ_close_X := min(δ_ident, δ_need_X)——缝闭合"
                                "需 ρ ≤ δ_close_X（双门同时满足）",
        "composite_rows": composite_rows,
        "r20_seam_parallel": {
            "rows": parallel,
            "note": "r* 口径 12 行并列——R20 缝表（3 口径 × 4 需求半径）逐行"
                    "精确重算恒等（本探针 require；门 G4 复验）",
        },
        "supply_demand_constant_summary": {
            "C_B": float(C_B), "C_A": float(C_A), "CVal": float(CVal),
            "note": "任务书口径 7.127939/18.957127/14.878732（6 位有效显示；"
                    "精确 Fraction 见 supply 层）"},
    }

    # ---------------- 4) (B) ε 空间链表（存档阶梯逐点 × 三口径）
    res = tube["spectral_tube"]["AAA"]["res"]
    keys_sorted = sorted(res, key=float)
    vals = [res[k]["rho_spec"] for k in keys_sorted]
    for a, b in zip(vals, vals[1:]):
        require(a <= b, "存档阶梯非单调（AAA）")
    ladder_rows = []
    for k in keys_sorted:
        rho = Fr(str(res[k]["rho_spec"]))
        ladder_rows.append({"eps": k, "rho_spec": res[k]["rho_spec"],
                            "rho_spec_exact": fs(rho), "n": res[k]["n"],
                            "tier": "float_advisory",
                            "note": "tube.json spectral_tube.AAA.res 存档点"
                                    "（数值层输入，如实标注）"})
    chain_rows = []
    for k in keys_sorted:
        rho = Fr(str(res[k]["rho_spec"]))
        ri = rho / δ_ident
        require(ri >= 2, f"辨识门比值 <2×（ε={k}）——宽安全边断言破损")
        for route, bound, cnote in (
                ("B_global_hoelder", C_B * sqrt_rat(rho, "hi"),
                 "C_B·√ρ（√ρ 上包，定向）"),
                ("A_narrow_linear", C_A * rho, "C_A·ρ（精确）"),
                ("numerical_linear", CVal * rho, "CVal·ρ（精确）")):
            rd = bound / r_eff
            require(rd >= 70, f"球门比值 <70×（ε={k}/{route}）——宽安全边断言"
                              "破损")
            chain_rows.append({
                "eps": k, "rho_spec": res[k]["rho_spec"],
                "route": route, "bound_form": cnote,
                "d_P_bound": {"exact": fs(bound), "float": float(bound),
                              "tier": "float_advisory"},
                "ratio_ident": {"exact": fs(ri), "float": float(ri),
                                "pass": bool(ri <= 1),
                                "direction": "ρ/δ_ident（>1 违反）"},
                "ratio_demand": {"exact": fs(rd), "float": float(rd),
                                 "safe_display_exact": fs(ceil_sig(rd, 2)),
                                 "pass": bool(rd <= 1),
                                 "direction": "d_P/r_eff（>1 违反）"},
                "composite": "fail（双门全败）" if (ri > 1 or rd > 1)
                             else "closed",
                "tier": "float_advisory",
            })
    require(all(r["composite"].startswith("fail") for r in chain_rows),
            "存在复合判定非败的存档阶梯点——与预期（全败）不符，如实拦")
    # floor 行与 R20 supply_rows 对账（bound/ratio float 逐位）
    r20_rows = {(r["route"], r["target"]): r
                for r in r20["l3_reconciliation"]["supply_rows"]}
    for route in ("B_global_hoelder", "A_narrow_linear", "numerical_linear"):
        mine = next(r for r in chain_rows
                    if r["eps"] == "1.5e-08" and r["route"] == route)
        theirs = r20_rows[(route, "r_eff")]
        require(mine["d_P_bound"]["float"] == theirs["bound_at_floor"]["float"],
                f"floor 行 {route} bound ≠ R20 supply_rows（float 逐位）")
        require(mine["ratio_demand"]["float"]
                == theirs["shortfall_ratio"]["float"],
                f"floor 行 {route} 比值 ≠ R20 supply_rows（float 逐位）")
    # M9 括带行
    eps_m9 = Fr(l2["eps_forcing"]["exact"])
    require(l2["eps_forcing"]["float"] == float(eps_m9),
            "l2 eps_forcing float 镜像不符")
    rho_plat_lo = Fr(str(res["0.0001"]["rho_spec"]))
    rho_plat_hi = Fr(str(res["0.0003"]["rho_spec"]))
    require(float(eps_m9) > 1e-4 and float(eps_m9) < 3e-4,
            "M9 ε_forcing 未落存档阶梯 1e-4–3e-4 括带内")
    m9_rows = []
    for tag, rho in (("bracket_lo", rho_plat_lo), ("bracket_hi", rho_plat_hi)):
        for route, bound in (("B_global_hoelder", C_B * sqrt_rat(rho, "hi")),
                             ("A_narrow_linear", C_A * rho),
                             ("numerical_linear", CVal * rho)):
            m9_rows.append({
                "bracket_end": tag, "route": route,
                "d_P_bound_exact": fs(bound), "d_P_bound_float": float(bound),
                "ratio_demand": {"exact": fs(bound / r_eff),
                                 "float": float(bound / r_eff)},
                "ratio_ident": {"exact": fs(rho / δ_ident),
                                "float": float(rho / δ_ident)},
                "composite": "fail（双门全败）",
                "tier": "float_advisory",
            })
    dn_num = r_eff / CVal
    require(rho_plat_lo / dn_num >= 399,
            "M9 括带下端对数值档阈值 shortfall < 399×（R20 断言延续）")
    epsilon_chain = {
        "ladder_points": ladder_rows,
        "monotone_ladder_verified": True,
        "table": chain_rows,
        "m9_bracket": {
            "eps_forcing_m9": {"exact": fs(eps_m9), "float": float(eps_m9),
                               "tier": "written_proof_fraction",
                               "note": "l2_rigorous /eps_forcing 精确 Fraction"
                                       "（M9 口径）"},
            "rho_bracket": [float(rho_plat_lo), float(rho_plat_hi)],
            "rows": m9_rows,
            "note": "阶梯非降 ⟹ ρ_spec(M9 ε_forcing) ∈ [0.2548,0.6447]（存档"
                    "不定值如实）；两端双门全败",
        },
        "eps_need_extrapolation": {
            "two_points": {
                "floor": {"eps": "1.5e-08", "rho_spec": float(rho_floor)},
                "platform": {"eps": "0.0001",
                             "rho_spec": float(rho_plat_lo)},
                "note": "任务书 B 块点名阶梯点『1e-4→0.2548』——平台样本取存档 "
                        "1e-4 点",
            },
            "alpha": {
                "formula": "α = ln(ρ_floor/ρ_plat)/ln(ε_floor/ε_plat)",
                "float": math.log(float(rho_floor) / float(rho_plat_lo))
                         / math.log(1.5e-8 / 1e-4),
                "design_float": 0.19308,
                "tier": "float_advisory",
                "note": "执行员重算 0.19307587251730365——任务书设计期 ≈0.19308 "
                        "命中（5 位有效）",
            },
            "eps_need": {
                "formula": "ε_need = ε_floor·(δ_need_num/ρ_floor)^{1/α}",
                "float": 1.5e-8 * (float(dn_num) / float(rho_floor))
                         ** (1.0 / (math.log(float(rho_floor)
                                            / float(rho_plat_lo))
                                    / math.log(1.5e-8 / 1e-4))),
                "design_float": "≈3.4e-18",
                "tier": "float_advisory",
                "note": "执行员重算为准（设计期 float 估计）；δ_need_num="
                        "r_eff/CVal（r_eff 主口径）",
            },
            "orders_below_deepest_sdp": math.log10(
                1.5e-8 / (1.5e-8 * (float(dn_num) / float(rho_floor))
                          ** (1.0 / (math.log(float(rho_floor)
                                             / float(rho_plat_lo))
                                     / math.log(1.5e-8 / 1e-4))))),
            "robustness_alt_platform_onset": {
                "eps": "5.3484317457756185e-06",
                "alpha_alt": math.log(float(rho_floor) / float(rho_plat_lo))
                             / math.log(1.5e-8
                                        / 5.3484317457756185e-06),
                "eps_need_alt": 1.5e-8 * (float(dn_num) / float(rho_floor))
                                ** (1.0 / (math.log(float(rho_floor)
                                                    / float(rho_plat_lo))
                                           / math.log(1.5e-8
                                                      / 5.3484317457756185e-06))),
                "note": "平台起点（5.3484e-6）替代 1e-4 的斜率对照——存档平台 "
                        "5.3484e-6–1e-4 平坦（ρ 同 0.2548），斜率取平台起点时 "
                        "ε_need′ 仍比伪近零地板 9.4e-9 低 >6 个数量级——结论对"
                        "平台歧义稳健",
            },
            "honest": "两点对数斜率外推＝设计期 float 估计（float_advisory，非"
                      "证书）：①仅两点、深部平台形状未知；②伪近零地板 9.4e-9"
                      "（tube.json verdict bottleneck：(0.1961,0.1961,0.1961) "
                      "深度 9.4e-9 级——可能是 SOS 族真零点）决定 SDP 供给深度"
                      "下界，ε 压缩不可达 1e-18 域；③ε_need 比最深 SDP 点 "
                      "1.5e-8 低 ~9.6 个数量级——dead-at-(9,6) 的算术面精确化",
            "pseudo_near_zero_floor": {
                "depth": 9.4e-9,
                "source": "tube.json /verdict/bottleneck（存档文本直读）",
                "tier": "float_advisory",
            },
        },
    }

    # ---------------- 5) (C) L6 衔接（能量底座复合）
    eb = l6["Ebar"]
    eb_iv = parse_iv(eb["interval"])
    require(eb_iv[0] == eb_iv[1], "Ē 区间非单点（存档形状前提破损）")
    ebar_lo = eb_iv[0]
    e_star = Fr(25759986531, 10 ** 9)         # 九位参考 E*（只读参考能量）
    e_hp = Fr(eb["eStarHighPrecision"])
    diff_exact = ebar_lo - e_star
    diff_float = float(ebar_lo) - 25.759986531
    require(float(diff_exact) > 0 and diff_exact < Fr(1, 10 ** 6),
            "Ē_lo−E* 非正或超 1e-6 铁律容差")
    require(abs(ebar_lo - e_hp) <= Fr(eb["absDiffUpper"]),
            "|Ē−E*_hp| 十进制差 > 存档 absDiffUpper（存档自洽面破损）")
    corr = gam * gam / (2 * mu_lo)            # γ²/(2μ_lo) 二次底座精确修正
    require(corr < Fr(1, 10 ** 15), "γ²/(2μ_lo) ≥ 1e-15（float64 ulp 之下前提"
                                    "破损）")
    wb = end["assembledRecord"]["wouldBe_if_chain_closed"]
    require(Fr(wb["value"]) == e_star and wb["float"] == 25.759986531,
            "wouldBe_if_chain_closed ≠ E*（记账定义值交叉失配）")
    # 需求面零余量：箱定律重导
    bins = l6["bins"]
    require(len(bins) == 48, "分箱数 ≠ 48")
    r32 = R_MAX / 16
    require(r32 == Fr(950125, 10 ** 8) == r_star == Fr(bins[31]["r"]),
            "r_32 = R_MAX/16 ≠ 950125/10⁸ = r* = bins[31].r（精确 Fraction）")
    # 全 48 箱 float 对定律 8 位有效舍入带（mp.nstr(…,8) 口径）
    for i, b in enumerate(bins):
        k = i + 1
        v = float(b["r"])
        law = float(R_MAX) * 2.0 ** ((k - 48) / 4.0)
        require(abs(v - law) <= 5.1e-8 * abs(law) + 1e-15,
                f"箱 {k} 半径偏离定律 8 位有效舍入带")
    # r_33 = r*·2^{1/4}：双层有理平方根包络重导
    s2_lo, s2_hi = sqrt_rat(Fr(2), "lo"), sqrt_rat(Fr(2), "hi")
    require(s2_lo * s2_lo <= 2 <= s2_hi * s2_hi, "√2 包络方向破损")
    b4_lo = sqrt_rat(2 * s2_lo, "lo")         # 2^{3/4} 下包
    b4_hi = sqrt_rat(2 * s2_hi, "hi")         # 2^{3/4} 上包
    require(b4_lo * b4_lo <= 2 * s2_lo and 2 * s2_hi <= b4_hi * b4_hi,
            "2^{3/4} 包络方向破损")
    r33_lo, r33_hi = R_MAX / (8 * b4_hi), R_MAX / (8 * b4_lo)
    arch33 = Fr(bins[32]["r"])
    require(arch33 - Fr(5, 10 ** 10) <= r33_lo
            and r33_hi <= arch33 + Fr(5, 10 ** 10),
            "r_33 包络未落在存档 8 位有效舍入窗内")
    adj = Fr(l6["negativeControls"]["doubleRadiusControl"]["adjacentBinMuUpper"])
    mu33 = parse_iv(bins[32]["mu"])
    require(adj <= 0 and mu33[1] <= 0, "相邻箱 μ 上端 > 0（零余量前提破损）")
    require(abs(adj - mu33[1]) <= Fr(1, 10 ** 9),
            "adjacentBinMuUpper 与 bins[32].mu 上端差 > 1e-9（9 位舍入带）")
    dexcl = parse_iv(qg["competitorExclusionRadius"])
    l6_composite = {
        "ebar": {
            "interval_str": eb["interval"],
            "lo": {"exact": fs(ebar_lo), "float": float(ebar_lo),
                   "tier": "interval_certified_numeric",
                   "note": "l6_intube /Ebar/interval 区间证书数值层（单点区间）"
                           "——能量底座"},
            "absDiffUpper": eb["absDiffUpper"],
            "eStarHighPrecision": eb["eStarHighPrecision"],
            "abs_check": {"decimal_diff": float(abs(ebar_lo - e_hp)),
                          "leq_absDiffUpper": True,
                          "note": "十进制精确差 ≤ 存档 absDiffUpper（存档自洽）"},
        },
        "ebar_lo_minus_E_star": {
            "exact": fs(diff_exact), "float_exact_decimal": float(diff_exact),
            "float64_subtraction": diff_float,
            "float64_note": "float64 减法 Sterbenz 精确（两操作数同数量级）——"
                            "差值为两 float64 之差的真实值；与十进制精确差的"
                            "偏离源于 float64 解析（≪ulp）",
            "rule_margin_factor": float(Fr(1, 10 ** 6) / diff_exact),
            "note": "Ē_lo 超九位参考 E*=25.759986531 达 2.69832e-10——≪1e-6 "
                    "铁律容差 ~3700×（float 精确算术亲证）",
            "tier": "interval_certified_numeric",
        },
        "composite_proposition": {
            "statement": "链假设（∀ 次水平集构型 Y：d_P(Y) ≤ C_X·ρ）＋ "
                         "C_X·ρ ≤ r_eff ⟹ E(Y) ≥ Ē_lo − γ²/(2·μ_lo)"
                         "（float64 粒度下 E(Y) ≥ Ē_lo）",
            "basis": "l6_intube 二次增长证书 E(Y) ≥ Ē − γ·d(Y) + "
                     "(μ/2)·d(Y)²（d(Y) ≤ r* 球内，模 SO(3)）；对 d 极小化"
                     "得底座 Ē − γ²/(2μ)",
            "gamma": {"exact": fs(gam), "float": float(gam),
                      "tier": "interval_certified_numeric"},
            "mu_lo": {"exact": fs(mu_lo), "float": float(mu_lo),
                      "tier": "interval_certified_numeric",
                      "note": "μ(r*)_lo——方向安全：r* 球证书 a fortiori 覆盖"
                              "子球 r_eff=r*−δ_orb<r*（μ 随 r 降同向：箱 31 "
                              "μ_lo=0.0313＞箱 32 μ_lo=0.0065＞箱 33 上端 "
                              "−0.0206）"},
            "quadratic_floor_correction": {
                "exact": fs(corr), "float": float(corr),
                "below_float64_ulp": True,
                "note": "γ²/(2μ_lo)——低于 Ē 的 float64 ulp（~3.55e-15）约三个"
                        "数量级（2⁻⁴⁸/corr=1448.5×=3.16 个数量级，D94 勘正）⟹ "
                        "float 粒度命题 E ≥ Ē_lo 成立（诚实细注）"},
            "wouldBe_consistency": {
                "archived": wb,
                "equals_E_star": True,
                "composite_floor_above_reference": True,
                "note": "复合底座 Ē_lo 高于参考值 E* ⟹ wouldBe_if_chain_closed"
                        "==E*（记账定义值）保守——不改账本（诚实注记）",
            },
        },
        "demand_face_zero_slack": {
            "r32_is_rstar": {
                "bin_law": l6["binning"]["law"],
                "bin_k": 32,
                "r32_exact": fs(r32),
                "equals_R_MAX_over_16": True,
                "equals_rigorousRadius": True,
                "equals_bins31_r": True,
                "note": "rigorousRadius 恰为箱 32 半径（r_32=R_MAX/16=="
                        "950125/10⁸ 精确 Fraction 亲证；全 48 箱对定律 8 位"
                        "有效舍入带逐箱复验）",
            },
            "adjacent_bin": {
                "bin_k": 33,
                "r33": {"archived": bins[32]["r"],
                        "recomputed_interval": [fs(r33_lo), fs(r33_hi)],
                        "recomputed_float": float(r33_lo),
                        "ratio_vs_rstar": float(r33_lo / r32),
                        "note": "r_33 = r*·2^{1/4}（=R_MAX·2^{−15/4}）——200-bit"
                                " 双层有理平方根包络重导，存档 8 位有效串在"
                                "舍入窗内"},
                "mu_upper_archived": l6["negativeControls"]
                                          ["doubleRadiusControl"]
                                          ["adjacentBinMuUpper"],
                "mu_upper_bins_exact": fs(mu33[1]),
                "mu_upper_leq_zero": True,
                "note": "相邻箱 33 μ 上端 ≤0（adjacentBinMuUpper==bins[32].mu "
                        "上端 9 位舍入）⟹ 需求半径不可经既有证书上松——闭合"
                        "负担全在 L3 供给（R20 结论定量强化）",
            },
            "competitor_exclusion": {
                "interval_str": qg["competitorExclusionRadius"],
                "hi_vs_r_eff": float(Fr(dexcl[1]) / r_eff),
                "note": "排除半径 [3.8519e-8,5.4901e-8] ≪ r_eff（比值 ~5.8e-6）"
                        "——排除面不构成缝瓶颈，维持注记",
            },
        },
    }

    # ---------------- 6) (D) 判定
    verdict = {
        "chain_closed": False,
        "binding": "L3 供给双门（辨识门 floor 2.5157×＋球门 num 72.93×/A "
                   "92.92×/B 161.92×）",
        "statement": "全存档供给点（七阶梯点＋M9 括带两端）双门全败（辨识门"
                     "比值 ≥2.5157×、球门比值 ≥72.93×，全部 ≥2×/≥70× 宽安全"
                     "边定向断言）⇒ chain_closed=False——与 R20 seam_closed="
                     "False 一致（细化非反转：缝会计单门升级双门＋ε 需求外推 "
                     "3.37e-18＋L6 能量底座复合 Ē_lo−E*=2.69832e-10＋需求面"
                     "零余量 r_32==r*）；binding=L3 供给双门",
        "consistency": {
            "r20_seam_closed": r20["verdict"]["seam_closed"],
            "endgameChain_closed": end["endgameChain"]["closed"],
            "endgameChain_blocking": end["endgameChain"]["blocking"],
        },
    }
    require(end["endgameChain"]["closed"] is False
            and end["endgameChain"]["blocking"] == ["L0", "L3"],
            "endgameChain 存档判定前提漂移（closed/blocking）")

    # ---------------- 7) 账本组装（确定性：零时间戳零 code_version）
    doc = {
        "kind": "n9-r21-chain-assembly",
        "task": "r21a-chain-assembly-probe",
        "seed": SEED,
        "heavy_solves": 0,
        "schema": {
            "tiers_vocabulary": list(TIERS),
            "tier_semantics": {
                "formal_lean": "TableB5Data/TableB5Uncond 精确 ℚ 常数与定理"
                               "（Lean；本件经 r20 账本直读携带）",
                "written_proof_fraction": "严格数值层精确 Fraction（书面证明"
                                          "非 Lean）",
                "interval_certified_numeric": "区间证书数值层（非 Lean）",
                "rejection_certified_numeric": "证书拒绝面（负对照在档）",
                "float_advisory": "未认证数值输入（如实标注，不入精确断言——"
                                  "只入宽安全边 ≥2× 定向断言）"},
            "determinism": ("零随机零时间戳零 code_version；sort_keys＋"
                            "indent=1——G2 重跑逐位一致的充分条件"),
            "artifact_class": ("数值面审计件（audit artifact）：不入 endgame"
                               ".json/citedCertificates/12 分区、不得成为 "
                               "endgame_chain.py 输入（R11C–R20 先例，D86 "
                               "裁决 1／D90 裁决 1）"),
            "rounding_policy": "阈值 floor 向 6 位有效数字（报小仍充分）；"
                               "比值 ceil 向（报大不低于真值）；float_advisory "
                               "输入只入 ≥2× 宽安全边定向断言",
        },
        "provenance": {
            "read_only": True,
            "E_star": "25.759986531（thomson-workflow/data/energies.json，"
                      "只读）",
            "inputs": {
                "numerics/bounds/results/r20_l5l6_seam.json": {
                    "sha256": sha256_of(R20_JSON),
                    "role": "供给常数/需求面/缝表 12 行直读源（R20A 产物）"},
                "numerics/bounds/results/tube.json": {
                    "sha256": sha256_of(TUBE_JSON),
                    "role": "辨识门阈值（half_gap/need）＋ε 阶梯（AAA/verdict）"},
                "numerics/bounds/results/l6_intube.json": {
                    "sha256": sha256_of(L6_JSON),
                    "role": "Ē 区间/γ/μ/分箱定律/负对照（L6 能量底座与需求面）"},
                "numerics/bounds/results/endgame.json": {
                    "sha256": sha256_of(ENDGAME_JSON),
                    "role": "wouldBe_if_chain_closed 记账值（只读交叉）"},
                "numerics/bounds/results/l2_rigorous.json": {
                    "sha256": sha256_of(L2_JSON),
                    "role": "eps_forcing 精确 Fraction（M9 口径）"},
            },
            "frozen_anchors": {
                "endgame_json_sha256":
                    "86863a09bf84e950e85fc5f902bc2b4046a87f06703bd782e5148fc119afd69f",
                "tableb5uncond_sha256":
                    "c79fc6231d1e13b8ffd7873d1338901602ed3b70b3f057ed4eec4eb757e36d5e",
                "tableb5polar_sha256":
                    "d8c58f7d2c56c39fbe1ae62d634fc6ea5bd585fa9f1c0b9c2e2fc909d4338516",
            },
        },
        "supply": supply,
        "demand": demand,
        "dual_gate": dual_gate,
        "epsilon_chain": epsilon_chain,
        "l6_composite": l6_composite,
        "verdict": verdict,
    }

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(doc, ensure_ascii=False, indent=1,
                                   sort_keys=True))
    log(f"[done ] {out_path}；chain_closed=False（binding=L3 供给双门）；"
        "exit 0")


if __name__ == "__main__":
    main()
