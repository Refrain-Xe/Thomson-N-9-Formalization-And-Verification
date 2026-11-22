#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r8c3_l2m9_gate.py — R8A 验收门：L2 ε_forcing 换 cap M9 口径重算（D29 裁决 3）。

任务书口径（seed 20261010，裸 python3，CWD 无关，负对照全触发）：

  G1  l2_rigorous.json inputs/params 指 M9 证书且在盘可 --verify-cert；
  G2  ε_forcing 新值门内独立 Fraction 复算（零 import 仓库路径，全自写：解析
      证书 dyadic 数据重推 (1+R2max)·E*−e_dy+defl 双口径）与存档逐位相等；
  G3  11 项 asserts 全真；门侧独立复核其中机器可核的机械部分：38 块 PSD
      LDLᵀ（自写无主元 LDLᵀ）、归一化残差 0、minorant 有理点抽查（含 ŵ²≥b²）；
      typed 恒等式/引理 4.1 正性（随机有理构型）系 l2_rigorize 本会话实跑产物，
      门侧记 archive_attested（其重算需全商环装配，非自写可短路径——如实分层）；
  G4  新值 0 < ε < 4.153454e-4（旧 M8 口径严格值上界）＋量级预测带
      [1.2e-4, 1.7e-4] 记录（带外如实记、不拦门）；
  G5  l3_analytic 重跑幂等（sha256 两跑一致）＋四门全过＋caliber(a) eps 与 l2
      逐位相等（失联必检出）＋ρ_capped 公式独立重算（逐 cellrad/√(ε/C) 分支，
      纯 Fraction 比较）＋ρ 随 √ε 单调（原始口径）；
  G6  endgame.json：L2 quant 含新精确分数、closed==false、assembledRecord
      分数串逐位不变（47517790735835014335570/1844674407417822803119）、
      spliceMapVerdict==维持 v2；L3 口径串「仍旧 cap 口径未重算」待刷新标注
      已解除（endgame_chain.py 牵动文案同步）；
  G7  decisions.md D29/D30 在档；
  G8  交付清单提交状态：独占文件须干净；共文件（endgame_chain.py＝R8A/R8C
      共面、notes/decisions.md＝整文件 add 防撞先例）判据改为「R8A 标记已入
      HEAD 且工作面存活」——并行会话在途 hunks/裁决节如实报告、不属本门拦截
      （防撞分工 D29 任务结构）；全树状态随 detail 报告。

  负对照（全触发才过门）：
    NC1  /tmp 副本 l2_rigorous.json 的 eps_forcing.exact 篡改 +1e-9
         ⇒ 子门（--l2-json 指副本）G2 独立复算失配 exit 1；
    NC2  /tmp 副本 l3_analytic.json 的 caliber(a) eps 与 l2 失联（减半）
         ⇒ 子门（--l3-json 指副本）G5 耦合检查检出 exit 1；
    NC3  M8 证书冒充 M9（/tmp 镜像树：M8 证书内容置于 …_M9.json 路径）
         ⇒ l2_rigorize.py params 断言 AssertionError 亲跑复核（exit ≠ 0）
         ＋门侧 params 校验函数同判据检出。

CWD 无关：全部路径自 __file__ 推导。裸 python3：门本体纯标准库；子进程调用
仓库脚本（typed_ladder --verify-cert / l3_analytic / 镜像 l2_rigorize）用
sys.executable。本门不重解任何 SDP、不改写任何仓库文件（l3_analytic 幂等
重跑不触发重写——其核心与存档一致时零写入）。
"""
from __future__ import annotations

import argparse
import json
import math
import random
import shutil
import subprocess
import sys
import tempfile
import time
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]                       # …/thomson-n9
RESULTS = HERE / "results"

SEED = 20261010                              # 任务书固定种子
LO = Fr(-187, 250)                           # m0748 档切口
CAP_M, CAP_K = 9, 6
D_H = 2 * CAP_M - 2                          # 16
DEG_P = 2 * D_H + 1                          # 33
B2 = (1 - LO) / 2                            # 437/500
E_DEC = Fr("25.759986531")                   # 十进制口径（D28 裁决 3 主口径）
E_BIN = Fr(25.759986531)                     # 二进制 double 精确值（load_E_star 同式）

CERT_REL = "certificates/n9-stage-a4-typedcap-m0748_M9.json"
L2_DEFAULT = RESULTS / "l2_rigorous.json"
L3_DEFAULT = RESULTS / "l3_analytic.json"
ENDGAME = RESULTS / "endgame.json"
DECISIONS = REPO / "notes" / "decisions.md"

# M8 口径基线（变更检测参考常量；出处 git 存档 l2_rigorous.json / l3_analytic.json
# @368fb89〔R7 终态〕，同 endgame_chain.R7_ASSEMBLED 常量先例。ε 旧值用存档
# float 字面值（0.0004153453999019569）——本门对该值只做 √ε 单调性比值检查
# （容差 1e-9 相对），float 精度充分且免手抄 84 位分数引入誊写风险）
EPS_M8_OLD_FLOAT = 0.0004153453999019569
RHO_CAPPED_M8_OLD = Fr(644725833, 10 ** 9)   # l3@368fb89 caliber_a ρ_capped（0.6447 平台）
ASSEMBLED_R7 = "47517790735835014335570/1844674407417822803119"   # R7_ASSEMBLED 同值

ASSERT11 = ("psd_all_blocks", "normalization_zero", "residuals_match_provenance",
            "certified_bitwise_equal", "identity_residual_zero",
            "positivity_spotcheck", "minorant_spotchecks", "w_hat_covers_domain",
            "swap_l1_preserved", "numerical_ledger_reproduced",
            "rigorous_le_ledger_plus_omitted_term")

F0, F1 = Fr(0), Fr(1)


# ============================================================ 自写精确线性代数
def ldl_pivot_free(A):
    """无主元交换 LDLᵀ（Fraction）：返回 D 对角列表；零主元 ⇒ None。

    与 thomson_certs.exact.is_positive_definite 同判据（对称阵正定 ⟺ 分解可
    完成且 D 全正）——本函数为门内独立实现（零 import 仓库路径）。
    """
    n = len(A)
    L = [[F0] * n for _ in range(n)]
    D = []
    for j in range(n):
        d = A[j][j] - sum(D[k] * L[j][k] * L[j][k] for k in range(j))
        if d == 0:
            return None
        for i in range(j + 1, n):
            L[i][j] = (A[i][j] - sum(D[k] * L[i][k] * L[j][k]
                                     for k in range(j))) / d
        D.append(d)
    return D


def is_pd(A):
    D = ldl_pivot_free(A)
    return D is not None and all(d > 0 for d in D)


def ceil_sqrt_rat(x: Fr) -> Fr:
    """typed_ladder.py:222 同式（ceil √x 于分母不变的有理实现）。"""
    p, q = x.numerator, x.denominator
    s = math.isqrt(p * q)
    return Fr(s if s * s == p * q else s + 1, q)


W_HAT = ceil_sqrt_rat(B2)


# ============================================================ minorant 自写重推
def cp_tables():
    """Cp/p_const（typed_ladder.QuotientMaps minorant_rhs 同式）。"""
    Csub = [[F0] * (D_H + 1) for _ in range(DEG_P + 1)]
    for i in range(D_H + 1):
        for m_ in range(i + 1):
            Csub[2 * m_][i] += Fr(math.comb(i, m_) * ((-2) ** m_))
    Cp = [[F0] * (D_H + 1) for _ in range(DEG_P + 1)]
    for r in range(1, DEG_P + 1, 2):
        Cp[r] = [-2 * x for x in Csub[r - 1]]
    p_const = [F0] * (DEG_P + 1)
    p_const[0] = F1
    return Cp, p_const


SIG_DEF = (("sig0", list(range(0, D_H + 1)), ((0, F1),)),
           ("sig1", list(range(0, D_H + 1)), ((1, F1),)),
           ("sig2", list(range(0, D_H)), ((0, B2), (2, Fr(-1)))),
           ("sig3", list(range(0, D_H)), ((1, B2), (3, Fr(-1)))))

CP, P_CONST = cp_tables()


def minorant_rhs(h):
    return [sum(CP[r][j] * h[j] for j in range(D_H + 1)) + P_CONST[r]
            for r in range(DEG_P + 1)]


def minorant_lhs(Sblocks):
    out = [F0] * (DEG_P + 1)
    for _name, mons_y, mult in SIG_DEF:
        S = Sblocks[_name]
        m = len(mons_y)
        for p_ in range(m):
            row = S[p_]
            for q_ in range(m):
                c = row[q_]
                if c == 0:
                    continue
                base = mons_y[p_] + mons_y[q_]
                for (eg, cg) in mult:
                    out[base + eg] += c * cg
    return out


def derive_R2_from_cert(cert: dict):
    """R2_AA/R2_AB/R2max 自证书 dyadic 块（h/σ）自写重推。"""
    b = cert["blocks"]
    R2 = {}
    for cls, hkey in (("AA", "h_AA_diag"), ("AB", "h_AB_diag")):
        h = [Fr(s) for s in b[hkey]]
        assert len(h) == D_H + 1, (hkey, len(h))
        S = {nm: [[Fr(x) for x in row] for row in b[f"sig_{cls}_{nm}"]]
             for (nm, _m, _mm) in SIG_DEF}
        rr = [x - y for x, y in zip(minorant_rhs(h), minorant_lhs(S))]
        R2[cls] = sum(abs(rr[j]) * W_HAT ** j for j in range(len(rr)))
    return R2, max(R2.values())


# ============================================================ 检查框架
class Gate:
    def __init__(self):
        self.checks = []

    def chk(self, name, ok, detail=""):
        self.checks.append((name, bool(ok), str(detail)))
        print(f"[{'OK ' if ok else 'FAIL'}] {name}"
              + (f"：{detail}" if detail else ""), flush=True)
        return bool(ok)

    def exit_code(self):
        return 0 if all(ok for _n, ok, _d in self.checks) else 1


def load(p: Path):
    return json.loads(p.read_text())


def sha256(p: Path) -> str:
    import hashlib
    return hashlib.sha256(p.read_bytes()).hexdigest()


# ============================================================ 主流程
def main() -> int:
    ap = argparse.ArgumentParser(description="R8A l2-m9-recalc 验收门（seed %d）" % SEED)
    ap.add_argument("--l2-json", default=str(L2_DEFAULT),
                    help="l2_rigorous.json 路径（NC1 子门指向 /tmp 篡改副本）")
    ap.add_argument("--l3-json", default=str(L3_DEFAULT),
                    help="l3_analytic.json 路径（NC2 子门指向 /tmp 篡改副本）")
    ap.add_argument("--skip-slow", action="store_true",
                    help="跳过重 IO 子检查（--verify-cert 子进程/l3 二跑）——"
                         "仅 NC 子门内部使用")
    ap.add_argument("--no-nc", action="store_true", help="跳过负对照（NC 子门用）")
    args = ap.parse_args()
    t0 = time.time()
    g = Gate()
    l2_path = Path(args.l2_json)
    l3_path = Path(args.l3_json)
    rng = random.Random(SEED)

    # ---------------- G1：inputs/params 指 M9 ＋ --verify-cert
    l2 = load(l2_path)
    inp = l2.get("inputs", {})
    g.chk("G1_inputs_certificate_is_M9",
          inp.get("certificate") == CERT_REL,
          f"inputs.certificate = {inp.get('certificate')}")
    cert_p = REPO / CERT_REL
    g.chk("G1_cert_on_disk", cert_p.exists(), str(cert_p))
    cert = load(cert_p)
    prm = cert.get("params", {})

    def params_ok(params: dict) -> tuple:
        """M9 冒充检（判据与 l2_rigorize.rebuild_certificate 断言同式）。"""
        try:
            return (Fr(params["a0"]) == LO and params["M"] == CAP_M
                    and params["K"] == CAP_K), dict(params)
        except (KeyError, ValueError, ZeroDivisionError):
            return False, dict(params)

    pok, pval = params_ok(prm)
    g.chk("G1_cert_params_M9", pok, f"params = {pval}")
    if not args.skip_slow:
        r = subprocess.run([sys.executable, "numerics/bounds/typed_ladder.py",
                            "--verify-cert", CERT_REL], cwd=str(REPO),
                           capture_output=True, text=True, timeout=1800)
        g.chk("G1_verify_cert_exit0", r.returncode == 0,
              (r.stdout or r.stderr).strip().splitlines()[-1][:160] if
              (r.stdout or r.stderr).strip() else f"exit={r.returncode}")

    # ---------------- G2：ε_forcing 双口径独立复算（零 import 自写）
    R2_derived, R2max_derived = derive_R2_from_cert(cert)
    prov = cert["provenance"]["residuals"]
    prov_R2max = Fr(prov["R2max"])
    g.chk("G2_R2max_rederived_bitwise", R2max_derived == prov_R2max,
          f"重推 {float(R2max_derived):.6e} vs provenance {float(prov_R2max):.6e}")
    e_dy = Fr(cert["blocks"]["e"][0])
    defl_prov = Fr(prov["defl"])
    claimed = Fr(cert["claimed_bound"])
    # defl 独立钉扎：claimed == (e−defl)/(1+R2max) ⇔ defl == e − claimed·(1+R2max)
    defl_id = e_dy - claimed * (1 + R2max_derived)
    g.chk("G2_defl_pinned_by_claimed_identity", defl_id == defl_prov,
          f"provenance {float(defl_prov):.6e} vs 恒等式 {float(defl_id):.6e}")
    # defl 权重核对（counts：AAA 3×1 / AAB 6×9 / ABC 1×27）
    R1p = {o: Fr(v) for o, v in prov["R1"].items()}
    defl_w = 3 * 1 * R1p["AAA"] + 6 * 9 * R1p["AAB"] + 1 * 27 * R1p["ABC"]
    g.chk("G2_defl_weights_match_counts", defl_w == defl_prov,
          f"Σ_counts·R1 = {float(defl_w):.6e}")
    eps_dec = (1 + R2max_derived) * E_DEC - e_dy + defl_prov
    eps_bin = (1 + R2max_derived) * E_BIN - e_dy + defl_prov
    arch_dec = Fr(l2["eps_forcing"]["exact"])
    g.chk("G2_eps_decimal_bitwise", eps_dec == arch_dec,
          f"复算 {float(eps_dec):.12e} vs 存档 {float(arch_dec):.12e}")
    arch_bin_s = l2["eps_forcing"].get("exact_binary_caliber")
    g.chk("G2_eps_binary_bitwise",
          arch_bin_s is not None and eps_bin == Fr(arch_bin_s),
          f"复算 {float(eps_bin):.12e} vs 存档 {arch_bin_s}")
    g.chk("G2_identity_eq_1pR2max_times_gap",
          eps_dec == (1 + R2max_derived) * (E_DEC - claimed),
          "ε == (1+R2max)·(E*−certified)（certified=claimed 逐位）")

    # ---------------- G3：11 asserts ＋ 机械部分门侧独立复核
    a2 = l2.get("asserts", {})
    bad = [k for k in ASSERT11 if a2.get(k) is not True]
    g.chk("G3_asserts_11_all_true", not bad,
          "11/11 全真" if not bad else f"缺真：{bad}")
    g.chk("G3_identity_positivity_archive_attested",
          a2.get("identity_residual_zero") is True
          and a2.get("positivity_spotcheck") is True
          and l2.get("typed_identity", {}).get("residual", "").startswith("0"),
          "typed 恒等式/正性＝l2_rigorize 本会话随机有理构型实跑（archive attested；"
          "门侧重算需全商环装配，非自写短路径——如实分层）")
    blk = cert["blocks"]
    mats = {f"F{k}": [[Fr(x) for x in row] for row in blk[f"F{k}"]]
            for k in range(CAP_K)}
    mats.update({k2: [[Fr(x) for x in row] for row in m]
                 for k2, m in blk.items() if k2.startswith("B_")})
    mats.update({k2: [[Fr(x) for x in row] for row in m]
                 for k2, m in blk.items() if k2.startswith("sig_")})
    g.chk("G3_psd_block_count_38", len(mats) == 38, f"{len(mats)} 块")
    n_pd = sum(1 for mmm in mats.values() if is_pd(mmm))
    g.chk("G3_psd_all_38_blocks_gate_side", n_pd == len(mats) == 38,
          f"自写 LDLᵀ 正定 {n_pd}/{len(mats)}")
    f_sizes = [len(mats[f"F{k}"]) for k in range(CAP_K)]
    g.chk("G3_F_sizes_M_minus_k", f_sizes == [CAP_M - k for k in range(CAP_K)],
          str(f_sizes))
    s111 = sum(sum(r) for r in mats["F0"])
    nrm = (3 * Fr(blk["c_A"][0]) + 54 * Fr(blk["c_B"][0])
           + 27 * Fr(blk["c_C"][0]) - e_dy - 9 * s111)
    g.chk("G3_normalization_zero", nrm == 0, f"3c_A+54c_B+27c_C−e−9ΣF⁰ = {nrm}")
    g.chk("G3_w_hat_covers", W_HAT ** 2 >= B2,
          f"ŵ={W_HAT}，ŵ²={float(W_HAT**2):.9f} ≥ b²={float(B2):.9f}")
    pts = [LO, (LO + 1) / 2, Fr(-1, 2), Fr(-3, 4), Fr(-3, 5), F0,
           Fr(1, 4), Fr(1, 2), Fr(3, 4), Fr(995, 1000)]
    pts += [Fr(rng.randint(-1870, 999), 1000) for _ in range(8)]  # seed 20261010
    n_chk = n_bad = 0
    for cls, hkey in (("AA", "h_AA_diag"), ("AB", "h_AB_diag")):
        h = [Fr(s) for s in blk[hkey]]
        for tp in pts:
            if not (LO <= tp < 1):
                continue
            Ht = sum(h[j] * tp ** j for j in range(len(h)))
            n_chk += 1
            if Ht > 0 and (2 - 2 * tp) * Ht * Ht > (1 + R2_derived[cls]) ** 2:
                n_bad += 1
    g.chk("G3_minorant_spotchecks_gate_side", n_bad == 0,
          f"(2−2t)H² ≤ (1+R2)² 有理点 {n_chk} 点全过（含 seed 抽样 8 点）")

    # ---------------- G4：量级门
    UPPER_M8 = Fr("0.0004153454")            # 任务书上界（M8 严格值 6 位舍入）
    g.chk("G4_eps_in_range", F0 < eps_dec < UPPER_M8,
          f"0 < {float(eps_dec):.9e} < {float(UPPER_M8):.6e}")
    in_band = Fr(12, 10 ** 5) <= eps_dec <= Fr(17, 10 ** 5)
    g.chk("G4_prediction_band_recorded", True,
          f"预测带 [1.2e-4, 1.7e-4]：{'带内 ✓' if in_band else '带外（如实记，不拦门）'}"
          f"（本门 G4 量级门已过）")

    # ---------------- G5：l3 幂等重跑 ＋ 耦合 ＋ ρ 公式独立重算
    l3 = load(l3_path)
    if args.skip_slow or l3_path != L3_DEFAULT:
        g.chk("G5_l3_rerun_idempotent", True,
              "（--skip-slow/--l3-json 模式：跳过二跑，仅耦合检查——NC 子门内部路由）")
    else:
        shas = []
        exits = []
        for _ in range(2):
            r = subprocess.run([sys.executable, "numerics/bounds/l3_analytic.py"],
                               cwd=str(REPO), capture_output=True, text=True,
                               timeout=1800)
            exits.append(r.returncode)
            shas.append(sha256(L3_DEFAULT))
        g.chk("G5_l3_rerun_idempotent",
              exits == [0, 0] and shas[0] == shas[1],
              f"两跑 exit={exits} sha256 一致={shas[0] == shas[1]}"
              f"（{shas[0][:16]}…）")
        l3 = load(L3_DEFAULT)
        gates_l3 = l3.get("gates", {})
        g.chk("G5_l3_four_gates_pass",
              bool(gates_l3) and all(v.get("passed") is True for v in gates_l3.values()),
              str({k: v.get("passed") for k, v in gates_l3.items()}))
    ca = l3["chain_L2_L3_L5_L6"]["caliber_a"]
    g.chk("G5_caliber_a_eps_couples_l2", Fr(ca["eps"]) == arch_dec,
          f"caliber(a) ε={float(Fr(ca['eps'])):.9e} vs l2 {float(arch_dec):.9e}")
    ic = l3["interval_constants"]
    fg = ic["per_cell_C"]["flat_global"]
    cells = ic["cells"]
    capped_ok = True
    capped_detail = []
    rad_binding = []
    for e2 in fg:
        k = e2["k"]
        C = Fr(e2["C_k"])
        rad = Fr(cells[k]["cellrad"])
        if eps_dec / C > rad * rad:          # √(ε/C) > cellrad（纯 Fraction 比较）
            capped_detail.append((k + 1, "cellrad"))
            rad_binding.append(rad)
        else:
            capped_detail.append((k + 1, "sqrt"))
            capped_ok = False                # √ 分支绑定 ⇒ 需有理 √ 上界才能精确
    rho_capped_arch = Fr(ca["delta_gram_upper"])
    rho_capped_rho_spec = Fr(l3["rho_spec"]["caliber_a_current_ledger"]["rho_capped"])
    g.chk("G5_rho_capped_two_ledger_fields_agree",
          rho_capped_arch == rho_capped_rho_spec,
          f"chain.delta_gram_upper == rho_spec.rho_capped = {float(rho_capped_arch):.9f}")
    rho_capped_re = max(rad_binding) if rad_binding else None
    g.chk("G5_rho_capped_recomputed",
          capped_ok and rho_capped_re is not None
          and rho_capped_re == rho_capped_arch,
          f"逐 cell 分支 {capped_detail} ⇒ max(cellrad) = "
          f"{float(rho_capped_re) if rho_capped_re is not None else '∅':.9f}"
          f" vs 存档 {float(rho_capped_arch):.9f}（全 cellrad 分支绑定 ⇒ 平台值）")
    C_min = Fr(ic["C_min"]["flat_global"])
    raw_new = math.sqrt(float(eps_dec / C_min))
    raw_old = math.sqrt(EPS_M8_OLD_FLOAT / float(C_min))
    raw_arch = l3["rho_spec"]["caliber_a_current_ledger"]["rho_raw_float"]
    g.chk("G5_rho_raw_follows_sqrt_eps",
          abs(raw_new / raw_arch - 1) < 1e-9 and raw_new < raw_old,
          f"√(ε/C_min) 复算 {raw_new:.6f} ≈ 存档 ρ_raw {raw_arch:.6f}；"
          f"M8→M9 √ε 单调下降 {raw_old:.6f}→{raw_new:.6f}"
          f"（×{raw_new/raw_old:.5f}=√(ε_new/ε_old)）")
    g.chk("G5_rho_capped_monotone_nondecreasing_eps",
          rho_capped_arch <= RHO_CAPPED_M8_OLD,
          f"ρ_capped {float(rho_capped_arch):.9f} ≤ M8 口径 {float(RHO_CAPPED_M8_OLD):.9f}"
          f"（相等＝cellrad 平台绑定，单调不增成立；预测带 0.37–0.40 系对绑定分支"
          f"误设——带外如实记，ρ_raw 已按 √ε 收缩）")

    # ---------------- G6：endgame.json 判定
    eg = load(ENDGAME)
    ec = eg["endgameChain"]
    l2q = next(c for c in ec["components"] if c["id"] == "L2")["quant"]
    g.chk("G6_l2_quant_contains_exact_fraction", str(arch_dec) in l2q,
          l2q[:130] + "…")
    g.chk("G6_closed_false", ec["closed"] is False, f"closed = {ec['closed']}")
    g.chk("G6_blocking_L0_L3", ec["blocking"] == ["L0", "L3"], str(ec["blocking"]))
    g.chk("G6_assembled_record_unchanged",
          eg["assembledRecord"]["value"] == ASSEMBLED_R7,
          eg["assembledRecord"]["value"])
    smv = eg.get("spliceMapVerdict", {})
    g.chk("G6_splice_map_keeps_v2",
          smv.get("assembled_equal_R7") is True and "维持 v2" in str(smv.get("verdict")),
          str(smv.get("verdict"))[:80])
    l3m = next(c for c in ec["components"] if c["id"] == "L3")["missing"] or ""
    g.chk("G6_l3_pending_refresh_annotation_lifted",
          "仍旧 cap 口径未重算" not in l3m and "已换 cap M9 口径" in l3m,
          "「待刷新」标注已解除（endgame_chain.py 牵动文案同步）")

    # ---------------- G7：decisions.md D29/D30
    dec = DECISIONS.read_text(encoding="utf-8")
    g.chk("G7_decisions_D29_D30",
          "### D29" in dec and "### D30" in dec,
          "D29（设计）＋D30（R8A 执行留痕）均在档")

    # ---------------- G8：交付清单提交状态
    deliverables = [
        "numerics/bounds/l2_rigorize.py", "numerics/bounds/l3_analytic.py",
        "numerics/bounds/endgame_chain.py", "numerics/bounds/r8c3_l2m9_gate.py",
        "thomson-n9/numerics/bounds/r8c3_l2m9_gate.py",
        "numerics/bounds/results/l2_rigorous.json",
        "numerics/bounds/results/l3_analytic.json",
        "numerics/bounds/results/endgame.json", "notes/decisions.md"]
    # endgame_chain.py 系 R8A/R8C 共文件（D29 任务结构并行分工）：R8C 在途
    # hunks（v2 探针消费面）不属本门拦截——本门判据＝R8A 唯一追加（L2 quant
    # 精确分数插值）已入 HEAD 且工作面仍存活（未被并行改写移除）。
    # notes/decisions.md 同为共文件（D22 裁决 4③ 整文件 add 防撞先例——并行
    # 会话追加其裁决节不拦本门）：判据＝D30 节已入 HEAD 且工作面存活。
    co_owned = {"numerics/bounds/endgame_chain.py": "eps_exact}；口径＝",
                "notes/decisions.md": "### D30"}
    st = [ln.rstrip() for ln in subprocess.run(
        ["git", "status", "--porcelain"], cwd=str(REPO),
        capture_output=True, text=True).stdout.splitlines() if ln.strip()]
    mine = [ln for ln in st if ln[3:] in deliverables and ln[3:] not in co_owned]
    co_ok = True
    co_detail = []
    for rel, marker in sorted(co_owned.items()):
        head = subprocess.run(["git", "show", f"HEAD:{rel}"], cwd=str(REPO),
                              capture_output=True, text=True)
        head_ok = head.returncode == 0 and marker in head.stdout
        live_ok = (REPO / rel).exists() and marker in (REPO / rel).read_text(
            encoding="utf-8")
        co_ok = co_ok and head_ok and live_ok
        co_detail.append(f"{rel.split('/')[-1]}：HEAD 含 R8A 标记={head_ok}，"
                         f"工作面存活={live_ok}")
    others = [ln for ln in st
              if ln[3:] not in deliverables and ln[3:] not in co_owned]
    g.chk("G8_deliverables_committed", not mine and co_ok,
          f"独占清单 {'干净' if not mine else '在途: ' + str([ln[3:] for ln in mine])}；"
          f"共文件 {co_detail}；并行会话在途 {len(others)} 项（R8B/R8C 面，不属"
          f"本门拦截——防撞分工见 D29 任务结构）：{[ln[3:] for ln in others][:6]}")

    # ---------------- 负对照（默认路径才跑；NC 子门 --no-nc 防递归）
    if not args.no_nc:
        tmp = Path(tempfile.mkdtemp(prefix="r8c3_nc_"))
        # NC1：eps 篡改 +1e-9 ⇒ G2 失配
        n1 = tmp / "l2_tampered.json"
        doc1 = load(l2_path if l2_path.exists() else L2_DEFAULT)
        doc1["eps_forcing"]["exact"] = str(Fr(doc1["eps_forcing"]["exact"])
                                           + Fr(1, 10 ** 9))
        n1.write_text(json.dumps(doc1, ensure_ascii=False, indent=1))
        r1 = subprocess.run([sys.executable, str(Path(__file__).resolve()),
                             "--l2-json", str(n1), "--skip-slow", "--no-nc"],
                            capture_output=True, text=True, timeout=1200)
        nc1_hit = (r1.returncode != 0
                   and any("G2_eps_decimal_bitwise" in ln and "FAIL" in ln
                           for ln in (r1.stdout or "").splitlines()))
        g.chk("NC1_tampered_eps_detected", nc1_hit,
              f"子门 exit={r1.returncode}，G2 失配检出")
        # NC2：l3 caliber(a) eps 减半 ⇒ G5 耦合检出
        n2 = tmp / "l3_tampered.json"
        doc2 = load(L3_DEFAULT)
        half = str(Fr(doc2["chain_L2_L3_L5_L6"]["caliber_a"]["eps"]) / 2)
        raw2 = json.dumps(doc2, ensure_ascii=False)
        old_eps_str = doc2["chain_L2_L3_L5_L6"]["caliber_a"]["eps"]
        raw2 = raw2.replace(old_eps_str, half)      # 全部出现处（chain+rho_spec）
        n2.write_text(raw2)
        r2 = subprocess.run([sys.executable, str(Path(__file__).resolve()),
                             "--l3-json", str(n2), "--skip-slow", "--no-nc"],
                            capture_output=True, text=True, timeout=1200)
        nc2_hit = (r2.returncode != 0
                   and any("G5_caliber_a_eps_couples_l2" in ln and "FAIL" in ln
                           for ln in (r2.stdout or "").splitlines()))
        g.chk("NC2_decoupled_l3_eps_detected", nc2_hit,
              f"子门 exit={r2.returncode}，G5 耦合失配检出")
        # NC3：M8 证书冒充 M9 ⇒ l2_rigorize params 断言 fail（/tmp 镜像亲跑）
        nc3_root = tmp / "m"
        bnd = nc3_root / "numerics" / "bounds"
        bnd.mkdir(parents=True)
        for f in HERE.glob("*.py"):
            shutil.copy(f, bnd / f.name)
        if (HERE / "typed").is_dir():
            shutil.copytree(HERE / "typed", bnd / "typed",
                            ignore=shutil.ignore_patterns("__pycache__"))
        (nc3_root / "certificates").mkdir()
        shutil.copy(REPO / "certificates" / "n9-stage-a4-typedcap-m0748_M8.json",
                    nc3_root / "certificates" / "n9-stage-a4-typedcap-m0748_M9.json")
        wf = tmp / "thomson-workflow"
        (wf / "certificates").mkdir(parents=True)
        (wf / "data").mkdir(parents=True)
        certs_link = wf / "certificates" / "thomson_certs"
        certs_link.symlink_to(REPO.parent / "thomson-workflow" / "certificates"
                              / "thomson_certs", target_is_directory=True)
        shutil.copy(REPO.parent / "thomson-workflow" / "data" / "energies.json",
                    wf / "data" / "energies.json")
        r3 = subprocess.run([sys.executable, "numerics/bounds/l2_rigorize.py"],
                            cwd=str(nc3_root), capture_output=True, text=True,
                            timeout=1200)
        nc3_hit = (r3.returncode != 0 and "AssertionError" in (r3.stderr or "")
                   and "params" in (r3.stderr or ""))
        pk8, _ = params_ok(load(REPO / "certificates"
                                / "n9-stage-a4-typedcap-m0748_M8.json")["params"])
        g.chk("NC3_m8_impersonation_params_fail", nc3_hit and pk8 is False,
              f"镜像亲跑 exit={r3.returncode}（params AssertionError）＋门侧判据"
              f"同检出（M8 params.M=8 ≠ 9）")
        shutil.rmtree(tmp, ignore_errors=True)

    # ---------------- 汇总
    all_ok = g.exit_code() == 0
    print(f"\n[{'PASS' if all_ok else 'FAIL'}] r8c3_l2m9_gate："
          + " ".join(f"{n}={'OK' if ok else 'FAIL'}" for n, ok, _ in g.checks)
          + f"（seed {SEED}，wall {time.time() - t0:.1f}s）")
    if not all_ok:
        sys.exit(1)
    return 0


if __name__ == "__main__":
    sys.exit(main())
