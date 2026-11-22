#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""verify_certificate.py — LP 下界证书的数值→精确桥接（dyadic 舍入 + 独立精确复核）。

输入：results/lp.json —— lp_bound.py 产出的 Yudin 两点 LP 下界的构造数据
（数值 LP 值 lp_raw、41 个 Legendre 系数的精确有理数；其中仅 ĉ_0 因 η 平移
非 dyadic，k≥1 系数已是 lp_bound 舍入过的 dyadic 有理数）。

本脚本【不信任 lp.json 的任何 checks 标志】，独立完成四步桥接：

  1) 舍入（安全方向 → dyadic）：全部系数向下取整到 2^-64 网格。floor 保持
     k≥1 系数 ≥ 0；c_0 下调 δ 只使 f 逐点变小（P_0=1），f ≤ φ 只会更容易成立。
  2) 精确重认证：在舍入后的系数上重新跑 lp_bound.certify 的纯 Fraction 分支
     定界 Taylor 扫描（同参数；产出 sup_{t∈[-1,1)}(f−φ) 的严格有理上界 M1，
     尾部 [1−2^-40,1) 由 Taylor 尾引理并入 M1）。若 M1 > 0（扫描上界不够紧），
     对 c_0 再做一次 dyadic 向下平移 c_0 ← floor_64(c_0 − (M1 + 2^-46))，使
     sup(f_cert − φ) ≤ −2^-46 < 0。两条路径的最终 sup 界都 ≤ 0，精确成立。
     另用 math.isqrt 的 φ 下界在有理点独立抽查 f_cert ≤ φ（不经扫描机制）。
  3) exact.py 复核（thomson-workflow/certificates/thomson_certs，纯标准库）：
     - K_f_test = [f_cert(x_i·x_j)]_{9×9}（9 个有理坐标测试点，内积有理）用
       is_positive_definite（无主元交换 LDLᵀ）验证严格正定——这是加法定理
       "c_k ≥ 0 ⇒ Σ_{i,j} f(x_i·x_j) ≥ N²c_0" 的 PSD 机制在具体构型上的实例
       复核（普遍命题本身是分析定理，不在机器验证范围内，见 provenance）；
     - 界值用纯 Fractions 两条独立途径重算并要求逐位相等：
       B = (N²ĉ_0 − N·f_cert(1))/2，其中 f_cert(1) 分别用 Σĉ_k（P_k(1)=1）
       与幂基 Horner 求值。
  4) 证书：按 schema.py 的 Certificate 格式写 certificates/n9-stage-a.json——
     41 个系数存为 41×41 对角块 f_coeffs_diag（下游可直接从对角线读回），
     K_f_test 存为 9×9 块；provenance 记录舍入损失（数值界 lp_raw − 精确界 B，
     精确有理数 + 浮点显示）、重认证扫描摘要与全部复核结果。

断言（任一违反打印原因并 sys.exit(1)）：
  k≥1 系数 ≥ 0；全部系数 dyadic（分母为 ≤ 2^64 的 2 的幂）；
  φ 有理点抽查全部通过；K_f_test 严格正定；
  0 ≤ B ≤ lp_raw（精确界 ≤ 数值界）；0 < B ≤ E* + 1e-6；
  证书 JSON 可 decode 且再编码逐字节一致。

用法（在 thomson-n9 下，用 numerics/.venv 的解释器——lp_bound 导入 numpy/scipy）：
  numerics/.venv/bin/python numerics/bounds/verify_certificate.py
  numerics/.venv/bin/python numerics/bounds/verify_certificate.py --round-bits 64
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]                                    # .../thomson-n9
WORKFLOW_CERTS = HERE.parents[2] / "thomson-workflow" / "certificates"
sys.path.insert(0, str(HERE))                             # 同目录的 lp_bound
sys.path.insert(0, str(WORKFLOW_CERTS))                   # thomson_certs（exact/schema）

import lp_bound                                           # noqa: E402 （复用其纯精确工具）
from thomson_certs.exact import is_positive_definite      # noqa: E402
from thomson_certs.schema import (                        # noqa: E402
    Certificate, decode_certificate, encode_certificate, fraction_to_str)

F0, F1 = Fraction(0), Fraction(1)

# 有理测试点（球面 S² 的有理坐标点，参数化 x(a,b)=(2a,2b,1−a²−b²)/(1+a²+b²)）：
# 用于 K_f_test 的实例正定性复核。9 点张成的调和函数维数 ≥ Σ_{k: c_k>0}(2k+1) ≥ 191。
TEST_AB = [(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1),
           (2, 1), (-2, 1), (1, -2), (3, 1)]

# φ 抽查点（有理数；t=-1 处 φ=1/2 精确已知，其余用 isqrt 下界）
SPOT_T = [-1, Fraction(-1, 2), 0, Fraction(1, 2), Fraction(4, 5),
          1 - Fraction(1, 2**16), 1 - Fraction(1, 2**30)]


def fail(msg: str) -> None:
    print(f"[FAIL] {msg}", flush=True)
    sys.exit(1)


def dyadic_floor(x: Fraction, bits: int) -> Fraction:
    """向下取整到 2^-bits 网格（安全方向：只减不增）。"""
    q = 1 << bits
    return Fraction((x.numerator * q) // x.denominator, q)


def is_dyadic(x: Fraction, bits: int) -> bool:
    d = x.denominator
    return d == 1 or (d <= (1 << bits) and (d & (d - 1)) == 0)


def rational_point(a, b):
    """x(a,b) = (2a, 2b, 1−a²−b²)/(1+a²+b²)，S² 上的有理坐标点。"""
    s = 1 + a * a + b * b
    return (2 * a / s, 2 * b / s, (1 - a * a - b * b) / s)


def main() -> None:
    ap = argparse.ArgumentParser(description="LP 下界的数值→精确桥接与证书生成")
    ap.add_argument("--lp", type=str, default=str(HERE / "results" / "lp.json"))
    ap.add_argument("--out", type=str,
                    default=str(REPO / "certificates" / "n9-stage-a.json"))
    ap.add_argument("--round-bits", type=int, default=64)
    ap.add_argument("--margin-exp", type=int, default=46)
    args = ap.parse_args()
    bits, mexp = args.round_bits, args.margin_exp
    margin = Fraction(1, 2**mexp)

    t_start = time.time()
    with open(args.lp) as f:
        lpj = json.load(f)
    N = int(lpj["target"]["N"])
    E_star = Fraction(str(lpj["target"]["E_star"]))        # 精确十进制
    lp_raw = Fraction(str(lpj["lp_raw"]))                  # 数值界（LP 原始值）
    deg = int(lpj["certificate"]["degree"])
    c_hat = [Fraction(s) for s in lpj["certificate"]["coeffs_legendre_exact"]]
    if len(c_hat) != deg + 1:
        fail(f"系数个数 {len(c_hat)} ≠ degree+1 = {deg + 1}")
    print(f"[load] N={N} deg={deg} lp_raw={float(lp_raw):.12f} "
          f"E*={float(E_star):.12f}（{args.lp}）", flush=True)

    # ---------------- 1) 舍入：全部系数 → dyadic（安全方向 = 向下） ----------------
    c_dy = [dyadic_floor(c, bits) for c in c_hat]
    delta = [a - b for a, b in zip(c_hat, c_dy)]           # 每个 ≥ 0
    changed = [k for k, dd in enumerate(delta) if dd != 0]
    print(f"[round] 2^-{bits} 向下舍入：改动系数下标 {changed}，"
          f"c_0 损失 δ0 = {float(delta[0]):.3e}", flush=True)
    if any(c < 0 for c in c_dy[1:]):
        fail("舍入后存在 k≥1 系数 < 0（非负条件被破坏）")

    # ---------------- 2) 精确重认证：fresh 分支定界扫描 + 必要的二次 dyadic 平移 ----
    LEG = lp_bound.legendre_power_basis(deg)
    power_dy = [F0] * (deg + 1)
    for k, c in enumerate(c_dy):
        for j, p in enumerate(LEG[k]):
            power_dy[j] += c * p

    cfg = dict(lp_bound.CFG)
    t0 = time.time()
    cert = lp_bound.certify(c_dy, power_dy, cfg)
    sweep_s = time.time() - t0
    M1 = cert["M"]
    print(f"[sweep] 重认证：{cert['n_eval']} 叶（pass {cert['n_pass']}，宽限 "
          f"{cert['n_leaf']}），M1 = sup(f_dy−φ) 上界 = {float(M1):.3e}，"
          f"tail_ok = {cert['tail_ok']}（{sweep_s:.1f}s）", flush=True)
    if not cert["tail_ok"]:
        fail(f"尾部区间认证失败：tail_bound = {float(cert['tail_bound']):.3e}")

    if M1 <= 0:
        # 扫描已直接认证 f_dy ≤ φ（sup 界 ≤ 0），无需再平移
        shift, c_cert, power_cert = F0, list(c_dy), list(power_dy)
        sup_final = M1
    else:
        eta = M1 + margin
        c0_pre = c_dy[0] - eta
        c0_cert = dyadic_floor(c0_pre, bits)
        delta2 = c0_pre - c0_cert                          # ≥ 0
        shift = eta + delta2
        c_cert = [c0_cert] + c_dy[1:]
        power_cert = list(power_dy)
        power_cert[0] -= shift                             # f_cert = f_dy − shift
        sup_final = M1 - shift                             # = −margin − delta2 < 0
    print(f"[shift] 二次平移 shift = {float(shift):.3e}，"
          f"sup(f_cert−φ) ≤ {float(sup_final):.3e}（精确 {'≤' if sup_final <= 0 else '>'} 0）",
          flush=True)
    if sup_final > 0:
        fail(f"最终 sup(f_cert−φ) 上界 = {sup_final} > 0，f ≤ φ 未被认证")

    # 系数的精确条件
    if any(c < 0 for c in c_cert[1:]):
        fail("证书存在 k≥1 系数 < 0")
    bad = [k for k, c in enumerate(c_cert) if not is_dyadic(c, bits)]
    if bad:
        fail(f"系数 {bad} 在 2^-{bits} 舍入后仍非 dyadic")
    print(f"[coeffs] k≥1 全部 ≥ 0 ✓；{deg + 1} 个系数全部分母 | 2^{bits} ✓", flush=True)

    # ---------------- 3) 界值的纯 Fractions 双路重算 ----------------
    f1_sum = sum(c_cert)                                   # f(1) = Σĉ_k（P_k(1)=1）
    f1_horner = lp_bound.horner(power_cert, F1)
    if f1_sum != f1_horner:
        fail(f"f_cert(1) 双路不一致：Σĉ_k = {f1_sum} ≠ Horner = {f1_horner}")
    B = Fraction(N * N * c_cert[0] - N * f1_sum, 2)
    print(f"[bound] 精确界 B = (N²ĉ_0 − N·f(1))/2 = {float(B):.12f}", flush=True)

    # φ 有理点抽查（isqrt 下界，独立于扫描机制）
    for t in SPOT_T:
        ft = lp_bound.horner(power_cert, Fraction(t))
        phi_lo = Fraction(1, 2) if t == -1 else lp_bound.phi_lower(Fraction(t), 64)
        if ft > phi_lo:
            fail(f"φ 抽查失败：f({float(t)}) = {float(ft):.15e} > φ下界 {float(phi_lo):.15e}")
    print(f"[spot ] f_cert ≤ φ 在 {len(SPOT_T)} 个有理点独立抽查通过（isqrt 下界）",
          flush=True)

    # K_f_test：有理测试点上的核 Gram 阵，exact.py 的 LDLᵀ 验证严格正定
    pts = [rational_point(Fraction(a), Fraction(b)) for a, b in TEST_AB]
    T = [[sum(pi[k] * pj[k] for k in range(3)) for pj in pts] for pi in pts]
    K = [[lp_bound.horner(power_cert, T[i][j]) for j in range(len(pts))]
         for i in range(len(pts))]
    for i in range(len(pts)):
        for j in range(i):
            if K[i][j] != K[j][i]:
                fail(f"K_f_test 不对称：[{i}][{j}] ≠ [{j}][{i}]")
    if not is_positive_definite(K):
        fail("K_f_test 未通过 exact.is_positive_definite（LDLᵀ）——"
             "核 PSD 机制实例复核失败")
    print("[pd   ] K_f_test（9×9，纯 Fraction LDLᵀ）严格正定 ✓", flush=True)

    # ---------------- 4) 断言：精确界 vs 数值界 / E* ----------------
    loss = lp_raw - B                                      # 数值界 − 精确界
    print(f"[loss ] 舍入损失 lp_raw − B = {float(loss):.6e}"
          f"（精确 {fraction_to_str(loss)[:40]}…）", flush=True)
    if B < 0:
        fail(f"精确界 B = {B} < 0")
    if B > lp_raw:
        fail(f"精确界 B = {float(B):.15e} > 数值界 lp_raw = {float(lp_raw):.15e}")
    tol = Fraction(1, 10**6)
    if not (0 < B <= E_star + tol):
        fail(f"违反 0 < B ≤ E* + 1e-6：B = {float(B):.15e}，"
             f"E* + 1e-6 = {float(E_star + tol):.15e}")
    print(f"[assert] 0 < B ≤ lp_raw ✓ 且 0 < B ≤ E* + 1e-6 ✓"
          f"（E* − B = {float(E_star - B):.9f}）", flush=True)
    b9 = B.numerator * 10**9 // B.denominator
    print(f"[report] 9 位小数报告值：{b9 / 10**9:.9f}（lp.json 报告 "
          f"{lpj['bound']:.9f}）", flush=True)

    # ---------------- 5) 证书 JSON（schema.py 格式） ----------------
    blocks = {
        # 证书多项式 f_cert = Σ ĉ_k P_k 的系数表（对角块，41×41）：
        # 下游从对角线读回系数；正性条件 c_k ≥ 0（k≥1）即对角元非负。
        "f_coeffs_diag": [[fraction_to_str(c_cert[j]) if i == j else "0"
                           for j in range(deg + 1)] for i in range(deg + 1)],
        # 核 Gram 阵实例块（exact.is_positive_definite 已验证严格正定）：
        # K[i][j] = f_cert(x_i·x_j)，x_i 为 provenance.params.test_points 的有理点。
        "K_f_test": [[fraction_to_str(x) for x in row] for row in K],
    }
    prov = {
        "repo": "thomson-n9",
        "generator": ("numerics/bounds/verify_certificate.py（候选构造来自 "
                      "numerics/bounds/lp_bound.py → results/lp.json）"),
        "date": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "upstream": ("thomson-workflow/certificates/thomson_certs（exact.py 无主元 "
                     "LDLᵀ + schema.py 交接格式）；Yudin/Delsarte 两点 LP 对偶"
                     "（Legendre 多项式 minorant，P_k 在 S² 正定）"),
        "params": {
            "N": N, "degree": deg, "potential": "phi(t) = (2-2t)^(-1/2)",
            "bound_formula": "E >= (N^2 c_0 - N f(1)) / 2 for f = Σ c_k P_k "
                             "with c_k>=0 (k>=1) and f<=phi on [-1,1)",
            "m_meaning": "m_lo/m_hi 为 minorant 条件 f<=phi 的自变量 t=cosθ 覆盖范围 "
                         "[-1,1)；t→1 处 φ→∞，[1-2^-40,1) 由扫描的 Taylor 尾引理并入 "
                         "sup 界（见 sweep）",
            "round_bits": bits,
            "sweep_params": {"first_level_intervals": cfg["FIRST_LEVEL"],
                             "min_leaf_width": f"2^-{cfg['W_MIN_EXP']}",
                             "taylor_exact_terms": cfg["TAYLOR_K"] + 1,
                             "tail_top": f"1-2^-{cfg['TAIL_EXP']}",
                             "phi_bound_resolution": f"2^-{cfg['PHI_P']}"},
            "test_points_param_ab": [[str(a), str(b)] for a, b in TEST_AB],
            "test_points_rational": [[fraction_to_str(c) for c in p] for p in pts],
        },
        "numerical_bound": {"lp_raw": float(lp_raw), "lp_reported": lpj["bound"]},
        "exact_bound": fraction_to_str(B),
        "rounding_loss": {
            "definition": "数值界 lp_raw − 精确界 B（精确有理数）",
            "exact": fraction_to_str(loss),
            "float": float(loss),
            "c0_dyadic_floor_loss": fraction_to_str(delta[0]),
            "k_indices_changed_by_rounding": changed,
            "post_sweep_c0_shift": fraction_to_str(shift),
        },
        "sweep": {
            "what": "lp_bound.certify 分支定界 Taylor 扫描在本脚本舍入后的系数上"
                    "【重跑】的 sup_{[-1,1)}(f_dy−φ) 严格有理上界",
            "M_f_dy_exact": fraction_to_str(M1),
            "M_f_dy_float": float(M1),
            "sup_f_cert_minus_phi_bound_exact": fraction_to_str(sup_final),
            "sup_f_cert_minus_phi_bound_float": float(sup_final),
            "leaves_evaluated": cert["n_eval"], "leaves_pass": cert["n_pass"],
            "leaves_at_width_limit": cert["n_leaf"],
            "tail_ok": bool(cert["tail_ok"]),
            "worst_leaf": ([float(cert["worst"][0]), float(cert["worst"][1])]
                           if cert["worst"] else None),
            "sweep_time_s": round(sweep_s, 2),
        },
        "phi_spot_checks": {
            "what": "f_cert ≤ φ 在有理点的独立抽查（math.isqrt 的 φ=1/√x 下界，"
                    "不经扫描机制）",
            "points_float": [float(t) for t in SPOT_T], "all_passed": True},
        "checks": {
            "coeffs_nonneg_k_ge_1": True,
            "all_coeffs_dyadic_denom_divides_2_pow_64": True,
            "f_le_phi_resweep_exact_rational": True,
            "f_le_phi_spot_checks_isqrt": True,
            "f1_two_way_exact_agreement": True,
            "K_f_test_positive_definite_exact_ldlt": True,
            "exact_bound_le_numerical_lp_raw": True,
        },
        "note_K_f_test_role": (
            "K_f_test 是加法定理 PSD 机制（c_k≥0 ⇒ 核 f(x·y) 在 S²×S² 半正定 ⇒ "
            "Σ_{i,j}f(x_i·x_j) ≥ N²c_0）在 9 个有理测试点构型上的实例复核；"
            "普遍命题本身是分析定理（Legendre 加法定理），不属于机器验证范围。"),
        "gap_to_E_star": {"exact": fraction_to_str(E_star - B),
                          "float": float(E_star - B)},
        "runtime_s": round(time.time() - t_start, 1),
        "repro": "numerics/.venv/bin/python numerics/bounds/verify_certificate.py",
    }
    cert_obj = Certificate(m_lo="-1", m_hi="1", blocks=blocks,
                           claimed_bound=fraction_to_str(B), provenance=prov)
    text = encode_certificate(cert_obj)
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(text)
    print(f"[out] 已写入 {out_path}（{len(text)} 字节）", flush=True)

    # 回读校验：decode → 字段一致 → 再编码逐字节一致
    rt = decode_certificate(out_path.read_text())
    assert rt.claimed_bound == fraction_to_str(B)
    assert rt.m_lo == "-1" and rt.m_hi == "1"
    assert Fraction(rt.blocks["f_coeffs_diag"][0][0]) == c_cert[0]
    assert [Fraction(rt.blocks["f_coeffs_diag"][k][k])
            for k in range(deg + 1)] == c_cert
    assert encode_certificate(rt) == text
    print("[rt  ] decode_certificate 回读 + 再编码逐字节一致 ✓", flush=True)
    print(f"[done] certified bound = {float(B):.12f}，"
          f"舍入损失 = {float(loss):.6e}，用时 {prov['runtime_s']}s", flush=True)


if __name__ == "__main__":
    main()
