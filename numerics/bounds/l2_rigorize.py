#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""l2_rigorize.py — L2 强制口径严格化：ε_forcing 从 float 求值改为精确有理数上界。

【R8A 换档（D29 裁决 3，2026-10-09）】证书输入 M8→M9：typed cap m0748 的
现行最优证书＝certificates/n9-stage-a4-typedcap-m0748_M9.json（campaign-2 R7B，
commit f05af76；certified=25.75984622533888，E*−c=1.403056611e-4）。旧 M8 口径
档由 git 历史承担（append-only：R5 存档 l2_rigorous.json@34a5d6b 语义不改写，
下文「数值口径对照」仍对 tube.json 的 M8 口径 float 账本如实复核——见 ⑥）。
E* 主口径换十进制 Fraction("25.759986531")（D28 裁决 3：未来消费端一律十进制
口径；二进制 double 精确值并记，差 −8.674815035192296e-16 ≪ 判定余量）。

GAP-REPORT Round 4 引理 L2（强制）：cap 域内 E(x) ≤ E* ⇒ 每类 λ_cls(x) ≤ ε_forcing。
账面数值口径（results/tube.json typed_slack.eps_forcing = 4.153070184893437e-4，
M8 cap 数据 float 求值）自述（eps_forcing_derivation）把 minorant 侧 (1+R2) 因子
列为"忽略级"。本脚本把全链改为精确 Fraction：

  ① 证书重建（certificates/n9-stage-a4-typedcap-m0748_M9.json）
     38 PSD 块精确 LDLᵀ、归一化 3c_A+54c_B+27c_C−9·ΣF⁽⁰⁾−e == 0、
     R1/R2/defl/R2max 精确重算并与 provenance 逐位相等、certified 重算 ==
     claimed_bound。
  ② dyadic 装配入账（对 results/typed_ladder_sol_m0748_M9.json 的 exact 解）
     e 向下舍入损失 e_raw−e_dy、h/ψ/c 最近舍入偏差 max|·| 全部精确有理数记录。
  ③ typed 恒等式（证书 dyadic 数据上）：Σ_84 λ_cls + Σ_all = ΣH − e_dy 于
     随机有理构型精确求值 == 0（残差精确入账）；引理 4.1 分型正性 Σ_all ≥ 0
     于随机有理构型抽查 ≥ 0。
  ④ minorant 侧：ŵ² ≥ b² = (1−lo)/2 精确断言 + 有理 t∈[lo,1) 抽查
     (2−2t)·H_cls(t)² ≤ (1+R2_cls)²。

推导（ε_forcing 的严格形式，对 cap 域 {min 内积 ≥ lo=−187/250} 内任意 9 点构型 x）：

    ΣH(x) ≤ (1+R2max)·E(x)                （Lukács minorant：H_cls(t) ≤ (1+R2_cls)·φ(t) 于 [lo,1)）
    ΣH(x) − e_dy = Σ_84 λ_cls(x) + Σ_all(x)   （③，精确恒等式）
    Σ_all(x) ≥ 0，λ_cls(x) ≥ −R1_{orbit(cls)} （正性 + R1 系数 ℓ₁ + 域乘子非负 + B 块 PSD）
  ⇒ λ_cls(x) = (ΣH−e_dy) − Σ_all − Σ_{cls'≠cls} λ_{cls'}
             ≤ (1+R2max)·E(x) − e_dy + Σ_{cls'} R1_{cls'}
             ≤ (1+R2max)·E* − e_dy + defl            （E(x) ≤ E*，全部 84 类计入=保守）
  ⇒ ε_forcing_rigorous = (1+R2max)·E* − e_dy + defl   （精确 Fraction）
     逐轨道更细：orbit o 中的类 λ_cls ≤ 同式 − R1_o（只扣除自身）。

与数值口径的关系（诚实入账；R8A 换档后两段式）：
  tube.json 数值账本（4.153070184893437e-4）系 M8 cap 数据的 float 求值
  （冻结存档）。本脚本对它做两件事：
  (a) 口径复核——用 M8 证书在盘数据（CERT8_PATH，只读）精确重装配其公式
      （E*−e_dy_M8）+defl_M8，须在 1e-12 内复现账面值（M8 档关系的机器复核）；
  (b) 换档改进断言——M9 口径严格值 ε_rig_M9 < ε_num_M8（字面形式；
      M8 时点该字面断言不可满足、差恰为 E*·R2max 的历史事实见 git 存档
      l2_rigorous.json@34a5d6b，本档并记 M9 口径内的同型分解恒等式
      ε_rig_M9 − ε_nor2_M9 == E*·R2max_M9，精确 ==）。

用法（thomson-n9 下）：
  numerics/.venv/bin/python numerics/bounds/l2_rigorize.py     # 全链 + results/l2_rigorous.json

严格性口径（如实）：全部算术为 Python Fraction（严格数值层，同仓库证书口径）；
typed 恒等式/引理 4.1 正性/Lukács 表示为结构性定理（PAPER.md §4–6.3），本脚本的
机器验证是随机有理点上的精确实例核验 + 归一化/残差的逐系数精确等式，未过 Lean 内核。
E* = 25.759986531 是三源校验参考值而非已证最优；"E(x) ≤ E*" 断言语义为
"与参考值不矛盾"。
"""
from __future__ import annotations

import json
import random
import subprocess
import sys
import time
from datetime import datetime, timezone
from fractions import Fraction
from itertools import combinations
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sys.path.insert(0, str(HERE))

from typed_ladder import QuotientMaps, load_E_star          # noqa: E402
from sdp_certify import rational_point                      # noqa: E402
from thomson_certs.exact import is_positive_definite        # noqa: E402

F0, F1 = Fraction(0), Fraction(1)
A0 = Fraction(-187, 250)                 # m0748 档切口（cap 域下界 lo）
CAP_M, CAP_K = 9, 6                      # R8A 换档：M8→M9（D29 裁决 3）
CERT_PATH = REPO / "certificates" / "n9-stage-a4-typedcap-m0748_M9.json"
SOL_PATH = HERE / "results" / "typed_ladder_sol_m0748_M9.json"
CERT8_PATH = REPO / "certificates" / "n9-stage-a4-typedcap-m0748_M8.json"
                                         # ⑥ 数值账本（tube.json，M8 口径）的
                                         # 数据来源——只读复核，不参与 ε 装配
TUBE_PATH = HERE / "results" / "tube.json"
OUT = HERE / "results" / "l2_rigorous.json"
IDENTITY_TRIALS = 2
FLOAT_NOISE = Fraction(1, 10 ** 15)      # tube.json float 求值的舍入噪声余量


def log(msg: str) -> None:
    print(msg, flush=True)


def code_version() -> str:
    try:
        return subprocess.check_output(
            ["git", "describe", "--always", "--dirty"], cwd=str(REPO),
            text=True, stderr=subprocess.DEVNULL).strip()
    except Exception:
        return "unknown(non-git)"


def fail(msg: str) -> None:
    print(f"[FAIL] {msg}", flush=True)
    sys.exit(1)


# ============================================================ 证书重建 + PSD
def rebuild_certificate(qm: QuotientMaps):
    """verify_cert_file 同款重建：blocks → data；全块 LDLᵀ；归一化；R1/R2 精确。"""
    cert = json.loads(CERT_PATH.read_text())
    assert Fraction(cert["params"]["a0"]) == A0 and cert["params"]["M"] == CAP_M \
        and cert["params"]["K"] == CAP_K, cert["params"]
    b = cert["blocks"]

    def uni(name):
        return [Fraction(x) for x in b[f"{name}_diag"]]

    data = dict(
        h_AA=uni("h_AA"), h_AB=uni("h_AB"), psi_AA=uni("psi_AA"), psi_AB=uni("psi_AB"),
        e=Fraction(b["e"][0]), c_A=Fraction(b["c_A"][0]), c_B=Fraction(b["c_B"][0]),
        c_C=Fraction(b["c_C"][0]),
        F=[[[Fraction(x) for x in row] for row in b[f"F{kk}"]]
           for kk in range(len(qm.F_sizes))],
        B={k[2:]: [[Fraction(x) for x in row] for row in m]
           for k, m in b.items() if k.startswith("B_")},
        sig={k[4:]: [[Fraction(x) for x in row] for row in m]
             for k, m in b.items() if k.startswith("sig_")})
    n_psd = 0
    for m in data["F"] + list(data["B"].values()) + list(data["sig"].values()):
        if not is_positive_definite([[x for x in row] for row in m]):
            fail("PSD 块精确 LDLᵀ 失败（重建数据与证书不符）")
        n_psd += 1
    # 归一化（恒等式的代数基础）：3c_A+54c_B+27c_C − 9·ΣF⁽⁰⁾ − e == 0
    s111 = sum(sum(row) for row in data["F"][0])
    nrm = (qm.nrm["c_A"] * data["c_A"] + qm.nrm["c_B"] * data["c_B"]
           + qm.nrm["c_C"] * data["c_C"] + qm.nrm["e"] * data["e"]
           - Fraction(qm.s111_factor) * s111)
    if nrm != 0:
        fail(f"归一化残差 {nrm} ≠ 0")
    # R1/R2 精确重算（与认证链同式）
    R1 = {}
    for orbit in ("AAA", "AAB", "ABC"):
        lv = qm.lam(orbit, data)
        sv = qm.sos_sum({nm: data["B"][f"{orbit}_{nm}"] for (nm, _g, _m) in qm.sos_def})
        R1[orbit] = sum(abs(x - y) for x, y in zip(lv, sv))
    R2 = {}
    for cls in ("AA", "AB"):
        lhs = qm.minorant_lhs({nm: data["sig"][f"{cls}_{nm}"]
                               for (nm, _my, _mu) in qm.sig_def})
        rhs = qm.minorant_rhs(data[qm.h_of[cls]])
        rr = [x - y for x, y in zip(rhs, lhs)]
        R2[cls] = sum(abs(rr[j]) * qm.w_hat ** j for j in range(len(rr)))
    defl = sum(qm.class_counts[o] * qm.counts[o] * R1[o] for o in R1)
    R2max = max(R2.values())
    certified = (data["e"] - defl) / (1 + R2max)
    claimed = Fraction(cert["claimed_bound"])
    if certified != claimed:
        fail(f"certified 重算 {float(certified):.15f} ≠ claimed {float(claimed):.15f}")
    # provenance 逐位比对
    prov = cert["provenance"]["residuals"]
    prov_ok = (all(Fraction(prov["R1"][o]) == R1[o] for o in R1)
               and all(Fraction(prov["R2"][c]) == R2[c] for c in R2)
               and Fraction(prov["defl"]) == defl
               and Fraction(prov["R2max"]) == R2max)
    if not prov_ok:
        fail("R1/R2/defl/R2max 与证书 provenance 不逐位相等")
    return cert, data, dict(psd_blocks=n_psd, R1=R1, R2=R2, defl=defl,
                            R2max=R2max, certified=certified, provenance_match=True)


# ============================================================ dyadic 装配入账
def dyadic_accounting(cert, data, k_bits: int):
    """exact 解 → dyadic 证书的舍入损失全部精确有理数入账。"""
    sol = json.loads(SOL_PATH.read_text())
    ex = sol["exact"]
    acc = {"solution": str(SOL_PATH.relative_to(REPO)),
           "round_bits": k_bits}
    # e：向下舍入（floor）——只许更小
    e_raw = Fraction(ex["e"])
    e_dy = data["e"]
    if not (F0 <= e_dy <= e_raw):
        fail("e_dy 不在 [0, e_raw] 内（floor 舍入方向错误）")
    acc["e_floor_loss_exact"] = str(e_raw - e_dy)
    acc["e_floor_loss_float"] = float(e_raw - e_dy)
    # h/ψ/c：最近舍入，逐系数精确偏差
    nearest = {}
    for key, name in (("h_AA", "h_AA"), ("h_AB", "h_AB"),
                      ("psi_AA", "psi_AA"), ("psi_AB", "psi_AB")):
        raw = [Fraction(s) for s in ex[name]]
        dy = data[key]
        if len(raw) != len(dy):
            fail(f"{key} 长度不一致（解 {len(raw)} vs 证书 {len(dy)}）")
        mx = max(abs(x - y) for x, y in zip(raw, dy))
        nearest[key] = mx
    for key, name in (("c_A", "c_A"), ("c_B", "c_B")):
        nearest[key] = abs(Fraction(ex[name]) - data[key])
    acc["nearest_rounding_max_abs_exact"] = {k2: str(v) for k2, v in nearest.items()}
    unit = Fraction(1, 2 ** (k_bits + 1))
    for k2, v in nearest.items():
        if v > unit:
            fail(f"{k2} 最近舍入偏差 {v} > 2^-(k+1) = {unit}")
    acc["nearest_bound"] = f"2^-{k_bits + 1}"
    acc["c_C_note"] = ("c_C 不舍入：由归一化 3c_A+54c_B+27c_C = e+9ΣF⁽⁰⁾ 以 Fraction "
                       "精确重算（见 normalization_residual == 0）")
    return acc


# ============================================================ typed 恒等式（证书数据上）
def identity_on_cert_data(qm: QuotientMaps, data, trials=IDENTITY_TRIALS, seed=20261005):
    """Σ_84 λ_cls + Σ_all = ΣH − e_dy 于随机有理构型（全 Fraction，== 0 精确）。"""
    ring = qm.ring
    types = [0] * 3 + [1] * 3 + [2] * 3
    rng = random.Random(seed)
    out = []
    for _ in range(trials):
        X = [rational_point(Fraction(rng.randint(-1 << 6, 1 << 6), 1 << 6),
                            Fraction(rng.randint(-1 << 6, 1 << 6), 1 << 6))
             for _ in range(9)]
        G = [[sum(a * b for a, b in zip(xi, xj)) for xj in X] for xi in X]
        s_vec, _ = qm.s_forms(data)
        sum_all = F0
        for i in range(9):
            for j in range(9):
                for l in range(9):
                    sum_all += ring.eval3(s_vec, G[i][j], G[i][l], G[j][l])
        lam_vecs = {cls: qm.full_lam(cls, data) for (cls, _o, _p) in qm.full_classes}
        sum_lam = F0
        for (i, j, l) in combinations(range(9), 3):
            tt = sorted([(types[i], i), (types[j], j), (types[l], l)])
            (_r0, i0), (_r1, j0), (_r2, l0) = tt
            cls = tuple(x[0] for x in tt)
            sum_lam += ring.eval3(lam_vecs[cls], G[i0][j0], G[i0][l0], G[j0][l0])
        sum_H = F0
        for i in range(9):
            for j in range(i + 1, 9):
                cls = "AA" if types[i] == types[j] else "AB"
                sum_H += ring.eval1(data[qm.h_of[cls]], G[i][j])
        diff = (sum_lam + sum_all) - (sum_H - data["e"])
        ok = (diff == 0) and sum_all >= 0
        out.append(dict(diff=str(diff), sum_all_sign_ok=bool(sum_all >= 0), ok=bool(ok)))
        log(f"[ident] trial: Σλ+Σ_all−(ΣH−e) = {diff}（Σ_all = "
            f"{'≥0 ✓' if sum_all >= 0 else '<0 ✗'}）")
        if diff != 0:
            fail("typed 恒等式在证书数据上失败（残差 ≠ 0）")
        if sum_all < 0:
            fail("分型正性抽查失败（Σ_all < 0）")
    return dict(trials=out, residual="0（精确，== 0 逐 trial）",
                statement=("Σ_84 λ_cls(x) + Σ_all(x) = ΣH(x) − e_dy，证书 dyadic 数据、"
                           "随机有理构型 × %d；Σ_all ≥ 0 为引理 4.1 分型正性抽查"
                           % trials))


# ============================================================ minorant 侧
def minorant_checks(qm: QuotientMaps, data, R2):
    """ŵ² ≥ b² 精确 + 有理 t 抽查 (2−2t)·H_cls² ≤ (1+R2_cls)²。"""
    if not (qm.w_hat ** 2 >= qm.b2):
        fail("ŵ² < b² = (1−lo)/2（R2 权重常数不覆盖 y 域）")
    checks = []
    lo = qm.lo
    pts = [lo, (lo + F1) / 2, Fraction(-1, 2) if lo <= Fraction(-1, 2) else lo,
           Fraction(-3, 4) if lo <= Fraction(-3, 4) else lo, F0,
           Fraction(1, 4), Fraction(1, 2), Fraction(3, 4), Fraction(995, 1000)]
    n_chk = 0
    for cls in ("AA", "AB"):
        h = data[qm.h_of[cls]]
        for tp in pts:
            if not (lo <= tp < 1):
                continue
            Ht = qm.ring.eval1(h, tp)
            n_chk += 1
            if Ht > 0 and (2 - 2 * tp) * Ht * Ht > (1 + R2[cls]) ** 2:
                fail(f"minorant {cls} 抽查失败 @t={float(tp)}")
        checks.append(cls)
    return dict(w_hat=str(qm.w_hat), b2=str(qm.b2), w_hat_sq_ge_b2=True,
                spot_points_checked=n_chk,
                claim=("H_cls(t) ≤ (1+R2_cls)·φ(t) 于 t∈[lo,1)（Lukács σ 表示 + "
                       "R2 加权 ℓ¹，ŵ ≥ b ⇒ |resid(y)| ≤ R2 于 y∈[0,b]）；机器抽查"
                       "(2−2t)H² ≤ (1+R2)² 全过"))


# ============================================================ 主流程
def main() -> None:
    t0 = time.time()
    # E* 双精确口径（D28 裁决 3：主口径＝十进制；二进制 double 精确值并记，
    # 差 −8.674815035192296e-16 为常量级、远小于本轮全部判定余量 1.40e-4）
    E_star_bin = load_E_star()      # 二进制：Fraction(json float)，与证书链同源
    E_star = Fraction("25.759986531")   # 十进制主口径（R8A 换档起 ε_forcing 用此）
    assert abs(E_star - E_star_bin) < Fraction(1, 10 ** 12), float(E_star)
    estar_dual_diff = E_star - E_star_bin
    qm = QuotientMaps(A0, CAP_M, CAP_K)
    log(f"[qm   ] QuotientMaps(a0={A0}, M={CAP_M}, K={CAP_K})：nmon={qm.nmon}，"
        f"d_H={qm.d_H}，ŵ={float(qm.w_hat):.12f}（b²={float(qm.b2):.12f}）")

    # ① 证书重建（PSD/归一化/R1/R2/certified 全精确）
    cert, data, rb = rebuild_certificate(qm)
    log(f"[cert ] {rb['psd_blocks']} PSD 块 LDLᵀ 通过；归一化残差 = 0；"
        f"R1 = { {o: float(v) for o, v in rb['R1'].items()} }；"
        f"defl = {float(rb['defl']):.6e}；R2max = {float(rb['R2max']):.6e}；"
        f"certified 重算 == claimed ✓")

    # ② dyadic 装配入账
    k_bits = int(cert["provenance"]["round_bits"])
    dyad = dyadic_accounting(cert, data, k_bits)
    log(f"[dyad ] e floor 损失 = {dyad['e_floor_loss_float']:.3e}；"
        f"最近舍入 max|Δ| ≤ 2^-{k_bits + 1} 全过")

    # ③ typed 恒等式（证书数据上，随机有理构型）
    ident = identity_on_cert_data(qm, data)
    log("[ident] 恒等式残差 = 0（精确）× 全部 trial")

    # ④ minorant 侧
    mino = minorant_checks(qm, data, rb["R2"])

    # ⑤ ε_forcing 严格形式（E* 十进制主口径；二进制口径并记——D28 裁决 3）
    e_dy = data["e"]
    defl, R2max = rb["defl"], rb["R2max"]
    eps_rig = (1 + R2max) * E_star - e_dy + defl
    eps_rig_bin = (1 + R2max) * E_star_bin - e_dy + defl
    per_orbit = {o: (1 + R2max) * E_star - e_dy + defl - rb["R1"][o]
                 for o in ("AAA", "AAB", "ABC")}
    # swap 类（u↔t 换位）的 R1 同权：换位是单项式置换 ⇒ ℓ₁ 不变（机器复核）
    swap_l1_ok = True
    for orbit in ("AAA", "AAB", "ABC"):
        lv = qm.lam(orbit, data)
        sv = qm.sos_sum({nm: data["B"][f"{orbit}_{nm}"] for (nm, _g, _m) in qm.sos_def})
        resid = [abs(x - y) for x, y in zip(lv, sv)]
        swapped = qm.ring.swap_ut(resid)
        if sum(resid) != sum(swapped):
            swap_l1_ok = False
    if not swap_l1_ok:
        fail("swap_ut 未保持 ℓ₁（换位类的 −R1 界不成立）")

    # ⑥ 与数值口径对照（诚实断言；R8A 换档后两段式——账本系 M8 口径冻结档）
    tube = json.loads(TUBE_PATH.read_text())
    eps_num = tube["typed_slack"]["eps_forcing"]         # M8 cap 数据 float 账本
    eps_num_q = Fraction(eps_num)                        # float 的精确 dyadic 值
    # (a) 账本口径复核：M8 证书在盘数据精确重装配 tube.json 公式
    cert8 = json.loads(CERT8_PATH.read_text())
    assert cert8["params"]["M"] == 8 and Fraction(cert8["params"]["a0"]) == A0, \
        cert8["params"]                                  # 防张冠李戴（M9 冒充）
    e_dy8 = Fraction(cert8["blocks"]["e"][0])
    defl8 = Fraction(cert8["provenance"]["residuals"]["defl"])
    eps_nor2_M8 = E_star - e_dy8 + defl8                 # 账本公式的精确求值
    if abs(eps_nor2_M8 - eps_num_q) > Fraction(1, 10 ** 12):
        fail(f"数值账本（M8 口径）复现失败：精确 {float(eps_nor2_M8):.15e} vs "
             f"tube.json {eps_num:.15e}")
    # (b) M9 口径数值公式 + 分解恒等式（差恰为 E*·R2max，精确 ==）
    eps_nor2 = E_star - e_dy + defl
    r2_term = E_star * R2max
    if eps_rig - eps_nor2 != r2_term:
        fail("M9 口径分解恒等式失败：ε_rig − ε_nor2 ≠ E*·R2max")
    # 换档改进断言（字面形式；M8 时点不可满足的历史口径见 git 存档 34a5d6b）
    if not (F0 < eps_rig < eps_num_q):
        fail(f"换档改进断言失败：ε_rig_M9={float(eps_rig):.6e} 须 ∈ "
             f"(0, 账本 M8 值 {eps_num:.6e})")
    literal_gap = eps_num_q - eps_rig                    # 账本 − 新严格值（改进量）
    log(f"[eps  ] ε_rig(M9) = {float(eps_rig):.10e}（精确十进制口径 {eps_rig}）；"
        f"M8 数值账本 = {eps_num:.10e}；改进 −{float(literal_gap):.6e}；"
        f"M9 内分解差 E*·R2max = {float(r2_term):.6e} ✓ 入账")

    doc = dict(
        kind="n9-l2-rigorized",
        script="bounds/l2_rigorize.py",
        code_version=code_version(),
        timestamp=datetime.now(timezone.utc).isoformat(timespec="seconds"),
        inputs=dict(certificate=str(CERT_PATH.relative_to(REPO)),
                    solution=str(SOL_PATH.relative_to(REPO)),
                    numerical_ledger=str(TUBE_PATH.relative_to(REPO)),
                    numerical_ledger_caliber_cert=str(CERT8_PATH.relative_to(REPO)),
                    energies="../thomson-workflow/data/energies.json"),
        caliber_switch=dict(
            ruling="D29 裁决 3（R8A，2026-10-09）：证书输入 M8→M9 换档",
            previous="M8 口径档见 git 历史（l2_rigorous.json@34a5d6b，ε=4.153454e-4，"
                     "append-only 不改写）；本档 cap 证书＝typed m0748_M9（campaign-2 "
                     "R7B，commit f05af76）"),
        E_star=dict(value=str(E_star), float=float(E_star),
                    caliber="十进制 25759986531/10^9（主口径，D28 裁决 3：未来消费端一律十进制）",
                    binary_double_exact=str(E_star_bin),
                    decimal_minus_binary_exact=str(estar_dual_diff),
                    decimal_minus_binary_float=float(estar_dual_diff),
                    dual_caliber_note=("差 −8.674815035192296e-16 上界注明：远小于本档全部"
                                       "判定余量（ε_forcing 本身 1.40e-4 量级、对账容差 "
                                       "1e-12），两口径并存不改判（D28 裁决 3）"),
                    semantics="三源校验参考值，非已证最优；E(x) ≤ E* 断言仅语义为与参考值不矛盾"),
        certificate_rebuild=dict(
            psd_blocks=rb["psd_blocks"],
            psd_method="exact Fractions LDLᵀ（thomson_certs.exact.is_positive_definite）",
            normalization_residual="0（精确：3c_A+54c_B+27c_C−9·ΣF⁽⁰⁾−e == 0）",
            R1_exact={o: str(v) for o, v in rb["R1"].items()},
            R2_exact={c: str(v) for c, v in rb["R2"].items()},
            defl_exact=str(defl), R2max_exact=str(R2max),
            certified_recomputed=str(rb["certified"]),
            claimed_bound=cert["claimed_bound"],
            bitwise_equal_to_claimed=True,
            provenance_residuals_match=True,
            swap_ut_preserves_l1=swap_l1_ok),
        dyadic_assembly=dyad,
        typed_identity=ident,
        minorant=mino,
        eps_forcing=dict(
            formula="λ_cls ≤ (1+R2max)·E* − e_dy + defl（精确 Fraction；"
                    "orbit o 的类可再减 R1_o）",
            derivation=[
                "ΣH(x) ≤ (1+R2max)·E(x)：H_cls(t) ≤ (1+R2_cls)·φ(t)=(1+R2_cls)·(2−2t)^(−1/2) 于 [lo,1)（Lukács σ 块 PSD + R2 精确加权 ℓ₁ 残差，ŵ ≥ b）",
                "恒等式 ΣH(x) − e_dy = Σ_84 λ_cls(x) + Σ_all(x)（证书数据上残差 = 0，精确）",
                "Σ_all(x) ≥ 0（引理 4.1 分型正性 + F 块精确 PSD）",
                "λ_cls(x) ≥ −R1_{orbit(cls)}（λ−SOS 系数 ℓ₁ = R1；域 {u,v,t ≥ lo, ≤1, detG ≥ 0} 上乘子与 SOS 非负、|单项式| ≤ 1；换位类 ℓ₁ 不变）",
                "⇒ λ_cls ≤ (1+R2max)·E − e_dy + Σ_{84} R1 = (1+R2max)·E − e_dy + defl ≤ (1+R2max)·E* − e_dy + defl"],
            exact=str(eps_rig), float=float(eps_rig),
            E_star_caliber="十进制 25759986531/10^9（主口径，D28 裁决 3）",
            exact_binary_caliber=str(eps_rig_bin),
            float_binary_caliber=float(eps_rig_bin),
            binary_minus_decimal_exact=str(eps_rig_bin - eps_rig),
            identity_check=dict(
                formula="ε_forcing == (1+R2max)·(E* − certified)（精确恒等式，"
                        "certified 重算 == claimed_bound 逐位——见 certificate_rebuild）",
                holds=bool(eps_rig == (1 + R2max) * (E_star - rb["certified"]))),
            per_orbit_exact={o: str(v) for o, v in per_orbit.items()},
            per_orbit_float={o: float(v) for o, v in per_orbit.items()},
            counts=dict(AAA="3 类 ×1", AAB="6 类 ×9", ABC="1 类 ×27", total=84),
            domain=f"cap 域：9 点单位球面构型，min 内积 ≥ lo = {A0}"),
        numerical_ledger_comparison=dict(
            ledger_value=eps_num,
            ledger_source="results/tube.json typed_slack.eps_forcing",
            ledger_caliber="M8 cap 数据（冻结存档；R8A 换档后账本本身不重生成）",
            ledger_formula="（E*−e_dy_M8）+ defl_M8，float 求值；自述把 (1+R2) 因子列为忽略级",
            ledger_caliber_recheck=dict(
                source=str(CERT8_PATH.relative_to(REPO)),
                exact_recompute_of_ledger_formula=str(eps_nor2_M8),
                reproduction_match_within_1e_12=True),
            m9_formula_exact_recompute=str(eps_nor2),
            rigorous_minus_m9_formula_exact=str(eps_rig - eps_nor2),
            decomposition="ε_rig(M9) − ε_nor2(M9) == E*·R2max(M9)（M9 口径内分解"
                          "恒等式，精确 ==；账本自身的 M8 口径差 E*·R2max_M8 见 git 存档）",
            ledger_minus_rigorous_exact=str(literal_gap),
            ledger_minus_rigorous_float=float(literal_gap),
            improvement_note=f"M8→M9 换档改进 −{float(literal_gap):.6e}"
                             f"（{float(literal_gap / eps_num_q) * 100:.2f}% of 账本值）",
            downstream_impact=("消费链联动（R8A）：l3_analytic.py 运行时直读本档 "
                              "eps_forcing.exact ⇒ caliber(a) ε 换新值；ρ_raw 由 4707.8 "
                              "随 √ε 降至 2736.2（×0.58121=√(ε_new/ε_old) 精确），"
                              "ρ_capped 维持 0.6447 平台（绑定约束＝cell₆ 平凡半径 "
                              "1−ν₆ 而非 √ε 分支——ε 须降至 ~1.5e-9 才脱离该平台，"
                              "任务书预测带 0.37–0.40 系对绑定分支的误设，如实入账）；"
                              "endgame_chain.py L2 quant/L3 口径串同步（「待刷新」"
                              "标注解除）")),
        asserts=dict(
            psd_all_blocks=True, normalization_zero=True, residuals_match_provenance=True,
            certified_bitwise_equal=True, identity_residual_zero=True,
            positivity_spotcheck=True, minorant_spotchecks=True,
            w_hat_covers_domain=True, swap_l1_preserved=True,
            numerical_ledger_reproduced=True,
            rigorous_le_ledger_plus_omitted_term=True,
            literal_rigorous_le_ledger=dict(
                feasible=True,
                ledger_minus_rigorous_exact=str(literal_gap),
                explanation=("R8A 换档后字面断言 ε_rig(M9) < ε_num(M8 账本) 可满足并"
                             "已实现为硬 fail 检查（0 < ε_rig < 账本值）。M8 时点该字面"
                             "断言不可满足（差恰为 E*·R2max_M8=3.838141e-8>0，实现为 "
                             "ε_rig ≤ ε_num + E*·R2max + 1e-15）——历史口径见 git 存档 "
                             "l2_rigorous.json@34a5d6b，append-only 不改写。相对改进 = "
                             f"{float(literal_gap / eps_num_q):.2e}"))),
        scope=("严格数值层（Python Fraction，同仓库证书口径）；结构性定理（typed 恒等式、"
               "引理 4.1 正性、Lukács 表示）为 PAPER.md §4–6.3 引用 + 随机有理点精确"
               "实例核验，未过 Lean 内核"),
        wall_s=round(time.time() - t0, 1),
    )
    OUT.write_text(json.dumps(doc, ensure_ascii=False, indent=1))
    print(json.dumps({
        "eps_forcing_rigorous": float(eps_rig),
        "eps_forcing_rigorous_binary_caliber": float(eps_rig_bin),
        "eps_forcing_numerical_ledger_M8": eps_num,
        "improvement_minus": float(literal_gap),
        "difference_E_star_times_R2max": float(r2_term),
        "asserts_all_pass": True,
        "out": str(OUT.relative_to(REPO)), "wall_s": doc["wall_s"]},
        ensure_ascii=False, indent=1))
    log(f"[done ] L2 严格化（M9 口径）完成：ε_forcing = {float(eps_rig):.10e}"
        f"（精确分数入 {OUT.relative_to(REPO)}）；exit 0")


if __name__ == "__main__":
    main()
