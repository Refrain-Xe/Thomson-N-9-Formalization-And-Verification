#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r9_v2iv_gate.py — R9B v2-interval-reverify 验收门（G1–G6 ＋ NC1–NC4）.

任务书口径（D33 裁决 5③／D34 裁决 2）：v2 contact 相位 0 存档证书
results/hermite_v2_probe_contact.json 的自写区间算术重验
（numerics/bounds/r9_v2iv_reverify.py，B≥120、零 hermite_minorant import）
——①七区域 Π≥0 重推＋c_const＋φ^{(m)} 公式；②W==17·2⁻⁴⁹ 恒等＋格点＋
coeffs[0]=M₀−W 语义；③直接区间路径 φ−M′≥0 全覆盖自适应二分；④strip gap
上界双口径（1%＋2⁻⁴⁹ 容差＋硬上界 <1e-12＋1.5717e4× 收紧比）；⑤c0_dense
witness。固定种子 20261010；负对照全触发；门总时长 <9 分钟。

R9 返工增补（返工员-R9，D36 裁决 1，2026-10-10，增补式扩展——历史检查
G1–G5/NC1–NC3b 全保留，沿 D29 裁决 5/D34 裁决 4 先例）：
  G6  ③ soundness 抽查机器化——R9B 会话曾以叙述口径记『300 随机叶
      认证下界−真值min ≤ +2.22e-16 零违例』（GAP-REPORT R9B ②／
      decisions D34 R9B 回填裁决 1），但当时未落盘机器字段；本检将其
      常态化：门内复刻 ③ 二分收集 pass 叶（受测机器件＝重验器
      LeafBender 同源，计数与 G1 新鲜产出逐位对账），seed 20261010 抽
      300 叶，每叶 float 网格＋三分定位近似 argmin 后单点精确 Fraction
      求值 g_ref=φ_hi−M′（≥g(t*)≥真min ⟹ 判据方向保守），要求
      slack=lo−g_ref ≤ +2.22e-16 零违例。
  NC4 G6 检出器负对照——同 300 叶 slack 全体 +1e-12 偏置 ⇒ 必现违例
      （验证比较方向/阈值逻辑真能翻红，沿 R9D『扩展前负对照亲验』先例）。

用法（campaign 根）：
  python3 thomson-n9/numerics/bounds/r9_v2iv_gate.py    # exit 0 = 过门
"""
from __future__ import annotations

import argparse
import json
import math
import random
import subprocess
import sys
import tempfile
import time
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
REPO = HERE.parents[1]
REVERIFY = HERE / "r9_v2iv_reverify.py"
CERT = RESULTS / "hermite_v2_probe_contact.json"
OUT = RESULTS / "r9_v2iv.json"
SEED_GATE = 20261010
GATE_CAP_S = 540                                  # 9 分钟
NC1_CAP_S = 120                                   # 快失败上限
ARCH_STRIP_FLOAT = Fraction("4.4283673247852223e-14")
M_OLD_CITED = Fraction("6.96e-10")
RATIO_BAND = (Fraction(14500), Fraction(16800))   # 1.5717e4× ±~7%
F0 = Fraction(0)


def fail(msg: str) -> None:
    print(f"[gate][FAIL] {msg}", flush=True)


def ok(msg: str) -> None:
    print(f"[gate][OK] {msg}", flush=True)


def run_reverify(args: list, expect_json: Path = None):
    t0 = time.time()
    cmd = [sys.executable, str(REVERIFY)] + args
    p = subprocess.run(cmd, capture_output=True, text=True, cwd=str(REPO))
    dt = time.time() - t0
    out = None
    if expect_json is not None and expect_json.exists():
        out = json.loads(expect_json.read_text())
    return p.returncode, p.stdout + p.stderr, out, dt


def mutate_cert(cert: dict, tmpdir: Path, name: str) -> Path:
    p = tmpdir / f"{name}.json"
    p.write_text(json.dumps(cert, ensure_ascii=False))
    return p


# ---------------- G6 附件（R9 返工增补，D36 裁决 1）
SND_N_LEAVES = 300                                 # R9B 叙述口径同数
SND_EPS = Fraction("2.22e-16")                     # 叙述口径同容差（float 噪声阶）
SND_BIAS = Fraction(1, 10 ** 12)                   # NC4 检出器偏置
PHI_ISQRT_BITS = 256                               # φ_hi 区间半宽 ~2⁻²⁵⁶ 相对


def _collect_pass_leaves(coeffs, B: int, eval_budget: int,
                         width_floor: Fraction, dom_hi: Fraction):
    """门内复刻 direct_interval_cover 二分循环收集 pass 叶 (a, b, lo)。

    受测机器件＝重验器 LeafBender（import 同一实现——G6 目的是给『认证下界
    是否真下界』配真值参考，非重造叶界机）；G1 ③ 刚证全过 ⟹ 复刻循环不得
    遇 violate/inconclusive/预算耗尽（遇即门 fail：转录或行为漂移）。"""
    sys.path.insert(0, str(HERE))
    import r9_v2iv_reverify as rv                  # noqa: E402（受测机器件）
    lb = rv.LeafBender(coeffs, B)
    stack = [(-Fraction(1), dom_hi)]
    leaves = []
    n_evals = 0
    while stack:
        a, b = stack.pop()
        n_evals += 1
        if n_evals > eval_budget:
            fail("G6 复刻二分 eval 预算耗尽（G1 ③ 刚全过，不应发生）")
            sys.exit(1)
        m = (a + b) / 2
        d = (b - a) / 2
        Mm, M1, M2, M3 = lb.poly_at(m)
        slop3 = abs(M3) * d ** 3 / 6 + lb.q4(d)
        phi_a, phip_a, phipp_a = lb.phi_side_lo(a)
        ma = m - a
        A = (phipp_a - M2) / 2
        Bc = phip_a - M1 + phipp_a * ma
        C = phi_a + phip_a * ma + phipp_a * ma * ma / 2 - Mm - slop3
        lo = rv.LeafBender.quad_min(A, Bc, C, d)
        if lo >= 0:
            leaves.append((a, b, lo))
            continue
        if b - a <= width_floor:
            fail("G6 复刻二分触 width_floor（G1 ③ 无 inconclusive，不应发生）")
            sys.exit(1)
        stack.append((m, b))
        stack.append((a, m))
    return leaves, n_evals


def _soundness_slack(coeffs, leaf) -> Fraction:
    """slack = lo − g_ref(t*)（精确 Fraction）。

    t*＝float 网格＋三分定位的近似 argmin（ε_search≈曲率·Δt²≲1e-30 ≪
    2.22e-16，float 搜索噪声只影响定位不影响判据）；g_ref(t*)＝
    φ_hi(t*)−M′(t*)：M′ 精确 Horner，φ_hi＝isqrt 整数缩放区间上端
    （[s/2^k,(s+1)/2^k]∋√u ⟹ φ_hi=2^k/s，相对半宽 2⁻²⁵⁶）。
    g_ref ≥ g(t*) ≥ 真min ⟹ PASS（slack≤ε）⟹ lo ≤ 真min+ε+2⁻²⁵⁵：
    判据与 R9B 叙述口径同向且保守。"""
    a, b, lo = leaf
    af, bf = float(a), float(b)
    cf = [float(c) for c in coeffs]

    def gf(t: float) -> float:                    # 仅用于定位，不入判据
        s = cf[-1]
        for c in reversed(cf[:-1]):
            s = s * t + c
        return 1.0 / math.sqrt(2.0 - 2.0 * t) - s

    w = bf - af
    npts = max(65, min(2049, int(w * 100000) + 65))
    bi, bv = 0, float("inf")
    for i in range(npts):
        v = gf(af + w * i / (npts - 1))
        if v < bv:
            bv, bi = v, i
    t0 = af + w * max(0, bi - 1) / (npts - 1)
    t1 = af + w * min(npts - 1, bi + 1) / (npts - 1)
    for _ in range(80):                           # 三分：宽度·3⁻⁸⁰（float 下限）
        c1 = t0 + (t1 - t0) / 3
        c2 = t1 - (t1 - t0) / 3
        if gf(c1) <= gf(c2):
            t1 = c2
        else:
            t0 = c1
    ts = Fraction((t0 + t1) / 2)                  # Fraction(float) 精确二进
    if not (a <= ts <= b):
        ts = Fraction((af + bf) / 2)
    Mv = Fraction(0)                              # M′(ts) 精确 Horner
    for c in reversed(coeffs):
        Mv = Mv * ts + c
    u = Fraction(2) - 2 * ts                      # >0（ts ≤ 1−2⁻⁴⁰ ⟹ u ≥ 2⁻³⁹）
    k = PHI_ISQRT_BITS
    n_int = Fraction(u.numerator * (1 << (2 * k)), u.denominator)
    if n_int.denominator != 1:
        fail("G6 φ 区间缩放非整（u 分母非 2 幂——不应发生）")
        sys.exit(1)
    s = math.isqrt(n_int.numerator)               # s ≤ √(u·2^2k) < s+1（精确）
    phi_hi = Fraction(1 << k, s)                  # 1/√u ≤ 2^k/s
    return lo - (phi_hi - Mv)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.parse_args()
    t_gate = time.time()
    checks = 0
    tmpdir = Path(tempfile.mkdtemp(prefix="r9v2iv_gate_"))

    # ---------------- G1 重验器亲跑（full scope，新鲜输出在临时目录，
    #                     不触盘上官方产出——树净先例沿 r9_s3_gate G2/G3）
    fresh = tmpdir / "fresh.json"
    rc, so, res, dt = run_reverify(
        ["--scope", "full", "--cert", str(CERT), "--out", str(fresh)], fresh)
    checks += 1
    if rc != 0 or res is None or not res.get("all_pass"):
        fail(f"G1 重验器 full 亲跑未全过（exit={rc}）\n{so[-1500:]}")
        sys.exit(1)
    items = res["items"]
    for key, name in (("regions", "①七区域"), ("w_identity", "②W 恒等"),
                      ("direct_interval", "③直接区间"), ("strip_gap", "④strip"),
                      ("c0_witness", "⑤c0 witness")):
        if not items[key].get("ok"):
            fail(f"G1 五项之 {name} 未 PASS")
            sys.exit(1)
    if res.get("seed") != SEED_GATE or int(res.get("B", 0)) < 120:
        fail("G1 seed/B 字段不符（须 20261010/B≥120）")
        sys.exit(1)
    if "code_version" not in res or "timings_s" not in res:
        fail("G1 产出缺 code_version/timings_s")
        sys.exit(1)
    ok(f"G1 重验器 full 亲跑五项 PASS（{dt:.1f}s，"
       f"total={res['timings_s']['total']}s，B={res['B']}）")

    # ---------------- G2 逐位：区域边界 / W 恒等式（门内独立重算）
    cert = json.loads(CERT.read_text())
    nodes = [float(x) for x in cert["nodes"]]
    nu = sorted(Fraction(x) for x in nodes)
    breaks = [Fraction(-1)] + nu + [Fraction(1)]
    regions = cert["interval_certificate"]["regions"]
    if len(regions) != len(breaks) - 1:
        fail("G2 区域数不符")
        sys.exit(1)
    for i, r in enumerate(regions):
        if (r["interval"][0] != str(breaks[i])
                or r["interval"][1] != str(breaks[i + 1])
                or Fraction(r["interval"][0]) != breaks[i]
                or Fraction(r["interval"][1]) != breaks[i + 1]):
            fail(f"G2 区域 {i} 边界 ≠ Fraction(float(ν)) 精确逐位")
            sys.exit(1)
    checks += 1
    hw_sum = sum((Fraction(s) for s in cert["halfwidths"]), F0)
    W = Fraction(cert["W"])
    if not (hw_sum == W == Fraction(17, 562949953421312)):
        fail("G2 Σhw==W==17·2⁻⁴⁹ 恒等式不符")
        sys.exit(1)
    if Fraction(cert["interval_certificate"]["c_const"]) != \
            Fraction(583401555, 32768):
        fail("G2 c_const ≠ 583401555/32768")
        sys.exit(1)
    # 与重验产出对账（重验侧旗标须全真）
    i1, i2 = items["regions"], items["w_identity"]
    if not (i1["boundaries_match_archive_bitwise"] and i1["union_covers_minus1_1_seamless"]
            and i1["neg_counts_6_to_0"] and i1["pi_all_nonneg"]
            and i1["c_const"]["equal"] and i1["hull"]["bitwise_match"]
            and i1["phi_derivs"]["symbolic_recurrence_ok"]
            and i1["phi_derivs"]["hull_interval_positivity"]):
        fail("G2 重验产出逐位旗标有假值")
        sys.exit(1)
    if not (i2["W_identity_exact"] and i2["all_coeffs_on_2m49_lattice"]
            and i2["midpoint_cell_structure"] and i2["hw_each_is_2m49"]
            and i2["coeffs0_semantics"]["identity_at_seeded_points"]):
        fail("G2 重验产出 ② 旗标有假值")
        sys.exit(1)
    checks += 1
    ok("G2 区域边界==Fraction(float(ν_k)) 逐位（7 区域）＋Σhw==W==17·2⁻⁴⁹ "
       "精确＋c_const/hull 逐位")

    # ---------------- G3 直接区间路径覆盖计数与叶预算
    i3 = items["direct_interval"]
    if not (i3["n_pass_leaves"] > 0 and i3["n_evals"] <= i3["leaf_eval_budget"]
            and i3["coverage_exact"] and i3["n_violations"] == 0
            and i3["n_inconclusive"] == 0 and i3["width_floor"]
            and i3["tail"]["trivially_positive"]
            and Fraction(i3["total_covered_with_tail"]) == 2):
        g3sum = json.dumps({k: i3.get(k) for k in
                            ("n_pass_leaves", "n_evals", "coverage_exact",
                             "n_violations", "n_inconclusive",
                             "total_covered_with_tail")}, ensure_ascii=False)
        fail(f"G3 覆盖/叶预算记录不完整：{g3sum}")
        sys.exit(1)
    checks += 1
    ok(f"G3 直接区间路径覆盖完整（{i3['n_pass_leaves']} 叶／"
       f"{i3['n_evals']} evals ≤ 预算 {i3['leaf_eval_budget']}；覆盖度量"
       f"==2 精确；min certified gap={i3['min_certified_gap_float']:.3e} ≥ 0）")

    # ---------------- G4 strip gap 双口径
    i4 = items["strip_gap"]
    sup_ub = Fraction(i4["sup"]["sup_ub"])
    r_cited = Fraction(i4["ratio_vs_cited"]["exact"])
    r_rebuilt = Fraction(i4["ratio_vs_rebuilt"]["exact"])
    if not i4["within_1pct_plus_2m49"]:
        fail(f"G4 口径 A 未过：|{float(sup_ub):.6e} − "
             f"{float(ARCH_STRIP_FLOAT):.6e}|={i4['abs_diff_float']:.3e} > "
             f"{i4['tol_abs_float']:.3e}")
        sys.exit(1)
    if not i4["hard_ub_lt_1e12"]:
        fail("G4 口径 B 硬上界 ≥1e-12")
        sys.exit(1)
    if not (RATIO_BAND[0] <= r_cited <= RATIO_BAND[1]
            and RATIO_BAND[0] <= r_rebuilt <= RATIO_BAND[1]):
        fail(f"G4 收紧比出带：cited={float(r_cited):.4e} "
             f"rebuilt={float(r_rebuilt):.4e} ∉ "
             f"[{float(RATIO_BAND[0]):.4e},{float(RATIO_BAND[1]):.4e}]")
        sys.exit(1)
    if not (i4["m_old_rebuild"]["coeffs_match_archive_bitwise"]
            and i4["m_old_rebuild"]["vs_cited_6p96e_10_ok"]):
        fail("G4 M_old 重建逐位/口径不符")
        sys.exit(1)
    checks += 1
    ok(f"G4 strip 双口径过（sup_ub={float(sup_ub):.6e}，1%+2⁻⁴⁹ 容差内；"
       f"<1e-12；收紧比 cited={float(r_cited):.4e}×／"
       f"rebuilt={float(r_rebuilt):.4e}×，1.5717e4× 定性保持；M_old 重建"
       f"逐位==hermite_probe.json）")

    # ---------------- G5 官方产出在盘且与新鲜输出实质字段逐位一致（防陈旧）
    if not OUT.exists():
        fail(f"G5 官方产出缺失：{OUT}")
        sys.exit(1)
    disk = json.loads(OUT.read_text())
    subst = [
        ("scope", res["scope"]), ("seed", res["seed"]), ("B", res["B"]),
        ("cert_sha256", res["cert_sha256"]),
        ("all_pass", res["all_pass"]),
        ("items.regions.ok", True),
        ("items.regions.boundaries", res["items"]["regions"]["boundaries"]),
        ("items.regions.c_const.equal", True),
        ("items.w_identity.W_identity_exact", True),
        ("items.direct_interval.n_pass_leaves",
         res["items"]["direct_interval"]["n_pass_leaves"]),
        ("items.direct_interval.n_evals",
         res["items"]["direct_interval"]["n_evals"]),
        ("items.direct_interval.covered_measure",
         res["items"]["direct_interval"]["covered_measure"]),
        ("items.direct_interval.min_certified_gap",
         res["items"]["direct_interval"]["min_certified_gap"]),
        ("items.strip_gap.sup.sup_ub", res["items"]["strip_gap"]["sup"]["sup_ub"]),
        ("items.strip_gap.ratio_vs_cited.exact",
         res["items"]["strip_gap"]["ratio_vs_cited"]["exact"]),
        ("items.c0_witness.recomputed", res["items"]["c0_witness"]["recomputed"]),
    ]
    mism = []
    for key, want in subst:
        node = disk
        for part in key.split("."):
            node = node.get(part) if isinstance(node, dict) else None
        if node != want:
            mism.append(f"{key}: 盘上={node!r} 新鲜={want!r}")
    if mism:
        fail("G5 盘上产出与新鲜输出实质字段失配（防陈旧）：\n  "
             + "\n  ".join(mism[:8]))
        sys.exit(1)
    checks += 1
    ok("G5 官方产出在盘且 16 个实质字段与新鲜亲跑逐位一致（scope/seed/B/"
       "cert_sha/边界/叶计数/覆盖度量/min gap/sup_ub/收紧比/c0 等；"
       "generated·timings·code_version 系运行时戳不入比较）")

    # ---------------- G6 ③ soundness 抽查机器化（R9 返工增补，D36 裁决 1）
    coeffs = [Fraction(s) for s in cert["coeffs"]]
    leaves, n_ev6 = _collect_pass_leaves(
        coeffs, int(res["B"]), 2_000_000, Fraction(1, 1 << 56),
        Fraction((1 << 40) - 1, 1 << 40))
    checks += 1
    if (len(leaves) != res["items"]["direct_interval"]["n_pass_leaves"]
            or n_ev6 != res["items"]["direct_interval"]["n_evals"]):
        fail(f"G6 复刻二分计数与 G1 新鲜产出不符（{len(leaves)} 叶/"
             f"{n_ev6} evals vs "
             f"{res['items']['direct_interval']['n_pass_leaves']}/"
             f"{res['items']['direct_interval']['n_evals']}）")
        sys.exit(1)
    rng = random.Random(SEED_GATE)
    idxs = rng.sample(range(len(leaves)), SND_N_LEAVES)
    t6 = time.time()
    slacks = [_soundness_slack(coeffs, leaves[i]) for i in idxs]
    viol = [s for s in slacks if s > SND_EPS]
    if viol:
        fail(f"G6 ③ soundness 抽查 {len(viol)}/{SND_N_LEAVES} 违例"
             f"（slack > +2.22e-16，max={float(max(slacks)):+.3e}）")
        sys.exit(1)
    ok(f"G6 ③ soundness 抽查（机器化，D36 裁决 1）：300 随机叶"
       f"（seed {SEED_GATE}）认证下界−真值参考 ≤ +2.22e-16 零违例"
       f"（max slack={float(max(slacks)):+.3e}；复刻二分 {len(leaves)} 叶/"
       f"{n_ev6} evals 与 G1 新鲜产出逐位对账；抽查 {time.time() - t6:.1f}s）")

    # ---------------- 负对照（/tmp 副本）
    with tempfile.TemporaryDirectory(prefix="r9v2iv_nc_") as td:
        tmpdir = Path(td)
        # NC1 coeffs[0]+2⁻⁴⁰ ⟹ ③ 检出负间隙 exit 1（argmin −0.99997 邻近快失败）
        c1 = json.loads(CERT.read_text())
        c1["coeffs"][0] = str(Fraction(c1["coeffs"][0]) + Fraction(1, 1 << 40))
        p1 = mutate_cert(c1, tmpdir, "nc1")
        o1 = tmpdir / "nc1.out.json"
        rc, so, r1, dt1 = run_reverify(
            ["--scope", "quick", "--cert", str(p1), "--out", str(o1)], o1)
        viol = (r1 or {}).get("items", {}).get("direct_interval", {}) \
            .get("violations", [])
        checks += 1
        if rc != 1 or not viol:
            fail(f"NC1 未按预期检出（exit={rc}, violations={len(viol)}）\n"
                 f"{so[-800:]}")
            sys.exit(1)
        vf = viol[0].get("interval_float")
        if not (vf and vf[0] >= -1.0 and vf[1] < -0.99):
            fail(f"NC1 检出位置不在 argmin −0.99997 邻近：{vf}")
            sys.exit(1)
        if dt1 > NC1_CAP_S:
            fail(f"NC1 未快失败（{dt1:.1f}s > {NC1_CAP_S}s）")
            sys.exit(1)
        if not (r1["items"]["regions"]["ok"] and r1["items"]["w_identity"]["ok"]):
            fail("NC1 误伤 ①②（应只有 ③ 检出）")
            sys.exit(1)
        ok(f"NC1 coeffs[0]+2⁻⁴⁰ ⟹ ③ 检出负间隙 exit 1（叶 "
           f"{vf[0]:.6f}..{vf[1]:.6f}，{dt1:.1f}s 快失败；①②不受扰）")
        # NC2 W→17/2⁵² ⟹ ② 恒等式失配 exit 1
        c2 = json.loads(CERT.read_text())
        c2["W"] = str(Fraction(17, 1 << 52))
        p2 = mutate_cert(c2, tmpdir, "nc2")
        o2 = tmpdir / "nc2.out.json"
        rc, so, r2, _ = run_reverify(
            ["--scope", "quick", "--cert", str(p2), "--out", str(o2)], o2)
        checks += 1
        if rc != 1 or (r2 or {}).get("items", {}).get("w_identity", {}).get("ok"):
            fail(f"NC2 未按预期检出（exit={rc}）\n{so[-800:]}")
            sys.exit(1)
        ok("NC2 W→17/2⁵² ⟹ ② W 恒等式失配 exit 1")
        # NC3a 区域截断（去尾区域）⟹ ① 覆盖检查 exit 1
        c3 = json.loads(CERT.read_text())
        c3["interval_certificate"]["regions"] = \
            c3["interval_certificate"]["regions"][:6]
        p3 = mutate_cert(c3, tmpdir, "nc3a")
        o3 = tmpdir / "nc3a.out.json"
        rc, so, r3, _ = run_reverify(
            ["--scope", "quick", "--cert", str(p3), "--out", str(o3)], o3)
        checks += 1
        if rc != 1 or (r3 or {}).get("items", {}).get("regions", {}).get("ok"):
            fail(f"NC3a 未按预期检出（exit={rc}）\n{so[-800:]}")
            sys.exit(1)
        ok("NC3a 区域截断（7→6）⟹ ① 覆盖检查 exit 1")
        # NC3b 边界翻转（区域 2 两端对调）⟹ ① 覆盖检查 exit 1
        c4 = json.loads(CERT.read_text())
        rr = c4["interval_certificate"]["regions"][2]
        rr["interval"] = [rr["interval"][1], rr["interval"][0]]
        p4 = mutate_cert(c4, tmpdir, "nc3b")
        o4 = tmpdir / "nc3b.out.json"
        rc, so, r4, _ = run_reverify(
            ["--scope", "quick", "--cert", str(p4), "--out", str(o4)], o4)
        checks += 1
        if rc != 1 or (r4 or {}).get("items", {}).get("regions", {}).get("ok"):
            fail(f"NC3b 未按预期检出（exit={rc}）\n{so[-800:]}")
            sys.exit(1)
        ok("NC3b 区域边界翻转 ⟹ ① 覆盖检查 exit 1")
        # NC4 G6 检出器负对照（R9 返工增补）：同 300 叶 slack +1e-12 偏置
        #    ⇒ 必现违例（比较方向/阈值逻辑翻红能力亲验，R9D 先例）
        viol_nc4 = [s for s in slacks if s + SND_BIAS > SND_EPS]
        checks += 1
        if not viol_nc4:
            fail("NC4 G6 检出器未按预期检出（+1e-12 偏置应产生违例）")
            sys.exit(1)
        ok(f"NC4 soundness 检出器 +1e-12 偏置 ⟹ {len(viol_nc4)}/{SND_N_LEAVES} "
           f"违例（max 偏置 slack={float(max(slacks)) + float(SND_BIAS):+.3e} "
           f"> +2.22e-16）——检出面亲验")

    wall = time.time() - t_gate
    if wall > GATE_CAP_S:
        fail(f"门总时长 {wall:.1f}s > {GATE_CAP_S}s")
        sys.exit(1)
    print(f"[gate] r9_v2iv_gate 全 {checks} 检 PASS（含 NC×5），"
          f"墙钟 {wall:.1f}s < 9 分钟；官方产出 {OUT}（门不触写，树净）",
          flush=True)
    sys.exit(0)


if __name__ == "__main__":
    main()
