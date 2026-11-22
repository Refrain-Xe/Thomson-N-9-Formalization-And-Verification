#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""cap_ladder.py —— N=9 near-sharp cap 阶梯与收尾设计的数据脚本（GAP-REPORT ③-3 落地）。

背景（N=9 与 N=7 的结构性反转，GAP-REPORT.md ②）：TTP 的最小内积
m* = −0.7475605 在主战场内部，任何 a₀ ≤ m* 的切口上三点 SDP 值 ≤ E*，
正裕度不存在；收尾只能靠"抬切口把 B(a₀) 逼近 E* + 定量稳定性 + 管状 +
刚性 + 全空间局部极小"。本脚本产出该路线的核心数据：

  子命令（每个都可单独跑，单命令 ≤10 分钟）：
    --solve TAG      解一档阶梯：a₀ ∈ {−0.90,−0.85,−0.80,−0.77,−0.755} 的
                     三点 SDP（midlarge=(8,6)，与 sdp_bound 同种子同参数，
                     Clarabel 主 / SCS 兜底），数值复核（sdp_bound.verify）
                     + TTP 复核 + 解数据落盘 results/cap_solution_<tag>.json，
                     合并进 results/cap_ladder.json；
                     断言 0 < e_safe ≤ E* + 1e-6（B(a₀) := 诚实折减界 e_safe）。
    --finalize       汇总：逐档断言、B(a₀) vs E* 差距、单调性检查、与 Round 1
                     存档（results/sdp.json m=−0.90 midlarge）的逐位交叉核对、
                     TTP 谱块；选出最好一档。
    --residual       残余量化（最好一档，数值证据）：
                     (a) slack 多项式在 Gram 域的自适应网格扫描 → 管半径
                         ρ_∞(ε)/ρ_spec(ε)（ε-水平集离 TTP 三点组的最大距离）；
                     (b) 求解器精度需求反推（要逼出 ε-管，恒等式残差 R1 需多小）；
                     (c) TTP 处 Riemann Hessian 谱（模旋转本质谱）+ 测地凸性
                         半径采样 → 能量-距离不等式的数值版本。
    --certify TAG    把该档的解数据走 sdp_certify 的精确认证链（dyadic 舍入＋
                     PSD 修复＋纯 Fraction 残差折减＋exact.py LDLᵀ），落盘
                     certificates/n9-stage-a3-cap-<tag>.json，摘要并入
                     cap_ladder.json。a₀ 以精确有理数入证书（切口参数化）。

  输出：results/cap_ladder.json（阶梯表 + 断言 + 残余量化 + 认证摘要）。
  诚实边界：--solve/--residual 的数字是**数值下界/数值证据**（e_safe 的折减中
  sup(H−φ) 是格点采样＋H″ 余量，非无穷维严格界）；只有 --certify 产出的
  certified 是精确有理数（覆盖范围 min 内积 ≥ a₀ 的构型，非全局）。

用法（thomson-n9 下）：
  numerics/.venv/bin/python numerics/bounds/cap_ladder.py --solve m090
  ...（m085/m080/m077/m0755 各一命令，~4-6 分钟/档）
  numerics/.venv/bin/python numerics/bounds/cap_ladder.py --finalize
  numerics/.venv/bin/python numerics/bounds/cap_ladder.py --residual
  numerics/.venv/bin/python numerics/bounds/cap_ladder.py --certify m0755
依赖：numpy/scipy（全路径）；cvxpy+clarabel 仅 --solve 需要（numerics/.venv）。
固定种子 20261003（同 sdp_bound.CFG.SEED）；求解器参数取 sdp_bound.CFG 原值。
"""
from __future__ import annotations

import argparse
import hashlib
import json
import random
import sys
import time
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]                                    # .../thomson-n9
sys.path.insert(0, str(HERE))                             # sdp_bound / sdp_certify
sys.path.insert(0, str(HERE.parents[2] / "thomson-workflow" / "certificates"))
sys.path.insert(0, str(HERE.parents[1] / "numerics"))     # family（ttp_check 内部再插）

import sdp_bound                                           # noqa: E402

SEED = sdp_bound.CFG["SEED"]                               # 20261003
CONFIG = "midlarge"
M, K = sdp_bound.CFG["CONFIGS"][CONFIG]                    # (8, 6)
PHI_TOL = Fraction(1, 10 ** 6)

# 阶梯：tag → (float a₀, 精确有理 a₀)。全部 a₀ ≤ −0.755 < m* ≈ −0.74756，
# 即每一档 TTP 都可行 ⇒ SDP 值 ≤ E*（断言 B ≤ E*+1e-6 的结构原因）。
LADDER = [
    ("m090", -0.90, Fraction(-9, 10)),
    ("m085", -0.85, Fraction(-17, 20)),
    ("m080", -0.80, Fraction(-4, 5)),
    ("m077", -0.77, Fraction(-77, 100)),
    ("m0755", -0.755, Fraction(-151, 200)),
]
LADDER_BY_TAG = {t: (af, ax) for t, af, ax in LADDER}

OUT_PATH = HERE / "results" / "cap_ladder.json"


# ============================================================ 公共
def load_json(path):
    with open(path) as f:
        return json.load(f)


def dump(doc):
    OUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    with open(OUT_PATH, "w") as f:
        json.dump(doc, f, ensure_ascii=False, indent=2)
    print(f"[out] 已写入 {OUT_PATH}", flush=True)


def load_doc():
    if OUT_PATH.exists():
        return load_json(OUT_PATH)
    return {"kind": "cap_ladder", "script": "cap_ladder.py", "ladder": [],
            "seed": SEED}


def e_star_and_refs():
    energies = load_json(HERE.parents[2] / "thomson-workflow" / "data" / "energies.json")
    E_star = float(energies["energies"]["9"]["value"])
    lp_record = Fraction(load_json(REPO / "certificates" / "n9-stage-a.json")["claimed_bound"])
    sdpj = load_json(HERE / "results" / "sdp.json")
    return E_star, energies["energies"]["9"]["highPrecision"], lp_record, sdpj


def ttp_config():
    """TTP 候选（z* Brent）与其 Gram 量——与 sdp_bound.ttp_check 同路径。"""
    from family import tri_cap_prism
    from scipy.optimize import minimize_scalar
    fE = lambda z: float(np.sum(
        1.0 / np.linalg.norm(tri_cap_prism(z)[:, None, :] - tri_cap_prism(z)[None, :, :],
                             axis=2)[np.triu_indices(9, 1)]))
    res = minimize_scalar(fE, bounds=(0.4, 0.9), method="bounded",
                          options={"xatol": 1e-13})
    z = float(res.x)
    X = tri_cap_prism(z)
    return z, X, float(fE(z))


def spectrum_block():
    z, X, E = ttp_config()
    G = X @ X.T
    t = np.sort(G[np.triu_indices(9, 1)])
    vals, counts = np.unique(np.round(t, 10), return_counts=True)
    nodes = [float(v) for v in vals]
    return dict(z_star=z, E_ttp=E, min_inner=float(t.min()),
                nodes=nodes, multiplicities=[int(c) for c in counts],
                min_spectral_gap=float(np.min(np.diff(vals))),
                note="6 节点谱 −0.7476/−0.7105/−0.5/0.0098/0.2427/0.3553，重数 6/6/3/3/6/12",
                method="family.tri_cap_prism + Brent（同 sdp_bound.ttp_check 路径）")


# ============================================================ --solve
def cmd_solve(tag, verbose=False):
    sdp_bound.require_cvxpy()
    a_fl, a_ex = LADDER_BY_TAG[tag]
    E_star, _, lp_record, _ = e_star_and_refs()
    doc = load_doc()
    doc.setdefault("target", {"N": 9, "E_star": E_star})
    doc["target"] = {"N": 9, "E_star": E_star,
                     "source": "thomson-workflow/data/energies.json energies.9.value"}
    doc.setdefault("reference", {})["lp_record_strict"] = float(lp_record)
    doc["reference"]["round1_sdp_esafe_m090"] = 25.752724580516784  # results/sdp.json 存档
    doc["reference"]["m_star_ttp"] = -0.7475605325955157

    rng = np.random.default_rng(SEED)
    maps = sdp_bound.assemble_maps(9, a_fl, M, K)
    ks = sdp_bound.kernel_selftest(maps, rng)
    ids = sdp_bound.identity_selftest(maps, rng)
    print(f"[selftest] Q 恒等式 max err {ks['Q_identity_max_err']:.2e}；正性 ok="
          f"{ks['positivity_ok']}；三点恒等式 ok={ids['ok']}", flush=True)
    if not (ks["positivity_ok"] and ids["ok"]):
        print("[assert] 自检失败——拒绝出界", flush=True)
        sys.exit(1)

    print(f"[{tag}] N=9 a₀={a_fl}（精确 {a_ex}）config={CONFIG} (M={M},K={K})", flush=True)
    t0 = time.time()
    e_val, info, chk, maps, V = sdp_bound.solve_case(9, a_fl, M, K, verbose=verbose)
    wall = time.time() - t0
    print(f"[{tag}] e_raw = {e_val!r}（{info['solver']} {info['status']}，"
          f"构建 {info['build_s']}s + 求解 {info['solve_s']}s）", flush=True)
    ttp = None
    if chk:
        print(f"[{tag}] 复核：resid_slack={chk['identity_residual_slack']:.2e} "
              f"resid_minor={chk['identity_residual_minorant']:.2e} "
              f"slack_min={min(chk['slack_min_random'], chk['slack_min_boundary']):.2e} "
              f"minor_viol={chk['minorant_max_violation']:.2e} "
              f"accepted={chk['accepted']}", flush=True)
        print(f"[{tag}] 折减 Δ={chk['deflation']:.3e} → e_safe={chk['e_safe']:.9f}",
              flush=True)
        if chk["e_safe"] > 0:
            ttp = sdp_bound.ttp_check(V["h"].value, chk["e_safe"], E_star)
            print(f"[{tag}] TTP：{json.dumps(ttp, ensure_ascii=False)}", flush=True)

    # 解数据落盘（sdp_certify 兼容格式，供 --certify 复用）
    sol = dict(
        h=[float(x) for x in V["h"].value],
        e=float(V["e"].value),
        F=[((np.asarray(Fk.value) + np.asarray(Fk.value).T) / 2).tolist()
           for Fk in V["F"]],
        B={name: ((np.asarray(Bv.value) + np.asarray(Bv.value).T) / 2).tolist()
           for name, _A, Bv in V["sos"]},
        sig={name: ((np.asarray(Bv.value) + np.asarray(Bv.value).T) / 2).tolist()
             for name, _A, Bv, _my, _mu in V["sig"]},
        solver_info={k2: v for k2, v in info.items()},
        verify=chk,
        a0=float(a_fl), a0_exact=str(a_ex), tag=tag,
        timestamp=datetime.now(timezone.utc).isoformat(timespec="seconds"),
    )
    sol_path = HERE / "results" / f"cap_solution_{CONFIG}_{tag}.json"
    txt = json.dumps(sol, ensure_ascii=False)
    sol_path.write_text(txt)
    sol_sha = hashlib.sha256(txt.encode()).hexdigest()[:16]
    print(f"[out] 解数据 {sol_path}（{len(txt)} 字节）", flush=True)

    B_val = float(chk["e_safe"]) if chk else float("nan")
    entry = dict(
        tag=tag, a0=a_fl, a0_exact=str(a_ex), config=CONFIG, M=M, K=K,
        B=B_val, e_raw=float(e_val),
        gap_E_star_B=E_star - B_val, gap_E_star_raw=E_star - float(e_val),
        deflation=float(chk["deflation"]) if chk else None,
        check=chk, ttp=ttp,
        solve=dict(solver=info["solver"], status=info["status"],
                   build_s=info["build_s"], solve_s=info["solve_s"], wall_s=round(wall, 1),
                   n_scalar_vars=info["n_scalar_vars"], n_eq_rows=info["n_eq_rows"],
                   nmon_slack=info["nmon_slack"], F_sizes=info["F_sizes"],
                   sos_block_sizes=info["sos_block_sizes"],
                   sig_sizes=info["sig_sizes"]),
        solution_file=str(sol_path.relative_to(REPO)), solution_sha256_16=sol_sha,
        run=dict(timestamp=datetime.now(timezone.utc).isoformat(timespec="seconds"),
                 argv=sys.argv[1:],
                 repro=f"numerics/.venv/bin/python numerics/bounds/cap_ladder.py --solve {tag}"),
    )
    doc["ladder"] = [c for c in doc.get("ladder", []) if c["tag"] != tag] + [entry]
    doc["ladder"].sort(key=lambda c: c["a0"])
    dump(doc)

    ok = chk is not None and 0 < B_val <= E_star + 1e-6
    print(f"[assert] {'PASS' if ok else 'FAIL'}：0 < B({a_fl}) = {B_val!r} "
          f"≤ E* + 1e-6 = {E_star + 1e-6!r}", flush=True)
    if not ok:
        sys.exit(1)
    # 与 Round 1 存档交叉核对（仅 m090 有存档可比）
    if tag == "m090":
        _, _, _, sdpj = e_star_and_refs()
        case = next((c for c in sdpj["cases"]
                     if c["m"] == -0.9 and c["config"] == "midlarge"), None)
        if case is not None:
            same = (float(e_val) == case["e"])
            print(f"[xcheck] m090 复跑 e 与 results/sdp.json 存档逐位一致：{same}"
                  f"（存档 {case['e']!r}）", flush=True)
            entry["bitwise_match_round1_archive"] = bool(same)
            dump(doc)


# ============================================================ --finalize
def cmd_finalize():
    E_star, E_hp, lp_record, sdpj = e_star_and_refs()
    doc = load_doc()
    entries = doc.get("ladder", [])
    if len(entries) < 5:
        print(f"[warn] 阶梯只有 {len(entries)} 档（任务要求 ≥5）", flush=True)
    doc["reference"].update(lp_record_strict=float(lp_record),
                            E_star_high_precision=E_hp)
    all_ok = True
    print(f"\n=== cap 阶梯（E* = {E_star:.9f}，LP 严格纪录 = {float(lp_record):.9f}）===",
          flush=True)
    print(f"{'a₀':>7} {'e_raw':>15} {'B=e_safe':>15} {'E*−B':>11} {'E*−raw':>11} "
          f"{'Δ折减':>9} {'status':>20} {'vars':>7}", flush=True)
    for c in entries:
        ok = 0 < c["B"] <= E_star + 1e-6
        all_ok &= ok
        print(f"{c['a0']:>7} {c['e_raw']:>15.9f} {c['B']:>15.9f} "
              f"{c['gap_E_star_B']:>11.3e} {c['gap_E_star_raw']:>11.3e} "
              f"{c['deflation']:>9.2e} {c['solve']['status']:>20} "
              f"{c['solve']['n_scalar_vars']:>7}", flush=True)
        c["assert_bound_range"] = bool(ok)
    if entries:
        best = max(entries, key=lambda c: c["B"])
        doc["best"] = dict(tag=best["tag"], a0=best["a0"], B=best["B"],
                           e_raw=best["e_raw"], gap_E_star=best["gap_E_star_B"])
        print(f"[best] {best['tag']}（a₀={best['a0']}）：B = {best['B']:.9f}，"
              f"E* − B = {best['gap_E_star_B']:.9f}", flush=True)
        # 单调性（精确 SDP 值对 a 非降；数值违反 = 求解器噪声指示，不硬断言）
        mono_raw = all(entries[i]["e_raw"] <= entries[i + 1]["e_raw"] + 1e-9
                       for i in range(len(entries) - 1))
        mono_B = all(entries[i]["B"] <= entries[i + 1]["B"] + 1e-9
                     for i in range(len(entries) - 1))
        doc["monotonicity"] = dict(e_raw_nondecreasing=bool(mono_raw),
                                   e_safe_nondecreasing=bool(mono_B),
                                   note="精确松弛值对 a₀ 单调非降是数学事实；"
                                        "False 仅指示求解器噪声")
        print(f"[mono ] e_raw 非降：{mono_raw}；e_safe 非降：{mono_B}", flush=True)
        if not mono_raw:
            for i in range(len(entries) - 1):
                if entries[i]["e_raw"] > entries[i + 1]["e_raw"] + 1e-9:
                    print(f"[mono ]   违反：a₀ {entries[i]['a0']} → "
                          f"{entries[i+1]['a0']}：{entries[i]['e_raw']:.9f} → "
                          f"{entries[i+1]['e_raw']:.9f}", flush=True)
    doc.setdefault("ttp_spectrum", spectrum_block())
    doc["finalized"] = datetime.now(timezone.utc).isoformat(timespec="seconds")
    dump(doc)
    if not all_ok:
        print("[assert] 存在档违反 0 < B ≤ E*+1e-6", flush=True)
        sys.exit(1)
    print("[assert] 全部档 0 < B(a₀) ≤ E* + 1e-6 PASS", flush=True)


# ============================================================ --residual
def slack_coeffs(a_fl, sol):
    maps = sdp_bound.assemble_maps(9, a_fl, M, K)
    h = np.array(sol["h"])
    Fvec = np.concatenate([np.asarray(F).reshape(-1) for F in sol["F"]])
    AR = sdp_bound.dense_to_sparse(maps["R_cols"]).toarray()
    return maps, maps["Ch"] @ h + maps["c_e"] * sol["e"] - AR @ Fvec


def eval_slack(ring, coeff, u, v, t):
    return ring.eval_batch(coeff, u, v, t)


def ttp_triples(X):
    G = X @ X.T
    n = len(X)
    idx = [(i, j, l) for i in range(n) for j in range(n) for l in range(n)
           if i != j and j != l and i != l]
    return np.array([[G[i, j], G[i, l], G[j, l]] for (i, j, l) in idx])


def scan_tube(a_fl, sol, eps_list, n_grid=256, chunk_axis=8, chunk=2_000_000):
    """全域均匀网格流式扫描（数值证据）。

    对每档 ε：ρ_∞(ε) = max over {(u,v,t)∈Gram域, slack≤ε} 的 min_τ ‖·−τ‖_∞
    （τ 取遍 TTP 三点组去重集）；ρ_spec(ε) = 同点集上"坐标到 6 节点谱最小距离"
    的最大值。距离函数 1-Lipschitz ⇒ ρ_true ≤ ρ_grid + √3·h（分辨率 h 报出）。
    附带：全域 min slack（负值深度 = 求解器残差指示）、99.9 分位梯度幅值。
    """
    from scipy.spatial import cKDTree
    maps, coeff = slack_coeffs(a_fl, sol)
    ring = maps["ring"]
    z, X, _ = ttp_config()
    trips = ttp_triples(X)
    uniq = np.unique(np.round(trips, 9), axis=0)          # TTP 三点组（去重）
    spec = np.array(spectrum_block()["nodes"])
    tree = cKDTree(uniq)

    g = np.linspace(a_fl, 1.0, n_grid)
    h = float(g[1] - g[0])
    eps_max = max(eps_list)
    res = {eps: dict(rho_inf=-1.0, rho_spec=-1.0, n_points=0, worst_point=None)
           for eps in eps_list}
    min_slack_global = np.inf
    grad_p999 = []
    step = max(1, n_grid // chunk_axis)
    for s0 in range(0, n_grid, step):
        gs = g[s0:s0 + step]
        U, Vv, T = np.meshgrid(gs, g, g, indexing="ij")
        det = 1 + 2 * U * Vv * T - U**2 - Vv**2 - T**2
        mask = det >= 0
        pts = np.stack([U[mask], Vv[mask], T[mask]], axis=1)
        del U, Vv, T, det
        for s in range(0, len(pts), chunk):
            p = pts[s:s + chunk]
            sl = eval_slack(ring, coeff, p[:, 0], p[:, 1], p[:, 2])
            if sl.min() < min_slack_global:
                min_slack_global = float(sl.min())
            # 梯度幅值（差分级：直接多项式求导，采样留档）
            if s == 0:
                pw = [np.ones(len(p))] + [None] * (ring.D + 1)
                for i in range(1, ring.D + 1):
                    pw[i] = pw[i - 1] * p[:, 0]
                pv = [np.ones(len(p))] + [None] * (ring.D + 1)
                for i in range(1, ring.D + 1):
                    pv[i] = pv[i - 1] * p[:, 1]
                pt_ = [np.ones(len(p))] + [None] * (ring.D + 1)
                for i in range(1, ring.D + 1):
                    pt_[i] = pt_[i - 1] * p[:, 2]
                gu = np.zeros(len(p)); gv = np.zeros(len(p)); gt = np.zeros(len(p))
                for q, c in enumerate(coeff):
                    if c == 0.0:
                        continue
                    i, j, l = ring.mons[q]
                    if i:
                        gu += c * i * pw[i - 1] * pv[j] * pt_[l]
                    if j:
                        gv += c * j * pw[i] * pv[j - 1] * pt_[l]
                    if l:
                        gt += c * l * pw[i] * pv[j] * pt_[l - 1]
                grad_p999.append(float(np.percentile(
                    np.sqrt(gu**2 + gv**2 + gt**2), 99.9)))
            m = sl <= eps_max
            if not m.any():
                continue
            p = p[m]
            d_inf = tree.query(p, k=1, p=np.inf)[0]
            d_spec = np.min(np.abs(p[:, :, None] - spec[None, None, :]),
                            axis=(1, 2))
            for eps in eps_list:
                me = sl[m] <= eps
                if not me.any():
                    continue
                di = d_inf[me]
                r = res[eps]
                r["n_points"] += int(me.sum())
                j = int(np.argmax(di))
                if di[j] > r["rho_inf"]:
                    r["rho_inf"] = float(di[j])
                    r["worst_point"] = [float(x) for x in p[me][j]]
                r["rho_spec"] = max(r["rho_spec"], float(d_spec[me].max()))
    for eps in eps_list:
        if res[eps]["rho_inf"] < 0:
            res[eps] = dict(rho_inf=None, rho_spec=None, n_points=0)
    Lgrad = float(max(grad_p999))
    print(f"[scan] 均匀网格 n={n_grid}（h={h:.2e}）：min slack = {min_slack_global:.3e}；"
          f"梯度幅值 P99.9 = {Lgrad:.2e}", flush=True)
    return res, uniq, float(min_slack_global), Lgrad, h


def two_point_tube(a_fl, E_star, delta, n=400001):
    """两点强制管：LP 精确证书 f 的 g(t) = φ(t) − f(t) ≥ 0 于 [−1,1)。

    对任何构型 Σ_{36 对} g(t_ij) = E − Σf ≤ E − B_LP（B_LP = LP 精确界，
    对一切构型成立）；故 E ≤ E* 的构型每对满足 g(t_ij) ≤ E* − B_LP。
    （36 项求和、各项 ≥ 0 ⇒ 单项 ≤ 全和；LP 证书是精确有理数，无求解器噪声。）
    扫描 {t ∈ [a₀,1): g ≤ s} 的区间结构与离 TTP 6 节点的距离。
    """
    lp = load_json(HERE / "results" / "lp.json")
    from fractions import Fraction as Fr
    # lp_bound.py 落盘的证书系数已是 η 平移后的 ĉ（f̂ ≤ φ 精确成立）
    coefs = [float(Fr(c)) for c in lp["certificate"]["coeffs_legendre_exact"]]
    B_LP = float(Fr(lp["bound_exact"]))
    t = np.linspace(a_fl, 1.0 - 1e-9, n)
    f = np.polynomial.legendre.legval(t, coefs)
    g = 1.0 / np.sqrt(2.0 - 2.0 * t) - f
    nodes = np.array(spectrum_block()["nodes"])
    sum_g_bound = E_star - B_LP

    def tube_at(s):
        m = g <= s
        # 区间提取
        d = np.diff(m.astype(np.int8))
        starts = list(np.where(d == 1)[0] + 1)
        ends = list(np.where(d == -1)[0] + 1)
        if m[0]:
            starts = [0] + starts
        if m[-1]:
            ends = [len(t)] + ends
        ivs = [(float(t[s0]), float(t[e - 1])) for s0, e in zip(starts, ends)]
        total = sum(hi - lo for lo, hi in ivs)
        # 管内点离 TTP 节点的最大距离（分辨率 (1-a)/n）
        dd = np.min(np.abs(t[:, None] - nodes[None, :]), axis=1)
        max_dist = float(dd[m].max()) if m.any() else None
        # 每个区间的中点与宽度（供设计用，只报前 8 个）
        detail = [dict(lo=lo, hi=hi, width=hi - lo) for lo, hi in ivs]
        detail.sort(key=lambda x: -x["width"])
        return dict(n_intervals=len(ivs), total_measure=float(total),
                    max_dist_to_ttp_nodes=max_dist,
                    intervals_widest_first=detail[:8])

    tubes = {str(s): tube_at(s) for s in (sum_g_bound,
                                          float(Fr(str(0.03))),
                                          float(Fr(str(0.01))),
                                          float(Fr(str(0.003))))}
    g_nodes = [float(np.polynomial.legendre.legval(x, coefs)) for x in nodes]
    return dict(sum_g_bound=float(sum_g_bound), B_LP=B_LP,
                deg=len(coefs) - 1, n_grid=n, grid_resolution=float(t[1] - t[0]),
                min_g=float(g.min()), argmin_g=float(t[int(np.argmin(g))]),
                g_at_ttp_nodes={f"{nd:.6f}": float(
                    1.0 / np.sqrt(2.0 - 2.0 * nd)
                    - np.polynomial.legendre.legval(nd, coefs)) for nd in nodes},
                g_at_nodes_report=g_nodes, tubes=tubes,
                derivation=("每对 g(t_ij) ≤ Σg = E−Σf ≤ E*−B_LP（Σf ≥ B_LP 对一切"
                            "构型、B_LP 为 LP 精确证书界）；g 用 lp.json 精确有理"
                            "系数以 float 求值（数值扫描，系数本身精确）"),
                status="numerical scan on exact-certificate minorant")


def hessian_analysis(X, n_dirs=48, t_grid=None):
    """TTP 处 E 的 Riemann Hessian 谱（模旋转）+ 测地二阶增长采样（数值）。"""
    def energy(Y):
        d = np.linalg.norm(Y[:, None, :] - Y[None, :, :], axis=2)
        return float(np.sum(1.0 / d[np.triu_indices(len(Y), 1)]))

    def grad(Y):
        n = len(Y)
        g = np.zeros_like(Y)
        for i in range(n):
            for j in range(n):
                if i == j:
                    continue
                r = Y[i] - Y[j]
                g[i] -= r / np.linalg.norm(r) ** 3
        return g

    def hess(Y):
        n = len(Y)
        H = np.zeros((3 * n, 3 * n))
        for i in range(n):
            for j in range(i + 1, n):
                r = Y[i] - Y[j]
                d = np.linalg.norm(r)
                blk = (3.0 * np.outer(r, r) / d**2 - np.eye(3)) / d**3
                H[3 * i:3 * i + 3, 3 * j:3 * j + 3] = -blk
                H[3 * j:3 * j + 3, 3 * i:3 * i + 3] = -blk
                H[3 * i:3 * i + 3, 3 * i:3 * i + 3] += blk
                H[3 * j:3 * j + 3, 3 * j:3 * j + 3] += blk
        return H

    Y = X / np.linalg.norm(X, axis=1, keepdims=True)
    g = grad(Y)
    H = hess(Y)
    # 球面拉格朗日修正：Hess_L = ∇²E + Σ μ_i I（μ_i = −x_i·∇_i E），切向取值
    mu = np.array([-float(Y[i] @ g[i]) for i in range(len(Y))])
    for i in range(len(Y)):
        H[3 * i:3 * i + 3, 3 * i:3 * i + 3] += mu[i] * np.eye(3)
    P = np.zeros((3 * len(Y), 3 * len(Y)))
    for i in range(len(Y)):
        P[3 * i:3 * i + 3, 3 * i:3 * i + 3] = np.eye(3) - np.outer(Y[i], Y[i])
    # 切空间基（27 → 18 维）：逐点切平面正交基拼接
    basis = []
    for i in range(len(Y)):
        e1 = np.cross(Y[i], [0, 0, 1.0])
        if np.linalg.norm(e1) < 0.5:
            e1 = np.cross(Y[i], [0, 1.0, 0])
        e1 /= np.linalg.norm(e1)
        e2 = np.cross(Y[i], e1)
        basis += [e1, e2]
    Tb = np.zeros((3 * len(Y), 2 * len(Y)))
    for c, e in enumerate(basis):
        i = c // 2
        Tb[3 * i:3 * i + 3, c] = e
    HT = Tb.T @ H @ Tb
    w = np.linalg.eigvalsh((HT + HT.T) / 2)
    # 与测地有限差分的交叉复核（随机方向 v：d²/dt² E(exp(tv)) ≈ vᵀH v / ‖v‖²）
    def exp_map(xi):
        Z = np.zeros_like(Y)
        for i in range(len(Y)):
            nrm = np.linalg.norm(xi[i])
            if nrm < 1e-15:
                Z[i] = Y[i]
            else:
                Z[i] = np.cos(nrm) * Y[i] + np.sin(nrm) * xi[i] / nrm
        return Z
    rng = np.random.default_rng(SEED)
    errs = []
    for _ in range(6):
        v = rng.normal(size=(len(Y), 3))
        v = np.einsum("ij,ijk->ik", v, np.eye(3)[None] - np.array(
            [np.outer(Y[i], Y[i]) for i in range(len(Y))]))
        v /= np.linalg.norm(v)
        h2 = 1e-5
        e0 = energy(Y)
        ep = energy(exp_map(v * h2))
        em = energy(exp_map(-v * h2))
        fd = (ep - 2 * e0 + em) / h2**2
        an = float(v.reshape(-1) @ H @ v.reshape(-1))
        errs.append(abs(fd - an) / max(1.0, abs(an)))
    # 二阶增长半径：随机方向上 E−E* ≥ (λ₊/4)·t² 成立的最大 t（采样版）
    lam_pos = w[w > 1e-8]
    lam_plus = float(lam_pos.min()) if len(lam_pos) else float("nan")
    R_num = 0.0
    if t_grid is None:
        t_grid = np.linspace(0.02, 3.0, 80)
    e0 = energy(Y)
    ok_all = np.ones(len(t_grid), dtype=bool)
    for _ in range(n_dirs):
        v = rng.normal(size=(len(Y), 3))
        v = np.einsum("ij,ijk->ik", v, np.array(
            [np.eye(3) - np.outer(Y[i], Y[i]) for i in range(len(Y))]))
        v /= np.linalg.norm(v)
        vals = np.array([energy(exp_map(v * t)) - e0 for t in t_grid])
        ok_all &= vals >= 0.25 * lam_plus * t_grid**2
    # R_num：前缀意义下全方向通过的最大 t（二阶增长 E−E* ≥ (λ₊/4)t² 的采样半径）
    prefix_ok = np.cumprod(ok_all).astype(bool)
    idx = np.where(prefix_ok)[0]
    R_num = float(t_grid[idx.max()]) if len(idx) else 0.0
    return dict(eigenvalues=[float(x) for x in w],
                n_zero_modes=int(np.sum(np.abs(w) < 1e-8)),
                lambda_plus=lam_plus,
                gradient_tangent_norm=float(np.linalg.norm(P @ g.reshape(-1))),
                fd_crosscheck_max_rel_err=float(max(errs)),
                second_growth_radius_sampled=R_num,
                n_dirs=n_dirs, t_grid=[float(t_grid[0]), float(t_grid[-1])],
                note="27 维嵌入 → 18 维切空间 Hessian（球面 Lagrange 修正）；"
                     "≈3 个零模 = 旋转轨道方向（理论预期）；二阶增长半径为随机方向采样，"
                     "非穷尽——数值证据")


def cmd_residual():
    E_star, _, lp_record, _ = e_star_and_refs()
    doc = load_doc()
    if "best" not in doc:
        cmd_finalize()
        doc = load_doc()
    best = doc["best"]
    entry = next(c for c in doc["ladder"] if c["tag"] == best["tag"])
    a_fl, a_ex = entry["a0"], entry["a0_exact"]
    sol = load_json(HERE.parents[1] / entry["solution_file"])
    print(f"[residual] 最好档 {best['tag']}（a₀={a_fl}）：B={best['B']:.9f}，"
          f"δ=E*−B={best['gap_E_star']:.9f}", flush=True)

    maps, coeff = slack_coeffs(a_fl, sol)
    ring = maps["ring"]
    z, X, E_ttp = ttp_config()
    trips = ttp_triples(X)
    sl_ttp = eval_slack(ring, coeff, trips[:, 0], trips[:, 1], trips[:, 2])
    dsum = float(sl_ttp.sum())
    # 每三点固有松弛：ΣH(TTP)−e = (dsum(slack)+7Σ_all)/14；Σ_all(TTP)≥0 数值上
    sumH_ttp = entry["ttp"]["sumH_at_ttp"]
    g_intr = 14.0 * (sumH_ttp - sol["e"]) / 504.0
    print(f"[residual] TTP 处 slack：min={sl_ttp.min():.3e} max={sl_ttp.max():.3e} "
          f"mean={sl_ttp.mean():.3e}；dsum={dsum:.6f}", flush=True)
    print(f"[residual] 每三点固有间隙 14(ΣH(TTP)−e)/504 = {g_intr:.3e}"
          f"（Σ_all(TTP)≈0 时即 TTP 处逐点 slack 水平）", flush=True)

    eps_list = [2e-5, 5e-5, 2e-4, 1e-3, 5e-3, 2e-2]
    tube, uniq_trips, min_slack_global, Lgrad, h_grid = scan_tube(
        a_fl, sol, eps_list, n_grid=256)
    spec = doc["ttp_spectrum"]
    print(f"\n[ tube ] ε-水平集离 TTP 三点组的最大距离（L∞；网格 h={h_grid:.1e}）：",
          flush=True)
    print(f"{'ε':>9} {'ρ_∞':>10} {'ρ_spec':>10} {'点数':>10}", flush=True)
    for eps in eps_list:
        r = tube.get(eps) if tube else None
        if r is None or r["rho_inf"] is None:
            print(f"{eps:>9.0e} {'—':>10}", flush=True)
        else:
            print(f"{eps:>9.0e} {r['rho_inf']:>10.5f} {r['rho_spec']:>10.5f} "
                  f"{r['n_points']:>10}", flush=True)

    # 精度需求反推：要逼出 ε-target 管，恒等式残差需多小
    chk = entry["check"]
    w = chk["viol_fine"]
    r1 = chk["identity_l1_slack"] + chk["psd_deficit_sos"]
    psd_f = chk["psd_deficit_F"]
    delta = best["gap_E_star"]
    e = sol["e"]

    def eps_forced(E_band, r1_val):
        """E ≤ E_band 的构型的**每个** Gram 三点 slack ≤ 本值（推导）：
        dsum(slack) + 7Σ_all = 14(ΣH−e)，ΣH ≤ E_band+36w，Σ_all ≥ −psdF/14
        ⇒ Σ_{504}(slack+r1) = dsum+504r1 ≤ 14(E_band+36w−e)+psdF/2+504r1；
        各项 ≥ 0 ⇒ 单项 ≤ 全和（**不除 504**——N=7 收尾正是靠取等把全和压到 0
        才消掉这个 ×504 放大；这里如实带放大）。"""
        return 14.0 * (E_band + 36 * w - e) + psd_f / 2.0 + 503.0 * r1_val

    eps_now_band = eps_forced(E_star + delta, r1)      # 任务书带：E ≤ E*+δ, δ=E*−B
    eps_now_star = eps_forced(E_star, r1)              # 收尾带：E ≤ E*
    print(f"\n[ forced ] 三点逐点强制水平 ε（当前精度 r1={r1:.2e}；含 ×504 放大）：",
          flush=True)
    print(f"  E ≤ E*+δ（δ={delta:.6f}）：ε = {eps_now_band:.3e}", flush=True)
    print(f"  E ≤ E*        ：ε = {eps_now_star:.3e}"
          f"（其中 14(E*−e) = {14.0*(E_star-e):.3e} 为原始松弛间隙贡献）",
          flush=True)
    r1_sens = {}
    for r1_hyp in [1e-6, 1e-7, 1e-8]:
        r1_sens[r1_hyp] = dict(band_Estar_plus_delta=eps_forced(E_star + delta, r1_hyp),
                               band_Estar=eps_forced(E_star, r1_hyp))
        print(f"  假想 r1={r1_hyp:.0e}：ε(E≤E*) = {r1_sens[r1_hyp]['band_Estar']:.3e}，"
              f"ε(E≤E*+δ) = {r1_sens[r1_hyp]['band_Estar_plus_delta']:.3e}", flush=True)
    prec = {}
    for eps_t in eps_list:
        # 单点 slack ≤ 14(E*+δ+36w−e) + psdF/2 + 503·r1 ⇒ r1 需求
        eff = eps_t - (14.0 * (E_star + delta + 36 * w - e) + psd_f / 2.0)
        r1_need = eff / 503.0 if eff > 0 else 0.0
        prec[eps_t] = dict(r1_needed=float(r1_need),
                           currently=float(r1),
                           feasible_now=bool(r1 <= r1_need + 1e-18) or eff <= 0)
    print(f"\n[ prec ] 三点管水平 ε 所需恒等式残差 r1（当前 {r1:.2e}；"
          f"ε 地板＝14(E*−e)={14.0*(E_star+delta-e):.1e}）：", flush=True)
    for eps_t in eps_list:
        print(f"  ε={eps_t:.0e}: r1 ≤ {prec[eps_t]['r1_needed']:.2e}"
              f"（{'当前已满足' if prec[eps_t]['feasible_now'] else '需提升精度'}）",
              flush=True)

    # ---- 两点强制管（LP 精确证书的 φ−f；无 ×504 放大、无求解器噪声）----
    tp = two_point_tube(a_fl, E_star, delta)
    print(f"\n[ 2pt ] LP 证书 f 的 g=φ−f 于 [a₀,1)：E≤E* 反例的每对 t_ij 满足 "
          f"g(t_ij) ≤ E*−B_LP = {tp['sum_g_bound']:.6f}", flush=True)
    for s, info in tp["tubes"].items():
        print(f"  g ≤ {float(s):.6f}：{info['n_intervals']} 个区间，"
              f"总测度 {info['total_measure']:.4f}，"
              f"离 TTP 节点最大距离 {info['max_dist_to_ttp_nodes']:.4f}", flush=True)
    print(f"  g 在 TTP 6 节点处：{tp['g_at_ttp_nodes']}", flush=True)

    # Hessian 与能量-距离界
    hess = hessian_analysis(X)
    lam = hess["lambda_plus"]
    d_delta = float(np.sqrt(4.0 * delta / lam)) if lam > 0 else float("nan")
    print(f"\n[ hess ] λ₊ = {lam:.6f}（{hess['n_zero_modes']} 个零模）；"
          f"FD 交叉复核 max rel err = {hess['fd_crosscheck_max_rel_err']:.2e}；"
          f"切向梯度范数 = {hess['gradient_tangent_norm']:.2e}", flush=True)
    print(f"[ hess ] 采样二阶增长半径 R_num = {hess['second_growth_radius_sampled']}"
          f"；δ={delta:.4f} → sqrt(4δ/λ₊) = {d_delta:.4f}"
          f"（{'≤' if d_delta <= hess['second_growth_radius_sampled'] else '>'} R_num）",
          flush=True)

    doc["residual"] = dict(
        tag=best["tag"], a0=a_fl, a0_exact=a_ex,
        status="numerical evidence（格点扫描＋采样 Hessian，非严格）",
        delta=float(delta), B=float(best["B"]), e_raw=float(e),
        slack_at_ttp=dict(min=float(sl_ttp.min()), max=float(sl_ttp.max()),
                          mean=float(sl_ttp.mean()), dsum=dsum),
        per_triple_intrinsic_gap=float(g_intr),
        n_ttp_triples_distinct=int(len(uniq_trips)),
        min_slack_global=float(min_slack_global),
        grad_lipschitz_est=float(Lgrad),
        grid_resolution=float(h_grid),
        tube={str(k): v for k, v in tube.items()},
        eps_forced=dict(
            band_Estar_plus_delta=float(eps_now_band),
            band_Estar=float(eps_now_star),
            raw_gap_contribution_14_Eminus_e=float(14.0 * (E_star - e)),
            r1_sensitivity={str(k): v for k, v in r1_sens.items()},
            derivation=("每 Gram 三点 slack ≤ 14(E_band+36w−e) + psdF/2 + 503·r1"
                        "（各项 ≥ 0 ⇒ 单项 ≤ 全和，**不除 504**；由 dsum+7Σ_all = "
                        "14(ΣH−e)、ΣH ≤ E_band+36w、Σ_all ≥ −psdF/14、slack ≥ −r1）。"
                        "N=7 收尾靠证书在 cap 上精确取等把全和压到 0；(8,6) 在 "
                        "a₀→m* 仍有原始间隙 ~5.5e-4 ⇒ 14(E*−e) ~ 7.7e-3 地板"),
        ),
        precision_requirements={str(k): v for k, v in prec.items()},
        two_point_tube=tp,
        hessian=hess,
        hessian_distance_bound=dict(lambda_plus=lam, delta=float(delta),
                                    d_sqrt_4delta_over_lambda=d_delta,
                                    within_sampled_radius=bool(
                                        d_delta <= hess["second_growth_radius_sampled"])),
    )
    dump(doc)


# ============================================================ --certify
def cmd_certify(tag):
    import sdp_certify
    from thomson_certs.schema import (Certificate, decode_certificate,
                                      encode_certificate, fraction_to_str)
    from thomson_certs.exact import is_positive_definite

    a_fl, a_ex = LADDER_BY_TAG[tag]
    if a_ex > Fraction(-3, 4):
        print(f"[assert] a₀={a_ex} > −3/4：认证抽查 t 表不再域内，未预置", flush=True)
        sys.exit(1)
    # (39/40)² > (1−a)/2 精确检查（R2 权重有效域）
    assert Fraction(39, 40) ** 2 > (1 - a_ex) / 2, "B_W=39/40 < b=sqrt((1−a)/2)"
    E_star, _, lp_record, _ = e_star_and_refs()
    doc = load_doc()
    entry = next(c for c in doc["ladder"] if c["tag"] == tag)
    sol = load_json(HERE.parents[1] / entry["solution_file"])
    sol_sha = hashlib.sha256(json.dumps(
        {k2: sol[k2] for k2 in ("h", "e", "F", "B", "sig")}, sort_keys=True)
        .encode()).hexdigest()[:16]

    t_start = time.time()
    em = sdp_certify.ExactMaps(9, a_ex, M, K)
    xdiff = sdp_certify.cross_check_float_maps(
        em, sdp_bound.assemble_maps(9, a_fl, M, K))
    print(f"[maps] 精确镜像（a={a_ex}）vs 浮点装配（a={a_fl}）：最大系数偏差 "
          f"{xdiff:.2e} ✓", flush=True)
    rng = random.Random(SEED)
    id_chk = sdp_certify.exact_identity_selftest(em, rng)
    pos_chk = sdp_certify.exact_positivity_selftest(em, rng)
    print(f"[selftest] 精确三点恒等式 ==0 ×{id_chk['trials']} ✓；"
          f"精确正性 ≥0 ×{pos_chk['trials']} ✓", flush=True)

    # 认证链（sdp_certify.certify_at 以模块全局 A_EXACT 参数化域检查/抽查表）
    saved = sdp_certify.A_EXACT
    sdp_certify.A_EXACT = a_ex
    try:
        result = None
        last_err = None
        for k in (48, 56, 64):
            try:
                result = sdp_certify.certify_at(
                    em, k, sol["h"], sol["e"], sol["F"], sol["B"], sol["sig"],
                    E_star=Fraction(str(E_star)), LP_RECORD=lp_record,
                    e_stored=entry["e_raw"], e_safe_stored=entry["B"])
            except SystemExit as exc:
                last_err = exc.code
                print(f"[retry] 粒度 2^-{k} 未过断言（码 {last_err}），换粒度", flush=True)
                continue
            break
    finally:
        sdp_certify.A_EXACT = saved
    if result is None:
        print(f"[FAIL] 全部粒度未通过（最后失败码 {last_err}）", flush=True)
        sys.exit(1)
    (h_dy, e_dy, F_dy, B_dy, sig_dy, shifts, R1, R2, _rsig, certified, spot) = result
    print(f"[bound] certified = {float(certified):.12f}（粒度 2^-{k}），"
          f"R1={float(R1):.3e}，R2={float(R2):.3e}，"
          f"舍入损失 e_safe−certified = {entry['B'] - float(certified):.3e}", flush=True)

    # 证书落盘
    blocks = {"e": [[fraction_to_str(e_dy)]]}
    blocks["h_diag"] = [[fraction_to_str(h_dy[j]) if i == j else "0"
                         for j in range(em.d_H + 1)] for i in range(em.d_H + 1)]
    for kk, m_k in enumerate(em.F_sizes):
        blocks[f"F{kk}"] = [[fraction_to_str(x) for x in row] for row in F_dy[kk]]
    for name, _gnz, _mons in em.sos_blocks:
        blocks[f"B_{name}"] = [[fraction_to_str(x) for x in row] for row in B_dy[name]]
    for name, _my, _mu in em.sig_def:
        blocks[name] = [[fraction_to_str(x) for x in row] for row in sig_dy[name]]
    prov = {
        "repo": "thomson-n9",
        "generator": (f"numerics/bounds/cap_ladder.py --certify {tag}"
                      "（解数据来自 --solve 的 cap 阶梯档；认证机器复用 "
                      "numerics/bounds/sdp_certify.py，切口参数化）"),
        "date": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "upstream": ("同 certificates/n9-stage-a2-sdp.json 的推导链"
                     "（(e−36·R1)/(1+R2)；三点 SDP 构造自 N=7 证明 "
                     "references/thomson-n7-lean/paper/PAPER.md §4–5.1 移植）"),
        "params": {
            "N": 9, "a": fraction_to_str(a_ex), "M": M, "K": K,
            "D": 2 * M - 2, "d_H": 2 * M - 2, "nmon": em.nmon,
            "F_sizes": em.F_sizes, "round_bits": k,
            "b2_exact": fraction_to_str(em.b2),
            "R2_weight": "39/40（(39/40)² > (1−a)/2 精确验证）",
            "scope": (f"对一切 min_(i<j) ⟨x_i,x_j⟩ ≥ {a_ex} 的 9 点单位球面构型 "
                      f"E(x) ≥ claimed_bound。cap 阶梯档 {tag}；[−1, {a_ex}) slab "
                      "带由另一条线负责，本证书不覆盖"),
        },
        "numerical_bound": {"e_raw": sol["e"], "e_safe": entry["B"],
                            "solution_dump": entry["solution_file"],
                            "solution_sha256_16": sol_sha},
        "exact_bound": fraction_to_str(certified),
        "residual_norms": {"R1_exact": fraction_to_str(R1),
                           "R2_exact": fraction_to_str(R2)},
        "psd_shifts": {name: fraction_to_str(d) for name, d in shifts.items()},
        "rounding_loss": {"definition": "e_safe(数值折减) − certified(精确)",
                          "float": entry["B"] - float(certified)},
        "checks": {
            "exact_maps_cross_check_float": True,
            "exact_three_point_identity_random_rational": id_chk,
            "exact_lemma4_1_positivity_random_rational": pos_chk,
            "all_blocks_exact_ldlt_positive_definite": True,
            "spot_checks": spot,
            "certified_gt_lp_record": True,
            "certified_le_Estar_plus_1e-6": True,
        },
        "gap_to_E_star": {"float": float(Fraction(str(E_star)) - certified)},
        "runtime_s": round(time.time() - t_start, 1),
        "repro": (f"numerics/.venv/bin/python numerics/bounds/cap_ladder.py "
                  f"--certify {tag}"),
    }
    cert_obj = Certificate(m_lo=fraction_to_str(a_ex), m_hi="1", blocks=blocks,
                           claimed_bound=fraction_to_str(certified), provenance=prov)
    text = encode_certificate(cert_obj)
    out_path = REPO / "certificates" / f"n9-stage-a3-cap-{tag}.json"
    out_path.write_text(text)
    print(f"[out] 已写入 {out_path}（{len(text)} 字节）", flush=True)

    # 回读独立重算
    rt = decode_certificate(out_path.read_text())
    h2 = [Fraction(rt.blocks["h_diag"][j][j]) for j in range(em.d_H + 1)]
    e2 = Fraction(rt.blocks["e"][0][0])
    F2 = [[[Fraction(x) for x in row] for row in rt.blocks[f"F{kk}"]]
          for kk in range(len(em.F_sizes))]
    B2 = {name[2:]: [[Fraction(x) for x in row] for row in rt.blocks[name]]
          for name in [f"B_{gn}" for gn, _g, _m in em.sos_blocks]}
    sig2 = {name: [[Fraction(x) for x in row] for row in rt.blocks[name]]
            for name, _my, _mu in em.sig_def}
    cert2 = sdp_certify.recompute_certified(em, h2, e2, F2, B2, sig2)
    if cert2 != certified:
        print(f"[FAIL] 回读重算 {cert2} ≠ {certified}", flush=True)
        sys.exit(1)
    # 进程外式复核：只读 JSON，全部块 exact LDLᵀ 正定
    npd = 0
    for name in list(rt.blocks):
        if name in ("e", "h_diag"):
            continue
        A = [[Fraction(x) for x in row] for row in rt.blocks[name]]
        if not is_positive_definite(A):
            print(f"[FAIL] 回读块 {name} LDLᵀ 非正定", flush=True)
            sys.exit(1)
        npd += 1
    print(f"[rt  ] 回读重算逐位一致 ✓；{npd} 个 PSD 块 exact LDLᵀ 全正定 ✓", flush=True)

    doc = load_doc()
    doc.setdefault("certification", {})[tag] = dict(
        a0=a_fl, a0_exact=str(a_ex),
        certified=float(certified), certified_exact=fraction_to_str(certified),
        R1=float(R1), R2=float(R2), round_bits=k,
        rounding_loss_vs_esafe=entry["B"] - float(certified),
        gap_to_E_star=float(Fraction(str(E_star)) - certified),
        gt_lp_record=bool(certified > lp_record),
        scope=f"min inner ≥ {a_ex}",
        certificate_file=str(out_path.relative_to(REPO)),
        n_psd_blocks_ldlt=npd, runtime_s=prov["runtime_s"],
    )
    dump(doc)
    print(f"[done] certified({tag}) = {float(certified):.12f} > LP 纪录 "
          f"{float(lp_record):.9f} ✓ 且 ≤ E*+1e-6 ✓", flush=True)


# ============================================================ --design
def cmd_design():
    """把阶梯+残余量化+认证的数字装订成量化的收尾设计（endgameDesign）。"""
    doc = load_doc()
    E_star, _, lp_record, _ = e_star_and_refs()
    res = doc.get("residual", {})
    cert = doc.get("certification", {})
    best_cert = max(cert.values(), key=lambda c: c["certified"]) if cert else None
    half_gap = doc["ttp_spectrum"]["min_spectral_gap"] / 2.0
    m_star = doc["ttp_spectrum"]["min_inner"]
    a0 = doc["best"]["a0"]
    lam = res["hessian"]["lambda_plus"]
    delta = res["delta"]

    design = dict(
        headline=(
            f"cap 侧（min 内积 ≥ {a0}）严格界 certified = "
            f"{best_cert['certified']:.12f}（E*−cert = {best_cert['gap_to_E_star']:.7f}）；"
            f"收尾 = 把 cap 内 E < E* 的构型逼进 TTP 管内再刚性+局部极小排除。"
            f"本轮量化结论：untyped (8,6) 三点松弛在 a₀→m* 时原始间隙地板 ~5.5e-4，"
            f"逐点 slack 强制含 ×504 型放大（单项 ≤ 全和），ε 地板 14(E*−e)≈7.7e-3，"
            f"对应谱管宽 0.25 ≫ 需求 0.0185——**管状收尾在 (8,6) untyped 上对任意求解"
            f"精度都不成立**，需要 typed / d_H=16 / 精确取等型证书（N=7 cap 是精确取等"
            f"E(P)−2.3e-16 才使全和=0 消掉放大）。"),
        components=[
            dict(name="cap 精确界（本档已严格）",
                 status="本轮已严格",
                 quant=(f"certified(a₀={a0}) = {best_cert['certified']:.12f}，"
                        f"精确有理数证书 {best_cert['certificate_file']}；"
                        f"18 块 exact LDLᵀ 全正定、回读逐位重算一致；"
                        f"另 m077/m085 档亦已认证（{cert['m077']['certified']:.9f} / "
                        f"{cert['m085']['certified']:.9f}），覆盖面更大。"
                        f"范围：min 内积 ≥ a₀ 的构型（非全局）")),
            dict(name="管宽需求（谱管）",
                 status="数值证据（扫描）",
                 quant=(f"TTP 谱最小间隙 {doc['ttp_spectrum']['min_spectral_gap']:.5f} ⇒ "
                        f"需要 per-pair 谱管半径 ρ_spec ≤ {half_gap:.5f}（否则'靠近哪个节点'"
                        f"不唯一，刚性论证无法定型）。当前最好强制水平：三点 ε(E≤E*) = "
                        f"{res['eps_forced']['band_Estar']:.2e}（r1→0 时地板 "
                        f"{res['eps_forced']['raw_gap_contribution_14_Eminus_e']:.2e}），"
                        f"对应 ρ_spec ≈ 0.25–0.33（tube 表）；即使取 ε = TTP 自身 slack 水平"
                        f"（max {res['slack_at_ttp']['max']:.1e}），ρ_spec(2e-5) = "
                        f"{res['tube']['2e-05']['rho_spec']:.4f} 仍超需求 4 倍——"
                        f"(8,6) untyped 的 slack 零集本身太胖（ε=2e-5 水平集占 Gram 域 "
                        f"0.94% 体积）。两点 LP 管同样失效（g≤E*−B_LP=0.0305 的水平集是"
                        f"一个测度 1.32/3.99 的单区间）")),
            dict(name="强制机制（forcing）",
                 status="数值证据（公式严格、输入数值）",
                 quant=("三点：每 Gram 三点 slack ≤ 14(E+36w−e)+psdF/2+503·r1（各项≥0 ⇒ "
                        "单项≤全和，×504 型放大；N=7 靠精确取等消掉）。两点：每对 "
                        "g(t)=φ−f̂(t) ≤ E−B_LP（无放大、LP 证书精确）；LP 触点已在 TTP "
                        "三个最低节点近切（g(−0.7476)=1.9e-7、g(−0.7105)=9.5e-6、"
                        "g(−0.5)=4.2e-6），但 g 缓增 ⇒ 管胖。KLT 式 6 节点 Hermite "
                        "minorant（17 条件，strategy.md §0.2）能把 Σg(TTP) 压到 ~1e-5 级，"
                        "但两点和界仍差 0.03 ⇒ 单点预算仍 ~8e-4——**两点信息穷尽**")),
            dict(name="TTP 管内的能量-距离界（Hessian）",
                 status="数值证据",
                 quant=(f"λ₊ = {lam:.6f}（18 维切空间 Hessian 最小正特征值，3 零模=旋转；"
                        f"FD 交叉复核 {res['hessian']['fd_crosscheck_max_rel_err']:.1e}；"
                        f"采样二阶增长半径 {res['hessian']['second_growth_radius_sampled']}）⇒ "
                        f"E ≤ E*+δ（δ={delta:.4f}）⇒ 测地距离 ≤ sqrt(4δ/λ₊) = "
                        f"{res['hessian_distance_bound']['d_sqrt_4delta_over_lambda']:.4f}。"
                        f"严格版需区间 Hessian（15 维本质空间）+ 覆盖半径论证，未开始")),
            dict(name="组合刚性（邻型计数）",
                 status="未开始",
                 quant=("形态（strategy.md §0.4）：全部内积 ∈ 6 节点集 ⇒ 每顶点邻型计数由"
                        "幂和矩条件（i≤3，随 H 次数可到 i≤5）唯一确定 ⇒ TTP 邻型唯一 ⇒ "
                        "取等。输入前提 = ρ_spec ≤ 0.0185 的谱管（见上，当前不可得）")),
            dict(name="全空间严格局部极小",
                 status="未开始（数值已完成，见上）",
                 quant=("TTP 处 15 维本质空间 Hessian 正定（数值 λ₊=0.144）；严格化用区间"
                        "算术（local_min.py 的一维机器可推广/重写 18 维）")),
            dict(name="slab 带 [−1, a₀)",
                 status="未开始（另一条线）",
                 quant=(f"带宽 {a0-(-1):.3f}（N=7 是 0.09）；带内不含候选（TTP min 内积 "
                        f"{m_star:.7f} > {a0}）；typed 三点证书机制（N7 Case 2）")),
            dict(name="拼接",
                 status="未开始",
                 quant=(f"E ≥ E* ⟸ [cap: certified {best_cert['certified']:.9f} 于 "
                        f"min 内积 ≥ {a0}] + [tube forcing + 刚性 + 局部极小把 cap 内 "
                        f"E<E* 排除] + [slab 带证书 ≥ E*]")),
        ],
        quantified_gaps=dict(
            raw_gap_floor_vs_cut="a₀ −0.90→−0.755 原始间隙 6.05e-4→5.49e-4：阶梯已到 (8,6) 的紧度地板",
            tube_needed_vs_available=(f"谱管需求 ρ_spec ≤ {half_gap:.4f}；可得（零噪声极限）"
                                      f"~0.25：差 ~14 倍；且 ε=2e-5（TTP 自身水平）仍 0.0755，"
                                      "结构性不足而非精度不足"),
            precision=("求解器 r1 当前 4.3e-5（m0755，干净解）；两点/证书链无噪声需求"
                       "已由精确证书满足（R1=5.70e-5 精确入账）"),
            hessian=(f"λ₊ = {lam:.6f}；sqrt(4δ/λ₊) = "
                     f"{res['hessian_distance_bound']['d_sqrt_4delta_over_lambda']:.4f} "
                     f"（δ={delta:.6f}）")),
        next_moves=[
            "typed 三点证书原型（区分 3+3+3 轨道；N7 Case 2 机制）在 small 规模打通——管状收尾的先决条件",
            "large=(9,6)（d_H=16=TTP 6 节点 Hermite 自然次数）对称性约化/低秩参数化重解——GAP-REPORT ③-2",
            "全空间区间 Hessian（local_min.py 机器推广）——收尾必要件里最独立、可先做",
            "slab 带（另一条线）与 cap 的 a₀ 必须衔接：slab 上边界 < −0.7476",
        ],
    )
    doc["endgameDesign"] = design
    dump(doc)
    print(json.dumps(design["quantified_gaps"], ensure_ascii=False, indent=2), flush=True)


# ============================================================ main
def main():
    ap = argparse.ArgumentParser(description="N=9 near-sharp cap 阶梯与收尾设计数据")
    ap.add_argument("--solve", metavar="TAG",
                    help="解一档阶梯（%s）" % "/".join(t for t, _, _ in LADDER))
    ap.add_argument("--finalize", action="store_true", help="汇总断言")
    ap.add_argument("--residual", action="store_true", help="残余量化（最好档）")
    ap.add_argument("--certify", metavar="TAG", help="精确认证一档")
    ap.add_argument("--design", action="store_true", help="装订收尾设计")
    ap.add_argument("--verbose", action="store_true")
    args = ap.parse_args()
    if args.solve:
        cmd_solve(args.solve, verbose=args.verbose)
    elif args.finalize:
        cmd_finalize()
    elif args.residual:
        cmd_residual()
    elif args.certify:
        cmd_certify(args.certify)
    elif args.design:
        cmd_design()
    else:
        ap.print_help()
        sys.exit(2)


if __name__ == "__main__":
    main()
