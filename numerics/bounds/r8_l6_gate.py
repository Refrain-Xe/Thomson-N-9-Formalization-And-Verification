#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r8_l6_gate.py — Round 8 / R8-3 L6 方向相关联合界（提升通道）验收门。

验收内容（任务书口径，CWD 无关——路径全部自 __file__ 解析；裸 python3）：
  ① 幂等：重跑 l6_intube.py → exit 0 且存档逐位一致（"archive check" 行＋sha256 前后不变）；
  ② 硬阈：r* ≥ 0.0084（R7-3 任务书未达目标；stretch 0.0095+）；μ@r* 区间严格 > 0（下端）；
  ③ 结构负对照：r* 相邻箱 μ 上端 ≤ 0；顶箱（加倍半径）μ 上端 ≤ 0；
  ④ 负对照 ≥ 5 项全触发：既有 4 项（加倍半径/μ 符号翻转/应力符号翻转/应力权重篡改）
     ＋联合通道专属（换回标量方向解耦 ⇒ r* 回退旧档 0.006718398305 及以下）；
  ⑤ ε*_L6 ∝ r*² 标度自洽：以 l3.C_glob.lo、l4.C_pro、l6.r* 精确 Fraction 重算
     ε* = C_lo·(r*/C_pro)²，与 l3 链扣 eps_star 相对偏差 ≤ 1e-6；且新旧 ε* 之比
     =（新 r*/旧 r*）²相对偏差 ≤ 1e-6；
  ⑥ legacy 通道字段与 R7 存档一致：legacyR73Archive 三常数逐位相等；一阶 klam
     不变（12.83599046）；修复规则后的 legacy box d2op ≠ R7 存档值（bug 修复生效留痕）；
  ⑦ schema=thomson-n9/bounds/l6-intube/2；l3.r_star_l6_used = l6 r*；
     l6_closure_radius_needed（≈0.0319，ε-链全闭尚需半径）在档且 > r*（如实差距）。

用法：python3 thomson-n9/numerics/bounds/r8_l6_gate.py   （任意 CWD）
exit 0 = 过门。
"""
from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from decimal import Decimal
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
L6_JSON = RESULTS / "l6_intube.json"
L3_JSON = RESULTS / "l3_analytic.json"
L4_JSON = RESULTS / "l4.json"

R73_KLAM = "12.83599046"
R73_D2OP = "2016.729948"
R73_RSTAR = "0.006718398305"
R73_EPS_L6 = Fr(Decimal("3.2548374834067015e-14"))   # R7 存档 ε*_L6（l3_analytic.json 旧档直读）
HARD_R = Fr(Decimal("0.0084"))

checks = []


def chk(name: str, ok: bool, detail: str = "") -> bool:
    checks.append((name, bool(ok), detail))
    print(f"[{'OK ' if ok else 'FAIL'}] {name}" + (f"：{detail}" if detail else ""),
          flush=True)
    return bool(ok)


def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def frac(s) -> Fr:
    return Fr(str(s))


def main() -> int:
    print("== R8-3 L6 联合界验收门（l6-intube/2 提升通道）==", flush=True)
    for p in (L6_JSON, L3_JSON, L4_JSON):
        if not p.exists():
            print(f"[FAIL] 缺输入 {p}")
            return 1
    h6_0 = sha(L6_JSON)

    # ---------- ① 幂等重算 ----------
    r6 = subprocess.run([sys.executable, str(HERE / "l6_intube.py")],
                        capture_output=True, text=True, timeout=600)
    ok1 = (r6.returncode == 0 and "archive check: recomputation identical" in r6.stdout
           and sha(L6_JSON) == h6_0)
    chk("G1_l6_idempotent", ok1,
        f"exit={r6.returncode}；存档 sha256 前后一致={sha(L6_JSON) == h6_0}"
        + ("" if ok1 else "；" + r6.stdout[-160:] + r6.stderr[-160:]))

    l6 = json.loads(L6_JSON.read_text())
    l3 = json.loads(L3_JSON.read_text())
    l4 = json.loads(L4_JSON.read_text())
    qg = l6["quadraticGrowth"]
    r_star = frac(qg["rigorousRadius"])
    _mu = qg["muAtRstar"]
    if isinstance(_mu, str):
        _mu = [s.strip() for s in _mu.strip("[]").split(",")]
    mu_lo = frac(_mu[0])

    # ---------- ② 硬阈 + μ>0 ----------
    bins = l6["bins"]

    def mu_ends(b):
        s = b["mu"].strip("[]").split(",")
        return frac(s[0]), frac(s[1])

    def bin_r(b):
        return frac(b["r"])

    r_idx = next(i for i, b in enumerate(bins) if bin_r(b) == r_star)
    chk("G2_rstar_hard_threshold", r_star >= HARD_R,
        f"r*={float(r_star):.10f} ≥ 0.0084（旧档 {R73_RSTAR}，"
        f"{float(r_star / frac(R73_RSTAR)):.3f}×；stretch 0.0095+ {'达成' if r_star >= Fr(Decimal('0.0095')) else '未达'}）")
    chk("G2_mu_interval_strictly_positive", mu_lo > 0,
        f"μ@r* = {qg['muAtRstar']}（下端 {float(mu_lo):.6e} > 0）")

    # ---------- ③ 结构负对照（相邻箱 / 顶箱）----------
    nxt = bins[r_idx + 1] if r_idx + 1 < len(bins) else None
    ok3 = (nxt is None or mu_ends(nxt)[1] <= 0) and mu_ends(bins[-1])[1] <= 0
    chk("G3_adjacent_and_top_bins_negative", ok3,
        f"相邻箱 r={nxt['r'] if nxt else '—'} μ 上端="
        f"{float(mu_ends(nxt)[1]):.3e} ≤ 0；顶箱 μ 上端={float(mu_ends(bins[-1])[1]):.3e} ≤ 0")

    # ---------- ④ 负对照 ≥5 全触发 ----------
    ncs = l6.get("negativeControls", {})
    need = ["doubleRadiusControl", "muSignFlipControl", "stressSignFlipControl",
            "stressWeightControl", "channelSwapScalarDecoupledControl"]
    all_trig = all(ncs.get(k, {}).get("triggered") is True for k in need)
    swap = ncs.get("channelSwapScalarDecoupledControl", {})
    swap_ok = (frac(swap.get("fallbackRstar", "1")) <= frac(R73_RSTAR)
               and frac(swap.get("fallbackRstar", "1")) < r_star)
    chk("G4_five_negative_controls", all_trig and swap_ok,
        f"5/5 触发；通道换回标量解耦 ⇒ r* 回退 {swap.get('fallbackRstar')} ≤ 旧档 {R73_RSTAR}"
        f"（< 新 r* {float(r_star):.7f}）——联合通道被实际使用")

    # ---------- ⑤ ε*_L6 ∝ r*² 标度自洽 ----------
    nl = l3.get("nodeLocal", {})
    c_lo = frac(nl["C_glob"]["lo"])
    c_pro = frac(l4["constants"]["C_exact"])
    lk6 = nl["chain_caliber_c"]["links"]["L6"]
    eps_recomputed = c_lo * (r_star / c_pro) ** 2
    eps_archived = frac(lk6["eps_star"])
    dev1 = abs(eps_recomputed - eps_archived) / eps_archived
    eps_new = eps_archived
    dev2 = abs(eps_new / R73_EPS_L6 - (r_star / frac(R73_RSTAR)) ** 2) / (r_star / frac(R73_RSTAR)) ** 2
    chk("G5_eps_l6_rstar_sq_scaling", dev1 <= Fr(1, 10 ** 6) and dev2 <= Fr(1, 10 ** 6),
        f"ε*_L6={float(eps_archived):.6e}；重算 C_lo·(r*/C_pro)² 相对偏差 {float(dev1):.2e} ≤ 1e-6；"
        f"新旧比 vs (r*比)² 相对偏差 {float(dev2):.2e} ≤ 1e-6；链扣缺口 "
        f"{lk6.get('deficit_factor_float')}×（旧 22.507×）")

    # ---------- ⑥ legacy 字段与 R7 存档一致 ----------
    td = l6.get("taylorDecomposition", {})
    leg = td.get("legacyR73Archive", {})
    leg_ok = (leg.get("r_star") == R73_RSTAR and leg.get("d2op_box") == R73_D2OP
              and leg.get("klam_slope") == R73_KLAM)
    klam_ok = td.get("firstOrder", {}).get("klam_slope") == R73_KLAM
    fixed_ok = td.get("secondOrderLegacyBox", {}).get("d2_modcs_opnorm") != R73_D2OP
    chk("G6_legacy_fields_match_r73_archive", leg_ok and klam_ok and fixed_ok,
        f"legacyR73Archive 三常数逐位一致；一阶 klam={td.get('firstOrder', {}).get('klam_slope')}"
        f"（不变）；修复规则后 legacy box d2op="
        f"{td.get('secondOrderLegacyBox', {}).get('d2_modcs_opnorm')}（≠ R7 存档 "
        f"{R73_D2OP}＝bug 修复生效）")

    # ---------- ⑦ schema / l3 口径 / 剩余差距留痕 ----------
    closure = nl["chain_caliber_c"].get("l6_closure_radius_needed", {})
    used = nl.get("r_star_l6_used", {})
    ok7 = (l6.get("schema") == "thomson-n9/bounds/l6-intube/2"
           and frac(used.get("value", "-1")) == r_star
           and closure.get("float") is not None
           and frac(closure["value"]) > r_star)
    chk("G7_schema_and_honest_gap", ok7,
        f"schema={l6.get('schema')}；l3.r_star_l6_used={used.get('float')}＝l6 r*；"
        f"ε-链全闭尚需 r*≈{closure.get('float')}（差 {closure.get('shortfall_factor')}×，"
        "本件单独不闭合——cap 前提兑现后的预制件，如实留档）")

    n_pass = sum(1 for _, ok, _ in checks if ok)
    print(f"== 门总计：{n_pass}/{len(checks)} 过 ==", flush=True)
    return 0 if n_pass == len(checks) else 1


if __name__ == "__main__":
    sys.exit(main())
