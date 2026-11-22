#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r11_m1light_gate.py — R11C M1 轻证书数据件验收门（G1–G5 ＋ 负对照 NC1/NC2）.

对象：numerics/bounds/results/lp_m1_light.json（D43 裁决 4＝stageb-scope §3
路线 (ii)）：对 189/8 目标的 Yudin/Delsarte 两点 LP 轻节点下界证书
（deg<=10，5–11 个 Legendre 系数，供后续轮 Lean 内核重放；系数面从
lp.json 的 41 个大幅缩减）。证书不信任 LP 求解器浮点：认证面全部精确
有理（Fraction），dyadic round_bits=64 铁律口径沿用（lp_bound.py 生成件）。

检查面（全部确定性；种子 20261013 按任务书记档，无随机路径）：
  G1 schema 沿冻结件 lp.json（顶层/certificate/method 键集一致，method 增
     code_version）＋checks 四布尔全 True＋seed/round_bits/度数/系数面
     （5–11 个）＋dyadic 铁律（k>=1 系数与 ĉ0+η 的分母整除 2^64）
  G2 Fraction 口径：bound_exact > 189/8 且 <= E*+1e-6（E* 直读
     thomson-workflow/data/energies.json，D28 裁决 3 十进制口径
     Fraction("25.759986531")）＋target.E_star 与 energies.json 一致
  G3 degree<=10 ＋ 门内独立重放（import lp_bound 验证函数：由存档系数＋η
     重构 fr/幂基，重跑 certify 精确有理分支定界扫描；重放墙钟 <=180s；
     两次重放 M 逐位相同＝确定性；M/η/叶计数/尾部逐位对上存档）
  G4 冻结件 lp.json 零改动（git diff HEAD 守卫＋status 干净）
  G5 门自算 bound_formula：(N²ĉ0 − N·f(1))/2，f(1)=Σĉ_k·P_k(1) 以本门
     自实现的精确有理 Legendre 递推求值（不 import lp_bound；递推自身
     先对 P_2/P_3 闭式自检），要求精确 Fraction == bound_exact，且报告值
     ＝floor(B·10^9)/10^9 逐位一致
  NC1 /tmp 副本篡一系数（ĉ1 += 2^-64，保持 dyadic/非负 ⇒ G1 放行）⇒
      必被 G3（重放 M 失配）或 G5（公式失配）拦 exit 1；未篡副本 exit 0 sanity
  NC2 /tmp 副本篡 bound：(a) 带内 +1/1000 ⇒ G5 拦；(b) 越界 +1 ⇒ G2 拦

用法（thomson-n9 下）：
  python3 numerics/bounds/r11_m1light_gate.py                    # 全门（exit 0 = 过）
  python3 numerics/bounds/r11_m1light_gate.py --artifact PATH   # 对指定副本跑门（NC 用）
  python3 numerics/bounds/r11_m1light_gate.py --no-nc           # 跳过 NC（NC 子进程用）
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import time
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
REPO = HERE.parents[1]                      # thomson-n9（git 根）
ENERGIES = HERE.parents[2] / "thomson-workflow" / "data" / "energies.json"
ARTIFACT = RESULTS / "lp_m1_light.json"
FROZEN_LP = RESULTS / "lp.json"

SEED_GATE = 20261013                        # 任务书固定种子（门检查无随机路径）
TARGET_LO = Fraction(189, 8)                # 189/8 = 23.625（本件目标下界）
E_STAR_DEC = Fraction("25.759986531")       # D28 裁决 3 十进制精确口径
TOL = Fraction(1, 10 ** 6)                  # 上界容差 1e-6（铁律口径）
N_ELECTRONS = 9
DEG_MAX = 10                                # 轻节点度数上限（D43 裁决 4）
COEFF_MIN, COEFF_MAX = 5, 11                # 系数面 5–11 个
REPLAY_BUDGET_S = 180.0                     # G3 重放墙钟上限
ROUND_BITS = 64                             # dyadic 铁律
CHECK_KEYS = ["coeffs_nonneg_k_ge_1", "f_le_phi_certified_exact_rational",
              "taylor_tail_rigorous", "tail_interval_check"]


def fail(msg: str) -> None:
    print(f"[gate][FAIL] {msg}", flush=True)
    sys.exit(1)


def okmsg(msg: str) -> None:
    print(f"[gate][ok] {msg}", flush=True)


def fr(s: str) -> Fraction:
    return Fraction(str(s))


# ---------------------------------------------------------------- G1
def check_g1(a: dict, lp: dict) -> dict:
    if set(a.keys()) != set(lp.keys()):
        fail(f"G1 顶层键集与 lp.json 不一致：{sorted(set(a.keys()) ^ set(lp.keys()))}")
    if set(a["certificate"].keys()) != set(lp["certificate"].keys()):
        fail("G1 certificate 键集与 lp.json 不一致")
    mkeys_extra = set(a["method"].keys()) - set(lp["method"].keys())
    if mkeys_extra != {"code_version"}:
        fail(f"G1 method 键集应恰增 code_version，实得差异 {sorted(mkeys_extra)}")
    if a["kind"] != "lp" or a["script"] != "lp_bound.py":
        fail(f"G1 kind/script 失配：{a['kind']}/{a['script']}")
    if a["target"]["N"] != N_ELECTRONS:
        fail(f"G1 target.N={a['target']['N']} != {N_ELECTRONS}")

    checks = a["certificate"]["checks"]
    if set(checks.keys()) != set(CHECK_KEYS) or any(checks[k] is not True for k in CHECK_KEYS):
        fail(f"G1 checks 四布尔须全 True（键集恰为 {CHECK_KEYS}），实得 {checks}")

    if a["method"]["seed"] != SEED_GATE:
        fail(f"G1 method.seed={a['method']['seed']} != {SEED_GATE}（任务书固定种子）")
    if a["method"]["round_bits"] != ROUND_BITS:
        fail(f"G1 method.round_bits={a['method']['round_bits']} != 64（dyadic 铁律）")
    cv = str(a["method"].get("code_version", ""))
    if not cv:
        fail("G1 method.code_version 缺失/为空（D43 裁决 4 provenance 要求）")

    deg = a["certificate"]["degree"]
    coeffs = a["certificate"]["coeffs_legendre_exact"]
    if not isinstance(deg, int) or deg <= 0:
        fail(f"G1 degree 非正整数：{deg!r}")
    if len(coeffs) != deg + 1:
        fail(f"G1 系数个数 {len(coeffs)} != degree+1 = {deg + 1}")
    if not (COEFF_MIN <= len(coeffs) <= COEFF_MAX):
        fail(f"G1 系数面 {len(coeffs)} 个不在轻节点范围 [{COEFF_MIN},{COEFF_MAX}]")

    chat = [fr(c) for c in coeffs]
    if any(c < 0 for c in chat[1:]):
        fail("G1 k>=1 系数出现负值（条件 (i) 破坏）")
    eta = fr(a["certificate"]["eta_exact"])
    if eta <= 0:
        fail("G1 eta <= 0")
    # dyadic 铁律：舍入系数 fr_k（=ĉ_k, k>=1；fr_0=ĉ0+η）分母整除 2^64
    dyad = 1 << ROUND_BITS
    for k, c in enumerate(chat):
        v = c + eta if k == 0 else c           # 还原生成时的 LP 舍入系数
        if v == 0:
            continue
        if (dyad % v.denominator) != 0:
            fail(f"G1 dyadic 铁律破坏：fr[{k}] 分母 {v.denominator} 不整除 2^{ROUND_BITS}")
    if fr(a["certificate"]["M_sup_f_minus_phi_exact"]) > eta:
        fail("G1 M > eta（η 平移不足以压住 sup(f−φ)）")
    if a["lp_raw"] < a["bound"] - 1e-9:
        fail("G1 lp_raw < bound（LP 值低于认证下界，异常）")
    nz = sum(1 for c in chat[1:] if c != 0)
    okmsg(f"G1 schema 沿 lp.json＋method 增 code_version（{cv}）；checks 四布尔全"
          f" True；seed={a['method']['seed']} round_bits=64；系数面 {len(chat)} 个"
          f"（k>=1 非零 {nz} 个）dyadic 2^-64 全过")
    return dict(deg=deg, coeffs=chat, eta=eta,
                M=fr(a["certificate"]["M_sup_f_minus_phi_exact"]))


# ---------------------------------------------------------------- G2
def check_g2(a: dict) -> Fraction:
    try:
        data = json.loads(ENERGIES.read_text())
        e9 = data["energies"]["9"]
    except Exception as e:
        fail(f"G2 energies.json 直读失败：{e}")
        raise
    e_star = Fraction(str(e9["value"]))
    if e_star != E_STAR_DEC:
        fail(f"G2 energies.json 值 {e_star} != 十进制口径 {E_STAR_DEC}")
    if a["target"]["E_star"] != e9["value"]:
        fail(f"G2 target.E_star={a['target']['E_star']} != energies.json {e9['value']}")
    if a["target"]["E_star_highPrecision"] != e9["highPrecision"]:
        fail("G2 target.E_star_highPrecision 与 energies.json 不一致")
    if "energies.json" not in str(a["target"]["source"]):
        fail(f"G2 target.source 与门内路径不符：{a['target']['source']}")

    B = fr(a["bound_exact"])
    if not (B > TARGET_LO):
        fail(f"G2 bound_exact={float(B):.9f} 未 > 189/8={float(TARGET_LO)}")
    if not (B <= e_star + TOL):
        fail(f"G2 bound_exact={float(B):.9f} > E*+1e-6={float(e_star + TOL):.9f}")
    gap_expected = float(e_star) - a["bound"]
    if abs(gap_expected - a["gap_to_E_star"]) > 5e-12:
        fail(f"G2 gap_to_E_star 记账失配：{a['gap_to_E_star']} vs 重算 {gap_expected}")
    okmsg(f"G2 Fraction：bound_exact={float(B):.9f} > 189/8 且 <= E*+1e-6"
          f"（E*={float(e_star)} 直读 energies.json；差距 {float(e_star - B):.9f}）")
    return B


# ---------------------------------------------------------------- G3
def check_g3(a: dict, g1: dict) -> None:
    deg = g1["deg"]
    if deg > DEG_MAX:
        fail(f"G3 degree={deg} > {DEG_MAX}（轻节点上限）")

    sys.path.insert(0, str(HERE))
    import lp_bound as lpb                    # noqa: E402（门内重放源）

    # 存档 sweep 参数与 lp_bound.CFG 一致（防静默改参）
    m = a["method"]
    cfg_expect = {
        "sweep_first_level_intervals": lpb.CFG["FIRST_LEVEL"],
        "sweep_min_width": f"2^-{lpb.CFG['W_MIN_EXP']}",
        "taylor_exact_terms": lpb.CFG["TAYLOR_K"] + 1,
        "phi_bound_resolution": f"2^-{lpb.CFG['PHI_P']}",
        "eta_margin": f"2^-46",
    }
    for k, v in cfg_expect.items():
        if m.get(k) != v:
            fail(f"G3 存档 method.{k}={m.get(k)!r} 与 lp_bound.CFG 重算 {v!r} 不一致")

    # 由存档证书重构生成时输入：fr_0 = ĉ0+η（η 平移前），fr_k = ĉ_k
    eta, chat = g1["eta"], g1["coeffs"]
    fr_coeffs = [chat[0] + eta] + list(chat[1:])

    # 幂基重构（精确有理）＋交叉自检
    LEG = lpb.legendre_power_basis(deg)
    power = [Fraction(0)] * (deg + 1)
    for k, c in enumerate(fr_coeffs):
        for j, p in enumerate(LEG[k]):
            power[j] += c * p
    from numpy.polynomial import legendre as _L           # 数值交叉检查（仅自检）
    for tchk in (-0.866, -0.5, 0.0, 0.31, 0.77, 0.996):
        v_exact = float(lpb.horner(power, Fraction(tchk)))
        v_ref = float(_L.legval(tchk, [float(c) for c in fr_coeffs]))
        if abs(v_exact - v_ref) > 1e-9 * max(1.0, abs(v_ref)):
            fail(f"G3 幂基重构与 numpy Legendre 求值不一致 @t={tchk}")

    cfg = dict(lpb.CFG)
    cfg.update(DEG=deg, NGRID=m["grid_points"], SEED=a["method"]["seed"])

    # 独立重放 ×2（确定性证据）＋墙钟预算
    t0 = time.time()
    cert1 = lpb.certify(fr_coeffs, power, cfg)
    cert2 = lpb.certify(fr_coeffs, power, cfg)
    replay_s = time.time() - t0
    if replay_s > REPLAY_BUDGET_S:
        fail(f"G3 重放墙钟 {replay_s:.1f}s > {REPLAY_BUDGET_S:.0f}s 预算")
    if cert1["M"] != cert2["M"]:
        fail("G3 两次重放 M 不一致（确定性破坏）")
    if cert1["M"] != g1["M"]:
        fail("G3 重放 M 与存档 M_sup_f_minus_phi_exact 逐位失配（系数被篡？）")
    if not cert1["tail_ok"]:
        fail("G3 重放尾部检查 tail_ok=False（tail_interval_check 破坏）")
    if g1["eta"] != cert1["M"] + lpb.CFG["ETA_MARGIN"]:
        fail("G3 eta != M + 2^-46（η 平移口径失配——f−η<=phi 认证破坏）")
    v = a["verification"]
    for key, rk in (("sweep_leaves_evaluated", "n_eval"),
                    ("sweep_leaves_pass", "n_pass"),
                    ("sweep_leaves_at_width_limit", "n_leaf")):
        if v[key] != cert1[rk]:
            fail(f"G3 verification.{key}={v[key]} != 重放 {cert1[rk]}")
    if v["tail_bound"] != float(cert1["tail_bound"]):
        fail("G3 verification.tail_bound 与重放不一致")

    # (i) 精确复核（重放路径独立断言，不依赖存档布尔）
    if any(c < 0 for c in chat[1:]):
        fail("G3 重放路径复核：k>=1 系数非负破坏")
    okmsg(f"G3 degree={deg}<={DEG_MAX}；门内重放 certify ×2（{replay_s:.1f}s<="
          f"{REPLAY_BUDGET_S:.0f}s）M 逐位一致==存档、eta==M+2^-46、tail_ok、"
          f"{v['sweep_leaves_evaluated']} 叶计数全对上——四检查由重放独立复核")


# ---------------------------------------------------------------- G4
def check_g4() -> None:
    r = subprocess.run(["git", "-C", str(REPO), "diff", "HEAD", "--",
                        str(FROZEN_LP.relative_to(REPO))],
                       capture_output=True, text=True)
    if r.returncode != 0:
        fail(f"G4 git diff 守卫执行失败：{r.stderr.strip()}")
    if r.stdout.strip():
        fail("G4 冻结件 lp.json 相对 HEAD 有改动")
    r2 = subprocess.run(["git", "-C", str(REPO), "status", "--porcelain", "--",
                         str(FROZEN_LP.relative_to(REPO))],
                        capture_output=True, text=True)
    if r2.stdout.strip():
        fail(f"G4 lp.json 出现在 git status：{r2.stdout.strip()}")
    head = subprocess.run(["git", "-C", str(REPO), "show",
                           f"HEAD:{FROZEN_LP.relative_to(REPO).as_posix()}"],
                          capture_output=True, text=True)
    if hashlib.sha256(head.stdout.encode()).hexdigest() != \
            hashlib.sha256(FROZEN_LP.read_bytes()).hexdigest():
        fail("G4 lp.json 工作树字节 != HEAD 版本（sha256 失配）")
    okmsg("G4 冻结件 lp.json 零改动（git diff HEAD 空＋status 干净＋sha256==HEAD）")


# ---------------------------------------------------------------- G5
def legendre_P_at(k: int, t: Fraction) -> Fraction:
    """精确有理 Legendre 递推求 P_k(t)：P0=1, P1=t,
    (k+1)P_{k+1} = (2k+1)·t·P_k − k·P_{k−1}。不依赖 lp_bound。"""
    p0, p1 = Fraction(1), Fraction(t)
    if k == 0:
        return p0
    if k == 1:
        return p1
    for j in range(1, k):
        p0, p1 = p1, (Fraction(2 * j + 1) * t * p1 - Fraction(j) * p0) / Fraction(j + 1)
    return p1


def check_g5(a: dict, g1: dict, B: Fraction) -> None:
    # 递推实现自检：对闭式 P2=(3t²−1)/2、P3=(5t³−3t)/2
    for t in (Fraction(1, 3), Fraction(-1, 2), Fraction(1, 1)):
        if legendre_P_at(2, t) != (3 * t * t - 1) / 2:
            fail(f"G5 Legendre 递推自检失败 P2({t})")
        if legendre_P_at(3, t) != (5 * t ** 3 - 3 * t) / 2:
            fail(f"G5 Legendre 递推自检失败 P3({t})")
    deg, chat = g1["deg"], g1["coeffs"]
    # f(1) = Σ ĉ_k·P_k(1)，P_k(1) 由递推逐个精确求值
    f1 = sum((c * legendre_P_at(k, Fraction(1)) for k, c in enumerate(chat)),
             Fraction(0))
    c0 = chat[0]
    B5 = Fraction(N_ELECTRONS * N_ELECTRONS * c0 - N_ELECTRONS * f1, 2)
    if B5 != B:
        fail(f"G5 门自算 bound_formula={float(B5):.12f} != 存档 bound_exact"
             f"={float(B):.12f}（精确 Fraction 失配）")
    # 报告值＝floor(B·10^9)/10^9 逐位
    scale = 10 ** 9
    i_rep = B5.numerator * scale // B5.denominator
    if a["bound"] != i_rep / scale:
        fail(f"G5 报告值 {a['bound']!r} != floor(B·10^9)/10^9 = {i_rep / scale!r}")
    if not (a["bound"] <= float(B5)):
        fail("G5 报告值超过精确下界（floor 口径破坏）")
    okmsg(f"G5 门自算 (N²ĉ0−N·f(1))/2（Legendre 精确有理递推，闭式自检过）＝"
          f"存档 bound_exact 逐位；报告值 {a['bound']}==floor(B·10^9)/10^9")


# ---------------------------------------------------------------- 负对照
def _run_gate_sub(path: Path) -> subprocess.CompletedProcess:
    return subprocess.run([sys.executable, str(Path(__file__).resolve()),
                           "--artifact", str(path), "--no-nc"],
                          capture_output=True, text=True)


def _last_gate_line(r: subprocess.CompletedProcess) -> str:
    lines = [ln for ln in r.stdout.splitlines() if "[gate]" in ln]
    return lines[-1] if lines else "(无 [gate] 行)"


def _fail_gates(r: subprocess.CompletedProcess) -> set:
    """子进程 [gate][FAIL] 行实际命中的检查面（G 编号）。"""
    hits = set()
    for ln in r.stdout.splitlines():
        if "[gate][FAIL]" in ln:
            for g in ("G1", "G2", "G3", "G4", "G5"):
                if g in ln:
                    hits.add(g)
    return hits


def run_nc(art_path: Path) -> None:
    base = Path("/tmp/r11c_m1light_nc")
    base.mkdir(parents=True, exist_ok=True)
    a = json.loads(art_path.read_text())

    # sanity：未篡改副本须 exit 0
    orig = base / "orig.json"
    orig.write_text(art_path.read_text())
    r0 = _run_gate_sub(orig)
    if r0.returncode != 0:
        fail(f"NC 前置失败：未篡改 /tmp 副本应 exit 0，实得 {r0.returncode}"
             f"（{_last_gate_line(r0)}）")

    # NC1 篡一系数：ĉ1 += 2^-64（仍 dyadic、仍非负 ⇒ G1 放行）⇒ G3/G5 拦
    t1 = json.loads(art_path.read_text())
    c1 = fr(t1["certificate"]["coeffs_legendre_exact"][1])
    t1["certificate"]["coeffs_legendre_exact"][1] = str(c1 + Fraction(1, 2 ** 64))
    p1 = base / "nc1_coeff.json"
    p1.write_text(json.dumps(t1, ensure_ascii=False, indent=2))
    r1 = _run_gate_sub(p1)
    h1 = _fail_gates(r1)
    if r1.returncode == 0 or not (h1 & {"G3", "G5"}):
        fail(f"NC1 未被 G3/G5 拦（exit {r1.returncode}，FAIL 面 {sorted(h1) or '无'}）："
             f"{_last_gate_line(r1)}")

    # NC2a 篡 bound（带内 +1/1000 ⇒ G2 放行）⇒ G5 拦
    t2 = json.loads(art_path.read_text())
    t2["bound_exact"] = str(fr(t2["bound_exact"]) + Fraction(1, 1000))
    p2 = base / "nc2a_bound.json"
    p2.write_text(json.dumps(t2, ensure_ascii=False, indent=2))
    r2 = _run_gate_sub(p2)
    h2 = _fail_gates(r2)
    if r2.returncode == 0 or not (h2 & {"G2", "G5"}):
        fail(f"NC2a 未被 G2/G5 拦（exit {r2.returncode}，FAIL 面 {sorted(h2) or '无'}）："
             f"{_last_gate_line(r2)}")

    # NC2b 篡 bound（越界 +1）⇒ G2 拦
    t3 = json.loads(art_path.read_text())
    t3["bound_exact"] = str(fr(t3["bound_exact"]) + 1)
    p3 = base / "nc2b_bound.json"
    p3.write_text(json.dumps(t3, ensure_ascii=False, indent=2))
    r3 = _run_gate_sub(p3)
    h3 = _fail_gates(r3)
    if r3.returncode == 0 or "G2" not in h3:
        fail(f"NC2b 未被 G2 拦（exit {r3.returncode}，FAIL 面 {sorted(h3) or '无'}）："
             f"{_last_gate_line(r3)}")

    for p in (orig, p1, p2, p3):
        p.unlink(missing_ok=True)
    okmsg(f"NC1 篡系数 ĉ1+=2^-64 ⇒ exit {r1.returncode}，FAIL 面 "
          f"{sorted(h1)} ⊂{{G3,G5}} 拦 ✓；NC2a 篡 bound 带内 ⇒ exit {r2.returncode}，"
          f"FAIL 面 {sorted(h2)} ⊂{{G2,G5}} 拦 ✓；NC2b 篡 bound 越界 ⇒ "
          f"exit {r3.returncode}，FAIL 面 {sorted(h3)}（G2）拦 ✓"
          f"（未篡副本 exit 0 sanity ✓）")


# ---------------------------------------------------------------- 主流程
def run_gate(art_path: Path, run_nc_flag: bool) -> None:
    print(f"[gate] r11_m1light_gate seed={SEED_GATE}（确定性检查，无随机路径）",
          flush=True)
    if not art_path.exists():
        fail(f"G1 数据件不在档：{art_path}")
    if not FROZEN_LP.exists():
        fail(f"G1 冻结件 lp.json 不在档：{FROZEN_LP}")
    a = json.loads(art_path.read_text())
    lp = json.loads(FROZEN_LP.read_text())
    g1 = check_g1(a, lp)
    B = check_g2(a)
    check_g3(a, g1)
    check_g4()
    check_g5(a, g1, B)
    if run_nc_flag:
        run_nc(art_path)
    print("[gate] 全门 PASS（G1–G5 ＋ NC1/NC2）", flush=True)


def main() -> None:
    ap = argparse.ArgumentParser(description="R11C M1 轻证书数据件验收门")
    ap.add_argument("--artifact", default=str(ARTIFACT),
                    help="数据件路径（默认 numerics/bounds/results/lp_m1_light.json）")
    ap.add_argument("--no-nc", action="store_true", help="跳过负对照（NC 子进程用）")
    args = ap.parse_args()
    run_gate(Path(args.artifact).resolve(), not args.no_nc)


if __name__ == "__main__":
    main()
