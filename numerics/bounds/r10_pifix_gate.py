#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r10_pifix_gate.py — R10A pifix-build-pi 验收门（G1–G5 ＋ NC1/NC2）.

任务书口径（D38 任务 1／R9B ④ 发现）：hermite_minorant.py:581-591
build_pi_polynomial 节点因子缺陷（常数 [ν] → 应为 (t−ν)=[−ν,1]）修复后：
单元恒等式自检、两变体回归重算（新文件 r10_pifix_probe_{contact,triple}.json，
冻结件零覆写）、账本在档、冻结件守卫与回归电池。

裸 python3 运行（无第三方依赖；CWD 无关——一切路径由 __file__ 解析；
campaign 根路由沿 D7/D8 包装器先例）：

    python3 numerics/bounds/r10_pifix_gate.py            # 仓内
    python3 thomson-n9/numerics/bounds/r10_pifix_gate.py # campaign 根

固定种子 20261012（任务书条款）。七项检查：

  G1  单元恒等（修后 build_pi_polynomial，import 受测函数；求值/对照构造
      全部门内自写 Fraction 路径）：
      contact（mult=2, cm=5）与 triple（mult=3, cm=0）各四检——
      ①次数 == 6·mult+cm（contact 17／triple 18）；②首一；③Π(ν_k)==0
      逐节点精确；④64 随机有理点与独立直接乘积构造
      ∏(t−ν_k)^mult·(t+1)^cm 逐位对拍（seed 20261012）。
  G2  contact 决定性字段对冻结存档逐位相等（任务书枚举集：W／coeffs／
      halfwidths／interval_certificate.ok==True／n_regions／逐区域
      interval·pi_sign·method·bound·sign_basis／hull／c_const／
      verdict=="alive"）＋唯一漂移 pi_degree 5→17；其余确定性字段
      （dominance/gap_metrics/e_anchor，剔运行时戳）advisory 比对——
      漂移只告警不判死（如实入档）。
  G3  triple 判死维持：interval_certificate.ok==False＋verdict=="dead"
      ＋pi_degree==18＋恰三 dip 区（pi_sign=="<0"）逐区 bound<0／
      pi_min<0＋门内独立 Fraction 构造 Π 于各区中点符号核验
      （∏(mid−ν_k)³<0）＋dense_and_local 直接格点负证据
      （dense.min<0，判死独立面）；新旧 dip pi_min/bound 对照入档输出。
  G4  冻结件守卫：git diff HEAD 对 hermite_v2_probe_contact.json／
      hermite_v2_probe_triple.json／hermite_probe.json 零改动
      （git status --porcelain 三路径零行双保险）。
  G5  回归电池：r8c3_engine_gate.py＋r9_v2iv_gate.py＋hermite_gate.py
      门内子进程复跑全 exit 0（墙钟逐门入档）。
  NC1 旧缺陷构造（常数 [ν] 节点因子 ×(t+1)^cm）内联重现必被 G1 检出
      （两变体各 ≥1 项恒等式错误）。
  NC2 /tmp 篡改新 contact 输出（翻一区域 bound "0"→"1/1000000"）必在
      G2 比对 exit 1——同门脚本 --g2-probe <篡改件> 子进程字面演示。

exit 0 = 过门；任一失败 exit 1（信息含检查号与定量内容）。
"""
from __future__ import annotations

import argparse
import json
import random
import subprocess
import sys
import time
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]                                    # .../thomson-n9
RESULTS = HERE / "results"
sys.path.insert(0, str(HERE))

SEED = 20261012
F0 = Fraction(0)
F1 = Fraction(1)

FROZEN = {"contact": RESULTS / "hermite_v2_probe_contact.json",
          "triple": RESULTS / "hermite_v2_probe_triple.json",
          "plain": RESULTS / "hermite_probe.json"}
NEW = {"contact": RESULTS / "r10_pifix_probe_contact.json",
       "triple": RESULTS / "r10_pifix_probe_triple.json"}
LEDGER = RESULTS / "r10_pifix.json"
BATTERY = [HERE / "r8c3_engine_gate.py", HERE / "r9_v2iv_gate.py",
           HERE / "hermite_gate.py"]

_checks = {"passed": 0, "failed": 0}
_failures: list[str] = []
_info: list[str] = []
_warn: list[str] = []


def ok(msg: str) -> None:
    _checks["passed"] += 1
    print(f"[gate][OK] {msg}", flush=True)


def fail(msg: str) -> None:
    _checks["failed"] += 1
    _failures.append(msg)
    print(f"[gate][FAIL] {msg}", flush=True)


def info(msg: str) -> None:
    _info.append(msg)
    print(f"[gate][info] {msg}", flush=True)


def warn(msg: str) -> None:
    _warn.append(msg)
    print(f"[gate][WARN] {msg}", flush=True)


def check(cond: bool, msg: str) -> None:
    if cond:
        ok(msg)
    else:
        fail(msg)


# ============================================================ 自写工具（不借受测代码）
def g_eval(coeffs, t: Fraction) -> Fraction:
    acc = F0
    for c in reversed(coeffs):
        acc = acc * t + c
    return acc


def g_direct_pi(t: Fraction, nu, mult: int, cm: int) -> Fraction:
    """独立直接乘积构造：∏_k (t−ν_k)^mult · (t+1)^cm。"""
    v = F1
    for x in nu:
        v *= (t - x) ** mult
    return v * (t + F1) ** cm


def g_bug_poly(nu, mult: int, cm: int):
    """旧缺陷构造内联重现（常数 [ν] 节点因子；NC1 用）。"""
    def mul(p, q):
        out = [F0] * (len(p) + len(q) - 1)
        for i, a in enumerate(p):
            if a:
                for j, b in enumerate(q):
                    out[i + j] += a * b
        return out

    poly = [F1]
    for v in nu:
        r = [Fraction(v)]
        for _ in range(mult - 1):
            r = mul(r, [Fraction(v)])
        poly = mul(poly, r)
    for _ in range(cm):
        poly = mul(poly, [F1, F1])
    return poly


def g_identity_errors(poly, nu, mult: int, cm: int, rng, n_points: int = 64):
    """G1 同款恒等式检查器（返回错误列表；空＝全过）。"""
    errs = []
    if len(poly) - 1 != len(nu) * mult + cm:
        errs.append(f"degree {len(poly) - 1} != {len(nu)}*{mult}+{cm}")
    if poly[-1] != 1:
        errs.append("not monic")
    for v in nu:
        if g_eval(poly, v) != 0:
            errs.append(f"Pi(nu) != 0 at {v}")
            break                                    # 逐位列出取首例即可
    for _ in range(n_points):
        t = Fraction(rng.randint(-(1 << 40), 1 << 40), 1 << 40)
        if g_eval(poly, t) != g_direct_pi(t, nu, mult, cm):
            errs.append(f"value != direct product at t={t}")
            break
    return errs


# ============================================================ G1 单元恒等
def g1_unit_identities() -> dict:
    import hermite_minorant as hm                   # 受测：修后 build_pi_polynomial
    tube = json.loads((RESULTS / "tube.json").read_text())["ttp_spectrum"]
    nu = [Fraction(float(x)) for x in tube["nodes"]]
    rng = random.Random(SEED)
    out = {"seed": SEED, "variants": {}}
    for name, mult, cm, deg in (("contact", 2, 5, 17), ("triple", 3, 0, 18)):
        poly = hm.build_pi_polynomial(nu, mult, cm)
        errs = g_identity_errors(poly, nu, mult, cm, rng)
        out["variants"][name] = dict(
            mult=mult, contact_minus1=cm, degree=len(poly) - 1,
            monic=bool(poly[-1] == 1),
            roots_exact=all(g_eval(poly, v) == 0 for v in nu),
            crosscheck_points=64, errors=errs[:6],
            ok=not errs)
        check(not errs,
              f"G1 {name} 单元恒等四检全过（次数={len(poly) - 1}=={deg}、首一、"
              f"Π(ν_k)==0 逐节点精确、64 随机有理点独立直接乘积逐位对拍）"
              + ("" if not errs else f"；错误：{errs[:3]}"))
    return out


def nc1_old_bug_detected() -> None:
    tube = json.loads((RESULTS / "tube.json").read_text())["ttp_spectrum"]
    nu = [Fraction(float(x)) for x in tube["nodes"]]
    rng = random.Random(SEED)
    for name, mult, cm in (("contact", 2, 5), ("triple", 3, 0)):
        bug = g_bug_poly(nu, mult, cm)
        errs = g_identity_errors(bug, nu, mult, cm, rng)
        check(bool(errs),
              f"NC1 旧缺陷构造（常数[ν]×(t+1)^{cm}）被 G1 检出："
              f"{len(errs)} 项错误（首例 {errs[0][:60]}…）" if errs else
              f"NC1 {name} 旧缺陷构造未被检出（检查器失效）")


# ============================================================ G2 contact 逐位比对
G2_DECISIVE_CERT = ["ok", "n_regions", "hull", "c_const"]
G2_DECISIVE_REGION = ["interval", "pi_sign", "method", "bound", "sign_basis"]
G2_DECISIVE_TOP = ["variant", "variant_config", "seed", "k", "B", "ncond",
                   "remainder", "nodes", "multiplicities", "W", "coeffs",
                   "halfwidths", "verdict"]


def compare_contact(new_path: Path, frozen_path: Path) -> list[str]:
    """决定性字段逐位比对（返回 mismatch 列表；空＝全同）。"""
    mism = []
    new = json.loads(new_path.read_text())
    fro = json.loads(frozen_path.read_text())
    for f in G2_DECISIVE_TOP:
        if new.get(f) != fro.get(f):
            mism.append(f"top.{f}: new={json.dumps(new.get(f))[:80]} != "
                        f"frozen={json.dumps(fro.get(f))[:80]}")
    nc, fc = new["interval_certificate"], fro["interval_certificate"]
    for f in G2_DECISIVE_CERT:
        if nc.get(f) != fc.get(f):
            mism.append(f"cert.{f}: new={json.dumps(nc.get(f))[:80]} != "
                        f"frozen={json.dumps(fc.get(f))[:80]}")
    if len(nc["regions"]) != len(fc["regions"]):
        mism.append(f"cert.regions 数：new={len(nc['regions'])} "
                    f"!= frozen={len(fc['regions'])}")
    else:
        for i, (rn, rf) in enumerate(zip(nc["regions"], fc["regions"])):
            for f in G2_DECISIVE_REGION:
                if rn.get(f) != rf.get(f):
                    mism.append(f"region[{i}].{f}: new={json.dumps(rn.get(f))[:80]}"
                                f" != frozen={json.dumps(rf.get(f))[:80]}")
    return mism


def g2_contact_bitwise() -> dict:
    new = json.loads(NEW["contact"].read_text())
    fro = json.loads(FROZEN["contact"].read_text())
    mism = compare_contact(NEW["contact"], FROZEN["contact"])
    check(not mism, "G2 contact 决定性字段对冻结件逐位相等（"
          f"{len(G2_DECISIVE_TOP)} 顶层＋{len(G2_DECISIVE_CERT)} 证书级＋"
          f"逐区域 {len(G2_DECISIVE_REGION)} 字段×{fro['interval_certificate']['n_regions']}"
          " 区）" + ("" if not mism else f"；首 3 项漂移：{mism[:3]}"))
    pd_new = new["interval_certificate"]["pi_degree"]
    pd_fro = fro["interval_certificate"]["pi_degree"]
    check(pd_new == 17 and pd_fro == 5,
          f"G2 唯一漂移 pi_degree {pd_fro}→{pd_new}（==6·2+5，修复直读）")
    # advisory：其余确定性字段（剔运行时戳/点数口径）
    advis = {}
    for key, drop in (("dominance_vs_old", {"check_s"}),
                      ("gap_metrics", {"metric_s"}),
                      ("e_anchor", set())):
        a = {k: v for k, v in new[key].items() if k not in drop}
        b = {k: v for k, v in fro[key].items() if k not in drop}
        same = a == b
        advis[key] = same
        (info if same else warn)(
            f"G2[advisory] {key}（剔 {sorted(drop)}）"
            f"{'逐位相同' if same else '存在漂移——不入判死面，如实入档'}")
    dl_new = new["dense_and_local"]
    dl_fro = fro["dense_and_local"]
    info(f"G2[advisory] dense 字段随点数不入比对：frozen points="
         f"{dl_fro['dense']['points']} min={dl_fro['dense']['min']:.3e}；"
         f"new points={dl_new['dense']['points']} "
         f"min={dl_new['dense']['min']:.3e}")
    return dict(mismatches=mism, pi_degree_frozen=pd_fro, pi_degree_new=pd_new,
                advisory=advis,
                dense_min_frozen=dl_fro["dense"]["min"],
                dense_min_new=dl_new["dense"]["min"])


def nc2_tamper_detected() -> None:
    import tempfile
    new = json.loads(NEW["contact"].read_text())
    tampered = json.loads(json.dumps(new))
    r0 = tampered["interval_certificate"]["regions"][0]
    assert r0["bound"] == "0", "NC2 前提：contact 首区域 bound=='0'（定理分支）"
    r0["bound"] = "1/1000000"
    r0["bound_float"] = 1e-06
    with tempfile.TemporaryDirectory(prefix="r10_nc2_") as td:
        tp = Path(td) / "r10_pifix_probe_contact.json"
        tp.write_text(json.dumps(tampered, ensure_ascii=False))
        p = subprocess.run([sys.executable, str(HERE / "r10_pifix_gate.py"),
                            "--g2-probe", str(tp)],
                           capture_output=True, text=True, timeout=300)
        detected = (p.returncode == 1
                    and any("region[0].bound" in ln for ln in
                            (p.stdout + p.stderr).splitlines()))
        check(detected,
              f"NC2 /tmp 篡改新 contact 输出（region[0].bound '0'→'1/1000000'）"
              f"在 G2 比对 exit 1（子进程 returncode={p.returncode}，"
              f"region[0].bound 漂移被点名）")


# ============================================================ G3 triple 判死维持
def g3_triple_death_maintained() -> dict:
    new = json.loads(NEW["triple"].read_text())
    fro = json.loads(FROZEN["triple"].read_text())
    cert = new["interval_certificate"]
    check(cert["ok"] is False and new["verdict"] == "dead",
          f"G3 triple 判死维持：interval_certificate.ok=={cert['ok']}、"
          f"verdict=={new['verdict']}（冻结件 ok="
          f"{fro['interval_certificate']['ok']}、verdict={fro['verdict']}）")
    pd_new = cert["pi_degree"]
    pd_fro = fro["interval_certificate"]["pi_degree"]
    check(pd_new == 18 and pd_fro == 0,
          f"G3 pi_degree {pd_fro}→{pd_new}（==6·3+0，修复直读）")
    dips = [r for r in cert["regions"] if r["pi_sign"] == "<0"]
    check(len(dips) == 3,
          f"G3 恰三 dip 区（Π<0 组合界分支）：实测 {len(dips)} 区")
    tube = json.loads((RESULTS / "tube.json").read_text())["ttp_spectrum"]
    nu = [Fraction(float(x)) for x in tube["nodes"]]
    old_dips = {tuple(r["interval"]): r for r in
                fro["interval_certificate"]["regions"] if r["pi_sign"] == "<0"}
    cmp_rows = []
    for r in dips:
        a, b = (Fraction(x) for x in r["interval"])
        mid = (a + b) / 2
        pi_mid = g_direct_pi(mid, nu, 3, 0)          # 独立构造 ∏(mid−ν)³
        bound = Fraction(r["bound"])
        pmin = Fraction(r["pi_min"])
        interval_key = tuple(r["interval"])
        old = old_dips.get(interval_key)
        cmp_rows.append(dict(
            interval=r["interval"], mid=str(mid),
            pi_mid_sign=("neg" if pi_mid < 0 else "nonneg"),
            pi_min_new=str(pmin)[:72], bound_new=str(bound)[:72],
            bound_new_float=float(bound),
            pi_min_old=(str(Fraction(old["pi_min"]))[:72] if old else None),
            bound_old_float=(float(Fraction(old["bound"])) if old else None),
            ok=bool(bound < 0 and pmin < 0 and pi_mid < 0)))
    check(all(row["ok"] for row in cmp_rows),
          "G3 三 dip 区逐区 bound<0＋pi_min<0＋门内独立 Fraction 构造 Π(mid)"
          "＝∏(mid−ν_k)³<0 符号核验（新 bound_float："
          + ", ".join(f"{row['bound_new_float']:.3e}" for row in cmp_rows)
          + "；旧失真值："
          + ", ".join(f"{row['bound_old_float']:.3e}" for row in cmp_rows)
          + "）")
    dmin = new["dense_and_local"]["dense"]["min"]
    check(dmin is not None and dmin < 0.0,
          f"G3 dense_and_local 直接格点负证据复核（判死独立面）："
          f"dense.min={dmin:.3e} < 0（points="
          f"{new['dense_and_local']['dense']['points']}，advisory 点数口径）")
    return dict(pi_degree_frozen=pd_fro, pi_degree_new=pd_new, dips=cmp_rows,
                dense_min_new=new["dense_and_local"]["dense"]["min"],
                dense_min_frozen=fro["dense_and_local"]["dense"]["min"],
                dense_points_new=new["dense_and_local"]["dense"]["points"],
                dense_points_frozen=fro["dense_and_local"]["dense"]["points"])


# ============================================================ G4 冻结件守卫
def g4_frozen_guard() -> dict:
    rel = [str(p.relative_to(REPO)) for p in
           (FROZEN["contact"], FROZEN["triple"], FROZEN["plain"])]
    diff = subprocess.run(["git", "diff", "HEAD", "--"] + rel,
                          cwd=str(REPO), capture_output=True, text=True)
    stat = subprocess.run(["git", "status", "--porcelain", "--"] + rel,
                          cwd=str(REPO), capture_output=True, text=True)
    clean = (diff.returncode == 0 and diff.stdout.strip() == ""
             and stat.returncode == 0 and stat.stdout.strip() == "")
    check(clean, "G4 冻结件守卫：git diff HEAD 与 git status --porcelain 对 "
          "hermite_v2_probe_contact.json／hermite_v2_probe_triple.json／"
          "hermite_probe.json 三路径零改动"
          + ("" if clean else f"；diff={diff.stdout[:120]} status={stat.stdout[:120]}"))
    return dict(paths=rel, git_diff_empty=bool(diff.stdout.strip() == ""),
                git_status_empty=bool(stat.stdout.strip() == ""))


# ============================================================ G5 回归电池
def g5_regression_battery() -> dict:
    out = {}
    for g in BATTERY:
        t0 = time.time()
        try:
            p = subprocess.run([sys.executable, str(g)], cwd=str(REPO),
                               capture_output=True, text=True, timeout=600)
            rc = p.returncode
            tail = (p.stdout.strip().splitlines() or [""])[-1][:100]
        except subprocess.TimeoutExpired:
            rc, tail = -1, "timeout 600s"
        out[g.name] = dict(exit=rc, wall_s=round(time.time() - t0, 1),
                           tail=tail)
        check(rc == 0, f"G5 {g.name} 复跑 exit 0（{out[g.name]['wall_s']}s，"
              f"尾行：{tail}）" if rc == 0 else
              f"G5 {g.name} 复跑 exit {rc}（尾行：{tail}）")
    return out


# ============================================================ 主流程
def main() -> int:
    t0 = time.time()
    ap = argparse.ArgumentParser(
        description="R10A pifix-build-pi 验收门（--g2-probe 仅 NC2 自反用）")
    ap.add_argument("--g2-probe", type=str, default=None,
                    help="NC2 专用：对指定 contact 探针文件单跑 G2 决定性"
                         "比对（mismatch ⇒ exit 1）")
    args = ap.parse_args()
    if args.g2_probe:
        mism = compare_contact(Path(args.g2_probe), FROZEN["contact"])
        if mism:
            for m in mism:
                print(f"[g2-probe][MISMATCH] {m}", flush=True)
            print(f"[g2-probe] FAIL：{len(mism)} 项决定性字段漂移", flush=True)
            return 1
        print("[g2-probe] 比对通过（无决定性漂移）", flush=True)
        return 0

    print(f"[gate] r10_pifix_gate 启动（seed {SEED}，python "
          f"{sys.version.split()[0]}）", flush=True)
    for p in (NEW["contact"], NEW["triple"], LEDGER, *FROZEN.values()):
        if not p.exists():
            fail(f"前置缺失：{p}")
    if _checks["failed"] == 0:
        g1_unit_identities()
        nc1_old_bug_detected()
        g2_contact_bitwise()
        nc2_tamper_detected()
        g3_triple_death_maintained()
        g4_frozen_guard()
        g5_regression_battery()
    print("-" * 72, flush=True)
    print(f"[gate] 检查统计：{_checks['passed']} 过 / {_checks['failed']} 败"
          f"（{time.time() - t0:.0f}s）", flush=True)
    for m in _failures:
        print(f"[gate:FAIL] {m}", flush=True)
    if _failures:
        return 1
    print("[gate] exit 0 — 过门", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
