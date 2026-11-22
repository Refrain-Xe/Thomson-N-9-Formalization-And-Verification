#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""hermite_gate.py — R6 hermite-engine 过门脚本（裸 python3，seed 20261006）.

检查序列（exit 0 = 过门）：
  ① 探针快速档复检（1e5 点）＋与存档 hermite_probe.json 一致性；
  ② 三分支：
     alive   ⇒ 全部 a5 证书 --verify-cert 式重验（Fraction 重算＋exact.py LDLᵀ
               ＋provenance 字段 --k/code_version/seed）＋条带 >E*、cap ≤E*+1e-6
               断言＋cap 验收（e_val>25.759986531 且 |e_val−25.75998653127|≤1e-9，
               裁决 D2）＋账本与实存证书一致；
     partial ⇒ 同上重验，blocked 条带必须带 best_certified_attempt 数字在账，
               账本（hermite_cap.json/hermite_strips.json）与 certificates/ 实存
               一致；
     dead    ⇒ notes/hermite-dead.md 在档，且无 a5 证书被声称有效；
  ③ 负对照三件（tmp 副本上）：
     (a) 节点扰动 1e-9 ⇒ 判据 (iii) 锚恒等必败（字面锚与存档同口径锚双双
         >1e-12）；
     (b) 去导数条件（纯 Lagrange）⇒ 判据 (i)/(ii) 必败；
     (c) 篡改证书一个 dyadic 系数位 ⇒ 证书验证必拒。
"""
from __future__ import annotations

import json
import random
import shutil
import sys
import tempfile
import time
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE / "typed"))
sys.path.insert(0, str(HERE.parents[2] / "thomson-workflow" / "certificates"))

SEED = 20261006
E_STAR = Fraction("25.759986531")             # energies.json 9 位参考值口径
E_HP = Fraction("25.75998653127")             # highPrecision 口径（D2）
PHI_TOL = Fraction(1, 10 ** 6)

import hermite_minorant as hm                                # noqa: E402
import hermite_ladder as hl                                  # noqa: E402
from thomson_certs.exact import is_positive_definite        # noqa: E402

RESULTS = HERE / "results"
PROBE_JSON = RESULTS / "hermite_probe.json"
CAP_JSON = RESULTS / "hermite_cap.json"
STRIPS_JSON = RESULTS / "hermite_strips.json"
CERTS = REPO / "certificates"
DEAD_NOTE = REPO / "notes" / "hermite-dead.md"

_failures: list[str] = []
_checks = {"passed": 0, "failed": 0}


def check(name: str, ok: bool, detail: str = "") -> bool:
    tag = "PASS" if ok else "FAIL"
    print(f"[gate:{tag}] {name}" + (f" — {detail}" if detail else ""), flush=True)
    if ok:
        _checks["passed"] += 1
    else:
        _checks["failed"] += 1
        _failures.append(f"{name}: {detail}")
    return ok


# ============================================================ ① 探针快速档复检
def probe_recheck() -> dict | None:
    if not PROBE_JSON.exists():
        check("① hermite_probe.json 在档", False)
        return None
    arch = json.loads(PROBE_JSON.read_text())
    check("① hermite_probe.json 在档", True)
    res = hm.run_probe(variant="hermite", npts=100_000, rigorous=False)
    check("① 快速档判据 (i) 非负", res["criteria"]["i_dense"]["ok"],
          f"dense min {res['criteria']['i_dense']['min']:.2e}")
    check("① 快速档判据 (ii) c0>0", res["criteria"]["ii_sq_gap"]["ok"],
          f"c0 {res['criteria']['ii_sq_gap']['c0']:.3e}")
    check("① 快速档判据 (iii) 同口径锚", res["criteria"]["iii_anchor"]["ok"],
          f"|ΔE| {res['criteria']['iii_anchor']['abs_diff_same_caliber']:.2e}")
    c0a = arch["criteria"]["ii_sq_gap"]["c0"]
    c0q = res["criteria"]["ii_sq_gap"]["c0"]
    check("① c0 与存档一致（rel 1e-6）", abs(c0q - c0a) / abs(c0a) < 1e-6,
          f"quick {c0q:.9e} vs archived {c0a:.9e}")
    E_a = arch["criteria"]["iii_anchor"]["E_H"]
    E_q = res["criteria"]["iii_anchor"]["E_H"]
    check("① E_H 与存档一致（1e-12）", abs(E_q - E_a) < 1e-12,
          f"quick {E_q:.15f} vs archived {E_a:.15f}")
    check("① 存档 verdict 字段", arch.get("verdict") in ("alive", "dead"),
          arch.get("verdict", "<missing>"))
    check("① 存档 provenance seed", arch.get("seed") == SEED, str(arch.get("seed")))
    check("① 存档 provenance code_version 在档",
          bool(arch.get("code_version")), str(arch.get("code_version")))
    return arch


# ============================================================ ② 证书重验
def verify_a5_cert(path: Path) -> bool:
    """--verify-cert 式重验（Fraction 重算＋LDLᵀ＋provenance 字段）。"""
    try:
        if "hermite-cap" in path.name:
            certified = hl.verify_cap_cert_file(path)
            ok_bound = 0 < certified <= E_STAR + PHI_TOL
            if not ok_bound:
                check(f"② {path.name} cap ≤E*+1e-6", False,
                      f"certified {float(certified):.12f}")
                return False
        elif "hermite-strip" in path.name:
            certified = hl.verify_strip_cert_file(path)
            if not certified > E_STAR:
                check(f"② {path.name} strip >E*", False,
                      f"certified {float(certified):.12f}")
                return False
        else:
            return check(f"② {path.name} 类型识别", False)
    except SystemExit:
        return check(f"② {path.name} 重验", False, "verify 进程 exit≠0")
        # verify 内部 fail() 打印过原因
    cert = json.loads(path.read_text())
    prov = cert.get("provenance", {})
    missing = [f for f in ("round_bits", "code_version", "seed") if f not in prov]
    if missing:
        return check(f"② {path.name} provenance 字段", False, f"缺 {missing}")
    check(f"② {path.name} 重验＋provenance（--k={prov['round_bits']}, "
          f"seed={prov['seed']}）", True)
    return True


def branch_checks(verdict: str, arch: dict) -> dict:
    summary = dict(cap=None, strips=[], blocked=[], branch=None)
    if verdict == "dead":
        summary["branch"] = "dead"
        check("② dead 分支：notes/hermite-dead.md 在档", DEAD_NOTE.exists())
        a5 = sorted(CERTS.glob("n9-stage-a5-hermite-*.json"))
        claimed = []
        if CAP_JSON.exists():
            for r in json.loads(CAP_JSON.read_text()).get("rungs", []):
                claimed.append(f"cap:{r['tag']}")
        if STRIPS_JSON.exists():
            for s in json.loads(STRIPS_JSON.read_text()).get("strips", []):
                if s.get("status") == "certified":
                    claimed.append(f"strip:{s['tag']}")
        check("② dead 分支：无 a5 证书被声称有效", not claimed and not a5,
              f"实存 {len(a5)}，声称 {claimed}")
        return summary
    # ---- cap ----
    cap_rows = []
    if verdict == "alive":
        check("② alive ⇒ results/hermite_cap.json 在档（相位 B 交付物）",
              CAP_JSON.exists())
    if CAP_JSON.exists():
        cap_rows = json.loads(CAP_JSON.read_text()).get("rungs", [])
    if verdict == "alive":
        check("② alive ⇒ cap 账本含 ≥1 档", len(cap_rows) >= 1,
              f"{len(cap_rows)} 档")
    for r in cap_rows:
        cert_path = REPO / r["certificate"]
        ok = verify_a5_cert(cert_path)
        summary.setdefault("cap_rungs", []).append(
            dict(tag=r["tag"], M=r.get("M"), e_val=r.get("e_raw"),
                 certified=r.get("certified_float"), verified=bool(ok)))
    # 验收（D2）只对**最佳档**执行（低档 canary 不作验收口径，但其证书仍全验）
    cap_acc = None
    if cap_rows:
        best = max(cap_rows, key=lambda r: r.get("certified_float", 0.0))
        e_val = best.get("e_raw")
        acc1 = e_val is not None and e_val > float(E_STAR)
        acc2 = e_val is not None and abs(e_val - float(E_HP)) <= 1e-9
        cap_acc = bool(acc1 and acc2)
        print(f"[gate:INFO] cap 最佳档 {best['tag']}(M={best.get('M')}) "
              f"e_val={e_val}（验收 e_val>25.759986531 且 |e_val−25.75998653127|"
              f"≤1e-9：{'达标' if cap_acc else '未达标'}）", flush=True)
        summary["cap"] = dict(tag=best["tag"], e_val=e_val,
                              certified=best["certified_float"],
                              acceptance=cap_acc)
    # ---- strips ----
    strip_rows = []
    if STRIPS_JSON.exists():
        strip_rows = json.loads(STRIPS_JSON.read_text()).get("strips", [])
    for s in strip_rows:
        status = s.get("status", "certified")
        if status == "certified":
            ok = verify_a5_cert(REPO / s["certificate"])
            summary["strips"].append(dict(tag=s["tag"], status="certified",
                                          certified=s["certified_float"], ok=bool(ok)))
        else:
            check(f"② strip {s['tag']} blocked 记账带数", bool(s.get("certified_float")),
                  f"best_certified_attempt={s.get('certified_float')}")
            summary["blocked"].append(dict(tag=s["tag"],
                                           best=s.get("certified_float")))
    # ---- 账本与实存一致 ----
    on_disk = {p.name for p in CERTS.glob("n9-stage-a5-hermite-*.json")}
    claimed_files = set()
    for r in cap_rows:
        claimed_files.add(Path(r["certificate"]).name)
    for s in strip_rows:
        if s.get("status") == "certified":
            claimed_files.add(Path(s["certificate"]).name)
    check("② 账本与实存证书一致", on_disk == claimed_files,
          f"disk-only={sorted(on_disk - claimed_files)} "
          f"ledger-only={sorted(claimed_files - on_disk)}")
    # ---- 分支判定（alive 探针下的工程结局：full / partial）----
    n_blocked = len(summary["blocked"])
    n_cert_strips = len(summary["strips"])
    summary["branch"] = ("full" if (cap_acc and n_blocked == 0 and n_cert_strips >= 3)
                         else "partial")
    print(f"[gate:INFO] 分支 = {summary['branch']}（cap 验收 "
          f"{'达标' if cap_acc else '未达标'}；条带 certified {n_cert_strips} / "
          f"blocked {n_blocked}）", flush=True)
    if summary["branch"] == "partial":
        check("② partial 分支：blocked 条带全部带 best_certified_attempt 数字",
              all(s.get("certified_float") for s in strip_rows
                  if s.get("status") != "certified"),
              f"blocked {[s['tag'] for s in strip_rows if s.get('status') != 'certified']}")
    return summary


# ============================================================ ③ 负对照
def negative_controls(arch: dict) -> None:
    # (a) 节点扰动 1e-9 ⇒ (iii) 锚恒等必败
    res = hm.run_probe(variant="hermite", npts=20_000, rigorous=False,
                       perturb_nodes=1e-9)
    d_lit = res["criteria"]["iii_anchor"]["abs_diff_vs_tube_literal"]
    anchor_arch = arch["criteria"]["iii_anchor"]["anchor_same_caliber"]
    d_arch = abs(res["criteria"]["iii_anchor"]["E_H"] - anchor_arch)
    check("③a 节点扰动 1e-9 ⇒ 字面锚 |Δ|>1e-12", d_lit > 1e-12, f"|Δ|={d_lit:.3e}")
    check("③a 节点扰动 1e-9 ⇒ 存档同口径锚 |Δ|>1e-12", d_arch > 1e-12,
          f"|Δ|={d_arch:.3e}")

    # (b) 纯 Lagrange（去导数条件）⇒ (i)/(ii) 必败
    res2 = hm.run_probe(variant="lagrange", npts=20_000, rigorous=False)
    c1 = res2["criteria"]["i_dense"]["ok"]
    c2 = res2["criteria"]["ii_sq_gap"]["ok"]
    check("③b 纯 Lagrange ⇒ (i) 必败", not c1,
          f"dense min {res2['criteria']['i_dense']['min']:.3e}")
    check("③b 纯 Lagrange ⇒ (ii) 必败", not c2,
          f"c0 {res2['criteria']['ii_sq_gap']['c0']:.3e}")

    # (c) 篡改证书一个 dyadic 系数位 ⇒ 验证必拒
    # 注：ψ share 常数位存在**中性方向**（恒等式 Σ_T λ_T 加权不变性——
    # 篡后数据仍是同一界的合法证书，验证正确地不拒）；故篡非中性目标：
    # e 标量、M 系数、claimed_bound 三处各测一次，全部必拒。
    certs = sorted(CERTS.glob("n9-stage-a5-hermite-*.json"))
    if not certs:
        check("③c 篡改对照（无证书可篡改时跳过）", True, "无 a5 证书")
        return
    src = certs[0]

    def try_verify(path: Path) -> bool:
        try:
            if "hermite-cap" in path.name:
                hl.verify_cap_cert_file(path)
            else:
                hl.verify_strip_cert_file(path)
            return False                    # 未拒
        except SystemExit:
            return True
        except Exception:
            return True

    k = json.loads(src.read_text())["provenance"]["round_bits"]
    tampers = {}
    o = json.loads(src.read_text())
    o["blocks"]["e"][0] = str(Fraction(o["blocks"]["e"][0]) + Fraction(1, 1 << (k - 1)))
    tampers["e_bit"] = o
    o = json.loads(src.read_text())
    o["blocks"]["M"][3] = str(Fraction(o["blocks"]["M"][3]) + Fraction(1, 1 << (k - 1)))
    tampers["M_bit"] = o
    o = json.loads(src.read_text())
    o["claimed_bound"] = str(Fraction(o["claimed_bound"]) + Fraction(1, 10 ** 9))
    tampers["claimed_bound"] = o
    for name, obj in tampers.items():
        with tempfile.TemporaryDirectory() as td:
            tmp = Path(td) / src.name
            tmp.write_text(json.dumps(obj, ensure_ascii=False))
            check(f"③c 篡改 {name} 一位 ⇒ 证书验证必拒", try_verify(tmp))


# ============================================================ 主流程
def main() -> int:
    t0 = time.time()
    rng = random.Random(SEED)
    print(f"[gate] hermite_gate 启动（seed {SEED}，python {sys.version.split()[0]}）",
          flush=True)
    arch = probe_recheck()
    if arch is None:
        print("[gate] FAIL：探针存档缺失，无法继续")
        return 1
    verdict = arch["verdict"]
    summary = branch_checks(verdict, arch)
    negative_controls(arch)
    print("-" * 72, flush=True)
    print(f"[gate] 检查统计：{_checks['passed']} 过 / {_checks['failed']} 败"
          f"（{time.time() - t0:.0f}s）", flush=True)
    if _failures:
        for f in _failures:
            print(f"[gate:FAIL] {f}", flush=True)
        return 1
    print(f"[gate] exit 0 — 过门（verdict={verdict}）", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
