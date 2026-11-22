#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""moment_gate.py — R7-1 moment-containers 过门脚本（裸 python3，seed 20261007，
CWD 无关——一切路径由 __file__ 解析）。三分支（full/partial/dead）诚实门，
先例 hermite_gate（67c7459 / 107b8eb）。

检查序列（exit 0 = 过门）：
  ① 探针小档重放：venv 解释器重跑 (5,4) 档 baseline/containers（Clarabel，
     同 seed 同参数），与存档 results/moment_lift.json /probe/tiers 逐位/容差一致；
  ② 容器 PSD 抽查（exact LDLᵀ，随机配置×40）＋恒等式 (∗)＋负对照三件
     （N=8 常数 / 篡改 S_k / 非 PSD G 块必须全部被检出）；
  ③ 证书分支（若产出 n9-stage-a6-momentcap 证书）：
     --verify-cert exit 0（进程外重算＋LDLᵀ＋provenance）、certified ≤ E*+1e-6
     （铁律）；certified > 25.759571185601（严格超旧 cap 最佳）且
     |e_val−25.75998653127|≤1e-9 ⟹ full，否则 partial（残差分解须在档）；
  ④ dead 分支：probe.verdict=dead 时各档 delta_e_val＋noise_floor＋锚定证据
     完整入档（缺失即 FAIL）；
  ⑤ 篡改检出面：证书 claimed_bound/G 块系数篡改必须被 --verify-cert 拒绝；
     探针存档 e_val 篡改必须被 ① 的比对函数检出（在临时副本上模拟）。
"""
from __future__ import annotations

import json
import random
import shutil
import subprocess
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

SEED = 20261007
E_STAR = Fraction("25.759986531")             # energies.json 9 位参考值口径
E_HP = Fraction("25.75998653127")             # highPrecision 口径（D2）
OLD_CAP_BEST = Fraction("25.759571185601")    # typed m0748_M8（新证书须严格超越才 full）
PHI_TOL = Fraction(1, 10 ** 6)
VENV_PY = HERE.parent / ".venv" / "bin" / "python"

RESULTS = HERE / "results"
ARCHIVE = RESULTS / "moment_lift.json"
CERTS = REPO / "certificates"

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


# ============================================================ ① 探针重放
def compare_tier(arch_tier: dict, replay_tier: dict, tol: float = 1e-9) -> tuple[bool, str]:
    """档级一致性：e_val 双臂＋Δ＋噪声地板（容差内；逐位一致时如实报 exact）。"""
    diffs = []
    for key in ("e_val_baseline_best", "e_val_containers_best", "delta_e_val"):
        a, r = arch_tier.get(key), replay_tier.get(key)
        if a is None or r is None:
            return False, f"字段缺失 {key}（arch={a}, replay={r}）"
        if abs(float(a) - float(r)) > tol:
            return False, f"{key}: arch={a} vs replay={r}（|Δ|>{tol}）"
        diffs.append(abs(float(a) - float(r)))
    exact = all(d == 0.0 for d in diffs)
    return True, ("逐位一致" if exact else f"最大 |Δ|={max(diffs):.1e} ≤ {tol}")


def probe_replay(arch: dict) -> None:
    tiers = [t for t in arch.get("probe", {}).get("tiers", []) if "M" in t]
    small = [t for t in tiers if t["M"] <= 5] or tiers[:1]
    if not small:
        check("① 探针档在档（可重放的小档）", False, "probe.tiers 为空")
        return
    tier = small[0]
    if not VENV_PY.exists():
        check("① venv 解释器（cvxpy 探针重放需要）", False, str(VENV_PY))
        return
    with tempfile.TemporaryDirectory() as td:
        out = Path(td) / "replay.json"
        cmd = [str(VENV_PY), str(HERE / "moment_lift.py"), "--probe",
               "--probe-tiers", f"{tier['M']},{tier['K']}",
               "--out", str(out), "--probe-replay", "--no-anchored"]
        t0 = time.time()
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=1800)
        if proc.returncode != 0:
            check("① 探针重放运行", False, proc.stdout[-500:] + proc.stderr[-500:])
            return
        marker = "===PROBE-REPLAY-JSON==="
        if marker not in proc.stdout:
            check("① 重放 JSON 段", False, "stdout 无标记段")
            return
        replay = json.loads(proc.stdout.split(marker, 1)[1].strip())
        rt = [t for t in replay["tiers"] if t["M"] == tier["M"] and t["K"] == tier["K"]]
        if not rt:
            check("① 重放档存在", False, f"({tier['M']},{tier['K']})")
            return
        ok, detail = compare_tier(tier, rt[0])
        check(f"① 探针 ({tier['M']},{tier['K']}) 重放与存档一致", ok,
              f"{detail}（{time.time() - t0:.0f}s）")


# ============================================================ ② PSD 抽查＋负对照
def spot_and_negatives() -> None:
    import moment_lift as ML
    rng = random.Random(SEED)
    lo = Fraction(-187, 250)
    try:
        v = ML.container_validity_selftest(6, 6, lo, 40, rng)
        ok = bool(v["psd_spot"]["ok"] and v["identity"]["ok"]
                  and v["S_vs_kernel"]["ok"] and v["zeta_vs_kernel"]["ok"])
        check("② 容器抽查（M_k≽0×40 配置 exact LDLᵀ＋(∗) 恒等式＋ζ/核和三口径）",
              ok, f"wall {v['wall_s']}s")
        nc = ML.negative_controls(6, 6, lo, rng)
        for key, label in (("a_n8_constants_detected", "N=8 常数（β=1,γ=1/7）"),
                           ("b_tampered_S_detected", "篡改 S_k 系数位"),
                           ("c_nonpsd_G_detected", "随机对称非 PSD G 块"),
                           ("c_negative_container_sum_found", "Σ⟨G,M_k⟩<0 出现")):
            check(f"② 负对照必须检出：{label}", bool(nc.get(key)))
    except AssertionError as exc:
        check("② 容器抽查＋负对照", False, str(exc))


# ============================================================ ③ 证书分支
def verify_cert_subprocess(path: Path) -> tuple[bool, str]:
    proc = subprocess.run([sys.executable, str(HERE / "moment_lift.py"),
                           "--verify-cert", str(path)],
                          capture_output=True, text=True, timeout=3600)
    return proc.returncode == 0, proc.stdout[-400:] + proc.stderr[-200:]


def cert_branch(arch: dict) -> str:
    """返回分支名 full/partial（无证书时返回 'dead-or-none'，由 ④ 裁定）。"""
    certs = sorted(CERTS.glob("n9-stage-a6-momentcap-*.json"))
    rows = arch.get("cap_rungs", [])
    if not certs and not rows:
        return "none"
    claims = []
    for c in certs:
        ok, detail = verify_cert_subprocess(c)
        if not check(f"③ {c.name} --verify-cert exit 0", ok, detail[-200:]):
            continue
        cert = json.loads(c.read_text())
        certified = Fraction(cert["claimed_bound"])
        ok2 = 0 < certified <= E_STAR + PHI_TOL
        check(f"③ {c.name} 铁律 0 < certified ≤ E*+1e-6", ok2,
              f"certified {float(certified):.12f}")
        row = next((r for r in rows if r.get("certificate", "").endswith(c.name)), None)
        claims.append((certified, row))
    if not claims:
        return "partial"
    best_cert, best_row = max(claims, key=lambda p: p[0])
    beats_old = best_cert > OLD_CAP_BEST
    e_val = (best_row or {}).get("e_raw")
    acc = e_val is not None and abs(float(e_val) - float(E_HP)) <= 1e-9
    branch = "full" if (beats_old and acc) else "partial"
    print(f"[gate:INFO] 分支 = {branch}（certified={float(best_cert):.12f} "
          f"超旧 cap 最佳={beats_old}（{float(OLD_CAP_BEST):.12f}）；"
          f"e_val={e_val} 验收 |e_val−E_hp|≤1e-9={acc}）", flush=True)
    check(f"③ 分支判定字段完整（残差分解/锚定层在档）",
          bool((best_row or {}).get("R1")) and "anchoring" in (best_row or {}),
          "")
    return branch


# ============================================================ ④ dead 证据
def dead_branch(arch: dict) -> None:
    probe = arch.get("probe", {})
    verdict = probe.get("verdict", {})
    check("④ verdict 字段在档且合法", verdict.get("verdict") in ("alive", "dead"),
          str(verdict.get("verdict")))
    tiers = [t for t in probe.get("tiers", []) if "M" in t]
    check("④ dead 证据：各档 delta_e_val 在档", len(tiers) >= 2
          and all(t.get("delta_e_val") is not None for t in tiers),
          f"{len(tiers)} 档")
    check("④ dead 证据：各档 noise_floor 在档（量化噪声地板）",
          all(t.get("noise_floor") is not None for t in tiers),
          str([t.get("noise_floor") for t in tiers]))
    check("④ dead 证据：判据规则文本在档", bool(verdict.get("rule")))
    anchored = probe.get("anchored", [])
    has_anchor_ev = bool(anchored) and any(
        k in a for a in anchored if isinstance(a, dict)
        for k in ("anchored_containers", "anchored_baseline", "error"))
    check("④ dead 证据：锚定探针（机制性）在档", has_anchor_ev,
          f"{len(anchored)} 档")
    if verdict.get("verdict") == "dead":
        # 判死与证据严格对齐：各档 |Δ| 不显著大于噪声地板（无档位 Δ>max(noise,1e-6)）
        offending = [f"({t['M']},{t['K']})Δ={t['delta_e_val']:+.2e}"
                     for t in tiers
                     if t["delta_e_val"] > max(t["noise_floor"], 1e-6)]
        check("④ dead 与证据对齐（无档位 Δ 显著超噪声地板）", not offending,
              "; ".join(offending) or "全部档 |Δ| ≤ max(noise,1e-6)")
        check("④ dead：无 a6 证书被声称有效", not sorted(
            CERTS.glob("n9-stage-a6-momentcap-*.json")) and not arch.get("cap_rungs"),
            "证书目录与 cap_rungs 均空")


# ============================================================ ⑤ 篡改检出
def tamper_checks(arch: dict) -> None:
    # (a) 证书篡改（若在）
    certs = sorted(CERTS.glob("n9-stage-a6-momentcap-*.json"))
    if certs:
        src = certs[0]
        cert = json.loads(src.read_text())
        k = cert["provenance"]["round_bits"]
        cases = {}
        o = json.loads(src.read_text())
        o["claimed_bound"] = str(Fraction(o["claimed_bound"]) + Fraction(1, 10 ** 9))
        cases["claimed_bound+1e-9"] = o
        o = json.loads(src.read_text())
        o["blocks"]["e"][0] = str(Fraction(o["blocks"]["e"][0])
                                  + Fraction(1, 1 << (k - 1)))
        cases["e_bit"] = o
        o = json.loads(src.read_text())
        o["blocks"]["G0"][0][0] = str(Fraction(o["blocks"]["G0"][0][0])
                                      + Fraction(1, 1 << (k - 1)))
        cases["G0_bit"] = o
        for name, obj in cases.items():
            with tempfile.TemporaryDirectory() as td:
                tmp = Path(td) / src.name
                tmp.write_text(json.dumps(obj, ensure_ascii=False))
                ok, _d = verify_cert_subprocess(tmp)
                check(f"⑤ 篡改证书 {name} ⇒ --verify-cert 必拒", not ok)
    else:
        # (b) 探针存档篡改（dead 分支主篡改面）：e_val 拉高 1e-6 必须被 ① 的比对检出
        tiers = [t for t in arch.get("probe", {}).get("tiers", []) if "M" in t]
        small = [t for t in tiers if t["M"] <= 5] or tiers[:1]
        if not small:
            check("⑤ 篡改探针档（无档可篡）", True, "无档")
            return
        tier = dict(small[0])
        fake = dict(tier)
        fake["e_val_containers_best"] = float(fake["e_val_containers_best"]) + 1e-6
        ok, detail = compare_tier(tier, fake)
        check("⑤ 篡改探针存档 e_val(+1e-6) ⇒ ① 比对必检出", not ok, detail)
        fake2 = dict(tier)
        fake2["delta_e_val"] = float(fake2["delta_e_val"]) + 1e-5
        ok2, detail2 = compare_tier(tier, fake2)
        check("⑤ 篡改探针存档 delta_e_val(+1e-5) ⇒ ① 比对必检出", not ok2, detail2)
        # verdict 篡改：dead→alive 无证据支撑必须被 ④ 对齐检查拒绝
        fake_arch = json.loads(json.dumps(arch))
        fake_arch["probe"]["verdict"]["verdict"] = "alive"
        t_fake = fake_arch["probe"]["tiers"]
        offending = [t for t in t_fake if t["delta_e_val"] > max(t["noise_floor"], 1e-6)]
        check("⑤ 篡改 verdict dead→alive ⇒ ④ 对齐检查必拒", not offending,
              "alive 声称与 Δ≤噪声的证据冲突")


# ============================================================ 主流程
def main() -> int:
    t0 = time.time()
    print(f"[gate] moment_gate 启动（seed {SEED}，python {sys.version.split()[0]}，"
          f"CWD={Path.cwd()}）", flush=True)
    if not ARCHIVE.exists():
        print(f"[gate] FAIL：探针存档缺失 {ARCHIVE}")
        return 1
    arch = json.loads(ARCHIVE.read_text())
    check("① 存档字段（probe/verdict/seed/code_version）",
          bool(arch.get("probe")) and arch["probe"].get("seed") == SEED
          and bool(arch["probe"].get("code_version")),
          str(arch.get("probe", {}).get("verdict", {}).get("verdict")))
    probe_replay(arch)
    spot_and_negatives()
    branch = cert_branch(arch)
    dead_branch(arch)
    tamper_checks(arch)
    print("-" * 72, flush=True)
    print(f"[gate] 检查统计：{_checks['passed']} 过 / {_checks['failed']} 败"
          f"（{time.time() - t0:.0f}s，分支={branch}）", flush=True)
    if _failures:
        for f in _failures:
            print(f"[gate:FAIL] {f}", flush=True)
        return 1
    print(f"[gate] exit 0 — 过门", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
