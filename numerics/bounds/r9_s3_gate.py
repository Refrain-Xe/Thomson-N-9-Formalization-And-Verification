#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r9_s3_gate.py — R9A s3-quotient-rederive 验收门（seed 20261010，全确定性）。

验收对象：
  验证器 numerics/bounds/r9_s3_rederive.py（S₃ 商环装配自写第二实现，
  stdlib only，禁 import typed_ladder/QuotientMaps/thomson_certs/sdp_bound/
  sdp_certify/l2_rigorize）
  产物 numerics/bounds/results/r9_s3_rederive.json

门检查（cheap-first：静态→负对照（验证器内部 cheap-first 使篡改副本在
R1/certified 相位快速失败）→亲跑→三方对账）：
  G1 验证器禁 import 静态查（AST import 节点；含正对照／负对照）
  G2 亲跑验证器（--out 指向临时目录，不触盘上结果 json）exit 0
  G3 三方逐位对账：盘上结果 json ↔ 证书 provenance ↔ l2_rigorous.json
     （R1×3／R2×2／defl／R2max／certified==claimed==certified_recomputed／
     ε_forcing.exact），另 G2 新鲜输出与盘上 json 全部值域逐位相等
     （防陈旧产物）
  G4 恒等式 trial 记录：≥3 trial、diff=="0" 精确、seed==20261011
     （盘上与新鲜两处）
  NC1 /tmp 证书副本 B_AAA_1[i][j] += 2⁻⁶⁰（seed 20261010 选 (i,j)）
     ⇒ 验证器 exit≠0 且检出面含 "R1"
  NC2 /tmp 副本 claimed_bound += 2⁻⁶⁰ ⇒ exit≠0 且检出面含 "certified"
  NC3 禁 import 正对照：注入副本必须被 G1 检出器标记（未标记 ⇒ 门 exit 1）

用法：python3 numerics/bounds/r9_s3_gate.py（CWD 无关；campaign 根路由经
thomson-n9/thomson-n9/… 包装器先例）。exit 0 = 过门。
"""
from __future__ import annotations

import ast
import json
import random
import subprocess
import sys
import tempfile
import time
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
VERIFIER = HERE / "r9_s3_rederive.py"
CERT = REPO / "certificates" / "n9-stage-a4-typedcap-m0748_M9.json"
RESULTS = HERE / "results" / "r9_s3_rederive.json"
L2R = HERE / "results" / "l2_rigorous.json"
SEED = 20261010
IDENT_SEED = 20261011
TAMPER = Fraction(1, 2 ** 60)
FORBIDDEN = ("typed_ladder", "QuotientMaps", "thomson_certs", "sdp_bound",
             "sdp_certify", "l2_rigorize")
RUN_TIMEOUT_S = 300

t_gate0 = time.time()


def log(msg: str) -> None:
    print(msg, flush=True)


def fail(msg: str) -> None:
    print(f"[FAIL] {msg}", flush=True)
    sys.exit(1)


def check(name: str, ok: bool, detail: str = "") -> bool:
    log(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f"：{detail}" if detail else ""))
    if not ok:
        fail(f"{name} 未过")
    return ok


# ============================================================ G1/NC3 检出器
def scan_forbidden_imports(path: Path):
    """AST 静态查：返回 (是否命中, 命中清单)。只查 import 节点（注释/
    文档字符串中的提及不算；动态 importlib 规避不在静态能力内，运行时
    sys.modules 复核在验证器内——如实分层）。"""
    bad = []
    tree = ast.parse(Path(path).read_text())
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for al in node.names:
                if al.name.split(".")[0] in FORBIDDEN:
                    bad.append(f"L{node.lineno} import {al.name}")
        elif isinstance(node, ast.ImportFrom):
            mod = node.module or ""
            if mod.split(".")[0] in FORBIDDEN:
                bad.append(f"L{node.lineno} from {mod} import …")
            elif node.level > 0:
                for al in node.names:
                    if al.name.split(".")[0] in FORBIDDEN:
                        bad.append(f"L{node.lineno} 相对 import {al.name}")
    return (len(bad) > 0), bad


def run_verifier(cert_path: Path, out_path: Path, timeout: int = RUN_TIMEOUT_S):
    t0 = time.time()
    proc = subprocess.run(
        [sys.executable, str(VERIFIER), "--cert", str(cert_path), "--out", str(out_path)],
        capture_output=True, text=True, timeout=timeout)
    dt = time.time() - t0
    return proc, dt


# ============================================================ 主流程
def main() -> None:
    if len(sys.argv) > 1:
        print(f"用法：{sys.argv[0]}（无参数；全确定性 seed={SEED}）", flush=True)
        sys.exit(2)
    tmp = tempfile.TemporaryDirectory(prefix="r9_s3_gate_")
    tmpdir = Path(tmp.name)
    summary = {}

    for p in (VERIFIER, CERT, RESULTS, L2R):
        if not p.exists():
            fail(f"必要文件不在盘：{p}")

    # ---- G1 静态禁 import（cheap-first 第一层）----
    t0 = time.time()
    hit, bad = scan_forbidden_imports(VERIFIER)
    check("G1 验证器禁 import 静态查", not hit, "; ".join(bad) if bad else
          f"AST import 节点 0 命中（禁清单 {list(FORBIDDEN)}）")
    pos = tmpdir / "pos_control.py"
    pos.write_text("import typed_ladder\nfrom sdp_bound import Poly3\n"
                   "from QuotientMaps import QuotientMaps\n")
    hit_p, bad_p = scan_forbidden_imports(pos)
    check("G1 正对照（含禁 import 的文件必须被标记）", hit_p, "; ".join(bad_p))
    neg = tmpdir / "neg_control.py"
    neg.write_text("import json\nimport fractions\nfrom math import comb\n")
    hit_n, _ = scan_forbidden_imports(neg)
    check("G1 负对照（干净 stdlib 文件不误报）", not hit_n)
    summary["G1_static_s"] = round(time.time() - t0, 2)

    # ---- NC3 禁 import 正对照（独立检出面：注入验证器副本）----
    t0 = time.time()
    injected = tmpdir / "r9_s3_rederive_injected.py"
    injected.write_text(VERIFIER.read_text() + "\nimport l2_rigorize  # 注入\n")
    hit_i, bad_i = scan_forbidden_imports(injected)
    check("NC3 禁 import 正对照（验证器副本注入 import l2_rigorize 必须被检出）",
          hit_i, "; ".join(bad_i))
    summary["NC3_s"] = round(time.time() - t0, 2)

    cert = json.loads(CERT.read_text())

    # ---- NC1 篡 B_AAA_1 系数 +2⁻⁶⁰ ⇒ R1 失配 exit 1 ----
    t0 = time.time()
    rng = random.Random(SEED)
    i_t, j_t = rng.randrange(165), rng.randrange(165)
    nc1 = json.loads(json.dumps(cert))          # 深拷贝
    nc1["blocks"]["B_AAA_1"][i_t][j_t] = str(
        Fraction(nc1["blocks"]["B_AAA_1"][i_t][j_t]) + TAMPER)
    nc1_path = tmpdir / "cert_nc1.json"
    nc1_path.write_text(json.dumps(nc1))
    proc1, dt1 = run_verifier(nc1_path, tmpdir / "out_nc1.json")
    detected1 = (proc1.returncode != 0) and ("R1" in proc1.stdout)
    check("NC1 B_AAA_1 系数 +2⁻⁶⁰ ⇒ exit≠0 且检出面含 R1", detected1,
          f"篡改 B_AAA_1[{i_t}][{j_t}]；exit={proc1.returncode}；"
          f"tail={' | '.join(proc1.stdout.strip().splitlines()[-1:])}")
    summary["NC1_s"] = round(dt1, 1)

    # ---- NC2 篡 claimed_bound +2⁻⁶⁰ ⇒ certified 失配 exit 1 ----
    t0 = time.time()
    nc2 = json.loads(json.dumps(cert))
    nc2["claimed_bound"] = str(Fraction(nc2["claimed_bound"]) + TAMPER)
    nc2_path = tmpdir / "cert_nc2.json"
    nc2_path.write_text(json.dumps(nc2))
    proc2, dt2 = run_verifier(nc2_path, tmpdir / "out_nc2.json")
    detected2 = (proc2.returncode != 0) and ("certified" in proc2.stdout)
    check("NC2 claimed_bound +2⁻⁶⁰ ⇒ exit≠0 且检出面含 certified", detected2,
          f"exit={proc2.returncode}；"
          f"tail={' | '.join(proc2.stdout.strip().splitlines()[-1:])}")
    summary["NC2_s"] = round(dt2, 1)

    # ---- G2 亲跑验证器（--out 临时目录，不触盘上结果 json）----
    t0 = time.time()
    proc, dt = run_verifier(CERT, tmpdir / "out_g2.json")
    check("G2 亲跑验证器 exit 0", proc.returncode == 0,
          f"{dt:.1f}s；{' | '.join(proc.stdout.strip().splitlines()[-1:])}")
    fresh = json.loads((tmpdir / "out_g2.json").read_text())
    summary["G2_run_s"] = round(dt, 1)

    # ---- G3 三方逐位对账（盘上 json ↔ 证书 provenance ↔ l2_rigorous）----
    t0 = time.time()
    res = json.loads(RESULTS.read_text())
    prov = cert["provenance"]["residuals"]
    l2r = json.loads(L2R.read_text())
    cr = l2r["certificate_rebuild"]
    F = Fraction

    def eq3(a, b, c):
        return str(F(a)) == str(F(b)) == str(F(c))

    g3 = dict(
        R1_AAA=eq3(res["R1_exact"]["AAA"], prov["R1"]["AAA"], cr["R1_exact"]["AAA"]),
        R1_AAB=eq3(res["R1_exact"]["AAB"], prov["R1"]["AAB"], cr["R1_exact"]["AAB"]),
        R1_ABC=eq3(res["R1_exact"]["ABC"], prov["R1"]["ABC"], cr["R1_exact"]["ABC"]),
        R2_AA=eq3(res["R2_exact"]["AA"], prov["R2"]["AA"], cr["R2_exact"]["AA"]),
        R2_AB=eq3(res["R2_exact"]["AB"], prov["R2"]["AB"], cr["R2_exact"]["AB"]),
        defl=eq3(res["defl_exact"], prov["defl"], cr["defl_exact"]),
        R2max=eq3(res["R2max_exact"], prov["R2max"], cr["R2max_exact"]),
        certified=(str(F(res["certified_recomputed"]))
                   == str(F(cert["claimed_bound"]))
                   == str(F(res["claimed_bound"]))
                   == str(F(cr["certified_recomputed"]))
                   == str(F(cr["claimed_bound"]))),
        eps=(str(F(res["l2_rigorous_match"]["eps_recomputed"]))
             == str(F(l2r["eps_forcing"]["exact"]))
             == str(F(fresh["l2_rigorous_match"]["eps_recomputed"]))),
        provenance_match_flags=(res["provenance_residuals_match"]
                                == fresh["provenance_residuals_match"]
                                == dict(R1={o: True for o in ("AAA", "AAB", "ABC")},
                                        R2={c: True for c in ("AA", "AB")},
                                        defl=True, R2max=True)),
    )
    # G2 新鲜输出与盘上 json 值域逐位相等（防陈旧产物）
    stale_fields = dict(
        R1_exact=fresh["R1_exact"] == res["R1_exact"],
        R2_exact=fresh["R2_exact"] == res["R2_exact"],
        defl_exact=fresh["defl_exact"] == res["defl_exact"],
        R2max_exact=fresh["R2max_exact"] == res["R2max_exact"],
        certified_recomputed=fresh["certified_recomputed"] == res["certified_recomputed"],
        claimed_bound=fresh["claimed_bound"] == res["claimed_bound"],
        identity_records=fresh["identity"]["records"] == res["identity"]["records"],
        structural_checks=fresh["structural_checks"] == res["structural_checks"],
        orbit_classes=(fresh["orbit_perm_consistency"]["classes"]
                       == res["orbit_perm_consistency"]["classes"] == 10),
    )
    check("G3 三方逐位对账（R1×3/R2×2/defl/R2max/certified/ε）",
          all(g3.values()), json.dumps(g3))
    check("G3 盘上 json 与 G2 新鲜输出值域逐位相等（防陈旧）",
          all(stale_fields.values()), json.dumps(stale_fields))
    summary["G3_s"] = round(time.time() - t0, 2)

    # ---- G4 恒等式 trial 记录 ----
    t0 = time.time()
    ok4 = True
    for tag, doc in (("盘上", res), ("新鲜", fresh)):
        recs = doc["identity"]["records"]
        ok4 = ok4 and len(recs) >= 3 and all(r["diff"] == "0" and r["ok"] for r in recs)
        ok4 = ok4 and doc["identity"]["seed"] == IDENT_SEED
        ok4 = ok4 and doc["cli"]["seed"] == IDENT_SEED
    check("G4 恒等式 trial：≥3 trial、diff=='0' 精确、seed==20261011（盘上＋新鲜）",
          ok4, f"盘上 {len(res['identity']['records'])} trial ／ "
               f"新鲜 {len(fresh['identity']['records'])} trial")
    summary["G4_s"] = round(time.time() - t0, 2)

    summary.update(
        seed=SEED, verifier=str(VERIFIER.relative_to(REPO)),
        results=str(RESULTS.relative_to(REPO)),
        cert=str(CERT.relative_to(REPO)), l2r=str(L2R.relative_to(REPO)),
        nc1_tamper=f"B_AAA_1[{i_t}][{j_t}] + 2^-60",
        nc2_tamper="claimed_bound + 2^-60",
        all_pass=True, wall_s=round(time.time() - t_gate0, 1))
    print(json.dumps(dict(kind="r9-s3-gate", **summary), ensure_ascii=False, indent=1))
    log(f"[done ] r9_s3_gate 全过（{summary['wall_s']}s）：G1（含正/负对照）＋NC3＋"
        f"NC1＋NC2＋G2＋G3（三方＋防陈旧）＋G4；exit 0")
    tmp.cleanup()


if __name__ == "__main__":
    main()
