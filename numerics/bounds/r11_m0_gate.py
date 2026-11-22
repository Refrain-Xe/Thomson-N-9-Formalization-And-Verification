#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r11_m0_gate.py — R11 M0 Lean 首证验收门（G1–G6 ＋ 负对照 NC1/NC2/NC3）.

任务书口径（r11a-m0-lean）：冻结挑战四定理首件真证明——ThomsonN9/Solution.lean 在逐字节
复述冻结前缀（挑战件 26–149 行：R3/SphereConfig/coulombEnergy/cyl/triCapPrism 及辅助引理
至 triCapPrism_mem）之后给出 thomson_nine_M0 的真 Lean 内核证明（无任何内核旁路）。
本门对盘上状态逐项独立重放（不信任任何日志/账本；全部确定性检查，无随机路径；
seed 20261013 按惯例记档）。PATH 自动前置 ~/.elan/bin（缺失即 FAIL 附信息）。

检查面（对应任务书 G1–G6）：
  G1 冻结守卫：git diff HEAD 对 formal/lean/ComparatorChallenges/ThomsonN9.lean、
     formal/lean/lakefile.toml、formal/lean/lake-manifest.json、formal/lean/lean-toolchain
     全空；references/thomson-n7-lean（git 仓库）git diff HEAD 全空＋references/ 树哈希
     （排除 .git/.lake，48 文件）与账本记录一致。
  G2 token 扫描：check.sh 步 2 同正则对 Solution.lean 零命中
     （sorry/native_decide/ofReduceBool/ofReduceNat/trustCompiler/axiom/opaque/unsafe/
      partial/set_option/implemented_by/extern/csimp/元编程/#eval/#exit 等）。
  G3 lake build ThomsonN9 ComparatorChallenges（先删两模块 olean 强制重 elaborate）：
     恰 4 条挑战 declaration-uses-sorry 警告、声明行号恰为 {158,166,172,179}；
     解件 0 条；且源码级挑战 stripped=='sorry' 行 == [160,168,175,183]、解件 == 0。
  G4 CheckAxioms（lake env lean scripts/CheckAxioms.lean）：输出含
     'ThomsonN9.thomson_nine_M0'，其公理集合恰为 {propext, Classical.choice, Quot.sound}，
     全输出无 sorryAx/ofReduceBool/ofReduceNat/trustCompiler。
  G5 语句保真（非 DEFERRED）：本门独立 dump 两模块 elaborated bodies
     （Challenge 全量、Solution 限 Challenge 常量名），跑 scripts/compare_statements.py：
     STATEMENT COMPARISON: OK、missing/bad 全空、compared==33、
     skipped(not attempted)=={M1, thomson_nine, unique}、摘要与账本一致。
  G6 negative-control.sh（语句比对有牙负对照，必要时先补 logs/Challenge.tsv）：
     exit 0 且 logs/negative-control.log 检出且仅检出 ThomsonN9.thomson_nine。
  账本核对：results/r11_m0_ledger.json 的受控字段（provenance/sorry_counts/axioms/
     statement_compare/negative_control/references 树哈希）与本门新鲜事实逐项比对
     （墙钟类字段仅查在场与类型，informational）。
  NC1 /tmp 副本篡入一行 sorry ⇒ G2 正则必检出（未篡 /tmp 副本 0 命中 sanity）。
  NC2 /tmp 副本命题行 (36 / 2 : ℝ)→(37 / 2 : ℝ)（恰一处替换）⇒ 独立编译＋dump＋
     compare_statements.py 必检出且仅检出 ThomsonN9.thomson_nine_M0、FAILED。
  NC3 /tmp 篡账本（sorry_counts.challenge 4→5）⇒ 账本核对必失配并点名该字段。

用法（CWD 无关——全部路径自 __file__ 推导）：
  python3 numerics/bounds/r11_m0_gate.py              # 全门（exit 0 = 过）
  python3 numerics/bounds/r11_m0_gate.py --ledger P   # 对指定账本副本跑核对（NC3 用；
                                                      # 注意仍会重放 G3–G6 以取得新鲜事实）
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
REPO = HERE.parents[1]                 # thomson-n9/
CAMPAIGN_ROOT = REPO.parent            # 八电子在球面的分布/
LEAN_DIR = REPO / "formal" / "lean"
REFERENCES = CAMPAIGN_ROOT / "references"
REF_N7 = REFERENCES / "thomson-n7-lean"

SEED_GATE = 20261013                   # 惯例记档；本门无随机路径（确定性）

CHAL_REL = "ComparatorChallenges/ThomsonN9.lean"
SOL_REL = "ThomsonN9/Solution.lean"
CHAL = LEAN_DIR / CHAL_REL
SOL = LEAN_DIR / SOL_REL
FROZEN_REPO_PATHS = [
    "formal/lean/ComparatorChallenges/ThomsonN9.lean",
    "formal/lean/lakefile.toml",
    "formal/lean/lake-manifest.json",
    "formal/lean/lean-toolchain",
]
CHECK_SH = LEAN_DIR / "scripts" / "check.sh"
NC_SH = LEAN_DIR / "scripts" / "negative-control.sh"
CMP_PY = LEAN_DIR / "scripts" / "compare_statements.py"
DUMP_LEAN = LEAN_DIR / "scripts" / "DumpBody.lean"
CHECK_AXIOMS = LEAN_DIR / "scripts" / "CheckAxioms.lean"
LEDGER = RESULTS / "r11_m0_ledger.json"
LOGS = LEAN_DIR / "logs"

EXPECTED_CHAL_DECL_LINES = {158, 166, 172, 179}   # 挑战四定理声明行（build 警告行号）
EXPECTED_CHAL_SORRY_LINES = [160, 168, 175, 183]  # 挑战源码 stripped=='sorry' 行
EXPECTED_SKIPPED = sorted(["ThomsonN9.thomson_nine_M1",
                           "ThomsonN9.thomson_nine", "ThomsonN9.thomson_nine_unique"])
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN_AXIOMS = ["sorryAx", "ofReduceBool", "ofReduceNat", "trustCompiler"]
EXPECTED_COMPARED = 33                             # 挑战常量 36 − 未尝试 3

TOKEN_SCAN_REGEX = (
    r"sorry|native_decide|ofReduceBool|ofReduceNat|trustCompiler"
    r"|^\s*(private |protected |noncomputable )*(axiom|opaque|unsafe|partial) "
    r"|set_option|implemented_by|@\[extern|csimp"
    r"|^\s*(macro|syntax|elab|notation|infix|prefix|postfix|open Lean|initialize|run_cmd)"
    r"|#eval|#exit"
)


def fail(msg: str) -> None:
    print(f"[gate][FAIL] {msg}", flush=True)
    sys.exit(1)


def okmsg(msg: str) -> None:
    print(f"[gate][ok] {msg}", flush=True)


def run(cmd, cwd=None, env=None, timeout_s=580):
    return subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True,
                          timeout=timeout_s)


def jload(p: Path):
    return json.loads(p.read_text())


def git_diff_names(repo: Path, paths=None):
    cmd = ["git", "-C", str(repo), "diff", "HEAD", "--name-only"]
    if paths:
        cmd += list(paths)
    r = run(cmd)
    if r.returncode != 0:
        fail(f"G1 git 调用失败（{repo}）：{r.stderr.strip()[:300]}")
    return [l for l in r.stdout.splitlines() if l.strip()]


def references_tree_sha256() -> tuple[str, int]:
    """references/ 内容哈希（排除 .git/.lake，路径排序，逐文件内容哈希链）。"""
    if not REFERENCES.is_dir():
        fail(f"G1 references/ 不在档：{REFERENCES}")
    h = hashlib.sha256()
    n = 0
    for root, dirs, files in os.walk(REFERENCES):
        dirs[:] = sorted(d for d in dirs if d not in (".git", ".lake"))
        for f in sorted(files):
            p = Path(root) / f
            h.update(str(p.relative_to(REFERENCES)).encode())
            h.update(hashlib.sha256(p.read_bytes()).digest())
            n += 1
    return h.hexdigest(), n


# ---------------------------------------------------------------- G1
def check_g1(ref_tree_expected: str | None) -> str:
    # (a) thomson-n9 仓库内四个冻结件
    for p in (CHAL, LEAN_DIR / "lakefile.toml", LEAN_DIR / "lake-manifest.json",
              LEAN_DIR / "lean-toolchain"):
        if not p.exists():
            fail(f"G1 冻结件不在档：{p}")
    dirty = git_diff_names(REPO, FROZEN_REPO_PATHS)
    if dirty:
        fail(f"G1 冻结守卫失守：git diff HEAD 检出改动 {dirty}")
    # (b) references/（thomson-n7-lean 自身是 git 仓库）
    if REF_N7.is_dir():
        if run(["git", "-C", str(REF_N7), "rev-parse", "--is-inside-work-tree"]).returncode == 0:
            d2 = git_diff_names(REF_N7)
            if d2:
                fail(f"G1 references/thomson-n7-lean git diff HEAD 非空：{d2[:5]}")
    else:
        fail(f"G1 references/thomson-n7-lean 不在档：{REF_N7}")
    ref_hash, nfiles = references_tree_sha256()
    if ref_tree_expected is not None and ref_hash != ref_tree_expected:
        fail(f"G1 references/ 树哈希与账本失配：现测 {ref_hash} ≠ 账本 {ref_tree_expected}"
             f"（{nfiles} 文件，排除 .git/.lake）")
    okmsg(f"G1 冻结守卫全空：thomson-n9 四冻结件 git diff HEAD 无改动；"
          f"references/thomson-n7-lean 干净；references/ 树哈希 {ref_hash}（{nfiles} 文件）"
          + ("与账本一致" if ref_tree_expected else "（账本核对见后）"))
    return ref_hash


# ---------------------------------------------------------------- G2
def token_scan(path: Path) -> list[str]:
    r = run(["grep", "-nE", TOKEN_SCAN_REGEX, str(path)])
    if r.returncode not in (0, 1):
        fail(f"G2 grep 扫描失败（{path}）：rc={r.returncode} {r.stderr.strip()[:200]}")
    return [l for l in r.stdout.splitlines() if l.strip()]


def check_g2() -> None:
    if not SOL.exists():
        fail(f"G2 解件不在档：{SOL}")
    hits = token_scan(SOL)
    if hits:
        fail(f"G2 token 扫描命中 {len(hits)} 处（check.sh 步 2 同正则）：{hits[:5]}")
    okmsg("G2 token 扫描 0 命中（check.sh 步 2 同正则，grep -nE）")


# ---------------------------------------------------------------- G3
def check_g3() -> dict:
    # 源码级先查
    for p, expect in ((CHAL, EXPECTED_CHAL_SORRY_LINES), (SOL, [])):
        if not p.exists():
            fail(f"G3 源文件不在档：{p}")
        lines = p.read_text().splitlines()
        got = [i + 1 for i, ln in enumerate(lines) if ln.strip() == "sorry"]
        if got != expect:
            fail(f"G3 源码级 sorry 行失配（{p.name}）：{got} ≠ 期望 {expect}")
    # 强制重 elaborate 两模块（.lake 系 gitignored 脚手架）
    libdir = LEAN_DIR / ".lake" / "build" / "lib" / "lean"
    if not (LEAN_DIR / ".lake" / "packages" / "mathlib" / ".lake" / "build" / "lib" / "lean"
            / "Mathlib" / "Init.olean").exists():
        fail("G3 Mathlib 预构建 olean 不在档（.lake/packages/mathlib/.lake/build）——"
             "本门不做网络拉取；请先在有网环境跑一次 scripts/check.sh 步 3")
    if libdir.exists():
        shutil.rmtree(libdir / "ComparatorChallenges", ignore_errors=True)
        shutil.rmtree(libdir / "ThomsonN9", ignore_errors=True)
        for pat in ("ThomsonN9.olean", "ThomsonN9.ilean", "ThomsonN9.trace",
                    "ThomsonN9.olean.hash", "ThomsonN9.ilean.hash"):
            (libdir / pat).unlink(missing_ok=True)
    t0 = time.time()
    r = run(["lake", "build", "ThomsonN9", "ComparatorChallenges"], cwd=LEAN_DIR,
            timeout_s=580)
    wall = time.time() - t0
    out = r.stdout + r.stderr
    if r.returncode != 0:
        fail(f"G3 lake build 失败 rc={r.returncode}：\n{out[-1500:]}")
    chal_lines = sorted({int(m.group(1)) for m in re.finditer(
        r"warning:\s*ComparatorChallenges/ThomsonN9\.lean:(\d+):\d+:\s*declaration uses `sorry`",
        out)})
    n_chal = len(re.findall(r"ComparatorChallenges/ThomsonN9\.lean.*sorry", out))
    n_sol = len(re.findall(r"ThomsonN9/Solution\.lean.*sorry", out))
    if n_chal != 4 or set(chal_lines) != EXPECTED_CHAL_DECL_LINES:
        fail(f"G3 挑战 sorry 警告失配：计 {n_chal} 条、声明行 {chal_lines}"
             f" ≠ 期望 4 条 @{sorted(EXPECTED_CHAL_DECL_LINES)}")
    if n_sol != 0:
        fail(f"G3 解件 sorry 警告 {n_sol} 条 ≠ 0")
    if "Build completed successfully" not in out:
        fail("G3 lake build 未报 Build completed successfully")
    okmsg(f"G3 lake build（强制重 elaborate）成功 [{wall:.1f}s]：恰 4 挑战 sorry"
          f" @ 声明行 {chal_lines}＋0 解件 sorry；源码级 [160,168,175,183]/[] 对上")
    return {"build_wall_s": round(wall, 2), "build_rc": r.returncode,
            "challenge_sorry": n_chal, "challenge_decl_lines": chal_lines,
            "solution_sorry": n_sol}


# ---------------------------------------------------------------- G4
def check_g4() -> list[str]:
    if not CHECK_AXIOMS.exists():
        fail(f"G4 CheckAxioms.lean 不在档：{CHECK_AXIOMS}")
    r = run(["lake", "env", "lean", "scripts/CheckAxioms.lean"], cwd=LEAN_DIR)
    out = r.stdout + r.stderr
    if r.returncode != 0:
        fail(f"G4 CheckAxioms 编译失败 rc={r.returncode}：\n{out[-1500:]}")
    for bad in FORBIDDEN_AXIOMS:
        if bad in out:
            fail(f"G4 CheckAxioms 输出含禁止公理 {bad}")
    m = re.search(r"'ThomsonN9\.thomson_nine_M0' depends on axioms: \[(.*?)\]", out)
    if not m:
        fail(f"G4 CheckAxioms 输出未找到 'ThomsonN9.thomson_nine_M0' 的公理行：\n{out[:800]}")
    axioms = sorted(a.strip() for a in m.group(1).split(",") if a.strip())
    if set(axioms) != ALLOWED_AXIOMS:
        fail(f"G4 thomson_nine_M0 公理集合 {axioms} ≠ 恰 {{propext, Classical.choice, Quot.sound}}")
    okmsg(f"G4 CheckAxioms：thomson_nine_M0 公理恰为 {axioms}，"
          "无 sorryAx/ofReduceBool/ofReduceNat/trustCompiler")
    return axioms


# ---------------------------------------------------------------- G5
def dump_module(workdir: Path, module: str, tsv: Path, only_names: Path | None) -> None:
    workdir.mkdir(parents=True, exist_ok=True)
    script = workdir / f"Dump_{module.replace('.', '_')}.lean"
    body = DUMP_LEAN.read_text()
    body = body.replace("DUMPMOD", module).replace("OUTFILE", str(tsv))
    script.write_text(f"import {module}\n" + body)
    env = dict(os.environ)
    if only_names is not None:
        env["DUMP_ONLY"] = str(only_names)
    r = run(["lake", "env", "lean", str(script)], cwd=LEAN_DIR, env=env)
    if r.returncode != 0:
        fail(f"G5 dump {module} 失败 rc={r.returncode}：\n{(r.stdout + r.stderr)[-1500:]}")
    if not tsv.exists():
        fail(f"G5 dump {module} 未产出 {tsv}")


def check_g5(workdir: Path) -> dict:
    if not CMP_PY.exists() or not DUMP_LEAN.exists():
        fail(f"G5 比对脚本不在档：{CMP_PY} / {DUMP_LEAN}")
    chal_tsv = workdir / "Challenge.tsv"
    sol_tsv = workdir / "Solution.tsv"
    names = workdir / "Challenge.names"
    dump_module(workdir, "ComparatorChallenges.ThomsonN9", chal_tsv, None)
    names.write_text("".join(l.split("\t")[0] + "\n"
                             for l in chal_tsv.read_text().splitlines() if l.strip()))
    dump_module(workdir, "ThomsonN9.Solution", sol_tsv, names)
    if "ThomsonN9." not in sol_tsv.read_text():
        fail("G5 语句比对 DEFERRED：Solution dump 无 ThomsonN9.* 常量行")
    r = run(["python3", str(CMP_PY), str(chal_tsv), str(sol_tsv)], cwd=LEAN_DIR)
    out = r.stdout
    if r.returncode != 0 or "STATEMENT COMPARISON: OK" not in out:
        fail(f"G5 compare_statements.py 失败 rc={r.returncode}：\n{out[-1500:]}")
    md = re.search(r"missing in Solution: \[(.*?)\]", out)
    bt = re.search(r"kind/universe/type mismatches: \[(.*?)\]", out)
    bv = re.search(r"definition value mismatches: \[(.*?)\]", out)
    if not (md and bt and bv) or md.group(1).strip() or bt.group(1).strip() or bv.group(1).strip():
        fail(f"G5 语句比对存在 missing/失配：\n{out[-1500:]}")
    mc = re.search(r"compared: (\d+) \((\d+) definitions", out)
    sk = re.search(r"skipped \(not attempted\): \[(.*?)\]", out)
    dg = re.search(r"sha256 of the compared Challenge text: ([0-9a-f]{64})", out)
    if not (mc and sk and dg):
        fail(f"G5 无法解析 compare_statements.py 输出：\n{out[:800]}")
    compared, ndefs = int(mc.group(1)), int(mc.group(2))
    skipped = sorted(s.strip().strip("'") for s in sk.group(1).split(",") if s.strip())
    if compared != EXPECTED_COMPARED:
        fail(f"G5 compared={compared} ≠ {EXPECTED_COMPARED}（挑战 36 − 未尝试 3）")
    if skipped != EXPECTED_SKIPPED:
        fail(f"G5 skipped(not attempted)={skipped} ≠ {EXPECTED_SKIPPED}")
    okmsg(f"G5 语句保真（非 DEFERRED）：compared={compared}（{ndefs} defs 带值）、"
          f"skipped(not attempted)={skipped}、missing/失配全空、"
          f"摘要 {dg.group(1)[:16]}…")
    return {"status": "OK", "compared": compared, "defs_with_values": ndefs,
            "skipped_not_attempted": skipped,
            "sha256_compared_challenge_text": dg.group(1)}


# ---------------------------------------------------------------- G6
def check_g6(workdir: Path) -> dict:
    if not NC_SH.exists():
        fail(f"G6 negative-control.sh 不在档：{NC_SH}")
    # 负对照脚本需要 check.sh 产出的 logs/Challenge.tsv；缺失则本门用同流程补齐
    if not (LOGS / "Challenge.tsv").exists():
        dump_module(LOGS, "ComparatorChallenges.ThomsonN9", LOGS / "Challenge.tsv", None)
        (LOGS / "Challenge.names").write_text("".join(
            l.split("\t")[0] + "\n" for l in
            (LOGS / "Challenge.tsv").read_text().splitlines() if l.strip()))
    t0 = time.time()
    r = run(["bash", str(NC_SH)], cwd=LEAN_DIR)
    wall = time.time() - t0
    out = r.stdout + r.stderr
    if r.returncode != 0 or "NEGATIVE CONTROL OK" not in out:
        fail(f"G6 negative-control.sh 失败 rc={r.returncode}：\n{out[-1500:]}")
    log = (LOGS / "negative-control.log").read_text() if (LOGS / "negative-control.log").exists() else ""
    if "mismatches: ['ThomsonN9.thomson_nine']" not in log:
        fail(f"G6 negative-control.log 未检出恰 ThomsonN9.thomson_nine：\n{log[-800:]}")
    if "STATEMENT COMPARISON: FAILED" not in log:
        fail("G6 negative-control.log 缺 STATEMENT COMPARISON: FAILED")
    okmsg(f"G6 负对照 OK [{wall:.1f}s]：检出且仅检出 ThomsonN9.thomson_nine")
    return {"status": "OK", "detected": "ThomsonN9.thomson_nine",
            "wall_s": round(wall, 2)}


# ---------------------------------------------------------------- 账本核对（NC3 靶）
def verify_ledger(path: Path, facts: dict) -> list[str]:
    errs = []
    if not path.exists():
        return [f"账本不在档：{path}"]
    try:
        led = jload(path)
    except Exception as e:                                    # noqa: BLE001
        return [f"账本 JSON 解析失败：{e}"]
    pv = led.get("provenance", {})
    toolchain = (LEAN_DIR / "lean-toolchain").read_text().strip()
    if pv.get("lean_toolchain") != toolchain:
        errs.append(f"provenance.lean_toolchain={pv.get('lean_toolchain')!r} ≠ 现测 {toolchain!r}")
    lakefile = (LEAN_DIR / "lakefile.toml").read_text()
    m = re.search(r'^rev\s*=\s*"([0-9a-f]{40})"', lakefile, re.M)
    if not m:
        errs.append("lakefile.toml 无法解析 mathlib rev")
    elif pv.get("mathlib_rev") != m.group(1):
        errs.append(f"provenance.mathlib_rev={pv.get('mathlib_rev')!r} ≠ lakefile 现测 {m.group(1)}")
    sc = led.get("sorry_counts", {})
    if sc.get("challenge") != facts["g3"]["challenge_sorry"]:
        errs.append(f"sorry_counts.challenge={sc.get('challenge')!r} ≠ 现测 {facts['g3']['challenge_sorry']}")
    if sc.get("challenge_decl_lines") != facts["g3"]["challenge_decl_lines"]:
        errs.append(f"sorry_counts.challenge_decl_lines={sc.get('challenge_decl_lines')!r}"
                    f" ≠ 现测 {facts['g3']['challenge_decl_lines']}")
    if sc.get("solution") != facts["g3"]["solution_sorry"]:
        errs.append(f"sorry_counts.solution={sc.get('solution')!r} ≠ 现测 {facts['g3']['solution_sorry']}")
    ax = led.get("axioms", {})
    if ax.get("ThomsonN9.thomson_nine_M0") != facts["g4"]:
        errs.append(f"axioms['ThomsonN9.thomson_nine_M0']={ax.get('ThomsonN9.thomson_nine_M0')!r}"
                    f" ≠ 现测 {facts['g4']}")
    stc = led.get("statement_compare", {})
    for k, v in (("status", facts["g5"]["status"]),
                 ("compared", facts["g5"]["compared"]),
                 ("skipped_not_attempted", facts["g5"]["skipped_not_attempted"]),
                 ("sha256_compared_challenge_text", facts["g5"]["sha256_compared_challenge_text"])):
        if stc.get(k) != v:
            errs.append(f"statement_compare.{k}={stc.get(k)!r} ≠ 现测 {v!r}")
    nc = led.get("negative_control", {})
    if nc.get("status") != facts["g6"]["status"] or nc.get("detected") != facts["g6"]["detected"]:
        errs.append(f"negative_control={nc!r} ≠ 现测 {facts['g6']}")
    fg = led.get("frozen_guard", {})
    if fg.get("references_tree_sha256") != facts["ref_tree"]:
        errs.append(f"frozen_guard.references_tree_sha256={fg.get('references_tree_sha256')!r}"
                    f" ≠ 现测 {facts['ref_tree']}")
    wl = led.get("wallclock_seconds", {})
    if not isinstance(wl, dict) or not all(isinstance(v, (int, float)) for v in wl.values()):
        errs.append("wallclock_seconds 非数值字典（informational 字段亦须结构完整）")
    if led.get("heavySolves") != 0:
        errs.append(f"heavySolves={led.get('heavySolves')!r} ≠ 0")
    return errs


# ---------------------------------------------------------------- NC1/NC2/NC3
def run_nc1() -> None:
    base = Path("/tmp/r11_m0_nc1")
    base.mkdir(parents=True, exist_ok=True)
    orig = SOL.read_text()
    clean = base / "Solution_clean.lean"
    clean.write_text(orig)
    if token_scan(clean):
        fail("NC1 前置失败：未篡改 /tmp 副本已被正则命中（G2 应为 0）")
    tampered = orig.replace("end ThomsonN9",
                            "theorem nc1_probe : (0 : ℝ) ≤ 1 := by sorry\n\nend ThomsonN9", 1)
    if tampered == orig or "sorry" not in tampered:
        fail("NC1 前置失败：篡改未生效")
    tdoc = base / "Solution_tampered.lean"
    tdoc.write_text(tampered)
    hits = token_scan(tdoc)
    if not any("sorry" in h for h in hits):
        fail(f"NC1 未检出篡入的 sorry（正则命中：{hits[:3]}）")
    okmsg(f"NC1 /tmp 副本篡入 sorry ⇒ G2 正则检出 {len(hits)} 处 ✓（未篡副本 0 命中 sanity ✓）")


def run_nc2(workdir: Path, chal_tsv: Path, names: Path) -> None:
    base = Path("/tmp/r11_m0_nc2")
    if base.exists():
        shutil.rmtree(base)
    (base / "ThomsonN9").mkdir(parents=True)
    lines = SOL.read_text().splitlines()
    # 唯一锚：M0 定理声明行（命题行 36/2 在 show/calc 中另有出现，不作锚）
    needle = "(36 / 2 : ℝ) ≤ coulombEnergy x := by"
    idx = [k for k, ln in enumerate(lines) if needle in ln]
    if len(idx) != 1:
        fail(f"NC2 前置失败：命题声明行锚出现 {len(idx)} 次 ≠ 1")
    k = idx[0]
    tampered_line = lines[k].replace("(36 / 2 : ℝ)", "(37 / 2 : ℝ)")
    # 篡改后原证明体不再可证：/tmp 副本内以占位证明截断（token 扫描只针对真解件，
    # 本篡改件不经 G2；语句比对只比 elaborated 类型，占位不掩蔽篡改）
    tampered_lines = lines[:k] + [tampered_line, "  sorry", "", "end ThomsonN9", ""]
    (base / "ThomsonN9" / "Solution.lean").write_text("\n".join(tampered_lines))
    r = run(["lake", "env", "lean", f"--root={base}",
             "-o", str(base / "ThomsonN9" / "Solution.olean"),
             str(base / "ThomsonN9" / "Solution.lean")], cwd=LEAN_DIR)
    if r.returncode != 0:
        fail(f"NC2 篡改解件编译失败 rc={r.returncode}：\n{(r.stdout + r.stderr)[-1500:]}")
    script = base / "DumpT.lean"
    script.write_text("import ThomsonN9.Solution\n" +
                      DUMP_LEAN.read_text().replace("DUMPMOD", "ThomsonN9.Solution")
                      .replace("OUTFILE", str(base / "t.tsv")))
    lp = run(["lake", "env", "printenv", "LEAN_PATH"], cwd=LEAN_DIR)
    if lp.returncode != 0:
        fail("NC2 无法取得 LEAN_PATH")
    env = dict(os.environ)
    env["LEAN_PATH"] = f"{base}:{lp.stdout.strip()}"
    env["DUMP_ONLY"] = str(names)
    r = run(["lake", "env", "env", f"LEAN_PATH={env['LEAN_PATH']}", f"DUMP_ONLY={names}",
             "lean", str(script)], cwd=LEAN_DIR)
    if r.returncode != 0 or not (base / "t.tsv").exists():
        fail(f"NC2 篡改解件 dump 失败 rc={r.returncode}：\n{(r.stdout + r.stderr)[-1500:]}")
    r = run(["python3", str(CMP_PY), str(chal_tsv), str(base / "t.tsv")], cwd=LEAN_DIR)
    out = r.stdout
    if r.returncode == 0 or "STATEMENT COMPARISON: FAILED" not in out:
        fail(f"NC2 未检出命题行篡改（36/2→37/2 仍 OK）：\n{out[-800:]}")
    if "mismatches: ['ThomsonN9.thomson_nine_M0']" not in out:
        fail(f"NC2 检出面非恰 thomson_nine_M0：\n{out[-800:]}")
    okmsg("NC2 命题行 36/2→37/2 篡改 ⇒ 语句文本比对检出且仅检出"
          " ThomsonN9.thomson_nine_M0（STATEMENT COMPARISON: FAILED）✓")


def run_nc3(ledger_path: Path, facts: dict) -> None:
    base = Path("/tmp/r11_m0_nc3")
    base.mkdir(parents=True, exist_ok=True)
    if not ledger_path.exists():
        fail(f"NC3 前置失败：账本不在档 {ledger_path}")
    led = jload(ledger_path)
    tampered = json.loads(json.dumps(led))
    tampered.setdefault("sorry_counts", {})["challenge"] = 5
    tpath = base / "r11_m0_ledger_tampered.json"
    tpath.write_text(json.dumps(tampered, ensure_ascii=False, indent=2))
    errs = verify_ledger(tpath, facts)
    if not errs:
        fail("NC3 未检出篡账本（sorry_counts.challenge 4→5 仍通过核对）")
    if not any("sorry_counts.challenge" in e for e in errs):
        fail(f"NC3 失配面未点名 sorry_counts.challenge：{errs}")
    okmsg(f"NC3 /tmp 篡账本（sorry_counts.challenge 4→5）⇒ 账本核对失配并点名该字段 ✓"
          f"（{len(errs)} 处失配）")


# ---------------------------------------------------------------- 主流程
def main() -> None:
    ap = argparse.ArgumentParser(description="R11 M0 Lean 首证验收门")
    ap.add_argument("--ledger", default=str(LEDGER),
                    help="账本路径（默认 results/r11_m0_ledger.json；NC3 用 --ledger 指篡改副本"
                         "时仍以真账本口径核对新鲜事实）")
    args = ap.parse_args()
    ledger_path = Path(args.ledger).resolve()

    print(f"[gate] r11_m0_gate seed={SEED_GATE}（确定性检查，无随机路径）", flush=True)
    elan_bin = Path.home() / ".elan" / "bin"
    if elan_bin.is_dir():
        os.environ["PATH"] = f"{elan_bin}{os.pathsep}{os.environ.get('PATH', '')}"
    for tool in ("lake", "lean", "elan"):
        if shutil.which(tool) is None:
            fail(f"工具 {tool} 不可解析（PATH 已前置 {elan_bin}）——环境级缺失，FAIL 附信息")
    print(f"[gate][info] 工具解析：lake={shutil.which('lake')} lean={shutil.which('lean')} "
          f"elan={shutil.which('elan')}", flush=True)

    facts: dict = {}
    facts["ref_tree"] = references_tree_sha256()[0]
    check_g1(jload(ledger_path).get("frozen_guard", {}).get("references_tree_sha256")
             if ledger_path.exists() else None)
    check_g2()
    facts["g3"] = check_g3()
    facts["g4"] = check_g4()
    workdir = Path("/tmp/r11_m0_gate_work")
    if workdir.exists():
        shutil.rmtree(workdir)
    facts["g5"] = check_g5(workdir)
    facts["g6"] = check_g6(workdir)

    errs = verify_ledger(ledger_path, facts)
    if errs:
        for e in errs:
            print(f"[gate][FAIL] 账本失配：{e}", flush=True)
        fail(f"账本核对 {len(errs)} 处失配（{ledger_path}）")
    okmsg(f"账本核对全过：{ledger_path}")

    run_nc1()
    run_nc2(workdir, workdir / "Challenge.tsv", workdir / "Challenge.names")
    run_nc3(ledger_path, facts)
    print("[gate] 全门 PASS（G1–G6 ＋ 账本核对 ＋ NC1 ＋ NC2 ＋ NC3）", flush=True)


if __name__ == "__main__":
    main()
