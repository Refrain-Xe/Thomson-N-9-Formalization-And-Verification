#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r12_m1_gate.py — R12a M1 Lean 全链验收门（G1–G8 ＋ 负对照 NC1/NC2/NC3）.

任务书口径（r12a-m1-lean-e2e）：冻结挑战四定理第二件真证明——Solution.lean 在
逐字节复述冻结前缀（挑战件 26–149 行）＋既有 M0 证明之后给出 thomson_nine_M1
的真 Lean 内核证明（无任何内核旁路），其全部有理数据来自生成模块
ThomsonN9/M1Data.lean（源自数据件 results/m1_lean_data.json，只读消费冻结件
results/lp_m1_light.json）。本门对盘上状态逐项独立重放（不信任任何日志/账本；
全部确定性检查，无随机路径；seed 20261014 惯例记档）。PATH 自动前置
~/.elan/bin（缺失即 FAIL 附信息）。

检查面（对应任务书 G1–G8）：
  G1 冻结守卫：git diff HEAD 对 formal/lean/ComparatorChallenges/ThomsonN9.lean、
     formal/lean/lakefile.toml、formal/lean/lake-manifest.json、
     formal/lean/lean-toolchain、numerics/bounds/results/lp_m1_light.json、
     numerics/bounds/results/lp.json 全空；references/thomson-n7-lean（git 仓库）
     git diff HEAD 全空＋references/ 树哈希（排除 .git/.lake）与账本一致。
  G2 token 扫描：check.sh 步 2 同正则对 Solution.lean 与 M1Data.lean 零命中
     （sorry/native_decide/ofReduceBool/ofReduceNat/trustCompiler/axiom/opaque/
      unsafe/partial/set_option/implemented_by/extern/csimp/元编程/#eval/#exit 等）。
  G3 lake build ThomsonN9 ComparatorChallenges（先删两模块 olean 强制重 elaborate）：
     恰 4 条挑战 declaration-uses-sorry 警告、声明行号恰为 {158,166,172,179}；
     解件 0 条；M1Data 0 条；源码级挑战 stripped=='sorry' 行 == [160,168,175,183]、
     解件 == []、M1Data == []。
  G4 CheckAxioms（lake env lean scripts/CheckAxioms.lean）：输出含
     'ThomsonN9.thomson_nine_M1'，其公理集合恰为 {propext, Classical.choice,
     Quot.sound}，全输出无 sorryAx/ofReduceBool/ofReduceNat/trustCompiler。
  G5 语句保真（非 DEFERRED）：本门独立 dump 两模块 elaborated bodies
     （Challenge 全量、Solution 限 Challenge 常量名），跑 scripts/compare_statements.py：
     STATEMENT COMPARISON: OK、missing/bad 全空、compared==34（33＋M1 重声明；
     M0 期为 33）、skipped 打印名单==实现硬编码 SKIP 集（presence-only 名单，
     非实际未比对名单）、Solution dump 含 thomson_nine_M1 行（在场即比对，
     bad_type 空即逐字一致）。
  G6 负对照三面（沿 r11_m0_gate 先例）：
     NC1 /tmp 副本篡入一行 sorry ⇒ G2 正则必检出（未篡副本 0 命中 sanity）；
     NC2 /tmp 副本命题行 (189 / 8 : ℝ)→(189 / 4 : ℝ)（恰一处替换）⇒ 独立编译＋
       dump＋compare_statements.py 必检出且仅检出 ThomsonN9.thomson_nine_M1、FAILED；
     NC3 /tmp 篡账本（sorry_counts.challenge 4→5）⇒ 账本核对必失配并点名该字段。
  G7 数据独立复核（stdlib-only 第二实现，不 import 仓内任何代码；全部精确
     Fraction）：m1_lean_data.json 与冻结 lp_m1_light.json 的逐项精确重推导——
     Legendre→单项式（独立 Bonnet 递推）==json f.monomial_coeffs；k≥1 支集
     {1,2,3,7}；p 系数独立重算；Möbius P(u) 独立重算；Lukács SOS 恒等式
     ΣD0·z0²+u·ΣD1·z1²==P 逐系数精确、D0/D1 全正；逐 k∈{1,2,3,7}：H 调和
     （独立拉普拉斯）、dim=2k+1、Gram 独立球面矩公式==R、Rinv·R==I、
     LDLᵀ 重乘==R、S·L==I、球面恒等式 D6==(2k+1)P_k(x·y)−ΣRinv·h·h 独立
     系数展开、(‖x‖²−1)A+(‖y‖²−1)B==D6 独立展开；装配 B=(81ĉ₀−9f(1))/2
     独立重算==lp_m1_light.bound_exact 逐位、189/8<B≤E*+1e-6（E* 只读
     thomson-workflow/data/energies.json，十进制口径 Fraction）。
  G8 账本锚：results/r12_m1_ledger.json 受控字段（provenance/sorry_counts/
     axioms/statement_compare/files sha256/gate steps/heavySolves）与本门新鲜
     事实逐项比对（墙钟类字段仅查在场与类型，informational）。

用法（CWD 无关——全部路径自 __file__ 推导）：
  python3 numerics/bounds/r12_m1_gate.py              # 全门（exit 0 = 过）
  python3 numerics/bounds/r12_m1_gate.py --ledger P   # 对指定账本副本跑核对
                                                      #（NC3 用；仍重放 G3–G7）
  python3 numerics/bounds/r12_m1_gate.py --skip-build # 跳过 G3 build（调试用，
                                                      # 正式验收不可带）
"""
from __future__ import annotations

import argparse
import hashlib
import sys as _sys

_sys.set_int_max_str_digits(2_000_000)
import json
import math
import os
import re
import shutil
import subprocess
import sys
import time
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
REPO = HERE.parents[1]                 # thomson-n9/
CAMPAIGN_ROOT = REPO.parent            # 八电子在球面的分布/
LEAN_DIR = REPO / "formal" / "lean"
REFERENCES = CAMPAIGN_ROOT / "references"
REF_N7 = REFERENCES / "thomson-n7-lean"

SEED_GATE = 20261014                   # 惯例记档；本门无随机路径（确定性）

CHAL_REL = "ComparatorChallenges/ThomsonN9.lean"
SOL_REL = "ThomsonN9/Solution.lean"
M1DATA_REL = "ThomsonN9/M1Data.lean"
CHAL = LEAN_DIR / CHAL_REL
SOL = LEAN_DIR / SOL_REL
M1DATA = LEAN_DIR / M1DATA_REL
FROZEN_REPO_PATHS = [
    "formal/lean/ComparatorChallenges/ThomsonN9.lean",
    "formal/lean/lakefile.toml",
    "formal/lean/lake-manifest.json",
    "formal/lean/lean-toolchain",
    "numerics/bounds/results/lp_m1_light.json",
    "numerics/bounds/results/lp.json",
]
CHECK_SH = LEAN_DIR / "scripts" / "check.sh"
NC_SH = LEAN_DIR / "scripts" / "negative-control.sh"
CMP_PY = LEAN_DIR / "scripts" / "compare_statements.py"
DUMP_LEAN = LEAN_DIR / "scripts" / "DumpBody.lean"
CHECK_AXIOMS = LEAN_DIR / "scripts" / "CheckAxioms.lean"
LEDGER = RESULTS / "r12_m1_ledger.json"
M1_JSON = RESULTS / "m1_lean_data.json"
LP_LIGHT = RESULTS / "lp_m1_light.json"
ENERGIES = CAMPAIGN_ROOT / "thomson-workflow" / "data" / "energies.json"
LOGS = LEAN_DIR / "logs"

EXPECTED_CHAL_DECL_LINES = {158, 166, 172, 179}
EXPECTED_CHAL_SORRY_LINES = [160, 168, 175, 183]
# compare_statements.py 的 "skipped (not attempted)" 行打印的是其硬编码 SKIP 常量集
# （presence-only 豁免名单），非实际未比对名单——按实现报准（D49 口径：
# 凡重声明逐字比对，compared 计数按实现报准）。
EXPECTED_SKIPPED_PRINT = sorted(["ThomsonN9.thomson_nine_M1",
                                 "ThomsonN9.thomson_nine",
                                 "ThomsonN9.thomson_nine_unique"])
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN_AXIOMS = ["sorryAx", "ofReduceBool", "ofReduceNat", "trustCompiler"]
EXPECTED_COMPARED = 34                             # 33（M0 期）＋ thomson_nine_M1 重声明
KS = [1, 2, 3, 7]

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


def sha256_file(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def git_diff_names(repo: Path, paths=None):
    cmd = ["git", "-C", str(repo), "diff", "HEAD", "--name-only"]
    if paths:
        cmd += list(paths)
    r = run(cmd)
    if r.returncode != 0:
        fail(f"G1 git 调用失败（{repo}）：{r.stderr.strip()[:300]}")
    return [l for l in r.stdout.splitlines() if l.strip()]


def references_tree_sha256() -> tuple[str, int]:
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
    for p in (CHAL, LEAN_DIR / "lakefile.toml", LEAN_DIR / "lake-manifest.json",
              LEAN_DIR / "lean-toolchain", LP_LIGHT, RESULTS / "lp.json"):
        if not p.exists():
            fail(f"G1 冻结件不在档：{p}")
    dirty = git_diff_names(REPO, FROZEN_REPO_PATHS)
    if dirty:
        fail(f"G1 冻结守卫失守：git diff HEAD 检出改动 {dirty}")
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
    okmsg(f"G1 冻结守卫全空：六冻结件（含 lp_m1_light.json/lp.json）git diff HEAD 无改动；"
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
    for p in (SOL, M1DATA):
        if not p.exists():
            fail(f"G2 文件不在档：{p}")
        hits = token_scan(p)
        if hits:
            fail(f"G2 token 扫描命中 {len(hits)} 处（{p.name}）：{hits[:5]}")
    okmsg("G2 token 扫描 0 命中（Solution.lean＋M1Data.lean，check.sh 步 2 同正则）")


# ---------------------------------------------------------------- G3
def check_g3() -> dict:
    for p, expect in ((CHAL, EXPECTED_CHAL_SORRY_LINES), (SOL, []), (M1DATA, [])):
        if not p.exists():
            fail(f"G3 源文件不在档：{p}")
        lines = p.read_text().splitlines()
        got = [i + 1 for i, ln in enumerate(lines) if ln.strip() == "sorry"]
        if got != expect:
            fail(f"G3 源码级 sorry 行失配（{p.name}）：{got} ≠ 期望 {expect}")
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
    n_m1 = len(re.findall(r"ThomsonN9/M1Data\.lean.*sorry", out))
    if n_chal != 4 or set(chal_lines) != EXPECTED_CHAL_DECL_LINES:
        fail(f"G3 挑战 sorry 警告失配：计 {n_chal} 条、声明行 {chal_lines}"
             f" ≠ 期望 4 条 @{sorted(EXPECTED_CHAL_DECL_LINES)}")
    if n_sol != 0:
        fail(f"G3 解件 sorry 警告 {n_sol} 条 ≠ 0")
    if n_m1 != 0:
        fail(f"G3 M1Data sorry 警告 {n_m1} 条 ≠ 0")
    if "Build completed successfully" not in out:
        fail("G3 lake build 未报 Build completed successfully")
    okmsg(f"G3 lake build（强制重 elaborate，含 M1Data）成功 [{wall:.1f}s]：恰 4 挑战 sorry"
          f" @ 声明行 {chal_lines}＋0 解件＋0 M1Data；源码级 [160,168,175,183]/[]/[] 对上")
    return {"build_wall_s": round(wall, 2), "build_rc": r.returncode,
            "challenge_sorry": n_chal, "challenge_decl_lines": chal_lines,
            "solution_sorry": n_sol, "m1data_sorry": n_m1}


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
    m = re.search(r"'ThomsonN9\.thomson_nine_M1' depends on axioms: \[(.*?)\]", out)
    if not m:
        fail(f"G4 CheckAxioms 输出未找到 'ThomsonN9.thomson_nine_M1' 的公理行：\n{out[:800]}")
    axioms = sorted(a.strip() for a in m.group(1).split(",") if a.strip())
    if set(axioms) != ALLOWED_AXIOMS:
        fail(f"G4 thomson_nine_M1 公理集合 {axioms} ≠ 恰 {{propext, Classical.choice, Quot.sound}}")
    if "ThomsonN9.thomson_nine_M1 : ∀ x ∈ ThomsonN9.SphereConfig 9, 189 / 8 ≤" not in out:
        fail(f"G4 #check 命题形状异常：\n{out[:800]}")
    okmsg(f"G4 CheckAxioms：thomson_nine_M1 公理恰为 {axioms}，"
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
        fail(f"G5 compared={compared} ≠ {EXPECTED_COMPARED}（33＋M1 重声明）")
    if skipped != EXPECTED_SKIPPED_PRINT:
        fail(f"G5 skipped 打印名单={skipped} ≠ 实现口径 {EXPECTED_SKIPPED_PRINT}")
    # M1 必须在场且已比对（bad_type 空 ⟹ 逐字一致；compared 34>33 ⟹ M1 计入）
    if "ThomsonN9.thomson_nine_M1\ttheorem" not in sol_tsv.read_text():
        fail("G5 Solution dump 无 thomson_nine_M1 行（重声明缺席）")
    okmsg(f"G5 语句保真（非 DEFERRED）：compared={compared}（{ndefs} defs 带值；M1 重声明"
          f"在场且逐字比对无失配）、skipped 打印名单（实现口径）={skipped}")
    return {"status": "OK", "compared": compared, "defs_with_values": ndefs,
            "skipped_print": skipped,
            "sha256_compared_challenge_text": dg.group(1)}


# ---------------------------------------------------------------- G7（stdlib-only 独立复核）
def _trim(a: list[Fr]) -> list[Fr]:
    b = list(a)
    while b and b[-1] == 0:
        b.pop()
    return b


def _upoly_mul(a: list[Fr], b: list[Fr]) -> list[Fr]:
    r = [Fr(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return r


def _legendre_mono(k: int) -> list[Fr]:
    L = [[Fr(1)], [Fr(0), Fr(1)]]
    for n in range(1, k):
        nxt = [Fr(0)] * (n + 2)
        for j, a in enumerate(L[n]):
            nxt[j + 1] += Fr(2 * n + 1, n + 1) * a
        for j, a in enumerate(L[n - 1]):
            nxt[j] -= Fr(n, n + 1) * a
        L.append(nxt)
    return L[k]


def _tri_lap(h: dict) -> dict:
    out: dict = {}
    for (a, b, c), v in h.items():
        if a >= 2:
            out[(a - 2, b, c)] = out.get((a - 2, b, c), Fr(0)) + v * a * (a - 1)
        if b >= 2:
            out[(a, b - 2, c)] = out.get((a, b - 2, c), Fr(0)) + v * b * (b - 1)
        if c >= 2:
            out[(a, b, c - 2)] = out.get((a, b, c - 2), Fr(0)) + v * c * (c - 1)
    return {k: v for k, v in out.items() if v != 0}


def _sphere_moment(a: int, b: int, c: int) -> Fr:
    if a % 2 or b % 2 or c % 2:
        return Fr(0)
    p_, q_, r_ = a // 2, b // 2, c // 2
    n = p_ + q_ + r_
    return Fr(2 * math.factorial(a) * math.factorial(b) * math.factorial(c)
              * math.factorial(n + 1),
              math.factorial(p_) * math.factorial(q_) * math.factorial(r_)
              * math.factorial(2 * n + 2))


def _mat_mul(A, B):
    n, m, p = len(A), len(B), len(B[0])
    return [[sum(A[i][k] * B[k][j] for k in range(m)) for j in range(p)] for i in range(n)]


def check_g7() -> dict:
    if not M1_JSON.exists() or not LP_LIGHT.exists() or not ENERGIES.exists():
        fail(f"G7 输入不在档：{M1_JSON} / {LP_LIGHT} / {ENERGIES}")
    m1 = jload(M1_JSON)
    lp = jload(LP_LIGHT)
    F = lambda xs: [Fr(x) for x in xs]                       # noqa: E731
    checks: list[str] = []

    # (a) f：Legendre→单项式独立重推导＋支集＋P_k(1)=1
    cs = F(lp["certificate"]["coeffs_legendre_exact"])
    assert len(cs) == 9 and lp["certificate"]["degree"] == 8
    if [k for k in range(1, 9) if cs[k] != 0] != [1, 2, 3, 7]:
        fail("G7 k≥1 支集 ≠ {1,2,3,7}")
    for k in range(9):
        if sum(_legendre_mono(k)) != 1:
            fail(f"G7 P_{k}(1) ≠ 1（独立 Bonnet）")
    fm = [Fr(0)] * 9
    for k in range(9):
        for j, a in enumerate(_legendre_mono(k)):
            fm[j] += cs[k] * a
    if _trim(fm) != _trim(F(m1["f"]["monomial_coeffs"])):
        fail("G7 f 单项式展开独立重推导 ≠ json f.monomial_coeffs")
    f1 = sum(cs)
    if f1 != Fr(m1["f"]["f_of_1"]) or sum(fm) != f1:
        fail("G7 f(1) 重算失配")
    checks.append("f 单项式/f(1)/支集/P_k(1)=1")

    # p 与 Möbius P 独立重算
    f2 = _upoly_mul(_trim(fm), _trim(fm))
    pcoef = [Fr(1)] + [Fr(0)] * 15
    for i, x in enumerate(_upoly_mul([Fr(2), Fr(-2)], f2)):
        pcoef[i] -= x
    if _trim(pcoef) != _trim(F(m1["f"]["p_coeffs"])):
        fail("G7 p 系数独立重算 ≠ json f.p_coeffs")
    N = 15
    Pu = [Fr(0)] * (N + 1)
    for i, pi in enumerate(pcoef):
        if pi == 0:
            continue
        row = [Fr(1)]
        for _ in range(i):
            row = _upoly_mul(row, [Fr(1), Fr(-1)])
        for _ in range(N - i):
            row = _upoly_mul(row, [Fr(1), Fr(1)])
        for j, x in enumerate(row):
            Pu[j] += pi * x
    if _trim(Pu) != _trim(F(m1["pos_certificate"]["moebius_P_coeffs"])):
        fail("G7 Möbius P(u) 独立重算 ≠ json pos_certificate.moebius_P_coeffs")
    checks.append("p 与 Möbius P 独立重算")

    # Lukács SOS：恒等式 ΣD0·z0² + u·ΣD1·z1² == P 精确；D 全正
    pc = m1["pos_certificate"]
    L0 = [[Fr(x) for x in row] for row in pc["L0"]]
    D0 = F(pc["D0"])
    L1 = [[Fr(x) for x in row] for row in pc["L1"]]
    D1 = F(pc["D1"])
    n = len(D0)
    lhs = [Fr(0)] * 16
    for i in range(n):
        z0 = [L0[j][i] for j in range(n)]
        sq = _upoly_mul(z0, z0)
        for j, x in enumerate(sq):
            lhs[j] += D0[i] * x
    for i in range(n):
        z1 = [L1[j][i] for j in range(n)]
        sq = _upoly_mul(z1, z1)
        for j, x in enumerate(sq):
            if j + 1 < 16:
                lhs[j + 1] += D1[i] * x
    if _trim(lhs) != _trim(Pu):
        fail("G7 Lukács SOS 恒等式 ΣD0·z0²+u·ΣD1·z1² == P(u) 精确复核失配")
    if not all(d > 0 for d in D0) or not all(d > 0 for d in D1):
        fail("G7 SOS 权重 D0/D1 非全正")
    checks.append(f"SOS 恒等式精确＋D0/D1 全正（8×8 LDLᵀ 主元；min D0≈{float(min(D0)):.3e}"
                  f"，min D1≈{float(min(D1)):.3e}，精确值见 json pos_certificate.D0/D1）")

    # (c) 核机制逐 k
    for k in KS:
        kd = m1["kernels"][str(k)]
        nk = kd["dim"]
        if nk != 2 * k + 1:
            fail(f"G7 k={k} dim={nk} ≠ {2 * k + 1}")
        H = [{tuple(e): Fr(v) for e, v in hp} for hp in kd["H_polys"]]
        for h in H:
            if _tri_lap(h):
                fail(f"G7 k={k} 基元非调和（独立拉普拉斯）")
        # Gram 独立球面矩公式
        R = [[sum(v1 * v2 * _sphere_moment(k1[0] + k2[0], k1[1] + k2[1], k1[2] + k2[2])
              for k1, v1 in H[i].items() for k2, v2 in H[j].items())
             for j in range(nk)] for i in range(nk)]
        if [[Fr(x) for x in row] for row in kd["R"]] != R:
            fail(f"G7 k={k} Gram 独立公式 ≠ json R")
        Rinv = [[Fr(x) for x in row] for row in kd["Rinv"]]
        ident = [[Fr(1) if i == j else Fr(0) for j in range(nk)] for i in range(nk)]
        if _mat_mul(Rinv, R) != ident or _mat_mul(R, Rinv) != ident:
            fail(f"G7 k={k} Rinv·R ≠ I")
        Lm = [[Fr(x) for x in row] for row in kd["L"]]
        Dm = F(kd["D"])
        diag = [[Dm[i] if i == j else Fr(0) for j in range(nk)] for i in range(nk)]
        LT = [[Lm[j][i] for j in range(nk)] for i in range(nk)]
        if _mat_mul(_mat_mul(Lm, diag), LT) != R:
            fail(f"G7 k={k} LDLᵀ 重乘 ≠ R")
        if not all(d > 0 for d in Dm):
            fail(f"G7 k={k} LDLᵀ 主元非全正")
        Sm = [[Fr(x) for x in row] for row in kd["S_Linv"]]
        if _mat_mul(Sm, Lm) != ident:
            fail(f"G7 k={k} S·L ≠ I（S=L⁻¹ 复核）")
        # 球面恒等式：D6 独立展开 == (2k+1)P_k(x·y) − Σ Rinv h h
        def dotpow(m):
            base = [(1, 0, 0, 1, 0, 0), (0, 1, 0, 0, 1, 0), (0, 0, 1, 0, 0, 1)]
            Rr = {(0,) * 6: Fr(1)}
            for _ in range(m):
                nxt = {}
                for kk, vv in Rr.items():
                    for b in base:
                        key = tuple(kk[i] + b[i] for i in range(6))
                        nxt[key] = nxt.get(key, Fr(0)) + vv
                Rr = nxt
            return Rr
        def padd(A_, B_):
            Rr = dict(A_)
            for kk, vv in B_.items():
                Rr[kk] = Rr.get(kk, Fr(0)) + vv
            return {kk: vv for kk, vv in Rr.items() if vv != 0}
        def hmul(A_, B_):
            Rr = {}
            for k1, v1 in A_.items():
                for k2, v2 in B_.items():
                    kk = tuple(k1[i] + k2[i] for i in range(6))
                    Rr[kk] = Rr.get(kk, Fr(0)) + v1 * v2
            return {kk: vv for kk, vv in Rr.items() if vv != 0}
        D6: dict = {}
        Lk = _legendre_mono(k)
        for e in range(len(Lk)):
            if Lk[e] == 0:
                continue
            for kk, vv in dotpow(e).items():
                D6[kk] = D6.get(kk, Fr(0)) + vv * Lk[e] * Fr(2 * k + 1)
        for l in range(nk):
            for j in range(nk):
                if Rinv[l][j] == 0:
                    continue
                prod = hmul({(k1[0], k1[1], k1[2], 0, 0, 0): v for k1, v in H[l].items()},
                            {(0, 0, 0, k2[0], k2[1], k2[2]): v for k2, v in H[j].items()})
                D6 = padd(D6, {kk: -Rinv[l][j] * vv for kk, vv in prod.items()})
        D6 = {kk: vv for kk, vv in D6.items() if vv != 0}
        D6_json = {tuple(e): Fr(v) for e, v in kd["D_terms"]}
        if D6 != D6_json:
            fail(f"G7 k={k} 球面恒等式 D6 独立展开 ≠ json D_terms")
        # 理想证书：(‖x‖²−1)A + (‖y‖²−1)B == D6
        X = {(2, 0, 0, 0, 0, 0): Fr(1), (0, 2, 0, 0, 0, 0): Fr(1),
             (0, 0, 2, 0, 0, 0): Fr(1), (0, 0, 0, 0, 0, 0): Fr(-1)}
        Y = {(0, 0, 0, 2, 0, 0): Fr(1), (0, 0, 0, 0, 2, 0): Fr(1),
             (0, 0, 0, 0, 0, 2): Fr(1), (0, 0, 0, 0, 0, 0): Fr(-1)}
        A_ = {tuple(e): Fr(v) for e, v in kd["A_terms"]}
        B_ = {tuple(e): Fr(v) for e, v in kd["B_terms"]}
        if padd(hmul(X, A_), hmul(Y, B_)) != D6_json:
            fail(f"G7 k={k} (‖x‖²−1)A+(‖y‖²−1)B ≠ D6（独立展开）")
        checks.append(f"k={k}: 调和基 dim={nk}＋Gram/Rinv/LDLᵀ/S＋球面恒等式＋理想证书")

    # (d) 装配：B 重算 == lp bound_exact 逐位；189/8 < B ≤ E*+1e-6
    B = (Fr(81) * cs[0] - 9 * f1) / 2
    if B != Fr(lp["bound_exact"]):
        fail("G7 装配 B=(81ĉ₀−9f(1))/2 独立重算 ≠ lp_m1_light.bound_exact")
    if Fr(m1["assembly"]["B"]) != B or Fr(m1["assembly"]["f_of_1"]) != f1:
        fail("G7 json assembly.B/f_of_1 与独立重算失配")
    energies = jload(ENERGIES)
    E_star = Fr(str(energies["energies"]["9"]["value"]))
    if Fr("25.759986531") != E_star:
        fail("G7 energies.json energies/9/value ≠ Fraction('25.759986531')（十进制口径）")
    if not (Fr(189, 8) < B <= E_star + Fr(1, 10 ** 6)):
        fail("G7 189/8 < B ≤ E*+1e-6 失败")
    # 冻结件 sha256 与 json provenance 一致
    if m1["source_artifact"]["sha256"] != sha256_file(LP_LIGHT):
        fail("G7 m1_lean_data.json source_artifact.sha256 ≠ 现测 lp_m1_light.json")
    checks.append(f"装配 B==bound_exact 逐位＋189/8<B≤E*+1e-6（B={float(B):.9f}）＋lp sha256")

    okmsg("G7 数据独立复核（stdlib-only 第二实现，全部精确 Fraction）全过："
          + "；".join(checks))
    return {"status": "OK", "checks": checks,
            "B": str(B), "E_star": str(E_star),
            "lp_m1_light_sha256": sha256_file(LP_LIGHT)}


# ---------------------------------------------------------------- 账本核对（NC3 靶）
def verify_ledger(path: Path, facts: dict) -> list[str]:
    errs: list[str] = []
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
    if pv.get("gate") != "numerics/bounds/r12_m1_gate.py":
        errs.append("provenance.gate 路径失配")
    if pv.get("seed") != SEED_GATE:
        errs.append(f"provenance.seed={pv.get('seed')!r} ≠ {SEED_GATE}")
    sc = led.get("sorry_counts", {})
    if sc.get("challenge") != facts["g3"]["challenge_sorry"]:
        errs.append(f"sorry_counts.challenge={sc.get('challenge')!r} ≠ 现测 {facts['g3']['challenge_sorry']}")
    if sc.get("challenge_decl_lines") != facts["g3"]["challenge_decl_lines"]:
        errs.append(f"sorry_counts.challenge_decl_lines={sc.get('challenge_decl_lines')!r}"
                    f" ≠ 现测 {facts['g3']['challenge_decl_lines']}")
    if sc.get("solution") != facts["g3"]["solution_sorry"]:
        errs.append(f"sorry_counts.solution={sc.get('solution')!r} ≠ 现测 {facts['g3']['solution_sorry']}")
    if sc.get("m1data") != facts["g3"]["m1data_sorry"]:
        errs.append(f"sorry_counts.m1data={sc.get('m1data')!r} ≠ 现测 {facts['g3']['m1data_sorry']}")
    ax = led.get("axioms", {})
    if ax.get("ThomsonN9.thomson_nine_M1") != facts["g4"]:
        errs.append(f"axioms['ThomsonN9.thomson_nine_M1']={ax.get('ThomsonN9.thomson_nine_M1')!r}"
                    f" ≠ 现测 {facts['g4']}")
    stc = led.get("statement_compare", {})
    for k, v in (("status", facts["g5"]["status"]),
                 ("compared", facts["g5"]["compared"]),
                 ("skipped_print", facts["g5"]["skipped_print"]),
                 ("sha256_compared_challenge_text", facts["g5"]["sha256_compared_challenge_text"])):
        if stc.get(k) != v:
            errs.append(f"statement_compare.{k}={stc.get(k)!r} ≠ 现测 {v!r}")
    d7 = led.get("data_recheck", {})
    if d7.get("status") != facts["g7"]["status"] or d7.get("B") != facts["g7"]["B"]:
        errs.append(f"data_recheck={d7.get('status')!r}/{d7.get('B')!r}"
                    f" ≠ 现测 {facts['g7']['status']}/{facts['g7']['B']}")
    if d7.get("lp_m1_light_sha256") != facts["g7"]["lp_m1_light_sha256"]:
        errs.append("data_recheck.lp_m1_light_sha256 ≠ 现测")
    fg = led.get("frozen_guard", {})
    if fg.get("references_tree_sha256") != facts["ref_tree"]:
        errs.append(f"frozen_guard.references_tree_sha256={fg.get('references_tree_sha256')!r}"
                    f" ≠ 现测 {facts['ref_tree']}")
    fl = led.get("files", {})
    for rel, p in (("ThomsonN9/Solution.lean", SOL), ("ThomsonN9/M1Data.lean", M1DATA),
                   ("numerics/bounds/m1_lean_data.py", HERE / "m1_lean_data.py"),
                   ("numerics/bounds/results/m1_lean_data.json", M1_JSON),
                   ("numerics/bounds/r12_m1_gate.py", HERE / "r12_m1_gate.py")):
        if fl.get(rel) != sha256_file(p):
            errs.append(f"files[{rel!r}] sha256 ≠ 现测")
    nc = led.get("negative_control", {})
    if nc.get("status") != "ALL_DETECTED" or nc.get("nc1") != "detected" \
            or nc.get("nc2") != "detected:ThomsonN9.thomson_nine_M1" or nc.get("nc3") != "detected":
        errs.append(f"negative_control={nc!r} ≠ ALL_DETECTED 三面")
    wl = led.get("wallclock_seconds", {})
    if not isinstance(wl, dict) or not all(isinstance(v, (int, float)) for v in wl.values()):
        errs.append("wallclock_seconds 非数值字典（informational 字段亦须结构完整）")
    if led.get("heavySolves") != 0:
        errs.append(f"heavySolves={led.get('heavySolves')!r} ≠ 0")
    return errs


# ---------------------------------------------------------------- NC1/NC2/NC3
def run_nc1() -> None:
    base = Path("/tmp/r12_m1_nc1")
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
    base = Path("/tmp/r12_m1_nc2")
    if base.exists():
        shutil.rmtree(base)
    (base / "ThomsonN9").mkdir(parents=True)
    # 解件 import ThomsonN9.M1Data：/tmp 根需带 M1Data 的已构建 olean（真实件不动）
    libdir2 = LEAN_DIR / ".lake" / "build" / "lib" / "lean" / "ThomsonN9"
    for ext in ("M1Data.olean", "M1Data.ilean", "M1Data.olean.hash", "M1Data.ilean.hash"):
        src = libdir2 / ext
        if src.exists():
            shutil.copy2(src, base / "ThomsonN9" / ext)
    lines = SOL.read_text().splitlines()
    needle = "(189 / 8 : ℝ) ≤ coulombEnergy x := by"
    idx = [k for k, ln in enumerate(lines) if needle in ln]
    if len(idx) != 1:
        fail(f"NC2 前置失败：M1 命题声明行锚出现 {len(idx)} 次 ≠ 1")
    k = idx[0]
    tampered_line = lines[k].replace("(189 / 8 : ℝ)", "(189 / 4 : ℝ)")
    # 篡改后原证明体不再可证：/tmp 副本内以占位证明截断（token 扫描只针对真解件；
    # 语句比对只比 elaborated 类型，占位不掩蔽篡改）
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
    lp_ = run(["lake", "env", "printenv", "LEAN_PATH"], cwd=LEAN_DIR)
    if lp_.returncode != 0:
        fail("NC2 无法取得 LEAN_PATH")
    env = dict(os.environ)
    env["LEAN_PATH"] = f"{base}:{lp_.stdout.strip()}"
    env["DUMP_ONLY"] = str(names)
    r = run(["lake", "env", "env", f"LEAN_PATH={env['LEAN_PATH']}", f"DUMP_ONLY={names}",
             "lean", str(script)], cwd=LEAN_DIR)
    if r.returncode != 0 or not (base / "t.tsv").exists():
        fail(f"NC2 篡改解件 dump 失败 rc={r.returncode}：\n{(r.stdout + r.stderr)[-1500:]}")
    r = run(["python3", str(CMP_PY), str(chal_tsv), str(base / "t.tsv")], cwd=LEAN_DIR)
    out = r.stdout
    if r.returncode == 0 or "STATEMENT COMPARISON: FAILED" not in out:
        fail(f"NC2 未检出命题行篡改（189/8→189/4 仍 OK）：\n{out[-800:]}")
    if "mismatches: ['ThomsonN9.thomson_nine_M1']" not in out:
        fail(f"NC2 检出面非恰 thomson_nine_M1：\n{out[-800:]}")
    okmsg("NC2 命题行 189/8→189/4 篡改 ⇒ 语句文本比对检出且仅检出"
          " ThomsonN9.thomson_nine_M1、FAILED ✓")


def run_nc3(workdir: Path, facts: dict) -> None:
    base = Path("/tmp/r12_m1_nc3")
    base.mkdir(parents=True, exist_ok=True)
    if not LEDGER.exists():
        fail(f"NC3 前置失败：账本不在档 {LEDGER}")
    led = jload(LEDGER)
    if led.get("sorry_counts", {}).get("challenge") != 4:
        fail("NC3 前置失败：账本 sorry_counts.challenge ≠ 4（无篡改面）")
    led["sorry_counts"]["challenge"] = 5
    tampered = base / "r12_m1_ledger_tampered.json"
    tampered.write_text(json.dumps(led, ensure_ascii=False, indent=1))
    errs = verify_ledger(tampered, facts)
    if not any("sorry_counts.challenge" in e for e in errs):
        fail(f"NC3 未检出篡账本（verify_ledger 报错面：{errs[:4]}）")
    # 未篡副本 sanity
    errs_clean = verify_ledger(LEDGER, facts)
    if errs_clean:
        fail(f"NC3 sanity：未篡账本 verify_ledger 已有失配 {errs_clean[:4]}")
    okmsg("NC3 /tmp 篡账本（sorry_counts.challenge 4→5）⇒ 账本核对必失配并点名"
          " sorry_counts.challenge ✓（未篡副本 sanity ✓）")


# ---------------------------------------------------------------- main
def main() -> None:
    ap = argparse.ArgumentParser(description="R12a M1 Lean 全链验收门")
    ap.add_argument("--ledger", type=Path, default=None,
                    help="对指定账本副本跑核对（NC3 用；仍重放 G3–G7）")
    ap.add_argument("--skip-build", action="store_true",
                    help="跳过 G3 build（调试用；正式验收不可带）")
    args = ap.parse_args()

    t_start = time.time()
    elan = Path.home() / ".elan" / "bin"
    if elan.is_dir():
        os.environ["PATH"] = f"{elan}:{os.environ.get('PATH', '')}"
    if run(["which", "lake"]).returncode != 0:
        fail("lake 不在 PATH（~/.elan/bin 前置后仍不可用）")

    ledger_path = args.ledger if args.ledger is not None else LEDGER
    ref_tree_expected = None
    if ledger_path.exists():
        try:
            ref_tree_expected = jload(ledger_path).get("frozen_guard", {}).get(
                "references_tree_sha256")
        except Exception:                                      # noqa: BLE001
            ref_tree_expected = None

    print(f"[gate] r12_m1_gate（seed {SEED_GATE}，CWD 无关）——开始")
    ref_tree = check_g1(ref_tree_expected)
    check_g2()
    facts: dict = {"ref_tree": ref_tree}
    if args.skip_build:
        print("[gate][warn] --skip-build：G3 跳过（调试模式，不作为验收口径）")
        facts["g3"] = {"build_wall_s": -1.0, "build_rc": 0, "challenge_sorry": 4,
                       "challenge_decl_lines": sorted(EXPECTED_CHAL_DECL_LINES),
                       "solution_sorry": 0, "m1data_sorry": 0}
    else:
        facts["g3"] = check_g3()
    facts["g4"] = check_g4()
    workdir = Path("/tmp/r12_m1_gate_work")
    if workdir.exists():
        shutil.rmtree(workdir)
    facts["g5"] = check_g5(workdir)
    facts["g7"] = check_g7()

    # 负对照（在新鲜事实齐备后）
    run_nc1()
    run_nc2(workdir, workdir / "Challenge.tsv", workdir / "Challenge.names")
    run_nc3(workdir, facts)

    # 账本核对（G8）
    errs = verify_ledger(ledger_path, facts)
    if errs:
        print("[gate][FAIL] G8 账本核对失配：")
        for e in errs:
            print(f"        - {e}")
        sys.exit(1)
    wall = time.time() - t_start
    okmsg(f"G8 账本锚：{ledger_path} 受控字段与新鲜事实全对上")
    print(f"[gate] PASS（{wall:.1f}s）——exit 0")
    print("      挑战件 4 sorry（M1 已证）＋解件/M1Data 0 sorry；"
          "thomson_nine_M1 公理恰三标准；语句比对 OK compared=34；"
          "G7 stdlib-only 数据独立复核全过；NC1/NC2/NC3 三面有牙；heavySolves=0")
    sys.exit(0)


if __name__ == "__main__":
    main()
