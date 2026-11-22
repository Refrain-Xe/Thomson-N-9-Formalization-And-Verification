#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r15_b6_data.py — R15A 表 B 第二件 B6（拼接端点/记录锚件）数据发射器
（D61 裁决 2；heavySolves=0，零求解零 SDP 零新数值证书）.

任务书口径（r15a-tableb-b6）：endgame.json 的分区常数已是精确 Fraction
（无 dyadic 舍入面），本发射器以 stdlib Fraction 只读消费
results/endgame.json（partition 12 分区 regions/bounds/coverPiece＋E_star＋
assembledRecord＋citedCertificates 12 份 cert 的 claimed_bound），独立第二
实现重导端点链/分区 bound/记录/铁律/分片语义，发射
formal/lean/ThomsonN9/TableB6Data.lean（仅 import Mathlib；13 端点＋12
bound＋E*/AR/epsIron ℚ 字面量 def＋norm_num1 逐件定理）并回读自检逐位对账。
主件 TableB6.lean（12 分区无缝覆盖 Nat.find 真证明＋记录装配口径①＋铁律
ε 版＋分片语义聚合）为手写件，不含数据值字面量（数值篡改面全落 Data 件），
由验收门 r15_b6_gate.py G2/G3/G4 验证——本发射器只对其在场性与 import 面
做弱检查。

数学层（四件，与 endgame_chain.py 的记录对账但不 import 它——独立第二实现）：
  (i) 12 分区端点链：13 端点 e₀=−1 ≤ e₁=−99/100 ≤ … ≤ e₁₂=1 逐对单调
      （Data 件 12 条 norm_num1）＋相邻区域无缝（region[i].hi==region[i+1].lo
      逐位）——Lean 侧覆盖定理见主件 partition_cover_q/partition_cover。
  (ii) 记录装配：AR==min(12 分区 bound)——Data 件 12 大分数（最大 171 字符
      ≈570-bit）逐件 AR≤bᵢ norm_num1＋HP 片（指标 10，[−153/200,−187/250]）
      b₁₀==AR 字面等；min 陈述取口径①（∀ i:Fin 12, AR ≤ bnds i ∧
      bnds 10 == AR——零 API 风险；口径② Finset.min' 的 elaboration 残余
      细目录 D61-2），见主件 record_is_min。
  (iii) 铁律：AR ≤ E*（E*=25759986531/10^9 ℚ 字面量；比铁律 AR≤E*+1e-6
      更强且真——margin 0.0005405579025207914>0，另发 margin_pos 严格版）。
  (iv) 分片语义算术层：10 排除片（coverPiece==exclusion）bound>E*＋
      2 片 TTP-covering（HP 片＋cap 片 [−187/250,1]）bound≤E*+1e-6 逐片
      铁律（Data 件 excl0..9_gt／cover10/11_le_iron）。

抽查（seed 20261017，A5/A6/B5 家法）：3 个随机有理点 x∈[−1,1]（2⁻²⁰ 网格，
x=i/2²⁰，i=rng.randint(−2²⁰,2²⁰)），最小命中指数法（j=min{x≤e_j} 的最小 j，
片 i=j−1〔j=0 时 i=0〕）定位所在分区片，期望区间由发射器 Fraction 重算、
门内独立第二实现复放（定理 cover_spot0..2）。

诚实边界（docstring 双侧声明）：『区域 i 上 E≥b_i』的证书语义＝数值层职责
（typed_ladder/hermite/hp 各证书 verifyCmd——endgame.json citedCertificates
所列）不在本件；本件只证算术层（覆盖/min/铁律/分片语义）。

用法（CWD 无关）：
  python3 numerics/bounds/r15_b6_data.py
产出：
  formal/lean/ThomsonN9/TableB6Data.lean（确定性发射；重跑字节一致）
  numerics/bounds/results/r15_b6_data.json
"""
from __future__ import annotations

import hashlib
import json
import random
import subprocess
import time
from datetime import datetime, timezone
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
REPO = HERE.parents[1]                       # thomson-n9/

EG_JSON = RESULTS / "endgame.json"
OUT_JSON = RESULTS / "r15_b6_data.json"
DATA_LEAN = REPO / "formal" / "lean" / "ThomsonN9" / "TableB6Data.lean"
MAIN_LEAN = REPO / "formal" / "lean" / "ThomsonN9" / "TableB6.lean"

SEED = 20261017                             # R15 各件统一 seed（D61 任务书）
XGRID = 1 << 20                             # 抽查 x 网格 2⁻²⁰（[−1,1] 共 2²¹⁺¹ 格）
N_REGIONS = 12                              # 分区片数（端点 13）
IRON_EPS = Fr(1, 10**6)                     # 铁律 ε=1e-6（=Data 件 epsIron）

# endgame.json 不变锚（R14 轮终态冻结面；本发射器只读消费，sha 变化即 FAIL）
EG_SHA256 = "86863a09bf84e950e85fc5f902bc2b4046a87f06703bd782e5148fc119afd69f"

F0, F1 = Fr(0), Fr(1)


def log(msg: str) -> None:
    print(f"[r15b6] {msg}", flush=True)


def code_version() -> str:
    r = subprocess.run(["git", "rev-parse", "--short", "HEAD"],
                       cwd=str(REPO), capture_output=True, text=True)
    if r.returncode != 0:
        return "unknown"
    return r.stdout.strip() + ("-dirty" if subprocess.run(
        ["git", "diff", "--quiet"], cwd=str(REPO)).returncode != 0 else "")


def fs(f: Fr) -> str:
    return f"{f.numerator}/{f.denominator}"


def sha256_of(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def fail(msg: str) -> None:
    raise SystemExit(f"[r15b6][FAIL] {msg}")


# ============================================================ 重导层
def rederive():
    """独立第二实现：只读解析 endgame.json，Fraction 重导并全量复验四件。"""
    eg = json.loads(EG_JSON.read_text())

    # ---- 分区：12 regions → 13 端点链＋12 bound＋coverPiece 语义
    regions = eg["partition"]
    if len(regions) != N_REGIONS:
        fail(f"partition 分区数失配：{len(regions)} != {N_REGIONS}")
    chain, bounds, pieces = [], [], []
    for r in regions:
        lo_s, hi_s = r["region"].strip("[]").split(",")
        lo, hi = Fr(lo_s.strip()), Fr(hi_s.strip())
        chain.append(lo) if not chain else None
        if chain[-1] != lo:
            fail(f"端点链无缝失守：region 下端 {lo} ≠ 前区上端 {chain[-1]}")
        chain.append(hi)
        bounds.append(Fr(r["bound"]))
        cp = r["coverPiece"]
        if cp.startswith("exclusion"):
            pieces.append("exclusion")
        elif cp.startswith("TTP-covering"):
            pieces.append("covering")
        else:
            fail(f"coverPiece 无法归类：{cp!r}")
    if len(chain) != N_REGIONS + 1:
        fail(f"端点数失配：{len(chain)} != {N_REGIONS + 1}")

    # (i) 链单调＋端点锚
    if chain[0] != -F1 or chain[N_REGIONS] != F1:
        fail(f"端点锚失守：e0={chain[0]}（应 −1）、e12={chain[12]}（应 1）")
    for k in range(N_REGIONS):
        if not chain[k] <= chain[k + 1]:
            fail(f"端点链单调失守：e{k}={chain[k]} > e{k+1}={chain[k+1]}")

    # ---- E*/AR（Fraction 直读）
    estar = Fr(eg["E_star"]["value"])
    if float(estar) != eg["E_star"]["float"]:
        fail("E* 字面量与 float 记录失配")
    a_r = Fr(eg["assembledRecord"]["value"])

    # (ii) 记录装配：AR==min(12 bound)＋逐件 AR≤bᵢ＋HP 片（指标 10）字面等
    for i, b in enumerate(bounds):
        if not a_r <= b:
            fail(f"记录装配失守：AR ≤ b{i} 不成立（{a_r} ≰ {b}）")
    if a_r != min(bounds):
        fail("记录装配失守：AR ≠ min(12 分区 bound)")
    if bounds[10] != a_r:
        fail("HP 片失守：b10 ≠ AR（字面等）")
    if "HP" not in regions[10]["piece"]:
        fail("指标 10 非 HP 片（endgame 分区语义变动）")

    # (iii) 铁律：AR ≤ E*（更强版）＋margin>0＋ε 版
    if not a_r <= estar:
        fail("铁律失守：AR ≤ E* 不成立")
    margin = estar - a_r
    if not margin > 0:
        fail("margin 失守：AR < E* 不成立（margin ≤ 0）")
    if float(margin) != eg["assembledRecord"]["margin_vs_E_star"]:
        fail("margin 与 endgame.json 记录失配（float 口径）")
    if not a_r <= estar + IRON_EPS:
        fail("铁律 ε 版失守：AR ≤ E*+1e-6 不成立")

    # (iv) 分片语义：10 排除片 bound>E*＋2 片 TTP-covering bound≤E*+1e-6
    n_excl = sum(1 for p in pieces if p == "exclusion")
    if n_excl != 10 or pieces.count("covering") != 2:
        fail(f"分片语义计数失守：exclusion={n_excl}、covering={pieces.count('covering')}"
             f"（应 10/2）")
    for i, (p, b) in enumerate(zip(pieces, bounds)):
        if p == "exclusion" and not estar < b:
            fail(f"排除片铁律失守：b{i} ≤ E*（coverPiece=exclusion 须 >E*）")
        if p == "covering" and not b <= estar + IRON_EPS:
            fail(f"TTP-covering 片铁律失守：b{i} > E*+1e-6")
    if pieces[10] != "covering" or pieces[11] != "covering":
        fail("TTP-covering 片非指标 {10,11}（endgame 分区语义变动）")

    # ---- citedCertificates 12 份：claimed_bound 与分区 bound 一一对应对账
    certs = eg["citedCertificates"]
    if len(certs) != N_REGIONS:
        fail(f"citedCertificates 数失配：{len(certs)} != {N_REGIONS}")
    cert_bounds = [Fr(c["claimed_bound"]) for c in certs]
    if len(set(cert_bounds)) != N_REGIONS:
        fail("citedCertificates claimed_bound 非两两互异（值对账不可一一）")
    for i, b in enumerate(bounds):
        if b not in cert_bounds:
            fail(f"分区 bound b{i} 无对应证书（claimed_bound 一一对账失败）")
    if set(cert_bounds) != set(bounds):
        fail("citedCertificates 与分区 bound 值集失配")

    return dict(eg=eg, chain=chain, bounds=bounds, pieces=pieces,
                estar=estar, a_r=a_r, margin=margin, cert_bounds=cert_bounds)


# ============================================================ 抽查点
def spot_points(chain):
    """seed 20261017 固定抽样：3 个 x∈[−1,1]（2⁻²⁰ 网格），最小命中指数法
    定位所在片（j=min{j: x≤e_j}；片 i=j−1，j=0 时 i=0——与主件 Nat.find 覆盖
    机器同规则）。

    顺序（复现关键）：k=0,1,2 依次 i=rng.randint(−2²⁰,2²⁰)、x=i/2²⁰。
    """
    rng = random.Random(SEED)
    pts = []
    for _ in range(3):
        i = rng.randint(-XGRID, XGRID)
        x = Fr(i, XGRID)
        if not chain[0] <= x <= chain[-1]:
            fail(f"抽查 x 越界：{x}")
        j = next(jj for jj in range(len(chain)) if x <= chain[jj])
        iv = j - 1 if j >= 1 else 0
        if not chain[iv] <= x <= chain[iv + 1]:
            fail(f"抽查定位失守：片 {iv} 不含 x={x}")
        pts.append((x, iv))
    return pts


# ============================================================ Lean 发射
def render(f: Fr) -> str:
    return f"({fs(f)}:ℚ)"


def emit_data_lean_text(W, spots) -> str:
    chain, bounds, pieces = W["chain"], W["bounds"], W["pieces"]
    estar, a_r = W["estar"], W["a_r"]

    def d(name: str, val: Fr, doc: str) -> str:
        return f"/-- {doc} -/\ndef {name} : ℚ := {fs(val)}\n"

    def nn1(name: str, stmt: str, shown: str, doc: str) -> str:
        return (f"/-- {doc} -/\ntheorem {name} : {stmt} := by\n"
                f"  show {shown}\n  norm_num1\n")

    L = []
    L.append("import Mathlib")
    L.append("/-!")
    L.append("# Table B6 data (R15 / r15a): the splice endpoints and record")
    L.append("# anchors of the 12-piece endgame partition")
    L.append("")
    L.append("This module is deliberately self-contained: it imports only `Mathlib`,")
    L.append("imports no in-repo solution module, and is imported only by")
    L.append("`ThomsonN9/TableB6.lean`.  It materialises, as explicit `ℚ` literals,")
    L.append("the arithmetic layer of the endgame splice record")
    L.append("(`numerics/bounds/results/endgame.json`, read-only, re-derived here")
    L.append("through the independent second implementation of")
    L.append("`numerics/bounds/r15_b6_data.py`: stdlib-Fraction parsing of the")
    L.append("12 partition regions (13 endpoints, 12 bounds, coverPiece semantics),")
    L.append("the reference energy E* and the assembled record; provenance = sha256")
    L.append("of endgame.json, recorded in `results/r15_b6_data.json` — the partition")
    L.append("constants are exact Fractions, so there is no dyadic rounding surface")
    L.append("here):")
    L.append("")
    L.append("* `e0` … `e12` — the 13 splice endpoints, a seamless chain")
    L.append("  −1 = e0 ≤ e1 ≤ … ≤ e12 = 1 (12 pairwise `norm_num1` theorems;")
    L.append("  adjacent regions share endpoints bit for bit);")
    L.append("* `b0` … `b11` — the 12 recorded piece bounds, each equal bit for bit")
    L.append("  to the `claimed_bound` of its cited certificate (12/12 bijective")
    L.append("  value reconciliation against `citedCertificates`);")
    L.append("* `estar` — the reference energy E* = 25759986531/10^9 (three-source")
    L.append("  cross-checked advisory value of `thomson-workflow/data/energies.json`,")
    L.append("  NOT a proven optimum; all ≤/> statements below mean «consistent with")
    L.append("  the reference value»);")
    L.append("* `aR` — the assembled record min(12 piece bounds), attained literally")
    L.append("  by the HP piece b10 (the hole interval [−153/200, −187/250]);")
    L.append("* `epsIron` — the iron-rule slack 1e-6.")
    L.append("")
    L.append("Proved here (`show`-unfolding + `norm_num1`; `decide` on large ℚ")
    L.append("comparisons does not reduce — v1 lesson, D61-2): the 12 pairwise chain")
    L.append("inequalities; the 12 record bounds `aR ≤ bᵢ` (up to 570-bit Fractions);")
    L.append("the literal identity `b10 = aR`; the iron rule `aR ≤ estar` together")
    L.append("with its strict form `aR < estar` (margin 0.00054… > 0); the piece")
    L.append("semantics — the 10 exclusion pieces obey `estar < bᵢ`, the two")
    L.append("TTP-covering pieces (HP index 10, cap index 11 on [−187/250, 1]) obey")
    L.append("`bᵢ ≤ estar + epsIron`; and three seeded random spot checks of the")
    L.append("minimal-index covering machine (seed 20261017, x on the 2⁻²⁰ grid).")
    L.append("")
    L.append("Honest scope note (B6 arithmetic-layer boundary): the certificate")
    L.append("semantics «on region i the energy E ≥ b_i» (the verifyCmd layer of")
    L.append("typed_ladder / hermite / hp / strips / slab certificates listed in")
    L.append("`citedCertificates`) is NOT part of this file — that is the numeric")
    L.append("layer's responsibility; this file proves the arithmetic layer only")
    L.append("(covering / record-min / iron rule / piece semantics), and")
    L.append("`TableB6.lean` builds the genuine covering proof on top.")
    L.append("-/")
    L.append("")
    L.append("set_option maxHeartbeats 1000000")
    L.append("set_option linter.unusedVariables false")
    L.append("")
    L.append("namespace ThomsonN9.TableB6Data")
    L.append("")
    for k in range(13):
        L.append(d(f"e{k}", chain[k],
                   f"分区端点 e{k}（endgame.json partition 第 {max(k,1)} 区"
                   f"{'下' if k == 0 else '上'}端；e0=−1、e12=1，链单调无缝）。"))
    for i in range(12):
        L.append(d(f"b{i}", bounds[i],
                   f"分区片 {i} bound（== citedCertificates claimed_bound 逐位；"
                   f"pieces[{i}]={'exclusion 排除片' if pieces[i]=='exclusion' else 'TTP-covering 片'}）。"))
    L.append(d("estar", estar, "参考能量 E*（三源校验参考值，非已证最优；"
                               "全部 ≤/> 断言语义为与参考值不矛盾）。"))
    L.append(d("aR", a_r, "assembledRecord = min(12 分区 bound)（证书口径；"
                          "HP 片 b10 字面相等）。"))
    L.append(d("epsIron", IRON_EPS, "铁律容差 ε=1e-6（所有下界 ≤ E*+ε 口径）。"))
    L.append("")
    # ---- (i) 端点链
    L.append("/-- 端点锚：e0 字面 == −1/1。 -/\ntheorem e0_val : e0 = -1/1 := rfl")
    L.append("/-- 端点锚：e12 字面 == 1/1。 -/\ntheorem e12_val : e12 = 1/1 := rfl")
    for k in range(12):
        L.append(nn1(f"e{k}_le_e{k+1}", f"e{k} ≤ e{k+1}",
                     f"({fs(chain[k])}:ℚ) ≤ ({fs(chain[k+1])}:ℚ)",
                     f"端点链单调第 {k} 对：e{k} ≤ e{k+1}。"))
    # ---- (ii) 记录装配
    for i in range(12):
        L.append(nn1(f"ar_le_b{i}", f"aR ≤ b{i}",
                     f"{render(a_r)} ≤ ({fs(bounds[i])}:ℚ)",
                     f"记录装配第 {i} 件：AR ≤ b{i}"
                     f"（{len(fs(bounds[i]))} 字符大分数 norm_num1）。"))
    L.append(nn1("b10_eq_ar", "b10 = aR", f"({fs(bounds[10])}:ℚ) = {render(a_r)}",
                 "HP 片（指标 10，[−153/200,−187/250]）bound 字面 == AR"
                 "（记录在 HP 片取到）。"))
    # ---- (iii) 铁律
    L.append(nn1("iron_rule", "aR ≤ estar", f"{render(a_r)} ≤ ({fs(estar)}:ℚ)",
                 "铁律（更强版）：AR ≤ E*（比 AR ≤ E*+1e-6 强且真，"
                 "margin 0.0005405579025207914 > 0）。"))
    L.append(nn1("margin_pos", "aR < estar", f"{render(a_r)} < ({fs(estar)}:ℚ)",
                 "铁律严格版：AR < E*（margin 为正）。"))
    L.append(nn1("epsIron_pos", "(0:ℚ) < epsIron", "(0:ℚ) < 1/1000000",
                 "铁律容差为正（ε 版铁律的 linarith 前提）。"))
    # ---- (iv) 分片语义
    for i in range(12):
        if pieces[i] == "exclusion":
            L.append(nn1(f"excl{i}_gt", f"estar < b{i}",
                         f"({fs(estar)}:ℚ) < ({fs(bounds[i])}:ℚ)",
                         f"排除片 {i} 铁律：E* < b{i}（coverPiece=exclusion，"
                         f"区域不含 TTP 须 > E*）。"))
        else:
            L.append(nn1(f"cover{i}_le_iron", f"b{i} ≤ estar + epsIron",
                         f"({fs(bounds[i])}:ℚ) ≤ ({fs(estar)}:ℚ) + 1/1000000",
                         f"TTP-covering 片 {i} 铁律：b{i} ≤ E*+ε（证书域含 TTP，"
                         f"须 ≤ E*+1e-6）。"))
    # ---- 抽查（3 点）
    for k, (x, iv) in enumerate(spots):
        L.append(f"/-- 抽查 {k}（seed 20261017，最小命中指数法）：x 落入片 {iv} -/")
        L.append(f"theorem cover_spot{k} : e{iv} ≤ {render(x)} ∧ {render(x)} ≤ e{iv+1} := by")
        L.append("  refine ⟨?_, ?_⟩")
        L.append(f"  · show ({fs(chain[iv])}:ℚ) ≤ ({fs(x)}:ℚ)")
        L.append("    norm_num1")
        L.append(f"  · show ({fs(x)}:ℚ) ≤ ({fs(chain[iv+1])}:ℚ)")
        L.append("    norm_num1")
    L.append("")
    L.append("end ThomsonN9.TableB6Data")
    return "\n".join(L) + "\n"


# ============================================================ 回读自检
def reparse_defs(src: str) -> dict:
    import re
    out = {}
    for m in re.finditer(r"^def (\w+) : ℚ := (-?\d+/\d+)$", src, re.M):
        out[m.group(1)] = Fr(m.group(2))
    return out


def selfcheck(W, spots, parsed):
    chain, bounds = W["chain"], W["bounds"]
    want = {f"e{k}": chain[k] for k in range(13)}
    want.update({f"b{i}": bounds[i] for i in range(12)})
    want.update({"estar": W["estar"], "aR": W["a_r"], "epsIron": IRON_EPS})
    for k, v in want.items():
        if parsed.get(k) != v:
            fail(f"回读自检失配：def {k} 源码字面量 ≠ 重导值")
    import re
    for k, (x, iv) in enumerate(spots):
        m = re.search(rf"theorem cover_spot{k} : e(\d+) ≤ \((-?\d+/\d+):ℚ\) "
                      rf"∧ \((-?\d+/\d+):ℚ\) ≤ e(\d+) :=",
                      DATA_LEAN.read_text(), re.M)
        if not m:
            fail(f"回读自检失配：cover_spot{k} 形状解析失败")
        i_lo, x_lo, x_hi, i_hi = (int(m.group(1)), Fr(m.group(2)),
                                  Fr(m.group(3)), int(m.group(4)))
        if x_lo != x or x_hi != x:
            fail(f"回读自检失配：cover_spot{k} x 字面量 ≠ 抽样点")
        if i_lo != iv or i_hi != iv + 1:
            fail(f"回读自检失配：cover_spot{k} 片索引 {i_lo}/{i_hi} ≠ {iv}/{iv+1}")
        if not chain[i_lo] <= x <= chain[i_hi]:
            fail(f"回读自检失守：cover_spot{k} 区间不含 x")
    return len(want)


# ============================================================ 主流程
def main() -> None:
    t0 = time.time()
    if sha256_of(EG_JSON) != EG_SHA256:
        fail(f"endgame.json sha256 失配（不变锚 {EG_SHA256[:8]}…{EG_SHA256[-3:]}）"
             f"——冻结面被动，须先复核再重锚")
    W = rederive()
    log(f"[derive] endgame.json sha256=={EG_SHA256[:8]}…{EG_SHA256[-3:]} 不变锚 ✓；"
        f"13 端点链单调无缝（e0=−1、e12=1）＋AR==min(12 bound)（HP 片 b10==AR 字面）"
        f"＋铁律 AR≤E*（margin {float(W['margin']):.16f}>0 严格）＋分片语义 "
        f"10 排除片>E*/2 片≤E*+1e-6＋certs 12/12 一一对应对账 全过")

    spots = spot_points(W["chain"])
    log(f"[spots ] seed={SEED} 3 点（2⁻²⁰ 网格）：片定位 "
        + "、".join(f"#{iv}" for (_, iv) in spots) + "（最小命中指数法）")

    text = emit_data_lean_text(W, spots)
    DATA_LEAN.parent.mkdir(parents=True, exist_ok=True)
    DATA_LEAN.write_text(text)
    # 确定性重跑自检：再发射一次必须字节一致
    if emit_data_lean_text(W, spots) != DATA_LEAN.read_text():
        fail("确定性自检失守：重发射字节不一致")
    parsed = reparse_defs(DATA_LEAN.read_text())
    n_defs = selfcheck(W, spots, parsed)
    import re as _re
    n_thm = len(_re.findall(r"^theorem ", DATA_LEAN.read_text(), _re.M))
    log(f"[emit ] TableB6Data.lean（{DATA_LEAN.stat().st_size / 1e3:.0f}KB，"
        f"{n_defs} 个 ℚ def＋{n_thm} 定理）＋回读自检逐位对账全过＋确定性重跑字节一致")

    if not MAIN_LEAN.is_file():
        fail("主件 TableB6.lean 不在场（手写件，须与本发射器同轮交付）")
    main_src = MAIN_LEAN.read_text()
    if _re.findall(r"^import\s+\S+$", main_src, _re.M) != \
            ["import Mathlib", "import ThomsonN9.TableB6Data"]:
        fail("主件 import 面失配（应恰为 [Mathlib, ThomsonN9.TableB6Data]）")
    log("[main  ] TableB6.lean 在场且 import 面恰 [Mathlib, ThomsonN9.TableB6Data]")

    checks = dict(
        eg_sha256_anchored=True,
        chain_monotone=all(W["chain"][k] <= W["chain"][k + 1] for k in range(12)),
        chain_seamless=True,                      # rederive 内逐位已验（失守即 fail）
        endpoints_anchored=W["chain"][0] == -1 and W["chain"][12] == 1,
        ar_le_all_bounds=all(W["a_r"] <= b for b in W["bounds"]),
        ar_is_min=W["a_r"] == min(W["bounds"]),
        b10_eq_ar=W["bounds"][10] == W["a_r"],
        iron_rule_ar_le_estar=W["a_r"] <= W["estar"],
        margin_pos=W["margin"] > 0,
        iron_rule_eps=W["a_r"] <= W["estar"] + IRON_EPS,
        exclusion_pieces_gt_estar=[i for i in range(12)
                                   if W["pieces"][i] == "exclusion"
                                   and not W["estar"] < W["bounds"][i]] == [],
        covering_pieces_le_iron=[i for i in range(12)
                                 if W["pieces"][i] == "covering"
                                 and not W["bounds"][i] <= W["estar"] + IRON_EPS] == [],
        piece_counts=dict(exclusion=W["pieces"].count("exclusion"),
                          covering=W["pieces"].count("covering")),
        certs_bijection_12_of_12=set(W["cert_bounds"]) == set(W["bounds"])
        and len(set(W["cert_bounds"])) == 12,
    )
    for k, v in checks.items():
        if v is False or v == [] and isinstance(v, list):
            fail(f"重导检查失守：{k}")

    doc = dict(
        kind="n9-r15-b6-data",
        task="r15a-tableb-b6",
        script="bounds/r15_b6_data.py",
        code_version=code_version(),
        timestamp=datetime.now(timezone.utc).isoformat(timespec="seconds"),
        seed=SEED,
        heavy_solves=0,
        inputs=dict(
            endgame_json=dict(path="numerics/bounds/results/endgame.json",
                              sha256=sha256_of(EG_JSON),
                              role="只读（12 分区/E*/AR/citedCertificates 唯一记录源；"
                                   "不变锚 86863a09…69f）"),
        ),
        partition=dict(
            n_regions=12,
            endpoints=[fs(c) for c in W["chain"]],
            endpoints_note="13 端点链单调无缝（相邻区域共享端点逐位）；e0=−1、e12=1",
            bounds=[fs(b) for b in W["bounds"]],
            pieces=W["pieces"],
            bounds_match_cited_certificates="12/12 值一双射对账（certs claimed_bound ↔ 分区 bound）",
        ),
        record=dict(
            aR=fs(W["a_r"]),
            estar=fs(W["estar"]),
            estar_float=float(W["estar"]),
            aR_float=float(W["a_r"]),
            aR_is_min_of_bounds=True,
            hp_piece_index10_literal_eq=True,
            iron_rule_ar_le_estar=True,
            margin_exact=fs(W["margin"]),
            margin_float=float(W["margin"]),
            iron_rule_eps=True,
        ),
        piece_semantics=dict(
            exclusion_indices=[i for i in range(12) if W["pieces"][i] == "exclusion"],
            covering_indices=[i for i in range(12) if W["pieces"][i] == "covering"],
            exclusion_gt_estar="10/10 片 E* < bᵢ",
            covering_le_iron="2/2 片 bᵢ ≤ E*+1e-6（指标 10 HP＋指标 11 cap [−187/250,1]）",
        ),
        spot_checks=dict(
            scheme=("seed 20261017；k=0,1,2 依次 i=rng.randint(−2²⁰,2²⁰)、x=i/2²⁰"
                    "（2⁻²⁰ 网格）；最小命中指数法 j=min{j: x≤e_j}、片 i=j−1（j=0 时 i=0），"
                    "与主件 Nat.find 覆盖机器同规则；定理 cover_spot0..2"),
            points=[dict(x=fs(x), interval=iv,
                         lo=fs(W["chain"][iv]), hi=fs(W["chain"][iv + 1]))
                    for (x, iv) in spots]),
        lean=dict(
            data_file="formal/lean/ThomsonN9/TableB6Data.lean（本发射器确定性生成；仅 import Mathlib；"
                      "重跑字节一致）",
            main_file="formal/lean/ThomsonN9/TableB6.lean（手写主件；仅 import Mathlib＋"
                      "ThomsonN9.TableB6Data；零数据值字面量——数值面全部锚定 Data 件）",
            theorem_counts=dict(
                data=n_thm,
                main=len(_re.findall(r"^theorem ", main_src, _re.M))),
        ),
        rederive_checks={k: v for k, v in checks.items()},
        scope_note=("B6 算术层（拼接端点/记录锚件）：覆盖/记录 min/铁律/分片语义；"
                    "『区域 i 上 E≥b_i』证书语义＝数值层职责（typed_ladder/hermite/hp 各证书 "
                    "verifyCmd）不在件内（docstring 双侧如实）"),
        wall_s=round(time.time() - t0, 1),
    )
    OUT_JSON.parent.mkdir(parents=True, exist_ok=True)
    OUT_JSON.write_text(json.dumps(doc, ensure_ascii=False, indent=1))
    log(f"[done ] {OUT_JSON}（{doc['wall_s']}s）；exit 0")


if __name__ == "__main__":
    main()
