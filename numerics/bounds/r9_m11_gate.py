#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r9_m11_gate.py — R9C m11-budget-decision 验收门（G1–G4 ＋ 负对照 NC1）.

任务书口径（D34 裁决 3）：M11 扩容决策件 notes/m11-expansion-decision.md 的
预算门裁决（不可触发）／成本模型／L0 终态链／重开条件／r8_m9 裁定五节，
全部算术由本门自四账本（m9_campaign／m10_campaign／typed_ladder／
hermite_v2_campaign）以 fractions.Fraction 独立重算，与文档宣称逐位比对；
E* 一律十进制口径 Fraction("25.759986531")（D28 裁决 3）。零求解零 SDP；
全部检查确定性（无随机路径；种子 20261010 按惯例记档）。

检查面：
  G1 决策文档在档且含五节锚（预算门裁决/成本模型/终态链/重开条件/r8_m9）
  G2 四账本 Fraction 重算 vs 文档宣称逐位一致（四源和/当量/两口径余量/
     每迭代两档/×3.40/12 角表全部格与端点/E*−attempt 链四数精确分数与
     float/X9）
  G3 触发器判定一致性（0.2<12 且 6.628<12 ⇒ not_triggered；四账本行数/
     状态/solve_s 签名＝R8 终账冻结态 ⇒ 本轮求解账增量 0，无新行）
  G4 D34/D29 裁决锚在档（文档引用＋decisions.md 章节在档）
  NC1 /tmp 文档副本预算和篡改（33.372→34.372）⇒ G2 失配 exit 1（自跑检出；
      未篡改 /tmp 副本 exit 0 作路由 sanity）

用法（thomson-n9 下）：
  python3 numerics/bounds/r9_m11_gate.py                 # 全门（exit 0 = 过）
  python3 numerics/bounds/r9_m11_gate.py --doc PATH      # 对指定文档副本跑门（NC 用）
  python3 numerics/bounds/r9_m11_gate.py --no-nc         # 跳过 NC1（NC 子进程用）
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
REPO = HERE.parents[1]

SEED_GATE = 20261010                     # 惯例记档；本门无随机路径（确定性）
E_STAR_DEC = Fraction("25.759986531")    # 十进制精确口径（D28 裁决 3）
EQUIV_UNIT_S = 10800                     # 1 当量 = 10800s
TRIGGER_EQUIV = Fraction(12)             # M11 触发器阈值（D29 裁决 1）
TASKBOOK_MARGIN = Fraction("0.2")        # 口径 A：任务书 R9 预算行余量（当量）
CAMPAIGN_CAP = Fraction(40)              # campaign 预算上限（当量）
X9_THRESHOLD = Fraction("5.3e-5")        # = 53/1000000（D29 裁决 2 相位 2 阈）

DOC_DEFAULT = REPO / "notes" / "m11-expansion-decision.md"
DECISIONS = REPO / "notes" / "decisions.md"
M9C = RESULTS / "m9_campaign.json"
M10C = RESULTS / "m10_campaign.json"
TL = RESULTS / "typed_ladder.json"
V2C = RESULTS / "hermite_v2_campaign.json"

ANCHORS = ["预算门裁决", "成本模型", "终态链", "重开条件", "r8_m9"]
SCALES = ["1.6", "1.85", "2.1", "2.5"]
ITERS = [50, 60, 70]

# R8 终账冻结签名（D29 回填裁决 6／D32 裁决 5；G3 增量 0 检查面）
M9_SIGNATURE = dict(pieces=["m082-m079", "m079-m765", "m765-m748", "m0748"],
                    statuses=["certified", "blocked", "blocked", "not_run"],
                    solve_s=[31536.3, 40741.8, 30226.8, None],
                    total_solve_s=102504.9, total_equivalents=9.491)
M10_SIGNATURE = dict(statuses=["certified", "blocked"],
                     solve_s=[121039.7, 64025.9],
                     total_solve_s=185065.6, total_equivalents=17.136)
TYPED_M9_SIGNATURE = dict(tag="m0748", solve_s=42305.7, iteration=89,
                          phase_value="pdOPT",
                          certified_float=25.75984622533888)
V2_SIGNATURE = dict(phase1_solve_s=30542.1, phase1_outcome="blocked",
                    phase2_launched=False, phase2_outcome="not_triggered",
                    budget_total=30542.1)


def fail(msg: str) -> None:
    print(f"[gate][FAIL] {msg}", flush=True)
    sys.exit(1)


def okmsg(msg: str) -> None:
    print(f"[gate][ok] {msg}", flush=True)


def jload(p: Path):
    return json.loads(p.read_text())


def f1(x: Fraction) -> str:
    return f"{float(x):.1f}"


def f2(x: Fraction) -> str:
    return f"{float(x):.2f}"


def f3(x: Fraction) -> str:
    return f"{float(x):.3f}"


# ---------------------------------------------------------------- 四账本重算
def load_sources():
    """四账本 → 七源 Fraction 值＋链上精确分数（全部逐字段直读，无硬编码数值）。"""
    m9 = jload(M9C)
    m10 = jload(M10C)
    tl = jload(TL)
    v2 = jload(V2C)

    pieces = ["m082-m079", "m079-m765", "m765-m748"]
    src = {k: Fraction(str(m9["budget"]["per_piece"][k]["solve_s"]))
           for k in pieces}
    # m9 rows 与 budget.per_piece 同值性（账本内部一致）
    for k, row in zip(pieces, m9["rows"][:3]):
        if Fraction(str(row["solve_s"])) != src[k]:
            fail(f"G2 账本内部不一致：m9 rows[{k}]≠budget.per_piece")
    src["m10_r0"] = Fraction(str(m10["rows"][0]["solve_s"]))
    src["m10_r1"] = Fraction(str(m10["rows"][1]["solve_s"]))
    m9rungs = [r for r in tl["rungs"] if r.get("M") == 9]
    if len(m9rungs) != 1:
        fail(f"G2 typed_ladder M9 rung 应恰 1 条，实得 {len(m9rungs)}")
    src["typed_m9"] = Fraction(str(m9rungs[0]["sdpa"]["solve_s"]))
    src["v2_phase1"] = Fraction(str(v2["phase1"]["solve_s"]))
    total = sum(src.values())

    # 每迭代两档（迭代数自同账本 sdpa.iteration 直读）
    iter_m9 = m9["rows"][2]["sdpa"]["iteration"]
    iter_m10 = m10["rows"][1]["sdpa"]["iteration"]
    per_iter_m9 = src["m765-m748"] / iter_m9
    per_iter_m10 = src["m10_r1"] / iter_m10

    # 链四档（精确分数＋E* 十进制口径差）
    chain = [
        ("a5 M10", Fraction(m10["rows"][1]["certified"])),
        ("v2 contact M9", Fraction(v2["phase1"]["certified"])),
        ("a5 M9", Fraction(m9["rows"][2]["certified"])),
        ("a5 M8", Fraction(m9["m8_baselines"]["m765-m748"]["certified"])),
    ]
    gaps = [(name, c, E_STAR_DEC - c) for name, c in chain]
    x9 = chain[1][1] - chain[2][1]
    if str(x9) != str(v2["X9"]["value"]):
        fail(f"G2 X9 重算 {x9} ≠ 账本 X9.value {v2['X9']['value']}")

    return dict(m9=m9, m10=m10, tl=tl, v2=v2, src=src, total=total,
                iter_m9=iter_m9, iter_m10=iter_m10,
                per_iter_m9=per_iter_m9, per_iter_m10=per_iter_m10,
                gaps=gaps, x9=x9, typed_rung=m9rungs[0])


# ---------------------------------------------------------------- G1
def check_g1(doc_text: str) -> None:
    for a in ANCHORS:
        if a not in doc_text:
            fail(f"G1 决策文档缺五节锚之一：{a}")
    okmsg(f"G1 决策文档在档且含五节锚（{'/'.join(ANCHORS)}）")


# ---------------------------------------------------------------- G2
def check_g2(doc_text: str, d: dict) -> dict:
    total = d["total"]
    equiv = total / EQUIV_UNIT_S
    margin_b = CAMPAIGN_CAP - equiv
    cells = {s: [d["per_iter_m10_round"] * Fraction(s) * it / EQUIV_UNIT_S
                 for it in ITERS] for s in SCALES}

    # —— 四源和与当量 ——
    if f1(total) != "360418.3":
        fail(f"G2 四源和重算＝{f1(total)}s ≠ 存档锚 360418.3s（账本被改动？）")
    if "360418.3" not in doc_text:
        fail("G2 文档缺四源和宣称 360418.3")
    if f3(equiv) != "33.372":
        fail(f"G2 四源和当量重算＝{f3(equiv)} ≠ 33.372")
    if "33.372" not in doc_text or "33.372/40" not in doc_text:
        fail("G2 文档缺当量宣称 33.372／33.372/40")
    # —— 预算两口径 ——
    if f3(margin_b) != "6.628":
        fail(f"G2 口径 B 重算＝{f3(margin_b)} ≠ 6.628")
    if "0.2" not in doc_text or "6.628" not in doc_text:
        fail("G2 文档缺两口径余量宣称 0.2／6.628")
    if f1(TASKBOOK_MARGIN * EQUIV_UNIT_S) != "2160.0" or "2160" not in doc_text:
        fail("G2 文档缺口径 A 换算 2160s")
    # —— 每迭代两档 ×3.40 ——
    if f1(d["per_iter_m9"]) != "335.9" or f1(d["per_iter_m10"]) != "1143.3":
        fail(f"G2 每迭代重算 M9={f1(d['per_iter_m9'])}s "
             f"M10={f1(d['per_iter_m10'])}s ≠ 335.9／1143.3")
    ratio = d["per_iter_m10"] / d["per_iter_m9"]
    if f2(ratio) != "3.40":
        fail(f"G2 每迭代比 M10/M9 重算＝{f2(ratio)} ≠ 3.40")
    for tok in ("335.9", "1143.3", "3.40"):
        if tok not in doc_text:
            fail(f"G2 文档缺成本模型宣称 {tok}")
    # 7×335.9＝2351.3>2160（口径 A 不可用性旁证）
    if f1(7 * d["per_iter_m9_round"]) != "2351.3" or "2351.3" not in doc_text:
        fail("G2 文档缺 7×335.9s＝2351.3s 旁证")
    # v2 最小整解 2.828 当量
    if f3(d["src"]["v2_phase1"] / EQUIV_UNIT_S) != "2.828" or \
            "2.828" not in doc_text:
        fail("G2 文档缺 v2 contact M9 最小整解成本 2.828 当量")
    # —— 12 角表 ——
    all_cells = [c for row in cells.values() for c in row]
    for s in SCALES:
        for c in cells[s]:
            if f2(c) not in doc_text:
                fail(f"G2 文档缺 12 角表格 {s}×：{f2(c)}")
    lo, hi = min(all_cells), max(all_cells)
    if f2(lo) != "8.47" or f2(hi) != "18.53":
        fail(f"G2 12 角表端点重算 {f2(lo)}–{f2(hi)} ≠ 8.47–18.53")
    if "8.47" not in doc_text or "18.53" not in doc_text:
        fail("G2 文档缺区间端点宣称 8.47／18.53")
    # —— E*−attempt 链四数（精确分数＋float 逐位） ——
    for name, cert, gap in d["gaps"]:
        if str(cert) not in doc_text:
            fail(f"G2 文档缺链档 {name} certified 精确分数 {cert}")
        if repr(float(cert)) not in doc_text:
            fail(f"G2 文档缺链档 {name} certified float {repr(float(cert))}")
        if str(gap) not in doc_text:
            fail(f"G2 文档缺链档 {name} E*−attempt 精确分数 {gap}")
        if repr(float(gap)) not in doc_text:
            fail(f"G2 文档缺链档 {name} E*−attempt float {repr(float(gap))}")
    # —— X9 ——
    if str(d["x9"]) not in doc_text:
        fail(f"G2 文档缺 X9 精确分数 {d['x9']}")
    if repr(float(d["x9"])) not in doc_text:
        fail(f"G2 文档缺 X9 float {repr(float(d['x9']))}")
    if "+2.934781374e-06" not in doc_text:
        fail("G2 文档缺 X9 档位记法 +2.934781374e-06")
    x9_ratio = X9_THRESHOLD / d["x9"]          # 阈/实测（低多少倍）
    if f1(x9_ratio) != "18.1" or "18.1" not in doc_text:
        fail("G2 文档缺 X9 距阈 18.1× 宣称")
    okmsg(f"G2 四源和 360418.3s＝33.372/40 当量；每迭代 335.9→1143.3（×3.40）；"
          f"12 角表 {f2(lo)}–{f2(hi)}；链四数＋X9 全部与文档逐位一致")

    return dict(equiv=equiv, margin_b=margin_b, cells=cells)


# ---------------------------------------------------------------- G3
def check_g3(doc_text: str, d: dict, g2: dict) -> None:
    # —— 触发器判定 ——
    a_ok = TASKBOOK_MARGIN < TRIGGER_EQUIV
    b_val = g2["margin_b"]
    b_ok = b_val < TRIGGER_EQUIV
    if not (a_ok and b_ok):
        fail(f"G3 触发器重算异常：口径A {TASKBOOK_MARGIN}<12={a_ok}、"
             f"口径B {float(b_val):.3f}<12={b_ok}（应均成立）")
    if f3(b_val) != "6.628":
        fail("G3 口径 B 端值非 6.628")
    for tok in ("不可触发", "not_triggered", "不排"):
        if tok not in doc_text:
            fail(f"G3 文档缺裁决宣称「{tok}」")

    # —— 四账本冻结签名 ⇒ 本轮求解账增量 0（无新行） ——
    m9, m10, v2, rung = d["m9"], d["m10"], d["v2"], d["typed_rung"]
    sig = M9_SIGNATURE
    if len(m9["rows"]) != 4:
        fail(f"G3 m9_campaign 行数 {len(m9['rows'])}≠4（有新行？）")
    if [r["piece"] for r in m9["rows"]] != sig["pieces"]:
        fail("G3 m9_campaign pieces 签名失配")
    if [r["status"] for r in m9["rows"]] != sig["statuses"]:
        fail("G3 m9_campaign statuses 签名失配（rows[3] 须仍 not_run——D32 裁决 5）")
    if [r["solve_s"] for r in m9["rows"]] != sig["solve_s"]:
        fail("G3 m9_campaign solve_s 签名失配")
    if Fraction(str(m9["budget"]["total_solve_s"])) != \
            Fraction(str(sig["total_solve_s"])):
        fail("G3 m9_campaign total_solve_s 失配")
    if Fraction(str(m9["budget"]["total_equivalents"])) != \
            Fraction(str(sig["total_equivalents"])):
        fail("G3 m9_campaign total_equivalents 失配")
    sig = M10_SIGNATURE
    if len(m10["rows"]) != 2:
        fail(f"G3 m10_campaign 行数 {len(m10['rows'])}≠2（有新行？）")
    if [r["status"] for r in m10["rows"]] != sig["statuses"] or \
            [r["solve_s"] for r in m10["rows"]] != sig["solve_s"]:
        fail("G3 m10_campaign 行签名失配")
    if Fraction(str(m10["budget"]["total_solve_s"])) != \
            Fraction(str(sig["total_solve_s"])):
        fail("G3 m10_campaign total_solve_s 失配")
    if Fraction(str(m10["budget"]["total_equivalents"])) != \
            Fraction(str(sig["total_equivalents"])):
        fail("G3 m10_campaign total_equivalents 失配")
    sig = TYPED_M9_SIGNATURE
    if rung.get("tag") != sig["tag"] or rung["sdpa"].get("phase_value") != \
            sig["phase_value"] or rung["sdpa"].get("iteration") != \
            sig["iteration"] or rung["sdpa"].get("solve_s") != sig["solve_s"] \
            or rung.get("certified_float") != sig["certified_float"]:
        fail("G3 typed_ladder M9 rung 签名失配")
    sig = V2_SIGNATURE
    p1, p2 = v2["phase1"], v2["phase2"]
    if p1.get("solve_s") != sig["phase1_solve_s"] or \
            (p1.get("outcome") or p1.get("status")) != sig["phase1_outcome"]:
        fail("G3 hermite_v2_campaign phase1 签名失配")
    if p2.get("launched") is not sig["phase2_launched"] or \
            p2.get("outcome") != sig["phase2_outcome"]:
        fail("G3 hermite_v2_campaign phase2 须仍 not_triggered")
    if Fraction(str(v2["budget"]["solve_s_total"])) != \
            Fraction(str(sig["budget_total"])):
        fail("G3 hermite_v2_campaign budget.solve_s_total 失配")
    if "无新行" not in doc_text:
        fail("G3 文档缺「无新行」增量 0 宣称")
    okmsg("G3 触发器 0.2<12 且 6.628<12 ⇒ not_triggered；四账本签名＝R8 终账"
          "冻结态 ⇒ 本轮求解账增量 0（hermite_v2_campaign/m9/m10 无新行）")


# ---------------------------------------------------------------- G4
def check_g4(doc_text: str) -> None:
    for anchor in ("D34 裁决 1", "D29 裁决 1", "D28 裁决 3",
                   "D31 裁决 6", "D32 裁决 5"):
        if anchor not in doc_text:
            fail(f"G4 文档缺裁决锚「{anchor}」")
    dec = DECISIONS.read_text()
    for sec in ("### D34", "### D29"):
        if sec not in dec:
            fail(f"G4 notes/decisions.md 缺章节锚 {sec}")
    okmsg("G4 裁决锚在档：文档 D34 裁决 1／D29 裁决 1（＋D28 裁决 3／"
          "D31 裁决 6／D32 裁决 5）；decisions.md 含 ### D34／### D29")


# ---------------------------------------------------------------- NC1
def run_nc1(doc_path: Path) -> None:
    self_py = Path(__file__).resolve()
    orig_txt = doc_path.read_text()
    base = Path("/tmp/r9c_m11_nc1")
    # 路由 sanity：未篡改 /tmp 副本须 exit 0
    orig_copy = base.with_name(base.name + "_orig.md")
    orig_copy.write_text(orig_txt)
    r0 = subprocess.run([sys.executable, str(self_py), "--doc", str(orig_copy),
                         "--no-nc"], capture_output=True, text=True)
    if r0.returncode != 0:
        fail(f"NC1 前置失败：未篡改 /tmp 副本应 exit 0，实得 "
             f"{r0.returncode}（{r0.stdout.strip().splitlines()[-1:] }）")
    # 篡改：预算和 33.372→34.372 ⇒ G2 失配 exit 1
    tampered = orig_txt.replace("33.372", "34.372")
    if tampered == orig_txt:
        fail("NC1 前置失败：文档无 33.372 可篡改")
    tdoc = base.with_name(base.name + "_doc.md")
    tdoc.write_text(tampered)
    r = subprocess.run([sys.executable, str(self_py), "--doc", str(tdoc),
                        "--no-nc"], capture_output=True, text=True)
    if r.returncode == 0:
        fail("NC1 未检出篡改（33.372→34.372 仍 exit 0）")
    if "G2" not in r.stdout:
        fail(f"NC1 失配面非 G2：\n{r.stdout}")
    orig_copy.unlink(missing_ok=True)
    tdoc.unlink(missing_ok=True)
    okmsg("NC1 /tmp 文档副本预算和篡改（33.372→34.372）⇒ G2 失配 "
          f"exit {r.returncode} 检出 ✓（未篡改副本 exit 0 sanity ✓）")


def run_gate(doc_path: Path, run_nc: bool) -> None:
    print(f"[gate] r9_m11_gate seed={SEED_GATE}（确定性检查，无随机路径）",
          flush=True)
    if not doc_path.exists():
        fail(f"G1 决策文档不在档：{doc_path}")
    doc_text = doc_path.read_text()
    d = load_sources()
    d["per_iter_m9_round"] = Fraction("335.9")    # 档位记法（D29 裁决 1 口径）
    d["per_iter_m10_round"] = Fraction("1143.3")  # 12 角表逐迭代基准
    if round(d["per_iter_m9"], 1) != d["per_iter_m9_round"] or \
            round(d["per_iter_m10"], 1) != d["per_iter_m10_round"]:
        fail("G2 每迭代档位记法与账本重算不符（335.9／1143.3）")

    check_g1(doc_text)
    g2 = check_g2(doc_text, d)
    check_g3(doc_text, d, g2)
    check_g4(doc_text)
    if run_nc:
        run_nc1(doc_path)
    print("[gate] 全门 PASS（G1–G4 ＋ NC1）", flush=True)


def main() -> None:
    ap = argparse.ArgumentParser(description="R9C m11-budget-decision 验收门")
    ap.add_argument("--doc", default=str(DOC_DEFAULT),
                    help="决策文档路径（默认 notes/m11-expansion-decision.md）")
    ap.add_argument("--no-nc", action="store_true",
                    help="跳过 NC1（NC 子进程内部用）")
    args = ap.parse_args()
    run_gate(Path(args.doc).resolve(), not args.no_nc)


if __name__ == "__main__":
    main()
