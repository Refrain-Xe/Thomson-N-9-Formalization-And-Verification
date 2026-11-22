#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r10_rc2_gate.py — R10C rc2-engine-survey 验收门（G1–G3 ＋ 负对照 NC1/NC2）.

任务书口径（D38 裁决 4）：RC2 重开条件候选引擎类预研件
notes/rc2-engine-survey.md（零实测设计件）的四节锚＋诚实锚；引档数字全部
由本门自四账本（m9_campaign／typed_ladder／m10_campaign／hermite_v2_campaign）
＋两 solver_events 以 fractions.Fraction 独立重算，与文档宣称逐位比对；
m11-expansion-decision.md 不被重写（git diff HEAD 守卫）。零求解零 SDP；
全部检查确定性（无随机路径；种子 20261012 按惯例记档）；CWD 无关
（路径全部自 __file__ 推导）。

检查面：
  G1 预研文档在档且含四节锚（标度复述/候选引擎类清单/首测排序/诚实边界）
     ＋『零实测』『非实测判据』（＋『设计层推算』）诚实锚
  G2 引档数字 Fraction 复算 vs 文档逐位一致：
     30226.8/90＝335.853、64025.9/56＝1143.32、比值 3.4042（×3.40）、
     迭代数 {90,89,91,110,56} 与四账本逐位（a5 M9/typed cap M9/
     v2 contact M9/Lukács M10/a5 M10）、七源和 360418.3s＝33.372/40、
     口径 B 715817/108000→6.628、最乐观角 91464/10800＝8.4689 当量、
     其半 4.2344 < 6.628（精确 Fraction 比较）、C1 判死线 715817/914640
     →0.7826、C2 成本 128051.8/10800→11.86、SDP 规模八数
     （2907/258016/3009/262280/3990/481248/4104/486546）＋规模增长三比值
     （1.3725/1.8652/1.8251）
  G3 notes/m11-expansion-decision.md 不被重写（git diff HEAD 守卫：
     该路径相对 HEAD 零改动）
  NC1 /tmp 文档副本 ×3.40 改 ×2.40 ⇒ G2 失配 exit 1（自跑检出；
      未篡改 /tmp 副本 exit 0 作路由 sanity）
  NC2 /tmp 副本迭代数 56 改 66（序列字面 {90,89,91,110,56}→…66）
      ⇒ G2 失配 exit 1

用法：
  python3 numerics/bounds/r10_rc2_gate.py                 # 全门（exit 0 = 过）
  python3 numerics/bounds/r10_rc2_gate.py --doc PATH      # 对指定文档副本跑门（NC 用）
  python3 numerics/bounds/r10_rc2_gate.py --no-nc         # 跳过 NC（NC 子进程用）
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
REPO = HERE.parents[1]

SEED_GATE = 20261012                     # 惯例记档；本门无随机路径（确定性）
EQUIV_UNIT_S = 10800                     # 1 当量 = 10800s
CAMPAIGN_CAP = Fraction(40)              # campaign 预算上限（当量）

DOC_DEFAULT = REPO / "notes" / "rc2-engine-survey.md"
M11_DOC = REPO / "notes" / "m11-expansion-decision.md"
M9C = RESULTS / "m9_campaign.json"
M10C = RESULTS / "m10_campaign.json"
TL = RESULTS / "typed_ladder.json"
V2C = RESULTS / "hermite_v2_campaign.json"
V2STRIPS = RESULTS / "hermite_v2_strips.json"
M10EV = RESULTS / "m10_solver_events.json"

ANCHORS = ["标度复述", "候选引擎类清单", "首测排序", "诚实边界",
           "零实测", "非实测判据", "设计层推算"]

# 档案冻结签名（G2 重算对象；失配即「账本被改动？」fail）
EXPECT = dict(
    m9_rows2_solve_s=30226.8, m9_rows2_iter=90, m9_rows2_phase="pdOPT",
    m10_rows1_solve_s=64025.9, m10_rows1_iter=56,
    m10_rows1_phase="noINFO",
    m10_rows0_solve_s=121039.7, m10_rows0_iter=110,
    typed_m9_solve_s=42305.7, typed_m9_iter=89,
    v2_phase1_solve_s=30542.1, v2_phase1_iter=91,
    m9_pp_solve_s=[31536.3, 40741.8, 30226.8],
)


def fail(msg: str) -> None:
    print(f"[gate][FAIL] {msg}", flush=True)
    sys.exit(1)


def okmsg(msg: str) -> None:
    print(f"[gate][ok] {msg}", flush=True)


def jload(p: Path):
    return json.loads(p.read_text())


def need(tok: str, doc_text: str, what: str) -> None:
    if tok not in doc_text:
        fail(f"G2 文档缺{what}宣称 {tok!r}")


def fdec(x: Fraction, n: int) -> str:
    return f"{float(x):.{n}f}"


# ---------------------------------------------------------------- 档案重算
def load_sources() -> dict:
    """四账本＋两 solver_events → Fraction 值与迭代数（全部逐字段直读）。"""
    m9, m10, tl, v2 = jload(M9C), jload(M10C), jload(TL), jload(V2C)
    ex = EXPECT

    r2, r10 = m9["rows"][2], m10["rows"][1]
    r10_0 = m10["rows"][0]
    if r2["solve_s"] != ex["m9_rows2_solve_s"] or \
            r2["sdpa"]["iteration"] != ex["m9_rows2_iter"] or \
            r2["sdpa"]["phase_value"] != ex["m9_rows2_phase"]:
        fail(f"G2 m9_campaign rows[2] 签名失配（{r2['solve_s']}/"
             f"{r2['sdpa']['iteration']}/{r2['sdpa']['phase_value']}）"
             "——账本被改动？")
    if r10["solve_s"] != ex["m10_rows1_solve_s"] or \
            r10["sdpa"]["iteration"] != ex["m10_rows1_iter"] or \
            r10["sdpa"]["phase_value"] != ex["m10_rows1_phase"]:
        fail(f"G2 m10_campaign rows[1] 签名失配（{r10['solve_s']}/"
             f"{r10['sdpa']['iteration']}/{r10['sdpa']['phase_value']}）"
             "——账本被改动？")
    if r10_0["solve_s"] != ex["m10_rows0_solve_s"] or \
            r10_0["sdpa"]["iteration"] != ex["m10_rows0_iter"]:
        fail("G2 m10_campaign rows[0] 签名失配——账本被改动？")

    rungs = [r for r in tl["rungs"] if r.get("M") == 9]
    if len(rungs) != 1:
        fail(f"G2 typed_ladder M9 rung 应恰 1 条，实得 {len(rungs)}")
    rung = rungs[0]
    if rung["sdpa"]["solve_s"] != ex["typed_m9_solve_s"] or \
            rung["sdpa"]["iteration"] != ex["typed_m9_iter"]:
        fail("G2 typed_ladder M9 rung 签名失配——账本被改动？")

    p1 = v2["phase1"]
    m = re.search(r"iter=(\d+)", p1.get("note", ""))
    if p1["solve_s"] != ex["v2_phase1_solve_s"] or m is None or \
            int(m.group(1)) != ex["v2_phase1_iter"]:
        fail("G2 hermite_v2_campaign phase1 签名失配（solve_s/note iter）"
             "——账本被改动？")
    v2_iter = int(m.group(1))
    # 交叉核对：行档 hermite_v2_strips contact M9 的 sdpa.iteration 同值
    if V2STRIPS.exists():
        row = [r for r in jload(V2STRIPS)["strips"]
               if r.get("tag") == "m765-m748" and r.get("M") == 9
               and r.get("variant") == "contact"]
        if len(row) != 1 or row[0]["sdpa"]["iteration"] != v2_iter:
            fail("G2 hermite_v2_strips contact M9 迭代数与 campaign note 不一致")

    # 七源（口径 B 重算读取面，同 r9_m11_gate G2 路径）
    pieces = ["m082-m079", "m079-m765", "m765-m748"]
    pp = {k: Fraction(str(m9["budget"]["per_piece"][k]["solve_s"]))
          for k in pieces}
    if [float(pp[k]) for k in pieces] != ex["m9_pp_solve_s"]:
        fail("G2 m9_campaign budget.per_piece 三片签名失配——账本被改动？")
    src = dict(pp)
    src["m10_r0"] = Fraction(str(r10_0["solve_s"]))
    src["m10_r1"] = Fraction(str(r10["solve_s"]))
    src["typed_m9"] = Fraction(str(rung["sdpa"]["solve_s"]))
    src["v2_phase1"] = Fraction(str(p1["solve_s"]))
    total = sum(src.values())

    # SDP 规模（结构层）
    st = v2["phase0"]["smoke"]["structure"]
    c9, c10 = st["contact@M9"], st["contact@M10"]

    ev_m9 = re.search(r"m=(\d+) entries=(\d+)",
                      m9["solver_events"]["m082-m079"][0]["detail"])
    m10ev = jload(M10EV)["events"]
    ev10_0 = re.search(r"m=(\d+) entries=(\d+)", m10ev[0]["detail"])
    ev10_1 = re.search(r"m=(\d+) entries=(\d+)", m10ev[1]["detail"])
    if not (ev_m9 and ev10_0 and ev10_1):
        fail("G2 solver_events detail 缺 m=/entries= 导出行——账本被改动？")
    canary = (int(ev_m9.group(1)), int(ev_m9.group(2)))
    luk10 = (int(ev10_0.group(1)), int(ev10_0.group(2)))
    a5_10 = (int(ev10_1.group(1)), int(ev10_1.group(2)))

    return dict(
        per_iter_m9=src["m765-m748"] / ex["m9_rows2_iter"],
        per_iter_m10=src["m10_r1"] / ex["m10_rows1_iter"],
        iters=[ex["m9_rows2_iter"], ex["typed_m9_iter"], v2_iter,
               ex["m10_rows0_iter"], ex["m10_rows1_iter"]],
        total=total, margin_b=CAMPAIGN_CAP - total / EQUIV_UNIT_S,
        contact_m9=(c9["m"], c9["entries"]),
        contact_m10=(c10["m"], c10["entries"]),
        canary=canary, lukacs10=luk10, a5_m10_scale=a5_10,
    )


# ---------------------------------------------------------------- G1
def check_g1(doc_text: str) -> None:
    for a in ANCHORS:
        if a not in doc_text:
            fail(f"G1 预研文档缺锚之一：{a}")
    okmsg(f"G1 预研文档在档且含四节锚＋诚实锚（{'/'.join(ANCHORS)}）")


# ---------------------------------------------------------------- G2
def check_g2(doc_text: str, d: dict) -> None:
    # —— 每迭代两档与 ×3.40 ——
    if fdec(d["per_iter_m9"], 3) != "335.853":
        fail(f"G2 每迭代 M9 重算＝{fdec(d['per_iter_m9'], 3)} ≠ 335.853")
    if fdec(d["per_iter_m10"], 2) != "1143.32":
        fail(f"G2 每迭代 M10 重算＝{fdec(d['per_iter_m10'], 2)} ≠ 1143.32")
    ratio = d["per_iter_m10"] / d["per_iter_m9"]
    if fdec(ratio, 4) != "3.4042":
        fail(f"G2 每迭代比 M10/M9 重算＝{fdec(ratio, 4)} ≠ 3.4042")
    for tok in ("335.853", "1143.32", "3.4042", "×3.40"):
        need(tok, doc_text, "成本模型")

    # —— 迭代数序列 {90,89,91,110,56}（四账本逐位） ——
    series_lit = "{" + ",".join(str(v) for v in d["iters"]) + "}"
    if series_lit != "{90,89,91,110,56}":
        fail(f"G2 迭代数序列重算＝{series_lit} ≠ {90,89,91,110,56}"
             "——账本被改动？")
    need(series_lit, doc_text, "迭代数序列字面")

    # —— 七源和／口径 B ——
    if fdec(d["total"], 1) != "360418.3":
        fail(f"G2 七源和重算＝{fdec(d['total'], 1)}s ≠ 360418.3（账本被改动？）")
    if fdec(d["total"] / EQUIV_UNIT_S, 3) != "33.372":
        fail(f"G2 七源和当量重算＝{fdec(d['total'] / EQUIV_UNIT_S, 3)} ≠ 33.372")
    if d["margin_b"] != Fraction(715817, 108000):
        fail(f"G2 口径 B 重算＝{d['margin_b']} ≠ 715817/108000")
    if fdec(d["margin_b"], 3) != "6.628":
        fail(f"G2 口径 B 重算＝{fdec(d['margin_b'], 3)} ≠ 6.628")
    for tok in ("360418.3", "33.372", "715817/108000", "6.628"):
        need(tok, doc_text, "预算口径")

    # —— 最乐观角／其半／判死线 ——
    best_s = Fraction("1143.3") * Fraction("1.6") * 50
    if best_s != 91464:
        fail(f"G2 最乐观角逐迭代基准重算＝{best_s} ≠ 91464")
    best = best_s / EQUIV_UNIT_S
    half = best_s / (2 * EQUIV_UNIT_S)
    if fdec(best, 4) != "8.4689" or fdec(best, 2) != "8.47":
        fail(f"G2 最乐观角重算＝{fdec(best, 4)}/{fdec(best, 2)} ≠ 8.4689/8.47")
    if fdec(half, 4) != "4.2344" or fdec(half, 2) != "4.23":
        fail(f"G2 最乐观角减半重算＝{fdec(half, 4)}/{fdec(half, 2)}"
             " ≠ 4.2344/4.23")
    if not half < d["margin_b"]:
        fail("G2 精确比较失败：4.2344 应 < 6.628（口径 B 可及域判定）")
    f_kill = d["margin_b"] / best
    if f_kill != Fraction(715817, 914640) or fdec(f_kill, 4) != "0.7826":
        fail(f"G2 C1 判死线重算＝{f_kill}（{fdec(f_kill, 4)}）"
             " ≠ 715817/914640（0.7826）")
    for tok in ("91464", "8.4689", "8.47", "4.2344", "4.23", "0.7826"):
        need(tok, doc_text, "最乐观角/减半/判死线")

    # —— C2 两片成本 ——
    c2 = Fraction("64025.9") * 2
    if c2 != Fraction("128051.8") or fdec(c2 / EQUIV_UNIT_S, 2) != "11.86":
        fail(f"G2 C2 成本重算＝{c2}/{fdec(c2 / EQUIV_UNIT_S, 2)} ≠ 11.86")
    for tok in ("128051.8", "11.86"):
        need(tok, doc_text, "C2 两片成本")

    # —— SDP 规模八数＋增长三比值 ——
    if d["contact_m9"] != (2907, 258016) or d["contact_m10"] != (3990, 481248) \
            or d["canary"] != (3009, 262280) or d["lukacs10"] != (4104, 486546) \
            or d["a5_m10_scale"] != (3990, 481248):
        fail(f"G2 SDP 规模签名失配：contact@M9 {d['contact_m9']}、"
             f"canary {d['canary']}、contact@M10 {d['contact_m10']}、"
             f"Lukács M10 {d['lukacs10']}——账本被改动？")
    g_m = Fraction(d["contact_m10"][0], d["contact_m9"][0])
    g_e = Fraction(d["contact_m10"][1], d["contact_m9"][1])
    g_pe = ratio / g_e
    if fdec(g_m, 4) != "1.3725" or fdec(g_e, 4) != "1.8652" or \
            fdec(g_pe, 4) != "1.8251":
        fail(f"G2 规模增长比重算 m={fdec(g_m, 4)} entries={fdec(g_e, 4)} "
             f"per-entry={fdec(g_pe, 4)} ≠ 1.3725/1.8652/1.8251")
    for tok in ("2907", "258016", "3009", "262280",
                "3990", "481248", "4104", "486546",
                "1.3725", "1.8652", "1.8251"):
        need(tok, doc_text, "SDP 规模/增长比")

    okmsg("G2 引档数字 Fraction 复算全过：335.853／1143.32／×3.4042、"
          f"迭代数 {series_lit} 四账本逐位、360418.3s＝33.372/40、"
          "口径 B 715817/108000→6.628、91464/10800＝8.4689（半 4.2344<6.628"
          " 精确成立）、判死线 0.7826、C2 11.86、SDP 规模八数＋三比值——"
          "全部与文档一致")


# ---------------------------------------------------------------- G3
def check_g3() -> None:
    if not M11_DOC.exists():
        fail(f"G3 m11 决策件不在档：{M11_DOC}")
    rel = "notes/m11-expansion-decision.md"
    r = subprocess.run(["git", "-C", str(REPO), "diff", "HEAD", "--", rel],
                       capture_output=True, text=True)
    if r.returncode != 0:
        fail(f"G3 git diff HEAD 守卫执行失败：{r.stderr.strip()}")
    if r.stdout.strip():
        fail(f"G3 {rel} 相对 HEAD 有改动（本件须 append-only 不重写它）：\n"
             f"{r.stdout[:500]}")
    okmsg(f"G3 {rel} 相对 HEAD 零改动（git diff HEAD 守卫 ✓）")


# ---------------------------------------------------------------- NC
def _subprocess_gate(doc_path: Path):
    return subprocess.run([sys.executable, str(Path(__file__).resolve()),
                           "--doc", str(doc_path), "--no-nc"],
                          capture_output=True, text=True)


def run_nc(doc_path: Path) -> None:
    self_py = Path(__file__).resolve()
    orig_txt = doc_path.read_text()

    # 路由 sanity：未篡改 /tmp 副本须 exit 0
    sanity = Path("/tmp/r10c_rc2_sanity.md")
    sanity.write_text(orig_txt)
    r0 = _subprocess_gate(sanity)
    if r0.returncode != 0:
        fail(f"NC 前置失败：未篡改 /tmp 副本应 exit 0，实得 {r0.returncode}"
             f"（{r0.stdout.strip().splitlines()[-1:]}）")

    # NC1：×3.40 改 ×2.40 ⇒ G2 失配 exit 1
    t1 = orig_txt.replace("×3.40", "×2.40")
    if t1 == orig_txt:
        fail("NC1 前置失败：文档无 ×3.40 可篡改")
    p1 = Path("/tmp/r10c_rc2_nc1.md")
    p1.write_text(t1)
    r1 = _subprocess_gate(p1)
    if r1.returncode == 0 or "G2" not in r1.stdout:
        fail(f"NC1 未按预期检出（×3.40→×2.40 应 G2 失配 exit 1）："
             f"exit {r1.returncode}\n{r1.stdout[-800:]}")

    # NC2：迭代数 56 改 66（序列字面末位）⇒ G2 失配 exit 1
    series_lit = "{" + ",".join(str(v) for v in [90, 89, 91, 110, 56]) + "}"
    tampered_lit = "{" + ",".join(str(v) for v in [90, 89, 91, 110, 66]) + "}"
    t2 = orig_txt.replace(series_lit, tampered_lit)
    if t2 == orig_txt:
        fail(f"NC2 前置失败：文档无序列字面 {series_lit} 可篡改")
    p2 = Path("/tmp/r10c_rc2_nc2.md")
    p2.write_text(t2)
    r2 = _subprocess_gate(p2)
    if r2.returncode == 0 or "G2" not in r2.stdout:
        fail(f"NC2 未按预期检出（56→66 应 G2 失配 exit 1）："
             f"exit {r2.returncode}\n{r2.stdout[-800:]}")

    for p in (sanity, p1, p2):
        p.unlink(missing_ok=True)
    okmsg(f"NC1 ×3.40→×2.40 ⇒ G2 失配 exit {r1.returncode} 检出 ✓；"
          f"NC2 迭代数 56→66 ⇒ G2 失配 exit {r2.returncode} 检出 ✓"
          "（未篡改副本 exit 0 sanity ✓）")


def run_gate(doc_path: Path, with_nc: bool) -> None:
    print(f"[gate] r10_rc2_gate seed={SEED_GATE}（确定性检查，无随机路径；"
          "零求解零 SDP）", flush=True)
    if not doc_path.exists():
        fail(f"G1 预研文档不在档：{doc_path}")
    doc_text = doc_path.read_text()
    d = load_sources()
    check_g1(doc_text)
    check_g2(doc_text, d)
    check_g3()
    if with_nc:
        run_nc(doc_path)
    print("[gate] 全门 PASS（G1–G3 ＋ NC1/NC2）", flush=True)


def main() -> None:
    ap = argparse.ArgumentParser(description="R10C rc2-engine-survey 验收门")
    ap.add_argument("--doc", default=str(DOC_DEFAULT),
                    help="预研文档路径（默认 notes/rc2-engine-survey.md）")
    ap.add_argument("--no-nc", action="store_true",
                    help="跳过 NC1/NC2（NC 子进程内部用）")
    args = ap.parse_args()
    run_gate(Path(args.doc).resolve(), not args.no_nc)


if __name__ == "__main__":
    main()
