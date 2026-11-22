#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r8c3_closure_gate.py — R8C 收口验收门（campaign dwfrun-41fdc169 第 3 轮）。

裸 python3 运行（无第三方依赖；CWD 无关——一切路径由 __file__ 解析；
仓外路由沿 R7B bd15f27／R7C e53952c 嵌套包装器先例）：

    python3 numerics/bounds/r8c3_closure_gate.py            # 仓内
    python3 thomson-n9/numerics/bounds/r8c3_closure_gate.py # campaign 根

固定种子 20261010（D29 任务书条款）。七项检查（对应 R8C 任务书验收判据
①–⑥＋负对照；数学内容与在盘证据逐项对齐、与分支自适应——翻正/未翻正
两分支各自定量断言）：

  C1 r8c3_l2m9_gate.py 复跑 exit 0（R8A 交付门——L2 cap M9 新口径）。
  C2 r8c3_engine_gate.py 复跑 exit 0（R8B 交付门——引擎 v2 条件阶梯）。
  C3 文档三件在档：GAP-REPORT「Round 8（campaign dwfrun-41fdc169 第 3 轮，
     2026-10-09）」节（与历史「Round 8（campaign 第 3 轮，2026-10-06）」节
     campaign ID＋日期消歧并存）＋PROGRESS 置顶条目＋decisions D29 结果
     追加回填（『D29 结果』或等价回填节在档）。
  C4 endgame.json 终态与在盘证据逐项对齐（Fraction 精确）：
     - closed == 关键路径合取（自洽）＋ closed 预期 false（L3 永久开放——
       dead-at-(9,6) D24/D25；新 ε_forcing ≫ ε_W；L6 仍缺）；
     - 铁律 assembledRecord ≤ E*+1e-6（精确 Fraction）；
     - assembledRecord == min(分区 bound)（精确重算）；
     - 分支断言（按 v2 在盘状态自适应）：
       翻正（v2 certified 行在盘）：blocking == [L3]、L0.rigorous=True、
         assembledRecord == typed cap m0748 M9 certified（typed_ladder.json
         rung 精确分数）、v2 证书 ∈ citedCertificates、分区含 v2 覆盖片、
         notes/splice-map.md 含 v3 节（D20 裁决 4）；
       未翻正（v2 blocked/探针判死）：blocking == [L0, L3]、
         assembledRecord == R7 存档值 47517790735835014335570/
         1844674407417822803119、splice-map 无 v3 节（维持 v2）、
         holeGapTable 每行 v2 三态列与在盘 v2 行一致；
     - L2 口径联动：l2_rigorous.json 的输入证书＝cap m0748_M9（R8A 交付，
       M8 旧口径已换记）且 endgame L2 quant 串与账本 ε_forcing 数值一致；
     - citedCertificates 每份在盘且 claimed_bound 与证书一致。
  C5 预算复盘：本轮 Σsolve_s/10800 ≤ 9.30（R8A/R8C 零求解＋R8B 战役账本
     逐解合计）＋campaign 累计 ≤ 40 当量（m9_campaign＋m10_campaign＋cap
     M9 typed 解＋R8B Σsolve_s）＋R8B 相位事件流一致（相位 0→1→2 单调、
     相位 2 仅在 X9 触发条件下启动）。
  C6 git status --porcelain 为空（真仓库强制；tmp 副本无 .git 记 skip）。
  C7 负对照（由调用方在 /tmp 选择性副本演练：翻正分支 L0.rigorous 改 true
     而无证书支撑 ⇒ endgame_gate gate-② 失配；未翻正分支 blocking 改 [] ⇒
     gate-③ 失配；本门不自带篡改逻辑——负对照面留档 GAP-REPORT 本轮节）。

exit 0 = 过门；任一失败 exit 1（信息含检查号与定量内容）。
"""
from __future__ import annotations

import json
import random
import re
import subprocess
import sys
import time
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]                                    # .../thomson-n9
RESULTS = HERE / "results"
ENDGAME = RESULTS / "endgame.json"
TYPED_LADDER = RESULTS / "typed_ladder.json"
L2_RIG = RESULTS / "l2_rigorous.json"
HERMITE_STRIPS = RESULTS / "hermite_strips.json"
M9_CAMPAIGN = RESULTS / "m9_campaign.json"
M10_CAMPAIGN = RESULTS / "m10_campaign.json"
GAP_REPORT = REPO / "GAP-REPORT.md"
PROGRESS = REPO / "PROGRESS.md"
DECISIONS = REPO / "notes" / "decisions.md"
SPLICE_MAP = REPO / "notes" / "splice-map.md"
WORKFLOW_DATA = HERE.parents[2] / "thomson-workflow" / "data" / "energies.json"

SEED = 20261010
EQUIV_UNIT_S = 10800                       # 当量单位（m9_campaign 口径）
ROUND_BUDGET_EQ = Fraction(930, 100)       # 本轮红线 ≤ 9.30 当量（D29 裁决 6）
CAMPAIGN_BUDGET_EQ = Fraction(40)          # campaign 累计 ≤ 40 当量
R7_ASSEMBLED = "47517790735835014335570/1844674407417822803119"
TOL_ESTAR = Fraction(1, 10**6)

R8A_GATE = HERE / "r8c3_l2m9_gate.py"
R8B_GATE = HERE / "r8c3_engine_gate.py"


class GateFail(Exception):
    pass


def check(cond: bool, msg: str) -> None:
    if not cond:
        raise GateFail(msg)


def load_json(path: Path):
    with open(path) as f:
        return json.load(f)


def frac(s) -> Fraction:
    return Fraction(str(s))


def _v2_variant_of(row) -> str | None:
    for k in ("variant", "minorant_variant", "engine"):
        v = str(row.get(k) or "").strip().lower()
        if v and ("v2" in v or v in ("contact", "triple")):
            return str(row.get(k))
    od = row.get("orders")
    if not od and isinstance(row.get("minorant"), dict):
        od = row["minorant"].get("orders")
    if isinstance(od, (list, tuple)):
        try:
            if any(int(x) >= 2 for x in od):
                return "triple"
        except (ValueError, TypeError):
            pass
    cm = row.get("contact_minus1")
    if isinstance(cm, int) and cm >= 5:
        return "contact"
    tg = str(row.get("tag") or "").lower()
    if "v2" in tg:
        return "v2"
    return None


def v2_rows_on_disk():
    """(cert_rows, blocked_rows)——hermite_strips.json ∪ hermite_v2_strips.json
    （R8B 独立账本）的 v2 行（D29 裁决 2）。"""
    cert_rows, blocked_rows = [], []
    _seen = set()
    for src in (HERMITE_STRIPS, RESULTS / "hermite_v2_strips.json"):
        if not src.exists():
            continue
        d = load_json(src)
        for r in d.get("strips", []):
            if _v2_variant_of(r) is None:
                continue
            _key = (r.get("tag"), r.get("M"), str(_v2_variant_of(r)))
            if _key in _seen:
                continue
            _seen.add(_key)
            if r.get("status") == "certified" and \
                    (REPO / str(r.get("certificate", "§"))).exists():
                cert_rows.append(r)
            else:
                blocked_rows.append(r)
    return cert_rows, blocked_rows


def find_v2_ledgers():
    """R8B 战役/事件账本（文件名含 v2 的 results/*.json）。"""
    out = []
    for p in sorted(RESULTS.glob("*.json")):
        if p.name == "endgame.json" or "v2" not in p.name.lower():
            continue
        try:
            d = load_json(p)
        except Exception:                                   # noqa: BLE001
            continue
        if isinstance(d, dict) and ("v2" in p.name.lower()
                                    or "v2" in str(d.get("kind", "")).lower()):
            out.append((f"results/{p.name}", d))
    return out


# ------------------------------------------------------------------ C1/C2 子门

def run_subgate(path: Path, tag: str) -> None:
    check(path.exists(), f"{tag} 子门不在盘：{path}")
    t0 = time.time()
    r = subprocess.run([sys.executable, str(path)], capture_output=True,
                       text=True, timeout=1800, cwd=str(REPO))
    tail = "\n".join((r.stdout or "").splitlines()[-6:])
    print(f"[{tag}] exit={r.returncode} ({time.time()-t0:.1f}s)：{path.name}",
          flush=True)
    check(r.returncode == 0,
          f"{tag} 子门复跑 exit {r.returncode}：\n{tail}")


# ------------------------------------------------------------------ C3 文档

def docs_check() -> dict:
    gap = GAP_REPORT.read_text(encoding="utf-8")
    prog = PROGRESS.read_text(encoding="utf-8")
    dec = DECISIONS.read_text(encoding="utf-8")
    # 本轮节（campaign ID＋日期消歧——历史「Round 8（campaign 第 3 轮，
    # 2026-10-06）」节不匹配本 regex）
    check(re.search(r"^#+ Round 8（campaign dwfrun-41fdc169 第 3 轮，2026-10-09",
                    gap, re.M) is not None,
          "C3 GAP-REPORT.md 无『Round 8（campaign dwfrun-41fdc169 第 3 轮，"
          "2026-10-09）』本轮节（D29 裁决 5 命名）")
    check(re.search(r"^#+ Round 8（campaign 第 3 轮，2026-10-06", gap, re.M)
          is not None,
          "C3 GAP-REPORT.md 历史节『Round 8（campaign 第 3 轮，2026-10-06）』"
          "缺失（append-only 消歧并存条款）")
    # PROGRESS 置顶条目：本轮条目在文件前 120 行内（置顶口径）
    head = prog.splitlines()[:120]
    check(any("Round 8（campaign dwfrun-41fdc169" in ln for ln in head),
          "C3 PROGRESS.md 前 120 行无本轮（campaign dwfrun-41fdc169）置顶条目")
    # decisions D29 结果追加回填：D29 节存在＋其后有结果回填标记
    m = re.search(r"^### D29（", dec, re.M)
    check(m is not None, "C3 notes/decisions.md 无 D29 节")
    d29_tail = dec[m.start():]
    backfill = re.search(r"D29[- ]?(结果|执行留痕|结果追加)", d29_tail)
    # 回填形态宽容：D29 节内含『结果』小节或 D29-结果 独立节
    check(backfill is not None
          or re.search(r"^#+ .*D29.*结果", d29_tail, re.M) is not None,
          "C3 notes/decisions.md D29 无结果追加回填（任务书③条款）")
    return {"gap_report_round": True, "progress_top": True,
            "d29_backfill": True}


# ------------------------------------------------------------------ C4 终态对齐

def alignment_check(E_star: Fraction) -> dict:
    d = load_json(ENDGAME)
    ec = d["endgameChain"]
    comps = {c["id"]: c for c in ec["components"]}
    cited = d.get("citedCertificates", [])

    # 自洽＋closed 语义
    critical = [c for c in ec["components"] if c.get("onCriticalPath", True)]
    check(ec["closed"] == all(c["rigorous"] for c in critical),
          "C4 closed != 关键路径合取（自洽失败）")
    check(ec["closed"] is False,
          "C4 closed 预期 false（L3 永久开放——dead-at-(9,6) D24/D25；任务书"
          "『不硬凑』条款；若证据翻正到 closed=true 须先复核本门全部断言）")
    # 铁律：assembledRecord ≤ E*+1e-6（TTP-covering 证书口径）
    rec = frac(d["assembledRecord"]["value"])
    check(rec <= E_star + TOL_ESTAR,
          f"C4 铁律违例：assembledRecord {float(rec)} > E*+1e-6")
    # assembledRecord == min(分区 bound) 精确重算
    part_bounds = [frac(r["bound"]) for r in d["partition"]]
    check(rec == min(part_bounds),
          "C4 assembledRecord != min(分区 bound)（精确 Fraction 重算）")
    # 分区无缝盖满 [−1,1]
    rs = sorted(d["partition"], key=lambda r: frac(r["region"].split(",")[0][1:]))
    cur = Fraction(-1)
    for r in rs:
        lo = frac(r["region"].split(",")[0][1:])
        hi = frac(r["region"].split(",")[1][:-1])
        check(lo == cur, f"C4 分区不连续：期望 {cur}，实为 {lo}")
        cur = hi
    check(cur == Fraction(1), f"C4 分区未盖满 [−1,1]，止于 {cur}")
    # citedCertificates 每份在盘＋claimed_bound 一致
    for e in cited:
        p = REPO / e["path"]
        check(p.exists(), f"C4 被引证书不在盘：{e['path']}")
        cb = frac(load_json(p)["claimed_bound"])
        check(cb == frac(e["claimed_bound"]),
              f"C4 证书 {e['path']} claimed_bound 与账本引用值不等")

    # L2 口径联动（R8A 交付）：l2_rigorous.json 输入证书＝cap M9
    l2 = load_json(L2_RIG)
    l2_inputs = json.dumps(l2.get("inputs", {}), ensure_ascii=False)
    check("M9" in l2_inputs or "m0748_M9" in l2_inputs,
          "C4 l2_rigorous.json 输入证书非 cap m0748_M9（R8A 口径换记未落地）")
    l2_eps = frac(l2["eps_forcing"]["exact"])
    l2_comp = comps["L2"]
    check(l2_comp["rigorous"] is True, "C4 L2 组件非 rigorous（R8A 后应绿）")
    check(f"{l2['eps_forcing']['float']:.6e}" in l2_comp["quant"],
          f"C4 endgame L2 quant 未反映账本 ε_forcing="
          f"{l2['eps_forcing']['float']:.6e}（消费链联动失配）")
    # L3 预期 blocked 且 quant 定量
    check(comps["L3"]["rigorous"] is False, "C4 L3 预期 blocked（永久开放）")
    check(re.search(r"\d", str(comps["L3"].get("quant") or "")),
          "C4 L3 quant 无定量内容")

    # 分支自适应断言
    v2_cert, v2_blk = v2_rows_on_disk()
    flipped = bool(v2_cert)
    if flipped:
        check(ec["blocking"] == ["L3"],
              f"C4 翻正分支 blocking 预期 [L3]，实为 {ec['blocking']}")
        check(comps["L0"]["rigorous"] is True,
              "C4 翻正分支 L0 未翻绿（v2 certified 在盘——洞消除）")
        ladder = load_json(TYPED_LADDER)
        m9_rung = next(r for r in ladder["rungs"]
                       if r.get("tag") == "m0748" and r.get("M") == 9)
        check(rec == frac(m9_rung["certified"]),
              f"C4 翻正分支 assembledRecord {float(rec)} != typed cap M9 值 "
              f"{float(frac(m9_rung['certified']))}（任务书定量断言）")
        cited_paths = {e["path"] for e in cited}
        for r in v2_cert:
            check(str(r["certificate"]) in cited_paths,
                  f"C4 v2 证书 {r['certificate']} 未入 citedCertificates")
        v2_tags = {r["tag"] for r in v2_cert}
        check(any(any(t in (p.get("piece") or "") for t in v2_tags)
                  for p in d["partition"]),
              "C4 翻正分支分区无 v2 覆盖片")
        sm = SPLICE_MAP.read_text(encoding="utf-8")
        check(re.search(r"^#+ .*v3", sm, re.M) is not None,
              "C4 翻正分支 splice-map.md 无 v3 节（D20 裁决 4——D16 裁决 5 "
              "逆否）")
        check(d["spliceMapVerdict"]["assembled_equal_R7"] is False,
              "C4 翻正分支 spliceMapVerdict.assembled_equal_R7 应为 False")
        # 翻绿须有证书支撑：L0.green 的每一洞片都有 certified>E* 行
        for r in v2_cert:
            check(frac(r["certified"]) > E_star,
                  f"C4 v2 行 {r['tag']} certified ≤ E*（翻绿无支撑）")
    else:
        check(ec["blocking"] == ["L0", "L3"],
              f"C4 未翻正分支 blocking 预期 [L0, L3]，实为 {ec['blocking']}")
        check(comps["L0"]["rigorous"] is False,
              "C4 未翻正分支 L0 不应翻绿（无 v2 certified 行在盘）")
        check(rec == frac(R7_ASSEMBLED),
              f"C4 未翻正分支 assembledRecord 预期 R7 存档值，实为 {rec}")
        sm = SPLICE_MAP.read_text(encoding="utf-8")
        v3_secs = re.findall(r"^#+ .*v3", sm, re.M)
        check(not v3_secs,
              "C4 未翻正分支 splice-map.md 不应有 v3 节（assembledRecord 未变"
              "——D20 裁决 4 维持 v2）")
        check(d["spliceMapVerdict"]["assembled_equal_R7"] is True,
              "C4 未翻正分支 spliceMapVerdict.assembled_equal_R7 应为 True")
        hgt = comps["L0"].get("holeGapTable")
        v2_all = {r["tag"] for r in (v2_cert + v2_blk)}
        if v2_all or find_v2_ledgers():
            check(isinstance(hgt, list) and hgt,
                  "C4 v2 产出在盘但 L0 无 holeGapTable（记账失配）")
            for row in (hgt or []):
                check(isinstance(row.get("v2"), dict),
                      f"C4 holeGapTable.{row.get('tag')} 缺 v2 三态列"
                      "（D29 裁决 2 消费面）")
    return {"flipped": flipped, "assembled": str(rec),
            "blocking": ec["blocking"], "n_cited": len(cited),
            "eps_forcing": str(l2_eps)}


# ------------------------------------------------------------------ C5 预算

def budget_check() -> dict:
    solve_s = 0.0
    sources = []
    # m9_campaign（campaign 第 1 轮）＋m10_campaign（第 2 轮 Lukács 片）：
    # budget.total_solve_s（两账本同字段名，D22 裁决 1/m10 同款 schema）
    for path, tag in ((M9_CAMPAIGN, "m9_campaign"),
                      (M10_CAMPAIGN, "m10_campaign")):
        check(path.exists(), f"C5 {tag}.json 不在盘")
        d = load_json(path)
        b = d.get("budget", {})
        s = None
        for k in ("total_solve_s", "solve_s", "sum_solve_s"):
            if b.get(k) is not None:
                s = float(b[k])
                break
        check(s is not None,
              f"C5 {tag}.json budget 无 total_solve_s 字段（口径缺件）")
        solve_s += s
        sources.append((tag, s))
    # cap m0748 M9 typed 解（R7B，sdpa.solve_s=42305.7——typed_ladder rung）
    ladder = load_json(TYPED_LADDER)
    m9_rung = next(r for r in ladder["rungs"]
                   if r.get("tag") == "m0748" and r.get("M") == 9)
    cap_s = (m9_rung.get("sdpa") or {}).get("solve_s")
    check(cap_s is not None,
          "C5 typed_ladder.json m0748 M9 rung 无 sdpa.solve_s 字段"
          "（campaign 累计口径缺件）")
    solve_s += float(cap_s)
    sources.append(("cap_m0748_M9_typed", float(cap_s)))
    # R8B 战役账本（本轮唯一求解线）：v2 行（hermite_v2_strips.json 的
    # strips[] / 任何 v2 战役账本的 rows[]）逐行 sdpa.solve_s/solve_s 合计；
    # 相位 0 构造/探针/烟测不计（0 当量口径——D29 裁决 2）
    r8b_s = 0.0
    r8b_rows_seen = 0
    declared_totals = []
    for w, d in find_v2_ledgers():
        for row in (list(d.get("rows", []) or [])
                    + list(d.get("strips", []) or [])):
            if not isinstance(row, dict):
                continue
            s = None
            if isinstance(row.get("sdpa"), dict):
                s = row["sdpa"].get("solve_s")
            if s is None:
                s = row.get("solve_s") or row.get("wall_s")
            if s is not None:
                r8b_s += float(s)
                r8b_rows_seen += 1
        b = d.get("budget", {})
        for k in ("total_solve_s", "solve_s", "sum_solve_s", "solve_s_total"):
            if b.get(k) is not None:
                declared_totals.append((w, float(b[k])))
                break
    # 声明值与逐行合计交叉核对（跨账本合计后统一比对——不静默取大取小）
    for w, dv in declared_totals:
        check(abs(dv - r8b_s) < 1.0,
              f"C5 R8B 账本 {w} 声明 Σsolve_s={dv} 与逐行合计 "
              f"{r8b_s} 不一致")
    solve_s += r8b_s
    sources.append(("r8b_engine_v2", r8b_s))
    round_eq = Fraction(int(round(r8b_s * 1000)), 1000) / EQUIV_UNIT_S
    total_eq = Fraction(int(round(solve_s * 1000)), 1000) / EQUIV_UNIT_S
    check(round_eq <= ROUND_BUDGET_EQ,
          f"C5 本轮预算超线：Σsolve_s={r8b_s}s={float(round_eq):.3f} 当量 > "
          f"{float(ROUND_BUDGET_EQ)}（D29 裁决 6）")
    check(total_eq <= CAMPAIGN_BUDGET_EQ,
          f"C5 campaign 累计超线：Σ={solve_s}s={float(total_eq):.3f} 当量 > 40")
    # R8B 相位事件流一致性：相位 0→1→2 单调＋相位 2 仅在触发条件下启动
    # （账本形态宽容：{phases:{phase0..}} 或顶层 phase0/phase1/phase2——
    # hermite_v2_campaign_state.json 为顶层形态）
    phase_stream_ok = True
    phase_detail = []
    for w, d in find_v2_ledgers():
        ph = d.get("phases")
        if not isinstance(ph, dict):
            ph = d if any(k in d for k in ("phase0", "phase1", "phase2")) else {}
        if not ph:
            continue
        seq = []
        for i in (0, 1, 2):
            p = ph.get(f"phase{i}") or {}
            st = (p.get("status") or p.get("outcome")
                  or ("launched" if p.get("launched") else
                      ("not_launched" if "launched" in p else "")))
            seq.append(str(st))
            phase_detail.append((w, f"phase{i}", str(st)[:40]))
        started = [i for i, s in enumerate(seq)
                   if s and not s.startswith(("not_", "null", "None", "false"))]
        if started != sorted(started) or (
                len(started) > 1 and started != list(range(min(started),
                                                           min(started)
                                                           + len(started)))):
            phase_stream_ok = False
        p2 = ph.get("phase2") or {}
        p2_on = bool(p2.get("launched")) or str(
            p2.get("status") or p2.get("outcome") or "") not in (
                "", "None", "null", "not_launched", "not_started",
                "not_triggered")
        if p2_on:
            trig = p2.get("trigger_eval") or p2.get("trigger") or p2.get("X9")
            if trig is None:
                phase_stream_ok = False
                phase_detail.append((w, "phase2", "启动但无触发器记录"))
    check(phase_stream_ok,
          f"C5 R8B 相位事件流不一致：{phase_detail}")
    return {"round_solve_s": r8b_s, "round_eq": float(round_eq),
            "campaign_solve_s": solve_s, "campaign_eq": float(total_eq),
            "sources": sources, "phases": phase_detail}


# ------------------------------------------------------------------ C6 git

def git_clean() -> None:
    if not (REPO / ".git").exists():
        print("[C6] skip：非 git 仓库（tmp 副本演练口径）", flush=True)
        return
    r = subprocess.run(["git", "status", "--porcelain"], cwd=str(REPO),
                       capture_output=True, text=True, timeout=60)
    check(r.returncode == 0, f"C6 git status 失败：{r.stderr}")
    check(r.stdout.strip() == "", f"C6 工作树不干净：\n{r.stdout}")
    print("[C6] git status --porcelain 为空 ✓", flush=True)


# ----------------------------------------------------------------------- main

def main() -> int:
    random.seed(SEED)                      # 固定种子（任务书条款；本门确定性）
    t0 = time.time()
    energies = load_json(WORKFLOW_DATA)["energies"]["9"]
    E_star = frac(energies["value"])
    d = load_json(ENDGAME)
    v2_cert, v2_blk = v2_rows_on_disk()
    print(f"[gate] E* = {E_star}；seed = {SEED}；分支探测：v2 certified "
          f"{len(v2_cert)} 行 / blocked {len(v2_blk)} 行 ⇒ "
          f"{'翻正' if v2_cert else '未翻正'}分支；存档 closed="
          f"{d['endgameChain']['closed']} assembledRecord="
          f"{d['assembledRecord']['float']}", flush=True)

    run_subgate(R8A_GATE, "C1")                            # C1
    run_subgate(R8B_GATE, "C2")                            # C2
    docs = docs_check()                                    # C3
    align = alignment_check(E_star)                        # C4
    budget = budget_check()                                # C5
    git_clean()                                            # C6
    print(f"[gate] C3 文档三件 ✓（{docs}）", flush=True)
    print(f"[gate] C4 终态对齐 ✓（分支={'翻正' if align['flipped'] else '未翻正'}，"
          f"blocking={align['blocking']}，cited={align['n_cited']} 份，"
          f"ε_forcing={align['eps_forcing'][:60]}…）", flush=True)
    print(f"[gate] C5 预算 ✓（本轮 {budget['round_solve_s']}s="
          f"{budget['round_eq']:.3f} 当量 ≤ 9.30；campaign 累计 "
          f"{budget['campaign_solve_s']}s={budget['campaign_eq']:.3f}/40 当量；"
          f"相位流 {len(budget['phases'])} 条记录一致）", flush=True)
    print(f"[gate] PASS（{time.time()-t0:.1f}s）——exit 0（负对照 C7 由调用方"
          f"在 /tmp 选择性副本演练，结果入 GAP-REPORT 本轮节）", flush=True)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except GateFail as e:
        print(f"[gate] FAIL：{e}", flush=True)
        print("[gate] exit 1", flush=True)
        sys.exit(1)
