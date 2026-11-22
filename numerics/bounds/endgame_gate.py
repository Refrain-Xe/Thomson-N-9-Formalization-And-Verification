#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""endgame_gate.py — Round 8（campaign 第 3 轮）收口验收门。

裸 python3 运行（无第三方依赖；认证链全部走 Fraction/子进程；CWD 无关——
一切路径由 __file__ 解析）：

    python3 numerics/bounds/endgame_gate.py        # exit 0 = 过门
    python3 thomson-n9/numerics/bounds/endgame_gate.py   # 自会话根（仓外）同效

六项检查（对应任务书 R8-4 验收门①–⑥，Round 8 口径；①②③⑤⑥ 结构性
检查与轮次无关，沿 Round 7，④ 升 Round 8 文档口径，③ 增 round8Inputs/
spliceMapVerdict 完整性）：

  ① endgame_chain.py --reverify-certs 重跑（--out 到临时文件，不动仓库存档）
     须 exit 0——重跑内部对每份被引证书进程外重验证（--verify-cert 或 HP
     reproduce）＋l3/l6/l4_orbit 账本幂等重跑门（含 R8-1/2/3 落盘的新证书
     ——产出自适应，D20 裁决 1），任一失败即 exit 1。
  ② 存档 endgame.json 与重跑产物逐位一致（Fraction）：closed、
     assembledRecord.value（精确分数串逐字符）、blocking、每组件
     id→(rigorous, status, missing, onCriticalPath)、partition 的 region→bound——
     【负对照面】在 tmp 副本把存档 endgame.json 任一组件改 rigorous=true
     （无证书支撑）⇒ ② 比对失配 ⇒ 本门 exit 1（演练于 /tmp，不动仓库）。
  ③ 完整性：
     - 自洽：closed == 全部关键路径组件 rigorous（L4 按 D1/D12 记
       onCriticalPath=false，不入合取，但其处置须在账并有 D1＋D12 引用；
       R7-2 分层记账 layers.exactLayer/stableLayer 的 rigorous 分记在账）；
     - closed=true ⇒ 关键路径组件全 rigorous、assembledRecord ≥ E*
       （Fraction 精确比较；结构性前提见 D19 裁决 3）、每份被引证书在盘
       且其 claimed_bound 与重跑重验（certReverify）一致；
     - closed=false ⇒ blocking 非空且逐项有定量理由串（missing 非空＋
       quant 含数字）；
     - Round 8 增补：round8Inputs 四键（m9_strips/m9_cap/anchor_probe/
       l6_joint）完整且 onDisk 布尔＋note 非空（D20 裁决 1/2 采信口径）；
       spliceMapVerdict.assembled_equal_R7 与 assembledRecord 对 R7 基准
       （47517790735835014335570/1844674407417822803119）的相等性一致；
       assembledRecord 变 ⇒ notes/splice-map.md 须含 v3 节（D16 裁决 5
       逆否——D20 裁决 4）。
  ④ 文档三件（Round 8 口径＋campaign-2 R7 增补式扩展——D27 裁决 5＋R8C-3
     campaign-3 增补式扩展——D29 裁决 5＋R9D campaign-4 增补式扩展——D34
     裁决 4/6＋R10D campaign-5 增补式扩展——D38 裁决 5＋R11D campaign-6
     增补式扩展——D43 裁决 5＋R12C campaign-7 增补式扩展——D49 裁决 3＋
     R13D campaign-8 增补式扩展——D52 裁决 5＋R14B campaign-9 增补式
     扩展——D56 裁决 4＋R15D campaign-10 增补式扩展——D61 裁决 5＋
     R16C campaign-11 增补式扩展——D67 裁决 3＋R17C campaign-12 增补式
     扩展——D72 裁决 3＋R18C campaign-13 增补式扩展——D77 裁决 3/4＋
     R19B campaign-14 增补式扩展——D82 裁决 4＋R20B campaign-15 增补式
     扩展——D86 裁决 4＋R21C campaign-16 增补式扩展——D88 裁决 2/
     D90 裁决 4 同式＋R22C campaign-17 增补式扩展——D96 裁决 4/
     D99 同式＋R23C campaign-18 增补式扩展——D101 裁决 4/
     D103 同式，
     历史检查全保留）：
     GAP-REPORT.md 含 Round 8 节（历史）＋『Round 7（campaign
     dwfrun-41fdc169』campaign-2 节＋『Round 8（campaign dwfrun-41fdc169』
     campaign-3 节＋『Round 9（campaign dwfrun-41fdc169』campaign-4 节＋
     『Round 10（campaign dwfrun-41fdc169』campaign-5 节＋『Round 11
     （campaign dwfrun-41fdc169』campaign-6 节＋『Round 12（campaign
     dwfrun-41fdc169』campaign-7 节＋『Round 13（campaign
     dwfrun-f9904baf』campaign-8 节＋『Round 14（campaign
     dwfrun-f9904baf』campaign-9 节＋『Round 15（campaign
     dwfrun-f9904baf』campaign-10 节＋『Round 16（campaign
     dwfrun-f9904baf』campaign-11 节＋『Round 17（campaign
     dwfrun-f9904baf』campaign-12 节＋『Round 18（campaign
     dwfrun-f9904baf』campaign-13 节＋『Round 19（campaign
     dwfrun-f9904baf』campaign-14 节＋『Round 20（campaign
     dwfrun-f9904baf』campaign-15 节＋『Round 21（campaign
     dwfrun-f9904baf』campaign-16 节＋『Round 22（campaign
     dwfrun-f9904baf』campaign-17 节＋『Round 23（campaign
     dwfrun-f9904baf』campaign-18 本轮节
     （campaign ID＋日期消歧，D29/D34/D38/D43/D49/D52/D56/D61/D67/D72/D77/D82/
     D86/D88-2/D90-4/D96-4/D101-4 裁决 5/6/3/4/5/3/3-4/4/2/4/4）、
     PROGRESS.md 有 Round 8 条目＋campaign-2/3/4/5/6/7/8/9/10/11/12/13/14/15/16/17/18
     本轮条目、notes/decisions.md 含 D19/D20＋D27＋D29＋D34＋D38＋D43＋D49＋
     D52＋D56＋D61＋D67＋D72＋D77＋D82＋D86＋D90＋D96＋D101 锚。
  ③′ campaign-3 R8C 增补（D29 裁决 5，分支自适应）：引擎 v2 产出在盘 ⇒
     holeGapTable v2 三态列完整性（certified/blocked/探针判死）；翻正 ⇒
     v2 证书在 citedCertificates＋分区含 v2 覆盖片（12→13）＋L0 组件 rigorous
     与 v2 证书支撑一致。
  ③ campaign-2 R7 增补：L0.holeGapTable 每行 m10 三态列完整性
     （certified/blocked/未到盘——M10 行在盘时；洞消除 ⇒ 改查 L0 翻绿）。
  ⑤ 负对照：由调用方在 tmp 副本演练（改 rigorous=true 无证书支撑 ⇒
     ② 比对失配 ⇒ exit 1）；本门不自带篡改逻辑。
  ⑥ git status --porcelain 为空（仓库是 git repo 时强制；tmp 副本无 .git
     则记 skip，不弱化真仓库检查）。
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
import tempfile
import time
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]                                    # .../thomson-n9
RESULTS = HERE / "results"
ENDGAME = RESULTS / "endgame.json"
GAP_REPORT = REPO / "GAP-REPORT.md"
PROGRESS = REPO / "PROGRESS.md"
SPLICE_MAP = REPO / "notes" / "splice-map.md"
DECISIONS = REPO / "notes" / "decisions.md"
WORKFLOW_DATA = HERE.parents[2] / "thomson-workflow" / "data" / "energies.json"

COMPONENT_IDS = ["L%d" % i for i in range(8)]


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


# ------------------------------------------------------------------ ① 重跑

def rerun_chain(tmp_out: Path) -> dict:
    cmd = [sys.executable, "numerics/bounds/endgame_chain.py",
           "--reverify-certs", "--out", str(tmp_out)]
    t0 = time.time()
    r = subprocess.run(cmd, cwd=str(REPO), capture_output=True, text=True,
                       timeout=1800)
    print(f"[gate-1] rerun exit={r.returncode} ({time.time()-t0:.1f}s): "
          f"{' '.join(cmd)}", flush=True)
    if r.returncode != 0:
        tail = "\n".join((r.stdout or "").splitlines()[-15:])
        raise GateFail(f"① endgame_chain.py --reverify-certs 重跑 exit "
                       f"{r.returncode}：\n{tail}")
    return load_json(tmp_out)


# ------------------------------------------------------------------ ② 逐位比对

def compare_bitwise(archived: dict, rerun: dict) -> None:
    a, b = archived["endgameChain"], rerun["endgameChain"]
    check(a["closed"] == b["closed"],
          f"② closed 不一致：存档 {a['closed']} vs 重跑 {b['closed']}")
    av, bv = archived["assembledRecord"]["value"], rerun["assembledRecord"]["value"]
    check(av == bv, f"② assembledRecord 分数串不逐位一致：{av} vs {bv}")
    check(frac(av) == frac(bv), "② assembledRecord Fraction 不等（串一致但值不等）")
    check(archived["assembledRecord"]["float"] == rerun["assembledRecord"]["float"],
          "② assembledRecord float 不一致")
    check(a.get("blocking") == b.get("blocking"),
          f"② blocking 不一致：{a.get('blocking')} vs {b.get('blocking')}")
    amap = {c["id"]: c for c in a["components"]}
    bmap = {c["id"]: c for c in b["components"]}
    check(set(amap) == set(bmap) == set(COMPONENT_IDS),
          f"② 组件集不为 L0–L7：{sorted(amap)}")
    for cid in COMPONENT_IDS:
        for k in ("rigorous", "status", "missing", "onCriticalPath"):
            av, bv = amap[cid].get(k), bmap[cid].get(k)
            check(av == bv, f"② 组件 {cid}.{k} 不一致：存档 {av!r} vs 重跑 {bv!r}")
    apart = {r["region"]: r["bound"] for r in archived["partition"]}
    bpart = {r["region"]: r["bound"] for r in rerun["partition"]}
    check(apart == bpart, "② partition 的 region→bound 不一致")
    print("[gate-2] 存档 vs 重跑逐位一致（closed/assembledRecord/blocking/"
          "组件三字段/partition）", flush=True)


# ------------------------------------------------------------------ ③ 完整性

def integrity(archived: dict, rerun: dict, E_star: Fraction) -> None:
    chain = archived["endgameChain"]
    comps = {c["id"]: c for c in chain["components"]}
    check(archived.get("kind") == "n9-endgame-round8",
          f"③ 存档 kind={archived.get('kind')} 非 n9-endgame-round8（Round 8 口径）")
    check(set(comps) == set(COMPONENT_IDS), "③ 组件不是 L0–L7 八件")

    # L4 的 D1/D12 处置（无论 closed 真假都要求在账；R7-2 分层记账在账）
    l4 = comps["L4"]
    check(l4.get("onCriticalPath") is False,
          "③ L4 须按裁决 D1/D12 记 onCriticalPath=false（备选离散路线）")
    disp = json.dumps(l4, ensure_ascii=False)
    check("D1" in disp and "D12" in disp and "备选" in disp,
          "③ L4 处置须引用裁决 D1＋D12 且写明『备选』路线性质")
    layers = l4.get("layers") or {}
    check(set(layers) == {"exactLayer", "stableLayer"},
          "③ L4 须分层记账（layers.exactLayer/stableLayer，R7-2 交付口径）")
    for lname, lay in layers.items():
        check(isinstance(lay.get("rigorous"), bool),
              f"③ L4.layers.{lname} 须分记 rigorous 布尔值")
        check(bool(str(lay.get("gaps") or "").strip()),
              f"③ L4.layers.{lname} 须有 gaps 诚实边界")
    dec = DECISIONS.read_text(encoding="utf-8")
    check("D12" in dec and "D13" in dec,
          "③ notes/decisions.md 缺 D12/D13 裁决（引用失锚）")
    check("D19" in dec and "D20" in dec,
          "③ notes/decisions.md 缺 D19/D20（Round 8 设计＋收口裁决，引用失锚）")

    # campaign-2 R7 增补：holeGapTable m10 三态列完整性（M10 行在盘时——
    # D27 裁决 1 消费面；洞消除（全翻正）⇒ L0 无 holeGapTable，改查 L0
    # 已翻绿——翻绿事实本身由 ② 存档=重跑与 ③ 自洽覆盖）
    _strips = load_json(RESULTS / "strips.json")
    m10_on_disk = (any(r.get("M") == 10 for r in _strips.get("strips", []))
                   or any(b.get("M") == 10
                          for b in _strips.get("blocked", [])))
    if (RESULTS / "hermite_strips.json").exists():
        _hs = load_json(RESULTS / "hermite_strips.json")
        m10_on_disk |= any(r.get("M") == 10 for r in _hs.get("strips", []))
    _l0 = comps["L0"]
    _hgt = _l0.get("holeGapTable")
    if m10_on_disk and isinstance(_hgt, list):
        for _row in _hgt:
            _m10 = _row.get("m10")
            check(isinstance(_m10, dict),
                  f"③ holeGapTable.{_row.get('tag')} 缺 m10 三态列"
                  "（M10 行在盘——D27 消费面）")
            if isinstance(_m10, dict):
                check(isinstance(_m10.get("turnsGreen"), bool),
                      f"③ holeGapTable.{_row.get('tag')}.m10.turnsGreen "
                      "须为布尔")
                _st = str(_m10.get("status") or "")
                check(_st.startswith(("certified", "尝试在盘未翻正", "未到盘")),
                      f"③ holeGapTable.{_row.get('tag')}.m10.status 非三态："
                      f"{_st[:40]}")
    elif m10_on_disk and _hgt is None:
        check(_l0.get("rigorous") is True,
              "③ M10 行在盘但 L0 无 holeGapTable 且未翻绿（洞消除记账失配）")

    # campaign-3 R8C 增补：引擎 v2 消费完整性（D29 裁决 5，分支自适应——
    # v2 产出在盘才检查；探测口径与 endgame_chain.py read_round8/_hole_gap_table
    # 同款：hermite_strips.json 行的 variant 字段或 engine/tag 含 v2 标记）
    v2_rows = []
    _v2_sources = []
    if (RESULTS / "hermite_strips.json").exists():
        _v2_sources.append(RESULTS / "hermite_strips.json")
    if (RESULTS / "hermite_v2_strips.json").exists():        # R8B 独立账本
        _v2_sources.append(RESULTS / "hermite_v2_strips.json")
    for _src in _v2_sources:
        _hs2 = load_json(_src)
        for _r in (_hs2.get("strips", []) + _hs2.get("blocked", [])):
            _m = [str(_r.get("variant") or ""), str(_r.get("engine") or "")]
            _is_v2 = any("v2" in x.lower() or x.lower() in ("contact", "triple")
                         for x in _m if x)
            _od = _r.get("orders")
            if _od is None and isinstance(_r.get("minorant"), dict):
                _od = _r["minorant"].get("orders")
            if not _is_v2 and isinstance(_od, (list, tuple)):
                try:
                    _is_v2 = any(int(x) >= 2 for x in _od)
                except (ValueError, TypeError):
                    pass
            if not _is_v2 and isinstance(_r.get("contact_minus1"), int) \
                    and _r.get("contact_minus1") >= 5:
                _is_v2 = True
            if not _is_v2 and "v2" in str(_r.get("tag") or "").lower():
                _is_v2 = True
            if _is_v2:
                v2_rows.append(_r)
    if v2_rows:
        _v2_cert_rows = [r_ for r_ in v2_rows
                         if r_.get("status") == "certified"
                         and (REPO / str(r_.get("certificate", "§"))).exists()]
        if _v2_cert_rows:
            # 翻正分支：L0 须翻绿（洞消除）＋holeGapTable 无（或行内 v2 列
            # certified）＋v2 证书在 citedCertificates＋分区含 v2 覆盖片
            check(_l0.get("rigorous") is True,
                  "③ v2 certified 行在盘但 L0 未翻绿（v2 消费失配——洞消除"
                  "记账未联动）")
            cited_paths = {e_["path"] for e_ in archived.get("citedCertificates", [])}
            for _vr in _v2_cert_rows:
                _crel = str(_vr.get("certificate"))
                check(_crel in cited_paths,
                      f"③ v2 证书 {_crel} 未入 citedCertificates（翻正分支消费"
                      "不完整）")
            _v2_tags = {r_.get("tag") for r_ in _v2_cert_rows}
            _v2_piece_in_partition = any(
                any(t_ in (r_.get("piece") or "") for t_ in _v2_tags)
                for r_ in archived.get("partition", []))
            check(_v2_piece_in_partition,
                  "③ v2 certified 在盘但 partition 无 v2 覆盖片（分区消费失配）")
        if isinstance(_hgt, list):
            _v2_tags_seen = {r_.get("tag") for r_ in v2_rows}
            for _row in _hgt:
                _v2 = _row.get("v2")
                if _row.get("tag") in _v2_tags_seen:
                    check(isinstance(_v2, dict),
                          f"③ holeGapTable.{_row.get('tag')} 缺 v2 三态列"
                          "（v2 行在盘——D29 裁决 2 消费面）")
                if isinstance(_v2, dict):
                    _st2 = str(_v2.get("status") or "")
                    check(_st2.startswith(("certified", "尝试在盘未翻正",
                                           "探针判死", "相位 0 探针 alive",
                                           "未到盘")),
                          f"③ holeGapTable.{_row.get('tag')}.v2.status "
                          f"非三态：{_st2[:40]}")

    # Round 8 增补：round8Inputs 完整性（D20 裁决 1/2 采信口径）
    r8i = archived.get("round8Inputs") or {}
    for k in ("m9_strips", "m9_cap", "anchor_probe", "l6_joint"):
        v = r8i.get(k)
        check(isinstance(v, dict), f"③ round8Inputs.{k} 缺失或非对象")
        if isinstance(v, dict):
            check(isinstance(v.get("onDisk"), bool),
                  f"③ round8Inputs.{k}.onDisk 须为布尔（在盘/未到盘采信口径）")
            check(bool(str(v.get("note") or "").strip()),
                  f"③ round8Inputs.{k}.note 须非空（未到盘也要如实记）")

    # Round 8 增补：spliceMapVerdict 与 assembledRecord 一致性（D20 裁决 4）
    smv = archived.get("spliceMapVerdict") or {}
    r7_base = frac("47517790735835014335570/1844674407417822803119")
    rec = frac(archived["assembledRecord"]["value"])
    eq = (rec == r7_base)
    check(smv.get("assembled_equal_R7") == eq,
          f"③ spliceMapVerdict.assembled_equal_R7={smv.get('assembled_equal_R7')} "
          f"与实际相等性 {eq} 不符")
    if not eq:
        sm = SPLICE_MAP.read_text(encoding="utf-8")
        check(re.search(r"^#+ .*v3", sm, re.M) is not None,
              "③ assembledRecord 变但 notes/splice-map.md 无 v3 节"
              "（D16 裁决 5 逆否——D20 裁决 4）")

    critical = [c for c in chain["components"]
                if c.get("onCriticalPath", True)]
    check(chain["closed"] == all(c["rigorous"] for c in critical),
          "③ 自洽失败：closed != 关键路径组件全 rigorous")

    cited = archived.get("citedCertificates", [])
    check(isinstance(cited, list) and cited, "③ citedCertificates 为空")

    if chain["closed"]:
        for c in critical:
            check(c["rigorous"], f"③ closed=true 但 {c['id']} 非 rigorous")
        rec = frac(archived["assembledRecord"]["value"])
        check(rec >= E_star,
              f"③ closed=true 但 assembledRecord {float(rec)} < E* {float(E_star)}")
        msg = "③ closed=true：关键路径全 rigorous＋assembledRecord ≥ E* ✓"
    else:
        blocking = chain.get("blocking") or []
        check(len(blocking) > 0, "③ closed=false 但 blocking 为空")
        for cid in blocking:
            c = comps[cid]
            check(bool(str(c.get("missing") or "").strip()),
                  f"③ closed=false 但阻断组件 {cid} 无 missing 说明")
            q = str(c.get("quant") or "")
            check(bool(q.strip()) and re.search(r"\d", q),
                  f"③ 阻断组件 {cid} 的 quant 无定量内容")
        msg = (f"③ closed=false：blocking={blocking} 逐项有定量理由串 ✓"
               "（closed 判定与证据对齐，不硬凑）")

    # 被引证书：在盘＋claimed bound 与账本/重验一致（closed 真假都查）
    rev = rerun.get("certReverify", {})
    for entry in cited:
        path = REPO / entry["path"]
        check(path.exists(), f"③ 被引证书不在盘：{entry['path']}")
        cert = load_json(path)
        cb = frac(cert["claimed_bound"])
        lb = frac(entry["claimed_bound"])
        check(cb == lb, f"③ 证书 {entry['path']} claimed_bound {cert['claimed_bound']}"
                        f" ≠ 账本引用值 {entry['claimed_bound']}")
        key = entry.get("reverifyKey") or entry["path"]
        r = rev.get(key)
        check(isinstance(r, dict),
              f"③ 证书 {entry['path']} 未被重跑 --reverify-certs 覆盖（key={key}）")
        if isinstance(r, dict):
            ok = (r.get("exit") == 0) and (r.get("bitwise_equal_to_archive", True))
            check(ok, f"③ 证书 {entry['path']} 重验未过：{json.dumps(r, ensure_ascii=False)[:300]}")
    print(f"[gate-3] {msg}；被引证书 {len(cited)} 份在盘且 claimed bound 与重验一致",
          flush=True)


# ------------------------------------------------------------------ ④ 文档

def docs_check() -> None:
    gap = GAP_REPORT.read_text(encoding="utf-8")
    check(re.search(r"^#+ .*Round 8", gap, re.M) is not None,
          "④ GAP-REPORT.md 无 Round 8 节")
    prog = PROGRESS.read_text(encoding="utf-8")
    check("Round 8" in prog, "④ PROGRESS.md 无 Round 8 条目")
    dec = DECISIONS.read_text(encoding="utf-8")
    check(re.search(r"^### D2[0-9]", dec, re.M) is not None,
          "④ notes/decisions.md 无 D20+ 执行会话裁决")
    # campaign-2 R7（R7C）增补式检查（D27 裁决 5：Round 8 检查保留——
    # 历史节仍在；新增本轮节检查，campaign ID 消歧）
    check(re.search(r"^#+ Round 7（campaign dwfrun-41fdc169", gap, re.M)
          is not None,
          "④ GAP-REPORT.md 无『Round 7（campaign dwfrun-41fdc169』本轮节"
          "（D27 裁决 5 消歧命名）")
    check("Round 7（campaign dwfrun-41fdc169" in prog,
          "④ PROGRESS.md 无本轮 Round 7（campaign dwfrun-41fdc169）条目")
    check("D27" in dec, "④ notes/decisions.md 缺 D27 锚（本轮设计裁决）")
    # campaign-3 R8C（R8C-3）增补式检查（D29 裁决 5：历史检查全保留——
    # Round 8 节（历史）与 R7 campaign-2 节检查在上方；新增本轮节 regex
    # ＋D29 锚，campaign ID＋日期消歧——『Round 8（campaign 第 3 轮，
    # 2026-10-06）』历史节不匹配本 regex）
    check(re.search(r"^#+ Round 8（campaign dwfrun-41fdc169", gap, re.M)
          is not None,
          "④ GAP-REPORT.md 无『Round 8（campaign dwfrun-41fdc169』本轮节"
          "（D29 裁决 5 消歧命名）")
    check("Round 8（campaign dwfrun-41fdc169" in prog,
          "④ PROGRESS.md 无本轮 Round 8（campaign dwfrun-41fdc169）条目")
    check("D29" in dec, "④ notes/decisions.md 缺 D29 锚（R8 设计裁决）")
    # campaign-4 R9D（本收口）增补式检查（D34 裁决 4/6：增补式扩展先例沿
    # D29 裁决 5——历史检查全保留（Round 8 节历史＋R7 campaign-2＋R8
    # campaign-3 节检查在上方）；新增本轮节 regex＋D34 锚，campaign ID＋
    # 日期消歧——『Round 9（campaign dwfrun-41fdc169 第 4 轮，2026-10-10）』
    # 本轮节）
    check(re.search(r"^#+ Round 9（campaign dwfrun-41fdc169", gap, re.M)
          is not None,
          "④ GAP-REPORT.md 无『Round 9（campaign dwfrun-41fdc169』本轮节"
          "（D34 裁决 6 消歧命名）")
    check("Round 9（campaign dwfrun-41fdc169" in prog,
          "④ PROGRESS.md 无本轮 Round 9（campaign dwfrun-41fdc169）条目")
    check("D34" in dec, "④ notes/decisions.md 缺 D34 锚（R9 设计裁决）")
    # campaign-5 R10D（本收口）增补式检查（D38 裁决 5：增补式扩展先例沿
    # D29 裁决 5/D34 裁决 4——历史检查全保留（Round 8 节历史＋R7 campaign-2
    # ＋R8 campaign-3＋R9 campaign-4 节检查在上方）；新增本轮节 regex＋D38
    # 锚，campaign ID＋日期消歧——『Round 10（campaign dwfrun-41fdc169
    # 第 5 轮，2026-10-10）』本轮节）
    check(re.search(r"^#+ Round 10（campaign dwfrun-41fdc169", gap, re.M)
          is not None,
          "④ GAP-REPORT.md 无『Round 10（campaign dwfrun-41fdc169』本轮节"
          "（D38 裁决 5 消歧命名）")
    check("Round 10（campaign dwfrun-41fdc169" in prog,
          "④ PROGRESS.md 无本轮 Round 10（campaign dwfrun-41fdc169）条目")
    check("D38" in dec, "④ notes/decisions.md 缺 D38 锚（R10 设计裁决）")
    # campaign-6 R11D（本收口）增补式检查（D43 裁决 5：增补式扩展先例沿
    # D29 裁决 5/D34 裁决 4/D38 裁决 5——历史检查全保留（Round 8 节历史＋
    # R7 campaign-2＋R8 campaign-3＋R9 campaign-4＋R10 campaign-5 节检查在
    # 上方）；新增本轮节 regex＋D43 锚，campaign ID＋日期消歧——『Round 11
    # （campaign dwfrun-41fdc169 第 6 轮，2026-10-10）』本轮节）
    check(re.search(r"^#+ Round 11（campaign dwfrun-41fdc169", gap, re.M)
          is not None,
          "④ GAP-REPORT.md 无『Round 11（campaign dwfrun-41fdc169』本轮节"
          "（D43 裁决 5 消歧命名）")
    check("Round 11（campaign dwfrun-41fdc169" in prog,
          "④ PROGRESS.md 无本轮 Round 11（campaign dwfrun-41fdc169）条目")
    check("D43" in dec, "④ notes/decisions.md 缺 D43 锚（R11 设计裁决）")
    # campaign-7 R12C（本收口）增补式检查（D49 裁决 3：增补式扩展先例沿
    # D29 裁决 5/D34 裁决 4/D38 裁决 5/D43 裁决 5——历史检查全保留（Round 8
    # 节历史＋R7 campaign-2＋R8 campaign-3＋R9 campaign-4＋R10 campaign-5＋
    # R11 campaign-6 节检查在上方）；新增本轮节 regex＋D49 锚，campaign ID＋
    # 日期消歧——『Round 12（campaign dwfrun-41fdc169 第 7 轮，2026-10-10）』
    # 本轮节）
    check(re.search(r"^#+ Round 12（campaign dwfrun-41fdc169", gap, re.M)
          is not None,
          "④ GAP-REPORT.md 无『Round 12（campaign dwfrun-41fdc169』本轮节"
          "（D49 裁决 3 消歧命名）")
    check("Round 12（campaign dwfrun-41fdc169" in prog,
          "④ PROGRESS.md 无本轮 Round 12（campaign dwfrun-41fdc169）条目")
    check("D49" in dec, "④ notes/decisions.md 缺 D49 锚（R12 设计裁决）")
    # campaign-8 R13D（本收口）增补式检查（D52 裁决 5：增补式扩展先例沿
    # D29 裁决 5/D34 裁决 4/D38 裁决 5/D43 裁决 5/D49 裁决 3——历史检查全
    # 保留（Round 8 节历史＋R7 campaign-2＋R8 campaign-3＋R9 campaign-4＋
    # R10 campaign-5＋R11 campaign-6＋R12 campaign-7 节检查在上方）；新增
    # 本轮节 regex＋D52 锚，campaign ID＋日期消歧——『Round 13（campaign
    # dwfrun-f9904baf 第 8 轮，2026-10-10）』本轮节）
    check(re.search(r"^#+ Round 13（campaign dwfrun-f9904baf", gap, re.M)
          is not None,
          "④ GAP-REPORT.md 无『Round 13（campaign dwfrun-f9904baf』本轮节"
          "（D52 裁决 5 消歧命名）")
    check("Round 13（campaign dwfrun-f9904baf" in prog,
          "④ PROGRESS.md 无本轮 Round 13（campaign dwfrun-f9904baf）条目")
    check("D52" in dec, "④ notes/decisions.md 缺 D52 锚（R13 设计裁决）")
    # campaign-9 R14B（本收口）增补式检查（D56 裁决 4：增补式扩展先例沿
    # D29 裁决 5/D34 裁决 4/D38 裁决 5/D43 裁决 5/D49 裁决 3/D52 裁决 5——
    # 历史检查全保留（Round 8 节历史＋R7 campaign-2＋R8 campaign-3＋R9
    # campaign-4＋R10 campaign-5＋R11 campaign-6＋R12 campaign-7＋R13
    # campaign-8 节检查在上方）；新增本轮节 regex＋D56 锚，campaign ID＋
    # 日期消歧——『Round 14（campaign dwfrun-f9904baf 第 9 轮，2026-10-11）』
    # 本轮节）
    check(re.search(r"^#+ Round 14（campaign dwfrun-f9904baf", gap, re.M)
          is not None,
          "④ GAP-REPORT.md 无『Round 14（campaign dwfrun-f9904baf』本轮节"
          "（D56 裁决 4 消歧命名）")
    check("Round 14（campaign dwfrun-f9904baf" in prog,
          "④ PROGRESS.md 无本轮 Round 14（campaign dwfrun-f9904baf）条目")
    check("D56" in dec, "④ notes/decisions.md 缺 D56 锚（R14 设计裁决）")
    # campaign-10 R15D（本收口）增补式检查（D61 裁决 5：增补式扩展先例沿
    # D29 裁决 5/D34 裁决 4/D38 裁决 5/D43 裁决 5/D49 裁决 3/D52 裁决 5/
    # D56 裁决 4——历史检查全保留（Round 8 节历史＋R7 campaign-2＋R8
    # campaign-3＋R9 campaign-4＋R10 campaign-5＋R11 campaign-6＋R12
    # campaign-7＋R13 campaign-8＋R14 campaign-9 节检查在上方）；新增
    # 本轮节 regex＋D61 锚，campaign ID＋日期消歧——『Round 15（campaign
    # dwfrun-f9904baf 第 10 轮，2026-10-11）』本轮节）
    check(re.search(r"^#+ Round 15（campaign dwfrun-f9904baf", gap, re.M)
          is not None,
          "④ GAP-REPORT.md 无『Round 15（campaign dwfrun-f9904baf』本轮节"
          "（D61 裁决 5 消歧命名）")
    check("Round 15（campaign dwfrun-f9904baf" in prog,
          "④ PROGRESS.md 无本轮 Round 15（campaign dwfrun-f9904baf）条目")
    check("D61" in dec, "④ notes/decisions.md 缺 D61 锚（R15 设计裁决）")
    # campaign-11 R16C（本收口）增补式检查（D67 裁决 3：增补式扩展先例沿
    # D29 裁决 5/D34 裁决 4/D38 裁决 5/D43 裁决 5/D49 裁决 3/D52 裁决 5/
    # D56 裁决 4/D61 裁决 5——历史检查全保留（Round 8 节历史＋R7 campaign-2
    # ＋R8 campaign-3＋R9 campaign-4＋R10 campaign-5＋R11 campaign-6＋R12
    # campaign-7＋R13 campaign-8＋R14 campaign-9＋R15 campaign-10 节检查在
    # 上方）；新增本轮节 regex＋D67 锚，campaign ID＋日期消歧——『Round 16
    # （campaign dwfrun-f9904baf 第 11 轮，2026-10-11）』本轮节）
    check(re.search(r"^#+ Round 16（campaign dwfrun-f9904baf", gap, re.M)
          is not None,
          "④ GAP-REPORT.md 无『Round 16（campaign dwfrun-f9904baf』本轮节"
          "（D67 裁决 3 消歧命名）")
    check("Round 16（campaign dwfrun-f9904baf" in prog,
          "④ PROGRESS.md 无本轮 Round 16（campaign dwfrun-f9904baf）条目")
    check("D67" in dec, "④ notes/decisions.md 缺 D67 锚（R16 设计裁决）")
    # campaign-12 R17C（本收口）增补式检查（D72 裁决 3：增补式扩展先例沿
    # D29 裁决 5/D34 裁决 4/D38 裁决 5/D43 裁决 5/D49 裁决 3/D52 裁决 5/
    # D56 裁决 4/D61 裁决 5/D67 裁决 3——历史检查全保留（Round 8 节历史＋
    # R7 campaign-2＋R8 campaign-3＋R9 campaign-4＋R10 campaign-5＋R11
    # campaign-6＋R12 campaign-7＋R13 campaign-8＋R14 campaign-9＋R15
    # campaign-10＋R16 campaign-11 节检查在上方）；新增本轮节 regex＋
    # D72 锚，campaign ID＋日期消歧——『Round 17（campaign
    # dwfrun-f9904baf 第 12 轮，2026-10-12）』本轮节）
    check(re.search(r"^#+ Round 17（campaign dwfrun-f9904baf", gap, re.M)
          is not None,
          "④ GAP-REPORT.md 无『Round 17（campaign dwfrun-f9904baf』本轮节"
          "（D72 裁决 3 消歧命名）")
    check("Round 17（campaign dwfrun-f9904baf" in prog,
          "④ PROGRESS.md 无本轮 Round 17（campaign dwfrun-f9904baf）条目")
    check("D72" in dec, "④ notes/decisions.md 缺 D72 锚（R17 设计裁决）")
    # campaign-13 R18C（本收口）增补式检查（D77 裁决 3/4：增补式扩展先例沿
    # D29 裁决 5/D34 裁决 4/D38 裁决 5/D43 裁决 5/D49 裁决 3/D52 裁决 5/
    # D56 裁决 4/D61 裁决 5/D67 裁决 3/D72 裁决 3——历史检查全保留（Round 8
    # 节历史＋R7 campaign-2＋R8 campaign-3＋R9 campaign-4＋R10 campaign-5＋
    # R11 campaign-6＋R12 campaign-7＋R13 campaign-8＋R14 campaign-9＋R15
    # campaign-10＋R16 campaign-11＋R17 campaign-12 节检查在上方）；新增
    # 本轮节 regex＋D77 锚，campaign ID＋日期消歧——『Round 18（campaign
    # dwfrun-f9904baf 第 13 轮，2026-10-12）』本轮节）
    check(re.search(r"^#+ Round 18（campaign dwfrun-f9904baf", gap, re.M)
          is not None,
          "④ GAP-REPORT.md 无『Round 18（campaign dwfrun-f9904baf』本轮节"
          "（D77 裁决 3 消歧命名）")
    check("Round 18（campaign dwfrun-f9904baf" in prog,
          "④ PROGRESS.md 无本轮 Round 18（campaign dwfrun-f9904baf）条目")
    check("D77" in dec, "④ notes/decisions.md 缺 D77 锚（R18 设计裁决）")
    # campaign-14 R19B（本收口）增补式检查（D82 裁决 4：增补式扩展先例沿
    # D29 裁决 5/D34 裁决 4/D38 裁决 5/D43 裁决 5/D49 裁决 3/D52 裁决 5/
    # D56 裁决 4/D61 裁决 5/D67 裁决 3/D72 裁决 3/D77 裁决 3/4——历史检查
    # 全保留（Round 8 节历史＋R7 campaign-2＋R8 campaign-3＋R9 campaign-4＋
    # R10 campaign-5＋R11 campaign-6＋R12 campaign-7＋R13 campaign-8＋R14
    # campaign-9＋R15 campaign-10＋R16 campaign-11＋R17 campaign-12＋R18
    # campaign-13 节检查在上方）；新增本轮节 regex＋D82 锚，campaign ID＋
    # 日期消歧——『Round 19（campaign dwfrun-f9904baf 第 14 轮，2026-10-12）』
    # 本轮节）
    check(re.search(r"^#+ Round 19（campaign dwfrun-f9904baf", gap, re.M)
          is not None,
          "④ GAP-REPORT.md 无『Round 19（campaign dwfrun-f9904baf』本轮节"
          "（D82 裁决 4 消歧命名）")
    check("Round 19（campaign dwfrun-f9904baf" in prog,
          "④ PROGRESS.md 无本轮 Round 19（campaign dwfrun-f9904baf）条目")
    check("D82" in dec, "④ notes/decisions.md 缺 D82 锚（R19 设计裁决）")
    # campaign-15 R20B（本收口）增补式检查（D86 裁决 4：增补式扩展先例沿
    # D29 裁决 5/D34 裁决 4/D38 裁决 5/D43 裁决 5/D49 裁决 3/D52 裁决 5/
    # D56 裁决 4/D61 裁决 5/D67 裁决 3/D72 裁决 3/D77 裁决 3/4/D82 裁决 4
    # ——历史检查全保留（Round 8 节历史＋R7 campaign-2＋R8 campaign-3＋
    # R9 campaign-4＋R10 campaign-5＋R11 campaign-6＋R12 campaign-7＋
    # R13 campaign-8＋R14 campaign-9＋R15 campaign-10＋R16 campaign-11＋
    # R17 campaign-12＋R18 campaign-13＋R19 campaign-14 节检查在上方）；
    # 新增本轮节 regex＋D86 锚，campaign ID＋日期消歧——『Round 20
    # （campaign dwfrun-f9904baf 第 15 轮，2026-10-13）』本轮节）
    check(re.search(r"^#+ Round 20（campaign dwfrun-f9904baf", gap, re.M)
          is not None,
          "④ GAP-REPORT.md 无『Round 20（campaign dwfrun-f9904baf』本轮节"
          "（D86 裁决 4 消歧命名）")
    check("Round 20（campaign dwfrun-f9904baf" in prog,
          "④ PROGRESS.md 无本轮 Round 20（campaign dwfrun-f9904baf）条目")
    check("D86" in dec, "④ notes/decisions.md 缺 D86 锚（R20 设计裁决）")
    # campaign-16 R21C（本收口）增补式检查（D88 裁决 2/D90 裁决 4 同式：
    # 增补式扩展先例沿 D29 裁决 5/D34 裁决 4/D38 裁决 5/D43 裁决 5/
    # D49 裁决 3/D52 裁决 5/D56 裁决 4/D61 裁决 5/D67 裁决 3/D72 裁决 3/
    # D77 裁决 3/4/D82 裁决 4/D86 裁决 4——历史检查全保留（Round 8 节
    # 历史＋R7 campaign-2＋R8 campaign-3＋R9 campaign-4＋R10 campaign-5＋
    # R11 campaign-6＋R12 campaign-7＋R13 campaign-8＋R14 campaign-9＋
    # R15 campaign-10＋R16 campaign-11＋R17 campaign-12＋R18 campaign-13＋
    # R19 campaign-14＋R20 campaign-15 节检查在上方）；新增本轮节 regex
    # ＋D90 锚，campaign ID＋日期消歧——『Round 21（campaign
    # dwfrun-f9904baf 第 16 轮，2026-10-24）』本轮节）
    check(re.search(r"^#+ Round 21（campaign dwfrun-f9904baf", gap, re.M)
          is not None,
          "④ GAP-REPORT.md 无『Round 21（campaign dwfrun-f9904baf』本轮节"
          "（D88-2/D90-4 消歧命名）")
    check("Round 21（campaign dwfrun-f9904baf" in prog,
          "④ PROGRESS.md 无本轮 Round 21（campaign dwfrun-f9904baf）条目")
    check("D90" in dec, "④ notes/decisions.md 缺 D90 锚（R21 设计裁决）")
    # campaign-17 R22C（本收口）增补式检查（D96 裁决 4/D99 同式：增补式
    # 扩展先例沿 D29 裁决 5/D34 裁决 4/D38 裁决 5/D43 裁决 5/D49 裁决 3/
    # D52 裁决 5/D56 裁决 4/D61 裁决 5/D67 裁决 3/D72 裁决 3/D77 裁决 3/4/
    # D82 裁决 4/D86 裁决 4/D88-2/D90-4——历史检查全保留（Round 8 节
    # 历史＋R7 campaign-2＋R8 campaign-3＋R9 campaign-4＋R10 campaign-5＋
    # R11 campaign-6＋R12 campaign-7＋R13 campaign-8＋R14 campaign-9＋
    # R15 campaign-10＋R16 campaign-11＋R17 campaign-12＋R18 campaign-13＋
    # R19 campaign-14＋R20 campaign-15＋R21 campaign-16 节检查在上方）；
    # 新增本轮节 regex＋D96 锚，campaign ID＋日期消歧——『Round 22
    # （campaign dwfrun-f9904baf 第 17 轮，2026-10-24）』本轮节）
    check(re.search(r"^#+ Round 22（campaign dwfrun-f9904baf", gap, re.M)
          is not None,
          "④ GAP-REPORT.md 无『Round 22（campaign dwfrun-f9904baf』本轮节"
          "（D96-4/D99 消歧命名）")
    check("Round 22（campaign dwfrun-f9904baf" in prog,
          "④ PROGRESS.md 无本轮 Round 22（campaign dwfrun-f9904baf）条目")
    check("D96" in dec, "④ notes/decisions.md 缺 D96 锚（R22 设计裁决）")
    # campaign-18 R23C（本收口）增补式检查（D101 裁决 4/D103 同式：增补式
    # 扩展先例沿 D29 裁决 5/D34 裁决 4/D38 裁决 5/D43 裁决 5/D49 裁决 3/
    # D52 裁决 5/D56 裁决 4/D61 裁决 5/D67 裁决 3/D72 裁决 3/D77 裁决 3/4/
    # D82 裁决 4/D86 裁决 4/D88-2/D90-4/D96-4——历史检查全保留（Round 8 节
    # 历史＋R7 campaign-2＋R8 campaign-3＋R9 campaign-4＋R10 campaign-5＋
    # R11 campaign-6＋R12 campaign-7＋R13 campaign-8＋R14 campaign-9＋
    # R15 campaign-10＋R16 campaign-11＋R17 campaign-12＋R18 campaign-13＋
    # R19 campaign-14＋R20 campaign-15＋R21 campaign-16＋R22 campaign-17 节
    # 检查在上方）；新增本轮节 regex＋D101 锚，campaign ID＋日期消歧——
    # 『Round 23（campaign dwfrun-f9904baf 第 18 轮，2026-10-24）』本轮节）
    check(re.search(r"^#+ Round 23（campaign dwfrun-f9904baf", gap, re.M)
          is not None,
          "④ GAP-REPORT.md 无『Round 23（campaign dwfrun-f9904baf』本轮节"
          "（D101-4/D103 消歧命名）")
    check("Round 23（campaign dwfrun-f9904baf" in prog,
          "④ PROGRESS.md 无本轮 Round 23（campaign dwfrun-f9904baf）条目")
    check("D101" in dec, "④ notes/decisions.md 缺 D101 锚（R23 设计裁决）")
    print("[gate-4] GAP-REPORT Round 8 节 ✓ / PROGRESS Round 8 条目 ✓ / "
          "decisions D20+ 在档 ✓＋campaign-2 节（Round 7 campaign "
          "dwfrun-41fdc169）＋D27 锚 ✓＋campaign-3 节（Round 8 campaign "
          "dwfrun-41fdc169）＋D29 锚 ✓＋campaign-4 节（Round 9 campaign "
          "dwfrun-41fdc169）＋D34 锚 ✓＋campaign-5 节（Round 10 campaign "
          "dwfrun-41fdc169）＋D38 锚 ✓＋campaign-6 节（Round 11 campaign "
          "dwfrun-41fdc169）＋D43 锚 ✓＋campaign-7 节（Round 12 campaign "
          "dwfrun-41fdc169）＋D49 锚 ✓＋campaign-8 节（Round 13 campaign "
          "dwfrun-f9904baf）＋D52 锚 ✓＋campaign-9 节（Round 14 campaign "
          "dwfrun-f9904baf）＋D56 锚 ✓＋campaign-10 节（Round 15 campaign "
          "dwfrun-f9904baf）＋D61 锚 ✓＋campaign-11 节（Round 16 campaign "
          "dwfrun-f9904baf）＋D67 锚 ✓＋campaign-12 节（Round 17 campaign "
          "dwfrun-f9904baf）＋D72 锚 ✓＋campaign-13 节（Round 18 campaign "
          "dwfrun-f9904baf）＋D77 锚 ✓＋campaign-14 节（Round 19 campaign "
          "dwfrun-f9904baf）＋D82 锚 ✓＋campaign-15 节（Round 20 campaign "
          "dwfrun-f9904baf）＋D86 锚 ✓＋campaign-16 节（Round 21 campaign "
          "dwfrun-f9904baf）＋D90 锚 ✓＋campaign-17 节（Round 22 campaign "
          "dwfrun-f9904baf）＋D96 锚 ✓＋campaign-18 节（Round 23 campaign "
          "dwfrun-f9904baf）＋D101 锚 ✓",
          flush=True)


# ------------------------------------------------------------------ ⑥ git

def git_clean() -> None:
    if not (REPO / ".git").exists():
        print("[gate-6] skip：非 git 仓库（tmp 副本演练口径）", flush=True)
        return
    r = subprocess.run(["git", "status", "--porcelain"], cwd=str(REPO),
                       capture_output=True, text=True, timeout=60)
    check(r.returncode == 0, f"⑥ git status 失败：{r.stderr}")
    check(r.stdout.strip() == "",
          f"⑥ 工作树不干净：\n{r.stdout}")
    print("[gate-6] git status --porcelain 为空 ✓", flush=True)


# ----------------------------------------------------------------------- main

def main() -> int:
    t0 = time.time()
    energies = load_json(WORKFLOW_DATA)["energies"]["9"]
    E_star = frac(energies["value"])
    archived = load_json(ENDGAME)
    print(f"[gate] E* = {E_star}（{WORKFLOW_DATA}）；存档 endgame.json "
          f"closed={archived['endgameChain']['closed']} "
          f"assembledRecord={archived['assembledRecord']['float']}", flush=True)

    with tempfile.TemporaryDirectory(prefix="endgame_gate_") as td:
        tmp_out = Path(td) / "endgame_rerun.json"
        rerun = rerun_chain(tmp_out)                    # ①
        compare_bitwise(archived, rerun)                # ②
        integrity(archived, rerun, E_star)              # ③
    docs_check()                                        # ④
    git_clean()                                         # ⑥
    print(f"[gate] PASS（{time.time()-t0:.1f}s）——exit 0", flush=True)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except GateFail as e:
        print(f"[gate] FAIL：{e}", flush=True)
        print("[gate] exit 1", flush=True)
        sys.exit(1)
