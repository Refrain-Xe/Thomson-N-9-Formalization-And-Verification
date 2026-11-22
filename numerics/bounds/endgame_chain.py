#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""endgame_chain.py — Round 8（campaign 第 3 轮）收口链装配与闭合判定（v3）。

架构 C（B 几何骨架＋KLT Hermite 引擎，notes/architecture-decision.md §2）。
闭合主链按裁决 D1/D12（notes/decisions.md §1-D1、§D12）记 **L2→L3→L5→L6**
（L5＝Procrustes 已严格；重构走 Gram 扰动→d_P≤C·δ→管内二次增长）；
账本 L4（组合刚性/邻型计数）按 D1/D12/D16 裁决 3 记 onCriticalPath=false
（备选离散路线，不在闭合关键路径，处置条目引用 decisions.md D12；R7-2 已
交付精确层＋稳定层，分层 rigorous 如实分记——见组件条目）。

v3（Round 8）相对 v2.x（Round 7，commit 898c522）的消费性更新（裁决 D19
设计＋D20 收口时序）：
  • **产出自适应消费（D20 裁决 1/2）**：R8-1/2/3 与本收口并行调度，其产出
    落盘时点不受本会话控制 ⇒ 三类产出全部「在盘则入账、未到盘则如实记
    missing＋维持 Round 7 记账值」，探测走既有账本 schema（新证书＝旧账本
    加行/加 rung 的 R6/R7 先例）：
    - R8-1 洞三片 M9（Lukács→results/strips.json strips[] M=9 行；a5→
      results/hermite_strips.json M=9 且 status=certified 行）：coverage()
      原子胞元取覆盖最大界的既有逻辑自动消费（certified > E* 的行自动消除
      对应洞）⇒ L0 逐片重记账；
    - R8-1 cap M9（results/typed_ladder.json rungs[] tag=m0748 M=9）：
      参与多引擎取最优（D10/D16 裁决 2 同规则，参与条件＝证书在盘＋可
      --verify-cert）；cap 换记 ⇒ L2/L3 的 ε_forcing 口径牵动按 D20 裁决 3
      如实标注（不以旧口径冒充）；
    - R8-3 L6 联合界（results/l6_intube.json quadraticGrowth.rigorousRadius
      新值）：read_l6 既有采信门（负对照 4/4＋μ>0）自动消费；
    - R8-2 锚定精确取等探针（alive/dead、dist、M-scaling）：多形态宽容
      探测，结果入 round8Inputs 与 L3 组件 narrative——探针产出不改变
      任何组件 rigorous 布尔（closed 语义只认关键路径全 rigorous＋
      assembledRecord ≥ E*，D19 裁决 3）。
  • closed 重试判定：closed=true 仅当关键路径全 rigorous 且
    assembledRecord ≥ E*（含 TTP 区域证书 ≥ E* 的结构性前提见 D19 裁决 3）；
    预期 false 时 blocking 逐项定量（L0 余片缺口、L3 精确取等 dist 与 L6
    ε* 缺口以 R8-2/R8-3 新值刷新——新值未到盘则按 D20 裁决 2 维持 R7 值
    并标注）。
  • splice-map 联动机器判定（D20 裁决 4）：assembledRecord 与 R7 存档值
    Fraction 逐位比较——相等 ⇒ splice-map 维持 v2（账本记 spliceMapVerdict）；
    变 ⇒ splice-map 需出 v3 同步（D16 裁决 5 逆否，由收口会话同步落笔）。
  • L4 分层记账维持 D16 裁决 3 不动（layers.exactLayer/stableLayer）。

输入（全部为既有存档账本/证书，本脚本【不重解任何 SDP】，只做精确装配与判定）：

  • E*（三源校验参考值）     ../thomson-workflow/data/energies.json（N=9）
  • 区域 A [−1,−0.90]        results/slab_band.json     （5 片 slab 证书，Round 2）
  • 区域 B [−0.90,−0.82]     results/strips.json        （3/6 片认证，Round 4）
  • 区域 C [−0.82,−0.748]    results/hermite_strips.json（a5 Hermite 条带，Round 6；
       文件缺失/含 blocked 片 ⇒ 对应子带回落 HP 兜底）
       HP 证书                certificates/n9-stage-a2-sdp-hp.json（m∈[−9/10,1]）
  • 区域 D [−0.748,1]        results/hermite_cap.json   （a5 Hermite cap，Round 6；
       文件缺失 ⇒ 回落旧 cap certificates/n9-stage-a4-typedcap-m0748_M8.json）
  • 收尾链零件（Round 5–7）  results/l2_rigorous.json（L2 强制，精确 Fraction）
                             results/l3_analytic.json（L3 解析谱管，D7 口径＋
                               R7-3 nodeLocal 层 C_glob/链 caliber(c)）
                             results/l4.json（L5 Procrustes 常数）
                             results/l6_intube.json（L6 管内二次增长区间证书，
                               R7-3 斜率压缩后 r*=0.0067184）
                             results/l4_orbit.json（L4 双轨道邻型计数，R7-2）
                             results/moment_lift.json（R7-1 矩容器判死账本）
                             results/tube.json / full_local_min.json /
                             local_min.json（交叉参考，Round 2–4）

两个判定：

  【判定 1·拼合口径】[−1,−0.748) exclusion 片全部正裕度（certified > E*，精确
    Fraction）；cap 片（含 TTP）为 TTP-covering（≤ E*+1e-6）。
    - 收尾链不闭合 ⇒ assembledRecord = min(各原子区域覆盖界)（证书口径）；
    - 收尾链闭合（closed=true，D1 主链）⇒ cap 区域界经链抬到 E*
      （L2→L3→L5→L6 在 cap 域证明 E ≥ E*），assembledRecord ≥ E*。

  【判定 2·收尾链闭合】closed = 关键路径组件（L0,L1,L2,L3,L5,L6,L7）全部
    rigorous；L4 按 D1/D12 记备选路线（onCriticalPath=false）不入合取
    （R7-2 已交付精确层＋稳定层，分层 rigorous 如实分记）。
    不闭合 ⇒ blocking 逐项给定量理由（缺什么参数、差多少）。

诚实口径：
  • "已严格"只认存档证书/账本字段＋（--reverify-certs）进程外重验证 exit code；
    没跑的检查记 "not run"，绝不以推断代替。
  • E* 是三源校验参考值而非已证最优：所有 "≤ E*+1e-6 / > E*" 断言语义是
    "与参考值不矛盾"。
  • 任一 Round 6 输入缺失/pending ⇒ 对应组件 rigorous=false＋blocked 精确量化
    （缺哪个文件/哪个参数、差多少），closed 判定与证据严格对齐、绝不硬凑。

用法（在 thomson-n9 下）：
  python3 numerics/bounds/endgame_chain.py
  python3 numerics/bounds/endgame_chain.py --reverify-certs
      # 进程外重验证【全部被引证书】（citedCertificates 逐份 --verify-cert；
      # HP 按存档 reproduce 命令重生成并逐位比对；l3/l6/l4_orbit 账本按其
      # 幂等重跑门），任一失败 ⇒ exit 1。
"""
from __future__ import annotations

import argparse
import json
import math
import re
import subprocess
import sys
import time
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]                                    # .../thomson-n9
RESULTS = HERE / "results"
CERTS = REPO / "certificates"
WORKFLOW_DATA = HERE.parents[2] / "thomson-workflow" / "data" / "energies.json"
OUT = RESULTS / "endgame.json"

F0, F1 = Fraction(0), Fraction(1)
TOL_ESTAR = Fraction(1, 10**6)          # "≤ E* + 1e-6" 的精确容差

# 收尾链主战场切口（Round 4 起不变）：m ≥ −0.748 = −187/250（< m* ⇒ cap 片含 TTP）
A0_CAP = Fraction(-187, 250)
STRIP_TOP = Fraction(-9, 10)            # 条带区上端（与 slab 区 [−1,−0.90] 相接）

# Round 6 新账本（允许缺失：对应组件记 blocked/pending，不硬凑）
HERMITE_STRIPS = RESULTS / "hermite_strips.json"
HERMITE_CAP = RESULTS / "hermite_cap.json"
L3_ANALYTIC = RESULTS / "l3_analytic.json"
L6_INTUBE = RESULTS / "l6_intube.json"
L2_RIG = RESULTS / "l2_rigorous.json"
L4_PROC = RESULTS / "l4.json"

# Round 7 新账本（允许缺失：对应组件记 blocked/pending，不硬凑）
MOMENT_LIFT = RESULTS / "moment_lift.json"      # R7-1 矩容器（branch=dead）
L4_ORBIT = RESULTS / "l4_orbit.json"            # R7-2 双轨道邻型计数

# Round 8 记账基准（D20 裁决 2：产出未到盘 ⇒ 维持 R7 值；用于变化检测）
R7_CAP_TYPED_M8 = "certificates/n9-stage-a4-typedcap-m0748_M8.json"
R7_L6_RSTAR = "0.006718398305"                  # R7-3 存档 r*（l6_intube.json）
# splice-map 联动基准（D20 裁决 4）：R7 存档 assembledRecord（commit 898c522
# 落盘、e2e165b/9018a26 复核逐位一致）。固定常量而非读 OUT 当前内容——
# 覆写后重跑须逐位一致（gate-② 口径），基准不能随重跑漂移；首次运行时若
# OUT 仍是 R7 版则与盘上值断言核对。
R7_ASSEMBLED = "47517790735835014335570/1844674407417822803119"
HOLE_R7_BEST = {                                # 洞三片 R7 最优尝试（对照基线）
    "m082-m079": {"lukacs_M8": "25.759782985769", "a5_M8": "25.759708213619"},
    "m079-m765": {"lukacs_M8": "25.759535741156", "a5_M8": "25.759471667086"},
    "m765-m748": {"lukacs_M7": "25.258718429318", "a5_M8": "25.759463585921"},
}


def fail(msg: str) -> None:
    print(f"[FAIL] {msg}", flush=True)
    sys.exit(1)


def code_version() -> str:
    try:
        return subprocess.check_output(
            ["git", "describe", "--always", "--dirty"], cwd=str(REPO),
            text=True, stderr=subprocess.DEVNULL).strip()
    except Exception:
        return "unknown(non-git)"


def load_json(path: Path):
    with open(path) as f:
        return json.load(f)


def frac(s) -> Fraction:
    """账本里的界/端点统一转精确 Fraction（接受 'p/q' 与十进制串）。"""
    return Fraction(str(s))


# ============================================================ Round 6 读者

def read_hermite_strips():
    """读 hermite_strips.json（a5 条带账本，hermite_ladder.py --strip 落盘）。

    返回 (certified_rows, blocked_rows, note)。文件缺失 ⇒ (None, None, 缺失说明)。
    行字段（hermite_ladder.py run_strip_hermite）：status/tag/lo/hi/M/K/e_raw/
    certified(str Fraction)/certified_float/margin_over_E_star/certificate/...；
    blocked 行不出证书（certificate 字段指向的文件不存在，不得引用）。
    """
    if not HERMITE_STRIPS.exists():
        return None, None, "hermite_strips.json 未落盘（R6-3 任务 pending）"
    d = load_json(HERMITE_STRIPS)
    cert, block = [], []
    for r in d.get("strips", []):
        if r.get("status") == "certified":
            cert.append(r)
        else:
            block.append(r)
    note = (f"kind={d.get('kind')}；{len(cert)} certified / {len(block)} blocked；"
            f"code_version={d.get('code_version')}；updated={d.get('updated')}")
    return cert, block, note


def read_hermite_cap():
    """读 hermite_cap.json（a5 cap 账本）。返回最佳 rung dict 或 None。

    最佳＝a0 == −187/250 的 rung 中 certified 最大者（证书必须在盘）。
    注意：a5 rung 不必然优于旧 typed cap（固定 Hermite minorant 的拟合损失），
    最终 cap 片取两引擎最大界（见 assemble/main 的 best-of 选择）。
    """
    if not HERMITE_CAP.exists():
        return None, "hermite_cap.json 未落盘（R6-2 任务 pending）"
    d = load_json(HERMITE_CAP)
    rungs = [r for r in d.get("rungs", [])
             if frac(r.get("a0", "0")) == A0_CAP
             and (REPO / str(r.get("certificate", "§"))).exists()]
    if not rungs:
        return None, (f"hermite_cap.json 在盘但无 a0={A0_CAP} 且证书在盘的 rung"
                      f"（rungs={[r.get('tag') for r in d.get('rungs', [])]}）")
    best = max(rungs, key=lambda r: frac(r["certified"]))
    note = (f"kind={d.get('kind')}；best rung {best['tag']}_M{best['M']} "
            f"certified={float(frac(best['certified'])):.12f}；"
            f"code_version={d.get('code_version')}；updated={d.get('updated')}")
    return best, note


def read_l3():
    if not L3_ANALYTIC.exists():
        return None, "l3_analytic.json 未落盘（R6-4 任务 pending）"
    d = load_json(L3_ANALYTIC)
    gates = d.get("gates", {})
    g_ok = all(gates.get(g, {}).get("passed") is True
               for g in ("G1_constants_match_archive", "G2_fields_complete",
                         "G3_negative_controls", "iv_verification"))
    note = (f"gates G1/G2/G3/iv 全过={g_ok}；code_version="
            f"{d.get('provenance', {}).get('code_version')}")
    return (d if g_ok else None), note + ("（门未全过 ⇒ 不采信，按 pending 处理）"
                                          if not g_ok else "")


def _interval_pair(v):
    """账本区间字段兼容读：list/tuple [lo,hi] 或字符串 '[lo,hi]'。"""
    if isinstance(v, str):
        v = json.loads(v)
    lo, hi = v[0], v[1]
    return Fraction(str(lo)), Fraction(str(hi))


def read_l6():
    if not L6_INTUBE.exists():
        return None, "l6_intube.json 未落盘（R6-6 任务 pending）"
    d = load_json(L6_INTUBE)
    ncs = d.get("negativeControls", {})
    nc_ok = all(ncs.get(k, {}).get("triggered") is True for k in (
        "doubleRadiusControl", "muSignFlipControl",
        "stressSignFlipControl", "stressWeightControl"))
    mu_lo, _mu_hi = _interval_pair(
        d.get("quadraticGrowth", {}).get("muAtRstar", "[0,0]"))
    ok = nc_ok and mu_lo > 0
    note = (f"负对照 4/4 触发={nc_ok}；μ 区间下端>0={mu_lo > 0}；"
            f"provenance={d.get('provenance', {}).get('codeVersion')}")
    return (d if ok else None), note + ("（自检未全过 ⇒ 不采信）" if not ok else "")


# ============================================================ Round 7 读者

def read_moment_lift():
    """读 moment_lift.json（R7-1 矩容器抬天花板实验账本）。

    返回 (data, note)。branch=dead ⇒ 无 a6 证书（phaseB.cap_m0748_M8_containers
    为 null、证书不在盘）——cap 记账不换片，只留对照。文件缺失 ⇒ (None, 缺失说明)。
    """
    if not MOMENT_LIFT.exists():
        return None, "moment_lift.json 未落盘（R7-1 任务 pending）"
    d = load_json(MOMENT_LIFT)
    branch = d.get("branch")
    v = d.get("probe", {}).get("verdict", {})
    note = (f"branch={branch}；探针 verdict={v.get('verdict')}；"
            f"Δe_val 三档={v.get('deltas')}；全局噪声地板="
            f"{v.get('noise_floor_global'):.3e}；anchored_reaches_E_star="
            f"{v.get('anchored_reaches_E_star')}；phaseB.status="
            f"{d.get('phaseB', {}).get('status')}；old_cap_best="
            f"{d.get('old_cap_best')}")
    return d, note


def read_l4_orbit():
    """读 l4_orbit.json（R7-2 双轨道邻型计数账本）。

    采信条件（缺一 ⇒ 不采信，按 pending 处理）：幸存集非空且单 iso 类且
    congruent-to-TTP；lemma.form=unconditional；轨道配平 balanced=true；
    script_sha256 与在盘 l4_orbit.py 一致（防窜改）。返回 (data, note)。
    """
    import hashlib
    if not L4_ORBIT.exists():
        return None, "l4_orbit.json 未落盘（R7-2 任务 pending）"
    d = load_json(L4_ORBIT)
    ss = d.get("survivorSet", {})
    cls = ss.get("classes", [{}])
    ok = (ss.get("nonEmpty") is True and ss.get("isoClasses") == 1
          and cls and cls[0].get("isoToTTP") is True
          and d.get("lemma", {}).get("form") == "unconditional"
          and d.get("orbitBalance", {}).get("balanced") is True)
    sha = hashlib.sha256((HERE / "l4_orbit.py").read_bytes()).hexdigest()
    sha_ok = sha == d.get("script_sha256")
    note = (f"幸存集={ss.get('labeledTotal')} 标号染色/{ss.get('isoClasses')} "
            f"iso 类（congruent-to-TTP）；lemma.form=unconditional；配平 "
            f"Σ_y=2·mult={d.get('orbitBalance', {}).get('balanced')}；"
            f"script_sha256 一致={sha_ok}；seed={d.get('seed')}")
    ok = ok and sha_ok
    return (d if ok else None), note + ("（采信条件未全过 ⇒ 不采信）"
                                        if not ok else "")


# ============================================================ Round 8 读者

def read_round8():
    """Round 8 产出探测（R8-1/2/3，产出自适应——D20 裁决 1/2）。

    全部走既有账本 schema（新证书＝旧账本加行/加 rung），不引入猜测性
    新文件名依赖；探测不到 ⇒ 对应键记 missing 说明，绝不以推断代替。
    返回 dict：m9_strips（洞三片 M9 行，Lukács/a5 分记，含未翻正对照）、
    m9_cap（typed m0748 M9 rung）、anchor_probe（R8-2 锚定探针）、
    l6_joint（R8-3 L6 r* 变化检测）、l3_l6_consistent（l3 链扣的
    r_star_l6_used 与 l6 新值一致性）。
    """
    out = {}

    # --- (a) R8-1 洞三片 M9：Lukács strips.json / a5 hermite_strips.json ---
    m9_lukacs_cert, m9_lukacs_blocked = [], []
    if (RESULTS / "strips.json").exists():
        d = load_json(RESULTS / "strips.json")
        for r_ in d.get("strips", []):
            if r_.get("M") == 9 and (REPO / str(r_.get("certificate", "§"))).exists():
                m9_lukacs_cert.append(r_)
        for b in d.get("blocked", []):
            if b.get("M") == 9:
                m9_lukacs_blocked.append(
                    {"tag": b.get("tag"), "M": b.get("M"),
                     "best_certified_attempt": b.get("best_certified_attempt"),
                     "reason": b.get("reason")})
    h_cert, h_block, _h_note = read_hermite_strips()
    m9_a5_cert = [dict(r_, engine="a5") for r_ in (h_cert or []) if r_.get("M") == 9]
    m9_a5_blocked = [{"tag": r_.get("tag"), "M": r_.get("M"),
                      "certified": r_.get("certified"),
                      "certified_float": r_.get("certified_float"),
                      "status": r_.get("status")}
                     for r_ in (h_block or []) if r_.get("M") == 9]
    # --- (a′) R8-1 战役账本（m9_campaign.json，D22 裁决 1）：canary/rows
    #     战役级状态如实转录——注意【不改变主账本记账】（M9 行折入
    #     strips.json/hermite_strips.json 之前，coverage/L0 记账不动——
    #     折入与 endgame 刷新按 D22 裁决 4 由 R8-1 会话收尾执行）---
    campaign = None
    if (RESULTS / "m9_campaign.json").exists():
        try:
            c = load_json(RESULTS / "m9_campaign.json")
            if "m9-campaign" in str(c.get("kind", "")):
                campaign = c
        except Exception:                                   # noqa: BLE001
            campaign = None
    camp_info = None
    if campaign is not None:
        cy = campaign.get("canary", {})
        rows = campaign.get("rows", [])
        camp_info = {
            "canary": {"piece": cy.get("piece"), "decision": cy.get("decision"),
                       "lift1": cy.get("lift1"),
                       "lift1_float": cy.get("lift1_float")},
            "rows": [{"piece": r_.get("piece"), "engine": r_.get("engine"),
                      "status": r_.get("status"),
                      "certified": r_.get("certified")} for r_ in rows],
        }
    m9_note = ("M9 证书在盘（coverage 自动入账）" if (m9_lukacs_cert or m9_a5_cert)
               else ("M9 尝试在盘但全部未翻正（blocked，无证书不入账）"
                     if (m9_lukacs_blocked or m9_a5_blocked)
                     else "未到盘（M9 行未折入 strips.json/hermite_strips.json——"
                          "D20 裁决 2：维持 R7 记账）"))
    if camp_info is not None and not (m9_lukacs_cert or m9_a5_cert):
        # 战役账本有实质进展而主账本未折入 ⇒ 如实并列（不改变记账）
        cs = camp_info["canary"]
        done = [r_ for r_ in camp_info["rows"]
                if str(r_.get("status") or "").startswith(("certified", "pdopt"))]
        m9_note += (f"；【战役账本在盘未折入】m9_campaign.json：canary "
                    f"decision={cs.get('decision')}、lift₁={cs.get('lift1_float')}"
                    f"（certified={cs.get('lift1')}），rows 已解 {len(done)}/"
                    f"{len(camp_info['rows'])}——按 D22 裁决 4 由 R8-1 收尾折入"
                    f"主账本并刷新本账本（收口时点不代折，防撞）")
    out["m9_strips"] = {
        "onDisk": bool(m9_lukacs_cert or m9_a5_cert or m9_lukacs_blocked
                       or m9_a5_blocked),
        "lukacs_certified": [{"tag": r_.get("tag"), "certified": r_.get("certified"),
                              "certificate": r_.get("certificate")}
                             for r_ in m9_lukacs_cert],
        "lukacs_blocked": m9_lukacs_blocked,
        "a5_certified": [{"tag": r_.get("tag"), "certified": r_.get("certified"),
                          "certificate": r_.get("certificate")} for r_ in m9_a5_cert],
        "a5_blocked": m9_a5_blocked,
        "campaignLedger": camp_info,
        "note": m9_note,
    }

    # --- (b) R8-1 cap M9：typed_ladder.json rungs[] m0748 M=9 ---
    m9_cap = None
    if (RESULTS / "typed_ladder.json").exists():
        ladder = load_json(RESULTS / "typed_ladder.json")
        m9_cap = next((r_ for r_ in ladder.get("rungs", [])
                       if r_.get("tag") == "m0748" and r_.get("M") == 9
                       and (REPO / str(r_.get("certificate", "§"))).exists()), None)
    out["m9_cap"] = {
        "onDisk": m9_cap is not None,
        "rung": ({"tag": m9_cap.get("tag"), "M": m9_cap.get("M"),
                  "K": m9_cap.get("K"), "certified": m9_cap.get("certified"),
                  "certificate": m9_cap.get("certificate")}
                 if m9_cap else None),
        "note": ("typed m0748 (9,6) 证书在盘 ⇒ 参与多引擎取最优（D10/D16 "
                 "裁决 2＋D20 裁决 1②；本 rung＝campaign-2 R7B 交付——"
                 "D27 裁决 2 并行条款，修订 D19 裁决 2 原串行条款）"
                 if m9_cap else
                 "未到盘（typed_ladder.json 无 m0748 M=9 rung 且证书在盘——"
                 "D19 裁决 2 原条款『条带未翻正则不解』已被 D27 裁决 2 修订"
                 "为并行立解；仍未到盘 ⇒ 求解未完成或未认证，如实记，"
                 "维持旧 cap 记账）"),
    }

    # --- (c) R8-2 锚定精确取等探针：多形态宽容探测 ---
    # 注意防 R7 既有键误配：moment_lift.json 的 anchoring_layer_status 是
    # R7-1「锚定层未跑」的状态说明（branch=dead 的一部分），不是 R8-2 探针
    # 产出 ⇒ 键级探测只认 anchor_probe/anchorProbe/r8 前缀/round8 字样，
    # 不认宽泛的 "anchor" 子串；文件级探测认文件名含 anchor/锚（现有
    # results/ 无此命名，命中即 R8-2 新产出）。
    hits = []
    if MOMENT_LIFT.exists():
        d = load_json(MOMENT_LIFT)
        for k, v in d.items():
            kl = k.lower().replace("-", "_")
            if ("anchor_probe" in kl or kl.startswith("r8") or "round8" in kl):
                hits.append((f"results/moment_lift.json#{k}", v))
    for p in sorted(RESULTS.glob("*.json")):
        nl = p.name.lower()
        if ("anchor" in nl or "锚" in p.name) and p.name != "endgame.json":
            try:
                hits.append((f"results/{p.name}", load_json(p)))
            except Exception as e:                      # noqa: BLE001
                hits.append((f"results/{p.name}", {"unreadable": str(e)}))
    def _anchor_summary(v, depth=0):
        """浅摘要：只提 verdict/alive/dead/dist/e_val/M-scaling 类字段。"""
        if not isinstance(v, dict) or depth > 2:
            return v if not isinstance(v, dict) else "{…}"
        keep = {}
        for k, x in v.items():
            kl = k.lower()
            if any(t in kl for t in ("verdict", "alive", "dead", "dist", "e_val",
                                     "eval", "m_scal", "mscal", "status", "branch",
                                     "verdicts")):
                keep[k] = x
            elif isinstance(x, dict):
                sub = _anchor_summary(x, depth + 1)
                if isinstance(sub, dict) and sub:
                    keep[k] = sub
        return keep
    out["anchor_probe"] = {
        "onDisk": bool(hits),
        "hits": [{"where": w, "summary": _anchor_summary(v)} for w, v in hits],
        "note": "",                    # 下方按「判定在盘/仅中间产物/未到盘」三态填
    }
    def _has_verdict(v):
        """判定级产出识别：verdict/decision/branch 类字段取 alive/dead 类值
        （含复合形如 "dead-at-(9,6)"；解文件 kind=*-solution 是求解中间
        产物，判定未出——不算判定在盘；verdict=dict 时递归一层）。"""
        def _is_verdict_str(x):
            s = str(x).lower()
            return ("dead" in s or s.startswith("alive")) and len(s) < 60
        if not isinstance(v, dict):
            return False
        for k, x in v.items():
            kl = k.lower()
            if kl in ("verdict", "branch", "decision", "probe_verdict"):
                if isinstance(x, str) and _is_verdict_str(x):
                    return True
                if isinstance(x, dict):                  # 递归一层（verdict 对象）
                    for k2, x2 in x.items():
                        if (k2.lower() in ("verdict", "decision", "branch")
                                and isinstance(x2, str) and _is_verdict_str(x2)):
                            return True
        return False
    if hits:
        verdict_hits = [ (w, v) for w, v in hits if _has_verdict(v) ]
        sol_hits = [ (w, v) for w, v in hits
                     if not _has_verdict(v)
                     and isinstance(v, dict)
                     and "solution" in str(v.get("kind", "")).lower() ]
        if verdict_hits:
            out["anchor_probe"]["note"] = (
                "探针判定在盘：" + "; ".join(
                    f"{w}（摘要入账；完整数字以其 JSON 为准）"
                    for w, _ in verdict_hits))
        elif sol_hits:
            out["anchor_probe"]["note"] = (
                "仅求解中间产物在盘（" + "、".join(w for w, _ in sol_hits)
                + "——kind=*-solution，判定 alive/dead 未出；D20 裁决 2："
                "L3 结构性前提状态未知如实记）")
        else:
            out["anchor_probe"]["note"] = (
                "探测命中但无判定级字段（" + "、".join(w for w, _ in hits)
                + "——按未决处理，D20 裁决 2）")
    else:
        out["anchor_probe"]["note"] = (
            "未到盘（本收口会话时点未探测到锚定探针账本——"
            "results/ 无 anchor 键 JSON、moment_lift.json 无 R8/anchor 节；"
            "D20 裁决 2：L3 结构性前提（D19 裁决 3：KLT 命题 4.3 等号"
            "证书）状态未知如实记）")

    # --- (d) R8-3 L6 联合界：r* 变化检测 + l3 链扣一致性 ---
    l6_new, l6_note = read_l6()
    r_star_cur = (l6_new["quadraticGrowth"]["rigorousRadius"]
                  if l6_new else None)
    changed = (r_star_cur is not None
               and frac(str(r_star_cur)) != frac(R7_L6_RSTAR))
    l3d, _l3_note = read_l3()
    r_used_raw = (l3d.get("nodeLocal", {}).get("r_star_l6_used")
                  if l3d is not None else None)
    if isinstance(r_used_raw, dict):
        r_used = r_used_raw.get("value")
    else:
        r_used = r_used_raw
    out["l6_joint"] = {
        "onDisk": bool(changed),
        "r_star_R7": R7_L6_RSTAR,
        "r_star_now": r_star_cur,
        "changed": bool(changed),
        "note": (f"L6 r* 新值 {r_star_cur} 入账（≠R7 值 {R7_L6_RSTAR}，"
                 f"read_l6 采信门通过）" if changed else
                 f"L6 r* 维持 R7 值 {r_star_cur}（R8-3 联合界产出未到盘——"
                 f"D20 裁决 2；硬阈 0.0084 见 D19 裁决 4）"),
        "l3_r_star_l6_used": r_used,
        "l3_l6_consistent": (None if (r_used is None or r_star_cur is None)
                             else frac(str(r_used)) == frac(str(r_star_cur))),
    }
    return out


# ============================================================ R8B v2 探测（D29 裁决 2 消费面）

def _v2_variant_of(row):
    """行级 v2 引擎标记（R8B engine-v2 战役产出——D29 裁决 2）。

    判据（宽容多形态，沿 read_round8 anchor_probe 先例）：
      - 显式标记：variant/minorant_variant/engine 任一字段含 'v2' 子串或
        取值 contact/triple（hermite_minorant.py --variant contact 先例）；
      - 结构标记（hermite_minorant.py v2 泛型产出的字段）：orders 含 2 阶
        ⇒ triple（6 节点×值+一阶+二阶 deg≤17）；contact_minus1 ≥ 5 ⇒
        contact（−1 处 0–4 阶接触，deg≤16）；
      - tag 含 v2。
    旧 a5 行（M7–M10：无 variant/orders/contact_minus1 字段、tag 无 v2）
    不会误配。"""
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


def read_engine_v2():
    """R8B 引擎 v2 产出探测（D29 裁决 2：翻正/blocked/探针判死三态消费）。

    数据源（既有 schema 优先，不引入猜测性新文件名依赖）：
      - results/hermite_strips.json 的 v2 行：status=certified 且证书在盘 ⇒
        洞片翻正（coverage 自动入账）；blocked ⇒ 精确 attempt＋v2 档斜率
        资产（D22 裁决 4② schema）；
      - 战役/探针账本（results/ 下文件名或 kind 含 v2 的 JSON）：相位 0
        区间证书败 ⇒ 探针判死（相位 1/2 不启动、零求解）时无主账本行，
        其 verdict 如实转录进 note。
    返回 (v2_cert_rows, v2_blocked_rows, ledgers, note)。"""
    cert_rows, blocked_rows = [], []
    h_cert, h_block, _h_note = read_hermite_strips()
    for r_ in (h_cert or []):
        if _v2_variant_of(r_) and (REPO / str(r_.get("certificate", "§"))).exists():
            cert_rows.append(r_)
    for r_ in (h_block or []):
        if _v2_variant_of(r_):
            blocked_rows.append(r_)
    # R8B 独立 v2 账本（hermite_ladder --out-strips hermite_v2_strips.json）：
    # 行 schema 同 hermite_strips.json（variant/minorant_variant 字段在档），
    # 按 (tag, M, variant) 与主账本行去重后并入
    v2_strips_path = RESULTS / "hermite_v2_strips.json"
    if v2_strips_path.exists():
        try:
            _v2db = load_json(v2_strips_path)
        except Exception:                                       # noqa: BLE001
            _v2db = {}
        _seen = {(r_["tag"], r_.get("M"), str(_v2_variant_of(r_)))
                 for r_ in (cert_rows + blocked_rows)}
        for r_ in (_v2db.get("strips", []) or []):
            if not isinstance(r_, dict) or _v2_variant_of(r_) is None:
                continue
            _key = (r_.get("tag"), r_.get("M"), str(_v2_variant_of(r_)))
            if _key in _seen:
                continue
            if (r_.get("status") == "certified"
                    and (REPO / str(r_.get("certificate", "§"))).exists()):
                cert_rows.append(r_)
            else:
                blocked_rows.append(r_)
    ledgers = []
    probe_verdicts = {}               # 文件名 → (variant, verdict)（探针级）
    for p in sorted(RESULTS.glob("*.json")):
        if p.name == "endgame.json" or "v2" not in p.name.lower():
            continue
        try:
            d = load_json(p)
        except Exception:                                       # noqa: BLE001
            continue
        if not isinstance(d, dict):
            continue
        if "v2" in str(d.get("kind", "")).lower() or "v2" in p.name.lower():
            ledgers.append((f"results/{p.name}", d))
            if "probe" in p.name.lower() or "probe" in str(d.get("kind", "")).lower():
                v = d.get("verdict")
                if isinstance(v, str):
                    probe_verdicts[p.name] = (str(d.get("variant")
                                                  or d.get("engine") or "?"), v)
    n_c, n_b = len(cert_rows), len(blocked_rows)
    n_alive = sum(1 for _, v in probe_verdicts.values()
                  if str(v).lower().startswith("alive"))
    n_dead = sum(1 for _, v in probe_verdicts.values()
                 if "dead" in str(v).lower())
    if n_c:
        state = (f"翻正 {n_c} 片（v2 certified 行在盘，coverage 自动入账——"
                 "洞消除分支）")
    elif n_b:
        state = (f"未翻正（{n_b} 行 blocked：精确 attempt＋v2 档斜率入档——"
                 "D22 裁决 4② schema；引擎改良此向判死留痕）")
    elif ledgers and probe_verdicts and n_alive == 0 and n_dead > 0:
        state = ("探针判死（全部 v2 变体探针 dead ⇒ 相位 1/2 不启动、零求解"
                 "——D29 裁决 2 回滚点触发）")
    elif ledgers and probe_verdicts and n_alive > 0:
        state = (f"相位 0 探针 {n_alive} alive/{n_dead} dead，相位 1/2 产出"
                 "未到盘（本收口会话时点——D29 裁决 2 条件阶梯在途/未启动，"
                 "如实记）")
    elif ledgers:
        state = ("无主账本 v2 行但战役/探针账本在盘（verdict 以下方 ledger "
                 "摘要为准，如实记）")
    else:
        state = "未到盘（本收口会话时点无 v2 行/账本——D29 裁决 2）"

    def _ledger_verdict(d):
        """浅摘要：verdict/decision/branch/status 类字段（一层递归）。"""
        keep = {}
        for k, x in (d.items() if isinstance(d, dict) else []):
            kl = k.lower()
            if any(t in kl for t in ("verdict", "decision", "branch", "status",
                                     "phase", "outcome", "budget")):
                keep[k] = x
            elif isinstance(x, dict):
                sub = {k2: x2 for k2, x2 in x.items()
                       if any(t in k2.lower() for t in
                              ("verdict", "decision", "branch", "status",
                               "phase", "outcome", "triggered", "passed"))}
                if sub:
                    keep[k] = sub
        return keep

    note = (f"engine-v2 三态={state}；certified {n_c}/blocked {n_b}；"
            f"账本 {[w for w, _ in ledgers] if ledgers else '无'}")
    return cert_rows, blocked_rows, ledgers, note


# ================================================================ 判定 1：拼合

def coverage(E_star: Fraction):
    """条带带覆盖分析：[−0.90,−0.748] 上已入账证书（旧 certified ∪ a5 certified）
    的无缝性。返回 (pieces, holes, hp_used, strips_info)。

    pieces：原子覆盖片 [{lo, hi, src, row, bound, cert}]（同带新旧证书并存取大界）。
    holes：certified 片未盖住的子区间（⇒ HP 兜底）。
    """
    slab = load_json(RESULTS / "slab_band.json")
    strips = load_json(RESULTS / "strips.json")
    h_cert, h_block, h_note = read_hermite_strips()

    # --- slabs（5 片，Round 2）---
    for s in slab["slabs"]:
        assert s["status"] == "CERTIFIED", s["slab"]
        assert frac(s["bound"]) > E_star, s["slab"]

    # --- 旧 certified 条带（Round 4 起；R8-1 M9 行按同 schema 自动入账）---
    old_cert = []
    for r in strips["strips"]:
        b = frac(r["certified"])
        assert b > E_star, (r["tag"], float(b - E_star))     # 正裕度（精确）
        eng = "Lukács (8,6)/(7,6)"
        if r.get("M") == 9:
            eng = "Lukács (9,6)（R8-1 M9 战役）"
        elif r.get("M") == 10:
            eng = "Lukács (10,6)（campaign-2 R7 M10 战役）"
        old_cert.append({"lo": frac(r["lo"]), "hi": frac(r["hi"]),
                         "bound": b, "cert": r["certificate"],
                         "tag": r["tag"], "engine": eng})

    # --- a5 Hermite certified 条带（Round 6 起；R8-1 M9 行按同 schema 入账；
    #     R8B engine-v2 行按 variant 标记入账——D29 裁决 2 消费面，沿 R7C
    #     M10 标签先例最小增量。行源＝hermite_strips.json ∪ hermite_v2_strips
    #     .json（R8B 独立账本，--out-strips 落盘；按 tag/M/variant 去重））---
    hm_cert = []
    _hm_seen = set()

    def _feed_hm(r):
        b = frac(r["certified"])
        assert b > E_star, (r.get("tag"), float(b - E_star))
        var2 = _v2_variant_of(r)
        if var2 is not None:
            eng = (f"Hermite a5-v2（{var2}）M{r.get('M')}"
                   "（R8B engine-v2 战役，D29 裁决 2）")
        else:
            eng = "Hermite a5"
            if r.get("M") == 9:
                eng = "Hermite a5 M9（R8-1 M9 战役）"
            elif r.get("M") == 10:
                eng = "Hermite a5 M10"
        hm_cert.append({"lo": frac(r["lo"]), "hi": frac(r["hi"]),
                        "bound": b, "cert": r["certificate"],
                        "tag": r["tag"], "engine": eng,
                        "M": r.get("M"), "K": r.get("K"),
                        "variant": var2})

    if h_cert is not None:
        for r in h_cert:
            _feed_hm(r)
    _v2_strips_path = RESULTS / "hermite_v2_strips.json"
    if _v2_strips_path.exists():
        try:
            _v2db = load_json(_v2_strips_path)
        except Exception:                                       # noqa: BLE001
            _v2db = {}
        for r in (_v2db.get("strips", []) or []):
            if (isinstance(r, dict) and r.get("status") == "certified"
                    and _v2_variant_of(r) is not None
                    and (REPO / str(r.get("certificate", "§"))).exists()
                    and (r.get("tag"), r.get("M"), str(_v2_variant_of(r)))
                    not in {(h["tag"], h["M"], h.get("variant"))
                            for h in hm_cert}):
                _feed_hm(r)

    # --- 原子胞元：certified 区间端点并集上逐胞取覆盖证书最大界 ---
    ivs = old_cert + hm_cert
    ends = sorted({STRIP_TOP, A0_CAP} | {e for iv in ivs for e in (iv["lo"], iv["hi"])})
    cells = [(ends[i], ends[i + 1]) for i in range(len(ends) - 1)]
    pieces, holes = [], []
    for lo, hi in cells:
        covering = [iv for iv in ivs if iv["lo"] <= lo and hi <= iv["hi"]]
        if not covering:
            holes.append((lo, hi))
            continue
        best = max(covering, key=lambda iv: iv["bound"])
        others = [iv for iv in covering if iv is not best]
        pieces.append({"lo": lo, "hi": hi, "bound": best["bound"],
                       "cert": best["cert"], "tag": best["tag"],
                       "engine": best["engine"],
                       "also_covered_by": [f"{iv['tag']}@{float(iv['bound']):.9f}"
                                           for iv in others]})

    strips_info = {
        "certified": [{"tag": p["tag"], "region": f"[{p['lo']},{p['hi']}]",
                       "engine": p["engine"],
                       "bound": str(p["bound"]), "bound_float": float(p["bound"]),
                       "margin_over_E_star_exact": str(p["bound"] - E_star),
                       "certificate": p["cert"],
                       "also_covered_by": p["also_covered_by"]}
                      for p in pieces],
        "hermiteBlocked": [dict(r) for r in (h_block or [])],
        "oldBlockedSuperseded": [
            {k: b[k] for k in ("tag", "lo", "hi", "best_certified_attempt",
                               "margin_over_E_star", "reason")}
            for b in strips.get("blocked", [])
            if not any(frac(b["lo"]) >= p["lo"] and frac(b["hi"]) <= p["hi"]
                       for p in hm_cert)],
        "allPositiveMargin": not holes,
        "hermiteLedgerNote": h_note,
        "note": ("原子胞元取覆盖证书最大界；洞（无已入账证书的子带）⇒ HP 兜底；"
                 "blocked 行的 best/certified 数值有效但无存档证书（正裕度断言"
                 "exit 1 时不落证书），不参与拼合 min"),
    }
    return pieces, holes, bool(holes), strips_info


def select_cap(r8=None):
    """cap 片证书选择：typed m0748_M8 / typed m0748_M9（R8-1，在盘时）／
    a5 Hermite rung / R7-1 矩容器 rung 之中 certified 最大者（域同为
    m ≥ −187/250、证书须在盘且可 --verify-cert）。
    D10（Round 6）确立「两引擎取最优」，Round 7 扩三引擎（D16 裁决 2），
    Round 8 再纳入 M9 typed 证书参与竞争（D19 裁决 2＋D20 裁决 1②：
    参与条件＝证书在盘＋可 --verify-cert）。
    返回 dict(h_cap, m_cap, note, bound, piece, source, cert_rel, cmd, key,
    a5_used, m9_used)。"""
    r8 = r8 or {}
    h_cap, note = read_hermite_cap()
    m_cap, m_note = read_moment_lift()
    ladder = load_json(RESULTS / "typed_ladder.json")
    capr = next(r for r in ladder["rungs"]
                if r.get("tag") == "m0748" and r.get("M") == 8)
    old_bound = frac(capr["certified"])
    old_rel = "certificates/n9-stage-a4-typedcap-m0748_M8.json"
    old = {"bound": old_bound, "cert_rel": old_rel,
           "cmd": ["numerics/bounds/typed_ladder.py", "--verify-cert", old_rel],
           "key": "cap_m0748_M8",
           "piece": "typed cap m0748 (8,6)",
           "source": "results/typed_ladder.json（Round 3–4）"}
    cands = [dict(old, engine="typed")]
    # R8-1 M9 typed cap（在盘才参与——D20 裁决 1②；D19 裁决 2 的预算条款
    # 规定条带未翻正则 cap M9 不解，此处纯消费：不在盘＝未解或未翻正）
    m9_rung = ((r8.get("m9_cap") or {}).get("rung"))
    if m9_rung is not None:
        m9_rel = str(m9_rung.get("certificate"))
        cands.append({"bound": frac(m9_rung["certified"]),
                      "cert_rel": m9_rel,
                      "cmd": ["numerics/bounds/typed_ladder.py", "--verify-cert",
                              m9_rel],
                      "key": "cap_m0748_M9",
                      "piece": "typed cap m0748 (9,6)",
                      "source": ("results/typed_ladder.json（campaign-2 "
                                 "R7B cap M9 typed，D27 裁决 2 并行条款）"),
                      "engine": "typed-M9"})
    if h_cap is not None:
        cands.append({"bound": frac(h_cap["certified"]),
                      "cert_rel": str(h_cap["certificate"]),
                      "cmd": ["numerics/bounds/hermite_ladder.py", "--verify-cert",
                              str(h_cap["certificate"])],
                      "key": f"cap_{h_cap['tag']}_M{h_cap.get('M')}",
                      "piece": (f"hermite cap {h_cap['tag']} (M={h_cap.get('M')}, "
                                f"K={h_cap.get('K')})"),
                      "source": f"results/hermite_cap.json（a5，Round 6）",
                      "engine": "a5"})
    # R7-1 矩容器 rung：仅当 phaseB 落了证书（branch≠dead）才参与取最优
    if m_cap is not None:
        pb = m_cap.get("phaseB", {}) or {}
        cert_rel = pb.get("cap_m0748_M8_containers")
        if isinstance(cert_rel, str) and (REPO / cert_rel).exists():
            cert = load_json(REPO / cert_rel)
            cands.append({"bound": frac(cert["claimed_bound"]),
                          "cert_rel": cert_rel,
                          "cmd": ["numerics/bounds/moment_lift.py", "--verify-cert",
                                  cert_rel],
                          "key": "cap_m0748_M8_moment",
                          "piece": "moment-container cap m0748 (8,6)（R7-1）",
                          "source": "results/moment_lift.json（R7-1）",
                          "engine": "moment"})
        else:
            note += ("；R7-1 矩容器无证书参与（" + m_note + "）")
    best = max(cands, key=lambda c: c["bound"])
    a5_used = best.get("engine") == "a5"
    m9_used = best.get("engine") == "typed-M9"
    if best["engine"] == "typed":
        others = "、".join(f"{c['engine']}@{float(c['bound']):.12f}"
                           for c in cands if c is not best)
        m9_phrase = ("在盘但未胜出" if m9_rung is not None
                     else "未到盘不参与（D20 裁决 2）")
        note += (f"；cap 片取旧 typed M8 证书（多引擎取最优：胜出 "
                 f"{float(best['bound']):.12f} vs {others}；M9 typed 证书"
                 f"{m9_phrase}）")
    elif m9_used:
        others = "、".join(f"{c['engine']}@{float(c['bound']):.12f}"
                           for c in cands if c is not best)
        note += (f"；cap 片换记 typed M9 证书（campaign-2 R7B 交付——"
                 f"D27 裁决 2；多引擎取最优：胜出 "
                 f"{float(best['bound']):.12f} vs {others}）——L2/L3 的 "
                 f"ε_forcing 口径牵动按 D20 裁决 3 如实标注")
    return dict(h_cap=h_cap, m_cap=m_cap, note=note, a5_used=a5_used,
                m9_used=m9_used, **best)


def assemble(E_star: Fraction, closed: bool, pieces, holes, hp_used, cap_sel):
    """装配 [−1,1] 原子区域分区；closed=true ⇒ cap 区域界经 D1 主链抬到 E*。"""
    hp_cert = load_json(CERTS / "n9-stage-a2-sdp-hp.json")

    # --- HP 证书（兜底片）---
    hp_bound = frac(hp_cert["claimed_bound"])
    hp_lo, hp_hi = frac(hp_cert["m_lo"]), frac(hp_cert["m_hi"])   # [−9/10, 1]
    assert (hp_lo, hp_hi) == (Fraction(-9, 10), F1), (hp_lo, hp_hi)

    # --- cap（select_cap 已选最优引擎证书）---
    cap_bound = cap_sel["bound"]
    cap_cert_rel = cap_sel["cert_rel"]
    assert frac(load_json(REPO / cap_cert_rel)["claimed_bound"]) == cap_bound
    if cap_sel.get("m9_used"):
        cap_piece = (f"{cap_sel['piece']}（多引擎取最优胜出——campaign-2 "
                     "R7B M9 证书换记〔D27 裁决 2〕，ε_forcing 口径牵动"
                     "见 D20 裁决 3）")
    elif not cap_sel["a5_used"] and cap_sel["h_cap"] is not None:
        cap_piece = (f"{cap_sel['piece']}（最优；a5 rung 在盘更弱＋R7-1 矩容器判死"
                     "无证书，见 round6Inputs/round7Inputs）")
    elif cap_sel["a5_used"]:
        cap_piece = f"{cap_sel['piece']}（最优，超越旧 typed cap）"
    else:
        cap_piece = f"{cap_sel['piece']}（a5 未落盘/未认证，回落旧证书）"
    cap_source = cap_sel["source"]
    if cap_sel["h_cap"] is not None and not cap_sel["a5_used"]:
        cap_source += ("；对照 results/hermite_cap.json（a5，Round 6）＋"
                       "results/moment_lift.json（R7-1 判死，无证书）")

    cited = [{"path": cap_cert_rel, "claimed_bound": str(cap_bound),
              "reverifyKey": cap_sel["key"], "verifyCmd": cap_sel["cmd"]}]

    # --- slabs（5 片）---
    slab = load_json(RESULTS / "slab_band.json")
    regions = []
    for s in slab["slabs"]:
        b = frac(s["bound"])
        assert b > E_star, (s["slab"], float(b - E_star))
        regions.append({"region": f"[{s['m_lo']},{s['m_hi']}]",
                        "lo": frac(s["m_lo"]), "hi": frac(s["m_hi"]),
                        "piece": f"slab {s['slab']}", "bound": b,
                        "exclusion": True})
        cited.append({"path": s["certificate"],
                      "claimed_bound": str(b),
                      "reverifyKey": f"slab_{s['slab']}",
                      "verifyCmd": ["numerics/bounds/slab_band.py",
                                    "--verify-cert", s["certificate"]]})

    # --- 条带片（coverage 已归并）---
    for p in pieces:
        engine_cmd = ("numerics/bounds/hermite_ladder.py"
                      if p["engine"].startswith("Hermite")
                      else "numerics/bounds/strips_final.py")
        regions.append({"region": f"[{p['lo']},{p['hi']}]", "lo": p["lo"],
                        "hi": p["hi"],
                        "piece": f"strip {p['tag']}（{p['engine']}）",
                        "bound": p["bound"], "exclusion": True})
        cited.append({"path": p["cert"], "claimed_bound": str(p["bound"]),
                      "reverifyKey": f"strip_{p['tag']}",
                      "verifyCmd": [engine_cmd, "--verify-cert", p["cert"]]})

    # --- 洞 ⇒ HP 兜底 ---
    for lo, hi in holes:
        assert hp_lo <= lo and hi <= hp_hi
        regions.append({"region": f"[{lo},{hi}]", "lo": lo, "hi": hi,
                        "piece": "HP m∈[−9/10,1]（兜底，条带受阻/未落盘）",
                        "bound": hp_bound, "exclusion": False})
    if holes:
        cited.append({"path": "certificates/n9-stage-a2-sdp-hp.json",
                      "claimed_bound": str(hp_bound), "reverifyKey": "hp_reproduce",
                      "verifyCmd": None})

    # --- cap 区域（含 TTP）---
    cap_effective = cap_bound
    if closed:
        # D1 主链（L2→L3→L5→L6）在 cap 域证明 E ≥ E* ⇒ 区域界抬到 max(cert, E*)
        cap_effective = max(cap_bound, E_star)
    regions.append({"region": f"[{A0_CAP},1]", "lo": A0_CAP, "hi": F1,
                    "piece": (f"{cap_piece}＋收尾链（closed ⇒ cap 域 E ≥ E*）"
                              if closed else cap_piece),
                    "bound": cap_effective, "exclusion": False})

    # 覆盖片口径断言：exclusion 片 > E*（精确）；TTP-covering 片 ≤ E*+1e-6
    for r in regions:
        if r["exclusion"]:
            if not r["bound"] > E_star:
                fail(f"exclusion 片 {r['piece']} 界 ≤ E*")
        elif not r["bound"] <= E_star + TOL_ESTAR:
            fail(f"TTP-covering 片 {r['piece']} 界 > E*+1e-6")

    # 分区自检：无缝盖满 [−1,1]
    rs = sorted(regions, key=lambda r: r["lo"])
    cur = Fraction(-1)
    for r in rs:
        if r["lo"] != cur:
            fail(f"分区不连续：期望 {cur}，实为 {r['lo']}")
        cur = r["hi"]
    if cur != F1:
        fail(f"分区未盖满 [−1,1]，止于 {cur}")

    assembled = min(r["bound"] for r in regions)
    weak = [r for r in regions if r["bound"] == assembled]
    bottleneck = ("、".join(sorted({r["piece"] for r in weak})) +
                  f"（{len(weak)} 片并列全局最弱）")
    if closed:
        criterion = ("closed=true（D1 主链 L2→L3→L5→L6）⇒ cap 区域界经链抬到 E*，"
                     "assembledRecord = min(区域界) ≥ E*")
    elif hp_used:
        criterion = ("closed=false 且条带带有洞（HP 兜底）⇒ assembledRecord = "
                     "min(各原子区域覆盖界)（证书口径）")
    else:
        criterion = ("closed=false（收尾链未闭合）但条带全正（洞不存在）⇒ "
                     "assembledRecord = min(各原子区域覆盖界)（证书口径，瓶颈=cap）")
    return (regions, assembled, bottleneck, criterion, cited)


# ================================================================ 判定 2：收尾链

def _hole_gap_table(E_star: Fraction, r8: dict):
    """洞区攻坚子带逐片缺口表（Round 8 记账口径——任务书「L0 洞三片逐片
    按新 M9 证书重记账」）。

    数据源（全部在盘账本，程序化读取，不硬编码）：
      - results/strips.json blocked 节（Lukács 各档 best_certified_attempt，
        R8-1 的 M9 尝试若未翻正也在此节，M=9）；
      - results/hermite_strips.json blocked 行（a5 各档 certified）。
    每行：子带 tag、当前在盘最优尝试（引擎/值/对 E* 缺口，Fraction）、
    R8-1 M9 状态（certified⇒翻绿并入 coverage；blocked⇒lift 实测；
    未到盘⇒canary 未测；m9 列冻结——D27 任务书条款）＋campaign-2 R7
    M10 三态列（certified/blocked/未到盘——D27 裁决 1 消费面，数据源
    ＝strips.json/hermite_strips.json 的 M=10 行，lift_vs_m9_best 供
    M9→M10 斜率标定）。canary 基线＝R7 m082-m079 最优尝试
    25.759782985769（D19 裁决 2：lift₁=certified−该值，lift₁<+1.0e-4 ⇒
    其余三解中止）。

    D28 复核修正（返工员-R7）：lift_vs_m9_best 的 M9 基线改读
    results/m9_campaign.json 的精确分数（blocked 行
    blocked_detail.best_certified_attempt / certified）——strips.json
    blocked 节 Lukács 行的 best_certified_attempt 是 12 位小数截断串，
    直接取差曾给该字段引入 4.78e-13 截断偏差（m079-m765 行，
    2026-10-09 复算员发现）。m9 列账面记录仍冻结不动（D27 任务书
    条款）；基线来源在行内 lift_baseline 键如实标注；m9_campaign.json
    缺席时回落账面口径（截断串），不静默。
    """
    strips = load_json(RESULTS / "strips.json")
    h_cert, h_block, _ = read_hermite_strips()
    m9 = r8.get("m9_strips", {})
    m9_cert_by_tag = {r_["tag"]: r_ for r_ in m9.get("lukacs_certified", [])}
    m9_cert_by_tag.update({r_["tag"]: r_ for r_ in m9.get("a5_certified", [])})
    m9_blk_by_tag = {r_["tag"]: r_ for r_ in m9.get("lukacs_blocked", [])}
    m9_blk_by_tag.update({r_["tag"]: r_ for r_ in m9.get("a5_blocked", [])})
    canary_base = frac(HOLE_R7_BEST["m082-m079"]["lukacs_M8"])
    # m10 行（campaign-2 R7 M10 战役——D27 裁决 1）：strips.json/
    # hermite_strips.json 既有 schema 加行，此处直读（与 read_round8 的
    # M9 过滤同款口径；m9 列冻结不动——D27 任务书条款）
    m10_cert_by_tag = {r_["tag"]: r_ for r_ in strips.get("strips", [])
                       if r_.get("M") == 10
                       and (REPO / str(r_.get("certificate", "§"))).exists()}
    m10_cert_by_tag.update({r_["tag"]: r_ for r_ in (h_cert or [])
                            if r_.get("M") == 10})
    m10_blk_by_tag = {b.get("tag"): b for b in strips.get("blocked", [])
                      if b.get("M") == 10}
    m10_blk_by_tag.update({r_.get("tag"): r_ for r_ in (h_block or [])
                           if r_.get("M") == 10})
    # v2 行（R8B engine-v2 战役——D29 裁决 2 消费面）：certified（证书在盘）
    # /blocked（精确 attempt＋v2 档斜率资产）/探针判死（相位 0 区间证书败 ⇒
    # 相位 1/2 未启动——战役账本 verdict 如实转录）三态列
    v2_cert_rows, v2_blk_rows, v2_ledgers, v2_note = read_engine_v2()
    v2_cert_by_tag = {r_["tag"]: r_ for r_ in v2_cert_rows}
    v2_blk_by_tag = {r_["tag"]: r_ for r_ in v2_blk_rows}
    # 探针判死（回滚点触发）＝有 v2 探针账本、全部变体 dead、且无任何
    # 主账本行/后续相位产出（D29 裁决 2——有 alive 变体时相位 1/2 在途，
    # 不得记『判死』）
    _v2_pv = {}
    for _w, _d in v2_ledgers:
        if "probe" in _w.lower() and isinstance(_d.get("verdict"), str):
            _v2_pv[_w] = _d["verdict"].lower()
    v2_probe_dead = (bool(_v2_pv)
                     and all("dead" in v for v in _v2_pv.values())
                     and not (v2_cert_rows or v2_blk_rows))
    v2_alive_inflight = (bool(_v2_pv)
                         and any(v.startswith("alive") for v in _v2_pv.values())
                         and not (v2_cert_rows or v2_blk_rows))
    # D28 复核修正：M9 基线精确分数表（m9_campaign.json blocked 行）。
    # strips.json blocked 节 Lukács M9 行的 best_certified_attempt 为
    # 12 位小数截断串（账面口径），取差会引入截断偏差——lift_vs_m9_best
    # 改用本表（m9 列 value 仍记账面口径，来源在 lift_baseline 标注）。
    m9_exact_by_tag = {}
    if (RESULTS / "m9_campaign.json").exists():
        try:
            camp9 = load_json(RESULTS / "m9_campaign.json")
        except Exception:                                       # noqa: BLE001
            camp9 = {}
        if "m9-campaign" in str(camp9.get("kind", "")):
            for r_ in camp9.get("rows", []):
                if r_.get("status") != "blocked":
                    continue
                bd = r_.get("blocked_detail") or {}
                v9x = (bd.get("best_certified_attempt")
                       or r_.get("best_certified_attempt")
                       or r_.get("certified"))
                if v9x is not None and r_.get("piece"):
                    try:
                        m9_exact_by_tag[r_["piece"]] = frac(v9x)
                    except (ValueError, ZeroDivisionError):
                        pass                                    # 如实回落账面口径

    rows = []
    tags = sorted({b.get("tag") for b in strips.get("blocked", [])}
                  | {r_.get("tag") for r_ in (h_block or [])})
    for tag in tags:
        cands = []
        for b in strips.get("blocked", []):
            if b.get("tag") == tag:
                cands.append((f"Lukács M{b.get('M')}（blocked 尝试）",
                              frac(b["best_certified_attempt"])))
        for r_ in (h_block or []):
            if r_.get("tag") == tag:
                cands.append((f"a5 M{r_.get('M')}（blocked 尝试）",
                              frac(r_["certified"])))
        if tag in m9_cert_by_tag:
            r9 = m9_cert_by_tag[tag]
            cands.append((f"R8-1 M9 certified（证书在盘）", frac(r9["certified"])))
        if tag in m10_cert_by_tag:
            r10 = m10_cert_by_tag[tag]
            cands.append(("campaign-2 R7 M10 certified（证书在盘）",
                          frac(r10["certified"])))
        best_eng, best_v = (max(cands, key=lambda t: t[1]) if cands
                            else (None, None))
        row = {"tag": tag,
               "best_attempt": {"engine": best_eng, "value": str(best_v),
                                "float": (float(best_v) if best_v is not None
                                          else None)},
               "gap_to_E_star": {"exact": (str(E_star - best_v)
                                           if best_v is not None else None),
                                 "float": (float(E_star - best_v)
                                           if best_v is not None else None)}}
        if tag in m9_cert_by_tag:
            v9 = frac(m9_cert_by_tag[tag]["certified"])
            row["m9"] = {"status": "certified（翻绿）",
                         "value": str(v9),
                         "turnsGreen": v9 > E_star,
                         "lift_vs_canary_base": (str(v9 - canary_base)
                                                 if tag == "m082-m079" else None)}
        elif tag in m9_blk_by_tag:
            b9 = m9_blk_by_tag[tag]
            v9 = b9.get("best_certified_attempt") or b9.get("certified")
            v9f = frac(str(v9)) if v9 is not None else None
            row["m9"] = {"status": "尝试在盘未翻正（blocked，无证书不入账）",
                         "value": (str(v9f) if v9f is not None else None),
                         "turnsGreen": False,
                         "lift_vs_canary_base": (
                             str(v9f - canary_base)
                             if (v9f is not None and tag == "m082-m079")
                             else None)}
        else:
            row["m9"] = {"status": "未到盘（本收口会话时点无 M9 行——"
                                   "D20 裁决 2）",
                         "value": None, "turnsGreen": False,
                         "lift_vs_canary_base": None}
        m9_val = row["m9"]["value"]
        # D28 复核修正：lift 基线优先取 m9_campaign.json 精确分数（仅当该
        # 片在盘且与 m9 列账面值不同值时才换基＋标注；其余行输出不变）。
        m9_col = frac(m9_val) if m9_val is not None else None
        base9 = m9_col
        lift_base_note = None
        if (m9_col is not None and tag in m9_exact_by_tag
                and m9_exact_by_tag[tag] != m9_col):
            base9 = m9_exact_by_tag[tag]
            lift_base_note = {
                "value": str(base9),
                "source": ("results/m9_campaign.json blocked_detail."
                           "best_certified_attempt（精确分数，D28 复核修正）；"
                           "m9 列 value 仍记 strips.json 账面 12 位截断串"
                           "（账面冻结，差 4.78e-13）")}
        # --- m10 三态列（certified/blocked/未到盘；D27 裁决 1 消费面）---
        if tag in m10_cert_by_tag:
            v10 = frac(m10_cert_by_tag[tag]["certified"])
            row["m10"] = {"status": "certified（翻绿）",
                          "value": str(v10),
                          "turnsGreen": v10 > E_star,
                          "lift_vs_m9_best": (str(v10 - base9)
                                              if base9 is not None else None)}
        elif tag in m10_blk_by_tag:
            b10 = m10_blk_by_tag[tag]
            v10 = b10.get("best_certified_attempt") or b10.get("certified")
            v10f = frac(str(v10)) if v10 is not None else None
            row["m10"] = {"status": "尝试在盘未翻正（blocked，无证书不入账）",
                          "value": (str(v10f) if v10f is not None else None),
                          "turnsGreen": False,
                          "lift_vs_m9_best": (
                              str(v10f - base9)
                              if (v10f is not None and base9 is not None)
                              else None)}
        else:
            row["m10"] = {"status": "未到盘（本收口会话时点无 M10 行——"
                                    "D27 裁决 1）",
                          "value": None, "turnsGreen": False,
                          "lift_vs_m9_best": None}
        if lift_base_note is not None:
            row["m10"]["lift_baseline"] = lift_base_note
        # --- v2 三态列（certified/blocked/探针判死——D29 裁决 2 消费面）---
        if tag in v2_cert_by_tag:
            r2 = v2_cert_by_tag[tag]
            v2v = frac(r2["certified"])
            row["v2"] = {
                "status": "certified（翻绿）",
                "variant": _v2_variant_of(r2), "M": r2.get("M"),
                "value": str(v2v), "float": float(v2v),
                "turnsGreen": v2v > E_star,
                "lift_vs_best_prior": (str(v2v - best_v)
                                       if best_v is not None else None),
                "gap_to_E_star": str(E_star - v2v)}
        elif tag in v2_blk_by_tag:
            r2 = v2_blk_by_tag[tag]
            a2v = r2.get("best_certified_attempt") or r2.get("certified")
            a2f = frac(str(a2v)) if a2v is not None else None
            row["v2"] = {
                "status": "尝试在盘未翻正（blocked，无证书不入账；v2 档斜率"
                          "资产入档——D22 裁决 4② schema）",
                "variant": _v2_variant_of(r2), "M": r2.get("M"),
                "value": (str(a2f) if a2f is not None else None),
                "float": (float(a2f) if a2f is not None else None),
                "turnsGreen": False,
                "lift_vs_best_prior": (str(a2f - best_v)
                                       if (a2f is not None
                                           and best_v is not None) else None),
                "gap_to_E_star": (str(E_star - a2f)
                                  if a2f is not None else None)}
        elif v2_probe_dead:
            row["v2"] = {
                "status": ("探针判死（R8B 相位 0 区间证书/占优检查败——全部"
                           " v2 变体探针 dead ⇒ 相位 1/2 未启动、零求解——"
                           "D29 裁决 2 回滚点触发；verdict 见"
                           " round8Inputs.engineV2）"),
                "variant": None, "M": None, "value": None, "turnsGreen": False,
                "lift_vs_best_prior": None, "gap_to_E_star": None}
        elif v2_alive_inflight:
            row["v2"] = {
                "status": ("相位 0 探针 alive（区间证书过）但相位 1/2 产出"
                           "未到盘（本收口会话时点——D29 裁决 2 条件阶梯"
                           "在途/未启动，如实记；探针摘要见"
                           " round8Inputs.engineV2）"),
                "variant": None, "M": None, "value": None, "turnsGreen": False,
                "lift_vs_best_prior": None, "gap_to_E_star": None}
        else:
            row["v2"] = {
                "status": "未到盘（本收口会话时点无 v2 行——D29 裁决 2）",
                "variant": None, "M": None, "value": None, "turnsGreen": False,
                "lift_vs_best_prior": None, "gap_to_E_star": None}
        rows.append(row)
    return rows


def chain(E_star: Fraction, hp_used: bool, holes, cap_sel: dict,
          strips_info: dict, r8: dict, r7_record=None):
    """八组件 L0–L7（D1 口径：L4 备选路线不入合取）。返回 (chain_res,
    remaining, closed, cited_extra)。r8＝read_round8() 的产出探测结果
    （D20 裁决 1/2：在盘入账/未到盘如实记 missing）；r7_record＝R7 存档
    assembledRecord（Fraction，用于 splice-map 联动机器判定——D20 裁决 4）。"""
    cap_bound = cap_sel["bound"]
    cap_piece = cap_sel["piece"] + (
        "（多引擎取最优：typed M8/typed M9（在盘时）/a5/R7-1 矩容器，"
        "见 round6Inputs/round7Inputs/round8Inputs）"
        if (cap_sel["h_cap"] is not None or (r8.get("m9_cap") or {}).get("onDisk"))
        else "")
    cap_source = cap_sel["source"]
    tube = load_json(RESULTS / "tube.json")
    flm = load_json(RESULTS / "full_local_min.json")
    lmin = load_json(RESULTS / "local_min.json")
    l2 = load_json(L2_RIG)
    h_cap_used = cap_sel["a5_used"]
    l4 = load_json(L4_PROC)
    l3, l3_note = read_l3()
    l6, l6_note = read_l6()

    meta = tube["meta"]
    m_star = float(meta["m_star"])
    if not (float(A0_CAP) < m_star):
        fail(f"切口 −0.748 须 < m*={m_star}（cap 片含 TTP）")
    z_lo, z_hi = (float(x) for x in
                  lmin["zStarInterval"].strip("[]").split(","))
    if not (z_lo <= float(meta["z_star"]) <= z_hi):
        fail("tube.json z* 不在 local_min.json 隔离区间内")

    delta_E = E_star - cap_bound                       # 精确
    if not flm["verified"]:
        fail("full_local_min.json verified != true")
    lam = frac(flm["lambdaCertifiedLowerBound"])       # 0.14378982（链上取强）

    # Round 7 读者（R7-1/R7-2 账本；允许缺失 ⇒ 组件 blocked）
    m_lift, m_note = read_moment_lift()
    l4o, l4o_note = read_l4_orbit()

    cited_extra = []                                   # 账本级引用（非证书）

    # ---------------- L0（Round 8：洞片逐片按 M9 记账——D20 裁决 1①/2）----------------
    if hp_used:
        hs = "；".join(f"[{lo},{hi}]" for lo, hi in holes)
        hb = strips_info.get("hermiteBlocked", [])
        best = max((frac(r["certified"]) for r in hb), default=None)
        ml_dead = ((m_lift is not None and m_lift.get("branch") == "dead")
                   or (m_lift is None))
        gap_table = _hole_gap_table(E_star, r8)
        # 逐片缺口串（程序化：每攻坚子带一列，最优尝试＋缺口＋M9 状态）
        per_hole = "；".join(
            f"{g['tag']}：best={g['best_attempt']['engine']}"
            f"@{g['best_attempt']['float']:.12f}（E*−best="
            f"{g['gap_to_E_star']['float']:+.3e}），M9 {g['m9']['status']}"
            + (f" lift₁={float(frac(g['m9']['lift_vs_canary_base'])):+.3e}"
               if g["m9"]["lift_vs_canary_base"] is not None else "")
            + f"，M10 {g['m10']['status']}"
            + (f"（对 M9 best lift={float(frac(g['m10']['lift_vs_m9_best'])):+.3e}）"
               if g["m10"]["lift_vs_m9_best"] is not None else "")
            + f"，v2 {g['v2']['status']}"
            + (f"（对在盘最优 lift="
               f"{float(frac(g['v2']['lift_vs_best_prior'])):+.3e}）"
               if g["v2"].get("lift_vs_best_prior") is not None else "")
            for g in gap_table)
        m9_any = bool((r8.get("m9_strips") or {}).get("onDisk"))
        l0 = {
            "id": "L0", "name": "条带片 [−1,−0.748) 全部 > E*（不含 TTP）",
            "rigorous": False,
            "status": (f"部分（[−1,−0.90] 5 片＋条带带 "
                       f"{len(strips_info['certified'])} 胞元认证；洞 {hs} 无证书）"
                       + ("；R8-1 M9 战役产出未到盘（本收口会话时点）——"
                          "D20 裁决 2 维持 R7 记账" if not m9_any else "")),
            "quant": (f"洞 {hs} 由 HP 兜底（HP=E*−"
                      f"{float(E_star - frac(load_json(CERTS / 'n9-stage-a2-sdp-hp.json')['claimed_bound'])):.3e}）；"
                      "【Round 8 逐片记账】" + per_hole
                      + ("；R7-1 矩容器判死（D13：Δe_val 三档 ≤ 噪声地板 8.53e-7、"
                         "锚定 λ′ 侧不可达）⇒ M 阶梯（R8-1 M9，D19 裁决 2）是"
                         "洞片唯一在攻路径，canary lift₁ 未测（产出未到盘）"
                         if (ml_dead and not m9_any) else "")),
            "missing": (f"洞子带 {hs} 的正裕度证书（逐片缺口见 quant；"
                        f"R8-1 M9 重解（引擎按 M8 逐片最优：m082-m079/m079-m765 "
                        f"用 Lukács、m765-m748 用 a5——D19 裁决 2）产出未到盘，"
                        "canary 条款（lift₁<+1.0e-4 ⇒ 中止）未经实测——D20 "
                        "裁决 2：不冒充、维持 R7 记账值）"),
            "holeGapTable": gap_table,
        }
    else:
        worst = min(frac(c["bound"]) for c in strips_info["certified"])
        m9_cert = ((r8.get("m9_strips") or {}).get("lukacs_certified", [])
                   + (r8.get("m9_strips") or {}).get("a5_certified", []))
        # campaign-2 R7 M10 翻绿片（D27 裁决 1：M10 certified 行经
        # coverage 自动入账——按引擎标签计数，不引入新读者）
        m10_cert = [c for c in strips_info["certified"]
                    if "M10" in c["engine"]]
        # R8B engine-v2 翻绿片（D29 裁决 2：v2 certified 行经 coverage 自动
        # 入账——引擎标签含 v2 计数）
        v2_cert = [c for c in strips_info["certified"] if "v2" in c["engine"]]
        l0 = {
            "id": "L0", "name": "条带片 [−1,−0.748) 全部 > E*（不含 TTP）",
            "rigorous": True,
            "status": (f"已严格（[−1,−0.90] 5 slab＋条带带 "
                       f"{len(strips_info['certified'])} 胞元全部 certified > E*，"
                       "每胞元证书在盘"
                       + (f"；R8-1 M9 翻绿 {len(m9_cert)} 片"
                          if m9_cert else "")
                       + (f"；campaign-2 R7 M10 翻绿 {len(m10_cert)} 片"
                          "（洞消除，D27 裁决 1）"
                          if m10_cert else "")
                       + (f"；R8B engine-v2 翻绿 {len(v2_cert)} 片（D29 "
                          "裁决 2——洞消除，assembledRecord→cap 片）"
                          if v2_cert else "") + "）"),
            "quant": (f"条带带最弱片裕度 {float(worst - E_star):+.3e}（精确 "
                      f"{worst - E_star}）；分区无缝断言见本脚本"),
            "missing": None,
        }

    # ---------------- L1 ----------------
    l1 = {
        "id": "L1", "name": f"cap：m ≥ −0.748 ⇒ E ≥ {float(cap_bound):.12f}",
        "rigorous": True, "status": f"已严格（{cap_piece}；"
        "PSD 块 LDLᵀ＋--verify-cert 进程外复核）",
        "quant": (f"ΔE = E*−certified = {float(delta_E):.4e}（精确 {delta_E}）；"
                  f"来源 {cap_source}"),
        "missing": None,
    }
    cited_extra.append({"path": ("results/hermite_cap.json"
                                 if h_cap_used else "results/typed_ladder.json"),
                        "note": "cap 账本（L1 证书的存档索引）"})

    # ---------------- L2 ----------------
    a2 = l2.get("asserts", {})
    l2_keys = ("psd_all_blocks", "normalization_zero", "residuals_match_provenance",
               "certified_bitwise_equal", "identity_residual_zero",
               "positivity_spotcheck", "minorant_spotchecks", "w_hat_covers_domain",
               "swap_l1_preserved", "numerical_ledger_reproduced",
               "rigorous_le_ledger_plus_omitted_term")
    l2_ok = all(a2.get(k) is True for k in l2_keys)
    eps_exact = l2["eps_forcing"]["exact"]
    # 口径串动态化（D29 裁决 3：R8A 换 cap M9 口径后「待刷新」标注自动解除；
    # 未换时如实保留待刷新标注——不以旧口径冒充新口径、亦不以新口径冒充旧）
    _l2_cert_in = str(l2.get("inputs", {}).get("certificate", ""))
    _l2_m9 = "M9" in _l2_cert_in.split("/")[-1]
    _l2_cal = ("cap m0748_M9（R8A M9 口径重算——D29 裁决 3 还账；证书 "
               f"{_l2_cert_in}）" if _l2_m9 else
               "旧 cap m0748_M8（待 R8A 换 M9 口径重算——D29 裁决 3 标注"
               "待刷新）")
    try:
        _r2max = frac(l2["certificate_rebuild"]["R2max_exact"])
        _lit_gap_txt = f"E*·R2max={float(E_star * _r2max):.2e}"
    except (KeyError, ValueError, ZeroDivisionError):
        _lit_gap_txt = "E*·R2max（值在档）"
    l2_comp = {
        "id": "L2", "name": "强制：E ≤ E* ⇒ 每类 λ_cls ≤ ε_forcing（精确 Fraction）",
        "rigorous": l2_ok,
        "status": ("已严格（l2_rigorous.json 11 项 asserts 全真；字面口径差 "
                   f"{_lit_gap_txt} 不可满足性如实入账；口径＝{_l2_cal}）"
                   if l2_ok else
                   "账本 asserts 未全过（按 pending 处理）"),
        "quant": (f"ε_forcing = {l2['eps_forcing']['float']:.6e}（精确 Fraction "
                  f"{eps_exact}；口径＝{_l2_cal} 的 e_dy/R1/defl）"),
        "missing": None if l2_ok else "l2_rigorous.json asserts 未全真",
    }
    cited_extra.append({"path": "results/l2_rigorous.json", "note": "L2 账本"})

    # ---------------- L3（解析口径，D7；R7-3 nodeLocal 层，v2.x）----------------
    # caliber(c) L6 链扣的动态口径串（诚实修正：R8-4 阶段 2 遗留硬编码
    # 22.5×/3.25e-14 系 R7-3 时点值，R8-3 后实际 11.25×/6.51e-14——本刷新起
    # 按 l3_analytic.json links 动态生成，杜绝账面自相矛盾）
    _l6lk = (((l3 or {}).get("nodeLocal", {}) or {})
             .get("chain_caliber_c", {}) or {}).get("links", {}) or {}
    _l6 = _l6lk.get("L6", {}) or {}
    l6_deficit_txt = (f"{_l6['deficit_factor_float']:.2f}×"
                      if _l6.get("deficit_factor_float") else "22.5×")
    l6_epsstar_txt = (f"{_l6['eps_star_float']:.2e}"
                      if _l6.get("eps_star_float") else "3.25e-14")
    eps_w_txt = "7.33e-13"            # 兜底（l3 在盘时下方按 eps_w_hi 刷新）
    if l3 is None:
        l3_comp = {
            "id": "L3", "name": "谱管（解析口径）：λ ≤ ε ⇒ 内积距 6 节点 ≤ ρ_spec(ε)",
            "rigorous": False, "status": f"blocked（{l3_note}）",
            "quant": l3_note,
            "missing": "l3_analytic.json（或其门未全过）——L3 无可采信数值",
        }
    else:
        ch = l3["chain_L2_L3_L5_L6"]["caliber_a"]
        cb = l3["chain_L2_L3_L5_L6"].get("caliber_b", [])
        elim = l3["reconciliation_sdp"]["elimination"]
        cb_best = cb[-1] if cb else {}
        nl = l3.get("nodeLocal", {})
        nl_present = bool(nl.get("present"))
        anchor_on_disk = bool((r8.get("anchor_probe") or {}).get("onDisk"))
        anchor_note = str((r8.get("anchor_probe") or {}).get("note") or "")
        # status 用稳定两态文案（gate-② 逐位比对 status；并行会话的中间
        # 产物放置/移动会抖动盘面——细节一律走 round8Inputs.note，不进
        # status）。只有 R8-2 的【最终判定】（alive/dead，终态产出）落盘
        # 才切换 status 文案。
        anchor_phrase = ("探针判定在盘（结果见 quant/round8Inputs）"
                         if anchor_note.startswith("探针判定在盘")
                         else "探针判定未出（D20 裁决 2 ⇒ 前提状态未知，"
                              "如实记；盘面细节见 round8Inputs）")
        cap_swapped = bool(cap_sel.get("m9_used"))
        # caliber(c)：ε_W 级口径的链判定（R7-3）；前提＝cap 抬至区间亏损级
        eps_w_hi = (frac(nl["eps_W"]["hi"]) if nl_present else None)
        c_links = (nl.get("chain_caliber_c", {}).get("links", {})
                   if nl_present else {})
        c_met = all(c_links.get(k, {}).get("premise_ok") is True
                    for k in ("L3_need", "L5", "L6"))
        eps_premise_realized = (nl_present and eps_w_hi is not None
                                and delta_E <= eps_w_hi)
        if eps_w_hi is not None:
            eps_w_txt = f"{float(eps_w_hi):.2e}"
        # 诚实口径：rigorous 只认「现行可行 ε（ε_forcing，cap 实证书口径）下
        # 链过」（caliber_a）或「caliber(c) 过且其 ε 前提已兑现」（cap 证书
        # 亏损 ≤ ε_W——R7-1 判死后未兑现）；caliber(b)/(c) 本身是反事实口径，
        # 前提未兑现不翻绿。
        l3_ok = (bool(ch.get("thresholds_met"))
                 or (c_met and eps_premise_realized))
        cg = nl.get("C_glob", {}) if nl_present else {}
        crit = nl.get("criterion", {}) if nl_present else {}
        car = (nl.get("chain_caliber_c", {}).get("caliber_a_rerun", {})
               if nl_present else {})
        l3_comp = {
            "id": "L3", "name": "谱管（解析口径）：λ ≤ ε ⇒ 内积距 6 节点 ≤ ρ_spec(ε)",
            "rigorous": l3_ok,
            "status": ("已严格（解析常数链在可行 ε 口径下全过）" if l3_ok else
                       "断点未消除（D7 口径如实＋R7-3 nodeLocal 层已把常数抬 "
                       "8518×，但现行可行 ε（ε_forcing，cap 未抬）下 ρ_raw 仍 "
                       "vacuous；ε_W 级口径的 caliber(c) 三链扣中 L6 仍缺 "
                       + l6_deficit_txt +
                       "且其 ε 前提因 R7-1 判死未兑现；Round 8 口径——cap 精确"
                       "取等的结构性前提（D19 裁决 3）生死由 R8-2 锚定探针定，"
                       + anchor_phrase
                       + "）"),
            "quant": (f"口径(a) ε_forcing={ch['eps_float']:.4e} ⇒ δ_gram="
                      f"{ch['delta_gram_float']:.6f}（L5 差 "
                      f"{ch['l5']['deficit_factor']:.2f}×、L6 差 "
                      f"{ch['l6']['deficit_factor']:.1f}×）；SDP 对账："
                      f"0.6447 平台逐位=1−ν₆（平凡几何值）；C_min="
                      f"{elim['C_min_flat_float']:.3e} vs 闭合需 "
                      f"C≥{elim['C_needed_for_need_float']:.4f}；闭链 ε*："
                      f"L3 need {l3['chain_L2_L3_L5_L6']['closure_requirement']['eps_star_L3_need_float']:.2e}"
                      f" / L5 {l3['chain_L2_L3_L5_L6']['closure_requirement']['eps_star_L5_float']:.2e}"
                      f" / L6 {l3['chain_L2_L3_L5_L6']['closure_requirement']['eps_star_L6_float']:.2e}"
                      + (f"；【R7-3 nodeLocal 层】C_glob∈[{cg.get('lo_float'):.6e},"
                         f"{cg.get('hi_float'):.6e}]（胞元全域严格 Fraction，"
                         f"结合位点={cg.get('binding_site')}，较 C_min 抬 "
                         f"{float(frac(cg['lo'])) / float(frac(elim['C_min_flat'])):.0f}×）；"
                         f"判据 C_glob≥ε_W/ρ_need²={crit.get('threshold_float'):.3e}"
                         f" PASS 余量 {crit.get('margin_float'):.1f}×；"
                         f"口径(a) 以 C_glob 重跑 ρ_raw={car.get('rho_raw_float'):.1f}"
                         f"（仍 vacuous）；口径(c)（ε_W={float(eps_w_hi):.3e} 级）："
                         f"L3-need 过 {c_links.get('L3_need', {}).get('margin_float'):.1f}×"
                         f"/L5 过 {c_links.get('L5', {}).get('margin_float'):.0f}×"
                         f"/L6 缺 {c_links.get('L6', {}).get('deficit_factor_float'):.1f}×"
                         f"（ε*_L6={c_links.get('L6', {}).get('eps_star_float'):.2e}）"
                         if nl_present else "（nodeLocal 层未落盘）")
                      + ("；【Round 8】R8-2 锚定精确取等探针在盘："
                         + json.dumps((r8.get("anchor_probe") or {}).get("hits"),
                                      ensure_ascii=False)[:400]
                         if anchor_on_disk else
                         "；【Round 8】R8-2 锚定探针未到盘——closed=true 的"
                         "结构性前提（D19 裁决 3：E_ttp−E*=2.6983e-10 ⇒ cap 三"
                         "点层损失须 ≤2.7e-10，阶梯斜率 ~3×/档 外推不可达 ⇒ "
                         "唯一已识别路径＝KLT 命题 4.3 等号证书）生死未卜，"
                         "如实记；L3 精确取等 dist 缺口维持 R7 值（cap "
                         "E*−4.1535e-4）")
                      + (("；cap 片已换记 typed M9（D20 裁决 3）⇒ 本组件 ε_"
                          "forcing 口径牵动：l2_rigorous.json 已换 cap M9 口径"
                          "重算（R8A 交付，D29 裁决 3——「待刷新」标注解除；"
                          "caliber(a) 的 ε_forcing/ρ_raw 经 l3_analytic 运行时"
                          "直读联动刷新）"
                          if (_l2_m9 and cap_swapped) else
                          "；cap 片已换记 typed M9（D20 裁决 3）⇒ 本组件 ε_"
                          "forcing 口径牵动：l2_rigorous.json 仍旧 cap 口径，"
                          "ε_forcing 精确 Fraction 重算＋caliber(a) ρ_raw 重跑"
                          "未由 R8/R7B 交付 ⇒ 标注待刷新、不以旧口径冒充")
                         if cap_swapped else "")),
            "missing": (None if l3_ok else
                        "ε 前提未兑现（R7-1 矩容器判死 ⇒ cap 证书口径 "
                        f"E*−{float(delta_E):.2e}"
                        + (("（campaign-2 R7B typed M9 换记；L2 账本已换 "
                            "cap M9 口径（R8A，D29 裁决 3）：ε_forcing="
                            f"{float(frac(eps_exact)):.2e}——仍 ≫ ε_W="
                            f"{float(eps_w_hi):.2e}）" if _l2_m9 else
                            "（campaign-2 R7B typed M9 换记；L2 账本 "
                            "ε_forcing=4.15e-4 仍旧 cap 口径未重算——D20 "
                            "裁决 3 牵动）")
                           if cap_swapped else
                           f"、可行 ε 仍=ε_forcing={float(frac(eps_exact)):.2e}")
                        + "，caliber(c) 需 ε≤ε_W="
                        f"{float(eps_w_hi):.2e}——cap 抬至区间亏损级无已识别"
                        "路径（锚定探针 dead-at-(9,6)，D24），M 阶梯只抬 "
                        "assembledRecord 不闭合收尾链（D25）"
                        + ("、cap M9 rung（campaign-2 R7B，D27 裁决 2）"
                           "未到盘" 
                           if not (r8.get("m9_cap") or {}).get("onDisk")
                           else "、cap M9 rung 在盘参与竞争（campaign-2 R7B）")
                        + "；即便 ε 兑现，"
                        "L6 半径仍差 " + l6_deficit_txt +
                        "（caliber(c) L6 链扣，D7 预判『终卡点"
                        "在 L6』经 R7-3 认证常数重跑证实；R8-3 L6 方向相关"
                        "联合界（估 r*→0.0095+，仍余 ~3.3×）"
                        + ("产出未到盘" if not (r8.get("l6_joint") or {}).get("changed")
                           else "已入账") + "）"),
        }
    cited_extra.append({"path": "results/l3_analytic.json", "note": "L3 账本"})

    # ---------------- L4（D1/D12：备选离散路线，不入合取；R7-2 已交付，分层记账）----------------
    if l4o is None:
        l4_comp = {
            "id": "L4", "name": "组合刚性：内积 ∈ 6 节点 ρ-管 ⇒ 邻型唯一 = TTP",
            "rigorous": False, "onCriticalPath": False,
            "status": (f"账本未采信（{l4o_note}）——按 D1/D12 记备选离散路线，"
                       "不在闭合关键路径"),
            "quant": l4o_note,
            "missing": "l4_orbit.json 采信条件未全过（或未落盘）",
        }
    else:
        ss = l4o["survivorSet"]
        ob = l4o["orbitBalance"]
        st = l4o["stability"]
        exact_rig = (ss.get("nonEmpty") is True and ss.get("isoClasses") == 1
                     and ss["classes"][0].get("isoToTTP") is True
                     and l4o["lemma"].get("form") == "unconditional")
        stable_rig = ("sigmaMinLower_cV" in st.get("vandermonde", {})
                      and "rhoMax_deltaOnly" in st.get("countingThreshold", {}))
        rho_max = float(st["countingThreshold"]["rhoMax_deltaOnly"])
        rho_floor = float(st["chainComparison"]["rhoSpecAtFloor"])
        l4_comp = {
            "id": "L4", "name": "组合刚性：内积 ∈ 6 节点 ρ-管 ⇒ 邻型唯一 = TTP",
            "rigorous": False, "onCriticalPath": False,
            "status": ("R7-2 已交付两件、分层如实记账（处置按裁决 D1/D12："
                       "ε-链 L2→L3→L5→L6 仍为首选主链 ⇒ L4 记备选离散路线、"
                       "onCriticalPath=false、不入 closed 合取；R7-1 判死后两"
                       "路线共同前置（cap 抬升）落空，主链选择维持 D1/D12 原文"
                       "——见 notes/decisions.md §D12/§D13/§D14）"),
            "layers": {
                "exactLayer": {
                    "rigorous": exact_rig,
                    "content": (f"幸存者集判定＋轨道计数（K9 六色边染色枚举："
                                f"float scout 容差 1e-3＋sup|det′|·半宽完备性"
                                f"证书 1.51e-4；精确复验＝Z[z,r]/(r²+z²−1) "
                                f"多项式恒等（16 恒等零类/2435 箱上排零/undecided "
                                f"0））：幸存集＝{ss['labeledTotal']} 标号染色＝"
                                f"{ss['isoClasses']} iso 类＝TTP（=9!/12，构造性"
                                f"实现证书在档）；引理取无条件形式——『9 单位"
                                f"向量、两两内积∈节点集 ⇒ 边染色≅TTP』；轨道"
                                f"配平 Σ_y#type=2·mult 对 tube.json "
                                f"6/6/3/3/6/12（{ob['structure']}；D12 帽-棱"
                                f"勘误再勘误：12ν₆＋6ν₂ 非 ν₅）"),
                    "gaps": ("E_ttp vs E* 在存档 z* 箱宽（7.63e-7）下 undecided"
                             "（一阶传播 1.18e-5 ≫ 差值 2.7e-10；对无条件引理"
                             "无影响）"),
                },
                "stableLayer": {
                    "rigorous": stable_rig,
                    "content": (f"ρ-近似计数常数与阈值（区间 Gauss-Jordan "
                                f"V⁻¹∋I 逐项验证）：c_V=σ(V) 下界 "
                                f"{float(st['vandermonde']['sigmaMinLower_cV']):.4e}、"
                                f"‖V⁻¹‖_∞ ≤ "
                                f"{float(st['vandermonde']['normInvInf'][1]):.2f}、"
                                f"计数阈值 ρ_max≈{rho_max:.2e}（‖V⁻¹‖_∞·δ_∞(ρ)"
                                f"<1/2）、对径分离 min|ν_a+ν_b|=2ν₄="
                                f"{float(st['antipodalSeparation']['minNuaNuB_lower']):.6f}"),
                    "premiseMet": False,
                    "gaps": (f"ρ 前提未由现行 ε-链满足：需 ρ≲{rho_max:.1e} 而现行 "
                             f"L3 ρ_spec 地板 {rho_floor:.4f}（差 "
                             f"{rho_floor / rho_max:.0f}×）——L3 缺口非本层缺口；"
                             f"『计数向量=轨道轮廓 ⇒≅TTP』的 ρ>0 推广后半"
                             f"（z₀ 禁三角类）未交付"),
                },
            },
            "quant": (f"精确层 rigorous={exact_rig}（幸存集=TTP 单类无条件引理）；"
                      f"稳定层常数 rigorous={stable_rig}（c_V/ρ_max/对径分离在档）"
                      f"但前提 ρ≲{rho_max:.1e} 未满足（现行 ρ_spec 地板 "
                      f"{rho_floor:.4f}，差 {rho_floor / rho_max:.0f}×）⇒ 链级"
                      "L4（ρ-管版邻型唯一）未装配；组件整体 rigorous=false 与"
                      "分层事实如实分记；l4_orbit_gate 五项过（幂等/正对照/"
                      "负对照×4/处置/配平，本收口会话亲跑 ALL PASS 53.2s）"),
            "missing": ("ρ-近似计数引理的 ρ 前提（依赖 L3 抬升——R7-1 判死后无"
                        "已识别路径）＋计数向量⇒≅TTP 的 ρ>0 后半；按 D1/D12 "
                        "延后非本轮闭合要件"),
        }
    cited_extra.append({"path": "results/l4_orbit.json",
                        "note": "L4 账本（R7-2 双轨道邻型计数）"})

    # ---------------- L5 ----------------
    cst = l4["constants"]
    nc = l4.get("selftest", {})
    nc_ok = all(nc.get(k, {}).get("triggered") is True for k in (
        "NC1_rank_deficient_planar", "NC2_certifier_teeth",
        "NC3_labeling_premise"))
    l5_ok = nc_ok and "C_exact" in cst and "delta_max_exact" in cst
    l5_comp = {
        "id": "L5", "name": "Gram→构型（Procrustes 重构）：‖G−G_TTP‖ ≤ η ⇒ "
                            "弦距离 d_P ≤ C·δ（线性 Lipschitz）",
        "rigorous": l5_ok,
        "status": ("已严格（results/l4.json：显式构造证明＋区间 Sylvester "
                   "λ₃≥2.970726＋三负对照全触发）" if l5_ok else
                   "l4.json 常数/负对照缺失（按 pending 处理）"),
        "quant": (f"C = {cst['C_float']:.15f}（δ ≤ δ_max = "
                  f"{cst['delta_max_float']:.15f}，内积口径；精确分数在档；"
                  f"距离口径 2C = {cst.get('C_chord_distance_float', float('nan')):.13f}）；"
                  "D1 主链重构环节＝Gram 扰动→d_P≤C·δ→管内二次增长"),
        "missing": None if l5_ok else "l4.json 自检字段不全",
    }
    cited_extra.append({"path": "results/l4.json", "note": "L5 账本"})

    # ---------------- L6 ----------------
    if l6 is None:
        l6_comp = {
            "id": "L6", "name": "管内二次增长：d_P ≤ r* ⇒ E ≥ E* − γd + (μ/2)d²",
            "rigorous": False, "status": f"blocked（{l6_note}）",
            "quant": l6_note,
            "missing": "l6_intube.json（或其负对照/μ>0 未过）——L6 无可采信数值",
        }
    else:
        qg = l6["quadraticGrowth"]
        r_star = float(qg["rigorousRadius"])
        mu_lo, mu_hi = _interval_pair(qg["muAtRstar"])
        comp_lo, _ = _interval_pair(qg["competitorExclusionRadius"])
        r_target = l6["reconciliation"]["rTargetFormula"]["value"]
        td = l6.get("taylorDecomposition", {})
        l6_ok = mu_lo > 0
        l6_changed = bool((r8.get("l6_joint") or {}).get("changed"))
        if l6_changed:
            r_head = (f"R8-3 方向相关联合界新值，前值 {R7_L6_RSTAR}；μ ∈ "
                      f"[{float(mu_lo):.10f}, {float(mu_hi):.10f}]；")
        else:
            r_head = (f"R7-3 由 0.0033592 抬 2.00×，μ@r* 由 0.0021870 升至 "
                      f"{float(mu_lo):.7f}，μ ∈ "
                      f"[{float(mu_lo):.10f}, {float(mu_hi):.10f}]；")
        if l6_changed:
            r8_l6_txt = (f"【Round 8】R8-3 方向相关联合界入账：r* 新值 "
                         f"{(r8.get('l6_joint') or {}).get('r_star_now')}"
                         f"（read_l6 采信门过，l3 链扣一致性="
                         f"{(r8.get('l6_joint') or {}).get('l3_l6_consistent')}）")
        else:
            r8_l6_txt = ("【Round 8】R8-3 方向相关联合界（D19 裁决 4：硬阈 "
                         "r*≥0.0084，估计 0.0095+）产出未到盘 ⇒ r* 维持 R7 值"
                         "（D20 裁决 2）")
        l6_comp = {
            "id": "L6", "name": "管内二次增长：d_P ≤ r* ⇒ E ≥ E* − γd + (μ/2)d²",
            "rigorous": l6_ok,
            "status": ("已严格（l6_intube.py KLT §7.4 Hessian 分解免 D³E＋区间"
                       "证书：分箱半径 r* 内 μ>0；4 负对照全触发；R7-3 斜率压缩"
                       "2.00×：一阶项钉在 sharp ∂M(0)（symmetric-Kronecker "
                       "K-lift 认证斜率 12.836）＋二阶 BD2 box 通道）" if l6_ok else
                       "μ 区间上端 ≤ 0（不可采信）"),
            "quant": (f"rigorous r* = {r_star}（" + r_head
                      + f"目标公式半径 "
                      f"{r_target} 本方法不可严格化——reconciliation."
                      f"rTargetFormula.certifiedHere=否，如实）；竞争者排除："
                      f"E ≤ Ē ⇒ d ≤ {float(comp_lo):.3e}；刚性：ν₆ 12 边 "
                      "Maxwell 计数结构性不刚（12<15），增广 ν₂ 18 边刚性＋"
                      "严格正自应力；caliber(c)（ε_W 级，R7-3 刷新、R8-3 "
                      "更新）：L6 链扣"
                      "ε*=" + l6_epsstar_txt + " vs ε_W=" + eps_w_txt +
                      " ⇒ 缺 " + l6_deficit_txt + "——ε-链终卡点"
                      "确认在 L6；" + r8_l6_txt),
            "missing": (None if l6_ok else "μ>0 未成立") if l6_ok else
                       (f"严格半径 {r_star} ≪ 公式值 {r_target}（"
                        f"{r_target / r_star:.1f}×）：闭合需 L3/L5 侧把 d_P 压到 "
                        f"≤ {r_star}；caliber(c) 口径下 L6 仍差 "
                        + l6_deficit_txt +
                        "（ε*_L6=" + l6_epsstar_txt + " < ε_W=" + eps_w_txt +
                        "；D15（原 D14）裁决 4："
                        "已识别未实施改良＝逐边双线性方向相关联合界（估计 "
                        "r*→0.0095+），BD2 .dd 区间宽度为瓶颈"
                        + ("——R8-3 已交付（见 quant）" if l6_changed else
                           "——R8-3 排入 Round 8（D19 裁决 4，硬阈 0.0084），"
                           "产出未到盘（D20 裁决 2）") + "）"),
        }
    cited_extra.append({"path": "results/l6_intube.json", "note": "L6 账本"})

    # ---------------- L7（splice-map 联动——D20 裁决 4，main 装配后回填）----------------
    l7_comp = {
        "id": "L7", "name": "排除/拼接：L0∪L1∪(L2→L3→L5→L6) ⇒ 全空间 E ≥ E*",
        "rigorous": True,
        "status": ("已记账（装配说明书 notes/splice-map.md（Round 8 版本判定"
                   "见 spliceMapVerdict——D20 裁决 4 机器判定，装配后回填）＋"
                   "本脚本分区机器断言：原子区域无缝盖满 [−1,1]、exclusion 片 "
                   "> E*、TTP-covering 片 ≤ E*+1e-6、assembledRecord=Fraction "
                   "min）；条件装配——前提为 L0–L6 全绿时给出全局结论"),
        "quant": ("splice-map.md v2 节＋endgame.json partition/citedCertificates；"
                  "closed 语义见 endgameChain.closedSemantics（D1/D12 口径）；"
                  "Round 8 口径：assembledRecord 变 ⇒ splice-map 出 v3 同步"
                  "（D16 裁决 5 逆否），不变 ⇒ 维持 v2 留痕（D20 裁决 4）"),
        "missing": None,
    }

    comp = [l0, l1, l2_comp, l3_comp, l4_comp, l5_comp, l6_comp, l7_comp]
    for c in comp:
        c.setdefault("onCriticalPath", True)
    critical = [c for c in comp if c["onCriticalPath"]]
    closed = all(c["rigorous"] for c in critical)

    if closed:
        remaining = []
    else:
        remaining = [
            f"{c['id']}（{c['name'].split('：')[0]}）：{c['missing']}"
            + (f"——{c['quant']}" if c["quant"] else "")
            for c in critical if not c["rigorous"]
        ]

    import math as _math
    r_formula = _math.sqrt(2 * float(delta_E) / float(lam))
    chain_res = {
        "mStar": m_star,
        "zStarInterval": lmin["zStarInterval"],
        "capDeltaE": {"exact": str(delta_E), "float": float(delta_E)},
        "lambdaMinQuotient": {"certified": str(lam),
                              "cross_impl_tube_mu0":
                                  tube["rigorous_lambda_min"]["mu0"],
                              "numeric": tube["hessian"]["lambda_min_quotient"],
                              "l6_point_cert":
                                  l6["lambda0"]["certified"] if l6 else None},
        "tubeRadius": {
            "formula_value_advisory": r_formula,
            "l6_rigorous_radius": (l6["quadraticGrowth"]["rigorousRadius"]
                                   if l6 else None),
            "l6_target_certified": (
                l6["reconciliation"]["rTargetFormula"]["certifiedHere"]
                if l6 else None),
            "note": ("公式值 sqrt(2ΔE/λ) 为 advisory；严格半径以 l6_intube.json "
                     "quadraticGrowth.rigorousRadius 为准（D1 主链 L6 口径）"),
        },
        "components": comp,
        "closed": closed,
        "closedSemantics": (
            "closed = 关键路径组件（L0,L1,L2,L3,L5,L6,L7）全部 rigorous"
            "（裁决 D1/D12：L4 记 onCriticalPath=false 备选离散路线，不入合取；"
            "其处置条目与引用 notes/decisions.md §1-D1/§D12 必须在账——见 L4 "
            "组件；R7-2 已交付精确层＋稳定层，分层 rigorous 如实分记）"),
        "mainChain": ("L2→L3→L5→L6（D1/D12；L5=Procrustes 已严格，重构走 "
                      "Gram 扰动→d_P≤C·δ→管内二次增长；R7-3 后 caliber(c) 口径"
                      "下 L3-need/L5 过、L6 缺 " + l6_deficit_txt +
                      "——终卡点在 L6）"),
        "blocking": [c["id"] for c in critical if not c["rigorous"]],
    }
    return chain_res, remaining, closed, cited_extra


# ============================================================ 证书进程外重验证

def reverify(py: str, cited: list) -> dict:
    """全部被引证书进程外重验证＋l3/l6 账本幂等重跑门。任一失败 ⇒ exit 1。"""
    out = {}
    for entry in cited:
        key, cmd = entry["reverifyKey"], entry.get("verifyCmd")
        if key == "hp_reproduce":
            sol = (REPO / "numerics/bounds/results/hp_solution_midlarge_m090.json")
            tmp = "/tmp/hp_cert_endgame_reverify.json"
            full = [py, "numerics/bounds/sdp_certify.py", "--solution", str(sol),
                    "--min-bound", "25.752410818", "--ref-safe",
                    "25.759446386373018", "--k", "64", "--out", tmp]
            t0 = time.time()
            r = subprocess.run(full, cwd=str(REPO), capture_output=True,
                               text=True, timeout=3600)
            if r.returncode != 0:
                fail(f"HP 证书重生成失败：\n{r.stdout}\n{r.stderr}")
            a = frac(load_json(Path(tmp))["claimed_bound"])
            b = frac(load_json(REPO / entry["path"])["claimed_bound"])
            out[key] = {"cmd": " ".join(full), "exit": r.returncode,
                        "claimed_bound_reproduced": str(a),
                        "bitwise_equal_to_archive": a == b,
                        "wall_s": round(time.time() - t0, 1)}
            print(f"[reverify] {key}: bitwise_equal={a == b}", flush=True)
            if a != b:
                fail("HP 证书重生成与存档不逐位一致")
            continue
        if not cmd:
            fail(f"被引证书 {entry['path']} 无 verify 命令")
        full = [py] + cmd
        t0 = time.time()
        r = subprocess.run(full, cwd=str(REPO), capture_output=True, text=True,
                           timeout=3600)
        out[key] = {"cmd": " ".join(full), "exit": r.returncode,
                    "tail": (r.stdout or r.stderr).strip().splitlines()[-2:],
                    "wall_s": round(time.time() - t0, 1)}
        print(f"[reverify] {key}: exit={r.returncode} "
              f"({out[key]['wall_s']}s)", flush=True)
        if r.returncode != 0:
            fail(f"证书重验证失败：{key}\n{out[key]['tail']}")

    # l3/l6/l4_orbit 账本幂等重跑门（确定性重算与存档比对，不重写）
    for key, script in (("l3_analytic_rerun", "numerics/bounds/l3_analytic.py"),
                        ("l6_intube_rerun", "numerics/bounds/l6_intube.py"),
                        ("l4_orbit_rerun", "numerics/bounds/l4_orbit.py")):
        t0 = time.time()
        r = subprocess.run([py, script], cwd=str(REPO), capture_output=True,
                           text=True, timeout=3600)
        out[key] = {"cmd": f"{py} {script}", "exit": r.returncode,
                    "tail": (r.stdout or r.stderr).strip().splitlines()[-2:],
                    "wall_s": round(time.time() - t0, 1)}
        print(f"[reverify] {key}: exit={r.returncode} ({out[key]['wall_s']}s)",
              flush=True)
        if r.returncode != 0:
            fail(f"账本幂等重跑失败：{key}\n{out[key]['tail']}")

    out["all_pass"] = True
    return out


# ======================================================================== main

def main() -> None:
    ap = argparse.ArgumentParser(
        description="Round 8（campaign 第 3 轮）收口链装配与闭合判定（v3）")
    ap.add_argument("--reverify-certs", action="store_true",
                    help="进程外重验证全部被引证书＋l3/l6/l4_orbit 幂等重跑门")
    ap.add_argument("--out", type=str, default=str(OUT))
    args = ap.parse_args()

    t0 = time.time()
    energies = load_json(WORKFLOW_DATA)["energies"]["9"]
    E_star = frac(energies["value"])
    assert E_star == Fraction("25.759986531"), float(E_star)

    # 账本间 E* 一致性
    for path, key in (("slab_band.json", "E_star"), ("strips.json", "E_star"),
                      ("typed_ladder.json", "E_star")):
        assert frac(load_json(RESULTS / path)[key]) == E_star, path
    assert frac(load_json(RESULTS / "tube.json")["meta"]["E_star"]) == E_star

    # R7 存档 assembledRecord 基准（splice-map 联动判定，D20 裁决 4）：
    # 固定常量（898c522 落盘）；若 OUT 仍是 R7 版则断言盘上值与常量一致
    r7_record = frac(R7_ASSEMBLED)
    if OUT.exists():
        old = load_json(OUT)
        if old.get("kind") == "n9-endgame-round7":
            assert frac(old["assembledRecord"]["value"]) == r7_record, \
                "盘上 R7 存档 assembledRecord 与基准常量不符（898c522 口径）"

    # 覆盖分析 → 组件判定 → 装配（closed 决定 cap 区域抬升）
    r8 = read_round8()
    pieces, holes, hp_used, strips_info = coverage(E_star)
    cap_sel = select_cap(r8)
    chain_res, remaining, closed, cited_extra = chain(
        E_star, hp_used, holes, cap_sel, strips_info, r8, r7_record)
    regions, assembled, bottleneck, criterion, cited = assemble(
        E_star, closed, pieces, holes, hp_used, cap_sel)

    # ---- splice-map 联动机器判定（D20 裁决 4）＋ L7 文案回填 ----
    if assembled == r7_record:
        splice_verdict = {
            "verdict": ("维持 v2（Round 8 记账值与 R7 存档逐位相等——D16 "
                        "裁决 5 逆否分支；不出 v3 节，留痕即可）"),
            "assembled_equal_R7": True}
    else:
        splice_verdict = {
            "verdict": ("assembledRecord 变 ⇒ splice-map 须出 v3 同步（D16 "
                        "裁决 5 逆否成立分支——收口会话同步落笔 v3 节；"
                        "未落笔 ⇒ 本账本与 splice-map.md 失配，验收门拦截）"),
            "assembled_equal_R7": False,
            "r7_value": str(r7_record), "r8_value": str(assembled)}
        l7c = next(c for c in chain_res["components"] if c["id"] == "L7")
        l7c["status"] = l7c["status"].replace(
            "Round 8 版本判定见 spliceMapVerdict——D20 裁决 4 机器判定，装配后回填",
            "Round 8 记账值已变 ⇒ splice-map v3 同步（D20 裁决 4）")
    if splice_verdict["assembled_equal_R7"]:
        l7c = next(c for c in chain_res["components"] if c["id"] == "L7")
        l7c["status"] = l7c["status"].replace(
            "Round 8 版本判定见 spliceMapVerdict——D20 裁决 4 机器判定，装配后回填",
            "Round 8 记账值未变 ⇒ splice-map 维持 v2（D20 裁决 4）")

    reverify_res = (reverify(sys.executable, cited) if args.reverify_certs
                    else {"status": "not run（传 --reverify-certs 启用；本文件"
                          "判定只依赖存档账本/证书字段）"})

    # R8B engine-v2 探测结果入 round8Inputs（D29 裁决 2 消费面——三态＋
    # 战役账本 verdict 摘要；探测时点＝本账本生成时刻）
    v2c, v2b, v2led, v2note = read_engine_v2()

    def _v2_ledger_digest():
        out = []
        for w, d in v2led:
            keep = {}
            for k, x in (d.items() if isinstance(d, dict) else []):
                kl = k.lower()
                if any(t in kl for t in ("verdict", "decision", "branch",
                                         "status", "phase", "outcome",
                                         "budget", "canary", "trigger")):
                    keep[k] = x
            out.append({"where": w, "summary": keep})
        return out

    # L1 的重验证佐证（若跑过）
    if isinstance(reverify_res, dict) and reverify_res.get("all_pass"):
        for c in chain_res["components"]:
            if c["id"] == "L1":
                c["quant"] += "；本轮 --reverify-certs 进程外复核 exit 0"

    doc = {
        "kind": "n9-endgame-round8",
        "script": "bounds/endgame_chain.py",
        "code_version": code_version(),
        "timestamp": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "E_star": {"value": str(E_star), "float": float(E_star),
                   "highPrecision": energies["highPrecision"],
                   "source": str(WORKFLOW_DATA),
                   "semantics": "三源校验参考值，非已证最优；全部 ≤/> 断言"
                                "语义为与参考值不矛盾"},
        "architecture": {
            "decision": "C-混合（B 几何骨架＋KLT Hermite 引擎）",
            "source": "notes/architecture-decision.md §2（Round 5，escalated=false）",
            "mainChain": chain_res["mainChain"],
            "rulings": ["D1（主链 L2→L3→L5→L6，L4 备选）", "D2（cap 验收口径）",
                        "D3（探针节点精确谱值）", "D4（收口任务位）",
                        "D5/D6（hermite-engine）", "D7（L3 常数口径）",
                        "D10（cap 取最优）", "D12（R7 四任务并行排程）",
                        "D13（R7-1 矩容器判死）", "D14（R7-2 L4 计数）",
                        "D15（R7-3 nodeLocal/L6 斜率，原 D14 重编号）",
                        "D19（Round 8 设计：M9 战役＋锚定探针＋L6 联合界）",
                        "D20（Round 8 收口：产出消费时序与自适应记账）"],
            "rulingsSource": "notes/decisions.md §1 及后续 D 条目",
        },
        "round6Inputs": {
            "hermite_strips": strips_info["hermiteLedgerNote"],
            "hermite_cap": cap_sel["note"],
            "l3_analytic": (read_l3()[1]),
            "l6_intube": (read_l6()[1]),
        },
        "round7Inputs": {
            "moment_lift": (read_moment_lift()[1]
                            + "；处置：branch=dead ⇒ 无 a6 证书，cap 片不换记"
                            "（D10/D12 规则下三引擎取最优仍胜出 typed "
                            "25.759571185601），条带行不变（洞片按 D12 延后"
                            " 第 3 轮）"),
            "l4_orbit": read_l4_orbit()[1],
            "l3_nodeLocal": (
                f"nodeLocal 层 present="
                f"{bool(load_json(L3_ANALYTIC).get('nodeLocal', {}).get('present'))}"
                f"（R7-3：C_glob∈[1.596355678e-7,1.597953632e-7]，判据余量 "
                f"74.6×；caliber(c) L3-need 74.6×/L5 6390×/L6 缺 22.5×；"
                f"D7 可回滚点『认证常数重跑链判定』已兑现——链判定字段以 "
                f"C_glob 刷新，结论仍 fail（现行 ε_forcing 下 ρ_raw=51.0 "
                f"vacuous））"),
            "l6_slope": (
                f"r*=0.003359199152→{load_json(L6_INTUBE)['quadraticGrowth']['rigorousRadius']}"
                f"（2.00×，K-lift 斜率 12.836＋BD2 box 二阶通道；μ@r* "
                f"0.0021870→0.0119344）"),
        },
        "round8Inputs": {
            "consumptionRule": ("D20 裁决 1/2（产出自适应）：R8-1/2/3 与收口"
                                "并行调度，产出在盘则按既有 schema 自动入账、"
                                "未到盘则如实记 missing＋维持 R7 记账值；探测"
                                "时点＝本账本生成时刻"),
            "m9_strips": r8["m9_strips"],
            "m9_cap": r8["m9_cap"],
            "anchor_probe": r8["anchor_probe"],
            "l6_joint": r8["l6_joint"],
            "capSelection": cap_sel["note"],
            "engineV2": {
                "onDisk": bool(v2c or v2b or v2led),
                "certified": [{"tag": r_["tag"], "M": r_.get("M"),
                               "variant": _v2_variant_of(r_),
                               "certified": r_.get("certified"),
                               "certificate": r_.get("certificate")}
                              for r_ in v2c],
                "blocked": [{"tag": r_["tag"], "M": r_.get("M"),
                             "variant": _v2_variant_of(r_),
                             "certified": r_.get("certified"),
                             "best_certified_attempt":
                                 r_.get("best_certified_attempt")}
                            for r_ in v2b],
                "ledgers": _v2_ledger_digest(),
                "note": v2note,
            },
        },
        "spliceMapVerdict": splice_verdict,
        "partition": [{
            "region": r["region"], "piece": r["piece"],
            "bound": str(r["bound"]), "bound_float": float(r["bound"]),
            "margin_vs_E_star": float(r["bound"] - E_star),
            "coverPiece": ("exclusion（区域不含 TTP，须 > E*）" if r["exclusion"]
                           else "TTP-covering（证书域含 TTP，须 ≤ E*+1e-6）")}
            for r in regions],
        "strips": strips_info,
        "assembledRecord": {
            "criterion": criterion,
            "value": str(assembled), "float": float(assembled),
            "margin_vs_E_star": float(E_star - assembled),
            "bottleneck": bottleneck,
            "chainLift": ("closed=true ⇒ cap 区域界抬到 max(cert, E*)（D1 主链）"
                          if closed else
                          "未启用（closed=false ⇒ 证书口径 min）"),
            "wouldBe_if_chain_closed": {"value": str(E_star),
                                        "float": float(E_star)},
        },
        "endgameChain": chain_res,
        "remainingGap": remaining,
        "citedCertificates": cited,
        "citedLedgers": cited_extra,
        "certReverify": reverify_res,
    }

    # ---- 判定逻辑自洽断言（exit 0 的充要内容；closed 真假均允许）----
    comp = doc["endgameChain"]["components"]
    critical = [c for c in comp if c.get("onCriticalPath", True)]
    assert doc["endgameChain"]["closed"] == all(c["rigorous"] for c in critical)
    if doc["endgameChain"]["closed"]:
        assert not doc["remainingGap"], "closed=true 但 remainingGap 非空"
        assert not holes, "closed=true 但 L0 有洞"
        assert frac(doc["assembledRecord"]["value"]) >= E_star, \
            "closed=true 但 assembledRecord < E*"
    else:
        assert doc["remainingGap"], "closed=false 须有 remainingGap"
        assert doc["endgameChain"]["blocking"], "closed=false 须列出断点"
    assert doc["assembledRecord"]["float"] == float(
        min(frac(r["bound"]) for r in regions))
    ex = [r for r in regions if r["exclusion"]]
    tc = [r for r in regions if not r["exclusion"]]
    assert all(r["bound"] > E_star for r in ex)
    assert all(r["bound"] <= E_star + TOL_ESTAR for r in tc)
    # L4 处置在账（D1/D12，v2.x 起：分层记账后仍须引用两条裁决）
    l4c = next(c for c in comp if c["id"] == "L4")
    l4j = json.dumps(l4c, ensure_ascii=False)
    assert l4c.get("onCriticalPath") is False and "D1" in l4j and "D12" in l4j
    # cap 片记账＝多引擎取最优的机器断言（D10/D16 裁决 2＋D20 裁决 1②：
    # typed M8 / typed M9（在盘时）/ a5 / R7-1 矩容器（在盘时）中 certified
    # 最大者；无证书支撑的候选不参与——本轮 R7-1 判死无矩容器证书）
    cap_region = next(r for r in doc["partition"]
                      if frac(r["region"].split(",")[0][1:]) == A0_CAP)
    expected_cap = (max(cap_sel["bound"], E_star) if doc["endgameChain"]["closed"]
                    else cap_sel["bound"])
    assert frac(cap_region["bound"]) == expected_cap, \
        ("cap 片记账须等于 select_cap 多引擎取最优结果（closed=false），"
         "或链闭合抬升 max(cap, E*)（closed=true）")
    m9_rung = (r8["m9_cap"]["rung"] or {})
    if m9_rung:
        best_incl_m9 = max(
            [frac(next(r for r in load_json(RESULTS / "typed_ladder.json")
                       ["rungs"] if r.get("tag") == "m0748" and r.get("M") == 8)
                  ["certified"]), frac(m9_rung["certified"])])
        assert cap_sel["bound"] >= best_incl_m9, \
            "typed M9 证书在盘 ⇒ cap 片须 ≥ typed M8/M9 之最大者"
    # round8Inputs 完整性（D20 裁决 1/2：四键必在，note 必非空）
    for k in ("m9_strips", "m9_cap", "anchor_probe", "l6_joint"):
        assert k in doc["round8Inputs"] and doc["round8Inputs"][k].get("note"), k
        assert isinstance(doc["round8Inputs"][k].get("onDisk"), bool), k
    # splice-map 联动（D20 裁决 4）：assembledRecord 变 ⇒ splice-map 须 v3
    if splice_verdict.get("assembled_equal_R7") is False:
        sm = (REPO / "notes" / "splice-map.md").read_text(encoding="utf-8")
        assert re.search(r"^#+ .*v3", sm, re.M), \
            "assembledRecord 变但 splice-map.md 无 v3 节（D16 裁决 5 逆否）"

    out_path = Path(args.out)
    with open(out_path, "w") as f:
        json.dump(doc, f, ensure_ascii=False, indent=1)
    print(json.dumps({
        "closed": doc["endgameChain"]["closed"],
        "assembledRecord": doc["assembledRecord"]["float"],
        "bottleneck": bottleneck,
        "blocking": doc["endgameChain"]["blocking"],
        "out": str(out_path), "wall_s": round(time.time() - t0, 1)},
        ensure_ascii=False, indent=1))
    print(f"[done] 收尾判定：closed={doc['endgameChain']['closed']}；"
          f"assembledRecord={doc['assembledRecord']['float']}；写入 {out_path}")


if __name__ == "__main__":
    main()
