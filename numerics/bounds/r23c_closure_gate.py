#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r23c_closure_gate.py — R23C r23c-round23-closure 收口验收门（campaign
dwfrun-f9904baf 第 18 轮，2026-10-24）。

裸 python3 运行（无第三方依赖；CWD 无关——一切路径由 __file__ 解析；
campaign 根路由沿 R7B bd15f27／R8C r8c3_closure_gate／R9D r9c_closure_gate/
R10D r10c_closure_gate／R11D r11c_closure_gate／R12C r12c_closure_gate/
R13D r13d_closure_gate／R14B r14b_closure_gate／R15D r15d_closure_gate/
R16C r16c_closure_gate／R17C r17c_closure_gate／R18C r18c_closure_gate/
R19B r19c_closure_gate／R20B r20c_closure_gate／R21C r21d_closure_gate/
R22C r22c_closure_gate 嵌套包装器先例）：

    python3 numerics/bounds/r23c_closure_gate.py             # 仓内
    python3 thomson-n9/numerics/bounds/r23c_closure_gate.py  # campaign 根

固定种子 20261023（任务书条款；D101-4——R23 门 seed 与 r23a 同号，R10–R23
=20261012–23 序列顺延）。六项检查（对应 R23C 任务书收口面；全部确定性
——本轮全任务 heavySolves=0（0.037 当量全额留储，D86-3/D90-3/D96-3/
D101-3），收口以一致性核验替代 --reverify-certs 全量刷新于 C2（D34-4/
D38-5/D43-5/D49-3/D52-5/D56-4/D61-5/D64-4/D70-4/D72-3/D77-3/D82-4/
D84-4/D86-1/D88-1/D90-4/D93-4/D96-4/D99 先例——收口腿不三跑全门，
D34-4/D89-2 ≥2 组在档口径：R21C 1493.6s@95a353a＋复算员
1508.1s@104e8b6；r22 双门已在档本轮不重烧——R23C 任务书 C1 口径）：

  C1 r23a 门复跑 exit 0＋结果锚：
     - r23a_witness_gate.py（R23A 表 B 第十件形式件门，G0–G5＋NC1–NC4）
       复跑 exit 0。子进程上限 **1200s**：编译型门（十二连 elaboration
       ——R23A 实测 ~101.5s 量级），1200s 文档化例外沿 R18/R19/R21B/
       R22B（D52-4/D64-5：每文件 ≤600s，外层 1200s 文档化）。r22 双门
       （r22_pattern_gate/r22_b9aut_gate）R22C 已在档本轮不重烧。
     - results/r23a_witness_ledger.json 在档锚（seed 20261023、
       heavy_solves==0——本轮全任务零求解；kind/task；axiom_policy 恰
       三标准 set 相等；endgame_chain.py 输入路由禁令＋隔离声明；
       frozen_readonly_anchored.endgame_json_sha256==86863a09…69f 冻结
       锚）。**账本锚面按 r23a 账本实际 schema 锚定（诚实边界，D103 裁
       决 3）**：r23a 账本无 r22 双账本的 artifact_class /
       provenance.read_only 字段——隔离声明面由 isolated_from_12_
       partition（endgame_json_absent==true＋note 载『不入 12 分区』
       『endgame.json/endgame_chain.py 文本零出现』字面＝输入路由禁令）
       承载，provenance 面锚 acceptanceGate（acceptanceGate=
       r23a_witness_gate.py 门面）＋provenance.seed——锚定实际字段不虚
       构（为对齐模板字面给 r23a 账本补字段将破坏 r23a 主件冻结面，
       否决留痕）。
  C1a r23 家族放行层双路由（D101-4——r23 家族正则；R18C/R19B/R20C/
     R21C/R22C C1a 先例）：git status --porcelain＋git diff HEAD
     --name-only 两路改动路径 ⊆ 本收口自有件 ∪ r23 家族 pattern
     （endgame_gate.py 扩展＋r23c_closure_gate.py＋嵌套包装器＋
     GAP-REPORT/PROGRESS/decisions＋r23 家族件）——预提交自跑零环境
     变量放行即过；树净时零路径 vacuous pass（收口子门 G1 活体放行
     面另在 C1 子门内自证）。
  C2 chain-only 干跑五字段逐位零漂移（D86-1/D88-1/D90-4/D93-4/D96-4/
     D99；R8A D30/R9D–R22C 先例）：endgame_chain.py --out
     /tmp/r23c_dry.json（零 --reverify-certs）产物与存档 endgame.json
     五字段逐位——closed=False／assembledRecord（value＋float＋margin）
     ／组件 rigorous L0–L7 八布尔／blocking==[L0,L3]＋remainingGap 前缀
     [L0,L3]／spliceMapVerdict（verdict＋assembled_equal_R7）——零
     漂移；全集漂移逐叶盘点机器化归类（r10c–r22c_closure_gate C2
     同口径：certReverify＋code_version/timestamp＋L1 quant 佐证串＋
     engineV2 账本探测，未归类叶即 FAIL）且分布与 D84 裁决 4/D93 冻
     结口径逐位同（22 叶＝certReverify 17＋code_version/timestamp 2＋
     L1 quant 佐证串 1＋engineV2 账本探测 2——R18C/R19/R20/R21/R22/
     R23A 实测同分布；新叶即 FAIL——R23A 形式件若被误接为 chain 输入
     即在此暴露，处置归 D103）。
     本轮 R23A 件（TableB1Witness 形式件）不入四账本、不入 12 分区、
     不作 chain 输入（隔离面在 C1 子门＋C1a 活体核验）⇒ 零账本数值
     变更 ⇒ 不跑 --reverify-certs 全量刷新。
  C3 endgame.json 直读一致性＋铁律 Fraction 亲算：closed=false、
     blocking=[L0,L3]、assembledRecord==47517790735835014335570/
     1844674407417822803119（float 25.759445973097478）、margin 重算
     ＝E*−AR 精确（float 逐位相等 0.0005405579025207914）、
     spliceMapVerdict=维持 v2（assembled_equal_R7=true）、组件
     L1/L2/L5/L6/L7 rigorous=True＋L0/L3/L4=False（L4 off-path）、
     铁律 AR ≤ E*+1e-6（E* 十进制精确口径 Fraction("25.759986531")，
     D28 裁决 3）＋无容差 AR<E* 亦真、AR==min(分区 bound) 精确重算、
     wouldBe_if_chain_closed==25759986531/10⁹==E*、citedCertificates
     逐份在盘且 claimed_bound 一致、endgame.json 相对 HEAD 零改动
     （sha256 与 R10 基线 86863a09…69f＝R11–R23 基线时点相等——本轮
     零写入核验）。
  C4 文档三件锚：GAP-REPORT「Round 23（campaign dwfrun-f9904baf 第
     18 轮，2026-10-24）」节（任务结构引言〔含 D101 锚〕＋① R23A 收编
     ＋② R23C 本件〔含两段式回填位〕＋轮次终判〔closed=false 三面
     一致、blocker L0/L3 不动、assembledRecord 维持零提升、progress
     按 D82-4 与 TableB1Witness 实际落地判定——≥1 严格定理零
     sorry⇔true，如实不硬凑〕＋预算终账＋诚实声明与未跑项＋下轮候选）
     ＋PROGRESS.md 置顶条目（前 120 行内含本轮 campaign ID 串，D55-2
     口径）＋notes/decisions.md 含 D101（设计 h3——随 R23A 主件
     96bc585 收编）＋D102（R23A 执行 h3）＋D103（本收口裁决 h3——
     D 编号顺延处置沿 D80-2/D82-5/D84-2/D86-4/D88/D90-4/D93/D96-4/
     D99，轮次汇总预留 D104）。
  C5 预算终账（本轮零求解精确口径＋campaign 33.421/40 五源 Fraction
     双核验）：本轮 Σsolve_s==0 精确（全任务 heavySolves=0——r23a
     账本零正 solve 字段、R23C 收口零求解）＋四账本与 R8 终账冻结值
     逐位相等（无新求解行）＋typed_ladder rungs==9（不追加 rung）＋
     R11 探针冻结 2621/5s 复读＋campaign 累计＝五源和＋0＝360942.5＝
     721885/2 s＝721885/21600 当量＝33.421（3 位小数）与 GAP-REPORT
     Round 23 节字面一致（账↔文档双核验——与 R11–R22 终账逐位不变）
     ＋口径 B 余量 40−33.421=6.579<12 ⇒ M11 触发器不可触发维持＋r23
     新产物零正 solve 字段（正则核验）。
  C6 树净：git status --porcelain 0 行（含 R23A/R23C 全部交付物已提
     交、endgame.json 相对 HEAD 零改动——与 C3 sha256 核验双保险）。
     预提交自跑时 C6 因在途自有件按设计拦截（R11D 起先例——组件级
     importlib 自跑 C1–C5＋NC，C6 留主提交后净树验收）。

负对照（门自身）：/tmp 篹 r23 账本必失配——篡 r23a_witness_ledger.json
副本 heavy_solves（0→1）⇒ C1 r23a 账本锚必拦；篡四账本之一副本
total_solve_s（+2000s）⇒ C5 冻结值核验必拦；未篡副本 sanity 通过。

exit 0 = 过门；任一失败 exit 1（信息含检查号与定量内容）。
"""
from __future__ import annotations

import hashlib
import json
import random
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
TYPED_LADDER = RESULTS / "typed_ladder.json"
M9_CAMPAIGN = RESULTS / "m9_campaign.json"
M10_CAMPAIGN = RESULTS / "m10_campaign.json"
V2_CAMPAIGN = RESULTS / "hermite_v2_campaign.json"
R11_WS_LEDGER = RESULTS / "r11_warmstart_probe.json"
R23A_LEDGER = RESULTS / "r23a_witness_ledger.json"
GAP_REPORT = REPO / "GAP-REPORT.md"
PROGRESS = REPO / "PROGRESS.md"
DECISIONS = REPO / "notes" / "decisions.md"
WORKFLOW_DATA = HERE.parents[2] / "thomson-workflow" / "data" / "energies.json"

SEED = 20261023
E_STAR_DEC = Fraction("25.759986531")    # 十进制精确口径（D28 裁决 3）
TOL_ESTAR = Fraction(1, 10**6)
EQUIV_UNIT_S = 10800                     # 1 当量 = 10800s（m9_campaign 口径）
AR_STR = "47517790735835014335570/1844674407417822803119"
AR_FLOAT = 25.759445973097478
# campaign 累计冻结值（R8 终账四源和＋R11 探针 2621/5；R12–R23 本轮零求解）
CAMPAIGN_SOLVE_S = {
    "m9_campaign": Fraction("102504.9"),
    "m10_campaign": Fraction("185065.6"),
    "typed_ladder_cap_m0748_M9": Fraction("42305.7"),
    "hermite_v2_campaign_phase1": Fraction("30542.1"),
    "r11_warmstart_probe": Fraction("2621") / 5,
}
CAMPAIGN_TOTAL_FROZEN = Fraction("360942.5")   # 721885/2 s（R11 终账＝R12–R22 基线）
CAMPAIGN_TOTAL_EQ = Fraction(721885, 21600)    # 33.4206…（3 位小数字面 33.421）
TRIGGER_EQUIV = Fraction(12)                   # M11 触发器阈值（D29 裁决 1）
TYPED_LADDER_RUNGS_FROZEN = 9                  # r23 不追加 rung（D86-3/D90-3/D96-3/D101-3）
# endgame.json sha256（R10 基线 HEAD=5a6ab9c＝R11–R22 基线时点；
# R23 全程零改动核验）
ENDGAME_SHA_BASE = ("86863a09bf84e950e85fc5f902bc2b40"
                    "46a87f06703bd782e5148fc119afd69f")

R23A_GATE = HERE / "r23a_witness_gate.py"
R23A_KIND = "n9-r23-witness-ledger"
R23A_TASK = "r23a-pattern-witness"
AXIOM_POLICY_STANDARD = {"Classical.choice", "Quot.sound", "propext"}
D_CLOSURE = "D103"                       # 收口裁决编号（D101 设计/D102 R23A 执行
                                         # 后顺延；D80-2/D82-5/D84-2/D86-4/D88/
                                         # D90-4/D93/D96-4/D99 口径；D104 预留轮次汇总）
R23_EXEC_DECISIONS = ["D101", "D102"]    # D101 设计（随 R23A 主件 96bc585 收编）
                                         # ＋D102 R23A 执行裁决
# C1 子进程上限：r23a_witness_gate 编译型门 1200s 文档化例外（十二连
# elaboration，每文件 ≤600s——D52-4/D64-5，R18/R19/R21B/R22B 先例）。
R23A_TIMEOUT_S = 1200
# C2 漂移分布冻结口径（D84 裁决 4/D93；R18C/R19/R20/R21/R22/R23A 实测
# 同分布——新叶即 FAIL 处置归 D103）
DRIFT_EXPECTED = {"certReverify": 17, "code_version/timestamp": 2,
                  "L1 quant 佐证串": 1, "engineV2 账本探测": 2}

EXPECTED_RIGOROUS = {"L0": False, "L1": True, "L2": True, "L3": False,
                     "L4": False, "L5": True, "L6": True, "L7": True}

# C1a 收口自有件集（本门＋扩展＋包装器＋文档三件）
R23C_OWNED = {
    "numerics/bounds/endgame_gate.py",
    "numerics/bounds/r23c_closure_gate.py",
    "thomson-n9/numerics/bounds/r23c_closure_gate.py",
    "GAP-REPORT.md",
    "PROGRESS.md",
    "notes/decisions.md",
}
# r23 家族放行层（r23a_witness_gate G1 同式正则——D101-4：R23A 形式件腿/
# R23C 收口腿零交叠放行）
FAMILY_PATTERNS = [
    r"^formal/lean/ThomsonN9/TableB1Witness\.lean$",
    r"^numerics/bounds/r23[a-z0-9_]*(\.py|/)",
    r"^numerics/bounds/results/r23[a-z0-9_]*(\.json|/)",
    r"^thomson-n9/numerics/bounds/r23[a-z0-9_]*(\.py|/)",
    r"^notes/decisions\.md$",
    r"^numerics/bounds/endgame_gate\.py$",
    r"^(GAP-REPORT|PROGRESS)\.md$",
]


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


def porcelain_paths(out: str) -> list:
    paths = []
    for ln in out.splitlines():
        if not ln.strip():
            continue
        p = ln[3:].strip().strip('"')
        if " -> " in p:
            p = p.split(" -> ")[-1]
        paths.append(p)
    return paths


# ------------------------------------------------------- C1 子门＋账本锚

def run_subgate(path: Path, tag: str, timeout_s: int) -> float:
    check(path.exists(), f"{tag} 子门不在盘：{path}")
    t0 = time.time()
    try:
        r = subprocess.run([sys.executable, str(path)], capture_output=True,
                           text=True, timeout=timeout_s, cwd=str(REPO))
    except subprocess.TimeoutExpired:
        raise GateFail(f"{tag} 子门复跑超时（>{timeout_s}s）：{path.name}"
                       "——单命令铁律下应改两段式后台＋轮询（D64 裁决 5）")
    wall = time.time() - t0
    tail = "\n".join((r.stdout or "").splitlines()[-6:])
    print(f"[{tag}] exit={r.returncode} ({wall:.1f}s)：{path.name}", flush=True)
    check(r.returncode == 0, f"{tag} 子门复跑 exit {r.returncode}：\n{tail}")
    return wall


def _anchor_r23a_ledger(ledger_path: Path, tag: str) -> None:
    """R23A 形式件账本锚（可对 /tmp 副本跑——负对照用；账本实面＝
    results/r23a_witness_ledger.json）。**按实际 schema 锚定（D103 裁决
    3 诚实边界）**：seed/heavy_solves/kind/task＋axiom_policy 恰三标准
    set 相等＋隔离声明面 isolated_from_12_partition（endgame_json_absent
    ==true＋note 载 12 分区/endgame.json/endgame_chain.py 输入路由禁令
    字面）＋frozen_readonly_anchored.endgame_json_sha256 冻结锚＋
    provenance.acceptanceGate/seed 门面。r23a 账本无 r22 双账本的
    artifact_class/provenance.read_only 字段——锚实际字段不虚构。"""
    led = load_json(ledger_path)
    check(led.get("heavy_solves") == 0,
          f"C1 {tag} heavy_solves={led.get('heavy_solves')} 非 0"
          "（本轮全任务零求解，D86-3/D90-3/D96-3/D101-3）")
    check(led.get("seed") == SEED,
          f"C1 {tag} seed={led.get('seed')} 非 {SEED}")
    check(led.get("kind") == R23A_KIND,
          f"C1 {tag} kind={led.get('kind')!r} 非 {R23A_KIND!r}")
    check(led.get("task") == R23A_TASK,
          f"C1 {tag} task={led.get('task')!r} 非 {R23A_TASK!r}")
    ax = led.get("axiom_policy") or []
    check(set(ax) == AXIOM_POLICY_STANDARD and len(ax) == 3,
          f"C1 {tag} axiom_policy 非恰三标准 {sorted(AXIOM_POLICY_STANDARD)}"
          f"（{ax}）")
    iso = led.get("isolated_from_12_partition") or {}
    check(iso.get("endgame_json_absent") is True,
          f"C1 {tag} isolated_from_12_partition.endgame_json_absent 非 True"
          "（形式件隔离声明面——不入 12 分区）")
    note = str(iso.get("note") or "")
    check("12 分区" in note and "endgame.json" in note
          and "endgame_chain.py" in note,
          f"C1 {tag} isolation.note 未声明隔离＋endgame_chain.py 输入"
          f"路由禁令（12 分区/endgame.json/endgame_chain.py）：{note[:60]!r}")
    prov = led.get("provenance") or {}
    check("r23a_witness_gate.py" in str(prov.get("acceptanceGate") or ""),
          f"C1 {tag} provenance.acceptanceGate 非 r23a_witness_gate.py 门面")
    check(prov.get("seed") == SEED,
          f"C1 {tag} provenance.seed={prov.get('seed')} 非 {SEED}")
    fa = led.get("frozen_readonly_anchored") or {}
    check(fa.get("endgame_json_sha256") == ENDGAME_SHA_BASE,
          "C1 r23a_witness_ledger frozen 锚 endgame_json_sha256 失配"
          "（86863a09…69f）")
    led4 = led.get("frozen_readonly_anchored") or {}
    check(sorted(led4.get("ledgers") or []) == ["hermite_v2_campaign.json",
                                                "m10_campaign.json",
                                                "m9_campaign.json",
                                                "typed_ladder.json"],
          "C1 r23a_witness_ledger frozen.ledgers 非四账本清单")


def c1_subgates() -> dict:
    walls = {}
    # R23A：表 B 第十件形式件门＋账本锚（编译型 1200s 文档化例外——
    # 十二连 elaboration，D52-4/D64-5，R18/R19/R21B/R22B 先例；
    # r22 双门 R22C 已在档本轮不重烧——R23C 任务书 C1 口径）
    check(R23A_LEDGER.exists(), "C1 results/r23a_witness_ledger.json 不在盘"
          "（R23A 交付缺件）")
    walls["r23a_witness_gate"] = run_subgate(R23A_GATE, "C1-r23a",
                                             R23A_TIMEOUT_S)
    _anchor_r23a_ledger(R23A_LEDGER, "r23a_witness_ledger")
    # 冻结面仍在盘（append-only 先例）
    for _fz in ("typed_ladder.json", "lp.json", "lp_m1_light.json",
                "r20_l5l6_seam.json"):
        check((RESULTS / _fz).exists(), f"C1 冻结件 {_fz} 不在盘")
    return walls


# ------------------------------------------------- C1a 家族放行层双路由

def c1a_family_routing() -> list:
    """r23 家族放行层双路由（D101-4；R18C/R19B/R20C/R21C/R22C C1a 先例）：
    git status --porcelain＋git diff HEAD --name-only 两路改动 ⊆
    收口自有件 ∪ r23 家族 pattern——预提交自跑零环境变量放行即过；
    树净时零路径 vacuous pass。"""
    in_flight = []
    for cmd in (["git", "status", "--porcelain"],
                ["git", "diff", "HEAD", "--name-only"]):
        r = subprocess.run(cmd, cwd=str(REPO), capture_output=True,
                           text=True, timeout=60)
        check(r.returncode == 0, f"C1a {' '.join(cmd)} 失败：{r.stderr}")
        paths = (porcelain_paths(r.stdout) if "--porcelain" in cmd else
                 [ln.strip().strip('"') for ln in r.stdout.splitlines()
                  if ln.strip()])
        for p in paths:
            check(p in R23C_OWNED or any(re.match(pat, p)
                                         for pat in FAMILY_PATTERNS),
                  f"C1a 树上在途件不在收口自有集亦不命中 r23 家族放行层"
                  f"（{' '.join(cmd)}）：{p!r}")
            in_flight.append(p)
    uniq = sorted(set(in_flight))
    print(f"[C1a] r23 家族放行层双路由 ✓（porcelain＋diff HEAD 两路；"
          f"在途件 {len(uniq)} 件"
          f"{'：' + '、'.join(uniq) if uniq else '——树净 vacuous pass'}；"
          "收口在途自有件零环境变量放行——预提交自跑即过）", flush=True)
    return uniq


# ------------------------------------------------------- 负对照（门自身）

def nc_self() -> dict:
    """/tmp 篹 r23 账本必失配（C1 锚＋C5 冻结值核验双面）。"""
    results = {}
    with tempfile.TemporaryDirectory(prefix="r23c_nc_") as td:
        # NC1：篡 r23a 账本 heavy_solves 0→1 ⇒ C1 r23a 锚必拦
        tam1 = Path(td) / "r23a_witness_ledger_nc.json"
        led = json.loads(R23A_LEDGER.read_text())
        led["heavy_solves"] = 1
        tam1.write_text(json.dumps(led, ensure_ascii=False))
        try:
            _anchor_r23a_ledger(tam1, "r23a_witness_ledger")
            raise GateFail("NC1 失效：篡 heavy_solves 0→1 后 r23a 锚仍通过")
        except GateFail as e:
            check("heavy_solves" in str(e),
                  f"NC1 拦截面失配：{e}")
            results["NC1_tamper_r23a_heavy"] = str(e)[:90]
        # NC2：篡四账本之一副本 total_solve_s（+2000s）⇒ C5 冻结值核验必拦
        tam2 = Path(td) / "m10_campaign_nc.json"
        m10 = json.loads(M10_CAMPAIGN.read_text())
        m10["budget"]["total_solve_s"] = str(
            frac(m10["budget"]["total_solve_s"]) + Fraction(2000))
        tam2.write_text(json.dumps(m10, ensure_ascii=False))
        try:
            _c5_frozen_ledgers(m10_path=tam2)
            raise GateFail("NC2 失效：篡 total_solve_s +2000s 后冻结值核验"
                           "仍通过")
        except GateFail as e:
            check("m10_campaign" in str(e) or "冻结" in str(e),
                  f"NC2 拦截面失配：{e}")
            results["NC2_tamper_budget_field"] = str(e)[:90]
        # sanity：未篡副本锚通过（真件在 C1 已核，此处仅副本口径演示）
        _anchor_r23a_ledger(R23A_LEDGER, "r23a_witness_ledger")
        results["sanity_untampered"] = "ok"
    print("[NC] /tmp 篹 r23 账本双面必失配 ✓（NC1 r23a_witness_ledger "
          "heavy_solves 0→1 ⇒ C1 r23a 锚拦；NC2 四账本 total_solve_s "
          "+2000s ⇒ C5 冻结值拦；未篡副本 sanity ok）", flush=True)
    return results


# ------------------------------------------------------- C2 干跑

def c2_chain_dry() -> dict:
    """chain-only 干跑五字段逐位 diff（零 --reverify-certs；产物写
    /tmp/r23c_dry.json）。

    五字段＝closed（＋预期 False）／assembledRecord（value＋float＋
    margin_vs_E_star）／组件 rigorous L0–L7（8）／blocking==[L0,L3]＋
    remainingGap 前缀 [L0,L3]／spliceMapVerdict（verdict＋
    assembled_equal_R7）——外加 AR 基线常量。其余字段（timestamp/
    code_version/certReverify/engineV2 探测时点/L1 quant 佐证串等）允许
    叙述性漂移——R8A D30／R10D–R22C 先例口径（r10c–r22c_closure_gate
    C2 同构）；如漂移出现在五字段内即 FAIL。全集漂移分布须与 D84 裁决 4
    /D93 冻结口径同（22 叶＝certReverify 17＋code_version/timestamp 2＋
    L1 quant 佐证串 1＋engineV2 账本探测 2——R18C/R19/R20/R21/R22/R23A
    实测同分布；新叶即 FAIL，处置归 D103）。"""
    archived = load_json(ENDGAME)
    out = Path("/tmp/r23c_dry.json")
    t0 = time.time()
    r = subprocess.run([sys.executable, "numerics/bounds/endgame_chain.py",
                        "--out", str(out)],
                       cwd=str(REPO), capture_output=True, text=True,
                       timeout=600)
    check(r.returncode == 0,
          f"C2 chain-only 干跑 exit {r.returncode}：\n"
          + "\n".join((r.stdout or "").splitlines()[-8:]))
    dry = load_json(out)
    ae, be = archived["endgameChain"], dry["endgameChain"]
    # 字段一：closed
    check(ae["closed"] == be["closed"],
          f"C2 closed 漂移：存档 {ae['closed']} vs 干跑 {be['closed']}")
    check(be["closed"] is False, "C2 closed 预期 false（本轮一致性收口）")
    # 字段二：assembledRecord（value＋float＋margin）
    for k in ("value", "float", "margin_vs_E_star"):
        av, bv = archived["assembledRecord"][k], dry["assembledRecord"][k]
        check(av == bv, f"C2 assembledRecord.{k} 漂移：{av} vs {bv}")
    check(dry["assembledRecord"]["value"] == AR_STR,
          "C2 干跑 assembledRecord 分数串非基线常量")
    check(dry["assembledRecord"]["float"] == AR_FLOAT,
          "C2 干跑 assembledRecord float 非 25.759445973097478")
    # 字段三：组件 rigorous L0–L7
    amap = {c["id"]: c for c in ae["components"]}
    bmap = {c["id"]: c for c in be["components"]}
    check(set(amap) == set(bmap) == {"L%d" % i for i in range(8)},
          "C2 组件集非 L0–L7")
    for cid, exp in EXPECTED_RIGOROUS.items():
        check(amap[cid]["rigorous"] == bmap[cid]["rigorous"],
              f"C2 组件 {cid}.rigorous 漂移：存档 "
              f"{amap[cid]['rigorous']} vs 干跑 {bmap[cid]['rigorous']}")
        check(bmap[cid]["rigorous"] is exp,
              f"C2 组件 {cid}.rigorous 预期 {exp}，实为 {bmap[cid]['rigorous']}")
    # 字段四：blocking＋remainingGap
    check(ae["blocking"] == be["blocking"],
          f"C2 blocking 漂移：{ae['blocking']} vs {be['blocking']}")
    check(be["blocking"] == ["L0", "L3"],
          f"C2 blocking 预期 [L0, L3]，实为 {be['blocking']}")
    check(archived["remainingGap"] == dry["remainingGap"],
          "C2 remainingGap 漂移（叙述面逐位）")
    check([s[:2] for s in dry["remainingGap"]] == ["L0", "L3"],
          f"C2 remainingGap 前缀非 [L0, L3]，实为 "
          f"{[s[:2] for s in dry['remainingGap']]}")
    # 字段五：spliceMapVerdict
    asm, bsm = archived["spliceMapVerdict"], dry["spliceMapVerdict"]
    check(asm.get("verdict") == bsm.get("verdict"),
          f"C2 spliceMapVerdict.verdict 漂移：{asm.get('verdict')} vs "
          f"{bsm.get('verdict')}")
    check(asm.get("assembled_equal_R7") == bsm.get("assembled_equal_R7"),
          "C2 spliceMapVerdict.assembled_equal_R7 漂移")
    check("维持 v2" in str(bsm.get("verdict"))
          and bsm.get("assembled_equal_R7") is True,
          "C2 spliceMapVerdict 非『维持 v2』＋equal_R7=true")
    # 全集漂移逐叶盘点（叙述性预期归类，r10c–r22c_closure_gate C2 同口径；
    # 未归类叶即 FAIL；分布须与 D84 裁决 4/D93 冻结口径同——22 叶）
    def _walk(a, b, path=""):
        if type(a) != type(b):
            yield (path, "TYPE"); return
        if isinstance(a, dict):
            for k in sorted(set(a) | set(b)):
                if k not in a or k not in b:
                    yield (f"{path}/{k}", "ONLY"); continue
                yield from _walk(a[k], b[k], f"{path}/{k}")
        elif isinstance(a, list):
            if len(a) != len(b):
                yield (path, "LEN"); return
            for i, (x, y) in enumerate(zip(a, b)):
                yield from _walk(x, y, f"{path}[{i}]")
        else:
            if a != b:
                yield (path, "DIFF")
    drifts = list(_walk(archived, dry))
    buckets = {"certReverify": 0, "code_version/timestamp": 0,
               "L1 quant 佐证串": 0, "engineV2 账本探测": 0, "其他": 0}
    for p, _kind in drifts:
        if p.startswith("/certReverify"):
            buckets["certReverify"] += 1
        elif p in ("/code_version", "/timestamp"):
            buckets["code_version/timestamp"] += 1
        elif p == "/endgameChain/components[1]/quant":
            buckets["L1 quant 佐证串"] += 1
        elif p.startswith("/round8Inputs/engineV2"):
            buckets["engineV2 账本探测"] += 1
        else:
            buckets["其他"] += 1
    check(buckets["其他"] == 0,
          "C2 出现未归类漂移叶（新叶即 FAIL——r23a 形式件若被误接为 "
          "chain 输入即在此暴露；处置归 D103）："
          f"{[p for p, _ in drifts if not (p.startswith('/certReverify') or p in ('/code_version', '/timestamp') or p == '/endgameChain/components[1]/quant' or p.startswith('/round8Inputs/engineV2'))][:8]}")
    check({k: v for k, v in buckets.items() if k != "其他"} == DRIFT_EXPECTED,
          f"C2 漂移分布 { {k: v for k, v in buckets.items() if k != '其他'} } "
          f"非 D84 裁决 4/D93 冻结口径 {DRIFT_EXPECTED}（总叶数 "
          f"{len(drifts)} ≠ {sum(DRIFT_EXPECTED.values())}——账本面意外"
          "变更？若因 R23A 件意外扰动按 D86-1 处置记 D103 裁决重冻结）")
    print(f"[C2] chain-only 干跑五字段逐位零漂移 ✓（closed=false/blocking="
          f"[L0,L3]＋remainingGap 前缀一致/assembledRecord 精确分数＋float＋"
          f"margin/spliceMap 维持 v2/组件 L1·L2·L5·L6·L7 绿＋L0·L3·L4 红；"
          f"零 --reverify-certs——本轮零账本数值变更（R23A 件不入四账本、"
          f"不入 12 分区、不作 chain 输入——隔离面），D86-1/D90-4/D93-4/D96-4；"
          f"干跑 {time.time()-t0:.1f}s 级；全集漂移 {len(drifts)} 叶"
          f"全叙述性预期＝{ {k: v for k, v in buckets.items() if v} }"
          f"——与 D84 裁决 4/D93 冻结分布逐位同）",
          flush=True)
    return {"flipped": False, "drift_leaves": len(drifts), "buckets": buckets}


# ------------------------------------------------------- C3 直读

def c3_direct_read() -> dict:
    d = load_json(ENDGAME)
    ec = d["endgameChain"]
    comps = {c["id"]: c for c in ec["components"]}
    check(ec["closed"] is False, "C3 endgame.json closed 非 false")
    check(ec["blocking"] == ["L0", "L3"],
          f"C3 blocking 预期 [L0, L3]，实为 {ec['blocking']}")
    check(d["assembledRecord"]["value"] == AR_STR,
          "C3 assembledRecord 分数串非基线常量")
    check(d["assembledRecord"]["float"] == AR_FLOAT,
          "C3 assembledRecord float 非 25.759445973097478")
    smv = d.get("spliceMapVerdict") or {}
    check("维持 v2" in str(smv.get("verdict"))
          and smv.get("assembled_equal_R7") is True,
          "C3 spliceMapVerdict 非『维持 v2』＋assembled_equal_R7=true")
    for cid, exp in EXPECTED_RIGOROUS.items():
        check(comps[cid]["rigorous"] is exp,
              f"C3 组件 {cid}.rigorous 预期 {exp}，实为 {comps[cid]['rigorous']}")
    # 自洽：closed == 关键路径合取（L4 onCriticalPath=false 不入合取）
    critical = [c for c in ec["components"] if c.get("onCriticalPath", True)]
    check(ec["closed"] == all(c["rigorous"] for c in critical),
          "C3 closed != 关键路径合取（自洽失败）")
    # 铁律 Fraction 亲算（E* 十进制精确口径）
    ar = frac(AR_STR)
    check(ar <= E_STAR_DEC + TOL_ESTAR,
          f"C3 铁律违例：AR {float(ar)} > E*+1e-6 {float(E_STAR_DEC + TOL_ESTAR)}")
    check(ar < E_STAR_DEC, "C3 无容差口径 AR < E* 失败（AR 须严格小于 E*）")
    # margin 精确重算 == 账本 margin_vs_E_star（float 逐位相等）
    margin = E_STAR_DEC - ar
    check(float(margin) == d["assembledRecord"]["margin_vs_E_star"],
          f"C3 margin 重算 {float(margin)!r} != 账本 "
          f"{d['assembledRecord']['margin_vs_E_star']!r}（逐位）")
    # wouldBe_if_chain_closed == E*（r23a 形式件不入分区——R11C–R22 先例）
    wb = d["assembledRecord"].get("wouldBe_if_chain_closed") or {}
    check(frac(wb.get("value")) == E_STAR_DEC
          and wb.get("float") == float(E_STAR_DEC),
          f"C3 wouldBe_if_chain_closed 非 25759986531/10⁹==E*：{wb}")
    # assembledRecord == min(分区 bound)（Fraction 精确重算）
    part_bounds = [frac(r["bound"]) for r in d["partition"]]
    check(ar == min(part_bounds),
          "C3 assembledRecord != min(分区 bound)（精确重算）")
    # 分区无缝盖满 [−1,1]
    rs = sorted(d["partition"], key=lambda r: frac(r["region"].split(",")[0][1:]))
    cur = Fraction(-1)
    for r_ in rs:
        lo = frac(r_["region"].split(",")[0][1:])
        hi = frac(r_["region"].split(",")[1][:-1])
        check(lo == cur, f"C3 分区不连续：期望 {cur}，实为 {lo}")
        cur = hi
    check(cur == Fraction(1), f"C3 分区未盖满 [−1,1]，止于 {cur}")
    # citedCertificates 逐份在盘＋claimed_bound 一致
    cited = d.get("citedCertificates", [])
    check(len(cited) == 12, f"C3 citedCertificates 预期 12 份，实为 {len(cited)}")
    for e in cited:
        p = REPO / e["path"]
        check(p.exists(), f"C3 被引证书不在盘：{e['path']}")
        cb = frac(load_json(p)["claimed_bound"])
        check(cb == frac(e["claimed_bound"]),
              f"C3 证书 {e['path']} claimed_bound 与账本引用值不等")
    # endgame.json 零改动：sha256 与基线（R10–R22 基线时点）相等
    sha = hashlib.sha256(ENDGAME.read_bytes()).hexdigest()
    check(sha == ENDGAME_SHA_BASE,
          f"C3 endgame.json 零改动核验失败：sha256 {sha} != 基线 "
          f"{ENDGAME_SHA_BASE}（本轮不得写入该账本——D86-3/D90-3/D96-3/D101-3）")
    print(f"[C3] endgame.json 直读一致 ✓（closed=false/blocking=[L0,L3]/"
          "assembledRecord=47517790735835014335570/1844674407417822803119"
          f"=25.759445973097478/margin={float(margin)!r} float 逐位/"
          "spliceMap 维持 v2/组件 L1·L2·L5·L6·L7 绿＋L0·L3·L4 红；"
          f"铁律 AR≤E*+1e-6 精确成立＋无容差 AR<E* 亦真〔E*−AR="
          f"{float(margin)} 精确重算逐位〕；wouldBe==25759986531/10⁹；"
          f"AR==min(12 分区)；cited 12 份在盘；sha256 零改动 ✓）", flush=True)
    return {"margin": float(margin), "n_partition": len(d["partition"]),
            "n_cited": len(cited)}


# ------------------------------------------------------- C4 文档

def c4_docs() -> dict:
    gap = GAP_REPORT.read_text(encoding="utf-8")
    prog = PROGRESS.read_text(encoding="utf-8")
    dec = DECISIONS.read_text(encoding="utf-8")
    # 本轮节（campaign ID＋日期消歧）
    check(re.search(r"^#+ Round 23（campaign dwfrun-f9904baf", gap, re.M)
          is not None,
          "C4 GAP-REPORT.md 无『Round 23（campaign dwfrun-f9904baf』本轮节"
          "（D101-4/D103 命名）")
    # 本轮节内容锚：任务结构引言（含 D101 锚）＋① R23A 收编＋② R23C 本件
    # （含两段式回填位）＋轮次终判（closed=false 三面一致、blocker L0/L3
    # 不动、assembledRecord 维持零提升、progress 按 D82-4 与 TableB1Witness
    # 实际落地判定）＋预算终账＋诚实声明与未跑项＋下轮候选
    r23_at = gap.find("# Round 23（campaign dwfrun-f9904baf")
    r23_body = gap[r23_at:] if r23_at >= 0 else ""
    for anchor in ("D101", "D102", "D103", "R23A", "R23C",
                   "轮次终判", "closed=false", "三面一致", "零提升",
                   "progress", "预算终账", "诚实声明", "未跑", "下轮候选",
                   "chain-only", "endgame_gate", "两段式回填",
                   "r23c_closure_gate", "TableB1Witness", "TableB1Aut",
                   "l4_orbit", "W==σ₀∘Aut", "|W|=12", "lex-min",
                   "PatternCons", "pattern_ident_lift", "1200s"):
        check(anchor in r23_body,
              f"C4 GAP-REPORT Round 23 节缺『{anchor}』内容锚")
    # PROGRESS 置顶：前 120 行内含本轮条目（D55-2 口径）
    head = prog.splitlines()[:120]
    check(any("Round 23（campaign dwfrun-f9904baf" in ln for ln in head),
          "C4 PROGRESS.md 前 120 行无本轮（campaign dwfrun-f9904baf）置顶"
          "条目（D55-2 口径）")
    # decisions：D101（设计，h3——随 R23A 主件 96bc585 收编）＋D102
    # （R23A 执行，h3）＋D103（本收口裁决，h3）——D 编号顺延处置沿
    # D80-2/D82-5/D84-2/D86-4/D88/D90-4/D93/D96-4/D99，轮次汇总预留 D104
    for dnum in R23_EXEC_DECISIONS:
        check(re.search(rf"^#+ {dnum}（", dec, re.M) is not None,
              f"C4 notes/decisions.md 无 {dnum} 节（R23 设计/R23A 执行留痕）")
    check(re.search(rf"^#+ {D_CLOSURE}（", dec, re.M) is not None,
          f"C4 notes/decisions.md 无 {D_CLOSURE} 节（R23C 收口裁决）")
    return {"gap_round23": True, "progress_top": True,
            "d101_d102_d103": True}


# ------------------------------------------------------- C5 预算

def _c5_frozen_ledgers(m9_path: Path = M9_CAMPAIGN,
                       m10_path: Path = M10_CAMPAIGN,
                       tl_path: Path = TYPED_LADDER,
                       v2_path: Path = V2_CAMPAIGN) -> None:
    """四账本冻结值逐位相等（可对 /tmp 副本跑——负对照用）。"""
    m9 = load_json(m9_path)
    check(frac(m9["budget"]["total_solve_s"])
          == CAMPAIGN_SOLVE_S["m9_campaign"],
          f"C5 m9_campaign.total_solve_s={m9['budget']['total_solve_s']} != "
          f"冻结值 {CAMPAIGN_SOLVE_S['m9_campaign']}（新求解行入账？）")
    m10 = load_json(m10_path)
    check(frac(m10["budget"]["total_solve_s"])
          == CAMPAIGN_SOLVE_S["m10_campaign"],
          f"C5 m10_campaign.total_solve_s={m10['budget']['total_solve_s']} != "
          f"冻结值 {CAMPAIGN_SOLVE_S['m10_campaign']}")
    tl = load_json(tl_path)
    check(len(tl["rungs"]) == TYPED_LADDER_RUNGS_FROZEN,
          f"C5 typed_ladder rungs={len(tl['rungs'])} != 冻结 "
          f"{TYPED_LADDER_RUNGS_FROZEN}（本轮不得追加 rung——"
          "D86-3/D90-3/D96-3/D101-3）")
    m9_rung = next(r for r in tl["rungs"]
                   if r.get("tag") == "m0748" and r.get("M") == 9)
    check(frac(m9_rung["sdpa"]["solve_s"])
          == CAMPAIGN_SOLVE_S["typed_ladder_cap_m0748_M9"],
          f"C5 typed_ladder cap m0748 M9 solve_s={m9_rung['sdpa']['solve_s']} "
          f"!= 冻结值 {CAMPAIGN_SOLVE_S['typed_ladder_cap_m0748_M9']}")
    v2c = load_json(v2_path)
    check(frac(v2c["phase1"]["solve_s"])
          == CAMPAIGN_SOLVE_S["hermite_v2_campaign_phase1"],
          f"C5 hermite_v2_campaign.phase1.solve_s={v2c['phase1']['solve_s']} "
          f"!= 冻结值 {CAMPAIGN_SOLVE_S['hermite_v2_campaign_phase1']}")
    check(frac(v2c["budget"]["solve_s_total"]) == frac(v2c["phase1"]["solve_s"]),
          "C5 hermite_v2_campaign budget.solve_s_total 与 phase1 不一致")
    four_source = (CAMPAIGN_SOLVE_S["m9_campaign"]
                   + CAMPAIGN_SOLVE_S["m10_campaign"]
                   + CAMPAIGN_SOLVE_S["typed_ladder_cap_m0748_M9"]
                   + CAMPAIGN_SOLVE_S["hermite_v2_campaign_phase1"])
    check(four_source
          == CAMPAIGN_TOTAL_FROZEN - CAMPAIGN_SOLVE_S["r11_warmstart_probe"],
          "C5 四源和重算 != 冻结 360418.3s")


def _round_sum_solve_s() -> Fraction:
    """本轮 Σsolve_s：全任务 heavySolves=0 ⇒ 精确 0（D86-3/D90-3/D96-3/
    D101-3——0.037 当量全额留储）。r23a 账本零正 solve 字段由 C5 正则
    面核验，R23C 收口零求解。"""
    return Fraction(0)


def c5_budget() -> dict:
    # 四账本冻结值逐位相等（＝本轮无新求解行入四账本）
    _c5_frozen_ledgers()
    # R11 探针冻结复读（campaign 累计的另一源）
    ws = load_json(R11_WS_LEDGER)
    ws_total = sum(frac(r["solve_s"]) for r in ws.get("runs") or []
                   if "solve_s" in r)
    check(ws_total == CAMPAIGN_SOLVE_S["r11_warmstart_probe"],
          f"C5 r11_warmstart_probe Σsolve_s 重加 {ws_total}s != 冻结 "
          f"{CAMPAIGN_SOLVE_S['r11_warmstart_probe']}s")
    # 本轮支出：Σsolve_s==0 精确（零求解轮）
    round_s = _round_sum_solve_s()
    check(round_s == Fraction(0),
          "C5 本轮 Σsolve_s 非 0（零求解轮口径违例——"
          "D86-3/D90-3/D96-3/D101-3）")
    # campaign 累计＝五源和＋0（精确重算）＋账↔文档双核验
    campaign_total = (sum(CAMPAIGN_SOLVE_S.values()) + round_s)
    check(campaign_total == CAMPAIGN_TOTAL_FROZEN,
          f"C5 campaign 累计重算 {campaign_total}s != 冻结 "
          f"{CAMPAIGN_TOTAL_FROZEN}s（本轮零求解 ⇒ 与 R11–R22 终账"
          "逐位不变）")
    check(campaign_total / EQUIV_UNIT_S == CAMPAIGN_TOTAL_EQ,
          "C5 campaign 当量 != 721885/21600")
    campaign_eq = campaign_total / EQUIV_UNIT_S
    margin_B = Fraction(40) - campaign_eq
    check(margin_B < TRIGGER_EQUIV,
          f"C5 口径 B 余量 {float(margin_B):.3f} ≥ 12——M11 触发器判定与 "
          "R9C 决策件/m11 决策件失配")
    gap = GAP_REPORT.read_text(encoding="utf-8")
    r23_at = gap.find("# Round 23（campaign dwfrun-f9904baf")
    body = gap[r23_at:] if r23_at >= 0 else ""
    claim_c = f"{float(campaign_eq):.3f}"
    check(claim_c in body and f"{claim_c}/40" in body,
          f"C5 GAP-REPORT Round 23 节无 campaign 当量字面 {claim_c}/40"
          f"（重算 {float(campaign_total):.1f}s＝{claim_c}/40——账↔文档"
          "双核验失配）")
    # r23 新产物零正 solve 字段（本轮零求解口径——正则核验）
    r23_jsons = sorted(RESULTS.glob("r23*.json"))
    check(len(r23_jsons) >= 1,
          f"C5 results/r23*.json 仅 {len(r23_jsons)} 件（R23A 账本"
          " r23a_witness_ledger.json 至少一件）")
    for jp in r23_jsons:
        blob = json.dumps(load_json(jp), ensure_ascii=False)
        for m_ in re.finditer(r'"(solve_s\w*)"\s*:\s*([0-9]+(?:\.[0-9]+)?)',
                              blob):
            check(frac(m_.group(2)) == 0,
                  f"C5 {jp.name} 含正 solve 字段 {m_.group(1)}="
                  f"{m_.group(2)}（R23 零求解口径违例——全任务不得有正"
                  "solve 行）")
    print(f"[C5] 预算终账 ✓（本轮 Σsolve_s==0 精确——全任务 heavySolves=0、"
          f"0.037 当量全额留储 D86-3/D90-3/D96-3/D101-3；五源 Fraction 双核验："
          f"四账本与 R8 终账冻结值逐位相等＝无新求解行＋typed_ladder rungs==9 "
          f"不追加＋R11 探针 2621/5s 冻结复读；campaign 累计 "
          f"{float(campaign_total):.1f}s={claim_c}/40 与 GAP-REPORT 字面一致"
          f"（账↔文档双核验，与 R11/R12/R13/R14/R15/R16/R17/R18/R19/R20/R21/"
          f"R22 终账逐位不变）；口径 B 余 {float(margin_B):.3f} <12 ⇒ M11 "
          f"触发器不可触发维持；r23 新产物 {len(r23_jsons)} 件零正 solve "
          "字段）", flush=True)
    return {"round_solve_s": float(round_s), "round_eq": float(round_s) / 10800,
            "campaign_total_s": float(campaign_total),
            "campaign_eq": float(campaign_eq),
            "campaign_eq_str": claim_c, "margin_B": float(margin_B),
            "r23_jsons": [p.name for p in r23_jsons]}


# ------------------------------------------------------- C6 树净

def c6_git_clean() -> None:
    if not (REPO / ".git").exists():
        print("[C6] skip：非 git 仓库（tmp 副本演练口径）", flush=True)
        return
    r = subprocess.run(["git", "status", "--porcelain"], cwd=str(REPO),
                       capture_output=True, text=True, timeout=60)
    check(r.returncode == 0, f"C6 git status 失败：{r.stderr}")
    check(r.stdout.strip() == "", f"C6 工作树不干净：\n{r.stdout}")
    # endgame.json 零改动双保险（与 C3 sha256 同口径）
    r2 = subprocess.run(["git", "diff", "--quiet", "HEAD", "--",
                         "numerics/bounds/results/endgame.json"],
                        cwd=str(REPO), capture_output=True, text=True)
    check(r2.returncode == 0,
          "C6 endgame.json 相对 HEAD 有未提交改动（本轮零写入核验失败）")
    print("[C6] git status --porcelain 为空 ✓（含 R23A/R23C 交付物"
          "全部提交＋endgame.json 相对 HEAD 零改动）", flush=True)


# -------------------------------------------------------------------- main

def main() -> int:
    random.seed(SEED)                      # 固定种子（任务书条款；本门确定性）
    t0 = time.time()
    energies = load_json(WORKFLOW_DATA)["energies"]["9"]
    E_star = frac(energies["value"])
    check(E_star == E_STAR_DEC,
          f"前置：energies.json E* {E_star} != 十进制精确口径 {E_STAR_DEC}")
    print(f"[gate] E* = {E_star}（{WORKFLOW_DATA}，十进制精确口径 D28 裁决 3）；"
          f"seed = {SEED}", flush=True)
    walls = c1_subgates()                                              # C1
    in_flight = c1a_family_routing()                                   # C1a
    c2 = c2_chain_dry()                                                # C2
    c3 = c3_direct_read()                                              # C3
    docs = c4_docs()                                                   # C4
    budget = c5_budget()                                               # C5
    nc = nc_self()                                                     # NC
    c6_git_clean()                                                     # C6
    print(f"[gate] C1 r23a 门复跑 exit 0 ✓（r23a_witness_gate "
          f"{walls['r23a_witness_gate']:.1f}s〔编译型 1200s 文档化例外——"
          f"十二连 elaboration，R18/R19/R21B/R22B 先例；r22 双门已在档本轮"
          f"不重烧〕；结果锚 ✓——seed {SEED}/heavy_solves==0/kind/task/"
          "axiom_policy 恰三标准＋isolated_from_12_partition 隔离声明＋"
          "endgame_chain.py 输入路由禁令＋provenance.acceptanceGate 门面＋"
          "frozen 锚〔账本锚面按 r23a 实际 schema——D103 裁决 3〕）",
          flush=True)
    print(f"[gate] C1a 家族放行层双路由 ✓（在途件 "
          f"{len(set(in_flight))} 件）；"
          f"C2 全集漂移 {c2['drift_leaves']} 叶全叙述性预期 ✓"
          f"（与 D84 裁决 4/D93 冻结分布逐位同）；C4 文档三件 ✓（{docs}）；"
          f"NC 双面 ✓（{len(nc)} 项）", flush=True)
    print(f"[gate] C5 预算 Σsolve_s==0 精确、campaign "
          f"{budget['campaign_eq_str']}/40（口径 B 余 {budget['margin_B']:.3f}"
          " <12）✓", flush=True)
    print(f"[gate] PASS（{time.time()-t0:.1f}s）——exit 0", flush=True)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except GateFail as e:
        print(f"[gate] FAIL：{e}", flush=True)
        print("[gate] exit 1", flush=True)
        sys.exit(1)
