#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r11c_closure_gate.py — R11D r11d-closure 收口验收门（campaign
dwfrun-41fdc169 第 6 轮，2026-10-10）。

裸 python3 运行（无第三方依赖；CWD 无关——一切路径由 __file__ 解析；
campaign 根路由沿 R7B bd15f27／R8C r8c3_closure_gate／R9D r9c_closure_gate／
R10D r10c_closure_gate 嵌套包装器先例）：

    python3 numerics/bounds/r11c_closure_gate.py             # 仓内
    python3 thomson-n9/numerics/bounds/r11c_closure_gate.py  # campaign 根

固定种子 20261013（任务书条款）。六项检查（对应 R11D 任务书收口面
①–⑧；全部确定性——本轮零求解（heavySolves=0，r11b 探针 0.163 当量系
任务书预算内既定支出非本收口会话求解），收口以一致性核验替代
--reverify-certs 全量刷新于 C2（D34 裁决 4／D38 裁决 5／D43 裁决 5
先例——endgame_gate 扩展后全门净树一跑另行在档）：

  C1 R11A/R11B/R11C 三门复跑 exit 0＋结果 json 在档锚：
     - r11_m0_gate.py 复跑 exit 0（R11A M0 Lean 首证门：G1 冻结守卫＋
       G2 token 扫描＋G3 lake build 恰 4 挑战 sorry@158/166/172/179＋
       解件 0＋G4 CheckAxioms M0 公理恰三标准公理＋G5 语句比对 OK 33＋
       G6 negative-control.sh 检出恰 thomson_nine＋NC1/NC2/NC3）＋
       results/r11_m0_ledger.json 在档锚（sorry_counts.challenge==4/
       solution==0、axioms ThomsonN9.thomson_nine_M0 恰
       {propext,Classical.choice,Quot.sound}、statement_compare OK
       compared==33、negative_control OK、heavySolves==0）；
     - r11_warmstart_gate.py 复跑 exit 0（R11B warm-start 探针交付质量
       门：G1 ledger 完整＋G2 冷重解确定性＋G3 消费推断＋G4 verdict 分支
       证据＋G5 预算 Fraction ≤2160s＋G6 冻结件零改动＋NC1/NC2）＋
       results/r11_warmstart_probe.json 在档锚（verdict 三值域、cold
       iterations==76、真实求解 runs≥2）；
     - r11_m1light_gate.py 复跑 exit 0（R11C M1 轻证书门：G1 schema＋
       G2 Fraction >189/8 且 ≤E*+1e-6＋G3 门内重放 certify ×2＋G4 lp.json
       冻结守卫＋G5 Legendre 精确重算＋NC1/NC2a/NC2b）＋
       results/lp_m1_light.json 在档锚（degree 8、seed 20261013、四检查
       全 True、bound_exact Fraction >189/8 且 ≤E*+1e-6）。
  C2 chain-only 干跑五字段 14 检查点逐位零漂移（D34 裁决 4／D38 裁决 5／
     D43 裁决 5；R8A D30／R9D／R10D 先例）：endgame_chain.py --out /tmp
     （零 --reverify-certs）产物与存档 endgame.json 五字段逐位——closed/
     blocking/assembledRecord 精确分数串＋float/spliceMapVerdict
     （verdict＋assembled_equal_R7）/组件 rigorous L0–L7 八布尔——零漂移；
     全集漂移逐叶盘点机器化归类（r10c_closure_gate C2 同口径：certReverify
     ＋code_version/timestamp＋L1 quant 佐证串＋engineV2 账本探测，未归类
     叶即 FAIL）。本轮 r11b 不入四账本（探针自有 r11_warmstart_probe.json，
     typed_ladder.json 不追加 rung——D43 裁决 5）⇒ 零账本数值变更 ⇒ 不跑
     --reverify-certs 全量刷新（≥2 组独立在档不重复消耗）。
  C3 endgame.json 直读一致性＋铁律 Fraction 亲算：closed=false、
     blocking=[L0,L3]、assembledRecord==47517790735835014335570/
     1844674407417822803119（float 25.759445973097478）、margin 重算
     ＝E*−AR 精确、spliceMapVerdict=维持 v2（assembled_equal_R7=true）、
     组件 L1/L2/L5/L6/L7 rigorous=True＋L0/L3/L4=False（L4 off-path）、
     铁律 AR ≤ E*+1e-6（E* 十进制精确口径 Fraction("25.759986531")，
     D28 裁决 3）、AR==min(分区 bound) 精确重算、citedCertificates 逐份
     在盘且 claimed_bound 一致、endgame.json 零改动（sha256 与 R10 基线
     5a6ab9c＝R11 基线 4ed4d5c 时点相等——本轮零写入核验）。
  C4 文档三件锚：GAP-REPORT「Round 11（campaign dwfrun-41fdc169 第 6 轮，
     2026-10-10）」节（含重构 1/3 换轴叙事＋R11A/R11B/R11C 收编＋D43 回填
     ＋诚实声明与未跑项锚＋下轮候选）＋PROGRESS.md 置顶条目＋
     notes/decisions.md D43 结果回填（R11D 节）锚。
  C5 预算终账（0.163/0.2 口径 A＋campaign 33.535/40 双核验）：本轮
     Σsolve_s 自 r11_warmstart_probe.json runs 以 Fraction 精确求和（R11A
     heavySolves=0／R11C scipy LP 非重求解口径 0／R11D 收口 0——探针 3 解
     为本轮全部支出）≤2160s（口径 A 硬顶＝0.2 当量）＋四账本与 R8 终账
     冻结值逐位相等（无新求解行）＋typed_ladder rungs==9（不追加 rung）＋
     campaign 累计＝360418.3s＋Σsolve_s 精确重算、当量化后与 GAP-REPORT
     Round 11 节字面 3 位小数一致（账↔文档双核验）＋口径 B 余量
     ＝40−campaign 当量 <12 ⇒ M11 触发器不可触发维持＋R11 新产物除探针
     账本外零正 solve 字段（正则核验）。
  C6 树净：git status --porcelain 0 行（含 R11A/B/C/D 全部交付物已提交、
     endgame.json 零改动——与 C3 sha256 核验双保险）。

负对照（--nc-self 或默认自检段）：/tmp 篡 r11 账本必失配——篡
r11_warmstart_probe.json 副本 solve_s（586.8→1586.8s 越预算顶）⇒ C5 预算
核验必拦；篡 r11_m0_ledger.json 副本 sorry_counts.solution（0→1）⇒ C1
账本锚必拦；未篡副本 sanity 通过。

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
R11_M0_LEDGER = RESULTS / "r11_m0_ledger.json"
R11_WS_LEDGER = RESULTS / "r11_warmstart_probe.json"
R11_M1_LIGHT = RESULTS / "lp_m1_light.json"
GAP_REPORT = REPO / "GAP-REPORT.md"
PROGRESS = REPO / "PROGRESS.md"
DECISIONS = REPO / "notes" / "decisions.md"
WORKFLOW_DATA = HERE.parents[2] / "thomson-workflow" / "data" / "energies.json"

SEED = 20261013
E_STAR_DEC = Fraction("25.759986531")    # 十进制精确口径（D28 裁决 3）
TOL_ESTAR = Fraction(1, 10**6)
LP_TARGET = Fraction(189, 8)             # M1 轻证书目标（≫ 严格要求）
EQUIV_UNIT_S = 10800                     # 1 当量 = 10800s（m9_campaign 口径）
AR_STR = "47517790735835014335570/1844674407417822803119"
AR_FLOAT = 25.759445973097478
# campaign 累计冻结值（R8 终账＝R9/R10/R11 基线，四源和）
CAMPAIGN_SOLVE_S = {
    "m9_campaign": Fraction("102504.9"),
    "m10_campaign": Fraction("185065.6"),
    "typed_ladder_cap_m0748_M9": Fraction("42305.7"),
    "hermite_v2_campaign_phase1": Fraction("30542.1"),
}
CAMPAIGN_TOTAL_FROZEN = Fraction("360418.3")   # 3604183/10 s
TYPED_LADDER_RUNGS_FROZEN = 9                  # r11b 探针不追加 rung（D43 裁决 5）
ROUND_BUDGET_S = Fraction(2160)                # 口径 A：本轮 0.2 当量硬顶
TRIGGER_EQUIV = Fraction(12)                   # M11 触发器阈值（D29 裁决 1）
# endgame.json sha256（R10 基线 HEAD=5a6ab9c 时点；R11 全程零改动核验）
ENDGAME_SHA_BASE = ("86863a09bf84e950e85fc5f902bc2b40"
                    "46a87f06703bd782e5148fc119afd69f")

R11A_GATE = HERE / "r11_m0_gate.py"
R11B_GATE = HERE / "r11_warmstart_gate.py"
R11C_GATE = HERE / "r11_m1light_gate.py"

EXPECTED_RIGOROUS = {"L0": False, "L1": True, "L2": True, "L3": False,
                     "L4": False, "L5": True, "L6": True, "L7": True}
WS_VERDICTS = {"channel_alive", "channel_dead", "channel_ignored"}


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


# ------------------------------------------------------- C1 三门＋账本锚

def run_subgate(path: Path, tag: str, timeout_s: int = 3600) -> float:
    check(path.exists(), f"{tag} 子门不在盘：{path}")
    t0 = time.time()
    r = subprocess.run([sys.executable, str(path)], capture_output=True,
                       text=True, timeout=timeout_s, cwd=str(REPO))
    wall = time.time() - t0
    tail = "\n".join((r.stdout or "").splitlines()[-6:])
    print(f"[{tag}] exit={r.returncode} ({wall:.1f}s)：{path.name}", flush=True)
    check(r.returncode == 0, f"{tag} 子门复跑 exit {r.returncode}：\n{tail}")
    return wall


def c1_anchor_m0(ledger_path: Path = R11_M0_LEDGER) -> None:
    """R11A M0 Lean 首证账本锚（可对 /tmp 副本跑——负对照用）。"""
    led = load_json(ledger_path)
    sc = led.get("sorry_counts") or {}
    check(sc.get("challenge") == 4 and sc.get("solution") == 0,
          f"C1 r11_m0_ledger sorry_counts 异常：{sc}（预期 challenge=4/"
          "solution=0——M0 真证明落地口径）")
    dl = sc.get("challenge_decl_lines")
    check(dl == [158, 166, 172, 179],
          f"C1 r11_m0_ledger challenge_decl_lines={dl} 非 [158,166,172,179]")
    ax = (led.get("axioms") or {}).get("ThomsonN9.thomson_nine_M0")
    check(sorted(ax or []) == ["Classical.choice", "Quot.sound", "propext"],
          f"C1 r11_m0_ledger M0 公理集异常：{ax}（预期恰三标准公理——无内核"
          "旁路）")
    stc = led.get("statement_compare") or {}
    check(stc.get("status") == "OK" and stc.get("compared") == 33,
          f"C1 r11_m0_ledger statement_compare={stc.get('status')}/"
          f"{stc.get('compared')} 非 OK/33（冻结命题语句保真锚）")
    nc = led.get("negative_control") or {}
    check(nc.get("status") == "OK",
          f"C1 r11_m0_ledger negative_control={nc.get('status')} 非 OK")
    check(led.get("heavySolves") == 0,
          f"C1 r11_m0_ledger heavySolves={led.get('heavySolves')} 非 0")
    check(led.get("gate_seed") == SEED,
          f"C1 r11_m0_ledger gate_seed={led.get('gate_seed')} 非 {SEED}")


def c1_anchor_ws(ledger_path: Path = R11_WS_LEDGER) -> None:
    """R11B warm-start 探针账本锚（可对 /tmp 副本跑——负对照用）。"""
    led = load_json(ledger_path)
    check(str(led.get("verdict")) in WS_VERDICTS,
          f"C1 r11_warmstart_probe verdict={led.get('verdict')} 不在三值域 "
          f"{sorted(WS_VERDICTS)}")
    runs = led.get("runs") or []
    real = [r for r in runs if str(r.get("phase", "")).startswith(("cold",
                                                                   "warm_"))]
    check(len(real) >= 2,
          f"C1 r11_warmstart_probe 真实求解 runs 仅 {len(real)}（预期 ≥2："
          "cold＋warm_self〔＋预算容 warm_dyad〕）")
    cold = [r for r in real if r.get("phase") == "cold"]
    if not cold:
        raise GateFail("C1 r11_warmstart_probe 无 cold run")
    check(len(cold) == 1 and int(cold[0].get("iterations", -1)) == 76,
          f"C1 r11_warmstart_probe cold.iterations="
          f"{cold[0].get('iterations')} 非 76（存档冷解确定性口径——G2 同锚）")
    check(frac(cold[0]["solve_s"]) > 0, "C1 r11_warmstart_probe cold.solve_s "
          "非正——探针支出记账异常")


def c1_anchor_m1(cert_path: Path = R11_M1_LIGHT) -> None:
    """R11C M1 轻证书数据件锚（可对 /tmp 副本跑——负对照用）。"""
    d = load_json(cert_path)
    check(str(d.get("kind")) == "lp",
          f"C1 lp_m1_light kind={d.get('kind')} 非 lp")
    cert = d.get("certificate") or {}
    check(cert.get("degree") == 8,
          f"C1 lp_m1_light degree={cert.get('degree')} 非 8（D44 裁决 1）")
    mth = d.get("method") or {}
    check(mth.get("seed") == SEED and mth.get("grid_points") == 8000,
          f"C1 lp_m1_light method seed/grid={mth.get('seed')}/"
          f"{mth.get('grid_points')} 非 {SEED}/8000")
    ck = cert.get("checks") or {}
    check(all(ck.get(k) is True for k in ("coeffs_nonneg_k_ge_1",
                                          "f_le_phi_certified_exact_rational",
                                          "taylor_tail_rigorous",
                                          "tail_interval_check")),
          f"C1 lp_m1_light certificate.checks 非全 True：{ck}")
    be = frac(d["bound_exact"])
    check(be > LP_TARGET,
          f"C1 lp_m1_light bound_exact {float(be)} ≤ 189/8=23.625（M1 目标"
          "失配）")
    check(be <= E_STAR_DEC + TOL_ESTAR,
          f"C1 lp_m1_light bound_exact {float(be)} > E*+1e-6（铁律违例）")


def c1_subgates() -> dict:
    walls = {}
    # R11A：M0 Lean 首证门＋账本锚
    check(R11_M0_LEDGER.exists(), "C1 results/r11_m0_ledger.json 不在盘"
          "（R11A 交付缺件）")
    walls["r11_m0_gate"] = run_subgate(R11A_GATE, "C1a")
    c1_anchor_m0()
    # R11B：warm-start 探针门＋账本锚
    check(R11_WS_LEDGER.exists(), "C1 results/r11_warmstart_probe.json 不"
          "在盘（R11B 交付缺件）")
    walls["r11_warmstart_gate"] = run_subgate(R11B_GATE, "C1b")
    c1_anchor_ws()
    # R11C：M1 轻证书门＋数据件锚
    check(R11_M1_LIGHT.exists(), "C1 results/lp_m1_light.json 不在盘"
          "（R11C 交付缺件）")
    walls["r11_m1light_gate"] = run_subgate(R11C_GATE, "C1c")
    c1_anchor_m1()
    # 冻结面仍在盘（append-only 先例）
    for _fz in ("typed_ladder.json", "lp.json"):
        check((RESULTS / _fz).exists(), f"C1 冻结件 {_fz} 不在盘")
    return walls


# ------------------------------------------------------- 负对照（门自身）

def nc_self() -> dict:
    """负对照：/tmp 篡 r11 账本必失配（C1 锚＋C5 预算核验双面）。"""
    results = {}
    with tempfile.TemporaryDirectory(prefix="r11c_nc_") as td:
        # NC1：篡 warm-start 探针 solve_s（+2000s 越预算顶）⇒ C5 预算核验必拦
        tam1 = Path(td) / "r11_warmstart_probe_nc.json"
        led = json.loads(R11_WS_LEDGER.read_text())
        bumped = False
        for r in led.get("runs", []):
            if str(r.get("phase")) == "cold" and frac(r["solve_s"]) > 0 \
                    and not bumped:
                r["solve_s"] = str(frac(r["solve_s"]) + Fraction(2000))
                bumped = True
        check(bumped, "NC1 构造失败：探针无正 solve_s 可篡")
        tam1.write_text(json.dumps(led, ensure_ascii=False))
        try:
            _round_sum_solve_s(tam1)
            raise GateFail("NC1 失效：篡 solve_s +2000s 后 Σ≤2160 仍通过")
        except GateFail as e:
            check("2160" in str(e) or "Σsolve_s" in str(e),
                  f"NC1 拦截面失配：{e}")
            results["NC1_tamper_solve_s"] = str(e)[:90]
        # NC2：篡 m0 账本 sorry_counts.solution 0→1 ⇒ C1 锚必拦
        tam2 = Path(td) / "r11_m0_ledger_nc.json"
        m0 = json.loads(R11_M0_LEDGER.read_text())
        m0["sorry_counts"]["solution"] = 1
        tam2.write_text(json.dumps(m0, ensure_ascii=False))
        try:
            c1_anchor_m0(tam2)
            raise GateFail("NC2 失效：篡 solution sorry 0→1 后 M0 锚仍通过")
        except GateFail as e:
            check("sorry_counts" in str(e),
                  f"NC2 拦截面失配：{e}")
            results["NC2_tamper_m0_sorry"] = str(e)[:90]
        # sanity：未篡副本锚通过（真件在 C1 已核，此处仅副本口径演示）
        c1_anchor_m1(R11_M1_LIGHT)
        results["sanity_untampered"] = "ok"
    print(f"[NC] /tmp 篡 r11 账本双面必失配 ✓（NC1 探针 solve_s +2000s ⇒ "
          f"C5 预算拦；NC2 m0 solution sorry 0→1 ⇒ C1 锚拦；未篡副本 "
          f"sanity ok）", flush=True)
    return results


# ------------------------------------------------------- C2 干跑

def c2_chain_dry() -> dict:
    """chain-only 干跑五字段 14 检查点逐位 diff（零 --reverify-certs；产物
    只写临时目录）。

    五字段 14 检查点＝closed(1)＋blocking(1)＋assembledRecord 精确分数串
    ＋float(2)＋spliceMapVerdict verdict＋assembled_equal_R7(2)＋组件
    rigorous L0–L7(8)。其余字段（timestamp/code_version/certReverify/
    engineV2 探测时点/L1 quant 佐证串等）允许叙述性漂移——R8A D30／
    R10D 先例口径（r10c_closure_gate C2 同构）；如漂移出现在五字段内
    即 FAIL。"""
    archived = load_json(ENDGAME)
    with tempfile.TemporaryDirectory(prefix="r11c_chain_dry_") as td:
        out = Path(td) / "endgame_dry.json"
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
    check(ae["closed"] == be["closed"],
          f"C2 closed 漂移：存档 {ae['closed']} vs 干跑 {be['closed']}")
    check(be["closed"] is False, "C2 closed 预期 false（本轮一致性收口）")
    check(ae["blocking"] == be["blocking"],
          f"C2 blocking 漂移：{ae['blocking']} vs {be['blocking']}")
    check(be["blocking"] == ["L0", "L3"],
          f"C2 blocking 预期 [L0, L3]，实为 {be['blocking']}")
    for k in ("value", "float"):
        av, bv = archived["assembledRecord"][k], dry["assembledRecord"][k]
        check(av == bv, f"C2 assembledRecord.{k} 漂移：{av} vs {bv}")
    check(dry["assembledRecord"]["value"] == AR_STR,
          "C2 干跑 assembledRecord 分数串非基线常量")
    check(dry["assembledRecord"]["float"] == AR_FLOAT,
          "C2 干跑 assembledRecord float 非 25.759445973097478")
    asm, bsm = archived["spliceMapVerdict"], dry["spliceMapVerdict"]
    check(asm.get("verdict") == bsm.get("verdict"),
          f"C2 spliceMapVerdict.verdict 漂移：{asm.get('verdict')} vs "
          f"{bsm.get('verdict')}")
    check(asm.get("assembled_equal_R7") == bsm.get("assembled_equal_R7"),
          "C2 spliceMapVerdict.assembled_equal_R7 漂移")
    check("维持 v2" in str(bsm.get("verdict"))
          and bsm.get("assembled_equal_R7") is True,
          "C2 spliceMapVerdict 非『维持 v2』＋equal_R7=true")
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
    # 全集漂移逐叶盘点（叙述性预期归类，r10c_closure_gate C2 同口径；
    # 未归类叶即 FAIL）
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
          f"C2 出现未归类漂移叶：{[p for p, _ in drifts if not (p.startswith('/certReverify') or p in ('/code_version', '/timestamp') or p == '/endgameChain/components[1]/quant' or p.startswith('/round8Inputs/engineV2'))][:8]}")
    print(f"[C2] chain-only 干跑五字段 14 检查点逐位零漂移 ✓（closed=false/"
          "blocking=[L0,L3]/assembledRecord 精确分数＋float/spliceMap 维持 v2/"
          "组件 L1·L2·L5·L6·L7 绿＋L0·L3·L4 红；零 --reverify-certs——本轮零"
          "账本数值变更（r11b 探针不入四账本、typed_ladder 不追加 rung），"
          f"D34 裁决 4；干跑 {time.time()-t0:.1f}s 级；全集漂移 {len(drifts)} 叶"
          f"全叙述性预期＝{ {k: v for k, v in buckets.items() if v} }）",
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
    # margin 精确重算 == 账本 margin_vs_E_star
    margin = E_STAR_DEC - ar
    check(abs(float(margin) - d["assembledRecord"]["margin_vs_E_star"])
          < 1e-15,
          f"C3 margin 重算 {float(margin)} != 账本 "
          f"{d['assembledRecord']['margin_vs_E_star']}")
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
    # endgame.json 零改动：sha256 与基线（R10 HEAD=5a6ab9c＝R11 时点）相等
    sha = hashlib.sha256(ENDGAME.read_bytes()).hexdigest()
    check(sha == ENDGAME_SHA_BASE,
          f"C3 endgame.json 零改动核验失败：sha256 {sha} != 基线 "
          f"{ENDGAME_SHA_BASE}（本轮不得写入该账本——D43 裁决 5）")
    print(f"[C3] endgame.json 直读一致 ✓（closed=false/blocking=[L0,L3]/"
          "assembledRecord=47517790735835014335570/1844674407417822803119"
          f"=25.759445973097478/spliceMap 维持 v2/组件 L1·L2·L5·L6·L7 绿；"
          f"铁律 AR≤E*+1e-6 精确成立〔E*−AR={float(margin)} 精确重算〕；"
          f"AR==min(12 分区)；cited 12 份在盘；sha256 零改动 ✓）", flush=True)
    return {"margin": float(margin), "n_partition": len(d["partition"]),
            "n_cited": len(cited)}


# ------------------------------------------------------- C4 文档

def c4_docs() -> dict:
    gap = GAP_REPORT.read_text(encoding="utf-8")
    prog = PROGRESS.read_text(encoding="utf-8")
    dec = DECISIONS.read_text(encoding="utf-8")
    # 本轮节（campaign ID＋日期消歧）
    check(re.search(r"^#+ Round 11（campaign dwfrun-41fdc169 第 6 轮，"
                    r"2026-10-10", gap, re.M) is not None,
          "C4 GAP-REPORT.md 无『Round 11（campaign dwfrun-41fdc169 第 6 轮，"
          "2026-10-10）』本轮节（D43 裁决 5 命名）")
    # 本轮节内容锚：重构 1/3 换轴叙事＋R11A/R11B/R11C 收编＋D43 回填＋
    # 诚实声明与未跑项＋下轮候选＋chain-only 干跑＋endgame_gate（收口方法
    # 学锚）＋progress 终判锚
    r11_at = gap.find("# Round 11（campaign dwfrun-41fdc169")
    r11_body = gap[r11_at:] if r11_at >= 0 else ""
    for anchor in ("R11A", "R11B", "R11C", "D43", "诚实声明", "chain-only",
                   "endgame_gate", "下轮候选", "重构", "progress"):
        check(anchor in r11_body,
              f"C4 GAP-REPORT Round 11 节缺『{anchor}』内容锚")
    # PROGRESS 置顶：前 120 行内含本轮条目
    head = prog.splitlines()[:120]
    check(any("Round 11（campaign dwfrun-41fdc169" in ln for ln in head),
          "C4 PROGRESS.md 前 120 行无本轮（campaign dwfrun-41fdc169）置顶条目")
    # decisions：D43 结果回填（R11D 节）
    m = re.search(r"^### D43（", dec, re.M)
    check(m is not None, "C4 notes/decisions.md 无 D43 节")
    check(re.search(r"D43 结果追加回填（R11D", dec) is not None,
          "C4 notes/decisions.md 无『D43 结果追加回填（R11D…』节（本收口"
          "会话回填）")
    return {"gap_round11": True, "progress_top": True, "d43_backfill": True}


# ------------------------------------------------------- C5 预算

def _round_sum_solve_s(ws_ledger_path: Path = R11_WS_LEDGER) -> Fraction:
    """本轮 Σsolve_s：自探针账本 runs 以 Fraction 精确求和（R11A/B/C/D
    中唯探针有真实求解支出——R11A heavySolves=0、R11C scipy LP 非重求解
    口径、R11D 收口零求解）。"""
    led = load_json(ws_ledger_path)
    total = Fraction(0)
    for r in led.get("runs") or []:
        if "solve_s" in r:
            total += frac(r["solve_s"])
    check(total > 0, "C5 Σsolve_s==0——探针支出未记账（r11b 探针账本应含"
          "真实求解行）")
    # 独立重加与账本自报 total_solve_s 逐位互核（双核验第一面）
    declared = ((led.get("budget") or {}).get("total_solve_s"))
    if declared is not None and ws_ledger_path == R11_WS_LEDGER:
        check(frac(declared) == total,
              f"C5 Σsolve_s 重加 {total}s != 探针账本自报 total_solve_s "
              f"{declared}s（双核验失配）")
    check(total <= ROUND_BUDGET_S,
          f"C5 Σsolve_s={total}s 越口径 A 硬顶 {ROUND_BUDGET_S}s（0.2 当量"
          "＝2160s）")
    return total


def c5_budget() -> dict:
    # 四账本冻结值逐位相等（＝本轮无新求解行入四账本）
    m9 = load_json(M9_CAMPAIGN)
    check(frac(m9["budget"]["total_solve_s"])
          == CAMPAIGN_SOLVE_S["m9_campaign"],
          f"C5 m9_campaign.total_solve_s={m9['budget']['total_solve_s']} != "
          f"冻结值 {CAMPAIGN_SOLVE_S['m9_campaign']}（新求解行入账？）")
    m10 = load_json(M10_CAMPAIGN)
    check(frac(m10["budget"]["total_solve_s"])
          == CAMPAIGN_SOLVE_S["m10_campaign"],
          f"C5 m10_campaign.total_solve_s={m10['budget']['total_solve_s']} != "
          f"冻结值 {CAMPAIGN_SOLVE_S['m10_campaign']}")
    tl = load_json(TYPED_LADDER)
    check(len(tl["rungs"]) == TYPED_LADDER_RUNGS_FROZEN,
          f"C5 typed_ladder rungs={len(tl['rungs'])} != 冻结 "
          f"{TYPED_LADDER_RUNGS_FROZEN}（r11b 探针不得追加 rung——D43 裁决 5）")
    m9_rung = next(r for r in tl["rungs"]
                   if r.get("tag") == "m0748" and r.get("M") == 9)
    check(frac(m9_rung["sdpa"]["solve_s"])
          == CAMPAIGN_SOLVE_S["typed_ladder_cap_m0748_M9"],
          f"C5 typed_ladder cap m0748 M9 solve_s={m9_rung['sdpa']['solve_s']} "
          f"!= 冻结值 {CAMPAIGN_SOLVE_S['typed_ladder_cap_m0748_M9']}")
    v2c = load_json(V2_CAMPAIGN)
    check(frac(v2c["phase1"]["solve_s"])
          == CAMPAIGN_SOLVE_S["hermite_v2_campaign_phase1"],
          f"C5 hermite_v2_campaign.phase1.solve_s={v2c['phase1']['solve_s']} "
          f"!= 冻结值 {CAMPAIGN_SOLVE_S['hermite_v2_campaign_phase1']}")
    check(frac(v2c["budget"]["solve_s_total"]) == frac(v2c["phase1"]["solve_s"]),
          "C5 hermite_v2_campaign budget.solve_s_total 与 phase1 不一致")
    check(sum(CAMPAIGN_SOLVE_S.values()) == CAMPAIGN_TOTAL_FROZEN,
          "C5 四源和重算 != 冻结 360418.3s")
    # 本轮支出：探针 Σsolve_s（Fraction；≤2160s 口径 A 硬顶）
    round_s = _round_sum_solve_s()
    round_eq = round_s / EQUIV_UNIT_S
    check(round_eq <= Fraction(1, 5),
          f"C5 本轮当量 {float(round_eq):.4f} > 0.2（口径 A）")
    # campaign 累计＝360418.3＋Σsolve_s（精确重算）＋账↔文档双核验
    campaign_total = CAMPAIGN_TOTAL_FROZEN + round_s
    campaign_eq = campaign_total / EQUIV_UNIT_S
    margin_B = Fraction(40) - campaign_eq
    check(margin_B < TRIGGER_EQUIV,
          f"C5 口径 B 余量 {float(margin_B):.3f} ≥ 12——M11 触发器判定与 "
          "R9C 决策件/m11 决策件失配")
    gap = GAP_REPORT.read_text(encoding="utf-8")
    r11_at = gap.find("# Round 11（campaign dwfrun-41fdc169")
    body = gap[r11_at:] if r11_at >= 0 else ""
    claim_c = f"{float(campaign_eq):.3f}"
    check(claim_c in body,
          f"C5 GAP-REPORT Round 11 节无 campaign 当量字面 {claim_c}"
          f"（重算 {float(campaign_total):.1f}s＝{claim_c}/40——账↔文档"
          "双核验失配）")
    # R11 新产物零正 solve 字段（探针账本除外——探针支出即本轮记账面）
    r11_jsons = sorted(p for p in RESULTS.glob("r11_*.json")
                       if p.name != R11_WS_LEDGER.name)
    check(len(r11_jsons) >= 1,
          f"C5 results/r11_*.json（除探针账本）仅 {len(r11_jsons)} 件"
          "（R11A ledger 至少一件）")
    for jp in r11_jsons:
        blob = json.dumps(load_json(jp), ensure_ascii=False)
        for m_ in re.finditer(r'"(solve_s\w*)"\s*:\s*([0-9]+(?:\.[0-9]+)?)',
                              blob):
            check(frac(m_.group(2)) == 0,
                  f"C5 {jp.name} 含正 solve 字段 {m_.group(1)}="
                  f"{m_.group(2)}（R11 零求解口径违例——探针外不得有正"
                  "solve 行）")
    camp_total_f = float(campaign_total)
    round_f = float(round_s)
    print(f"[C5] 预算终账 ✓（本轮 Σsolve_s={round_f:.1f}s="
          f"{float(round_eq):.3f}/0.2 当量——探针解独占、口径 A 硬顶 2160s "
          f"内；四账本与 R8 终账冻结值逐位相等＝无新求解行＋typed_ladder "
          f"rungs==9 不追加；campaign 累计 {camp_total_f:.1f}s={claim_c}/40 "
          f"与 GAP-REPORT 字面一致（账↔文档双核验）；口径 B 余 "
          f"{float(margin_B):.3f} <12 ⇒ M11 触发器不可触发维持；R11 新产物 "
          f"{len(r11_jsons)} 件（探针外）零正 solve 字段）",
          flush=True)
    return {"round_solve_s": float(round_s), "round_eq": float(round_eq),
            "campaign_total_s": float(campaign_total),
            "campaign_eq": float(campaign_eq),
            "campaign_eq_str": claim_c, "margin_B": float(margin_B),
            "r11_jsons_ex_ws": [p.name for p in r11_jsons]}


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
    print("[C6] git status --porcelain 为空 ✓（含 R11A/B/C/D 交付物全部提交＋"
          "endgame.json 相对 HEAD 零改动）", flush=True)


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
    c2 = c2_chain_dry()                                                # C2
    c3 = c3_direct_read()                                              # C3
    docs = c4_docs()                                                   # C4
    budget = c5_budget()                                               # C5
    nc = nc_self()                                                     # NC
    c6_git_clean()                                                     # C6
    print(f"[gate] C1 三门复跑 exit 0 ✓（r11_m0_gate "
          f"{walls['r11_m0_gate']:.1f}s＋r11_warmstart_gate "
          f"{walls['r11_warmstart_gate']:.1f}s＋r11_m1light_gate "
          f"{walls['r11_m1light_gate']:.1f}s；结果 json 在档锚 ✓）", flush=True)
    print(f"[gate] C2 全集漂移 {c2['drift_leaves']} 叶全叙述性预期 ✓；"
          f"C4 文档三件 ✓（{docs}）；NC 双面 ✓（{len(nc)} 项）", flush=True)
    print(f"[gate] C5 预算 {budget['round_eq']:.3f}/0.2、campaign "
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
