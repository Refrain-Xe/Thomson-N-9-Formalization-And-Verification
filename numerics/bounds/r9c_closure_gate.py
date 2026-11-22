#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r9c_closure_gate.py — R9D round9-closure 收口验收门（campaign
dwfrun-41fdc169 第 4 轮，2026-10-10）。

裸 python3 运行（无第三方依赖；CWD 无关——一切路径由 __file__ 解析；
campaign 根路由沿 R7B bd15f27／R8C r8c3_closure_gate 嵌套包装器先例）：

    python3 numerics/bounds/r9c_closure_gate.py            # 仓内
    python3 thomson-n9/numerics/bounds/r9c_closure_gate.py # campaign 根

固定种子 20261010（任务书条款）。六项检查（对应 R9D 任务书验收判据
①–⑥；全部确定性——本轮零求解零新证书零账本数值变更，收口以一致性
核验替代 --reverify-certs 全量刷新，D34 裁决 4）：

  C1 R9A/R9B/R9C 三门复跑 exit 0＋结果 json 在档锚：
     - r9_m11_gate.py 复跑 exit 0（R9C 决策件门，G3 本身核四账本
       R8 终账冻结签名＝求解账增量 0）；
     - r9_s3_gate.py 复跑 exit 0（R9A S₃ 商环装配自写第二实现门）＋
       results/r9_s3_rederive.json 在档（kind=n9-r9-s3-rederive）；
     - r9_v2iv_gate.py 复跑 exit 0（R9B v2 相位 0 区间算术重验门）＋
       results/r9_v2iv.json 在档；
     ——门日志 exit 0 以「本门内复跑捕获的退出码＋墙钟」为据（复跑即
     在档证据，GAP-REPORT 本轮节 ⑥ 同口径转录）。
  C2 chain-only 干跑五字段逐位 diff（D34 裁决 4；R8A D30 先例）：
     endgame_chain.py --out /tmp（零 --reverify-certs）产物与存档
     endgame.json 五字段逐位——closed / blocking / assembledRecord
     精确分数串＋float / spliceMapVerdict（verdict＋assembled_equal_R7）
     / 组件 rigorous L0–L7 八布尔——零漂移；本轮零新证书零账本数值
     变更 ⇒ 不跑 --reverify-certs 全量刷新（理由留档 D34 裁决 4，
     ≥2 组独立在档不重复消耗）。
  C3 endgame.json 直读一致性＋铁律 Fraction 亲算：closed=false、
     blocking=[L0,L3]、assembledRecord==47517790735835014335570/
     1844674407417822803119（float 25.759445973097478）、margin 重算
     ＝E*−AR 精确、spliceMapVerdict=维持 v2（assembled_equal_R7=true）、
     组件 L1/L2/L5/L6/L7 rigorous=True＋L0/L3/L4=False（L4 off-path）、
     铁律 AR ≤ E*+1e-6（E* 十进制精确口径 Fraction("25.759986531")，
     D28 裁决 3）、AR==min(分区 bound) 精确重算、citedCertificates
     逐份在盘且 claimed_bound 一致、endgame.json 零改动（sha256 与
     R9 基线 7f49b40 相等——本轮零写入核验）。
  C4 文档三件锚：GAP-REPORT「Round 9（campaign dwfrun-41fdc169 第 4 轮，
     2026-10-10）」节（含 R9A/R9B/R9C 结果收编＋D34 回填＋诚实声明与
     未跑项锚）＋PROGRESS.md 置顶条目＋notes/decisions.md D34 结果回填
     （R9D 节）与 D35 收口裁决锚。
  C5 预算零增量终账：本轮 Σsolve_s=0（四任务零求解；四账本
     hermite_v2_campaign/m9_campaign/m10_campaign/typed_ladder 与 R8
     终账冻结值逐位相等＝无新求解行）＋campaign 累计 360418.3s=
     33.372/40 当量不变（Fraction 精确重算）＋任务书余量两读法并记
     （口径 A 0.2 当量＝2160s；口径 B 40 上限推 715817/108000≈6.628
     当量）两读法均 <12 ⇒ M11 触发器不可触发（与 R9C 决策件一致）＋
     R9 新增零求解产物（r9_s3_rederive.json/r9_v2iv.json）无正
     solve_s 字段。
  C6 树净：git status --porcelain 0 行（含 R9A/B/C 全部交付物已提交、
     endgame.json 零改动——与 C3 sha256 核验双保险）。

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
R9_S3_JSON = RESULTS / "r9_s3_rederive.json"
R9_V2IV_JSON = RESULTS / "r9_v2iv.json"
GAP_REPORT = REPO / "GAP-REPORT.md"
PROGRESS = REPO / "PROGRESS.md"
DECISIONS = REPO / "notes" / "decisions.md"
WORKFLOW_DATA = HERE.parents[2] / "thomson-workflow" / "data" / "energies.json"

SEED = 20261010
E_STAR_DEC = Fraction("25.759986531")    # 十进制精确口径（D28 裁决 3）
TOL_ESTAR = Fraction(1, 10**6)
EQUIV_UNIT_S = 10800                     # 1 当量 = 10800s（m9_campaign 口径）
R9_ASSEMBLED = "47517790735835014335570/1844674407417822803119"
R9_AR_FLOAT = 25.759445973097478
# campaign 累计冻结值（R8 终账＝R9 基线，四源和）
CAMPAIGN_SOLVE_S = {
    "m9_campaign": Fraction("102504.9"),
    "m10_campaign": Fraction("185065.6"),
    "typed_ladder_cap_m0748_M9": Fraction("42305.7"),
    "hermite_v2_campaign_phase1": Fraction("30542.1"),
}
CAMPAIGN_TOTAL = Fraction("360418.3")    # 3604183/10 s
CAMPAIGN_EQ = Fraction(3604183, 108000)  # = 33.372064814…（33.372 三位）
MARGIN_A = Fraction("0.2")               # 口径 A：任务书 R9 预算行余量
MARGIN_B = Fraction(40) - CAMPAIGN_EQ    # 口径 B：40 上限推 ≈6.628
TRIGGER_EQUIV = Fraction(12)             # M11 触发器阈值（D29 裁决 1）
# endgame.json R9 基线 sha256（HEAD=7f49b40 时点；零改动核验）
ENDGAME_SHA_R9_BASE = ("86863a09bf84e950e85fc5f902bc2b40"
                       "46a87f06703bd782e5148fc119afd69f")

R9C_GATE = HERE / "r9_m11_gate.py"
R9A_GATE = HERE / "r9_s3_gate.py"
R9B_GATE = HERE / "r9_v2iv_gate.py"


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


# ------------------------------------------------------------------ C1 三门

def run_subgate(path: Path, tag: str, timeout_s: int = 1800) -> float:
    check(path.exists(), f"{tag} 子门不在盘：{path}")
    t0 = time.time()
    r = subprocess.run([sys.executable, str(path)], capture_output=True,
                       text=True, timeout=timeout_s, cwd=str(REPO))
    wall = time.time() - t0
    tail = "\n".join((r.stdout or "").splitlines()[-6:])
    print(f"[{tag}] exit={r.returncode} ({wall:.1f}s)：{path.name}", flush=True)
    check(r.returncode == 0, f"{tag} 子门复跑 exit {r.returncode}：\n{tail}")
    return wall


def c1_subgates() -> dict:
    walls = {}
    walls["r9_m11_gate"] = run_subgate(R9C_GATE, "C1a")
    # R9A 结果 json 在档锚
    check(R9_S3_JSON.exists(), "C1 results/r9_s3_rederive.json 不在盘（R9A 交付缺件）")
    s3 = load_json(R9_S3_JSON)
    check(str(s3.get("kind")) == "n9-r9-s3-rederive",
          f"C1 r9_s3_rederive.json kind={s3.get('kind')} 非 n9-r9-s3-rederive")
    walls["r9_s3_gate"] = run_subgate(R9A_GATE, "C1b")
    # R9B 结果 json 在档锚
    check(R9_V2IV_JSON.exists(), "C1 results/r9_v2iv.json 不在盘（R9B 交付缺件）")
    v2iv = load_json(R9_V2IV_JSON)
    _v2iv_id = " ".join(str(v2iv.get(k) or "") for k in ("kind", "task",
                                                         "script"))
    check("v2iv" in _v2iv_id.lower() or "v2-interval" in _v2iv_id.lower(),
          f"C1 r9_v2iv.json kind/task/script 无 v2iv 标识：{_v2iv_id[:60]}")
    check(v2iv.get("all_pass") is True,
          "C1 r9_v2iv.json all_pass 非 True（R9B 重验未全过——按证据处置不硬凑）")
    walls["r9_v2iv_gate"] = run_subgate(R9B_GATE, "C1c")
    return walls


# ------------------------------------------------------------------ C2 干跑

def c2_chain_dry() -> dict:
    """chain-only 干跑五字段逐位 diff（零 --reverify-certs；产物只写临时目录）。

    五字段＝closed / blocking / assembledRecord（精确分数串＋float）/
    spliceMapVerdict（verdict＋assembled_equal_R7）/ 组件 rigorous L0–L7。
    其余字段（timestamp/code_version/certReverify/engineV2 探测时点等）
    允许叙述性漂移——R8A D30 先例口径；如漂移出现在五字段内即 FAIL。"""
    archived = load_json(ENDGAME)
    with tempfile.TemporaryDirectory(prefix="r9c_chain_dry_") as td:
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
    check(be["closed"] is False, "C2 closed 预期 false（本轮零求解收账轮）")
    check(ae["blocking"] == be["blocking"],
          f"C2 blocking 漂移：{ae['blocking']} vs {be['blocking']}")
    check(be["blocking"] == ["L0", "L3"],
          f"C2 blocking 预期 [L0, L3]，实为 {be['blocking']}")
    for k in ("value", "float"):
        av, bv = archived["assembledRecord"][k], dry["assembledRecord"][k]
        check(av == bv, f"C2 assembledRecord.{k} 漂移：{av} vs {bv}")
    check(dry["assembledRecord"]["value"] == R9_ASSEMBLED,
          "C2 干跑 assembledRecord 分数串非 R9 基线常量")
    check(dry["assembledRecord"]["float"] == R9_AR_FLOAT,
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
    expected = {"L0": False, "L1": True, "L2": True, "L3": False,
                "L4": False, "L5": True, "L6": True, "L7": True}
    for cid, exp in expected.items():
        check(amap[cid]["rigorous"] == bmap[cid]["rigorous"],
              f"C2 组件 {cid}.rigorous 漂移：存档 "
              f"{amap[cid]['rigorous']} vs 干跑 {bmap[cid]['rigorous']}")
        check(bmap[cid]["rigorous"] is exp,
              f"C2 组件 {cid}.rigorous 预期 {exp}，实为 {bmap[cid]['rigorous']}")
    print(f"[C2] chain-only 干跑五字段逐位零漂移 ✓（closed=false/"
          "blocking=[L0,L3]/assembledRecord 精确分数＋float/spliceMap 维持 v2/"
          "组件 L1·L2·L5·L6·L7 绿＋L0·L3·L4 红；零 --reverify-certs——本轮零新"
          f"证书零账本数值变更，D34 裁决 4；干跑 {time.time()-t0:.1f}s 级）",
          flush=True)
    return {"flipped": False}


# ------------------------------------------------------------------ C3 直读

def c3_direct_read() -> dict:
    d = load_json(ENDGAME)
    ec = d["endgameChain"]
    comps = {c["id"]: c for c in ec["components"]}
    # 直读五字段
    check(ec["closed"] is False, "C3 endgame.json closed 非 false")
    check(ec["blocking"] == ["L0", "L3"],
          f"C3 blocking 预期 [L0, L3]，实为 {ec['blocking']}")
    check(d["assembledRecord"]["value"] == R9_ASSEMBLED,
          "C3 assembledRecord 分数串非 R9 基线常量")
    check(d["assembledRecord"]["float"] == R9_AR_FLOAT,
          "C3 assembledRecord float 非 25.759445973097478")
    smv = d.get("spliceMapVerdict") or {}
    check("维持 v2" in str(smv.get("verdict"))
          and smv.get("assembled_equal_R7") is True,
          "C3 spliceMapVerdict 非『维持 v2』＋assembled_equal_R7=true")
    expected = {"L0": False, "L1": True, "L2": True, "L3": False,
                "L4": False, "L5": True, "L6": True, "L7": True}
    for cid, exp in expected.items():
        check(comps[cid]["rigorous"] is exp,
              f"C3 组件 {cid}.rigorous 预期 {exp}，实为 {comps[cid]['rigorous']}")
    # 自洽：closed == 关键路径合取（L4 onCriticalPath=false 不入合取）
    critical = [c for c in ec["components"] if c.get("onCriticalPath", True)]
    check(ec["closed"] == all(c["rigorous"] for c in critical),
          "C3 closed != 关键路径合取（自洽失败）")
    # 铁律 Fraction 亲算（E* 十进制精确口径）
    ar = frac(R9_ASSEMBLED)
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
    # endgame.json 零改动：sha256 与 R9 基线（HEAD=7f49b40 时点）相等
    sha = hashlib.sha256(ENDGAME.read_bytes()).hexdigest()
    check(sha == ENDGAME_SHA_R9_BASE,
          f"C3 endgame.json 零改动核验失败：sha256 {sha} != R9 基线 "
          f"{ENDGAME_SHA_R9_BASE}（本轮不得写入该账本——D34 裁决 4）")
    print(f"[C3] endgame.json 直读一致 ✓（closed=false/blocking=[L0,L3]/"
          "assembledRecord=47517790735835014335570/1844674407417822803119"
          f"=25.759445973097478/spliceMap 维持 v2/组件 L1·L2·L5·L6·L7 绿；"
          f"铁律 AR≤E*+1e-6 精确成立〔E*−AR={float(margin)} 精确重算〕；"
          f"AR==min(12 分区)；cited 12 份在盘；sha256 零改动 ✓）", flush=True)
    return {"margin": float(margin), "n_partition": len(d["partition"]),
            "n_cited": len(cited)}


# ------------------------------------------------------------------ C4 文档

def c4_docs() -> dict:
    gap = GAP_REPORT.read_text(encoding="utf-8")
    prog = PROGRESS.read_text(encoding="utf-8")
    dec = DECISIONS.read_text(encoding="utf-8")
    # 本轮节（campaign ID＋日期消歧）
    check(re.search(r"^#+ Round 9（campaign dwfrun-41fdc169 第 4 轮，2026-10-10",
                    gap, re.M) is not None,
          "C4 GAP-REPORT.md 无『Round 9（campaign dwfrun-41fdc169 第 4 轮，"
          "2026-10-10）』本轮节（D34 裁决 6 命名）")
    # 本轮节内容锚：R9A/R9B/R9C 收编＋D34 回填＋诚实声明与未跑项＋
    # chain-only 干跑＋endgame_gate 终验（收口方法学锚）
    r9_at = gap.find("# Round 9（campaign dwfrun-41fdc169")
    r9_body = gap[r9_at:] if r9_at >= 0 else ""
    for anchor in ("R9A", "R9B", "R9C", "D34", "诚实声明", "chain-only",
                   "endgame_gate"):
        check(anchor in r9_body,
              f"C4 GAP-REPORT Round 9 节缺『{anchor}』内容锚")
    # PROGRESS 置顶：前 120 行内含本轮条目
    head = prog.splitlines()[:120]
    check(any("Round 9（campaign dwfrun-41fdc169" in ln for ln in head),
          "C4 PROGRESS.md 前 120 行无本轮（campaign dwfrun-41fdc169）置顶条目")
    # decisions：D34 结果回填（R9D 节）＋D35 收口裁决
    m = re.search(r"^### D34（", dec, re.M)
    check(m is not None, "C4 notes/decisions.md 无 D34 节")
    check(re.search(r"D34 结果追加回填（R9D", dec) is not None,
          "C4 notes/decisions.md 无『D34 结果追加回填（R9D…』节（本收口会话回填）")
    check(re.search(r"^### D35（", dec, re.M) is not None,
          "C4 notes/decisions.md 无 D35 收口裁决节")
    return {"gap_round9": True, "progress_top": True,
            "d34_backfill": True, "d35": True}


# ------------------------------------------------------------------ C5 预算

def c5_budget() -> dict:
    # 四账本冻结值逐位相等（＝本轮无新求解行）
    m9 = load_json(M9_CAMPAIGN)
    m9_total = frac(m9["budget"]["total_solve_s"])
    check(m9_total == CAMPAIGN_SOLVE_S["m9_campaign"],
          f"C5 m9_campaign.total_solve_s={m9_total} != 冻结值 "
          f"{CAMPAIGN_SOLVE_S['m9_campaign']}（本轮出现新求解行？）")
    m10 = load_json(M10_CAMPAIGN)
    m10_total = frac(m10["budget"]["total_solve_s"])
    check(m10_total == CAMPAIGN_SOLVE_S["m10_campaign"],
          f"C5 m10_campaign.total_solve_s={m10_total} != 冻结值 "
          f"{CAMPAIGN_SOLVE_S['m10_campaign']}")
    tl = load_json(TYPED_LADDER)
    m9_rung = next(r for r in tl["rungs"]
                   if r.get("tag") == "m0748" and r.get("M") == 9)
    cap_s = frac(m9_rung["sdpa"]["solve_s"])
    check(cap_s == CAMPAIGN_SOLVE_S["typed_ladder_cap_m0748_M9"],
          f"C5 typed_ladder cap m0748 M9 solve_s={cap_s} != 冻结值 "
          f"{CAMPAIGN_SOLVE_S['typed_ladder_cap_m0748_M9']}")
    v2c = load_json(V2_CAMPAIGN)
    v2_s = frac(v2c["phase1"]["solve_s"])
    check(v2_s == CAMPAIGN_SOLVE_S["hermite_v2_campaign_phase1"],
          f"C5 hermite_v2_campaign.phase1.solve_s={v2_s} != 冻结值 "
          f"{CAMPAIGN_SOLVE_S['hermite_v2_campaign_phase1']}")
    check(frac(v2c["budget"]["solve_s_total"]) == v2_s,
          "C5 hermite_v2_campaign budget.solve_s_total 与 phase1 逐行不一致")
    # 四源和精确重算 == 360418.3s == 33.372/40 当量
    total = sum(CAMPAIGN_SOLVE_S.values())
    check(total == CAMPAIGN_TOTAL,
          f"C5 四源和重算 {total} != 冻结 {CAMPAIGN_TOTAL}")
    check(total / EQUIV_UNIT_S == CAMPAIGN_EQ,
          "C5 campaign 当量重算 != 3604183/108000")
    # 本轮增量：R9 四任务全部零求解 ⇒ Σsolve_s(round 9)==0
    # （四账本已与 R8 终账逐位相等 ⇒ 增量恒 0；新产物无正 solve_s）
    for jp in (R9_S3_JSON, R9_V2IV_JSON):
        blob = json.dumps(load_json(jp), ensure_ascii=False)
        for m_ in re.finditer(r'"(solve_s\w*)"\s*:\s*([0-9.]+)', blob):
            check(frac(m_.group(2)) == 0,
                  f"C5 {jp.name} 含正 solve 字段 {m_.group(1)}="
                  f"{m_.group(2)}（本轮零求解口径违例）")
    # 两读法余量并记＋M11 触发器不可触发（与 R9C 决策件一致）
    check(MARGIN_A < TRIGGER_EQUIV and MARGIN_B < TRIGGER_EQUIV,
          "C5 两读法余量均 <12 不成立（M11 触发器判定与 R9C 决策件失配）")
    print(f"[C5] 预算零增量 ✓（本轮 Σsolve_s=0——四账本与 R8 终账冻结值逐位"
          f"相等＝无新求解行；campaign 累计 {float(total)}s="
          f"{float(total / EQUIV_UNIT_S):.3f}/40 当量不变；两读法余量：口径 A "
          f"{float(MARGIN_A)} 当量＝{int(MARGIN_A * EQUIV_UNIT_S)}s、口径 B "
          f"{float(MARGIN_B):.3f} 当量，均 <12 ⇒ M11 触发器不可触发）", flush=True)
    return {"round_solve_s": 0, "campaign_total_s": float(total),
            "campaign_eq": float(total / EQUIV_UNIT_S),
            "margin_A": float(MARGIN_A), "margin_B": float(MARGIN_B)}


# ------------------------------------------------------------------ C6 树净

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
    print("[C6] git status --porcelain 为空 ✓（含 R9A/B/C 交付物全部提交＋"
          "endgame.json 相对 HEAD 零改动）", flush=True)


# ----------------------------------------------------------------------- main

def main() -> int:
    random.seed(SEED)                      # 固定种子（任务书条款；本门确定性）
    t0 = time.time()
    energies = load_json(WORKFLOW_DATA)["energies"]["9"]
    E_star = frac(energies["value"])
    check(E_star == E_STAR_DEC,
          f"C5 前置：energies.json E* {E_star} != 十进制精确口径 {E_STAR_DEC}")
    print(f"[gate] E* = {E_star}（{WORKFLOW_DATA}，十进制精确口径 D28 裁决 3）；"
          f"seed = {SEED}", flush=True)
    walls = c1_subgates()                                              # C1
    c2_chain_dry()                                                     # C2
    c3 = c3_direct_read()                                              # C3
    docs = c4_docs()                                                   # C4
    budget = c5_budget()                                               # C5
    c6_git_clean()                                                     # C6
    print(f"[gate] C1 三门复跑 exit 0 ✓（r9_m11_gate {walls['r9_m11_gate']:.1f}s"
          f"＋r9_s3_gate {walls['r9_s3_gate']:.1f}s＋r9_v2iv_gate "
          f"{walls['r9_v2iv_gate']:.1f}s；结果 json 两件在档锚 ✓）", flush=True)
    print(f"[gate] C4 文档三件 ✓（{docs}）", flush=True)
    print(f"[gate] PASS（{time.time()-t0:.1f}s）——exit 0", flush=True)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except GateFail as e:
        print(f"[gate] FAIL：{e}", flush=True)
        print("[gate] exit 1", flush=True)
        sys.exit(1)
