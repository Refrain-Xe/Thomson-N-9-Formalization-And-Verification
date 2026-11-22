#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""l4_orbit_gate.py — L4 双轨道邻型计数（R7-2）验收门。

裸 python3 运行（仅依赖 mpmath；CWD 无关——路径全部从 __file__ 解析）：

    python3 thomson-n9/numerics/bounds/l4_orbit_gate.py     # exit 0 = 过门

五项检查（对应任务书 R7-2 验收门①–⑤）＋一项汇总：

  ① 幂等重算：子进程重跑 l4_orbit.py --dps 50 --out tmp，与存档
     results/l4_orbit.json 逐字节一致（输出确定性：无时间戳/运行时）。
  ② 正对照：TTP 染色必在幸存集——门内独立重建 TTP 染色（闭式分类，不读
     存档），与模块构造证书的染色全等、过精确层（accepted）、与存档代表
     元素 iso、存档 isoClasses=1 且 isoToTTP=true。
  ③ 负对照 ≥3：
     (a) 单边改色 ν₆→ν₅：精确层必须拒绝，且拒绝路由＝4×4 det（nonzero-on-box）；
     (a2) 单边改色 ν₄→ν₃：同样必须被拒绝（任意路由）；
     (b) 区间精度截断 dps15：E_ttp vs E* 边界支路必须被标记 undecided
         （非静默通过）；且 dps15 不得把 dps50 的 undecided 支路「偷偷判定」
         （无假精度）；如实报告 dps15 新增 undecided 支路数；
     (c) Vandermonde 常数篡改：对存档副本篡改 c_V / ‖V⁻¹‖_∞ / ρ_max，
         字段级一致性核对（存档 vs 重跑）必须检出（真存档须通过同一核对）。
  ④ 幸存者非空且逐个有显式处置（≅TTP 实现证书 / E>E* 区间证书 / gaps），
     引理形式与类集一致（unconditional ⇒ 全类 isoToTTP）。
  ⑤ 轨道计数与 tube.json 重数配平：Σ_y #type_y = 2·mult 逐节点、类目计数
     和=36、棱顶/帽顶轮廓×6/×3 复原 perNodeSums、类目→节点与闭式推导一致。
  ⑥ 汇总自洽：scout 幸存数=精确层接受数=iso 成员总数；tube 10 位节点值
     落入闭式区间；scout 完备性界 < 容差；exactLayer undecided=0；seed 一致。
"""
from __future__ import annotations

import importlib.util
import json
import random
import subprocess
import sys
import tempfile
import time
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent          # .../thomson-n9/numerics/bounds
REPO = HERE.parents[1]                          # .../thomson-n9
RESULTS = HERE / "results"
ARCHIVE = RESULTS / "l4_orbit.json"
TUBE = RESULTS / "tube.json"

SEED = 20261007


class GateFail(Exception):
    pass


def check(cond, msg):
    if not cond:
        raise GateFail(msg)
    return True


def load_json(p: Path):
    with open(p) as f:
        return json.load(f)


# ---------------------------------------------------------------- 模块装载

def load_module():
    spec = importlib.util.spec_from_file_location("l4_orbit", HERE / "l4_orbit.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


# ---------------------------------------------------------------- ① 幂等重算

def rerun(mod, tmp_out: Path) -> float:
    t0 = time.time()
    r = subprocess.run(
        [sys.executable, str(HERE / "l4_orbit.py"), "--out", str(tmp_out),
         "--dps", "50"],
        cwd=str(REPO), capture_output=True, text=True, timeout=480)
    dt = time.time() - t0
    print(f"[gate-1] rerun exit={r.returncode} ({dt:.1f}s)", flush=True)
    if r.returncode != 0:
        tail = "\n".join((r.stdout or "").splitlines()[-12:])
        raise GateFail(f"① l4_orbit.py 重跑 exit {r.returncode}:\n{tail}")
    return dt


def bitwise_identical(a: Path, b: Path):
    return a.read_bytes() == b.read_bytes()


# ---------------------------------------------------------------- ③(c) 字段级一致性

STABILITY_FIELDS = [
    ("stability", "vandermonde", "normInvInf"),
    ("stability", "vandermonde", "normInvFro"),
    ("stability", "vandermonde", "sigmaMinLower_cV"),
    ("stability", "countingThreshold", "rhoMax_deltaOnly"),
    ("stability", "antipodalSeparation", "minNuaNuB_lower"),
]


def get_field(d, path):
    for k in path:
        d = d[k]
    return d


def check_stability_consistency(archive: dict, rerun_out: dict, label: str):
    for path in STABILITY_FIELDS:
        av, rv = get_field(archive, path), get_field(rerun_out, path)
        check(av == rv, f"③(c) [{label}] 一致性检出失配: {'.'.join(path)} "
                        f"存档={av!r} vs 重跑={rv!r}")


# ---------------------------------------------------------------- ② 门内独立 TTP 染色

def gate_ttp_coloring():
    """闭式独立重建（不读存档）：上/下三角 k=0,1,2（z=±z*，半径 ρ）、帽
    j=0,1,2（z=0，半径 1，角 π/3+2πj/3）。顶点序：top0..2, bottom0..2, cap0..2。
    节点序 ν₁..ν₆（升序）：-（1+z²)/2, -ρ, -1/2, 1-2z², (3z²-1)/2, ρ/2。
    分类：
      三角内部（同层）        → ν₅ (4)
      上下同方位（竖棱）      → ν₄ (3)
      上下错位               → ν₁ (0)
      帽-帽                  → ν₃ (2)
      帽 j-棱 k，(j−k)≡0,2   → ν₆ (5)
      帽 j-棱 k，(j−k)≡1     → ν₂ (1)
    """
    C = {}
    for i in range(9):
        for j in range(i + 1, 9):
            ti = i % 3
            tj = j % 3
            if i < 6 and j < 6:
                li = 0 if i < 3 else 1                 # 层
                lj = 0 if j < 3 else 1
                if li == lj:
                    c = 4                              # ν₅ 三角内部
                elif ti == tj:
                    c = 3                              # ν₄ 竖棱
                else:
                    c = 0                              # ν₁ 错位
            elif i >= 6 and j >= 6:
                c = 2                                  # ν₃ 帽-帽
            else:
                cap = (i if i >= 6 else j) - 6
                pr = j if i >= 6 else i
                c = 5 if (cap - pr) % 3 in (0, 2) else 1
            C[(i, j)] = c
    return C


# ---------------------------------------------------------------- 主门

def main() -> int:
    t_start = time.time()
    random.seed(SEED)
    print(f"[gate] seed={SEED}  CWD-independent（从 __file__ 解析）", flush=True)

    check(ARCHIVE.exists(), f"存档缺失: {ARCHIVE}")
    archive = load_json(ARCHIVE)
    mod = load_module()
    check(mod.SEED == SEED, f"seed 不一致: 模块 {mod.SEED} vs 门 {SEED}")

    # ---------------- ① 幂等重算
    with tempfile.TemporaryDirectory() as td:
        tmp_out = Path(td) / "l4_orbit_rerun.json"
        rerun(mod, tmp_out)
        check(bitwise_identical(ARCHIVE, tmp_out),
              "① 幂等重算与存档不逐位一致")
        rerun_out = load_json(tmp_out)
        print("[gate-1] 存档 vs 重跑逐字节一致 ✓", flush=True)

        # ---------------- ③(c) Vandermonde 常数篡改（同一核对函数，真档须过）
        check_stability_consistency(archive, rerun_out, "真存档")
        tampered = 0
        for path, mutate in [
            (("stability", "vandermonde", "sigmaMinLower_cV"),
             lambda v: "9.9999999999999999e-01"),
            (("stability", "vandermonde", "normInvInf"),
             lambda v: [v[0], "1.0"]),
            (("stability", "countingThreshold", "rhoMax_deltaOnly"),
             lambda v: 0.5),
        ]:
            tam = json.loads(json.dumps(archive))
            set_field = lambda d, p, val: (d.__setitem__(p[-1], val)
                                           if len(p) == 1 else
                                           set_field(d[p[0]], p[1:], val))
            set_field(tam, list(path), mutate(get_field(tam, path)))
            try:
                check_stability_consistency(tam, rerun_out, f"篡改 {path[-1]}")
                raise GateFail(f"③(c) 篡改 {'.'.join(path)} 未被检出")
            except GateFail as e:
                if "未被检出" in str(e):
                    raise
                tampered += 1
                print(f"[gate-3c] 篡改 {'.'.join(path)} 被检出 ✓", flush=True)
        check(tampered == 3, f"③(c) 篡改检出数 {tampered} < 3")

    # ---------------- ② 正对照
    ttp_gate = gate_ttp_coloring()
    ttp_mod, checks = mod.ttp_reference_coloring()
    check(ttp_gate == ttp_mod, "② 门内独立 TTP 染色 ≠ 模块构造证书染色")
    ctx = mod.compute_context(50)
    verdict, route = mod.verify_coloring(ttp_gate, ctx["tri_dec"], ctx["quad_dec"])
    check(verdict == "accepted",
          f"② 正对照：TTP 染色未过精确层（{verdict}, {route}）")
    rep = archive["survivorSet"]["representative"]
    repC = mod.coloring_from_tuple(tuple(rep))
    check(mod.iso_to(ttp_gate, repC), "② 门内 TTP 染色与存档代表元素不 iso")
    check(archive["survivorSet"]["isoClasses"] == 1
          and archive["survivorSet"]["classes"][0]["isoToTTP"] is True
          and archive["survivorSet"]["labeledTotal"] > 0,
          "② 存档 isoClasses/isoToTTP/labeledTotal 异常")
    hist_gate = [sum(1 for v in ttp_gate.values() if v == k) for k in range(6)]
    check(hist_gate == archive["survivorSet"]["classes"][0]["histogram"],
          f"② 门内 TTP 直方图 {hist_gate} ≠ 存档类直方图")
    print(f"[gate-2] 正对照：独立重建 TTP 染色 accepted＋iso＋直方图 "
          f"{hist_gate} ✓（构造证书 {len(checks)} 项）", flush=True)

    # ---------------- ③(a)/(a2) 单边改色负对照
    for (frm, to, want_route) in [(5, 4, "4x4"), (3, 2, None)]:
        edge = next(e for e in sorted(ttp_gate) if ttp_gate[e] == frm)
        C2 = dict(ttp_gate)
        C2[edge] = to
        v2, r2 = mod.verify_coloring(C2, ctx["tri_dec"], ctx["quad_dec"])
        check(v2 == "rejected",
              f"③(a) 改色 ν{frm+1}→ν{to+1}（边 {edge}）未被拒绝: {v2} {r2}")
        if want_route is not None:
            check(r2[0] == want_route,
                  f"③(a) 改色 ν{frm+1}→ν{to+1} 拒绝路由 {r2[0]} ≠ {want_route}")
            check(r2[2] == mod.D_REJ_NZ,
                  f"③(a) 拒绝决策 {r2[2]} ≠ nonzero-on-box")
        print(f"[gate-3a] 改色 ν{frm+1}→ν{to+1} 边{edge} 被拒（路由 {r2[0]}, "
              f"{r2[2]}）✓", flush=True)

    # ---------------- ③(b) dps15 截断
    ctx15 = mod.compute_context(15)
    E15 = mod.E_interval_from_hist(hist_gate, ctx15["nu_iv"])
    v15 = mod.E_branch_verdict(E15, ctx["e_star"])
    check(v15 == "undecided-at-zbox",
          f"③(b) dps15 边界支路（E_ttp vs E*）未被标记 undecided: {v15}")
    E50 = mod.E_interval_from_hist(hist_gate, ctx["nu_iv"])
    v50 = mod.E_branch_verdict(E50, ctx["e_star"])
    check(v50 == "undecided-at-zbox",
          f"③(b) dps50 边界支路同样应 undecided（结构边界）: {v50}")
    # 无假精度：dps50 undecided 的支路，dps15 不得判定
    bad = [k for k, (d, _) in ctx["quad_dec"].items()
           if d[0] == mod.D_UNDEC and ctx15["quad_dec"][k][0] != mod.D_UNDEC]
    bad += [k for k, (d, _) in ctx["tri_dec"].items()
            if d[0] == mod.D_UNDEC and ctx15["tri_dec"][k][0] != mod.D_UNDEC]
    check(not bad, f"③(b) dps15 出现假精度（dps50 undecided 被 dps15 判定）: "
                   f"{bad[:3]}")
    extra15 = sum(1 for k, (d, _) in ctx["quad_dec"].items()
                  if d[0] != mod.D_UNDEC and ctx15["quad_dec"][k][0] == mod.D_UNDEC)
    extra15 += sum(1 for k, (d, _) in ctx["tri_dec"].items()
                   if d[0] != mod.D_UNDEC and ctx15["tri_dec"][k][0] == mod.D_UNDEC)
    w15 = float(E15.b - E15.a)
    w50 = float(E50.b - E50.a)
    print(f"[gate-3b] dps15：E 边界支路 undecided（非静默）✓；无假精度 ✓；"
          f"dps15 新增 undecided 支路 {extra15}（类 margins ≥5.4e-5，"
          f"截断不致骑墙——如实报告）；E 区间宽 15dps={w15:.6e} ≥ "
          f"50dps={w50:.6e}: {w15 >= w50}", flush=True)
    check(w15 >= w50, "③(b) E 区间宽度 dps15 < dps50（区间外包单调性异常）")

    # ---------------- ④ 幸存者处置
    ss = archive["survivorSet"]
    check(ss["nonEmpty"] is True, "④ 幸存集为空")
    allowed = {"congruent-to-TTP", "E-greater-than-Estar-excluded", "gap-see-gaps"}
    for cls in ss["classes"]:
        check(cls["disposition"] in allowed,
              f"④ 类 {cls['index']} 处置非法: {cls['disposition']}")
        if cls["disposition"] == "congruent-to-TTP":
            check(len(cls["realizationCertificate"]) == 3,
                  f"④ 类 {cls['index']} 实现证书缺失")
            check(cls["isoToTTP"] is True, f"④ 类 {cls['index']} isoToTTP 不一致")
        if cls["disposition"] == "E-greater-than-Estar-excluded":
            ec = archive["energyTable"]["classes"][cls["index"]]
            check(ec["vs_Estar"] == "greater-than-Estar",
                  f"④ 类 {cls['index']} E 证书缺失/不符")
    form = archive["lemma"]["form"]
    if form == "unconditional":
        check(all(c["isoToTTP"] for c in ss["classes"]),
              "④ unconditional 形式但存在非 TTP 类")
    check(isinstance(archive["gaps"], list) and len(archive["gaps"]) >= 1
          and all(isinstance(g, str) and g for g in archive["gaps"]),
          "④ gaps 非空字符串列表")
    print(f"[gate-4] 幸存集非空（{ss['labeledTotal']} 标号染色, "
          f"{ss['isoClasses']} 类）；处置={[c['disposition'] for c in ss['classes']]}；"
          f"lemma.form={form}；gaps={len(archive['gaps'])} 条 ✓", flush=True)

    # ---------------- ⑤ 轨道配平
    ob = archive["orbitBalance"]
    tube = load_json(TUBE)
    mults = tube["ttp_spectrum"]["multiplicities"]
    check(ob["perNodeSums_Sigma_y"] == [2 * m for m in mults] == ob["twoTimesMult"],
          f"⑤ Σ_y #type ≠ 2·mult: {ob['perNodeSums_Sigma_y']} vs "
          f"{[2 * m for m in mults]}")
    check(ob["balanced"] is True, "⑤ balanced ≠ true")
    reconstruct = [6 * ob["prismVertexProfile"][k] + 3 * ob["capVertexProfile"][k]
                   for k in range(6)]
    check(reconstruct == ob["perNodeSums_Sigma_y"],
          f"⑤ 6·棱顶轮廓+3·帽顶轮廓 ≠ perNodeSums: {reconstruct}")
    check(sum(c["count"] for c in ob["categories"].values()) == 36,
          "⑤ 类目计数和 ≠ 36")
    expect_node = {"triangle-internal": 4, "vertical-edge": 3, "cross-misaligned": 0,
                   "cap-cap": 2, "cap-prism-r0": 5, "cap-prism-r1": 1,
                   "cap-prism-r2": 5}
    for name, spec in expect_node.items():
        check(ob["categories"][name]["node"] == spec,
              f"⑤ 类目 {name} 节点 {ob['categories'][name]['node']} ≠ 闭式 {spec}")
    expect_cnt = {"triangle-internal": 6, "vertical-edge": 3, "cross-misaligned": 6,
                  "cap-cap": 3, "cap-prism-r0": 6, "cap-prism-r1": 6,
                  "cap-prism-r2": 6}
    for name, cnt in expect_cnt.items():
        check(ob["categories"][name]["count"] == cnt,
              f"⑤ 类目 {name} 计数 {ob['categories'][name]['count']} ≠ {cnt}")
    print("[gate-5] 轨道配平：Σ_y=2·mult 逐节点 ✓；轮廓复原 ✓；类目闭式一致 ✓",
          flush=True)

    # ---------------- ⑥ 汇总自洽
    el = archive["exactLayer"]
    sc = archive["scout"]
    check(sc["labeledSurvivors"] == ss["labeledTotal"] == el["accepted"],
          f"⑥ scout {sc['labeledSurvivors']} / 存档 {ss['labeledTotal']} / "
          f"精确层 {el['accepted']} 不一致")
    check(el["undecidedSurvivors"] == 0 and el["rejected"] == 0,
          f"⑥ 精确层 rejected/undecided 非 0: {el['rejected']}/{el['undecidedSurvivors']}")
    check(all(archive["nodes"]["tube_10digit_contained"]),
          "⑥ tube 10 位节点值未全落入闭式区间")
    check(sc["completenessBound4"] < sc["tol4"]
          and sc["completenessBound3"] < -sc["tol3"],
          "⑥ scout 完备性界不小于容差")
    check(archive["seed"] == SEED and archive["dps"] == 50,
          "⑥ 存档 seed/dps 异常")
    import hashlib
    check(archive["script_sha256"] ==
          hashlib.sha256((HERE / "l4_orbit.py").read_bytes()).hexdigest(),
          "⑥ 存档 script_sha256 与当前脚本不一致（改码后未重产存档）")
    print("[gate-6] 汇总自洽 ✓（scout=exact=iso 成员数、tube 核对、完备性界、"
          "sha256）", flush=True)

    print(f"[gate] ALL PASS ({time.time() - t_start:.1f}s)", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
