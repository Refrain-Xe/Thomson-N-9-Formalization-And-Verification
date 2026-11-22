#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r22_pattern_gate.py — R22A 验收门（G0–G3＋NC；seed 20261022）。

裸 python3 运行（仅依赖 mpmath 经 l4_orbit 间接；CWD 无关——路径全部从
__file__ 解析，l4_orbit_gate 同式先例）：

    python3 thomson-n9/numerics/bounds/r22_pattern_gate.py   # exit 0 = 过门
    python3 numerics/bounds/r22_pattern_gate.py              # CWD＝仓库根

被验件＝numerics/bounds/r22_pattern_numeric.py＋results/r22_pattern_numeric.json
（task r22a-pattern-numeric，D96 裁决 1；审计件零求解零 SDP 零 Lean 面新增）。

检查面：

  G0 锚面（在场＋只读＋隔离）：endgame.json sha256 活体==冻结锚
     86863a09…69f==json 记录；l4_orbit.json sha256 记录==活体；存档 json
     结构锚（artifact_class=='audit'、provenance.read_only==true、
     heavy_solves==0、seed==20261022、schema、script_sha256==活体、
     sort_keys+indent 逐字节复序列化一致、递归零 timestamp/code_version 键）；
     隔离面活体（endgame.json/endgame_chain.py 字节零 "r22"、citedCertificates
     零 r22、12 分区 partition 长度==12 不变）。
  G1 F1 枚举重建活体：importlib 复用 l4_orbit.py 全枚举
     （compute_context(50)＋build_tables＋run_scout＋verify_coloring）——
     scout==exact accepted==distinct==30240==json 记录==存档 labeledTotal。
  G2 F2/F3/F4/F5 活体＋门内独立移植第三分类实现：
     F2 ttp_reference_coloring() vs r15_b1_data.nodeOfN_rule（import）vs
        门内独立移植 gate_node_of_n——三方两两 36/36 零 mismatch==json 记录；
     F3 全 S₉ 扫描 |Aut|==12==json elements、生成元
        g₁/k/h（轮换记法 (012)(345)(678)/(01)(34)(78)/(03)(14)(25)）张成==
        全群、阶分布（lex 扫描序）[1,2,2,3,3,2,2,2,2,6,6,2]==json、
        阶重集 {1:1,2:7,3:2,6:2}（≅D₃×C₂）；
     F4 orbit{σ·ttp_ref:σ∈S₉} 9! 全扫描（禁采样）去重==30240==F1 幸存集
        全集逐位集合相等==存档 labeledTotal、9!/30240==12==|Stab|、
        orbit/survivor 指纹==json 记录；
     F5 存档 canonical rep（l4_orbit.json survivorSet.classes[0].
        representative）恰 12 个 σ-见证、lex-min σ₀==[0,5,6,4,2,1,7,3,8]
        ==json feedContract、见证列表==json、σ₀∘Aut==见证集。
  G3 幂等重跑：子进程重跑 r22_pattern_numeric.py --out /tmp，与存档
     results/r22_pattern_numeric.json 逐字节 cmp 一致（输出确定性：
     sort_keys+indent、无时间戳/code_version）。
  NC-a 篡改 orbit 或幸存集单元素：orbit_stab_consistency 必须 False
     （幸存集翻转一元／orbit 删一元／orbit 添外来元——三种注入）。
  NC-b 篡改 |Aut|==12 或生成元张成：aut_consistency 必须 False
     （Aut 删一元／Aut 换入非元／生成元 g₁→(01) 错置换）。
  NC-c 篡改存档 rep 单色：见证计数≠12（feed contract 判据必 FAIL）。

诚实边界：本门零求解零 SDP 零 Lean 面；endgame.json/l4_orbit.json/
tube.json/local_min.json 只读（sha256 锚双面）；r22 家族不入 12 分区
（隔离面）；幸存集/轨道全集逐位比较在门内活体执行、无采样降口径。
"""
from __future__ import annotations

import importlib.util
import json
import random
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent          # .../thomson-n9/numerics/bounds
REPO = HERE.parents[1]                          # .../thomson-n9
RESULTS = HERE / "results"
ARCHIVE = RESULTS / "r22_pattern_numeric.json"
L4_ARCHIVE = RESULTS / "l4_orbit.json"
ENDGAME = RESULTS / "endgame.json"
ENDGAME_CHAIN = HERE / "endgame_chain.py"
MAIN = HERE / "r22_pattern_numeric.py"

SEED = 20261022
ANCHOR_ENDGAME_SHA256 = ("86863a09bf84e950e85fc5f902bc2b4046a87f"
                         "06703bd782e5148fc119afd69f")
ANCHOR_ORDER_DIST_LEX = [1, 2, 2, 3, 3, 2, 2, 2, 2, 6, 6, 2]
ANCHOR_ORDER_MULTISET = {"1": 1, "2": 7, "3": 2, "6": 2}
ANCHOR_SIGMA0 = [0, 5, 6, 4, 2, 1, 7, 3, 8]
ANCHOR_CYCLES = {"g1": "(012)(345)(678)", "k": "(01)(34)(78)",
                 "h": "(03)(14)(25)"}


class GateFail(Exception):
    pass


def check(cond, msg):
    if not cond:
        raise GateFail(msg)
    return True


def load_json(p: Path):
    with open(p) as f:
        return json.load(f)


def sha256_file(p: Path) -> str:
    import hashlib
    return hashlib.sha256(p.read_bytes()).hexdigest()


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def tuple_set_sha256(mod, tuples) -> str:
    return mod.tuple_set_sha256(tuples)


def find_forbidden_keys(obj, bad, path=""):
    """递归扫描：键名含 timestamp/code_version 即违例。"""
    hits = []
    if isinstance(obj, dict):
        for k, v in obj.items():
            kl = str(k).lower()
            if "timestamp" in kl or "code_version" in kl:
                hits.append(f"{path}.{k}")
            hits += find_forbidden_keys(v, bad, f"{path}.{k}")
    elif isinstance(obj, list):
        for i, v in enumerate(obj):
            hits += find_forbidden_keys(v, bad, f"{path}[{i}]")
    return hits


# ---------------------------------------------------------------- 门内独立移植（第三分类实现）

def gate_node_of_n(i: int, j: int) -> int:
    """门内独立移植 nodeOfN（第三分类实现，与 r15 import／主件 port 异构）：
    按顶点几何位（上三角 z=+z*／下三角 z=−z*／帽 z=0，方位角 k）直接分类，
    不引用 r15/l4/主件的分类代码。ν 序（升序）：ν₁=−(1+z²)/2、ν₂=−ρ、
    ν₃=−1/2、ν₄=1−2z²、ν₅=(3z²−1)/2、ν₆=ρ/2。"""
    a, b = min(i, j), max(i, j)
    la, lb = a // 3, b // 3          # 0 上三角 / 1 下三角 / 2 帽
    if la == lb == 2:
        return 2                     # 帽-帽 → ν₃
    if la < 2 and lb < 2:
        if la == lb:
            return 4                 # 同层三角内部 → ν₅
        if a % 3 == b % 3:
            return 3                 # 竖棱（同方位）→ ν₄
        return 0                     # 上下错位 → ν₁
    cap, prism = (a, b) if la == 2 else (b, a)
    d = (cap % 3 - prism % 3) % 3
    return 5 if d in (0, 2) else 1   # 帽-棱：残差 0,2 → ν₆；1 → ν₂


# ---------------------------------------------------------------- 主门

def main() -> int:
    t_start = time.time()
    random.seed(SEED)
    print(f"[gate] seed={SEED}  CWD-independent（从 __file__ 解析）", flush=True)

    check(ARCHIVE.exists(), f"存档缺失: {ARCHIVE}")
    check(L4_ARCHIVE.exists(), f"l4_orbit.json 缺失: {L4_ARCHIVE}")
    check(ENDGAME.exists(), f"endgame.json 缺失: {ENDGAME}")
    archive = load_json(ARCHIVE)
    mod = load_module("r22_pattern_numeric", MAIN)
    check(mod.SEED == SEED, f"seed 不一致: 模块 {mod.SEED} vs 门 {SEED}")
    l4 = load_module("l4_orbit", HERE / "l4_orbit.py")
    r15 = load_module("r15_b1_data", HERE / "r15_b1_data.py")

    # ================= G0 锚面
    endgame_sha = sha256_file(ENDGAME)
    check(endgame_sha == ANCHOR_ENDGAME_SHA256,
          f"G0 endgame.json sha256 活体 {endgame_sha} ≠ 冻结锚")
    check(archive.get("artifact_class") == "audit",
          f"G0 artifact_class != 'audit': {archive.get('artifact_class')!r}")
    check(archive.get("provenance", {}).get("read_only") is True,
          "G0 provenance.read_only != true")
    check(archive.get("heavy_solves") == 0,
          f"G0 heavy_solves != 0: {archive.get('heavy_solves')!r}")
    check(archive.get("seed") == SEED, f"G0 seed != {SEED}")
    check(archive.get("schema") == "thomson-n9/bounds/r22-pattern-numeric/1",
          f"G0 schema 异常: {archive.get('schema')!r}")
    check(archive.get("script_sha256") == sha256_file(MAIN),
          "G0 script_sha256 与当前 r22_pattern_numeric.py 不一致（改码后未重产存档）")
    raw = ARCHIVE.read_bytes()
    check(raw == (json.dumps(archive, indent=1, sort_keys=True,
                             ensure_ascii=False) + "\n").encode(),
          "G0 存档非 sort_keys+indent 确定性字节布局")
    bad_keys = find_forbidden_keys(archive, None)
    check(not bad_keys, f"G0 出现 timestamp/code_version 键: {bad_keys}")
    l4_json = load_json(L4_ARCHIVE)
    check(archive["inputs"]["l4_orbit_json"]["sha256"] == sha256_file(L4_ARCHIVE),
          "G0 l4_orbit.json sha256 记录与活体不一致")
    check(l4_json["survivorSet"]["classes"][0]["representative"]
          == archive["feedContract"]["canonicalRep"],
          "G0 json canonicalRep ≠ l4_orbit.json 存档 rep")
    # 隔离面活体
    check(b"r22" not in ENDGAME.read_bytes(),
          "G0 隔离面：endgame.json 字节出现 r22")
    check(b"r22" not in ENDGAME_CHAIN.read_bytes(),
          "G0 隔离面：endgame_chain.py 字节出现 r22")
    endgame_doc = load_json(ENDGAME)
    cited_paths = [c.get("path", "") for c in endgame_doc.get("citedCertificates", [])]
    check(not [p for p in cited_paths if "r22" in p],
          f"G0 隔离面：citedCertificates 出现 r22: {cited_paths}")
    check(len(endgame_doc.get("partition", [])) == 12,
          f"G0 12 分区 partition 长度 != 12: {len(endgame_doc.get('partition', []))}")
    print("[gate-0] 锚面：endgame.json sha256==冻结锚、结构锚、隔离面"
          "（endgame.json/endgame_chain.py 零 r22 字节、citedCertificates 零 r22、"
          "12 分区不变）✓", flush=True)

    # ================= G1 F1 枚举重建活体
    t0 = time.time()
    ctx = l4.compute_context(mod.DPS)
    NU = l4.nu_float(ctx["zmid"])
    ok3, ok4, _, _ = l4.build_tables(NU)
    sols = l4.run_scout(ok3, ok4)
    survivors = []
    for s in sols:
        verdict, _ = l4.verify_coloring(l4.coloring_from_tuple(s),
                                        ctx["tri_dec"], ctx["quad_dec"])
        if verdict == "accepted":
            survivors.append(s)
    dt_enum = time.time() - t0
    check(len(sols) == 30240, f"G1 scout={len(sols)} != 30240")
    check(len(survivors) == 30240, f"G1 exact accepted={len(survivors)} != 30240")
    check(len(set(survivors)) == 30240,
          f"G1 distinct={len(set(survivors))} != 30240")
    en = archive["enumeration"]
    check(en["scout"] == en["exactAccepted"] == en["distinctAccepted"] == 30240,
          f"G1 json 枚举记录异常: {en['scout']}/{en['exactAccepted']}/"
          f"{en['distinctAccepted']}")
    check(l4_json["survivorSet"]["labeledTotal"] == 30240
          == en["archivedLabeledTotal"], "G1 存档 labeledTotal != 30240")
    check(en["survivorSetSha256"] == tuple_set_sha256(mod, survivors),
          "G1 幸存集指纹 != json 记录")
    print(f"[gate-1] F1 活体重建：scout==accepted==distinct==30240"
          f"（{dt_enum:.1f}s）；指纹==json ✓", flush=True)

    # ================= G2 F2/F3/F4/F5 活体
    # ---- F2 桥面
    ttp_ref, realiz_checks = l4.ttp_reference_coloring()
    ttp_tuple = tuple(ttp_ref[e] for e in mod.PAIRS)
    rule_tuple = mod.node_tuple_of(r15.nodeOfN_rule)
    gate_tuple = mod.node_tuple_of(gate_node_of_n)
    mis_cert_rule = sum(1 for k in range(36) if ttp_tuple[k] != rule_tuple[k])
    mis_cert_gate = sum(1 for k in range(36) if ttp_tuple[k] != gate_tuple[k])
    mis_rule_gate = sum(1 for k in range(36) if rule_tuple[k] != gate_tuple[k])
    check(mis_cert_rule == mis_cert_gate == mis_rule_gate == 0,
          f"G2/F2 出现 mismatch: {mis_cert_rule}/{mis_cert_gate}/{mis_rule_gate}")
    bm = archive["bridge"]["mismatches"]
    check(bm["certificate_vs_ruleImport"] == bm["certificate_vs_independentPort"]
          == bm["ruleImport_vs_independentPort"] == 0
          and archive["bridge"]["pairsChecked"] == 36,
          f"G2/F2 json 桥面记录异常: {bm}")
    print("[gate-2/F2] 桥面：构造证书 vs r15 import vs 门内独立移植 "
          "36/36 零 mismatch ✓", flush=True)

    # ---- F3 自同构群面
    aut = mod.aut_scan(ttp_tuple, rule_tuple)
    gens = [mod.GEN_G1, mod.GEN_K, mod.GEN_H]
    check(len(aut) == 12, f"G2/F3 |Aut|={len(aut)} != 12")
    ag = archive["automorphismGroup"]
    check(ag["order"] == 12 and ag["elements"] == [list(s) for s in aut],
          "G2/F3 json elements ≠ 活体 Aut 扫描")
    check(mod.span(gens) == set(aut) and ag["spanEqualsGroup"] is True,
          "G2/F3 生成元张成 ≠ 全群")
    for name, perm in (("g1", mod.GEN_G1), ("k", mod.GEN_K), ("h", mod.GEN_H)):
        check(ag["generators"][name]["perm"] == list(perm)
              and ag["generators"][name]["cycles"] == ANCHOR_CYCLES[name]
              and mod.cycles_str(perm) == ANCHOR_CYCLES[name],
              f"G2/F3 生成元 {name} 记法/记录异常")
    orders_lex = [mod.perm_order(s) for s in aut]
    check(orders_lex == ANCHOR_ORDER_DIST_LEX == ag["orderDistributionLexScan"],
          f"G2/F3 阶分布(lex) {orders_lex} ≠ 锚 {ANCHOR_ORDER_DIST_LEX}")
    mult = {}
    for s in aut:
        mult[mod.perm_order(s)] = mult.get(mod.perm_order(s), 0) + 1
    check({str(k): mult[k] for k in sorted(mult)} == ANCHOR_ORDER_MULTISET
          == ag["orderMultiset"], f"G2/F3 阶重集 {mult} ≠ D₃×C₂ 型")
    print(f"[gate-2/F3] 自同构群：|Aut|=12、生成元张成==全群、阶分布(lex)"
          f"={orders_lex}（≅D₃×C₂）✓", flush=True)

    # ---- F4 轨道-稳定子面
    orbit = mod.orbit_set(ttp_tuple)
    check(mod.orbit_stab_consistency(orbit, survivors,
                                     l4_json["survivorSet"]["labeledTotal"]),
          "G2/F4 轨道-稳定子判据失败（全集逐位集合相等/计数/9!÷）")
    os_ = archive["orbitStabilizer"]
    check(os_["orbitSize"] == 30240 and os_["orbitEqualsSurvivorSet"] is True
          and os_["index"] == 12 and os_["stabOrder"] == 12
          and os_["orbitSha256"] == tuple_set_sha256(mod, orbit),
          "G2/F4 json 轨道记录异常")
    check(os_["sampling"] == "none-full-set（9!=362880 全扫描，禁采样）",
          f"G2/F4 sampling 口径异常: {os_['sampling']!r}")
    print("[gate-2/F4] 轨道-稳定子：orbit(9! 全扫描)==幸存集全集逐位相等==30240、"
          "9!/30240==12==|Stab| ✓", flush=True)

    # ---- F5 σ₀ 实例化面
    rep = tuple(l4_json["survivorSet"]["classes"][0]["representative"])
    check(rep in set(survivors), "G2/F5 存档 rep 不在活体幸存集")
    witnesses = mod.witness_scan(rep, rule_tuple)
    sigma0 = min(witnesses)
    fc = archive["feedContract"]
    check(len(witnesses) == 12 == fc["witnessCount"],
          f"G2/F5 见证计数 {len(witnesses)} != 12")
    check(list(sigma0) == ANCHOR_SIGMA0 == fc["sigma0LexMin"],
          f"G2/F5 σ₀ {list(sigma0)} != 锚 {ANCHOR_SIGMA0}")
    check(fc["witnesses"] == [list(s) for s in witnesses],
          "G2/F5 json 见证列表 ≠ 活体扫描")
    check({mod.compose(sigma0, s) for s in aut} == set(witnesses),
          "G2/F5 见证集 ≠ σ₀∘Aut 陪集")
    print(f"[gate-2/F5] σ₀ 实例化：rep 见证恰 12、lex-min σ₀={ANCHOR_SIGMA0}、"
          f"陪集一致 ✓", flush=True)

    # ================= G3 幂等重跑（子进程 cmp）
    with tempfile.TemporaryDirectory() as td:
        tmp_out = Path(td) / "r22_pattern_rerun.json"
        t0 = time.time()
        r = subprocess.run(
            [sys.executable, str(MAIN), "--out", str(tmp_out)],
            cwd=str(REPO), capture_output=True, text=True, timeout=480)
        dt_rerun = time.time() - t0
        print(f"[gate-3] rerun exit={r.returncode} ({dt_rerun:.1f}s)", flush=True)
        if r.returncode != 0:
            tail = "\n".join((r.stdout or "") + (r.stderr or "")).splitlines()[-12:]
            raise GateFail(f"G3 子进程重跑 exit {r.returncode}:\n{tail}")
        check(tmp_out.read_bytes() == raw,
              "G3 幂等重跑与存档不逐字节一致（cmp）")
        print("[gate-3] 幂等重跑与存档逐字节一致（cmp）✓", flush=True)

        # ================= NC 负对照（同一判据函数，篡改必 FAIL）
        # NC-a 篡改 orbit 或幸存集单元素
        s_flip = set(survivors)
        s_flip.discard(survivors[0])
        s_flip.add(tuple(1 if v == 0 else v for v in survivors[0]))
        o_drop = set(orbit)
        o_drop.pop()
        o_add = set(orbit)
        o_add.add(tuple(5 for _ in range(36)))
        check(not mod.orbit_stab_consistency(orbit, s_flip, 30240),
              "NC-a 幸存集翻转一元未被检出")
        check(not mod.orbit_stab_consistency(o_drop, survivors, 30240),
              "NC-a orbit 删一元未被检出")
        check(not mod.orbit_stab_consistency(o_add, survivors, 30240),
              "NC-a orbit 添外来元未被检出")
        print("[gate-NC-a] 篡改 orbit/幸存集单元素（翻转/删/添）→ 判据全 False ✓",
              flush=True)

        # NC-b 篡改 |Aut|==12 或生成元张成
        check(not mod.aut_consistency(aut[:-1], gens),
              "NC-b Aut 删一元未被检出")
        wrong = (1, 0, 2, 3, 4, 5, 6, 7, 8)          # (01)——非 Aut 元
        check(wrong not in set(aut), "NC-b 错置换恰为 Aut 元（注入失效）")
        swapped = list(aut)
        swapped[5] = wrong
        check(not mod.aut_consistency(swapped, gens),
              "NC-b Aut 换入非元未被检出")
        check(not mod.aut_consistency(aut, [wrong, mod.GEN_K, mod.GEN_H]),
              "NC-b 生成元 g₁→(01) 篡改未被检出")
        print("[gate-NC-b] 篡改 |Aut|/张成（删元/换非元/错生成元）→ 判据全 False ✓",
              flush=True)

        # NC-c 篡改存档 rep 单色
        rep2 = list(rep)
        rep2[0] = 1 if rep[0] != 1 else 2
        w2 = mod.witness_scan(tuple(rep2), rule_tuple)
        check(len(w2) != 12,
              f"NC-c 篡改 rep 单色后见证计数仍 12（注入失效）: {len(w2)}")
        print(f"[gate-NC-c] 篡改 rep 单色 → 见证计数 {len(w2)}≠12（feed contract "
              f"判据 FAIL）✓", flush=True)

    print(f"[gate] ALL PASS ({time.time() - t_start:.1f}s)", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
