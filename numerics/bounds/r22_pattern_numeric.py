#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r22_pattern_numeric.py — R22A 主件：l4_orbit (P1)–(P4) pattern-consistency
组合枚举数值层（σ₀ 显式化＋轨道-稳定子精确计数；D95 候选①／D96 裁决 1 落地；
D92 裁决 2(δ) 预留插入点自此供数）。

裸 python3 运行（mpmath 经 l4_orbit 间接依赖；CWD 无关——路径全部从
__file__ 解析，沿 l4_orbit.py 先例）：

    python3 numerics/bounds/r22_pattern_numeric.py           # 主链 + results/
    python3 numerics/bounds/r22_pattern_numeric.py --out P   # 门重算用
    python3 thomson-n9/numerics/bounds/r22_pattern_numeric.py
        # ↑ CWD＝campaign 根的等价路由（同一文件，__file__ 解析不变）

【七面数学内容（对应任务书 F1–F6＋F7 归门）】
  F1 枚举重建：importlib 复用 l4_orbit.py（l4_orbit_gate 同源先例）跑
     compute_context(50)＋build_tables＋run_scout＋verify_coloring 全枚举——
     scout==30240、exact accepted==30240、distinct==30240。
  F2 桥面：ttp_reference_coloring()（构造性多项式恒等证书）vs 算术分类
     nodeOfN 双实现对账（import r15_b1_data.nodeOfN_rule＋本文件独立移植
     第二实现）——36/36 零 mismatch（三方两两）。
  F3 自同构群面：全 S₉ 扫描 Aut(ttp_ref)（σ 满足
     ttp_ref[(min(σi,σj),max(σi,σj)) 色]==nodeOfN(i,j) ∀36 对）恰 12 元；
     生成元 g₁=[1,2,0,4,5,3,7,8,6]（=(012)(345)(678)）、k=[1,0,2,4,3,5,6,8,7]
     （=(01)(34)(78)）、h=[3,4,5,0,1,2,6,7,8]（=(03)(14)(25)）张成==全群；
     阶分布（lex 扫描序）[1,2,2,3,3,2,2,2,2,6,6,2]（≅D₃×C₂——D3h 型 12 阶，
     l4_orbit.json orbitBalance erratum『D12 勘误』的群论面）。
  F4 轨道-稳定子面：orbit{σ·ttp_ref:σ∈S₉} 去重==30240==存档 labeledTotal==
     F1 幸存计数，且 orbit 与幸存集全集逐位集合相等（9! 全扫描、禁采样）；
     9!/30240==12==|Stab| 精确。
  F5 σ₀ 实例化面（pattern_ident_lift 桥插入点数据层——TableB5Chain.lean
     281–288 PatternCons def＋:313 pattern_ident_lift 定理的 σ₀ 显式实例化
     数据）：存档 canonical rep（l4_orbit.json survivorSet.classes[0].
     representative；元组 index k↔第 k 个 (i,j) i<j lex 对）恰 12 个
     σ-见证满足 rep[σ(i),σ(j)]==nodeOfN(i,j) ∀36 对；lex-min
     σ₀==[0,5,6,4,2,1,7,3,8] 显式记录为 feed contract。
  F6 孤立面：本 json artifact_class=='audit'、provenance.read_only==true、
     endgame.json sha256 冻结锚、不入 endgame.json/citedCertificates/12 分区、
     不作 endgame_chain.py 输入（路由禁令声明面；活体 grep 归门 G0）。
  F7 负对照 ≥2（NC-a/NC-b/NC-c）：归验收门 r22_pattern_gate.py（G0–G3＋NC）。

【诚实边界】
  · 本件为审计件（artifact_class='audit'）：零求解零 SDP 零 Lean 面新增；
    数值层系数值面不构成严格增量（D96 裁决 3，R9D/R20/R21A 先例）。
  · 幸存集/轨道全集不入 json（30240×36 体积考虑）：json 存计数＋sha256
    指纹；全集逐位集合相等由门 G2 活体全扫描执行（禁采样口径不变）。
  · σ₀ 与 12 见证是「rep 与 nodeOfN 算术分类的对齐置换」数据面：PatternCons
    （Lean 条件形，对 hT 全称量化）的 Y 侧几何前提（Gram 节点管）仍由
    l4_orbit (P1)–(P4)／L6 供给，本件只交付 σ₀/计数/指纹数据层。

输出 JSON 确定性（sort_keys＋indent、无时间戳/code_version、无随机序；
seed 20261022 仅声明——流程本身无随机性，l4_orbit.py 先例）⇒ 幂等重跑
逐位一致。
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import itertools
import json
import random
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent          # .../thomson-n9/numerics/bounds
REPO = HERE.parents[1]                          # .../thomson-n9
RESULTS = HERE / "results"
L4_ARCHIVE = RESULTS / "l4_orbit.json"
ENDGAME = RESULTS / "endgame.json"
OUT_DEFAULT = RESULTS / "r22_pattern_numeric.json"

SEED = 20261022
DPS = 50
ANCHOR_ENDGAME_SHA256 = ("86863a09bf84e950e85fc5f902bc2b4046a87f"
                         "06703bd782e5148fc119afd69f")

PAIRS = [(i, j) for i in range(9) for j in range(i + 1, 9)]     # lex 对
PIDX = {e: k for k, e in enumerate(PAIRS)}                       # 对→元组 index
FACT9 = 362880

GEN_G1 = (1, 2, 0, 4, 5, 3, 7, 8, 6)    # (012)(345)(678)
GEN_K = (1, 0, 2, 4, 3, 5, 6, 8, 7)     # (01)(34)(78)
GEN_H = (3, 4, 5, 0, 1, 2, 6, 7, 8)     # (03)(14)(25)
ANCHOR_ORDER_DIST_LEX = [1, 2, 2, 3, 3, 2, 2, 2, 2, 6, 6, 2]
ANCHOR_SIGMA0 = [0, 5, 6, 4, 2, 1, 7, 3, 8]


def log(msg: str) -> None:
    print(msg, flush=True)


def sha256_file(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def tuple_set_sha256(tuples) -> str:
    """确定性指纹：sorted 元组列表逐行渲染后 sha256。"""
    h = hashlib.sha256()
    for t in sorted(tuples):
        h.update(",".join(str(v) for v in t).encode())
        h.update(b"\n")
    return h.hexdigest()


# ============================================================ 群论纯函数（门同源调用／NC 注入点）

def compose(s, t):
    """(s∘t)(i) = s(t(i))——one-line 组合。"""
    return tuple(s[t[i]] for i in range(9))


def phi(sigma, tup):
    """拉回作用 (σ·C)[i,j] = C[σ(i),σ(j)]，36 元组 lex 对约定。"""
    return tuple(tup[PIDX[(min(sigma[i], sigma[j]), max(sigma[i], sigma[j]))]]
                 for (i, j) in PAIRS)


def perm_order(sigma):
    e = tuple(range(9))
    cur = e
    for n in range(1, FACT9 + 1):
        cur = compose(sigma, cur)
        if cur == e:
            return n
    raise AssertionError("perm_order: not finite")


def cycles_str(sigma):
    """轮换分解记法（如 (012)(345)(678)）。"""
    seen = [False] * 9
    parts = []
    for i in range(9):
        if seen[i]:
            continue
        orb = []
        j = i
        while not seen[j]:
            seen[j] = True
            orb.append(j)
            j = sigma[j]
        if len(orb) > 1:
            parts.append("(" + "".join(str(v) for v in orb) + ")")
    return "".join(parts) if parts else "id"


def span(gens):
    """⟨gens⟩ 闭包（双向乘法，确定性迭代）。"""
    e = tuple(range(9))
    S = {e}
    frontier = True
    while frontier:
        frontier = False
        for g in gens:
            for x in list(S):
                for c in (compose(g, x), compose(x, g)):
                    if c not in S:
                        S.add(c)
                        frontier = True
    return S


def node_of_n_port(i: int, j: int) -> int:
    """算术分类 nodeOfN 独立移植（本文件第二实现；与 r15_b1_data.nodeOfN_rule
    对账）。规则面：同 3 行块 → 帽行块(2) ν₃ / 棱行块 ν₅；帽-棱定向残差
    (帽位−棱位) mod 3 ==1 → ν₂ 否则 ν₆；异棱行块同方位 ν₄、错位 ν₁。"""
    a, b = min(i, j), max(i, j)
    la, lb = a // 3, b // 3
    if la == lb:
        return 2 if la == 2 else 4
    if la == 2:
        return 1 if (a % 3 + 3 - b % 3) % 3 == 1 else 5
    if lb == 2:
        return 1 if (b % 3 + 3 - a % 3) % 3 == 1 else 5
    return 3 if a % 3 == b % 3 else 0


def node_tuple_of(fn) -> tuple:
    return tuple(fn(i, j) for (i, j) in PAIRS)


def aut_scan(ttp_tuple, node_tuple):
    """全 S₉ 扫描 Aut(ttp_ref)：φ_σ(ttp) == nodeOfN tuple 的 σ（lex 序）。"""
    out = []
    for sigma in itertools.permutations(range(9)):
        if phi(sigma, ttp_tuple) == node_tuple:
            out.append(sigma)
    return out


def witness_scan(rep, node_tuple):
    """rep 的 σ-见证全扫描：rep[σ(i),σ(j)]==nodeOfN(i,j) ∀36 对（lex 序）。"""
    out = []
    for sigma in itertools.permutations(range(9)):
        if phi(sigma, rep) == node_tuple:
            out.append(sigma)
    return out


def orbit_set(ttp_tuple):
    """{σ·ttp_ref : σ∈S₉} 全扫描去重（禁采样）。"""
    return {phi(sigma, ttp_tuple) for sigma in itertools.permutations(range(9))}


def orbit_stab_consistency(orbit, survivors, archived_labeled_total) -> bool:
    """F4 判据（纯函数——NC 注入点）：orbit==幸存集全集逐位集合相等，
    |orbit|==30240==存档 labeledTotal，9!/|orbit|==12。"""
    orbit, survivors = set(orbit), set(survivors)
    return (orbit == survivors
            and len(orbit) == len(survivors) == archived_labeled_total == 30240
            and FACT9 // len(orbit) == 12)


def aut_consistency(aut, gens) -> bool:
    """F3 判据（纯函数——NC 注入点）：恰 12 元、生成元张成==全群、
    阶分布 lex 扫描序==锚、阶重集=={1:1, 2:7, 3:2, 6:2}（D₃×C₂ 型）。"""
    if len(aut) != 12:
        return False
    if span(gens) != set(aut):
        return False
    if [perm_order(s) for s in aut] != ANCHOR_ORDER_DIST_LEX:
        return False
    mult = {}
    for s in aut:
        mult[perm_order(s)] = mult.get(perm_order(s), 0) + 1
    return mult == {1: 1, 2: 7, 3: 2, 6: 2}


# ============================================================ 主流程

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=str(OUT_DEFAULT))
    args = ap.parse_args()
    random.seed(SEED)                     # 确定性声明（流程本身无随机性）
    t_start = time.time()

    l4 = load_module("l4_orbit", HERE / "l4_orbit.py")
    r15 = load_module("r15_b1_data", HERE / "r15_b1_data.py")

    # ---------- 输入锚（只读）
    endgame_sha = sha256_file(ENDGAME)
    if endgame_sha != ANCHOR_ENDGAME_SHA256:
        log(f"[FAIL] endgame.json sha256 漂移: {endgame_sha}")
        return 1
    l4_json = json.loads(L4_ARCHIVE.read_text())
    l4_sha = sha256_file(L4_ARCHIVE)

    # ---------- F1 枚举重建（importlib 复用 l4_orbit.py，全枚举）
    t0 = time.time()
    ctx = l4.compute_context(DPS)
    NU = l4.nu_float(ctx["zmid"])
    ok3, ok4, _, _ = l4.build_tables(NU)
    sols = l4.run_scout(ok3, ok4)
    t_scout = time.time() - t0
    n_acc = 0
    n_rej = 0
    n_und = 0
    survivors = []
    for s in sols:
        verdict, _ = l4.verify_coloring(l4.coloring_from_tuple(s),
                                        ctx["tri_dec"], ctx["quad_dec"])
        if verdict == "accepted":
            n_acc += 1
            survivors.append(s)
        elif verdict == "rejected":
            n_rej += 1
        else:
            n_und += 1
    distinct = len(set(survivors))
    log(f"[F1] scout={len(sols)} accepted={n_acc} distinct={distinct} "
        f"rejected={n_rej} undecided={n_und} ({t_scout:.1f}s)")
    if not (len(sols) == n_acc == distinct == 30240):
        log(f"[FAIL] F1 与任务书锚不符: scout={len(sols)} accepted={n_acc} "
            f"distinct={distinct}（锚 30240/30240/30240）——如实报不硬凑")
        return 1
    if n_rej or n_und:
        log(f"[FAIL] F1 精确层出现 rejected/undecided: {n_rej}/{n_und}")
        return 1
    archived_total = l4_json["survivorSet"]["labeledTotal"]
    if archived_total != 30240 or len(sols) != archived_total:
        log(f"[FAIL] F1 与存档 labeledTotal 不符: {len(sols)} vs {archived_total}")
        return 1

    # ---------- F2 桥面（构造证书 vs 算术分类双实现）
    ttp_ref, realiz_checks = l4.ttp_reference_coloring()
    ttp_tuple = tuple(ttp_ref[e] for e in PAIRS)
    rule_tuple = node_tuple_of(r15.nodeOfN_rule)          # 实现①：r15 import
    port_tuple = node_tuple_of(node_of_n_port)            # 实现②：独立移植
    mis_cert_rule = sum(1 for (i, j), k in ttp_ref.items() if r15.nodeOfN_rule(i, j) != k)
    mis_cert_port = sum(1 for k in range(36) if ttp_tuple[k] != port_tuple[k])
    mis_rule_port = sum(1 for k in range(36) if rule_tuple[k] != port_tuple[k])
    log(f"[F2] certificate_vs_ruleImport={mis_cert_rule} "
        f"certificate_vs_independentPort={mis_cert_port} "
        f"ruleImport_vs_independentPort={mis_rule_port}（pairsChecked=36）")
    if mis_cert_rule or mis_cert_port or mis_rule_port:
        log("[FAIL] F2 桥面出现 mismatch——如实报不硬凑")
        return 1

    # ---------- F3 自同构群面（全 S₉ 扫描）
    t0 = time.time()
    aut = aut_scan(ttp_tuple, rule_tuple)
    t_aut = time.time() - t0
    gens = [GEN_G1, GEN_K, GEN_H]
    ok_aut = aut_consistency(aut, gens)
    order_dist_lex = [perm_order(s) for s in aut]
    order_mult = {}
    for s in aut:
        order_mult[perm_order(s)] = order_mult.get(perm_order(s), 0) + 1
    log(f"[F3] |Aut|={len(aut)} span==group={span(gens) == set(aut)} "
        f"orders(lex)={order_dist_lex} ({t_aut:.1f}s)")
    if not ok_aut:
        log("[FAIL] F3 与任务书锚不符（|Aut|==12／生成元张成／阶分布）——"
            "如实报不硬凑")
        return 1

    # ---------- F4 轨道-稳定子面（9! 全扫描，禁采样）
    t0 = time.time()
    orbit = orbit_set(ttp_tuple)
    t_orb = time.time() - t0
    ok_orbit = orbit_stab_consistency(orbit, survivors, archived_total)
    log(f"[F4] |orbit|={len(orbit)} orbit==survivorSet={orbit == set(survivors)} "
        f"9!/|orbit|={FACT9 // len(orbit)} ({t_orb:.1f}s)")
    if not ok_orbit:
        log("[FAIL] F4 轨道-稳定子判据不符——如实报不硬凑")
        return 1

    # ---------- F5 σ₀ 实例化面（存档 canonical rep）
    rep = tuple(l4_json["survivorSet"]["classes"][0]["representative"])
    if rep not in set(survivors):
        log("[FAIL] F5 存档 canonical rep 不在重枚举幸存集中")
        return 1
    t0 = time.time()
    witnesses = witness_scan(rep, rule_tuple)
    t_wit = time.time() - t0
    sigma0 = min(witnesses)
    log(f"[F5] witnessCount={len(witnesses)} lex-min σ₀={list(sigma0)} "
        f"({t_wit:.1f}s)")
    if len(witnesses) != 12 or list(sigma0) != ANCHOR_SIGMA0:
        log(f"[FAIL] F5 与任务书锚不符: |wit|={len(witnesses)}（锚 12）、"
            f"σ₀={list(sigma0)}（锚 {ANCHOR_SIGMA0}）——如实报不硬凑")
        return 1
    # 见证集＝σ₀∘Aut 陪集一致性（结构自检；φ_σ∘φ_τ=φ_{τ∘σ} ⇒ W=σ₀·Stab）
    coset = {compose(sigma0, s) for s in aut}
    if coset != set(witnesses):
        log("[FAIL] F5 见证集 ≠ σ₀∘Aut 陪集")
        return 1

    # ---------- F6 孤立面＋汇总 JSON（确定性：sort_keys＋indent、无时间戳）
    out = {
        "artifact_class": "audit",
        "kind": "n9-r22-pattern-numeric",
        "schema": "thomson-n9/bounds/r22-pattern-numeric/1",
        "script": "bounds/r22_pattern_numeric.py",
        "script_sha256": sha256_file(HERE / "r22_pattern_numeric.py"),
        "seed": SEED,
        "heavy_solves": 0,
        "task": "r22a-pattern-numeric",
        "inputs": {
            "l4_orbit_json": {
                "path": "numerics/bounds/results/l4_orbit.json",
                "sha256": l4_sha,
                "inner_script_sha256": l4_json["script_sha256"],
                "role": "模块 import 源＋存档 labeledTotal/canonical rep 读取源（只读）",
            },
            "r15_b1_data_py": {
                "path": "numerics/bounds/r15_b1_data.py",
                "sha256": sha256_file(HERE / "r15_b1_data.py"),
                "role": "nodeOfN_rule import（Lean TableB1.lean:823 同构规则）",
            },
            "tube_json_sha256": sha256_file(RESULTS / "tube.json"),
            "local_min_json_sha256": sha256_file(RESULTS / "local_min.json"),
            "zBox": l4_json["inputs"]["zBox"],
        },
        "enumeration": {
            "facet": "F1 枚举重建（importlib 复用 l4_orbit.py：compute_context(50)"
                     "＋build_tables＋run_scout＋verify_coloring 全枚举；"
                     "l4_orbit_gate 同源先例）",
            "scout": len(sols),
            "exactAccepted": n_acc,
            "distinctAccepted": distinct,
            "rejected": n_rej,
            "undecided": n_und,
            "archivedLabeledTotal": archived_total,
            "dps": DPS,
            "survivorSetSha256": tuple_set_sha256(survivors),
            "fullSetInJson": False,
            "fullSetNote": "幸存集/轨道全集不入 json（体积）；全集逐位集合相等由"
                           "门 G2 活体 9! 全扫描执行（禁采样）",
        },
        "bridge": {
            "facet": "F2 桥面（构造性多项式恒等证书 vs 算术分类 nodeOfN 双实现"
                     "对账）",
            "certificate": "l4_orbit.ttp_reference_coloring()（族坐标(×2)∈"
                           "Q(√3)[z,r] Gram 逐项多项式恒等——l4_orbit (P5)）",
            "classifiers": {
                "ruleImport": "r15_b1_data.nodeOfN_rule（Lean nodeOfN 同构规则）",
                "independentPort": "r22_pattern_numeric.node_of_n_port（本文件"
                                   "独立移植第二实现）",
            },
            "pairsChecked": 36,
            "mismatches": {
                "certificate_vs_ruleImport": mis_cert_rule,
                "certificate_vs_independentPort": mis_cert_port,
                "ruleImport_vs_independentPort": mis_rule_port,
            },
            "realizationCertificateChecks": realiz_checks,
        },
        "automorphismGroup": {
            "facet": "F3 自同构群面（全 S₉ 扫描）",
            "definition": "Aut(ttp_ref) = {σ∈S₉ : ttp_ref[(min(σi,σj),"
                          "max(σi,σj))] == nodeOfN(i,j) ∀36 对}（F2 桥面下即"
                          "Stab(ttp_ref)）",
            "order": len(aut),
            "elements": [list(s) for s in aut],
            "generators": {
                "g1": {"perm": list(GEN_G1), "cycles": cycles_str(GEN_G1)},
                "k": {"perm": list(GEN_K), "cycles": cycles_str(GEN_K)},
                "h": {"perm": list(GEN_H), "cycles": cycles_str(GEN_H)},
            },
            "spanEqualsGroup": span(gens) == set(aut),
            "orderDistributionLexScan": order_dist_lex,
            "orderMultiset": {str(k): order_mult[k] for k in sorted(order_mult)},
            "structure": "≅ D₃×C₂（D3h 型 12 阶；l4_orbit.json orbitBalance "
                         "erratum『D12 勘误』的群论面）",
        },
        "orbitStabilizer": {
            "facet": "F4 轨道-稳定子面",
            "action": "(σ·C)[i,j] = C[σ(i),σ(j)]（拉回作用；36 元组 lex 对约定）",
            "orbitSize": len(orbit),
            "orbitEqualsSurvivorSet": orbit == set(survivors),
            "sampling": "none-full-set（9!=362880 全扫描，禁采样）",
            "archivedLabeledTotal": archived_total,
            "index": FACT9 // len(orbit),
            "stabOrder": len(aut),
            "identity": "9!/30240 == 12 == |Stab(ttp_ref)|（精确）",
            "orbitSha256": tuple_set_sha256(orbit),
        },
        "feedContract": {
            "facet": "F5 σ₀ 实例化面（pattern_ident_lift 桥插入点数据层）",
            "consumer": "formal/lean/ThomsonN9/TableB5Chain.lean:281–288 "
                        "PatternCons def ＋ :313 pattern_ident_lift 定理"
                        "（D92 裁决 2(δ) 预留插入点自此供数）",
            "patternConsStatement": "PatternCons Y z ρ σ₀ := ∀ hT i j (i≠j), "
                                    "|Y (σ₀ i) ⬝ᵥ Y (σ₀ j) − ν_{nodeOfN i j}| ≤ ρ"
                                    "——σ₀ 为 Y 侧实现与 nodeOfN 算术分类的对齐"
                                    "置换；Y 侧几何前提（Gram 节点管）由 "
                                    "l4_orbit (P1)–(P4)/L6 供给，本件只交付数据层",
            "canonicalRepSource": "l4_orbit.json survivorSet.classes[0]."
                                  "representative（single iso class 30240 元）",
            "pairIndexConvention": "元组 index k ↔ 第 k 个 (i,j) i<j lex 对"
                                   "（l4_orbit.coloring_from_tuple 同约定）",
            "witnessDefinition": "σ 满足 rep[σ(i),σ(j)]==nodeOfN(i,j) ∀36 对"
                                 "（即 φ_σ(rep)==nodeOfN tuple）",
            "canonicalRep": list(rep),
            "canonicalRepSha256": hashlib.sha256(
                ",".join(str(v) for v in rep).encode()).hexdigest(),
            "witnessCount": len(witnesses),
            "witnesses": [list(s) for s in witnesses],
            "sigma0LexMin": list(sigma0),
            "cosetConsistency": "witnesses == {σ₀∘s : s∈Aut}（Aut 左陪集；组合"
                                "约定 (s∘t)(i)=s(t(i))）",
        },
        "isolation": {
            "facet": "F6 孤立面",
            "endgameJsonSha256": endgame_sha,
            "endgameJsonSha256AnchorMatch": endgame_sha == ANCHOR_ENDGAME_SHA256,
            "read_only": True,
            "declaration": "本件不入 endgame.json/citedCertificates/12 分区、"
                           "不作 endgame_chain.py 输入（路由禁令；R11C–R21 先例）；"
                           "活体 grep＋endgame.json sha256 冻结锚归门 G0",
        },
        "gaps": [],
        "provenance": {
            "read_only": True,
            "commands": ["python3 numerics/bounds/r22_pattern_numeric.py"],
            "deps": ["mpmath（经 l4_orbit.py 间接：区间算术）＋其余 stdlib"],
            "determinism": "seed 20261022 仅声明——流程本身无随机性（l4_orbit.py"
                           " 先例）；DFS 固定迭代序、S₉ 扫描 itertools.lex 序；"
                           "输出 sort_keys+indent、无时间戳/code_version ⇒ "
                           "幂等重跑逐位一致",
            "frozen_anchors": {
                "endgame_json_sha256": ANCHOR_ENDGAME_SHA256,
            },
            "acceptanceGate": "numerics/bounds/r22_pattern_gate.py（G0–G3＋NC，"
                              "seed 20261022）",
        },
    }
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=1, sort_keys=True,
                                   ensure_ascii=False) + "\n")
    log(f"done: {out_path} (total {time.time() - t_start:.1f}s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
