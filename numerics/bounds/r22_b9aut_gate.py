#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r22_b9aut_gate.py — R22B 表 B 第九件（TTP 边染色自同构群 |Aut|=12 严格化）
验收门（G0–G5＋负对照 NC1/NC2/NC3；seed 20261022；编译型门——十一连
elaboration，单文件 ≤600s（D52-4/D64-5），外层 1200s 文档化例外沿 R18/R19/
R21B；CWD 无关——路径全部从 __file__ 解析）.

任务书口径（r22b-b9aut-lean，campaign dwfrun-f9904baf 第 17 轮续，D95 候选②
第九件选项启用、B2–B4/B3 维持另议不排 D61-1）：被验件＝
formal/lean/ThomsonN9/TableB1Aut.lean（namespace ThomsonN9.TableB1Aut；仅
import Mathlib＋ThomsonN9.TableB1——nodeOfN 所在 TableB1.lean:823；不 import
仓内其他解件、不被其 import——TableB5Chain 先例；不触 Solution.lean/scripts/
check.sh/lakefile/挑战文件/references）＋本门＋嵌套 CWD 包装器（D52-4 先例）＋
会话根包装器（D7/D8/D9 先例，仓外不入版本库）＋账本
results/r22_b9aut_ledger.json。零求解零 SDP 零 emitter（本件无数据发射器——
G2 纯 elaboration，R21B 的发射器重跑面不适用）。

检查面（对应任务书 G0–G5＋NC1/NC2/NC3）：
  G0 账本自锚：在场＋seed==20261022＋heavy_solves==0＋kind/task＋
     axiom_policy 恰三标准 set 相等＋theorem_count 与源 regex 重数一致＋
     自有件 sha256 严格锚＋endgame 冻结锚字符串。
  G1 所有权＋冻结面＋隔离面：git 双路由（porcelain＋diff HEAD --name-only）
     改动 ⊆ 自有件（＋R22B_G1_ALLOW_FOREIGN 自跑逐件放行〔默认关〕＋r22
     家族放行层——D90-4 同款）；表 B 十一件 Lean git diff 守卫（冻结十件＋
     本件）＋挑战件目录/＋references/ 零触碰＋四账本 sha256 冻结锚＋
     endgame.json==86863a09…69f；隔离面：r22_b9aut 不入 endgame.json/
     endgame_chain.py 文本＋chain-only 干跑五字段零漂移＋全集漂移叶 ⊆
     冻结 22 叶（新叶即 FAIL，处置归 D99）。
  G2 依赖序十一连 elaboration（TableB1Data→TableB1→TableB5Data→TableB5→
     TableB5Core→TableB5Trace→TableB5Polar→TableB5Uncond→TableB5ChainData→
     TableB5Chain→TableB1Aut），均 exit 0、输出无 error/sorry、墙钟 ≤600s/件。
  G3 公理直查活体：#print axioms 于 TableB1Aut 全部 theorem（regex 枚举，
     账本记精确数 21）——公理集 ⊆ {propext, Classical.choice, Quot.sound}，
     零 sorryAx/ofReduceBool/ofReduceNat/trustCompiler（D82-4 口径）。
  G4 语句锚：import 面恰两行（import Mathlib＋import ThomsonN9.TableB1）；
     接口形（ttpAutPred 行内 ∀ 形／ttpAut Set 形／DecidablePred 实例／
     Fintype 实例）＋12 行表全在（tblRow 逐行字面）＋逐元成员 tau_mem＋
     两两互异 head3_inj＋card_ge＋上界链牙（nodeOfN_two_caps／caps_third／
     third_cap_unique／not_cap_of_distinct／nu2_partner／inPartners／
     pin5_unique／partner_other_unique／sig_values／eq_tau_of_vals／upper）＋
     card_le＋头条 card_ttpAut_eq_12＝12＋轨道-稳定子锚（Nat.factorial 9、
     30240）＋mem_iff_in_table＋零 sorry＋零 ≥15 位数字字面量＋非交叠守卫
     （其余 ThomsonN9 件/根模块/lake 面/脚本零 TableB1Aut 引用）。
  G5 第二实现面（门内独立 Python，零仓 import 于被验件）：独立第四实现
     nodeOfN 几何位直分类 vs r15_b1_data.nodeOfN_rule（import）36/36 逐位
     对账（nodeOfN 相关锚 sanity）→Lean 源直读 12 行表→逐行双射性＋36 条件
     判定→全 S₉ 扫描（362880 全集，禁采样）Aut==12 行表逐位集合相等==r22
     _pattern_numeric.json automorphismGroup.elements 逐位→生成元 g₁/k/h
     张成==全群→阶分布（lex）[1,2,2,3,3,2,2,2,2,6,6,2]＋阶重集
     {1:1,2:7,3:2,6:2}≅D₃×C₂→head3 三元组两两相异→9!/12==30240==
     l4_orbit.json labeledTotal==r22_pattern F4 orbitSize、9!/30240==12==
     |Stab|。
  NC1 注入 sorry 必被 G3 拦：/tmp 副本把 tau_mem 证明改 sorry → 独立编译
     必现 sorry 警告＋公理必现 sorryAx（未篡原件 sanity＝G3 全过）。
  NC2 篡 nodeOfN 相关锚必拦：/tmp 门内端口副本把 ν₂ 残差规则 1→5（帽-棱
     伙伴面反转——现实作弊向）→ 与 r15_b1_data.nodeOfN_rule 36/36 对账必
     现 mismatch（有牙实证；未篡端口 sanity＝G5 对账零 mismatch）。
  NC3 篡 12 表一元必拦：解析表副本把第 1 行交换两元（保持双射性）→
     行 36 条件判定必 FAIL＋解析集≠全扫描 Aut（有牙实证；未篡表 sanity＝
     G5 全过）。

诚实边界：本门零求解零 SDP 零 emitter；endgame.json/四账本/l4_orbit.json/
tube.json 只读未动（sha256 锚＋干跑零漂移双面）；r22_b9aut 家族不入 12 分区
（隔离面）；|Aut|=12 为无条件组合命题（无 L6/pattern 类条件假设——条件性
诚实边界不存在，D97 可回滚点段口径）；4 层 Fin-decide 实例综合在本工具链
不可用，计数引理按 3 层 phrasing＋not_cap_of_distinct 符号提升（Lean 件内
留痕）。closed 终判与 L0/L3 blocker 均不动。

用法（CWD 无关）：
  python3 numerics/bounds/r22_b9aut_gate.py    # 全门（exit 0 = 过）
  python3 thomson-n9/numerics/bounds/r22_b9aut_gate.py
      # ↑ CWD＝campaign 根的验收命令（真实门直路由）；CWD＝仓库根时命中
      #   嵌套 CWD 包装器（thomson-n9/thomson-n9/…，D52-4 先例）
"""
from __future__ import annotations

import hashlib
import itertools
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
REPO = HERE.parents[1]                 # thomson-n9/
LEAN_DIR = REPO / "formal" / "lean"

SEED_GATE = 20261022                   # R22 各门统一 seed（D97 门 seed 序列）
ELAB_LIMIT_S = 600                     # G2 每文件 ≤10 min（D52-4/D64-5）
COMPILE_TIMEOUT_S = 620

AUT_REL = "formal/lean/ThomsonN9/TableB1Aut.lean"
GATE_REL = "numerics/bounds/r22_b9aut_gate.py"
WRAPPER_REL = "thomson-n9/numerics/bounds/r22_b9aut_gate.py"   # 嵌套 CWD 包装器
LEDGER_REL = "numerics/bounds/results/r22_b9aut_ledger.json"
DECISIONS_REL = "notes/decisions.md"
OWNED = {AUT_REL, GATE_REL, WRAPPER_REL, LEDGER_REL, DECISIONS_REL}

PARALLEL_FAMILY = [
    r"^formal/lean/ThomsonN9/TableB1Aut\.lean$",
    r"^numerics/bounds/r22[a-z0-9_]*(\.py|/)",
    r"^numerics/bounds/results/r22[a-z0-9_]*(\.json|/)",
    r"^thomson-n9/numerics/bounds/r22[a-z0-9_]*(\.py|/)",
    r"^notes/decisions\.md$",
    r"^notes/r22a-pattern-numeric\.md$",
    r"^notes/[a-z0-9-]+\.md$",
    r"^numerics/bounds/endgame_gate\.py$",
    r"^(GAP-REPORT|PROGRESS)\.md$",
]

# 只读冻结件（表 B 全家族——十件冻结＋本件 TableB1Aut：显式 git diff 守卫；
# 本件在 OWNED 集内，diff-vs-HEAD 于净树时为零）。
FROZEN_READONLY = (
    "formal/lean/ThomsonN9/TableB5.lean",
    "formal/lean/ThomsonN9/TableB5Data.lean",
    "formal/lean/ThomsonN9/TableB5Core.lean",
    "formal/lean/ThomsonN9/TableB5Trace.lean",
    "formal/lean/ThomsonN9/TableB5Polar.lean",
    "formal/lean/ThomsonN9/TableB5Uncond.lean",
    "formal/lean/ThomsonN9/TableB1.lean",
    "formal/lean/ThomsonN9/TableB1Data.lean",
    "formal/lean/ThomsonN9/TableB6.lean",
    "formal/lean/ThomsonN9/TableB6Data.lean",
    "formal/lean/ThomsonN9/TableB1Aut.lean",
)
FROZEN_DIRS = ("formal/lean/ComparatorChallenges", "references")
FROZEN_LEDGERS = {
    "numerics/bounds/results/m9_campaign.json":
        "583e5dd11356472b47e8d9e8fac7865ec434800c99919df31d247f30b260114a",
    "numerics/bounds/results/m10_campaign.json":
        "9f6cf91c3adf1e0908c2f41084e53380237ca58840f82bbdcd720c54421c23ed",
    "numerics/bounds/results/hermite_v2_campaign.json":
        "4ebcbedd1e8dc300ab9e6bc0e3b756c75b7f4cbe4fe00675719217f90ea41765",
    "numerics/bounds/results/typed_ladder.json":
        "78fc1102e6d864115204fae21959f3704841aa688b07a30a9567bbdca4683318",
}
ENDGAME_REL = "numerics/bounds/results/endgame.json"
ENDGAME_SHA256 = "86863a09bf84e950e85fc5f902bc2b4046a87f06703bd782e5148fc119afd69f"
L4_REL = "numerics/bounds/results/l4_orbit.json"
R22P_REL = "numerics/bounds/results/r22_pattern_numeric.json"

NONOVERLAY_FILES = ("ThomsonN9/Solution.lean", "ThomsonN9/TableA.lean",
                    "ThomsonN9/TableA1.lean", "ThomsonN9/TableA1Data.lean",
                    "ThomsonN9/TableA3.lean", "ThomsonN9/TableA4.lean",
                    "ThomsonN9/TableA6.lean", "ThomsonN9/M1Data.lean",
                    "ThomsonN9/TableB1.lean", "ThomsonN9/TableB1Data.lean",
                    "ThomsonN9/TableB5.lean", "ThomsonN9/TableB5Core.lean",
                    "ThomsonN9/TableB5Trace.lean", "ThomsonN9/TableB5Polar.lean",
                    "ThomsonN9/TableB5Uncond.lean", "ThomsonN9/TableB5Data.lean",
                    "ThomsonN9/TableB5Chain.lean",
                    "ThomsonN9/TableB5ChainData.lean",
                    "ThomsonN9/TableB6.lean", "ThomsonN9/TableB6Data.lean",
                    "ThomsonN9.lean", "lakefile.toml", "scripts/check.sh")

# 22 叶＝certReverify 17＋code_version/timestamp 2＋L1 quant 1＋engineV2 2
# （D84-4 口径；R20B/R21A/R21B 同表）。
FROZEN_DRIFT_LEAVES = frozenset({
    "/certReverify/all_pass", "/certReverify/cap_m0748_M9",
    "/certReverify/hp_reproduce", "/certReverify/l3_analytic_rerun",
    "/certReverify/l4_orbit_rerun", "/certReverify/l6_intube_rerun",
    "/certReverify/slab_sm19o20_m91o100", "/certReverify/slab_sm1_m99o100",
    "/certReverify/slab_sm91o100_m9o10", "/certReverify/slab_sm97o100_m19o20",
    "/certReverify/slab_sm99o100_m97o100", "/certReverify/status",
    "/certReverify/strip_m079-m765", "/certReverify/strip_m082-m079",
    "/certReverify/strip_m085-m082", "/certReverify/strip_m088-m085",
    "/certReverify/strip_m090-m088", "/code_version",
    "/endgameChain/components/1/quant", "/round8Inputs/engineV2/ledgers/7",
    "/round8Inputs/engineV2/note", "/timestamp",
})

TMP = Path("/tmp/r22_b9aut_gate")
OLEAN_REL = ".lake/build/lib/lean/ThomsonN9"

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN_AXIOMS = ("sorryAx", "ofReduceBool", "ofReduceNat", "trustCompiler")

# 编译序（G2 依赖序十一连——任务书口径〔TableB1Data…TableB1Aut〕）
COMPILE_ORDER = [
    ("ThomsonN9/TableB1Data.lean", "TableB1Data"),
    ("ThomsonN9/TableB1.lean", "TableB1"),
    ("ThomsonN9/TableB5Data.lean", "TableB5Data"),
    ("ThomsonN9/TableB5.lean", "TableB5"),
    ("ThomsonN9/TableB5Core.lean", "TableB5Core"),
    ("ThomsonN9/TableB5Trace.lean", "TableB5Trace"),
    ("ThomsonN9/TableB5Polar.lean", "TableB5Polar"),
    ("ThomsonN9/TableB5Uncond.lean", "TableB5Uncond"),
    ("ThomsonN9/TableB5ChainData.lean", "TableB5ChainData"),
    ("ThomsonN9/TableB5Chain.lean", "TableB5Chain"),
    ("ThomsonN9/TableB1Aut.lean", "TableB1Aut"),
]

# 设计师 12 行表锚（＝r22_pattern_numeric.json automorphismGroup.elements
# lex 序＝任务书 image-tuple [σ0,…,σ8] 表——G5 独立扫描对账的第三源）
ANCHOR_ROWS = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8],
    [0, 2, 1, 3, 5, 4, 8, 7, 6],
    [1, 0, 2, 4, 3, 5, 6, 8, 7],
    [1, 2, 0, 4, 5, 3, 7, 8, 6],
    [2, 0, 1, 5, 3, 4, 8, 6, 7],
    [2, 1, 0, 5, 4, 3, 7, 6, 8],
    [3, 4, 5, 0, 1, 2, 6, 7, 8],
    [3, 5, 4, 0, 2, 1, 8, 7, 6],
    [4, 3, 5, 1, 0, 2, 6, 8, 7],
    [4, 5, 3, 1, 2, 0, 7, 8, 6],
    [5, 3, 4, 2, 0, 1, 8, 6, 7],
    [5, 4, 3, 2, 1, 0, 7, 6, 8],
]
ANCHOR_GENS = {"g1": [1, 2, 0, 4, 5, 3, 7, 8, 6],
               "k": [1, 0, 2, 4, 3, 5, 6, 8, 7],
               "h": [3, 4, 5, 0, 1, 2, 6, 7, 8]}
ANCHOR_ORDER_DIST_LEX = [1, 2, 2, 3, 3, 2, 2, 2, 2, 6, 6, 2]
ANCHOR_ORDER_MULTISET = {"1": 1, "2": 7, "3": 2, "6": 2}


class GateFail(Exception):
    pass


def fail(msg: str) -> None:
    raise GateFail(msg)


def okmsg(msg: str) -> None:
    print(f"[gate][OK ] {msg}", flush=True)


def sha256_of(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def load_json(p: Path):
    return json.loads(p.read_text())


def gate_env() -> dict:
    elan = Path.home() / ".elan" / "bin"
    env = dict(os.environ)
    env["PATH"] = str(elan) + os.pathsep + env.get("PATH", "")
    return env


def run(cmd, cwd: Path, timeout_s: int = 605):
    return subprocess.run(cmd, cwd=str(cwd), env=gate_env(), capture_output=True,
                          text=True, timeout=timeout_s)


# ============================================================ 独立第四实现
def gate_node_of_n(i: int, j: int) -> int:
    """门内独立第四实现 nodeOfN（与 TableB1.lean:823 同构；r15 import／
    r22_pattern 主件移植／r22_pattern_gate 几何直分类之外的新字面）：
    按顶点几何位（上三角 z=+z*／下三角 z=−z*／帽 z=0，方位角 k）直接分类。
    ν 序（升序）：ν₁=−(1+z²)/2、ν₂=−ρ、ν₃=−1/2、ν₄=1−2z²、ν₅=(3z²−1)/2、
    ν₆=ρ/2；帽-棱残差 (cap−prism)%3≡1 → ν₂(1)、≡0,2 → ν₆(5)。"""
    if i == j:
        return 9
    la, lb = i // 3, j // 3          # 0 上三角 / 1 下三角 / 2 帽
    if la == lb == 2:
        return 2                     # 帽-帽 → ν₃
    if la < 2 and lb < 2:
        if la == lb:
            return 4                 # 同层三角内部 → ν₅
        return 3 if i % 3 == j % 3 else 0   # 竖棱 ν₄ / 上下错位 ν₁
    cap, prism = (i, j) if la == 2 else (j, i)
    d = (cap % 3 - prism % 3) % 3
    return 1 if d == 1 else 5        # 帽-棱：残差 1 → ν₂；0,2 → ν₆


def row_satisfies(node_of_n, row) -> bool:
    """image-tuple row 的 36 条件判定（i<j 无序对；nodeOfN 对称故与有序 72
    条件等价——Lean 件的有序形式由 tau_mem 逐元 decide 承载）。"""
    return all(node_of_n(row[i], row[j]) == node_of_n(i, j)
               for i in range(9) for j in range(9) if i < j)


def compose(t, s):
    """image-tuple 合成：(t∘s)(i) = t(s(i))。"""
    return tuple(t[i] for i in s)


def perm_order(t):
    ident = tuple(range(9))
    n, c = 1, tuple(t)
    while c != ident:
        c = compose(c, t)
        n += 1
    return n


def parse_lean_rows(src: str):
    """从 Lean 源 tblRow 定义块直读 12 行（G5 第二实现的『表』侧——
    非独立重算，而是对被验件字面的逐位解析）。"""
    m = re.search(r"def tblRow[\s\S]*?\| _ =>", src)
    if not m:
        fail("G5 预置失败：Lean 源缺 tblRow 定义块")
    block = m.group(0)
    rows = []
    for mm in re.finditer(r"\| (\d+) => !\[(\d(?:, \d)*)\]", block):
        rows.append((int(mm.group(1)), [int(v) for v in mm.group(2).split(", ")]))
    if len(rows) != 12:
        fail(f"G5 预置失败：tblRow 块仅解析出 {len(rows)} 行（应 12）")
    if [k for k, _ in rows] != list(range(12)):
        fail("G5 预置失败：tblRow 行号非 0..11 序")
    return [r for _, r in rows]


# ============================================================ G0
def gate0_ledger():
    led_path = REPO / LEDGER_REL
    if not led_path.is_file():
        fail(f"G0 账本不在场：{LEDGER_REL}")
    led = load_json(led_path)
    if led.get("seed") != SEED_GATE:
        fail(f"G0 seed 失配：{led.get('seed')!r} != {SEED_GATE}")
    if led.get("heavy_solves") != 0:
        fail(f"G0 heavy_solves 失配：{led.get('heavy_solves')!r} != 0")
    if led.get("kind") != "n9-r22-b9aut-ledger":
        fail(f"G0 kind 失配：{led.get('kind')!r}")
    if led.get("task") != "r22b-b9aut-lean":
        fail(f"G0 task 失配：{led.get('task')!r}")
    files = led.get("files", {})
    for rel in OWNED:
        if rel not in files:
            fail(f"G0 账本 files 缺自有件：{rel}")
    if set(led.get("axiom_policy", [])) != ALLOWED_AXIOMS:
        fail(f"G0 axiom_policy 失配（应恰三标准 set 相等）：{led.get('axiom_policy')!r}")
    data = led.get("data", {})
    if data.get("heavy_solves") != 0:
        fail("G0 data.heavy_solves 失配")
    n_theorems = len(re.findall(r"^theorem (\w+)",
                                (REPO / AUT_REL).read_text(), re.M))
    if data.get("theorem_count") != n_theorems:
        fail(f"G0 theorem_count 失配：账本 {data.get('theorem_count')} != "
             f"regex 重数 {n_theorems}")
    for rel in (AUT_REL, GATE_REL, WRAPPER_REL):
        want = files.get(rel)
        if want in (None, "self"):
            fail(f"G0 files 锚缺失：{rel}")
        if sha256_of(REPO / rel) != want:
            fail(f"G0 新件 sha256 漂移：{rel}")
    fa = led.get("frozen_readonly_anchored", {})
    if fa.get("endgame_json_sha256") != ENDGAME_SHA256:
        fail("G0 冻结锚 endgame_json_sha256 失配")
    okmsg(f"G0 账本自锚（seed={SEED_GATE}，heavy_solves=0，kind/task，"
          f"axiom_policy 恰三标准 set 相等，theorem_count==regex 重数 "
          f"{n_theorems}，自有件 sha256 严格锚，endgame 冻结锚字符串在账）")
    return led


# ============================================================ G1
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


def gate1_ownership() -> None:
    allow_foreign = {q.strip() for q in
                     os.environ.get("R22B_G1_ALLOW_FOREIGN", "").split(",")
                     if q.strip()}
    for cmd in (["git", "status", "--porcelain"],
                ["git", "diff", "HEAD", "--name-only"]):
        r = run(["git", *cmd[1:]], REPO)
        if r.returncode != 0:
            fail(f"G1 {cmd[1]} 失败：{r.stderr.strip()[:300]}")
        paths = (porcelain_paths(r.stdout) if "--porcelain" in cmd else
                 [ln.strip().strip('"') for ln in r.stdout.splitlines()
                  if ln.strip()])
        for p in paths:
            if p in OWNED:
                continue
            if p in allow_foreign:
                print(f"[gate][G1][自跑放行] 并行在途件：{p}")
                continue
            if any(re.match(pat, p) for pat in PARALLEL_FAMILY):
                print(f"[gate][G1][r22 家族放行] 在途件（D90-4 pattern）：{p}")
                continue
            fail(f"G1 树上出现非本任务自有件（{cmd[1]}）：{p!r}"
                 f"（自有集={sorted(OWNED)}；r22 家族放行层未覆盖）")
    r = run(["git", "diff", "HEAD", "--"] + list(FROZEN_READONLY), REPO)
    if r.stdout.strip():
        fail("G1 表 B 十一件 Lean 冻结只读面被触碰（git diff 非空）")
    for d in FROZEN_DIRS:
        r = run(["git", "status", "--porcelain", "--", d + "/"], REPO)
        if r.stdout.strip():
            fail(f"G1 冻结目录被触碰：{d}")
    for rel, want in FROZEN_LEDGERS.items():
        h = sha256_of(REPO / rel)
        if h != want:
            fail(f"G1 四账本 sha256 冻结锚失配：{rel}（{h[:16]}… != {want[:16]}…）")
    if sha256_of(REPO / ENDGAME_REL) != ENDGAME_SHA256:
        fail("G1 endgame.json sha256 != 86863a09…69f")
    okmsg("G1 所有权＋冻结面：git 双路由改动 ⊆ 自有件＋r22 家族放行层；"
          "表 B 十一件 Lean git diff 守卫＋挑战件/ references/ 零触碰＋"
          "四账本 sha256 冻结锚＋endgame.json==86863a09…69f 全过")


def _leaf_diff(x, y, path: str) -> list:
    out = []
    if isinstance(x, dict) and isinstance(y, dict):
        for k in sorted(set(x) | set(y)):
            if k not in x or k not in y:
                out.append(f"{path}/{k}")
            else:
                out += _leaf_diff(x[k], y[k], f"{path}/{k}")
    elif isinstance(x, list) and isinstance(y, list):
        for i in range(max(len(x), len(y))):
            if i >= len(x) or i >= len(y):
                out.append(f"{path}/{i}")
            else:
                out += _leaf_diff(x[i], y[i], f"{path}/{i}")
    elif x != y:
        out.append(path)
    return out


def gate1_isolation() -> None:
    """审计件隔离面：不入 12 分区、不作 chain 输入、干跑零漂移＋冻结 22 叶。"""
    tag = "r22_b9aut"
    if tag in (REPO / ENDGAME_REL).read_text():
        fail(f"G1 隔离面：{tag} 出现在 endgame.json 文本中（审计件非证书）")
    endgame_chain = REPO / "numerics" / "bounds" / "endgame_chain.py"
    if tag in endgame_chain.read_text():
        fail(f"G1 隔离面：{tag} 出现在 endgame_chain.py 文本中（禁止输入）")
    out = TMP / "chain_dry.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    r = run([sys.executable, "numerics/bounds/endgame_chain.py",
             "--out", str(out)], REPO)
    if r.returncode != 0:
        fail(f"G1 chain-only 干跑 exit {r.returncode}")
    arch = load_json(REPO / ENDGAME_REL)
    dry = load_json(out)
    if dry["endgameChain"]["closed"] is not False or \
            arch["endgameChain"]["closed"] is not False:
        fail("G1 干跑 closed 漂移（应 False）")
    for k in ("value", "float", "margin_vs_E_star"):
        if arch["assembledRecord"][k] != dry["assembledRecord"][k]:
            fail(f"G1 干跑 assembledRecord.{k} 漂移")
    if len(dry["endgameChain"]["components"]) != 8:
        fail("G1 干跑组件集非 L0–L7")
    for a, b in zip(arch["endgameChain"]["components"],
                    dry["endgameChain"]["components"]):
        if a["id"] != b["id"] or a.get("rigorous") != b.get("rigorous"):
            fail(f"G1 干跑组件 {a.get('id')} rigorous 漂移")
    if dry["endgameChain"]["blocking"] != ["L0", "L3"]:
        fail("G1 干跑 blocking != [L0, L3]")
    if arch["spliceMapVerdict"]["verdict"] != dry["spliceMapVerdict"]["verdict"] \
            or arch["spliceMapVerdict"].get("assembled_equal_R7") != \
            dry["spliceMapVerdict"].get("assembled_equal_R7"):
        fail("G1 干跑 spliceMapVerdict 漂移")
    drifted = set(_leaf_diff(arch, dry, ""))
    fresh = drifted - FROZEN_DRIFT_LEAVES
    if fresh:
        fail(f"G1 冻结漂移分布出现新叶（{len(fresh)} 处——审计件若被误接为 "
             f"chain 输入即在此暴露；处置归 D99）：{sorted(fresh)[:6]}")
    missing = FROZEN_DRIFT_LEAVES - drifted
    if missing:
        fail(f"G1 漂移分布叶缺失（{len(missing)} 处——环境面变化，如实拦）："
             f"{sorted(missing)[:4]}")
    okmsg("G1 隔离面：r22_b9aut 不入 endgame.json/endgame_chain.py 文本；"
          "chain-only 干跑五字段逐位零漂移＋全集漂移恰为冻结 22 叶"
          "（certReverify 17＋code_version/timestamp 2＋L1 quant 1＋engineV2 2）")


# ============================================================ G2
def compile_lean(rel_source: str, olean_name: str) -> float:
    t0 = time.time()
    olean = LEAN_DIR / OLEAN_REL / f"{olean_name}.olean"
    olean.parent.mkdir(parents=True, exist_ok=True)
    try:
        r = run(["lake", "env", "lean", "-o", f"{OLEAN_REL}/{olean_name}.olean",
                 rel_source], LEAN_DIR, timeout_s=COMPILE_TIMEOUT_S)
    except subprocess.TimeoutExpired:
        fail(f"G2 elaboration 超时（>{COMPILE_TIMEOUT_S}s，{rel_source}）")
    wall = time.time() - t0
    if r.returncode != 0:
        fail(f"G2 elaboration 失败（exit {r.returncode}，{rel_source}）：\n"
             f"{r.stdout[-800:]}\n{r.stderr[-800:]}")
    out = r.stdout + r.stderr
    if "error" in out or "sorry" in out:
        fail(f"G2 elaboration 输出含 error/sorry（{rel_source}）：\n{out[-800:]}")
    if wall > ELAB_LIMIT_S:
        fail(f"G2 elaboration 超限：{rel_source} 墙钟 {wall:.1f}s > {ELAB_LIMIT_S}s")
    return wall


def gate2_elaborate() -> dict:
    walls = {}
    for src, ol in COMPILE_ORDER:
        walls[ol] = round(compile_lean(src, ol), 1)
        okmsg(f"G2 elaboration：{src} exit 0 无 error/sorry"
              f"（{walls[ol]}s ≤ {ELAB_LIMIT_S}s）")
    okmsg("G2 依赖序十一连完毕（TableB1Data→TableB1→TableB5Data→TableB5→"
          "Core→Trace→Polar→Uncond→ChainData→Chain→TableB1Aut），olen 落 "
          ".lake/build 供 G3/NC 复用")
    return walls


# ============================================================ G3
def parse_axiom_lines(out: str) -> dict:
    ax = {}
    for m in re.finditer(r"'([^']+)'\s+does not depend on any axioms", out):
        ax[m.group(1)] = set()
    for m in re.finditer(r"'([^']+)'\s+depends on axioms:\s*\[([^\]]*)\]", out):
        ax[m.group(1)] = ({a.strip() for a in m.group(2).split(",")}
                          if m.group(2).strip() else set())
    return ax


def theorem_names(src: str) -> list:
    return re.findall(r"^theorem (\w+)", src, re.M)


def check_axioms(ax: dict, full_names: list, ctx: str) -> None:
    for th in full_names:
        if th not in ax:
            fail(f"{ctx}：公理输出缺定理 {th}（解析到 {len(ax)}/{len(full_names)}）")
        bad = ax[th] - ALLOWED_AXIOMS
        if bad:
            fail(f"{ctx}：定理 {th} 依赖非标准公理 {sorted(bad)}")
        for f in FORBIDDEN_AXIOMS:
            if f in ax[th]:
                fail(f"{ctx}：定理 {th} 依赖 {f}")
    okmsg(f"{ctx}：{len(full_names)} 定理公理集全 ⊆ {{propext, Classical.choice, "
          "Quot.sound}} 零 sorryAx")


def gate3_axioms(led: dict) -> None:
    src = (LEAN_DIR / "ThomsonN9" / "TableB1Aut.lean").read_text()
    names = theorem_names(src)
    if led["data"]["theorem_count"] != len(names):
        fail(f"G3 theorem_count 失配：账本 {led['data']['theorem_count']} != "
             f"regex 重数 {len(names)}")
    d = LEAN_DIR / OLEAN_REL
    d.mkdir(parents=True, exist_ok=True)
    axfile = d / "AxCheckTableB1Aut.lean"
    lines = ["import ThomsonN9.TableB1Aut"]
    for th in names:
        lines.append(f"#print axioms ThomsonN9.TableB1Aut.{th}")
    axfile.write_text("\n".join(lines) + "\n")
    r = run(["lake", "env", "lean", str(axfile)], LEAN_DIR,
            timeout_s=COMPILE_TIMEOUT_S)
    if r.returncode != 0:
        fail(f"G3 公理检查编译失败：\n{r.stdout[-600:]}\n{r.stderr[-600:]}")
    ax = parse_axiom_lines(r.stdout + r.stderr)
    check_axioms(ax, [f"ThomsonN9.TableB1Aut.{t}" for t in names], "G3 TableB1Aut")
    okmsg(f"G3 公理直查活体：TableB1Aut {len(names)} 定理全过（恰三标准；"
          "零 sorryAx——D82-4 口径）")


# ============================================================ G4
def gate4_statements() -> None:
    src = (LEAN_DIR / "ThomsonN9" / "TableB1Aut.lean").read_text()
    imports = re.findall(r"^import\s+\S+", src, re.M)
    if imports != ["import Mathlib", "import ThomsonN9.TableB1"]:
        fail(f"G4 import 面失配（应恰两行）：{imports}")
    anchors = [
        # 接口形（(i) 载体）
        (r"def ttpAutPred \(σ : Equiv\.Perm \(Fin 9\)\) : Prop :=",
         "成员条件 def（行内 ∀ 形）"),
        (r"∀ i j : Fin 9, i ≠ j → nodeOfN \(σ i\)\.val \(σ j\)\.val = nodeOfN i\.val j\.val",
         "36 条件有限合取行内形"),
        (r"def ttpAut : Set \(Equiv\.Perm \(Fin 9\)\) := \{σ \| ttpAutPred σ\}",
         "Set 形式"),
        (r"instance ttpAutPredDecidable \(σ : Equiv\.Perm \(Fin 9\)\) : Decidable \(ttpAutPred σ\)",
         "DecidablePred 实例"),
        (r"instance ttpAutFintype :\n    Fintype \{σ : Equiv\.Perm \(Fin 9\) // ∀ i j : Fin 9, i ≠ j →",
         "Fintype 实例（行内形式声明）"),
        # (ii) 12 行表＋逐元成员＋两两互异＋下界
        (r"def tblRow \(n : ℕ\) : Fin 9 → Fin 9 :=", "12 行表 def"),
        (r"\| 0 => !\[0, 1, 2, 3, 4, 5, 6, 7, 8\]", "表行 0"),
        (r"\| 1 => !\[0, 2, 1, 3, 5, 4, 8, 7, 6\]", "表行 1"),
        (r"\| 2 => !\[1, 0, 2, 4, 3, 5, 6, 8, 7\]", "表行 2"),
        (r"\| 3 => !\[1, 2, 0, 4, 5, 3, 7, 8, 6\]", "表行 3"),
        (r"\| 4 => !\[2, 0, 1, 5, 3, 4, 8, 6, 7\]", "表行 4"),
        (r"\| 5 => !\[2, 1, 0, 5, 4, 3, 7, 6, 8\]", "表行 5"),
        (r"\| 6 => !\[3, 4, 5, 0, 1, 2, 6, 7, 8\]", "表行 6"),
        (r"\| 7 => !\[3, 5, 4, 0, 2, 1, 8, 7, 6\]", "表行 7"),
        (r"\| 8 => !\[4, 3, 5, 1, 0, 2, 6, 8, 7\]", "表行 8"),
        (r"\| 9 => !\[4, 5, 3, 1, 2, 0, 7, 8, 6\]", "表行 9"),
        (r"\| 10 => !\[5, 3, 4, 2, 0, 1, 8, 6, 7\]", "表行 10"),
        (r"\| 11 => !\[5, 4, 3, 2, 1, 0, 7, 6, 8\]", "表行 11"),
        (r"noncomputable def tau \(n : Fin 12\) : Equiv\.Perm \(Fin 9\) :=", "tau def"),
        (r"theorem tau_mem \(n : Fin 12\) : ttpAutPred \(tau n\)", "逐元成员定理"),
        (r"theorem head3_inj : Function\.Injective \(fun n : Fin 12 => head3 \(tau n\)\)",
         "两两互异（head3 注入）"),
        (r"theorem card_ge : 12 ≤ Fintype\.card", "下界 card_ge"),
        # (iii) 上界链牙
        (r"theorem nodeOfN_two_caps : ∀ i j : Fin 9, nodeOfN i\.val j\.val = 2 →",
         "色 2 帽-帽唯一性"),
        (r"def inPartners \(w x : ℕ\) : Prop :=", "ν₂ 伙伴面 def"),
        (r"theorem caps_third : ∀ d a b : Fin 9, a ≠ b →", "帽第三元覆盖（3 层 decide）"),
        (r"theorem third_cap_unique : ∀ a b c : Fin 9, a ≠ b → a ≠ c → b ≠ c →",
         "第三帽唯一性"),
        (r"theorem not_cap_of_distinct \(σ : Equiv\.Perm \(Fin 9\)\) \(hcond : ttpAutPred σ\)",
         "非帽传递（符号提升）"),
        (r"theorem nu2_partner : ∀ u v : Fin 9, nodeOfN u\.val v\.val = 1 →",
         "色 1 伙伴面"),
        (r"theorem pin5_unique : ∀ u v b : Fin 9, nodeOfN u\.val v\.val = 4 →",
         "ν₅∩伙伴面唯一性"),
        (r"theorem partner_other_unique : ∀ w u v : Fin 9, inPartners w\.val u\.val →",
         "补元唯一性"),
        (r"theorem sig_values \(σ : Equiv\.Perm \(Fin 9\)\) \(hcond : ttpAutPred σ\) :",
         "签名决定引理"),
        (r"\(σ 1\)\.val = pin5 \(σ 0\)\.val \(σ 8\)\.val ∧", "sig_values σ-项牙 1"),
        (r"\(σ 8\)\.val = thirdCap \(σ 6\)\.val \(σ 7\)\.val :=", "sig_values σ-项牙 2"),
        (r"theorem eq_tau_of_vals \(σ : Equiv\.Perm \(Fin 9\)\) \(r : Fin 12\)",
         "九像值 finisher"),
        (r"theorem upper : ∀ σ : Equiv\.Perm \(Fin 9\), ttpAutPred σ →",
         "上界分支树定理"),
        (r"theorem card_le : Fintype\.card", "上界 card_le"),
        # (iv) 头条＋锚＋桥
        (r"theorem card_ttpAut_eq_12 :\n    Fintype\.card \{σ : Equiv\.Perm \(Fin 9\) // ∀ i j : Fin 9, i ≠ j →",
         "头条定理语句形"),
        (r"= 12 :=\n  le_antisymm card_le card_ge", "头条 12 牙（le_antisymm）"),
        (r"theorem card_factorial_anchor : Nat\.factorial 9 /", "轨道-稳定子锚（9!）"),
        (r"= 30240 := by\n  rw \[card_ttpAut_eq_12\]\n  norm_num", "30240 norm_num 牙"),
        (r"theorem mem_iff_in_table \{σ : Equiv\.Perm \(Fin 9\)\} :",
         "Set 形式↔12 显式表桥"),
    ]
    for pat, name in anchors:
        if not re.search(pat, src, re.M):
            fail(f"G4 语句锚缺失：{name}（pattern {pat!r}）")
    # 零 sorry：剥离模块/定理 docstring（/-! … -/ 与 /-- … -/）后扫描——
    # docstring 的『zero `sorry`』叙述性提及不算，定理体出现即拦。
    stripped = re.sub(r"/--?[\s\S]*?-/", "", src)
    if re.search(r"\bsorry\b|sorryAx\b", stripped):
        fail("G4 禁串失守：TableB1Aut.lean 非 docstring 面含 sorry/sorryAx")
    # 零 ≥15 位数字字面量
    long_lits = re.findall(r"\d{15,}", src)
    if long_lits:
        fail(f"G4 零 ≥15 位数字字面量失守：{long_lits[:3]}")
    # 非交叠守卫（其余件/根模块/lake/脚本零 TableB1Aut 引用）
    for rel in NONOVERLAY_FILES:
        p = LEAN_DIR / rel
        if p.is_file() and "TableB1Aut" in p.read_text():
            fail(f"G4 非交叠守卫：{rel} 含 'TableB1Aut'（本件必须不被其余件/"
                 "根模块引用）")
    for rel in ("lakefile.toml", "scripts/check.sh"):
        p = REPO / rel
        if p.is_file() and "TableB1Aut" in p.read_text():
            fail(f"G4 非交叠守卫：{rel} 含 'TableB1Aut'")
    okmsg(f"G4 语句锚：import 面恰两行；{len(anchors)} 锚全在（接口形四件/"
          "12 行表全在/逐元成员/两两互异/card_ge/上界链十牙/card_le/头条 12/"
          "轨道-稳定子锚 30240/Set↔表桥）＋零 sorry＋零 ≥15 位字面量＋"
          "非交叠零引用")


# ============================================================ G5
def gate5_second_impl() -> dict:
    t0 = time.time()
    src = (LEAN_DIR / "ThomsonN9" / "TableB1Aut.lean").read_text()
    # (a) 独立第四实现 vs r15 import（nodeOfN 相关锚 sanity）
    import importlib.util
    spec = importlib.util.spec_from_file_location("r15_b1_data",
                                                  HERE / "r15_b1_data.py")
    r15 = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(r15)
    # 36 无序/有序 i≠j 对（nodeOfN 分类仅在 i≠j 有定义；i=j 为哑值 9——
    # r15 规则同构面同样只在 i≠j 承重）
    mis = sum(1 for i in range(9) for j in range(9)
              if i != j and gate_node_of_n(i, j) != r15.nodeOfN_rule(i, j))
    if mis != 0:
        fail(f"G5 独立第四实现 vs r15 nodeOfN_rule 出现 {mis} 处 mismatch")
    # (b) Lean 源直读 12 行表
    rows = parse_lean_rows(src)
    if [list(r) for r in rows] != ANCHOR_ROWS:
        fail("G5 Lean 源 12 行表 != 设计师锚表（逐位）")
    for k, row in enumerate(rows):
        if sorted(row) != list(range(9)):
            fail(f"G5 表行 {k} 非双射")
        if not row_satisfies(gate_node_of_n, row):
            fail(f"G5 表行 {k} 36 条件判定 FAIL（门内独立实现）")
    # (c) 全 S₉ 扫描（禁采样）
    aut = [list(t) for t in itertools.permutations(range(9))
           if row_satisfies(gate_node_of_n, t)]
    if len(aut) != 12:
        fail(f"G5 全 S₉ 扫描 |Aut|={len(aut)} != 12")
    if sorted(map(tuple, aut)) != sorted(map(tuple, rows)):
        fail("G5 全扫描 Aut != Lean 12 行表（逐位集合）")
    # (d) r22_pattern_numeric.json 对账
    r22p = load_json(REPO / R22P_REL)
    if r22p["automorphismGroup"]["elements"] != aut:
        fail("G5 扫描 Aut != r22_pattern_numeric.json elements（逐位）")
    if r22p["automorphismGroup"]["order"] != 12:
        fail("G5 r22_pattern order != 12")
    # (e) 生成元张成
    span = {tuple(range(9))}
    gens = [tuple(g) for g in ANCHOR_GENS.values()]
    frontier = True
    while frontier:
        frontier = False
        for g in gens:
            for x in list(span):
                for y in (compose(g, x), compose(x, g)):
                    if y not in span:
                        span.add(y)
                        frontier = True
    if set(span) != set(map(tuple, rows)):
        fail("G5 生成元 g₁/k/h 张成 != 全群")
    # (f) 阶分布＋重集
    dist = [perm_order(tuple(r)) for r in rows]
    if dist != ANCHOR_ORDER_DIST_LEX:
        fail(f"G5 阶分布(lex) {dist} != {ANCHOR_ORDER_DIST_LEX}")
    mult = {}
    for o in dist:
        mult[o] = mult.get(o, 0) + 1
    if {str(k): v for k, v in sorted(mult.items())} != ANCHOR_ORDER_MULTISET:
        fail(f"G5 阶重集 {mult} != D₃×C₂ 型 {ANCHOR_ORDER_MULTISET}")
    # (g) head3 两两相异
    h3 = {(r[0], r[1], r[2]) for r in rows}
    if len(h3) != 12:
        fail("G5 head3 三元组非两两相异")
    # (h) 轨道-稳定子算术锚
    l4 = load_json(REPO / L4_REL)
    labeled_total = l4["survivorSet"]["labeledTotal"]
    fact9 = 362880
    if fact9 // 12 != 30240 or fact9 % 12 != 0:
        fail("G5 9!/12 != 30240（整除）")
    if labeled_total != 30240:
        fail(f"G5 l4_orbit.json labeledTotal != 30240：{labeled_total}")
    if r22p["orbitStabilizer"]["orbitSize"] != 30240 or \
            r22p["orbitStabilizer"]["index"] != 12 or \
            r22p["orbitStabilizer"]["stabOrder"] != 12:
        fail("G5 r22_pattern F4 轨道-稳定子记录异常")
    if fact9 // 30240 != 12:
        fail("G5 9!/30240 != 12（|Stab| 口径）")
    dt = time.time() - t0
    okmsg(f"G5 第二实现面：独立第四实现 vs r15 nodeOfN_rule 36/36 零 mismatch；"
          f"Lean 源 12 行表逐行双射＋36 条件全过；全 S₉ 扫描（禁采样）"
          f"Aut==12 行表==r22_pattern elements 逐位；生成元张成==全群；"
          f"阶分布(lex)={dist}（≅D₃×C₂）；head3 两两相异；9!/12==30240=="
          f"labeledTotal==orbitSize、9!/30240==12==|Stab|（{dt:.1f}s）")
    return {"rows": rows, "aut": aut, "order_dist": dist}


# ============================================================ NC
def nc1_sorry_injection() -> None:
    d = TMP / "nc1"
    if d.exists():
        for p in sorted(d.rglob("*")):
            if p.is_file():
                p.unlink()
    (d / "ThomsonN9").mkdir(parents=True, exist_ok=True)
    src = (LEAN_DIR / "ThomsonN9" / "TableB1Aut.lean").read_text()
    m = re.search(r"theorem tau_mem[\s\S]*?:= by\n", src)
    if not m:
        fail("NC1 预置失败：tau_mem 未定位")
    nxt = re.search(r"\n/-- |\ntheorem |\nnoncomputable def |\ndef |instance ",
                    src[m.end():])
    body_end = m.end() + (nxt.start() + 1 if nxt else len(src))
    tampered = src[:m.end()] + "  sorry\n\n" + src[body_end:]
    (d / "ThomsonN9" / "TableB1Aut.lean").write_text(tampered)
    for dep in ("TableB1Data.olean", "TableB1.olean"):
        s = LEAN_DIR / OLEAN_REL / dep
        if not s.is_file():
            fail(f"NC1 预置失败：依赖 olen 不在场（G2 应已编译）：{s}")
        (d / "ThomsonN9" / dep).write_bytes(s.read_bytes())
    lp = run(["lake", "env", "printenv", "LEAN_PATH"], LEAN_DIR).stdout.strip()
    env = gate_env()
    env["LEAN_PATH"] = f"{d}:{lp}"
    b = subprocess.run(["lean", "--root", str(d), "-o",
                        str(d / "ThomsonN9" / "TableB1Aut.olean"),
                        str(d / "ThomsonN9" / "TableB1Aut.lean")],
                       cwd=str(LEAN_DIR), env=env, capture_output=True,
                       text=True, timeout=COMPILE_TIMEOUT_S)
    if b.returncode != 0 or "declaration uses `sorry`" not in (b.stdout + b.stderr):
        fail(f"NC1 注入 sorry 后编译未产生 sorry 警告（exit {b.returncode}）：\n"
             f"{(b.stdout + b.stderr)[-500:]}")
    axfile = d / "axcheck.lean"
    axfile.write_text("import ThomsonN9.TableB1Aut\n"
                      "#print axioms ThomsonN9.TableB1Aut.tau_mem\n")
    a = subprocess.run(["lean", str(axfile)], cwd=str(LEAN_DIR), env=env,
                       capture_output=True, text=True, timeout=COMPILE_TIMEOUT_S)
    ax = parse_axiom_lines(a.stdout)
    th = "ThomsonN9.TableB1Aut.tau_mem"
    caught = th in ax and ("sorryAx" in ax[th] or bool(ax[th] - ALLOWED_AXIOMS))
    if not caught:
        fail(f"NC1 失守：注入 sorry 后公理检查未现 sorryAx（{ax}）")
    okmsg(f"NC1 注入 sorry 必被 G3 拦：篡件 tau_mem 公理集 = "
          f"{sorted(ax.get(th, set()))}（含 sorryAx——有牙实证；原件 sanity＝"
          "G3 全过）")


def nc2_nodeofn_anchor_tamper() -> None:
    """篡 nodeOfN 相关锚（两向注入，均须被拦）：
    (a) 值向：门内端口 ν₂ 残差 1→5（帽-棱伙伴面数值反转）→ r15 对账必拦；
    (b) 位向：残差方向反转（prism−cap 替代 cap−prism——伙伴面几何反转，
        现实作弊向）→ r15 对账 mismatch＋12 行判定 6 行 FAIL
        （值向为类后重标记、保等价——位向才动分类本体）。"""
    def tampered_value(i: int, j: int) -> int:
        v = gate_node_of_n(i, j)
        return 5 if v == 1 else v          # 现实作弊向：假装残差 1 → ν₆

    def tampered_direction(i: int, j: int) -> int:
        if i == j:
            return 9
        la, lb = i // 3, j // 3
        if la == lb == 2:
            return 2
        if la < 2 and lb < 2:
            return 4 if la == lb else (3 if i % 3 == j % 3 else 0)
        cap, prism = (i, j) if la == 2 else (j, i)
        d = (prism % 3 - cap % 3) % 3      # 方向反转
        return 1 if d == 1 else 5

    rule = r15_rule()
    mis = sum(1 for i in range(9) for j in range(9)
              if i != j and tampered_value(i, j) != rule(i, j))
    if mis == 0:
        fail("NC2 失守：篡 ν₂ 残差规则未被 r15 对账检出")
    mis_d = sum(1 for i in range(9) for j in range(9)
                if i != j and tampered_direction(i, j) != rule(i, j))
    if mis_d == 0:
        fail("NC2 失守：残差方向反转未被 r15 对账检出")
    rows = parse_lean_rows((LEAN_DIR / "ThomsonN9" / "TableB1Aut.lean")
                           .read_text())
    n_fail = sum(0 if row_satisfies(tampered_direction, r) else 1 for r in rows)
    if n_fail == 0:
        fail("NC2 失守：残差方向反转后行判定未 FAIL")
    okmsg(f"NC2 篡 nodeOfN 相关锚必拦：值向 ν₂ 残差 1→5 → r15 对账 {mis} 有序对 "
          f"mismatch；位向残差方向反转 → r15 对账 {mis_d} 有序对 mismatch＋"
          f"12 行判定 {n_fail} 行 FAIL（有牙实证；未篡端口 sanity＝G5 对账"
          "零 mismatch）")


def r15_rule():
    import importlib.util
    spec = importlib.util.spec_from_file_location("r15_b1_data_nc2",
                                                  HERE / "r15_b1_data.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod.nodeOfN_rule


def nc3_table_tamper() -> None:
    """篡 12 表一元：第 1 行交换前两元（保持双射性）→ 行判定＋扫描集合必拦。"""
    rows = [list(r) for r in parse_lean_rows(
        (LEAN_DIR / "ThomsonN9" / "TableB1Aut.lean").read_text())]
    bad = [list(r) for r in rows]
    bad[1][0], bad[1][1] = bad[1][1], bad[1][0]   # 行 1 交换两元（仍双射）
    if sorted(bad[1]) != list(range(9)):
        fail("NC3 预置失败：篡行非双射（注入无效）")
    caught_member = not row_satisfies(gate_node_of_n, bad[1])
    if not caught_member:
        fail("NC3 失守：篡行未被 36 条件判定检出")
    aut = {tuple(t) for t in itertools.permutations(range(9))
           if row_satisfies(gate_node_of_n, t)}
    caught_set = set(map(tuple, bad)) != aut
    if not caught_set:
        fail("NC3 失守：篡表未被全扫描集合相等检出")
    okmsg("NC3 篡 12 表一元必拦：行 1 交换两元（保持双射）→ 行 36 条件判定 "
          "FAIL＋解析集≠全扫描 Aut（有牙实证；未篡表 sanity＝G5 全过）")


# ============================================================ main
def run_gate() -> dict:
    led = gate0_ledger()
    gate1_ownership()
    gate1_isolation()
    walls = gate2_elaborate()
    gate3_axioms(led)
    gate4_statements()
    g5 = gate5_second_impl()
    nc1_sorry_injection()
    nc2_nodeofn_anchor_tamper()
    nc3_table_tamper()
    return {"walls": walls, "g5": len(g5["aut"])}


def main() -> None:
    t0 = time.time()
    print(f"[gate] r22_b9aut_gate.py seed={SEED_GATE}（编译型门——十一连 "
          "elaboration，单文件 ≤600s；外层 1200s 文档化例外沿 R18/R19/R21B；"
          "零求解零 SDP 零 emitter；CWD 无关）")
    try:
        info = run_gate()
    except GateFail as e:
        print(f"[gate][FAIL] {e}", flush=True)
        sys.exit(1)
    wall = time.time() - t0
    print(f"[gate] PASS（{wall:.1f}s）——exit 0")
    print(f"[gate] elaboration 墙钟：{info['walls']}（十一连）")
    print("[gate] heavySolves=0（形式件：endgame.json/四账本只读未动；"
          "r22_b9aut 家族不入 12 分区）")


if __name__ == "__main__":
    main()
