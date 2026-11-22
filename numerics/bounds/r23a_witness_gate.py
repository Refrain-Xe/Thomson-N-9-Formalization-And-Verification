#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r23a_witness_gate.py — R23A 表 B 第十件（canonical rep 数据层形式消费：
σ₀ 见证性质＋对齐陪集唯一性 W==σ₀∘Aut＋|W|=12＋lex-min==σ₀＋PatternCons
见证无关性＋pattern_ident_lift σ₀ 实例）验收门（G0–G5＋NC1–NC4；seed
20261023——R10–R22=20261012–22 序列顺延；编译型门——十二连 elaboration，
单文件 ≤600s（D52-4/D64-5），外层 1200s 文档化例外沿 R18/R19/R21B/R22B；
CWD 无关——路径全部从 __file__ 解析）.

任务书口径（r23a-pattern-witness，campaign dwfrun-f9904baf 第 18 轮，D100
④(1)(2) 合一、D101 裁决 1/2）：被验件＝
formal/lean/ThomsonN9/TableB1Witness.lean（namespace ThomsonN9.TableB1Witness；
仅 import Mathlib＋ThomsonN9.TableB1＋ThomsonN9.TableB1Aut＋
ThomsonN9.TableB5Chain——传递闭包 ~13 文件；不 import 仓内其他解件、不被其
import——TableB5Chain/TableB1Aut 先例；不触 Solution.lean/scripts/check.sh/
lakefile/挑战文件/references）＋本门＋嵌套 CWD 包装器（D52-4 先例）＋账本
results/r23a_witness_ledger.json。零求解零 SDP 零 emitter。

方向裁决（D102 留痕；设计师预锚 2026-10-24 的 ∘ 形不变）：本工具链 Mathlib
的 Equiv.Perm 乘法为函数复合序——Mathlib/Algebra/Group/End.lean:68
`instance instMul : Mul (Perm α) where mul f g := Equiv.trans g f`，即
(e₁*e₂) i = e₁ (e₂ i)（非任务书预锚行文的旧约定 e₂ (e₁ i)）。故函数复合
(σ₀∘s)(i)=σ₀(s i) 在 mul 记号下＝`sigma0 * s`（任务书 (iv) W=={σ₀ * tau n}
与本工具链一致）；预锚的数学内容（正向 {σ₀∘s : s∈Aut}==W 成立、反向
{s∘σ₀} 不成立）由本门 G5 两方向对账活体复验，反向必不等——天然判别（NC3）。

检查面（对应任务书 G0–G5＋NC）：
  G0 账本自锚：在场＋seed==20261023＋heavy_solves==0＋kind/task＋
     axiom_policy 恰三标准 set 相等＋theorem_count 与源 regex 重数一致＋
     自有件 sha256 严格锚（漂移拦截有牙——NC4 活体实证）＋endgame 冻结锚
     字符串。
  G1 所有权＋冻结面＋隔离面：git 双路由（porcelain＋diff HEAD --name-only）
     改动 ⊆ 自有件（＋R23A_G1_ALLOW_FOREIGN 自跑逐件放行〔默认关〕＋r23
     家族放行层——D90-4 同款）；表 B 十二件 Lean git diff 守卫（冻结十一件
     ＋本件）＋挑战件目录/＋references/ 零触碰＋四账本 sha256 冻结锚＋
     endgame.json==86863a09…69f；隔离面：r23a_witness 不入 endgame.json
     （citedCertificates/12 分区零触碰）/endgame_chain.py 文本＋chain-only
     干跑五字段零漂移＋全集漂移叶 ⊆ 冻结 22 叶（D84-4/D93 口径）。
  G2 依赖序十二连 elaboration（TableB1Data→TableB1→TableB5Data→TableB5→
     TableB5Core→TableB5Trace→TableB5Polar→TableB5Uncond→TableB5ChainData→
     TableB5Chain→TableB1Aut→TableB1Witness），均 exit 0、输出无 error/
     sorry、墙钟 ≤600s/件。
  G3 公理直查活体：#print axioms 于 TableB1Witness 全部 theorem（regex 枚
     举，账本记精确数 19）——公理集 ⊆ {propext, Classical.choice,
     Quot.sound}，零 sorryAx/ofReduceBool/ofReduceNat/trustCompiler（D82-4
     口径）。
  G4 语句锚：import 恰三行 ThomsonN9（＋Mathlib）；接口形（witnessPred 行内
     ∀ 形／witnessSet Set 形／DecidablePred 实例／Fintype 实例）＋repData
     36 行全在（逐行字面＋pair 注释序）＋σ₀ 行逐位（sigRow0 image-tuple
     [0,5,6,4,2,1,7,3,8]）＋sigma0_witness（decide 臂 tau_mem :149 同式）＋
     陪集定理双向（witness_coset_iff 正向桥／mem_witness_iff_coset 唯一性／
     mem_witness_iff_table 12 显式元桥／witnessSet_eq_coset Set 等式）＋
     card 头条（le_antisymm card_le_witness card_ge_witness）＋lex-min
     （lexLess/lex_min_arm/sigma0_lex_min）＋见证无关性 pattern_cons_coset
     ＋σ₀ 实例锚 pattern_ident_lift_sigma0＋零 sorry＋零 ≥15 位数字字面量
     ＋非交叠守卫（其余 ThomsonN9 件/根模块/lake 面/脚本零 TableB1Witness
     引用）。
  G5 第二实现面（门内独立 Python，零仓 import 于被验件）：独立实现 nodeOfN
     （几何位直分类）vs r15_b1_data.nodeOfN_rule（import）72 有序对零
     mismatch→读 json feedContract.canonicalRep 并 sha256 校验
     （",".join 串==canonicalRepSha256==e69c0253…f225）→Lean 源直读
     repData 36 行==canonicalRep 逐位、sigRow0==sigma0LexMin 逐位→独立重算
     σ₀ 见证 36/36 无序对（72 有序对）零 mismatch→全 S₉ 362880 禁采样扫描
     |W|==12 且与 feedContract.witnesses 12 元列表逐位集合相等→W=={σ₀∘s :
     s∈Aut} 两方向对账（正向集合相等必过；反向 {s∘σ₀} 必不等——天然判别，
     交叠元数如实记）→lex-min(W)==σ₀（首差 lex）→W∩Aut==∅（对齐置换在
     Aut 外——陪集真位移）→9!/12==30240==l4_orbit labeledTotal。
  NC1 篹 rep 单色必拦（Lean 编译型有牙）：/tmp 副本把 repData 第 5 项
     （pair (0,6)）4→5 → sigma0_witness 的 decide 臂必 FAIL（编译非零退出
     ＋错误行定位）；数值侧同篡→σ₀ 见证 36 对重算 ≥1 mismatch（未篡原件
     sanity＝G2/G5 全过）。
  NC2 篹 σ₀ 表一元必拦：解析 sigRow0 后交换前两元（保持双射）→与
     sigma0LexMin 逐位 mismatch＋篡后 σ₀ 见证 36 对 FAIL（∉W）＋陪集
     {σ₀ᵗ∘s}≠W（有牙实证；未篡 sanity＝G5 全过）。
  NC3 篹陪集方向天然判别：反向对账 {s∘σ₀ : s∈Aut} != W 必 FAIL（若形式件
     方向篹反，G5 正向对账即拦）；交叠元数 |W∩反向陪集|＝1 如实记——反向
     陪集与 W 交叠但集合不等（非空交不削弱判别牙：判据是集合相等而非空交）。
  NC4 账本篡改面（沿 r22b NC 有牙实证）：/tmp 账本副本 theorem_count +1
     或 axiom_policy 摘除 propext → G0 校验逻辑必 GateFail（未篡账本
     sanity＝G0 全过）。

诚实边界：本门零求解零 SDP 零 emitter；endgame.json/四账本/l4_orbit.json/
r22_pattern_numeric.json 只读未动（sha256 锚＋干跑零漂移双面）；r23a_witness
家族不入 12 分区（隔离面）；|W|=12/W==σ₀∘Aut/lex-min==σ₀ 为无条件组合命题
（无 L6/pattern 类条件假设——PatternCons 消费面为显式假设接口，条件性诚实
边界在件内 docstring 留痕，D97 可回滚点段口径）。closed 终判与 L0/L3
blocker 均不动（r23c 收口判定）。

用法（CWD 无关）：
  python3 numerics/bounds/r23a_witness_gate.py    # 全门（exit 0 = 过）
  python3 thomson-n9/numerics/bounds/r23a_witness_gate.py
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

SEED_GATE = 20261023                   # R23 门 seed（R10–R22=20261012–22 顺延）
ELAB_LIMIT_S = 600                     # G2 每文件 ≤10 min（D52-4/D64-5）
COMPILE_TIMEOUT_S = 620

WITNESS_REL = "formal/lean/ThomsonN9/TableB1Witness.lean"
GATE_REL = "numerics/bounds/r23a_witness_gate.py"
WRAPPER_REL = "thomson-n9/numerics/bounds/r23a_witness_gate.py"   # 嵌套 CWD 包装器
LEDGER_REL = "numerics/bounds/results/r23a_witness_ledger.json"
DECISIONS_REL = "notes/decisions.md"
OWNED = {WITNESS_REL, GATE_REL, WRAPPER_REL, LEDGER_REL, DECISIONS_REL}

PARALLEL_FAMILY = [
    r"^formal/lean/ThomsonN9/TableB1Witness\.lean$",
    r"^numerics/bounds/r23[a-z0-9_]*(\.py|/)",
    r"^numerics/bounds/results/r23[a-z0-9_]*(\.json|/)",
    r"^thomson-n9/numerics/bounds/r23[a-z0-9_]*(\.py|/)",
    r"^notes/decisions\.md$",
    r"^notes/[a-z0-9-]+\.md$",
    r"^numerics/bounds/endgame_gate\.py$",
    r"^(GAP-REPORT|PROGRESS)\.md$",
]

# 只读冻结件（表 B 全家族——十一件冻结＋本件 TableB1Witness＝十二件：显式
# git diff 守卫；本件在 OWNED 集内，diff-vs-HEAD 于净树时为零）。
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
    "formal/lean/ThomsonN9/TableB1Witness.lean",
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
                    "ThomsonN9/TableB1Aut.lean",
                    "ThomsonN9/TableB5.lean", "ThomsonN9/TableB5Core.lean",
                    "ThomsonN9/TableB5Trace.lean", "ThomsonN9/TableB5Polar.lean",
                    "ThomsonN9/TableB5Uncond.lean", "ThomsonN9/TableB5Data.lean",
                    "ThomsonN9/TableB5Chain.lean",
                    "ThomsonN9/TableB5ChainData.lean",
                    "ThomsonN9/TableB6.lean", "ThomsonN9/TableB6Data.lean",
                    "ThomsonN9.lean", "lakefile.toml", "scripts/check.sh")

# 22 叶＝certReverify 17＋code_version/timestamp 2＋L1 quant 1＋engineV2 2
# （D84-4 口径；R20B/R21A/R21B/R22B 同表）。
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

TMP = Path("/tmp/r23a_witness_gate")
OLEAN_REL = ".lake/build/lib/lean/ThomsonN9"

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN_AXIOMS = ("sorryAx", "ofReduceBool", "ofReduceNat", "trustCompiler")

# 编译序（G2 依赖序十二连——任务书口径〔十一连＋本件 TableB1Witness〕）
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
    ("ThomsonN9/TableB1Witness.lean", "TableB1Witness"),
]

# 设计师锚（＝r22_pattern_numeric.json feedContract 层——G5 独立对账第三源）
ANCHOR_SIG0 = [0, 5, 6, 4, 2, 1, 7, 3, 8]
ANCHOR_CANON_REP_SHA256 = ("e69c0253f3325aaacec6be147db0dde31abe1a0251273b386c6"
                           "3e91a9808f225")
ANCHOR_AUT_ROWS = [
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


# ============================================================ 独立实现
def gate_node_of_n(i: int, j: int) -> int:
    """门内独立实现 nodeOfN（与 TableB1.lean:823 同构；r15 import／
    r22_pattern 主件移植／r22_b9aut_gate 几何直分类之外的新字面）：
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


PAIRS_LEX = [(i, j) for i in range(9) for j in range(9) if i < j]   # 36 无序对


def rep_pair(rep36, a: int, b: int) -> int:
    """无序对检索（pairIndex k↔第 k 个 i<j lex 对——feedContract
    pairIndexConvention 同约定）。"""
    i, j = (a, b) if a < b else (b, a)
    return rep36[PAIRS_LEX.index((i, j))]


def compose(t, s):
    """image-tuple 合成：(t∘s)(i) = t(s(i))——函数复合序。"""
    return tuple(t[i] for i in s)


def witness_pred(rep36, s) -> bool:
    """见证成员条件（rep[σ(i),σ(j)]==nodeOfN(i,j) ∀36 无序对）。"""
    return all(rep_pair(rep36, s[i], s[j]) == gate_node_of_n(i, j)
               for i in range(9) for j in range(9) if i < j)


def parse_lean_repdata(src: str):
    """从 Lean 源 repData 定义块直读 36 项（行号＋pair 注释＋色值）。"""
    m = re.search(r"def repData[\s\S]*?\| _ =>", src)
    if not m:
        fail("G5 预置失败：Lean 源缺 repData 定义块")
    block = m.group(0)
    rows = []
    for mm in re.finditer(r"\| (\d+) => (\d)  -- pair \((\d), ?(\d)\)", block):
        rows.append((int(mm.group(1)), int(mm.group(2)),
                     (int(mm.group(3)), int(mm.group(4)))))
    if len(rows) != 36:
        fail(f"G5 预置失败：repData 块仅解析出 {len(rows)} 行（应 36）")
    if [k for k, _, _ in rows] != list(range(36)):
        fail("G5 预置失败：repData 行号非 0..35 序")
    if [pr for _, _, pr in rows] != PAIRS_LEX:
        fail("G5 预置失败：repData pair 注释非 i<j lex 序")
    return [v for _, v, _ in rows]


def parse_lean_sigrow0(src: str):
    """从 Lean 源直读 σ₀ 行（image-tuple）。"""
    m = re.search(r"def sigRow0 : Fin 9 → Fin 9 := !\[(\d(?:, \d)*)\]", src)
    if not m:
        fail("G5 预置失败：Lean 源缺 sigRow0 定义")
    row = [int(v) for v in m.group(1).split(", ")]
    if sorted(row) != list(range(9)):
        fail("G5 预置失败：sigRow0 非双射")
    return row


# ============================================================ G0
def gate0_ledger(led_path: Path | None = None) -> dict:
    """G0 账本自锚（led_path 供 NC4 篹改面复用——默认真实账本路径）。"""
    if led_path is None:
        led_path = REPO / LEDGER_REL
    if not led_path.is_file():
        fail(f"G0 账本不在场：{led_path}")
    led = load_json(led_path)
    if led.get("seed") != SEED_GATE:
        fail(f"G0 seed 失配：{led.get('seed')!r} != {SEED_GATE}")
    if led.get("heavy_solves") != 0:
        fail(f"G0 heavy_solves 失配：{led.get('heavy_solves')!r} != 0")
    if led.get("kind") != "n9-r23-witness-ledger":
        fail(f"G0 kind 失配：{led.get('kind')!r}")
    if led.get("task") != "r23a-pattern-witness":
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
                                (REPO / WITNESS_REL).read_text(), re.M))
    if data.get("theorem_count") != n_theorems:
        fail(f"G0 theorem_count 失配：账本 {data.get('theorem_count')} != "
             f"regex 重数 {n_theorems}")
    for rel in (WITNESS_REL, GATE_REL, WRAPPER_REL):
        want = files.get(rel)
        if want in (None, "self"):
            fail(f"G0 files 锚缺失：{rel}")
        if sha256_of(REPO / rel) != want:
            fail(f"G0 新件 sha256 漂移：{rel}")
    fa = led.get("frozen_readonly_anchored", {})
    if fa.get("endgame_json_sha256") != ENDGAME_SHA256:
        fail("G0 冻结锚 endgame_json_sha256 失配")
    if led_path == REPO / LEDGER_REL:
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
                     os.environ.get("R23A_G1_ALLOW_FOREIGN", "").split(",")
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
                print(f"[gate][G1][r23 家族放行] 在途件（D90-4 pattern）：{p}")
                continue
            fail(f"G1 树上出现非本任务自有件（{cmd[1]}）：{p!r}"
                 f"（自有集={sorted(OWNED)}；r23 家族放行层未覆盖）")
    r = run(["git", "diff", "HEAD", "--"] + list(FROZEN_READONLY), REPO)
    if r.stdout.strip():
        fail("G1 表 B 十二件 Lean 冻结只读面被触碰（git diff 非空）")
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
    okmsg("G1 所有权＋冻结面：git 双路由改动 ⊆ 自有件＋r23 家族放行层；"
          "表 B 十二件 Lean git diff 守卫＋挑战件/ references/ 零触碰＋"
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
    tag = "r23a_witness"
    if tag in (REPO / ENDGAME_REL).read_text():
        fail(f"G1 隔离面：{tag} 出现在 endgame.json 文本中（审计件非证书——"
             "citedCertificates/12 分区零触碰）")
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
             f"chain 输入即在此暴露；处置归 D99/D103）：{sorted(fresh)[:6]}")
    missing = FROZEN_DRIFT_LEAVES - drifted
    if missing:
        fail(f"G1 漂移分布叶缺失（{len(missing)} 处——环境面变化，如实拦）："
             f"{sorted(missing)[:4]}")
    okmsg("G1 隔离面：r23a_witness 不入 endgame.json（citedCertificates/12 "
          "分区零触碰）/endgame_chain.py 文本；chain-only 干跑五字段逐位零"
          "漂移＋全集漂移恰为冻结 22 叶（certReverify 17＋code_version/"
          "timestamp 2＋L1 quant 1＋engineV2 2——D84-4/D93 口径）")


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
    okmsg("G2 依赖序十二连完毕（TableB1Data→TableB1→TableB5Data→TableB5→"
          "Core→Trace→Polar→Uncond→ChainData→Chain→TableB1Aut→"
          "TableB1Witness），olen 落 .lake/build 供 G3/NC 复用")
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
    src = (LEAN_DIR / "ThomsonN9" / "TableB1Witness.lean").read_text()
    names = theorem_names(src)
    if led["data"]["theorem_count"] != len(names):
        fail(f"G3 theorem_count 失配：账本 {led['data']['theorem_count']} != "
             f"regex 重数 {len(names)}")
    d = LEAN_DIR / OLEAN_REL
    d.mkdir(parents=True, exist_ok=True)
    axfile = d / "AxCheckTableB1Witness.lean"
    lines = ["import ThomsonN9.TableB1Witness"]
    for th in names:
        lines.append(f"#print axioms ThomsonN9.TableB1Witness.{th}")
    axfile.write_text("\n".join(lines) + "\n")
    r = run(["lake", "env", "lean", str(axfile)], LEAN_DIR,
            timeout_s=COMPILE_TIMEOUT_S)
    if r.returncode != 0:
        fail(f"G3 公理检查编译失败：\n{r.stdout[-600:]}\n{r.stderr[-600:]}")
    ax = parse_axiom_lines(r.stdout + r.stderr)
    check_axioms(ax, [f"ThomsonN9.TableB1Witness.{t}" for t in names],
                 "G3 TableB1Witness")
    okmsg(f"G3 公理直查活体：TableB1Witness {len(names)} 定理全过（恰三标准；"
          "零 sorryAx——D82-4 口径）")


# ============================================================ G4
def gate4_statements() -> None:
    src = (LEAN_DIR / "ThomsonN9" / "TableB1Witness.lean").read_text()
    imports = re.findall(r"^import\s+\S+", src, re.M)
    if imports != ["import Mathlib", "import ThomsonN9.TableB1",
                   "import ThomsonN9.TableB1Aut", "import ThomsonN9.TableB5Chain"]:
        fail(f"G4 import 面失配（应恰 Mathlib＋三行 ThomsonN9）：{imports}")
    anchors = [
        # (i) rep 数据层＋σ₀＋见证性质
        (r"namespace ThomsonN9\.TableB1Witness", "namespace 面"),
        (r"def sigRow0 : Fin 9 → Fin 9 := !\[0, 5, 6, 4, 2, 1, 7, 3, 8\]",
         "σ₀ 行逐位（image-tuple [0,5,6,4,2,1,7,3,8]）"),
        (r"theorem sigRow0_bij : Function\.Bijective sigRow0 := by decide",
         "σ₀ 行双射性"),
        (r"noncomputable def sigma0 : Equiv\.Perm \(Fin 9\) := Equiv\.ofBijective sigRow0 sigRow0_bij",
         "σ₀ 显式 Equiv.Perm"),
        (r"def pairIdx \(i j : ℕ\) : ℕ := 8 \* i - i \* \(i - 1\) / 2 \+ \(j - i - 1\)",
         "pairIndex（k↔第 k 个 i<j lex 对）"),
        (r"def repData \(k : ℕ\) : ℕ :=", "repData 36 行表 def"),
        (r"def repPair \(a b : ℕ\) : ℕ :=", "rep 无序对检索 def"),
        (r"theorem sigma0_witness \(i j : Fin 9\) \(hij : i ≠ j\) :",
         "头条之一 sigma0_witness 语句形"),
        (r"fin_cases i <;> fin_cases j <;> decide",
         "decide 臂（tau_mem :149 同式）"),
        # (ii) 载体＋陪集
        (r"def witnessPred \(σ : Equiv\.Perm \(Fin 9\)\) : Prop :=",
         "成员条件 def（行内 ∀ 形）"),
        (r"∀ i j : Fin 9, i ≠ j → repPair \(σ i\)\.val \(σ j\)\.val = nodeOfN i\.val j\.val",
         "36 条件有限合取行内形"),
        (r"def witnessSet : Set \(Equiv\.Perm \(Fin 9\)\) := \{σ \| witnessPred σ\}",
         "Set 形式"),
        (r"instance witnessPredDecidable \(σ : Equiv\.Perm \(Fin 9\)\) : Decidable \(witnessPred σ\)",
         "DecidablePred 实例"),
        (r"instance witnessFintype :", "Fintype 实例"),
        (r"theorem witness_coset_iff \(s : Equiv\.Perm \(Fin 9\)\) :",
         "对齐陪集桥"),
        (r"witnessPred \(sigma0 \* s\) ↔ ttpAutPred s",
         "陪集桥方向牙（σ₀∘s＝sigma0 * s——函数复合序 mul）"),
        (r"theorem mul_coset_left \(σ : Equiv\.Perm \(Fin 9\)\) :",
         "复合恒等左"),
        (r"theorem mul_coset_right \(σ : Equiv\.Perm \(Fin 9\)\) :",
         "复合恒等右"),
        (r"theorem mem_witness_iff_coset \{σ : Equiv\.Perm \(Fin 9\)\} :",
         "头条之二 对齐陪集唯一性语句形"),
        (r"σ ∈ witnessSet ↔ sigma0\.symm \* σ ∈ ttpAut",
         "唯一性牙（σ₀⁻¹∘σ∈ttpAut）"),
        (r"theorem mem_witness_iff_table \{σ : Equiv\.Perm \(Fin 9\)\} :",
         "12 显式元桥语句形"),
        (r"σ ∈ witnessSet ↔ ∃ n : Fin 12, σ = sigma0 \* tau n",
         "12 显式元桥牙（W=={σ₀ * tau n}）"),
        (r"theorem witnessSet_eq_coset :",
         "Set 形式陪集等式语句形"),
        (r"witnessSet = \(fun s : Equiv\.Perm \(Fin 9\) => sigma0 \* s\) '' ttpAut",
         "Set 等式牙（W=={σ₀∘s : s∈ttpAut} 像）"),
        # (iii) card 头条
        (r"theorem card_le_witness :", "上界 card_le_witness"),
        (r"theorem card_ge_witness :", "下界 card_ge_witness"),
        (r"theorem card_witness_eq_12 :", "头条之三 card 语句形"),
        (r"= 12 :=\n  le_antisymm card_le_witness card_ge_witness",
         "头条 12 牙（le_antisymm）"),
        # (iv) lex-min
        (r"def lexLess \(σ τ : Equiv\.Perm \(Fin 9\)\) : Prop :=",
         "首差 lex 序 def"),
        (r"theorem lex_min_arm \(n : Fin 12\) :", "lex 逐臂定理"),
        (r"theorem sigma0_lex_min : ∀ σ ∈ witnessSet, σ = sigma0 ∨ lexLess sigma0 σ",
         "头条之四 lex-min 语句形"),
        # (v)(vi) PatternCons 消费＋σ₀ 实例锚
        (r"theorem pattern_cons_coset \{Y : Matrix \(Fin 9\) \(Fin 3\) ℝ\} \{z ρ : ℝ\}",
         "头条之五 PatternCons 见证无关性语句形"),
        (r"PatternCons Y z ρ sigma0", "PatternCons 消费牙"),
        (r"theorem pattern_ident_lift_sigma0 \{Y : Matrix \(Fin 9\) \(Fin 3\) ℝ\} \{z ρ : ℝ\}",
         "头条之六 σ₀ 实例锚语句形"),
        (r"pattern_ident_lift hT h1 h2 hρ sigma0 hpat i j hij",
         "pattern_ident_lift 实例化牙"),
    ]
    for pat, name in anchors:
        if not re.search(pat, src, re.M):
            fail(f"G4 语句锚缺失：{name}（pattern {pat!r}）")
    rows = re.findall(r"\| (\d+) => (\d)  -- pair \((\d), ?(\d)\)", src)
    if len(rows) != 36:
        fail(f"G4 repData 36 行全在失守：仅 {len(rows)} 行")
    # 零 sorry：剥离模块/定理 docstring（/-! … -/ 与 /-- … -/）后扫描——
    # docstring 的『zero `sorry`』叙述性提及不算，定理体出现即拦。
    stripped = re.sub(r"/--?[\s\S]*?-/", "", src)
    if re.search(r"\bsorry\b|sorryAx\b", stripped):
        fail("G4 禁串失守：TableB1Witness.lean 非 docstring 面含 sorry/sorryAx")
    # 零 ≥15 位数字字面量
    long_lits = re.findall(r"\d{15,}", src)
    if long_lits:
        fail(f"G4 零 ≥15 位数字字面量失守：{long_lits[:3]}")
    # 非交叠守卫（其余件/根模块/lake/脚本零 TableB1Witness 引用）
    for rel in NONOVERLAY_FILES:
        p = LEAN_DIR / rel
        if p.is_file() and "TableB1Witness" in p.read_text():
            fail(f"G4 非交叠守卫：{rel} 含 'TableB1Witness'（本件必须不被其余件/"
                 "根模块引用）")
    for rel in ("lakefile.toml", "scripts/check.sh"):
        p = REPO / rel
        if p.is_file() and "TableB1Witness" in p.read_text():
            fail(f"G4 非交叠守卫：{rel} 含 'TableB1Witness'")
    okmsg(f"G4 语句锚：import 面 Mathlib＋恰三行 ThomsonN9；{len(anchors)} 锚"
          "全在（接口形四件/repData 36 行全在/σ₀ 行逐位/sigma0_witness decide 臂/"
          "陪集定理双向四件/card 头条 le_antisymm/lex-min 三件/见证无关性/"
          "σ₀ 实例锚）＋零 sorry＋零 ≥15 位字面量＋非交叠零引用")


# ============================================================ G5
def gate5_second_impl() -> dict:
    t0 = time.time()
    src = (LEAN_DIR / "ThomsonN9" / "TableB1Witness.lean").read_text()
    # (a) 独立实现 vs r15 import（nodeOfN 相关锚 sanity——72 有序对）
    import importlib.util
    spec = importlib.util.spec_from_file_location("r15_b1_data",
                                                  HERE / "r15_b1_data.py")
    r15 = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(r15)
    mis = sum(1 for i in range(9) for j in range(9)
              if i != j and gate_node_of_n(i, j) != r15.nodeOfN_rule(i, j))
    if mis != 0:
        fail(f"G5 独立实现 vs r15 nodeOfN_rule 出现 {mis} 处 mismatch")
    # (b) json canonicalRep 读取＋sha256 校验
    r22p = load_json(REPO / R22P_REL)
    fc = r22p["feedContract"]
    rep = fc["canonicalRep"]
    join_sha = hashlib.sha256(",".join(map(str, rep)).encode()).hexdigest()
    if join_sha != fc["canonicalRepSha256"]:
        fail(f"G5 canonicalRep sha256 失配：{join_sha} != "
             f"{fc['canonicalRepSha256']}")
    if fc["canonicalRepSha256"] != ANCHOR_CANON_REP_SHA256:
        fail("G5 canonicalRep sha256 != 设计师冻结锚 e69c0253…f225")
    if len(rep) != 36:
        fail("G5 canonicalRep 非 36 项")
    # (c) Lean 源直读对账
    rep_lean = parse_lean_repdata(src)
    if rep_lean != rep:
        bad = [(k, a, b) for k, (a, b) in enumerate(zip(rep_lean, rep)) if a != b]
        fail(f"G5 Lean repData != json canonicalRep（{len(bad)} 处逐位失配）")
    sig0 = parse_lean_sigrow0(src)
    if sig0 != ANCHOR_SIG0:
        fail(f"G5 Lean sigRow0 != 设计师锚 {ANCHOR_SIG0}")
    if fc.get("sigma0LexMin") != ANCHOR_SIG0:
        fail("G5 json sigma0LexMin != 设计师锚")
    # (d) 独立重算 σ₀ 见证 36/36（72 有序对）
    wit_mis = sum(1 for i in range(9) for j in range(9)
                  if i != j and rep_pair(rep, sig0[i], sig0[j])
                  != gate_node_of_n(i, j))
    if wit_mis != 0:
        fail(f"G5 σ₀ 见证重算 {wit_mis} 有序对 mismatch（应 36/36 零差）")
    # (e) 全 S₉ 扫描（禁采样）
    W = [list(p) for p in itertools.permutations(range(9)) if witness_pred(rep, p)]
    if len(W) != 12:
        fail(f"G5 全 S₉ 扫描 |W|={len(W)} != 12")
    if sorted(map(tuple, W)) != sorted(map(tuple, fc["witnesses"])):
        fail("G5 扫描 W != feedContract.witnesses（逐位集合）")
    # (f) 陪集两方向对账（正向必等、反向必不等——天然判别）
    aut = [tuple(r) for r in ANCHOR_AUT_ROWS]
    if r22p["automorphismGroup"]["elements"] != [list(a) for a in aut]:
        fail("G5 设计师锚表 != r22_pattern automorphismGroup.elements")
    sig0t = tuple(sig0)
    fwd = sorted(set(compose(sig0t, s) for s in aut))
    rev = sorted(set(compose(s, sig0t) for s in aut))
    if fwd != sorted(map(tuple, W)):
        fail("G5 正向对账 FAIL：{σ₀∘s : s∈Aut} != W（形式件陪集方向若有误即在此暴露）")
    if rev == sorted(map(tuple, W)):
        fail("G5 判别失效：反向 {s∘σ₀} 意外等于 W（反向必不等——天然判别失守）")
    inter = len(set(rev) & set(map(tuple, W)))
    # (g) lex-min==σ₀（首差 lex——即 tuple lex 序）
    if min(W) != sig0:
        fail(f"G5 lex-min(W)={min(W)} != σ₀")
    # (h) W∩Aut==∅（对齐置换在 Aut 外）＋轨道-稳定子锚
    Wset = set(map(tuple, W))
    if Wset & set(aut):
        fail("G5 W∩Aut 非空（σ₀∘Aut 陪集与 Aut 相交 ⟺ σ₀∈Aut——对齐置换应在 Aut 外）")
    l4 = load_json(REPO / L4_REL)
    labeled_total = l4["survivorSet"]["labeledTotal"]
    fact9 = 362880
    if fact9 // 12 != 30240 or fact9 % 12 != 0:
        fail("G5 9!/12 != 30240（整除）")
    if labeled_total != 30240:
        fail(f"G5 l4_orbit.json labeledTotal != 30240：{labeled_total}")
    if r22p["orbitStabilizer"]["orbitSize"] != 30240 or \
            r22p["orbitStabilizer"]["stabOrder"] != 12:
        fail("G5 r22_pattern F4 轨道-稳定子记录异常")
    dt = time.time() - t0
    okmsg(f"G5 第二实现面：独立实现 vs r15 nodeOfN_rule 72/72 零 mismatch；"
          f"canonicalRep sha256==e69c0253…f225 亲算；Lean repData 36 行==json "
          f"逐位、sigRow0==sigma0LexMin 逐位；σ₀ 见证重算 36/36 零差；全 S₉ "
          f"扫描（禁采样）|W|=12==feedContract.witnesses 逐位集合；正向对账 "
          f"W=={{σ₀∘s : s∈Aut}} 过、反向 {{s∘σ₀}} != W（交叠 {inter} 元——"
          f"集合不等判别牙在）；lex-min(W)==σ₀；W∩Aut==∅；9!/12==30240=="
          f"labeledTotal（{dt:.1f}s）")
    return {"w": W, "rep": rep, "sig0": sig0, "aut": aut, "inter": inter}


# ============================================================ NC
def nc1_rep_single_color_tamper() -> None:
    """篹 rep 单色必拦（Lean 编译型有牙）：/tmp 副本 repData 第 5 项（pair
    (0,6)）4→5 → sigma0_witness 的 decide 臂必 FAIL（编译非零退出＋错误行
    定位）；数值侧同篡 → σ₀ 见证 36 对重算 ≥1 mismatch（未篡 sanity＝G2/G5）。"""
    d = TMP / "nc1"
    if d.exists():
        for p in sorted(d.rglob("*")):
            if p.is_file():
                p.unlink()
    (d / "ThomsonN9").mkdir(parents=True, exist_ok=True)
    src = (LEAN_DIR / "ThomsonN9" / "TableB1Witness.lean").read_text()
    if "| 5 => 4  -- pair (0,6)" not in src:
        fail("NC1 预置失败：repData 第 5 项字面未定位")
    tampered = src.replace("| 5 => 4  -- pair (0,6)", "| 5 => 5  -- pair (0,6)")
    (d / "ThomsonN9" / "TableB1Witness.lean").write_text(tampered)
    for dep in ("TableB1Data.olean", "TableB1.olean", "TableB5Data.olean",
                "TableB5.olean", "TableB5Core.olean", "TableB5Trace.olean",
                "TableB5Polar.olean", "TableB5Uncond.olean",
                "TableB5ChainData.olean", "TableB5Chain.olean",
                "TableB1Aut.olean"):
        s = LEAN_DIR / OLEAN_REL / dep
        if not s.is_file():
            fail(f"NC1 预置失败：依赖 olen 不在场（G2 应已编译）：{s}")
        (d / "ThomsonN9" / dep).write_bytes(s.read_bytes())
    lp = run(["lake", "env", "printenv", "LEAN_PATH"], LEAN_DIR).stdout.strip()
    env = gate_env()
    env["LEAN_PATH"] = f"{d}:{lp}"
    b = subprocess.run(["lean", "--root", str(d), "-o",
                        str(d / "ThomsonN9" / "TableB1Witness.olean"),
                        str(d / "ThomsonN9" / "TableB1Witness.lean")],
                       cwd=str(LEAN_DIR), env=env, capture_output=True,
                       text=True, timeout=COMPILE_TIMEOUT_S)
    if b.returncode == 0:
        fail("NC1 失守：篹 rep 单色后编译意外通过（sigma0_witness decide 臂未拦）")
    out = b.stdout + b.stderr
    m = re.search(r"theorem sigma0_witness[\s\S]*?fin_cases i <;> fin_cases j <;> decide",
                  tampered)
    if not m:
        fail("NC1 预置失败：sigma0_witness decide 行未定位")
    ln = tampered[:m.end()].count("\n") + 1
    if f"TableB1Witness.lean:{ln}:" not in out:
        fail(f"NC1 错误未定位到 sigma0_witness decide 行（{ln}）：\n{out[-600:]}")
    # 数值侧同篡（σ₀ 见证重算口径——非直比较口径：canonicalRep 与 nodeOfN
    # 本就 27/36 直差，对齐性只在 σ₀-重排下成立）
    rep_t = parse_lean_repdata(tampered)
    sig0 = parse_lean_sigrow0(tampered)
    mis = sum(1 for i in range(9) for j in range(9)
              if i != j and rep_pair(rep_t, sig0[i], sig0[j])
              != gate_node_of_n(i, j))
    if mis == 0:
        fail("NC1 失守：篹 rep 单色后 σ₀ 见证重算零 mismatch")
    okmsg(f"NC1 篹 rep 单色必拦：repData[5]（pair (0,6)）4→5 → Lean 编译非零"
          f"退出＋错误定位 sigma0_witness decide 行 {ln}（decide 臂 FAIL——有牙"
          f"实证）；数值侧 σ₀ 见证重算 {mis} 有序对 mismatch（未篡原件 "
          f"sanity＝G2/G5 全过）")


def nc2_sig0_row_tamper() -> None:
    """篹 σ₀ 表一元必拦：解析 sigRow0 后交换前两元（保持双射）→与
    sigma0LexMin 逐位 mismatch＋篡后 σ₀ 见证 36 对 FAIL（∉W）＋陪集
    {σ₀ᵗ∘s}≠W（有牙实证；未篡 sanity＝G5 全过）。"""
    src = (LEAN_DIR / "ThomsonN9" / "TableB1Witness.lean").read_text()
    sig0 = parse_lean_sigrow0(src)
    r22p = load_json(REPO / R22P_REL)
    fc = r22p["feedContract"]
    rep = fc["canonicalRep"]
    tampered = list(sig0)
    tampered[0], tampered[1] = tampered[1], tampered[0]
    tampered = tuple(tampered)
    if sorted(tampered) != list(range(9)):
        fail("NC2 预置失败：篡行非双射（注入无效）")
    caught_json = tampered != tuple(fc["sigma0LexMin"])
    if not caught_json:
        fail("NC2 失守：篡 σ₀ 行未被 sigma0LexMin 逐位锚检出")
    mis = sum(1 for i in range(9) for j in range(9)
              if i != j and rep_pair(rep, tampered[i], tampered[j])
              != gate_node_of_n(i, j))
    if mis == 0:
        fail("NC2 失守：篡 σ₀ 行未被 36 对见证判定检出（仍在 W？）")
    aut = [tuple(r) for r in ANCHOR_AUT_ROWS]
    coset_t = sorted(set(compose(tampered, s) for s in aut))
    W = set(map(tuple, fc["witnesses"]))
    caught_coset = coset_t != sorted(W)
    if not caught_coset:
        fail("NC2 失守：篡 σ₀ 后陪集集合意外仍等于 W")
    okmsg(f"NC2 篹 σ₀ 表一元必拦：sigRow0 前两元交换（保持双射）→与 "
          f"sigma0LexMin 逐位 mismatch＋篡后 σ₀ 见证 {mis}/72 有序对 FAIL"
          f"（∉W）＋陪集 {{σ₀ᵗ∘s}}≠W（有牙实证；未篡 sanity＝G5 全过）")


def nc3_coset_direction_discriminator() -> None:
    """篹陪集方向天然判别：反向对账 {s∘σ₀ : s∈Aut} != W 必 FAIL（若形式件
    方向篹反，G5 正向对账即拦）；交叠元数 |W∩反向陪集| 如实记——反向陪集与
    W 交叠但集合不等（判据是集合相等而非空交）。"""
    r22p = load_json(REPO / R22P_REL)
    fc = r22p["feedContract"]
    sig0 = tuple(fc["sigma0LexMin"])
    aut = [tuple(r) for r in ANCHOR_AUT_ROWS]
    W = set(map(tuple, fc["witnesses"]))
    fwd = set(compose(sig0, s) for s in aut)
    rev = set(compose(s, sig0) for s in aut)
    if fwd != W:
        fail("NC3 预置失败：正向陪集 != W（设计师锚失效）")
    if rev == W:
        fail("NC3 失守：反向陪集意外等于 W（方向判别牙失守）")
    inter = len(W & rev)
    okmsg(f"NC3 篹陪集方向天然判别：正向 {{σ₀∘s}}==W（{len(fwd)} 元逐位）过；"
          f"反向 {{s∘σ₀}} != W（交叠 {inter} 元、集合不等——反向必不等判别牙在；"
          "若形式件陪集方向篹反，G5 正向对账即拦）")


def nc4_ledger_tamper() -> None:
    """账本篡改面（沿 r22b NC 有牙实证）：/tmp 账本副本 theorem_count +1 或
    axiom_policy 摘除 propext → G0 校验逻辑必 GateFail（未篡账本 sanity＝
    G0 全过——run_gate 已先跑真实 G0）。"""
    led = load_json(REPO / LEDGER_REL)
    variants = []
    a = json.loads(json.dumps(led))
    a["data"]["theorem_count"] = int(a["data"]["theorem_count"]) + 1
    variants.append(("theorem_count+1", a))
    b = json.loads(json.dumps(led))
    b["axiom_policy"] = [x for x in b["axiom_policy"] if x != "propext"]
    variants.append(("axiom_policy 摘 propext", b))
    for name, tam in variants:
        p = TMP / f"nc4_{abs(hash(name)) % 10**8}.json"
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(json.dumps(tam, ensure_ascii=False, indent=1))
        caught = False
        try:
            gate0_ledger(p)
        except GateFail:
            caught = True
        if not caught:
            fail(f"NC4 失守：账本篡改（{name}）未被 G0 校验逻辑检出")
    okmsg("NC4 账本篡改面必拦：theorem_count+1／axiom_policy 摘 propext 两向 "
          "篡改 → G0 校验逻辑均 GateFail（有牙实证；未篡账本 sanity＝G0 全过）")


# ============================================================ main
def run_gate() -> dict:
    led = gate0_ledger()
    gate1_ownership()
    gate1_isolation()
    walls = gate2_elaborate()
    gate3_axioms(led)
    gate4_statements()
    g5 = gate5_second_impl()
    nc1_rep_single_color_tamper()
    nc2_sig0_row_tamper()
    nc3_coset_direction_discriminator()
    nc4_ledger_tamper()
    return {"walls": walls, "g5_w": len(g5["w"]), "inter": g5["inter"]}


def main() -> None:
    t0 = time.time()
    print(f"[gate] r23a_witness_gate.py seed={SEED_GATE}（编译型门——十二连 "
          "elaboration，单文件 ≤600s；外层 1200s 文档化例外沿 R18/R19/R21B/"
          "R22B；零求解零 SDP 零 emitter；CWD 无关）")
    try:
        info = run_gate()
    except GateFail as e:
        print(f"[gate][FAIL] {e}", flush=True)
        sys.exit(1)
    wall = time.time() - t0
    print(f"[gate] PASS（{wall:.1f}s）——exit 0")
    print(f"[gate] elaboration 墙钟：{info['walls']}（十二连）")
    print(f"[gate] G5 |W|={info['g5_w']}（陪集反向交叠 {info['inter']} 元）")
    print("[gate] heavySolves=0（形式件：endgame.json/四账本只读未动；"
          "r23a_witness 家族不入 12 分区）")


if __name__ == "__main__":
    main()
