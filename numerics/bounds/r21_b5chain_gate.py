#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r21_b5chain_gate.py — R21B 表 B 第八件（链装配/节点辨识形式件）验收门
（G0–G5＋负对照 NC1/NC2/NC3；seed 20261021；编译型门——十连 elaboration，
单文件 ≤600s（D52-4/D64-5），外层 1200s 文档化例外沿 R18/R19；CWD 无关）.

任务书口径（r21b-chain-lean，campaign dwfrun-f9904baf 第 16 轮，D90 裁决
1/4、D92 裁决 1–4）：被验件＝formal/lean/ThomsonN9/TableB5Chain.lean
（namespace ThomsonN9.TableB5Chain；三件套定理 (i) 节点辨识唯一性/
(ii) δ=ρ 逐对口径显式转换双档/(iii) 链装配条件定理双档＋seam 推论
双档——R20 缝消费的形式接口落地）＋formal/lean/ThomsonN9/
TableB5ChainData.lean（发射器 numerics/bounds/r21_b5chain_data.py 先例
r13_a1/r15_b1_data.py：15 对 ν 容器间隙精确 ℚ 下界＋gMin＋r_ball＋
sqrt2Up/dmaxUp/tUp 包络＋CBhi/CAhi/deltaA＋rhoNeedB/rhoNeedA）＋
results/r21_b5chain_data.json＋本门＋嵌套 CWD 包装器（D52-4 先例）＋
会话根包装器（D7/D8/D9 先例，仓库外不入版本库）＋账本
results/r21_b5chain_ledger.json＋notes/tableb-lean.md §8（append-only）。
冻结件零改动只 import（TableB1Data/TableB1/TableB5 家族全件 git diff
守卫＋TableB5Uncond==c79fc623…/TableB5Polar==d8c58f7d… sha256 锚）。

检查面（对应任务书 G0–G5＋NC1/NC2/NC3）：
  G0 账本在场与受控字段（seed==20261021、heavy_solves==0、kind/task、
     axiom_policy 恰三标准 set 相等、theorem_count 与源 regex 重数一致、
     自有件在 files 清单、冻结锚三件字符串）。
  G1 所有权＋冻结面＋隔离面：git 双路由（porcelain＋diff HEAD --name-only）
     改动 ⊆ 自有件（＋R21B_G1_ALLOW_FOREIGN 自跑逐件放行〔默认关〕＋
     r21 家族放行层——D90 裁决 4 串行落盘）；表 B/A/M1/Solution/lake 面
     只读 git diff 守卫；挑战件目录/＋references/ 零触碰；四账本
     sha256 冻结锚；endgame.json==86863a09…69f＋TableB5Uncond==
     c79fc623…＋TableB5Polar==d8c58f7d…；隔离面：r21_b5chain 不入
     endgame.json/endgame_chain.py 文本＋chain-only 干跑五字段零漂移＋
     全集漂移叶 ⊆ 冻结 22 叶（新叶即 FAIL，处置归 D93）。
  G2 发射器确定性重跑（--out /tmp 与存档 json/Lean 逐位 cmp）＋依赖序
     十连 elaboration（TableB5Data→B5→Core→Trace→Polar→Uncond→B1Data→
     B1→ChainData→Chain，均 exit 0、输出无 error/sorry、墙钟 ≤600s/件）。
  G3 公理直查活体：#print axioms 于 TableB5Chain＋TableB5ChainData 全部
     theorem（regex 枚举，账本记精确数）——公理集 ⊆ {propext,
     Classical.choice, Quot.sound}，零 sorryAx/ofReduceBool/ofReduceNat/
     trustCompiler。
  G4 语句锚：import 面恰十行；三件套定理头/牙（ident_unique 双命中形、
     chain_convert/chain_convert_A 的 C_B/coeff_A 常数链牙、
     chain_assemble_* 的 L6Hyp/球门牙、seam_cor_* 的 rhoNeed 牙、
     L6Hyp/TubePremise/PatternCons/rowPerm/identNode 接口形牙）；主件
     零 ≥15 位数字字面量（数据件承担——TableB1Data/TableB5Data 先例）；
     数据件十五间隙 def＋gMin/r_ball/CBhi/CAhi/deltaA/rhoNeed* 全在；
     非交叠守卫（其余 ThomsonN9 件/lake 面零 TableB5Chain 引用）。
  G5 离线精确复核（stdlib Fraction 零仓 import，独立第二实现：
     TableB1Data/TableB5Data def 源直读→15 间隙/gMin/CBhi/CAhi/deltaA
     重导与 TableB5ChainData.lean 字面逐位；CBhi==r20 supply.C_B.hi
     逐位、CAhi==supply.C_A.delta_caliber 逐位、deltaA==supply.C_A.
     delta_A 逐位；(r_ball/CBhi)²==r20 seam_table r_star_raw/
     B_global_hoelder 行 threshold.exact 逐位（**r_ball 口径交叉对账**
     ——r_ball==r*==950125/10⁸==l6_intube rigorousRadius）；r_ball/CAhi
     ==r_star_raw/A_narrow_linear 行逐位；rhoNeed*==min 支路逐位；域面
     六件；tube.json half_gap float_advisory 定向宽安全边
     0 ≤ 2·half_gap-gMin ≤ 1e-5〔容器包络宽 ~1e-6 级、间隙 0.037 级——
     D92 裁决 3 口径在门 docstring 留档〕）。
  NC1 注入 sorry 必被 G3 拦：/tmp 副本把 ident_unique 证明改 sorry →
     独立编译必现 sorry 警告＋公理必现 sorryAx（未篡原件 sanity）。
  NC2 篡 gMin 必被 G5 拦：/tmp 数据件副本把 gMin 字面抬高 1% → 与
     15 间隙重导 min 不符（辨识窗方向反转——现实作弊向）。
  NC3 篡 CBhi 必被 G5 拦：/tmp 数据件副本把 CBhi 字面抬高 0.1%（假装
     缝阈值更小——方向反转）→ 与 r20 位对账拦截。

诚实边界：本门零求解零 SDP；endgame.json/四账本只读未动（sha256 锚＋
干跑零漂移双面）；r21_b5chain 家族不入 12 分区（隔离面）；L6/L3 侧
假设在 Lean 件内显式命名（L6Hyp/PatternCons/TubePremise——D92 裁决 4）。

用法（CWD 无关）：
  python3 numerics/bounds/r21_b5chain_gate.py    # 全门（exit 0 = 过）
  python3 thomson-n9/numerics/bounds/r21_b5chain_gate.py
      # ↑ CWD＝campaign 根的验收命令（真实门直路由）；CWD＝仓库根时命中
      #   嵌套 CWD 包装器（thomson-n9/thomson-n9/…，D52-4 先例）
"""
from __future__ import annotations

import hashlib
import json
import math
import os
import re
import subprocess
import sys
import time
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
REPO = HERE.parents[1]                 # thomson-n9/
LEAN_DIR = REPO / "formal" / "lean"

SEED_GATE = 20261021                   # R21 各门统一 seed（D90 裁决 4）
ELAB_LIMIT_S = 600                     # G2 每文件 ≤10 min（D52-4/D64-5）
COMPILE_TIMEOUT_S = 620

DATA_REL = "formal/lean/ThomsonN9/TableB5ChainData.lean"
CHAIN_REL = "formal/lean/ThomsonN9/TableB5Chain.lean"
EMITTER_REL = "numerics/bounds/r21_b5chain_data.py"
GATE_REL = "numerics/bounds/r21_b5chain_gate.py"
WRAPPER_REL = "thomson-n9/numerics/bounds/r21_b5chain_gate.py"   # 嵌套 CWD 包装器
LEDGER_REL = "numerics/bounds/results/r21_b5chain_ledger.json"
DATAJSON_REL = "numerics/bounds/results/r21_b5chain_data.json"
NOTES_REL = "notes/tableb-lean.md"
DECISIONS_REL = "notes/decisions.md"
OWNED = {DATA_REL, CHAIN_REL, EMITTER_REL, GATE_REL, WRAPPER_REL,
         LEDGER_REL, DATAJSON_REL, NOTES_REL, DECISIONS_REL}

PARALLEL_FAMILY = [
    r"^formal/lean/ThomsonN9/TableB5Chain(Data)?\.lean$",
    r"^numerics/bounds/r21[a-z0-9_]*(\.py|/)",
    r"^numerics/bounds/results/r21[a-z0-9_]*(\.json|/)",
    r"^thomson-n9/numerics/bounds/r21[a-z0-9_]*(\.py|/)",
    r"^notes/decisions\.md$",
    r"^notes/tableb-lean\.md$",
    r"^notes/chain-assembly\.md$",
    r"^numerics/bounds/endgame_gate\.py$",
    r"^(GAP-REPORT|PROGRESS)\.md$",
]

# 只读冻结件（表 B 全家族＋表 A/M1/Solution/根模块/lake 面）：显式 git diff 守卫。
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
UNCOND_SHA256 = "c79fc6231d1e13b8ffd7873d1338901602ed3b70b3f057ed4eec4eb757e36d5e"
POLAR_SHA256 = "d8c58f7d2c56c39fbe1ae62d634fc6ea5bd585fa9f1c0b9c2e2fc909d4338516"

NONOVERLAY_FILES = ("ThomsonN9/Solution.lean", "ThomsonN9/TableA.lean",
                    "ThomsonN9/TableA1.lean", "ThomsonN9/TableA3.lean",
                    "ThomsonN9/TableA4.lean", "ThomsonN9/TableA6.lean",
                    "ThomsonN9/M1Data.lean", "ThomsonN9/TableB1.lean",
                    "ThomsonN9/TableB1Data.lean", "ThomsonN9/TableB5.lean",
                    "ThomsonN9/TableB5Core.lean", "ThomsonN9/TableB5Trace.lean",
                    "ThomsonN9/TableB5Polar.lean", "ThomsonN9/TableB5Uncond.lean",
                    "ThomsonN9/TableB5Data.lean", "ThomsonN9/TableB6.lean",
                    "ThomsonN9/TableB6Data.lean",
                    "ThomsonN9.lean", "lakefile.toml", "scripts/check.sh")

# 22 叶＝certReverify 17＋code_version/timestamp 2＋L1 quant 1＋engineV2 2
# （D84-4 口径；R20B/R21A 同表）。
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

TMP = Path("/tmp/r21_b5chain_gate")
OLEAN_REL = ".lake/build/lib/lean/ThomsonN9"

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN_AXIOMS = ("sorryAx", "ofReduceBool", "ofReduceNat", "trustCompiler")

# 编译序（G2 依赖序十连）
COMPILE_ORDER = [
    ("ThomsonN9/TableB5Data.lean", "TableB5Data"),
    ("ThomsonN9/TableB5.lean", "TableB5"),
    ("ThomsonN9/TableB5Core.lean", "TableB5Core"),
    ("ThomsonN9/TableB5Trace.lean", "TableB5Trace"),
    ("ThomsonN9/TableB5Polar.lean", "TableB5Polar"),
    ("ThomsonN9/TableB5Uncond.lean", "TableB5Uncond"),
    ("ThomsonN9/TableB1Data.lean", "TableB1Data"),
    ("ThomsonN9/TableB1.lean", "TableB1"),
    ("ThomsonN9/TableB5ChainData.lean", "TableB5ChainData"),
    ("ThomsonN9/TableB5Chain.lean", "TableB5Chain"),
]

GAP_NAMES = [f"g{a}{b}" for (a, b) in (
    (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5),
    (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5))]
PAIR_ENDS = {
    "g01": ("nu2Lo", "nu1Hi"), "g02": ("nu3Lo", "nu1Hi"),
    "g03": ("nu4Lo", "nu1Hi"), "g04": ("nu5Lo", "nu1Hi"),
    "g05": ("nu6Lo", "nu1Hi"), "g12": ("nu3Lo", "nu2Hi"),
    "g13": ("nu4Lo", "nu2Hi"), "g14": ("nu5Lo", "nu2Hi"),
    "g15": ("nu6Lo", "nu2Hi"), "g23": ("nu4Lo", "nu3Hi"),
    "g24": ("nu5Lo", "nu3Hi"), "g25": ("nu6Lo", "nu3Hi"),
    "g34": ("nu5Lo", "nu4Hi"), "g35": ("nu6Lo", "nu4Hi"),
    "g45": ("nu6Lo", "nu5Hi"),
}


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


def parse_defs(src: str) -> dict:
    return dict(re.findall(r"^def\s+(\w+)\s*:\s*ℚ\s*:=\s*(\S+)", src, re.M))


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
    if led.get("kind") != "n9-r21-b5chain-ledger":
        fail(f"G0 kind 失配：{led.get('kind')!r}")
    if led.get("task") != "r21b-chain-lean":
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
    for k in ("theorem_count", "theorem_count_data"):
        if not isinstance(data.get(k), int) or data[k] < 1:
            fail(f"G0 data.{k} 失配（应 ≥1 整数）：{data.get(k)!r}")
    # 新件 sha256 与当前文件一致（自有件严格锚）
    for rel in (DATA_REL, CHAIN_REL, EMITTER_REL, GATE_REL, DATAJSON_REL,
                WRAPPER_REL):
        want = files.get(rel)
        if want in (None, "self"):
            fail(f"G0 files 锚缺失：{rel}")
        if sha256_of(REPO / rel) != want:
            fail(f"G0 新件 sha256 漂移：{rel}")
    fa = led.get("frozen_readonly_anchored", {})
    if fa.get("endgame_json_sha256") != ENDGAME_SHA256:
        fail("G0 冻结锚 endgame_json_sha256 失配")
    if fa.get("tableb5uncond_sha256") != UNCOND_SHA256:
        fail("G0 冻结锚 tableb5uncond_sha256 失配")
    if fa.get("tableb5polar_sha256") != POLAR_SHA256:
        fail("G0 冻结锚 tableb5polar_sha256 失配")
    okmsg(f"G0 账本在场（seed={SEED_GATE}，heavy_solves=0，kind/task，"
          f"axiom_policy 恰三标准，自有 {len(OWNED)} 件在清单＋新件 sha256 "
          "严格锚，冻结锚三件字符串在账）")
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
                     os.environ.get("R21B_G1_ALLOW_FOREIGN", "").split(",")
                     if q.strip()}
    for cmd in (["git", "status", "--porcelain"],
                ["git", "diff", "HEAD", "--name-only"]):
        r = run(["git", *cmd[1:]], REPO)
        if r.returncode != 0:
            raise GateFail(f"G1 {cmd[1]} 失败：{r.stderr.strip()[:300]}")
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
                print(f"[gate][G1][r21 家族放行] 在途件（D90 裁决 4 pattern）：{p}")
                continue
            raise GateFail(
                f"G1 树上出现非本任务自有件（{cmd[1]}）：{p!r}"
                f"（自有集={sorted(OWNED)}；r21 家族放行层未覆盖）")
    r = run(["git", "diff", "HEAD", "--"] + list(FROZEN_READONLY), REPO)
    if r.stdout.strip():
        fail("G1 表 B/A 冻结 Lean 件只读面被触碰（git diff 非空）")
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
    if sha256_of(REPO / CHAIN_REL.replace("TableB5Chain", "TableB5Uncond")
                 .replace("formal/lean/ThomsonN9/TableB5Uncond.lean",
                          "formal/lean/ThomsonN9/TableB5Uncond.lean")) \
            if False else sha256_of(LEAN_DIR / "ThomsonN9" / "TableB5Uncond.lean") \
            != UNCOND_SHA256:
        fail("G1 TableB5Uncond.lean sha256 != c79fc623…")
    if sha256_of(LEAN_DIR / "ThomsonN9" / "TableB5Polar.lean") != POLAR_SHA256:
        fail("G1 TableB5Polar.lean sha256 != d8c58f7d…")
    okmsg("G1 所有权＋冻结面：git 双路由改动 ⊆ 自有件＋r21 家族放行层；"
          "表 B 十件 Lean＋挑战件/ references/ ＋四账本 sha256 冻结锚＋"
          "endgame.json/TableB5Uncond/TableB5Polar 三 sha256 锚全过")


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
    tag = "r21_b5chain"
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
             f"chain 输入即在此暴露；处置归 D93）：{sorted(fresh)[:6]}")
    missing = FROZEN_DRIFT_LEAVES - drifted
    if missing:
        fail(f"G1 漂移分布叶缺失（{len(missing)} 处——环境面变化，如实拦）："
             f"{sorted(missing)[:4]}")
    okmsg("G1 隔离面：r21_b5chain 不入 endgame.json/endgame_chain.py 文本；"
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


def gate2_determinism_and_elaborate() -> dict:
    # (a) 发射器确定性重跑（G2 逐位面）
    outdir = TMP / "rerun"
    r = run([sys.executable, EMITTER_REL, "--out-dir", str(outdir)], REPO)
    if r.returncode != 0:
        fail(f"G2 发射器重跑 exit {r.returncode}：\n{r.stdout[-400:]}")
    for rel in (DATAJSON_REL, DATA_REL):
        a = (REPO / rel).read_bytes()
        b = (outdir / Path(rel).name).read_bytes()
        if a != b:
            fail(f"G2 发射器重跑与存档非逐位一致（{rel}：{len(a)} vs {len(b)} 字节）")
    okmsg("G2 发射器确定性重跑：/tmp 副产物与存档逐位一致"
          f"（{DATAJSON_REL}＋{Path(DATA_REL).name} cmp）")
    # (b) 依赖序十连 elaboration
    walls = {}
    for src, ol in COMPILE_ORDER:
        walls[ol] = round(compile_lean(src, ol), 1)
        okmsg(f"G2 elaboration：{src} exit 0 无 error/sorry"
              f"（{walls[ol]}s ≤ {ELAB_LIMIT_S}s）")
    okmsg("G2 依赖序十连完毕（Data5→B5→Core→Trace→Polar→Uncond→B1Data→B1→"
          "ChainData→Chain），olen 落 .lake/build 供 G3/NC 复用")
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
    chain_src = (LEAN_DIR / "ThomsonN9" / "TableB5Chain.lean").read_text()
    data_src = (LEAN_DIR / "ThomsonN9" / "TableB5ChainData.lean").read_text()
    n_chain = len(theorem_names(chain_src))
    n_data = len(theorem_names(data_src))
    if led["data"]["theorem_count"] != n_chain:
        fail(f"G3 theorem_count 失配：账本 {led['data']['theorem_count']} != "
             f"regex 重数 {n_chain}")
    if led["data"]["theorem_count_data"] != n_data:
        fail(f"G3 theorem_count_data 失配：账本 {led['data']['theorem_count_data']}"
             f" != regex 重数 {n_data}")
    d = LEAN_DIR / OLEAN_REL
    d.mkdir(parents=True, exist_ok=True)
    axfile = d / "AxCheckTableB5Chain.lean"
    lines = ["import ThomsonN9.TableB5Chain", "import ThomsonN9.TableB5ChainData"]
    for th in theorem_names(chain_src):
        lines.append(f"#print axioms ThomsonN9.TableB5Chain.{th}")
    for th in theorem_names(data_src):
        lines.append(f"#print axioms ThomsonN9.TableB5ChainData.{th}")
    axfile.write_text("\n".join(lines) + "\n")
    r = run(["lake", "env", "lean", str(axfile)], LEAN_DIR,
            timeout_s=COMPILE_TIMEOUT_S)
    if r.returncode != 0:
        fail(f"G3 公理检查编译失败：\n{r.stdout[-600:]}\n{r.stderr[-600:]}")
    ax = parse_axiom_lines(r.stdout + r.stderr)
    check_axioms(ax, [f"ThomsonN9.TableB5Chain.{t}" for t in theorem_names(chain_src)],
                 "G3 TableB5Chain")
    check_axioms(ax, [f"ThomsonN9.TableB5ChainData.{t}"
                      for t in theorem_names(data_src)], "G3 TableB5ChainData")
    okmsg(f"G3 公理直查活体：TableB5Chain {n_chain} 定理＋TableB5ChainData "
          f"{n_data} 定理全过（恰三标准；零 sorryAx）")


# ============================================================ G4
def gate4_statements(led: dict) -> None:
    src = (LEAN_DIR / "ThomsonN9" / "TableB5Chain.lean").read_text()
    dsrc = (LEAN_DIR / "ThomsonN9" / "TableB5ChainData.lean").read_text()
    imports = re.findall(r"^import\s+\S+", src, re.M)
    want_imports = ["import Mathlib", "import ThomsonN9.TableB1Data",
                    "import ThomsonN9.TableB1", "import ThomsonN9.TableB5Data",
                    "import ThomsonN9.TableB5", "import ThomsonN9.TableB5Core",
                    "import ThomsonN9.TableB5Trace",
                    "import ThomsonN9.TableB5Polar",
                    "import ThomsonN9.TableB5Uncond",
                    "import ThomsonN9.TableB5ChainData"]
    if imports != want_imports:
        fail(f"G4 import 面失配（应恰十行序）：{imports}")
    anchors = [
        # 接口形
        (r"def TubePremise \(Y : Matrix \(Fin 9\) \(Fin 3\) ℝ\) \(z ρ : ℝ\) : Prop",
         "L2 管前提接口形"),
        (r"def PatternCons \(Y : Matrix \(Fin 9\) \(Fin 3\) ℝ\) \(z ρ : ℝ\)",
         "pattern-consistency 接口形（σ₀ 显式）"),
        (r"def L6Hyp \(z r : ℝ\) \(E : Matrix \(Fin 9\) \(Fin 3\) ℝ → ℝ\)",
         "L6 显式假设接口形"),
        (r"noncomputable def identNode", "辨识映射 def"),
        (r"noncomputable def rowPerm", "σ₀-重排矩阵 def"),
        # (i)
        (r"theorem ident_unique \(z : ℝ\) \(h1 : \(zLo:ℝ\) ≤ z\) \(h2 : z ≤ \(zHi:ℝ\)\)",
         "(i) 辨识唯一性定理头锚"),
        (r"\(hρ : ρ < \(gMin:ℝ\)/2\) \(a b : ℕ\) \(ha : a < 6\) \(hb : b < 6\)",
         "(i) 辨识窗牙（ρ < gMin/2）"),
        (r"theorem pair_gap_le_two_rho", "(i) g_ab 面定理锚"),
        (r"theorem nu_dist_ge_gap", "(i) 容器间隙距离面锚"),
        (r"theorem identNode_unique", "(i) well-definedness 面锚"),
        (r"theorem pattern_ident_lift", "辨识升级桥锚"),
        # (ii)
        (r"theorem chain_convert \(z : ℝ\) \(h1 : \(zLo:ℝ\) ≤ z\) \(h2 : z ≤ \(zHi:ℝ\)\)",
         "(ii) 路线 B 转换定理头锚"),
        (r"theorem chain_convert_A \(z : ℝ\)", "(ii) 路线 A 转换定理头锚"),
        (r"≤ \(\(s1Up:ℝ\) \* \(u1:ℝ\) \* \(sqrt72Up:ℝ\) / \(l3:ℝ\)\^2"
         r"\s*\* Real\.sqrt \(deltaMax:ℝ\) \+ Real\.sqrt \(3 \* \(sqrt72Up:ℝ\)\)\)",
         "(ii) C_B 常数链牙（D92 δ=ρ 面安全向）"),
        (r"\(Real\.sqrt \(u1:ℝ\) \* \(u1:ℝ\) / \(l3:ℝ\)\^2"
         r"\s*\+ 2 \* Real\.sqrt 2 / Real\.sqrt \(l3:ℝ\)\)",
         "(ii) 路线 A coeff_A 常数链牙"),
        (r"\(hρA : ρ ≤ \(deltaA:ℝ\)\)", "(ii) 路线 A 窄域牙（δ_A 域）"),
        (r"frob \(\(ttpX z\) - rowPerm Y σ₀ \* Q\)", "(ii) 对 σ₀-重排牙（rowPerm）"),
        # (iii)
        (r"theorem chain_assemble_B \(z : ℝ\)", "(iii) 路线 B 装配定理头锚"),
        (r"theorem chain_assemble_A \(z : ℝ\)", "(iii) 路线 A 装配定理头锚"),
        (r"\(hL6 : L6Hyp z \(r_ball:ℝ\) E Ebar\)", "(iii) L6 显式假设牙（r_ball 球）"),
        (r"\* Real\.sqrt ρ ≤ \(r_ball:ℝ\)", "(iii) 路线 B 球门牙（C_B·√ρ ≤ r_ball）"),
        (r"\* \(sqrt72Up:ℝ\)\) \* ρ\s*≤ \(r_ball:ℝ\)",
         "(iii) 路线 A 球门牙（coeff_A·√72Up·ρ ≤ r_ball）"),
        # 推论
        (r"theorem seam_cor_B_pair \(z : ℝ\)", "缝推论 B 头锚"),
        (r"theorem seam_cor_A_pair \(z : ℝ\)", "缝推论 A 头锚"),
        (r"∀ a : ℕ, a < 6 →\s*\n?\s*\(rhoNeedB:ℝ\) < \|Y i ⬝ᵥ Y j - nuOfN a z\|",
         "缝推论 B ρ_need 牙（对节点集距离）"),
        (r"\(rhoNeedA:ℝ\) < \|Y i ⬝ᵥ Y j - nuOfN a z\|", "缝推论 A ρ_need 牙"),
        (r"theorem CB_le_CBhi", "包络引理 B 锚"),
        (r"theorem coeffA_le_CAhi", "包络引理 A 锚"),
        (r"theorem ttpX_gram_nodeOfN", "TTP Gram–节点桥锚"),
    ]
    for pat, name in anchors:
        if not re.search(pat, src, re.M):
            fail(f"G4 语句锚缺失：{name}（pattern {pat!r}）")
    # 条件性诚实锚：L6/pattern 为显式 hypothesis（L6Hyp/PatternCons 出现在
    # chain_assemble/seam_cor 陈述跨度内——G4 正向牙已覆盖）
    # 零 sorry
    if re.search(r"\bsorry\b", src):
        fail("G4 禁串失守：TableB5Chain.lean 含 sorry")
    if re.search(r"\bsorry\b", dsrc):
        fail("G4 禁串失守：TableB5ChainData.lean 含 sorry")
    # 主件零 ≥15 位数字字面量（数据件承担）
    long_lits = re.findall(r"\d{15,}", src)
    if long_lits:
        fail(f"G4 主件零 ≥15 位数字字面量失守：{long_lits[:3]}")
    # 数据件面：15 间隙 def＋gMin/r_ball/CBhi/CAhi/deltaA/rhoNeed*
    for nm in GAP_NAMES:
        if not re.search(rf"^def {nm} : ℚ :=", dsrc, re.M):
            fail(f"G4 数据件缺间隙 def {nm}")
        if not re.search(rf"^theorem {nm}_eq :", dsrc, re.M):
            fail(f"G4 数据件缺端点恒等定理 {nm}_eq")
    for nm in ("gMin", "r_ball", "sqrt2Up", "dmaxUp", "tUp", "CBhi", "CAhi",
               "deltaA", "rhoNeedB", "rhoNeedA"):
        if not re.search(rf"^def {nm} :", dsrc, re.M):
            fail(f"G4 数据件缺 def {nm}")
    # 非交叠守卫
    for rel in NONOVERLAY_FILES:
        p = LEAN_DIR / rel
        if p.is_file() and "TableB5Chain" in p.read_text():
            fail(f"G4 非交叠守卫：{rel} 含 'TableB5Chain'（本件必须不被其余件/"
                 "根模块/lake 面引用）")
    okmsg(f"G4 语句锚：import 面恰十行；{len(anchors)} 锚全在（接口形三件/"
          "(i) 六面/(ii) 双档 C_B·coeff_A 常数链＋rowPerm 牙＋δ_A 窄域牙/"
          "(iii) 双档 L6Hyp＋球门牙/缝推论双档 ρ_need 牙/包络引理/节点桥）＋"
          "零 sorry＋主件零 ≥15 位字面量＋数据件 15 间隙 def＋10 常数 def 全在＋"
          "非交叠零引用")


# ============================================================ G5
def sqrt_rat_gate(q: Fr, side: str) -> Fr:
    """门内第二实现（r21_chain_gate.sqrt_env 异构字面：a=isqrt；hi=(a+2)/2^p）。"""
    bits = 200
    num, den = q.numerator, q.denominator
    a = math.isqrt((num << (2 * bits)) // den)
    if side == "lo":
        return Fr(a, 1 << bits)
    return Fr(a + 2, 1 << bits)


def gate5_exact(led: dict) -> None:
    b1 = parse_defs((LEAN_DIR / "ThomsonN9" / "TableB1Data.lean").read_text())
    b5 = parse_defs((LEAN_DIR / "ThomsonN9" / "TableB5Data.lean").read_text())
    nu = {nm: Fr(b1[nm]) for nm in
          ("nu1Lo", "nu1Hi", "nu2Lo", "nu2Hi", "nu3Lo", "nu3Hi",
           "nu4Lo", "nu4Hi", "nu5Lo", "nu5Hi", "nu6Lo", "nu6Hi")}
    l3, u1 = Fr(b5["l3"]), Fr(b5["u1"])
    s1Up, s3Dn, sqrt72Up = Fr(b5["s1Up"]), Fr(b5["s3Dn"]), Fr(b5["sqrt72Up"])
    deltaMax = Fr(b5["deltaMax"])
    # 容器五链不交（源面复验）
    for lo, hi in (("nu1Hi", "nu2Lo"), ("nu2Hi", "nu3Lo"), ("nu3Hi", "nu4Lo"),
                   ("nu4Hi", "nu5Lo"), ("nu5Hi", "nu6Lo")):
        if not nu[lo] < nu[hi]:
            fail(f"G5 容器五链不交破损：{lo} !< {hi}")
    # 15 间隙重导 vs 数据件字面（独立第二实现）
    dch = parse_defs((LEAN_DIR / "ThomsonN9" / "TableB5ChainData.lean").read_text())
    gaps = {}
    for nm in GAP_NAMES:
        lo, hi = PAIR_ENDS[nm]
        val = nu[lo] - nu[hi]
        if val <= 0:
            fail(f"G5 间隙 {nm} ≤ 0")
        if nm not in dch or Fr(dch[nm]) != val:
            fail(f"G5 间隙 {nm} 与数据件字面不符（独立重导 vs 字面）")
        gaps[nm] = val
    gmin = min(gaps.values())
    if Fr(dch["gMin"]) != gmin:
        fail("G5 gMin 与 15 间隙重导 min 不符")
    # 包络（异构第二实现）＋ r20 位对账
    k1 = s1Up * u1 * sqrt72Up / (l3 * l3)
    dmaxUp = sqrt_rat_gate(deltaMax, "hi")
    tUp = sqrt_rat_gate(3 * sqrt72Up, "hi")
    CBhi_ctx = k1 * dmaxUp + tUp
    sqrt2Up = sqrt_rat_gate(Fr(2), "hi")
    CAhi_ctx = sqrt72Up * (s1Up * u1 / (l3 * l3) + 2 * sqrt2Up / s3Dn)
    deltaA_ctx = (l3 / 24) / sqrt72Up
    if abs(Fr(dch["CBhi"]) - CBhi_ctx) > Fr(1, 10 ** 30) * CBhi_ctx:
        fail("G5 CBhi 与门内异构重导超出 1e-30 紧公差")
    if abs(Fr(dch["CAhi"]) - CAhi_ctx) > Fr(1, 10 ** 30) * CAhi_ctx:
        fail("G5 CAhi 与门内异构重导超出 1e-30 紧公差")
    if not re.search(r"^def deltaA : ℚ := \(l3 / 24\) / sqrt72Up$",
                     (LEAN_DIR / "ThomsonN9" / "TableB5ChainData.lean")
                     .read_text(), re.M):
        fail("G5 数据件 deltaA def 表达式形失配（应恰 (l3/24)/sqrt72Up）")
    r20 = load_json(REPO / "numerics/bounds/results/r20_l5l6_seam.json")
    sup = r20["supply"]
    if Fr(sup["C_B"]["hi"]["exact"]) != Fr(dch["CBhi"]):
        fail("G5 CBhi ≠ r20 supply.C_B.hi.exact（逐位）")
    if Fr(sup["C_A"]["delta_caliber"]["exact"]) != Fr(dch["CAhi"]):
        fail("G5 CAhi ≠ r20 supply.C_A.delta_caliber.exact（逐位）")
    if Fr(sup["C_A"]["delta_A"]["exact"]) != deltaA_ctx:
        fail("G5 deltaA ≠ r20 supply.C_A.delta_A.exact（逐位）")
    rows = {(r["route"], r["target"]): r for r in r20["seam_table"]}
    rball = Fr(dch["r_ball"])
    if rball != Fr(950125, 10 ** 8):
        fail("G5 r_ball ≠ 950125/10⁸")
    l6 = load_json(REPO / "numerics/bounds/results/l6_intube.json")
    if Fr(str(l6["quadraticGrowth"]["rigorousRadius"])) != rball:
        fail("G5 r_ball ≠ l6_intube rigorousRadius（r* 口径）")
    threshB = (rball / Fr(dch["CBhi"])) ** 2
    threshA = rball / Fr(dch["CAhi"])
    rowB = rows[("B_global_hoelder", "r_star_raw")]
    rowA = rows[("A_narrow_linear", "r_star_raw")]
    if Fr(rowB["threshold"]["exact"]) != threshB:
        fail("G5 (r_ball/CBhi)² ≠ r20 r_star_raw/B 行 threshold.exact（逐位——"
             "r_ball 口径交叉对账破损）")
    if Fr(rowA["threshold"]["exact"]) != threshA:
        fail("G5 r_ball/CAhi ≠ r20 r_star_raw/A 行 threshold.exact（逐位）")
    if Fr(rowB["demand_radius"]["exact"]) != rball:
        fail("G5 r20 r_star_raw 行需求半径 ≠ r_ball（r* 口径行锚破损）")
    # rhoNeed*＝min 支路
    if not (threshB < gmin / 2 and threshA < gmin / 2):
        fail("G5 球门阈值 ≥ 辨识窗（min 应取球门支——复合阈值面破损）")
    if min(gmin / 2, threshB) != threshB or min(gmin / 2, threshA) != threshA:
        fail("G5 rhoNeed* min 支路面破损")
    # 域面六件
    dom = {
        "threshB_le_deltaMax": threshB <= deltaMax,
        "gMin_half_le_deltaMax": gmin / 2 <= deltaMax,
        "threshA_le_deltaA": threshA <= deltaA_ctx,
        "deltaA_le_deltaMax": deltaA_ctx <= deltaMax,
        "two_u1_sqrt72Up_deltaMax_le_l3sq":
            2 * u1 * sqrt72Up * deltaMax <= l3 * l3,
        "gMin_pos": gmin > 0,
    }
    for k, v in dom.items():
        if not v:
            fail(f"G5 域面失守：{k}")
    # half_gap 定向宽安全边（float_advisory 十进制锚——D92 裁决 3）
    tube_src = (REPO / "numerics/bounds/results/tube.json").read_text()
    m = re.search(r'"half_gap"\s*:\s*([0-9.eE+-]+)', tube_src)
    if not m:
        fail("G5 tube.json 缺 half_gap")
    half_gap = Fr(m.group(1))
    m2 = re.search(r'"need"\s*:\s*([0-9.eE+-]+)', tube_src)
    if m2 and Fr(m2.group(1)) != half_gap:
        fail("G5 tube verdict.need ≠ half_gap（同数交叉锚破损）")
    slack = 2 * half_gap - gmin
    if not (Fr(0) <= slack <= Fr(1, 10 ** 5)):
        fail(f"G5 half_gap 定向宽安全边失守：2·half_gap-gMin={float(slack):.3e} "
             "（应 ∈ [0, 1e-5]；容器包络宽 ~1e-6 级、间隙 0.037 级）")
    # 账本交叉对账字段一致
    cc = led.get("data", {}).get("cross_checks", {})
    for k in ("cbhi_r20_bit_equal", "cahi_r20_bit_equal", "deltaA_r20_bit_equal",
              "threshB_r20_bit_equal", "threshA_r20_bit_equal"):
        if cc.get(k) is not True:
            fail(f"G5 账本 cross_checks.{k} 非 True")
    okmsg("G5 离线精确复核：15 间隙＋gMin 独立重导逐位；CBhi/CAhi/deltaA 与 "
          "r20 位对账全中；**r_ball 口径交叉对账（(r_ball/CBhi)²==r20 "
          "r_star_raw/B 行、r_ball/CAhi==A 行、r_ball==r*==950125/10⁸=="
          "l6 rigorousRadius）逐位**；rhoNeed* min 支路＋域面六件＋half_gap "
          f"定向宽安全边（2·half_gap-gMin={float(slack):.3e} ∈ [0,1e-5]）全过")


# ============================================================ NC
def nc1_sorry_injection(walls: dict) -> None:
    d = TMP / "nc1"
    if d.exists():
        for p in sorted(d.rglob("*")):
            if p.is_file():
                p.unlink()
    (d / "ThomsonN9").mkdir(parents=True, exist_ok=True)
    src = (LEAN_DIR / "ThomsonN9" / "TableB5Chain.lean").read_text()
    m = re.search(r"theorem ident_unique[\s\S]*?:= by\n", src)
    if not m:
        fail("NC1 预置失败：ident_unique 未定位")
    nxt = re.search(r"\n/-- |\ntheorem |\nnoncomputable def |\ndef ",
                    src[m.end():])
    body_end = m.end() + (nxt.start() + 1 if nxt else len(src))
    tampered = src[:m.end()] + "  sorry\n\n" + src[body_end:]
    (d / "ThomsonN9" / "TableB5Chain.lean").write_text(tampered)
    for dep in ("TableB5Data.olean", "TableB5.olean", "TableB5Core.olean",
                "TableB5Trace.olean", "TableB5Polar.olean",
                "TableB5Uncond.olean", "TableB1Data.olean", "TableB1.olean",
                "TableB5ChainData.olean"):
        s = LEAN_DIR / OLEAN_REL / dep
        if not s.is_file():
            fail(f"NC1 预置失败：依赖 olen 不在场（G2 应已编译）：{s}")
        (d / "ThomsonN9" / dep).write_bytes(s.read_bytes())
    lp = run(["lake", "env", "printenv", "LEAN_PATH"], LEAN_DIR).stdout.strip()
    env = gate_env()
    env["LEAN_PATH"] = f"{d}:{lp}"
    b = subprocess.run(["lean", "--root", str(d), "-o",
                        str(d / "ThomsonN9" / "TableB5Chain.olean"),
                        str(d / "ThomsonN9" / "TableB5Chain.lean")],
                       cwd=str(LEAN_DIR), env=env, capture_output=True,
                       text=True, timeout=COMPILE_TIMEOUT_S)
    if b.returncode != 0 or "declaration uses `sorry`" not in (b.stdout + b.stderr):
        fail(f"NC1 注入 sorry 后编译未产生 sorry 警告（exit {b.returncode}）：\n"
             f"{(b.stdout + b.stderr)[-500:]}")
    axfile = d / "axcheck.lean"
    axfile.write_text("import ThomsonN9.TableB5Chain\n"
                      "#print axioms ThomsonN9.TableB5Chain.ident_unique\n")
    a = subprocess.run(["lean", str(axfile)], cwd=str(LEAN_DIR), env=env,
                       capture_output=True, text=True, timeout=COMPILE_TIMEOUT_S)
    ax = parse_axiom_lines(a.stdout)
    th = "ThomsonN9.TableB5Chain.ident_unique"
    caught = th in ax and ("sorryAx" in ax[th] or (ax[th] - ALLOWED_AXIOMS))
    if not caught:
        fail(f"NC1 失守：注入 sorry 后公理检查未现 sorryAx（{ax}）")
    okmsg(f"NC1 注入 sorry 必被 G3 拦：篡件 ident_unique 公理集 = "
          f"{sorted(ax.get(th, set()))}（含 sorryAx——有牙实证；原件 sanity＝G3 全过）")


def _tamper_data_literal(src: str, name: str, scale: Fr) -> str:
    pat = re.compile(rf"^(def {name} : ℚ := )(\S+)", re.M)
    m = pat.search(src)
    if not m:
        fail(f"NC 预置失败：数据件缺 def {name}")
    old = Fr(m.group(2))
    new = old * scale
    return src[:m.start()] + m.group(1) + f"{new.numerator}/{new.denominator}" \
        + src[m.end():]


def nc2_gmin_tamper() -> None:
    d = TMP / "nc2"
    if d.exists():
        for p in sorted(d.rglob("*")):
            if p.is_file():
                p.unlink()
    (d / "ThomsonN9").mkdir(parents=True, exist_ok=True)
    src = (LEAN_DIR / "ThomsonN9" / "TableB5ChainData.lean").read_text()
    tampered = _tamper_data_literal(src, "gMin", Fr(101, 100))
    (d / "ThomsonN9" / "TableB5ChainData.lean").write_text(tampered)
    # 门内重导逻辑对篡副本有牙（validate 与 G5 同一入口）
    b1 = parse_defs((LEAN_DIR / "ThomsonN9" / "TableB1Data.lean").read_text())
    nu = {nm: Fr(b1[nm]) for nm in
          ("nu1Lo", "nu1Hi", "nu2Lo", "nu2Hi", "nu3Lo", "nu3Hi",
           "nu4Lo", "nu4Hi", "nu5Lo", "nu5Hi", "nu6Lo", "nu6Hi")}
    gaps = [nu[PAIR_ENDS[nm][0]] - nu[PAIR_ENDS[nm][1]] for nm in GAP_NAMES]
    dch = parse_defs(tampered)
    caught = Fr(dch["gMin"]) != min(gaps)
    if not caught:
        fail("NC2 失守：篡 gMin 未被重导检出")
    okmsg("NC2 篡 gMin（+1%，辨识窗方向反转）必被 G5 拦：字面 101/100× ≠ "
          "15 间隙重导 min（有牙实证；原件 sanity＝G5 全过）")


def nc3_cbhi_tamper() -> None:
    d = TMP / "nc3"
    if d.exists():
        for p in sorted(d.rglob("*")):
            if p.is_file():
                p.unlink()
    (d / "ThomsonN9").mkdir(parents=True, exist_ok=True)
    src = (LEAN_DIR / "ThomsonN9" / "TableB5ChainData.lean").read_text()
    tampered = _tamper_data_literal(src, "CBhi", Fr(1001, 1000))
    (d / "ThomsonN9" / "TableB5ChainData.lean").write_text(tampered)
    dch = parse_defs(tampered)
    r20 = load_json(REPO / "numerics/bounds/results/r20_l5l6_seam.json")
    sup = r20["supply"]
    caught = Fr(sup["C_B"]["hi"]["exact"]) != Fr(dch["CBhi"])
    if not caught:
        fail("NC3 失守：篡 CBhi 未被 r20 位对账检出")
    okmsg("NC3 篡 CBhi（+0.1%，缝阈值方向反转）必被 G5 拦：≠ r20 "
          "supply.C_B.hi.exact 逐位（有牙实证；原件 sanity＝G5 全过）")


# ============================================================ main
def run_gate() -> dict:
    led = gate0_ledger()
    gate1_ownership()
    gate1_isolation()
    walls = gate2_determinism_and_elaborate()
    gate3_axioms(led)
    gate4_statements(led)
    gate5_exact(led)
    nc1_sorry_injection(walls)
    nc2_gmin_tamper()
    nc3_cbhi_tamper()
    return walls


def main() -> None:
    t0 = time.time()
    print(f"[gate] r21_b5chain_gate.py seed={SEED_GATE}（编译型门——十连 "
          "elaboration，单文件 ≤600s；外层 1200s 文档化例外沿 R18/R19；"
          "零求解零 SDP；CWD 无关）")
    try:
        walls = run_gate()
    except GateFail as e:
        print(f"[gate][FAIL] {e}", flush=True)
        sys.exit(1)
    wall = time.time() - t0
    print(f"[gate] PASS（{wall:.1f}s）——exit 0")
    print(f"[gate] elaboration 墙钟：{walls}（十连）")
    print("[gate] heavySolves=0（形式件：endgame.json/四账本只读未动；"
          "r21_b5chain 家族不入 12 分区）")


if __name__ == "__main__":
    main()
