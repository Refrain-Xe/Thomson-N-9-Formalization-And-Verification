#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r18b_dperp_gate.py — R18B B5c 步骤 6 缺口研究件（D77 裁决 2 证据与方向
供件）验收门（G1–G5＋负对照 NC）。

任务书口径（r18b-dperp-gap-study，campaign dwfrun-f9904baf 第 13 轮）：
零 Lean 件入库、零求解、纯 notes＋/tmp 探针（R15C/R16B/R17B 同款），与 R18A
文件集零交叠。产出件 notes/dperp-gap-study.md（§i 反射族反例机器核验＋§ii
块恒等式探针＋§iii σ₃(Y) 自举路线＋§iv ½-Hölder 面与三路线评估）＋本门＋
嵌套 CWD 包装器＋decisions D79。本门为纯 python3 文本＋git 状态＋Fraction
重算检查（零 Lean 编译、零求解、零网络）。

检查面（全部确定性；seed 20261018 记档——Fraction 重算的确定性口径）：
  G1 零入库守卫：git status --porcelain＋git diff HEAD --name-only 的全部
     改动路径 ⊆ 本任务自有件（＋r18 家族放行层〔r18 pattern＋R18A/R18C
     在途件＋轮次文档三件——D68-3/D77-3 同款〕）；formal/ 与 references/
     certificates/ 挑战件目录零改动（单独响亮报错）；四账本
     （m9_campaign/m10_campaign/hermite_v2_campaign/typed_ladder）＋
     endgame.json＋l4.json（只读评估面）sha256 冻结锚。
  G2 反例 Fraction 门内独立重算（第三实现，与 /tmp/r18b_counterexample.py
     零共享代码）：从 notes §i.2 的 X-FRACTIONS 块（BEGIN/END 标记）解析
     9×3 有理 X 与 Q̃ = diag(−1,1,1)，双路重算——(α) Gram＝Σ zip 乘积 vs
     (β) Gram＝逐分量乘加；frob D∥²＝逐元平方和 vs 闭式 4·Σᵢx_{i0}²；
     det＝Bareiss 算法（vs /tmp 的 Gauss-Jordan/cofactor 两路）——核验
     η == 0（81 元全零）、δ == 0、行单位 9/9×2、det ≠ 0、frob D∥² > 0 =
     (σ₁β)²；并 cross-check notes 记录的 det/frob D∥² 两个字面与重算逐位
     相等（门内独立重算的『确定性重跑一致』机器面）。
  G3 /tmp 探针日志在盘非零字节（R17B G3 口径）：notes 附录 B 全部 12 条
     /tmp 路径逐一存在且 size > 0——每条『已跑』声明必须带可核验日志。
  G4 notes 锚：heavySolves = 0 字面／X-FRACTIONS 标记对／反例数值字面
     （det 与 frob D∥² 两字面）／seed 20261018 字面／三路线在档
     （σ₃(Y) 自举＋E(I−P₀)=Y·D_⊥ᵀ 面＋谱扰动 Weyl 型三标记）／
     越权陈述零命中（『已证』『已 Lean 化』『证明已完成』『本体入 Lean』
     模式 regex 全文件零命中——探针≠证明，R15C/R16B/R17B 同款）。
  G5 零求解正则：本任务新产物（notes＋门＋包装器）零正 solve 字段
     （solve_s/solve_seconds/total_solve_s/heavy_solves 域值全为 0 或缺席）。
  NC 篡 notes 反例数字：/tmp 副本篡 frob D∥² 与 det 两字面（数字面替换）
     ⇒ G4 字面锚必 FAIL（双棱）＋G2 cross-check 必 FAIL（第三棱）；原件
     sanity：G2/G4 对真件全过。

用法（CWD 无关）：
  python3 numerics/bounds/r18b_dperp_gate.py              # 全门（exit 0 = 过）
  python3 numerics/bounds/r18b_dperp_gate.py --file PATH  # 对副本跑 G2/G4/G5（NC 用）
  python3 numerics/bounds/r18b_dperp_gate.py --no-nc      # 跳过 NC
"""
from __future__ import annotations

import argparse
import hashlib
import re
import subprocess
import sys
import time
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]                        # thomson-n9/
STUDY_DEFAULT = REPO / "notes" / "dperp-gap-study.md"
GATE_REL = "numerics/bounds/r18b_dperp_gate.py"
WRAPPER_REL = "thomson-n9/numerics/bounds/r18b_dperp_gate.py"   # 嵌套 CWD 包装器
STUDY_REL = "notes/dperp-gap-study.md"
DECISIONS_REL = "notes/decisions.md"

SEED_GATE = 20261018                          # R18 各门统一 seed（Fraction 重算确定性口径）

OWNED = {STUDY_REL, GATE_REL, WRAPPER_REL, DECISIONS_REL}

# r18 家族放行层（D68-3/D77-3 同款：R18A 已提交件不在 git status 面；
# R18C 在途件＋轮次文档三件——本任务与 R18A/R18C 文件集零交叠）。
PARALLEL_FAMILY = [
    r"^numerics/bounds/r18[a-z0-9_]*(\.py|/)",
    r"^numerics/bounds/results/r18[a-z0-9_]*(\.json|/)",
    r"^thomson-n9/numerics/bounds/r18[a-z0-9_]*(\.py|/)",
    r"^notes/decisions\.md$",
    r"^notes/dperp-gap-study\.md$",
    r"^notes/tableb-lean\.md$",
    r"^numerics/bounds/endgame_gate\.py$",
    r"^(GAP-REPORT|PROGRESS)\.md$",
]

# 硬禁区（零改动，单独响亮报错）：formal/ 全树、references/、certificates/。
HARD_DENIED_PREFIXES = ("formal/", "references/", "certificates/")

# 只读冻结件 sha256 锚（四账本＋endgame.json＋l4.json——只读评估面）。
FROZEN_SHA256 = {
    "numerics/bounds/results/endgame.json":
        "86863a09bf84e950e85fc5f902bc2b4046a87f06703bd782e5148fc119afd69f",
    "numerics/bounds/results/m9_campaign.json":
        "583e5dd11356472b47e8d9e8fac7865ec434800c99919df31d247f30b260114a",
    "numerics/bounds/results/m10_campaign.json":
        "9f6cf91c3adf1e0908c2f41084e53380237ca58840f82bbdcd720c54421c23ed",
    "numerics/bounds/results/hermite_v2_campaign.json":
        "4ebcbedd1e8dc300ab9e6bc0e3b756c75b7f4cbe4fe00675719217f90ea41765",
    "numerics/bounds/results/typed_ladder.json":
        "78fc1102e6d864115204fae21959f3704841aa688b07a30a9567bbdca4683318",
    "numerics/bounds/results/l4.json":
        "9f588a3b61c562d8574523d57ac5e868a893b62f4db52509280b9c090300fb96",
}

# G3：notes 附录 B 全部 /tmp 路径（在盘非零字节逐一核验）。
TMP_EVIDENCE = [
    "/tmp/r18b_probe1_block_id.lean",
    "/tmp/r18b_probe1_block_id.log",
    "/tmp/r18b_probe2_bootstrap.lean",
    "/tmp/r18b_probe2_bootstrap.log",
    "/tmp/r18b_counterexample.py",
    "/tmp/r18b_counterexample.log",
    "/tmp/r18b_closure_study.py",
    "/tmp/r18b_closure_study.log",
    "/tmp/r18b_det_rerun1.log",
    "/tmp/r18b_det_rerun2.log",
    "/tmp/r18b_det_rerun3.log",
    "/tmp/r18b_final_pass.log",
    "/tmp/r18b_final_run.sh",
]

# G2：反例记录字面（notes §i.2）——cross-check 双锚。
DET_LITERAL = "27644548911799213067871202087424/1250488850331411254353184573409"
FDPAR_LITERAL = "204442845285416922537088/16856636797887840591561"

# G4：三路线标记（在档锚）。
ROUTE_ANCHORS = ["σ₃(Y) 自举", "E(I−P₀)=Y·D_⊥ᵀ 面", "谱扰动 Weyl 型"]

# G4：越权陈述模式（探针件禁止宣称证明完成；R15C/R16B/R17B 同款）。
OVERREACH_PATTERNS = [
    r"已证",
    r"已\s*Lean\s*化",
    r"已形式化",
    r"证明已完成",
    r"本体已完成",
    r"已证毕",
]

# G5：solve 字段正则（新产物零正 solve 字段）。
SOLVE_FIELD_RE = re.compile(
    r'(?:solve_s|solve_seconds|total_solve_s|heavy_solves)["\']?\s*[:=]\s*["\']?'
    r'([0-9]+(?:\.[0-9]+)?)', re.I)

X_BLOCK_RE = re.compile(r"<!--X-FRACTIONS-BEGIN-->(.*?)<!--X-FRACTIONS-END-->", re.S)
ROW_RE = re.compile(r"\[\s*(-?\d+/\d+)\s*,\s*(-?\d+/\d+)\s*,\s*(-?\d+/\d+)\s*\]")


class GateFail(Exception):
    pass


def log(msg: str) -> None:
    print(msg, flush=True)


def sha256_of(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def parse_X(text: str):
    m = X_BLOCK_RE.search(text)
    if not m:
        raise GateFail("G2 FAIL：notes 无 X-FRACTIONS 标记块（BEGIN/END）")
    if "diag(-1,1,1)" not in m.group(1):
        raise GateFail("G2 FAIL：X 块内无 Q̃ = diag(-1,1,1) 字面")
    rows = [(Fr(a), Fr(b), Fr(c)) for a, b, c in ROW_RE.findall(m.group(1))]
    if len(rows) != 9:
        raise GateFail(f"G2 FAIL：X 行数 {len(rows)} != 9")
    return rows


def gram_alpha(rows):
    """Gram 实现 α：zip 逐分量乘积求和（Σ zip(*pair, mul)）。"""
    from operator import mul
    return [[sum(map(mul, r1, r2)) for r2 in rows] for r1 in rows]


def gram_beta(rows):
    """Gram 实现 β：显式下标三分量乘加。"""
    out = []
    for r1 in rows:
        row = []
        for r2 in rows:
            s = Fr(0)
            for k in range(3):
                s = s + r1[k] * r2[k]
            row.append(s)
        out.append(row)
    return out


def det_bareiss(Min):
    """3×3 Fraction Bareiss 行列式（第三实现；与 /tmp 的 Gauss-Jordan/cofactor 零共享）。"""
    n = len(Min)
    M = [row[:] for row in Min]
    prev = Fr(1)
    sign = 1
    for k in range(n - 1):
        if M[k][k] == 0:
            piv = next((r for r in range(k + 1, n) if M[r][k] != 0), None)
            if piv is None:
                return Fr(0)
            M[k], M[piv] = M[piv], M[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) / prev
        prev = M[k][k]
    return sign * M[n - 1][n - 1]


def check_g2(text: str) -> str:
    rows = parse_X(text)
    Y = [(-a, b, c) for a, b, c in rows]                  # Y := X·diag(−1,1,1)
    # 行单位（X 与 Y 各 9）
    for name, M in (("X", rows), ("Y", Y)):
        for i, r in enumerate(M):
            s = Fr(0)
            for x in r:
                s = s + x * x
            if s != 1:
                raise GateFail(f"G2 FAIL：{name} 行 {i} 自点积 {s} != 1（行单位被违）")
    # Gram 双实现逐位相等 ⟹ η == 0、δ == 0
    GXa, GYa = gram_alpha(rows), gram_alpha(Y)
    GXb, GYb = gram_beta(rows), gram_beta(Y)
    if GXa != GXb or GYa != GYb:
        raise GateFail("G2 FAIL：Gram 双实现（α/β）不一致")
    diffs = [GYa[i][j] - GXa[i][j] for i in range(9) for j in range(9)]
    if any(d != 0 for d in diffs):
        raise GateFail("G2 FAIL：G_Y != G_X（81 元非全零——反例核验意外失败）")
    eta_sq = sum((d * d for d in diffs), Fr(0))
    delta = max((abs(GYa[i][j] - GXa[i][j]) for i in range(9) for j in range(9) if i != j),
                default=Fr(0))
    if eta_sq != 0 or delta != 0:
        raise GateFail(f"G2 FAIL：η² = {eta_sq}、δ = {delta}（须全零）")
    # det（Bareiss 第三实现）——S = XᵀX（3×3）：S[i][j] = Σ_k X[k][i]·X[k][j]
    S = [[sum(rows[k][i] * rows[k][j] for k in range(9)) for j in range(3)]
         for i in range(3)]
    det = det_bareiss(S)
    if det == 0:
        raise GateFail("G2 FAIL：det(XᵀX) == 0（Bareiss）——β 分母良定义面被违")
    mrec = re.search(r"det\(XᵀX\) = \*\*(\S+)\*\*", text)
    if not mrec:
        raise GateFail("G2 FAIL：notes 无『det(XᵀX) = **…**』记录字面（转录锚缺位）")
    if Fr(mrec.group(1)) != det:
        raise GateFail(f"G2 FAIL：notes 记录 det {mrec.group(1)} != 门内重算 {det}"
                       "（反例数字被篡或转录漂移）")
    if Fr(DET_LITERAL) != det:
        raise GateFail("G2 FAIL：门内常量 det 锚与重算不符（门自身漂移）")
    # frob D∥² 双路（逐元平方和 vs 闭式 4·Σ x_{i0}²）
    fd1 = sum(((Y[i][k] - rows[i][k]) ** 2 for i in range(9) for k in range(3)), Fr(0))
    fd2 = 4 * sum((rows[i][0] ** 2 for i in range(9)), Fr(0))
    if fd1 != fd2:
        raise GateFail(f"G2 FAIL：frob D∥² 双路不一致 {fd1} vs {fd2}")
    if not fd1 > 0:
        raise GateFail("G2 FAIL：frob D∥² ≤ 0（反例缺口本体消失）")
    mrec2 = re.search(r"frob D_∥² = \*\*(\S+)\*\*", text)
    if not mrec2:
        raise GateFail("G2 FAIL：notes 无『frob D_∥² = **…**』记录字面（转录锚缺位）")
    if Fr(mrec2.group(1)) != fd1:
        raise GateFail(f"G2 FAIL：notes 记录 frob D∥² {mrec2.group(1)} != 门内重算"
                       f" {fd1}（反例数字被篡或转录漂移）")
    if Fr(FDPAR_LITERAL) != fd1:
        raise GateFail("G2 FAIL：门内常量 frob D∥² 锚与重算不符（门自身漂移）")
    return (f"G2 反例门内独立重算（第三实现 Bareiss/α/β）：行单位 9/9×2 ✓、"
            f"η == δ == 0 ✓、det = {det} ≠ 0 ✓、frob D∥² = {fd1} > 0 = (σ₁β)²"
            "（λ₁β² = 0）✓——notes 两记录字面 cross-check 逐位相等 ✓")


def check_g3() -> str:
    missing = [p for p in TMP_EVIDENCE if not (Path(p).is_file()
               and Path(p).stat().st_size > 0)]
    if missing:
        raise GateFail(f"G3 FAIL：/tmp 证据缺席或零字节：{missing}")
    return f"G3 /tmp 探针日志在盘非零字节：{len(TMP_EVIDENCE)} 条全过"


def check_g4(text: str) -> str:
    if "heavySolves = 0" not in text:
        raise GateFail("G4 FAIL：无 heavySolves = 0 字面")
    if "<!--X-FRACTIONS-BEGIN-->" not in text or "<!--X-FRACTIONS-END-->" not in text:
        raise GateFail("G4 FAIL：无 X-FRACTIONS 标记对")
    if DET_LITERAL not in text:
        raise GateFail(f"G4 FAIL：反例数值字面（det {DET_LITERAL}）不在档")
    if FDPAR_LITERAL not in text:
        raise GateFail(f"G4 FAIL：反例数值字面（frob D∥² {FDPAR_LITERAL}）不在档")
    if str(SEED_GATE) not in text:
        raise GateFail("G4 FAIL：seed 20261018 字面不在档")
    for a in ROUTE_ANCHORS:
        if a not in text:
            raise GateFail(f"G4 FAIL：三路线标记缺位：{a}")
    for pat in OVERREACH_PATTERNS:
        if re.search(pat, text):
            raise GateFail(f"G4 FAIL：越权陈述命中模式 {pat}（探针≠证明）")
    return ("G4 notes 锚：heavySolves = 0 ✓＋X-FRACTIONS 标记对 ✓＋det/frob D∥²"
            " 反例字面 ✓＋seed 20261018 ✓＋三路线标记（σ₃(Y) 自举／"
            "E(I−P₀)=Y·D_⊥ᵀ 面／谱扰动 Weyl 型）✓＋越权陈述零命中 ✓")


def check_g5(texts: dict) -> str:
    for name, t in texts.items():
        for m in SOLVE_FIELD_RE.finditer(t):
            if Fr(m.group(1)) > 0:
                raise GateFail(f"G5 FAIL：{name} 含正 solve 字段 {m.group(0)!r}")
    return "G5 零求解正则：新产物零正 solve 字段 ✓"


def check_g1() -> str:
    try:
        st = subprocess.check_output(["git", "status", "--porcelain"],
                                     cwd=str(REPO), text=True, timeout=60)
        df = subprocess.check_output(["git", "diff", "HEAD", "--name-only"],
                                     cwd=str(REPO), text=True, timeout=60)
    except Exception as e:                                   # pragma: no cover
        raise GateFail(f"G1 FAIL：git 状态读取失败：{e}")
    paths = set()
    for line in st.splitlines():
        if not line:
            continue
        raw = line[3:]                     # porcelain v1：XY 两字符＋空格＋路径
        if " -> " in raw:                  # 重命名行取新路径
            raw = raw.split(" -> ")[-1]
        paths.add(raw.strip('"'))
    paths |= {l.strip() for l in df.splitlines() if l.strip()}
    hard = [p for p in paths if any(p.startswith(pre) for pre in HARD_DENIED_PREFIXES)]
    if hard:
        raise GateFail(f"G1 FAIL：硬禁区改动（formal/references/certificates）：{hard}")
    foreign = []
    for p in paths:
        if p in OWNED:
            continue
        if any(re.match(pat, p) for pat in PARALLEL_FAMILY):
            continue
        foreign.append(p)
    if foreign:
        raise GateFail(f"G1 FAIL：非本任务且非 r18 家族放行层的改动：{sorted(foreign)}")
    frozen_bad = []
    for rel, want in FROZEN_SHA256.items():
        p = REPO / rel
        if not p.is_file():
            frozen_bad.append(f"{rel}（缺席）")
        elif sha256_of(p) != want:
            frozen_bad.append(f"{rel}（sha256 漂移）")
    if frozen_bad:
        raise GateFail(f"G1 FAIL：只读冻结件被动：{frozen_bad}")
    formal_changed = [p for p in paths if p.startswith("formal/")]
    return (f"G1 零入库守卫：改动 {len(paths)} 件全部 ⊆ 自有件∪r18 家族放行层 ✓；"
            f"formal/ 零改动（{len(formal_changed)} 件）✓；四账本＋endgame.json＋"
            f"l4.json sha256 冻结锚 {len(FROZEN_SHA256)} 件全过 ✓")


def nc_tamper() -> str:
    """NC：篡 notes 反例数字（frob D∥² 与 det 两字面的数字面）⇒ G4 必拦＋
    G2 cross-check 必拦；原件 sanity 全过。"""
    src = STUDY_DEFAULT.read_text(encoding="utf-8")
    if FDPAR_LITERAL not in src or DET_LITERAL not in src:
        raise GateFail("NC FAIL：原件本已缺反例字面（前置异常）")
    tam = src.replace(FDPAR_LITERAL,
                      "204442845285416922537088/16856636797887840591562"
                      ).replace(DET_LITERAL,
                                "27644548911799213067871202087424/1250488850331411254353184573410")
    # G4 棱
    try:
        check_g4(tam)
        raise GateFail("NC FAIL：篡 frob D∥²/det 字面后 G4 未检出（门失效）")
    except GateFail as e:
        if "NC FAIL" in str(e):
            raise
        log(f"[nc  ] G4 检出篡改副本 ✓（{str(e)[:60]}…）")
    # G2 棱（cross-check）
    try:
        check_g2(tam)
        raise GateFail("NC FAIL：篡 det 字面后 G2 cross-check 未检出（门失效）")
    except GateFail as e:
        if "NC FAIL" in str(e):
            raise
        log(f"[nc  ] G2 检出篡改副本 ✓（{str(e)[:60]}…）")
    # 原件 sanity
    check_g4(src)
    check_g2(src)
    return "NC 双棱：篡反例数字 ⇒ G4 字面锚＋G2 cross-check 均检出；原件 sanity 全过 ✓"


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--file", default=None,
                    help="对指定 notes 副本跑 G2/G4/G5（NC 用；G1/G3 仍对真仓/真盘）")
    ap.add_argument("--no-nc", action="store_true")
    args = ap.parse_args()
    t0 = time.time()
    study = Path(args.file).resolve() if args.file else STUDY_DEFAULT
    try:
        if not study.is_file():
            raise GateFail(f"notes 件不在位：{study}")
        text = study.read_text(encoding="utf-8")
        if len(text.strip()) < 5000:
            raise GateFail(f"notes 件过短（{len(text)} 字符 < 5000，疑似占位）")
        log(f"[gate] R18B dperp-gap-study 门启动（seed {SEED_GATE}，对象 {study}）")
        log(f"[gate][ok] {check_g1()}")
        log(f"[gate][ok] {check_g2(text)}")
        log(f"[gate][ok] {check_g3()}")
        log(f"[gate][ok] {check_g4(text)}")
        wrapper = REPO / WRAPPER_REL
        texts = {"notes": text}
        if wrapper.is_file():
            texts["wrapper"] = wrapper.read_text(encoding="utf-8")
        log(f"[gate][ok] {check_g5(texts)}")
        if not args.no_nc:
            log(f"[gate][ok] {nc_tamper()}")
        wall = time.time() - t0
        print(f"[gate] PASS（{wall:.1f}s）——exit 0", flush=True)
    except GateFail as e:
        print(f"[gate][FAIL] {e}", flush=True)
        sys.exit(1)


if __name__ == "__main__":
    main()
