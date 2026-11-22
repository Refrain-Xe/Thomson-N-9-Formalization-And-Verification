#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""r10_stageb_gate.py — R10B stageb-scope 验收门（G1–G3 ＋ 负对照 NC1/NC2）.

任务书口径（D38 裁决 3）：Lean Stage B 范围件 notes/stageb-scope.md 的五节
正文（§0–§4）＋§5 关系节全部在档且关键内容锚在位（G1）；文档所引机器事实
由本门对盘上文件独立重算核对（G2）；文档所引证书计数/尺寸与盘上 glob 实测
一致（G3）。零求解零 SDP 零 Lean 构建；全部检查确定性（无随机路径；
种子 20261012 按惯例记档）。

检查面：
  G1 文档六节锚（§0 冻结命题/§1 三层分工/§2 结构定理清单与依赖序/
     §3 M0/M1 先行方案/§4 环境前提与工程量分档/§5 与 campaign 路线关系）
     ＋关键内容锚（恰 4 处 sorry/160/168/175/183/四定理名/189/8/23.625/
     bound_exact/pin_hashes/不承诺/25.759986531/check.sh/RC1/RC2/
     D34 裁决 5② 等）
  G2 机器事实核（全部本门独立重算，不信任文档）：
     (a) ThomsonN9.lean 逐行 stripped=='sorry' 计数==4 且行号==[160,168,175,183]，
         四定理名以 `^theorem thomson_nine(_M0|_M1|_unique)?\b` 在档；
     (b) lp.json bound_exact 以 Fraction 解析 > 189/8 且 ≤ E*+1e-6，
         E* 只读 thomson-workflow/data/energies.json energies[9].value；
     (c) 文档所引 LP 界（repr(float(bound_exact)) 与 lp.json bound 字段串）
         与盘上 lp.json 逐位一致（NC2 靶）；
     (d) formal/lean/scripts/pin_hashes.sh 与 check.sh 在盘；
     (e) which lake/lean/elan（shutil.which）与已入账 ledger
         results/r10_stageb_env_ledger.json 对比打印——informational，
         不作 pass 判据（不一致只 [info] 警告不 fail）。
  G3 文档所引证书计数（27 份）与逐份字节数、总字节数与盘上
     glob certificates/*.json 实测一致（逐份精确比对）。
  NC1 /tmp 文档副本 sorry 数改 5（「恰 4 处 sorry」→「恰 5 处 sorry」）
     ⇒ G1 失配 exit 1（自跑检出；未篡改 /tmp 副本 exit 0 作路由 sanity）
  NC2 /tmp 副本 LP 界引 25.7（25.72949096219507→25.7）⇒ G2 失配 exit 1

用法（thomson-n9 下；CWD 无关——全部路径自 __file__ 推导）：
  python3 numerics/bounds/r10_stageb_gate.py                 # 全门（exit 0 = 过）
  python3 numerics/bounds/r10_stageb_gate.py --doc PATH      # 对指定文档副本跑门（NC 用）
  python3 numerics/bounds/r10_stageb_gate.py --no-nc         # 跳过 NC1/NC2（NC 子进程用）
"""
from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
REPO = HERE.parents[1]                 # thomson-n9/
CAMPAIGN_ROOT = REPO.parent            # 八电子在球面的分布/

SEED_GATE = 20261012                   # 惯例记档；本门无随机路径（确定性）
E_TOL = Fraction(1, 1000000)           # 1e-6（铁律：下界 ≤ E*+1e-6）
M1_TARGET = Fraction(189, 8)           # 23.625

DOC_DEFAULT = REPO / "notes" / "stageb-scope.md"
LEAN_CHAL = REPO / "formal" / "lean" / "ComparatorChallenges" / "ThomsonN9.lean"
LP_JSON = RESULTS / "lp.json"
PIN_HASHES = REPO / "formal" / "lean" / "scripts" / "pin_hashes.sh"
CHECK_SH = REPO / "formal" / "lean" / "scripts" / "check.sh"
ENERGIES = CAMPAIGN_ROOT / "thomson-workflow" / "data" / "energies.json"
CERTS_DIR = REPO / "certificates"
ENV_LEDGER = RESULTS / "r10_stageb_env_ledger.json"

# G1：六节锚（五节正文 §0–§4 ＋ §5 关系节）
SECTION_ANCHORS = [
    "§0 冻结命题",
    "§1 三层分工",
    "§2 结构定理清单与依赖序",
    "§3 M0/M1 先行方案",
    "§4 环境前提与工程量分档",
    "§5 与 campaign 路线关系",
]
# G1：关键内容锚（子串；NC1 篡改「恰 4 处 sorry」即失配）
CONTENT_ANCHORS = [
    "恰 4 处 sorry",
    "160/168/175/183",
    "thomson_nine_M0",
    "thomson_nine_M1",
    "thomson_nine_unique",
    "thomson_nine",
    "189/8",
    "23.625",
    "bound_exact",
    "pin_hashes",
    "check.sh",
    "不承诺",
    "结构定理层",
    "证书数据层",
    "advisory",
    "exact.py",
    "25.759986531",
    "RC1",
    "RC2",
    "D34 裁决 5②",
    "三层分工",
]

SORRY_LINES_EXPECTED = [160, 168, 175, 183]
THEOREM_PATTERNS = [
    r"^theorem\s+thomson_nine_M0\b",
    r"^theorem\s+thomson_nine_M1\b",
    r"^theorem\s+thomson_nine\b",
    r"^theorem\s+thomson_nine_unique\b",
]


def fail(msg: str) -> None:
    print(f"[gate][FAIL] {msg}", flush=True)
    sys.exit(1)


def okmsg(msg: str) -> None:
    print(f"[gate][ok] {msg}", flush=True)


def jload(p: Path):
    return json.loads(p.read_text())


# ---------------------------------------------------------------- G1
def check_g1(doc_text: str) -> None:
    for a in SECTION_ANCHORS:
        if a not in doc_text:
            fail(f"G1 范围文档缺节锚：{a}")
    for a in CONTENT_ANCHORS:
        if a not in doc_text:
            fail(f"G1 范围文档缺内容锚：{a}")
    # 「恰 4 处 sorry」锚的严格 regex（NC1 靶位：改成 5 即此处失配）
    if not re.search(r"恰 4 处 sorry", doc_text):
        fail("G1 范围文档缺「恰 4 处 sorry」宣称（regex）")
    okmsg("G1 六节锚＋关键内容锚全在（恰 4 处 sorry/160/168/175/183/四定理名/"
          "189/8/23.625/bound_exact/pin_hashes/不承诺/25.759986531/RC1/RC2/"
          "D34 裁决 5② 等）")


# ---------------------------------------------------------------- G2
def load_e_star() -> Fraction:
    """E* 只读 thomson-workflow/data/energies.json energies[9].value。"""
    if not ENERGIES.exists():
        fail(f"G2 参考能量文件不在档（只读）：{ENERGIES}")
    d = jload(ENERGIES)
    es = d["energies"]
    e9 = es["9"] if isinstance(es, dict) else es[9]
    return Fraction(str(e9["value"]))


def check_g2(doc_text: str) -> Fraction:
    # (a) Lean 冻结件机器事实
    if not LEAN_CHAL.exists():
        fail(f"G2 冻结挑战件不在档：{LEAN_CHAL}")
    lines = LEAN_CHAL.read_text().splitlines()
    sorry_lines = [i + 1 for i, ln in enumerate(lines) if ln.strip() == "sorry"]
    if len(sorry_lines) != 4:
        fail(f"G2 ThomsonN9.lean sorry 计数=={len(sorry_lines)}≠4（行号 {sorry_lines}）")
    if sorry_lines != SORRY_LINES_EXPECTED:
        fail(f"G2 ThomsonN9.lean sorry 行号 {sorry_lines}≠{SORRY_LINES_EXPECTED}")
    for pat in THEOREM_PATTERNS:
        if not re.search(pat, LEAN_CHAL.read_text(), re.MULTILINE):
            fail(f"G2 冻结件缺定理声明（regex {pat}）")

    # (b) lp.json bound_exact：Fraction 独立重算
    if not LP_JSON.exists():
        fail(f"G2 LP 证书不在档：{LP_JSON}")
    lp = jload(LP_JSON)
    be_str = lp["bound_exact"]
    be = Fraction(be_str)
    e_star = load_e_star()
    if not be > M1_TARGET:
        fail(f"G2 lp.json bound_exact=={float(be)!r} 不 > 189/8")
    if not be <= e_star + E_TOL:
        fail(f"G2 lp.json bound_exact=={float(be)!r} 不 ≤ E*+1e-6=="
             f"{float(e_star + E_TOL)!r}")
    # lp.json 内部一致：float 字段 bound 与 bound_exact 同值（9 位十进舍入口径）
    if Fraction(str(lp["bound"])) != Fraction(str(round(float(be), 9))):
        fail("G2 lp.json bound 与 bound_exact 的 9 位舍入口径不一致")

    # (c) 文档所引 LP 界与盘上 lp.json 逐位一致（NC2 靶位）
    be_repr = repr(float(be))
    if be_repr not in doc_text:
        fail(f"G2 文档缺 LP 界 bound_exact float repr {be_repr}（与 lp.json 失配）")
    if str(lp["bound"]) not in doc_text:
        fail(f"G2 文档缺 lp.json bound 字段串 {lp['bound']}")
    # E* 直读锚
    if str(e_star.numerator) != "25759986531" or float(e_star) != 25.759986531:
        fail(f"G2 energies.json energies[9].value 异常：{e_star}")
    if "25.759986531" not in doc_text:
        fail("G2 文档缺 E* 宣称 25.759986531")

    # (d) 脚本在盘
    for p in (PIN_HASHES, CHECK_SH):
        if not p.exists():
            fail(f"G2 脚本不在盘：{p}")

    # (e) which 三连 informational（不作 pass 判据）
    if ENV_LEDGER.exists():
        led = jload(ENV_LEDGER)
        for tool in ("lake", "lean", "elan"):
            fresh = shutil.which(tool)
            rec = led["which"].get(tool, "（ledger 未记）")
            tag = "一致" if (fresh is None) == (rec is None) else "不一致"
            print(f"[gate][info] G2(e) which {tool}: 现测={fresh or 'NOT FOUND'} "
                  f"ledger={rec if rec else 'NOT FOUND'} → {tag}（informational，"
                  "不作 pass 判据）", flush=True)
    else:
        print(f"[gate][info] G2(e) 环境账 ledger 不在档（{ENV_LEDGER}），"
              "which 对比跳过（informational）", flush=True)

    okmsg(f"G2 机器事实核全过：sorry 计数=4@{SORRY_LINES_EXPECTED}、四定理名在档、"
          f"bound_exact={be_repr} > 189/8 且 ≤ E*+1e-6（E*={float(e_star)!r} 只读 "
          f"energies.json energies[9].value）、pin_hashes.sh/check.sh 在盘、"
          "which 三连 informational 已打印")
    return be


# ---------------------------------------------------------------- G3
def check_g3(doc_text: str) -> None:
    if not CERTS_DIR.is_dir():
        fail(f"G3 证书目录不在档：{CERTS_DIR}")
    files = sorted(CERTS_DIR.glob("*.json"))
    n = len(files)
    if n != 27:
        fail(f"G3 certificates/*.json 实测 {n} 份 ≠ 文档口径 27 份")
    if "27 份" not in doc_text:
        fail("G3 文档缺证书计数宣称「27 份」")
    total = 0
    missing = []
    for f in files:
        size = f.stat().st_size
        total += size
        # 文档行：| `filename` | bytes(带千分逗号) | MB |
        m = re.search(r"\|\s*`" + re.escape(f.name) + r"`\s*\|\s*([\d,]+)\s*\|",
                      doc_text)
        if not m:
            missing.append(f.name)
            continue
        cited = int(m.group(1).replace(",", ""))
        if cited != size:
            fail(f"G3 文档所引 {f.name} 字节数 {cited} ≠ 盘上实测 {size}")
    if missing:
        fail(f"G3 文档缺 {len(missing)} 份证书的字节表行：{missing[:5]}…")
    if str(total) not in doc_text:
        fail(f"G3 文档缺总字节数宣称 {total}")
    mb = total / 1048576
    if f"{mb:.2f}" not in doc_text:
        fail(f"G3 文档缺总 MB 宣称 {mb:.2f}")
    okmsg(f"G3 证书计数/尺寸与盘上一致：27 份、合计 {total:,} 字节＝{mb:.2f} MB、"
          "逐份字节精确比对通过")


# ---------------------------------------------------------------- NC1/NC2
def _run_sub(doc: Path) -> subprocess.CompletedProcess:
    return subprocess.run(
        [sys.executable, str(Path(__file__).resolve()), "--doc", str(doc),
         "--no-nc"], capture_output=True, text=True)


def run_nc1(doc_path: Path) -> None:
    base = Path("/tmp/r10b_stageb_nc1")
    orig = doc_path.read_text()
    # 路由 sanity：未篡改 /tmp 副本须 exit 0
    orig_copy = base.with_name(base.name + "_orig.md")
    orig_copy.write_text(orig)
    r0 = _run_sub(orig_copy)
    if r0.returncode != 0:
        fail(f"NC1 前置失败：未篡改 /tmp 副本应 exit 0，实得 {r0.returncode}"
             f"（尾行：{r0.stdout.strip().splitlines()[-1:]}）")
    # 篡改：sorry 数改 5 ⇒ G1 失配 exit 1
    tampered = orig.replace("恰 4 处 sorry", "恰 5 处 sorry")
    if tampered == orig:
        fail("NC1 前置失败：文档无「恰 4 处 sorry」可篡改")
    tdoc = base.with_name(base.name + "_doc.md")
    tdoc.write_text(tampered)
    r = _run_sub(tdoc)
    if r.returncode == 0:
        fail("NC1 未检出篡改（恰 4 处 sorry→恰 5 处 sorry 仍 exit 0）")
    if "G1" not in r.stdout:
        fail(f"NC1 失配面非 G1：\n{r.stdout}")
    orig_copy.unlink(missing_ok=True)
    tdoc.unlink(missing_ok=True)
    okmsg(f"NC1 /tmp 文档副本 sorry 数改 5 ⇒ G1 失配 exit {r.returncode} 检出 ✓"
          "（未篡改副本 exit 0 sanity ✓）")


def run_nc2(doc_path: Path) -> None:
    base = Path("/tmp/r10b_stageb_nc2")
    orig = doc_path.read_text()
    # 路由 sanity：未篡改 /tmp 副本须 exit 0
    orig_copy = base.with_name(base.name + "_orig.md")
    orig_copy.write_text(orig)
    r0 = _run_sub(orig_copy)
    if r0.returncode != 0:
        fail(f"NC2 前置失败：未篡改 /tmp 副本应 exit 0，实得 {r0.returncode}"
             f"（尾行：{r0.stdout.strip().splitlines()[-1:]}）")
    # 篡改：LP 界引 25.7（长串先换，避免前缀残留）⇒ G2 失配 exit 1
    be_repr = repr(float(Fraction(jload(LP_JSON)["bound_exact"])))
    tampered = orig.replace(be_repr, "25.7").replace(
        str(jload(LP_JSON)["bound"]), "25.7")
    if tampered == orig:
        fail(f"NC2 前置失败：文档无 LP 界 {be_repr} 可篡改")
    tdoc = base.with_name(base.name + "_doc.md")
    tdoc.write_text(tampered)
    r = _run_sub(tdoc)
    if r.returncode == 0:
        fail("NC2 未检出篡改（LP 界→25.7 仍 exit 0）")
    if "G2" not in r.stdout:
        fail(f"NC2 失配面非 G2：\n{r.stdout}")
    orig_copy.unlink(missing_ok=True)
    tdoc.unlink(missing_ok=True)
    okmsg(f"NC2 /tmp 副本 LP 界引 25.7 ⇒ G2 失配 exit {r.returncode} 检出 ✓"
          "（未篡改副本 exit 0 sanity ✓）")


def run_gate(doc_path: Path, run_nc: bool) -> None:
    print(f"[gate] r10_stageb_gate seed={SEED_GATE}（确定性检查，无随机路径）",
          flush=True)
    if not doc_path.exists():
        fail(f"范围文档不在档：{doc_path}")
    doc_text = doc_path.read_text()
    check_g1(doc_text)
    check_g2(doc_text)
    check_g3(doc_text)
    if run_nc:
        run_nc1(doc_path)
        run_nc2(doc_path)
    print("[gate] 全门 PASS（G1–G3 ＋ NC1 ＋ NC2）", flush=True)


def main() -> None:
    ap = argparse.ArgumentParser(description="R10B stageb-scope 验收门")
    ap.add_argument("--doc", default=str(DOC_DEFAULT),
                    help="范围文档路径（默认 notes/stageb-scope.md）")
    ap.add_argument("--no-nc", action="store_true",
                    help="跳过 NC1/NC2（NC 子进程内部用）")
    args = ap.parse_args()
    run_gate(Path(args.doc).resolve(), not args.no_nc)


if __name__ == "__main__":
    main()
