#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""warmstart_probe.py — R11B：SDPA-GMP warm-start 初值通道端到端死活探针.

任务（r11b-warmstart-probe，D43 裁决 2）：RC2 C1 第 0 项『初值注入配置验证』
预算内兑现。sdpa_gmp 7.1.3 CLI 原生初值通道（-id/-is＋位置参 [InitialPtFile]）
已亲验存在；本探针裁三件未决：
  ① .ini 文件 GMP 200 位精度格式（源码 sdpa_io.cpp IO::read(fpData,xMat,yVec,
     zMat,inputSparse) 解码＋官方 example1.ini 对照，见 --format-spec）；
  ② 初值是否真被消费（同输入确定性求解器：暖启迭代数 ≠ 冷解迭代数 ⇔ 消费；
     .ini 被忽略 ⇒ 输出与冷解逐位相同）；
  ③ 收敛认证质量是否退化（暖启 .result 走 typed_ladder 认证链：
     solution_from_parse → certify(k=48) → certified 与存档证书逐位比对
     ＋ --verify-cert 独立复核 exit 0）。

载体＝在册最小整解档 typed cap m090 M6（存档冷解 586.8s/76 iter/pdOPT，
dat-s/param/result 三件冻结于 results/typed_ladder_work/m090_M6/，全程零改动
——工作副本一律在 /tmp）。三解：
  cold      同 dat-s/param 冷重解（确定性基线；迭代数应 == 76）；
  warm_self 存档 pdOPT .result → .ini（逐 token 原样回注）重解；
  warm_dyad 预算容则：.ini 值截断到 2^-24 dyadic 网格（floor，口径同
             sdp_certify.dyad(floor=True)）重解——传质损失鲁棒性。

.ini 密集格式规格（sdpa-gmp-7.1.3 源码 sdpa_io.cpp:149-282 解码；官方
example1.ini 亲验）：纯顺序 scanf 流（%*[^0-9+-]%Fe；花括号/逗号/换行均为
可跳字符），依次为
  1. yVec：m 个数（读入后取负——与 .result xVec 显示层的取负互抵，回注
     原样 token 即还原内部 yVec）；
  2. zMat：全部 SDP 块（blockStruct ≥2 者，按出现序）各 size² 个数（行主序，
     全方阵含下三角；仅 i≤j 且 ≠0 者生效——零是占位符，必须写出）；
  3. zMat LP 部：LP_nBlock 个数（blockStruct <0 与 ==1 者摊平，按出现序）；
  4. xMat：SDP 块同 2；
  5. xMat LP 部：同 3。
REVERSE_PRIMAL_DUAL build（sdpa_tool.h:58 无条件定义）：.result 的 xVec 段＝
内部 yVec 取负显示、xMat 段＝内部 zMat、yMat 段＝内部 xMat（sdpa_io.cpp:
1503-1513），故 .result→.ini 映射＝xVec→yVec 段、xMat→zMat 段、yMat→xMat 段
（原始 blockStruct 顺序拆块后按 SDP-先-LP-后重排）。

用法（全部子命令幂等可重跑；求解一律外部 nohup 后台＋轮询）：
  python3 numerics/bounds/warmstart_probe.py --format-spec
  python3 numerics/bounds/warmstart_probe.py --smoke [--sdpa-bin BIN]
  python3 numerics/bounds/warmstart_probe.py --run [--sdpa-bin BIN]
      [--stages pre,smoke,cold,warm_self,warm_dyad,cert]
  python3 numerics/bounds/warmstart_probe.py --convert SRC.result SRC.dat-s OUT.ini
      [--dyadic-floor-bits N]

产出 ledger：numerics/bounds/results/r11_warmstart_probe.json
（runs[solve_s/iterations/objVal/phase]、verdict=channel_alive|channel_dead|
channel_ignored、消费推断、预算 Σ（Fraction 精确）、存档 .result sha256 前后
值、.ini 格式规格摘要、provenance）。
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import re
import subprocess
import sys
import time
from datetime import datetime, timezone
from decimal import Decimal
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
RESULTS = HERE / "results"
LEDGER = RESULTS / "r11_warmstart_probe.json"

# ---- 载体（冻结件，只读） ------------------------------------------------
ARCH = RESULTS / "typed_ladder_work" / "m090_M6"
ARCH_DAT = ARCH / "typed_cap.dat-s"
ARCH_PARAM = ARCH / "param.sdpa"
ARCH_RESULT = ARCH / "typed_cap.result"
ARCH_SOL = RESULTS / "typed_ladder_sol_m090_M6.json"
ARCH_CERT = REPO / "certificates" / "n9-stage-a4-typedcap-m090_M6.json"

# G6 冻结面（git diff 守卫路径；sha256 前后值另记三件套）
FROZEN_PATHS = [
    "numerics/bounds/results/typed_ladder_work",
    "numerics/bounds/results/typed_ladder.json",
    "numerics/bounds/results/typed_ladder_sol_m090_M6.json",
    "numerics/bounds/results/lp.json",
    "certificates/n9-stage-a4-typedcap-m090_M6.json",
]

SDPA_BIN = Path("/tmp/hpbuild/sdpa-gmp-7.1.3/sdpa_gmp")
SRC_URL = ("https://downloads.sourceforge.net/project/sdpa/sdpa-gmp/"
           "sdpa-gmp-7.1.3.src.20150320.tar.gz")

BUDGET_CAP_S = Fraction(2160)          # 口径 A 硬顶（0.2 当量）
EQUIV_UNIT_S = 10800
COLD_TIMEOUT_S = 1500                  # 冷解看门狗（存档 584.4s CPU）
WARM_TIMEOUT_FLOOR_S = 60              # 暖启看门狗下限

PARAM_SDPA = """500unsigned int maxIteration;
1.0E-30\tdouble 0.0 < epsilonStar;
1.0E4   double 0.0 < lambdaStar;
2.0   \tdouble 1.0 < omegaStar;
-1.0E5  double lowerBound;
1.0E5   double upperBound;
0.1    \tdouble 0.0 <= betaStar <  1.0;
0.3    \tdouble 0.0 <= betaBar  <  1.0, betaStar <= betaBar;
0.9    \tdouble 0.0 < gammaStar <  1.0;
1.0E-30\tdouble 0.0 < epsilonDash;
200     precision
"""

# 官方 example1（sdpa-gmp-7.1.3 源包自带；GPL，随包再分发口径——探针烟雾验
# 专用，逐字节内嵌以保证 /tmp 源包消失后仍可复跑）
EXAMPLE1_DAT_S = '''"Example 1: mDim = 3, nBLOCK = 1, {2}"
   3  =  mDIM
   1  =  nBOLCK
   2  = bLOCKsTRUCT
48, -8, 20
0 1 1 1 -11
0 1 2 2 23
1 1 1 1 10
1 1 1 2 4
2 1 2 2 -8
3 1 1 2 -8
3 1 2 2 -2
'''
EXAMPLE1_INI_OFFICIAL = """{0.0, -4.0, 0.0}
{ {11.0, 0.0}, {0.0, 9.0} }
{ {5.9,  -1.375}, {-1.375, 1.0} }
"""

INI_FORMAT_SPEC = dict(
    reader="sdpa_io.cpp:149 IO::read(fpData, xMat, yVec, zMat, inputSparse)",
    stream="sequential gmp_fscanf %*[^0-9+-]%Fe（200 位精度，param 读入即 "
           "mpf_set_default_prec(200)）；花括号/逗号/换行皆可跳字符",
    order=["yVec: m 个数（读入即取负——与 .result xVec 显示取负互抵）",
           "zMat: SDP 块（blockStruct≥2，按出现序）各 size² 个数（行主序全方阵"
           "，零必须显式占位：仅 i≤j 且 ≠0 生效）",
           "zMat LP: LP_nBlock 个数（blockStruct<0 与 ==1 摊平，按出现序）",
           "xMat: 同 zMat 结构",
           "xMat LP: 同上"],
    result_mapping="REVERSE_PRIMAL_DUAL（sdpa_tool.h:58 无条件）：.result xVec 段"
                   "＝内部 yVec×(−1)、xMat 段＝内部 zMat、yMat 段＝内部 xMat"
                   "（sdpa_io.cpp:1503-1513）⇒ 回注映射 xVec→yVec、xMat→zMat、"
                   "yMat→xMat，原始 blockStruct 顺序拆块后 SDP-先-LP-后重排",
    official_sample="example1.ini（源包自带）＝ yVec {0,-4,0} ＋ zMat {{11,0},{0,9}}"
                    " ＋ xMat {{5.9,-1.375},{-1.375,1}}——全方阵含显式零亲验",
    cli="option type 2: -id <ini>（dense）/-is <ini>（sparse）；option type 1: "
        "位置参 [InitialPtFile]（文件名以 -s 结尾判 sparse）",
    consumption_path="sdpa_main.cpp:256-277 读入 currentPt + computeInverse ＋ "
                     "mu.initialize(currentPt)＋主循环 solveInfo.update 走 "
                     "initPt_xMat/initPt_zMat 参照（源码级在案）",
)

NUM_RE = re.compile(r"[+-]\d+\.\d+[eE][+-]\d+")


def fail(msg: str) -> None:
    print(f"[probe][FAIL] {msg}", flush=True)
    sys.exit(1)


def sha256_of(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


# ============================================================ .result 结构解析
def read_dat_s_header(dat_s: Path) -> dict:
    """dat-s 头：mDIM / nBLOCK / blockStruct（原样含负号与 1）。"""
    lines = dat_s.read_text().splitlines()
    idx = 0
    while lines[idx].startswith(("*", '"')):
        idx += 1
    m = int(re.match(r"\s*(\d+)", lines[idx]).group(1))
    nblk = int(re.match(r"\s*(\d+)", lines[idx + 1]).group(1))
    bs = [int(t) for t in lines[idx + 2].replace("=", " ").split()
          if re.fullmatch(r"-?\d+", t)]
    assert len(bs) == nblk, f"blockStruct 计数 {len(bs)} ≠ nBLOCK {nblk}"
    return dict(m=m, n_block=nblk, block_struct=bs)


def split_top_groups(section: str) -> list:
    """扫描 depth-1 花括号组（外层大括号已剥）。"""
    start = section.index("{")
    body = section[start + 1:]
    groups, depth, gs = [], 0, None
    for i, ch in enumerate(body):
        if ch == "{":
            if depth == 0:
                gs = i
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0 and gs is not None:
                groups.append(body[gs:i + 1])
                gs = None
            elif depth < 0:
                break
    return groups


def parse_matrix_section(section: str, block_struct: list) -> dict:
    """xMat/yMat 段 → {'sdp': [块][行][token], 'lp': [token]}（原始顺序拆块）."""
    groups = split_top_groups(section)
    if len(groups) != len(block_struct):
        fail(f"矩阵段顶层组数 {len(groups)} ≠ nBLOCK {len(block_struct)}")
    sdp, lp = [], []
    for size, g in zip(block_struct, groups):
        if size >= 2:
            rows = re.findall(r"\{([^{}]*)\}", g)
            if len(rows) != size:
                fail(f"SDP 组行数 {len(rows)} ≠ size {size}")
            mat = []
            for r_ in rows:
                toks = [t for t in re.split(r"[,\s]+", r_) if t]
                if len(toks) != size:
                    fail(f"SDP 行元素数 {len(toks)} ≠ size {size}")
                for t in toks:
                    if not NUM_RE.fullmatch(t):
                        fail(f"SDP token 非法：{t[:40]}")
                mat.append(toks)
            sdp.append(mat)
        else:
            flat = g.strip()
            if not (flat.startswith("{") and flat.endswith("}")):
                fail("LP 组格式异常")
            toks = [t for t in re.split(r"[{},\s]+", flat[1:-1]) if t]
            if len(toks) != abs(size):
                fail(f"LP 组元素数 {len(toks)} ≠ |size| {abs(size)}")
            for t in toks:
                if not NUM_RE.fullmatch(t):
                    fail(f"LP token 非法：{t[:40]}")
            lp.extend(toks)
    return dict(sdp=sdp, lp=lp)


def parse_result_full(result_path: Path, dat_s: Path) -> dict:
    """完整解析 .result：info 统计＋xVec tokens＋xMat/yMat 结构（token 原样）."""
    text = result_path.read_text()
    hdr = read_dat_s_header(dat_s)

    def grab(pat):
        mm = re.search(pat, text)
        return mm.group(1) if mm else None

    info = dict(
        phase_value=grab(r"phase\.value = (\S+)"),
        iteration=int(grab(r"Iteration = (\d+)") or -1),
        mu=grab(r"mu = ([0-9.eE+-]+)"),
        relative_gap=grab(r"relative gap = ([0-9.eE+-]+)"),
        p_feas_error=grab(r"p\.feas\.error = ([0-9.eE+-]+)"),
        d_feas_error=grab(r"d\.feas\.error = ([0-9.eE+-]+)"),
        obj_primal=grab(r"objValPrimal = ([0-9.eE+-]+)"),
        obj_dual=grab(r"objValDual = ([0-9.eE+-]+)"),
    )
    i_xv = text.index("xVec = ")
    i_xm = text.index("xMat = ")
    i_ym = text.index("yMat = ")
    xv_body = text[i_xv:i_xm]
    xv_body = xv_body[xv_body.index("{"):xv_body.rindex("}") + 1]
    xvec = [t for t in re.split(r"[{},\s]+", xv_body) if t]
    if len(xvec) != hdr["m"]:
        fail(f"xVec 元素数 {len(xvec)} ≠ mDIM {hdr['m']}")
    for t in xvec:
        if not NUM_RE.fullmatch(t):
            fail(f"xVec token 非法：{t[:40]}")
    # 迭代表（消费证据用：逐位比对暖启 vs 冷解轨迹）
    table = [mm.group(0).strip() for mm in re.finditer(
        r"^\s*\d+ [0-9.e+-]+ [0-9.e+-]+ [0-9.e+-]+ [+-][0-9.e+-]+ "
        r"[+-][0-9.e+-]+ [0-9.e+-]+ [0-9.e+-]+ [0-9.e+-]+\s*$", text, re.M)]
    xmat = parse_matrix_section(text[i_xm:i_ym], hdr["block_struct"])
    ymat = parse_matrix_section(text[i_ym:], hdr["block_struct"])
    return dict(info=info, xvec=xvec, xmat=xmat, ymat=ymat, table=table,
                header=hdr)


# ============================================================ .result → .ini
def dyadic_floor_token(tok: str, bits: int) -> str:
    """token → floor(v·2^bits)/2^bits 的精确十进制串（分母 2^bits ⇒ 有限小数）."""
    v = Fraction(Decimal(tok))
    p = math.floor(v * (1 << bits))
    return dyadic_frac_to_dec(p, bits)


def dyadic_clamp_token(tok: str, bits: int) -> str:
    """token → 最近 2^-bits 网格点、但 |v|<半格者钉到 ±2^-bits（不落零）.

    控因对照（warm_dyad_clamp24）用：区分『粗截断落零→reader 零跳过→
    setIdentity(λ*=1e4) 默认值陷阱』与『网格粗本身』两种死因。"""
    v = Fraction(Decimal(tok))
    if v == 0:
        return "0.0"
    p = (2 * v * (1 << bits) + Fraction(1, 2)).__floor__()
    if p == 0:
        p = 1 if v > 0 else -1
    return dyadic_frac_to_dec(p, bits)


def dyadic_frac_to_dec(p: int, bits: int) -> str:
    """整数 p / 2^bits 的精确十进制串（不约分；p 可负）。"""
    ip, fp = divmod(abs(p), 1 << bits)
    frac_digits = str(fp * (5 ** bits)).zfill(bits) if bits > 0 else ""
    return ("-" if p < 0 else "") + f"{ip}.{frac_digits or '0'}"


def emit_ini(parsed: dict, dyadic_floor_bits: int | None = None) -> str:
    """按密集 .ini 规格回注（token 原样或 dyadic floor 变换）."""
    xform = (lambda t: dyadic_floor_token(t, dyadic_floor_bits)) \
        if dyadic_floor_bits else (lambda t: t)
    out = []
    out.append("{" + ",".join(xform(t) for t in parsed["xvec"]) + "}")
    for which in ("xmat", "ymat"):
        sec = parsed[which]
        for mat in sec["sdp"]:
            rows = ["{" + ",".join(xform(t) for t in row) + "}" for row in mat]
            out.append("{" + ",".join(rows) + "}")
        out.append("{" + ",".join(xform(t) for t in sec["lp"]) + "}")
    return "\n".join(out) + "\n"


def convert(result_path: Path, dat_s: Path, out_ini: Path,
            dyadic_floor_bits: int | None = None,
            dyadic_clamp_bits: int | None = None) -> dict:
    parsed = parse_result_full(result_path, dat_s)
    if dyadic_clamp_bits:
        xform = lambda t: dyadic_clamp_token(t, dyadic_clamp_bits)  # noqa: E731
        out = ["{" + ",".join(xform(t) for t in parsed["xvec"]) + "}"]
        for which in ("xmat", "ymat"):
            sec = parsed[which]
            for mat in sec["sdp"]:
                rows = ["{" + ",".join(xform(t) for t in row) + "}" for row in mat]
                out.append("{" + ",".join(rows) + "}")
            out.append("{" + ",".join(xform(t) for t in sec["lp"]) + "}")
        text = "\n".join(out) + "\n"
    else:
        text = emit_ini(parsed, dyadic_floor_bits)
    out_ini.parent.mkdir(parents=True, exist_ok=True)
    out_ini.write_text(text)
    n_num = (len(parsed["xvec"])
             + sum(len(r) for mat in parsed["xmat"]["sdp"] for r in mat)
             + len(parsed["xmat"]["lp"])
             + sum(len(r) for mat in parsed["ymat"]["sdp"] for r in mat)
             + len(parsed["ymat"]["lp"]))
    zeros = sum(1 for sec in ("xmat", "ymat") for mat in parsed[sec]["sdp"]
                for row in mat for t in row if float(t) == 0.0) \
        + sum(1 for sec in ("xmat", "ymat") for t in parsed[sec]["lp"]
              if float(t) == 0.0) \
        + sum(1 for t in parsed["xvec"] if float(t) == 0.0)
    return dict(out=str(out_ini), bytes=len(text), numbers=n_num,
                zero_tokens=zeros, dyadic_floor_bits=dyadic_floor_bits,
                dyadic_clamp_bits=dyadic_clamp_bits,
                block_struct=parsed["header"]["block_struct"][:8],
                n_sdp_blocks=len(parsed["xmat"]["sdp"]),
                n_lp_entries=len(parsed["xmat"]["lp"]))


# ============================================================ 求解运行器
def run_sdpa(sdpa_bin: Path, dat: Path, out: Path, param: Path,
             init: Path | None = None, positional_init: bool = False,
             timeout_s: float = 3600.) -> dict:
    """一次 sdpa_gmp 求解；返回 wall 时间/退出码/输出尾部。始终写日志旁件。"""
    if positional_init:
        cmd = [str(sdpa_bin), str(dat), str(out), str(init), "-pt", "0"]
    else:
        cmd = [str(sdpa_bin), "-ds", str(dat), "-o", str(out), "-p", str(param)]
        if init is not None:
            cmd += ["-id", str(init)]
    log = out.with_suffix(".stdout")
    t0 = time.time()
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True,
                              timeout=timeout_s, cwd=str(out.parent))
        rc, so, se, killed = proc.returncode, proc.stdout, proc.stderr, False
    except subprocess.TimeoutExpired as exc:
        rc, killed = None, True
        so = (exc.stdout or b"").decode() if isinstance(exc.stdout, bytes) else (exc.stdout or "")
        se = (exc.stderr or b"").decode() if isinstance(exc.stderr, bytes) else (exc.stderr or "")
    solve_s = time.time() - t0
    log.write_text(f"$ {' '.join(cmd)}\nrc={rc}\n--- stdout tail ---\n"
                   f"{so[-4000:]}\n--- stderr tail ---\n{se[-4000:]}\n")
    return dict(cmd=cmd, solve_s=round(solve_s, 1), rc=rc, killed=killed,
                stdout_tail=so[-800:], stderr_tail=se[-800:])


def parse_run(out: Path, dat: Path, run: dict) -> dict:
    if run["rc"] != 0 or run["killed"] or not out.exists():
        return dict(parsed=False, info=dict(phase_value=None, iteration=-1,
                                            obj_primal=None))
    parsed = parse_result_full(out, dat)
    return dict(parsed=True, info=parsed["info"], table=parsed["table"])


def append_run(led: dict, row: dict) -> None:
    """按 phase 去重追加（幂等重跑不重复计数）。"""
    led["runs"] = [r for r in led["runs"] if r["phase"] != row["phase"]]
    led["runs"].append(row)


# ============================================================ ledger
def load_ledger() -> dict:
    if LEDGER.exists():
        return json.loads(LEDGER.read_text())
    return dict(runs=[], stages_done=[], ini_files={}, frozen_sha256={})


def save_ledger(led: dict) -> None:
    LEDGER.parent.mkdir(parents=True, exist_ok=True)
    LEDGER.write_text(json.dumps(led, ensure_ascii=False, indent=1))


# ============================================================ 烟雾验（官方小样）
def stage_smoke(workroot: Path, sdpa_bin: Path, led: dict) -> None:
    if "smoke" in led.get("stages_done", []):
        print("[smoke] 已跑过，跳过（幂等）", flush=True)
        return
    d = workroot / "smoke"
    d.mkdir(parents=True, exist_ok=True)
    dat, param = d / "example1.dat-s", d / "param.sdpa"
    dat.write_text(EXAMPLE1_DAT_S)
    param.write_text(PARAM_SDPA)
    # ① 冷解
    r_cold = run_sdpa(sdpa_bin, dat, d / "cold.result", param)
    p_cold = parse_run(d / "cold.result", dat, r_cold)
    if not p_cold["parsed"]:
        fail(f"smoke 冷解失败：rc={r_cold['rc']} stderr={r_cold['stderr_tail'][-300:]}")
    # ② 官方 .ini 注入（通道本身，隔离转换器缺陷）
    ini_off = d / "example1.ini"
    ini_off.write_text(EXAMPLE1_INI_OFFICIAL)
    r_off = run_sdpa(sdpa_bin, dat, d / "official_ini.result", param, init=ini_off)
    p_off = parse_run(d / "official_ini.result", dat, r_off)
    # ③ 自转换 .result→.ini 注入（本探针转换器往返）
    conv = convert(d / "cold.result", dat, d / "self.ini")
    r_self = run_sdpa(sdpa_bin, dat, d / "self_ini.result", param, init=d / "self.ini")
    p_self = parse_run(d / "self_ini.result", dat, r_self)
    # ④ 位置参初值通道（option type 1；param 用 ./param.sdpa 约定）
    r_pos = run_sdpa(sdpa_bin, dat, d / "positional.result", None,
                     init=ini_off, positional_init=True)
    p_pos = parse_run(d / "positional.result", dat, r_pos)
    for tag, rr, pp in (("smoke_cold", r_cold, p_cold),
                        ("smoke_official_ini", r_off, p_off),
                        ("smoke_self_ini", r_self, p_self),
                        ("smoke_positional_ini", r_pos, p_pos)):
        append_run(led, dict(
            phase=tag, solve_s=str(rr["solve_s"]),
            iterations=pp["info"]["iteration"] if pp["parsed"] else -1,
            objVal=pp["info"]["obj_primal"], phase_value=pp["info"]["phase_value"],
            rc=rr["rc"], killed=rr["killed"],
            stderr_summary=(rr["stderr_tail"][-300:] or "(empty)"),
            stdout_summary=(rr["stdout_tail"][-300:] or "(empty)"),
            parsed=pp["parsed"]))
        print(f"[smoke] {tag}: iter={pp['info']['iteration'] if pp['parsed'] else -1}"
              f" phase={pp['info']['phase_value']} rc={rr['rc']} ({rr['solve_s']}s)",
              flush=True)
    led["ini_files"]["smoke_self_ini"] = conv
    ok_conv = p_self["parsed"] and p_cold["parsed"] and \
        p_self["info"]["iteration"] != p_cold["info"]["iteration"]
    print(f"[smoke] 官方 ini iter {p_off['info']['iteration'] if p_off['parsed'] else -1}"
          f" vs 冷解 {p_cold['info']['iteration']}；自转换 ini "
          f"{p_self['info']['iteration'] if p_self['parsed'] else -1}；"
          f"位置参 {p_pos['info']['iteration'] if p_pos['parsed'] else -1}", flush=True)


# ============================================================ 主探针各阶段
def stage_pre(led: dict) -> None:
    for name, p in (("dat-s", ARCH_DAT), ("param", ARCH_PARAM),
                    ("result", ARCH_RESULT), ("sol", ARCH_SOL),
                    ("cert", ARCH_CERT)):
        led["frozen_sha256"][name] = dict(path=str(p), sha256=sha256_of(p))
    led["provenance"] = dict(
        task="r11b-warmstart-probe（D43 裁决 2；RC2 C1 第 0 项）",
        sdpa_bin=str(SDPA_BIN), sdpa_bin_sha256=sha256_of(SDPA_BIN),
        sdpa_source=SRC_URL,
        sdpa_source_files_read=["sdpa_gmp.cpp(sdpa_io.cpp):IO::read 初始点读取"
                                "（dense/sparse 双路）", "sdpa_main.cpp:256-277 消费路径",
                                "sdpa_tool.h:58 REVERSE_PRIMAL_DUAL=1",
                                "sdpa_struct.h P_FORMAT=%+72.66Fe（本机构建补丁）",
                                "example1.ini 官方样例"],
        carrier="typed cap m090 M6（存档冷解 586.8s/76 iter/pdOPT）",
        budget_cap_s=str(BUDGET_CAP_S), equiv_unit_s=EQUIV_UNIT_S,
        date=datetime.now(timezone.utc).isoformat(timespec="seconds"))
    led["ini_format_spec"] = INI_FORMAT_SPEC
    save_ledger(led)


def budget_sum(led: dict) -> Fraction:
    return sum((Fraction(r["solve_s"]) for r in led["runs"]), Fraction(0))


def stage_cold(workroot: Path, sdpa_bin: Path, led: dict, arch: dict) -> None:
    d = workroot / "cold"
    d.mkdir(parents=True, exist_ok=True)
    dat, param = d / "typed_cap.dat-s", d / "param.sdpa"
    dat.write_bytes(ARCH_DAT.read_bytes())
    param.write_bytes(ARCH_PARAM.read_bytes())
    rr = run_sdpa(sdpa_bin, dat, d / "typed_cap.result", param,
                  timeout_s=COLD_TIMEOUT_S)
    pp = parse_run(d / "typed_cap.result", dat, rr)
    led["cold"] = dict(
        solve_s=str(rr["solve_s"]), rc=rr["rc"], killed=rr["killed"],
        iterations=pp["info"]["iteration"] if pp["parsed"] else -1,
        phase_value=pp["info"]["phase_value"],
        objVal=pp["info"]["obj_primal"], mu=pp["info"]["mu"],
        relative_gap=pp["info"]["relative_gap"],
        table_identical_to_archive=(pp.get("table") == arch["table"]),
        stderr_summary=(rr["stderr_tail"][-300:] or "(empty)"))
    append_run(led, dict(phase="cold", solve_s=str(rr["solve_s"]),
                            iterations=led["cold"]["iterations"],
                            objVal=led["cold"]["objVal"],
                            phase_value=led["cold"]["phase_value"],
                            rc=rr["rc"], killed=rr["killed"], parsed=pp["parsed"],
                            stderr_summary=led["cold"]["stderr_summary"]))
    save_ledger(led)
    print(f"[cold] iter={led['cold']['iterations']} "
          f"phase={led['cold']['phase_value']} 表逐位同档="
          f"{led['cold']['table_identical_to_archive']} ({rr['solve_s']}s)", flush=True)


def warm_stage(workroot: Path, sdpa_bin: Path, led: dict, arch: dict,
               tag: str, dyadic_bits: int | None) -> None:
    d = workroot / tag
    d.mkdir(parents=True, exist_ok=True)
    dat, param = d / "typed_cap.dat-s", d / "param.sdpa"
    dat.write_bytes(ARCH_DAT.read_bytes())
    param.write_bytes(ARCH_PARAM.read_bytes())
    ini = d / (f"warm_dyad{dyadic_bits}.ini" if dyadic_bits else "warm_self.ini")
    conv = convert(ARCH_RESULT, ARCH_DAT, ini, dyadic_bits)
    led["ini_files"][tag] = conv
    remaining = BUDGET_CAP_S - budget_sum(led)
    timeout_s = float(min(max(remaining - Fraction(5), Fraction(WARM_TIMEOUT_FLOOR_S)),
                          Fraction(1200)))
    rr = run_sdpa(sdpa_bin, dat, d / "typed_cap.result", param, init=ini,
                  timeout_s=timeout_s)
    pp = parse_run(d / "typed_cap.result", dat, rr)
    cold_it = led.get("cold", {}).get("iterations")
    led[tag] = dict(
        solve_s=str(rr["solve_s"]), rc=rr["rc"], killed=rr["killed"],
        timeout_s=round(timeout_s, 1),
        iterations=pp["info"]["iteration"] if pp["parsed"] else -1,
        phase_value=pp["info"]["phase_value"],
        objVal=pp["info"]["obj_primal"], mu=pp["info"]["mu"],
        relative_gap=pp["info"]["relative_gap"],
        iterations_equal_cold=((pp["info"]["iteration"] if pp["parsed"] else None)
                               == cold_it),
        table_identical_to_cold=(pp.get("table") == arch.get("table")),
        stderr_summary=(rr["stderr_tail"][-300:] or "(empty)"),
        stdout_summary=(rr["stdout_tail"][-300:] or "(empty)"))
    append_run(led, dict(phase=tag, solve_s=str(rr["solve_s"]),
                            iterations=led[tag]["iterations"],
                            objVal=led[tag]["objVal"],
                            phase_value=led[tag]["phase_value"],
                            rc=rr["rc"], killed=rr["killed"], parsed=pp["parsed"],
                            stderr_summary=led[tag]["stderr_summary"]))
    save_ledger(led)
    print(f"[{tag}] iter={led[tag]['iterations']} phase={led[tag]['phase_value']}"
          f" killed={rr['killed']} ({rr['solve_s']}s, ini {conv['numbers']} 数"
          f"/{conv['bytes']}B)", flush=True)


def stage_cert(workroot: Path, led: dict) -> None:
    """暖启 .result 走 typed_ladder 认证链＋verify-cert 独立复核。"""
    sys.path.insert(0, str(HERE))
    sys.path.insert(0, str(HERE / "typed"))
    sys.path.insert(0, str(HERE.parents[2] / "thomson-workflow" / "certificates"))
    import typed_ladder as tl                                      # noqa: E402

    warm_dir = workroot / "warm_self"
    warm_result = warm_dir / "typed_cap.result"
    if not warm_result.exists():
        led["cert"] = dict(ran=False, reason="warm_self .result 不在盘")
        save_ledger(led)
        return
    E_star = tl.load_E_star()
    arch_cert = json.loads(ARCH_CERT.read_text())
    k = arch_cert["provenance"]["round_bits"]
    a0, M, K = Fraction(arch_cert["params"]["a0"]), arch_cert["params"]["M"], \
        arch_cert["params"]["K"]
    qm = tl.QuotientMaps(a0, M, K)
    ex = tl.SDPAExporter(qm)
    parsed = tl.parse_result(warm_result)
    if parsed["info"]["phase_value"] != "pdOPT":
        led["cert"] = dict(ran=False, reason=f"暖启非 pdOPT："
                                             f"{parsed['info']['phase_value']}")
        save_ledger(led)
        return
    data = tl.solution_from_parse(ex, parsed, E_star + tl.PHI_TOL)
    sol = dict(exact=dict(
        h_AA=[str(x) for x in data["h_AA"]], h_AB=[str(x) for x in data["h_AB"]],
        psi_AA=[str(x) for x in data["psi_AA"]],
        psi_AB=[str(x) for x in data["psi_AB"]],
        c_A=str(data["c_A"]), c_B=str(data["c_B"]), c_C=str(data["c_C"]),
        e=str(data["e"]),
        F=[[[str(x) for x in row] for row in m_] for m_ in data["F"]],
        B={n: [[str(x) for x in row] for row in m_] for n, m_ in data["B"].items()},
        sig={n: [[str(x) for x in row] for row in m_]
             for n, m_ in data["sig"].items()}))
    out = dict(ran=True, k=k)
    try:
        cert = tl.certify(qm, sol, k, "m090/M6-warmself", E_star,
                          min_bound=tl.F0)
        certified = cert["certified"]
        out["certified"] = str(certified)
        out["certified_bitwise_equal_archive"] = \
            (certified == Fraction(arch_cert["claimed_bound"]))
        out["archived_claimed_bound"] = arch_cert["claimed_bound"]
        warm_cert_path = warm_dir / "warm_self_cert.json"
        tl.write_certificate(qm, cert, "m090", a0, M, K, sol,
                             dict(sdpa_info=led.get("warm_self", {}), reused=False),
                             warm_cert_path)
        out["warm_cert_path"] = str(warm_cert_path)
        proc = subprocess.run(
            [sys.executable, str(HERE / "typed_ladder.py"), "--verify-cert",
             str(warm_cert_path)], capture_output=True, text=True, timeout=3600)
        out["verify_cert_exit"] = proc.returncode
        out["verify_cert_tail"] = proc.stdout[-400:]
        proc2 = subprocess.run(
            [sys.executable, str(HERE / "typed_ladder.py"), "--verify-cert",
             str(ARCH_CERT)], capture_output=True, text=True, timeout=3600)
        out["verify_cert_archive_exit"] = proc2.returncode
    except tl.CertError as exc:
        out["cert_error"] = str(exc)[:500]
    led["cert"] = out
    save_ledger(led)
    print(f"[cert] {json.dumps({k2: v for k2, v in out.items() if k2 != 'verify_cert_tail'}, ensure_ascii=False)}",
          flush=True)


RESULT_PATHS = {  # 各求解阶段的 .result 落盘位置（/tmp 工作副本）
    "cold": "/tmp/r11_ws/work/cold/typed_cap.result",
    "warm_self": "/tmp/r11_ws/work/warm_self/typed_cap.result",
    "warm_dyad": "/tmp/r11_ws/work/warm_dyad/typed_cap.result",
}


def finalize(led: dict) -> None:
    cold = led.get("cold", {})
    ws = led.get("warm_self", {})
    cert = led.get("cert", {})
    arch_obj = json.loads(ARCH_SOL.read_text())["solver_info"]["obj_primal"]
    # result_path 回填（消费证据可在盘复核）
    for r in led["runs"]:
        if r["phase"] in RESULT_PATHS and "result_path" not in r:
            r["result_path"] = RESULT_PATHS[r["phase"]]
    # 确定性口径：iterations==76 且迭代表与存档逐位一致；否则 deviation 需带解释
    arch_it = 76
    led["determinism"] = dict(
        archive_iterations=arch_it, cold_iterations=cold.get("iterations"),
        table_identical_to_archive=cold.get("table_identical_to_archive"),
        determinism_deviation=bool(
            cold.get("iterations") != arch_it
            or cold.get("table_identical_to_archive") is not True),
        explanation="")
    if led["determinism"]["determinism_deviation"]:
        led["determinism"]["explanation"] = (
            f"冷重解 iterations={cold.get('iterations')}（存档 {arch_it}），"
            f"表逐位同档={cold.get('table_identical_to_archive')}——同输入"
            "确定性求解器口径下应逐位一致，偏离需人工核对")
    consumed = (ws.get("iterations", -1) != cold.get("iterations", -2)
                and ws.get("iterations", -1) >= 0)
    obj_match = (ws.get("objVal") is not None and ws.get("objVal") == arch_obj)
    quality_ok = bool(cert.get("ran") and cert.get("verify_cert_exit") == 0
                      and cert.get("certified_bitwise_equal_archive"))
    solver_failed = (ws.get("rc") not in (0, None)) or ws.get("killed") \
        or not ws.get("phase_value")
    if consumed and quality_ok and obj_match:
        verdict = "channel_alive"
        reason = "暖启迭代≠冷解＋认证链复现存档 certified 逐位＋objVal 对上"
    elif consumed and solver_failed:
        verdict = "channel_dead"
        reason = f"初值被读但求解失败（rc={ws.get('rc')} killed={ws.get('killed')}）"
    elif consumed:
        verdict = "channel_dead"
        reason = ("初值被消费但质量退化："
                  f"obj_match={obj_match} cert={json.dumps({k: cert.get(k) for k in ('ran', 'verify_cert_exit', 'certified_bitwise_equal_archive', 'cert_error')}, ensure_ascii=False)}")
    elif ws.get("rc") not in (0, None) or ws.get("killed"):
        verdict = "channel_dead"
        reason = f"暖启求解失败（rc={ws.get('rc')} killed={ws.get('killed')}）"
    else:
        verdict = "channel_ignored"
        reason = (f"暖启迭代==冷解（{ws.get('iterations')}=={cold.get('iterations')}）"
                  "——同输入确定性求解器输出未变，.ini 未被消费")
    led["verdict"] = verdict
    led["verdict_reason"] = reason
    led["consumption"] = dict(
        consumed=consumed,
        rule="暖启迭代数 ≠ 冷解迭代数 ⇔ consumed（同输入确定性求解器；"
             ".ini 被忽略 ⇒ 输出逐位相同）",
        cold_iterations=cold.get("iterations"), warm_iterations=ws.get("iterations"),
        warm_table_identical_to_cold=ws.get("table_identical_to_cold"),
        solver_failed=bool(solver_failed))
    led["quality"] = dict(
        archived_objVal=arch_obj, warm_objVal=ws.get("objVal"), objVal_match=obj_match,
        verify_cert_exit=cert.get("verify_cert_exit"),
        certified_bitwise_equal_archive=cert.get("certified_bitwise_equal_archive"),
        certified=cert.get("certified"),
        archived_claimed_bound=cert.get("archived_claimed_bound"),
        warm_cert_path=cert.get("warm_cert_path"))
    total = budget_sum(led)
    led["budget"] = dict(
        total_solve_s=str(total), cap_s=str(BUDGET_CAP_S),
        within_cap=bool(total <= BUDGET_CAP_S),
        heavy_equivalents=str(total / EQUIV_UNIT_S),
        runs_counted=len(led["runs"]))
    # 存档件 sha256 复核（探针自身视角；门再做独立前后比对）
    led["frozen_sha256_after"] = {
        name: sha256_of(Path(v["path"])) for name, v in led["frozen_sha256"].items()}
    led["frozen_intact"] = all(
        led["frozen_sha256_after"][n] == v["sha256"]
        for n, v in led["frozen_sha256"].items())
    save_ledger(led)
    print(f"[verdict] {verdict}: {reason}", flush=True)
    print(f"[budget] Σsolve_s = {total} / {BUDGET_CAP_S}s；runs="
          f"{len(led['runs'])}；存档件零改动={led['frozen_intact']}", flush=True)


# ============================================================ main
def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--format-spec", action="store_true",
                    help="打印 .ini 格式规格（源码解码）")
    ap.add_argument("--smoke", action="store_true", help="官方小样烟雾验")
    ap.add_argument("--run", action="store_true", help="主探针（分阶段）")
    ap.add_argument("--stages", default="pre,smoke,cold,warm_self,warm_dyad,cert",
                    help="逗号分隔：pre,smoke,cold,warm_self,warm_dyad,cert")
    ap.add_argument("--sdpa-bin", default=str(SDPA_BIN))
    ap.add_argument("--workroot", default="/tmp/r11_ws/work")
    ap.add_argument("--convert", nargs=3, metavar=("RESULT", "DAT_S", "OUT_INI"),
                    help=".result → .ini 转换（独立于探针可用）")
    ap.add_argument("--dyadic-floor-bits", type=int, default=None,
                    help="转换时截断到 2^-N dyadic 网格（floor）")
    ap.add_argument("--dyadic-clamp-bits", type=int, default=None,
                    help="转换时钉到最近 2^-N 网格点（小值不落零；控因对照）")
    args = ap.parse_args()

    if args.format_spec:
        print(json.dumps(INI_FORMAT_SPEC, ensure_ascii=False, indent=1))
        return
    if args.convert:
        res, dat, out = (Path(p) for p in args.convert)
        info = convert(res, dat, out, args.dyadic_floor_bits,
                       args.dyadic_clamp_bits)
        print(json.dumps(info, ensure_ascii=False, indent=1))
        return

    sdpa_bin = Path(args.sdpa_bin)
    if not (sdpa_bin.exists() and os.access(sdpa_bin, os.X_OK)):
        fail(f"sdpa_gmp 不可执行：{sdpa_bin}")
    workroot = Path(args.workroot)
    workroot.mkdir(parents=True, exist_ok=True)

    if args.smoke:
        led = load_ledger()
        stage_smoke(workroot, sdpa_bin, led)
        led["stages_done"].append("smoke")
        save_ledger(led)
        return

    if not args.run:
        ap.error("需要 --format-spec / --smoke / --run / --convert 之一")

    led = load_ledger()
    stages = [s.strip() for s in args.stages.split(",") if s.strip()]
    arch_parsed = None
    if any(s in stages for s in ("cold", "warm_self", "warm_dyad")):
        arch_parsed = parse_result_full(ARCH_RESULT, ARCH_DAT)
    for st in stages:
        if st == "pre":
            stage_pre(led)
        elif st == "smoke":
            stage_smoke(workroot, sdpa_bin, led)
        elif st == "cold":
            stage_cold(workroot, sdpa_bin, led, arch_parsed)
            # 冷解迭代表留档供暖启逐位比对
            cold_tbl = parse_result_full(workroot / "cold" / "typed_cap.result",
                                         workroot / "cold" / "typed_cap.dat-s")
            led["cold_table_rows"] = cold_tbl["table"]
        elif st == "warm_self":
            arch = dict(table=led.get("cold_table_rows"))
            warm_stage(workroot, sdpa_bin, led, arch, "warm_self", None)
        elif st == "warm_dyad":
            if budget_sum(led) + Fraction(600) > BUDGET_CAP_S:
                led["warm_dyad"] = dict(skipped=True,
                                        reason=f"预算余量不足以安全启动 "
                                               f"（Σ={budget_sum(led)}）")
                save_ledger(led)
                print("[warm_dyad] 跳过：预算余量不足", flush=True)
            else:
                arch = dict(table=led.get("cold_table_rows"))
                warm_stage(workroot, sdpa_bin, led, arch, "warm_dyad", 24)
        elif st == "cert":
            stage_cert(workroot, led)
        if st not in led["stages_done"]:
            led["stages_done"].append(st)
        save_ledger(led)
    if "cert" in stages or any(s in stages for s in ("warm_self", "cold")):
        finalize(led)


if __name__ == "__main__":
    main()
