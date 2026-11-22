"""schema.py — 精确证书 JSON 的数据模式与编解码。

这是数值员与形式化员之间的交接格式（见 thomson-workflow/PROTOCOL.md §2）：
数值员交付证书 JSON → 验证员用 exact.py 独立复核 → 形式化员按同一 schema 生成
Lean 侧数据 → 验证员比对两侧逐位一致。

所有有理数在 JSON 中以 'p/q'（或整数 'p'）字符串存储，杜绝浮点。
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from fractions import Fraction

__all__ = ["SchemaError", "Certificate", "fraction_to_str", "str_to_fraction",
           "encode_certificate", "decode_certificate"]

# 最简形式：可选负号 + 数字，可选 /正整数分母
_RAT = re.compile(r"^-?\d+(/\d+)?$")


class SchemaError(ValueError):
    """证书不符合 schema。"""


def fraction_to_str(f: Fraction) -> str:
    """Fraction → 最简字符串：分母为 1 时输出 'p'，否则 'p/q'。"""
    f = Fraction(f)
    return str(f.numerator) if f.denominator == 1 else f"{f.numerator}/{f.denominator}"


def str_to_fraction(s: str) -> Fraction:
    """'p' / 'p/q' → Fraction；格式非法或分母为 0 抛 SchemaError。"""
    if not isinstance(s, str) or not _RAT.match(s):
        raise SchemaError(f"不是合法的有理数字符串: {s!r}")
    try:
        return Fraction(s)
    except (ValueError, ZeroDivisionError) as exc:
        raise SchemaError(f"无法解析有理数 {s!r}") from exc


@dataclass
class Certificate:
    """一份精确证书（例如一个 slab / 三点 SDP 块）。

    字段：
      m_lo, m_hi   : 分裂变量 m（如最小内积）所在胞腔的下/上端点，'p/q' 字符串。
      blocks       : 命名矩阵块，如 {'K': [['1', '0'], ['0', '3/7']]}；
                     元素均为 'p/q' 字符串；块内必须对称（decode 时校验）。
      claimed_bound: 本证书声称的界（如能量下界），'p/q' 字符串。
      provenance   : 溯源字典，至少含：
                     - 'repo'      产出仓库（N9/N10/N11）
                     - 'generator' 生成脚本或命令
                     - 'params'    胞腔/结构参数
                     - 'date'      产出日期（ISO 8601）
                     - 'upstream'  上游依据（论文/参考仓库）
    """

    m_lo: str
    m_hi: str
    blocks: dict[str, list[list[str]]]
    claimed_bound: str
    provenance: dict = field(default_factory=dict)


def encode_certificate(cert: Certificate) -> str:
    """Certificate → 紧凑 JSON 字符串（键排序，稳定输出，适合钉哈希）。"""
    payload = {
        "m_lo": cert.m_lo,
        "m_hi": cert.m_hi,
        "blocks": cert.blocks,
        "claimed_bound": cert.claimed_bound,
        "provenance": cert.provenance,
    }
    _validate_payload(payload)
    return json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def decode_certificate(text: str) -> Certificate:
    """JSON 字符串 → Certificate；结构或数值格式非法抛 SchemaError。"""
    try:
        payload = json.loads(text)
    except json.JSONDecodeError as exc:
        raise SchemaError(f"JSON 解析失败: {exc}") from exc
    _validate_payload(payload)
    return Certificate(
        m_lo=payload["m_lo"],
        m_hi=payload["m_hi"],
        blocks=payload["blocks"],
        claimed_bound=payload["claimed_bound"],
        provenance=payload.get("provenance", {}),
    )


def _validate_payload(p) -> None:
    if not isinstance(p, dict):
        raise SchemaError("证书必须是 JSON 对象")
    for key in ("m_lo", "m_hi", "claimed_bound"):
        if key not in p:
            raise SchemaError(f"缺少必填字段 {key}")
        str_to_fraction(p[key])  # 只为校验，抛 SchemaError 即非法
    blocks = p.get("blocks")
    if not isinstance(blocks, dict) or not blocks:
        raise SchemaError("blocks 必须是非空对象")
    for name, mat in blocks.items():
        if not isinstance(mat, list) or not mat:
            raise SchemaError(f"块 {name} 必须是非空二维数组")
        n = len(mat)
        for i, row in enumerate(mat):
            if not isinstance(row, list) or len(row) != n:
                raise SchemaError(f"块 {name} 第 {i} 行不是长 {n} 的数组")
            for j, x in enumerate(row):
                str_to_fraction(x)
        for i in range(n):
            for j in range(i):
                if Fraction(mat[i][j]) != Fraction(mat[j][i]):
                    raise SchemaError(f"块 {name} 不对称: [{i}][{j}]≠[{j}][{i}]")
    prov = p.get("provenance", {})
    if not isinstance(prov, dict):
        raise SchemaError("provenance 必须是对象")
    for key in ("repo", "generator", "date"):
        if not prov.get(key):
            raise SchemaError(f"provenance 缺少 {key}")
