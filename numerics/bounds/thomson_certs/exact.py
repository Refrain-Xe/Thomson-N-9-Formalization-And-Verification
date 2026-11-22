"""exact.py — 纯标准库 fractions 的精确对称线性代数。

数值→精确桥接层的独立复核工具（见 thomson-workflow/README.md 第 4 层方法论）：
数值员产出精确有理数证书后，验证员用本模块在**不依赖任何求解器与浮点**的前提下
独立复核。改编背景：thomson-n7-lean 仓库要求 "Every certificate is exact integer
or rational data checked in the Lean kernel"（其 README.md），本模块把 kernel 之外的
复核做成同一精神的 Python 侧实现。

无主元交换（pivot-free）的 LDLᵀ 分解：对称矩阵 A = L D Lᵀ，L 单位下三角，D 对角。
对称方阵正定 ⟺ 无主元交换 LDLᵀ 可完成且 D 的对角元全正。中途出现零主元即失败
（该矩阵有零前导主子式，既不正定也不可完成本分解）。

输入约定：矩阵元素只接受 int / Fraction / 形如 'p/q' 或 'p' 的 str；不接受 float
（float 会带入二进制噪声，违背精确语义）。
"""

from __future__ import annotations

from fractions import Fraction

__all__ = ["ExactMatrixError", "NotSymmetricError", "ZeroPivotError",
           "rational_ldlt", "is_positive_definite"]


class ExactMatrixError(ValueError):
    """矩阵不满足本模块的前置条件（非方阵、非对称、元素非精确有理数等）。"""


class NotSymmetricError(ExactMatrixError):
    """矩阵不对称。"""


class ZeroPivotError(ExactMatrixError):
    """无主元交换 LDLᵀ 中途遇到零主元，分解无法继续。"""


def _to_fraction(x) -> Fraction:
    """把元素转成 Fraction；float 一律拒绝。"""
    if isinstance(x, float):
        raise ExactMatrixError(
            "不接受 float 元素（二进制噪声违背精确语义）；请传 int/Fraction/'p/q' 字符串")
    try:
        return Fraction(x)
    except (TypeError, ValueError) as exc:
        raise ExactMatrixError(f"无法把 {x!r} 解释为精确有理数") from exc


def _as_matrix(A) -> list[list[Fraction]]:
    n = len(A)
    if n == 0:
        raise ExactMatrixError("矩阵为空")
    rows = []
    for i, row in enumerate(A):
        if len(row) != n:
            raise ExactMatrixError(f"第 {i} 行长度 {len(row)} ≠ 方阵阶数 {n}")
        rows.append([_to_fraction(x) for x in row])
    return rows


def rational_ldlt(A):
    """无主元交换的精确 LDLᵀ 分解。

    参数 A：对称方阵，元素为 int/Fraction/'p/q' 字符串。
    返回 (L, d)：L 为单位下三角 Fraction 方阵（list[list[Fraction]]），
    d 为对角元列表 list[Fraction]，满足 A = L · diag(d) · Lᵀ。

    失败抛 ExactMatrixError 子类：非对称抛 NotSymmetricError；
    中途零主元抛 ZeroPivotError（此时矩阵有零前导主子式，必不正定）。
    """
    rows = _as_matrix(A)
    n = len(rows)
    for i in range(n):
        for j in range(i):
            if rows[i][j] != rows[j][i]:
                raise NotSymmetricError(
                    f"A[{i}][{j}]={rows[i][j]} ≠ A[{j}][{i}]={rows[j][i]}")
    L = [[Fraction(1) if i == j else Fraction(0) for j in range(n)] for i in range(n)]
    d: list[Fraction] = [Fraction(0)] * n
    for j in range(n):
        # d_j = A[j][j] - Σ_{k<j} L[j][k]^2 · d_k
        dj = rows[j][j]
        for k in range(j):
            dj -= L[j][k] * L[j][k] * d[k]
        if dj == 0:
            raise ZeroPivotError(f"第 {j} 个主元为 0，无主元交换 LDLᵀ 无法继续")
        d[j] = dj
        # L[i][j] = (A[i][j] - Σ_{k<j} L[i][k]·L[j][k]·d_k) / d_j,  i > j
        for i in range(j + 1, n):
            lij = rows[i][j]
            for k in range(j):
                lij -= L[i][k] * L[j][k] * d[k]
            L[i][j] = lij / dj
    return L, d


def is_positive_definite(A) -> bool:
    """精确判定对称方阵 A 是否正定（元素 int/Fraction/'p/q' 字符串）。

    判据：A 对称且无主元交换 LDLᵀ 的对角元全正（LDLᵀ 可完成时这是正定的充要条件；
    中途零主元 → 不正定，返回 False；不对称 → 抛 NotSymmetricError）。
    """
    try:
        _, d = rational_ldlt(A)
    except ZeroPivotError:
        return False
    return all(di > 0 for di in d)
