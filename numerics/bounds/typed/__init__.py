# typed — Bachoc–Vallentin 分型三点构造（S² 适配，N=7 证明 §6 的推广）
"""typed 三点构造包：分型基、typed 三点对称化、SDP 数据装配与求解复核。

模块：
  core.py            类型结构、装配（协变块/份额/slacks/归一化/minorant 地图）、自检
  solve.py           cvxpy SDP 构建、求解、数值复核与折减
  typed_selftest.py  N∈{2,3,4,6,12} 紧合自检表（deliverable）
  calibrate_n7.py    N=7 关键档校准（对照 references/thomson-n7-lean/paper/）
  prototype_n9.py    N=9 typed 原型运行（规模/耗时/界值）

数学说明见 core.py 模块 docstring。
"""
from . import core, solve  # noqa: F401

__all__ = ["core", "solve"]
