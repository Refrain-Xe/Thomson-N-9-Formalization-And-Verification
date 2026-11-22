"""thomson_certs — Thomson 证明工程的精确证书工具包。

子模块：
  exact  : 纯 fractions 的对称矩阵精确 LDLᵀ / 正定性判定（验证员独立复核用）
  schema : 证书 JSON 的数据类与编解码（数值员↔形式化员交接格式）

用法（在 certificates/ 目录下）：
  python3 tests/test_exact.py
"""

from .exact import is_positive_definite, rational_ldlt
from .schema import Certificate, decode_certificate, encode_certificate

__all__ = ["is_positive_definite", "rational_ldlt",
           "Certificate", "encode_certificate", "decode_certificate"]
