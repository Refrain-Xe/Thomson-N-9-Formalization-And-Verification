#!/bin/bash
# sdpa_build.sh — 在 macOS（darwin/arm64，clang）上从源码构建 SDPA-GMP 7.1.3。
#
# hp_solve.py（路线 a：扩展精度求解）需要 sdpa_gmp 可执行文件；本脚本是把
# 2026-10-03 本机构建过程（GMP 6.3.0 + sdpa-gmp 7.1.3）固化下来的配方，
# 在干净的 /tmp 目录里自包含可重跑。需要的只有：clang/clang++、make、curl。
#
# 用法：  bash numerics/bounds/sdpa_build.sh /tmp/hpbuild
# 产物：  $1/sdpa-gmp-7.1.3/sdpa_gmp
# 之后：  python3 numerics/bounds/hp_solve.py --sdpa-bin $1/sdpa-gmp-7.1.3/sdpa_gmp
#
# 三处源码补丁（都在本脚本里自动完成）：
#  ① spooles 2.2（sdpa 的稀疏 Cholesky）：Make.inc 加 clang 兼容旗
#     （-Wno-int-conversion -Wno-implicit-function-declaration -Wno-implicit-int
#      -Wno-incompatible-function-pointer-types）；
#  ② sdpa_struct.h 的 P_FORMAT 从 %+18.12Fe 改 %+72.66Fe——默认只打印 12 位
#     解数字，撑不起 2^-48 以下的 dyadic 舍入，改后 .result 输出 66 位十进制；
#  ③ config.guess/config.sub 换 2021 版（原 2009 版不认识 arm64-apple-darwin25）。
# 另外两个坑：sdpa-gmp 源码包内嵌的 spooles.2.2.tgz 在 sourceforge 下载里损坏
# （tar 报 gzip error），从 netlib 单独下载替换；configure 需要 libgmpxx，
# GMP 要 --enable-cxx。
set -euo pipefail

BUILD="${1:-/tmp/hpbuild}"
mkdir -p "$BUILD" && cd "$BUILD"

echo "== [1/4] GMP 6.3.0 (需要 C++ 支持：libgmpxx) =="
if [ ! -x "$BUILD/gmp-install/lib/libgmpxx.a" ]; then
  curl -sL -m 300 -o gmp-6.3.0.tar.xz "https://ftp.gnu.org/gnu/gmp/gmp-6.3.0.tar.xz"
  tar xf gmp-6.3.0.tar.xz
  ( cd gmp-6.3.0 \
    && ./configure --prefix="$BUILD/gmp-install" --enable-static --disable-shared --enable-cxx \
    && make -j"$(sysctl -n hw.ncpu)" && make install )
fi
echo "GMP ok: $BUILD/gmp-install"

echo "== [2/4] sdpa-gmp 7.1.3 源码 =="
if [ ! -d "$BUILD/sdpa-gmp-7.1.3" ]; then
  curl -sL -m 600 -o sdpa-gmp.tar.gz \
    "https://downloads.sourceforge.net/project/sdpa/sdpa-gmp/sdpa-gmp-7.1.3.src.20150320.tar.gz"
  tar xzf sdpa-gmp.tar.gz
fi
cd "$BUILD/sdpa-gmp-7.1.3"

echo "== [3/4] spooles 2.2（netlib 下载替换 + clang 旗） =="
curl -sL -m 300 -o spooles.2.2.tgz "https://netlib.org/linalg/spooles/spooles.2.2.tgz"
tar tzf spooles.2.2.tgz > /dev/null   # 完整性检查，损坏即中止
cp spooles.2.2.tgz spooles/archive/spooles.2.2.tgz
python3 - << 'PYEOF'
from pathlib import Path
p = Path("spooles/Makefile")
t = p.read_text()
anchor = "\tcd build ; patch -p0 < ../patches/patch-Make.inc\n"
inject = (anchor
          + "\tcd build ; sed -i '' 's/^# CC = cc/  CC = cc/; s|^  CC = /usr/lang-4.0/bin/cc|# CC = /usr/lang-4.0/bin/cc|' Make.inc\n"
          + "\tcd build ; sed -i '' 's/CFLAGS += -O2 -funroll-all-loops $$(pthead_cflags)/CFLAGS += -O2 -funroll-all-loops -Wno-int-conversion -Wno-implicit-function-declaration -Wno-implicit-int -Wno-incompatible-function-pointer-types/' Make.inc\n")
if "Wno-int-conversion" not in t:
    assert anchor in t, "spooles Makefile 锚点缺失（版本变了？）"
    p.write_text(t.replace(anchor, inject))
print("spooles Makefile patched")
PYEOF
make -C spooles

echo "== [4/4] configure + make sdpa_gmp（精度补丁 + 新 config 脚本） =="
sed -i '' 's/#define P_FORMAT "%+18.12Fe"/#define P_FORMAT "%+72.66Fe"/' sdpa_struct.h
sed -i '' 's/"P_FORMAT/" P_FORMAT/g; s/P_FORMAT"/P_FORMAT "/g' *.cpp
curl -sL -m 90 -o config.guess "https://raw.githubusercontent.com/gcc-mirror/gcc/master/config.guess"
curl -sL -m 90 -o config.sub   "https://raw.githubusercontent.com/gcc-mirror/gcc/master/config.sub"
chmod +x config.guess config.sub
CC=clang CXX=clang++ ./configure \
  --with-gmp-includedir="$BUILD/gmp-install/include" \
  --with-gmp-libdir="$BUILD/gmp-install/lib"
make -j"$(sysctl -n hw.ncpu)"
./sdpa_gmp 2>&1 | head -3 || true
echo "== 完成：$BUILD/sdpa-gmp-7.1.3/sdpa_gmp =="
