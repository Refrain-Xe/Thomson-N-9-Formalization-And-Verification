#!/usr/bin/env python3
"""Generate publication-grade vector PDF (and PNG preview) figures for the
Thomson N=9 arXiv paper directly from the verified Lean 4 certificate data.

Outputs (written to the directory containing this script):
  - fig_ttp.pdf / fig_ttp.png         : D3h tricapped trigonal prism on S^2
  - fig_overview.pdf / fig_overview.png : Two-certificate proof architecture
  - fig_minorant.pdf / fig_minorant.png : Cap minorant H(t) and 6-trough log-gap
"""

from __future__ import annotations

import os
import re
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.patches as patches
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch
from mpl_toolkits.mplot3d import Axes3D  # noqa: F401
import numpy as np
import mpmath as mp

ROOT = Path(__file__).resolve().parents[2]
OUT = Path(__file__).resolve().parent

plt.rcParams.update({
    "font.family": "serif",
    "mathtext.fontset": "cm",
    "axes.linewidth": 0.9,
    "xtick.direction": "in",
    "ytick.direction": "in",
    "pdf.fonttype": 42,
    "ps.fonttype": 42,
})


def compute_ttp_points(z: float) -> np.ndarray:
    rho = np.sqrt(1.0 - z * z)
    pts = []
    for k in range(3):
        th = 2.0 * np.pi * k / 3.0
        pts.append([rho * np.cos(th), rho * np.sin(th), z])
    for k in range(3):
        th = 2.0 * np.pi * k / 3.0
        pts.append([rho * np.cos(th), rho * np.sin(th), -z])
    for k in range(3):
        th = np.pi / 3.0 + 2.0 * np.pi * k / 3.0
        pts.append([np.cos(th), np.sin(th), 0.0])
    return np.array(pts, dtype=float)


def load_cap_minorant_from_lean():
    harm_txt = (ROOT / "formal/lean/ThomsonN9/StageB/CapCertHarmData.lean").read_text()
    bern_txt = (ROOT / "formal/lean/ThomsonN9/StageB/CapCertBernData.lean").read_text()

    S2 = int(re.search(r"def S2\s*:\s*ℤ\s*:=\s*(\d+)", harm_txt).group(1))
    mH = re.search(r"def H_int\s*:\s*List ℤ\s*:=\s*\[([^\]]+)\]", harm_txt)
    H_int = [int(x.strip()) for x in mH.group(1).split(",") if x.strip()]
    mRy = re.search(r"def res_y_int\s*:\s*List ℤ\s*:=\s*\[([^\]]+)\]", harm_txt)
    res_y_int = [int(x.strip()) for x in mRy.group(1).split(",") if x.strip()]
    R2 = sum(abs(x) for x in res_y_int) / (20.0 * S2)

    tubes_y = []
    for k in range(6):
        lo_s = re.search(rf"def yTubeLo_{k}\s*:\s*ℚ\s*:=\s*(\d+)\s*/\s*(\d+)", bern_txt)
        hi_s = re.search(rf"def yTubeHi_{k}\s*:\s*ℚ\s*:=\s*(\d+)\s*/\s*(\d+)", bern_txt)
        ylo = int(lo_s.group(1)) / int(lo_s.group(2))
        yhi = int(hi_s.group(1)) / int(hi_s.group(2))
        tubes_y.append((ylo, yhi))
    return S2, H_int, R2, tubes_y


def eval_poly_mp(coeffs_int: list[int], S2: int, t_val: float) -> float:
    mp.mp.dps = 50
    t = mp.mpf(str(t_val))
    acc = mp.mpf(0)
    for c in reversed(coeffs_int):
        acc = acc * t + mp.mpf(c)
    return float(acc / mp.mpf(S2))


def make_fig_ttp():
    z_star = 0.7036483958041318
    pts = compute_ttp_points(z_star)

    fig = plt.figure(figsize=(8.4, 4.1))
    ax = fig.add_subplot(1, 2, 1, projection="3d")

    # Translucent unit sphere wireframe
    u = np.linspace(0, 2 * np.pi, 48)
    v = np.linspace(0, np.pi, 24)
    xs = np.outer(np.cos(u), np.sin(v))
    ys = np.outer(np.sin(u), np.sin(v))
    zs = np.outer(np.ones_like(u), np.cos(v))
    ax.plot_surface(xs, ys, zs, color="#e8eef5", alpha=0.22, linewidth=0, shade=True)
    ax.plot_wireframe(xs, ys, zs, rstride=4, cstride=6, color="#9fb3c8", alpha=0.25, linewidth=0.5)

    # Equatorial circle
    th = np.linspace(0, 2 * np.pi, 120)
    ax.plot(np.cos(th), np.sin(th), np.zeros_like(th), "--", color="#7a8fa6", lw=0.8, alpha=0.65)

    # Draw nearest-neighbor / structural edges:
    # - top & bottom triangles (nu4 = 0.2427, mult 6): navy
    # - cap-prism adjacent edges (nu5 = 0.3553, mult 12): teal
    # - prism vertical edges (nu3 = 0.0098, mult 3): amber
    for i in range(9):
        for j in range(i + 1, 9):
            d = float(np.dot(pts[i], pts[j]))
            if abs(d - 0.355274) < 0.01:
                ax.plot(*zip(pts[i], pts[j]), color="#0f766e", lw=1.7, alpha=0.92)
            elif abs(d - 0.242682) < 0.01:
                ax.plot(*zip(pts[i], pts[j]), color="#1d4ed8", lw=1.9, alpha=0.95)
            elif abs(d - 0.009758) < 0.01:
                ax.plot(*zip(pts[i], pts[j]), color="#d97706", lw=1.3, ls="--", alpha=0.85)

    # Plot vertices by orbit
    ax.scatter(pts[:3, 0], pts[:3, 1], pts[:3, 2], s=68, color="#1d4ed8",
               edgecolor="white", linewidth=1.0, zorder=10, label="Top prism ($+z^*$)")
    ax.scatter(pts[3:6, 0], pts[3:6, 1], pts[3:6, 2], s=68, color="#2563eb",
               edgecolor="white", linewidth=1.0, marker="s", zorder=10, label="Bottom prism ($-z^*$)")
    ax.scatter(pts[6:, 0], pts[6:, 1], pts[6:, 2], s=84, color="#dc2626",
               edgecolor="white", linewidth=1.0, marker="^", zorder=11, label="Equatorial caps ($z=0$)")

    # Label vertices cleanly (offsets chosen orthogonal to view_init(elev=19, azim=28))
    offsets = [
        (0.14, -0.05, 0.08), (-0.15, 0.10, 0.09), (-0.14, -0.15, 0.09),
        (0.13, 0.03, -0.15), (-0.15, 0.12, -0.13), (0.06, -0.20, -0.14),
        (0.10, 0.12, 0.02), (-0.16, 0.04, 0.02), (0.06, -0.18, 0.02),
    ]
    for idx in range(9):
        p = pts[idx]
        dx, dy, dz = offsets[idx]
        ax.text(p[0] + dx, p[1] + dy, p[2] + dz, f"${idx}$", fontsize=8.5, color="#111827")

    ax.set_box_aspect([1, 1, 1])
    ax.set_xlim([-1.15, 1.15])
    ax.set_ylim([-1.15, 1.15])
    ax.set_zlim([-1.15, 1.15])
    ax.view_init(elev=19, azim=28)
    ax.set_axis_off()
    ax.set_title(r"$D_{3h}$ Tricapped Trigonal Prism $X_{\mathrm{TTP}}(z^*)$", fontsize=10.5, pad=2)
    ax.legend(loc="lower center", bbox_to_anchor=(0.5, -0.06), ncol=2, frameon=False, fontsize=8.0)

    # Right panel: inner-product spectrum bar chart of the 36 pairs
    ax2 = fig.add_subplot(1, 2, 2)
    levels = [
        (r"$\nu_0$", -0.74756053, 6, "#64748b", "top–bot opp."),
        (r"$\nu_1$", -0.71054833, 6, "#64748b", "cap–prism opp."),
        (r"$\nu_2$", -0.50000000, 3, "#64748b", "cap–cap"),
        (r"$\nu_3$",  0.00975787, 3, "#d97706", "prism vert."),
        (r"$\nu_4$",  0.24268160, 6, "#1d4ed8", "top/bot tri."),
        (r"$\nu_5$",  0.35527417, 12, "#0f766e", "cap–prism adj."),
    ]
    xs_pos = [lv[1] for lv in levels]
    mults = [lv[2] for lv in levels]
    cols = [lv[3] for lv in levels]

    ax2.axvline(-0.9, color="#b91c1c", ls=":", lw=1.2)
    ax2.axvspan(-1.0, -0.9, color="#fee2e2", alpha=0.55, label=r"Slab $[-1, -9/10]$")
    ax2.axvspan(-0.9, 1.0, color="#ecfdf5", alpha=0.35, label=r"Cap $[-9/10, 1]$")

    ax2.bar(xs_pos, mults, width=0.032, color=cols, edgecolor="#111827", linewidth=0.7, zorder=5)
    for idx, (sym, xval, mult, col, desc) in enumerate(levels):
        yoff = mult + 0.45
        if idx == 0:
            ax2.annotate(f"{sym}\n({mult})", xy=(xval, mult), xytext=(xval - 0.065, mult + 1.75),
                         fontsize=8.2, ha="center", arrowprops=dict(arrowstyle="-", lw=0.6, color="#475569"))
        elif idx == 1:
            ax2.annotate(f"{sym}\n({mult})", xy=(xval, mult), xytext=(xval + 0.085, mult + 1.75),
                         fontsize=8.2, ha="center", arrowprops=dict(arrowstyle="-", lw=0.6, color="#475569"))
        else:
            ax2.text(xval, yoff, f"{sym}\n({mult})", fontsize=8.2, ha="center", va="bottom")

    ax2.set_xlim(-1.02, 0.65)
    ax2.set_ylim(0, 15.8)
    ax2.set_xlabel(r"Pairwise inner product $t_{ij} = \langle x_i, x_j \rangle$", fontsize=9.5)
    ax2.set_ylabel("Multiplicity (total 36 pairs)", fontsize=9.5)
    ax2.set_title(r"Inner-product spectrum at $z^* \approx 0.7036484$", fontsize=10.5)
    ax2.legend(loc="upper center", bbox_to_anchor=(0.45, 0.98), frameon=True,
               facecolor="white", framealpha=0.92, fontsize=8.0)
    ax2.grid(axis="y", ls="--", alpha=0.35)

    plt.tight_layout()
    fig.savefig(OUT / "fig_ttp.pdf", bbox_inches="tight")
    fig.savefig(OUT / "fig_ttp.png", dpi=220, bbox_inches="tight")
    plt.close(fig)


def make_fig_overview():
    fig, ax = plt.subplots(figsize=(9.2, 4.3))
    ax.set_xlim(0, 100)
    ax.set_ylim(0, 48)
    ax.axis("off")

    def box(x, y, w, h, title, body, fc, ec, title_col="#0f172a"):
        p = FancyBboxPatch((x, y), w, h, boxstyle="round,pad=0.6,rounding_size=1.4",
                           facecolor=fc, edgecolor=ec, linewidth=1.3)
        ax.add_patch(p)
        ax.text(x + w / 2, y + h - 2.3, title, ha="center", va="top",
                fontsize=8.8, fontweight="bold", color=title_col)
        ax.text(x + w / 2, y + h / 2 - 1.5, body, ha="center", va="center",
                fontsize=7.6, color="#1e293b", linespacing=1.32)

    def arrow(x1, y1, x2, y2, label=None, lx=None, ly=None, col="#334155"):
        arr = FancyArrowPatch((x1, y1), (x2, y2), arrowstyle="-|>",
                              mutation_scale=11, linewidth=1.2, color=col)
        ax.add_patch(arr)
        if label:
            ax.text(lx if lx is not None else (x1 + x2) / 2,
                    ly if ly is not None else (y1 + y2) / 2,
                    label, fontsize=7.5, ha="center", va="center",
                    color=col, bbox=dict(facecolor="white", edgecolor="none", pad=1.0))

    # Top input box
    box(23, 39.2, 54, 7.8,
        r"Input: $x \in \mathrm{SphereConfig}\;9$ with $E(x) \leq E_{\mathrm{ttp,hi}}$",
        r"Case split on minimum pairwise inner product $m = \min_{i<j}\langle x_i, x_j\rangle \in [-1, 1)$",
        "#f8fafc", "#475569")

    # Left branch: Slab exclusion
    box(2, 22.0, 29, 12.2,
        r"Case 1: Slab $m \leq -9/10$",
        "Single $(2,7)$-typed 3-point SDP\n"
        r"$M=6, K=6$, scale $S_2 = 2^{72}$" + "\n"
        "Pure integer Cholesky + Kronecker\n"
        r"$\Rightarrow E(x) \geq 25.76553 > E_{\mathrm{ttp,hi}}$",
        "#fef2f2", "#dc2626", "#991b1b")

    box(2, 6.2, 29, 9.6,
        "Strict Exclusion (Contradiction)",
        r"Margin $+5.54 \times 10^{-3}$ above $E_{\mathrm{ttp,hi}}$" + "\n"
        "SlabCert.slab_exclusion\n"
        "(no minimizer possible)",
        "#fee2e2", "#b91c1c", "#7f1d1d")

    # Right branch: Cap -> Bernstein -> Rigidity -> LocalMin
    box(36, 22.0, 29, 12.2,
        r"Case 2: Cap $m \geq -9/10$",
        r"Single $S_3$-invariant 3-point SDP" + "\n"
        r"$M=10, K=10$, scale $S_2 = 2^{152}$" + "\n"
        "19 parallel 2D-Kronecker slices\n"
        r"$2\Delta_{\mathrm{cap}}-R_2 = 2.95\times 10^{-16} < 5\times 10^{-15}$",
        "#eff6ff", "#2563eb", "#1e40af")

    box(69, 22.0, 29, 12.2,
        "L3: 7-Piece Bernstein Tubes",
        r"Degree-37 $P_\varepsilon(y) \geq 0$ on 7 pieces" + "\n"
        r"Forces every pair $t_{ij}$ within" + "\n"
        r"$\rho = 10^{-4}$ of $\nu_k(z^*)$ ($k \in \{0..5\}$)" + "\n"
        "CapCert.cap_tube_forcing",
        "#f0fdf4", "#16a34a", "#166534")

    box(69, 4.5, 29, 12.2,
        "L4–L5: Rigidity & Procrustes",
        r"3-/4-pt Gram bitmasks + 28-leaf DFS" + "\n"
        r"Identifies unique $S_9$ orbit of TTP" + "\n"
        r"Procrustes $C_A \leq 18.96 \Rightarrow$" + "\n"
        r"$\|X_{\mathrm{TTP}}(z^*)-P_\sigma\mathrm{toMat}(x) Q\|_F \leq 1/500$",
        "#fefce8", "#ca8a04", "#854d0e")

    box(36, 4.5, 29, 12.2,
        "L6: Local Strict Minimality",
        r"IVT $z^* \in [z^*_{\mathrm{lo}}, z^*_{\mathrm{hi}}]$ (width $10^{-18}$)" + "\n"
        r"Compact $O(3)$ gauge + Bregman–Young" + "\n"
        r"$27\times 27$ integer Cholesky $\mu \geq 37/1000$" + "\n"
        r"$E(y)-E(P) \geq \frac{1}{30}\|g(y)-P\|_F^2$",
        "#f5f3ff", "#7c3aed", "#5b21b6")

    # Arrows (respecting FancyBboxPatch outer pad=0.6 so endpoints meet box borders cleanly)
    arrow(37, 38.55, 18, 34.85, r"$m \leq -9/10$", 21.5, 37.1, "#dc2626")
    arrow(56, 38.55, 50.5, 34.85, r"$m \geq -9/10$", 61.5, 36.9, "#2563eb")
    arrow(16.5, 21.35, 16.5, 16.45, None, col="#b91c1c")
    arrow(65.65, 28.1, 68.35, 28.1, None, col="#16a34a")
    arrow(83.5, 21.35, 83.5, 17.35, r"$\rho=10^{-4}$", 88.8, 19.35, "#ca8a04")
    arrow(68.35, 10.6, 65.65, 10.6, None, col="#7c3aed")

    # Final conclusion ribbon under L6
    ax.text(50.5, 1.3,
            r"$\Rightarrow$ Global optimality & $O(3)\times S_9$ uniqueness (thomson_nine, thomson_nine_unique, thomson_nine_main)",
            ha="center", va="center", fontsize=8.2, fontweight="bold", color="#3b0764")

    plt.tight_layout()
    fig.savefig(OUT / "fig_overview.pdf", bbox_inches="tight")
    fig.savefig(OUT / "fig_overview.png", dpi=220, bbox_inches="tight")
    plt.close(fig)


def make_fig_minorant():
    S2, H_int, R2, tubes_y = load_cap_minorant_from_lean()

    # Exact TTP nodes at z*
    z_star = 0.7036483958041318
    rho_s = np.sqrt(1.0 - z_star * z_star)
    nus = [
        -0.5 * (1 - z_star ** 2) - z_star ** 2,
        -rho_s,
        -0.5,
        1.0 - 2.0 * z_star ** 2,
        1.0 - 1.5 * (1 - z_star ** 2),
        0.5 * rho_s,
    ]

    # Sample grid concentrated near the 6 nodes and across [-0.9, 0.92]
    ts_base = np.linspace(-0.90, 0.92, 900)
    ts_fine = []
    for nu in nus:
        for delta in np.geomspace(1e-6, 0.03, 45):
            if -0.90 <= nu - delta <= 0.92:
                ts_fine.append(nu - delta)
            if -0.90 <= nu + delta <= 0.92:
                ts_fine.append(nu + delta)
        ts_fine.append(nu)
    ts = np.unique(np.concatenate([ts_base, np.array(ts_fine)]))

    # Evaluate H(t) in high precision so log10(phi - H) is accurate down to 1e-18!
    mp.mp.dps = 50
    S2_mp = mp.mpf(S2)
    coeffs_mp = [mp.mpf(c) for c in H_int]
    R2_mp = mp.mpf(str(R2))

    phi_vals = np.empty_like(ts)
    H_vals = np.empty_like(ts)
    gap_vals = np.empty_like(ts)

    for idx, tv in enumerate(ts):
        tm = mp.mpf(str(float(tv)))
        acc = mp.mpf(0)
        for c in reversed(coeffs_mp):
            acc = acc * tm + c
        h = acc / S2_mp
        ph = mp.mpf(1) / mp.sqrt(2 - 2 * tm)
        # Certified nonnegative pair gap (1 + R2) * phi(t) - H(t) >= 0
        g = (1 + R2_mp) * ph - h
        phi_vals[idx] = float(ph)
        H_vals[idx] = float(h)
        gap_vals[idx] = max(float(g), 1e-22)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.4, 3.8))

    # Left panel: phi(t) vs H(t)
    ax1.plot(ts, phi_vals, color="#0f172a", lw=2.0, label=r"$\varphi(t) = (2-2t)^{-1/2}$")
    ax1.plot(ts, H_vals, color="#dc2626", lw=1.4, ls="--", label=r"$H(t)$ (deg-18 $S_3$ minorant)")
    for k, nu in enumerate(nus):
        ph = 1.0 / np.sqrt(2.0 - 2.0 * nu)
        ax1.plot(nu, ph, "o", color="#2563eb", ms=4.5, zorder=6)
    ax1.set_xlim(-0.92, 0.95)
    ax1.set_ylim(0.5, 2.7)
    ax1.set_xlabel(r"Inner product $t = \langle x_i, x_j \rangle$", fontsize=9.5)
    ax1.set_ylabel("Pair potential value", fontsize=9.5)
    ax1.set_title(r"Cap minorant $H(t) \leq (1+R_2)\varphi(t)$ on $[-9/10, 1)$", fontsize=10.0)
    ax1.legend(loc="upper left", frameon=True, facecolor="white", framealpha=0.92, fontsize=8.2)
    ax1.grid(True, ls="--", alpha=0.35)

    # Right panel: log10 gap showing the 6 sharp zero-gap troughs and exact Bernstein locus
    eps_y = 5e-15
    bern_locus = (eps_y + R2) * phi_vals
    ax2.semilogy(ts, gap_vals, color="#1d4ed8", lw=1.25, label=r"$(1+R_2)\varphi(t) - H(t)$")
    ax2.semilogy(ts, bern_locus, color="#dc2626", ls="--", lw=1.15,
                 label=r"$P_\varepsilon(y)=0$ locus $(\varepsilon_y+R_2)\varphi(t)$")
    ax2.axhline(1.4763e-16, color="#0f766e", ls=":", lw=1.2,
                label=r"Per-pair cap budget $\Delta_{\mathrm{cap}} = 1.48\times 10^{-16}$")

    for k, nu in enumerate(nus):
        ax2.axvline(nu, color="#94a3b8", ls=":", lw=0.75, zorder=1)
        if k == 0:
            ax2.text(nu - 0.055, 2.5e-1, r"$\nu_0$", fontsize=8.0, ha="center", color="#334155")
        elif k == 1:
            ax2.text(nu + 0.055, 2.5e-1, r"$\nu_1$", fontsize=8.0, ha="center", color="#334155")
        else:
            ax2.text(nu, 2.5e-1, rf"$\nu_{k}$", fontsize=8.0, ha="center", color="#334155")

    ax2.set_xlim(-0.92, 0.92)
    ax2.set_ylim(1e-25, 1.5)
    ax2.set_xlabel(r"Inner product $t = \langle x_i, x_j \rangle$", fontsize=9.5)
    ax2.set_ylabel(r"Minorant gap $(1+R_2)\varphi(t) - H(t)$", fontsize=9.5)
    ax2.set_title(r"Six sharp troughs at $\nu_0,\dots,\nu_5$ & $P_\varepsilon(y)=0$ locus", fontsize=10.0)
    ax2.legend(loc="lower right", frameon=True, facecolor="white", framealpha=0.94, fontsize=7.5)
    ax2.grid(True, which="major", ls="--", alpha=0.35)

    plt.tight_layout()
    fig.savefig(OUT / "fig_minorant.pdf", bbox_inches="tight")
    fig.savefig(OUT / "fig_minorant.png", dpi=220, bbox_inches="tight")
    plt.close(fig)


if __name__ == "__main__":
    make_fig_ttp()
    make_fig_overview()
    make_fig_minorant()
    print("Generated fig_ttp, fig_overview, fig_minorant (.pdf and .png) in", OUT)
