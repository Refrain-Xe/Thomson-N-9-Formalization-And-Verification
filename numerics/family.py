#!/usr/bin/env python3
"""One-dimensional optimisation inside the triCapPrism family (D3h tricapped trigonal prism).

The family is the exact Python image of the Lean definition `ThomsonN9.triCapPrism` in
formal/lean/ComparatorChallenges/ThomsonN9.lean: for z in (0, 1),

  indices 0..2 : top triangle,     height +z, radius sqrt(1 - z^2), angles 2*pi*k/3
  indices 3..5 : bottom triangle,  height -z, radius sqrt(1 - z^2), angles 2*pi*k/3
  indices 6..8 : equatorial caps,  height  0, radius 1,             angles pi/3 + 2*pi*k/3.

This script
  1. minimises E(z) over z in (0, 1) (grid bracket + bounded Brent),
  2. checks the family optimum against the multistart global optimum recorded in
     reference_config.json (written by optimize.py): energies must agree, and the multisets of
     pairwise distances must agree (a rotation-invariant fingerprint of the configuration),
  3. reports z* next to the expected value ~0.70365 quoted in the N = 7 challenge file.

Exits 1 if any consistency check fails or reference_config.json is missing.
"""
from __future__ import annotations

import json
import os
import sys

import numpy as np
from scipy.optimize import minimize_scalar

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from energy import coulomb_energy, pairwise_distances  # noqa: E402

REF_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "reference_config.json")
EXPECTED_Z = 0.70365          # quoted in references/.../ThomsonN7.lean (triCapPrism docstring)
Z_TOL = 1e-3                  # sanity tolerance for the reported constant only
ENERGY_TOL = 1e-7             # family optimum vs multistart global optimum
DIST_TOL = 1e-6               # sorted pairwise-distance spectra


def tri_cap_prism(z: float) -> np.ndarray:
    """The D3h tricapped trigonal prism with height parameter z, matching triCapPrism in Lean."""
    rho = np.sqrt(1.0 - z * z)
    pts = []
    for k in range(3):
        pts.append((rho * np.cos(2 * np.pi * k / 3), rho * np.sin(2 * np.pi * k / 3), z))
    for k in range(3):
        pts.append((rho * np.cos(2 * np.pi * k / 3), rho * np.sin(2 * np.pi * k / 3), -z))
    for k in range(3):
        pts.append((np.cos(np.pi / 3 + 2 * np.pi * k / 3), np.sin(np.pi / 3 + 2 * np.pi * k / 3), 0.0))
    return np.array(pts)


def family_energy(z: float) -> float:
    return coulomb_energy(tri_cap_prism(z))


def main() -> int:
    if not os.path.exists(REF_FILE):
        print(f"missing {REF_FILE}: run optimize.py first")
        return 1
    with open(REF_FILE) as f:
        ref = json.load(f)
    e_global = float(ref["energy"])
    X_global = np.array([[float(v) for v in row] for row in ref["coordinates"]])

    # 1. locate the family optimum: coarse grid, then Brent in the best bracket
    grid = np.linspace(1e-4, 1 - 1e-4, 2000)
    vals = np.array([family_energy(z) for z in grid])
    i = int(np.argmin(vals))
    lo, hi = grid[max(i - 1, 0)], grid[min(i + 1, len(grid) - 1)]
    res = minimize_scalar(family_energy, bounds=(lo, hi), method="bounded",
                          options={"xatol": 1e-13})
    z_star = float(res.x)
    e_family = float(res.fun)

    print(f"family optimum:  z* = {z_star:.12f}   E(z*) = {e_family:.12f}")
    print(f"expected z ~ {EXPECTED_Z} (quoted constant),  difference {abs(z_star - EXPECTED_Z):.3e}")
    print(f"global optimum (optimize.py): E = {e_global:.12f}")
    print(f"|E(z*) - E_global| = {abs(e_family - e_global):.3e}")

    # 2a. energy consistency
    if abs(e_family - e_global) >= ENERGY_TOL:
        print(f"CONSISTENCY FAILED: family energy differs from the global optimum by >= {ENERGY_TOL}")
        return 1

    # 2b. structural consistency: sorted pairwise-distance spectra must coincide
    d_family = np.sort(pairwise_distances(tri_cap_prism(z_star)))
    d_global = np.sort(pairwise_distances(X_global))
    dmax = float(np.max(np.abs(d_family - d_global)))
    print(f"max |pairwise-distance spectrum difference| = {dmax:.3e}")
    if dmax >= DIST_TOL:
        print(f"CONSISTENCY FAILED: distance spectra differ by >= {DIST_TOL}")
        return 1

    # 3. sanity of the quoted constant (advisory only)
    if abs(z_star - EXPECTED_Z) >= Z_TOL:
        print(f"WARNING: z* deviates from the quoted constant {EXPECTED_Z} by more than {Z_TOL}")

    print("FAMILY CONSISTENCY OK: the multistart global optimum is the tricapped trigonal prism")
    return 0


if __name__ == "__main__":
    sys.exit(main())
