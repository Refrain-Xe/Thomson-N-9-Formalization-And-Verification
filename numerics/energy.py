#!/usr/bin/env python3
"""Coulomb energy of point configurations on the unit sphere (Thomson problem, N = 9 package).

E(x) = sum_{i<j} 1 / ||x_i - x_j||,  x_i in R^3, ||x_i|| = 1.

This mirrors the Lean definition `ThomsonN9.coulombEnergy` in
formal/lean/ComparatorChallenges/ThomsonN9.lean (sum over i of sum over j > i of ||x i - x j||⁻¹):
same pairs, same order-insensitive sum. Coincident points make the energy infinite; here that is
an error rather than +infinity, so that a silent collapse can never look like a low energy.
"""
from __future__ import annotations

import numpy as np


def pairwise_distances(X) -> np.ndarray:
    """All pairwise distances as a flat array of length n(n-1)/2, in (i, j) lexicographic order."""
    X = np.asarray(X, dtype=float)
    n = X.shape[0]
    if X.ndim != 2 or X.shape[1] != 3:
        raise ValueError(f"expected an (n, 3) array of coordinates, got shape {X.shape}")
    iu = np.triu_indices(n, k=1)
    diff = X[iu[0]] - X[iu[1]]
    return np.sqrt(np.einsum("ij,ij->i", diff, diff))


def coulomb_energy(X) -> float:
    """Coulomb energy sum_{i<j} 1/||x_i - x_j|| of an (n, 3) coordinate array."""
    d = pairwise_distances(X)
    if np.any(d <= 0.0):
        raise ValueError("coincident points: the Coulomb energy is infinite")
    return float(np.sum(1.0 / d))


if __name__ == "__main__":
    # smoke test: the regular octahedron (N = 6, known energy 3 + 6*sqrt(2)/2 ... in fact
    # 12 edges at distance sqrt(2) and 3 antipodal pairs at distance 2, so E = 12/sqrt(2) + 3/2.
    octa = np.array([[1, 0, 0], [-1, 0, 0], [0, 1, 0], [0, -1, 0], [0, 0, 1], [0, 0, -1]], float)
    E = coulomb_energy(octa)
    expected = 12 / np.sqrt(2) + 3 / 2
    print(f"octahedron energy: {E:.15f}  expected {expected:.15f}  diff {abs(E - expected):.2e}")
    assert abs(E - expected) < 1e-12
    print("energy.py smoke test OK")
