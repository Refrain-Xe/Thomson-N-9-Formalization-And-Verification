#!/usr/bin/env python3
"""Global multistart optimisation of the 9-point Coulomb energy on the unit sphere.

Runs >= 40 random starts (64 here, fixed seed, so the output reference_config.json is
reproducible), minimises with SLSQP under the constraints ||x_i|| = 1, polishes the best
solutions, and finally checks the best energy against the literature value for the D3h
tricapped trigonal prism. On success writes the optimal coordinates with 17 significant
digits to reference_config.json (next to this script) and exits 0; on any mismatch it
exits 1 (the workflow treats the exit code as an acceptance gate).

Reference energy: E_9 = 25.759986531... is NOT hard-coded here. It is read at run time from
thomson-workflow/data/energies.json (`energies.9.value`, the three-source-verified single
source of truth; same table also states the D3h tricapped trigonal prism configuration).
Acceptance: |E_best - E_9| < 1e-6.

--selftest runs a negative control of that acceptance gate: after the same optimisation, the
exact assertion path is walked with a deliberately wrong reference (true value +/- 0.5); the
rejection must trigger for both signs (and the true reference must be accepted), otherwise the
selftest fails. The real mode is unchanged: exit 0 on acceptance, 1 on mismatch, and only the
real mode writes reference_config.json.
"""
from __future__ import annotations

import json
import os
import sys

import numpy as np
from scipy.optimize import minimize

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from energy import coulomb_energy  # noqa: E402

N = 9
N_STARTS = 64          # >= 40 required by the acceptance standard
SEED = 20261002
TOLERANCE = 1e-6
# Sole trusted source of the reference energy (three-source-verified: Wikipedia, Wales-Ulker
# CCD update source Deeter, local recompute). thomson-workflow/data/energies.json says
# energies.9 = {value: 25.759986531, highPrecision: 25.759986531270, status: "confirmed"};
# if that file ever disagrees with anything here, the file wins and the mismatch is escalated.
ENERGIES_JSON = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                             "..", "..", "thomson-workflow", "data", "energies.json")
OUT_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "reference_config.json")


def load_reference_energy() -> float:
    """E_9 from thomson-workflow/data/energies.json, failing loudly if it is unavailable.

    No silent fallback to a hard-coded constant: a gate that silently switched to a baked-in
    number would defeat the point of sourcing the reference from the calibrated file.
    """
    try:
        with open(ENERGIES_JSON) as f:
            data = json.load(f)
    except (OSError, json.JSONDecodeError) as exc:
        print(f"cannot read {ENERGIES_JSON}: {exc}")
        print("the reference energy is sourced only from thomson-workflow/data/energies.json")
        raise SystemExit(1)
    try:
        entry = data["energies"]["9"]
        value = float(entry["value"])
        high = float(entry["highPrecision"])
        status = entry["status"]
    except (KeyError, TypeError, ValueError) as exc:
        print(f"malformed N=9 entry in {ENERGIES_JSON}: {exc}")
        raise SystemExit(1)
    if status != "confirmed":
        print(f"N=9 entry in {ENERGIES_JSON} has status {status!r}, expected 'confirmed'")
        raise SystemExit(1)
    if abs(value - high) > 1e-6:
        print(f"inconsistent N=9 entry in {ENERGIES_JSON}: value {value} vs highPrecision {high}")
        raise SystemExit(1)
    print(f"reference energy: {ENERGIES_JSON}")
    print(f"  N=9 value {value} (highPrecision {high}, status {status})")
    return value


def random_start(rng: np.random.Generator) -> np.ndarray:
    """9 random points on the sphere (normalised Gaussians), a fresh basin per start."""
    X = rng.standard_normal((N, 3))
    return X / np.linalg.norm(X, axis=1, keepdims=True)


def total_energy(flat: np.ndarray) -> float:
    return coulomb_energy(flat.reshape(N, 3))


def norm_constraints():
    return [{"type": "eq", "fun": (lambda v, i=i: float(v[3 * i:3 * i + 3] @ v[3 * i:3 * i + 3] - 1.0))}
            for i in range(N)]


def run_slsqp(x0: np.ndarray, ftol: float, maxiter: int):
    return minimize(total_energy, x0.ravel(), method="SLSQP",
                    constraints=norm_constraints(),
                    options={"maxiter": maxiter, "ftol": ftol})


def polish(x: np.ndarray) -> tuple[float, np.ndarray]:
    """Re-run SLSQP from x with tighter tolerances until it stops improving."""
    for _ in range(6):
        res = run_slsqp(x, ftol=1e-16, maxiter=5000)
        if res.fun >= total_energy(x) - 1e-16:
            x = res.x
            break
        x = res.x
    return total_energy(x), x


def accepted(e_best: float, reference: float, tolerance: float) -> bool:
    """The acceptance assertion path, shared verbatim by the real run and --selftest."""
    if abs(e_best - reference) >= tolerance:
        print(f"ACCEPTANCE FAILED: |E_best - {reference}| >= {tolerance}")
        return False
    return True


def selftest(e_best: float, reference: float, delta: float = 0.5) -> int:
    """Negative control: the acceptance gate must reject a deliberately wrong reference.

    Walks the very same `accepted` path as the real run with the poisoned reference
    `reference + delta` and `reference - delta`. Each poisoned reference must TRIGGER the
    rejection; the triggered assertion is caught here, and only if every expectation holds
    does this print PASS and return 0. The true reference must also be accepted (the
    control's own control), otherwise the whole gate is broken.
    """
    ok = True
    if accepted(e_best, reference, TOLERANCE):
        print("selftest: true reference accepted by the gate (control of the control)")
    else:
        print("SELFTEST FAILED: the gate rejected the TRUE reference")
        ok = False
    for d in (delta, -delta):
        wrong = reference + d
        try:
            assert not accepted(e_best, wrong, TOLERANCE), \
                f"the gate ACCEPTED the wrong reference {wrong}"
        except AssertionError as exc:
            print(f"SELFTEST FAILED: {exc}")
            ok = False
            continue
        print(f"selftest: wrong reference {wrong} triggered the assertion, as required")
    if not ok:
        print("SELFTEST FAILED: the acceptance gate cannot be trusted")
        return 1
    print(f"SELFTEST PASS: the acceptance gate rejects wrong references (+/- {delta})")
    return 0


def parse_args(argv: list[str]) -> int:
    """Return 1 for --selftest mode, 0 for the real run; exit(2) on unknown arguments."""
    unknown = [a for a in argv if a != "--selftest"]
    if unknown:
        print(f"unknown arguments {unknown}: only --selftest is supported")
        raise SystemExit(2)
    return 1 if "--selftest" in argv else 0


def main() -> int:
    selftest_mode = parse_args(sys.argv[1:])
    reference_energy = load_reference_energy()
    rng = np.random.default_rng(SEED)
    results = [run_slsqp(random_start(rng), ftol=1e-12, maxiter=2000) for _ in range(N_STARTS)]
    results.sort(key=lambda r: r.fun)

    e_best, x_flat = polish(results[0].x)
    for res in results[1:8]:
        e, x = polish(res.x)
        if e < e_best:
            e_best, x_flat = e, x
    X = x_flat.reshape(N, 3)

    # report the basin statistics: how many raw starts landed at the best value
    at_best = sum(1 for r in results if abs(r.fun - e_best) < 1e-6)
    distinct = sorted({round(r.fun, 6) for r in results})
    print(f"starts: {N_STARTS}   seed: {SEED}")
    print(f"local minima found (6 d.p.): {distinct}")
    print(f"starts reaching the best basin: {at_best}")
    print(f"best energy: {e_best:.12f}")
    print(f"reference:   {reference_energy}   |diff| = {abs(e_best - reference_energy):.3e}")

    norms = np.linalg.norm(X, axis=1)
    print(f"norm deviation from 1: max {np.max(np.abs(norms - 1)):.2e}")

    if selftest_mode:
        # negative control of the gate; no file is written in this mode
        return selftest(e_best, reference_energy)

    if not accepted(e_best, reference_energy, TOLERANCE):
        return 1

    payload = {
        "n": N,
        "energy": e_best,
        "reference_energy": reference_energy,
        "tolerance": TOLERANCE,
        "seed": SEED,
        "starts": N_STARTS,
        "conjectured_minimizer": "D3h tricapped trigonal prism (triCapPrism z*, z* ~ 0.70365)",
        "note": "coordinates are only defined up to a global rotation; family.py identifies the "
                "configuration through the (rotation-invariant) multiset of pairwise distances",
        "coordinates": [[format(v, ".17g") for v in row] for row in X],
    }
    with open(OUT_FILE, "w") as f:
        json.dump(payload, f, indent=2, sort_keys=True)
        f.write("\n")
    print(f"wrote {OUT_FILE}")
    print("ACCEPTANCE OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
