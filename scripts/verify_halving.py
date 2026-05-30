#!/usr/bin/env python3
"""Run the exact verification API and an independent rational rederivation."""
from __future__ import annotations

from fractions import Fraction as F
from pathlib import Path
import sys

HERE = Path(__file__).resolve()
CANDIDATES = [HERE.parent, HERE.parents[1] if len(HERE.parents) > 1 else HERE.parent, Path.cwd()]
for candidate in CANDIDATES:
    if (candidate / "kalton_api.py").exists():
        sys.path.insert(0, str(candidate))
        break
else:
    raise RuntimeError("Could not find kalton_api.py next to this script or in the repository root")

import kalton_api as kr  # noqa: E402


def independent_rederivation() -> dict[str, F]:
    """Recompute the final constants without calling kalton_api.case_constants().

    This duplicates the algebra in the paper directly: choose q0, choose the two
    frequency caps, solve for the mixing parameters, form the two affine bounds,
    and balance them.  It is intentionally written independently of the API's
    helper functions so that the command-line verifier has a second exact route
    to the headline constant.
    """
    q0 = F(7437, 15625)
    p0 = F(1) - q0
    alpha1 = F(1003, 10000)
    alpha2 = F(47, 625)
    alpha1_target = F(3009, 10000)
    alpha2_target = F(329, 1250)

    tau1 = (q0**3 - alpha1) / (q0**3 - q0**4)
    tau2 = (p0**4 - alpha2) / (p0**4 - p0**5)

    assert (F(1) - tau1) * q0**3 + tau1 * q0**4 == alpha1
    assert (F(1) - tau2) * p0**4 + tau2 * p0**5 == alpha2
    assert alpha1 / F(1, 3) == alpha1_target
    assert alpha2 / F(2, 7) == alpha2_target
    assert F(1, 16) < alpha2

    # Case 1: E=q(1-u) <= 2q0 and the mixed triple/fourfold deficit is
    # 3E+4+tau1(E+2).
    D1 = F(6) * q0 + F(4) + tau1 * (F(2) * q0 + F(2))
    A1 = F(10) + F(3, 2) * D1  # first expander (theta=1/3)
    y1 = (A1 - F(15)) / (F(1, 2) + F(7, 3))
    C1_left = A1 - F(1, 2) * y1
    C1_right = F(15) + F(7, 3) * y1

    # Case 2: A^{cap 4} on the deficit side and mixed 4/5 intersections
    # on the surplus side.
    X0 = F(4) * p0 + F(6) + tau2 * (p0 + F(1))
    A2 = F(47, 5) + F(7, 5) * X0  # first two-sided expander (theta=2/7)
    y2 = (A2 - F(47, 3)) / (F(2, 5) + F(11, 6))
    C2_left = A2 - F(2, 5) * y2
    C2_right = F(47, 3) + F(11, 6) * y2

    assert C1_left == C1_right
    assert C2_left == C2_right

    return {
        "q0": q0,
        "p0": p0,
        "alpha1": alpha1,
        "alpha2": alpha2,
        "alpha1_target": alpha1_target,
        "alpha2_target": alpha2_target,
        "tau1": tau1,
        "tau2": tau2,
        "D1": D1,
        "A1": A1,
        "y1": y1,
        "C1": C1_left,
        "X0": X0,
        "A2": A2,
        "y2": y2,
        "C2": C2_left,
        "Cmax": max(C1_left, C2_left),
    }


def main() -> None:
    result = kr.run_all_checks(verbose=False)
    constants = result["constants"]
    independent = independent_rederivation()

    for key in (
        "q0",
        "p0",
        "alpha1",
        "alpha2",
        "alpha1_target",
        "alpha2_target",
        "tau1",
        "tau2",
        "C1",
        "C2",
        "Cmax",
    ):
        assert independent[key] == constants[key], (key, independent[key], constants[key])

    print("API exact-arithmetic checks passed.")
    print("Independent rational rederivation passed.")
    print(f"C1={constants['C1']} = {float(constants['C1']):.12f}")
    print(f"C2={constants['C2']} = {float(constants['C2']):.12f}")
    print(f"Cmax={constants['Cmax']} < {kr.FINAL_SAFE_BOUND} = {float(kr.FINAL_SAFE_BOUND):.12f}")
    print("All checks passed.")


if __name__ == "__main__":
    main()
