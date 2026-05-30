"""Exact rational API for the Kalton--Roberts sub-19.838 bound.

The module uses only Python's standard library. It is meant to be imported
from the accompanying Jupyter notebook without installing the package.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from typing import Dict, List, Tuple
import math

Interval = Tuple[F, F]
LOG_TERMS = 140
DELTA = F(1, 100)
E2_UPPER = F(739, 100)  # e^2 < 7.39
ENDPOINT_MARGIN = F(1, 1000)
FINAL_SAFE_BOUND = F(9919, 500)  # 19.838


def exp_upper_bound(n: int = 10) -> F:
    """A rational upper bound for e from its Taylor series and a geometric tail."""
    partial = sum(F(1, math.factorial(k)) for k in range(n + 1))
    # Tail from 1/(n+1)! onward; subsequent ratios are at most 1/(n+2).
    tail = F(1, math.factorial(n + 1)) * F(n + 2, n + 1)
    return partial + tail


def verify_e_squared_bound() -> F:
    """Certify e^2 < 739/100 using only rational arithmetic."""
    e_upper = exp_upper_bound(10)
    assert e_upper * e_upper < E2_UPPER, (e_upper, e_upper * e_upper, E2_UPPER)
    return e_upper


@dataclass(frozen=True)
class ExpanderCase:
    name: str
    alpha: F
    r: int
    theta: F


EXPANDERS: Tuple[ExpanderCase, ...] = (
    ExpanderCase("E1", F(1003, 10000), 4, F(1, 3)),
    ExpanderCase("E2", F(3009, 10000), 4, F(4, 7)),
    ExpanderCase("E3", F(47, 625), 4, F(2, 7)),
    ExpanderCase("E4", F(329, 1250), 5, F(5, 11)),
)


def add_interval(x: Interval, y: Interval) -> Interval:
    return (x[0] + y[0], x[1] + y[1])


def neg_interval(x: Interval) -> Interval:
    return (-x[1], -x[0])


def scale_interval(c: F, x: Interval) -> Interval:
    if c >= 0:
        return (c * x[0], c * x[1])
    return (c * x[1], c * x[0])


def _log2_interval(n: int = LOG_TERMS) -> Interval:
    # log 2 = 2 atanh(1/3).
    t = F(1, 3)
    total = F(0)
    power = t
    for k in range(n):
        total += F(2) * power / F(2 * k + 1)
        power *= t * t
    remainder = F(2) * power / (F(2 * n + 1) * (F(1) - t * t))
    return (total, total + remainder)


_LOG2 = _log2_interval()


def log_interval(z: F, n: int = LOG_TERMS) -> Interval:
    """Return a rigorous rational interval containing log(z)."""
    if z <= 0:
        raise ValueError("log input must be positive")
    if z == 1:
        return (F(0), F(0))

    y = z
    exponent = 0
    while y < 1:
        y *= 2
        exponent -= 1
    while y > 2:
        y /= 2
        exponent += 1

    # 1 <= y <= 2, hence 0 <= t <= 1/3.
    t = (y - 1) / (y + 1)
    total = F(0)
    power = t
    for j in range(n):
        total += F(2) * power / F(2 * j + 1)
        power *= t * t
    remainder = F(2) * power / (F(2 * n + 1) * (F(1) - t * t))
    base = (total, total + remainder)
    if exponent == 0:
        return base
    return add_interval(base, scale_interval(F(exponent), _LOG2))


def entropy_interval(a: F, b: F) -> Interval:
    """Interval for h(a,b)=a log a-b log b-(a-b) log(a-b)."""
    if not (a > 0 and 0 <= b <= a):
        raise ValueError(f"bad entropy arguments a={a}, b={b}")
    c = a - b
    out: Interval = (F(0), F(0))
    out = add_interval(out, scale_interval(a, log_interval(a)))
    if b:
        out = add_interval(out, scale_interval(-b, log_interval(b)))
    if c:
        out = add_interval(out, scale_interval(-c, log_interval(c)))
    return out


def phi_interval(r: int, theta: F, x: F) -> Interval:
    """Interval for the Pippenger entropy exponent Phi_{r,theta}(x)."""
    out = entropy_interval(F(1), x)
    out = add_interval(out, entropy_interval(theta, x))
    out = add_interval(out, entropy_interval(F(r) * x / theta, F(r) * x))
    out = add_interval(out, neg_interval(entropy_interval(F(r), F(r) * x)))
    return out


def phi_second_lower(r: int, theta: F, alpha: F, delta: F = DELTA) -> F:
    """A rational lower bound for Phi'' on [delta, alpha]."""
    return F(r - 2) / alpha + F(r - 1) / (F(1) - delta) - F(1) / (theta - alpha)


def expander_certificate(case: ExpanderCase) -> Dict[str, object]:
    small_base = E2_UPPER * case.theta ** (1 - case.r) * DELTA ** (case.r - 2)
    second_lower = phi_second_lower(case.r, case.theta, case.alpha)
    delta_interval = phi_interval(case.r, case.theta, DELTA)
    alpha_interval = phi_interval(case.r, case.theta, case.alpha)
    return {
        "name": case.name,
        "alpha": case.alpha,
        "r": case.r,
        "theta": case.theta,
        "small_base": small_base,
        "phi_second_lower": second_lower,
        "phi_delta": delta_interval,
        "phi_alpha": alpha_interval,
    }


def verify_expanders(verbose: bool = False) -> List[Dict[str, object]]:
    verify_e_squared_bound()
    rows = []
    for case in EXPANDERS:
        row = expander_certificate(case)
        assert row["small_base"] < F(1, 20), (case.name, row["small_base"])
        assert row["phi_second_lower"] > F(3), (case.name, row["phi_second_lower"])
        assert row["phi_delta"][1] < -ENDPOINT_MARGIN, (case.name, row["phi_delta"])
        assert row["phi_alpha"][1] < -ENDPOINT_MARGIN, (case.name, row["phi_alpha"])
        rows.append(row)
        if verbose:
            print(
                f"{case.name}: alpha={case.alpha}, r={case.r}, theta={case.theta}, "
                f"small_base={row['small_base']} < 1/20; "
                f"Phi'' lower={row['phi_second_lower']} > 3; "
                f"endpoints < -{ENDPOINT_MARGIN}"
            )
    return rows


def case_constants() -> Dict[str, F]:
    q0 = F(7437, 15625)
    p0 = F(1) - q0
    alpha1 = F(1003, 10000)
    alpha2 = F(47, 625)
    alpha1_target = F(3009, 10000)
    alpha2_target = F(329, 1250)

    tau1 = (q0 ** 3 - alpha1) / (q0 ** 3 - q0 ** 4)
    tau2 = (p0 ** 4 - alpha2) / (p0 ** 4 - p0 ** 5)

    # Case 1: mixed triple/fourfold intersections on the A-side.
    D1 = F(6) * q0 + F(4) + tau1 * (F(2) * q0 + F(2))
    A1 = F(10) + F(3, 2) * D1
    y1 = (A1 - F(15)) / (F(1, 2) + F(7, 3))
    C1 = A1 - F(1, 2) * y1

    # Case 2: A^{cap 4} on the deficit side and a mixed 4/5 intersection
    # on the surplus side.
    X0 = F(4) * p0 + F(6) + tau2 * (p0 + F(1))
    A2 = F(47, 5) + F(7, 5) * X0
    y2 = (A2 - F(47, 3)) / (F(2, 5) + F(11, 6))
    C2 = A2 - F(2, 5) * y2

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
        "C1": C1,
        "X0": X0,
        "A2": A2,
        "y2": y2,
        "C2": C2,
        "Cmax": max(C1, C2),
    }


def verify_final_arithmetic(verbose: bool = False) -> Dict[str, F]:
    c = case_constants()
    q0, p0 = c["q0"], c["p0"]
    alpha1, alpha2 = c["alpha1"], c["alpha2"]
    tau1, tau2 = c["tau1"], c["tau2"]

    assert F(0) <= tau1 <= F(1)
    assert F(0) <= tau2 <= F(1)
    assert (F(1) - tau1) * q0 ** 3 + tau1 * q0 ** 4 == alpha1
    assert (F(1) - tau2) * p0 ** 4 + tau2 * p0 ** 5 == alpha2

    assert alpha1 / F(1, 3) == c["alpha1_target"]
    assert alpha2 / F(2, 7) == c["alpha2_target"]
    assert F(1, 16) < alpha2

    # Check the displayed balances.
    assert c["C1"] == c["A1"] - F(1, 2) * c["y1"]
    assert c["C1"] == F(15) + F(7, 3) * c["y1"]
    assert c["C2"] == c["A2"] - F(2, 5) * c["y2"]
    assert c["C2"] == F(47, 3) + F(11, 6) * c["y2"]

    assert c["C1"] == F(23662339508853784054849, 1192830849380162250000)
    assert c["C2"] == F(694198146664396294486127753, 34994834677886019996000000)
    assert c["Cmax"] == c["C2"]
    assert c["C1"] < c["C2"] < FINAL_SAFE_BOUND

    if verbose:
        print(f"q0={q0}; p0={p0}; tau1={tau1}; tau2={tau2}")
        print(f"Case 1 constant C1={c['C1']} = {float(c['C1']):.12f}")
        print(f"Case 2 constant C2={c['C2']} = {float(c['C2']):.12f}")
        print(f"Final bound Cmax={c['Cmax']} < {FINAL_SAFE_BOUND} = {float(FINAL_SAFE_BOUND):.12f}")
    return c


def run_all_checks(verbose: bool = True) -> Dict[str, object]:
    constants = verify_final_arithmetic(verbose=verbose)
    expanders = verify_expanders(verbose=verbose)
    if verbose:
        print("All checks passed.")
    return {"constants": constants, "expanders": expanders}


def decimal(frac: F, digits: int = 12) -> str:
    return f"{float(frac):.{digits}f}"


def summary_table() -> List[Dict[str, str]]:
    c = case_constants()
    rows: List[Dict[str, str]] = [
        {"quantity": "q0", "exact": str(c["q0"]), "decimal": decimal(c["q0"])},
        {"quantity": "p0", "exact": str(c["p0"]), "decimal": decimal(c["p0"])},
        {"quantity": "tau1", "exact": str(c["tau1"]), "decimal": decimal(c["tau1"])},
        {"quantity": "tau2", "exact": str(c["tau2"]), "decimal": decimal(c["tau2"])},
        {"quantity": "C1", "exact": str(c["C1"]), "decimal": decimal(c["C1"])},
        {"quantity": "C2", "exact": str(c["C2"]), "decimal": decimal(c["C2"])},
        {"quantity": "Cmax", "exact": str(c["Cmax"]), "decimal": decimal(c["Cmax"])},
        {"quantity": "safe bound", "exact": str(FINAL_SAFE_BOUND), "decimal": decimal(FINAL_SAFE_BOUND)},
    ]
    return rows


def main() -> None:
    run_all_checks(verbose=True)


if __name__ == "__main__":
    main()
