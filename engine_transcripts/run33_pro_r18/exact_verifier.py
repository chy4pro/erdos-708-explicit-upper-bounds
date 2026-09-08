#!/usr/bin/env python3
"""Exact-arithmetic certificate-constant verifier for H_(97/10).

Python 3.10+; standard library only. No floating-point arithmetic is used.
Usage:
  python exact_verifier.py --output constants.json
This checks the finite numerical assertions and the infinite-tail bounds in
the accompanying proof. It is not a formal proof-assistant/kernel proof.
"""
from __future__ import annotations
from fractions import Fraction as F
from math import comb, factorial, floor
from functools import lru_cache
from pathlib import Path
import argparse
import json
import sys

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

Q = 65536
H = F(1025, 1024)
GAMMA = F(211, 210)
K = F(8, 3)
LAMBDA = F(51, 10)
RHO = F(5, 4)
LOSS = F(47, 16)
T = F(541, 100)
C = F(97, 10)
A0 = F(4377, 100000)
Z = F(9, 2)
D = 4

def check(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)

def ceil_fraction(x: F) -> int:
    return -((-x.numerator) // x.denominator)

def decimal_interval(x: F, digits: int = 12) -> str:
    """An outward rational decimal interval, never a floating-point value."""
    den = 10**digits
    lo = (x.numerator * den) // x.denominator
    return f"[{lo}/{den}, {lo+1}/{den}]"

@lru_cache(None)
def exponents(j: int, L: int) -> tuple[int, ...]:
    es = set()
    a = 1
    while a*D <= L:
        for b in range(D, 2*D):
            v = a*b
            if j <= v <= L:
                es.add(v)
        a *= 2
    return tuple(sorted(es))

@lru_cache(None)
def carrier_counts(j: int, L: int, Nmax: int) -> tuple[tuple[int, ...], ...]:
    """Coefficients of G^N-(G-X^j)^N at degrees L+1,...,L+j."""
    es = exponents(j, L)
    check(j in es, "last level must be present")
    maxdeg = L+j
    full = [0]*(maxdeg+1)
    omit = [0]*(maxdeg+1)
    full[0] = omit[0] = 1
    rows = []
    for N in range(Nmax+1):
        row = tuple(full[L+d]-omit[L+d] for d in range(1, j+1))
        check(all(a >= 0 for a in row), "nonnegative carrier counts")
        rows.append(row)
        if N < Nmax:
            full = [
                v + sum(full[i-e] for e in es if e <= i)
                for i, v in enumerate(full)
            ]
            omit = [
                v + sum(omit[i-e] for e in es if e != j and e <= i)
                for i, v in enumerate(omit)
            ]
    return tuple(rows)

def epsilon(theta: F, mass: F, threshold: F = T) -> tuple[F, int, int, F]:
    """Best of the proved elementary-symmetric majorants, with exact arithmetic.

    a=(threshold-mass)/theta; r in [2,floor(a)+1];
    v=floor(r*a/(r-1)); A=(v-a)/binom(v,r).
    """
    a = (threshold-mass)/theta
    candidates = []
    for r in range(2, floor(a)+2):
        v = floor(r*a/(r-1))
        check(v >= r and v > a, "valid scalar-majorant maximizing vertex")
        A = (v-a)/comb(v, r)
        eps = theta*A*(H/theta)**r/factorial(r)
        candidates.append((eps, r, v, A))
    check(bool(candidates), "nonempty moment family")
    return min(candidates)

def scale_bound(j: int, L: int, threshold: F = T, slope: F = K) -> dict:
    theta = F(j, L)
    eps = [epsilon(theta, 1+F(d, L), threshold) for d in range(1, j+1)]
    Nmax = floor((slope+1)/theta+1)
    rows = carrier_counts(j, L, Nmax)
    best = F(0)
    argmax = 0
    for N, counts in enumerate(rows):
        val = F(0)
        for d, count in enumerate(counts, 1):
            if not count:
                continue
            mass = 1+F(d, L)
            numerator = max(F(0), 1-max(F(0), N*theta-mass)/slope)
            denominator = max(F(d, L), N*theta-1)
            val += count*eps[d-1][0]*numerator/denominator
        if val > best:
            best, argmax = val, N
    return {
        "j": j, "L": L, "theta": theta, "bound": best,
        "maximizing_N": argmax, "Nmax": Nmax,
        "moments": [
            {"d": d, "mass": 1+F(d, L), "epsilon": ep,
             "r": r, "maximizing_vertex": v, "vertex_constant": A}
            for d, (ep, r, v, A) in enumerate(eps, 1)
        ],
    }

def exp_upper(a: F, n: int) -> F:
    check(a >= 0 and a < n+2, "geometric exponential-tail condition")
    partial = sum((a**i/F(factorial(i)) for i in range(n+1)), F(0))
    return partial + a**(n+1)/factorial(n+1)/(1-a/F(n+2))

def fj_upper(j: int, x: F) -> F:
    # All omitted exponents are distinct integers >=128.
    return (
        1 + sum((x**a for a in range(j, 8)), F(0))
        + sum((x**(a*2**r) for r in range(1, 5) for a in range(4, 8)), F(0))
        + x**128/(1-x)
    )

def retention_knapsack(j: int, L: int) -> F:
    """EXHAUSTIVE finite multiset check of the carrier modulus exponent.

    Remove one last theta. The preceding mass is <=1 and >1-theta.
    All available values are >=theta. Costs are 9L times the exponent.
    """
    es = exponents(j, L)
    cost = lambda v: 3*L if 2*v > L else 4*v
    dp: list[int | None] = [None]*(L+1)
    dp[0] = 0
    for s in range(1, L+1):
        choices = [
            dp[s-v]+cost(v) for v in es
            if v <= s and dp[s-v] is not None
        ]
        if choices:
            dp[s] = max(choices)
    best = max(
        dp[s]+cost(j) for s in range(L-j+1, L+1)
        if dp[s] is not None
    )
    return F(best, 9*L)

def encode(obj):
    if isinstance(obj, F):
        return {"numerator": str(obj.numerator), "denominator": str(obj.denominator)}
    raise TypeError(type(obj).__name__)

def run() -> dict:
    check(LOSS+RHO*T == C, "threshold identity")
    check(F(2)+F(45,16)/3 == LOSS, "rounding-loss identity")
    check(C >= 7, "large-atom and dense branches")
    check(2*3*5*7*11*13*17 > Q, "large-atom primorial bound")
    check(2*3*5*7 == 210, "nonzero-carrier cofactor bound")

    dense = (1-F(1,Q))*H-H**8/factorial(8)
    check(dense > 1, "dense branch")

    window = LAMBDA*(1-2*GAMMA*H/K)
    check(window == F(718539,573440), "window-value exact fraction")
    check(window > RHO, "window coefficient exceeds rounding factor")

    cases = [(4,4)] + [(j,L) for L in (8,16,32,64,128,256,512) for j in range(4,8)]
    scales = [scale_bound(j,L) for j,L in cases]
    groups = {}
    retention = []
    for (j,L), row in zip(cases, scales):
        groups[L] = groups.get(L,F(0)) + row["bound"]
        exponent = retention_knapsack(j,L)
        check(exponent <= F(2,3), "finite carrier-modulus audit")
        retention.append({"j":j, "L":L, "maximum_exponent":exponent})
    bounds = {4:24680, 8:128711, 16:25773, 32:5665, 64:1025, 128:150, 256:21, 512:3}
    for L, b in bounds.items():
        check(groups[L] < F(b,10**6), f"finite group {L}")
    finite = sum(groups.values(), F(0))
    check(finite < F(187,1000), "total finite part")

    # Elementary bounds used to remove exponentials and logarithms from the tail check.
    E = F(87,32)
    check(exp_upper(F(1),8) < E, "e < 87/32")
    check(E**3 < Z**2, "log(9/2) > 3/2")
    check(sum((F(1,factorial(i)) for i in range(5)),F(0)) > F(8,3), "e > 8/3")
    exp_argument = (Z-1)*H
    check(exp_upper(exp_argument,30) < F(133,4), "exp((7/2)H) < 133/4")
    check(F(133,4)**100 < A0**100*Z**441, "Chernoff base <= A0")

    tail_specs = [
        (4,F(583,1000),F(632591,500000)),
        (5,F(321,500),F(159089,125000)),
        (6,F(69,100),F(1278827,1000000)),
        (7,F(73,100),F(639137,500000)),
    ]
    tail_rows = []
    for j,x,Fj in tail_specs:
        check(fj_upper(j,x) <= Fj, f"generating series majorant {j}")
        check(Fj >= F(5,4), "logarithmic lower bound")
        q_cubed = A0**3*x**(-3*j)*Fj**11
        check(q_cubed < 1, f"all-scale exponential base {j}")
        Sx = sum((x**(-d) for d in range(1,j+1)), F(0))
        tail_rows.append({"j":j,"x":x,"F":Fj,"S":Sx,"q_cubed":q_cubed})
    check(F(4,5)**4 < F(3,4)**3, "low-N exponential base")
    L0=1024
    t=F(3,4)**146  # floor(1024/7)=146
    low=(F(9,8)*sum((r["j"]*r["S"] for r in tail_rows),F(0))*t/(1-t))
    high=(F(2187,4096)*F(4,3)/L0**2
          *sum((r["j"]**2*r["F"]*r["S"] for r in tail_rows),F(0)))
    check(low+high < F(3,1000), "total infinite tail")
    check(finite+low+high < F(19,100), "global pointwise coefficient")
    check(LAMBDA*F(19,100) == F(969,1000), "pointwise slack")
    check(F(969,1000) < 1, "pointwise feasibility")

    return {
        "status":"PASS: exact rational/integer numerical verification",
        "threshold":C,"g_coefficient":C+16,
        "constants":{"Q":Q,"H_star":H,"Gamma":GAMMA,"K":K,"lambda":LAMBDA,
                     "rho":RHO,"loss":LOSS,"T":T,"a0":A0},
        "dense_margin":dense-1,"window_coefficient":window,
        "window_minus_rho":window-RHO,
        "finite_groups":groups,"finite_total":finite,
        "tail_low":low,"tail_high":high,"tail_total":low+high,
        "pointwise_total_bound":LAMBDA*(finite+low+high),
        "finite_scales":scales,"tail_rows":tail_rows,
        "retention_multiset_audit":retention,
        "coverage":{
            "finite_constants":"EXHAUSTIVE rational coefficient calculation on all 29 listed scales",
            "tail":"Rational checks of analytic bounds for every remaining scale",
            "formalization":"Not a proof-assistant/kernel formalization"
        }
    }

def main() -> None:
    parser=argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("constants.json"))
    args=parser.parse_args()
    result=run()
    args.output.write_text(json.dumps(result,default=encode,indent=2),encoding="utf-8")
    print(result["status"])
    print("c =", C, "; g(n) <=", C+16, "* n")
    print("finite =", decimal_interval(result["finite_total"]))
    print("tail   =", decimal_interval(result["tail_total"]))
    print("lambda*(finite+tail) =", decimal_interval(result["pointwise_total_bound"]))
    print("window coefficient =", result["window_coefficient"])
    print("wrote",args.output)

if __name__=="__main__":
    main()