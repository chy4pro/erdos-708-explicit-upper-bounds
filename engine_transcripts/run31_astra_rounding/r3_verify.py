"""Exact one-prime audits for the R3 formulation counterexamples."""
from fractions import Fraction
import json
from pathlib import Path


def v2(k):
    return (k & -k).bit_length() - 1


def audit(n, K):
    A = [2**j for j in range(1, n + 1)]
    R = n * (n + 1) // 2
    x = 2**K - 2**n
    vals = [v2(b) for b in range(x + 1, x + 2**n + 1)]
    ordered = sorted(vals, reverse=True)
    # Exact fractional knapsack optimum, with unit costs and upper bounds.
    remaining = R
    tau = Fraction(0)
    for v in ordered:
        if not remaining:
            break
        take = min(Fraction(1), Fraction(remaining, v))
        tau += take
        remaining -= v * take
    g, covered = 0, 0
    while covered < R:
        covered += ordered[g]
        g += 1
    witness = [2**K] + [2**K - 2**j for j in range(1, n)]
    for j in range(1, n + 1):
        assert sum(v2(b) >= j for b in witness) >= n - j + 1
    assert max(vals) == K and tau == Fraction(R, K) and g == 1
    assert len(set(witness)) == n
    assert all(x < b <= x + 2**n for b in witness)
    return dict(A=A, x=x, K=K, R=R, tau_raw=str(tau), g=g,
                tau_cap="1", tau_level=str(n), g_level=n,
                level_witness=witness, original_witness=[2**K],
                gap_raw=str(Fraction(g) - tau),
                gap_raw_over_n=str((Fraction(g) - tau) / n))


if __name__ == "__main__":
    rows = [audit(2, 3)] + [audit(n, 10 * n * (n + 1) // 2) for n in range(1, 13)]
    dest = Path(__file__).with_name("r3_exact.jsonl")
    dest.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in rows))
    print(json.dumps({"instances": len(rows), "all_exact_assertions_passed": True,
                      "max_raw_gap_over_n": str(max(Fraction(r["gap_raw_over_n"]) for r in rows)),
                      "output": str(dest)}))
