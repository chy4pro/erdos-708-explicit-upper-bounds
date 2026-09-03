#!/usr/bin/env python3
"""Exact minimum |B| for Erdős #708 instances by dynamic programming over capped valuation vectors.
G(A, x) = min |B|, B subset of {x+1, ..., x+max(A)}, with prod(A) | prod(B).
Also reproduces the Erdős–Surányi lower-bound construction: A = {p_i p_j}, all p_i within a factor sqrt(2),
x chosen so that the unique multiple of every p_i p_j in the interval is the same integer u (in the middle), u divisible by
each p_i exactly once.  Predicted: G >= 1 + l(l-2) = (l-1)^2 for l primes (n = C(l,2)); e.g. l=3 -> 4 = g(3), l=4 -> 9.
Usage: python3 gn_dp.py [l]"""
import sys, itertools, math

def vp(x, p):
    c = 0
    while x % p == 0:
        x //= p; c += 1
    return c

def min_B(A, x):
    m = max(A)
    primes = sorted({p for a in A for p in range(2, a + 1) if a % p == 0 and all(p % q for q in range(2, int(p ** .5) + 1))})
    need = tuple(sum(vp(a, p) for a in A) for p in primes)
    cand = []
    for y in range(x + 1, x + m + 1):
        v = tuple(min(vp(y, p), need[i]) for i, p in enumerate(primes))
        if any(v): cand.append(v)
    # DP: best[state] = min count; state = capped valuation vector
    best = {tuple(0 for _ in primes): 0}
    for v in cand:
        new = dict(best)
        for s, c in best.items():
            t = tuple(min(s[i] + v[i], need[i]) for i in range(len(primes)))
            if new.get(t, 10 ** 9) > c + 1: new[t] = c + 1
        best = new
    return best.get(need)

def es_construction(primes):
    P = math.prod(primes)
    A = [p * q for p, q in itertools.combinations(primes, 2)]
    m = max(A); n = len(A)
    # u in the middle: u = x + t0 with t0 = m//2 ; need u == 0 mod P, u not 0 mod p^2, and no p^3 in interval etc.
    t0 = m // 2
    worst = 0; wx = None
    for k in range(1, 40):
        u = k * P
        if any(u % (p * p) == 0 for p in primes): continue
        x = u - t0
        if x < 0: continue
        g = min_B(A, x)
        if g > worst: worst, wx = g, x
    return n, m, worst, wx

if __name__ == "__main__":
    l = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    sets = {3: [17, 19, 23], 4: [41, 43, 47, 53], 5: [101, 103, 107, 109, 113]}
    primes = sets[l]
    assert 2 * primes[0] ** 2 > primes[-1] ** 2
    n, m, worst, wx = es_construction(primes)
    print(f"l={l} primes={primes} n={n} m={m}: ES-construction min|B| = {worst} (predicted (l-1)^2 = {(l-1)**2}) at x={wx}")
    # sanity: a few random positions for the same A
    import random
    random.seed(1)
    A = [p * q for p, q in itertools.combinations(primes, 2)]
    vals = [min_B(A, random.randrange(1, 10 ** 6)) for _ in range(5)]
    print("random x -> min|B| =", vals)
