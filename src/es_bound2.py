#!/usr/bin/env python3
"""P18's algorithm: g(n) <= F(n) = n(ceil(log2(2n)) + ceil(log2(ceil(log2(2n)))) + 2), n >= 2.  Implements the construction
(large atoms per prime greedy; small atoms next-fit binned; small bins globally distinct outside U) and verifies on random
instances that the output B lies in I, prod(A) | prod(B), and |B| <= D <= F(n). Also checks (B1),(B2) numerically."""
import math, random, time, sys
from es_bound import factor, divides

def Lam(t):
    r = 0
    while 2 ** r < t: r += 1
    return r

def F(n):
    r = Lam(2 * n); s = Lam(r); return n * (r + s + 2)

def params(n):
    r = Lam(2 * n); s = Lam(r); C = r + s + 2; H = n * C; k = (C - 1) // 2
    return H, k, C

def construct18(A, x):
    n = len(A); m = max(A); I = list(range(x + 1, x + m + 1))
    H, k, C = params(n)
    if m <= H: return I, len(I), H   # whole interval (prod A | m! | prod I)
    demands = []   # (value, prime or None)
    for a in A:
        f = factor(a)
        cur = 1
        for p in sorted(f):
            q = p ** f[p]
            if H * q > m: demands.append((q, p))            # large atom
            else:
                if H * cur * q <= m: cur *= q
                else:
                    demands.append((cur, None)); cur = q
        if cur > 1: demands.append((cur, None))
    D = len(demands)
    assert D <= H, f"budget lemma violated: D={D} > H={H}"
    # large demands per prime
    U = set(); usedp = {}
    large = [(q, p) for q, p in demands if p is not None]
    byp = {}
    for q, p in large: byp.setdefault(p, []).append(q)
    for p, qs in byp.items():
        used = set()
        for q in sorted(qs, reverse=True):
            b = next(u for u in I if u % q == 0 and u not in used)
            used.add(b); U.add(b)
    B = set(U)
    for d, p in demands:
        if p is None:
            b = next(u for u in I if u % d == 0 and u not in B)
            B.add(b)
    return sorted(B), D, H

if __name__ == "__main__":
    # (B1),(B2)
    bad = 0
    for n in list(range(2, 2000)) + [10**4, 10**5, 10**6, 10**9, 10**12]:
        H, k, C = params(n)
        b1 = H >= n * (2 * k + 1)
        b2 = (k + 1) * n * math.log2(H) <= k * H
        if not (b1 and b2): bad += 1; print("param fail", n, H, k)
    print("budget conditions checked for n=2..1999 and larger: failures =", bad)
    print("F(n):", {n: F(n) for n in [2, 3, 4, 5, 10, 20, 100, 1000, 10**6]})
    random.seed(5); t0 = time.time(); runs = 0; fails = 0; over = 0
    while time.time() - t0 < 150:
        n = random.choice([2, 3, 4, 5, 6, 8, 10]); A = sorted(random.sample(range(2, 3000), n))
        x = random.choice([random.randrange(0, 10**7), (math.lcm(*A) - max(A) // 2) if math.lcm(*A) > max(A) else 0])
        B, D, H = construct18(A, x); runs += 1
        ok = all(x < b <= x + max(A) for b in B) and divides(A, B) and len(B) <= D <= H and H == F(n)
        if not ok: fails += 1; print("FAIL", A, x, B, D, H)
    print(f"algorithm P18: {runs} random runs, {fails} failures")
    A = [323, 391, 437]; x = 74072; B, D, H = construct18(A, x)
    print("ES l=3:", B, "D =", D, "H =", H, "valid:", divides(A, B))
