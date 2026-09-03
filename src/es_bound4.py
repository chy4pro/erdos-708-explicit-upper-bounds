#!/usr/bin/env python3
"""Q23's Theorem D (Qwen3.8-Max, 2026-09-04): for an integer k >= 2, if a_n^(k-1) >= (k n)^(k+1) then g <= k n.
Core: k-split lemma — atoms Q (product A), integer H <= m with A^2 H^(k+1) <= m^(k+1)  ==>  Q splits into <= k pieces,
each a singleton atom or a bin f with f H <= m.  Then: pieces <= kn = H; large singletons (qH > m) placed per prime;
bins (fH <= m, so >= H multiples in I) get private multiples avoiding <= H-1 forbidden positions.
This script implements the construction and verifies it on random instances above the threshold, for k = 2..6."""
import math, random, time, sys
from es_bound import factor, divides

def ksplit(atoms, H, m, k):
    """atoms: list of prime powers (pairwise coprime), product A with A^2 H^(k+1) <= m^(k+1). Returns list of pieces
    (each a list of atoms) of length <= k, every piece either a singleton or a bin with product*H <= m."""
    A = math.prod(atoms)
    assert A * A * H ** (k + 1) <= m ** (k + 1), "k-split hypothesis violated"
    if k == 1:
        assert A * H <= m
        return [list(atoms)] if atoms else []
    if not atoms: return []
    big = [q for q in atoms if q * q * H > m]
    if big:
        q = big[0]; rest = list(atoms); rest.remove(q)
        return [[q]] + ksplit(rest, H, m, k - 1)
    f = 1; used = []; rest = list(atoms)
    while rest and f * f * H < m:
        q = rest.pop(0); f *= q; used.append(q)
        assert f * H <= m
    if not rest: return [used]
    assert f * f * H >= m
    return [used] + ksplit(rest, H, m, k - 1)

def construct_k(A, x, k):
    n = len(A); m = max(A); H = k * n; I = list(range(x + 1, x + m + 1))
    assert m ** (k - 1) >= H ** (k + 1)
    assert H <= m
    large = []; bins = []
    for a in A:
        atoms = [p ** e for p, e in factor(a).items()]
        pieces = ksplit(atoms, H, m, k)
        assert len(pieces) <= k
        for piece in pieces:
            f = math.prod(piece)
            if len(piece) == 1 and f * H > m: large.append((f, list(factor(f))[0]))
            else:
                assert f * H <= m
                bins.append(f)
    assert len(large) + len(bins) <= H
    U = set(); byp = {}
    for q, p in large: byp.setdefault(p, []).append(q)
    for p, qs in byp.items():
        used = set()
        for q in sorted(qs, reverse=True):
            b = next(u for u in I if u % q == 0 and u not in used)
            used.add(b); U.add(b)
    B = set(U)
    for f in bins:
        b = next(u for u in I if u % f == 0 and u not in B)
        B.add(b)
    return sorted(B)

if __name__ == "__main__":
    random.seed(21); t0 = time.time(); runs = {k: 0 for k in range(2, 7)}; fails = 0
    while time.time() - t0 < 200:
        k = random.choice([2, 3, 4, 5, 6]); n = random.choice([2, 3, 4, 5, 6, 8])
        H = k * n; m0 = math.ceil(H ** ((k + 1) / (k - 1)))
        while m0 ** (k - 1) < H ** (k + 1): m0 += 1
        m = random.randrange(m0, 3 * m0 + 2)
        if random.random() < 0.4:
            sm = random.choice([6, 12, 30, 60, 210, 420, 2310, 30030])
            if m < 2 * sm: continue
            A = sorted(set(sm * random.randrange(1, m // sm + 1) for _ in range(n - 1)) | {m})
            if len(A) != n or max(A) != m: continue
        else:
            A = sorted(random.sample(range(2, m), n - 1)) + [m]
        x = random.choice([random.randrange(0, 10 ** 8), (math.lcm(*A) - m // 2) if math.lcm(*A) > m else 0])
        B = construct_k(A, x, k); runs[k] += 1
        if not (all(x < b <= x + m for b in B) and divides(A, B) and len(B) <= k * n):
            fails += 1; print("FAIL", k, A, x, B)
    print("Theorem D construction: runs per k =", runs, "; failures =", fails)
    # thresholds table
    for k in range(2, 8):
        print(f"k={k}: a_n >= (kn)^{{(k+1)/(k-1)}} = ({k}n)^{(k+1)/(k-1):.3f}  ->  g <= {k}n")
