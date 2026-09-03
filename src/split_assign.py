#!/usr/bin/env python3
"""Conjecture S test for Erdős #708: choose for each a a coprime split a = d1*d2 (d2 = 1 allowed) and assign every demand
d to an element b of I = (x, x+a_n] such that for each b and prime p: sum of v_p(d) over demands at b <= v_p(b).
If feasible, B = set of used elements has |B| <= 2n and prod(A) | prod(B).  Exact backtracking (small instances only).
Usage: python3 split_assign.py            (fixed tests + random instances, internal time cap)"""
import sys, math, random, time, itertools
from functools import lru_cache
sys.setrecursionlimit(10000)

def factor(n):
    f = {}; d = 2
    while d * d <= n:
        while n % d == 0: f[d] = f.get(d, 0) + 1; n //= d
        d += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f

def coprime_splits(a):
    f = factor(a); ps = list(f)
    out = set()
    for r in range(0, len(ps) + 1):
        for sub in itertools.combinations(ps, r):
            d1 = math.prod(p ** f[p] for p in sub); d2 = a // d1
            out.add((max(d1, d2), min(d1, d2)))
    return sorted(out, reverse=True)

def feasible(A, x, deadline):
    m = max(A); I = list(range(x + 1, x + m + 1))
    primes = sorted({p for a in A for p in factor(a)})
    cap = {b: {p: 0 for p in primes} for b in I}
    for b in I:
        fb = factor(b)
        for p in primes: cap[b][p] = fb.get(p, 0)
    # candidates per demand d: elements b with d | b
    def cands(d): return [b for b in I if b % d == 0]
    # order a's by fewest candidate multiples (hardest first)
    order = sorted(A, key=lambda a: len(cands(a)))
    def rec(i):
        if time.time() > deadline: raise TimeoutError
        if i == len(order): return True
        a = order[i]
        for d1, d2 in coprime_splits(a):
            for b1 in cands(d1):
                f1 = factor(d1)
                if any(cap[b1][p] < e for p, e in f1.items()): continue
                for p, e in f1.items(): cap[b1][p] -= e
                if d2 == 1:
                    if rec(i + 1): return True
                else:
                    f2 = factor(d2)
                    for b2 in cands(d2):
                        if any(cap[b2][p] < e for p, e in f2.items()): continue
                        for p, e in f2.items(): cap[b2][p] -= e
                        if rec(i + 1): return True
                        for p, e in f2.items(): cap[b2][p] += e
                for p, e in f1.items(): cap[b1][p] += e
        return False
    return rec(0)

if __name__ == "__main__":
    tests = [([323, 391, 437], 74072, "ES l=3"), ([10, 12, 15, 20], 50, "P17 g(4)>=5"), ([5, 10, 12, 15, 20], 50, "P17 g(5)>=6"),
             ([1763, 1927, 2021, 2173, 2279, 2491], 26348553, "ES l=4")]
    for A, x, name in tests:
        t0 = time.time()
        try: r = feasible(A, x, time.time() + 120)
        except TimeoutError: r = "TIMEOUT"
        print(f"{name}: A={A} x={x} -> S feasible: {r}  ({time.time()-t0:.1f}s)", flush=True)
    random.seed(7); t_end = time.time() + 400; bad = 0; tried = 0
    while time.time() < t_end:
        n = random.choice([3, 4, 5]); A = sorted(random.sample(range(2, 61), n)); L = math.lcm(*A)
        x = random.choice([t * L - max(A) // 2 for t in (1, 2, 3)] + [random.randrange(0, 3000)])
        if x < 0: continue
        try: r = feasible(A, x, time.time() + 20)
        except TimeoutError: continue
        tried += 1
        if not r: bad += 1; print("S INFEASIBLE:", A, x, flush=True)
    print(f"random: tried {tried}, infeasible {bad}")
