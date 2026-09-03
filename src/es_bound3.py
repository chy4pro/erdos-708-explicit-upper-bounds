#!/usr/bin/env python3
"""Q21's theorem (Qwen3.8-Max, 2026-09-03): if a_n >= 8 n^3 then the split-assignment statement S holds and 2n elements
suffice. Construction: C = M/(2n); each a has at most one prime-power factor > C (that one is a 'large' demand, cofactor
< 2n <= C); otherwise all prime-power factors <= C and a <= M <= C^{3/2}, so they split into two coprime parts <= C
(two-bin packing lemma). Large demands: per-prime injection (nested Hall / greedy by exponent). Small demands (<= C):
each has >= 2n multiples in I, at most 2n-1 forbidden -> private fresh multiple. Verify on random instances."""
import math, random, time, sys
from es_bound import factor, divides

def two_bin_split(qs, C):
    """qs: prime powers <= C with product P <= C^{3/2}. Return (s, P//s) with both <= C."""
    P = math.prod(qs)
    if P <= C: return P, 1
    big = [q for q in qs if q * q > C]     # q > sqrt(C)
    if big: s = big[0]
    else:
        s = 1
        for q in qs:
            s *= q
            if s * C >= P: break          # s >= P/C
    assert s <= C and P // s <= C and P % s == 0, (qs, C, s)
    return s, P // s

def construct21(A, x):
    n = len(A); M = max(A); I = list(range(x + 1, x + M + 1))
    assert M >= 8 * n ** 3
    C = M / (2 * n)
    demands = []   # (value, prime or None, source)
    for a in A:
        f = factor(a); qs = [p ** e for p, e in f.items()]
        large = [(p, e) for p, e in f.items() if p ** e > C]
        assert len(large) <= 1
        if large:
            p, e = large[0]; q = p ** e
            demands.append((q, p, a))
            if a // q > 1: demands.append((a // q, None, a))
        else:
            s, t = two_bin_split(qs, C)
            if s > 1: demands.append((s, None, a))
            if t > 1: demands.append((t, None, a))
    assert len(demands) <= 2 * n
    U = set()
    byp = {}
    for q, p, a in demands:
        if p is not None: byp.setdefault(p, []).append(q)
    for p, qs in byp.items():
        used = set()
        for q in sorted(qs, reverse=True):
            b = next(u for u in I if u % q == 0 and u not in used)
            used.add(b); U.add(b)
    B = set(U)
    for d, p, a in demands:
        if p is None:
            cands = [u for u in I if u % d == 0 and u not in B]
            assert cands, "no fresh multiple"
            B.add(cands[0])
    return sorted(B)

if __name__ == "__main__":
    random.seed(9); t0 = time.time(); runs = 0; fails = 0
    while time.time() - t0 < 150:
        n = random.choice([2, 3, 4, 5, 6, 7]); M0 = 8 * n ** 3
        M = random.randrange(M0, 4 * M0)
        A = sorted(random.sample(range(2, M), n - 1)) + [M]
        # bias towards smooth / structured a's sometimes
        if random.random() < 0.4:
            sm = random.choice([6, 10, 12, 30, 60, 210, 420, 2310])
            if M < 2 * sm: continue
            A = sorted(set(sm * random.randrange(1, M // sm + 1) for _ in range(n - 1)) | {M})
            if len(A) != n or max(A) != M: continue
        x = random.choice([random.randrange(0, 10 ** 7), (math.lcm(*A) - M // 2) if math.lcm(*A) > M else 0])
        M = max(A)
        B = construct21(A, x); runs += 1
        ok = all(x < b <= x + M for b in B) and divides(A, B) and len(B) <= 2 * n
        if not ok: fails += 1; print("FAIL", A, x, B)
    print(f"Theorem C construction: {runs} random runs (a_n >= 8n^3), {fails} failures; |B| <= 2n always")
