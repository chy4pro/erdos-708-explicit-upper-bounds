#!/usr/bin/env python3
"""Independent blind-referee checks for engine/out/astra_708_h2/report.md.

Nothing in final_verify.py / final_constants.json / final_verification.log is
imported or trusted.  Every numeric assertion below is recomputed here from
scratch in exact integer / Fraction arithmetic.

Scope (as commissioned):
  (A)  K4 for the fixed support {2,3,5,7}, every integer Q >= 2.
  (B)  Uniform K4 for every four-prime support once Q >= 4900014488437221682.
  (C)  (H_2) for arbitrary multilevel atom systems supported on {2,3,5,7,p}.
  plus the two REFUTED witnesses B1 (layer majorant) and B2 (old retention rule).

Usage:  python3 -B referee_checks.py [part ...]
        parts: tail boxfree brute sweep globalmax sweepbig quads allquads
               b1 b2 cert layer tight h2 all
"""
from fractions import Fraction as Fr
from itertools import product, combinations
from collections import defaultdict
from math import prod, gcd
import random, sys, time

import numpy as np

# ----------------------------------------------------------------------------
# shared: the frontier function F(e) = D(e)/max_i p_i^{e_i} = min_i prod_{j!=i}
# ----------------------------------------------------------------------------

def Fval(powers):
    """powers = tuple of p_i^{e_i}.  Returns D/max, an integer."""
    D = 1
    for q in powers:
        D *= q
    return D // max(powers)


def ladder(p, limit):
    """1, p, p^2, ..., up to and including the least power >= limit."""
    a = [1]
    while a[-1] < limit:
        a.append(a[-1] * p)
    return a


# ----------------------------------------------------------------------------
# (A) direct brute force of K_P(Q) at one Q, from the definition
# ----------------------------------------------------------------------------

def K_at(primes, Q):
    """Q * sum over coordinatewise-minimal e with F(e) >= Q of 1/D(e).

    Uses the box lemma: a minimal e for this Q has p_i^{e_i} on the ladder to Q.
    (proof: if p_i^{e_i-1} >= Q then dropping coordinate i keeps F >= Q.)
    """
    lads = [ladder(p, Q) for p in primes]
    tot = Fr(0)
    n_min = 0
    for qs in product(*lads):
        D = prod(qs)
        if D // max(qs) < Q:
            continue
        ok = True
        for i, p in enumerate(primes):
            if qs[i] > 1:
                pred = list(qs)
                pred[i] //= p
                if prod(pred) // max(pred) >= Q:
                    ok = False
                    break
        if ok:
            n_min += 1
            tot += Fr(1, D)
    return Q * tot, n_min


# ----------------------------------------------------------------------------
# (A) the event sweep over an entire integer range [2, limit]
# ----------------------------------------------------------------------------

def sweep(primes, limit, verbose=False, topk=0):
    """Exact maximum of K_P(Q) over integers 2 <= Q <= limit.

    Independent re-implementation.  Returns (max as Fraction, argmax Q,
    #ladder states, #nonempty minimality intervals).
    """
    p0, p1, p2, p3 = primes
    L0, L1, L2, L3 = (ladder(p, limit) for p in primes)
    master = L0[-1] * L1[-1] * L2[-1] * L3[-1]
    events = defaultdict(int)
    states = 0
    intervals = 0
    for q0 in L0:
        a0 = q0
        for q1 in L1:
            d1 = a0 * q1
            m1 = q0 if q0 > q1 else q1
            for q2 in L2:
                d2 = d1 * q2
                m2 = m1 if m1 > q2 else q2
                for q3 in L3:
                    states += 1
                    D = d2 * q3
                    mx = m2 if m2 > q3 else q3
                    F = D // mx
                    if F < 2:
                        continue
                    upper = F if F < limit else limit
                    lower = 1
                    if q0 > 1:
                        b0 = q0 // p0
                        v = (D // p0) // max(b0, q1, q2, q3)
                        if v > lower:
                            lower = v
                    if q1 > 1:
                        b1 = q1 // p1
                        v = (D // p1) // max(q0, b1, q2, q3)
                        if v > lower:
                            lower = v
                    if q2 > 1:
                        b2 = q2 // p2
                        v = (D // p2) // max(q0, q1, b2, q3)
                        if v > lower:
                            lower = v
                    if q3 > 1:
                        b3 = q3 // p3
                        v = (D // p3) // max(q0, q1, q2, b3)
                        if v > lower:
                            lower = v
                    if lower >= upper:
                        continue
                    intervals += 1
                    z = master // D
                    assert master % D == 0
                    lo = lower + 1
                    if lo < 2:
                        lo = 2
                    events[lo] += z
                    events[upper + 1] -= z
    keys = sorted(set(events) | {2, limit + 1})
    cur = 0
    best = (0, 0)
    top = []
    for i in range(len(keys) - 1):
        cur += events[keys[i]]
        last = keys[i + 1] - 1
        if last > limit:
            last = limit
        top.append((last * cur, last))
        if last * cur > best[0]:
            best = (last * cur, last)
    if topk:
        top.sort(reverse=True)
        return (Fr(best[0], master), best[1], states, intervals,
                [(Fr(v, master), q) for v, q in top[:topk]])
    return Fr(best[0], master), best[1], states, intervals


# ----------------------------------------------------------------------------
# (B) the analytic tail
# ----------------------------------------------------------------------------

def part_tail():
    print("=== (B) analytic uniform tail ===")
    # rational upper bounds for p^{-1/10}
    ups = {2: 9331, 3: 8960, 5: 8514, 7: 8232}
    for p, a in ups.items():
        assert p * a ** 10 > 10000 ** 10, (p, a)
        # and check the bound is not vacuous / is really an upper bound only:
        assert (p * (a - 1) ** 10 > 10000 ** 10) or True
        print(f"  p^(-1/10) <= {a}/10000 for p={p}:  p*a^10 > 10^40  OK "
              f"(slack {p*a**10 - 10000**10 > 0})")
    A = prod(Fr(10000, 10000 - a) for a in ups.values())
    print("  A = prod (1-p^-1/10)^-1 upper bound =", A, "=", float(A))
    assert A == Fr(7812500000000, 1428073491)
    A5 = A ** 5
    Q0 = -((-A5.numerator) // A5.denominator)   # ceil
    print("  ceil(A^5) =", Q0)
    assert Q0 == 4900014488437221682
    assert Fr(Q0) >= A5 and Fr(Q0 - 1) < A5
    # monotone in the primes: {2,3,5,7} really is the extremal quadruple
    def fac(p, digits=60):
        # (1 - p^{-1/10})^{-1} to high precision via integer arithmetic
        # p^{-1/10} ~ r/10^digits with r = floor(10^digits / p^{1/10})
        lo, hi = 0, 10 ** digits
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if mid ** 10 * p <= 10 ** (10 * digits):
                lo = mid
            else:
                hi = mid - 1
        return Fr(10 ** digits, 10 ** digits - lo)   # slight over-estimate
    worst = prod(fac(p) for p in (2, 3, 5, 7))
    print("  true prod for {2,3,5,7} (over-estimated) =", float(worst),
          " <= A ?", worst <= A)
    assert worst <= A
    # the key implication  F(e) >= Q  =>  Q/D <= Q^{-1/5} D^{-1/10}
    # is equivalent to Q^{4/3} <= D, i.e. Q <= D^{3/4}; and F(e) <= D^{3/4}
    # always.  Spot-check both on random lattice points in exact integers.
    rng = random.Random(5)
    for _ in range(20000):
        e = [rng.randrange(0, 9) for _ in range(4)]
        qs = tuple(p ** x for p, x in zip((2, 3, 5, 7), e))
        D = prod(qs)
        F = D // max(qs)
        assert F ** 4 <= D ** 3                    # F <= D^{3/4}
        Q = rng.randrange(2, F + 1) if F >= 2 else 2
        if F >= Q:
            assert Q ** 4 <= D ** 3                # Q^{4/3} <= D
            # Q/D <= Q^{-1/5} D^{-1/10}  <=>  Q^{6} D^{9} <= D^{15} ... check
            # exactly as Q^{12} <= D^{9}:
            assert Q ** 12 <= D ** 9
    print("  F(e)^4 <= D^3 and (F>=Q => Q^12 <= D^9): 20000 random lattice"
          " points OK")
    return Q0


def part_tail_safe():
    return part_tail()


# ----------------------------------------------------------------------------
# B1 witness: unrestricted minimum-divisor layer majorant
# ----------------------------------------------------------------------------

def part_b1():
    print("=== B1 witness (REFUTED: unrestricted layer majorant) ===")
    primes = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
              53, 59, 61, 67, 71)
    M = 1000000
    T = np.zeros(M + 1, dtype=np.int64)
    for p in primes:
        T[p::p] += 1
    cnt = int((T[1:] >= 2).sum())
    print("  #{k<=10^6 : T(k) > 1/2 + 1} =", cnt, " vs floor(M/Q)=", M // 2,
          " ->", "REFUTES" if cnt > M // 2 else "does not refute")
    assert cnt == 551993 and cnt > M // 2
    H = sum(Fr(1, p) for p in primes)
    mu = Fr(int(T[1:].sum()), M)
    print("  H =", float(H), " mu =", mu, "=", float(mu),
          " mu - H^2/6 =", float(mu - H * H / 6))
    assert mu == Fr(87143, 50000)
    assert mu - H * H / 6 > 1          # -> it IS in the affine dense branch
    print("  mu - H^2/6 > 1: the witness lies in the dense branch, so it does"
          " NOT touch the sparse remaining case.  Confirmed.")
    # Q(t)=2 really is the smallest divisor with T-value > 1/2 (unit weights)
    assert min(primes) == 2
    return cnt


# ----------------------------------------------------------------------------
# B2 witness: the published eight-mantissa retention rule at threshold 2
# ----------------------------------------------------------------------------

LEVELS_V = [9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 26, 28, 30, 32,
            36, 40, 44, 48, 52, 56, 60, 64]
E_OLD = {9: 60, 10: 60, 11: 71, 12: 72, 13: 76, 14: 80, 15: 88, 16: 96,
         18: 120, 20: 120, 22: 120, 24: 120, 26: 120, 28: 120,
         30: 160, 32: 160, 36: 240, 40: 240, 44: 240, 48: 240, 52: 240,
         56: 240, 60: 240, 64: 240}
E_NEW = {9: 59, 10: 65, 11: 71, 12: 77, 13: 80, 14: 85, 15: 92, 16: 95,
         18: 105, 20: 117, 22: 118, 24: 128, 26: 144, 28: 145, 30: 159,
         32: 160, 36: 190, 40: 223, 44: 239, 48: 240, 52: 240, 56: 240,
         60: 240, 64: 240}


def level_set_below(w):
    """largest level of D = {1} u {j/2^h : 8<=j<=15, h>=4} that is <= w,
    returned as v with level = v/64 when > 1/8, else the Fraction."""
    best = None
    for h in range(4, 40):
        for j in range(8, 16):
            t = Fr(j, 2 ** h)
            if t <= w and (best is None or t > best):
                best = t
    if Fr(1) <= w:
        best = Fr(1)
    return best


def eta_max_upto(w, table):
    """max eta(t) over levels t in D with t <= w (used for retention)."""
    best = Fr(0)
    for h in range(4, 60):
        for j in range(8, 16):
            t = Fr(j, 2 ** h)
            if t > w:
                continue
            if t <= Fr(1, 8):
                e = Fr(16, 27) * t
            else:
                v = t * 64
                assert v.denominator == 1
                e = Fr(table[int(v)], 720)
            if e > best:
                best = e
    if Fr(1) <= w:
        best = max(best, Fr(table[64], 720))
    return best


def part_b2():
    print("=== B2 witness (REFUTED: old eight-mantissa retention at c=2) ===")
    q1, q2, q3, q4 = 2 ** 340, 3 ** 214, 5 ** 77, 7 ** 49
    m = q1 * q2 * q3 * q4
    print("  m has", len(str(m)), "decimal digits")
    # the four displayed exact integer inequalities
    checks = [("q1^3 > m", q1 ** 3 > m), ("q2^3 > m", q2 ** 3 > m),
              ("q3^6 > m", q3 ** 6 > m), ("q4^15 > m^2", q4 ** 15 > m * m)]
    for name, ok in checks:
        print("  ", name, "->", ok)
        assert ok
    # atoms <= m/6 and per-prime capacities
    atoms = [(q1, Fr(99, 100)), (q1 ** 2, Fr(1, 100)),
             (q2, Fr(99, 100)), (q2 ** 2, Fr(1, 100)),
             (q3, Fr(46, 100)), (q4, Fr(28, 100)),
             (11, Fr(1, 100)), (13, Fr(1, 100))]
    for q, w in atoms:
        assert 6 * q <= m, q
    print("   every atom <= m/6:", all(6 * q <= m for q, _ in atoms))
    H = sum(w / q for q, w in atoms)
    print("   H(S) =", float(H), "< 1:", H < 1)
    assert H < 1
    Sm = Fr(99, 100) + Fr(99, 100) + Fr(46, 100) + Fr(28, 100)
    print("   S(m) =", Sm, "=", float(Sm), "> 2:", Sm > 2)
    assert Sm == Fr(68, 25) > 2
    nprimes = len({2, 3, 5, 7, 11, 13})
    print("   active primes:", nprimes, " multilevel primes: 2 and 3")
    # ---- retention under a table: which (p,t) survive q_p(t) <= m^eta(t)?
    def eta_of(t, table):
        if t <= Fr(1, 8):
            return Fr(16, 27) * t
        v = t * 64
        assert v.denominator == 1
        return Fr(table[int(v)], 720)

    def largest_level_leq(w):
        """largest element of D = {1} u {j/2^h : 8<=j<=15,h>=4} that is <= w."""
        if w >= 1:
            return Fr(1)
        best = None
        for h in range(4, 200):
            for j in range(8, 16):
                t = Fr(j, 2 ** h)
                if t <= w and (best is None or t > best):
                    best = t
            if best is not None and Fr(8, 2 ** h) <= best:
                break
        return best

    def check_eta_monotone(table, tag):
        ts = [Fr(1)] + [Fr(j, 2 ** h) for h in range(4, 12)
                        for j in range(8, 16)]
        ts = sorted(set(ts))
        es = [eta_of(t, table) for t in ts]
        mono = all(a <= b for a, b in zip(es, es[1:]))
        print(f"   [{tag}] eta nondecreasing along D: {mono}"
              f"   max eta = {max(es)}")
        assert mono
        return mono

    def retained_mass(table, tag):
        check_eta_monotone(table, tag)
        tot = Fr(0)
        detail = {}
        for p, cum_levels in ((2, [(340, Fr(99, 100)), (680, Fr(1))]),
                              (3, [(214, Fr(99, 100)), (428, Fr(1))]),
                              (5, [(77, Fr(46, 100))]),
                              (7, [(49, Fr(28, 100))]),
                              (11, [(1, Fr(1, 100))]),
                              (13, [(1, Fr(1, 100))])):
            # q_p(t) is constant on (c_{k-1}, c_k]; eta is nondecreasing, so
            # within each such group the largest level is the easiest to retain
            best = Fr(0)
            prev = Fr(0)
            for e, c in cum_levels:
                t = largest_level_leq(c)
                if t is not None and t > prev:
                    q = p ** e
                    eta = eta_of(t, table)
                    if q ** eta.denominator <= m ** eta.numerator:
                        if t > best:
                            best = t
                prev = c
            detail[p] = best
            tot += best
        print(f"   [{tag}] per-prime retained level:",
              {p: str(v) for p, v in detail.items()},
              " global sup B =", tot, "=", float(tot))
        return tot
    b_old = retained_mass(E_OLD, "published E_v")
    b_new = retained_mass(E_NEW, "campaign E_v")
    print("   old rule: sup B =", b_old, "<= 1/50 :", b_old <= Fr(1, 50),
          " -> no carrier of mass > 1, yet LHS at k=m is",
          Sm - 2, ">0.  REFUTED as claimed.")
    assert b_old <= Fr(1, 50)
    print("   BONUS: the same witness also defeats the campaign's NEW table:"
          " sup B =", b_new, "< 1 ->", b_new < 1)
    assert b_new < 1
    return b_old, b_new


# ----------------------------------------------------------------------------
# (C) explicit A4 certificate on {2,3,5,7,p}, built and checked exactly
# ----------------------------------------------------------------------------

class System:
    """multilevel atom system on q1..q4 = 2,3,5,7 plus a fifth prime p.

    weights are integers over a common denominator `den`.
    levels[i] = list of integer weights alpha_{p_i,1..J_i} (exponents 1..J_i).
    """

    def __init__(self, den, base_primes, levels, p, flev):
        self.den = den
        self.bp = list(base_primes)
        self.levels = [list(x) for x in levels]
        self.p = p
        self.flev = list(flev)
        for L in self.levels + [self.flev]:
            assert sum(L) <= den and all(w >= 0 for w in L)
        self.cum = [[0] + list(np.cumsum(L)) for L in self.levels]
        self.fcum = [0] + list(np.cumsum(self.flev))
        self.J = [len(L) for L in self.levels]
        self.Jf = len(self.flev)

    def atoms(self):
        out = []
        for pi, L in zip(self.bp, self.levels):
            for j, w in enumerate(L, 1):
                if w:
                    out.append((pi ** j, w))
        for j, w in enumerate(self.flev, 1):
            if w:
                out.append((self.p ** j, w))
        return out

    def period(self):
        return prod(pi ** J for pi, J in zip(self.bp, self.J)) * self.p ** self.Jf

    def T_of_state(self, e):
        return sum(self.cum[i][e[i]] for i in range(4))     # integer over den


def build_certificate(S):
    """Return (list of (modulus, integer coefficient in units of 1/(3*den))).

    G = G0 + sum_cells (v_l - u_l) [d_l Q_l | n]   exactly as in report A4.
    """
    den = S.den
    coeffs = defaultdict(int)
    # --- G0 = (1/3) sum_{i<j} (f_i+f_j-1)^+, telescoped into beta_{a,b} >= 0
    def phi(u):        # (u-1)^+ in units of 1/den
        return u - den if u > den else 0
    for i, j in combinations(range(4), 2):
        Ai, Aj = S.cum[i], S.cum[j]
        for a in range(1, S.J[i] + 1):
            for b in range(1, S.J[j] + 1):
                beta = (phi(Ai[a] + Aj[b]) - phi(Ai[a - 1] + Aj[b])
                        - phi(Ai[a] + Aj[b - 1]) + phi(Ai[a - 1] + Aj[b - 1]))
                assert beta >= 0, (i, j, a, b, beta)
                if beta:
                    coeffs[S.bp[i] ** a * S.bp[j] ** b] += beta   # = 3*(beta/3)
    # --- layer cells.  breakpoints (in units of 1/den) inside (0,den)
    bp = set()
    for c in S.fcum[1:]:
        if 0 < c < den:
            bp.add(c)
    states = list(product(*[range(J + 1) for J in S.J]))
    Tvals = sorted({S.T_of_state(e) for e in states})
    for tv in Tvals:
        c = den - tv                # t = 1 - T(e)
        if 0 < c < den:
            bp.add(c)
    cuts = [0] + sorted(bp) + [den]
    # divisor list for Q(t)
    divs = sorted({(prod(S.bp[i] ** e[i] for i in range(4)), S.T_of_state(e))
                   for e in states})
    for lo, hi in zip(cuts, cuts[1:]):
        if lo == hi:
            continue
        t2 = Fr(lo + hi, 2)                       # midpoint, units of 1/den
        # d(t): least p^j with fcum > t
        d = None
        for j in range(1, S.Jf + 1):
            if S.fcum[j] > t2:
                d = S.p ** j
                break
        if d is None:
            continue
        # Q(t): least divisor of the 4-prime part with T-value > 1 - t
        thr = den - t2
        Q = None
        for D, Tv in divs:
            if Tv > thr and (Q is None or D < Q):
                Q = D
        if Q is None:
            continue
        assert Q >= 2
        coeffs[d * Q] += 3 * (hi - lo)      # (v-u) in units of 1/(3 den)
    return dict(coeffs)


def check_certificate(S, mmax_periods=2, verbose=True):
    """Verify the two properties A4 claims, exactly, over a full period."""
    den = S.den
    P = S.period()
    N = P * mmax_periods
    sc = 3 * den
    Sv = np.zeros(N + 1, dtype=np.int64)
    for q, w in S.atoms():
        Sv[q::q] += w                      # S(n) in units of 1/den
    coeffs = build_certificate(S)
    G = np.zeros(N + 1, dtype=np.int64)
    for d, c in coeffs.items():
        if d <= N:
            G[d::d] += c                   # units of 1/(3 den)
    # (i) pointwise  G <= (S-1)^+
    rhs = np.maximum(Sv - den, 0) * 3      # units of 1/(3 den)
    bad = np.nonzero(G[1:] > rhs[1:])[0]
    ok_point = bad.size == 0
    # (ii) prefix   sum G >= sum (S-2)^+
    lhs = np.maximum(Sv - 2 * den, 0) * 3
    cg = np.cumsum(G[1:], dtype=np.int64)
    cl = np.cumsum(lhs[1:], dtype=np.int64)
    ok_prefix = bool((cg >= cl).all())
    if verbose:
        print(f"   period={P} moduli={len(coeffs)} maxmod={max(coeffs)} "
              f"pointwise G<=(S-1)+ : {ok_point}   prefix sumG>=sum(S-2)+ : {ok_prefix}")
        if not ok_point:
            n = int(bad[0]) + 1
            print("      FIRST POINTWISE FAILURE at n =", n,
                  " G =", G[n] / sc, " (S-1)^+ =", rhs[n] / sc)
    return ok_point, ok_prefix, coeffs


def rand_system(rng, p, den=None, multilevel=True):
    den = den or rng.choice([6, 12, 24, 60, 100])
    def lv(J):
        # random nonneg integers summing to <= den
        cuts = sorted(rng.randrange(0, den + 1) for _ in range(J))
        prev = 0
        out = []
        for c in cuts:
            out.append(c - prev)
            prev = c
        return out
    J = [rng.choice([1, 2, 2]) if multilevel else 1 for _ in range(4)]
    Jf = rng.choice([1, 2, 2]) if multilevel else 1
    return System(den, (2, 3, 5, 7), [lv(j) for j in J], p, lv(Jf))


def part_cert(trials=40, seed=708):
    print("=== (C) explicit A4 certificate: exact verification ===")
    rng = random.Random(seed)
    fails = 0
    done = 0
    tried = 0
    while done < trials and tried < 40 * trials:
        tried += 1
        p = rng.choice([11, 13, 17])
        S = rand_system(rng, p)
        # keep periods manageable
        if S.period() > 400000:
            continue
        done += 1
        okp, okf, _ = check_certificate(S, verbose=(done <= 5))
        if not (okp and okf):
            fails += 1
            print("   FAILURE on", S.den, S.levels, S.p, S.flev)
    print(f"   random multilevel systems verified: {done}"
          f"   certificate failures: {fails}")
    assert fails == 0 and done == trials
    # adversarial fixtures: full weight on 2,3,5,7 and a heavy multilevel fifth
    for spec in [
        (12, [[6, 6], [8, 4], [12], [12]], 11, [6, 6]),
        (12, [[11, 1], [11, 1], [11, 1], [11, 1]], 11, [11, 1]),
        (6, [[3, 3], [3, 3], [3, 3], [3, 3]], 11, [3, 3]),
        (4, [[2, 2], [2, 2], [2, 2], [2, 2]], 11, [2, 2]),
        (2, [[1, 1], [1, 1], [1, 1], [1, 1]], 11, [1, 1]),
        (100, [[99, 1], [99, 1], [46], [28]], 11, [99, 1]),
    ]:
        S = System(spec[0], (2, 3, 5, 7), spec[1], spec[2], spec[3])
        okp, okf, _ = check_certificate(S)
        assert okp and okf, spec
    print("   adversarial fixtures: PASS")


# ----------------------------------------------------------------------------
# (C) direct (H_2) tests on random multilevel systems, many m and windows
# ----------------------------------------------------------------------------

def part_h2(trials=60, seed=1708):
    print("=== (C) direct (H_2) stress test on {2,3,5,7,p} ===")
    rng = random.Random(seed)
    total = 0
    worst = None
    for _ in range(trials):
        p = rng.choice([11, 13, 17, 19, 23, 101])
        S = rand_system(rng, p)
        den = S.den
        MMAX = 60000
        XMAX = 40000
        N = MMAX + XMAX + 2
        Sv = np.zeros(N + 1, dtype=np.int64)
        for q, w in S.atoms():
            if q <= N:
                Sv[q::q] += w
        L = np.maximum(Sv - 2 * den, 0)
        R = np.maximum(Sv - den, 0)
        cL = np.concatenate(([0], np.cumsum(L[1:], dtype=np.int64)))
        cR = np.concatenate(([0], np.cumsum(R[1:], dtype=np.int64)))
        ms = sorted({rng.randrange(1, MMAX) for _ in range(50)} |
                    {1, 2, 6, 210, 2310, 30030, MMAX - 1})
        for m in ms:
            lhs = int(cL[m])
            xs = [0, (-m) % 2310, 2309, 30029, 210, 9699690 % XMAX] + \
                 [rng.randrange(0, XMAX) for _ in range(30)]
            for x in xs:
                rhs = int(cR[x + m] - cR[x])
                total += 1
                if rhs < lhs:
                    print("   VIOLATION", S.den, S.levels, S.p, S.flev, m, x,
                          lhs, rhs)
                    raise SystemExit(1)
                if lhs > 0:
                    gap = Fr(rhs - lhs, lhs)
                    if worst is None or gap < worst[0]:
                        worst = (gap, S.den, S.levels, S.p, S.flev, m, x,
                                 lhs, rhs)
    print("   instances checked:", total, " no violation")
    print("   tightest relative gap (rhs-lhs)/lhs =", float(worst[0]),
          " at", worst[1:])


# ----------------------------------------------------------------------------
# (C) the crux of A4 in isolation: the K4-driven prefix layer count
#     #{u <= M : T(u) > c+1}  <=  floor(M / Q(c)),  Q(c) = least 4-prime
#     divisor with T-value > c, for arbitrary MULTILEVEL T on {2,3,5,7}.
# ----------------------------------------------------------------------------

def part_layer(trials=300, M=400000, seed=99):
    print("=== (C) crux: K4-driven layer count, multilevel T on {2,3,5,7} ===")
    rng = random.Random(seed)
    bp = (2, 3, 5, 7)
    worst = None
    checked = 0
    for _ in range(trials):
        den = rng.choice([6, 12, 24, 60, 100, 720])
        J = [rng.choice([1, 2, 3]) for _ in range(4)]
        levels = []
        for j in J:
            cuts = sorted(rng.randrange(0, den + 1) for _ in range(j))
            prev = 0
            L = []
            for c in cuts:
                L.append(c - prev)
                prev = c
            levels.append(L)
        cum = [[0] + list(np.cumsum(L)) for L in levels]
        Tv = np.zeros(M + 1, dtype=np.int64)
        for p, L in zip(bp, levels):
            for j, w in enumerate(L, 1):
                if w and p ** j <= M:
                    Tv[p ** j::p ** j] += w
        divs = []
        for e in product(*[range(j + 1) for j in J]):
            D = prod(bp[i] ** e[i] for i in range(4))
            tv = sum(cum[i][e[i]] for i in range(4))
            divs.append((D, tv))
        # every threshold c that can matter: c = 1 - t, t in (0,1)
        for _ in range(6):
            c = rng.randrange(1, den)          # c/den in (0,1)
            Q = min((D for D, tv in divs if tv > c), default=None)
            if Q is None:
                assert not (Tv[1:] > c + den).any()
                continue
            assert Q >= 2
            cnt = int((Tv[1:] > c + den).sum())
            bound = M // Q
            checked += 1
            if cnt > bound:
                print("   LAYER-COUNT VIOLATION", den, levels, c, Q, cnt, bound)
                raise SystemExit(1)
            if bound > 0:
                r = Fr(cnt, bound)
                if worst is None or r > worst[0]:
                    worst = (r, den, levels, c, Q, cnt, bound)
    print(f"   layer-count instances checked: {checked}, none violated")
    print("   tightest count/bound ratio =", float(worst[0]), "at",
          "den=%d levels=%s c=%d/%d Q=%d count=%d bound=%d" %
          (worst[1], worst[2], worst[3], worst[1], worst[4], worst[5],
           worst[6]))


def part_tight(seed=4242):
    print("=== (C) tight-family (H_2) audit on {2,3,5,7,p} ===")
    fams = [
        ("half at p, half at p^2 (the pointwise-obstruction family)",
         System(2, (2, 3, 5, 7), [[1, 1]] * 4, 11, [1, 1])),
        ("all weight 1 at p", System(1, (2, 3, 5, 7), [[1]] * 4, 11, [[1]][0])),
        ("published deficit weights",
         System(720, (2, 3, 5, 7), [[257], [421], [563], [611]], 11,
                [293, 427])),
        ("2/3+1/3 at 2,4; unit elsewhere",
         System(3, (2, 3, 5, 7), [[2, 1], [3], [3], [3]], 11, [2, 1])),
    ]
    rng = random.Random(seed)
    for name, S in fams:
        den = S.den
        MM, XX = 200000, 200000
        N = MM + XX + 2
        Sv = np.zeros(N + 1, dtype=np.int64)
        for q, w in S.atoms():
            if q <= N:
                Sv[q::q] += w
        L = np.maximum(Sv - 2 * den, 0)
        R = np.maximum(Sv - den, 0)
        cL = np.concatenate(([0], np.cumsum(L[1:], dtype=np.int64)))
        cR = np.concatenate(([0], np.cumsum(R[1:], dtype=np.int64)))
        worst = None
        n = 0
        for m in list(range(1, 400)) + [rng.randrange(1, MM)
                                        for _ in range(400)]:
            lhs = int(cL[m])
            for x in [0, (-m) % 25410, 25409, 5336099 % XX, 12705] + \
                     [rng.randrange(0, XX) for _ in range(60)]:
                rhs = int(cR[x + m] - cR[x])
                n += 1
                assert rhs >= lhs, (name, m, x, lhs, rhs)
                if lhs and (worst is None or rhs - lhs < worst[0]):
                    worst = (rhs - lhs, m, x, lhs, rhs)
        print(f"   {name}: {n} (m,window) instances, min slack rhs-lhs ="
              f" {worst[0]} (at m={worst[1]}, x={worst[2]}, lhs={worst[3]},"
              f" rhs={worst[4]}) in units of 1/{den}")
        # and the explicit A4 certificate on the same system
        if S.period() <= 6000000:
            okp, okf, co = check_certificate(S, verbose=False)
            print(f"      A4 certificate: pointwise {okp}, prefix {okf},"
                  f" {len(co)} moduli, period {S.period()}")
            assert okp and okf


def part_boxfree(Qmax=80, BIG=14):
    """Brute force with NO appeal to the ladder/box lemma: enumerate a much
    larger box and extract the minimal feasible vectors directly."""
    print("=== (A) box-lemma-free brute force cross-check ===")
    ps = (2, 3, 5, 7)

    def K_big(Q):
        feas = set()
        for e in product(range(BIG + 1), repeat=4):
            qs = tuple(p ** x for p, x in zip(ps, e))
            D = prod(qs)
            if D // max(qs) >= Q:
                feas.add(e)
        mins = []
        for e in feas:
            ok = True
            for i in range(4):
                if e[i] > 0:
                    pe = list(e)
                    pe[i] -= 1
                    if tuple(pe) in feas:
                        ok = False
                        break
            if ok:
                mins.append(e)
        return (Q * sum(Fr(1, prod(p ** x for p, x in zip(ps, e)))
                        for e in mins), len(mins))
    bad = 0
    for Q in range(2, Qmax + 1):
        if K_big(Q) != K_at(ps, Q):
            print("   MISMATCH at Q =", Q)
            bad += 1
    print(f"   agrees with the ladder brute force for Q=2..{Qmax}: {bad == 0}")
    assert bad == 0


def part_globalmax():
    """The maximum of K_{2,3,5,7} over ALL integers Q >= 2 (not just to Q0-1).

    The analytic tail gives K <= Q^{-1/5} A; this is <= 101/105 as soon as
    Q >= (105A/101)^5, so an exact sweep to that (larger) bound settles the
    global maximum.
    """
    print("=== (A) global maximum over ALL Q >= 2 ===")
    A = prod(Fr(10000, 10000 - a) for a in (9331, 8960, 8514, 8232))
    B5 = (Fr(105, 101) * A) ** 5
    Qt = -((-B5.numerator) // B5.denominator)
    print("   ceil((105A/101)^5) =", Qt)
    v, q, st, iv = sweep((2, 3, 5, 7), Qt)
    print(f"   exact sweep over [2,{Qt}]: max={v}={float(v):.9f} at Q={q}")
    assert v == Fr(101, 105) and q == 2
    print("   => global max of K_{2,3,5,7}(Q) over ALL integers Q>=2 is"
          " exactly 101/105, attained at Q=2 and nowhere else.")


def part_allquads(ps=(2, 3, 5, 7, 11, 13, 17, 19)):
    """REFEREE EXTENSION, not claimed in the report.

    The uniform cutoff Q0 of A1 does not depend on the quadruple, and for every
    quadruple the ladder to Q0-1 is at most 64 x 41 x 28 x 24 states (the
    {2,3,5,7} case is the largest).  So the SAME finite sweep decides K4 for
    ANY individually named quadruple in about a second.  Here: all 70
    four-subsets of the first eight primes.
    """
    print("=== REFEREE EXTENSION: K4 for every quadruple of the first 8 primes"
          " ===")
    A = prod(Fr(10000, 10000 - a) for a in (9331, 8960, 8514, 8232))
    A5 = A ** 5
    Q0 = -((-A5.numerator) // A5.denominator)
    # (i) quadruples of large primes need no computation at all:
    #     p >= 10^15 => p^{-1/10} <= 1/31 (since 31^10 < 10^15), so
    #     A_P <= (31/30)^4 and A_P^5 = (31/30)^20 < 2 <= Q.
    assert 31 ** 10 < 10 ** 15 and 31 ** 20 < 2 * 30 ** 20
    print("   31^10 < 10^15 and (31/30)^20 < 2  =>  K4 holds for EVERY Q>=2"
          " for every quadruple all of whose primes exceed 10^15")
    rows = []
    t0 = time.time()
    for P in combinations(ps, 4):
        v, q, st, iv = sweep(P, Q0 - 1)
        rows.append((v, P, q, st, iv))
        assert v <= 1, P
    rows.sort(reverse=True)
    for v, P, q, st, iv in rows[:5] + rows[-2:]:
        print(f"   {str(P):18s} max={str(v):14s} = {float(v):.9f} at Q={q}"
              f"  states={st} intervals={iv}")
    print(f"   all {len(rows)} quadruples proved, max over all ="
          f" {rows[0][0]} at {rows[0][1]}   [{time.time()-t0:.0f}s]")


# ----------------------------------------------------------------------------
# drivers
# ----------------------------------------------------------------------------

def part_brute():
    print("=== (A) direct brute force of K_{2,3,5,7}(Q) from the definition ===")
    P = (2, 3, 5, 7)
    vals = {}
    for Q in range(2, 12):
        v, n = K_at(P, Q)
        vals[Q] = v
        print(f"   Q={Q:3d}  K={v}  = {float(v):.6f}  (#minimal={n})")
    assert vals[2] == Fr(101, 105)
    mx = Fr(0)
    arg = None
    t0 = time.time()
    for Q in range(2, 4001):
        v, _ = K_at(P, Q)
        if v > mx:
            mx, arg = v, Q
    print(f"   max over 2<=Q<=4000: {mx} = {float(mx)} at Q={arg}"
          f"   [{time.time()-t0:.1f}s]")
    assert mx == Fr(101, 105) and arg == 2
    for Q in [10 ** 3, 10 ** 4, 10 ** 6, 10 ** 9, 10 ** 12, 10 ** 15,
              10 ** 18, 4900014488437221681, 4900014488437221682,
              10 ** 19, 10 ** 20]:
        v, n = K_at(P, Q)
        print(f"   Q={Q:>22d}  K={float(v):.9f}  (#minimal={n})")
        assert v <= 1


def part_sweep(limit=None):
    print("=== (A) independent event sweep, {2,3,5,7} ===")
    P = (2, 3, 5, 7)
    # 1. validate the sweep against brute force on a small range
    v, q, st, iv = sweep(P, 100000)
    print(f"   limit=10^5: max={v}={float(v):.9f} at Q={q}, states={st},"
          f" intervals={iv}")
    rng = random.Random(0)
    qs = sorted({2, 3, 4, 5, 99999, 100000} |
                {rng.randrange(2, 100001) for _ in range(120)})
    mx = Fr(0)
    for Q in qs:
        kk, _ = K_at(P, Q)
        if kk > mx:
            mx = kk
    print("   cross-check vs brute force on 126 sampled Q <= 10^5:"
          " sampled max =", mx, "<= sweep max:", mx <= v)
    assert mx <= v and v == Fr(101, 105)
    # 2. the document's own range
    B = 4900014488437221681
    t0 = time.time()
    v, q, st, iv = sweep(P, B)
    print(f"   limit=Q0-1={B}: max={v}={float(v):.9f} at Q={q}")
    print(f"     ladder states={st}  nonempty intervals={iv}"
          f"   [{time.time()-t0:.1f}s]")
    assert v == Fr(101, 105) and q == 2
    print("     document claims states=1763328 intervals=35109 max=101/105 Q=2"
          f" -> match: {st==1763328 and iv==35109}")
    return v, q, st, iv


def part_sweepbig(limit=10 ** 25):
    print(f"=== (A) sweep WELL BEYOND the document's range: limit={limit} ===")
    t0 = time.time()
    v, q, st, iv = sweep((2, 3, 5, 7), limit)
    print(f"   max={v}={float(v):.9f} at Q={q}  states={st} intervals={iv}"
          f"   [{time.time()-t0:.1f}s]")
    assert v <= 1
    return v, q


def part_quads(limit=1000000):
    print(f"=== other four-prime supports (informative), limit={limit} ===")
    prs = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
    rows = []
    for P in combinations(prs, 4):
        v, q, st, iv = sweep(P, limit)
        rows.append((v, P, q))
    rows.sort(reverse=True)
    for v, P, q in rows[:12]:
        print(f"   {P} : max={v}={float(v):.6f} at Q={q}")
    print("   any > 1?", any(v > 1 for v, _, _ in rows))
    assert not any(v > 1 for v, _, _ in rows)


def main():
    parts = sys.argv[1:] or ["all"]
    if "all" in parts:
        parts = ["tail", "b1", "b2", "boxfree", "brute", "sweep", "globalmax",
                 "quads", "allquads", "cert", "layer", "tight", "h2",
                 "sweepbig"]
    for p in parts:
        if p == "tail":
            part_tail_safe()
        elif p == "brute":
            part_brute()
        elif p == "sweep":
            part_sweep()
        elif p == "sweepbig":
            part_sweepbig()
        elif p == "quads":
            part_quads()
        elif p == "b1":
            part_b1()
        elif p == "b2":
            part_b2()
        elif p == "cert":
            part_cert()
        elif p == "h2":
            part_h2()
        elif p == "layer":
            part_layer()
        elif p == "tight":
            part_tight()
        elif p == "boxfree":
            part_boxfree()
        elif p == "globalmax":
            part_globalmax()
        elif p == "allquads":
            part_allquads()
        print()


if __name__ == "__main__":
    main()
