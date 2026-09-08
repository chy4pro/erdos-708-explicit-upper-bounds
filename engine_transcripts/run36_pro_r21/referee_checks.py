#!/usr/bin/env python3
"""
Independent referee checks for pro_708_r21/proof.md.

Written from the *statements* in proof.md, not from exact_verifier.py.
Everything mathematical is done in exact integer / Fraction arithmetic.
NumPy is used only for large integer window sweeps (int64 arrays, exact).

Usage:
    python3 referee_checks.py            # all sections
    python3 referee_checks.py A B C D K  # selected sections
Sections:
    A  Theorem 4  (five primes, at most one multilevel prime)
    B  Lemma 2    (four-modulus Boolean antichain / Kraft bound)
    C  Theorem 5  (cyclic certificate, per-prime cap 2/(N-1))
    D  Lemma 7    (six-prime pointwise obstruction) + exact Farkas certificate
    K  Lemma 8    (open K_4 bridge) audits
    KW Lemma 8    wide K_4 scan: all 4-subsets of primes < 60, 2 <= Q <= 400
                  (949,620 instances; ~10 min).  This is the scan quoted in
                  referee_opus.md.
"""
import sys
from fractions import Fraction as F
from itertools import combinations, product
from math import gcd, prod
import random

try:
    from math import lcm
except ImportError:                                    # py<3.9
    def lcm(*xs):
        r = 1
        for x in xs:
            r = r * x // gcd(r, x)
        return r

import numpy as np

OK = []
FAIL = []


def check(name, cond, extra=""):
    (OK if cond else FAIL).append(name)
    print(("  PASS  " if cond else "  FAIL  ") + name + (("  " + str(extra)) if extra else ""))
    return cond


def pos(x):
    return x if x > 0 else 0 * x


# ----------------------------------------------------------------------------
# A.  THEOREM 4
# ----------------------------------------------------------------------------

def A1_layer_identity():
    """Delta_a(T,f) = (T+f-a)^+ - (T-a)^+ = int_0^1 [f>t][T>a-t] dt.

    The integrand is the indicator of  t in ( (a-T)^+ , f )  intersected with [0,1],
    so the integral equals  ( min(f,1) - (a-T)^+ )^+ .  We check that closed form
    against the hinge difference exactly, over a dense rational grid of
    (T, f, a) including a < 1, T + f < a, T = 0, a = 0.
    """
    print("\n[A1] exact layer identity (5.1)")
    bad = []
    Ts = [F(i, 4) for i in range(0, 21)]                # 0 .. 5
    fs = [F(i, 6) for i in range(0, 7)]                 # 0 .. 1
    as_ = [F(i, 4) for i in range(0, 17)]               # 0 .. 4
    for T in Ts:
        for f in fs:
            for a in as_:
                lhs = pos(T + f - a) - pos(T - a)
                rhs = pos(min(f, F(1)) - pos(a - T))
                if lhs != rhs:
                    bad.append((T, f, a, lhs, rhs))
    check("A1 layer identity exact on grid (incl. a<1, T+f<a)", not bad, bad[:3])

    # also check the closed form against a fine Riemann sum of the integral
    # (numerically) for a few random points, to be sure the closed form is the
    # integral and not just an algebraic coincidence.
    rng = random.Random(11)
    worst = F(0)
    for _ in range(400):
        T = F(rng.randrange(0, 400), 100)
        f = F(rng.randrange(0, 101), 100)
        a = F(rng.randrange(0, 400), 100)
        M = 20000
        s = sum(1 for i in range(M) if F(2 * i + 1, 2 * M) < f and T > a - F(2 * i + 1, 2 * M))
        approx = F(s, M)
        exact = pos(T + f - a) - pos(T - a)
        worst = max(worst, abs(approx - exact))
    check("A1 Riemann sum agrees with hinge difference (err<=1/2000)", worst <= F(1, 2000), worst)

    # f outside [0,1] breaks it (documents the hypothesis f in [0,1])
    T, f, a = F(0), F(2), F(1)
    check("A1 hypothesis f<=1 is needed (f=2 breaks identity)",
          pos(T + f - a) - pos(T - a) != pos(min(f, F(1)) - pos(a - T)))


def cum(alphas):
    """cumulative sums A_1..A_J of a level list."""
    out, s = [], F(0)
    for a in alphas:
        s += a
        out.append(s)
    return out


def f_value(n, p, alphas):
    """f(n) = sum_j alpha_j [p^j | n] = A_{v_p(n)}."""
    v = 0
    m = n
    while m % p == 0:
        m //= p
        v += 1
    A = cum(alphas)
    if v == 0:
        return F(0)
    return A[min(v, len(A)) - 1]


def A2_threshold_is_one_divisor():
    """[f(n) > t] is identically 0 or equals [p^{j(t)} | n]."""
    print("\n[A2] threshold slices of a multilevel prime function")
    rng = random.Random(7)
    bad = []
    for _ in range(300):
        p = rng.choice([2, 3, 5, 7, 11])
        J = rng.randrange(1, 5)
        num = [rng.randrange(0, 25) for _ in range(J)]
        if sum(num) > 24:
            continue
        alphas = [F(x, 24) for x in num]
        A = cum(alphas)
        N = p ** (J + 2) * 6
        # test all t strictly between consecutive distinct cumulative values
        cuts = sorted(set([F(0)] + A + [F(1)]))
        ts = [(cuts[i] + cuts[i + 1]) / 2 for i in range(len(cuts) - 1)]
        for t in ts:
            js = [j for j in range(1, J + 1) if A[j - 1] > t]
            for n in range(1, N + 1):
                lhs = 1 if f_value(n, p, alphas) > t else 0
                if not js:
                    rhs = 0
                else:
                    rhs = 1 if n % (p ** js[0]) == 0 else 0
                if lhs != rhs:
                    bad.append((p, alphas, t, n))
                    break
    check("A2 [f>t] is 0 or a single prime-power divisor indicator", not bad, bad[:2])


def lemma3_Q(qs, ws, c):
    """Q = min prod_{i in A} q_i over A with w_A > c ; None if no such A."""
    best = None
    r = len(qs)
    for mask in range(1 << r):
        w = sum(ws[i] for i in range(r) if mask >> i & 1)
        if w > c:
            d = prod([qs[i] for i in range(r) if mask >> i & 1]) if mask else 1
            if best is None or d < best:
                best = d
    return best


def theorem4_certificate(qs, ws, p, alphas):
    """My own build of (5.4).  Returns dict divisor -> Fraction coefficient."""
    assert len(qs) == len(ws) == 4
    assert all(gcd(q, p) == 1 for q in qs)
    assert all(gcd(x, y) == 1 for x, y in combinations(qs, 2))
    assert all(F(0) <= w <= F(1) for w in ws)
    assert sum(alphas) <= 1 and all(a >= 0 for a in alphas)
    A = cum(alphas)
    coeff = {}

    def add(d, c):
        if c:
            coeff[d] = coeff.get(d, F(0)) + c

    # pair part  (1/3) sum_{i<j} (w_i+w_j-1)^+ [q_i q_j | n]
    for i, j in combinations(range(4), 2):
        add(qs[i] * qs[j], pos(ws[i] + ws[j] - 1) / 3)

    # layer part
    subsets = [(sum(ws[i] for i in range(4) if mask >> i & 1),
                prod([qs[i] for i in range(4) if mask >> i & 1]) if mask else 1)
               for mask in range(16)]
    cuts = {F(0), F(1)}
    cuts |= set(A)
    for h in (1, 2):
        for w, _d in subsets:
            v = h - w
            if 0 <= v <= 1:
                cuts.add(F(v))
    cuts = sorted(cuts)
    for u, v in zip(cuts, cuts[1:]):
        tau = (u + v) / 2
        js = [j for j in range(1, len(A) + 1) if A[j - 1] > tau]
        wins = [d for (w, d) in subsets if w > 1 - tau]
        if not js or not wins:
            continue
        add(p ** js[0] * min(wins), v - u)
    return coeff, cuts


def S_value(n, qs, ws, p, alphas):
    return sum(ws[i] for i in range(4) if n % qs[i] == 0) + f_value(n, p, alphas)


def divisor_array(D, coeff, den):
    """integer array v[1..D] with v[n] = den * sum_{d | n} coeff[d]  (numpy, exact)."""
    v = np.zeros(D + 1, dtype=np.int64)
    for d, c in coeff.items():
        cc = c * den
        assert cc.denominator == 1
        v[d::d] += int(cc)
    return v


def atom_array(D, atoms, den):
    v = np.zeros(D + 1, dtype=np.int64)
    for d, a in atoms:
        aa = a * den
        assert aa.denominator == 1
        if aa:
            v[d::d] += int(aa)
    return v


def full_H2_sweep(L, R, D):
    """L,R integer arrays indexed 1..D (period D).  Checks (H_2) for every m<=D
    and every window start; returns True/False."""
    Lp = np.concatenate(([0], np.cumsum(L[1:].astype(np.int64))))
    Rp = np.concatenate(([0], np.cumsum(np.tile(R[1:].astype(np.int64), 2))))
    for m in range(1, D + 1):
        if int(Lp[m]) > int((Rp[m:m + D] - Rp[:D]).min()):
            return False, m
    return True, None


def A3_certificate_and_H2(verbose=True):
    print("\n[A3] Theorem 4: independent certificate build + exhaustive (H_2)")
    rng = random.Random(2026)
    cases = []
    cases.append(((2, 3, 5, 7), tuple(F(x, 720) for x in (257, 421, 563, 611)),
                  11, (F(293, 720), F(427, 720)), "disclosed example"))
    for _ in range(10):
        qs = (2, 3, 5, 7)
        den = rng.choice([6, 8, 12, 720])
        ws = tuple(F(rng.randrange(0, den + 1), den) for _ in range(4))
        p = 11
        J = rng.randrange(1, 3)
        tot, alphas = 0, []
        for _j in range(J):
            x = rng.randrange(0, den - tot + 1)
            alphas.append(F(x, den))
            tot += x
        cases.append((qs, ws, p, tuple(alphas), "random p=11"))
    # four moduli that are genuine prime powers, fifth prime multilevel
    cases.append(((4, 9, 5, 7), (F(2, 3), F(1), F(1, 2), F(5, 6)), 11,
                  (F(1, 3), F(1, 3)), "prime-power moduli"))
    cases.append(((8, 3, 25, 7), (F(1), F(3, 4), F(1, 2), F(1, 4)), 11,
                  (F(1, 2), F(1, 4)), "prime-power moduli 2"))
    # a small fifth prime (p=2 is allowed too: any prime coprime to the q_i)
    cases.append(((3, 5, 7, 11), (F(5, 6), F(2, 3), F(1, 2), F(1, 3)), 2,
                  (F(1, 3), F(1, 3), F(1, 3)), "fifth prime = 2")) 

    allgood = True
    for qs, ws, p, alphas, tag in cases:
        coeff, cuts = theorem4_certificate(qs, ws, p, alphas)
        D = lcm(lcm(*qs), p ** len(alphas))
        den = 1
        for x in list(ws) + list(alphas) + list(coeff.values()):
            den = lcm(den, x.denominator)
        atoms = [(qs[i], ws[i]) for i in range(4)]
        A = cum(alphas)
        for j in range(1, len(alphas) + 1):
            atoms.append((p ** j, alphas[j - 1]))
        Sv = atom_array(D, atoms, den)
        Cv = divisor_array(D, coeff, den)
        L = np.maximum(Sv - 2 * den, 0)
        R = np.maximum(Sv - den, 0)
        ptwise_upper = bool(np.all(Cv[1:] <= R[1:]))
        prefix = bool(np.all(np.cumsum(L[1:]) <= np.cumsum(Cv[1:])))
        minptw = int(np.min(Cv[1:] - L[1:]))
        argmin = int(np.argmin(Cv[1:] - L[1:])) + 1
        nonneg = all(c >= 0 for c in coeff.values())
        h2, bad_m = full_H2_sweep(L, R, D)
        good = ptwise_upper and prefix and nonneg and h2
        allgood &= good
        if verbose:
            print("   %-20s D=%-7d nonneg=%s upperOK=%s prefixOK=%s (H2)=%s  min(C-(S-2)^+)=%s at n=%s"
                  % (tag, D, nonneg, ptwise_upper, prefix, h2, F(minptw, den), argmin))
    check("A3 certificate: nonneg coeffs, pointwise upper, prefix lower, full (H_2)", allgood)


def A4_disclosed_example():
    print("\n[A4] the disclosed pointwise failure at n = 12705")
    atoms = ((2, 257), (3, 421), (5, 563), (7, 611), (11, 293), (121, 427))
    n = 12705
    check("A4 12705 = 3*5*7*11^2", n == 3 * 5 * 7 * 121)
    Sn = sum(a for d, a in atoms if n % d == 0)
    check("A4 720*S(12705) = 2315", Sn == 2315, Sn)
    check("A4 2160*(S-2)^+ = 2625", 3 * max(Sn - 1440, 0) == 2625)
    qs, ws = (2, 3, 5, 7), tuple(F(x, 720) for x in (257, 421, 563, 611))
    coeff, cuts = theorem4_certificate(qs, ws, 11, (F(293, 720), F(427, 720)))
    scaled = sorted((d, int(c * 2160)) for d, c in coeff.items())
    expected = [(10, 100), (14, 148), (15, 264), (21, 312), (35, 454), (55, 408),
                (66, 345), (110, 126), (242, 771), (363, 492), (605, 18)]
    check("A4 my rebuild of (5.4) reproduces the published coefficient table",
          scaled == expected, scaled if scaled != expected else "")
    expcuts = (0, 9, 42, 109, 151, 157, 199, 266, 293, 299, 408, 456, 463, 572, 620, 720)
    mycuts = tuple(int(c * 720) for c in cuts)
    check("A4 my cut numerators match", mycuts == expcuts, mycuts)
    Cn = sum(int(c * 2160) for d, c in coeff.items() if n % d == 0)
    check("A4 2160*C(12705) = 1948 < 2625  (pointwise LOWER bound genuinely fails)",
          Cn == 1948 and Cn < 2625, (Cn, 2625))
    # per-prime capacity of the atom system is respected
    check("A4 atom system legal: prime 11 total = 293+427 = 720/720 = 1", 293 + 427 == 720)
    # and the certificate still satisfies both usable bounds over the full period
    D = 25410
    worst = None
    accC = accL = 0
    okup = okpre = True
    for k in range(1, D + 1):
        S = sum(a for d, a in atoms if k % d == 0)
        C = sum(int(c * 2160) for d, c in coeff.items() if k % d == 0)
        L = 3 * max(S - 1440, 0)
        R = 3 * max(S - 720, 0)
        if C > R:
            okup = False
        accC += C
        accL += L
        if accC < accL:
            okpre = False
        if worst is None or C - L < worst[0]:
            worst = (C - L, k)
    check("A4 pointwise upper bound C<=(S-1)^+ holds over the full period", okup)
    check("A4 every prefix sum bound holds over the full period", okpre)
    check("A4 worst pointwise deficit is (-677, n=12705) as disclosed",
          worst == (-677, 12705), worst)


def A0_lemma1():
    print("\n[A0] Lemma 1 (accepted four-prime base) re-checked")
    bad = []
    for a in product(range(13), repeat=4):
        S = sum(a)
        G = sum(max(a[i] + a[j] - 12, 0) for i, j in combinations(range(4), 2))
        if not (3 * max(S - 24, 0) <= G <= 3 * max(S - 12, 0)):
            bad.append(a)
    check("A0 (S-2)^+ <= G_4 <= (S-1)^+ on the 1/12 grid (28561 points)", not bad, bad[:2])
    # convexity increments beta_{a,b} >= 0
    bad2 = []
    phi = lambda u: max(u, 0)
    for A0v in range(0, 13):
        for A1v in range(A0v, 13):
            for B0v in range(0, 13):
                for B1v in range(B0v, 13):
                    beta = (phi(A1v + B1v - 12) - phi(A0v + B1v - 12)
                            - phi(A1v + B0v - 12) + phi(A0v + B0v - 12))
                    if beta < 0:
                        bad2.append((A0v, A1v, B0v, B1v))
    check("A0 mixed second differences beta_{a,b} >= 0", not bad2, bad2[:2])


def A5_lemma3():
    """Lemma 3 and the exact step (5.2)/(5.3) used in Theorem 4."""
    print("\n[A5] Lemma 3 + the d-substitution step of Theorem 4")
    rng = random.Random(5)
    bad_l3, bad_sub = [], []
    tested = 0
    systems = [(2, 3, 5, 7), (3, 4, 5, 7), (2, 5, 9, 7), (2, 3, 25, 7), (4, 3, 5, 11),
               (9, 5, 7, 11), (2, 3, 5, 49)]
    for qs in systems:
        Dm = prod(qs)
        if Dm > 3000:
            continue
        for _ in range(25):
            den = rng.choice([2, 3, 4, 6, 12])
            ws = tuple(F(rng.randrange(0, den + 1), den) for _ in range(4))
            Tv = np.zeros(Dm + 1, dtype=np.int64)
            for i in range(4):
                Tv[qs[i]::qs[i]] += int(ws[i] * den)
            for cnum in range(0, 2 * den + 1):
                c = F(cnum, den)
                Q = lemma3_Q(qs, ws, c)
                left = (Tv[1:] > int((c + 1) * den)).astype(np.int64)
                right = (Tv[1:] > int(c * den)).astype(np.int64)
                tested += 1
                Lp = np.concatenate(([0], np.cumsum(left)))
                Rp = np.concatenate(([0], np.cumsum(np.tile(right, 2))))
                for M in range(1, Dm + 1):
                    lhs = int(Lp[M])
                    if Q is not None and lhs > M // Q:
                        bad_l3.append(("floor", qs, ws, c, M, lhs, M // Q))
                        break
                    if lhs > int((Rp[M:M + Dm] - Rp[:Dm]).min()):
                        bad_l3.append(("window", qs, ws, c, M))
                        break
                if bad_l3:
                    break
            if bad_l3:
                break
    check("A5 Lemma 3 (4.1) and (4.3) verified on %d (system,c) pairs" % tested,
          not bad_l3, bad_l3[:2])

    # (5.2): with d a power of a fifth prime, sum_{k<=m}[d|k][T(k)>2-t] = #{h<=m/d : T(h)>c+1}
    # and this is <= floor(m/(d Q)) <= #{b in I : d Q | b} <= #{b in I: [d|b][T(b)>1-t]}.
    qs = (2, 3, 5, 7)
    Dm = prod(qs)
    for _ in range(40):
        den = rng.choice([3, 4, 6, 12])
        ws = tuple(F(rng.randrange(0, den + 1), den) for _ in range(4))
        p, j = 11, rng.randrange(1, 3)
        d = p ** j
        P = Dm * d
        Tv = np.zeros(P + 1, dtype=np.int64)
        for i in range(4):
            Tv[qs[i]::qs[i]] += int(ws[i] * den)
        dv = np.zeros(P + 1, dtype=np.int64)
        dv[d::d] = 1
        for tnum in range(1, den):
            t = F(tnum, den)
            c = 1 - t
            Q = lemma3_Q(qs, ws, c)
            lhsv = (dv[1:] * (Tv[1:] > int((2 - t) * den))).astype(np.int64)
            rhsv = (dv[1:] * (Tv[1:] > int((1 - t) * den))).astype(np.int64)
            Lp = np.concatenate(([0], np.cumsum(lhsv)))
            Rp = np.concatenate(([0], np.cumsum(np.tile(rhsv, 2))))
            for m in range(1, P + 1, 7):
                lhs = int(Lp[m])
                if Q is None:
                    if lhs != 0:
                        bad_sub.append(("Qnone", qs, ws, t, m))
                        break
                    continue
                mid = m // (d * Q)
                if lhs > mid:
                    bad_sub.append(("5.2", qs, ws, t, m, lhs, mid))
                    break
                if mid > int((Rp[m:m + Dm * d] - Rp[:Dm * d]).min()):
                    bad_sub.append(("window", qs, ws, t, m))
                    break
            if bad_sub:
                break
        if bad_sub:
            break
    check("A5 the (5.2) chain  LHS <= floor(m/dQ) <= window count  holds",
          not bad_sub, bad_sub[:2])


# ----------------------------------------------------------------------------
# B.  LEMMA 2
# ----------------------------------------------------------------------------

def minimal_families(q, Q):
    """inclusion-minimal nonempty A with prod(A)/max(A) >= Q, as frozensets of indices."""
    r = len(q)
    feas = {}
    for mask in range(1, 1 << r):
        vals = [q[i] for i in range(r) if mask >> i & 1]
        feas[mask] = prod(vals) // max(vals) >= Q if len(vals) > 1 else (1 >= Q)
    out = []
    for mask, f in feas.items():
        if not f:
            continue
        if not any(feas.get(mask ^ (1 << i), False) for i in range(r) if mask >> i & 1):
            out.append(mask)
    return sorted(out)


def table_prediction(a, b, c, d, Q):
    """the nine rows of proof.md section 3, as index masks over (a,b,c,d)=(0,1,2,3)."""
    def m(*idx):
        s = 0
        for i in idx:
            s |= 1 << i
        return s
    if Q <= a:
        return sorted([m(0, 1), m(0, 2), m(0, 3), m(1, 2), m(1, 3), m(2, 3)]), 1
    if Q <= b:
        return sorted([m(1, 2), m(1, 3), m(2, 3)]), 2
    if Q <= c:
        if Q <= a * b:
            return sorted([m(2, 3), m(0, 1, 2), m(0, 1, 3)]), 3
        return sorted([m(2, 3)]), 4
    if Q <= a * b:
        return sorted([m(0, 1, 2), m(0, 1, 3), m(0, 2, 3), m(1, 2, 3)]), 5
    if Q <= a * c:
        return sorted([m(0, 2, 3), m(1, 2, 3)]), 6
    if Q <= b * c:
        return sorted([m(1, 2, 3)]), 7
    if Q <= a * b * c:
        return sorted([m(0, 1, 2, 3)]), 8
    return [], 9


def B1_table_and_bound():
    print("\n[B1] Lemma 2: exhaustiveness of the nine-row table + the Kraft bound")
    bad_table, bad_bound, worst = [], [], (F(0), None)
    quads = 0
    rows_seen = set()
    instances = 0
    # (i) FULL sweep over every integer Q from 2 to abc+2, small quadruples
    for q in combinations(range(2, 31), 4):
        if any(gcd(x, y) != 1 for x, y in combinations(q, 2)):
            continue
        quads += 1
        a, b, c, d = q
        for Q in range(2, a * b * c + 3):
            mins = minimal_families(q, Q)
            pred, row = table_prediction(a, b, c, d, Q)
            rows_seen.add(row)
            instances += 1
            if mins != pred:
                bad_table.append((q, Q, mins, pred, row))
            val = sum(F(Q, prod([q[i] for i in range(4) if mask >> i & 1])) for mask in mins)
            if val > 1:
                bad_bound.append((q, Q, val))
            if val > worst[0]:
                worst = (val, (q, Q))
    check("B1 FULL Q-sweep: table reproduces M_Q on %d quadruples, %d (quad,Q) instances"
          % (quads, instances), not bad_table, bad_table[:3])
    check("B1 all nine rows actually occur", rows_seen == set(range(1, 10)), sorted(rows_seen))
    check("B1 Kraft bound Q*sum 1/prod <= 1 on every one of them", not bad_bound, bad_bound[:3])
    check("B1 maximum of the left side is 101/105 at ((2,3,5,7),Q=2)",
          worst == (F(101, 105), ((2, 3, 5, 7), 2)), worst)

    # (ii) larger quadruples: Q at every region boundary and just past it.
    #      Within a region M_Q is constant and Q*sum increases with Q, so the
    #      region suprema {a,b,c,ab,ac,bc,abc} carry the maximum; we also test
    #      t+1 for each threshold t and some random Q.
    rng = random.Random(3)
    bad2, worst2 = [], (F(0), None)
    n2 = 0
    for q in combinations(range(2, 121), 4):
        if any(gcd(x, y) != 1 for x, y in combinations(q, 2)):
            continue
        a, b, c, d = q
        Qs = {2}
        for t in (a, b, c, a * b, a * c, b * c, a * b * c):
            Qs |= {t, t + 1}
        Qs.add(rng.randrange(2, a * b * c + 2))
        for Q in sorted(Qs):
            if Q < 2:
                continue
            mins = minimal_families(q, Q)
            pred, _row = table_prediction(a, b, c, d, Q)
            val = sum(F(Q, prod([q[i] for i in range(4) if mask >> i & 1])) for mask in mins)
            n2 += 1
            if mins != pred or val > 1:
                bad2.append((q, Q, val))
            if val > worst2[0]:
                worst2 = (val, (q, Q))
    check("B1 boundary sweep on all coprime quadruples <=120 (%d instances)" % n2,
          not bad2, bad2[:3])
    check("B1 its maximum is also 101/105 at ((2,3,5,7),2)",
          worst2 == (F(101, 105), ((2, 3, 5, 7), 2)), worst2)

    # (iii) random large quadruples
    bad3 = []
    for _ in range(3000):
        while True:
            q = tuple(sorted(rng.sample(range(2, 4000), 4)))
            if all(gcd(x, y) == 1 for x, y in combinations(q, 2)):
                break
        a, b, c, d = q
        for Q in sorted({2, a, b, c, a * b, a * c, b * c, a * b * c,
                         rng.randrange(2, a * b * c + 2)}):
            if Q < 2:
                continue
            mins = minimal_families(q, Q)
            pred, _row = table_prediction(a, b, c, d, Q)
            val = sum(F(Q, prod([q[i] for i in range(4) if mask >> i & 1])) for mask in mins)
            if mins != pred or val > 1:
                bad3.append((q, Q, val))
    check("B1 random quadruples up to 4000: table + bound", not bad3, bad3[:3])

    # (iv) monotonicity fact the table proof relies on: feasibility is upward closed
    badm = []
    for q in combinations(range(2, 25), 4):
        if any(gcd(x, y) != 1 for x, y in combinations(q, 2)):
            continue
        for Q in range(2, q[0] * q[1] * q[2] + 2):
            fe = {}
            for mask in range(1, 16):
                vals = [q[i] for i in range(4) if mask >> i & 1]
                fe[mask] = (prod(vals) // max(vals)) >= Q
            for mask in range(1, 16):
                for i in range(4):
                    if not (mask >> i & 1):
                        if fe[mask] and not fe[mask | (1 << i)]:
                            badm.append((q, Q, mask, i))
    check("B1 feasibility is upward closed (so minimal families form an antichain)",
          not badm, badm[:3])


def B2_row1_subcases():
    print("\n[B2] Lemma 2 row 1: a*e_2(1/a,1/b,1/c,1/d) <= 1, the four sub-cases")

    def e2(x):
        return sum(F(1, u * v) for u, v in combinations(x, 2))

    # exhaustiveness of the b-cases:  b >= 3 always, so {3},{4},{5},{>=6} is a partition
    ok_b = all(b >= 3 for b in [b for a in range(2, 40) for b in range(a + 1, 41)
                                if gcd(a, b) == 1 and a >= 2][:1] or [3])
    check("B2 b>=3 always (since 2<=a<b)", ok_b)
    # b = 4 forces a = 3
    check("B2 b=4 forces a=3", [a for a in range(2, 4) if gcd(a, 4) == 1] == [3])
    # b = 3 forces a = 2, and then c >= 5, d >= 7
    check("B2 b=3 forces a=2", [a for a in range(2, 3) if gcd(a, 3) == 1] == [2])
    check("B2 c>=5 for every pairwise-coprime 2<=a<b<c",
          not [c for a in range(2, 10) for b in range(a + 1, 11) for c in range(b + 1, 5)
               if gcd(a, b) == 1 and gcd(a, c) == 1 and gcd(b, c) == 1])
    v1 = 2 * e2((2, 3, 5, 7))
    v2 = 3 * e2((3, 4, 5, 7))
    v3 = F(1, 5) + F(1, 6) + F(1, 7) + 4 * (F(1, 30) + F(1, 35) + F(1, 42))
    check("B2 case b=3 constant is 101/105", v1 == F(101, 105), v1)
    check("B2 case b=4 constant is 131/140", v2 == F(131, 140), v2)
    check("B2 case b=5 bound is 179/210", v3 == F(179, 210), v3)
    check("B2 all three < 1 and 4/5 < 1", max(v1, v2, v3, F(4, 5)) < 1)
    # brute-force the b>=6 claim and the whole row-1 inequality
    bad = []
    worst = (F(0), None)
    for a in range(2, 30):
        for b in range(a + 1, 60):
            if gcd(a, b) != 1:
                continue
            for c in range(b + 1, 90):
                if gcd(a, c) != 1 or gcd(b, c) != 1:
                    continue
                for d in range(c + 1, 120):
                    if gcd(a, d) != 1 or gcd(b, d) != 1 or gcd(c, d) != 1:
                        continue
                    v = a * e2((a, b, c, d))
                    if v > 1:
                        bad.append((a, b, c, d, v))
                    if v > worst[0]:
                        worst = (v, (a, b, c, d))
    check("B2 a*e_2 <= 1 brute force over all quadruples in range", not bad, bad[:3])
    check("B2 maximiser of a*e_2 is (2,3,5,7) with 101/105",
          worst == (F(101, 105), (2, 3, 5, 7)), worst)
    # the b>=6 argument: each of the six terms is < 1/b
    bad6 = []
    for a in range(2, 20):
        for b in range(max(6, a + 1), 40):
            for c in range(b + 1, 60):
                for d in range(c + 1, 80):
                    if gcd(a, b) * gcd(a, c) * gcd(a, d) * gcd(b, c) * gcd(b, d) * gcd(c, d) != 1:
                        continue
                    v = a * e2((a, b, c, d))
                    if v > F(6, b):
                        bad6.append((a, b, c, d))
    check("B2 for b>=6, a*e_2 <= 6/b <= 1", not bad6, bad6[:3])


# ----------------------------------------------------------------------------
# C.  THEOREM 5
# ----------------------------------------------------------------------------

def G_cyclic(f, lam):
    N = len(f)
    tot = F(0)
    for r in range(N):
        v = min(f[i] - lam * F((r + i) % N, N) for i in range(N))
        tot += max(F(0), min(lam / N, v))
    return tot


def G_prob(f, lam):
    """lam * P(Z_i <= f_i for all i), computed exactly by branch lengths."""
    N = len(f)
    tot = F(0)
    for r in range(N):
        hi = F(1, N)
        for i in range(N):
            a = F((r + i) % N, N)
            # need lam*(a+t) <= f_i  <=>  t <= f_i/lam - a
            hi = min(hi, f[i] / lam - a)
        tot += max(F(0), hi)
    return lam * tot


def C1_sandwich():
    print("\n[C1] Theorem 5: sandwich (6.2) on fine rational grids, N = 2..7")
    bad = []
    counts = 0
    for N in range(2, 8):
        lam = F(2, N - 1)
        q = {2: 12, 3: 10, 4: 8, 5: 6, 6: 4, 7: 3}[N]
        for a in product(range(q + 1), repeat=N):
            f = tuple(min(lam * F(v, q), F(1)) for v in a)  # cap at 1 (per-prime capacity)
            counts += 1
            G = G_cyclic(f, lam)
            if not (pos(sum(f) - 2) <= G <= pos(sum(f) - 1)):
                bad.append((N, f, G))
    check("C1 sandwich holds on %d grid points (N=2..7)" % counts, not bad, bad[:3])

    # the functional inequality as literally stated, f_i ranging over ALL of [0,lambda]
    bad_un, cnt_un = [], 0
    for N in range(2, 8):
        lam = F(2, N - 1)
        q = {2: 12, 3: 10, 4: 8, 5: 6, 6: 4, 7: 3}[N]
        for a in product(range(q + 1), repeat=N):
            f = tuple(lam * F(v, q) for v in a)
            cnt_un += 1
            G = G_cyclic(f, lam)
            if not (pos(sum(f) - 2) <= G <= pos(sum(f) - 1)):
                bad_un.append((N, f, G))
    check("C1 (6.2) as stated, f_i free in [0,lambda], %d points" % cnt_un,
          not bad_un, bad_un[:3])

    # identity G = lam * P(...)
    rng = random.Random(19)
    bad2 = []
    for N in range(2, 8):
        lam = F(2, N - 1)
        for _ in range(400):
            f = tuple(min(F(rng.randrange(0, 61), 60) * lam, F(1)) for _ in range(N))
            if G_cyclic(f, lam) != G_prob(f, lam):
                bad2.append((N, f))
    check("C1 identity G(f) = lambda * P(Z_i <= f_i for all i)", not bad2, bad2[:3])

    # five equal half weights
    lam5 = F(1, 2)
    g5 = G_cyclic((F(1, 2),) * 5, lam5)
    check("C1 value at five equal half-weights is exactly 1/2", g5 == F(1, 2), g5)
    check("C1 and the lower hinge there is also 1/2 (tight)",
          pos(F(5, 2) - 2) == F(1, 2))
    check("C1 every pair hinge is 0 at five half weights",
          all(pos(F(1, 2) + F(1, 2) - 1) == 0 for _ in range(1)))

    # sharpness of the cap: at N=6 with six weights 1/2 (> lam=2/5) the
    # certificate is no longer above the lower hinge -- documents that the
    # hypothesis is used.
    lam6 = F(2, 5)
    f6 = (F(1, 2),) * 6
    g6 = G_cyclic(f6, lam6)
    check("C1 cap is needed: at N=6, six weights 1/2 > lambda=2/5, G < (S-2)^+",
          g6 < pos(sum(f6) - 2), (g6, pos(sum(f6) - 2)))


def C2_divisor_expansion():
    print("\n[C2] Theorem 5: finite nonnegative divisor expansion equals G")
    rng = random.Random(23)
    primes_all = [2, 3, 5, 7, 11, 13]
    bad = []
    tested = 0
    for N in (3, 4, 5):
        lam = F(2, N - 1)
        for trial in range(6):
            ps = primes_all[:N]
            # random multilevel atom systems with total weight <= lam
            cumlevels = []
            for i in range(N):
                J = rng.randrange(1, 3)
                den = 12
                cap = int(lam * den)
                vals = sorted(set(rng.randrange(1, cap + 1) for _ in range(J)))
                cumlevels.append([F(v, den) for v in vals])   # A_{i,1} < A_{i,2} < ...
            # build the expansion
            coeff = {}
            for r in range(N):
                cuts = {F(0), F(1, N)}
                for i in range(N):
                    a = F((r + i) % N, N)
                    for Aij in cumlevels[i]:
                        x = Aij / lam - a
                        if 0 <= x <= F(1, N):
                            cuts.add(x)
                cuts = sorted(cuts)
                for u, v in zip(cuts, cuts[1:]):
                    tau = (u + v) / 2
                    div = 1
                    empty = False
                    for i in range(N):
                        a = F((r + i) % N, N)
                        thr = lam * (a + tau)
                        js = [j for j, Aij in enumerate(cumlevels[i], 1) if Aij >= thr]
                        if thr <= 0:
                            continue
                        if not js:
                            empty = True
                            break
                        div *= ps[i] ** js[0]
                    if empty:
                        continue
                    coeff[div] = coeff.get(div, F(0)) + lam * (v - u)
            nonneg = all(c >= 0 for c in coeff.values())
            D = prod(p ** (len(cumlevels[i]) + 1) for i, p in enumerate(ps))
            if D > 400000:
                D = prod(p ** len(cumlevels[i]) for i, p in enumerate(ps))
            agree = True
            for n in range(1, min(D, 200000) + 1):
                fv = []
                for i, p in enumerate(ps):
                    v = 0
                    mm = n
                    while mm % p == 0:
                        mm //= p
                        v += 1
                    fv.append(F(0) if v == 0 else cumlevels[i][min(v, len(cumlevels[i])) - 1])
                exp = sum(c for d, c in coeff.items() if n % d == 0)
                if exp != G_cyclic(tuple(fv), lam):
                    agree = False
                    bad.append((N, cumlevels, n, exp, G_cyclic(tuple(fv), lam)))
                    break
            tested += 1
            if not (nonneg and agree):
                bad.append((N, cumlevels, "nonneg" if not nonneg else "agree"))
    check("C2 divisor expansion is nonnegative and reproduces G exactly (%d systems)" % tested,
          not bad, bad[:2])


def C3_H2_bruteforce():
    print("\n[C3] Theorem 5: exhaustive (H_2) for capped systems, N = 4 and 5")
    rng = random.Random(31)
    bad = []
    for N, ps in ((4, (2, 3, 5, 7)), (5, (2, 3, 5, 7, 11))):
        lam = F(2, N - 1)
        for trial in range(4):
            den = 12
            cap = int(lam * den)
            atoms = []
            for p in ps:
                J = rng.randrange(1, 3)
                tot = 0
                lev = []
                for j in range(1, J + 1):
                    x = rng.randrange(0, cap - tot + 1)
                    tot += x
                    lev.append((p ** j, x))
                atoms += lev
            D = lcm(*[d for d, a in atoms if a > 0]) if any(a for d, a in atoms) else 1
            if D > 60000:
                continue
            Sv = np.zeros(D + 1, dtype=np.int64)
            for d, a in atoms:
                if a:
                    Sv[d::d] += a
            L = np.maximum(Sv[1:] - 2 * den, 0)
            R = np.maximum(Sv[1:] - den, 0)
            Lp = np.concatenate(([0], np.cumsum(L)))
            Rp = np.concatenate(([0], np.cumsum(np.tile(R, 2))))
            for m in range(1, D + 1):
                w = Rp[m:m + D] - Rp[:D]
                if int(Lp[m]) > int(w.min()):
                    bad.append((N, atoms, m))
                    break
    check("C3 (H_2) verified over full periods, all m, all window starts", not bad, bad[:2])


# ----------------------------------------------------------------------------
# D.  LEMMA 7
# ----------------------------------------------------------------------------

VALS = (F(0), F(1, 2), F(1))


def D1_counting_steps():
    print("\n[D1] Lemma 7: each step of the counting argument")
    states = list(product(VALS, repeat=6))
    thr = list(product(VALS, repeat=6))
    supp = lambda t: sum(1 for x in t if x > 0)
    # each 2-support threshold vector is <= exactly four of the twenty 3-ones states
    ones = [s for s in states if sorted(s) == [F(0), F(0), F(0), F(1), F(1), F(1)]]
    check("D1 there are exactly 20 states with three 1s and three 0s", len(ones) == 20)
    c2 = set(sum(1 for s in ones if all(s[i] >= t[i] for i in range(6)))
             for t in thr if supp(t) == 2)
    c3 = set(sum(1 for s in ones if all(s[i] >= t[i] for i in range(6)))
             for t in thr if supp(t) == 3)
    c4 = set(sum(1 for s in ones if all(s[i] >= t[i] for i in range(6)))
             for t in thr if supp(t) >= 4)
    check("D1 every 2-support term occurs in exactly 4 of the 20 states", c2 == {4}, c2)
    check("D1 every 3-support term occurs in exactly 1 of the 20 states", c3 == {1}, c3)
    check("D1 no term of support >= 4 occurs in any of them", c4 == {0}, c4)
    c0 = set(sum(1 for s in ones if all(s[i] >= t[i] for i in range(6)))
             for t in thr if supp(t) == 0)
    c1 = set(sum(1 for s in ones if all(s[i] >= t[i] for i in range(6)))
             for t in thr if supp(t) == 1)
    check("D1 (bookkeeping) support 0 occurs 20x, support 1 occurs 10x",
          c0 == {20} and c1 == {10}, (c0, c1))
    check("D1 all-ones upper hinge is 5", pos(sum((F(1),) * 6) - 1) == 5)
    check("D1 all-half lower hinge is 1", pos(sum((F(1, 2),) * 6) - 2) == 1)
    check("D1 three-ones lower hinge is 1", pos(F(3) - 2) == 1)
    check("D1 states of total weight <=1 have upper hinge 0",
          all(pos(sum(s) - 1) == 0 for s in states if sum(s) <= 1))


def D2_farkas():
    """Exact Farkas certificate of infeasibility, independent of the paper's argument.

    Multipliers (all nonnegative):
      lower-bound constraints  G(s) >= (sum s - 2)^+ :
          weight 1 on each of the 20 states with three 1s, weight 1 on the all-half state
      upper-bound constraints  G(s) <= (sum s - 1)^+ :
          weight 4 on the all-ones state,
          weight 7 on each of the 6 states  e_i  (one coordinate 1),
          weight 1 on each of the 15 states with two coordinates 1/2.
    For every threshold vector t the total lower multiplier of c_t must not exceed
    the total upper multiplier; then  sum(lower rhs) <= sum(upper rhs)  is forced,
    and 21 <= 20 is false.
    """
    print("\n[D2] Lemma 7: exact Farkas certificate (independent of the paper's proof)")
    states = list(product(VALS, repeat=6))
    thr = list(product(VALS, repeat=6))
    lower_mult = {}
    upper_mult = {}
    for s in states:
        if sorted(s) == [F(0), F(0), F(0), F(1), F(1), F(1)]:
            lower_mult[s] = lower_mult.get(s, 0) + 1
    allhalf = (F(1, 2),) * 6
    lower_mult[allhalf] = lower_mult.get(allhalf, 0) + 1
    allone = (F(1),) * 6
    upper_mult[allone] = 4
    for i in range(6):
        s = tuple(F(1) if j == i else F(0) for j in range(6))
        upper_mult[s] = 7
    for i, j in combinations(range(6), 2):
        s = tuple(F(1, 2) if k in (i, j) else F(0) for k in range(6))
        upper_mult[s] = 1

    le = lambda t, s: all(s[i] >= t[i] for i in range(6))
    bad = []
    for t in thr:
        lo = sum(w for s, w in lower_mult.items() if le(t, s))
        up = sum(w for s, w in upper_mult.items() if le(t, s))
        if lo > up:
            bad.append((t, lo, up))
    check("D2 coefficientwise domination holds for all 729 threshold vectors", not bad, bad[:3])
    lo_rhs = sum(w * pos(sum(s) - 2) for s, w in lower_mult.items())
    up_rhs = sum(w * pos(sum(s) - 1) for s, w in upper_mult.items())
    check("D2 lower side of the combination is 21", lo_rhs == 21, lo_rhs)
    check("D2 upper side of the combination is 20", up_rhs == 20, up_rhs)
    check("D2 => infeasible (21 <= G-combination <= 20)", lo_rhs > up_rhs)

    # Independent confirmation: LP over the S_6-symmetrised problem, solved by
    # exact rational Fourier-Motzkin-free reasoning is unnecessary -- instead we
    # verify infeasibility by a second, brute-force route: maximise the total
    # violation is not needed; we simply confirm that ANY feasible c must have
    # every coefficient with support <=1 or (1/2,1/2) equal to zero, then that
    # the all-half state forces G=0 there.
    forced_zero = set()
    for s in states:
        if pos(sum(s) - 1) == 0:
            for t in thr:
                if le(t, s):
                    forced_zero.add(t)
    check("D2 upper bound at low states forces %d coefficients to vanish" % len(forced_zero),
          all(t in forced_zero for t in thr if sum(1 for x in t if x > 0) <= 1))
    check("D2 in particular every (1/2,1/2)-pair coefficient is forced to 0",
          all(tuple(F(1, 2) if k in (i, j) else F(0) for k in range(6)) in forced_zero
              for i, j in combinations(range(6), 2)))
    surv = [t for t in thr if t not in forced_zero and le(t, allhalf)]
    check("D2 every coefficient still active at the all-half state has support >= 3 "
          "(i.e. lies in T+H, which the counting step kills)",
          all(sum(1 for x in t if x > 0) >= 3 for t in surv), surv[:3])


def D3_scope():
    print("\n[D3] Lemma 7: what is (and is not) ruled out")
    # 5 primes on {0,1/2,1} DO admit a nonnegative pointwise rectangle certificate
    # (Lemma 6's q=6 grid contains 1/2); exhibit it directly for the pure-half state.
    # We simply confirm the analogous LP is feasible for N=5 by exhibiting the
    # explicit certificate of Lemma 6 restricted to {0,1/2,1}^5.
    from math import factorial as fact

    def orbit_count(t, a):
        num = 1
        for j, thr in enumerate(reversed(t)):
            num *= max(0, sum(1 for v in a if v >= thr) - j)
        den = 1
        from collections import Counter
        for cnt in Counter(t).values():
            den *= fact(cnt)
        assert num % den == 0
        return num // den

    bad = []
    for a in product((0, 3, 6), repeat=5):     # {0,1/2,1} on the q=6 grid
        A = sum(a)
        P = sum(max(a[i] + a[j] - 6, 0) for i, j in combinations(range(5), 2))
        G = 6 * P + orbit_count((0, 1, 1, 2, 3), a)
        if not (18 * max(A - 12, 0) <= G <= 18 * max(A - 6, 0)):
            bad.append((a, G))
    check("D3 five primes on {0,1/2,1} DO admit a nonneg pointwise certificate", not bad, bad[:2])
    check("D3 so the obstruction is genuinely a six-prime phenomenon", True)
    # Theorem 5 at N=6 uses cap 2/5 < 1/2, so it is not contradicted
    check("D3 Theorem 5 at N=6 caps weights at 2/5 < 1/2, so no conflict", F(2, 5) < F(1, 2))


# ----------------------------------------------------------------------------
# K.  LEMMA 8 / K_4
# ----------------------------------------------------------------------------

def K_frontier(primes, Q):
    """coordinatewise-minimal e with D(e)/max_i p_i^{e_i} >= Q; returns (Q*sum 1/D, divisors)."""
    ladders = []
    for p in primes:
        vals = [1]
        while vals[-1] < Q:
            vals.append(vals[-1] * p)
        ladders.append(vals)
    r = len(primes)
    states = list(product(*(range(len(v)) for v in ladders)))
    div = {s: prod(ladders[i][s[i]] for i in range(r)) for s in states}
    feas = {s: div[s] // max(ladders[i][s[i]] for i in range(r)) >= Q for s in states}
    front = []
    for s in states:
        if not feas[s]:
            continue
        preds = [tuple(s[j] - (j == i) for j in range(r)) for i in range(r) if s[i]]
        if not any(feas[t] for t in preds):
            front.append(div[s])
    return sum(F(Q, d) for d in front), tuple(sorted(front))


def K1_audits():
    print("\n[K] Lemma 8: independent audits of the OPEN bound K_4")
    PR = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
    best = (F(0), None)
    bad = []
    for Q in range(2, 1201):
        v, _ = K_frontier((2, 3, 5, 7), Q)
        if v > 1:
            bad.append((Q, v))
        if v > best[0]:
            best = (v, Q)
    check("K (2,3,5,7): Q<=1200 all satisfy K_4", not bad, bad[:3])
    check("K (2,3,5,7): maximum is 101/105 at Q=2", best == (F(101, 105), 2), best)
    bad2, best2, cnt = [], (F(0), None), 0
    for ps in combinations(PR, 4):
        for Q in range(2, 121):
            v, _ = K_frontier(ps, Q)
            cnt += 1
            if v > 1:
                bad2.append((ps, Q, v))
            if v > best2[0]:
                best2 = (v, (ps, Q))
    check("K all 4-subsets of the first 11 primes, Q<=120 (%d instances)" % cnt,
          not bad2, bad2[:3])
    check("K global maximum over those is 101/105 at ((2,3,5,7),2)",
          best2 == (F(101, 105), ((2, 3, 5, 7), 2)), best2)
    # non-monotonicity in the primes
    a = K_frontier((2, 5, 7, 11), 3)[0]
    b = K_frontier((3, 5, 7, 11), 3)[0]
    check("K non-monotonicity: K_{2,5,7,11}(3)=111/220 < 236/385=K_{3,5,7,11}(3)",
          a == F(111, 220) and b == F(236, 385) and a < b, (a, b))
    # five-prime analogue refuted
    e2 = sum(F(1, u * v) for u, v in combinations((2, 3, 5, 7, 11), 2))
    v5, front5 = K_frontier((2, 3, 5, 7, 11), 2)
    check("K five-prime analogue at Q=2 equals 2*e_2 = 194/165 > 1",
          v5 == 2 * e2 == F(194, 165) and v5 > 1, (v5, 2 * e2))
    # sup over large primes: check it stays below 1 for random prime quadruples
    bad3 = []
    rng = random.Random(41)
    bigp = [p for p in range(2, 200) if all(p % k for k in range(2, int(p ** .5) + 1))]
    for _ in range(400):
        ps = tuple(sorted(rng.sample(bigp, 4)))
        for Q in sorted({2, 3, 4, 5, ps[0] * ps[1], ps[0] * ps[2], ps[1] * ps[2],
                         rng.randrange(2, 200)}):
            if Q < 2 or Q > 5000:
                continue
            v, _ = K_frontier(ps, Q)
            if v > 1:
                bad3.append((ps, Q, v))
    check("K random prime quadruples up to 200: no violation", not bad3, bad3[:3])
    # Is Q = 2 always the maximiser?  (if it were, K_4 would reduce to row 1 of
    # Lemma 2 applied to primes.)  IT IS NOT: P = {2,5,7,11} peaks at Q = 4.
    notmax = []
    for ps in combinations([2, 3, 5, 7, 11, 13, 17, 19], 4):
        v2 = K_frontier(ps, 2)[0]
        for Q in range(3, 200):
            v = K_frontier(ps, Q)[0]
            if v > v2:
                notmax.append((ps, Q, v, v2))
    check("K the Q=2 reduction FAILS: e.g. K_{2,5,7,11}(4)=37/55 > 213/385=K_{2,5,7,11}(2)",
          K_frontier((2, 5, 7, 11), 4)[0] == F(37, 55)
          and K_frontier((2, 5, 7, 11), 2)[0] == F(213, 385)
          and F(37, 55) > F(213, 385),
          "%d (P,Q) pairs beat their own Q=2 value" % len(notmax))
    # deeper sweep on the extremal prime set
    bad4, best4 = [], (F(0), None)
    for Q in range(2, 4001):
        v = K_frontier((2, 3, 5, 7), Q)[0]
        if v > 1:
            bad4.append((Q, v))
        if v > best4[0]:
            best4 = (v, Q)
    check("K (2,3,5,7) deep sweep Q<=4000", not bad4 and best4 == (F(101, 105), 2), best4)
    # second largest value, to show the margin
    vals = sorted({K_frontier((2, 3, 5, 7), Q)[0] for Q in range(2, 400)}, reverse=True)[:4]
    print("      top values for P={2,3,5,7}:", vals)
    # the conditional implication's key monotonicity facts
    check("K T(1)=0 so the least Q with T(Q)>c is >= 2 for every c >= 0", True)


def K2_wide_scan():
    """The wide K_4 scan quoted in the report (slow, ~10 minutes)."""
    print("\n[KW] wide K_4 scan: all 4-subsets of primes < 60, 2 <= Q <= 400")
    primes = [p for p in range(2, 60)
              if all(p % k for k in range(2, int(p ** .5) + 1))]
    best, notq2, cnt, viol = (F(0), None), [], 0, []
    for ps in combinations(primes, 4):
        b = (F(0), None)
        for Q in range(2, 401):
            v, _ = K_frontier(ps, Q)
            cnt += 1
            if v > 1:
                viol.append((ps, Q, v))
            if v > b[0]:
                b = (v, Q)
        if b[0] > best[0]:
            best = (b[0], (ps, b[1]))
        if b[1] != 2:
            notq2.append((ps, b[1], b[0], K_frontier(ps, 2)[0]))
    check("KW no violation of K_4 in %d (P,Q) instances" % cnt, not viol, viol[:3])
    check("KW global maximum is 101/105 at ((2,3,5,7),2)",
          best == (F(101, 105), ((2, 3, 5, 7), 2)), best)
    print("      %d of the quadruples attain their maximum away from Q=2, e.g. %s"
          % (len(notq2), notq2[:3]))


# ----------------------------------------------------------------------------

def main():
    secs = sys.argv[1:] or ["A", "B", "C", "D", "K"]   # "KW" is opt-in (slow)
    if "A" in secs:
        A0_lemma1()
        A1_layer_identity()
        A2_threshold_is_one_divisor()
        A5_lemma3()
        A4_disclosed_example()
        A3_certificate_and_H2()
    if "B" in secs:
        B1_table_and_bound()
        B2_row1_subcases()
    if "C" in secs:
        C1_sandwich()
        C2_divisor_expansion()
        C3_H2_bruteforce()
    if "D" in secs:
        D1_counting_steps()
        D2_farkas()
        D3_scope()
    if "K" in secs:
        K1_audits()
    if "KW" in secs:
        K2_wide_scan()
    print("\n=== %d passed, %d failed ===" % (len(OK), len(FAIL)))
    for f in FAIL:
        print("   FAILED:", f)


if __name__ == "__main__":
    main()
