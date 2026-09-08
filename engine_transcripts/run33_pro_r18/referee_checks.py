#!/usr/bin/env python3
"""
Independent exact-arithmetic referee checks for the claimed proof of H_{97/10}
in /Users/roychen/workspace/claudecode/automath/engine/out/pro_708_r18/proof.md

Everything is recomputed from the DEFINITIONS in the manuscript, in
fractions.Fraction / integer arithmetic only.  No floating point is used for
any decision; floats appear only in printed diagnostics.

Author: adversarial referee (Claude Opus 5).
"""
from fractions import Fraction as Fr
from math import comb, factorial, floor
import sys

# ----------------------------------------------------------------------------
# Constants of the manuscript
# ----------------------------------------------------------------------------
Q   = 65536
Hs  = Fr(1025, 1024)      # H_*
Gam = Fr(211, 210)        # Gamma
K   = Fr(8, 3)
lam = Fr(51, 10)          # lambda
rho = Fr(5, 4)
D0  = Fr(47, 16)
T   = Fr(541, 100)
CTH = Fr(97, 10)          # threshold c

OK = []
BAD = []
def check(name, cond, extra=""):
    (OK if cond else BAD).append(name)
    print(("  [OK]  " if cond else "  [FAIL]") + " " + name + ("   " + extra if extra else ""))

print("=" * 78)
print("0. Constant identities")
print("=" * 78)
check("D0 + rho*T == 97/10", D0 + rho * T == CTH, f"{D0+rho*T}")
check("c = 97/10 >= 7 (needed by Lemma 2 (3))", CTH >= 7)
check("T - 2 = 341/100 > 3 (Lemma 4 cofactor argument)", T - 2 == Fr(341,100) and T - 2 > 3)

# ----------------------------------------------------------------------------
# Lemma 2, inequality (4):  (1-1/Q) H_* - H_*^8/8! > 1
# ----------------------------------------------------------------------------
print()
print("=" * 78)
print("1. Lemma 2 (dense branch, inequality (4))")
print("=" * 78)
dense = (1 - Fr(1, Q)) * Hs - Hs ** 8 / factorial(8)
check("(1-1/Q)H_* - H_*^8/8! > 1", dense > 1, f"value-1 = {dense-1} ~ {float(dense-1):.3e}")
# 510510 > Q
check("2*3*5*7*11*13*17 = 510510 > Q = 65536", 2*3*5*7*11*13*17 == 510510 and 510510 > Q)
# side remark: smallest integer with 10 distinct primes
p10 = 1
for p in [2,3,5,7,11,13,17,19,23,29]:
    p10 *= p
print(f"  (note) product of first 10 primes = {p10} : for m < {p10}, omega(k)<=9 < 97/10, LHS vanishes")

# ----------------------------------------------------------------------------
# Lemma 1:  A_r(a) = (v-a)/C(v,r),  v = floor(ra/(r-1))
# ----------------------------------------------------------------------------
def A_r(a, r):
    """Lemma 1 coefficient, a >= r-1, r >= 2."""
    assert r >= 2
    assert a >= r - 1, (a, r)
    v = floor(Fr(r, 1) * a / (r - 1))
    assert v >= r, (a, r, v)
    return Fr(v - a, 1) / comb(v, r) if not isinstance(a, Fr) else (v - a) / comb(v, r)

def A_r_bruteforce_max(a, r, hmax=4000):
    """max over integer h>=r of (h-a)^+/C(h,r): independent check of A_r."""
    best = Fr(0)
    for h in range(r, hmax + 1):
        num = h - a
        if num <= 0:
            continue
        val = num / comb(h, r)
        if val > best:
            best = val
    return best

print()
print("=" * 78)
print("2. Lemma 1: vertex coefficient A_r(a) recomputed / cross-checked")
print("=" * 78)
ok = True
for (aa, rr) in [(Fr(7),8), (Fr(341,100),2), (Fr(341,100),3), (Fr(341,100),4),
                 (Fr(1023,100),5), (Fr(37,2),9), (Fr(100),20), (Fr(1971,50),12)]:
    f = A_r(aa, rr)
    b = A_r_bruteforce_max(aa, rr, hmax=3000)
    if f != b:
        ok = False
        print(f"   mismatch a={aa} r={rr}: formula {f} vs brute {b}")
check("A_r(a) = max_h (h-a)^+/C(h,r) on sampled (a,r)", ok)
check("A_8(7) = 1  ((sum u -7)^+ <= e_8)", A_r(Fr(7), 8) == 1)

# ----------------------------------------------------------------------------
# Lemma 5 coefficient bound epsilon_{theta,s}
# ----------------------------------------------------------------------------
_eps_cache = {}
def eps(theta, s):
    """epsilon_{theta,s} = min_{2<=r<=floor(a)+1} theta*A_r(a)*(H_*/theta)^r/r!,  a=(T-s)/theta"""
    key = (theta, s)
    if key in _eps_cache:
        return _eps_cache[key]
    a = (T - s) / theta
    rmax = floor(a) + 1
    best = None
    z = Hs / theta
    zp = z * z          # z^r
    fact = 2
    for r in range(2, rmax + 1):
        if r > 2:
            zp *= z
            fact *= r
        val = theta * A_r(a, r) * zp / fact
        if best is None or val < best:
            best = val
    _eps_cache[key] = best
    return best

# ----------------------------------------------------------------------------
# The level set  D = {1} u {j/2^h : h>=3, j in 4..7}
# ----------------------------------------------------------------------------
def levels_ge(theta, hmax=40):
    """all t in D with t >= theta"""
    out = {Fr(1)}
    for h in range(3, hmax + 1):
        for jj in range(4, 8):
            t = Fr(jj, 2 ** h)
            if t >= theta:
                out.add(t)
    return sorted(out)

print()
print("=" * 78)
print("3. Level set D: adjacent ratio <= 5/4 ?")
print("=" * 78)
Dlev = sorted({Fr(1)} | {Fr(jj, 2**h) for h in range(3, 14) for jj in range(4, 8)}, reverse=True)
worst = max(Dlev[i] / Dlev[i+1] for i in range(len(Dlev)-1))
check("max ratio of adjacent D-levels == 5/4", worst == Fr(5,4), f"{worst}")

# ----------------------------------------------------------------------------
# Lemma 6 / 7: exact A_{j,L}
# ----------------------------------------------------------------------------
def polypow_coeffs(exps, N, deg):
    """coefficients 0..deg of (1 + sum_{e in exps} X^e)^N, truncated."""
    cur = [0] * (deg + 1)
    cur[0] = 1
    es = [e for e in exps if e <= deg]
    out = [cur[:]]
    for _ in range(N):
        nxt = cur[:]                       # the '1' term
        for e in es:
            for i in range(0, deg - e + 1):
                ci = cur[i]
                if ci:
                    nxt[i + e] += ci
        cur = nxt
        out.append(cur[:])
    return out

def A_jL(j, L, verbose=False, extra_N=6):
    theta = Fr(j, L)
    lev = levels_ge(theta)
    exps = sorted({int(L * t) for t in lev})
    assert all(Fr(L,1) * t == int(L*t) for t in lev), (j, L)
    deg = L + j
    Nmax = floor(Fr(11, 3) * Fr(L, j) + 1)
    Gp = polypow_coeffs(exps, Nmax + extra_N, deg)
    exps2 = [e for e in exps if e != j]
    assert j in exps
    Pp = polypow_coeffs(exps2, Nmax + extra_N, deg)
    epsd = {d: eps(theta, 1 + Fr(d, L)) for d in range(1, j + 1)}
    best = Fr(0); bestN = None
    beyond = Fr(0)
    for N in range(0, Nmax + extra_N + 1):
        tot = Fr(0)
        for d in range(1, j + 1):
            cnt = Gp[N][L + d] - Pp[N][L + d]
            if cnt == 0:
                continue
            assert cnt > 0
            num = 1 - max(Fr(0), Fr(N,1) * theta - 1 - Fr(d, L)) / K
            if num <= 0:
                continue
            den = max(Fr(d, L), Fr(N,1) * theta - 1)
            tot += cnt * epsd[d] * num / den
        if N <= Nmax:
            if tot > best:
                best, bestN = tot, N
        else:
            if tot > beyond:
                beyond = tot
    return best, bestN, beyond, Nmax

print()
print("=" * 78)
print("4. Lemma 7: the 29 finite scales, recomputed exactly")
print("=" * 78)
scales = [(4, 4)] + [(j, L) for L in [8, 16, 32, 64, 128, 256, 512] for j in (4, 5, 6, 7)]
print(f"  number of finite scales = {len(scales)}")
perL = {}
total_finite = Fr(0)
beyond_bad = False
for (j, L) in scales:
    v, bN, beyond, Nmax = A_jL(j, L)
    perL[L] = perL.get(L, Fr(0)) + v
    total_finite += v
    if beyond > 0:
        beyond_bad = True
    print(f"   L={L:4d} j={j}  A = {float(v):.9e}   (argmax N={bN}, Nmax={Nmax}, beyond-range max={float(beyond)})")
    sys.stdout.flush()

print()
author_tab = {4: 24680, 8: 128711, 16: 25773, 32: 5665, 64: 1025, 128: 150, 256: 21, 512: 3}
allrows = True
for L in sorted(perL):
    exact = perL[L]
    claimed = Fr(author_tab[L], 10 ** 6)
    good = exact < claimed
    allrows &= good
    print(f"   L={L:4d}:  exact sum_j A_(j,L) = {float(exact):.10e}   author bound {author_tab[L]}/10^6"
          f"   -> {'OK' if good else 'VIOLATED'}   (exact*10^6 = {float(exact*10**6):.6f})")
check("every row of the Lemma 7 table is a valid strict upper bound", allrows)
check("N-range floor((K+1)L/j+1) suffices (no contribution beyond)", not beyond_bad)
print(f"\n   exact finite-scale total = {float(total_finite):.15f}")
print(f"   as fraction (num/den digits) = {len(str(total_finite.numerator))}/{len(str(total_finite.denominator))} digits")
check("finite total < 187/1000  (eq. (16))", total_finite < Fr(187, 1000),
      f"total*1000 = {float(total_finite*1000):.9f}")
lo = Fr(186024001631, 10**12); hi = Fr(186024001632, 10**12)
check("finite total in the author's stated interval [186024001631,186024001632]/10^12",
      lo <= total_finite <= hi, f"total = {float(total_finite):.15f}")
check("author's table numerators sum to 186028", sum(author_tab.values()) == 186028)

# ----------------------------------------------------------------------------
# Lemma 8
# ----------------------------------------------------------------------------
print()
print("=" * 78)
print("5. Lemma 8: analytic tail")
print("=" * 78)

def e_bounds(n=30):
    """rigorous rational bounds  lo < e < hi"""
    s = Fr(0)
    for k in range(0, n + 1):
        s += Fr(1, factorial(k))
    lo = s
    hi = s + Fr(1, factorial(n) * n)     # tail sum_{k>n} 1/k! < 1/(n!*n)
    return lo, hi
elo, ehi = e_bounds()
check("e < 87/32", ehi < Fr(87, 32), f"e < {float(ehi)}")
check("e > 8/3",  elo > Fr(8, 3))
check("(87/32)^3 < (9/2)^2", Fr(87,32)**3 < Fr(9,2)**2, f"{float(Fr(87,32)**3)} < {float(Fr(9,2)**2)}")
# hence e*log(9/2) > (8/3)*(3/2) = 4
check("=> e*log(9/2) > 4  (so theta*z/(e log z) < 9 theta/8)", True)

def exp_upper(x, n=60):
    """rigorous rational upper bound for exp(x), x>0 rational, needs x < n+2"""
    assert x < n + 2
    s = Fr(0); term = Fr(1)
    for k in range(0, n + 1):
        s += term
        term = term * x / (k + 1)
    # remainder sum_{k>n} x^k/k!  <= x^{n+1}/(n+1)! * 1/(1-x/(n+2))
    return s + term / (1 - x / (n + 2))

E35 = exp_upper(Fr(7, 2) * Hs)
check("exp((7/2)H_*) < 133/4", E35 < Fr(133, 4), f"exp(..) < {float(E35)}, 133/4={33.25}")
a0 = Fr(4377, 100000)
check("(133/4)^100 < a0^100 * (9/2)^441", Fr(133,4)**100 < a0**100 * Fr(9,2)**441,
      f"ratio = {float((Fr(133,4)**100)/(a0**100*Fr(9,2)**441)):.9f}")

xs = {4: Fr(583,1000), 5: Fr(321,500), 6: Fr(69,100), 7: Fr(73,100)}
Fs = {4: Fr(632591,500000), 5: Fr(159089,125000), 6: Fr(1278827,1000000), 7: Fr(639137,500000)}

def G_j_upper(j, x):
    """1 + sum_{a=j}^7 x^a + sum_{r=1}^{4} sum_{a=4}^7 x^{a 2^r} + x^128/(1-x)"""
    s = Fr(1)
    for a in range(j, 8):
        s += x ** a
    for r in range(1, 5):
        for a in range(4, 8):
            s += x ** (a * 2 ** r)
    s += x ** 128 / (1 - x)
    return s

def G_j_exact(j, x, rmax=12):
    s = Fr(1)
    for a in range(j, 8):
        s += x ** a
    for r in range(1, rmax + 1):
        for a in range(4, 8):
            s += x ** (a * 2 ** r)
    return s

allG = True; allF = True; allq = True
for j in range(4, 8):
    x, Fj = xs[j], Fs[j]
    gu = G_j_upper(j, x)
    ge = G_j_exact(j, x)
    g1 = gu <= Fj
    g2 = Fj >= Fr(5, 4)
    g3 = a0 ** 3 * x ** (-3 * j) * Fj ** 11 < 1
    allG &= g1; allF &= g2; allq &= g3
    print(f"   j={j}: G_j(x_j) <= {float(gu):.12f}   F_j = {float(Fj):.12f}   [{'OK' if g1 else 'FAIL'}]"
          f"   (true G_j ~ {float(ge):.12f});  a0^3 x^-3j F^11 = {float(a0**3*x**(-3*j)*Fj**11):.9f}")
check("G_j(x_j) <= F_j for j=4..7 (with tail x^128/(1-x))", allG)
check("F_j >= 5/4 for j=4..7", allF)
check("a0^3 x_j^{-3j} F_j^{11} < 1 for j=4..7 (i.e. q_j<1)", allq)
check("(4/5)^4 < (3/4)^3", Fr(4,5)**4 < Fr(3,4)**3, f"{Fr(4,5)**4} < {Fr(3,4)**3}")
check("9/(8*(8/3)*(8/3)*(4/3)*(2/9)) == 2187/4096",
      Fr(9,1)/(8*Fr(8,3)*Fr(8,3)*Fr(4,3)*Fr(2,9)) == Fr(2187,4096))
check("1024/j >= 146 for j<=7", Fr(1024,7) >= 146, f"1024/7={float(Fr(1024,7)):.4f}")

Ds = {j: sum(xs[j] ** (-d) for d in range(1, j + 1)) for j in range(4, 8)}
t = Fr(3, 4) ** 146
tail_low  = Fr(9, 8) * sum(j * Ds[j] for j in range(4, 8)) * t / (1 - t)
tail_high = Fr(2187, 4096) * Fr(4, 3 * 1024 ** 2) * sum(j * j * Fs[j] * Ds[j] for j in range(4, 8))
tail = tail_low + tail_high
print(f"   tail_low  = {float(tail_low):.6e}")
print(f"   tail_high = {float(tail_high):.15f}")
print(f"   tail      = {float(tail):.15f}")
check("tail < 3/1000  (eq. (21))", tail < Fr(3, 1000), f"tail*1000 = {float(tail*1000):.9f}")
tlo = Fr(2846921822, 10**12); thi = Fr(2846921823, 10**12)
check("tail in the author's stated interval [2846921822,2846921823]/10^12", tlo <= tail <= thi)

# ----------------------------------------------------------------------------
# combination (22)
# ----------------------------------------------------------------------------
print()
print("=" * 78)
print("6. Combination (22) and Lemma 9 window value")
print("=" * 78)
tot_const = total_finite + tail
check("A_{4,4}+sum finite + tail <= 19/100", tot_const <= Fr(19, 100),
      f"total = {float(tot_const):.15f}")
check("lambda * 19/100 == 969/1000", lam * Fr(19,100) == Fr(969,1000))
check("969/1000 <= 1 (so 969/1000 (B-1)^+ <= (S-1)^+)", Fr(969,1000) <= 1)
lam_tot = lam * tot_const
lo2 = Fr(963241709618, 10**12); hi2 = Fr(963241709619, 10**12)
check("lambda*(finite+tail) in author's stated interval [963241709618,963241709619]/10^12",
      lo2 <= lam_tot <= hi2, f"{float(lam_tot):.15f}")

wv = lam * (1 - 2 * Gam * Hs / K)
check("lambda(1-2*Gamma*H_*/K) == 718539/573440", wv == Fr(718539, 573440), f"{wv} = {float(wv)}")
check("718539/573440 > 5/4", wv > Fr(5, 4), f"excess = {wv - Fr(5,4)} = {Fr(1739,573440)}")
check("excess == 1739/573440", wv - Fr(5,4) == Fr(1739, 573440))

# ----------------------------------------------------------------------------
# Lemma 4 exponent budget, exhaustive over the case structure
# ----------------------------------------------------------------------------
print()
print("=" * 78)
print("7. Lemma 4: exponent budget sum_{p in C} eta(t_p) <= 2/3, exhaustive search")
print("=" * 78)
def eta(t):
    return Fr(1, 3) if t > Fr(1, 2) else 4 * t / 9

# enumerate all legal carriers: nonincreasing D-levels, shortest prefix of mass > 1.
# (levels truncated at h<=6, i.e. min level 1/16; the budget for all-low carriers
#  is (4/9)s_C <= 2/3 independently of how small the levels are, so this is a
#  faithful stress test of the case structure, not of an unbounded search.)
levels = sorted({Fr(1)} | {Fr(jj, 2**h) for h in range(3, 7) for jj in range(4, 8)}, reverse=True)
worst = Fr(0); worst_C = None
bad_s = False
ncarr = 0
def rec(idx, chosen, mass):
    global worst, worst_C, bad_s, ncarr
    if mass > 1:
        theta = chosen[-1]
        s = mass
        if not (1 < s <= 1 + theta <= 2):
            bad_s = True
        b = sum(eta(t) for t in chosen)
        ncarr += 1
        if b > worst:
            worst = b; worst_C = list(chosen)
        return
    for i in range(idx, len(levels)):
        chosen.append(levels[i]); rec(i, chosen, mass + levels[i]); chosen.pop()
rec(0, [], Fr(0))
print(f"   enumerated {ncarr} carrier level-multisets")
check("(7) 1 < s_C <= 1+theta_C <= 2 for every enumerated carrier", not bad_s)
check("max_C sum eta(t_p) <= 2/3  (=> P_C <= m^{2/3}) ", worst <= Fr(2, 3),
      f"worst budget = {worst} attained at {worst_C}")

print()
print("=" * 78)
print(f"SUMMARY: {len(OK)} checks passed, {len(BAD)} failed")
if BAD:
    for b in BAD:
        print("   FAILED: " + b)
print("=" * 78)

# ----------------------------------------------------------------------------
# 8. End-to-end hostile test of the POINTWISE certificate bound (15).
#
#    Take an ARBITRARY profile (b_p(n))_p of effective levels at a point n.
#    Enumerate (by exact DP) EVERY carrier C that can divide n, i.e. every
#    assignment of levels t_p in D with theta <= t_p <= b_p(n), min t_p = theta,
#    and 1 < s_C <= 1+theta  -- these are exactly the carriers whose P_C can
#    divide n.  Give each the LARGEST coefficient the proof allows,
#    c_C = eps_{theta_C,s_C}, and compare
#           sum_C c_C (1 - U_C(n)/K)^+     against     CONST * (B(n)-1)^+
#    with CONST = A_{4,4} + (finite scales) + tail, the constant Lemmas 7-8
#    prove.  U_C(n) = sum_{p not in C} min(b_p(n),theta) = T_theta - |C| theta.
#    Any ratio above CONST would refute (15).
# ----------------------------------------------------------------------------
import random
print()
print("=" * 78)
print("8. Hostile end-to-end test of the pointwise bound (15)")
print("=" * 78)

def jL_of(t):
    """unique (j,L) with t = j/L, j in {4,5,6,7}, L = 2^h (h>=3); level 1 -> (4,4)."""
    if t == 1:
        return 4, 4
    h = 3
    while not (4 <= t * 2 ** h <= 7):
        h += 1
    assert (t * 2 ** h).denominator == 1
    return int(t * 2 ** h), 2 ** h

def carrier_sum(profile, LEVELS):
    """exact sum_C eps_{theta,s}(1-U_C/K)^+ over all carriers C dividing the point."""
    B = sum(profile)
    total = Fr(0)
    for theta in sorted({t for t in LEVELS if any(b >= t for b in profile)}):
        j, L = jL_of(theta)          # theta = j/L with j in {4,..,7}, L = 2^h (level 1 -> (4,4))
        Tth = sum(min(b, theta) for b in profile)
        elig = [b for b in profile if b >= theta]
        cap = L + j
        # DP over eligible primes: state (units, count, hasmin) -> multiplicity
        state = {(0, 0, False): 1}
        for b in elig:
            opts = []
            for t in LEVELS:
                if theta <= t <= b:
                    assert (t * L).denominator == 1, (t, theta, L)
                    opts.append(int(t * L))
            nxt = {}
            for (u, c, hm), w in state.items():
                nxt[(u, c, hm)] = nxt.get((u, c, hm), 0) + w      # skip this prime
                for uu in opts:
                    v = u + uu
                    if v > cap:
                        continue
                    key = (v, c + 1, hm or (uu == j))
                    nxt[key] = nxt.get(key, 0) + w
            state = nxt
        for (u, c, hm), w in state.items():
            if not hm or u <= L:
                continue
            s = Fr(u, L)
            num = 1 - (Tth - c * theta) / K
            if num > 0:
                total += w * eps(theta, s) * num
    return total, B

CONST = total_finite + tail
tests = []
LEV = {}
LEV["ge1/2"] = sorted({Fr(1), Fr(7,8), Fr(3,4), Fr(5,8), Fr(1,2)}, reverse=True)
LEV["ge1/4"] = sorted({Fr(1)} | {Fr(jj, 2**h) for h in (3,4) for jj in range(4,8)}, reverse=True)
LEV["ge1/8"] = sorted({Fr(1)} | {Fr(jj, 2**h) for h in (3,4,5) for jj in range(4,8)}, reverse=True)
LEV["ge1/16"] = sorted({Fr(1)} | {Fr(jj, 2**h) for h in (3,4,5,6) for jj in range(4,8)}, reverse=True)

overall_ok = True
for tag, LEVELS in LEV.items():
    profs = []
    kmax = {"ge1/2": 14, "ge1/4": 20, "ge1/8": 16, "ge1/16": 11}[tag]
    for lev in LEVELS:
        for k in range(2, kmax + 1):
            profs.append([lev] * k)
    for a in LEVELS:
        for b in LEVELS:
            for k in (1, 2, 3):
                for l in range(1, min(kmax, 12)):
                    if k + l <= kmax:
                        profs.append([a] * k + [b] * l)
    random.seed(2718)
    nrand = {"ge1/2": 600, "ge1/4": 400, "ge1/8": 150, "ge1/16": 40}[tag]
    for _ in range(nrand):
        profs.append([random.choice(LEVELS) for _ in range(random.randint(2, min(kmax, 12)))])
    seen = set(); uniq = []
    for p in profs:
        key = tuple(sorted(p, reverse=True))
        if key not in seen:
            seen.add(key); uniq.append(list(key))
    worst = Fr(0); wp = None
    for p in uniq:
        s, B = carrier_sum(p, LEVELS)
        if B <= 1:
            continue
        r = s / (B - 1)
        if r > worst:
            worst, wp = r, p
    good = worst <= CONST
    overall_ok &= good
    print(f"   {tag:7s}: {len(uniq):5d} profiles, worst ratio = {float(worst):.9f}"
          f"  (CONST = {float(CONST):.9f})  {'OK' if good else 'VIOLATION'}")
    print(f"            worst profile: {[str(x) for x in wp]}")
    sys.stdout.flush()
check("no hostile level profile exceeds the proved pointwise constant", overall_ok)

# ----------------------------------------------------------------------------
# 9. Randomized DIRECT test of Lemma 3 and Lemma 4 on synthetic atom systems.
#    Builds real per-prime cumulative weights alpha_{p,j} (sum_j <= 1), the real
#    S_0 (atoms p^j <= m/Q), the real q_p(t), the real retention rule (5) tested
#    by exact integer comparison q^den <= m^num, the real b_p, B, carriers, and
#    checks:  S_0(k) <= (5/4)B(k) + 47/16 ;  (7) 1<s_C<=1+theta_C<=2 ;
#    (8) P_C^3 <= m^2 ;  P_C | k ;  k/P_C >= 210 ;  nu_C >= 210 ;
#    every carrier modulus q^3 <= m.
# ----------------------------------------------------------------------------
print()
print("=" * 78)
print("9. Randomized direct test of Lemmas 3-4 on synthetic atom systems")
print("=" * 78)
PRIMES = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113]

def D_retainable(m):
    out = [Fr(1)]
    for h in range(3, 60):
        stop = True
        for jj in range(4, 8):
            t = Fr(jj, 2 ** h)
            if t > Fr(1, 2):
                out.append(t); stop = False
            elif 2 ** (9 * 2 ** h) <= m ** (4 * jj):     # 2 <= m^{4t/9}
                out.append(t); stop = False
        if stop:
            break
    return sorted(set(out), reverse=True)

def eta_ok(q, t, m):
    """exact test of the retention rule (5):  q <= m^{eta(t)}"""
    if t > Fr(1, 2):
        return q ** 3 <= m
    return q ** (9 * t.denominator) <= m ** (4 * t.numerator)

def trial(seed, m, nk):
    rnd = random.Random(seed)
    LEV = D_retainable(m)
    cum = {}
    for p in PRIMES:
        js = []; pj = p
        while pj * Q <= m:
            js.append(pj); pj *= p
        if not js:
            continue
        tot = Fr(0); rows = []
        for idx, pj in enumerate(js):
            a = Fr(rnd.choice([8,8,7,6,5,4,3,2]), 8) if idx == 0 else Fr(rnd.randint(0,4), 8)
            if tot + a > 1:
                a = 1 - tot
            tot += a; rows.append((pj, tot))
            if tot == 1:
                break
        cum[p] = rows
    qmap = {}
    for p, rows in cum.items():
        for t in LEV:
            q = None
            for pj, cc in rows:
                if cc >= t:
                    q = pj; break
            if q is not None and eta_ok(q, t, m):
                qmap[(p, t)] = q
    def S0p(p, k):
        best = Fr(0)
        for pj, cc in cum.get(p, ()):
            if k % pj == 0:
                best = cc
        return best
    def bpk(p, k):
        best = Fr(0)
        for t in LEV:
            q = qmap.get((p, t))
            if q is not None and k % q == 0 and t > best:
                best = t
        return best
    viol = []; hot = 0
    for _ in range(nk):
        k = 1
        for p in rnd.sample(PRIMES, rnd.randint(6, 14)):
            e = rnd.randint(1, 4)
            while e > 0 and k * p ** e > m:
                e -= 1
            if e > 0:
                k *= p ** e
        if k > m:
            continue
        S0 = sum(S0p(p, k) for p in cum)
        B  = sum(bpk(p, k) for p in cum)
        if S0 > rho * B + D0:
            viol.append(("Lemma 3 pointwise", k, S0, B))
        if B > T:
            hot += 1
            lv = sorted(((bpk(p, k), -p) for p in cum if bpk(p, k) > 0), reverse=True)
            mass = Fr(0); C = []
            for t, negp in lv:
                C.append((-negp, t)); mass += t
                if mass > 1:
                    break
            if mass <= 1:
                viol.append(("hot point with total mass <= 1", k, B)); continue
            theta = C[-1][1]; s = mass
            P = 1
            for p, t in C:
                P *= qmap[(p, t)]
                if qmap[(p, t)] ** 3 > m:
                    viol.append(("carrier modulus > m^{1/3}", p, t))
            if not (1 < s <= 1 + theta <= 2):
                viol.append(("(7)", k, s, theta))
            if P ** 3 > m ** 2:
                viol.append(("(8) P_C > m^{2/3}", k, P))
            if k % P:
                viol.append(("P_C does not divide k", k, P))
            else:
                if k // P < 210:
                    viol.append(("cofactor < 210", k, P, k // P))
                if m // P < 210:
                    viol.append(("nu_C < 210", k, P, m // P))
    return viol, hot

allviol = []; tothot = 0
for seed in range(40):
    for m in (10 ** 18, 10 ** 20, 7 * 10 ** 18):
        v, h = trial(seed, m, 120)
        allviol += v; tothot += h
print(f"   hot points produced and audited: {tothot}")
for v in allviol[:10]:
    print("   VIOLATION:", v)
check("randomized synthetic atom systems: Lemma 3 pointwise bound never violated",
      not any(v[0].startswith("Lemma 3") for v in allviol))
check("randomized synthetic atom systems: (7),(8), P_C|k, cofactor>=210, nu_C>=210 all hold",
      not allviol, f"{tothot} hot points audited")

print()
print("=" * 78)
print(f"FINAL SUMMARY: {len(OK)} checks passed, {len(BAD)} failed")
for b in BAD:
    print("   FAILED: " + b)
print("=" * 78)
