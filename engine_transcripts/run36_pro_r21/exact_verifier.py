#!/usr/bin/env python3
"""Exact verification for the restricted five-prime hinge results.
Standard-library proof checks: python verifier.py
Long-window/search audits (requires numpy): python verifier.py --full
No floating-point arithmetic is used in any mathematical check.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, combinations_with_replacement, product
from math import factorial, gcd, lcm, prod
import argparse

PRIMES = (2, 3, 5, 7, 11, 13, 17, 19)
P5 = tuple(combinations(range(5), 2))
T5 = tuple(combinations(range(5), 3))
SUB5 = tuple(tuple(i for i in range(5) if mask >> i & 1)
             for mask in range(32))
GRID = {
    6: (108, (((0, 1, 1, 2, 3), 1),)),
    8: (1440, (((0, 1, 1, 2, 5), 4),
               ((0, 1, 1, 3, 4), 3),
               ((0, 1, 2, 3, 3), 1),
               ((0, 1, 2, 3, 4), 4)))
}
T3_ATOMS = ((2, 257), (3, 421), (5, 563), (7, 611),
            (11, 293), (121, 427))
EXPECTED_CERT = ((10, 100), (14, 148), (15, 264), (21, 312),
                 (35, 454), (55, 408), (66, 345), (110, 126),
                 (242, 771), (363, 492), (605, 18))
EXPECTED_CUTS = (0, 9, 42, 109, 151, 157, 199, 266,
                 293, 299, 408, 456, 463, 572, 620, 720)
HR = ((10000, 5349, 1711, 1722),
      (100000, 3995409, 17103, 17115),
      (1000000, 3839019, 171021, 171038))
STRESS = (
    ("reflected", 10000, 40820, 123048, 841864, 845202, 2504340),
    ("CRT-centred", 10000, 45820, 123048, 841864, 842732, 2502102),
    ("sieve-rich", 10000, 5349, 123048, 841864, 843626, 2502018),
    ("reflected", 100000, 27050, 1255602, 8434996, 8438334, 25021431),
    ("CRT-centred", 100000, 77050, 1255602, 8434996, 8435816, 25016892),
    ("sieve-rich", 100000, 3995409, 1255602, 8434996, 8437001, 25021218),
    ("reflected", 1000000, 41810, 12559716, 84360289, 84363627, 250189746),
    ("CRT-centred", 1000000, 541810, 12559716, 84360289, 84362108, 250188414),
    ("sieve-rich", 1000000, 3839019, 12559716, 84360289, 84362090, 250188312),
)

def positive(x):
    return max(x, 0)

def elementary(xs, r):
    return sum(prod(z) for z in combinations(xs, r))

def orbit_count(t, a):
    """Distinct permutations of t that are componentwise <= a."""
    numerator = 1
    for j, threshold in enumerate(reversed(t)):
        numerator *= max(0, sum(v >= threshold for v in a) - j)
    denominator = prod(factorial(c) for c in Counter(t).values())
    assert numerator % denominator == 0
    return numerator // denominator

def verify_base_and_constants():
    for a in product(range(7), repeat=4):
        s = sum(a)
        pair_sum = sum(positive(a[i] + a[j] - 6)
                       for i, j in combinations(range(4), 2))
        assert 3 * positive(s - 12) <= pair_sum <= 3 * positive(s - 6)
    levels = tuple(combinations_with_replacement(range(7), 2))
    for (a0, a1), (b0, b1) in product(levels, repeat=2):
        beta = (positive(a1+b1-6) - positive(a0+b1-6)
                - positive(a1+b0-6) + positive(a0+b0-6))
        assert beta >= 0
    assert 2*elementary(tuple(F(1,q) for q in (2,3,5,7)), 2) == F(101,105)
    assert 3*elementary(tuple(F(1,q) for q in (3,4,5,7)), 2) == F(131,140)
    assert 4*elementary(tuple(F(1,q) for q in (4,5,6,7)), 2) == F(179,210)
    assert max(F(101,105), F(131,140), F(179,210), F(4,5)) < 1
    # (18-sqrt(30))/7 > 1, since sqrt(30) < 11.
    assert 30 < 11**2
    print("base grid:", 7**4, "mixed-difference checks:", len(levels)**2)

def boolean_minimals(qs, Q):
    r = len(qs)
    feasible = {}
    for mask in range(1 << r):
        values = tuple(qs[i] for i in range(r) if mask >> i & 1)
        feasible[mask] = bool(values) and prod(values)//max(values) >= Q
    return tuple(mask for mask in feasible if feasible[mask]
                 and not any(feasible[mask ^ (1 << i)]
                             for i in range(r) if mask >> i & 1))

def boolean_kraft(qs, Q):
    return sum(F(Q, prod(qs[i] for i in range(len(qs))
                         if mask >> i & 1))
               for mask in boolean_minimals(qs, Q))

def verify_boolean_kraft():
    checked = 0
    largest = (F(0), None)
    for qs in combinations(range(2, 31), 4):
        if any(gcd(a,b) != 1 for a,b in combinations(qs,2)):
            continue
        a,b,c,d = qs
        for Q in sorted({a,b,c,a*b,a*c,b*c,a*b*c}):
            value = boolean_kraft(qs,Q)
            assert value <= 1
            checked += 1
            if value > largest[0]:
                largest = (value, (qs,Q))
    assert checked == 17738
    assert largest == (F(101,105), ((2,3,5,7),2))
    assert boolean_kraft((2,3,5,7,11),2) == F(194,165)
    print("Boolean audit:", checked, largest)

def verify_grid_certificates():
    for q,(scale,terms) in GRID.items():
        histogram = {}
        for a in combinations_with_replacement(range(q+1),5):
            A = sum(a)
            P = sum(positive(a[i]+a[j]-q) for i,j in P5)
            G = (scale//(3*q))*P
            G += sum(c*orbit_count(t,a) for t,c in terms)
            lower = G-(scale//q)*positive(A-2*q)
            upper = (scale//q)*positive(A-q)-G
            assert lower >= 0 and upper >= 0, (q,a,lower,upper)
            row = histogram.setdefault(A,[0,10**9,10**9])
            row[0] += 1
            row[1] = min(row[1],lower)
            row[2] = min(row[2],upper)
        count = sum(row[0] for row in histogram.values())
        assert count == {6:462,8:1287}[q]
        assert min(row[1] for row in histogram.values()) == 0
        assert min(row[2] for row in histogram.values()) == 0
        print("grid certificate:", q, scale, count)
        print("sum -> (count, minimum lower slack, minimum upper slack)")
        print(histogram)

def cyclic_certificate(f, lam):
    N = len(f)
    return sum(max(F(0), min(lam/N,
                   min(f[i]-lam*F((r+i)%N,N) for i in range(N))))
               for r in range(N))

def verify_cyclic_certificate():
    count = 0
    for N,q in ((2,4),(3,4),(4,4),(5,4),(6,2),(7,2),(8,2)):
        lam = F(2,N-1)
        for a in product(range(q+1),repeat=N):
            f = tuple(lam*F(v,q) for v in a)
            G = cyclic_certificate(f,lam)
            assert positive(sum(f)-2) <= G <= positive(sum(f)-1)
            count += 1
    assert count == 13377
    assert cyclic_certificate((F(1,2),)*5,F(1,2)) == F(1,2)
    print("cyclic functional-box audit:", count)

def verify_rejected_candidates():
    def third_difference(base, increment):
        return sum((-1)**(3-k)*factorial(3)//(factorial(k)*factorial(3-k))
                   *positive(base+k*increment-1) for k in range(4))
    assert third_difference(F(1,2),F(1,2)) == -F(1,2)
    assert third_difference(F(0),F(1)) == -1
    def h(v):
        return sum(positive(min(v[i],F(1,3)) -
                   max(F(0),*(1-2*v[j] for j in range(3) if j != i)))
                   for i in range(3))
    f = (F(1,3),)*2+(F(2,3),)*3
    G = sum(positive(f[i]+f[j]-1) for i,j in P5)/3
    G += sum(h(tuple(f[i] for i in T)) for T in T5)/20
    assert G == F(29,60) < positive(sum(f)-2) == F(2,3)
    f = (F(1,6),)*2+(F(5,6),)*3
    capped = tuple(min(z,F(1,2)) for z in f)
    CDF = sum((-1)**len(T)*positive(1-sum(capped[i] for i in T))**4
              for T in SUB5)
    G = sum(positive(f[i]+f[j]-1) for i,j in P5)/3 + F(8,11)*CDF
    assert G == F(670,891) < positive(sum(f)-2) == F(5,6)
    assert G-F(5,6) == -F(145,1782)
    print("rejected-candidate witnesses: verified exactly")

def elimination_certificate(qs, weights, p, levels, denominator):
    assert len(qs) == len(weights) == 4
    assert all(gcd(p,q) == 1 for q in qs)
    assert all(gcd(a,b) == 1 for a,b in combinations(qs,2))
    assert all(0 <= w <= denominator for w in weights)
    subsets = tuple((sum(weights[i] for i in range(4) if mask >> i & 1),
                     prod(qs[i] for i in range(4) if mask >> i & 1))
                    for mask in range(16))
    cumulative = []
    total = 0
    for d,a in levels:
        z = d
        while z % p == 0:
            z //= p
        assert z == 1 and a >= 0
        total += a
        cumulative.append((d,total))
    assert total <= denominator
    cuts = {0,denominator} | {a for d,a in cumulative}
    cuts |= {h*denominator-w for h in (1,2) for w,d in subsets
             if 0 <= h*denominator-w <= denominator}
    cuts = tuple(sorted(cuts))
    coefficients = {}
    for i,j in combinations(range(4),2):
        c = positive(weights[i]+weights[j]-denominator)
        if c:
            d = qs[i]*qs[j]
            coefficients[d] = coefficients.get(d,0)+c
    for u,v in zip(cuts,cuts[1:]):
        powers = [d for d,A in cumulative if 2*A > u+v]
        winners = [d for w,d in subsets if 2*w > 2*denominator-u-v]
        if not powers or not winners:
            continue
        d = powers[0]*min(winners)
        coefficients[d] = coefficients.get(d,0)+3*(v-u)
    return 3*denominator,tuple(sorted(coefficients.items())),cuts

def verify_explicit_certificate():
    den,coeff,cuts = elimination_certificate(
        (2,3,5,7),(257,421,563,611),11,((11,293),(121,427)),720)
    assert den == 2160 and coeff == EXPECTED_CERT and cuts == EXPECTED_CUTS
    D = lcm(*(d for d,a in T3_ATOMS))
    accumulated_C = accumulated_L = 0
    minimum_pointwise = (0,0)
    for n in range(1,D+1):
        S = sum(a for d,a in T3_ATOMS if n % d == 0)
        C = sum(a for d,a in coeff if n % d == 0)
        L = 3*positive(S-1440)
        R = 3*positive(S-720)
        assert C <= R
        accumulated_C += C
        accumulated_L += L
        assert accumulated_C >= accumulated_L
        if C-L < minimum_pointwise[0]:
            minimum_pointwise = (C-L,n)
    assert D == 25410 and minimum_pointwise == (-677,12705)
    for name,m,x,L,CK,CI,R in STRESS:
        assert sum(a*(m//d) for d,a in coeff) == CK
        assert sum(a*((x+m)//d-x//d) for d,a in coeff) == CI
        assert L <= CK <= CI <= R
    print("explicit certificate:",den,coeff)
    print("cut numerators:",cuts)
    print("full-period certificate audit:",D,minimum_pointwise)

def projection_frontier(Q, primes):
    ladders = []
    for p in primes:
        values = [1]
        while values[-1] < Q:
            values.append(values[-1]*p)
        ladders.append(values)
    r = len(primes)
    states = tuple(product(*(range(len(v)) for v in ladders)))
    divisors = {s:prod(ladders[i][s[i]] for i in range(r)) for s in states}
    feasible = {s:divisors[s]//max(ladders[i][s[i]] for i in range(r)) >= Q
                for s in states}
    frontier = []
    for s in states:
        if not feasible[s]:
            continue
        predecessors = (tuple(s[j]-(j == i) for j in range(r))
                        for i in range(r) if s[i])
        if not any(feasible[t] for t in predecessors):
            frontier.append(divisors[s])
    return sum(F(Q,d) for d in frontier),tuple(frontier)

def audit_open_projection_bound():
    best = (F(0),None)
    for Q in range(2,301):
        value,ds = projection_frontier(Q,PRIMES[:4])
        assert value <= 1
        if value > best[0]:
            best = (value,Q)
    assert best == (F(101,105),2)
    checked = 0
    for primes in combinations(PRIMES[:6],4):
        for Q in range(2,61):
            value,ds = projection_frontier(Q,primes)
            assert value <= 1
            checked += 1
    assert checked == 885
    assert projection_frontier(3,(2,5,7,11))[0] == F(111,220)
    assert projection_frontier(3,(3,5,7,11))[0] == F(236,385)
    assert F(111,220) < F(236,385)
    print("OPEN-bound finite audits only:",299,checked,best)

def audit_tail_grid(q):
    import numpy as np
    D = 210
    values = np.array([[int(k % p == 0) for p in PRIMES[:4]]
                       for k in range(1,D+1)],dtype=np.int64)
    lengths = np.arange(1,D+1)[:,None]
    starts = np.arange(D)[None,:]
    checked = 0
    for weights in product(range(q+1),repeat=4):
        S = values @ np.array(weights,dtype=np.int64)
        for t in range(1,q+1):
            left = (S > 2*q-t).astype(np.int64)
            right = (S > q-t).astype(np.int64)
            pref = np.concatenate(([0],np.cumsum(np.tile(right,2))))
            windows = pref[starts+lengths]-pref[starts]
            assert np.all(np.cumsum(left) <= windows.min(axis=1))
            checked += 1
    assert checked == q*(q+1)**4
    print("tail grid:",q,checked,"window instances:",checked*D*D)

def period_values(atoms):
    import numpy as np
    D = lcm(*(d for d,a in atoms))
    assert 2*D*sum(a for d,a in atoms) < 2**63
    n = np.arange(1,D+1,dtype=np.int64)
    S = np.zeros(D,dtype=np.int64)
    for d,a in atoms:
        S += (n % d == 0)*a
    return D,S

def period_search(atoms,denominator,all_lengths=False):
    import numpy as np
    D,S = period_values(atoms)
    LP = np.concatenate(([0],np.cumsum(np.maximum(S-2*denominator,0))))
    RP = np.concatenate(([0],np.cumsum(np.tile(
        np.maximum(S-denominator,0),2))))
    lengths = (range(1,D+1) if all_lengths else
               sorted({D} | {m for m in (66,100,1000,10000,100000,1000000)
                             if m <= D}))
    H = sum(F(a,denominator*d) for d,a in atoms)
    assert H < 1
    total = eligible = 0
    records = []
    for m in lengths:
        windows = RP[m:m+D]-RP[:D]
        lhs = int(LP[m])
        rhs = int(windows.min())
        x = int(windows.argmin())
        assert lhs <= rhs,(atoms,denominator,m,x,lhs,rhs)
        total += D
        mu = F(int(S[:m].sum()),m*denominator)
        assert mu <= H
        if (m >= 66 and 6*max(d for d,a in atoms) <= m and
                lhs > 0 and mu-H*H/6 < 1):
            eligible += D
        if not all_lengths or m in (66,100,1000,D):
            records.append((m,lhs,rhs,x))
    return D,total,eligible,H,tuple(records)

def audit_period_search():
    total = eligible = 0
    for N in (5,6,7,8):
        den = factorial(N)
        for kind in (0,1):
            weights = (tuple(den-den//(i+2) for i in range(N)) if kind == 0
                       else tuple(den*(i+2)//(N+2) for i in range(N)))
            result = period_search(tuple(zip(PRIMES[:N],weights)),den,N == 5)
            total += result[1]
            eligible += result[2]
            print("search:",N,kind,den,weights,result)
    atoms = tuple(z for p,a in zip(PRIMES[:5],(180,240,360,480,540))
                  for z in ((p,a),(p*p,720-a)))
    result = period_search(atoms,720)
    total += result[1]
    eligible += result[2]
    assert total == 190246980 and eligible == 127514310
    print("multi-level search:",atoms,result)
    print("search totals:",total,eligible)

def direct_hinges(atoms,denominator,m,x):
    import numpy as np
    n = np.arange(1,m+1,dtype=np.int64)
    left = np.zeros(m,dtype=np.int64)
    right = np.zeros(m,dtype=np.int64)
    for d,a in atoms:
        left += (n % d == 0)*a
        right += ((n+x%d) % d == 0)*a
    return (int(np.maximum(left-2*denominator,0).sum()),
            int(np.maximum(right-denominator,0).sum()))

def audit_special_windows():
    import numpy as np
    D = prod(PRIMES)
    n = np.arange(1,D+1,dtype=np.int64)
    free = np.ones(D,dtype=np.int64)
    for p in PRIMES:
        free[n % p == 0] = 0
    pref = np.concatenate(([0],np.cumsum(np.tile(free,2))))
    for m,x,baseline,maximum in HR:
        windows = pref[m:m+D]-pref[:D]
        assert int(windows.argmax()) == x
        assert int(pref[m]) == baseline
        assert int(windows[x]) == maximum > baseline
    del n,free,pref,windows
    for name,m,x,L,CK,CI,R in STRESS:
        lhs,rhs = direct_hinges(T3_ATOMS,720,m,x)
        assert 3*lhs == L and 3*rhs == R
        assert L <= CK <= CI <= R
    cluster = (101,103,107,109,113,127,131,137,139)
    assert all(all(p % a for a in range(2,p) if a*a <= p) for p in cluster)
    assert all(101 <= p and p*p < 2*101**2 for p in cluster)
    m = cluster[-2]*cluster[-1]
    x = prod(cluster)-m//2
    assert m == 19043 and x == 4343678784233757066
    assert direct_hinges(tuple((p,1) for p in cluster),1,m,x) == (0,8)
    print("sieve-rich windows:",HR)
    print("certificate stress chains:",STRESS)
    print("prime-cluster witness:",m,x,0,8)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--full",action="store_true")
    args = parser.parse_args()
    verify_base_and_constants()
    verify_boolean_kraft()
    verify_grid_certificates()
    verify_cyclic_certificate()
    verify_rejected_candidates()
    verify_explicit_certificate()
    if args.full:
        audit_open_projection_bound()
        audit_tail_grid(3)
        audit_tail_grid(6)
        audit_period_search()
        audit_special_windows()
    print("All requested exact checks passed.")

if __name__ == "__main__":
    main()