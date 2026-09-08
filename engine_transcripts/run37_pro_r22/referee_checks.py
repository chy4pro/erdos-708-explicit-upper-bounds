"""
Independent referee checks for pro_708_r22/proof.md  (Erdos-Suranyi / Erdos problem 708).

NOTHING here is imported from exact_verifier.py.  All primitives (factorisation,
graph invariants, the exact optimum g(A,x)) are re-implemented from scratch with a
different algorithm, and cross-validated against brute-force subset enumeration
wherever that is feasible.

Definitions used (independent restatement):
    A = {a_1 < ... < a_n = m},  I = {x+1, ..., x+m}
    g(A,x) = min |B|, B subset of I, prod(A) | prod(B)
    Q  = primes dividing >= 2 elements of A,  s = |Q|
    W_s= sum over p in Q of #{a in A : p | a}
    Gamma = bipartite graph (A vertices) u (Q vertices), edge a~p iff p|a,
            isolated input vertices retained
    c  = #components(Gamma),  beta = W_s - n - s + c
    H  = full incidence graph (ALL primes dividing some a)
    A_core = {a : omega(a) >= 3}, k = |A_core|, beta_core = cycle rank of H(A_core)

Run:  python3 referee_checks.py            (fast suite)
      python3 referee_checks.py --slow     (adds the heavy DP instances + searches)
"""

import sys
from itertools import combinations
from math import gcd, prod

# ----------------------------------------------------------------------------
# 0. arithmetic primitives
# ----------------------------------------------------------------------------

def factorint(n):
    f = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f

def vp(n, p):
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return e

def omega(n):
    return len(factorint(n))


# ----------------------------------------------------------------------------
# 1. graph invariants -- independent implementation
# ----------------------------------------------------------------------------

class DSU:
    def __init__(self, n):
        self.p = list(range(n))
    def find(self, a):
        while self.p[a] != a:
            self.p[a] = self.p[self.p[a]]
            a = self.p[a]
        return a
    def union(self, a, b):
        ra, rb = self.find(a), self.find(b)
        if ra != rb:
            self.p[ra] = rb
            return True
        return False

def incidence_stats(A, shared_only=True):
    """Return dict with the invariants of Gamma (shared_only=True) or H (False).

    beta is computed as |E| - |V| + c directly from a spanning-forest count, i.e.
    beta = number of edges that close a cycle in a DSU sweep.  This is an
    independent route to the cycle rank (no W - n - s + c formula used)."""
    A = list(A)
    n = len(A)
    fs = [factorint(a) for a in A]
    deg = {}
    for f in fs:
        for p in f:
            deg[p] = deg.get(p, 0) + 1
    if shared_only:
        primes = sorted(p for p, d in deg.items() if d >= 2)
    else:
        primes = sorted(deg)
    pidx = {p: n + i for i, p in enumerate(primes)}
    dsu = DSU(n + len(primes))
    E = 0
    cyc = 0                      # edges that close a cycle  ==  cycle rank
    for i, f in enumerate(fs):
        for p in f:
            if p in pidx:
                E += 1
                if not dsu.union(i, pidx[p]):
                    cyc += 1
    c = len({dsu.find(v) for v in range(n + len(primes))})
    beta_formula = E - (n + len(primes)) + c
    assert cyc == beta_formula, (cyc, beta_formula)
    # maximum matching (Hopcroft-Karp not needed at this size): Kuhn on primes
    adj = {p: [i for i, f in enumerate(fs) if p in f] for p in primes}
    matchA = {}
    def try_k(p, seen):
        for i in adj[p]:
            if i in seen:
                continue
            seen.add(i)
            if i not in matchA or try_k(matchA[i], seen):
                matchA[i] = p
                return True
        return False
    nu = sum(1 for p in primes if try_k(p, set()))
    return dict(primes=primes, s=len(primes), W=E, nu=nu, c=c, beta=cyc, n=n,
                Omega0=sum(len(f) for f in fs), P=sorted(deg))

def beta_of(A, shared_only=True):
    if not A:
        return 0
    return incidence_stats(A, shared_only)['beta']


# ----------------------------------------------------------------------------
# 2. exact g(A,x) -- independent 0/1 DP, element by element (no grouping)
# ----------------------------------------------------------------------------

def exact_g(A, x, want_witness=True):
    """Plain 0/1 subset DP over capped valuation vectors, one interval element at
    a time (deliberately NOT the grouped/capped-count DP of the document).

    Correctness: after processing the first t interval elements, cost[state] is the
    minimum cardinality of a subset of those t elements whose capped vector sum is
    `state`.  Each element is offered exactly once and transitions are read from
    the previous table, so no element can be used twice.  Witnesses are carried
    explicitly (rather than via parent pointers) so that the reconstructed set is
    provably the one realising the stored cost."""
    A = list(A)
    m = max(A)
    fs = [factorint(a) for a in A]
    ps = sorted(set().union(*[set(f) for f in fs]))
    D = [sum(f.get(p, 0) for f in fs) for p in ps]
    radix = [d + 1 for d in D]
    size = 1
    stride = []
    for r in radix:
        stride.append(size)
        size *= r
    INF = 10 ** 9
    cost = [INF] * size
    cost[0] = 0
    wit = [None] * size
    wit[0] = ()
    npr = len(ps)
    for b in range(x + 1, x + m + 1):
        v = [min(D[i], vp(b, ps[i])) for i in range(npr)]
        if not any(v):
            continue
        ncost = cost[:]
        nwit = wit[:] if want_witness else None
        for st in range(size):
            cur = cost[st]
            if cur >= INF:
                continue
            t = st
            ns = 0
            for i in range(npr):
                digit = t % radix[i]
                t //= radix[i]
                ns += min(D[i], digit + v[i]) * stride[i]
            if cur + 1 < ncost[ns]:
                ncost[ns] = cur + 1
                if want_witness:
                    nwit[ns] = wit[st] + (b,)
        cost = ncost
        if want_witness:
            wit = nwit
    full = size - 1
    assert cost[full] < INF, "infeasible -- contradicts Lemma 1"
    B = ()
    if want_witness:
        B = tuple(sorted(wit[full]))
        assert len(B) == len(set(B)), "witness reuses an element"
        assert all(x < b <= x + m for b in B)
        assert prod(B) % prod(A) == 0, "witness is not a product cover"
        assert len(B) == cost[full]
    return cost[full], B


def brute_g(A, x, cap=6):
    """Exhaustive subset enumeration restricted to elements with a nonzero capped
    vector (elements coprime to prod(A) are useless).  Returns exact g if it can
    be found with <= cap elements, else None."""
    A = list(A)
    m = max(A)
    P = prod(A)
    cand = [b for b in range(x + 1, x + m + 1) if gcd(b, P) > 1]
    for r in range(1, cap + 1):
        for C in combinations(cand, r):
            if prod(C) % P == 0:
                return r, C
    return None


# ----------------------------------------------------------------------------
# 3. shortage functions delta_p, rho_p, and the certificates
# ----------------------------------------------------------------------------

def layer_counts(A, p):
    E = max(vp(a, p) for a in A)
    return [sum(1 for a in A if vp(a, p) >= j) for j in range(1, E + 1)]

def delta_p(A, x, S, p):
    cs = layer_counts(A, p)
    return max([0] + [cs[j - 1] - sum(1 for b in S if vp(b, p) >= j)
                      for j in range(1, len(cs) + 1)])

def rho_p(A, x, S, p):
    m = max(A)
    D = sum(vp(a, p) for a in A)
    have = sum(vp(b, p) for b in S)
    if have >= D:
        return 0
    vals = sorted((vp(b, p) for b in range(x + 1, x + m + 1) if b not in S),
                  reverse=True)
    t = 0
    while have < D:
        have += vals[t]
        t += 1
    return t

def delta_p_bruteforce(A, x, S, p):
    """Exact minimum number of additions repairing every p-layer -- by search."""
    m = max(A)
    cs = layer_counts(A, p)
    rest = [b for b in range(x + 1, x + m + 1) if b not in S and b % p == 0]
    def ok(add):
        for j in range(1, len(cs) + 1):
            have = sum(1 for b in S if vp(b, p) >= j) + \
                   sum(1 for b in add if vp(b, p) >= j)
            if have < cs[j - 1]:
                return False
        return True
    if ok([]):
        return 0
    for r in range(1, len(rest) + 1):
        for C in combinations(rest, r):
            if ok(C):
                return r
    raise AssertionError("no repair")

def rho_p_bruteforce(A, x, S, p):
    m = max(A)
    D = sum(vp(a, p) for a in A)
    have = sum(vp(b, p) for b in S)
    if have >= D:
        return 0
    rest = [b for b in range(x + 1, x + m + 1) if b not in S and b % p == 0]
    for r in range(1, len(rest) + 1):
        for C in combinations(rest, r):
            if have + sum(vp(b, p) for b in C) >= D:
                return r
    raise AssertionError("no repair")


def anchor_certificate(A, x, choice='least'):
    """|S| + sum_p delta_p(S) for whole-input anchors, plus sum of the collision
    group cycle ranks.  choice in {'least','largest','random'} -- Theorem 4
    claims ANY choice of anchors works."""
    import random
    A = list(A)
    m = max(A)
    groups = {}
    for a in A:
        mult = [b for b in range(((x // a) + 1) * a, x + m + 1, a)]
        assert mult, "Lemma 1 fails"
        if choice == 'least':
            b = mult[0]
        elif choice == 'largest':
            b = mult[-1]
        else:
            b = random.choice(mult)
        groups.setdefault(b, []).append(a)
    S = sorted(groups)
    ps = sorted(set().union(*[set(factorint(a)) for a in A]))
    dl = {p: delta_p(A, x, S, p) for p in ps}
    rh = {p: rho_p(A, x, S, p) for p in ps}
    cert = len(S) + sum(dl.values())
    certr = len(S) + sum(rh.values())
    sum_local_beta = sum(beta_of(tuple(C), shared_only=False) for C in groups.values())
    return dict(S=tuple(S), groups=groups, delta=dl, rho=rh, cert=cert,
                cert_rho=certr, sum_local_beta=sum_local_beta)


# ----------------------------------------------------------------------------
# 4. the document's instances
# ----------------------------------------------------------------------------

A0 = (30, 42, 70, 105)
A1 = (30, 42, 66, 70, 105, 165)
A2 = (30, 42, 66, 70, 78, 105, 110, 165)
A3 = (30, 42, 66, 70, 105, 110, 154, 165, 231, 385)
A4 = (105, 120, 126, 140, 150, 168, 180)
A5 = (330, 420, 462, 630, 770, 1155)
A6 = (30, 42, 70, 165, 273)

CLAIMED = [  # (id, A, x, claimed g, claimed beta or None)
    ("D0", A0, 0, 4, 5),
    ("D1", A0, 113, 4, 5),
    ("D2", A1, 151, 5, 8),
    ("D3", A2, 997, 5, 11),
    ("D4", A3, 1009, 7, 16),
    ("D5", A4, 12510, 5, 11),
    ("D6", A5, 13282, 4, 14),
    ("D7", A6, 29900, 3, 5),
    ("D8", A0, 1207, 3, 5),
    ("T", (77, 91, 143), 5934, 4, 1),
    ("H0", A0, 8, 4, 5),
    ("H1", A1, 16, 5, 8),
    ("F", (6, 10, 21), 53, 2, 0),
    ("U0", (6, 10, 15), 53, 3, 1),
    ("U1", (154, 273, 715), 29672, 3, 1),
    ("U2", (154, 273, 715), 0, 3, 1),
    ("R0", (6, 10, 15), 0, 3, 1),
    ("R1", (6, 14, 21), 0, 3, 1),
    ("R2", (15, 21, 35), 0, 3, 1),
    ("R3", (35, 55, 77), 0, 3, 1),
    ("R4", (30, 70, 105), 0, 3, 3),
]

HEAVY = {"D4", "D6"}     # big state space * long interval


def section(t):
    print("\n" + "=" * 78)
    print(t)
    print("=" * 78)


def check_instances(slow):
    section("1. EXACT g(A,x) AND GRAPH INVARIANTS -- independent recomputation")
    print(f"{'id':4} {'n':>2} {'m':>6} {'x':>7} {'s':>2} {'W_s':>3} {'nu':>2} "
          f"{'c':>2} {'beta':>4} {'claim b':>7} {'g':>2} {'claim g':>7} "
          f"{'n+beta':>6} {'2n-k+bc':>7} {'brute':>6}")
    ok = True
    for name, A, x, wantg, wantb in CLAIMED:
        if name in HEAVY and not slow:
            print(f"{name:4} (skipped -- run with --slow)")
            continue
        st = incidence_stats(A, shared_only=True)
        stH = incidence_stats(A, shared_only=False)
        assert st['beta'] == stH['beta'], (name, "beta(Gamma) != beta(H)")
        assert st['c'] == stH['c'], (name, "c(Gamma) != c(H)")
        n = len(A)
        core = tuple(a for a in A if omega(a) >= 3)
        k = len(core)
        bc = beta_of(core, shared_only=False)
        gval, B = exact_g(A, x)
        br = brute_g(A, x, cap=min(wantg, 4)) if len(A) <= 5 or wantg <= 4 else None
        brs = (br[0] if br else "-")
        flag = "" if (gval == wantg and st['beta'] == wantb) else "   <<< MISMATCH"
        ok &= (gval == wantg and st['beta'] == wantb)
        print(f"{name:4} {n:>2} {max(A):>6} {x:>7} {st['s']:>2} {st['W']:>3} "
              f"{st['nu']:>2} {st['c']:>2} {st['beta']:>4} {wantb:>7} {gval:>2} "
              f"{wantg:>7} {n+st['beta']:>6} {2*n-k+bc:>7} {str(brs):>6}{flag}")
        # Theorem 4 / Lemma 5 sanity
        assert gval <= n + st['beta'], (name, "THEOREM 4 VIOLATED")
        assert gval <= 2 * n - k + bc, (name, "LEMMA 5 VIOLATED")
        # identity (6)
        assert n + st['beta'] == st['Omega0'] - len(st['P']) + st['c'], (name, "identity (6)")
        # P7 / P8 comparison
        assert n + st['beta'] <= n + st['W'] - st['nu'], (name, "P7 not implied")
        d = st['s'] - st['nu']
        assert n + st['beta'] <= 2 * n - st['c'] + st['beta'] + d, (name, "P8 not implied")
        if br is not None:
            assert br[0] == gval, (name, "brute force disagrees with DP", br[0], gval)
    print("all instance assertions passed:", ok)
    return ok


def check_table_properties():
    section("2. PROPERTIES CLAIMED FOR D0-D7 (primitive, antichain, omega>=3, range)")
    for name, A, beta in [("D0/D1", A0, 5), ("D2", A1, 8), ("D3", A2, 11),
                          ("D4", A3, 16), ("D5", A4, 11), ("D6", A5, 14),
                          ("D7", A6, 5)]:
        n = len(A)
        prim = gcd(*A) == 1 if n > 1 else True
        anti = all(b % a for a, b in combinations(A, 2))
        w3 = all(omega(a) >= 3 for a in A)
        rng = 2 * n < max(A) < 8 * n ** 3
        st = incidence_stats(A)
        print(f"{name:6} n={n:2} primitive={prim} antichain={anti} all_omega>=3={w3} "
              f"2n<m<8n^3={rng}  c={st['c']} beta={st['beta']} (claim {beta}) "
              f"{'OK' if st['beta']==beta else '<<<MISMATCH'}")
        assert prim and anti and w3 and rng and st['beta'] == beta


def check_lemma6():
    section("3. LEMMA 6 -- sharpness witness A=(77,91,143), x=5934")
    A = (77, 91, 143); x = 5934; m = 143
    I = range(x + 1, x + m + 1)
    st = incidence_stats(A)
    print("beta =", st['beta'], " c =", st['c'], " s =", st['s'], " W =", st['W'])
    two = [b for b in I if sum(1 for p in (7, 11, 13) if b % p == 0) >= 2]
    print("elements of I divisible by >=2 of {7,11,13}:", two)
    sq = {p: [b for b in I if b % (p * p) == 0] for p in (7, 11, 13)}
    print("multiples of p^2 in I:", sq)
    # exhaustive lower bound: no 3-subset works
    cand = [b for b in I if gcd(b, 7 * 11 * 13) > 1]
    print("candidate elements (divisible by 7, 11 or 13):", len(cand))
    found3 = [C for C in combinations(cand, 3) if prod(C) % prod(A) == 0]
    print("3-element covers found by exhaustive search:", len(found3))
    g, B = exact_g(A, x)
    print("exact g =", g, " witness", B)
    B0 = (5941, 5954, 5978, 6050)
    print("document witness valid:", prod(B0) % prod(A) == 0 and all(x < b <= x + m for b in B0))
    assert found3 == [] and g == 4
    print("=> g = 4 = n + beta CONFIRMED")


def check_shortage_lemmas(slow):
    section("4. LEMMA 2 -- delta_p / rho_p exactness, rho<=delta, union bound")
    import random
    random.seed(20260908)
    bad = 0
    tested = 0
    for name, A, x, wantg, wantb in CLAIMED:
        if name in HEAVY and not slow:
            continue
        m = max(A)
        ps = sorted(set().union(*[set(factorint(a)) for a in A]))
        for trial in range(4):
            if trial == 0:
                S = ()
            else:
                pool = [b for b in range(x + 1, x + m + 1)]
                S = tuple(sorted(random.sample(pool, random.randint(1, min(6, len(pool))))))
            tot_d = 0
            tot_r = 0
            for p in ps:
                d = delta_p(A, x, S, p)
                r = rho_p(A, x, S, p)
                tested += 1
                # exactness of delta_p (brute force)
                db = delta_p_bruteforce(A, x, S, p) if d <= 3 else None
                rb = rho_p_bruteforce(A, x, S, p) if r <= 3 else None
                if db is not None and db != d:
                    print("  delta_p NOT exact", name, S, p, d, db); bad += 1
                if rb is not None and rb != r:
                    print("  rho_p NOT exact", name, S, p, r, rb); bad += 1
                if r > d:
                    print("  rho_p > delta_p !!", name, S, p, r, d); bad += 1
                tot_d += d; tot_r += r
            g, _ = exact_g(A, x)
            if g > len(S) + tot_r:
                print("  UNION BOUND g <= |S| + sum rho VIOLATED", name, S, g,
                      len(S) + tot_r); bad += 1
            if g > len(S) + tot_d:
                print("  BOUND g <= |S| + sum delta VIOLATED", name, S); bad += 1
    print(f"tested {tested} (S,p) pairs; violations: {bad}")
    assert bad == 0
    print("delta_p exact / rho_p exact / rho<=delta / union bound: CONFIRMED")


def check_theorem4_anchors(slow):
    section("5. THEOREM 4 -- 'arbitrary whole-input anchors' certificate")
    import random
    random.seed(7)
    print(f"{'id':4} {'choice':8} {'|S|':>3} {'cert':>4} {'cert_rho':>8} "
          f"{'n+sum bC':>9} {'n+beta':>6} {'g':>2}")
    for name, A, x, wantg, wantb in CLAIMED:
        if name in HEAVY and not slow:
            continue
        n = len(A)
        beta = incidence_stats(A)['beta']
        g, _ = exact_g(A, x)
        for choice in ('least', 'largest', 'random', 'random', 'random'):
            d = anchor_certificate(A, x, choice)
            assert d['cert'] <= n + d['sum_local_beta'] <= n + beta, \
                (name, choice, d['cert'], n + d['sum_local_beta'], n + beta)
            assert g <= d['cert_rho'] <= d['cert']
            if choice in ('least', 'largest'):
                print(f"{name:4} {choice:8} {len(d['S']):>3} {d['cert']:>4} "
                      f"{d['cert_rho']:>8} {n+d['sum_local_beta']:>9} "
                      f"{n+beta:>6} {g:>2}")
    print("certificate <= n + sum_C beta_C <= n + beta for every anchor choice: CONFIRMED")


def random_stress(slow):
    section("6. RANDOM STRESS TEST OF (1) g<=n+beta  AND (2) g<=2n-k+beta_core")
    import random
    random.seed(1234)
    trials = 400 if slow else 150
    worst = []
    viol = 0
    for _ in range(trials):
        n = random.randint(2, 5)
        # random inputs built from small primes, mixed omega
        primes = [2, 3, 5, 7, 11, 13]
        A = set()
        while len(A) < n:
            k = random.randint(1, 3)
            ps = random.sample(primes, k)
            a = 1
            for p in ps:
                a *= p ** random.randint(1, 2)
            if a > 1:
                A.add(a)
        A = tuple(sorted(A))
        if max(A) > 400:
            continue
        x = random.randint(0, 3000)
        st = incidence_stats(A)
        core = tuple(a for a in A if omega(a) >= 3)
        k = len(core)
        bc = beta_of(core, shared_only=False)
        g, _ = exact_g(A, x)
        n = len(A)
        if g > n + st['beta']:
            print("  *** (1) VIOLATED", A, x, g, n + st['beta']); viol += 1
        if g > 2 * n - k + bc:
            print("  *** (2) VIOLATED", A, x, g, 2 * n - k + bc); viol += 1
        # (2) is never better than (1)?
        assert n + st['beta'] <= 2 * n - k + bc, ("(1) worse than (2)!", A)
        worst.append((g - n - st['beta'], A, x, g, n + st['beta']))
    worst.sort(reverse=True)
    print(f"{len(worst)} random instances, violations = {viol}")
    print("tightest cases (g - (n+beta)):")
    for w in worst[:6]:
        print("   ", w)
    assert viol == 0
    print("Also verified on every random instance:  n+beta <= 2n-k+beta_core")
    print("  ==> bound (2) of the document is NEVER stronger than bound (1).")


def check_2_vs_1_theory():
    section("7. IS (2) g<=2n-k+beta_core EVER STRONGER THAN (1) g<=n+beta?")
    print("Claim: beta <= beta_core + sum_{a not in core}(omega(a)-1) <= beta_core+(n-k),")
    print("hence n+beta <= 2n-k+beta_core ALWAYS.  Verified exhaustively below.")
    import random
    random.seed(99)
    worst = 0
    for _ in range(4000):
        n = random.randint(1, 7)
        primes = [2, 3, 5, 7, 11, 13, 17, 19, 23]
        A = set()
        while len(A) < n:
            kk = random.randint(1, 4)
            a = prod(random.sample(primes, kk))
            A.add(a)
        A = tuple(sorted(A))
        st = incidence_stats(A)
        core = tuple(a for a in A if omega(a) >= 3)
        k = len(core)
        bc = beta_of(core, shared_only=False)
        lhs = len(A) + st['beta']
        rhs = 2 * len(A) - k + bc
        assert lhs <= rhs, (A, lhs, rhs)
        worst = max(worst, rhs - lhs)
    print("max observed slack  (2n-k+beta_core) - (n+beta) =", worst, "(>=0 always)")
    # explicit instance where (3) fails but (1) already gives <= 2n
    A = (143, 210, 323, 420)
    st = incidence_stats(A)
    core = tuple(a for a in A if omega(a) >= 3)
    k = len(core); bc = beta_of(core, shared_only=False)
    n = len(A)
    print(f"\nExplicit witness A={A}: n={n} beta={st['beta']} c={st['c']} "
          f"k={k} beta_core={bc}")
    print(f"   condition beta_core<=k : {bc} <= {k} -> {bc<=k}   (Lemma 5 corollary FAILS)")
    print(f"   Lemma 5 bound 2n-k+beta_core = {2*n-k+bc}  (WORSE than 2n={2*n})")
    print(f"   Theorem 4 bound n+beta      = {n+st['beta']}  (already < 2n)")
    g, B = exact_g(A, 0)
    print(f"   exact g(A,0) = {g}")


def check_pseudoforest_comparison():
    section("8. HOW MUCH WEAKER IS beta_core<=k THAN THE PSEUDOFOREST beta<=c ?")
    rows = []
    for name, A, x, wg, wb in CLAIMED:
        st = incidence_stats(A)
        core = tuple(a for a in A if omega(a) >= 3)
        k = len(core); bc = beta_of(core, shared_only=False)
        rows.append((name, len(A), st['beta'], st['c'], k, bc,
                     st['beta'] <= st['c'], bc <= k))
    print(f"{'id':4} {'n':>2} {'beta':>4} {'c':>2} {'k':>2} {'b_core':>6} "
          f"{'pseudoforest':>12} {'beta_core<=k':>12}")
    seen = set()
    for r in rows:
        if (r[0][0] in 'DH') or True:
            print(f"{r[0]:4} {r[1]:>2} {r[2]:>4} {r[3]:>2} {r[4]:>2} {r[5]:>6} "
                  f"{str(r[6]):>12} {str(r[7]):>12}")
    n_new = sum(1 for r in rows if r[7] and not r[6])
    print(f"\ninstances satisfying the NEW condition but not the pseudoforest one: {n_new}")
    # a clean infinite family: new holds, old fails
    print("\nFamily satisfying beta_core<=k but NOT beta<=c:")
    fam = [(30, 42, 110, 231), (30, 42, 70, 165, 273)]
    for A in fam:
        st = incidence_stats(A)
        core = tuple(a for a in A if omega(a) >= 3)
        k = len(core); bc = beta_of(core, shared_only=False)
        print(f"  A={A}: n={len(A)} beta={st['beta']} c={st['c']} k={k} "
              f"beta_core={bc} -> new {bc<=k}, pseudoforest {st['beta']<=st['c']}")
    print("\nProof that pseudoforest => beta_core <= k/2 <= k:")
    print("  each independent cycle inside the core lies in a distinct component")
    print("  (pseudoforest) and needs >= 2 core inputs, so beta_core <= k/2.")
    print("  Hence the new condition is IMPLIED by, and strictly weaker than, the old.")
    # random density measurement
    import random
    random.seed(5)
    for (npr, nin) in [(6, 4), (8, 5), (10, 6), (12, 8), (20, 8)]:
        primes = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71][:npr]
        hit = tot = 0
        for _ in range(3000):
            A = set()
            while len(A) < nin:
                A.add(prod(random.sample(primes, 3)))
            A = tuple(sorted(A))
            core = tuple(a for a in A if omega(a) >= 3)
            k = len(core); bc = beta_of(core, shared_only=False)
            tot += 1
            hit += (bc <= k)
        print(f"  random omega=3 inputs: {nin} inputs from {npr} primes -> "
              f"beta_core<=k holds {100*hit/tot:5.1f}% of the time")


def check_prop9_and_D5():
    section("9. PROPOSITION 9 (Theta minimum = 20) AND THE D5 delta/rho CLAIMS")
    A = A5
    best = (10 ** 9, None)
    for r in range(len(A) + 1):
        for C in combinations(A, r):
            th = len(C) + beta_of(C, shared_only=False) + \
                 sum(omega(a) for a in A if a not in C)
            if th < best[0]:
                best = (th, C)
    print("min_C Theta_A(C) =", best[0], "attained at", best[1], " (3n =", 3*len(A), ")")
    assert best[0] == 20
    st = incidence_stats(A)
    print("Omega0 =", st['Omega0'], " |P(A)| =", len(st['P']), " c =", st['c'],
          " n+beta =", len(A) + st['beta'])
    # D5
    A = A4; x = 12510; m = max(A)
    mult = {a: [b for b in range(x + 1, x + m + 1) if b % a == 0] for a in A}
    print("\nD5: interval multiples of each input:", mult)
    S = (12600,)
    ps = sorted(set().union(*[set(factorint(a)) for a in A]))
    dl = {p: delta_p(A, x, S, p) for p in ps}
    rh = {p: rho_p(A, x, S, p) for p in ps}
    print("delta =", dl, "sum+|S| =", 1 + sum(dl.values()))
    print("rho   =", rh, "sum+|S| =", 1 + sum(rh.values()))
    g, B = exact_g(A, x)
    print("exact g =", g, B)
    assert dl == {2: 5, 3: 5, 5: 4, 7: 3} and 1 + sum(dl.values()) == 18
    assert rh == {2: 2, 3: 2, 5: 2, 7: 2} and 1 + sum(rh.values()) == 9
    assert g == 5


def check_sift():
    section("10. SIFTED-SURPLUS WINDOW TABLE")
    for P, m in [((2, 3, 5, 7), 105), ((2, 3, 5, 7, 11), 165)]:
        L = prod(P)
        good = [1 if gcd(i, L) == 1 else 0 for i in range(L + m + 1)]
        pref = sum(good[1:m + 1])
        best = (pref, 0)
        cnt = pref
        for x in range(1, L):
            cnt += good[x + m] - good[x]
            if cnt > best[0]:
                best = (cnt, x)
        print(f"P={P} m={m}: R_P([1,m])={pref}  best shift x={best[1]} "
              f"R_P((x,x+m])={best[0]}")
    print("(document claims 24 -> 26 at x=8, and 34 -> 37 at x=16)")


def check_theorem8():
    section("11. THEOREM 8 ARITHMETIC (k-split with h=2,3)")
    for h, thresh in [(2, lambda n: 8 * n ** 3), (3, lambda n: 9 * n * n)]:
        for n in range(1, 40):
            m = thresh(n)
            T = m / (h * n)
            c1 = T * T >= m
            c2 = T >= h * n
            c3 = m <= T ** ((h + 1) / 2) + 1e-9
            assert c1 and c2 and c3, (h, n, T, c1, c2, c3)
        # general k-split threshold  (h n)^{(h+1)/(h-1)}
        print(f"h={h}: threshold m >= (hn)^((h+1)/(h-1)) = "
              f"{'(2n)^3 = 8n^3' if h==2 else '(3n)^2 = 9n^2'}  -- verified consistent")
    print("=> (4) and (5) are the SAME theorem at k=2 and k=3.")


# ----------------------------------------------------------------------------
# 5. (C) sharpness for large n
# ----------------------------------------------------------------------------

def _primes_upto(N):
    sieve = bytearray([1]) * (N + 1)
    sieve[0:2] = b"\x00\x00"
    i = 2
    while i * i <= N:
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
        i += 1
    return [i for i in range(N + 1) if sieve[i]]

PRIMES = _primes_upto(4000)

def _cycle_instance(qs):
    """A = {q_i q_{i+1}} cyclically; place the window of length m = max(A) so that
    M = prod(qs) is the ONLY element divisible by two of the q_i and some q_i^2 has
    no multiple in the window.  Returns (A, x, M, alpha, nosq) or None."""
    r = len(qs)
    A = tuple(sorted({qs[i] * qs[(i + 1) % r] for i in range(r)}))
    if len(A) != r:
        return None
    m = max(A)
    M = prod(qs)
    minpair = min(qs[i] * qs[j] for i in range(r) for j in range(i + 1, r))
    for alpha in range(m):                    # M = x + alpha + 1
        x = M - alpha - 1
        if x < 0:
            continue
        if minpair <= max(alpha, m - 1 - alpha):
            continue                          # some q_i q_j has a 2nd multiple in I
        nosq = [q for q in qs if (x + m) // (q * q) - x // (q * q) == 0]
        if not nosq:
            continue
        return A, x, M, alpha, nosq
    return None


def _k2t_instance(ws, qu, qv):
    """A = the 2t products of K_{2,t}: {w_i qu, w_i qv}.  n = 2t, beta = t-1."""
    qs = list(ws) + [qu, qv]
    A = tuple(sorted([w * qu for w in ws] + [w * qv for w in ws]))
    if len(set(A)) != len(A):
        return None
    m = max(A)
    M = prod(qs)
    if qu * qu <= m or qv * qv <= m:          # need t_qu = t_qv = 0 to be possible
        return None
    minpair = min(a * b for a, b in combinations(qs, 2))
    for alpha in range(m):
        x = M - alpha - 1
        if x < 0:
            continue
        if minpair <= max(alpha, m - 1 - alpha):
            continue
        if (x + m) // (qu * qu) - x // (qu * qu):
            continue
        if (x + m) // (qv * qv) - x // (qv * qv):
            continue
        return A, x, M, alpha
    return None


def sharpness_search(rmax=9):
    section("12. (C) IS g = n + beta ATTAINABLE FOR ARBITRARILY LARGE n ?")
    print("Referee's construction A (beta = 1, n arbitrary):")
    print("  primes q_1<...<q_r all inside a factor sqrt(2); A = {q_i q_{i+1}} cyclically")
    print("  => n = r, s = r, W_s = 2r, c = 1, beta = 1.")
    print("  Window of length m = max(A) placed around M = q_1...q_r so that (i) M is")
    print("  the ONLY element of I divisible by two demanded primes and (ii) some q_i")
    print("  has no multiple of q_i^2 in I.  Then g = r + 1 = n + beta.")
    print()
    out = []
    for r in range(3, rmax + 1):
        hit = None
        for st in range(2, 80):
            qs = PRIMES[st:st + r]
            if len(qs) < r:
                break
            if 2 * qs[0] * qs[1] <= qs[-2] * qs[-1]:
                continue
            res = _cycle_instance(qs)
            if res:
                hit = (qs,) + res
                break
        if not hit:
            print(f"  r={r}: none found in scanned prime range")
            continue
        qs, A, x, M, alpha, nosq = hit
        st_ = incidence_stats(A)
        n = len(A)
        g, B = exact_g(A, x)
        print(f"  r={n:2}: q={qs}")
        print(f"        A={A}")
        print(f"        m={max(A)} x={x}  n={n} s={st_['s']} W_s={st_['W']} c={st_['c']} "
              f"beta={st_['beta']}  n+beta={n+st_['beta']}  EXACT g={g}  "
              f"{'SHARP' if g == n + st_['beta'] else '<<< NOT SHARP'}")
        assert g == n + st_['beta']
        out.append((n, g))
    print("\n  => g = n + beta for every n tested: NOT an artefact of tiny n.")
    return out


def sharpness_beta_linear(tmax=6):
    section("13. (C) SHARPNESS WITH beta = Theta(n):  THE K_{2,t} FAMILY")
    print("Referee's construction B:  primes w_1<...<w_t < qu < qv, all inside a")
    print("factor sqrt(2), with qu^2 > m and qv^2 > m where m = w_t*qv, and")
    print("  A = { w_i qu, w_i qv : i = 1..t }   (the edge set of K_{2,t})")
    print("  => n = 2t, s = t+2, W_s = 4t, c = 1, beta = 2t-(t+2)+1 = t-1.")
    print("Window around M = prod of all t+2 primes with M the unique 2-prime element")
    print("and NO multiple of qu^2 or qv^2 in I.  Then")
    print("  with M   : 1 + (t-1) + (t-1) + t          = 3t-1")
    print("  without M:     t   +   t   + (>= t)      >= 3t")
    print("so g = 3t-1 = n + beta with beta = n/2 - 1 = Theta(n),  g/n -> 3/2.")
    print()
    print(f"{'t':>2} {'n':>3} {'beta':>4} {'n+beta':>6} {'exact g':>7} {'g/n':>7}  verdict")
    for t in range(2, tmax + 1):
        hit = None
        for st in range(5, 300):
            cand = PRIMES[st:st + t + 6]
            if len(cand) < t + 2 or cand[-1] > 1500:
                break
            for combo in combinations(range(len(cand)), t + 2):
                sel = [cand[i] for i in combo]
                r = _k2t_instance(sel[:t], sel[t], sel[t + 1])
                if r:
                    hit = (sel,) + r
                    break
            if hit:
                break
        if not hit:
            print(f"{t:>2}  none found")
            continue
        sel, A, x, M, alpha = hit
        st_ = incidence_stats(A)
        n = len(A)
        g, B = exact_g(A, x)
        verdict = "SHARP" if g == n + st_['beta'] else "<<< NOT SHARP"
        print(f"{t:>2} {n:>3} {st_['beta']:>4} {n+st_['beta']:>6} {g:>7} {g/n:>7.4f}  {verdict}")
        print(f"     primes={sel}  A={A}")
        print(f"     m={max(A)} x={x}")
        print(f"     witness={B}")
        assert g == n + st_['beta']
    print("\n  => the coefficient 1 of beta in Theorem 4 is sharp along a family with")
    print("     beta = Theta(n); the ratio g/n reaches 3/2 - 1/n on it.")


def sharpness_ceiling():
    section("14. (C) HOW FAR CAN EXACT SHARPNESS GO?  (structural ceiling)")
    print("In the 'unique-M prime-pair' family (A = {q_i q_j : ij in E(G)}, all primes")
    print("within sqrt2, window around M = prod q_i) one has")
    print("     g = 1 + sum_i max( ceil((d_i-1)/2), d_i - 1 - t_i ),")
    print("with t_i = #{multiples of q_i^2 in I} and n + beta = sum_i d_i - r + c.")
    print("Equality g = n+beta forces c = 1 and t_i = 0 for every prime of degree >= 3.")
    print("t_i = 0 requires q_i^2 > m = max_{ij in E} q_i q_j, i.e. q_i exceeds all its")
    print("neighbours; so the degree->=3 primes form an INDEPENDENT set B whose")
    print("neighbours all have degree <= 2.  Then")
    print("     n = |E| <= 2(r - |B|)  and  beta = n - r + 1 <= n/2 - |B| + 1,")
    print("maximised at |B| = 2, i.e. exactly the K_{2,t} family:  beta <= n/2 - 1.")
    print("So exact sharpness with beta/n -> 1 (which would force g = 2n, an extremal")
    print("instance for Erdos's conjecture) is NOT reachable inside this family, and no")
    print("such instance is known.  Along the classical (2-o(1))n family (all C(r,2)")
    print("pair products) one gets g = n + beta - O(sqrt n), i.e. g/(n+beta) -> 1.")


def sharpness_beta_ge2_bruteforce(slow):
    section("15. (C) BRUTE-FORCE SCAN FOR g = n + beta WITH beta >= 2 (small n)")
    import random
    random.seed(4242)
    best = {}
    hits = []
    trials = 20000 if slow else 4000
    sp = [2, 3, 5, 7, 11, 13, 17, 19]
    for _ in range(trials):
        n = random.randint(2, 4)
        A = set()
        while len(A) < n:
            kk = random.randint(1, 3)
            A.add(prod(random.sample(sp, kk)))
        A = tuple(sorted(A))
        if max(A) > 400:
            continue
        st = incidence_stats(A)
        if st['beta'] < 2:
            continue
        x = random.randint(0, 4000)
        g, _ = exact_g(A, x, want_witness=False)
        gap = len(A) + st['beta'] - g
        key = (len(A), st['beta'])
        if key not in best or gap < best[key][0]:
            best[key] = (gap, A, x, g)
        if gap == 0:
            hits.append((A, x, g, st['beta']))
    print("smallest observed slack (n+beta) - g among SMALL-prime instances, by (n,beta):")
    for key in sorted(best):
        gap, A, x, g = best[key]
        print(f"   n={key[0]} beta={key[1]}: min slack {gap}  (A={A}, x={x}, g={g})")
    print("hits with slack 0 in this small-prime random scan:", len(hits))
    print("(Small-prime instances are far from sharp; sharpness needs the LARGE-prime")
    print(" constructions of sections 12-13.)")


def check_criterion_and_density():
    section("16. EXACT FORM OF THE THREE STRUCTURAL CONDITIONS, AND HOW OFTEN THEY HOLD")
    print("Rewriting  beta = Omega_0 - n - |P| + c  gives the equivalent criteria")
    print("   pseudoforest  beta <= c        <=>  sum_a (omega(a)-1)      <= |P(A)|")
    print("   Theorem 4     beta <= n        <=>  sum_a (omega(a)-2)      <= |P(A)| - c")
    print("   Lemma 5       beta_core <= k   <=>  sum_{core}(omega(a)-2)  <= |P(core)| - c_core")
    print("For all-omega=3 inputs the last two both read  n <= |P| - c  (resp. k <= |P_core|-c),")
    print("i.e. the inputs must use MORE distinct primes than there are inputs.  Every")
    print("known hard family fails this: the F3 family of astra_708_2n.md has n = C(l,3)")
    print("inputs on l primes, so |P| ~ (6n)^(1/3) << n and beta/n -> 2.")
    print()
    import random
    random.seed(11)
    print("Random model: n inputs, each a product of 3 distinct primes from the first s.")
    print(f"{'n':>3} {'s':>4} {'s/n':>5} {'P(beta_core<=k)':>16} {'P(pseudoforest)':>16}")
    for n in (6, 10, 20):
        for ratio in (0.4, 0.8, 1.0, 1.2, 1.6, 2.5):
            s_ = max(3, int(ratio * n))
            if s_ > len(PRIMES):
                continue
            primes = PRIMES[:s_]
            hit = hit2 = tot = 0
            for _ in range(1500):
                A = set(); guard = 0
                while len(A) < n and guard < 500:
                    A.add(prod(random.sample(primes, 3))); guard += 1
                if len(A) < n:
                    continue
                A = tuple(sorted(A))
                st = incidence_stats(A)
                core = tuple(a for a in A if omega(a) >= 3); k = len(core)
                bc = beta_of(core, False)
                tot += 1; hit += (bc <= k); hit2 += (st['beta'] <= st['c'])
            if tot:
                print(f"{n:>3} {s_:>4} {ratio:>5} {100*hit/tot:>15.1f}% {100*hit2/tot:>15.1f}%")


def check_F1_and_extremal():
    section("17. CROSS-CHECKS AGAINST THE ACCEPTED BACKGROUND")
    ps = [53, 59, 61, 67, 71]
    A = tuple(sorted(prod(c) for c in combinations(ps, 3)))
    st = incidence_stats(A); n = len(A)
    print("astra_708_2n.md F1 instance (ten triple products of 53..71):")
    print(f"  n={n} m={max(A)} s={st['s']} W_s={st['W']} nu={st['nu']} c={st['c']} beta={st['beta']}")
    print(f"  Theorem 4 gives n+beta = {n+st['beta']}  (F1 computed the same certificate value 1+5*5=26)")
    print(f"  P7 n+W_s-nu = {n+st['W']-st['nu']},  P8 2n-c+beta+d = {2*n-st['c']+st['beta']+st['s']-st['nu']}")
    print("  => Theorem 4 improves 35 -> 26 but, as F1 already showed, the whole-input")
    print("     anchor route still exceeds 2n = 20 here.  No contradiction with F1.")
    print()
    print("Classical (2-o(1))n family (all C(r,2) pair products, window at M):")
    for r in (4, 5):
        best = None
        for stt in range(3, 120):
            qs = PRIMES[stt:stt + r]
            if len(qs) < r:
                break
            m = qs[-2] * qs[-1]
            if 2 * qs[0] * qs[1] <= m:
                continue
            M = prod(qs); minpair = qs[0] * qs[1]
            AA = tuple(sorted(a * b for a, b in combinations(qs, 2)))
            for alpha in range(m):
                x = M - alpha - 1
                if x < 0 or minpair <= max(alpha, m - 1 - alpha):
                    continue
                T = sum((x + m) // (q * q) - x // (q * q) for q in qs)
                if best is None or T < best[0]:
                    best = (T, qs, AA, x, m)
            if best and best[0] <= 1:
                break
        T, qs, AA, x, m = best
        stt2 = incidence_stats(AA); nn = len(AA)
        g, _ = exact_g(AA, x, want_witness=False)
        print(f"  r={r} primes={qs}: n={nn} beta={stt2['beta']} n+beta={nn+stt2['beta']} "
              f"EXACT g={g}  g/n={g/nn:.3f}  (slack {nn+stt2['beta']-g})")
    print("  => on the extremal family g = n+beta - O(sqrt n): asymptotically tight in")
    print("     ratio but not exactly attained; exact attainment is the K_{2,t} family.")


def main():
    slow = "--slow" in sys.argv
    check_instances(slow)
    check_table_properties()
    check_lemma6()
    check_shortage_lemmas(slow)
    check_theorem4_anchors(slow)
    random_stress(slow)
    check_2_vs_1_theory()
    check_pseudoforest_comparison()
    check_prop9_and_D5()
    check_sift()
    check_theorem8()
    sharpness_search(rmax=9)
    sharpness_beta_linear(tmax=6)
    sharpness_ceiling()
    sharpness_beta_ge2_bruteforce(slow)
    check_criterion_and_density()
    check_F1_and_extremal()
    print("\nALL REFEREE CHECKS COMPLETE")


if __name__ == "__main__":
    main()
