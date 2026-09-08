"""Independent adversarial referee verifier for pro_708_r19/proof.md.

Written from the manuscript's definitions only; exact integer / Fraction
arithmetic throughout, no floating point in any decision.

  python3 referee_checks.py            # everything (~4 min)
  python3 referee_checks.py E1 E2 E3   # select the stress-test blocks

Sections
  A  levels D, eta table, Lemma 3 retention knapsack (15)-(16),
     Lemma 4 rounding knapsack (22)-(23), Lemma 2 dense branch,
     Lemma 1 vertex bound, Lemma 10 (exact recomputation of both sides)
  B  Lemma 6: prime densities (29) by sieve, the analytic continuation (35),
     the (30) class counts, K_theta > H*+delta*theta, lambda_theta
  C  Lemma 7/8: all 57 finite scales recomputed from (28),(39),(40),(42)
  D  Lemma 8: the infinite tail (46)-(53)
  E  hostile end-to-end tests (counting polynomial, pointwise certificate,
     synthetic atom systems)
  F  exact grand total, adversarial-audit fixture, transfer arithmetic
"""
import sys, random, itertools
from fractions import Fraction as F
from math import comb, factorial, isqrt, prod, gcd

import sys
from fractions import Fraction as F
from math import comb, factorial

Hs = F(1025,1024); rho = F(9,8); T = F(401,75)

Ktab={
 8:{8:F(200,40)},
 16:{8:F(125,40),9:F(113,40),10:F(125,40),11:F(138,40),12:F(150,40),13:F(162,40),14:F(175,40),15:F(187,40)},
 32:{8:F(61,40),9:F(72,40),10:F(78,40),11:F(73,40),12:F(79,40),13:F(87,40),14:F(97,40),15:F(91,40)},
 64:{8:F(50,40),9:F(54,40),10:F(57,40),11:F(58,40),12:F(60,40),13:F(58,40),14:F(57,40),15:F(66,40)},
 128:{8:F(45,40),9:F(46,40),10:F(47,40),11:F(48,40),12:F(47,40),13:F(50,40),14:F(48,40),15:F(49,40)},
 256:{8:F(43,40),9:F(43,40),10:F(43,40),11:F(43,40),12:F(44,40),13:F(44,40),14:F(44,40),15:F(45,40)},
 512:{8:F(41,40),9:F(41,40),10:F(42,40),11:F(42,40),12:F(42,40),13:F(42,40),14:F(42,40),15:F(42,40)},
 1024:{j:F(41,40) for j in range(8,16)},
}
CLAIM = {8:48879, 16:549612, 32:271163, 64:99084, 128:20073, 256:1577, 512:26, 1024:1}

def delta(th):
    if th>=F(7,8): return F(9,40)
    if th>=F(3,4): return F(3,20)
    return F(1,8)

# ---------------- epsilon_{theta,s}  (28), via un-normalised integer comparison
_FACT=[1]
def fact(n):
    while len(_FACT)<=n: _FACT.append(_FACT[-1]*len(_FACT))
    return _FACT[n]

def epsilon(theta, s):
    a = (T-s)/theta
    if a < 1: return None
    rmax = a.numerator//a.denominator + 1          # floor(a)+1
    # (H*/theta)^r  incrementally as (p/q)^r
    hp = Hs/theta
    p, q = hp.numerator, hp.denominator
    best_n = best_d = None
    pw_p, pw_q = p, q                              # r = 1
    for r in range(2, rmax+1):
        pw_p *= p; pw_q *= q
        v = int((r*a)/(r-1))                       # floor
        if v < r: continue
        # val = theta*(v-a)*(p/q)^r / (v)_r ;  (v)_r = fact(v)/fact(v-r)
        va = v - a                                 # Fraction
        num = theta.numerator*va.numerator*pw_p*fact(v-r)
        den = theta.denominator*va.denominator*pw_q*fact(v)
        if best_n is None or num*best_d < best_n*den:
            best_n, best_d = num, den
    return F(best_n, best_d)

# ---------------- level set restricted to a scale
def exponents(j, L):
    """{ L*t : t in D, t >= j/L }  as a sorted list of ints (each level once)."""
    th = F(1) if L==8 else F(j,L)
    S=set()
    h=4
    while 2**h <= L:
        for jj in range(8,16):
            t=F(jj,2**h)
            if t>=th: S.add(int(L*t))
        h+=1
    if F(1)>=th: S.add(L)                          # level 1
    return sorted(S)

def Dlevels_ge(th):
    """levels of D in [th, 1]"""
    S={F(1)}
    h=4
    while F(15,2**h) >= th:
        for jj in range(8,16):
            t=F(jj,2**h)
            if t>=th: S.add(t)
        h+=1
        if h>40: break
    return sorted(S)

def polymul_sparse(a, exps, cap):
    r=[0]*(cap+1)
    for i,ci in enumerate(a):
        if ci:
            for e in exps:
                k=i+e
                if k<=cap: r[k]+=ci
                else: break
    return r

def A40(j, L, K):
    th = F(1) if L==8 else F(j,L)
    exps = exponents(j,L)
    jexp = exps[0]                                 # = j (the level theta)
    assert jexp == (8 if L==8 else j)
    cap = L + j
    kmax = cap//jexp
    exps2 = exps[1:]                               # P - X^j
    E = {}                                         # E[k][d]
    cur=[0]*(cap+1); cur[0]=1
    cur2=[0]*(cap+1); cur2[0]=1
    for k in range(1, kmax+1):
        cur = polymul_sparse(cur, exps, cap)
        cur2 = polymul_sparse(cur2, exps2, cap)
        row = {}
        for d in range(1, j+1):
            val = cur[L+d]-cur2[L+d]
            if val: row[d]=val
        if row: E[k]=row
    if not E: return F(0), 0
    eps = {d: epsilon(th, 1+F(d,L)) for d in range(1,j+1)}
    Nmax = int(K/th) + int(1/th) + 2
    nmax = int(K/th)+1
    W = {}                                          # W[(d,n)]
    for d in range(1,j+1):
        for n in range(0, nmax+1):
            pen = 1 - n*th/K
            if pen<=0: continue
            den = F(d,L)+n*th
            W[(d,n)] = eps[d]*pen/den
    if not W: return F(0),0
    # common denominator -> integer inner loop
    Dc = 1
    for w in W.values():
        Dc = Dc*w.denominator//__import__('math').gcd(Dc, w.denominator)
    Wi = {kk: int(v*Dc) for kk,v in W.items()}
    best=0; bestN=0
    for N in range(0, Nmax+1):
        tot=0
        for (d,n),wi in Wi.items():
            k=N-n
            if k<1 or k>kmax: continue
            row=E.get(k)
            if not row: continue
            e=row.get(d)
            if e: tot += comb(N,k)*e*wi
        if tot>best: best=tot; bestN=N
    # confirm the N-range truncation
    for N in range(Nmax+1, Nmax+7):
        tot=0
        for (d,n),wi in Wi.items():
            k=N-n
            if 1<=k<=kmax and E.get(k,{}).get(d): tot+=comb(N,k)*E[k][d]*wi
        assert tot==0, f"nonzero beyond N-range at (j={j},L={L},N={N})"
    return F(best,Dc), bestN

def A42(j, L, K):
    th = F(1) if L==8 else F(j,L)
    assert th>=F(1,2)
    e_th = epsilon(th, 2*th) if th>F(1,2) else F(0)
    h_th = epsilon(F(1,2), F(3,2)) if th==F(1,2) else F(0)
    lv = Dlevels_ge(th)
    Ecum = {}
    acc=F(0)
    for v in lv:
        # E_theta(v) = sum over levels t with theta < t <= v
        acc = sum((epsilon(th, th+t) for t in lv if th<t<=v), F(0))
        Ecum[v]=acc
    Nmax = int(K/th)+int(1/th)+2
    best=F(0); arg=None
    for N in range(2, Nmax+7):
        p2 = 1-(N-2)*th/K
        p3 = 1-(N-3)*th/K
        p2 = p2 if p2>0 else F(0)
        p3 = p3 if p3>0 else F(0)
        for v in lv:
            num = N*(N-1)*(e_th/2+Ecum[v])*p2 + comb(N,3)*h_th*p3
            den = N*v-1
            if den==0:
                assert num==0, f"zero denominator with nonzero numerator (j={j},L={L},N={N},v={v})"
                continue
            r=num/den
            if r>best: best=r; arg=(N,v)
    return best, arg

def run(Ls):
    grand=F(0)
    for L in Ls:
        tot=F(0); rows=[]
        for j in sorted(Ktab[L]):
            K=Ktab[L][j]
            th = F(1) if L==8 else F(j,L)
            lam = rho*K/(K-Hs-delta(th)*th)
            a40,N40 = A40(j,L,K)
            if th>=F(1,2):
                a42,arg42 = A42(j,L,K)
                A = min(a40,a42)
                tag=f"A40={float(a40):.9f} A42={float(a42):.9f} arg42={arg42}"
            else:
                A=a40; tag=f"A40={float(a40):.9f} (Nmax arg {N40})"
            tot += lam*A
            rows.append(f"    j={j:2d} th={str(th):>9s} K={str(K):>7s} lam={float(lam):.6f} "
                        f"A={float(A):.9f} lam*A={float(lam*A):.9f}   {tag}")
        for r in rows: print(r)
        cl=F(CLAIM[L],10**6)
        print(f"  L={L:5d}: sum_j lambda*A = {float(tot):.9f}   claim {CLAIM[L]}/1e6 = {float(cl):.9f}   "
              f"{'OK' if tot<cl else '**EXCEEDS CLAIM**'}   (as 1e6 units: {float(tot*10**6):.4f})")
        sys.stdout.flush()
        grand+=tot
    print(f"TOTAL over {Ls}: {float(grand):.9f}  ({float(grand*10**6):.4f} in 1e-6 units)")
    return grand



from fractions import Fraction as F
from math import comb, factorial, isqrt

OUT = []
def say(s):
    print(s)
    OUT.append(s)

def ok(name, cond, extra=""):
    say(("PASS  " if cond else "**FAIL** ") + name + (("   " + extra) if extra else ""))
    return cond

# ---------------------------------------------------------------- constants
Q = 2**16
Hs = F(1025, 1024)
rho = F(9, 8)
T = F(401, 75)
D0 = F(3601, 1280)
c_thr = F(56501, 6400)

say("=== PART A ===")
ok("(1) D0 + rho*T = 56501/6400", D0 + rho*T == c_thr, f"{D0+rho*T}")
ok("c = 56501/6400 < 97/10", c_thr < F(97,10), f"{float(c_thr)}")
ok("c >= 7 (needed by Lemma 2)", c_thr >= 7)

# ---------------------------------------------------------------- level set D
def D_levels(hmax=24):
    L = [F(1)]
    for h in range(4, hmax+1):
        for j in range(8, 16):
            L.append(F(j, 2**h))
    return sorted(set(L), reverse=True)

Dl = D_levels(24)
ratios = []
for i in range(len(Dl)-1):
    ratios.append(Dl[i]/Dl[i+1])
ok("max adjacent ratio in D is 9/8", max(ratios) == rho, f"max={max(ratios)}")

# successor map (in D)
def successor(t):
    # smallest level in D strictly greater than t
    cands = [u for u in Dl if u > t]
    return min(cands) if cands else None

# ---------------------------------------------------------------- eta
Etab = {}
for v in (9,10): Etab[v]=60
Etab[11]=71; Etab[12]=72; Etab[13]=76; Etab[14]=80; Etab[15]=88; Etab[16]=96
for v in (18,20,22,24,26,28): Etab[v]=120
for v in (30,32): Etab[v]=160
for v in (36,40,44,48,52,56,60,64): Etab[v]=240

# which D levels are > 1/8 ?
big = sorted({t for t in Dl if t > F(1,8)})
bigv = sorted({int(t*64) for t in big})
ok("levels of D above 1/8 are exactly v/64 for the 24 tabulated v",
   all(t*64 == int(t*64) for t in big) and bigv == sorted(Etab.keys()),
   f"count={len(bigv)}")

def eta(t):
    if t <= F(1,8):
        return F(16,27)*t
    v = t*64
    assert v.denominator == 1
    return F(Etab[int(v)], 720)

ok("(12) eta(t) <= 1/3 for every level",
   all(eta(t) <= F(1,3) for t in Dl), f"max={max(eta(t) for t in Dl)}")
ok("(12) eta(t) <= 16t/27 for every level",
   all(eta(t) <= F(16,27)*t for t in Dl))

# ---------------------------------------------------------------- Lemma 3 knapsack (15)-(16)
V = sorted(Etab.keys())          # levels above 1/8, in units of 1/64
def Dv_table(vmin):
    NEG = None
    f = [NEG]*65
    f[0] = 0
    for w in range(1, 65):
        best = NEG
        for u in V:
            if u >= vmin and u <= w and f[w-u] is not None:
                cand = f[w-u] + Etab[u]
                if best is None or cand > best:
                    best = cand
        f[w] = best
    return f

res16 = {}
for v in V:
    f = Dv_table(v)
    best = None
    for w in range(65-v, 65):
        if 0 <= w <= 64 and f[w] is not None:
            cand = f[w] + Etab[v]
            if best is None or cand > best:
                best = cand
    res16[v] = best
ok("(16) max_{65-v<=w<=64}(D_v(w)+E_v) = 480 for all 24 v",
   all(r == 480 for r in res16.values()),
   f"values={sorted(set(res16.values()))}")
ok("(11) exponent budget 480/720 = 2/3", F(480,720) == F(2,3))

# independent (different formulation): exhaustive DFS over nonincreasing multisets
best_seen = F(0)
worst = None
def dfs(idx, mass, eta_sum, vmin, chosen):
    """levels chosen in nonincreasing order from V (units 1/64); prefix must be
    'shortest with mass > 64'.  We enumerate: all multisets whose mass w/o the
    last (= minimum) element is <= 64 and whose total mass is > 64."""
    global best_seen, worst
    if mass > 64:
        # this is a valid shortest prefix iff mass - last <= 64, guaranteed by construction
        if eta_sum > best_seen:
            best_seen = eta_sum; worst = list(chosen)
        return
    for u in V:
        if u > vmin:
            continue
        dfs(idx+1, mass+u, eta_sum + F(Etab[u],720), u, chosen+[u])
for u in V:
    dfs(1, u, F(Etab[u],720), u, [u])
ok("Lemma 3 exhaustive enumeration: max sum eta over theta>1/8 carriers = 2/3",
   best_seen == F(2,3), f"max={best_seen}, attained e.g. by {worst}")

# theta <= 1/8 branch
ok("Lemma 3 low branch: (16/27)*(9/8) = 2/3", F(16,27)*F(9,8) == F(2,3))

# ---------------------------------------------------------------- Lemma 4 knapsack (22)-(23)
succ_v = {}
for i, v in enumerate(V):
    succ_v[v] = V[i+1] if i+1 < len(V) else 64      # reward 64 at the top
# sanity: successor in D agrees
agree = True
for v in V:
    t = F(v,64)
    s = successor(t)
    if v == 64:
        agree &= (s is None)
    else:
        agree &= (s == F(succ_v[v],64))
ok("reward r_v = next level in D (64 at the top)", agree)

R = [None]*720
R[0] = 0
for w in range(1, 720):
    best = None
    for v in V:
        E = Etab[v]
        if E <= w and R[w-E] is not None:
            cand = R[w-E] + succ_v[v]
            if best is None or cand > best:
                best = cand
    R[w] = best

bestval = None; bestw = None
for w in range(0, 720):
    if R[w] is None: continue
    val = 1440*R[w] + 243*(720-w)
    if bestval is None or val > bestval:
        bestval = val; bestw = w
ok("(23) max over attainable w<=719 of 1440R(w)+243(720-w) = 259272",
   bestval == 259272, f"max={bestval} at w={bestw}, R={R[bestw]}")
ok("(23) maximiser w=696, R(w)=176", bestw == 696 and R[696] == 176,
   f"w={bestw}, R={R[bestw]}")
# claimed maximizing pattern 1,1,7/16,1/4
pat = [64,64,28,16]
ok("claimed pattern 1,1,7/16,1/4 has cost 696 and reward 176",
   sum(Etab[v] for v in pat) == 696 and sum(succ_v[v] for v in pat) == 176,
   f"cost={sum(Etab[v] for v in pat)}, reward={sum(succ_v[v] for v in pat)}")
ok("(23)/92160 = 3601/1280", F(259272, 92160) == D0, f"{F(259272,92160)}")
ok("92160 = 64*1440 = 128*720", 92160 == 64*1440 == 128*720)
ok("rho*t = (243/128)*eta(t) for t <= 1/8",
   all(rho*t == F(243,128)*eta(t) for t in Dl if t <= F(1,8)))

# ---------------------------------------------------------------- Lemma 2 dense branch
val = (1 - F(1,Q))*Hs - Hs**8/factorial(8)
ok("(6) (1-1/Q)H* - H*^8/8! > 1", val > 1, f"excess={val-1} = {float(val-1):.6e}")

# ---------------------------------------------------------------- Lemma 1 (3) spot check
def Ar(a, r):
    v = (r*a)//(r-1)          # floor for Fraction
    v = int(v)
    return F(v - a, comb(v, r)), v
bad = []
for (num,den) in [(7,1),(251,75),(1123,200),(83,16),(401,75)]:
    a = F(num,den)
    for r in range(2, int(a)+2):
        A, v = Ar(a, r)
        for h in range(0, 40):
            if F(h) - a > A*comb(h, r):
                bad.append((a,r,h))
ok("Lemma 1 (3) vertex inequality holds at sampled (a,r)", not bad, f"{bad[:3]}")

# ---------------------------------------------------------------- Lemma 10
P21 = [503,509,521,523,541,547,557,563,569,571,577,
       587,593,599,601,607,613,617,619,631,641]
def isprime(n):
    if n < 2: return False
    for d in range(2, isqrt(n)+1):
        if n % d == 0: return False
    return True
ok("all 21 listed numbers are prime and there are 21 of them",
   len(P21)==21 and len(set(P21))==21 and all(isprime(p) for p in P21))
ok("the 21 primes are exactly the primes in [503,641]",
   P21 == [p for p in range(503,642) if isprime(p)])
m10 = 631*641
ok("m = 631*641 = 404471", m10 == 404471, f"{m10}")
pairs = [P21[i]*P21[j] for i in range(21) for j in range(i+1,21)]
ok("C(21,2)=210 pair products", len(pairs)==210)
ok("largest pair product = m", max(pairs)==m10)
ok("smallest pair product 503*509 = 256027", min(pairs)==256027, f"{min(pairs)}")
ok("2*min pair product > m (each pair product occurs exactly once in [1,m])",
   2*min(pairs) > m10, f"2*256027={2*256027} > {m10}")
triples = 503*509*521
ok("smallest triple product 503*509*521 = 133390067 > m",
   triples == 133390067 and triples > m10, f"{triples}")
QP = 1
for p in P21: QP *= p
x10 = QP - 202236
claimed_x = 8741863184546118987302153833068330864675030899050452812141
ok("(54) x = Q_P - 202236 equals the printed integer", x10 == claimed_x,
   f"mine={x10}")
ok("window I = {Q_P-202235,...,Q_P+202235} has length m",
   (x10+1 == QP-202235) and (x10+m10 == QP+202235) and (2*202235+1 == m10))
ok("window radius 202235 < smallest pair product", 202235 < min(pairs))

# exact LHS by direct enumeration
Pset = set(P21)
lhs = F(0)
cnt2 = 0
for k in range(1, m10+1):
    s = 0
    for p in P21:
        if k % p == 0:
            s += 1
            if s >= 2 and k % (p) == 0:
                pass
    if s >= 2: cnt2 += 1
    if s > F(19,10):
        lhs += F(s) - F(19,10)
ok("(55) LHS = sum_{k<=m}(S(k)-19/10)^+ = 21 (direct enumeration)",
   lhs == 21, f"LHS={lhs}, #k with S(k)>=2 is {cnt2}")
ok("exactly 210 integers k<=m with S(k)>=2", cnt2 == 210)

# exact RHS: b = Q_P + r, p|b <=> p|r  (p | Q_P)
rhs = F(0)
worst_off = 0
for r in range(-202235, 202236):
    if r == 0:
        s = 21
    else:
        s = sum(1 for p in P21 if r % p == 0)
        worst_off = max(worst_off, s)
    if s > 1:
        rhs += s - 1
ok("(55) RHS = sum_{b in I}(S(b)-1)^+ = 20 (direct enumeration over offsets)",
   rhs == 20, f"RHS={rhs}, max S at a non-centre point = {worst_off}")
ok("H_{19/10} refuted: 21 > 20", lhs > rhs)

# generalisation: conditions for r primes in [M, sqrt2 M)
say("")
say("--- generalisation checks ---")
say("  2*p1*p2 >= 2M^2 > p_{r-1}p_r  (since p_i < sqrt2 M)  -> each pair product once")
say("  smallest triple >= M^3 > 2M^2 > m  for M > 2         -> no triple in [1,m]")
say("  window radius (m-1)/2 < M^2 <= p1*p2                 -> only Q_P has 2 chosen primes")
say("  L = C(r,2)(2-c), R = r-1;  L > R  <=>  (r/2)(2-c) > 1  <=>  c < 2 - 2/r")
for r in (2,3,5,10,21,100):
    lhs_g = F(comb(r,2))*(2-F(19,10)); rhs_g = r-1
    thr = 2 - F(2,r)
    say(f"   r={r:4d}: threshold 2-2/r = {thr} = {float(thr):.6f}")
ok("failure condition C(r,2)(2-c) > r-1  <=>  c < 2-2/r  (algebra)",
   all((F(comb(r,2))*(2-cc) > r-1) == (cc < 2-F(2,r))
       for r in range(2,60) for cc in [F(1),F(3,2),F(19,10),F(199,100),F(2)]))

with open("/tmp/refA.txt","w") as f:
    f.write("\n".join(OUT))


from fractions import Fraction as F
from math import comb

OUT=[]
def say(s):
    print(s); OUT.append(s)
def ok(n,c,e=""):
    say(("PASS  " if c else "**FAIL** ")+n+(("   "+e) if e else "")); return c

Hs=F(1025,1024); rho=F(9,8); T=F(401,75)

say("=== PART B ===")
# ---------------------------------------------------------- sieve
N=2**21
sieve=bytearray([1])*(N+1); sieve[0]=sieve[1]=0
i=2
while i*i<=N:
    if sieve[i]: sieve[i*i::i]=bytearray(len(sieve[i*i::i]))
    i+=1
pi=[0]*(N+1); c=0
for n in range(N+1):
    c+=sieve[n]; pi[n]=c
say(f"  pi(210)={pi[210]}  pi(2310)={pi[2310]}  pi(30030)={pi[30030]}  pi(2^21)={pi[N]}")

def check(lo, hi, bound):
    bad=[]
    for v in range(lo, hi+1):
        if F(pi[v],v) > bound:
            bad.append((v,pi[v]))
            if len(bad)>3: break
    return bad
b1=check(210, 2**15, F(9,40))
b2=check(2310, 2**17, F(3,20))
b3=check(30030, 2**21, F(1,8))
ok("(29) pi(v)/v <= 9/40 on [210, 2^15] (every integer checked)", not b1, str(b1[:3]))
ok("(29) pi(v)/v <= 3/20 on [2310, 2^17] (every integer checked)", not b2, str(b2[:3]))
ok("(29) pi(v)/v <= 1/8 on [30030, 2^21] (every integer checked)", not b3, str(b3[:3]))
say(f"  worst ratios: 210 -> {F(pi[210],210)}={float(F(pi[210],210)):.6f} (9/40=0.225)")
say(f"                2310 -> {F(pi[2310],2310)}={float(F(pi[2310],2310)):.6f} (3/20=0.15)")
mx=max(F(pi[v],v) for v in range(2310,2**17+1))
say(f"                max on [2310,2^17] = {float(mx):.6f}")
mx3=max(F(pi[v],v) for v in range(30030,N+1))
say(f"                max on [30030,2^21] = {float(mx3):.6f} (1/8=0.125)")

# analytic continuation (35): pi(x) log x / x < 17/10 for x >= 2^15
# 18 log x/x  +  log 4  +  2 log4/log x, with 2/3 < log2 < 7/10
say("  (35): 18 log x/x + log4 + 2log4/log x  <=  189/32768 + 7/5 + 14/50 at x=2^15")
tot=F(189,32768)+F(7,5)+F(14,50)
ok("(35) 189/32768 + 7/5 + 14/50 < 17/10", tot < F(17,10), f"{tot}={float(tot):.6f}")
# consequences using log2 > 2/3
for (lo_pow, bound, name) in ((15,F(9,40),"9/40"),(17,F(3,20),"3/20"),(21,F(1,8),"1/8")):
    val = F(17,10)/(lo_pow*F(2,3))
    ok(f"  for x>=2^{lo_pow}: 1.7/log x < 1.7/({lo_pow}*2/3) = {val} <= {name}",
       val <= bound, f"{float(val):.6f} vs {float(bound):.6f}")

# ---------------------------------------------------------- (30)/(31) class counts
def Dlevels(hmax=20):
    L=[F(1)]
    for h in range(4,hmax+1):
        for j in range(8,16): L.append(F(j,2**h))
    return sorted(set(L), reverse=True)
Dl=Dlevels(20)
def delta(th):
    if th>=F(7,8): return F(9,40)
    if th>=F(3,4): return F(3,20)
    return F(1,8)
def cls(th):
    if th>=F(7,8): return 1
    if th>=F(3,4): return 2
    return 3
need={1:4,2:5,3:6}
cof={4:210,5:2310,6:30030}
bad=[]; report={}
for th in Dl:
    # #outside primes  >  (T-1-th)/th   using b_p <= theta_C for outside primes
    nmin = (T-1-th)/th
    import math
    k = math.floor(nmin)+1                 # strictly greater -> at least floor+1
    if nmin == int(nmin): k = int(nmin)+1
    cl=cls(th)
    report.setdefault(cl, []).append((th,k))
    if k < need[cl]: bad.append((th,k,cl))
ok("(30) class 1 (theta>=7/8) forces >=4 outside primes  [uses b_p<=theta_C]",
   all(k>=4 for th,k in report[1]), f"min={min(k for th,k in report[1])}")
ok("(30) class 2 (3/4<=theta<7/8) forces >=5 outside primes",
   all(k>=5 for th,k in report[2]),
   f"levels={[(str(t),k) for t,k in report[2]]}")
ok("(30) class 3 (theta<3/4) forces >=6 outside primes",
   all(k>=6 for th,k in report[3]),
   f"min over first few = {[(str(t),k) for t,k in report[3][:4]]}")
# what happens with the weaker b_p <= 1 that the referral suggests?
say("  --- counter-probe: with only b_p <= 1 (mass > T-1-theta), the counts are:")
for cl in (1,2,3):
    ths=[t for t,_ in report[cl]]
    import math
    ks=[math.floor(T-1-t)+1 for t in ths]
    say(f"      class {cl}: min count {min(ks)} (needed {need[cl]})")
say("  -> classes 2 and 3 REQUIRE the sharper b_p <= theta_C, and the discreteness of D.")
_b = (F(41,8)-1-F(11,16))/F(11,16)
say(f"      41/8 = {float(F(41,8)):.6f} < T = {float(T):.6f}; at theta=11/16, (41/8-1-th)/th = {_b} exactly -> strict '>' gives >=6")

# ---------------------------------------------------------- lambda table
Ktab={
 8:{8:F(200,40)},
 16:{8:F(125,40),9:F(113,40),10:F(125,40),11:F(138,40),12:F(150,40),13:F(162,40),14:F(175,40),15:F(187,40)},
 32:{8:F(61,40),9:F(72,40),10:F(78,40),11:F(73,40),12:F(79,40),13:F(87,40),14:F(97,40),15:F(91,40)},
 64:{8:F(50,40),9:F(54,40),10:F(57,40),11:F(58,40),12:F(60,40),13:F(58,40),14:F(57,40),15:F(66,40)},
 128:{8:F(45,40),9:F(46,40),10:F(47,40),11:F(48,40),12:F(47,40),13:F(50,40),14:F(48,40),15:F(49,40)},
 256:{8:F(43,40),9:F(43,40),10:F(43,40),11:F(43,40),12:F(44,40),13:F(44,40),14:F(44,40),15:F(45,40)},
 512:{8:F(41,40),9:F(41,40),10:F(42,40),11:F(42,40),12:F(42,40),13:F(42,40),14:F(42,40),15:F(42,40)},
 1024:{j:F(41,40) for j in range(8,16)},
}
bad=[]
for L,d in Ktab.items():
    for j,K in d.items():
        th = F(1) if L==8 else F(j,L)
        if not (K > Hs + delta(th)*th): bad.append((L,j,float(K)))
ok("K_theta > H* + delta(theta)theta for all 57 finite scales", not bad, str(bad))
# tail
th_max=F(15,2048)
Kt=F(41,40)
lam_t = rho*Kt/(Kt-Hs-F(1,8)*th_max)
ok("tail: K=41/40 > H*+delta*theta and lambda_theta < 50 for L>=2048",
   Kt>Hs+F(1,8)*th_max and lam_t<50, f"sup lambda = {lam_t} = {float(lam_t):.6f}")

with open("/tmp/refB.txt","w") as f: f.write("\n".join(OUT))


import sys
from fractions import Fraction as F
from math import prod
Hs=F(1025,1024); rho=F(9,8); T=F(401,75); D0=F(3601,1280); C0=F(56501,6400)
OUT=[]
def say(s):
    print(s); sys.stdout.flush(); OUT.append(s)
def ok(n,c,e=""):
    say(("PASS  " if c else "**FAIL** ")+n+(("   "+e) if e else "")); return c

say("=== PART F ===")
grand=F(0); per={}
for L in [8,16,32,64,128,256,512,1024]:
    tot=F(0)
    for j in sorted(Ktab[L]):
        K=Ktab[L][j]; th=F(1) if L==8 else F(j,L)
        lam=rho*K/(K-Hs-delta(th)*th)
        a40,_=A40(j,L,K)
        if th>=F(1,2):
            a42,_=A42(j,L,K); A=min(a40,a42)
        else: A=a40
        tot+=lam*A
    per[L]=tot; grand+=tot
    say(f"   L={L:5d}  mine = {float(tot*10**6):12.4f}e-6   claim = {CLAIM[L]:7d}e-6   "
        f"{'OK' if tot<F(CLAIM[L],10**6) else 'EXCEEDS'}")
ok("every one of the 8 per-L table entries is a valid strict upper bound",
   all(per[L] < F(CLAIM[L],10**6) for L in per))
ok("(44) my exact finite total < 990415/1e6",
   grand < F(990415,10**6),
   f"mine = {float(grand*10**6):.4f}e-6 vs 990415e-6 (slack {float((F(990415,10**6)-grand)*10**6):.4f}e-6)")
say(f"   exact finite total = {grand}")
ok("finite total + tail bound < 1 (the whole pointwise factor)",
   F(990415,10**6)+F(1,1000) == F(198283,200000) < 1)

# --- adversarial-audit fixture (discarded eta(1/2)=1/4 rule)
m=2**132; qs=(2**33,3**20,5**13); P=prod(qs); q=7**15
k=P*prod((11,13,17,19,23,29,31,37))
ok("audit fixture: each carrier modulus <= m^{1/4} under the DISCARDED rule",
   all(z**4<=m for z in qs))
ok("audit fixture: q = 7^15 <= m^{1/3}", q**3<=m)
ok("audit fixture: k <= m < P*q  (so the negative modulus exceeds m)",
   k<=m<P*q, f"k/m = {float(k/m):.6f}, Pq/m = {float(P*q/m):.4f}")
ok("audit fixture: B(k) = 11/2 > T", F(11,2)>T, f"11/2 = 5.5 > {float(T):.6f}")

# --- transfer arithmetic
bad=[n for n in range(1,20000) if -(-C0.numerator*n//C0.denominator)+2*n > 11*n]
ok("g(n) <= ceil(cn)+2n <= 11n for n=1..19999 (and c<=9 gives it for all n)",
   not bad and C0<=9, str(bad[:3]))

with open("/tmp/refF.txt","w") as f: f.write("\n".join(OUT))


from fractions import Fraction as F
from math import factorial, comb

OUT=[]
def say(s):
    print(s); OUT.append(s)
def ok(n,c,e=""):
    say(("PASS  " if c else "**FAIL** ")+n+(("   "+e) if e else "")); return c

Hs=F(1025,1024); rho=F(9,8); T=F(401,75); a0=F(120347,2500000)
say("=== PART D ===")

# ---------- rigorous rational bounds on exp
def exp_lower(x, N=60):
    return sum((x**n)/factorial(n) for n in range(N+1))
def exp_upper(x, N=60):
    """sum_{n<=N} x^n/n!  +  x^{N+1}/(N+1)! * 1/(1-x/(N+2))   (needs N+2 > x > 0)"""
    assert x>0 and F(N+2)>x
    s = exp_lower(x,N)
    tail = (x**(N+1))/factorial(N+1) / (1 - x/(N+2))
    return s+tail
e_lo, e_hi = exp_lower(F(1),25), exp_upper(F(1),25)
ok("e < 87/32", e_hi < F(87,32), f"e < {float(e_hi):.10f}")
ok("e > 8/3", e_lo > F(8,3), f"e > {float(e_lo):.10f}")
ok("(87/32)^3 < (9/2)^2", F(87,32)**3 < F(9,2)**2, f"{float(F(87,32)**3):.6f} < 20.25")
say("  => log(9/2) > 3/2 and e > 8/3  =>  e*log(9/2) > 4   [so z/(e log z) < (9/2)/4 = 9/8 = rho]")

x = F(7,2)*Hs
eu = exp_upper(x, 60)
ok("exp((7/2)H*) < 133/4", eu < F(133,4), f"exp((7/2)H*) < {float(eu):.9f} vs 33.25")
ok("(47) (133/4)^75 < a0^75 (9/2)^326",
   F(133,4)**75 < a0**75 * F(9,2)**326,
   f"ratio = {float((F(133,4)**75)/(a0**75*F(9,2)**326)):.9f}")
say(f"  a0 = {a0} = {float(a0):.9f}; minimal admissible a0 = (133/4)/(9/2)^(326/75) "
    f"= {float(F(133,4)/ (F(9,2)**F(326,75).numerator)**F(1,75) if False else 0)}")
# margin, numerically
import math
need = math.exp(3.5*float(Hs))/ (4.5**(326/75))
say(f"  exact-arith admissible floor for a0 is about {need:.9f}; a0 = {float(a0):.9f}; "
    f"relative margin {(float(a0)-need)/need*100:.4f}%")

# ---------- the (x_j, Pbar_j, sigma_j) table
tab = {
 8:(F(473,625),   F(421847,10**6),  F(157,200)),
 9:(F(3883,5000), F(42539,10**5),   F(827,1000)),
10:(F(7939,10000),F(42847,10**5),   F(859,1000)),
11:(F(4047,5000), F(107879,250000), F(22,25)),
12:(F(8233,10000),F(216251,500000), F(111,125)),
13:(F(4181,5000), F(86661,200000),  F(441,500)),
14:(F(8481,10000),F(215799,500000), F(863,1000)),
15:(F(8593,10000),F(213963,500000), F(83,100)),
}
def Pcal_bound(j,x):
    """upper bound for  sum_{a=j}^{15} x^a + sum_{h>=1} sum_{a=8}^{15} x^{a 2^h}
       (exact through h=4, remainder by x^256/(1-x))."""
    s = sum(x**a for a in range(j,16))
    for h in range(1,5):
        for a in range(8,16): s += x**(a*2**h)
    return s + x**256/(1-x)
def Pcal_lower(j,x):
    s = sum(x**a for a in range(j,16))
    for h in range(1,5):
        for a in range(8,16): s += x**(a*2**h)
    return s

bad=[]
for j,(xj,Pb,sg) in tab.items():
    up = Pcal_bound(j,xj); lo = Pcal_lower(j,xj)
    c1 = (0 < lo) and (up <= Pb) and (Pb < 1)
    c2 = (a0*xj**(-j))**40 <= sg**40 * (1-Pb)**41
    if not (c1 and c2): bad.append((j,c1,c2))
    say(f"   j={j:2d}: P_j(x_j) <= {float(up):.9f}  Pbar={float(Pb):.9f}  ok={c1}; "
        f"(49) slack ratio {float((a0*xj**(-j))**40 / (sg**40*(1-Pb)**41)):.6f}  ok={c2}")
ok("0 < P_j(x_j) <= Pbar_j < 1 for all j, and (49) holds for all j", not bad, str(bad))

# ---------- (52)/(53)
tot = F(0)
for j,(xj,Pb,sg) in tab.items():
    Dj = sum(xj**(-d) for d in range(1,j+1))
    zj = sg**(2048//j)
    assert zj<1
    term = 50*rho*j*Dj/(Pb*(1-Pb)) * zj/(1-zj)
    tot += term
    say(f"   j={j:2d}: z_j = sigma^{2048//j} = {float(zj):.6e}, term = {float(term):.6e}")
ok("(53) tail sum < 1/1000", tot < F(1,1000),
   f"tail = {float(tot):.9e}  ( = {float(tot*1000):.6f} x 1/1000 )")

# ---------- closing constants
fin = F(990415,10**6)
ok("(44)+(53): 990415/1e6 + 1/1000 = 198283/200000", fin+F(1,1000)==F(198283,200000),
   f"{fin+F(1,1000)}")
ok("(45) 198283/200000 < 1", F(198283,200000)<1, f"{float(F(198283,200000)):.6f}")
# my own recomputed finite total
mine = {8:F(0),16:F(0)}
say("")
say("  my recomputed per-L totals (1e-6 units): 48878.5585, 549611.3594, 271162.2971,")
say("     99083.0052, 20072.6904, 1576.4180, 25.5148, 0.0201  -> 990409.8635 < 990415")

with open("/tmp/refD.txt","w") as f: f.write("\n".join(OUT))


import sys, random, itertools
from fractions import Fraction as F
from math import comb, factorial

Hs=F(1025,1024); rho=F(9,8); T=F(401,75); D0=F(3601,1280); Q=2**16
OUT=[]
def say(s):
    print(s); sys.stdout.flush(); OUT.append(s)
def ok(n,c,e=""):
    say(("PASS  " if c else "**FAIL** ")+n+(("   "+e) if e else "")); return c

WHICH = set(a for a in sys.argv[1:] if a.startswith("E")) or {"E1","E2","E3"}
say("=== PART E ===")

# ------------------------------------------------------------------ E1
if "E1" in WHICH:
    def brute_E(j,L,k,d):
        th = F(1) if L==8 else F(j,L)
        lv = [F(e,L) for e in exponents(j,L)]
        target = 1+F(d,L); cnt=0
        def rec(i, tot, mn):
            nonlocal cnt
            if i==k:
                if tot==target and mn==th: cnt+=1
                return
            for t in lv:
                if tot+t*(k-i) > target + (k-i)*0: pass
                if tot+t > target: continue
                rec(i+1, tot+t, min(mn,t))
        rec(0, F(0), F(99))
        return cnt
    bad=[]; ntest=0
    for (j,L) in [(8,8),(8,16),(11,16),(15,16),(8,32),(13,32),(9,64),(15,64)]:
        exps=exponents(j,L); cap=L+j; kmax=cap//exps[0]
        cur=[0]*(cap+1); cur[0]=1
        cur2=[0]*(cap+1); cur2[0]=1
        for k in range(1,min(kmax,4)+1):
            cur=polymul_sparse(cur,exps,cap); cur2=polymul_sparse(cur2,exps[1:],cap)
            for d in range(1,j+1):
                got=cur[L+d]-cur2[L+d]; want=brute_E(j,L,k,d); ntest+=1
                if got!=want: bad.append((j,L,k,d,got,want))
    ok(f"E1: E_{{k,d}} equals brute-force count of level assignments "
       f"({ntest} coefficients, 8 scales, k<=4)", not bad, str(bad[:4]))

# ------------------------------------------------------------------ E2
FINAL = F(198283,200000)
_K={}
for L,d in Ktab.items():
    for j,K in d.items():
        _K[F(1) if L==8 else F(j,L)] = K
def Kof(th): return _K.get(th, F(41,40))
_lam={}
def lam_of(th):
    if th not in _lam:
        K=Kof(th); _lam[th]=rho*K/(K-Hs-delta(th)*th)
    return _lam[th]
_eps={}
def eps_c(th,s):
    if (th,s) not in _eps: _eps[(th,s)]=epsilon(th,s)
    return _eps[(th,s)]

def stress(prof, pool):
    """prof: sorted-descending caps at n.  Enumerate EVERY carrier (subset +
    level assignment with t_p<=cap_p, min=theta, mass>1, mass-theta<=1)."""
    N=len(prof); B=sum(prof); tot=F(0); ncar=0
    idxs=list(range(N))
    for k in range(2, N+1):
        for idx in itertools.combinations(idxs, k):
            outside=[i for i in idxs if i not in idx]
            pools=[[t for t in pool if t<=prof[i]] for i in idx]
            if any(not p for p in pools): continue
            res=[]
            def rec(i, asg, s):
                if s>2: return                      # s <= 1+theta <= 2
                if i==k:
                    th=min(asg)
                    if s>1 and s-th<=1: res.append((th,s))
                    return
                for t in pools[i]:
                    rec(i+1, asg+[t], s+t)
            rec(0,[],F(0))
            for th,s in res:
                U=sum(min(prof[t],th) for t in outside)
                pen=1-U/Kof(th)
                if pen<=0: continue
                ncar+=1
                tot += lam_of(th)*eps_c(th,s)*pen
    return tot, FINAL*max(F(0),B-1), B, ncar

if "E2" in WHICH:
    poolA = sorted(Dlevels_ge(F(1,2)), reverse=True)          # 9 levels, k<=3
    poolB = sorted(Dlevels_ge(F(1,4)), reverse=True)          # 17 levels, k<=5
    random.seed(20260907)
    def batch(pool, Nmax, nrand, tag):
        profiles=[]
        for N in range(2,Nmax+1):
            for combo in itertools.combinations_with_replacement(pool, N):
                profiles.append(list(combo))
        for _ in range(nrand):
            profiles.append([random.choice(pool) for _ in range(random.randint(2,Nmax))])
        worst=(0.0,None); fails=[]; ncar_tot=0
        for prof in profiles:
            prof=sorted(prof, reverse=True)
            tot,rhs,B,nc=stress(prof,pool); ncar_tot+=nc
            r=float(tot/rhs) if rhs>0 else (0.0 if tot==0 else 9e9)
            if r>worst[0]: worst=(r,prof)
            if tot>rhs: fails.append(([str(z) for z in prof],float(tot),float(rhs)))
        ok(f"E2{tag}: pointwise bound F(n) <= (198283/200000)(B(n)-1)^+ on "
           f"{len(profiles)} profiles ({ncar_tot} carriers enumerated)", not fails,
           f"worst LHS/RHS = {worst[0]:.6f} at {[str(x) for x in worst[1]]}")
    batch(poolA, 6, 300, "a  [levels >= 1/2, N<=6]")
    poolB2=[F(1),F(15,16),F(12,16),F(9,16),F(8,16),F(15,32),F(11,32),F(8,32)]
    batch(poolB2, 4, 300, "b  [mixed levels >= 1/4, N<=4]")

    fails2=[]; worst2=0.0
    for th in [F(8,16),F(9,16),F(12,16),F(15,16),F(1)]:
        pl=[t for t in Dlevels_ge(th)]
        for N in range(2,10):
            tot,rhs,B,nc=stress([th]*N, pl)
            r=float(tot/rhs) if rhs>0 else (0.0 if tot==0 else 9e9)
            worst2=max(worst2,r)
            if tot>rhs: fails2.append((str(th),N,float(tot),float(rhs)))
    ok("E2b: flat profiles at a single level, N up to 9", not fails2,
       f"worst ratio {worst2:.6f}  {fails2[:3]}")

# ------------------------------------------------------------------ E3
if "E3" in WHICH:
    Etab={}
    for v in (9,10): Etab[v]=60
    Etab[11]=71; Etab[12]=72; Etab[13]=76; Etab[14]=80; Etab[15]=88; Etab[16]=96
    for v in (18,20,22,24,26,28): Etab[v]=120
    for v in (30,32): Etab[v]=160
    for v in (36,40,44,48,52,56,60,64): Etab[v]=240
    def eta(t):
        if t<=F(1,8): return F(16,27)*t
        return F(Etab[int(t*64)],720)
    def Dset(hmax):
        S=[F(1)]
        for h in range(4,hmax+1):
            for j in range(8,16): S.append(F(j,2**h))
        return sorted(set(S),reverse=True)
    Dl=Dset(10)
    primes=[2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,
            101,103,107,109,113,127,131,137,139,149]
    badall=[]; results=[]
    for (m,seed) in [(10**18,1),(7*10**18,2),(10**20,3),(2**80,4),(10**24,5),(10**30,6)]:
        rnd=random.Random(seed)
        S0={}
        for p in primes:
            rem=F(1); a={}
            for jj in range(1,4):
                if rem<=0: break
                w=F(rnd.randint(0,int(rem*16)),16)
                if w>0 and p**jj<=m//Q: a[jj]=w
                if w>0: rem-=w
            S0[p]=a
        maxi={p:(max(S0[p]) if S0[p] else 0) for p in primes}
        cum={}
        for p in primes:
            c=F(0)
            for i in range(1,maxi[p]+1):
                c+=S0[p].get(i,F(0)); cum[(p,i)]=c
        qp={}
        for p in primes:
            for t in Dl:
                for i in range(1,maxi[p]+1):
                    if cum[(p,i)]>=t: qp[(p,t)]=p**i; break
        ret=set()
        for (p,t),q in qp.items():
            e=eta(t)
            if q**e.denominator <= m**e.numerator: ret.add((p,t))
        bad_mod=[(p,str(t)) for (p,t) in ret if qp[(p,t)]**3>m]
        if bad_mod: badall.append(("modulus",m,bad_mod[:2]))
        retp={}
        for (p,t) in ret: retp.setdefault(p,[]).append(t)
        for p in retp: retp[p].sort(reverse=True)
        def bp(p,n):
            for t in retp.get(p,()):
                if n % qp[(p,t)]==0: return t
            return F(0)
        def S0f(p,n):
            return sum(w for jj,w in S0[p].items() if n % p**jj==0)
        rnd2=random.Random(seed*77); hot=0; checked=0
        for trial in range(4000):
            k=1
            for p in rnd2.sample(primes, rnd2.randint(4,14)):
                e=rnd2.randint(1,3)
                if k*p**e<=m: k*=p**e
            if k<2: continue
            checked+=1
            Bk=sum(bp(p,k) for p in primes); S0k=sum(S0f(p,k) for p in primes)
            if S0k > rho*Bk+D0: badall.append(("rounding",m,k,float(S0k),float(rho*Bk+D0)))
            if Bk>T:
                hot+=1
                lv=sorted(((bp(p,k),p) for p in primes if bp(p,k)>0), key=lambda z:(-z[0],z[1]))
                s=F(0); C=[]
                for t,p in lv:
                    C.append((p,t)); s+=t
                    if s>1: break
                th=min(t for _,t in C); PC=1
                for p,t in C: PC*=qp[(p,t)]
                if not (1<s<=1+th): badall.append(("mass",m,k,float(s),float(th)))
                if PC**3>m**2: badall.append(("PC",m,k,PC))
                if k%PC!=0: badall.append(("divide",m,k,PC))
                need = 210 if th>=F(7,8) else (2310 if th>=F(3,4) else 30030)
                if k//PC < need: badall.append(("cofactor",m,k,k//PC,need,str(th)))
                if m//PC < need: badall.append(("nu",m,k,m//PC,need))
                # every capped atom q satisfies P_C*q <= m
                for p in primes:
                    if any(pp==p for pp,_ in C): continue
                    for t in retp.get(p,()):
                        if min(t,th)>0 and PC*qp[(p,t)]>m:
                            badall.append(("negmod",m,k,p,str(t))); break
        results.append((m,checked,hot))
    say("  synthetic runs (m, points tested, hot points): "+str(results))
    ok("E3: no violation of Lemma 3 / 4 / 6 on synthetic atom systems",
       not badall, str(badall[:4]))

with open("/tmp/refE.txt","w") as f: f.write("\n".join(OUT))
