#!/usr/bin/env python3
"""Exact certificates for H_(56501/6400), plus reproducible adversarial audits.

Only the Python standard library is used. All certificate arithmetic is integer
or Fraction arithmetic. Searches in the audit are finite, deterministic searches;
they are not invoked as evidence for a universal hinge inequality.
"""
from bisect import bisect_right
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, product
from math import comb, factorial, isqrt, prod
import hashlib
import json

Q = 2**16
H = F(1025, 1024)
RHO = F(9, 8)
T = F(401, 75)
D0 = F(3601, 1280)
C0 = F(56501, 6400)
SMALL_SLOPE = F(16, 27)
SMALL_LOSS = F(243, 128)
# t=v/64; eta(t)=ETA[v]/720. Below or at 1/8, eta(t)=16*t/27.
ETA = {
    9:60, 10:60, 11:71, 12:72, 13:76, 14:80, 15:88, 16:96,
    18:120, 20:120, 22:120, 24:120, 26:120, 28:120,
    30:160, 32:160,
    36:240, 40:240, 44:240, 48:240, 52:240, 56:240, 60:240, 64:240,
}
# Entries are 40*K. At L=8 there is just j=8; otherwise j=8,...,15.
K40 = {
    8:[200],
    16:[125,113,125,138,150,162,175,187],
    32:[61,72,78,73,79,87,97,91],
    64:[50,54,57,58,60,58,57,66],
    128:[45,46,47,48,47,50,48,49],
    256:[43,43,43,43,44,44,44,45],
    512:[41,41,42,42,42,42,42,42],
    1024:[41,41,41,41,41,41,41,41],
}
FINITE_MICRO = {
    8:48879, 16:549612, 32:271163, 64:99084,
    128:20073, 256:1577, 512:26, 1024:1,
}
KTAIL = F(41,40)
LAMBDA_TAIL = F(50)
A0 = F(120347,2500000)
# x_j, an upper bound for P_j(x_j), and sigma_j.
TAIL = {
    8:(F(473,625), F(421847,1000000), F(157,200)),
    9:(F(3883,5000), F(42539,100000), F(827,1000)),
    10:(F(7939,10000), F(42847,100000), F(859,1000)),
    11:(F(4047,5000), F(107879,250000), F(22,25)),
    12:(F(8233,10000), F(216251,500000), F(111,125)),
    13:(F(4181,5000), F(86661,200000), F(441,500)),
    14:(F(8481,10000), F(215799,500000), F(863,1000)),
    15:(F(8593,10000), F(213963,500000), F(83,100)),
}
PREC = 56


def ceildiv(a, b):
    assert a >= 0 and b > 0
    return (a+b-1)//b


def delta(theta):
    if theta >= F(7,8):
        return F(9,40)
    if theta >= F(3,4):
        return F(3,20)
    return F(1,8)


def multiplier(theta, K):
    den = K-H-delta(theta)*theta
    assert den > 0
    return RHO*K/den


def exp_upper(x, n=40):
    assert 0 <= x < n+2
    term = F(1)
    ans = term
    for k in range(1,n+1):
        term *= x/k
        ans += term
    nxt = term*x/(n+1)
    return ans+nxt/(1-x/F(n+2))


def log_lower(z, n=20):
    assert z > 1
    u = (z-1)/(z+1)
    return 2*sum((u**(2*k+1)/F(2*k+1) for k in range(n)), F(0))


def retention_and_rounding():
    levels = sorted(ETA)
    for v,e in ETA.items():
        assert F(e,720) <= F(1,3)
        assert F(e,720) <= SMALL_SLOPE*F(v,64)
    assert SMALL_SLOPE*(1+F(1,8)) == F(2,3)
    maxima = []
    for v in levels:
        dp = [None]*65
        dp[0] = 0
        for w in range(1,65):
            vals = [dp[w-u]+ETA[u] for u in levels
                    if u >= v and u <= w and dp[w-u] is not None]
            if vals:
                dp[w] = max(vals)
        mx = max(dp[w]+ETA[v] for w in range(65-v,65)
                 if dp[w] is not None)
        assert mx <= 480
        maxima.append([v,mx])
    reward = {v:(levels[i+1] if i+1 < len(levels) else 64)
              for i,v in enumerate(levels)}
    dp = [None]*720
    dp[0] = 0
    for w in range(1,720):
        vals = [dp[w-ETA[v]]+reward[v] for v in levels
                if ETA[v] <= w and dp[w-ETA[v]] is not None]
        if vals:
            dp[w] = max(vals)
    vals = [(1440*dp[w]+243*(720-w),w) for w in range(720)
            if dp[w] is not None]
    value,where = max(vals)
    assert value == 259272 and where == 696
    assert F(value,92160) == D0
    assert D0+RHO*T == C0 < 9 < F(97,10)
    assert C0 >= 7 and T > F(41,8)
    dense = (1-F(1,Q))*H-H**8/factorial(8)
    assert dense > 1
    print('retention prefix maxima [v,720*budget]:', maxima)
    print('rounding maximum:', str(D0), 'at cost', where, '/720')


def sieve(limit):
    a = bytearray(b'\1')*(limit+1)
    a[0:2] = b'\0\0'
    for p in range(2,isqrt(limit)+1):
        if a[p]:
            a[p*p:limit+1:p] = b'\0'*(((limit-p*p)//p)+1)
    return [p for p in range(2,limit+1) if a[p]]


def prime_density_certificates():
    pp = sieve(2**21)
    assert bisect_right(pp,64) == 18
    u = F(1,3)
    ll = log_lower(F(2),20)
    lu = ll+2*u**41/(41*(1-u*u))
    assert F(2,3) < ll <= lu < F(7,10)
    # These are the rational constants in the analytic proof in the text.
    assert F(7,5)+F(14,50)+F(189,32768) < F(17,10)
    assert F(17,10)/(17*F(2,3)) == F(3,20)
    assert F(17,10)/(21*F(2,3)) < F(1,8)
    ranges = [(210,32768,9,40), (2310,2**17,3,20),
              (30030,2**21,1,8)]
    for start,end,num,den in ranges:
        assert den*bisect_right(pp,start) <= num*start
        for i in range(bisect_right(pp,start-1),bisect_right(pp,end-1)):
            assert den*(i+1) <= num*pp[i]
    assert prod(pp[:4]) == 210
    assert prod(pp[:5]) == 2310
    assert prod(pp[:6]) == 30030
    print('prime-density finite ranges: PASS')
    return pp


@lru_cache(maxsize=None)
def fact(n):
    return factorial(n)


def moment_envelopes(L,j):
    """Return exact outward-rounded epsilon values, in common units 2^-bits."""
    bits = 64+32*ceildiv(L,j)
    hh = H*F(L,j)
    hats,orders = [],[]
    for d in range(1,j+1):
        # a=(T-1-d/L)/(j/L)=(326*L-75*d)/(75*j).
        an,ad = 326*L-75*d,75*j
        pn,pd = hh.numerator,hh.denominator
        bn,bd,br = None,None,None
        for r in range(2,an//ad+2):
            pn *= hh.numerator
            pd *= hh.denominator
            v = (r*an)//((r-1)*ad)
            assert v >= r
            dn = 75*j*v-an
            assert dn > 0
            falling = fact(v)//fact(v-r)
            num,den = dn*pn,75*L*pd*falling
            if bn is None or num*bd < bn*den:
                bn,bd,br = num,den,r
        assert bn is not None and br >= 2
        hats.append(ceildiv(bn << bits,bd))
        orders.append(br)
    return bits,hats,orders


def coefficient_rows(L,j):
    levels = {L}
    z = 1
    while 8*z <= L:
        levels.update(a*z for a in range(8,16) if j <= a*z <= L)
        z *= 2
    levels = sorted(levels)
    assert j in levels
    degree = L+j
    p = [0]*(degree+1)
    p[0] = 1
    q = p[:]
    rows = []
    def multiply(ar,exponents):
        out = [0]*(degree+1)
        for v in exponents:
            for w in range(degree-v+1):
                if ar[w]:
                    out[w+v] += ar[w]
        return out
    for k in range(1,degree//j+1):
        p = multiply(p,levels)
        q = multiply(q,[v for v in levels if v != j])
        row = [p[L+d]-q[L+d] for d in range(1,j+1)]
        assert min(row) >= 0
        rows.append(row)
    return levels,rows


def general_scale_bound(L,j,K,bits,hats,rows):
    kn,kd = K.numerator,K.denominator
    maxn = (kn*L)//(kd*j)+(L+j)//j+1
    best = 0
    weighted = [[(d,c*hats[d-1]) for d,c in enumerate(row,1) if c]
                for row in rows]
    for N in range(2,maxn+1):
        val = 0
        for k,row in enumerate(weighted,1):
            if k > N:
                break
            n = N-k
            pen = kn*L-kd*n*j
            if pen <= 0:
                continue
            choose = comb(N,k)
            for d,c in row:
                num = choose*c*pen
                den = (kn*(d+n*j)) << bits
                val += ceildiv(num << PREC,den)
        best = max(best,val)
    return F(best,1 << PREC)


def high_scale_bound(L,j,K,bits,hats,levels):
    theta = F(j,L)
    eps = [F(h,1 << bits) for h in hats]
    e2 = eps[2*j-L-1] if theta > F(1,2) else F(0)
    e3 = eps[j-1] if theta == F(1,2) else F(0)
    best = F(0)
    maxn = (K.numerator*L)//(K.denominator*j)+3
    for N in range(2,maxn+1):
        p2 = max(F(0),1-(N-2)*theta/K)
        p3 = max(F(0),1-(N-3)*theta/K) if N >= 3 else F(0)
        for cap in levels:
            es = sum((eps[j+t-L-1] for t in levels if j < t <= cap),F(0))
            num = N*(N-1)*(e2/2+es)*p2
            if e3 and N >= 3:
                num += comb(N,3)*e3*p3
            den = F(N*cap,L)-1
            if den > 0:
                best = max(best,num/den)
            else:
                assert num == 0
    return best


def finite_scale_certificates():
    total = F(0)
    for L,ks in K40.items():
        subtotal = F(0)
        for j,k40 in zip(([8] if L == 8 else range(8,16)),ks):
            K,theta = F(k40,40),F(j,L)
            bits,hats,orders = moment_envelopes(L,j)
            levels,rows = coefficient_rows(L,j)
            if theta >= F(1,2):
                aa = high_scale_bound(L,j,K,bits,hats,levels)
            else:
                aa = general_scale_bound(L,j,K,bits,hats,rows)
            subtotal += multiplier(theta,K)*aa
        upper = F(FINITE_MICRO[L],10**6)
        assert subtotal < upper
        total += upper
        print('finite scale',L,'<',str(upper),flush=True)
    assert total == F(990415,10**6)
    return total


def tail_certificate():
    ee = sum((F(1,factorial(k)) for k in range(13)),F(0))
    assert ee*log_lower(F(9,2),20) > 4
    assert exp_upper(F(7,2)*H,40) < F(133,4)
    assert F(133,4)**75 < A0**75*F(9,2)**326
    assert RHO*KTAIL/(KTAIL-H-F(1,8)*F(15,2048)) < LAMBDA_TAIL
    ans = F(0)
    for j,(x,pbar,sigma) in TAIL.items():
        p = sum((x**a for a in range(j,16)),F(0))
        p += sum((x**(a*2**h) for h in range(1,5)
                  for a in range(8,16)),F(0))
        p += x**256/(1-x)
        assert 0 < p <= pbar < 1
        assert (A0*x**(-j))**40 <= sigma**40*(1-pbar)**41
        pref = LAMBDA_TAIL*RHO*j*sum((x**(-d) for d in range(1,j+1)),F(0))
        pref /= pbar*(1-pbar)
        z = sigma**(2048//j)
        ans += pref*z/(1-z)
    assert ans < F(1,1000)
    print('infinite tail < 1/1000')
    return F(1,1000)


def crt(residues):
    """Return the least nonnegative x satisfying x=r (mod p)."""
    x,mod = 0,1
    for p,r in sorted(residues.items()):
        x += mod*((r-x)*pow(mod,-1,p) % p)
        mod *= p
    assert all(x % p == r % p for p,r in residues.items())
    return x,mod


def hr_audit(pp):
    """Deterministic HR-type admissible-tuple search, then exact verification."""
    m,cutoff = 20000,2498
    primes = pp[:bisect_right(pp,cutoff)]
    rr = {p:(m//2) % p for p in primes if p <= isqrt(m)}
    cov = bytearray(m+1)
    for p,r in rr.items():
        for i in range(r or p,m+1,p):
            cov[i] += 1
    for p in primes:
        if p in rr:
            continue
        hist = [0]*p
        for i in range(1,m+1):
            if cov[i] == 0:
                hist[i % p] += 1
        r = hist.index(min(hist))
        rr[p] = r
        for i in range(r or p,m+1,p):
            cov[i] += 1
    history = [sum(v == 0 for v in cov[1:])]
    for _ in range(3):
        changed = False
        for p in reversed(primes):
            old = rr[p]
            for i in range(old or p,m+1,p):
                cov[i] -= 1
            hist = [0]*p
            for i in range(1,m+1):
                if cov[i] == 0:
                    hist[i % p] += 1
            mn = min(hist)
            r = old if hist[old] == mn else hist.index(mn)
            changed |= (r != old)
            rr[p] = r
            for i in range(r or p,m+1,p):
                cov[i] += 1
        history.append(sum(v == 0 for v in cov[1:]))
        if not changed:
            break
    offsets = [i for i in range(1,m+1) if cov[i] == 0]
    assert len(offsets) == 2268 < cutoff
    assert bisect_right(pp,m) == 2262
    assert all(all(i % p != rr[p] for i in offsets) for p in primes)
    # Primes above cutoff exceed the number of offsets, so cannot be exhausted.
    x,period = crt({p:-r for p,r in rr.items()})
    assert all(all((x+i) % p for p in primes) for i in offsets)
    payload = {'m':m,'cutoff':cutoff,'residues':sorted(rr.items()),'offsets':offsets}
    digest = hashlib.sha256(json.dumps(payload,separators=(',',':')).encode()).hexdigest()
    print('HR-type audit:',history,'pi(m)=2262','object SHA256='+digest)
    return rr


def count_multiples(x,m,d):
    return (x+m)//d-x//d


def carrier_window_audit(hr_residues):
    ps = (3,5,7,11,13,17)
    period = prod(ps)
    theta,K = F(1),F(5)
    lam = multiplier(theta,K)
    hh = sum((F(1,p) for p in ps),F(0))
    assert hh < H
    for m in (10**4,10**5,10**6,10**7):
        assert all(p**3 <= m for p in ps)
        mass = (m//period)*(6-T)
        nu = m//15
        coeff = lam*mass/nu
        assert coeff <= 1  # Strongest pointwise case: outside mass zero.
        xx,_ = crt({p:-hr_residues[p] for p in ps})
        dense = (-(m//2)) % period
        xs = (0,(-m) % period,dense,xx)
        for x in xs:
            ff = coeff*(count_multiples(x,m,15)-sum(
                (F(count_multiples(x,m,15*p),5) for p in ps[2:]),F(0)))
            rhs = 0
            for r in range(2,len(ps)+1):
                rhs += (-1)**r*sum(count_multiples(x,m,prod(z))
                                    for z in combinations(ps,r))
            assert RHO*mass <= ff <= rhs
    print('reflected / centered CRT / HR carrier-window audits: PASS')


def discarded_rule_refutation():
    m = 2**132
    qs = (2**33,3**20,5**13)
    pc = prod(qs)
    q = 7**15
    source = pc*prod((11,13,17,19,23,29,31,37))
    assert all(z**4 <= m for z in qs)
    assert q**3 <= m
    assert source <= m < pc*q
    assert F(11,2) > T
    print('discarded eta(1/2)=1/4 rule: negative-modulus assertion REFUTED')
    print(json.dumps({'m':m,'P':pc,'q':q,'source':source,'Pq':pc*q},sort_keys=True))


def explicit_counterexample(pp):
    ps = tuple(p for p in pp if p >= 500)[:21]
    assert ps == (503,509,521,523,541,547,557,563,569,571,577,
                  587,593,599,601,607,613,617,619,631,641)
    m = ps[-2]*ps[-1]
    center = prod(ps)
    h = m//2
    x = center-h-1
    assert m == 404471 and m % 2 == 1
    assert m < 2*ps[0]*ps[1] and m < prod(ps[:3])
    a,b = bytearray(m+1),bytearray(m+1)
    for p in ps:
        for i in range(p,m+1,p):
            a[i] += 1
        first = h % p+1
        for i in range(first,m+1,p):
            b[i] += 1
    left10 = sum(max(10*v-19,0) for v in a[1:])
    right10 = sum(10*max(v-1,0) for v in b[1:])
    assert (left10,right10) == (210,200)
    assert left10 > right10
    print('H_(19/10) REFUTED:',json.dumps({
        'primes':ps,'m':m,'x':x,'L':'21','R':'20'},sort_keys=True))


def exhaustive_small_grid():
    ps,period,maxm = (2,3,5,7),210,420
    best,record = F(1),None
    checks = 0
    for weights in product(range(3),repeat=4):
        vals = [sum(a for p,a in zip(ps,weights) if n % p == 0)
                for n in range(1,period+maxm)]
        rp = [0]
        for a in vals:
            rp.append(rp[-1]+max(a-2,0))
        cnt = [0]*9
        for m in range(1,maxm+1):
            cnt[vals[m-1]] += 1
            rr,x = min((rp[x+m]-rp[x],x) for x in range(period))
            checks += period
            assert sum(max(i-4,0)*cnt[i] for i in range(9)) <= rr
            assert sum(max(i-6,0)*cnt[i] for i in range(9)) <= rr
            if rr == 0:
                root = F(max(i for i in range(9) if cnt[i]),2)
            else:
                root = None
                for lo in range(8):
                    n = sum(cnt[lo+1:])
                    mass = sum(i*cnt[i] for i in range(lo+1,9))
                    if n:
                        z = F(mass-rr,n)
                        if lo <= z <= lo+1:
                            root = z/2
                            break
                if root is None:
                    continue
            if root > best:
                best,record = root,(weights,m,x,rr)
    assert checks == 7144200 and best == F(5,4)
    print('EXHAUSTIVE half-weight four-prime grid:',checks,
          'windows; max critical threshold',str(best),'record',record)


def main():
    retention_and_rounding()
    pp = prime_density_certificates()
    finite = finite_scale_certificates()
    tail = tail_certificate()
    assert finite+tail == F(198283,200000) < 1
    discarded_rule_refutation()
    explicit_counterexample(pp)
    exhaustive_small_grid()
    hr = hr_audit(pp)
    carrier_window_audit(hr)
    print('FINAL: H_'+str(C0)+'; g(n) <= ceil('+str(C0)+'*n)+2*n <= 11*n')
    print('Universal proof dependencies: the mathematical lemmas in the text;')
    print('all numerical assertions above have passed exact arithmetic.')


if __name__ == '__main__':
    main()