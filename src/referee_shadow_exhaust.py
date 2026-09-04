from fractions import Fraction as F
import random
SC=1000
def exhaustive(alpha, C, m, t):
    Q=1
    for p,d in alpha.items(): Q*=p**max(d)
    # f(n) = (S0(n)-1)^+ scaled by SC, periodic mod Q ; build over [0, Q+m)
    N=Q+m+1
    S=[0]*N
    for p,d in alpha.items():
        for j,a in d.items():
            q=p**j
            for n in range(0,N,q): S[n]+=a
    f=[max(v-SC,0) for v in S]
    pre=[0]*(N+1)
    for i in range(N): pre[i+1]=pre[i]+f[i]
    # R(x) = sum_{b=x+1}^{x+m} f(b), x = 0..Q-1  (period Q)
    best=None
    for x in range(Q):
        R=pre[x+m+1]-pre[x+1]
        if best is None or R<best[0]: best=(R,x)
    # L over K={1..m}
    SK=[0]*(m+1)
    for p,d in alpha.items():
        for j,a in d.items():
            q=p**j
            for n in range(q,m+1,q): SK[n]+=a
    highs=[k for k in range(1,m+1) if SK[k]>C*SC]
    L=sum(SK[k]-C*SC for k in highs)
    Cstar=F(t,3)*(1-F(1,6**(t-1)))
    kmin=min(highs) if highs else None
    Rmin=F(best[0],SC)
    ok = (Rmin**t)*kmin >= (Cstar**t)*(m**t) if kmin else True
    return dict(Q=Q,m=m,L=float(F(L,SC)),Rmin=float(Rmin),xmin=best[1],kmin=kmin,
                bound=float(Cstar)*m/kmin**(1.0/t) if kmin else None, ok=ok, nhigh=len(highs))

print("=== exhaustive over ALL window positions x mod Q (t=2, C=4) ===")
cases=[
 ({2:{1:900},3:{1:880},5:{1:950},7:{1:990},11:{1:970}}, 2310),
 ({2:{1:900},3:{1:880},5:{1:950},7:{1:990},11:{1:970}}, 5000),
 ({2:{1:700,2:300},3:{1:880},5:{1:950},7:{1:990},11:{1:970},13:{1:600}}, 4000),
 ({2:{1:990},3:{1:990},5:{1:990},7:{1:990},11:{1:990},13:{1:990}}, 3000),
]
allok=True
for alpha,m in cases:
    r=exhaustive(alpha,4,m,2)
    allok&=r['ok']
    print(" Q=%7d m=%5d nhigh=%d kmin=%5d L=%.3f   min over ALL x: R=%.3f (x=%d)   C*m/k^{1/2}=%.3f   holds:%s  R/bound=%.1f"%(
        r['Q'],r['m'],r['nhigh'],r['kmin'],r['L'],r['Rmin'],r['xmin'],r['bound'],r['ok'],r['Rmin']/r['bound']))
    print("      also (SC_4) itself:  L=%.3f <= min_x R=%.3f  -> %s"%(r['L'],r['Rmin'],r['L']<=r['Rmin']))
print("all exhaustive checks pass:",allok)
