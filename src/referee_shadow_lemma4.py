from fractions import Fraction as F
import random
SC=100
def run(C, primes, maxj, seed, m, nx=40):
    rng=random.Random(seed)
    alpha={}
    Q=1
    for p in primes:
        J=rng.randint(1,maxj)
        w=[rng.randint(30,SC)]+[rng.randint(0,30) for _ in range(J-1)]
        if sum(w)>SC:
            s=sum(w); w=[x*SC//s for x in w]
        alpha[p]={j+1:w[j] for j in range(J) if w[j]>0}
        Q*=p**J
    P=len(primes)
    def S0(n):
        return sum(a for p,d in alpha.items() for j,a in d.items() if n%(p**j)==0)
    q=m//Q; s=m-q*Q
    U=max(max(S0(r)-C*SC,0) for r in range(1,Q+1))
    Ucond=(C-1)*q*SC>=U
    Pcond=(C-1)*q>=P-C
    L=sum(max(S0(k)-C*SC,0) for k in range(1,m+1))
    worstR=None
    for _ in range(nx):
        x=rng.randint(0,10**6)
        R=sum(max(S0(b)-SC,0) for b in range(x+1,x+m+1))
        if worstR is None or R<worstR: worstR=R
    return dict(Q=Q,P=P,q=q,U=F(U,SC),cond42=Ucond,cond41=Pcond,L=F(L,SC),minR=F(worstR,SC),ok=L<=worstR)
print("=== Lemma 4 (periodic branch), scaled threshold C ===")
bad=0; n=0
for C in [2,3,4]:
    for seed in range(1,25):
        primes=random.Random(seed*7+C).sample([2,3,5,7,11,13],k=random.Random(seed+C).randint(3,5))
        r=run(C,sorted(primes),2,seed,m=random.Random(seed*3+C).randint(500,4000),nx=25)
        n+=1
        if r['cond42'] and not r['ok']:
            bad+=1; print("  VIOLATION under (4.2):",C,r)
        if r['cond41'] and not r['cond42']:
            print("  (4.1) holds but (4.2) fails -- would break the implication (4.1)=>(4.2):",C,r)
print("instances:",n," violations of Lemma 4 conclusion when its hypothesis holds:",bad)
# show a few
for C in [4]:
    for seed in [1,2,3]:
        primes=sorted(random.Random(seed*7+C).sample([2,3,5,7,11,13],k=4))
        r=run(C,primes,2,seed,m=3000,nx=15)
        print("  C=%d primes=%s Q=%d q=%d U=%s (4.2)=%s (4.1)=%s L=%s minR=%s L<=R:%s"%(
            C,primes,r['Q'],r['q'],r['U'],r['cond42'],r['cond41'],r['L'],r['minR'],r['ok']))
