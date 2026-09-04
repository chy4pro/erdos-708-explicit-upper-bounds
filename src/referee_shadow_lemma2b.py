from fractions import Fraction as F
import random, math

def engine_construct(xs, t, lo=F(4,3), hi=F(2), big=F(2,3)):
    """Lemma 1 with C=2t: needs sum(xs) > 2t. Returns t disjoint index groups."""
    idx=list(range(len(xs)))
    large=[i for i in idx if xs[i]>big]; small=[i for i in idx if xs[i]<=big]
    groups=[]
    if len(large)>=2*t:
        sel=large[:2*t]
        return [[sel[2*j],sel[2*j+1]] for j in range(t)]
    l=len(large); s=l//2
    for j in range(s): groups.append([large[2*j],large[2*j+1]])
    pool=large[2*s:]+small; r=t-s; pos=0
    for j in range(r):
        g=[];tot=F(0)
        while tot<=lo:
            if pos>=len(pool): return None
            g.append(pool[pos]); tot+=xs[pool[pos]]; pos+=1
        groups.append(g)
    return groups

def build(primes, maxj, rng):
    """random atoms alpha[p][j], j>=1, sum_j alpha<=1"""
    alpha={}
    for p in primes:
        js=list(range(1,maxj+1))
        base=F(rng.randint(60,100),100)      # heavy weight on j=1
        w=[base]+[F(rng.randint(0,40),100) for _ in js[1:]]
        tot=sum(w)
        if tot>1: w=[x/tot for x in w]
        alpha[p]={j:w[j-1] for j in js if w[j-1]>0}
    return alpha

def S0(n, alpha):
    s=F(0)
    for p,d in alpha.items():
        for j,a in d.items():
            if n % (p**j)==0: s+=a
    return s

def a_p(n,p,alpha):
    return sum(a for j,a in alpha[p].items() if n%(p**j)==0)

def run(t, m, primes, maxj, seed, verbose=False):
    rng=random.Random(seed)
    alpha=build(primes,maxj,rng)
    C=2*t
    S=[F(0)]*(m+1)
    for p,d in alpha.items():
        for j,a in d.items():
            q=p**j
            if q> m: continue
            for n in range(q,m+1,q): S[n]+=a
    highs=[k for k in range(1,m+1) if S[k]>C]
    if not highs: return None
    x=rng.randint(0,10**7)
    # R over window I
    R=F(0)
    for b in range(x+1,x+m+1):
        v=S0(b,alpha)
        if v>1: R+=v-1
    L=sum(S[k]-C for k in highs)
    Cstar=F(t,3)*(1-F(1,6**(t-1)))
    bad=[]
    certfail=[]
    for k in highs:
        xs=[];ps=[]
        for p in alpha:
            v=a_p(k,p,alpha)
            if v>0: xs.append(v); ps.append(p)
        assert sum(xs)>C, (sum(xs),C)
        G=engine_construct(xs,t)
        if G is None: return ("LEMMA1FAIL",k)
        Ds=[]
        for g in G:
            D=1
            for i in g:
                p=ps[i]; Jp=max(j for j in alpha[p] if k%(p**j)==0); D*=p**Jp
            Ds.append(D)
        # checks
        assert all(k%D==0 for D in Ds)
        pr=1
        for D in Ds: pr*=D
        assert k%pr==0, (k,pr,Ds)
        assert all(D>=6 for D in Ds)
        # pointwise certificate on the whole window
        for b in range(x+1,x+m+1):
            tt=sum(1 for D in Ds if b%D==0)
            if tt:
                if F(tt,3) > (S0(b,alpha)-1 if S0(b,alpha)>1 else F(0)):
                    certfail.append((k,b,tt))
        rhs=Cstar*F(m)/F(k)**F(1,1)  # placeholder
        # exact comparison R >= Cstar * m / k^(1/t):  R^t * k >= Cstar^t * m^t
        if (R**t)*k < (Cstar**t)*(m**t):
            bad.append((k,float(R),float(Cstar*m/k**(1.0/t))))
    return dict(t=t,m=m,x=x,nhigh=len(highs),L=float(L),R=float(R),
                minhigh=min(highs), bound=float(Cstar*m/min(highs)**(1.0/t)),
                bound_m=float(Cstar*m**(1-1.0/t)),
                bad=bad, certfail=certfail[:5], ncertfail=len(certfail))

random.seed(1)
cases=[]
for seed in range(1,26):
    r=run(2, 20000, [2,3,5,7,11,13,17], 3, seed)
    if r: cases.append(r)
nb=sum(len(c['bad']) for c in cases); nc=sum(c['ncertfail'] for c in cases)
print("t=2 C=4 : instances with L>0:", len(cases), " bound violations:", nb, " certificate violations:", nc)
for c in cases[:6]:
    print("   m=%d nhigh=%d L=%.3f R=%.3f  minhigh=%d  bound(k)=%.2f  bound(m)=%.2f  R/L=%.1f"%(
        c['m'],c['nhigh'],c['L'],c['R'],c['minhigh'],c['bound'],c['bound_m'],c['R']/c['L'] if c['L'] else -1))
