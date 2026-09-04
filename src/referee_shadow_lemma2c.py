from fractions import Fraction as F
import random

def engine_construct(xs,t,lo=F(4,3),big=F(2,3)):
    idx=list(range(len(xs)))
    large=[i for i in idx if xs[i]>big]; small=[i for i in idx if xs[i]<=big]
    if len(large)>=2*t:
        sel=large[:2*t]; return [[sel[2*j],sel[2*j+1]] for j in range(t)]
    l=len(large); s=l//2
    groups=[[large[2*j],large[2*j+1]] for j in range(s)]
    pool=large[2*s:]+small; pos=0
    for j in range(t-s):
        g=[];tot=F(0)
        while tot<=lo:
            if pos>=len(pool): return None
            g.append(pool[pos]);tot+=xs[pool[pos]];pos+=1
        groups.append(g)
    return groups

def sieve(alpha,start,length):
    """S0 on [start+1, start+length] as list of Fractions"""
    S=[F(0)]*(length+1)
    for p,d in alpha.items():
        for j,a in d.items():
            q=p**j
            if q>start+length: continue
            first=((start//q)+1)*q
            n=first
            while n<=start+length:
                S[n-start]+=a; n+=q
    return S

def run(t,m,primes,maxj,seed,hi_lo,hi_hi):
    rng=random.Random(seed)
    C=2*t
    alpha={}
    for p in primes:
        base=F(rng.randint(hi_lo,hi_hi),100)
        w=[base]+[F(rng.randint(0,int(100-hi_hi)),100) for _ in range(maxj-1)]
        if sum(w)>1:
            s=sum(w); w=[x/s for x in w]
        alpha[p]={j+1:w[j] for j in range(maxj) if w[j]>0}
    SK=sieve(alpha,0,m)
    highs=[k for k in range(1,m+1) if SK[k]>C]
    if not highs: return None
    x=rng.randint(0,10**9)
    SI=sieve(alpha,x,m)
    R=sum((v-1) for v in SI[1:] if v>1)
    L=sum(SK[k]-C for k in highs)
    Cstar=F(t,3)*(1-F(1,6**(t-1)))
    bad=[];certfail=0
    for k in highs[:6]:
        xs=[];ps=[]
        for p in alpha:
            v=sum(a for j,a in alpha[p].items() if k%(p**j)==0)
            if v>0: xs.append(v);ps.append(p)
        G=engine_construct(xs,t)
        if G is None: return ("LEMMA1FAIL",k,float(sum(xs)))
        Ds=[]
        for g in G:
            D=1
            for i in g:
                p=ps[i];Jp=max(j for j in alpha[p] if k%(p**j)==0);D*=p**Jp
            Ds.append(D)
        pr=1
        for D in Ds: pr*=D
        assert k%pr==0 and all(D>=6 for D in Ds), (k,Ds)
        for b in range(x+1,x+m+1):
            tt=sum(1 for D in Ds if b%D==0)
            if tt and F(tt,3) > max(SI[b-x]-1,F(0)): certfail+=1
        if (R**t)*k < (Cstar**t)*(m**t): bad.append((k,float(R)))
    kmin=min(highs)
    return dict(t=t,m=m,nhigh=len(highs),L=float(L),R=float(R),kmin=kmin,
                bnd_k=float(Cstar)*m/kmin**(1.0/t), bnd_m=float(Cstar)*m**(1-1.0/t),
                bad=bad,certfail=certfail)

for (t,primes,maxj,hl,hh,m) in [(2,[2,3,5,7,11,13,17,19],2,85,100,100000),
                                 (2,[2,3,5,7,11,13,17,19,23],3,80,95,100000),
                                 (3,[2,3,5,7,11,13,17,19,23,29,31],2,88,100,100000)]:
    tot=0;nb=0;nc=0;minratio=None;worst=None
    for seed in range(1,61):
        r=run(t,m,primes,maxj,seed,hl,hh)
        if r is None: continue
        if isinstance(r,tuple): print("LEMMA1 FAILURE",r); continue
        tot+=1; nb+=len(r['bad']); nc+=r['certfail']
        ratio=r['R']/r['bnd_k']
        if minratio is None or ratio<minratio: minratio=ratio; worst=r
    print("t=%d C=%d m=%d primes<=%d : instances L>0: %d | bound violations %d | pointwise-cert violations %d"%(t,2*t,m,primes[-1],tot,nb,nc))
    if worst: print("   tightest: kmin=%d L=%.4f R=%.2f  C*m/k^(1/t)=%.2f  ratio R/bound=%.2f  C*m^(1-1/t)=%.2f"%(
        worst['kmin'],worst['L'],worst['R'],worst['bnd_k'],minratio,worst['bnd_m']))
