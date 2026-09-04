from fractions import Fraction as F
import random
# integer-scaled sieve (weights are multiples of 1/SC)
SC=1000
def sieve_int(alpha,start,length):
    S=[0]*(length+1)
    for p,d in alpha.items():
        for j,a in d.items():
            q=p**j
            if q>start+length: continue
            n=((start//q)+1)*q
            while n<=start+length:
                S[n-start]+=a; n+=q
    return S
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

def experiment(t,primes,m,seed,nx=400,maxj=2):
    rng=random.Random(seed); C=2*t
    alpha={}
    for p in primes:
        b=rng.randint(int(0.86*SC),SC)
        rest=SC-b
        d={1:b}
        if maxj>1 and rest>0 and rng.random()<0.5: d[2]=rng.randint(0,rest)
        alpha[p]={j:v for j,v in d.items() if v>0}
    SK=sieve_int(alpha,0,m)
    highs=[k for k in range(1,m+1) if SK[k]>C*SC]
    if not highs: return None
    Cstar=F(t,3)*(1-F(1,6**(t-1)))
    # build D's for the smallest high point
    k=min(highs)
    xs=[];ps=[]
    for p in alpha:
        v=F(sum(a for j,a in alpha[p].items() if k%(p**j)==0),SC)
        if v>0: xs.append(v);ps.append(p)
    G=engine_construct(xs,t)
    if G is None: return ("L1FAIL",)
    Ds=[]
    for g in G:
        D=1
        for i in g:
            p=ps[i];Jp=max(j for j in alpha[p] if k%(p**j)==0);D*=p**Jp
        Ds.append(D)
    pr=1
    for D in Ds: pr*=D
    assert k%pr==0 and all(D>=6 for D in Ds)
    L=F(sum(SK[q]-C*SC for q in highs),SC)
    bound=Cstar*F(m)  # /k^(1/t) handled by exact power comparison
    worst=None; viol=0; certviol=0
    for trial in range(nx):
        x = rng.randint(0,10**9) if trial else 0
        if trial==1: x = pr*rng.randint(1,10**5) - m//2   # window centred on a multiple of prod D
        SI=sieve_int(alpha,x,m)
        R=F(sum(v-SC for v in SI[1:] if v>SC),SC)
        for b in range(x+1,x+m+1):
            tt=sum(1 for D in Ds if b%D==0)
            if tt and F(tt,3)>max(F(SI[b-x],SC)-1,F(0)): certviol+=1
        if (R**t)*k < (Cstar**t)*(m**t): viol+=1
        if worst is None or R<worst[0]: worst=(R,x)
    return dict(m=m,k=k,Ds=Ds,L=float(L),minR=float(worst[0]),xworst=worst[1],
                bnd_k=float(Cstar)*m/k**(1.0/t), bnd_m=float(Cstar)*m**(1-1.0/t),
                viol=viol,certviol=certviol,nhigh=len(highs))

print("=== t=2 (C=4), m close to the smallest high point: the tight regime k~m ===")
for m in [2310,2500,3000,5000,10000]:
    got=0
    for seed in range(1,40):
        r=experiment(2,[2,3,5,7,11,13],m,seed,nx=120)
        if r is None or isinstance(r,tuple): continue
        got+=1
        if got==1:
            print(" m=%6d k=%5d D=%s  L=%.3f  min_x R=%.3f (x=%d)  C*m/k^(1/2)=%.3f  C*m^(1/2)=%.3f  violations=%d certviol=%d"%(
                r['m'],r['k'],r['Ds'],r['L'],r['minR'],r['xworst'],r['bnd_k'],r['bnd_m'],r['viol'],r['certviol']))
    if got==0: print(" m=%6d : no high point"%m)
