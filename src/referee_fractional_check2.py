import numpy as np, random, math, sys

def primes_upto(N):
    s=np.ones(N+1,dtype=bool); s[:2]=False
    for i in range(2,int(N**0.5)+1):
        if s[i]: s[i*i::i]=False
    return np.nonzero(s)[0]

def S_on_1m(m, zmap):
    """S(k)=sum_p min(z_p v_p(k),1) for k=1..m, exact-ish float."""
    S=np.zeros(m+1)
    for p,z in zmap.items():
        if p>m: continue
        # v_p(k) for multiples
        pk=p; contrib=np.zeros(m+1)
        j=1
        while pk<=m:
            idx=np.arange(pk,m+1,pk)
            contrib[idx]+=1.0   # counts v_p
            pk*=p; j+=1
        v=contrib
        idx=np.nonzero(v)[0]
        S[idx]+=np.minimum(z*v[idx],1.0)
    return S

def S_on_interval(x, m, zmap):
    """S(b) for b=x+1..x+m."""
    S=np.zeros(m)
    lo=x+1; hi=x+m
    for p,z in zmap.items():
        v=np.zeros(m)
        pk=p
        while pk<=hi:
            start=((lo+pk-1)//pk)*pk
            if start<=hi:
                idx=np.arange(start-lo, hi-lo+1, pk)
                v[idx]+=1.0
            if pk> hi//p: break
            pk*=p
        idx=np.nonzero(v)[0]
        S[idx]+=np.minimum(z*v[idx],1.0)
    return S

def atoms(zmap, bound):
    """alpha_{p,j} for p^j<=bound; returns list (p,j,pj,alpha)"""
    out=[]
    for p,z in zmap.items():
        pk=p; j=1
        while pk<=bound:
            a=min(j*z,1.0)-min((j-1)*z,1.0)
            if a>0: out.append((p,j,pk,a))
            pk*=p; j+=1
    return out

random.seed(20260903); np.random.seed(20260903)
PR=primes_upto(200000)

def run_case(m, mode, nprimes=None, verbose=False):
    lim=m
    cand=[int(p) for p in PR if p<=lim]
    if nprimes is not None and nprimes<len(cand):
        cand=sorted(random.sample(cand,nprimes))
    if mode=='ones':      zmap={p:1.0 for p in cand}
    elif mode=='unif':    zmap={p:random.random() for p in cand}
    elif mode=='small':   zmap={p:random.random()*0.15 for p in cand}
    elif mode=='theta':   
        th=random.uniform(0.0,0.6); zmap={p:min(1.0,p**(-th)) for p in cand}
    elif mode=='mixed':   zmap={p:random.choice([1.0,0.7,0.4,random.random(),0.05]) for p in cand}
    zmap={p:z for p,z in zmap.items() if z>0}

    S=S_on_1m(m,zmap)
    A_all=atoms(zmap,m)                 # atoms with p^j<=m  -> S_m
    A0=[a for a in A_all if a[2]<=m/64] # atoms with p^j<=m/64 -> S_0
    # L1 check: S_m(k)==S(k) for k<=m
    Sm=np.zeros(m+1)
    for (p,j,pk,al) in A_all: Sm[pk::pk]+=al
    err=np.max(np.abs(Sm[1:]-S[1:]))
    S0=np.zeros(m+1)
    for (p,j,pk,al) in A0: S0[pk::pk]+=al
    S1=Sm-S0
    l4 = float(np.max(S1[1:])) if m>1 else 0.0
    H64=sum(al/pk for (p,j,pk,al) in A0)
    Bm0=sum(al*(m//pk) for (p,j,pk,al) in A0)
    capped=float(np.sum(np.minimum(S0[1:],64.0)))
    V = Bm0-(m+1)
    lhs65=float(np.sum(np.maximum(S[1:]-65.0,0.0)))
    lhs64_0=float(np.sum(np.maximum(S0[1:]-64.0,0.0)))
    return dict(m=m,mode=mode,nP=len(zmap),L1err=err,L4max=l4,H64=H64,capped=capped,
                V=V,lhs65=lhs65,lhs64_0=lhs64_0,zmap=zmap,S=S,S0=S0,A0=A0)

print("m      mode    |P|   L1err     max S1  H64      cappedMass-(m+1)   V      Sum(S0-64)+  Sum(S-65)+  L4ok  L5ok")
rows=[]
for m in [5000, 8000, 20000, 64000, 130000]:
    for mode in ['ones','unif','small','theta','mixed']:
        for nP in [None, 50, 300]:
            r=run_case(m,mode,nP)
            L4ok = (r['L4max']<=1.0+1e-9) if m>4096 else None
            L5ok = None
            if r['H64']>=17/16: L5ok = (r['capped']>=r['m']+1-1e-6)
            rows.append((r,L4ok,L5ok))
            print(f"{m:<7}{mode:<8}{r['nP']:<6}{r['L1err']:.2e}  {r['L4max']:7.4f} {r['H64']:8.4f} {r['capped']-(m+1):16.2f} {r['V']:10.2f} {r['lhs64_0']:10.2f} {r['lhs65']:10.2f}  {str(L4ok):5} {str(L5ok)}")
