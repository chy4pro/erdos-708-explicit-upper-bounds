#!/usr/bin/env python3
"""Hybrid adversary for (LAP): centred coordinates n in [-h, L-h); class 0 for p <= sqrt(L) (keeps +-1 and +-primes), then for
sqrt(L) < p <= L the class minimising the (LAP) loss (1-t) t^{c+1} summed over the class. Exact evaluation from x with z=1 on
all primes <= L.  Usage: python3 adv_window2.py L t1 t2 ..."""
import sys, math
import numpy as np
def primes_upto(N):
    s=bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2,int(N**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(N+1) if s[i]]
L=int(sys.argv[1]); P=primes_upto(L); r=int(math.isqrt(L)); h=L//2
n=np.arange(-h, L-h, dtype=np.int64); i_all=np.arange(L, dtype=np.int64)
wk=np.zeros(L+1)
for p in P:
    q=p
    while q<=L: wk[q::q]+=1; q*=p
wk=wk[1:]
for t in map(float, sys.argv[2:]):
    c=np.zeros(L, dtype=np.int64); choice={}
    for p in P:
        res=np.mod(n,p)
        if p<=r: cls=0
        else:
            tot=np.bincount(res, weights=(1-t)*t**(c+1), minlength=p); cls=int(np.argmin(tot))
        choice[p]=cls; c[res==cls]+=1
    x=0; M=1
    for p,cls in choice.items():
        a=(-1-h-cls)%p; tt=((a-x)*pow(M,-1,p))%p; x+=M*tt; M*=p
    wI=np.zeros(L)
    for p in P:
        q=p; idx=i_all
        while True:
            sel=idx[np.mod((x%q)+1+idx, q)==0]
            if len(sel)==0: break
            wI[sel]+=1; idx=sel; q*=p
    lhs=(t**(wI+1)).sum(); rhs=(t**wk).sum()
    print(f"L={L} t={t}: LHS={lhs:.3f} RHS={rhs:.3f} slack={rhs-lhs:.3f} rel={(rhs-lhs)/rhs:.4f}  (#w=0 in window: {int((wI==0).sum())}, pi(L)={len(P)})", flush=True)
    if lhs>rhs:
        open(f"lap_counterexample_L{L}_t{t}.txt","w").write(f"# (LAP) VIOLATED: L={L} t={t} LHS={lhs} RHS={rhs}, z=1 on all primes<=L\nL={L}\nt={t}\nx={x}\n"); print("  WRITTEN certificate", flush=True)
