#!/usr/bin/env python3
"""Evaluate (TH), (PQ), (LAYER) and the level-set statement (LS0) on a huge-x window from a certificate file.
Valuations on I computed from residues of x (exact, iterating prime powers). Usage: python3 bigwindow_eval.py certfile"""
import sys, math, random
import numpy as np
def primes_upto(N):
    s=bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2,int(N**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(N+1) if s[i]]
cert=dict(l.strip().split('=',1) for l in open(sys.argv[1]) if '=' in l and not l.startswith('#'))
m=int(cert['m']); x=int(cert['x']); P=primes_upto(m)
# valuations: vI[p] = array of v_p(x+1+i), vK[p] = v_p(k), k=1..m
vI={}; vK={}
i_all=np.arange(m, dtype=np.int64)
for p in P:
    v=np.zeros(m, dtype=np.int64); q=p; idx=i_all
    while True:
        xq=x%q
        sel=idx[np.mod(xq+1+idx, q)==0]
        if len(sel)==0: break
        v[sel]+=1; idx=sel; q*=p
    vI[p]=v
    vk=np.zeros(m+1, dtype=np.int64); q=p
    while q<=m: vk[q::q]+=1; q*=p
    vK[p]=vk[1:]
def weights(z):
    wI=np.zeros(m); wK=np.zeros(m)
    for p,zp in z.items():
        if zp: wI+=zp*vI[p]; wK+=zp*vK[p]
    return wI,wK
def report(name,z):
    wI,wK=weights(z)
    L=np.maximum(wK-2,0).sum(); R=np.maximum(wI-1,0).sum()
    # (PQ) per prime power
    worst=(1e18,None)
    for p,zp in z.items():
        if not zp: continue
        q=p
        while q<=m:
            maskI=vI[p]>=int(round(math.log(q,p))); maskK=vK[p]>=int(round(math.log(q,p)))
            lhs=np.minimum(1,1/wI[maskI]).sum(); NI=int(maskI.sum()); rhs=NI-(m//q)+np.minimum(1,2/wK[maskK]).sum()
            if rhs-lhs<worst[0]: worst=(rhs-lhs,q)
            q*=p
    # (LAYER): for values v of wK > 2: #{wK>=v} <= #{wI>=v-1}
    sK=np.sort(wK); sI=np.sort(wI); vals=np.unique(sK[sK>2+1e-9]); lay=(1e18,None)
    for v in vals:
        a=len(sK)-np.searchsorted(sK,v-1e-9); b=len(sI)-np.searchsorted(sI,v-1-1e-9)
        if b-a<lay[0]: lay=(b-a,round(float(v),3))
    # (LS0) tau=1,2: #{k<=m: wK>=2tau} <= #{b in I: wI>=tau}
    ls=[]
    for tau in (0.5,1,1.5,2,3):
        a=int((wK>=2*tau-1e-9).sum()); b=int((wI>=tau-1e-9).sum()); ls.append((tau,b-a))
    print(f"{name}: (TH) slack={R-L:.1f}  (PQ) min slack={worst[0]:.3f} at q={worst[1]}  (LAYER) min slack={lay}  (LS0) tau->slack {ls}")
r=int(math.isqrt(m))
report("z=1 on primes<=m/2", {p:1.0 for p in P if p<=m//2})
report("z=1 on all primes<=m", {p:1.0 for p in P})
report("z=1 on primes<=sqrt(m)", {p:1.0 for p in P if p<=r})
report("z=1 on sqrt(m)<p<=m/2", {p:1.0 for p in P if r<p<=m//2})
report("z=1/2 on all", {p:0.5 for p in P})
report("z=1 on p<=sqrt m, 1/2 above", {p:(1.0 if p<=r else 0.5) for p in P})
random.seed(3); report("random z", {p:random.random() for p in P})
report("z=p^-0.5", {p:p**-0.5 for p in P})
report("z=1 on p<=20", {p:1.0 for p in P if p<=20})
