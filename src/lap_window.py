#!/usr/bin/env python3
"""(LAP) on a huge-x window: sum_{b in I} t^{w(b)+1} <= sum_{k<=m} t^{w(k)} for t in (0,1]. Usage: python3 lap_window.py certfile"""
import sys, math, random
import numpy as np
def primes_upto(N):
    s=bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2,int(N**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(N+1) if s[i]]
cert=dict(l.strip().split('=',1) for l in open(sys.argv[1]) if '=' in l and not l.startswith('#'))
m=int(cert['m']); x=int(cert['x']); P=primes_upto(m); i_all=np.arange(m, dtype=np.int64)
vI={}; vK={}
for p in P:
    v=np.zeros(m, dtype=np.int64); q=p; idx=i_all
    while True:
        sel=idx[np.mod((x%q)+1+idx, q)==0]
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
ts=np.concatenate([np.linspace(0.0005,0.05,100), np.linspace(0.05,1,96)])
r=int(math.isqrt(m))
for name,z in [("z=1 on primes<=m/2",{p:1.0 for p in P if p<=m//2}),("z=1 all primes<=m",{p:1.0 for p in P}),
               ("z=1 on p<=sqrt m",{p:1.0 for p in P if p<=r}),("z=1/2 all",{p:0.5 for p in P}),("z=p^-0.5",{p:p**-0.5 for p in P})]:
    wI,wK=weights(z); worst=(1e18,None)
    for t in ts:
        R=(t**wK).sum(); Lj=(t**(wI+1)).sum(); s=(R-Lj)/R
        if s<worst[0]: worst=(s,float(t))
    print(f"{name}: (LAP) min relative slack {worst[0]:.4f} at t={worst[1]:.4f}")
