#!/usr/bin/env python3
"""Objective-driven adversarial windows (CRT) for (LAP) and (PQ').  For a target functional Phi(c) of the hit-count vector c
(c_i = number of chosen residue classes containing position i, one class per prime p in S), greedily choose for each prime the
class that loses the least Phi-mass, build x by CRT, then evaluate the inequality EXACTLY from x (true valuations).
(LAP):  sum_{n in J} t^{w(n)+1} <= sum_{n<=L} t^{w(n)}     (PQ'): sum_J f_a(w) <= sum_{[1,L]} g_a(w), z = 1 on S.
Usage: python3 adv_window.py L"""
import sys, math
import numpy as np
def primes_upto(N):
    s=bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2,int(N**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(N+1) if s[i]]
L=int(sys.argv[1]); i_all=np.arange(L, dtype=np.int64)
def build(S, loss):      # loss(c) = mass lost when a position with current count c gets one more hit (>=0)
    c=np.zeros(L, dtype=np.int64); choice={}
    for p in S:
        res=np.mod(i_all,p); w=loss(c)
        tot=np.bincount(res, weights=w, minlength=p)
        cls=int(np.argmin(tot)); choice[p]=cls; c[res==cls]+=1
    x=0; M=1
    for p,cls in choice.items():
        a=(-1-cls)%p; t=((a-x)*pow(M,-1,p))%p; x+=M*t; M*=p
    return x
def true_w(x, S):        # exact valuations of x+1+i for p in S (z=1)
    wI=np.zeros(L); 
    for p in S:
        q=p; idx=i_all
        while True:
            sel=idx[np.mod((x%q)+1+idx, q)==0]
            if len(sel)==0: break
            wI[sel]+=1; idx=sel; q*=p
    return wI
def wK(S):
    v=np.zeros(L+1)
    for p in S:
        q=p
        while q<=L: v[q::q]+=1; q*=p
    return v[1:]
P=primes_upto(L); r=int(math.isqrt(L))
for Sname,S in [("primes<=L/2",[p for p in P if p<=L//2]),("all primes<=L",P)]:
    wk=wK(S)
    for t in (0.003,0.01,0.02,0.05,0.1,0.2,0.4):
        x=build(S, lambda c: (t**(c+1))*(1-t))
        wI=true_w(x,S); lhs=(t**(wI+1)).sum(); rhs=(t**wk).sum()
        print(f"[{Sname}] (LAP) t={t}: LHS={lhs:.2f} RHS={rhs:.2f} slack={(rhs-lhs):.2f} rel={(rhs-lhs)/rhs:.4f}", flush=True)
    for a in (0.5,1.0,1.5,2.0,3.0):
        f=lambda u: np.minimum(1.0, 1.0/np.maximum(a+u,1e-300)) if a>0 else np.where(u==0,1.0,np.minimum(1.0,1.0/np.maximum(u,1e-300)))
        g=lambda u: np.minimum(1.0, 2.0/np.maximum(a+u,1e-300)) if a>0 else np.where(u==0,1.0,np.minimum(1.0,2.0/np.maximum(u,1e-300)))
        x=build(S, lambda c: f(c.astype(float))-f(c.astype(float)+1))
        wI=true_w(x,S); lhs=f(wI).sum(); rhs=g(wk).sum()
        print(f"[{Sname}] (PQ') a={a}: LHS={lhs:.2f} RHS={rhs:.2f} slack={(rhs-lhs):.2f} rel={(rhs-lhs)/rhs:.4f}", flush=True)
