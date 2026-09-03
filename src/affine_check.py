#!/usr/bin/env python3
"""Corollary 'trivial regime' (paper v7, Section 8): the affine certificate c_1 = -1, c_{p^j} = z_p gives
sum_{b in I} (w(b)-1)^+ >= sum_{k<=m} w(k) - m for every window I of length m.  For 0/1 weights (distinct-prime version) it
proves the threshold-2 hinge inequality whenever #{k<=m : w(k)=0} <= #{k<=m : w(k)>=2}.
Prints, for P = all primes <= m, the affine value against W_omega = sum (omega-2)^+ (m = 300, 500, 1000), and for
P = primes in [53,653], m = 10^8, the counts showing that the affine bound is negative there (anchors are needed).
Usage: python3 affine_check.py [--big]"""
import sys, numpy as np
def primes_upto(N):
    s=np.ones(N+1,bool); s[:2]=False
    for i in range(2,int(N**.5)+1):
        if s[i]: s[i*i::i]=False
    return [int(p) for p in np.nonzero(s)[0]]
def omega_counts(m,P):
    w=np.zeros(m+1,np.int8)
    for p in P: w[p::p]+=1
    return w[1:]
for m in (300,500,1000):
    w=omega_counts(m,primes_upto(m)).astype(np.int64)
    W=int(np.maximum(w-2,0).sum()); V=int(w.sum())-m; Pi=int((w==1).sum())
    print(f"m={m}: W_omega={W}  V_affine={V}  V-W={V-W}  (= m-2-Pi(m) with Pi={Pi}: {m-2-Pi})")
if "--big" in sys.argv:
    m=10**8; P=[p for p in primes_upto(653) if p>=53]; w=omega_counts(m,P)
    n0=int((w==0).sum()); n2=int((w>=2).sum()); W=int(np.maximum(w.astype(np.int32)-2,0).sum()); V=int(w.astype(np.int64).sum())-m
    print(f"P=[53,653], m=1e8: #w=0 {n0}  #w>=2 {n2}  W_omega {W}  V_affine {V}")
