#!/usr/bin/env python3
"""LP relaxation of abstract_count_ilp.py with dual certificate.  min sum_t n_t (w(t)-1)^+  s.t.  floor(m/d) <= N(d) <= floor(m/d)+1
(N(1) = m), n_t >= 0 real.  If the LP minimum >= true K-side, an explicit dual certificate proves (TH) for this (m,P,z) from
counting alone; we print the multipliers: mu_d (on N(d) >= floor(m/d)) and lam_d (on N(d) <= floor(m/d)+1).
Usage: python3 abstract_count_lp.py m p1 p2 ... [--z ...]"""
import sys, math, itertools
import numpy as np
from scipy.optimize import linprog
args=sys.argv[1:]; m=int(args[0])
if '--z' in args:
    i=args.index('--z'); P=[int(a) for a in args[1:i]]; Z=[float(a) for a in args[i+1:]]
else: P=[int(a) for a in args[1:]]; Z=[1.0]*len(P)
E=[int(math.log(m,p))+1 for p in P]
types=list(itertools.product(*[range(e+1) for e in E])); T=len(types)
w=lambda t: sum(z*a for z,a in zip(Z,t)); dval=lambda d: math.prod(p**a for p,a in zip(P,d))
def divides(d,t): return all(a<=b for a,b in zip(d,t))
A=np.array([[1.0 if divides(d,t) else 0.0 for t in types] for d in types]); q=np.array([m//dval(d) for d in types],float)
one=tuple([0]*len(P)); i1=types.index(one)
# constraints: -A n <= -q  (lower), A n <= q+1 (upper, except d=1 where equality)
Aub=np.vstack([-A, A]); bub=np.concatenate([-q, q+1]); bub[T+i1]=m
c=np.array([max(0.0,w(t)-1.0) for t in types])
res=linprog(c, A_ub=Aub, b_ub=bub, bounds=[(0,None)]*T, method='highs')
def vp(n,p):
    k=0
    while n%p==0: n//=p; k+=1
    return k
K=sum(max(0.0, w(tuple(min(vp(k,p),e) for p,e in zip(P,E)))-2.0) for k in range(1,m+1))
print(f"m={m} P={P} z={Z}: LP min = {res.fun:.3f} vs K-side {K:.3f} -> {'LP CERTIFICATE EXISTS' if res.fun>=K-1e-9 else 'LP relaxation below K-side'}")
duals=-res.ineqlin.marginals   # >= 0 multipliers for A_ub n <= b_ub
mu=duals[:T]; lam=duals[T:]
nz=[(types[j], dval(types[j]), round(mu[j],3), round(lam[j],3)) for j in range(T) if mu[j]>1e-9 or lam[j]>1e-9]
nz.sort(key=lambda r:r[1])
print("  nonzero multipliers (type, d, mu_lower, lam_upper):"); 
for r in nz[:40]: print("   ", r)
print(f"  #nonzero: mu {int((mu>1e-9).sum())}, lam {int((lam>1e-9).sum())}; certificate value = sum mu*q - sum lam*(q+1) = {float(mu@q - lam@(q+1) + lam[i1]*(q[i1]+1-m)):.3f}")
