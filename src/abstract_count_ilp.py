#!/usr/bin/env python3
"""Can (TH) be proved from multiples-counting alone?  Abstract 'interval-like' multisets: choose counts n_t >= 0 of valuation
types t = (a_p)_{p in P}, 0 <= a_p <= e_p, subject to N(d) := sum_{t : d | t} n_t in {floor(m/d), floor(m/d)+1} for every d and
sum n_t = m; minimise sum_t n_t (w(t)-1)^+ and compare with the true K-side sum_{k<=m} (w(k)-2)^+ (exponents capped the same way).
If the minimum is below the K-side, no argument using only N_I(d) >= floor(m/d) (and <= +1) can prove (TH).
Usage: python3 abstract_count_ilp.py m p1 p2 ... [--z z1 z2 ...]"""
import sys, math, itertools
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
args=sys.argv[1:]; m=int(args[0]); 
if '--z' in args:
    i=args.index('--z'); P=[int(a) for a in args[1:i]]; Z=[float(a) for a in args[i+1:]]
else: P=[int(a) for a in args[1:]]; Z=[1.0]*len(P)
E=[int(math.log(m,p))+1 for p in P]
types=list(itertools.product(*[range(e+1) for e in E])); T=len(types)
w=lambda t: sum(z*a for z,a in zip(Z,t))
def divides(d,t): return all(a<=b for a,b in zip(d,t))
def dval(d): return math.prod(p**a for p,a in zip(P,d))
rows=[]; lo=[]; hi=[]
for d in types:
    row=np.array([1.0 if divides(d,t) else 0.0 for t in types]); q=m//dval(d)
    rows.append(row); lo.append(q); hi.append(q+1 if d!=tuple([0]*len(P)) else m)
A=np.array(rows); c=np.array([max(0.0,w(t)-1.0) for t in types])
res=milp(c=c, constraints=LinearConstraint(A,np.array(lo,float),np.array(hi,float)), integrality=np.ones(T), bounds=Bounds(0,m))
# true K-side with the same capping
def vp(n,p):
    c=0
    while n%p==0: n//=p; c+=1
    return c
K=sum(max(0.0, w(tuple(min(vp(k,p),e) for p,e in zip(P,E)))-2.0) for k in range(1,m+1))
Kside_real=sum(max(0.0, sum(z*vp(k,p) for z,p in zip(Z,P))-2.0) for k in range(1,m+1))
print(f"m={m} P={P} z={Z} caps={E} types={T}: abstract min RHS = {res.fun:.3f} (status {res.status}); true K-side (capped) = {K:.3f}, real = {Kside_real:.3f} -> {'COUNTING ALONE CANNOT PROVE (TH)' if res.fun < K-1e-9 else 'counting suffices here'}")
if res.fun < K-1e-9:
    sol=res.x.round().astype(int)
    print("  abstract multiset (type:count) for types with count>0 and w>=1:", [(types[i],int(sol[i])) for i in range(T) if sol[i]>0 and w(types[i])>=1][:12])
