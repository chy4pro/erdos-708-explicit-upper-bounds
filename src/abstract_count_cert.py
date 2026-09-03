#!/usr/bin/env python3
"""Print the full dual certificate of the sparse counting LP (see abstract_count_lp2.py). Usage: same."""
import sys, math, itertools
import numpy as np
from scipy.sparse import lil_matrix, csr_matrix, vstack
from scipy.optimize import linprog
args=sys.argv[1:]; m=int(args[0])
if '--z' in args:
    i=args.index('--z'); P=[int(a) for a in args[1:i]]; Z=[float(a) for a in args[i+1:]]
else: P=[int(a) for a in args[1:]]; Z=[1.0]*len(P)
E=[int(math.log(m,p))+1 for p in P]
types=list(itertools.product(*[range(e+1) for e in E])); T=len(types); idx={t:i for i,t in enumerate(types)}
w=lambda t: sum(z*a for z,a in zip(Z,t)); dval=lambda d: math.prod(p**a for p,a in zip(P,d))
A=lil_matrix((T,T))
for j,t in enumerate(types):
    for d in itertools.product(*[range(a+1) for a in t]): A[idx[d],j]=1.0
A=csr_matrix(A); q=np.array([m//dval(d) for d in types],float); i1=idx[tuple([0]*len(P))]
Aub=vstack([-A, A]).tocsr(); bub=np.concatenate([-q, q+1]); bub[T+i1]=m
c=np.array([max(0.0,w(t)-1.0) for t in types])
res=linprog(c, A_ub=Aub, b_ub=bub, bounds=[(0,None)]*T, method='highs')
duals=-res.ineqlin.marginals; mu=duals[:T]; lam=duals[T:]
def vp(n,p):
    k=0
    while n%p==0: n//=p; k+=1
    return k
K=sum(max(0.0, w(tuple(min(vp(k,p),e) for p,e in zip(P,E)))-2.0) for k in range(1,m+1))
print(f"m={m} P={P} z={Z}: LP min {res.fun:.3f} >= K-side {K:.3f}")
rows=[(dval(types[j]), types[j], mu[j], lam[j]) for j in range(T) if mu[j]>1e-9 or lam[j]>1e-9]
rows.sort()
for d,t,a,b in rows: print(f"   d={d:5d} exps={t}  mu={a:.3f}  lam={b:.3f}")
