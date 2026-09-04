from itertools import combinations, product
from fractions import Fraction as F
import random, math

print("=== D. Lemma 9: 9-coordinate vertex/cube separation ===")
n=9
pairs=list(combinations(range(n),2))
def L(z): return 7*max(sum(z)-4,0)
def R(z): return sum(max(z[i]+z[j]-1,0) for i,j in pairs)
viol=[]
for v in product([0,1],repeat=n):
    if L(v)>R(v)+1e-12: viol.append(v)
print(" vertices violating 7(t-4)^+ <= sum_pairs (z_i+z_j-1)^+ :", len(viol))
print(" table t: L, R ->", [(t, 7*max(t-4,0), len(list(combinations(range(t),2)))) for t in range(0,10)])
h=[F(1,2)]*n
Lf=7*(F(9,2)-4); Rf=sum(max(h[i]+h[j]-1,F(0)) for i,j in pairs)
print(" z=1/2^9 :  LHS =",Lf,"  RHS =",Rf,"  violation:",Lf>Rf)
# minimise R-L over the cube by random+coordinate descent to confirm 1/2 is (near) worst
best=(1e9,None)
random.seed(1)
for _ in range(4000):
    z=[random.random() for _ in range(n)]
    for _ in range(60):
        i=random.randrange(n)
        cands=[k/40 for k in range(41)]
        vals=[]
        for c in cands:
            z[i]=c; vals.append(R(z)-L(z))
        z[i]=cands[vals.index(min(vals))]
    d=R(z)-L(z)
    if d<best[0]: best=(d,list(z))
print(" min over cube (numeric) R-L =", round(best[0],4), " at z ~", [round(t,3) for t in best[1]])

print()
print("=== E. Lemma 12: positive pair terms ===")
# (a) concrete corollary: baseline c_1=-1, c_p=z_p, c_pq = lam z_p z_q, z_p=z_q=1/2
lam=F(1,3); zp=F(1,2)
val=F(-1)+zp+zp+lam*zp*zp
print(" baseline+lam*z_p z_q at n=pq, z=1/2:  sum_{d|n}c_d =",val," ; (S-1)^+ =",max(zp+zp-1,F(0)),
      " -> infeasible:", val>0)
# (b) literal statement 'A(u,v)>0 impossible' WITHOUT the normalisation: explicit feasible counterexample
# certificate: c_1=-1, c_p=0 all p, c_{pq}=+1 for one fixed pair {p,q}. Check (F) for all subsets Q.
def feas(cdict, zvals, maxsz=6):
    ks=sorted(zvals)
    ok=True; worst=None
    for r in range(len(ks)+1):
        for Q in combinations(ks,r):
            s=sum(zvals[i] for i in Q)
            tot=sum(c for A,c in cdict.items() if set(A)<=set(Q))
            if tot>max(s-1,F(0)):
                ok=False; worst=(Q,tot,max(s-1,F(0)))
    return ok,worst
zv={i:F(1,2) for i in range(6)}
cd={(): F(-1), (0,1): F(1)}
print(" c_1=-1, c_{p1p2}=+1 (a POSITIVE pair term with z_p+z_q=1<=1): feasible for all Q?", feas(cd,zv))
cd2={(): F(-1), (0,1): F(1), (2,3): F(1)}
print(" two positive pair terms +1 each: feasible?", feas(cd2,zv))
cd3={(): F(-1), (0,1): F(1,2)}
print(" c_1=-1, c_{p1p2}=+1/2 with z_i=1/4 (sum of two = 1/2 <1): ",
      feas({(): F(-1), (0,1): F(1,2)}, {i:F(1,4) for i in range(6)}))

print()
print("=== F. Lemma 13: fixed-degree pointwise polynomial ===")
# verify the root argument numerically for d=5, eps=1/5, C=4
import numpy as np
d=5; eps=F(1,5); C=4
print(" q=0..d hinge values:", [(q, max(eps*q-C,F(0)), max(eps*q-1,F(0))) for q in range(d+1)])
print(" both hinges vanish on q=0..d:", all(max(eps*q-1,F(0))==0 for q in range(d+1)))
print(" so P has d+1 roots => P==0; but at q=", math.ceil(C/float(eps))+1, " LHS=",
      float(max(eps*(math.ceil(C/float(eps))+1)-C,F(0))), ">0  => contradiction")
