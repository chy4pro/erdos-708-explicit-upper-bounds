#!/usr/bin/env python3
"""GRAPH CERTIFICATE for the 0/1 hinge inequality (TH) with prime set P (all primes <= m by default), from counting alone.
Find mu_e >= 0 on pairs e = pq (pq <= m) and lam_t >= 0 on triples t = pqr such that for every S subset of P:
   sum_{e subset S} mu_e - sum_{t subset S} lam_t <= (|S|-1)^+                                   (feasibility)
and maximise V = sum_e mu_e floor(m/e) - sum_t lam_t (floor(m/t)+1).  If V >= sum_{k<=m} (omega_P(k)-2)^+ then (TH) holds for
(m, P, z = 1_P) and EVERY x, because N_I(e) >= floor(m/e) and N_I(t) <= floor(m/t)+1 (with (Omega-omega) handled exactly by
prime-power counts).  Constraint generation: separation = MILP over subsets S.  Usage: python3 graph_cert.py m [pmax]"""
import sys, math, itertools, time
import numpy as np
from scipy.optimize import linprog, milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix, csr_matrix
m=int(sys.argv[1]); spec=sys.argv[2] if len(sys.argv)>2 else "all"; ITCAP=int(sys.argv[3]) if len(sys.argv)>3 else 400
import random
def primes_upto(N):
    s=bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2,int(N**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(N+1) if s[i]]
PP=primes_upto(m)
if spec=="all": P=PP
elif spec.startswith("le:"): P=[p for p in PP if p<=int(spec[3:])]
elif spec.startswith("range:"): a,b=map(int,spec[6:].split(":")); P=[p for p in PP if a<=p<=b]
elif spec.startswith("random:"): sd,dens=spec[7:].split(":"); random.seed(int(sd)); P=[p for p in PP if random.random()<float(dens)]
elif spec.startswith("no:"): ex=set(map(int,spec[3:].split(","))); P=[p for p in PP if p not in ex]
n=len(P)
E=[(i,j) for i in range(n) for j in range(i+1,n) if P[i]*P[j]<=m]
TCAP=float(sys.argv[4]) if len(sys.argv)>4 else 3.0
Tr=[(i,j,k) for i in range(n) for j in range(i+1,n) for k in range(j+1,n) if P[i]*P[j]*P[k]<=TCAP*m]   # triples up to TCAP*m (cost 1 each)
nv=len(E)+len(Tr); cE=np.array([m//(P[i]*P[j]) for i,j in E],float); cT=np.array([m//(P[i]*P[j]*P[k])+1 for i,j,k in Tr],float)
obj=-np.concatenate([cE,-cT])   # linprog minimises: minimise -V
def omega_target():
    tot=0
    for k in range(1,m+1):
        w=sum(1 for p in P if k%p==0); tot+=max(0,w-2)
    return tot
target=omega_target()
# constraint rows: for subset S (as index list): sum mu_e [e in S] - sum lam_t [t in S] <= |S|-1 (S nonempty)
rows=[]; rhs=[]
def add_S(S):
    Sset=set(S); r=np.zeros(nv)
    for a,(i,j) in enumerate(E):
        if i in Sset and j in Sset: r[a]=1
    for b,(i,j,k) in enumerate(Tr):
        if i in Sset and j in Sset and k in Sset: r[len(E)+b]=-1
    rows.append(r); rhs.append(max(0,len(S)-1))
# seed: all pairs and triples and 4-sets among small primes
for (i,j) in E: add_S((i,j))
for (i,j,k) in Tr: add_S((i,j,k))
for S in itertools.combinations(range(min(n,7)),4): add_S(S)
t0=time.time(); it=0
while True:
    it+=1
    res=linprog(obj, A_ub=np.array(rows), b_ub=np.array(rhs,float), bounds=[(0,1)]*len(E)+[(0,None)]*len(Tr), method='highs')
    mu=res.x[:len(E)]; lam=res.x[len(E):]; V=-res.fun
    # separation MILP: y_p in {0,1}, x_e <= y_i, y_j ; x_e binary; t-var z_t >= y_i+y_j+y_k-2 ; maximise sum mu x_e - sum lam z_t - sum y_p + 1
    ny=n; nx=len(E); nz=len(Tr); N=ny+nx+nz
    c=np.zeros(N); c[:ny]=1.0; c[ny:ny+nx]=-mu; c[ny+nx:]=lam      # minimise -(sum mu x - sum lam z - sum y + 1)
    A=lil_matrix((2*nx+nz, N)); lo=[]; hi=[]
    r=0
    for a,(i,j) in enumerate(E):
        A[r,ny+a]=1; A[r,i]=-1; lo.append(-np.inf); hi.append(0); r+=1
        A[r,ny+a]=1; A[r,j]=-1; lo.append(-np.inf); hi.append(0); r+=1
    for b,(i,j,k) in enumerate(Tr):
        A[r,ny+nx+b]=-1; A[r,i]=1; A[r,j]=1; A[r,k]=1; lo.append(-np.inf); hi.append(2); r+=1
    sep=milp(c=c, constraints=LinearConstraint(csr_matrix(A), np.array(lo), np.array(hi,float)), integrality=np.ones(N), bounds=Bounds(0,1))
    viol=-(sep.fun)+1   # = max(sum mu x - sum lam z - sum y) + 1
    S=[i for i in range(ny) if sep.x[i]>0.5]
    if viol<=1e-7 or len(S)==0:
        break
    add_S(S)
    if it>ITCAP: print("ITERATION CAP HIT — certificate NOT verified"); break
print(f"m={m} P={spec} (|P|={n}, pairs {len(E)}, triples {len(Tr)}): V*={V:.3f} vs target sum_K(omega-2)^+={target} -> {'CERTIFICATE (0/1 TH proved for all x)' if V>=target-1e-7 else 'NO graph certificate'}; iters={it}, cuts={len(rows)}, {time.time()-t0:.0f}s")
nzmu=[(P[i]*P[j],round(mu[a],3)) for a,(i,j) in enumerate(E) if mu[a]>1e-6]; nzl=[(P[i]*P[j]*P[k],round(lam[b],3)) for b,(i,j,k) in enumerate(Tr) if lam[b]>1e-6]
print("  mu:",nzmu[:40]); print("  lam:",nzl[:30])
