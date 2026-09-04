# Validate the LP encoding on a tiny instance: threshold r=2, N small.
# Certificate class A ("all-n (F)"):   forall n>=1 : sum_{D|n} c_D <= (S0(n)-1)^+
# Certificate class B ("window (F)"):  forall b in I : sum_{D|b} c_D <= (S0(b)-1)^+
import itertools, numpy as np
from scipy.optimize import linprog

primes=[101,103,107,109,113,127,131,137,139]      # N=9 "selected" primes
N=len(primes); r=2
m = primes[-1]**3                                  # m = z^3 analogue
P = 1
for p in primes: P*=p
# high points: k<=m with >=3 selected primes ; moduli = divisors of high points
# candidate moduli: (subset S of selected primes, |S|>=2) x multiplier u in {1,2,4,3}
mults=[1,2,3,4]
mods=[]
for size in (2,3):
    for S in itertools.combinations(range(N),size):
        prodS=1
        for i in S: prodS*=primes[i]
        for u in mults:
            D=u*prodS
            # is D a divisor of some high point k<=m ?  need k = D * (extra selected primes to reach 3) <= m
            need=3-size
            extra=1; cnt=0
            for i in range(N):
                if cnt==need: break
                if i not in S: extra*=primes[i]; cnt+=1
            if D*extra<=m: mods.append((S,u,D))
idx={ (S,u):j for j,(S,u,D) in enumerate(mods)}
w=np.array([m//D for (S,u,D) in mods],dtype=float)

def solve(constraints):
    A=[];b=[]
    for (Tset,uset,cap) in constraints:
        row=np.zeros(len(mods))
        for j,(S,u,D) in enumerate(mods):
            if set(S)<=Tset and (u in uset): row[j]=1
        A.append(row); b.append(cap)
    res=linprog(-w,A_ub=np.array(A),b_ub=np.array(b),bounds=[(0,None)]*len(mods),method='highs')
    return -res.fun,res

# class A constraints: n = (any subset T of selected primes) x (any multiplier divisibility pattern)
# n divisible by u iff u | n ; take n = 2^2*3*prod(T) to allow every u, and all sub-patterns
consA=[]
for sz in range(0,N+1):
    for T in itertools.combinations(range(N),sz):
        Tset=set(T); cap=max(sz-1,0)
        for uset in [ {1},{1,2},{1,3},{1,2,4},{1,2,3},{1,2,3,4} ]:
            consA.append((Tset,frozenset(uset),cap))
vA,_=solve(consA)

# class B constraints: b in I = {P,...,P+m-1}; S0(P)=N, S0(P+t)=S0(t)<=3 for 1<=t<=m-1.
# b=P: odd, not divisible by 3? P is a product of primes>3 so gcd(P,6)=1 -> only u=1 moduli divide P
consB=[]
consB.append((set(range(N)),frozenset({1}),N-1))
for sz in range(0,4):
    for T in itertools.combinations(range(N),sz):
        cap=max(sz-1,0)
        for uset in [ {1},{1,2},{1,3},{1,2,4},{1,2,3},{1,2,3,4} ]:
            consB.append((set(T),frozenset(uset),cap))
vB,_=solve(consB)

# max spanning tree over pair weights floor(m/(p q))  (matroid prediction for class A)
import heapq
edges=sorted([(m//(primes[i]*primes[j]),i,j) for i in range(N) for j in range(i+1,N)],reverse=True)
par=list(range(N))
def find(x):
    while par[x]!=x: par[x]=par[par[x]]; x=par[x]
    return x
mst=0
for wt,i,j in edges:
    a,b_=find(i),find(j)
    if a!=b_: par[a]=b_; mst+=wt
L=sum(m//(primes[i]*primes[j]*primes[k]) for i in range(N) for j in range(i+1,N) for k in range(j+1,N))
cap6=(N-1)*(m//(primes[0]*primes[1]))
print("tiny instance: N=%d  m=%d  #moduli=%d"%(N,m,len(mods)))
print("  L (exact, threshold 2)            =", L)
print("  class-A LP optimum (all n)        = %.6f"%vA)
print("  max-spanning-forest prediction    =", mst)
print("  Lemma-6-style cap (N-1)*m/(p1p2)  =", cap6)
print("  class-B LP optimum (window only)  = %.6f"%vB)
print("  agreement A == MST :", abs(vA-mst)<1e-6*max(1,mst))
