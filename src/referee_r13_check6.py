from fractions import Fraction as F
from itertools import combinations
import random, math
from functools import reduce

print("=== G. Lemma 17: sliding-window certificate ===")

def sliding(alphas):
    """alphas: list of Fractions (atom lengths) in the fixed order.
       Returns dict A(frozenset of indices) -> Lebesgue measure c_A (Fraction)."""
    Z=sum(alphas); n=len(alphas)
    ends=[F(0)]*(n+1)
    for i,a in enumerate(alphas): ends[i+1]=ends[i]+a
    if Z<1: return {}
    # breakpoints of t -> A_t on [0, Z-1]: at ends[i] and ends[i]-1
    bps=set([F(0),Z-1])
    for e in ends:
        if 0<=e<=Z-1: bps.add(e)
        if 0<=e-1<=Z-1: bps.add(e-1)
    bps=sorted(bps)
    c={}
    for u,v in zip(bps,bps[1:]):
        if v<=u: continue
        t=(u+v)/2
        A=frozenset(i for i in range(n) if ends[i]<t+1 and ends[i+1]>t)  # J_i=(ends[i],ends[i+1]) meets (t,t+1)
        c[A]=c.get(A,F(0))+(v-u)
    return c

def Fsigma_runs(alphas, Q):
    """sum over maximal runs of (len-1)^+"""
    tot=F(0); cur=F(0)
    for i,a in enumerate(alphas):
        if i in Q: cur+=a
        else:
            tot+=max(cur-1,F(0)); cur=F(0)
    tot+=max(cur-1,F(0))
    return tot

random.seed(11)
allok=True
for trial in range(300):
    n=random.randint(2,8)
    alphas=[F(random.randint(1,9),random.randint(1,6)) for _ in range(n)]
    c=sliding(alphas)
    # (a) nonnegativity
    if any(v<0 for v in c.values()): print("NEG COEFF"); allok=False
    # (b) identity (12.2)/(12.3) and feasibility (12.4) for every subset Q
    for r in range(n+1):
        for Q in combinations(range(n),r):
            Qs=set(Q)
            lhs=sum(v for A,v in c.items() if set(A)<=Qs)
            rhs=Fsigma_runs(alphas,Qs)
            if lhs!=rhs: print("  (12.3) MISMATCH",alphas,Q,lhs,rhs); allok=False
            S=sum(alphas[i] for i in Q)
            if lhs>max(S-1,F(0)): print("  (12.4) INFEASIBLE",alphas,Q,lhs,S); allok=False
print(" 300 random atom systems, all subsets:  nonneg + run-formula (12.3) + F_sigma<=(S-1)^+ (12.4):", allok)

# degenerate case: zero-length atoms
alphas=[F(2),F(0),F(2)]
c=sliding(alphas)
Q={0,2}
lhs=sum(v for A,v in c.items() if set(A)<=Q); rhs=Fsigma_runs(alphas,Q)
print(" zero-length atom in the middle, Q={0,2}:  sum_{A<=Q}c_A =",lhs," run formula =",rhs,
      " -> identity (12.2)/(12.3) FAILS unless alpha=0 atoms are discarded:", lhs!=rhs)

print()
print("=== H. Lemma 17 as a DIVISOR certificate: lcm merge, (F), and V(c)=sum_{k<=m}F_sigma(k) ===")
def lcm(a,b): return a*b//math.gcd(a,b)
def build_divisor_cert(mods, alphas):
    c=sliding(alphas); cd={}
    for A,v in c.items():
        d=reduce(lcm,[mods[i] for i in A],1)
        cd[d]=cd.get(d,F(0))+v
    return cd
def Sfun(n, mods, alphas):
    return sum(alphas[i] for i in range(len(mods)) if n%mods[i]==0)

for (mods,alphas,m) in [([2,3,5,7],[F(1,2)]*4,2000),
                        ([2,3,5,7,11,13],[F(3,4),F(1,2),F(1),F(1,3),F(1),F(2,3)],5000),
                        ([4,9,5,7,11],[F(1),F(1),F(1,2),F(1,2),F(1)],3000)]:
    cd=build_divisor_cert(mods,alphas)
    neg=[d for d,v in cd.items() if v<0]
    # (F) for all n up to a big bound (values only depend on divisibility pattern -> test all patterns)
    bad=0
    for r in range(len(mods)+1):
        for Q in combinations(range(len(mods)),r):
            n=reduce(lcm,[mods[i] for i in Q],1)
            tot=sum(v for d,v in cd.items() if n%d==0)
            S=sum(alphas[i] for i in Q)
            if tot>max(S-1,F(0)): bad+=1
    V=sum(v*(m//d) for d,v in cd.items())
    tot=sum(Sfun(k,mods,alphas) for k in range(1,m+1))
    Fs=F(0)
    for k in range(1,m+1):
        Q=set(i for i in range(len(mods)) if k%mods[i]==0)
        Fs+=Fsigma_runs(alphas,Q)
    print(f" mods={mods}: neg coeffs={len(neg)}  (F) violations={bad}  V(c)={V}  sum_k F_sigma(k)={Fs}  equal={V==Fs}")
