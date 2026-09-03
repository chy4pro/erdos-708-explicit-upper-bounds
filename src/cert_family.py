#!/usr/bin/env python3
"""Certificate family C_r for the 0/1 hinge inequality with P = all primes <= m (the hardest 0/1 case).
R = first r primes.  c_d = (-1)^{omega(d)} for squarefree d = prod(A') with A' subset R, |A'| >= 2, and for d = q*prod(A') with q a
prime not in R, A' subset R nonempty (sign (-1)^{|A'|+1}).  Dual feasibility (proved): for T = A ∪ Q, sum = (|A|-1)^+ + |Q|[A≠∅] <= |T|-1.
Value V_r = sum_{c_d>0} c_d floor(m/d) - sum_{c_d<0} |c_d| (floor(m/d)+1)  [every negative term costs +1 for the possible extra multiple;
terms with d > m: floor = 0, cost 1 if negative, 0 gain if positive -> drop positive d > m].  Target W = sum_{k<=m} (omega(k)-2)^+.
Also the trivial star (r=1: edges 2q only) and the forest bound.  Usage: python3 cert_family.py m rmax"""
import sys, math, itertools
m=int(sys.argv[1]); rmax=int(sys.argv[2])
def primes_upto(N):
    s=bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2,int(N**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(N+1) if s[i]]
P=primes_upto(m)
# W = sum_{k<=m} (omega(k)-2)^+ via sieve of omega
om=[0]*(m+1)
for p in P:
    for k in range(p,m+1,p): om[k]+=1
W=sum(max(0,o-2) for o in om[1:])
print(f"m={m}: W = sum_K (omega-2)^+ = {W}; pi(m)={len(P)}")
for r in range(1,rmax+1):
    R=P[:r]; Rset=set(R); V=0
    # internal terms: A' subset R, |A'|>=2
    for k in range(2,r+1):
        for Ap in itertools.combinations(R,k):
            d=math.prod(Ap); sign=(-1)**k
            if sign>0: V+= m//d
            else: V-= (m//d+1)
    # mixed terms: q not in R, A' subset R nonempty, sign (-1)^{|A'|+1}
    for q in P[r:]:
        for k in range(1,r+1):
            for Ap in itertools.combinations(R,k):
                d=q*math.prod(Ap); sign=(-1)**(k+1)
                if sign>0: V+= m//d
                else: V-= (m//d+1)
    print(f"  r={r} (R={R}): V_r = {V}  ->  {'OK (>= W)' if V>=W else 'short by '+str(W-V)}")
