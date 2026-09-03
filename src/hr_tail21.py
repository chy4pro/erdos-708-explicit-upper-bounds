#!/usr/bin/env python3
"""Same centred-sieve construction as hr_construct.py, then evaluate P20's (Tail21) with Q = primes <= m/2, L = m, y = x:
LHS = #{n<=m : omega_Q(n)>=2}, RHS = #{b in I : omega_Q(b)>=1} = m - #rough.  Usage: python3 hr_tail21.py m"""
import sys, math
import numpy as np
def primes_upto(N):
    s=bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2,int(N**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(N+1) if s[i]]
m=int(sys.argv[1]); P=primes_upto(m//2); pi_m=len(primes_upto(m)); h=m//2
n=np.arange(-h, m-h, dtype=np.int64); alive=np.ones(m, dtype=bool); choice={}; r=int(math.isqrt(m))
for p in P:
    if p<=r: cls=0
    else:
        cnt=np.bincount(np.mod(n[alive], p), minlength=p); cls=int(np.argmin(cnt))
    choice[p]=cls; alive &= (np.mod(n, p)!=cls)
surv=int(alive.sum())
x=0; M=1
for p,cls in choice.items():
    a=(-1-h-cls)%p; t=((a-x)*pow(M,-1,p))%p; x+=M*t; M*=p
rough=np.ones(m, dtype=bool); i=np.arange(m, dtype=np.int64)
for p in P: rough &= (np.mod((x%p)+1+i, p)!=0)
R=int(rough.sum()); assert R==surv
# omega_Q on [1,m]
om=np.zeros(m+1, dtype=np.int64)
for p in P: om[p::p]+=1
lhs=int((om[1:]>=2).sum()); rhs=m-R
print(f"m={m}: rough count |T|={R}, pi(m)+1={pi_m+1}, (NM) violated: {R>pi_m+1}; (Tail21) with Q=primes<=m/2: LHS={lhs} RHS={rhs} -> {'VIOLATED' if lhs>rhs else 'holds'} (x has {len(str(x))} digits)")
if R>pi_m+1 or lhs>rhs:
    with open(f"nm_counterexample_m{m}.txt","w") as f:
        f.write(f"# centred-sieve window: m={m}, |T|={R} integers in I=[x+1,x+m] with no prime factor <= m/2, pi(m)={pi_m}; (Tail21) LHS={lhs} RHS={rhs}\nm={m}\nx={x}\n")
