#!/usr/bin/env python3
"""Numerical test of P19's hinge inequalities for Erdős #708.
(TH): for all m, x >= 0 and weights 0 <= z_p <= 1 (w(k) = sum_p z_p v_p(k)):  sum_{k<=m} (w(k)-2)^+ <= sum_{b=x+1}^{x+m} (w(b)-1)^+.
(BH): same with the LHS restricted to any A subset of [1,m] (implied by TH).  Random and adversarial z (0/1 vectors on prime
subsets, all ones, single primes, halves), m <= 400, x random / structured. Reports the minimum slack RHS-LHS."""
import random, math, time, sys
from es_bound import factor
def primes_upto(N):
    s=bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2,int(N**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(N+1) if s[i]]
def w_of(k, z):
    return sum(z.get(p,0.0)*e for p,e in factor(k).items())
random.seed(3); t0=time.time(); worst=(1e9,None); tests=0
while time.time()-t0 < float(sys.argv[1]) if len(sys.argv)>1 else 240:
    m=random.randint(2,400); x=random.choice([0, random.randint(0,10**6), random.randint(0,10**12), (math.lcm(*range(2,min(m,30)))-m//2)])
    if x<0: x=0
    P=primes_upto(m)
    mode=random.random()
    if mode<0.25: z={p:1.0 for p in P}
    elif mode<0.5: z={p:1.0 for p in P if random.random()<0.5}
    elif mode<0.7: z={p:random.random() for p in P}
    elif mode<0.85: z={p:1.0 for p in P if p<=random.choice([3,5,7,11,13,30])}
    else: z={p:random.choice([0.0,0.5,1.0]) for p in P}
    # include primes > m dividing elements of I (they also count with z_p <= 1; choose z=1 for them adversarially)
    L=sum(max(0.0, w_of(k,z)-2) for k in range(1,m+1))
    R=0.0
    for b in range(x+1,x+m+1):
        wb=sum(z.get(p, 1.0 if p>m else 0.0)*e for p,e in factor(b).items())  # primes > m get z=1 (worst for nothing: they only increase RHS)
        R+=max(0.0,wb-1)
    tests+=1; slack=R-L
    if slack<worst[0]: worst=(slack,(m,x,mode)); print(f"new min slack {slack:.3f} at m={m} x={x} mode={mode:.2f}", flush=True)
print(f"tests={tests}; minimum slack RHS-LHS = {worst[0]:.3f} at {worst[1]}  (negative would refute (TH))")
