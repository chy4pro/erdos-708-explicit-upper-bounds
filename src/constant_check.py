#!/usr/bin/env python3
"""Exact budget check for the weighted sieve lemma with theta = 1/(4H) (Q29's Lemma 1): rho*_j = least rho with
Q (4H)^k H^rho / rho! <= 1/(2(k+1)), k = 2^j, j < Q = 1 + floor(log2(R-1)), R = floor(log2 L); A* = sum_{j<Q} 2^{-j}(2^{j+1} + rho*_j - 1) + R 2^{1-Q}.
Reports max (A*+1)/H over L = 2^b, and the same with H_RS = max(4, lnln L + B1 + 1/(ln L)^2)."""
import math
B1=0.2614972128476427837554268386086958590516
def rho_star(Q,H,k):
    lhs=math.log(Q)+k*math.log(4*H)+math.log(2*(k+1))
    f=lambda rho: lhs+rho*math.log(H)-math.lgamma(rho+1)
    lo,hi=0,8
    while f(hi)>0: hi*=2
    while hi-lo>1:
        mid=(lo+hi)//2
        if f(mid)>0: lo=mid
        else: hi=mid
    return hi if f(lo)>0 else lo
def budget(L_ln, R, Hfun):
    H=Hfun(L_ln); Q=1+int(math.floor(math.log2(R-1))) if R>=2 else 1
    A=0.0
    for j in range(Q):
        k=2**j
        if k>R-1: break
        A+=2.0**(-j)*(2*k+rho_star(Q,H,k)-1)
    A+=R*2.0**(1-Q)
    return (A+1)/H, H, Q
H1=lambda lnL: math.e*math.log(1+lnL)
HRS=lambda lnL: max(4.0, math.log(lnL)+B1+1/lnL**2)
for name,Hf in (("H=e ln(1+ln L)",H1),("H_RS",HRS)):
    worst=(0,None); worst_small=(0,None)
    for b in list(range(4,2000))+list(range(2000,200001,97)):
        lnL=b*math.log(2); r,H,Q=budget(lnL,b,Hf)
        if r>worst[0]: worst=(r,(b,round(H,2),Q))
    print(f"{name}: max (A*+1)/H over b in 4..200000 = {worst[0]:.4f} at (b,H,Q)={worst[1]}")
    for b in (4,5,6,8,10,16,32,100,1000,10000,100000,200000):
        r,H,Q=budget(b*math.log(2),b,Hf); print(f"   b={b}: ratio={r:.3f} H={H:.2f} Q={Q}")

# --- scan H within each R-range: for fixed R=b, L in [2^b, 2^{b+1}) so lnL in [b ln2, (b+1) ln2); the ratio depends on (b, H(lnL)) only
import sys
if len(sys.argv)>1 and sys.argv[1]=='scan':
    for name,Hf in (("H=e ln(1+ln L)",H1),("H_RS",HRS)):
        worst=(0,None)
        for b in list(range(4,300))+list(range(300,5000,23))+list(range(5000,200001,1997)):
            lo=b*math.log(2); hi=(b+1)*math.log(2)
            for t in range(0,12):
                lnL=lo+(hi-lo)*t/12; r,H,Q=budget(lnL,b,Hf)
                if r>worst[0]: worst=(r,(b,t,round(H,3),Q))
        print(f"SCAN {name}: sup (A*+1)/H = {worst[0]:.4f} at (b, t/40, H, Q) = {worst[1]}")
