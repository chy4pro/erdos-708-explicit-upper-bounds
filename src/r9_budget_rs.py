#!/usr/bin/env python3
"""What P25's geometric-layer budget would give if H = e ln(1+ln L) were replaced by the Rosser-Schoenfeld bound
H_RS = ln ln L + B1 + 1/(2 ln^2 L), B1 = 0.2614972128 (Theorem 5 of Rosser-Schoenfeld 1962, valid for L > 1),
with a floor H >= Hmin so that the auxiliary inequalities stay valid. Everything else exactly as in r9_budget_check.py.
Reports sup (B_L + 3)/lnln L and (B_L + 3)/H."""
import math, sys
q=51/50; delta=1/50; B1=0.2614972128
def layers(R):
    ks=[]; j=0
    while True:
        k=math.ceil(q**j)
        if k>R-1: break
        ks.append(k); j+=1
    return ks
def rho_of(H,G,k):
    h0=math.e*H; A=math.log(4*G)+k*math.log(8*H)
    s=min(A, 2*A/math.log(2+A/h0))
    rho=math.ceil(h0+s)
    ok = math.lgamma(rho+1) >= math.log(4*G)+k*math.log(8*H)+rho*math.log(H)-1e-9
    return rho, ok
def budget(lnL, Hmin):
    H=max(Hmin, math.log(lnL)+B1+1/(2*lnL*lnL)); R=int(math.floor(lnL/math.log(2)))
    ks=layers(R); Q=len(ks); B=0.0; allok=True
    for j,k in enumerate(ks):
        rho,ok=rho_of(H,Q,k); allok&=ok; B+=delta*q**(-j)*(2*k+rho)
    return H,R,Q,B,allok
for Hmin in (2.0, 3.0, 4.0):
    worst=(0,None); worstH=(0,None)
    for b in list(range(16,400))+list(range(400,3000,13))+list(range(3000,200001,997)):
        lnL=b*math.log(2); H,R,Q,B,ok=budget(lnL,Hmin)
        if not ok: print("FACTORIAL CONDITION FAILS", b); break
        lnln=math.log(lnL)
        if lnln>0 and (B+3)/lnln>worst[0]: worst=((B+3)/lnln,(b,round(H,2),Q))
        if (B+3)/H>worstH[0]: worstH=((B+3)/H,(b,round(H,2),Q))
    print(f"Hmin={Hmin}: sup (B+3)/lnlnL = {worst[0]:.3f} at {worst[1]};  sup (B+3)/H = {worstH[0]:.3f} at {worstH[1]}")
    for b in (64,100,200,1000,10000,200000):
        H,R,Q,B,ok=budget(b*math.log(2),Hmin); print(f"   b={b}: H={H:.2f} Q={Q} B+3={B+3:.1f}  (B+3)/lnlnL={(B+3)/math.log(b*math.log(2)):.2f}")
