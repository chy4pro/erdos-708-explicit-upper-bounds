#!/usr/bin/env python3
"""Independent recomputation of P25's budget: q=51/50 geometric layers k_j=ceil(q^j) (k_j <= R-1), Q = #layers, H = e h, h = ln(1+ln L),
rho(H,G,k) = ceil(h0 + s(A)) with h0 = eH, A = ln(4G) + k ln(8H), s(A) = min(A, 2A/ln(2+A/h0))  [no square root: corrected 09-04 after referee], G = Q;
B_L = sum_j alpha_j (2 k_j + rho_j), alpha_j = delta q^{-j}, delta = 1/50.  Check B_L + 3 < 19.24 h and the scalar inequality l J(h)/h < 5.
Also verify rho satisfies rho! >= 4G (8H)^k H^rho via lgamma."""
import math
q=51/50; delta=1/50
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
    # verify factorial condition rho! >= 4G (8H)^k H^rho
    ok = math.lgamma(rho+1) >= math.log(4*G)+k*math.log(8*H)+rho*math.log(H)-1e-9
    return rho, ok
def budget(lnL):
    h=math.log(1+lnL); H=math.e*h; R=int(math.floor(lnL/math.log(2)))
    ks=layers(R); Q=len(ks); B=0.0; allok=True
    for j,k in enumerate(ks):
        rho,ok=rho_of(H,Q,k); allok&=ok; B+=delta*q**(-j)*(2*k+rho)
    return h,H,R,Q,B,allok
worst=(0,None)
for b in list(range(77,400))+list(range(400,3000,13))+list(range(3000,200001,997)):
    for t in range(0,6):
        lnL=(b+t/6)*math.log(2); h,H,R,Q,B,ok=budget(lnL)
        if h<4: continue
        r=(B+3)/h
        if not ok: print("FACTORIAL CONDITION FAILS", b, t)
        if r>worst[0]: worst=(r,(b,t,round(h,3),Q,R))
print(f"sup (B_L+3)/h over h>=4 (b in 77..200000) = {worst[0]:.4f} at {worst[1]}   (claimed < 19.24)")
for b in (77,100,200,500,1000,10000,100000,200000):
    h,H,R,Q,B,ok=budget(b*math.log(2)); print(f"  b={b}: h={h:.3f} Q={Q} (B+3)/h={(B+3)/h:.3f} ok={ok}")
# scalar inequality l J(h)/h < 5 for 4<=h<=8, with l = ln(8 e h), v0 = e^2-2, J(h) = ln(v0 e^2 h / l) + 2 ln((h-1.5)/ln v0)
v0=math.e**2-2; mx=0
for i in range(0,40001):
    h=4+4*i/40000; l=math.log(8*math.e*h); J=math.log(v0*math.e**2*h/l)+2*math.log((h-1.5)/math.log(v0)); mx=max(mx,l*J/h)
print(f"max of l J(h)/h on [4,8] (fine grid) = {mx:.4f} (claimed < 5, engine bound 4.9652 on [4.40,4.45])")
# analytic tail for h>=8: (y+3.08)(3y+1.01)e^{-y} at y = ln 8
y=math.log(8); print(f"(y+3.08)(3y+1.01)e^-y at y=ln8: {(y+3.08)*(3*y+1.01)*math.exp(-y):.4f} (claimed < 4.677)")
