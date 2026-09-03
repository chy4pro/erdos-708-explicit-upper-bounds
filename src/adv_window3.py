#!/usr/bin/env python3
"""Large-L adversary for (LAP) sum_{n in J} t^{w(n)+1} <= sum_{n<=L} t^{w(n)} (z=1 on all primes <= L).
Centred coordinates; class 0 for p <= sqrt(L); for larger p choose the class minimising the (LAP) loss over positions with
c <= 1 (weights t^{c+1}); CRT; exact valuations on the window by slice updates using x mod p^j. Usage: python3 adv_window3.py L t_greedy [t_eval ...]"""
import sys, math, time
import numpy as np
def primes_upto(N):
    s=bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2,int(N**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(N+1) if s[i]]
t0=time.time(); L=int(sys.argv[1]); tg=float(sys.argv[2]); tevals=[float(v) for v in sys.argv[3:]] or [tg]
P=primes_upto(L); r=int(math.isqrt(L)); h=L//2
n=np.arange(-h, L-h, dtype=np.int64)
c=np.zeros(L, dtype=np.int64); choice={}
for p in P:
    if p<=r:
        cls=0; c[np.mod(n,p)==cls]+=1
    else:
        m=c<=1; nn=n[m]; cc=c[m]
        tot=np.bincount(np.mod(nn,p), weights=(1-tg)*tg**(cc+1), minlength=p); cls=int(np.argmin(tot))
        sel=np.nonzero(m)[0][np.mod(nn,p)==cls]; c[sel]+=1
    choice[p]=cls
print(f"greedy done {time.time()-t0:.0f}s; approx #c=0: {int((c==0).sum())}, pi(L)={len(P)}", flush=True)
x=0; M=1
for p,cls in choice.items():
    a=(-1-h-cls)%p; tt=((a-x)*pow(M,-1,p))%p; x+=M*tt; M*=p
print(f"CRT done {time.time()-t0:.0f}s; x has {len(str(x))} digits", flush=True)
wI=np.zeros(L)
for p in P:
    q=p
    while True:
        i0=(-1-x)%q
        if i0>=L: break
        wI[i0::q]+=1; q*=p
print(f"valuations done {time.time()-t0:.0f}s; #w=0 in window: {int((wI==0).sum())}", flush=True)
wk=np.zeros(L+1)
for p in P:
    q=p
    while q<=L: wk[q::q]+=1; q*=p
wk=wk[1:]
for t in tevals:
    lhs=(t**(wI+1)).sum(); rhs=(t**wk).sum()
    print(f"L={L} t={t}: LHS={lhs:.3f} RHS={rhs:.3f} slack={rhs-lhs:.3f} rel={(rhs-lhs)/rhs:.5f}", flush=True)
    if lhs>rhs:
        with open(f"lap_counterexample_L{L}.txt","w") as f:
            f.write(f"# (LAP) VIOLATED: L={L} t={t} LHS={lhs} RHS={rhs}; z=1 on all primes<=L; window I=[x+1,x+L]\nL={L}\nt={t}\nx={x}\n")
        print("  CERTIFICATE WRITTEN", flush=True)
