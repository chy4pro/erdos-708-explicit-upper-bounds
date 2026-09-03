#!/usr/bin/env python3
"""Numerical sanity check of P22's Theorem A: for 0/1 weights (prime set P), sum_{n<=m}(Omega_P(n)-c*(m))^+ <= sum_{b in I}(Omega_P(b)-1)^+
with c*(m) = 5 + max(2, ceil(2 e^2 ln(1 + ln m /6))), and Lemma 3 itself. Random and structured x (incl. windows centred at highly
divisible numbers), P random/all/small. Usage: python3 thmA_check.py SECONDS"""
import random, math, time, sys
def primes_upto(N):
    s=bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2,int(N**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(N+1) if s[i]]
def cstar(m): return 5+max(2, math.ceil(2*math.e**2*math.log(1+math.log(m)/6)))
def s_of(L): return max(2, math.ceil(2*math.e**2*math.log(1+math.log(L)/6)))
def omegaP_vec(start,m,P,mult=True):
    v=[0]*m
    for p in P:
        q=p
        while q<=start+m:
            first=((start+1+q-1)//q)*q
            for b in range(first,start+m+1,q): v[b-start-1]+=1
            if not mult: break
            q*=p
    return v
random.seed(5); t0=time.time(); tests=0; fails=0; lem3=0; lem3f=0; minslack=10**9
while time.time()-t0<float(sys.argv[1]):
    m=random.randint(3,3000); PP=primes_upto(m); mode=random.random()
    if mode<0.3: P=PP
    elif mode<0.6: P=[p for p in PP if random.random()<random.random()]
    else: P=[p for p in PP if p<=random.randint(2,60)]
    if not P: continue
    c=cstar(m); xs=[0, random.randint(0,10**9)]
    B=1
    for p in P[:25]: B*=p**(int(math.log(m,p))+1)
    xs+=[B-(m//2)-1, random.randint(2,9)*B-(m//2)-1, B-1]
    wK=omegaP_vec(0,m,P); L=sum(max(0,v-c) for v in wK)
    for x in xs:
        wI=omegaP_vec(x,m,P); R=sum(max(0,v-1) for v in wI); tests+=1
        if L>R: fails+=1; print("THM A FAILS", m, len(P), x if x<10**12 else "big", L, R)
        minslack=min(minslack, R-L)
    # Lemma 3 on the same window: Q = P (distinct primes), L=m>=64
    if m>=64:
        s=s_of(m); wKd=omegaP_vec(0,m,P,False); lhs=sum(1 for v in wKd if v>=s+5)
        for x in xs:
            wId=omegaP_vec(x,m,P,False); rhs=sum(1 for v in wId if v>=1); lem3+=1
            if lhs>rhs: lem3f+=1; print("LEMMA 3 FAILS", m, len(P), lhs, rhs)
print(f"Theorem A: tests={tests}, failures={fails}, min slack={minslack}; Lemma 3: tests={lem3}, failures={lem3f}; c*(3000)={cstar(3000)}, c*(10^6)={cstar(10**6)}, 20lnln(10^6)={20*math.log(math.log(10**6)):.1f}")
