#!/usr/bin/env python3
"""Test P20's (Tail21): for finite prime set Q, L>=1, y>=0: #{n<=L : omega_Q(n)>=2} <= #{y<n<=y+L : omega_Q(n)>=1}.
Random Q/L/y plus structured y (y = -1 mod prod(sub); centred: y = t*prod(Q) - ceil(L/2)). Usage: python3 tail21_test.py SECONDS"""
import random, math, time, sys
def primes_upto(N):
    s=bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2,int(N**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(N+1) if s[i]]
def omega_ge(start, L, Q, thr):
    c=[0]*L
    for p in Q:
        first=((start+1+p-1)//p)*p
        for n in range(first, start+L+1, p): c[n-start-1]+=1
    return sum(1 for v in c if v>=thr)
random.seed(int(time.time())%1000); t0=time.time(); tests=0; fails=[]; worst=(10**9,None)
while time.time()-t0 < float(sys.argv[1]):
    L=random.randint(2,700); P=primes_upto(L); mode=random.random()
    if mode<0.3: Q=[p for p in P if p<=L//2]
    elif mode<0.6: Q=[p for p in P if random.random()<random.random()]
    else:
        lo,hi=sorted(random.sample(range(2,L+2),2)); Q=[p for p in P if lo<=p<=hi]
    if not Q: continue
    ys=[0, random.randint(0,10**9)]
    sub=random.sample(Q, min(len(Q), random.randint(1,10))); M=math.prod(sub); MQ=math.prod(Q[:min(len(Q),60)])
    ys += [M-1, M*random.randint(1,5)-1, random.randint(1,10**6)*M-random.randint(1,L), MQ*random.randint(1,9)-(L+1)//2, MQ-(L+1)//2]
    lhs=omega_ge(0,L,Q,2)
    for y in ys:
        if y<0: continue
        rhs=omega_ge(y,L,Q,1); tests+=1; s=rhs-lhs
        if s<worst[0]: worst=(s,(L,y if y<10**12 else f"~1e{len(str(y))}",len(Q),round(mode,2)))
        if s<0: fails.append((L,len(Q),mode))
print(f"tests={tests}; failures={len(fails)}; min slack {worst}")
