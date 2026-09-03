#!/usr/bin/env python3
"""Fast adversarial test of (TH): sum_{k<=m}(w(k)-2)^+ <= sum_{b in I}(w(b)-1)^+, w = sum_p z_p v_p, 0<=z_p<=1, primes p<=m
(primes > m only raise the RHS, so the adversary sets them to 0). Valuations on the interval by sieving. Structured x:
x = -1 mod prod(S) for prime subsets S (all p in S divide x+1), x = 0, random. Usage: python3 hinge_test2.py SECONDS"""
import random, math, time, sys
def primes_upto(N):
    s=bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2,int(N**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(N+1) if s[i]]
def wvec(start, m, z):   # w(start+1 .. start+m) via sieving over primes with z_p > 0
    w=[0.0]*m
    for p,zp in z.items():
        if zp==0: continue
        q=p
        while q<=start+m:
            first=((start+1+q-1)//q)*q
            for b in range(first, start+m+1, q): w[b-start-1]+=zp
            q*=p
    return w
random.seed(int(time.time()) % 1000); t0=time.time(); worst=(1e9,None); tests=0
while time.time()-t0 < float(sys.argv[1]):
    m=random.randint(2,600); P=primes_upto(m)
    mode=random.random()
    if mode<0.2: z={p:1.0 for p in P}
    elif mode<0.4: z={p:1.0 for p in P if random.random()<random.random()}
    elif mode<0.55: z={p:random.random() for p in P}
    elif mode<0.7:
        lo,hi=sorted(random.sample(range(2,m+2),2)); z={p:1.0 for p in P if lo<=p<=hi}
    elif mode<0.85: z={p:random.choice([0.0,0.5,1.0]) for p in P}
    else: z={p:1.0/p**random.random() for p in P}
    S=[p for p in P if z.get(p,0)>0]
    xs=[0, random.randint(0,10**9)]
    if S:
        sub=random.sample(S, min(len(S), random.randint(1,8))); M=math.prod(sub)
        xs.append(M-1); xs.append(M*random.randint(1,5)-1); xs.append(M-m//2 if M>m else 0)
        xs.append(random.randint(1,10**6)*M - random.randint(1,m))
    wl=wvec(0,m,z); L=sum(max(0.0,v-2) for v in wl)
    for x in xs:
        if x<0: continue
        wr=wvec(x,m,z); R=sum(max(0.0,v-1) for v in wr); tests+=1
        slack=R-L
        if slack<worst[0]:
            worst=(slack,(m,x,mode,len(S))); print(f"new min slack {slack:.3f} at m={m} x={x} mode={mode:.2f} |S|={len(S)}", flush=True)
print(f"tests={tests}; minimum slack = {worst[0]:.3f} at {worst[1]}  (negative would refute TH)")
