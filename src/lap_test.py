#!/usr/bin/env python3
"""Test P21's Laplace candidate (LAP): for all t in (0,1], sum_{n in J} t^{w(n)+1} <= sum_{n<=L} t^{w(n)}
(J an interval of length L). (LAP) implies (PQ') for a >= 2. Also the weaker (LAP2): sum_J t^{w} <= 2 sum_{<=L} t^{w}
(expected to FAIL as t->0 on rough-dense windows). Usage: python3 lap_test.py SECONDS"""
import random, math, time, sys
def primes_upto(N):
    s=bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2,int(N**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(N+1) if s[i]]
def wvec(start, m, z):
    w=[0.0]*m
    for p,zp in z.items():
        if zp==0: continue
        q=p
        while q<=start+m:
            first=((start+1+q-1)//q)*q
            for b in range(first, start+m+1, q): w[b-start-1]+=zp
            q*=p
    return w
ts=[0.001,0.01,0.03,0.1,0.2,0.3,0.4,0.5,0.6,0.7,0.8,0.9,0.95,1.0]
random.seed(int(time.time())%1000); t0=time.time(); tests=0; f1=0; f2=0; w1=(1e9,None); w2=(1e9,None)
while time.time()-t0 < float(sys.argv[1]):
    m=random.randint(2,500); P=primes_upto(m); mode=random.random()
    if mode<0.2: z={p:1.0 for p in P}
    elif mode<0.4: z={p:1.0 for p in P if random.random()<random.random()}
    elif mode<0.55: z={p:random.random() for p in P}
    elif mode<0.7:
        lo,hi=sorted(random.sample(range(2,m+2),2)); z={p:1.0 for p in P if lo<=p<=hi}
    elif mode<0.85: z={p:random.choice([0.0,0.5,1.0]) for p in P}
    else: z={p:1.0/p**random.random() for p in P}
    S=[p for p in P if z.get(p,0)>0]
    if not S: continue
    xs=[0, random.randint(0,10**9)]
    sub=random.sample(S, min(len(S), random.randint(1,8))); M=math.prod(sub)
    xs += [M-1, M*random.randint(1,5)-1, random.randint(1,10**6)*M-random.randint(1,m)]
    Sp=S[:min(len(S),40)]; B=1
    for p in Sp: B*=p**(int(math.log(m,p))+1)
    xs += [B-(m//2)-1, random.randint(2,9)*B-(m//2)-1]
    wl=wvec(0,m,z)
    for x in xs:
        if x<0: continue
        wr=wvec(x,m,z); tests+=1
        for t in ts:
            R=sum(t**v for v in wl); Lj=sum(t**(v+1) for v in wr); Lj2=sum(t**v for v in wr)
            s1=(R-Lj)/max(R,1e-12); s2=(2*R-Lj2)/max(R,1e-12)
            if s1<w1[0]: w1=(s1,(m,'sym' if x>10**15 else x,t,len(S),round(mode,2)))
            if s2<w2[0]: w2=(s2,(m,'sym' if x>10**15 else x,t,len(S),round(mode,2)))
            if s1<-1e-9: f1+=1
            if s2<-1e-9: f2+=1
print(f"tests={tests}; (LAP) failures={f1} min rel slack {w1}; (LAP2 factor-2) failures={f2} min rel slack {w2}")
