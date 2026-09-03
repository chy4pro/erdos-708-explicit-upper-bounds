#!/usr/bin/env python3
"""Test P20's layer inequality (LAYER): for all t >= 1, #{k<=m : w(k) > t+1} <= #{b in I : w(b) > t}
(equivalently for every value v = w(k) > 2: #{k : w(k) >= v} <= #{b in I : w(b) >= v-1}). Also the extended range t >= 0
(values v > 1). Same instance generator as hinge_test2.py. Usage: python3 layer_test.py SECONDS"""
import random, math, time, sys, bisect
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
def cnt_ge(sorted_vals, v): return len(sorted_vals)-bisect.bisect_left(sorted_vals, v-1e-9)
random.seed(int(time.time())%1000); t0=time.time(); tests=0; fail1=0; fail0=0; worst1=(10**9,None); worst0=(10**9,None)
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
        xs += [M-1, M*random.randint(1,5)-1, M-m//2 if M>m else 0, random.randint(1,10**6)*M-random.randint(1,m), M*random.randint(1,50)-(m//2)]
    wl=sorted(wvec(0,m,z)); vals=sorted(set(v for v in wl if v>1+1e-9))
    for x in xs:
        if x<0: continue
        wr=sorted(wvec(x,m,z)); tests+=1
        for v in vals:
            lhs=cnt_ge(wl,v); rhs=cnt_ge(wr,v-1); s=rhs-lhs
            if v>2+1e-9:
                if s<worst1[0]: worst1=(s,(m,x,round(v,3),len(S),round(mode,2)))
                if s<0: fail1+=1
            else:
                if s<worst0[0]: worst0=(s,(m,x,round(v,3),len(S),round(mode,2)))
                if s<0: fail0+=1
print(f"tests={tests}; (LAYER) t>=1 failures={fail1}, min slack {worst1}; extended 0<=t<1 failures={fail0}, min slack {worst0}")
