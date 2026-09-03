#!/usr/bin/env python3
"""Dialogue's per-prime-power sufficient condition for (TH).  Writing c(I)=sum_I min(w,1)=sum_q z_q sum_{b in I, q|b} theta_b
with theta_b=min(1,1/w(b)), and sum_K min(w,2)=sum_q z_q sum_{k<=m, q|k} theta'_k with theta'_k=min(1,2/w(k)), (TH) follows from
(PQ) for every prime power q with z_q>0:  sum_{b in I, q|b} min(1,1/w(b)) <= delta_q + sum_{k<=m, q|k} min(1,2/w(k)),
delta_q = N_I(q) - floor(m/q) in {0,1}.  Instances: hinge_test2 generator + symmetric adversary (window centred at a number
divisible by high powers of all weighted primes).  Usage: python3 pq_test.py SECONDS"""
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
random.seed(int(time.time())%1000); t0=time.time(); tests=0; fails=0; worst=(1e9,None); TH_fails=0
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
    # symmetric adversary: b0 = t * prod_{p in S'} p^{e_p}, e_p = floor(log_p m)+1, window centred at b0
    Sp=S[:min(len(S),40)]; B=1
    for p in Sp: B*=p**(int(math.log(m,p))+1)
    for t in (1, random.randint(2,9)):
        b0=t*B; xs.append(b0-(m//2)-1)
    wl=wvec(0,m,z); L=sum(max(0.0,v-2) for v in wl)
    for x in xs:
        if x<0: continue
        wr=wvec(x,m,z); tests+=1
        R=sum(max(0.0,v-1) for v in wr)
        if R-L<-1e-9: TH_fails+=1; print("TH FAIL?!", m, x, flush=True)
        for p in S:
            q=p
            while q<=m:
                # I-side
                first=((x+1+q-1)//q)*q; lhs=0.0; NI=0
                for b in range(first, x+m+1, q):
                    wb=wr[b-x-1]; lhs+=min(1.0,1.0/wb); NI+=1
                rhs=NI-(m//q)
                for k in range(q, m+1, q):
                    wk=wl[k-1]; rhs+=min(1.0,2.0/wk)
                s=rhs-lhs
                if s<worst[0]: worst=(s,(m,x if x<10**15 else f"~1e{len(str(x))}",q,len(S),round(mode,2)))
                if s<-1e-9:
                    fails+=1
                    if fails<=5: print(f"PQ FAIL: m={m} q={q} slack={s:.3f} |S|={len(S)} mode={mode:.2f} x={'sym' if x>10**15 else x}", flush=True)
                q*=p
print(f"tests={tests}; (PQ) failures={fails}; min slack {worst}; TH_fails={TH_fails}")
