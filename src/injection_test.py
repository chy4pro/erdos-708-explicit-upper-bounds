#!/usr/bin/env python3
"""Test P20's route for (TH): does an injection phi: K2 -> I exist with (k/p) | phi(k) for some prime p | k (so that
w(phi(k)) >= w(k) - z_p >= w(k) - 1)?  K2 = {k <= m : w(k) >= 2}, I = {x+1..x+m}.  Bipartite matching by augmenting paths.
Usage: python3 injection_test.py SECONDS"""
import random, math, time, sys
def primes_upto(N):
    s=bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2,int(N**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(N+1) if s[i]]
def factor_small(k, P):
    f={}
    for p in P:
        if p*p>k: break
        while k%p==0: f[p]=f.get(p,0)+1; k//=p
    if k>1: f[k]=f.get(k,0)+1
    return f
def matching(adj, nL):
    match={}  # right -> left
    def try_k(u, seen):
        for v in adj[u]:
            if v in seen: continue
            seen.add(v)
            if v not in match or try_k(match[v], seen):
                match[v]=u; return True
        return False
    return sum(try_k(u,set()) for u in range(nL))
random.seed(5); t0=time.time(); tests=0; fails=[]
while time.time()-t0 < float(sys.argv[1]):
    m=random.randint(4,300); P=primes_upto(m)
    mode=random.random()
    if mode<0.3: z={p:1.0 for p in P}
    elif mode<0.6: z={p:1.0 for p in P if random.random()<random.random()}
    elif mode<0.8: z={p:random.random() for p in P}
    else:
        lo,hi=sorted(random.sample(range(2,m+2),2)); z={p:1.0 for p in P if lo<=p<=hi}
    S=[p for p in P if z.get(p,0)>0]
    if not S: continue
    xs=[random.randint(0,10**9)]
    sub=random.sample(S,min(len(S),random.randint(1,6))); M=math.prod(sub); xs += [M-1, M*random.randint(1,9)-random.randint(1,m)]
    for x in xs:
        if x<0: continue
        I=list(range(x+1,x+m+1))
        wk={k:sum(z.get(p,0)*e for p,e in factor_small(k,P).items()) for k in range(1,m+1)}
        K2=[k for k in range(1,m+1) if wk[k]>=2-1e-12]
        if not K2: continue
        # candidate b's for k: multiples in I of k/p for primes p|k with z_p>0 (any prime p|k is allowed; using z_p>0 primes is the useful choice)
        adj=[]
        for k in K2:
            f=factor_small(k,P); cands=set()
            for p in f:
                d=k//p
                first=((x+1+d-1)//d)*d
                for b in range(first, x+m+1, d): cands.add(b)
            adj.append(sorted(cands))
        mt=matching(adj,len(K2)); tests+=1
        if mt<len(K2):
            fails.append((m,x,len(K2),mt,len(S)))
            print(f"HALL FAILS: m={m} x={x} |K2|={len(K2)} matched={mt} |S|={len(S)}", flush=True)
            if len(fails)>=8: break
    if len(fails)>=8: break
print(f"tests={tests}; injection failures={len(fails)}")
