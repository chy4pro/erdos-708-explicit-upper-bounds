#!/usr/bin/env python3
"""(INJ): for every m >= 1, x >= 0 there is an injection phi: {2..m} -> {x+1..x+m} such that for each k some prime p | k has
(k/p) | phi(k).  (INJ) implies (TH) for every weight vector 0 <= z_p <= 1 at once, since w(phi(k)) >= w(k) - z_p >= w(k) - 1.
Exhaustive x-sweep for small m (x mod lcm(1..m) suffices? no: residues of x mod all d <= m/2 matter -> sweep x over a window
and random x), plus structured x.  Usage: python3 inj_full_test.py SECONDS"""
import random, math, time, sys
def primes_upto(N):
    s=bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2,int(N**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(N+1) if s[i]]
def matching(adj):
    match={}
    def try_k(u, seen):
        for v in adj[u]:
            if v in seen: continue
            seen.add(v)
            if v not in match or try_k(match[v], seen):
                match[v]=u; return True
        return False
    return sum(try_k(u,set()) for u in range(len(adj)))
def cofactors(k,P):
    out=set(); kk=k
    for p in P:
        if p*p>kk: break
        if kk%p==0:
            out.add(k//p)
            while kk%p==0: kk//=p
    if kk>1: out.add(k//kk)
    return out
def inj_ok(m,x,P):
    adj=[]
    for k in range(2,m+1):
        c=set()
        for d in cofactors(k,P):
            first=((x+1+d-1)//d)*d
            c.update(range(first, x+m+1, d))
        adj.append(sorted(c))
    return matching(adj)==m-1
random.seed(11); t0=time.time(); tests=0; fails=[]
P=primes_upto(2000)
# exhaustive small m over a window of x
for m in range(2,41):
    L=math.lcm(*range(1,m+1))
    for x in range(0, min(L, 3000)):
        tests+=1
        if not inj_ok(m,x,P): fails.append((m,x)); print("INJ FAILS", m, x, flush=True)
    if fails: break
print("small-m sweep done", tests, "tests,", len(fails), "failures", f"{time.time()-t0:.0f}s")
while time.time()-t0 < float(sys.argv[1]) and not fails:
    m=random.randint(40,400)
    xs=[random.randint(0,10**9), random.randint(0,10**15)]
    S=random.sample(P[:25], random.randint(1,6)); M=math.prod(S); xs += [M-1, M*random.randint(1,7)-random.randint(1,m), M-m//2 if M>m else 1]
    for x in xs:
        if x<0: continue
        tests+=1
        if not inj_ok(m,x,P): fails.append((m,x)); print("INJ FAILS", m, x, flush=True)
print(f"tests={tests}; failures={len(fails)}")
