#!/usr/bin/env python3
"""Necessary condition for AF (forest transfer, 0/1 weights, P = primes <= m/2 or all primes <= m): ignore the forest constraint and ask
whether the units (omega(k)-2)^+ of each k <= m can be routed to b in I with capacity (omega(b)-1)^+, where a unit of k may go to b
iff some pair {p,q} subset S(k) has pq | b.  Max-flow (Dinic).  Windows: centred sieve + CRT (dense rough numbers) and random x.
If the flow relaxation fails, AF fails (DTH may still hold).  Usage: python3 af_flow_test.py m"""
import sys, math, random
from collections import deque
def primes_upto(N):
    s=bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2,int(N**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(N+1) if s[i]]
class Dinic:
    def __init__(s,n): s.n=n; s.g=[[] for _ in range(n)]
    def add(s,u,v,c): s.g[u].append([v,c,len(s.g[v])]); s.g[v].append([u,0,len(s.g[u])-1])
    def bfs(s,src,t):
        s.lv=[-1]*s.n; s.lv[src]=0; q=deque([src])
        while q:
            u=q.popleft()
            for v,c,_ in s.g[u]:
                if c>0 and s.lv[v]<0: s.lv[v]=s.lv[u]+1; q.append(v)
        return s.lv[t]>=0
    def dfs(s,u,t,f):
        if u==t: return f
        while s.it[u]<len(s.g[u]):
            e=s.g[u][s.it[u]]; v,c,r=e
            if c>0 and s.lv[v]==s.lv[u]+1:
                d=s.dfs(v,t,min(f,c))
                if d>0: e[1]-=d; s.g[v][r][1]+=d; return d
            s.it[u]+=1
        return 0
    def maxflow(s,src,t):
        fl=0
        while s.bfs(src,t):
            s.it=[0]*s.n
            while True:
                f=s.dfs(src,t,10**9)
                if f==0: break
                fl+=f
        return fl
sys.setrecursionlimit(100000)
m=int(sys.argv[1]); P=primes_upto(m); r=int(math.isqrt(m)); h=m//2
def window_centred(S):
    n=list(range(-h,m-h)); alive=[1]*m; choice={}
    for p in S:
        if p<=r: cls=0
        else:
            cnt={}
            for i in range(m):
                if alive[i]: cnt[n[i]%p]=cnt.get(n[i]%p,0)+1
            cls=min(range(p), key=lambda c:(cnt.get(c,0),c))
        choice[p]=cls
        for i in range(m):
            if n[i]%p==cls: alive[i]=0
    x=0; M=1
    for p,cls in choice.items():
        a=(-1-h-cls)%p; t=((a-x)*pow(M,-1,p))%p; x+=M*t; M*=p
    return x
def Sset(n_, S):  # set of primes in S dividing n_ (n_ may be huge: use residues)
    return frozenset(p for p in S if n_%p==0)
def test(S, x, label):
    SK=[Sset(k,S) for k in range(1,m+1)]
    SI=[Sset(x+1+i,S) for i in range(m)]
    demand=[max(0,len(s)-2) for s in SK]; cap=[max(0,len(s)-1) for s in SI]
    D=sum(demand); C=sum(cap)
    # graph: src -> k (demand) ; k -> b if some pair of S(k) divides b, i.e. |S(k) ∩ S(b)| >= 2 ; b -> t (cap)
    N=2+m+m; src=0; t=1; g=Dinic(N)
    for k in range(m):
        if demand[k]==0: continue
        g.add(src,2+k,demand[k])
        for b in range(m):
            if cap[b]>0 and len(SK[k]&SI[b])>=2: g.add(2+k,2+m+b,demand[k])
    for b in range(m):
        if cap[b]>0: g.add(2+m+b,t,cap[b])
    f=g.maxflow(src,t)
    print(f"[{label}] m={m} |S|={len(S)}: demand={D} capacity={C} maxflow={f} -> {'FLOW OK' if f==D else 'FLOW FAILS (AF false here)'} ; (DTH) {'holds' if D<=C else 'FAILS'}", flush=True)
for Sname,S in [("primes<=m/2",[p for p in P if p<=m//2]),("all primes<=m",P),("primes<=sqrt(m)",[p for p in P if p<=r])]:
    x=window_centred(S); test(S,x,Sname+" dense")
    random.seed(1); test(S,random.randint(10**6,10**9),Sname+" random x")
    B=1
    for p in S[:min(len(S),30)]: B*=p**(int(math.log(m,p))+1)
    test(S,B-h-1,Sname+" symmetric")
