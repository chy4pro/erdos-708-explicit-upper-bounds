#!/usr/bin/env python3
"""Refute P20's matching statement (NM) [equivalently (SB)] for explicit (m, x).
(NM): the bipartite graph L=[1,m], R=I={x+1..x+m}, k~b iff k/gcd(k,b) in {1} U primes, has a perfect matching.
Hall obstruction: T = {b in I : lpf(b) > m/2}. For k <= m and rough b, gcd(k,b) in {1, q} with q > m/2 prime, so
k ~ b forces k in {1} U primes.  Hence |N(T)| <= pi(m)+1 and (NM) fails whenever |T| >= pi(m)+2.
Construction: choose for each prime p <= m/2 the residue class of positions i in [0,m) that will be divisible by p
(greedy: the class with fewest surviving candidates), CRT gives x; then verify everything directly on the integers.
Usage: python3 nm_refute.py m1 m2 ...   (window positions are i = 0..m-1, b = x+1+i)"""
import sys, math
def primes_upto(N):
    s=bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2,int(N**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(N+1) if s[i]]
def greedy_pattern(m):
    P=[p for p in primes_upto(m//2)]
    alive=bytearray([1])*m; choice={}
    for p in P:
        cnt=[0]*p
        for i in range(m):
            if alive[i]: cnt[i%p]+=1
        r=min(range(p), key=lambda r:(cnt[r], r))
        choice[p]=r
        for i in range(r,m,p): alive[i]=0
    return P, choice, [i for i in range(m) if alive[i]]
def crt_x(choice):
    # need x+1+r ≡ 0 (mod p)  i.e. x ≡ -1-r (mod p)
    x=0; M=1
    for p,r in choice.items():
        a=(-1-r)%p
        # x + M*t ≡ a (mod p)
        t=((a-x)*pow(M,-1,p))%p
        x+=M*t; M*=p
    return x, M
for m in map(int, sys.argv[1:]):
    P, choice, surv = greedy_pattern(m)
    pi_m=len(primes_upto(m))
    print(f"m={m}: greedy rough-pattern size {len(surv)} vs pi(m)+1={pi_m+1}", flush=True)
    if len(surv) < pi_m+2: continue
    x, M = crt_x(choice)
    # direct verification on integers
    T=[]
    for i in range(m):
        b=x+1+i
        if all(b%p for p in P): T.append(b)
    assert len(T)==len(surv), (len(T), len(surv))
    # N(T) under P20's adjacency: k ~ b iff k/gcd(k,b) is 1 or prime
    small_primes=set(primes_upto(m))
    N=set()
    for k in range(1,m+1):
        for b in T:
            g=math.gcd(k, b%k if k>1 else 0) if k>1 else 1
            q=k//g
            if q==1 or q in small_primes: N.add(k); break
    print(f"  x has {len(str(x))} digits; |T|={len(T)} rough numbers in I; |N(T)|={len(N)}; Hall violated: {len(T)>len(N)}", flush=True)
    assert N <= ({1}|small_primes)
    if len(T)>len(N):
        open(f"nm_counterexample_m{m}.txt","w").write(f"m={m}\nx={x}\n|T|={len(T)} |N(T)|={len(N)}\nchoice(p->residue class of i in [0,m) with p | x+1+i)={choice}\n")
        print(f"  written nm_counterexample_m{m}.txt", flush=True)
        break
