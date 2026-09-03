# Written by the independent Claude Opus referee run (09-04) that checked the 0/1 threshold-4 theorem; imports referee_c4_cert.
import numpy as np, sys
from referee_c4_cert import primes_upto, icbrt


def scan(P, m, X, report=True, label=''):
    """min over 0<=x<=X of RHS(x)-LHS, RHS(x)=sum_{b=x+1}^{x+m}(Om_P(b)-1)^+."""
    N = X + m
    Om = np.zeros(N + 1, dtype=np.int16)
    for p in P:
        pk = p
        while pk <= N:
            Om[pk::pk] += 1
            if pk > N // p:
                break
            pk *= p
    g = np.maximum(Om.astype(np.int64) - 1, 0)
    cs = np.concatenate(([0], np.cumsum(g[1:])))  # cs[i]=sum_{b<=i} g(b)
    LHS = int(np.maximum(Om[1:m + 1].astype(np.int64) - 4, 0).sum())
    rhs = cs[m:N + 1] - cs[0:N + 1 - m]          # index x -> RHS(x)
    diff = rhs - LHS
    i = int(np.argmin(diff))
    if report:
        print(f'{label:34s} m={m:9d} |P|={len(P):6d} LHS={LHS:10d} minRHS-LHS={int(diff[i]):10d} at x={i}  RHS(0)-LHS={int(diff[0])}')
    return int(diff[i]), i, LHS
