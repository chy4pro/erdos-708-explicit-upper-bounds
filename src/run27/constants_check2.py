"""Rigorous sup over theta of psi_S(theta) = 2^{S/theta} theta^{1-r} H^r / r!, r = floor(31/theta)+1 (sigma = 32, c = 31).
On each piece theta in (31/r, 31/(r-1)] r is constant and log psi is decreasing in theta, so sup = max over r >= 32 of the
value at theta = 31/r (left endpoint, r fixed).  Also general c (sigma = 63 - c): pieces (c/r, c/(r-1)], r >= c+1.
Report: S*(lambda) = largest S with 2*lambda*S*sup psi_S <= S-1 ; for lambda in {2, 600} and c in {31, 40, 50, 60}.
"""
from math import log10, lgamma, log, floor
H = 17/16
def logpsi(S, r, c):
    theta = c / r
    return (S/theta)*log10(2) + (1-r)*log10(theta) + r*log10(H) - lgamma(r+1)/log(10)
def sup_logpsi(S, c, rmax=200000):
    best = -1e18; br = None
    for r in range(c+1, rmax):
        v = logpsi(S, r, c)
        if v > best: best, br = v, r
        # for large r, logpsi ~ (r/c)(S log2 - c log(c/(eH))) : if slope negative and r > 10c, stop
        if r > 20*c and v < best - 50: break
    return best, br
for c in [31, 40, 50, 60]:
    print(f"c = {c} (carrier mass window ({63-c-1}, {63-c+1}), cap >= {63-c-1}):")
    for S in [72, 100, 106, 110, 150, 200, 250]:
        b, br = sup_logpsi(S, c)
        print(f"   S={S:4d}: sup log10 psi_S = {b:10.3f} (at r={br}, theta={c/br:.4f});  log10(2 S sup) = {log10(2*S)+b:9.3f}")
    for lam in [2, 600]:
        Sstar = None
        for S in range(65, 400):
            b, _ = sup_logpsi(S, c)
            if log10(2*lam*S) + b <= log10(S-1): Sstar = S
            else: break
        print(f"   lambda={lam}: S* = {Sstar}")
