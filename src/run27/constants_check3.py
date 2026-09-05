"""Feasibility threshold S*(m) of the sigma=3 (c=60) prefix certificate for GENERAL atom systems (multi-level allowed).
ov(b) <= 2 E S sup_{theta in [60/log2 m, 1]} G(theta),  G(theta) = theta^{1-r} (H^r/r!) (1 + S E/theta)^{3/theta}, r = floor(60/theta)+1,
E = log2(m/64) (max number of atom levels per prime), H = 17/16.  Feasible with lambda=2 iff 4 E S sup G <= S - 1.
On each piece of constant r, log G is decreasing in theta, so sup = max over integers r in [61, log2 m + 1] of G at theta = 60/r.
We evaluate r on {61..2000} U geometric grid (ratio 1.0005) up to rmax U {rmax}, and require 4 E S supG <= (S-1)/10 (safety factor 10
covering both the r-grid and the S-grid, ratio 1.2).  Reported S*(m) is the largest S on the S-grid passing the check.
Asymptotically log10 G(60/r) ~ r [ log10(e/60) + log10 H + (1/20) log10(S E r/60) ], positive for large r once S E log2(m) > 60*10^26.4,
so S*(m) ~ 1.5e28 / (log2 m)^2.
"""
from math import log10, lgamma, log, log2, floor, ceil
H = 17/16
def logG(S, E, r):
    theta = 60 / r
    return (1 - r) * log10(theta) + r * log10(H) - lgamma(r + 1) / log(10) + (3 / theta) * log10(1 + S * E / theta)
def rgrid(rmax):
    rs = list(range(61, min(2000, rmax) + 1))
    r = 2000.0
    while r < rmax:
        r *= 1.0005
        rs.append(int(r))
    rs.append(rmax)
    return sorted(set(x for x in rs if 61 <= x <= rmax))
def sup_logG(S, E, rs):
    return max(logG(S, E, r) for r in rs)
for lgm in [3000, 1e4, 1e5, 1e6, 1e8, 1e10, 1e12]:
    E = lgm * log2(10) - 6
    rmax = int(floor(lgm * log2(10))) + 1
    rs = rgrid(rmax)
    Sstar = None; S = 64.0
    while S < 1e40:
        v = sup_logG(S, E, rs)
        if log10(4 * E * S) + v <= log10((S - 1) / 10): Sstar = S
        else: break
        S *= 1.2
    print(f"log10 m = {lgm:>12.0f}: E = log2(m/64) = {E:.3e}, rmax = {rmax}, |r-grid| = {len(rs)}, S*(m) >= {Sstar:.3e}  (asymptotic 1.5e28/(log2 m)^2 = {1.5e28/(lgm*log2(10))**2:.1e})")
