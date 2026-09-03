#!/usr/bin/env python3
"""Random search for small-n instances of Erdős #708 with large min|B| (gacha). ES-style placement: u = t*lcm(A) in the
middle of the interval, plus random x. Hard cap via SECONDS. Usage: python3 search_small_n.py N SECONDS"""
import sys, random, math, time
from gn_dp import min_B
n = int(sys.argv[1]); cap = float(sys.argv[2]); t0 = time.time(); random.seed(n)
best = (0, None, None); tried = 0
while time.time() - t0 < cap:
    A = sorted(random.sample(range(2, 61), n))
    L = math.lcm(*A); an = max(A)
    xs = [t * L - an // 2 for t in range(1, 4)] + [random.randrange(0, 5000) for _ in range(2)]
    for x in xs:
        if x < 0: continue
        g = min_B(A, x); tried += 1
        if g > best[0]: best = (g, A, x); print(f"new best: min|B|={g} A={A} x={x}", flush=True)
print(f"n={n}: tried {tried} instances in {time.time()-t0:.0f}s; best = {best}")
