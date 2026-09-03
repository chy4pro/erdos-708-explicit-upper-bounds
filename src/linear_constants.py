#!/usr/bin/env python3
"""For a_n >= n^e, the best linear constant from Theorem D (least k >= 2 with n^{e(k-1)} >= (kn)^{k+1}), with
Theorem A's F(n)/n as fallback where no k is admissible; prints the supremum over n and where it is attained."""
import math, sys
def Fn(n):
    r = math.ceil(math.log2(2 * n)); s = math.ceil(math.log2(r)); return r + s + 2
def best(n, e):
    ln = math.log(n)
    for k in range(2, 80):
        if e * (k - 1) * ln >= (k + 1) * (math.log(k) + ln) - 1e-12: return k
    return Fn(n)
for e, name in [(3, '3'), (2, '2'), (1.75, '7/4')]:
    worst = max((best(n, e), n) for n in range(2, 200000))
    print(f"a_n >= n^{name}: g <= {worst[0]} n (worst at n = {worst[1]})")
