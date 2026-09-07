from fractions import Fraction as Q
from math import factorial

H, G, K = Q(1025, 1024), Q(65536, 65535), Q(35, 16)
f, E = Q(2633, 2000), Q(87, 32)
caps = {
    1: Q(51,100), 2: Q(6,25), 4: Q(3,100),
    8: Q(1,250), 16: Q(1,2000),
    32: Q(1,16000), 64: Q(1,100000)
}

for ell, cap in caps.items():
    r = 4 if ell == 1 else 9*ell//2
    eps = G * Q(ell**(r-1), factorial(r)) * H**r
    if ell == 1:
        eps /= 2

    degree = ell + 1
    steps = [0] + [1 << j for j in range(ell.bit_length())]
    polynomial = [1] + [0]*degree
    best = Q(0)

    for N in range(int((K+1)*ell+1) + 1):
        clip = max(Q(0), 1-max(Q(0), Q(N-ell-1, ell))/K)
        denominator = max(Q(1, ell), Q(N-ell, ell))
        best = max(best, polynomial[degree]*clip/denominator)
        polynomial = [
            sum(polynomial[s-j] for j in steps if j <= s)
            for s in range(degree+1)
        ]

    assert 24*eps*best < cap, (ell, float(24*eps*best), float(cap))
    print("ell", ell, "24*eps*R_ell <=", float(24*eps*best), "cap", float(cap))

assert 4**16 * f**51 * (2*E*H/9)**72 < 1
assert 16*f**4 * (2*E*H/9)**9 < Q(9,16)

q = Q(3,4)**128
tail = 96*G*q/(1-q) + 256*G*f/(K*128**2)
assert tail < Q(1,100)
assert sum(caps.values(), Q(0)) + Q(1,100) < Q(4,5)
assert 24*(1-2*G*H/K) == Q(62248,30583) > 2
print("tail <", float(tail), "| finite+tail sum =", float(sum(caps.values(), Q(0)) + Q(1,100)), "< 0.8")
print("window factor 24(1-2γH*/K) =", 24*(1-2*G*H/K), "≈", float(24*(1-2*G*H/K)))
print("ALL ASSERTIONS PASSED")
