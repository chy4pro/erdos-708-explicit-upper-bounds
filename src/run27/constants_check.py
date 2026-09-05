"""Numerical checks for the round-15 report (Erdos #708, F1_708).
(1) Rescaled hinge-moment inequality: for a in [0,theta]^N, sum t, c>0, r = floor(c/theta)+1:
      (t-c)^+ <= theta^{1-r} e_r(a).     (random + adversarial tests, exact rationals)
(2) eps(theta) := theta^{2-r} H^r / r!  (r = floor(31/theta)+1, H = 17/16): carried-mass-per-multiple bound.
(3) psi_S(theta) := 2^{S/theta} * eps(theta)/theta ; overload bound ov(b) <= 2 * S * max_theta psi_S(theta)  (SAP systems).
    Report max over theta in (0,1] for S = 72, 100, 105, 110, and the largest S with 2*S*max psi_S(theta)*lambda <= S-1 (lambda = 2).
(4) 131# (product of first 32 primes) = lower bound on the number of multiples of a carrier.
"""
from fractions import Fraction
from math import factorial, floor, log10, log2
import random, itertools

def e_r(a, r):
    # elementary symmetric polynomial, exact
    E = [Fraction(0)] * (r + 1); E[0] = Fraction(1)
    for x in a:
        for k in range(r, 0, -1):
            E[k] += E[k - 1] * x
    return E[r]

def check_rescaled(trials=3000, seed=1):
    rng = random.Random(seed); worst = Fraction(0); bad = 0
    for _ in range(trials):
        theta = Fraction(rng.randint(1, 20), 20)
        c = Fraction(rng.randint(1, 40), 4)
        N = rng.randint(1, 60)
        mode = rng.random()
        if mode < 0.3:
            a = [theta] * N
        elif mode < 0.6:
            a = [theta * Fraction(rng.randint(0, 8), 8) for _ in range(N)]
        else:
            a = [theta] * (N // 2) + [theta * Fraction(rng.randint(1, 100), 100) for _ in range(N - N // 2)]
        t = sum(a); r = floor(c / theta) + 1
        lhs = max(t - c, Fraction(0)); rhs = theta ** (1 - r) * e_r(a, r)
        if lhs > rhs: bad += 1
        if rhs > 0: worst = max(worst, lhs / rhs)
    print(f"(1) rescaled hinge-moment inequality: violations={bad} of {trials}, max ratio lhs/rhs = {float(worst):.6f}")

def eps(theta, H=17/16, c=31):
    r = floor(c / theta) + 1
    # compute log10 to avoid overflow
    lg = (2 - r) * log10(theta) + r * log10(H) - sum(log10(i) for i in range(1, r + 1))
    return lg

def psi(S, theta):
    return S / theta * log10(2) + eps(theta) - log10(theta)

def scan(S):
    best = -1e9; bt = None
    thetas = [i / 1000 for i in range(1, 1001)]
    for th in thetas:
        v = psi(S, th)
        if v > best: best, bt = v, th
    return best, bt

if __name__ == "__main__":
    check_rescaled()
    print("(2) eps(theta) = theta^{2-r} H^r/r!, r = floor(31/theta)+1, H = 17/16  (log10):")
    for th in [1.0, 0.9, 0.8, 0.7, 0.6, 0.5, 0.4, 0.3, 0.25, 0.2, 0.1, 0.05, 0.02]:
        print(f"    theta={th:5.2f}  r={floor(31/th)+1:5d}  log10 eps = {eps(th):9.2f}")
    print("(3) overload bound: ov(b) <= 2 S max_theta psi_S(theta), psi_S = 2^{S/theta} eps(theta)/theta")
    for S in [72, 100, 105, 108, 110, 115, 120]:
        b, bt = scan(S)
        tot = log10(2 * S) + b
        print(f"    S={S:4d}: max log10 psi = {b:8.3f} at theta={bt:.3f};  log10(2 S max psi) = {tot:8.3f};  lambda=2 feasible: {log10(2)+tot <= log10(S-1)}")
    # largest S with 2*S*maxpsi*2 <= S-1
    Smax = None
    for S in range(65, 200):
        b, _ = scan(S)
        if log10(4*S) + b <= log10(S-1): Smax = S
        else: break
    print(f"    largest S with lambda=2 feasibility: S* = {Smax}")
    primes = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131]
    P = 1
    for p in primes: P *= p
    print(f"(4) 131# = product of first 32 primes = {P} ~ 10^{log10(P):.2f}")
    # (5) example family numbers: Q = primes in (10^51, 10^138], sum 1/q ~ ln(138/51)
    from math import log
    print(f"(5) example: sum_(10^51<q<=10^138) 1/q ~ ln(138/51) = {log(138/51):.4f} < 17/16;  |Q| ~ 10^138/(138 ln 10) ~ 10^{138-log10(138*log(10)):.1f}")
    # moment control thresholds: C(|Q|, r) <= m / r!  <=> log10 m >= r*136 + log10(r!) roughly
    for r in [24, 25, 32, 65]:
        lg = r * 135.5 - sum(log10(i) for i in range(1, r + 1)) + sum(log10(i) for i in range(1, r + 1))
        print(f"    r={r}: C(|Q|,r) ~ 10^{r*135.5 - sum(log10(i) for i in range(1,r+1)):.0f};  need log10 m >= {r*135.5:.0f} for r-th moment control")
