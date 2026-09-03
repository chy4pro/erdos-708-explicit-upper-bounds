"""Independent re-implementation of the round-10 C=4 certificates."""
from fractions import Fraction as F
from math import comb, gcd
from itertools import combinations
import numpy as np


def primes_upto(n):
    if n < 2:
        return []
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = False
    return [int(v) for v in np.nonzero(s)[0]]


def icbrt(m):
    y = int(round(m ** (1 / 3)))
    while y ** 3 > m:
        y -= 1
    while (y + 1) ** 3 <= m:
        y += 1
    return y


def omega_arrays(P, m):
    """Omega_P(k), omega_P(k), omega_S(k) for k<=m as numpy int arrays (index k)."""
    Om = np.zeros(m + 1, dtype=np.int64)
    om = np.zeros(m + 1, dtype=np.int64)
    for p in P:
        if p > m:
            continue
        pk = p
        while pk <= m:
            Om[pk::pk] += 1
            pk *= p
        om[p::p] += 1
    return Om, om


def build_certificate(P, m):
    """Return (branch, cert dict d->Fraction, data)."""
    y = icbrt(m)
    S = [p for p in P if p <= y]
    H = sum(F(1, p) for p in S)
    eta = (1 + F(1, y)) * H
    cert = {}
    if eta <= 2:
        branch = 'sparse'
        # prime powers p^j, j>=2, p^j<=m, p in P
        for p in P:
            pk = p * p
            while pk <= m:
                cert[pk] = cert.get(pk, F(0)) + 1
                pk *= p
        for a, b in combinations(S, 2):
            cert[a * b] = cert.get(a * b, F(0)) + F(11, 21)
        for a, b, c in combinations(S, 3):
            cert[a * b * c] = cert.get(a * b * c, F(0)) - F(1, 7)
    else:
        branch = 'dense'
        cert[1] = F(-1)
        for p in P:
            pk = p
            while pk <= m:
                cert[pk] = cert.get(pk, F(0)) + 1
                pk *= p
    cert = {d: c for d, c in cert.items() if c != 0}
    return branch, cert, dict(y=y, S=S, H=H, eta=eta)


def V_m(cert, m):
    v = F(0)
    for d, c in cert.items():
        q = m // d
        v += c * q if c > 0 else c * (q + 1)
    return v


def check_F(cert, P, nmax):
    """Verify sum_{d|n} c_d <= (Omega_P(n)-1)^+ for all n<=nmax."""
    Pset = set(P)
    tot = [F(0)] * (nmax + 1)
    for d, c in cert.items():
        if d > nmax:
            continue
        for n in range(d, nmax + 1, d):
            tot[n] += c
    Om, _ = omega_arrays(P, nmax)
    bad = []
    for n in range(1, nmax + 1):
        rhs = max(int(Om[n]) - 1, 0)
        if tot[n] > rhs:
            bad.append((n, tot[n], rhs))
    return bad


def interval_rhs(P, x, m):
    """sum_{b=x+1}^{x+m} (Omega_P(b)-1)^+ computed by a segmented sieve."""
    lo, hi = x + 1, x + m
    Om = np.zeros(m, dtype=np.int64)
    for p in P:
        pk = p
        while pk <= hi:
            start = ((lo + pk - 1) // pk) * pk
            if start <= hi:
                Om[start - lo::pk] += 1
            if pk > hi // p:
                break
            pk *= p
    return int(np.maximum(Om - 1, 0).sum()), Om


def lhs_sum(P, m, c=4):
    Om, _ = omega_arrays(P, m)
    return int(np.maximum(Om[1:m + 1] - c, 0).sum())
