"""Exact, falsifiable checks of the signed-certificate proof's components.

No external packages. Writes only next to this script. These checks supplement
the analytic proof; they are not a finite verification of universal SC_64.
"""
from collections import defaultdict
from fractions import Fraction as F
from math import factorial, isqrt, prod
from pathlib import Path
import json
import random

ROOT = Path(__file__).resolve().parent
results = {}


def primes_from(start, count):
    out = []
    n = max(2, start)
    while len(out) < count:
        if all(n % d for d in range(2, isqrt(n) + 1)):
            out.append(n)
        n += 1
    return out


def dyadic_floor(a):
    assert 0 < a <= 1
    t = F(1)
    while t > a:
        t /= 2
    return t


def preprocess(levels, m):
    """levels[p] is the list (exponent, original cumulative value)."""
    kept = {}
    for p, entries in levels.items():
        seen = set()
        out = []
        for e, a in entries:
            if a == 0:
                continue
            t = dyadic_floor(a)
            if t in seen:
                continue
            seen.add(t)
            assert t.numerator == 1
            if (p ** e) ** (16 * t.denominator) <= m:
                out.append((e, t))
        if out:
            kept[p] = out
    return kept


def mean(levels):
    total = F(0)
    for p, entries in levels.items():
        prev = F(0)
        for e, a in entries:
            total += (a - prev) / p**e
            prev = a
    return total


def contribution(entries, exponent):
    return max((a for e, a in entries if e <= exponent), default=F(0))


def capped_increments(entries, theta):
    prev = F(0)
    for e, a in entries:
        now = min(a, theta)
        if now > prev:
            yield e, now - prev
        prev = now


def count_check(theta, available, budget=F(3)):
    """Actual weighted subset count using a polynomial DP, not the bound."""
    t = theta.denominator
    assert theta == F(1, t)
    cap = int(budget * t)
    dp = [0] * (cap + 1)
    dp[0] = 1
    for entries in available:
        old = dp
        dp = old.copy()
        for a in entries:
            if a < theta:
                continue
            units = int(a * t)
            for s in range(cap - units + 1):
                dp[s + units] += old[s]
    return sum(dp)


def run_constants():
    base = 2**23 * F(187, 768)**12
    assert base < F(1, 2)
    assert F(1631, 600) < F(11, 4)
    assert 12 * F(17, 416) == F(51, 104) < F(1, 2)
    assert 3 * (1 - F(17, 64)) == F(141, 64) > 2
    vals = {}
    for t in (1, 2, 4, 8, 16, 32, 64):
        g = F(t ** (12*t) * 17 ** (12*t+1) * 2 ** (23*t),
              16 ** (12*t+1) * factorial(12*t+1))
        assert g <= F(17, 416)
        vals[str(t)] = float(g)
    # A deliberately weaker exponential estimate does NOT certify the margin.
    bad_base = 2**23 * F(17, 64)**12  # replacing e by 3
    assert bad_base > F(1, 2)
    results['constants'] = {
        'exact_base': str(base), 'base_upper_bound': '1/2',
        'exact_cross_product_gap': base.denominator - 2*base.numerator,
        'G_diagnostics': vals,
        'negative_control_e_bound_3_fails': str(bad_base),
    }


def run_preprocessing():
    rng = random.Random(70816)
    ps = primes_from(101, 80)
    comparisons = 0
    nonvacuous_hinges = 0
    max_loss = F(0)
    for trial in range(140):
        levels = {}
        exponents = {}
        for p in ps:
            cut = F(rng.choice((1, 7, 15, 31, 63)), 64)
            levels[p] = [(1, cut), (2, F(1))]
            exponents[p] = 2 if trial == 0 else rng.choice((0, 1, 2, 2, 2, 2, 2, 2, 2, 2))
        k = prod(p**e for p, e in exponents.items())
        m = max(k * rng.choice((1, 2, 64)), max(ps)**2 * 64 + 1)
        new = preprocess(levels, m)
        h, hb = mean(levels), mean(new)
        assert h < F(17, 16)
        assert hb <= h
        original = sum(contribution(levels[p], e) for p, e in exponents.items())
        rounded = sum(contribution(new.get(p, []), e) for p, e in exponents.items())
        assert original <= 2*rounded + 32
        assert max(original-64, 0) <= 2*max(rounded-16, 0)
        nonvacuous_hinges += original > 64
        max_loss = max(max_loss, original - 2*rounded)
        for p, entries in new.items():
            assert len({a for _, a in entries}) == len(entries)
            assert sum(a for _, a in entries) <= 2*entries[-1][1]
            for e, a in entries:
                assert (p**e)**(16*a.denominator) <= m
        comparisons += 1
    assert nonvacuous_hinges > 0

    # A family where the removal costs >16, so omitting the rounding loss fails.
    close_primes = primes_from(1000003, 31)
    m = prod(close_primes)
    levels = {p: [(1, F(63, 64))] for p in close_primes}
    new = preprocess(levels, m)
    assert not new
    original = 31 * F(63, 64)
    assert original > 16 and original < 32
    assert max(close_primes) <= m//64
    assert mean(levels) < F(17, 16)
    results['preprocessing'] = {
        'seed': 70816, 'instances': comparisons,
        'positive_original_threshold_64_hinges': nonvacuous_hinges,
        'largest_sample_S_minus_2B': str(max_loss),
        'negative_control_loss_16_fails': {
            'primes': close_primes, 'm': str(m),
            'original_mass': str(original), 'retained_mass': '0',
            'H': str(mean(levels)),
        },
    }


def run_carrier_counts():
    rng = random.Random(160708)
    cases = []
    for t in (1, 2, 4, 8, 16, 64):
        theta = F(1, t)
        for nprimes in (3, 10, 30, 193):
            available = []
            for _ in range(nprimes):
                values = [F(2**j, t) for j in range(t.bit_length())]
                values = [v for v in values if rng.randrange(4) != 0]
                available.append(values)
            count = count_check(theta, available)
            neligible = sum(any(a >= theta for a in vals) for vals in available)
            bound = 2 ** (3*t + neligible)
            assert count <= bound
            cases.append({'t': t, 'primes': nprimes,
                          'count_bits': count.bit_length(),
                          'bound_bits': bound.bit_length()})

    # Higher-level stress: a prime may have a tiny carrier mass and unit mass at n.
    theta = F(1, 64)
    available = [[theta, F(1)] for _ in range(192)]
    count = count_check(theta, available)
    assert count <= 2 ** (3*64 + 192)

    # The dyadic hypothesis is essential. At p=2 use 10,000 distinct cumulative
    # values in (1/2,1), plus unit anchors at 3 and 5, and last mass 1/2 at 7.
    # Each p=2 level gives a positive-weight carrier 2^e * 3 * 5 * 7.
    # At n divisible by every level, T_(1/2)=2, so the false uncompressed bound
    # would be 2^((3+2)/(1/2))=1024; actual last-7 choices are 10,000.
    raw_count = 0
    claimed_uncompressed_bound = 2**10
    for e in range(1, 10001):
        a = F(10000+e, 20001)
        assert F(1, 2) < a < 1
        assert 2+a < 3 and 2+a+F(1, 2) > 3
        prefix_weight = min(2+a+F(1,2), F(3))-max(2+a, F(2))
        raw_count += prefix_weight > 0
    assert raw_count > claimed_uncompressed_bound
    results['carrier_count'] = {
        'cases': cases,
        'higher_level_stress_actual_count': str(count),
        'negative_control_no_dyadic_compression': {
            'actual_count': raw_count,
            'false_bound': claimed_uncompressed_bound,
            'last_mass': '1/2', 'capped_mass': '2',
        },
    }


def run_exact_carrier_system():
    ps = primes_from(101, 33)
    p0, sap = ps[0], ps[1:]
    levels = {p: [(1, F(1, 2))] for p in sap}
    levels[p0] = [(1, F(1, 2)), (2, F(1))]
    all_sap = prod(sap)
    period = all_sap * p0**2
    m = period * 10**20 + period//7 + 12345
    assert preprocess(levels, m) == levels
    h = mean(levels)
    assert h < F(17, 16)
    # All hot effective patterns, classified independently by their masses.
    patterns = []
    patterns.append(([(p,1,F(1,2)) for p in sap] + [(p0,1,F(1,2))],
                     m//(all_sap*p0)-m//period, F(1,2)))
    patterns.append(([(p,1,F(1,2)) for p in sap] + [(p0,2,F(1))],
                     m//period, F(1)))
    for missing in sap:
        modulus = (all_sap//missing)*p0**2
        patterns.append(([(p,1,F(1,2)) for p in sap if p != missing] + [(p0,2,F(1))],
                         m//modulus-m//period, F(1,2)))
    carried = defaultdict(F)
    metadata = {}
    l_value = F(0)
    for atoms, count, deficit in patterns:
        assert count >= 0
        assert sum(a for _, _, a in atoms) - 16 == deficit > 0
        l_value += count*deficit
        atoms = sorted(atoms, key=lambda item: (-item[2], item[0], item[1]))
        s, modulus, support, total_w = F(0), 1, [], F(0)
        for p, e, a in atoms:
            old = s
            s += a
            modulus *= p**e
            support.append(p)
            w = max(F(0), min(s,F(3))-max(old,F(2)))
            if w:
                assert 2 < s < 4
                carried[modulus] += count*deficit*w
                data = (tuple(support), a, s)
                assert modulus not in metadata or metadata[modulus] == data
                metadata[modulus] = data
            total_w += w
        assert total_w == 1
    assert sum(carried.values()) == l_value > 0
    coeff = {}
    signed = defaultdict(F)
    for P, mass in carried.items():
        support, theta, mu = metadata[P]
        r = int(12/theta)+1
        eps = theta**(2-r)*h**r/factorial(r)
        assert mass <= eps*F(m,P)
        c = mass/(m//P)
        assert c <= 2*eps
        assert P**4 < m
        coeff[P] = c
        signed[P] += 3*c
        for p, entries in levels.items():
            if p in support:
                continue
            for e, beta in capped_increments(entries, theta):
                D = P*p**e
                assert D**16 < m**5
                signed[D] -= F(3,16)*c*beta

    def count_window(d, x):
        return (x+m)//d - x//d

    starts = [0, period//2, period*123456789+period//3,
              factorial(500)-m, factorial(500)-m//2]
    values = []
    for x in starts:
        assert x >= 0
        value = sum(c*count_window(d,x) for d,c in signed.items())
        lower = 3*(1-h/4)*l_value
        assert value >= lower >= F(141,64)*l_value
        values.append({'x':str(x), 'value':str(value),
                       'value_over_L_B':str(value/l_value)})

    rng = random.Random(7081601)
    for trial in range(1200):
        exponents = {p:rng.randrange(2) for p in sap}
        exponents[p0] = rng.randrange(3)
        if trial % 100 == 0:
            exponents = {p:1 for p in sap}
            exponents[p0] = 2
        n = prod(p**e for p,e in exponents.items())
        bval = sum(contribution(levels[p],e) for p,e in exponents.items())
        via_divisors = sum(c for d,c in signed.items() if n%d == 0)
        via_formula = F(0)
        for P,c in coeff.items():
            if n%P:
                continue
            support, theta, mu = metadata[P]
            u = sum(min(contribution(levels[p],e),theta)
                    for p,e in exponents.items() if p not in support)
            via_formula += 3*c*(1-u/16)
        assert via_formula == via_divisors
        assert via_formula <= max(bval-1,0)

    results['exact_nonvacuous_multilevel_system'] = {
        'primes':ps, 'p0_levels': ['1/2','1'], 'other_prime_mass':'1/2',
        'm':str(m), 'H_B':str(h), 'L_B':str(l_value),
        'hot_effective_patterns':len(patterns), 'carriers':len(carried),
        'combined_signed_moduli':len(signed),
        'positive_coefficients':sum(c>0 for c in signed.values()),
        'negative_coefficients':sum(c<0 for c in signed.values()),
        'pointwise_formula_samples':1200,
        'window_value_checks':values,
        'scope':'An exact threshold-16 intermediate system, not a numerical proof of universal SC_64.',
    }


if __name__ == '__main__':
    for name, fn in [('constants',run_constants),
                     ('preprocessing',run_preprocessing),
                     ('carrier counts',run_carrier_counts),
                     ('exact carrier system',run_exact_carrier_system)]:
        fn()
        print(name + ': PASS', flush=True)
    (ROOT/'exact_checks.json').write_text(json.dumps(results,indent=2)+'\n')
    print('All exact checks passed. Detailed results: exact_checks.json', flush=True)
