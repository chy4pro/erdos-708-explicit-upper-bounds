# Internal audit of the signed-certificate argument

PROVED (audit scope): this is a local mathematical audit, supplemented by exact rational checks. No external referee or Lean kernel has certified the argument.

| Claim or possible failure | Status | Resolution |
|---|---|---|
| Rounding can increase some atom increments, so coordinatewise comparison of the new mean would be invalid | PROVED | Compare the functions over a common complete period. Pointwise B <= S implies H_B <= H even when individual increments increase. |
| Pruning levels might change a retained cumulative mass | PROVED | Define the new increments as differences of consecutive retained values. They telescope to exactly the retained dyadic value. |
| The cost removal might only give a per-prime, rather than a total, loss | PROVED | The first moduli attaining the bad rounded values are at distinct primes and their product divides k. Summing their logarithms gives one total loss of 32. |
| The threshold after preprocessing might be wrong | PROVED | S <= 2B+32 gives (S-64)^+ <= 2(B-16)^+, exactly the threshold used for the new carried masses. |
| The residual moment order might be off by one | PROVED | Carrier mass is strictly below 4, so residual mass exceeds 12. With theta=1/t, t a positive integer, the hinge moment order is 12t+1. |
| The exact splitting in Lemma A might fail at higher prime powers | PROVED | It is used only for a carrier built from k's own effective levels. At an arbitrary window point the proof uses capped mass and excludes every prime dividing P. |
| The new carrier count might silently ignore arbitrarily many levels | PROVED | Retained masses at one prime are distinct dyadic values. The generating weight sum sum_j 2^(-2^j) <= 1 bounds all levels at once. |
| A prime occurring in a carrier may have much larger mass at the tested point n | PROVED | min(b_p(n),theta_P)=theta_P for each p dividing P, regardless of upgrades. Thus U_P=T_theta-theta*omega(P), with theta*omega(P)<4. |
| High total B but small capped T_theta might evade the signed cutoff | PROVED | Feasibility does not require every such term to be negative. Positive terms are counted at their own T_theta<20, and the sum of all possible last masses is at most 2B. |
| A negative extension can exceed m, making its +1 count error unaffordable | PROVED | log P<log(m)/4 and every retained atom modulus q<=m^(1/16). Thus Pq<m^(5/16)<m. |
| A negative extension can overlap a prime of P | PROVED | Those primes are excluded in U_P. Every extension uses a coprime q, so its modulus is exactly Pq. |
| Combining equal signed moduli might invalidate the lower bound | PROVED | The value is bounded before combining terms, using a lower bound on each positive term and an upper bound on each subtracted nonnegative term. Combining is a finite sum identity. |
| The pointwise estimate has enough room at B just above 2 | PROVED | g <= (51/104)B < B/2 <= B-1 for B>2. For B<=2 no carrier divides n. |
| The interval-value multiplier pays for the factor 2 lost in preprocessing | PROVED | 3(1-H_B/4) >= 141/64 > 2. The resulting original factor is 141/128. |
| The existing reflected-window obstruction rules out this certificate | REFUTED | The actual round-13/14 statements concern nonnegative certificates. This certificate has essential negative coefficients. |
| The new argument establishes the original (NC) | OPEN | It does not. It establishes the brief's alternative T1 target, SC_64, directly. |

PROVED (validation record): `exact_checks.py` checks 140 preprocessing systems, including 121 with positive original threshold-64 hinges; 24 exact weighted counting instances; a higher-level stress case; and a nonzero threshold-16 system with 33 primes, one two-level prime, 34 hot effective patterns, 11 carriers, and 309 combined signed moduli. The latter has 298 negative coefficients. Its carried masses, interval values on five windows, and 1,200 pointwise evaluations are checked with fractions and integers.

PROVED (negative controls): the checks reject a preprocessing loss of 16, reject the capped carrier count without dyadic compression, and reject use of the coarser numerical bound e<3 for the chosen constant estimate. These are tests of possible incorrect arguments, not counterexamples to SC_64 or (NC).

PROVED (test repair record): the first preprocessing test generator produced no positive threshold-64 hinge; its explicit nonvacuity assertion failed, and the generator was corrected to produce hot inputs. The first uncompressed-count negative control included an endpoint equal to 1/2 instead of strictly above it; its strict-inequality assertion failed, and its denominator was corrected from 20002 to 20001. Neither repair changes the mathematical proof or its constants. The complete corrected suite passes.
