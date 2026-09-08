# Hinge campaign route ledger

Started 2026-09-08 19:05 UTC. Single agent; no git or internet; all campaign writes stay in this directory. T1 and T2 have equal rank. T3 opens only after both freeze. Each route receives a judge decision before another route-sized allocation; two consecutive unchanged gap sentences freeze it. Decisions concern the uniform gap, not computation counts.

| Route | Advantage | Weakness | Obstacle | Verification bridge | Status |
|---|---|---|---|---|---|
| R-a, elimination / K4 | Existing four-prime base; handles multilevel layers exactly | K4 alone covers only five primes | Uniform prime-power antichain estimate, then extension beyond five | Exact frontier enumeration, layer counts, complete analytic bound | Frozen for uniform T1; fixed-support theorem proved |
| R-b, domination after summation | Avoids the six-prime nonnegative pointwise obstruction | A divisor minimum can undercount multiple incomparable witnesses | Uniform prefix tail versus window layer count | Exact layer-tail checks on all required adversarial families | Frozen for uniform T1 |
| R-c, signed certificate at 2 | Signed coefficients survive R7 | Negative-modulus errors and rounding loss dominate at low threshold | Feasible signed family with sufficient window value for every sparse system | Explicit coefficients, exact floor counts and pointwise checks | Frozen at 2; lowered to T3 |
| R-d, exact refutation | A single rational witness resolves T2 | Periods and weight arrangements grow rapidly | A strictly negative rational hinge gap | Integer-scaled hinge sums, CRT residues, full-period finite scans where feasible | Frozen; no counterexample |

## Source audit

R8 in the brief overstates the paper: the restrictions “at least two multilevel” and “some total weight > 1/2” are established only for exactly five active primes. For N >= 6 the cap available is 2/(N-1), not 1/2. Its nonempty example has only one multilevel prime. Use the paper's broader reduction (m/6 truncation, >=5 primes, m>=66, positive LHS, H<h0 and mu-H²/6<1), with the extra restrictions only in the five-prime branch. No refutation of H2 follows from this correction.

R4's certificate is BELOW the right hinge pointwise and ABOVE the left hinge after prefix summation; “dominates the right hinge” in the prose has its order reversed.

Gap: a proof or exact counterexample is missing for all atom systems, all m, and all windows in the corrected sparse remaining case.

## Judge round 1 (after adversarial pass and first allocations)

- R-a: CONTINUE. The frontier sweep checked four prime quadruples for every Q<=100000. More substantially, a geometric-series argument proves K4 uniformly for Q>=4900014488437221682. The exact finite sweep for {2,3,5,7} closes the gap below that cutoff: 1763328 exponent states, 35109 nonempty frontier intervals, finite maximum 101/105 at Q=2. This proves K4 for that fixed prime set for ALL Q, hence unrestricted five-prime H2 when four active primes are 2,3,5,7. Gap: missing a uniform argument for other prime supports and for six or more primes, for all m and all windows.
- R-b: CONTINUE for one narrowed assessment. The unrestricted minimum-modulus layer estimate is REFUTED: unit weights on primes through 71, M=1000000, c=1/2 give 551993 prefix points with T>1+c but floor(M/Q)=500000, Q=2. This example is in the affine dense branch (mu-H²/6>1), so it does not refute the restricted sparse version. Gap: missing a prefix-to-layer estimate on the sparse remaining case for arbitrary numbers of multilevel primes, all m and all windows.
- R-c: CONTINUE for one narrowed assessment. Reusing the eight-mantissa retention rule at c=2 is REFUTED on an exact six-prime, two-multilevel, truncated sparse system: S(m)=68/25 but B(n)<=1/50 everywhere, hence no mass>1 carrier exists. Gap: missing a different signed finite family with pointwise feasibility and sufficient window value on every sparse remaining system, all m and all windows.
- R-d: CONTINUE. No H2 counterexample in 116424000 full-period window instances, including 106444800 satisfying a certified subset of the sparse conditions. Weight choices and m choices were sampled, not exhaustive. Gap: missing an exact negative hinge gap on an untested atom system, m and window, or a uniform exclusion of all such gaps.

## Judge round 2 (narrowed assessment)

- R-a: the additional 74-support sweep through Q=1000000 does not bridge arbitrary prime supports. The large-Q proof bounds a sum over all exponent vectors and leaves a finite Q range but infinitely many prime supports. Even full K4 would handle only five primes; K5's Boolean majorant already exceeds 1. Gap: missing a uniform argument for other prime supports and for six or more primes, for all m and all windows.
- R-b: the fixed-support K4 result gives the precise valid five-prime layer certificate; it supplies no induction step over an arbitrary five-prime base. The dense obstruction can be excluded but this does not prove the needed sparse layer inequality. Gap: missing a prefix-to-layer estimate on the sparse remaining case for arbitrary numbers of multilevel primes, all m and all windows.
- R-c: narrowing to R8 does not remove the retention obstruction: the recorded example itself has six primes, two multilevel, H<1, all atoms<=m/6 and positive LHS. Altering retention would require a new simultaneous rounding and negative-modulus budget proof, absent here. Gap: missing a different signed finite family with pointwise feasibility and sufficient window value on every sparse remaining system, all m and all windows.
- R-d: no counterexample in 215838 additional sampled windows on seven/eight primes (199962 in a certified subset of the sparse remaining case). The period reduction and d! vertex bound do not make these samples exhaustive. Gap: missing an exact negative hinge gap on an untested atom system, m and window, or a uniform exclusion of all such gaps.

Judge decision: each route's last two gap sentences are unchanged. Freeze R-a/R-b/R-c for uniform T1 and R-d for T2. Retain the proved fixed-support K4 and five-prime theorem; neither is a claim of T1. Open T3 now: improve the global signed-certificate threshold below 56501/6400. No wall-clock stopping criterion was used.

## T3 allocation and judge record

The first coefficient allocation (through approximately 19:24 UTC) replaced the dense-branch mean by 1000003/1000000, used outside-prime counts at small last levels, and selected rational K values. Judge: the discovery sum at T=267/50 was below 1 but required exact scales and a new infinite-tail certificate. Move to the retention allocation before further coefficient optimization.

The retention allocation improved D0 from 3601/1280 to 28407/10240. Its 4479 finite carrier constraints were checked during discovery, then independently replaced by the exact prefix-budget recurrence for the proof. Judge after 5000 trials: retain the candidate table; its global use still required the complete signed-certificate audit. After 20000 additional trials the loss was unchanged. Gap: missing a uniformly certified threshold below the best assembled candidate through a better retention or coefficient bound, for all atom systems, all m and all windows.

The second retention assessment exhausted 176 feasible single-unit neighbors without an improvement. The coefficient assessment proved the exact scale bound at T=5337547/1000000; the immediately smaller 10^-6-grid parameter gave a bound greater than 1 through L=512. Gap: missing a uniformly certified threshold below the best assembled candidate through a better retention or coefficient bound, for all atom systems, all m and all windows.

Judge: freeze further parameter optimization in this campaign. This is not a global optimality claim. Complete the exact audit and written proof of the retained candidate.

## Final judge (2026-09-08 19:46 UTC)

T3 **PROVED**: H_c for c=280923567/32000000=8.77886146875, for all atom systems, all m and all windows. The exact total multiplier is 499998420228283/500000000000000<1. The full verification script passed, including all 65 scales, the analytic tail, selected moment crosschecks, fixed-support K4 and actual signed families. Full proofs and the dependency block are in report.md. No kernel verification is claimed. T1/T2 remain open; the fixed-support five-prime result is retained separately.

Gap: H2, its refutation, and every global threshold below 280923567/32000000 remain unproved here for all atom systems, all m and all windows.
