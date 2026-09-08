# Erdős 708 rounding campaign — route ledger

Started 2026-09-07 14:24 UTC. No wall-clock cap. The brief's 45-minute first-pass allotments are route review points, not a campaign cap. A settled target can end the campaign; otherwise two successive unchanged gap reviews freeze a route before lowering. Refutation agent started first at approximately 14:25 UTC. All writes are confined to this directory; no git or internet.

The exact LP is the **uncapped** valuation LP in paper equation (LP), with 0≤y≤1. In particular v_p(x+t) is not capped by the input demand. G denotes the integral minimum for an instance, and τ the optimum of this LP.

| Route | Advantage | Weakness | Obstacle / initial gap | Verification bridge | Status |
|---|---|---|---|---|---|
| R1 Iterative/dependent rounding | At a vertex only prime rows can support fractional variables. | Valuations can be arbitrarily large and the cross-prime sets are not laminar. | Need an arithmetic charge ≤n for the cost of rounding fractional support. | Exact rational primal/dual and DP; prove each exchange preserves every valuation demand. | Active, root |
| R2 Integral large primes, fractional small primes | Only π(cn)=o(n) small-prime rows remain. | Fixing integral elements can raise the residual fractional optimum. | Need total large-prime forcing cost, relative to τ, ≤n−π(cn). | Residual LP identity and exact CRT/HR tests. | Active, large_prime_rounding agent |
| R3 Modified LP | Capped valuations or knapsack cover constraints remove individual huge-valuation fractions. | Stronger relaxation can cost much more than original τ. | Need both a rounding theorem and a value theorem for the actual modified LP. | Integral equivalence, feasible lifts, exact separating instances. | Active, modified_lp agent |
| R4 Exact/asymptotic refutation | Arbitrary x allows CRT control of prime powers. | Finite numerical gaps alone cannot establish a uniform asymptotic obstruction. | Need exact G and τ on a growing explicit family. | Rational primal/dual equality, exact DP, distinct interval witnesses. | Active, refutation agent; runs first |
| R5 Pseudoforest/cycle interpolation | Existing input-incidence theorem is proved. | Input cycle rank need not reflect output LP rounding loss. | Need a proved comparison between β_H and τ or G−τ. | Exact x=0 and reflected controls; inspect high-cycle families. | Active, root |

## Target interpretation

T1 contains three different alternatives: additive o(n), additive n, and a fixed multiplicative factor plus a fixed additive constant. Refuting one does not refute the others. T2's standard mathematical notation “≫n” means an Ω(n) lower bound; a gap approaching n suffices for that reading, but does not mean a superlinear gap or refute additive n. The report will state this distinction expressly.

## Initial gap review — 14:27 UTC

Candidate R4 construction: n large distinct input primes, each with a unique interval multiple of valuation at least K, at different positions; CRT prescribes those positions. Then G=n and τ≤n/K. Pending complete existence proof and exact audits. No route is frozen.

Gap: prove and independently verify the CRT family giving G=n and τ≤n/K; additive loss≤n remains a separate open target.

## Success review — 14:36 UTC

The campaign has reached the brief's **settled-target** stopping condition: R4 proves T2 in its standard Ω(n) meaning, with exact G=n, τ=n/K for every n and K≥2. The global desired consequence 18n+o(n) is also proved by a hybrid argument. No route is described as frozen; the two-unchanged-gap rule is unnecessary when a target is settled. The 45-minute first-pass review points have not arrived, and no elapsed-time cap was used. Lowered T3 targets were not activated after success; R3's formulation work belongs to the originally specified R3 route.

| Route | Final claim / finding | Verification bridge completed | Remaining gap / status |
|---|---|---|---|
| R1 | Strict vertex rounding G<τ+r; demand integrality, laminarity, and total unimodularity do not justify a sublinear loss. | Complete support-count proof; exact CRT diagonal K·Id; explicit determinant −2 and crossing sets. | **OPEN:** universally charge the rounding increase by n. Stopped at campaign success, not frozen. |
| R2 | **PROVED:** g(n)≤19n and g(n)≤18n+π((18n)^(19/34))−1. Sharper r≤n+π(√m), combined with supplied k-split, gives the result. | Complete proofs in r2_large_prime_bounds.md, independently audited by root and modified_lp. | No gap in these global bounds. **OPEN:** G≤τ+n uniformly; direct long-interval branch does not imply an instancewise LP comparison. |
| R3 | **PROVED:** demand-capped and level LP values ≤17n via a generalized monotone-valuation hinge theorem; demand capping is integral-equivalent. **REFUTED:** level LP integral equivalence. | Complete primal/dual argument; 13 exact one-prime tests, independently checked. | **OPEN:** additive-n rounding for the modified polytope. Value bridge solved. |
| R4 | **PROVED T2:** G−τ=(1−1/K)n. **REFUTED:** uniform o(n) loss and fixed ατ+C bounds. | Exact CRT formula, elementary prime-band existence, rational primal=dual, exact DP; all 85 distinct tested instances settled. | No gap in linear-loss T2. No claim of superlinear loss, loss>n, or refutation of additive n. |
| R5 | **REFUTED:** β_H≤G−τ, by A={30,42,70,105}, x=210^10−1, β_H=5, G−τ=7/10. | Exact dual, one-element cover, native DP recheck, explicit graph count. | **OPEN:** an alternative quantitative comparison supporting the proposed interpolation. |

The finite search comprises 93 jobs across 85 distinct instances, including CRT/ES, HR, reflected, and modified-LP controls at n≤12. All exact optima are settled. Five DP state-cap exclusions are retained and subsequently repaired by exact rational dual lower bounds matching integral witnesses. The observed maximum (G−τ)/n is 99/100.

Gap: T2 and the global bounds g(n)≤19n and g(n)≤18n+o(n) are proved; the universal instancewise bound G≤τ+n and additive-n rounding for modified LPs remain OPEN.
