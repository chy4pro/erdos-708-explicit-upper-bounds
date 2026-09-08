# PROOF CAMPAIGN — Erdős 708: the rounding loss (GPT-6 Astra; no wall-clock cap)

## Where the constant now comes from
g(n) ≤ (c+16)n is proved for the hinge threshold c = 17 (paper v13, all kernel-checked: lean/proofenv/Erdos708/H17/, lean/README.md in the repo):
the fractional cover value τ*(A,x) of the LP of Section 7 (paper /Users/roychen/workspace/claudecode/automath/papers/erdos708/main.tex) is at
most c·n, and Lemma round turns a fractional cover into an integral one with at most (number of primes dividing ∏A) extra elements, which is
< 16n when a_n < 8n³ (Lemma fewprimes); for a_n ≥ 8n³, 2n suffice outright (Theorem long). The rounding term 16n is now LARGER than the
threshold term. Every unit removed from it improves the world record for Erdős's $100 question directly. (The 2n campaign proved that τ*/n can
approach 2 on explicit CRT sequences, so the LP route can never beat 2n by the fractional value alone; the rounding is the other half.)

## Targets (prove-or-refute at equal rank; no time cap; stop only when settled or every route and lowered target is frozen)
T1: prove that for every instance (A, x) there is an integral cover B ⊆ I with |B| ≤ τ*(A,x) + o(n) (explicit o(n)), or ≤ τ* + n, or ≤ (1+ε)τ* + C.
    Any of these with the proved threshold 17 gives g(n) ≤ 18n + o(n), 18n, or (1+ε)17n + C — a large improvement of 33n.
T2: prove a lower bound showing the rounding loss can be ≫ n for the LP as formulated (an explicit family with τ* small but every integral
    cover large), which would show the LP route is capped and redirect the whole line — equally valuable; exact instances required (our exact
    DP problems/erdos708/repo/src/gn_dp.py recomputes g(A,x), and problems/erdos708/hotset_lp.py-style LPs recompute τ*).
T3 (lowered targets, only after T1/T2 freeze): rounding loss ≤ n for a_n ≥ n^{2+ε}; or a modified LP (e.g. over prime powers, or with the
    long-interval structure) whose integrality gap is provably ≤ n.

## PROVED tools (Sections 5, 7, 13–15; Lean-checked; use as black boxes)
Duality (Lemma dual): τ* = max over weights z ∈ [0,1]^primes of Σ_{a∈A} w_z(a) − Σ_{b∈I}(w_z(b) − 1)^+, attained in the cube.
Rounding (Lemma round): from an optimal fractional cover y ∈ [0,1]^I, the set {b : y_b > 0}… (read the exact statement and proof in main.tex;
the loss is bounded by the number of primes whose demand is met fractionally). Few primes (Lemma fewprimes). Long intervals (Theorem long,
k-split). Hinge inequalities with thresholds 65 and 17 (all weights), 4 (0/1 weights). Exact small values g(3)=4, g(4) ≥ 5, g(5) ≥ 6.
Structural 2n theorem (engine/harvest/astra_708_2n.md): after discarding inputs with ≤ 2 distinct prime factors, if every component of the
shared-prime incidence graph has at most one cycle then 2n suffice (pseudoforest criterion), and 2n + 2β_H in general.

## Dead routes
D1 Bounding the loss by the number of primes: it can be ≍ n, so no o(n) this way. D2 Naive independent rounding of y (Bernoulli) fails on
prime-power demands. D3 Reductions to unweighted matchings / Laplace inequalities refuted on Hensley–Richards windows (test every intermediate
statement on such windows). D4 Two-sided multiple counts alone cannot give absolute thresholds (projective planes).

## Routes (v2.5: routes.md with ≥4 routes × advantage/weakness/obstacle/verification bridge; 45-minute first pass each; judge extends; the
## only progress metric is the gap sentence; two unchanged ⇒ freeze and lower; refutation agent runs first: compute τ* and g(A,x) exactly on
## CRT/HR/reflected instances at n ≤ 12 and report the maximum observed integrality gap (g − τ*)/n with witnesses)
R1 Iterative rounding / dependent rounding with the prime-power incidence structure (each window element b serves the atoms it contains;
   the LP is a covering LP with demands per prime; look for a laminar or matroid structure on the constraints that gives loss ≤ n or ≤ #cycles).
R2 Greedy + LP: assign the large primes (p > n) integrally first (each such prime divides ≤ (a_n/p)+1 window elements; the LP restricted to
   small primes has fractional value bounded by the hinge), then round the small-prime LP whose primes number only π(n) = o(n).
R3 Modify the LP: prime-power constraints (demand v_p(∏A) at each p^j level) or a flow formulation; prove its integrality gap is ≤ n and that
   its value is still ≤ τ* + O(hinge) — the goal is a formulation whose polytope is integral or nearly so.
R4 Refutation: build instances with τ* ≈ n but integral covers ≥ 1.5n (the Erdős–Surányi construction has g ≈ 2n with τ* ≈ ?; compute τ* exactly
   on those instances first).
R5 Use the pseudoforest theorem: cover the pseudoforest part with 2 per input and bound the cyclic excess β_H via the LP; an integral cover of
   size 2n + O(β_H) with β_H ≤ (loss of the LP) would already give an interpolation.

## Output contract
engine/out/astra_708_rounding/: routes.md, refutation_log.md (τ* and g on every instance tried, max gap, witnesses), checkpoint.md every 30
minutes ending with the gap sentence, report.md with every claim PROVED / CONDITIONAL / REFUTED / OPEN, complete proofs, exact witnesses,
"final claim ← lemmas ← unproved items". No cap. Touch nothing outside this directory (read anything); no git; no internet.
