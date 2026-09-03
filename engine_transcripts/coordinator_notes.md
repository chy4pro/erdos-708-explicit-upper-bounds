# Erdős #708 — dialogue working notes (2026-09-03)

Statement (Er92c §1): g(n) = least g such that for every 1 < a_1 < … < a_n and every x ≥ 0 some g integers in
(x, x + a_n] have product ≡ 0 mod ∏a_i. Known: g(2)=2, g(3)=4, g(n) ≥ (2−o(1))n (ES 1959). No upper bound recorded.

## Verified facts (gn_dp.py = exact min|B| by DP over capped valuation vectors)
- ES family l=3 (17,19,23), x=74072 → 4; l=4 (41,43,47,53), x=26348553 → 6 (p_i² multiples save one element each).
- P17 intermediate examples: A=(10,12,15,20), x=50 → 5 (mechanism: 25 > a_n = 20, so E_5 = 3 costs three 5-multiples,
  all with poor 2/3-valuations); A=(5,10,12,15,20), x=50 → 6. Hence g(4) ≥ 5, g(5) ≥ 6. Worst x < 3600 same.
- Per-prime dominance (easy lemma): #{a ∈ A : p^j | a} ≤ ⌊a_n/p^j⌋ ≤ #{b ∈ I : p^j | b}; hence for each prime p an
  injection φ_p : {a : p | a} → I with v_p(φ_p(a)) ≥ v_p(a) exists (nested Hall). Gives only |B| ≤ Σ_a ω(a) (non-linear).
- Trap (both Q20 responses): a shared element contributes its valuation ONCE. Mandatory test for any algorithm: the l=3
  ES instance must output ≥ 4 elements.
- Distinct-multiples matching for a ≤ a_n/2 is NOT available: van Doorn–Li–Tang (arXiv 2603.28636, Erdős #650) —
  an interval of length 2·max(A) guarantees only min(m, ⌈2√m⌉) disjoint (a, multiple) pairs, optimally.

## Reformulation worth attacking (dialogue): the split-assignment problem
Choose for each a a factorisation a = d₁(a)·d₂(a) with gcd(d₁,d₂) = 1 (d₂ = 1 allowed) and assign each of the ≤ 2n
"demands" d ∈ {d₁(a), d₂(a)} to an element β(d) ∈ I such that for every element b and every prime p,
Σ_{d : β(d) = b} v_p(d) ≤ v_p(b). Then B = β(demands) has |B| ≤ 2n and ∏A | ∏B.
Conjecture S: such a split and assignment always exist. S ⇒ g(n) ≤ 2n. S holds on the ES family (halves = the two primes;
u absorbs one demand per prime, singles the rest). S is a finite integer-feasibility question for each (A, x) — test it
by ILP/backtracking on adversarial instances before any proof attempt. Where S could fail: several a's sharing a prime p
with p² > a_n (each element then absorbs ≤ 1 unit of p) — but #{a : p | a} ≤ ⌊a_n/p⌋ ≤ #multiples of p in I, so the
p-units alone always fit; failures must come from cross-prime packing.
Weaker but still new: any assignment with k demands per a ⇒ g ≤ k·n; a 3-split (T2 with C = 3) may be provable first.

## S test results (22:18 CDT)
split_assign.py: S feasible on ES l=3, ES l=4, P17's (10,12,15,20)/x=50 and (5,10,12,15,20)/x=50, and 965,773 random instances (n ≤ 5, a_n ≤ 60): 0 infeasible.
Structural observation: capacity constraints are per prime; composite demands are the only cross-prime coupling; S holds outright when every a has ≤ 2 distinct primes (finest split + per-prime dominance). Counterexamples, if any, need a's with ≥ 3 primes and scarce composite multiples.
Gacha (search_small_n.py, a_n ≤ 60): n=4 best 5 (P17's instance), n=5 best 5 — no instance beyond P17's.
