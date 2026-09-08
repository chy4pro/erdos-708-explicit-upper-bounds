PASS-WITH-REPAIRS — C1, C2, C3, C4 and the F1/F2 refutations are CONFIRMED as stated and no mathematical error was found anywhere; the R3 value bounds (C5) are correct but NOT derivable from the four black boxes as literally given — they need the atom-system hinge inequality thm:h17, not "τ*≤17n" — and four presentational/bookkeeping defects need repair.

# Adversarial referee report — `engine/out/astra_708_rounding/report.md`

Referee: Claude Opus 5, blind adversarial mode. Date 2026-09-07.
Method: every displayed inequality re-derived from scratch from the four black boxes only; every finite witness recomputed independently in exact rational arithmetic; the cited source theorems in `papers/erdos708/` read to check that the report's paraphrases of them are faithful; the three shipped verifiers re-run; and every one of the 85 distinct integral optima independently certified (36 by the exact LP dual with G = ⌈τ*⌉, 29 structurally, 8 by my own exhaustive-subset / capped-state-DP search, 12 trivially). No file in the campaign directory was modified.

---

## C1. g(n) ≤ 19n for every n ≥ 1 — **CONFIRMED**

Every step checks out, including the two places where the argument is genuinely delicate.

1. **r ≤ n + π(√m).** If p ≠ q are both > √m and both divide some a ≤ m, then pq > m ≥ a. So each a contributes at most one distinct prime factor > √m, giving ≤ n such primes across A; the rest are ≤ √m, giving ≤ π(√m). Every p ∈ P divides some a ≤ m, so P is exhausted. Correct.
2. **Strict rounding G < τ* + r.** With y* an optimal vertex, F = {b : 0 < y*_b < 1}, B = {b : y*_b > 0}: B covers because y* ≤ 1 and Σ_b v_p(b)y*_b ≥ R_p; and |B| = #{y*=1} + |F| = τ* − Σ_F y*_b + |F| = τ* + Σ_F(1 − y*_b). If F ≠ ∅ each summand is < 1 strictly (y*_b > 0), so |B| < τ* + |F| ≤ τ* + r. If F = ∅ then |B| = τ* < τ* + r because r ≥ 1 (n ≥ 1 and every a > 1, so ∏A has a prime factor). Correct, and the |F| ≤ r input is exactly the vertex count granted in Black box 1's proof.
3. **The strictness is genuinely load-bearing, and it is genuinely proved.** τ* ≤ 17n and r ≤ n + π(3n) ≤ 2n+1 give τ* + r ≤ 19n + 1. The *non-strict* lemma yields only G ≤ 19n+1; the sharpest non-strict repair available (#{y*=1} ≤ ⌊τ*⌋) still yields 19n+1. So 19n requires G < 19n+1, i.e. strictness. Since 17n + n + π(3n) is an integer and G is an integer, G < that integer gives G ≤ 18n + π(3n) − 1. Both the necessity and the proof are as the report says.
4. **Regime split is exact and exhaustive.** For k = 3 the Black box 3 hypothesis a_n^{k−1} ≥ (kn)^{k+1} reads m² ≥ (3n)⁴, which is *equivalent* to m ≥ 9n² (verified symbolically at the boundary for n ≤ 19). So the two branches m ≥ 9n² (⇒ G ≤ 3n ≤ 19n) and m < 9n² (⇒ √m < 3n) tile all instances. Correct.
5. **π(3n) ≤ n+1.** Exactly n integers of [1,3n] are coprime to 6 (n = 2h: h full blocks × 2; n = 2h+1: the extra {6h+1,6h+2,6h+3} contributes exactly 6h+1). All primes > 3 in [1,3n] lie in that set, 1 lies in it and is not prime, and 2, 3 ≤ 3n for n ≥ 1. Hence π(3n) ≤ (n−1)+2 = n+1. Verified for all n < 60000 by sieve; no violations. Endpoint n = 1: π(3) = 2 = n+1, tight.
6. **n = 1, 2, 3.** 17n + n + π(3n) − 1 = 19, 38, 57 = 19n exactly. Verified numerically for n ≤ 11; and the report's separate remark that 25 gives π(3n) ≤ n for n ≥ 9 (hence g(n) ≤ 19n−1) is also correct and numerically clean.

Note that 19n is not in `papers/erdos708/main.tex` (the string "19n" does not occur); the published constant there is 33n (Theorem thm:h17). So the improvement is real. It is, however, a two-line combination of two theorems that already sit in the same paper — see "Hostile reader" below.

## C2. g(n) ≤ 18n + π((18n)^{19/34}) − 1 = 18n + o(n) — **CONFIRMED**

- Exponent arithmetic. Black box 3 with k = 18 reads m^17 ≥ (18n)^19. Its negation gives m < (18n)^{19/17}, hence √m < (18n)^{19/34}. (19/17)/2 = 19/34. Verified numerically at the integer boundary for n ≤ 9: `m^17 ≥ (18n)^19 ⟺ m ≥ (18n)^{19/17}` with no off-by-one.
- Inner regime: r ≤ n + π(T), T = (18n)^{19/34}; τ* ≤ 17n; strict rounding and integrality of G and of 18n + π(T) give G ≤ 18n + π(T) − 1.
- **Domination of the outer regime.** T ≥ 18^{19/34} ≈ 5.029 > 2 for every n ≥ 1, so π(T) ≥ 1 and 18n + π(T) − 1 ≥ 18n ≥ the outer ksplit bound. Verified for every k in 2..18 at n = 1 (Y_k(1) ranges 2.83…5.03, all > 2). The claim that both regimes are covered by the single expression is therefore correct, including the endpoint.
- o(n): π(T) − 1 ≤ T − 1 = (18n)^{19/34} − 1 and 19/34 < 1. The explicit error claim in the ledger is exactly this and is correct. The sharper O(n^{19/34}/log n) uses the report's own elementary Chebyshev-type estimate π(t) ≤ √t + 8(ln2)t/ln t, whose proof I checked (Erdős's binomial argument, θ(t) < 4t ln 2, primes in (√t, t] each contribute > (ln t)/2) and which I verified numerically for all t ≤ 200000 with zero violations.
- Sanity check on the constant: this unconditional 18n + o(n) matches the *conditional* g(n) ≤ 18n of the paper's Theorem thm:cond (which assumes Conjecture conj:TH). That coincidence is not an error — thm:cond spends 2n + 16n, the new route spends 17n + n — but it is the strongest single statement in the report and deserves the closest scrutiny before publication. I re-derived it three times and found no gap.

## C3. Exact CRT family with G = n, τ* = n/K for all n ≥ 1, K ≥ 2 — **CONFIRMED** (one presentational defect)

- **Positions lie in the window.** t_i = ⌊m/2⌋ + i ∈ [1,m] since n ≤ ⌈m/2⌉ (m = p_n ≥ Q ≥ 6n).
- **Exact valuation.** x + t_i ≡ p_i^K (mod p_i^{K+1}) and x + t_i > 0, so v_{p_i}(x+t_i) = K exactly. CRT is solvable (p_i^{K+1} pairwise coprime) and the explicit formula given is the standard one.
- **Uniqueness of the multiple of p_i in I.** Offsets divisible by p_i are t_i + jp_i ∩ [1,m]. The band gives p_1 ≥ Q > (3/4)m, hence t_i ≤ m/2 + n < 2Q/3 + Q/6 = 5Q/6 < Q ≤ p_1 (so j = −1 falls below 1) and t_i + p_1 > m/2 + 3m/4 > m (so j = +1 falls above m). Both inequalities in the report ("m − p_1 < t_i ≤ p_1") are correct as derived.
- **No cross-contamination.** Since x + t_{i'} is the unique multiple of p_{i'}, no designated position carries two nonzero rows; the constraint matrix is K times a permutation of unit columns.
- **G = n.** R_{p_i} = 1 and only x+t_i has v_{p_i} > 0, so every cover contains all n positions; those n suffice (K ≥ 1). Both bounds exact.
- **τ* = n/K.** Primal y = 1/K on the n positions is feasible (K y = 1 ≥ 1, and 1/K ≤ 1), cost n/K. Dual z_{p_i} = 1/K has w_z ≤ 1 everywhere (w_z = 1 at the designated positions, 0 elsewhere), so all box penalties vanish and its value is Σ R_p z_p = n/K. Matching primal/dual ⇒ τ* = n/K. Correct; this is a complete certificate, not a solver output.
- **Prime-band existence.** Σ 1/p diverges (the report's Euler-product proof is correct: −log(1−1/p) ≤ 2/p for p ≥ 2, and ∏_{p≤N}(1−1/p)^{-1} ≥ Σ_{k≤N} 1/k). If all late bands [(4/3)^j, (4/3)^{j+1}) held ≤ n−1 primes their reciprocal mass would be ≤ (n−1)(3/4)^j, summable — contradiction. With Q = ⌈(4/3)^j⌉, every prime of that band lies in [Q, 4Q/3). Bands can be taken arbitrarily late, so Q ≥ 6n is available. Termination proof is correct and elementary.
- **Verified numerically.** For the report's headline witness (n = 12, K = 100), I recomputed: each of the 12 input primes has exactly one multiple in I, at offsets 78…89, each of valuation exactly 100; τ = 3/25 = n/K; G = 12; (G−τ)/n = 99/100. All twelve K = 100 spike jobs give 99/100 and all twelve K = 10 jobs give 9/10.

**Defect (presentational, not mathematical):** the exhibited witness A = [101,…,157] does **not** satisfy the stated band hypothesis — 157 > 4·101/3 = 134.67, so the primes are not inside any [Q, 4Q/3). It happens to satisfy the weaker conditions the proof actually uses (t_max = 89 ≤ p_1 = 101 and t_min + p_1 = 179 > m = 157), which I verified directly, so the instance is genuine. But as printed, the report's "largest-n maximizing witness" is not an instance of the construction rule it is presented under. Repair: either state P1's hypothesis as the weaker `⌊m/2⌋ + n ≤ p_1` (which is all the proof needs, and is what the witness satisfies), or replace the witness with a banded one.

## C4. The three refutations follow from C3 with K = n — **CONFIRMED**

Taking K = n (legal for n ≥ 2) gives τ* = 1, G = n, loss n − 1 on an explicit instance for every n.
- No uniform h(n) = o(n) with G ≤ τ* + h(n): would force h(n) ≥ n − 1.
- No fixed α, C with G ≤ ατ* + C: would force n ≤ α + C for all n.
- No fixed c < 1, C with G ≤ τ* + cn + C: would force (1−c)n ≤ 1 + C for all n.
All three are correct, and the quantifiers ("uniform in the instance, h a function of n alone"; "α, C absolute") are stated precisely enough that the refutations bite. The report is also correct and commendably careful that this does **not** refute G ≤ τ* + n (the family has G − τ* = n − n/K < n strictly) and does not establish superlinear loss; "≫n" is explicitly declared to mean Ω(n).

## C5. F1/F2 and the R3 claims — **split verdict**

### F1 (laminar / automatic TU) — **CONFIRMED**
{2,4,6} and {3,6} in [1,6] are crossing, not nested, so not laminar. Columns 6, 10, 15 against rows 2, 3, 5 give exactly [[1,1,0],[1,0,1],[0,1,1]] with determinant −2, a genuine submatrix of the prime-incidence matrix. The report's own hedge ("a matrix obstruction, not a claim that a particular Erdős instance has the generic triangle gap") is the right hedge and should be kept.

### F2 (β_H ≤ G − τ) — **CONFIRMED**, recomputed independently
A = {30,42,70,105}, u = 210^10, x = u−1. I recomputed: R_p = 3 for p ∈ {2,3,5,7}; v_p(u) = 10 for all four; max_{b∈I, b≠u} v_2(b) = 6; primal y_u = 3/10 feasible with cost 3/10; dual z_2 = 1/10 with **zero** box penalties over the whole window and value 3/10. Matching ⇒ τ = 3/10 exactly, G = 1, G − τ = 7/10. Bipartite incidence: 8 vertices, 12 edges (I recounted the 12 edges), connected ⇒ β_H = 5 > 7/10. Refutation valid. The scope hedge ("refutes that proposed R5 comparison only; does not refute G ≤ 2n + 2β_H") is correct and necessary.

### R3 §1 generalized monotone-valuation hinge — **proof CORRECT, but UNPROVED from the black boxes as listed**

The offending step, named as requested:

> "Thus S, on all relevant integers, is exactly an atom system covered by **Theorem threshold 17** in `papers/erdos708/sec_h17.tex`."

Black box 2 as handed to me is the *consequence* "τ* ≤ 17n for every instance". R3 invokes the *hinge inequality itself*,
Σ_{k≤m}(S(k)−17)^+ ≤ Σ_{b∈I}(S(b)−1)^+ for every atom system,
which is strictly stronger and is not recoverable from τ* ≤ 17n. Nor is the conclusion recoverable by another route: from the black boxes alone one gets only τ_cap ≤ G ≤ 19n (using C1), not τ_cap ≤ 17n. So **relative to the brief's list, τ_cap ≤ 17n and τ_level ≤ 17n are UNPROVED.**

Relative to the actual repository this is a non-issue: `papers/erdos708/sec_h17.tex` Theorem thm:h17 states exactly the atom-system hinge inequality, and its formalisation note says `Erdos708H17.g_le_33n` is Lean-checked. The report is *explicit* that it uses "the supplied atom-system hinge17", so it is not smuggling anything. The mismatch is between the brief's black-box list and the report's actual input, and it should be recorded as such rather than as "no unproved items".

Given thm:h17, I checked the derivation line by line and it is **correct**:
- s_p = min(f_p,1), e_p = (f_p−1)^+ are nondecreasing, vanish at 0, and f_p = s_p + e_p. ✓
- Increments α_{p,j} = s_p(j) − s_p(j−1) ≥ 0 with Σ_j α_{p,j} = s_p(J_p) ≤ 1, and s_p(v_p(k)) = Σ_j α_{p,j}[p^j | k]: this is verbatim the paper's definition of an atom system. Truncation at J_p (largest valuation among the finitely many relevant integers) is legitimate — it changes S on no relevant integer and makes the system finitely supported, which thm:h17 requires. ✓
- Σ_{k≤m} E(k) ≤ Σ_{b∈I} E(b) by expanding into β_{p,j} ≥ 0 and using #{b ∈ I : p^j | b} ≥ ⌊m/p^j⌋. ✓
- Pointwise (W−17)^+ ≤ E + (S−17)^+ (case split on S+E ≤ 17) and (W−1)^+ = E + (S−1)^+ (if E > 0 some f_p > 1 so s_p = 1 so S ≥ 1). Both identities are exact. ✓

### R3 §2 corollary (value ≤ 17n for any monotone-profile cover LP) — **CORRECT given thm:h17**
The dual after eliminating box multipliers is Σ z_{p,t} d_{p,t} − Σ_{b∈I}(W(b)−1)^+; the demand hypothesis d ≤ Σ_a h(v_p(a)) with z ≥ 0 gives Σ z d ≤ Σ_{a∈A} W(a); then W(a) ≤ 17 + (W(a)−17)^+, A ⊆ [1,m] distinct, and the generalized hinge give ≤ 17n. Feasibility of y ≡ 1 follows from the same increment/multiple count. Strong duality applies (feasible + bounded). No error.

### R3 §3 demand-capped LP — **CORRECT**
Integral equivalence: both directions checked (the converse case-splits on whether some selected b has v_p(b) ≥ R_p). h_p(v) = min(v,R_p) satisfies h_p(v_p(a)) = v_p(a) so the demand hypothesis holds with equality; τ_cap ≤ 17n follows from §2. τ_raw ≤ τ_cap ≤ G is correct. The observation that τ_cap = G = n while τ_raw = n/K → 0 on the CRT family (so τ_cap ≰ ατ_raw + C) is correct. The "adding rows min(v,q), q ≤ R_p, adds nothing" claim is correct: min(v,q)/q ≥ min(v,R_p)/R_p pointwise (three cases), so the R_p row implies each of them fractionally.

### R3 §4 level LP — **CORRECT**
Feasibility (N_{p,j} ≤ ⌊m/p^j⌋), the summed-coefficient identity Σ_{j≤L_p}[p^j|b] = min(v_p(b),L_p) with Σ_j N_{p,j} = R_p (so level-feasible ⇒ original-feasible, fractionally as well as integrally), and τ_level ≤ 17n via h_{p,j}(v) = [v ≥ j] are all correct. I recomputed both counterexamples:
- A = {2,4}, x = 4, I = {5,6,7,8}: R_2 = 3, τ_raw = τ_cap = G = 1 (I solved the one-row LP by exhaustive rational search), level row j=1 forces y_6 = y_8 = 1 so τ_level = 2 with integral witness {6,8}. ✓
- Amplification A = {2,…,2^n}, x = 2^K − 2^n, K ≥ max(R,n): I recomputed n = 4 (K = 10): max valuation in I is K at the endpoint, τ_raw = R/K, τ_cap = 1, G = 1, and the level witness {2^K} ∪ {2^K − 2^j : 1 ≤ j ≤ n−1} lies in I with valuations K,1,…,n−1 and satisfies every level row with equality. Row j = 1 forces τ_level ≥ n. So τ_level = g_level = n while G = 1. ✓
The ledger's "PROVED / REFUTED equivalence" wording for this row is accurate.

### R3 §5–§6 audits — **CORRECT**
r ≤ 2n + π(2n) for m < 8n³ (three primes > 2n would exceed (2n)³); r ≤ 3n−1 (p_i ≥ 2i−1; log concavity midpoint bound log(2i−1) ≥ ∫_{i−1}^i log 2t dt; Σ ≥ 3n log(6n/e) > 3n log 2n by e < 3; contradiction with ∏_{p|∏A} p ≤ m^n < (8n³)^n); hence G ≤ 20n−1 non-strictly and 20n−2 strictly. The complementary branch m ≥ 8n³ is exactly Black box 3 with k = 2. All correct, including at n = 1 (m < 8 ⇒ r ≤ 2 ⇒ G ≤ 18).

---

## Overclaims in the ledger and the final dependency block

1. **"← no unproved items" for the modified-LP row.** The chain's root input is the atom-system hinge inequality (thm:h17), *not* Black box 2 as the brief states it. Relative to the brief's list this is an unproved item. Repair: change the leaf to "supplied atom-system hinge inequality thm:h17 (`sec_h17.tex`)" and note that the weaker "τ* ≤ 17n" formulation does not suffice. (The report's prose already says "derived from the supplied atom-system hinge17", so this is a one-line fix in the dependency block.)
2. **Missing attribution for the E+S splitting.** `papers/erdos708/main.tex`, Remark [fractional weights] (≈ line 848) already contains the identical argument for the linear profile: "Writing w_z = E + S with S(n)=Σ_p min(z_p v_p(n),1) and E=Σ_p(z_p v_p(n)−1)^+, one has (w_z−1)^+ = E + (S−1)^+ …, (w_z−c)^+ ≤ E + (S−c)^+, and Σ_I E ≥ Σ_K E because … nonnegative increments". R3 §1's "general monotone-valuation hinge theorem" is that remark with `z_p·v` replaced by an arbitrary nondecreasing f_p — a real but one-line generalization, and the remark's proof already never used linearity. Presenting it as a new theorem without citing the remark is a novelty overclaim. Repair: cite the remark and describe §1 as its generalization.
3. **"all optima settled exactly" — the claim is TRUE, but `final_verify.py` does not establish it.** The verifier re-proves optimality only for the 24 unique-spike jobs (structurally: each prime has a unique multiple in I) and the 5 `repair_` jobs (G ≥ ⌈τ*⌉ from the exact dual, matched by a verified cover). For the other 44 distinct records it checks only the *cover* (an upper bound) and inherits the lower bound from a search-time DP it does not repeat, which the report discloses in prose while the ledger row still says **PROVED** and the dependency block says "no unproved items about these finite instances".
   *I closed this gap myself, and it closes completely:* of the 44 non-structural distinct instances, **36 satisfy G = ⌈τ*⌉** — so the exact rational dual already in the ledger proves optimality, and the verifier simply never applies that test outside the `repair_` family. For the remaining **8** I re-proved optimality independently: 7 by exhaustive enumeration of every subset of G−1 interval positions (no dedup, up to C(14669,2) = 1.08·10⁸ subsets), and the last one (A = [10403,…,12317], n = 10, G = 12, τ* = 11, P = {101,…,113}, all demands 4) by my own capped-state DP over the 10 distinct columns, which returns 12. **Zero mismatches.** All 85 distinct instances are therefore genuinely settled, including the R3 twelve (G = 1 is trivially optimal there).
   Repair is one line of code, not a retraction: add the `g == ceil(tau)` certification to every record, not just `repair_`, and the shipped verifier will cover 41 of the 44 by itself.
4. **τ_cap and τ_level are hard-coded, not certified.** In `r3_verify.py` the fields `tau_cap="1"` and `tau_level=str(n)` are written as constants, and `final_verify.py`'s `assert Q(r['tau_cap'])==1` merely re-reads them. Their values are correct (I re-derived both: τ_cap ≥ 1 since c_{p,b} ≤ R_p; τ_level ≥ n from the 0/1 level-1 row), but the *verifier* certifies neither. Repair: say so, or add the two one-line LP certificates.
5. Minor: "= 18n+o(n)" written as an equality between a concrete expression and an asymptotic class; and the ledger's `min{19n, 20n−2, …}` is correct but the 20n−2 term only bites at n = 1 (where it gives 18). Neither is an error.

## Global vs instancewise: **handled correctly**

This is the place where a report like this usually breaks, and this one does not. Line 24, R2's "Status distinction" paragraph, and R3 §6's closing paragraph all say the same correct thing: the global bounds are *cover* bounds, the large-m branch invokes ksplit instead of comparing to τ*, and τ* can be arbitrarily small there, so **no** universal instancewise G ≤ τ* + n + o(n) is proved. The instancewise statement that *is* proved is confined to its regime ("G < τ* + n + π(T_n) for m < T_18(n)"). G ≤ τ* + n is left OPEN, correctly, and the CRT family is explicitly said not to refute it. The uncapped/capped distinction (τ_raw vs τ_cap vs τ_level) is maintained throughout, including the warning that τ_cap ≰ ατ_raw + C.

## What a hostile reader at erdosproblems.com would object to

- **"This is a corollary, not a theorem."** g(n) ≤ 19n is Theorem ksplit (k = 3) + Theorem h17 + Lemma round + a two-line prime count, all four already in the same paper. The reader's objection will be that the paper's own authors could have written this line, not that it is wrong. The honest framing is "the published 33n improves to 19n by taking k = 3 in the k-split rather than k = 2, which shrinks the residual regime from m < 8n³ to m < 9n² and collapses Lemma fewprimes' 16n to n + π(3n) ≤ 2n+1" — i.e. state the *mechanism*, since the mechanism is the whole content.
- **"18n + o(n) unconditionally is suspiciously equal to your conditional 18n."** Expect this to draw the most fire. It is correct (17n + n vs 2n + 16n), but the report should preempt the question explicitly.
- **The witness that does not satisfy its own hypothesis** (C3 above). A referee who spot-checks one thing will spot-check the printed witness.
- **"PROVED" on a finite-search row** whose lower bounds the shipped verifier leaves to an unrepeated DP for 44 of 85 instances. (The row is true — I certified all 85 — but a reader who runs only `final_verify.py` cannot see that.)
- **No Lean.** The report says clearly that nothing here is newly kernel-checked, which is the right disclosure; but the surrounding project's own standard is Lean-verified claims, and 19n/18n+o(n) are short enough to formalize on top of the existing `Erdos708H17` and ksplit developments. Publishing the constants before formalizing them will be read as a step down from the paper's standard.
- **Novelty of the CRT counterexample.** It refutes only comparisons nobody proved; the paper contains no claim of an o(n) integrality gap for eq:LP. Presenting "REFUTED" rows with the same visual weight as the new upper bounds overstates their significance. They are useful *negative* guidance (they show why the rounding term cannot be beaten by any LP-comparison argument on the raw LP), and should be framed that way.
- **Submission hygiene.** Under the site's one-proof-claim-per-problem convention, a 33n → 19n improvement is a revision of the existing claim, not a new one.

## Bottom line

- C1 **CONFIRMED**. C2 **CONFIRMED**. C3 **CONFIRMED** (fix the witness/hypothesis mismatch). C4 **CONFIRMED**.
- C5: F1 **CONFIRMED**, F2 **CONFIRMED**; R3's hinge/corollary/cap-equivalence/level results are **mathematically correct** but **UNPROVED from the black-box list as given** — the named step is R3 §1's appeal to the atom-system Theorem threshold 17, which is the hinge *inequality* and not the stated Black box 2 (τ* ≤ 17n). With `sec_h17.tex` Theorem thm:h17 admitted as an input, they are CONFIRMED.
- The finite ledger (93 jobs, 85 distinct instances, all optima exact, max (G−τ)/n = 99/100) is **true and now fully independently certified**, though the shipped verifier alone does not establish it for 44 of the 85.
- **No mathematical error was found anywhere in the report.** The defects are one presentational mismatch (the witness that violates its own hypothesis), one missing attribution (the E+S splitting is already the paper's own remark), one under-powered verifier, and one black-box bookkeeping error (the R3 chain's real input is thm:h17, not "τ* ≤ 17n"). None of them touches the correctness of C1–C4. Hence PASS-WITH-REPAIRS rather than PASS; none of the repairs requires re-proving anything.
