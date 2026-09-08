PASS-WITH-REPAIRS
PASS

# Adversarial referee report — `pro_708_r19/proof.md`

**Referee:** Claude Opus 5, blind/hostile mode. Every numerical constant below was
recomputed **from the manuscript's definitions** by a script I wrote myself
(`referee_checks.py`, this directory), in `fractions.Fraction` / big-integer
arithmetic only. No floating point enters any decision. I wrote and ran all of my
own numbers before reading `exact_verifier.py`; the comparison is in §7.
66 named checks, all passing; runtime ≈ 4 min.

**Claims refereed.**
(A) For every finite atom system (α_{p,j} ≥ 0, Σ_j α_{p,j} ≤ 1 per prime,
S(n) = Σ α_{p,j}[p^j | n]), every m ≥ 1 and every window I = {x+1,…,x+m},
Σ_{k≤m}(S(k) − 56501/6400)^+ ≤ Σ_{b∈I}(S(b) − 1)^+.
(B) H_{19/10} is false (explicit 21-prime instance), and every absolute c < 2 fails.

**Verdicts.**

* **(A) PASS-WITH-REPAIRS.** I found **no mathematical error and no numerical
  error**. All 57 finite scales, the tail, and every displayed constant reproduce
  under independent exact recomputation, each strictly inside its claimed bound.
  But **Lemma 6's derivation of (30)–(31) is not valid as written** (R1 below):
  the sentence "Because T > 41/8, this forces at least four/five/six outside
  primes" does not follow from the displayed hypothesis; it needs two further
  facts, both true and both available elsewhere in the manuscript but neither
  invoked. This is not cosmetic — I verified that the naive reading collapses the
  proof (§4). A second derivation, the tail's (52), omits the summation range that
  produces the exponents in (49) (R2). Both repairs are two sentences each. With
  them inserted, (A) is a complete and correct proof.
* **(B) PASS.** The 21-prime instance is exactly right — I recomputed **both**
  sides of (55) by direct enumeration (404 471 integers and 404 471 window
  offsets), getting 21 and 20. The generalisation is correct: all three geometric
  conditions do follow from "r primes in [M, √2 M)" with M > 2, and the
  cluster-existence argument via divergence of Σ1/p is valid. Three provisos are
  tacit but harmless (§6).

---

## 1. Lemma-by-lemma verdicts

| Lemma | Verdict | Note |
|---|---|---|
| 1 — moments, hinge majorant, exponential moment | **correct** | vertex bound re-derived + spot-checked; concavity/vertex principle and the *h < r* case still asserted (G6) |
| 2 — large-atom truncation, dense branch | **correct** | exact excess 9127710437643246821282611/9748777809372369664830603264 ≈ 9.3629·10⁻⁴ > 0 |
| 3 — repaired eight-mantissa retention | **correct** | max adjacent D-ratio **exactly 9/8**; η ≤ 1/3 and η ≤ 16t/27 at every level; knapsack (16) = **480** for all 24 v; independently reproduced by exhaustive multiset enumeration |
| 4 — rounding loss 3601/1280 | **correct** | (23) max = **259272 at w = 696, R = 176**, exactly as claimed; 259272/92160 = 3601/1280 |
| 5 — finite carrier family, ε_{θ,s} | **correct** | no Γ loss; range 2 ≤ r ≤ ⌊a⌋+1 always non-empty (a ≥ T−2 = 251/75) and v_r > a in all 141 130 (r,v) pairs |
| 6 — prime densities, certificate value | **correct conclusion, invalid derivation of (30)–(31)** | see R1 |
| 7 — pointwise feasibility, (40)/(42) | **correct** | E_{k,d} matches brute force on 259 coefficients; N-range (41) verified to truncate (all terms 0 beyond it, checked at every scale) |
| 8 — 57 finite scales + tail | **correct**, recomputed exactly | every per-L entry a valid strict upper bound; tail derivation under-specified (R2) |
| 9 — closing chain | **correct** | 198283/200000 < 1; m = 1 and dense branch covered |
| 10 — refutation of H_{19/10}, barrier c ≥ 2 | **correct** | both sides recomputed by direct enumeration |

---

## 2. Lemma 3 — the repaired retention rule (task item (i))

**The table is complete and consistent.** The D-levels strictly above 1/8 are
exactly the 24 values v/64 with
v ∈ {9,…,15} ∪ {16,18,…,30} ∪ {32,36,…,60} ∪ {64}, and the table lists exactly
those 24. Level 1/8 = 8/64 is *not* in the table and correctly falls in the
η(t) = 16t/27 branch. Verified: **η(t) ≤ 1/3** at every level (max = 240/720 = 1/3,
attained at v ∈ {36,…,64}) and **η(t) ≤ 16t/27** at every level (equality at
v = 9, 18, 36 — the table is tight in three places).

**Does the knapsack really cover every shortest prefix?** Yes, and both branches
are sound.

* θ ≤ 1/8: the bound Σ_{p∈C} η(t_p) ≤ (16/27)s uses (12) **at every level of the
  carrier, not only the low ones** — so prefixes mixing levels above and below 1/8
  (including level 1 = 64/64) are covered. s ≤ 1 + θ ≤ 9/8 gives (16/27)(9/8) = 2/3
  exactly.
* θ > 1/8: every level of C is then ≥ θ > 1/8, hence in the 24-element table,
  hence an integer multiple of 1/64. The prefix condition is exactly
  65 − v ≤ w ≤ 64 for the mass w of C minus its last (= minimum) element.

**My exact recomputation of (16):** for **every one of the 24 v**, the maximum is
**480**, i.e. Σ η ≤ 480/720 = 2/3. I also re-derived this by a *different*
formulation — exhaustive DFS over all admissible nonincreasing level multisets —
and got the same 2/3, attained e.g. by eight primes at level 9/64 (mass 72/64,
Σ η = 8·60/720 = 2/3) and by the two-prime level-1 carrier. **(11) holds.**

**Moduli.** η ≤ 1/3 everywhere ⇒ every retained modulus q_p(t) ≤ m^{1/3}. The
atoms of b_p sit at the retained q_p(t), and capping (min(b_p,θ)) only removes
increments, never adds moduli — so every atom of B and of every capped outside
function has modulus ≤ m^{1/3}, and **P_C q ≤ m^{2/3}·m^{1/3} = m** (17). Task
item (i) confirmed on both counts. I additionally confirmed this on 24 000
synthetic points across six values of m up to 10³⁰ (§5, E3): zero violations.

*Small gap (G-a):* Lemma 3 uses q_p(t_p) ≤ p^{v_p(k)} (minimality of q_p) without
saying so; this is what converts non-retention into a_p > η(t_p). Same as r18's G2.

---

## 3. Lemma 4 — the rounding knapsack (task item (ii))

**Is the reward r_v the correct error bound?** Yes. If t_p is the largest D-level
≤ f_p = S_{0,p}(k), then f_p < successor(t_p), so the error f_p − ρ b_p(k) ≤ f_p is
strictly below the successor level. I checked that "the next v in the table"
coincides with the successor *in D* at all 24 levels, and that the top level v = 64
correctly gets reward 64 (error ≤ f_p ≤ 1). ✔

**Levels t_p ≤ 1/8 (21).** ρ t_p = (243/128) η(t_p) is an *identity* there, because
η(t) = 16t/27 exactly on that branch: (9/8)·(27/16) = 243/128. I verified
ρt = (243/128)η(t) at every D-level ≤ 1/8. ✔

**"Total large-level cost ≤ 719".** Justified: a_p > η(t_p) = E_v/720 for each
unretained large level, so Σ_large a_p > w/720; with Σ_p a_p ≤ 1 this forces
w/720 < 1, i.e. w ≤ 719 as w is an integer. The strictness in (20) is genuinely
load-bearing (w = 720 would give 1440·R(720)+0, and R(720) = 180 giving 259200 —
still below 259272, so in fact nothing breaks, but the argument as given is the
right one). ✔ (Requires m ≥ 2 so that log m > 0; the manuscript disposes of m = 1
in the first line of the proof. ✔)

**My exact recomputation of (23).** Over all attainable w ≤ 719,
max{1440 R(w) + 243(720−w)} = **259272**, attained at **w = 696 with R(696) = 176** —
the manuscript's values to the digit. The stated maximiser 1, 1, 7/16, 1/4 does have
cost 240+240+120+96 = 696 and reward 64+64+30+18 = 176. ✔
259272/92160 = **3601/1280** = D₀, and D₀ + ρT = 3601/1280 + 1203/200 = **56501/6400**. ✔

---

## 4. Lemma 6 — R1, the one derivation that is invalid as written

### 4.1 The prime-density bounds (29) — correct

I sieved to 2²¹ and checked **every integer** (not only the primes, which is all
the manuscript and the author's verifier check):
π(ν)/ν ≤ 9/40 on [210, 2¹⁵]; ≤ 3/20 on [2310, 2¹⁷]; ≤ 1/8 on [30030, 2²¹]. All hold.
Worst values: π(210)/210 = 23/105 = 0.2190 (vs 0.225); max on [2310,2¹⁷] = 0.14885
(vs 0.15); max on [30030,2²¹] = 0.10820 (vs 0.125).

The analytic continuation (35) is correct:
189/32768 + 7/5 + 14/50 = 1380981/819200 = 1.685768 < 17/10. The three
consequences also hold — but see the knife-edge K2 below.

*Gaps (G-b, editorial):* ϑ(x) ≤ x log 4 is sketched (the induction step only);
∫₆₄^x dt/log²t ≤ 2x/log²x is asserted with the hint "log 64 > 4" (it is true: the
derivative of 2x/log²x − ∫ is (1/log²x)(1 − 4/log x) > 0 for x > e⁴); and the
monotonicity of 18 log x / x is implicit.

### 4.2 R1 — "T > 41/8 forces ≥ 4/5/6 outside primes" does not follow as written

At a hot source, Σ_{p∉C} b_p(k) > T − 1 − θ_C. **With only b_p ≤ 1** (the natural
reading, and the one the referral proposes), this bounds the number of outside
primes below by ⌊T−1−θ_C⌋+1, and I computed that this gives

| class | needed | what b_p ≤ 1 actually yields |
|---|---|---|
| θ ≥ 7/8 | 4 | **4** ✔ |
| 3/4 ≤ θ < 7/8 | 5 | **4** ✘ |
| θ < 3/4 | 6 | **4** ✘ |

so classes 2 and 3 fail. Two further facts are required, and both are true:

1. **b_p(k) ≤ θ_C for every outside prime** at an assigned source (the carrier is
   the shortest prefix of a *nonincreasing* ordering). The manuscript states this
   in the proof of Lemma 5 — but Lemma 6 never refers back to it. With it, the
   count is > (T−1)/θ_C − 1.
2. **The discreteness of D.** With (1) alone and only the stated inequality
   T > 41/8, class 2 still gives only 4 as θ ↑ 7/8, and class 3 only 5 as θ ↑ 3/4.
   One must observe that the D-levels in [3/4, 7/8) are just {3/4, 13/16} and the
   largest D-level below 3/4 is 11/16. Then (41/8 − 1 − θ)/θ equals 66/13 − 1 =
   4.077 → ≥ 5 at θ = 13/16, and **exactly 5** at θ = 11/16 → ≥ 6 by strictness.

With both facts and the true T = 401/75 the margins are comfortable (my exact
values for (T−1)/θ − 1 at the binding levels: 251/75 = 3.347 → ≥4; 4241/975 = 4.350
→ ≥5; 4391/825 = 5.322 → ≥6), and (31) holds. **I verified the corrected count at
every D-level: class 1 min 4, class 2 min 5, class 3 min 6.** ✔

**This is load-bearing, not decorative.** I re-ran the entire 57-scale computation
with δ ≡ 9/40 (what ν_C ≥ 210 alone would license):

| δ | finite total | tail λ_θ |
|---|---|---|
| as written (9/40, 3/20, 1/8) | **990409.86·10⁻⁶** | 49.902 < 50 ✔ |
| δ ≡ 9/40 everywhere | **1015628.29·10⁻⁶ > 1** ✘ | 51.535 > 50 ✘ |

So the proof does not close without the sharper δ. **Repair required:** insert
facts (1) and (2) at the point of use in Lemma 6.

### 4.3 The certificate value (34), (36)–(37) — correct

* (36) is right: #{b ∈ I : P_C q | b} ≤ ⌊m/(P_C q)⌋ + 1 = ⌊ν/q⌋ + 1, using the
  nested-floor identity ⌊m/(P_C q)⌋ = ⌊⌊m/P_C⌋/q⌋.
* **"All these primes are at most ν"** is correct and I confirm the reason the
  manuscript does not give (G-c): an atom q = p^i of U_C has q ≤ m^{1/3} and
  P_C q ≤ m, so p ≤ p^i ≤ m/P_C, and being an integer, p^i ≤ ⌊m/P_C⌋ = ν.
* **"each prime's cap is θ_C"** is correct: min(b_p(·), θ_C) is a nondecreasing
  step function of v_p with total increment ≤ θ_C, so Σ_i β_{p,i} ≤ θ_C and the
  "+1" floor errors total at most θ_C·#{primes with atoms} ≤ θ_C π(ν). ✔
* Hence (37), and with Σ_I [P_C|b] ≥ ν and (31)–(32),
  Σ_I λ_θ c_C[P_C|b](1 − U_C/K_θ) ≥ λ_θ c_C ν (K−H_*−δθ)/K = ρ c_C ν = ρ M_C,
  giving (34). The r18 Γ-loss is genuinely gone; this is the substantive
  improvement of r19 over r18. ✔
* K_θ > H_* + δ(θ)θ holds at **all 57 finite scales and on the tail** (checked).

---

## 5. Lemma 7 — the counting (task item (iv))

**Is E_{k,d} an upper bound for the carriers of cardinality k, mass 1+d/L, minimum
θ dividing n?** Yes. Every p ∈ C has q_p(t_p) | P_C | n and t_p ≥ θ, so C sits
inside the N primes with b_p(n) ≥ θ; C(N,k) chooses them, and
[X^{L+d}](P^k − (P−X^j)^k) counts the level assignments of total mass 1+d/L using
the level θ at least once. Ignoring the cap t_p ≤ b_p(n) and modulus availability
only inflates the count. **Brute-force check:** I enumerated all level assignments
directly and compared against the polynomial coefficients for
(j,L) ∈ {(8,8),(8,16),(11,16),(15,16),(8,32),(13,32),(9,64),(15,64)}, k ≤ 4, all d —
**259 coefficients, zero mismatches.**

*(G-d, r18's G3 and G5 unrepaired.)* "Every carrier level ≥ θ is an integer
multiple of 1/L" is used to write s = 1 + d/L and is never proved (one line: a
level j′/2^{h′} with 2^{h′} > L is ≤ 15/2^{h+1} < 8/2^h ≤ θ). And the injectivity
of C ↦ level assignment needs the remark that q_p(t) depends only on (p,t).

**(38)** is right: U_C(n) ≥ (N−k)θ and B(n) − 1 ≥ d/L + (N−k)θ. **(41)** is right
and conservative: positive terms need N−k < K/θ and k ≤ ⌊1/θ⌋+1, so
N ≤ ⌊K/θ⌋+⌊1/θ⌋+1, one less than the stated bound. I verified **numerically at
every one of the 57 scales** that all terms vanish for six values of N beyond the
stated range (the author's verifier does not check this; I do).

**(42) for θ ≥ 1/2 is valid.** θ > 1/2 ⇒ k ≤ 1/θ+1 < 3 and k ≥ 2, so exactly two
primes; the pair count splits into "both at θ" (C(N,2)·e_θ) and "one at θ, one at
t ∈ (θ, v_i]" ((N−1)Σ_i E_θ(v_i)), which is exactly the displayed numerator. At
θ = 1/2 the "both at θ" pairs have mass exactly 1, not > 1, so **e_{1/2} = 0 is
correct**, and the only k = 3 carriers are the all-1/2 triples (any level > 1/2
would push the mass past 1+θ = 3/2), giving C(N,3)ε_{1/2,3/2} — correct. The
denominator Σ_i v_i − 1 ≤ B(n) − 1 is legitimate. The "all caps equal" reduction is
the mediant inequality Σn_i/Σd_i ≤ max_i n_i/d_i with d_i = v_i − 1/N ≥ 0 (needs
v_i ≥ θ ≥ 1/2 ≥ 1/N for N ≥ 2); the only zero denominator (N = 2, θ = v = 1/2) has
zero numerator, as the manuscript says and as my code asserts. ✔
I confirm A42 ≤ A40 at **every** θ ≥ 1/2 scale, so (42) really is the smaller bound.
**(42) is load-bearing:** with A40 alone the L = 16 row would be ≈ 0.80, not 0.5496.

---

## 6. Lemma 8 — my exact recomputation of all 57 scales, and the tail

### 6.1 The 57 finite scales (task item (v))

Recomputed from scratch: exponent sets from D, integer polynomial powers,
ε_{θ,s} by exact un-normalised integer comparison over 2 ≤ r ≤ ⌊a⌋+1, λ_θ from (32)
with the manuscript's K_θ table, and A_θ = (42) for θ ≥ 1/2, (40) otherwise.

| L | claimed bound (10⁻⁶) | **my exact value (10⁻⁶)** | OK |
|---:|---:|---:|:--:|
| 8 | 48879 | **48878.5585** | ✔ |
| 16 | 549612 | **549611.3594** | ✔ |
| 32 | 271163 | **271162.2971** | ✔ |
| 64 | 99084 | **99083.0052** | ✔ |
| 128 | 20073 | **20072.6904** | ✔ |
| 256 | 1577 | **1576.4180** | ✔ |
| 512 | 26 | **25.5148** | ✔ |
| 1024 | 1 | **0.0201** | ✔ (very loose, harmless) |
| **total** | **990415** | **990409.8636** | ✔ (slack 5.136·10⁻⁶) |

Every one of the eight table entries is a valid **strict** upper bound. My
per-scale value agrees with the author's declared per-scale bound in the sense of
lying strictly below it, at all eight scales.

### 6.2 The tail

All of (46)–(53) check out exactly:

| item | claim | **my exact check** |
|---|---|---|
| e < 87/32, e > 8/3, (87/32)³ < (9/2)² | — | ✔ ✔ 20.095917 < 20.25 ⇒ e·log(9/2) > 4 ⇒ z/(e log z) < 9/8 = ρ |
| exp((7/2)H_*) < 133/4 | — | **< 33.228833195** (rigorous Taylor + geometric remainder) ✔ |
| (47) (133/4)⁷⁵ < a₀⁷⁵(9/2)³²⁶ | — | ratio **0.999884258 < 1** ✔ — see knife-edge K1 |
| 0 < 𝒫_j(x_j) ≤ P̄_j < 1 | all j | ✔ (tightest j = 8: 0.421846017 ≤ 0.421847) |
| (49) (a₀x_j^{−j})⁴⁰ ≤ σ_j⁴⁰(1−P̄_j)⁴¹ | all j | ✔, slack ratios 0.961–0.989 |
| λ_θ < 50 for L ≥ 2048 | — | sup λ_θ = **31488/631 = 49.901743** ✔ |
| (53) tail < 1/1000 | — | **8.017031·10⁻⁴** = 0.8017/1000 ✔ |
| (44)+(53) = 198283/200000 < 1 | — | ✔ 0.991415 |

**I re-derived (52) independently** and it comes out exactly as printed —
contribution ≤ 50ρj·D_j/P̄_j · a₀^{L/j}x_j^{−L}(1−P̄_j)^{−M−1}, and the reduction to
σ_j^{L/j}/(1−P̄_j) is *precisely* condition (49) once M ≤ K/θ = (41/40)(L/j) — which
is where the exponents 40 and 41 in (49) come from. The geometric summation with
z_j = σ_j^{⌊2048/j⌋} and 2^h ≥ h+1 is right. **Direct verification:** at (L,j) =
(2048,15) and (2048,13) I evaluated the *exact* tail expression Σ_N Σ_{k,d} … with
the direct coefficient bound (46), the discarded penalty and denominator 1/L, and
compared with (52): 1.556·10⁻⁹ vs 1.911·10⁻⁶ and 4.803·10⁻⁷ vs 4.306·10⁻⁴ — (52)
dominates with three orders of magnitude to spare. ✔

**R2 (repair needed).** The text says "discard the penalty ... replace the maximum
over N by a sum", but *never states the summation range* M. Without the surviving
support restriction n = N−k < K_θ/θ the sum Σ_n(1−P̄)^{−n−1} diverges, and (49)'s
exponents 40/41 are unmotivated. One sentence fixes it: "*terms with N−k ≥ K_θ/θ
have zero penalty, so the sum may be truncated at M = ⌈K_θ/θ⌉−1 ≤ (41/40)(L/j),
which is what turns (51) into the exponent 41/40 in (49).*"

*(G-e, r18's G4 unrepaired.)* The domination 𝒫_j(x) ≥ P_{j,L}(x) — needed for
E_{k,d} ≤ x^{−(L+d)}P̄_j^k — is never asserted. It is true: the exponent
j′·2^{h₀−h′} of a level j′/2^{h′} ≥ j/L lands in the a·2^h band, and level 1
(exponent L = 2^{h₀}) is supplied by a = 8, h = h₀−3 ≥ 1; all exponents of 𝒫_j are
distinct so no cancellation.

---

## 7. Lemma 9, m = 1, and the dependency closure (task item (vi))

The closing chain is airtight:
Σ_{k≤m}(S−c)^+ =^{(5)} Σ(S₀−c)^+ ≤^{(19)} ρL_B ≤^{(34)} Σ_I F ≤^{(45)}
(198283/200000)Σ_I(B−1)^+ ≤ Σ_I(S−1)^+, the last step because B ≤ S₀ ≤ S globally
and 198283/200000 < 1. (5) needs c ≥ 7 and 56501/6400 = 8.828… ≥ 7 ✔.
m = 1 gives S(1) = 0 so the LHS is 0 ✔. The dense branch (H(S₀) ≥ H_*) is Lemma 2
and needs only c ≥ 7 ✔. The sparse branch with no hot points has L_B = 0 ✔.
Every branch is covered.

**Overclaim in the dependency closure.** "Unproved items used in these claims:
NONE" is not accurate. Used but not proved in full: Chebyshev's ϑ(x) ≤ x log 4
(sketched); the divergence of Σ_p 1/p (sketched, and only in Lemma 10);
∫₆₄^x dt/log²t ≤ 2x/log²x; the mean-monotonicity of H under pointwise domination
("averaging over a common period"); Lemma 1's coordinatewise-concavity/vertex
principle. All five are true and standard; the closure block should list them as
classical inputs rather than claim none exist.

The transfer arithmetic is fine: ⌈(56501/6400)n⌉ + 2n ≤ 11n for every n ≥ 1
(because 56501/6400 ≤ 9). ✔

---

## 8. Lemma 10 (task item (vii)) — claim (B)

### 8.1 The explicit instance — exactly right

Recomputed from scratch, nothing taken on trust:

* The 21 listed numbers are prime, distinct, and are **exactly** the primes in
  [503, 641]. ✔
* m = 631·641 = **404471**; the 210 pair products all lie in [256027, 404471], the
  largest being m itself. ✔
* 2·256027 = 512054 > 404471, so **each pair product has exactly one multiple in
  [1,m]**. ✔ Smallest triple 503·509·521 = **133390067 > m**, so no k ≤ m has three
  chosen prime factors. ✔
* **Direct enumeration over all k ≤ 404471:** exactly **210** integers have S(k) ≥ 2
  (all with S = 2), giving Σ(S(k)−19/10)^+ = 210·(1/10) = **21**. ✔
* Q_P − 202236 equals the 58-digit x in (54) **digit for digit**; I recomputed
  Q_P and subtracted. ✔ I = {Q_P−202235, …, Q_P+202235} has exactly m elements
  (2·202235+1 = 404471). ✔
* **Direct enumeration over all 404471 window offsets r:** since p | Q_P for every
  chosen p, p | Q_P+r ⟺ p | r; the maximum S at a non-centre point is **1**, so
  Σ_{b∈I}(S(b)−1)^+ = (21−1) = **20**. ✔ (The radius 202235 < 256027 = the smallest
  pair product is the reason.)

**21 > 20: H_{19/10} is refuted.** Consistent with the general threshold
2 − 2/21 = 40/21 = 1.90476 > 19/10.

### 8.2 The generalisation — correct

For r primes p₁<…<p_r in [M, √2 M) with m = p_{r−1}p_r and the window centred at
Q_P, all conditions hold:

* **pair products once:** 2p₁p₂ ≥ 2M² > p_{r−1}p_r = m ✔ (this is exactly what the
  ratio √2 buys).
* **no triples:** the smallest triple ≥ M³ > 2M² > m whenever M > 2 ✔.
* **window radius:** (m−1)/2 < m/2 < M² ≤ p₁p₂ = the smallest pair product, so
  pq | (b − Q_P) forces b = Q_P ✔.
* **counts:** L = C(r,2)(2−c), R = r−1, and C(r,2)(2−c) > r−1 ⟺ (r/2)(2−c) > 1 ⟺
  c < 2 − 2/r. I verified this equivalence symbolically over r = 2..59 and five c.
* **cluster existence:** if no [M,√2M) held r primes, then each
  [2^{j/2}, 2^{(j+1)/2}) — which *is* an interval of the required shape — would hold
  ≤ r−1 primes, whence Σ_p 1/p ≤ (r−1)Σ_j 2^{−j/2} < ∞, contradicting Euler. The
  cited Σ_{n≤y}1/n ≤ ∏_{p≤y}(1−1/p)^{−1} is the standard argument. ✔

**Three tacit provisos** (all harmless, none affecting the conclusion):

1. L = C(r,2)(2−c) tacitly assumes **c ≥ 1**; for c < 1 the single-prime multiples
   also contribute and L is strictly larger, so failure holds a fortiori.
2. The window is centred exactly, which needs **m odd** — true, since all p_i are
   odd once M > 2.
3. "sufficiently large" is doing the work of **M > 2** (for M³ > 2M²) and of the
   primes being odd; the manuscript should say which.

**Verdict (B): PASS.** No overclaim: the manuscript explicitly refrains from
claiming a counterexample to H₂ or H₃, and c < 2 strictly is all that is proved.

---

## 9. Independent end-to-end tests

1. **Counting polynomial vs brute force** — 259 coefficients across 8 scales,
   k ≤ 4, **zero mismatches**.
2. **Pointwise certificate stress test.** For explicit level profiles at a point n
   I enumerated **every** carrier that can divide n (subset + level assignment with
   t_p ≤ b_p(n), min = θ, mass > 1, mass − θ ≤ 1), gave each the largest
   coefficient the proof allows (c_C = ε_{θ,s}) and the manuscript's λ_θ, K_θ, and
   compared Σ_C λ_θ ε(1−U_C/K_θ)^+ with (198283/200000)(B(n)−1)^+.
   Over **6 081 profiles / 1 736 294 carriers** (levels ≥ 1/2 with N ≤ 6; mixed
   levels ≥ 1/4 with N ≤ 4; flat profiles with N ≤ 9): **no violation**, worst
   observed ratio **0.6034** against the proved 0.9914 — a factor 1.64 of headroom.
3. **Synthetic atom systems.** Genuine α_{p,j} on 35 primes, the true S₀ (atoms
   p^j ≤ m/Q), the true q_p(t), retention by exact integer comparison
   q^{den η} ≤ m^{num η}, the true b_p, B, and the true carriers, at
   m = 10¹⁸, 7·10¹⁸, 10²⁰, 2⁸⁰, 10²⁴, 10³⁰. Over **24 000 points, 4 775 hot points**:
   every one of S₀(k) ≤ ρB(k)+3601/1280, 1 < s_C ≤ 1+θ_C, P_C³ ≤ m², P_C | k,
   k/P_C ≥ 210/2310/30030 by class, ν_C ≥ the same, every retained modulus ≤ m^{1/3},
   and **every negative modulus P_C q ≤ m** held. **Zero violations.**
4. **The adversarial-audit fixture** (the *discarded* η(1/2) = 1/4 rule) is
   genuine: 2³³, 3²⁰, 5¹³ ≤ m^{1/4} and 7¹⁵ ≤ m^{1/3} with m = 2¹³², the source
   k ≤ m < Pq (Pq/m = 31.88), and B(k) = 11/2 > T. The manuscript is right that the
   final rule avoids the defect.

---

## 10. Cross-check against the author's verifier

Only after my own numbers were fixed did I read `exact_verifier.py`. Its
definitions match mine with no drift: `moment_envelopes` implements (28) with
a = (326L−75d)/(75j) and rounds ε **upward** (`ceildiv`, valid);
`coefficient_rows` produces the same exponent set as mine (its `8*z <= L` loop
admits z = L/8 only for a = 8, which is the level-1 exponent L, and nothing
spurious); `general_scale_bound` is (40) with N_max = ⌊K/θ⌋+⌊1/θ⌋+2 and every term
rounded up; `high_scale_bound` is (42) with the correct index arithmetic
(d = 2j−L for e₂, d = j for e₃, d = j+t−L for E_θ). Its declared per-scale bounds
(48879, 549612, 271163, 99084, 20073, 1577, 26, 1 in 10⁻⁶) are the manuscript's,
and all eight are **above** my independently computed values.

Two things it does **not** check, which I did: (a) that all terms vanish beyond the
N-range (41) — I confirmed at every scale; (b) it asserts
`F(17,10)/(17*F(2,3)) == F(3,20)` — an *equality*, so the strictness of the 3/20
bound rests entirely on prose (see K2).

---

## 11. Complete list of gaps

**Repairs required** (the proof is not derivable as written without them):

* **R1 (Lemma 6, (30)–(31)) — load-bearing.** "Because T > 41/8, this forces at
  least four/five/six outside primes" needs (i) b_p(k) ≤ θ_C for outside primes at
  an assigned source (proved in Lemma 5, never cited here) and (ii) the
  discreteness of D (largest D-levels below 7/8 and 3/4 are 13/16 and 11/16).
  With only b_p ≤ 1 the counts are 4/4/4 and the proof **fails numerically**
  (finite total 1015628·10⁻⁶ > 1, tail λ > 50). §4.2.
* **R2 (Lemma 8, (50)–(53)).** The summation range M = ⌈K_θ/θ⌉−1 ≤ (41/40)(L/j) is
  never stated; without it the n-sum diverges and (49)'s exponents 40/41 are
  unexplained. §6.2.

**True statements used without proof** (each one line; none is an error):

* **G-a (Lemma 3/4).** q_p(t_p) ≤ p^{v_p(k)} by minimality of q_p — this is what
  turns non-retention into a_p > η(t_p). (r18's G2, unrepaired.)
* **G-b (Lemma 6).** ϑ(x) ≤ x log 4 is only sketched; ∫₆₄^x dt/log²t ≤ 2x/log²x and
  the monotonicity of 18 log x/x are asserted.
* **G-c (Lemma 6, (37)).** "All these primes are at most ν" — needs
  p ≤ p^i ≤ m/P_C and integrality.
* **G-d (Lemma 7).** "Every carrier level ≥ θ is an integer multiple of 1/L" and
  "carriers are determined by their level assignment" (q_p(t) depends only on
  (p,t)). (r18's G3, G5, unrepaired.)
* **G-e (Lemma 8).** 𝒫_j(x) ≥ P_{j,L}(x) is never asserted. (r18's G4, unrepaired.)
* **G-f (Lemma 1).** The vertex principle for coordinatewise-concave functions and
  the *h < r* case. (r18's G6, unrepaired.)
* **G-g (Lemma 3).** Mean monotonicity of H under pointwise domination is asserted
  ("averaging over a common period").
* **G-h (Lemma 10).** The three tacit provisos of §8.2 (c ≥ 1, m odd, M > 2).

**Overclaim.**

* **G-i.** "Unproved items used in these claims: NONE" — see §7. Chebyshev's
  ϑ-bound and Euler's divergence of Σ1/p are classical inputs, sketched not proved.
  Also, the manuscript reuses the r18 architecture wholesale but the closure block
  does not say so.

**Knife-edges — must never be re-derived in floating point.**

* **K1.** (47) holds by a ratio of **0.999884** (0.012 % in the 75-th power,
  0.064 % in a₀ itself). a₀ = 120347/2500000 is essentially optimal.
* **K2.** The 3/20 density bound for x ≥ 2¹⁷ comes out as
  1.7/(17·(2/3)) = 3/20 **exactly**; it survives only because log 2 > 2/3 and (35)
  are both strict. The author's verifier asserts equality here. Either quote a
  sharper rational log 2 (e.g. > 6931/10000) or extend the sieve to 2¹⁸.
* **K3.** (49) holds with slack ratios 0.961–0.989; 𝒫_j(x_j) ≤ P̄_j with relative
  margins ~10⁻⁶.
* **K4.** Master slack: my exact finite total + tail = **991211.6·10⁻⁶**, i.e. the
  whole pointwise factor has only **0.88 %** headroom below 1. Nothing here is
  robust to a re-parametrisation.

**Not checked, not used.** The HR-type audit's SHA-256, the 7 144 200-window
half-weight search, and the reflected/CRT window audits are auxiliary; the proof
does not depend on them and I did not reproduce them. (Unlike r18, the cited
verifier is actually present, so r18's G7 is resolved.)

---

## 12. Bottom line

The three PROVED rows of the route table hold up. R1 (eight mantissas, adjacent
ratio exactly 9/8) is right and the repaired η really does deliver the 2/3
exponent budget — I reproduced 480/720 by two independent methods, and the
negative-modulus defect of the discarded rule is genuinely fixed. R3 (prime-density
δ(θ) feeding level-dependent K_θ, λ_θ, plus the cardinality-aware E_{k,d} and the
θ ≥ 1/2 bound (42)) is what buys 8.828 from 9.7, and every one of the 57 finite
scales plus the tail reproduces exactly and strictly inside its claimed bound. R4
is exactly right.

I could not break it. The mathematics is correct. But Lemma 6's key count is not
derivable from the sentence the manuscript offers, and the tail's truncation range
is missing, so I cannot certify the manuscript as it stands.

**(A) PASS-WITH-REPAIRS** — apply R1 and R2, and insert G-a…G-h, before
formalization; correct the "NONE" in the dependency closure.
**(B) PASS.**

*Artifacts:* `referee_checks.py` (this directory) — my independent exact-arithmetic
verifier, 66 checks, all passing. `python3 referee_checks.py` runs everything
(≈ 4 min); `python3 referee_checks.py E1 E2 E3` selects the stress-test blocks.
