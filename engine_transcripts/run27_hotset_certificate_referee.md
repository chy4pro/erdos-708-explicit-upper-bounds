# Referee report — Erdős #708, round 15 (hot-set-excluded prefix certificate for the sparse core)

Target: `/Users/roychen/workspace/claudecode/automath/engine/out/claude_blitz_0905/F1_708/report.md`
Background: brief `engine/briefs/erdos708_r15_pro.md`; paper `papers/erdos708/main.tex` (Thm `four`, Prop `cert`,
Cor `affine`, Thm `shadow`, Lem `largeatoms`, Cor `sparsecore`); round-14 referee `engine/harvest/erdos708_pro_r14_referee.md`.
Date 2026-09-05. Every numeric claim below was recomputed independently
(`venv_milp/bin/python`; scripts `ref_v1.py`, `ref_v2.py`, `ref_v3.py` in the session scratchpad).
The three `constants_check*.py` in the target directory were re-run and **reproduce their logs byte-for-byte**.

## 0. Verdict table

| # | Item (report §) | Verdict | Severity |
|---|---|---|---|
| 1 | Thm 4.1 — (SC_64), indeed threshold 4, for 0/1 atom systems, every m, every window (§4) | **PASS** | writing gap only (minor) |
| 2 | Identity W_T = λ(L − Σ_{b∈T} ov(b)); reduction of T1' to (NC) (Prop 5.6, §5.6) | **PASS (exact)** | — |
| 3 | Lemma A + the rescaled hinge–moment inequality (§5.3) | **PASS** | — |
| 4 | Lemma B (§5.4) | **PASS** | — |
| 5 | Theorem C, S*(m) ≈ 1.5·10²⁸/(log₂m)², SAP threshold 260 (§5.5) | **PASS** (numerics conservative) | GAP: floating point, not interval-certified (minor) |
| 6 | Prop 2.1 — barriers escaped with \|T\| = 1 (§2) | **PASS** | novelty limited (see §6) |
| 7 | Prop 3.1 — "carrier = full pattern" violates Hall (§3) | **PASS** on the Hall claim | one auxiliary constant wrong (cosmetic) |
| 8 | Lemma 6.1 — small carriers never half-swallowed (§6.1) | **FAIL as stated / repairable** | **moderate** |
| 9 | §6.2 necessary conditions + 10⁻¹²²m budget bound | **GAP** (budget additivity unproved; numeric slip ×130) | moderate |
| 10 | §6.2 realisation of a fully swallowed carrier (SKETCH) | **FAIL as written** (H ≈ 1.24 > 17/16) — repairable | moderate (already tagged SKETCH) |
| 11 | §6.3 (SC_64) on the crowding family, every m | **PASS for m ≤ 10³⁰²⁹⁷; GAP for larger m** | minor (repair supplied below) |
| 12 | §8 toy LPs; §7, §9, §10 (status tags, dependency graph) | **PASS** — no overclaim found | — |

**Overall: ACCEPT the mathematics of §§2–5 and the status tags; amend §6.1 and §6.2; patch one step of §6.3.**
The report does not overclaim: (NC) and T1' are tagged OPEN/CONDITIONAL exactly where they are, the §6.2
realisation is tagged SKETCH, and the failed script cases in §8 are disclosed. The one place where it *under*-claims
is Theorem C (see §7 below).

---

## 1. Item (1): 0/1 systems, threshold 4, all m (report §4) — **PASS**

Statement checked: if all atom weights are 0/1 then (Σ_e α_{p,e} ≤ 1 forces at most one active e per prime, so the
hypothesis "one atom per prime" is *not* an extra assumption) S₀ = ω_Q for a set Q of **pairwise coprime prime
powers** q ≤ m/64, and Σ_{k≤m}(ω_Q(k)−4)⁺ ≤ Σ_{b∈I}(ω_Q(b)−1)⁺.

The three questions posed:

* **Threshold 4 vs 64.** Correct direction: (S₀−64)⁺ ≤ (S₀−4)⁺ pointwise, so the threshold-4 statement implies
  (SC_64) a fortiori. ✔
* **L and R.** L = Σ_{k≤m}(S₀(k)−64)⁺ over the *initial segment* K = [1,m]; R = Σ_{b∈I}(S₀(b)−1)⁺ over the *window*.
  Theorem `four` has exactly the same two-sided shape (`\sum_{k\le m}(\Omega_P(k)-4)^+\le\sum_{b\in I}(\Omega_P(b)-1)^+`,
  eq. (`eq:four`), for every x ≥ 0). No mismatch. ✔
* **Window vs initial segment.** Prop `cert` supplies ⌊m/d⌋ ≤ N_I(d) ≤ ⌊m/d⌋+1 for any window of m consecutive
  integers; the certificate is *window-free* (feasibility (`eq:F`) is required for every positive integer n), so
  nothing about I is used beyond those counts. ✔

Validity of the adaptation, ingredient by ingredient (I re-derived each with prime powers in place of primes):

(i) **Cube-root peeling.** y = ⌊m^{1/3}⌋; three pairwise coprime q > y have product ≥ (y+1)³ > m, so ω_{Q_L}(k) ≤ 2
for k ≤ m and (ω_Q−4)⁺ ≤ (ω_{Q_S}−2)⁺. ✔ (The paper's step is stated for primes but uses only pairwise coprimality.)

(ii) **Sparse branch.** With r = ω_{Q_S}(n): Σ_{d|n}c_d = (11/21)C(r,2) − (1/7)C(r,3) = r(r−1)(13−r)/42 ≤ (r−1)⁺ ≤
(ω_Q(n)−1)⁺ for *every* n (r(13−r) ≤ 42 for all integers r, and the expression is ≤ 0 for r > 13). ✔ The pairs and
triples qq′, qq′q″ are honest moduli because Q is pairwise coprime, so E₂ = Σ_{k≤m}C(ω_{Q_S}(k),2) and
E₃ = Σ_{k≤m}C(ω_{Q_S}(k),3) hold verbatim. ✔ The repeated-prime term A ≡ 0, correctly noted.

(iii) **Value.** C(|Q_S|,3) ≤ E₃ needs qq′q″ ≤ y³ ≤ m ✔; 3E₃ ≤ ηE₂ needs qq′ ≤ y² hence ⌊m/qq′⌋ ≥ y ✔;
V(c) ≥ E₂/3 ≥ Σ_{k≤m}(ω_{Q_S}(k)−2)⁺ ✔. In the sparse core Σ_{q∈Q_S}1/q ≤ H < 17/16 and m > 4096 ⇒ y ≥ 16 ⇒
η ≤ (17/16)² = 1.129 < 2 ✔.

(iv) **Dense branch.** The report calls the adaptation "verbatim"; it is not quite. Two prime-specific steps must be
redone, and both survive:
  * the paper rules out y ≤ 4 by the numbers η ≤ 0, ¾, 10/9, 25/24 for *prime* sets. For pairwise coprime prime
    powers ≤ y the maxima are H ≤ ½ (y = 2), H ≤ 5/6 (y = 3: {2,3}), H ≤ 5/6 (y = 4: {2,3} or {3,4} — 2 and 4 are
    not coprime), giving η ≤ ¾, 10/9, 25/24 < 2. So η > 2 still forces y ≥ 5. ✔
  * "|Q| ≤ π(y) ≤ y" becomes "#{prime powers ≤ y} ≤ y" (they are distinct integers in [2,y]). ✔
  The greedy set with 3/2 ≤ H_{Q′} < 2 works because every modulus is ≥ 2 so the last term added is ≤ ½ ✔; the
  affine certificate c₁ = −1, c_q = 1 (q ∈ Q, q ≤ m) has Σ_{d|n}c_d = ω_Q(n) − 1 ≤ (ω_Q(n)−1)⁺ ✔ and
  V(c) = Σ_{k≤m}ω_Q(k) − (m+1) ✔, so Σ_{k≤m}min(ω_Q(k),4) ≥ m+1 is again what is needed ✔.

**Verdict: PASS.** Severity of "verbatim": editorial. When this is written up, six extra lines for (iv) are required.
There is **no cheap reduction** to Theorem `four` itself (ω_Q ≤ Ω_P bounds the *wrong* side of R), so the
prime-power version is genuinely needed and is a genuine, if routine, extension.

## 2. Item (2): the exact identity and the reduction to (NC) (report §5.6) — **PASS (exact)**

Every step re-derived:
* Σ_i w_{k,i} = |(2,3] ∩ [0,s_A)| = 1 for hot k (s_A = S₀(k) > 64), and the prefixes P_i(k) are pairwise distinct, so
  Σ_P M_w(P) = Σ_{k hot} d_k = L. ✔
* Carriers divide some k ≤ m, hence P ≤ m, hence N_I(P) ≥ ⌊m/P⌋ ≥ 1: c_P = λM_w(P)/N_I(P) is well defined,
  nonnegative, supported on D ≤ m — inside the referee addendum's cone. ✔
* Feasibility off T is the definition of T = {b : λ·ov(b) > cap(b)}; no circularity, ov depends only on M_w, N_I. ✔
* W_T = λΣ_P M_w(P)(1 − t_P/N_I(P)) and Σ_P M_w(P)t_P/N_I(P) = Σ_{b∈T}Σ_{P|b}M_w(P)/N_I(P) = Σ_{b∈T}ov(b) by
  exchanging the two sums. Hence **W_T = λ(L − Σ_{b∈T}ov(b))**, an identity, not an inequality. ✔
* W_T ≥ L ⇔ Σ_{b∈T}ov(b) ≤ (1−1/λ)L; λ = 2 gives (NC): Σ_{b∈T}ov(b) ≤ L/2. ✔
* R ≥ Σ_{b∈I∖T}cap(b) ≥ Σ_{b∈I∖T}Σ_{P|b}c_P = W_T. ✔ Corollary 5.7 is correctly labelled CONDITIONAL.

This is the cleanest thing in the report. It converts T1′ into a single, sharply stated mass-concentration
inequality and should be quoted verbatim in the next brief.

## 3. Item (3a): Lemma A (report §5.3) — **PASS**

* **S₀(k) = μ(P) + S₀^{(P)}(j)** for k = Pj with P = P_i(k). Correct *because P is built from k's own effective
  atoms*: for p | P, a_p(k) = A_{p,e*_p(k)} = a_p(P); for p ∤ P, v_p(j) = v_p(k). ✔ (This exactness is what fails in
  Lemma 6.1 — see §5 below.)
* μ(P) = s_i < 4 ⇒ d_k < S₀^{(P)}(j) − 60, and d_k > 0 ⇒ d_k ≤ (S₀^{(P)}(j) − 60)⁺. ✔
* a_p(j) ≤ θ = a_i for all p ∤ P, since those effective atoms follow u_i in the "heavier first" order ≺. ✔
* **Rescaled hinge–moment inequality** (t−c)⁺ ≤ θ^{1−r}e_r(a) for a ∈ [0,θ]^N, r = ⌊c/θ⌋+1. The bracketed proof is
  correct in full: e_{C+1} is Schur-concave on ℝ^N_{≥0} (Schur's criterion gives
  (x_i−x_j)(∂_i−∂_j)e_r = −(x_i−x_j)²e_{r−2}(x_{≠i,j}) ≤ 0); (1^{⌊T⌋},{T},0,…) majorises every x ∈ [0,1]^N of sum T;
  e_{C+1} at that vector is C(⌊T⌋,C+1)+{T}C(⌊T⌋,C) ≥ (⌊T⌋−C)⁺+{T}·1[⌊T⌋≥C] ≥ (T−C)⁺ (all three cases
  ⌊T⌋ > C, = C, < C checked). The rescaling x = a/θ, C = ⌊c/θ⌋ uses (t/θ − c/θ)⁺ ≤ (t/θ − ⌊c/θ⌋)⁺ ✔.
  The 3000 exact-rational random/adversarial tests reproduce: 0 violations, max ratio exactly 1.
* Injectivity of k ↦ j = k/P for fixed P ✔; w_{k,i} ≤ s_i − s_{i−1} = θ ✔; (M) applied with N = ⌊m/P⌋ ≤ m/P and the
  primes p | P dropped (which only lowers e_r(h)) ✔. (M) itself re-derived: Σ_{j≤N}∏_{p∈B}a_p(j) =
  Σ_{(e_p)}∏α_{p,e_p}⌊N/∏p^{e_p}⌋ ≤ N∏_{p∈B}h_p, using coprimality of the moduli. ✔
* (m/P)/N_I(P) ≤ (m/P)/⌊m/P⌋ ≤ 2 for P ≤ m. ✔
* **By-products.** S₀^{(P)}(j) > 60 with all a_p(j) ≤ θ_P gives ω(j) > 60/θ_P ≥ 60, so θ_P ≥ 60/log₂(m/P) ≥ 60/log₂m
  and j ≥ p₁···p₆₁. I recomputed the 61-primorial: **10^117.84** (report: 10^117.8, and it uses only > 10^113). ✔
  Also log₁₀ε(1) = 61log₁₀(17/16) − log₁₀(61!) = **−82.099** (report: −82.1). ✔

Lemma A is the technical heart of the round and it is correct. Choosing the moment order **r ≈ 60/θ adapted to the
last-atom mass**, instead of the brief's fixed order 32, is the actual new idea and it does what is claimed.

## 4. Item (3b): Lemma B (report §5.4) — **PASS**

* Atoms of P′ precede q in ≺ ⇒ A_{p′,e′} ≥ θ_q; p′^{e′} | b ⇒ a_{p′}(b) ≥ A_{p′,e′} ≥ θ_q ⇒ at most ⌊S/θ_q⌋ such
  primes, each with ≤ E admissible exponents. ✔
* w_{k,i} > 0 ⇒ μ(P′) = s_{i−1} ≤ 3, and each atom of P′ has mass ≥ θ_q ⇒ |P′| ≤ 3/θ_q. ✔
* Distinct atom sets give distinct integers P′ (atoms of P sit at distinct primes), so counting atom sets is a valid
  upper bound. ✔
* Σ_{l≤L}C(M,l) ≤ (1+M)^L for L ≥ 1 (term-wise 1/l! ≤ C(L,l)). ✔ SAP bound 2^{S/θ_q}: E = 1, P′ a subset of the
  ≤ ⌊S/θ_q⌋ effective atoms of b of mass ≥ θ_q. ✔

## 5. Item (4): Theorem C (report §5.5) — **PASS**, numerics conservative

Structure: ov(b) ≤ Σ_q 2ε(θ_q)·#{carriers P | b with last atom q} (Lemma A) ≤ Σ_q 2θ_q·G_S(θ_q) (Lemma B), and
Σ_q θ_q = Σ_{(p,e)∈𝒜, p^e|b} A_{p,e} ≤ E·Σ_p a_p(b) = ES (for a fixed p, A_{p,e} ≤ a_p(b) for all e ≤ e*_p(b), and
there are ≤ E of them). ⇒ ov(b) ≤ 2ES·sup G_S. ✔ All steps correct.

* **Piecewise monotonicity.** On θ ∈ (60/r, 60/(r−1)] one has ⌊60/θ⌋+1 = r constant, and log G_S =
  (1−r)logθ + log(H^r/r!) + (3/θ)log(1+SE/θ) is decreasing in θ (r ≥ 61 > 1). The supremum on the piece is the limit
  at the *excluded* left endpoint, i.e. the formula at θ = 60/r **with the same r** — which is exactly what
  `constants_check3.py::logG` evaluates. **No off-by-one.** ✔ The restriction θ ≥ 60/log₂m corresponds to
  r ≤ ⌊log₂m⌋+1 = `rmax`; where the piece-maximum falls below the allowed θ-range the script over-estimates, which
  is conservative. ✔
* **ov(b) = 0 for S ≤ 2** (μ(P) > 2 and D | n ⇒ S₀(n) ≥ μ(D)). ✔
* **Independent recomputation of S\*(m)** with the *full integer* r-grid (no geometric sub-sampling) and *no* safety
  factor, solving 4ES·sup_r G_S ≤ S−1 exactly:

  | log₁₀ m | report's S\* | exact S\* (this referee) |
  |---|---|---|
  | 3000 | ≥ 1.25·10²⁰ | **1.355·10²⁰** |
  | 10⁴ | ≥ 1.169·10¹⁹ | **1.219·10¹⁹** |
  | 10⁵ | ≥ 1.021·10¹⁷ | **1.219·10¹⁷** |

  The reported values are conservative by 4–20 %. I also verified directly (not by the report's monotonicity
  argument) that 4ES·sup G_S ≤ S−1 holds for **every** S from 3 to the reported S\* on a ratio-1.05 grid: no failure.
  ✔ The asymptotic S\*(m) ≈ 1.5·10²⁸/(log₂m)² is reproduced by hand: the bracket
  log₁₀(e/60)+log₁₀H+(1/20)log₁₀(SEr/60) changes sign at SEr = 60·10^26.36, and with E ≈ r_max ≈ log₂m this is
  60·10^26.36/(log₂m)² = 1.51·10²⁸/(log₂m)². ✔
* **SAP m-free threshold.** Re-scanned the full integer range r = 61…3·10⁶ (the report scanned to 10⁷ via
  `constants_check4`, whose log is present): the largest S with 4S·sup_r ψ_S ≤ S−1 is **262**; S = 263 fails. The
  asymptotic slope S log₁₀2 − 60 log₁₀(60/(eH)) per unit of 1/θ changes sign at S = 262.6, consistent. The report
  states **260** for margin. ✔
* **GAP (minor).** All of this is double-precision floating point. `constants_check4.log` additionally ends in a
  `ModuleNotFoundError: No module named 'sympy'`, so the "61-primorial = 10^117.8" line it is cited for was never
  produced by that script — I computed it independently (10^117.84) and it is right, but the citation is stale.
  For a paper or a Lean statement, sup_r G_S must be certified in interval arithmetic; the report itself says so.

**Under-claim.** Theorem C + Prop 5.6 immediately yield an *unconditional* theorem the report never states:

> **If every b ∈ I has S₀(b) ≤ S\*(m), then T = ∅ and R ≥ W_∅ = 2L.** In particular (SC_64) holds on I with a
> factor 2 to spare. For SAP systems the hypothesis is the m-free "S₀ ≤ 260 on I", for every m > 4096.

See §7.

## 6. Item (5): Prop 2.1 and Prop 3.1 (report §§2–3)

**Prop 2.1 — PASS.** Feasibility: at b ∈ I∖T with w = ω_P(b) ≤ w*, Σ_{pq|b}c_{pq} = C(w,2)·2/w* = w(w−1)/w* ≤ w−1 =
cap(b) for w ≥ 1, and 0 = 0 for w ∈ {0,1}. ✔ Value ≥ (2/w*)Σ_{pq≤m}(⌊m/pq⌋−1). ✔ On the r14 family w* ≤ 65 is
exactly r14 Corollary 9 as re-verified in the round-14 referee report ("S₀ ≤ 65 off B") ✔. The w* values for the r13
and centred families are quoted from documents not supplied to me; they are plausible (ω_P(t) ≤ log m / log p_min for
the reflected/centred points, since S₀(B±t) = S₀(t)) but are **asserted, not verified here**. The estimate
W_T ≥ mH²/74 − n² drops Σ_p 1/p², legitimate for these families; against L ≤ mH^65/65! the conclusion W_T ≫ L is
robust by ~10^80 whatever the constants. ✔

*Novelty caveat.* The round-14 referee had already exhibited the |T| = 1 escape on exactly the B2 family (c_D = 64 on
65-products, value 64·L_64; and c_{pq} = 1/3 on the C = 2 witness, value 13.8·L₂). Prop 2.1 replaces that by a
uniform pair certificate and extends it to two further families. Useful consolidation; not a new phenomenon.

**Prop 3.1 — PASS on the Hall claim.** The pigeonhole (65 dyadic intervals cover [p₀^65,(2p₀)^65], so one holds
≥ C(n,65)/65 of the 65-products) ✔; S₀(k_A) = 65, d_k = 1 ✔; k_A > m/2 ⇒ B ± k_A ∉ I = (B−m/2, B+m/2] so B is the
unique multiple ✔; cap(B) = n−1 ≪ C(n,65)/65 ✔. Hall fails, so coordinator note (i)'s "carrier = full pattern D_k"
cannot be routed. This is a clean and correct refutation.

*Cosmetic error.* "R ≥ 2#{t < m/2 : ω_P(t) ≥ 2} ≥ m(Σ1/p)²/3" is not justified: Σ_{p<q}⌊N/pq⌋ counts each t with
multiplicity C(ω_P(t),2) ≤ C(65,2) = 2080, so the honest bound is ≈ m(Σ1/p)²/128, not /3. Since L ≤ mH^65/65!, the
conclusion R ≫ L is unaffected. Severity: cosmetic.

## 7. Item (6): Lemma 6.1 and §6.2, §6.3

### 7.1 Lemma 6.1 — **FAIL as stated; repairable; the m ≤ 10³⁰⁰⁰ application survives**

The proof writes, for a crowded multiple b = Pj of a carrier P, "S₀^{(P)}(j) = S₀(b) − μ(P) > S\*(m) − 4".
**This is wrong.** The exact splitting S₀(Pj) = μ(P) + S₀^{(P)}(j) of Lemma A holds only because there P was built
from *k's own effective atoms*. For an arbitrary multiple b = Pj the correct identity is

  S₀(b) = Σ_{p|P} a_p(b) + S₀^{(P)}(j),  and Σ_{p|P} a_p(b) can be as large as ω(P), not μ(P) < 4

(b may carry higher powers of the primes of P than P does). Since a carrier has μ(P) < 4 with all atom masses
≥ θ_P ≥ 60/log₂(m/P), one gets ω(P) ≤ 4/θ_P ≤ log₂(m)/15, which is **665 for m = 10³⁰⁰⁰ but 2.2·10⁹ for
m = 10^{10^{10}}**. The corrected statement is

  **f_P < H(1 + P/32)/(S\*(m) − ω(P)),  ω(P) ≤ log₂(m/P)/15.**

Everything else in the proof is right: the multiples Pj of P in I form N_I(P) consecutive j; Σ_j S₀^{(P)}(j) ≤
Σ_{(p,e)}α_{p,e}(N_I(P)/p^e + 1) ≤ N_I(P)H + (m/64)H using p^e ≤ m/64; and (m/64)/N_I(P) ≤ P/32 from
N_I(P) ≥ ⌊m/P⌋ ≥ m/(2P). ✔

Consequence for the stated conclusion "f_P ≤ 1/2 for P ≤ 15·S\*(m)": at P = 15S\* the numerator is
(17/16)(15S\*/32) = 0.498 S\*, so one needs ω(P) ≲ 0.0039·S\*(m). With S\*(m) ≈ 1.5·10²⁸/(log₂m)² and
ω(P) ≤ log₂m/15 this holds iff **log₁₀ m ≲ 2.9·10⁸**. For the regime the report actually uses it in
(m ≤ 10³⁰⁰⁰: ω(P) ≤ 665 against 0.0039·S\* = 4.7·10¹⁷) the lemma survives with 15 orders of room. But the lemma is
stated with no restriction on m and is false, as stated, for m beyond ≈ 10^{3·10⁸}. **Severity: moderate** — the
statement must be amended; no downstream PROVED claim in the m ≤ 10³⁰⁰⁰ range is lost.

### 7.2 §6.2 — necessary conditions **GAP**, realisation **FAIL as written**

Necessary conditions: q > N_I(P) ⇒ q divides at most one multiple of P in I ✔; carriers ≤ m/10^117.8 ⇒ q ≤ m/10^113
⇒ P > 10^113/2 ✔; 4ε(1)C(W,3) > W−1 ⇒ W > 1.37·10⁴¹ ✔ (I get 1.226·10⁴¹ from ε(1) = 10^−82.099 taken exactly;
the report's 1.3·10⁴¹ is in the safe direction); Σ1/q ≥ WN·64/m ≥ 32W/P and H < 17/16 ⇒ W < 17P/512 = P/30.1 ✔ ⇒
P > 4.1·10⁴² ✔.

Two defects:

* **GAP (moderate): budget additivity is not established.** "each swallowed carrier costs reciprocal budget
  ≥ 32·10⁴¹/P, so Σ_{P swallowed} 1/P ≤ 3.3·10⁻⁴¹" silently assumes the private-prime sets of distinct swallowed
  carriers are disjoint. A prime q with q > N_I(P) ≥ N_I(P′) can be private for both P and P′; "private" only means
  q divides at most one multiple of *each* P. Without disjointness the budgets do not add and the 10⁻¹²²m mass bound
  — quoted again in §6.4 and §7 as the reason the mechanism is harmless — is not proved.
* **Numeric slip (harmless direction).** (17/16)/(32·1.3·10⁴¹) = **2.55·10⁻⁴³**, not 3.3·10⁻⁴¹. The report used the
  100× weaker value and still reached < 10⁻¹²²m, so the conclusion is safe (the true bound would be 10⁻¹²⁴·⁶m).

* **Realisation (SKETCH) — FAIL as written.** The stated system has base atoms α = 0.3 on all primes in [p₀,p₀²⁰]
  (H ≈ 0.3 ln 20 = **0.899**) *plus* private unit primes throughout (10⁵⁰⁰,10⁷⁰⁰], whose reciprocal sum is
  ln 1.4 = **0.336**. Total **H ≈ 1.235 > 17/16 = 1.0625**: the sparse-regime hypothesis fails, so the exhibited
  window is not an instance of (SC_64) at all. The report's line "Σ1/q ≤ 0.34, total H ≤ 1.0625 − ε" is simply an
  arithmetic error (0.899 + 0.336 ≠ ≤ 1.0625).
  **Repair:** take the WN = 10⁶⁹⁶ private primes from (10⁶⁹⁹,10⁷⁰⁰] instead — there are ≈ 10^696.75 of them, and
  their reciprocal sum is ≤ 10⁶⁹⁶·10⁻⁶⁹⁹ = 10⁻³, leaving H ≈ 0.90 < 17/16. Every other size in the sketch checks
  out (hot k needs ≥ 214 base atoms ✔; carriers have 7–13 base atoms ✔; P ≈ p₀²⁴⁰ = 10¹²⁰⁰⁰, N ≈ 10⁵⁰⁰ ≥ 2^200 ✔;
  the hot integer q₁q₂q₃·(204 base primes) ≈ 10^12300 ≤ m = 10^12500 with S₀ = 64.2 > 64 ✔; the ≺-prefix of mass in
  (2,3] is exactly q₁q₂q₃ ✔; (0.9)²⁰⁴/204! = 10^−392.9 ≈ the quoted 10⁻³⁹⁰ ✔; ov ≈ 10¹⁹⁷ > W/2 = 5·10¹⁹⁵ ✔).
  With that one change the sketch looks sound, but it remains a sketch and I did not certify the CRT step.

### 7.3 §6.3 crowding family — **PASS for m ≤ 10^30297; GAP above that**

Verified: Σ_{q∈Q}1/q ≈ ln(138/51) = 0.9954 < 17/16 ✔; carriers are exactly the 3-subsets (all masses 1, μ ∈ (2,4)) ✔;
crowded ⇒ 4ε(1)C(ω,3) > ω−1 ⇒ ω > **1.226·10⁴¹** ✔; log₁₀C(|Q|,24) ≤ **3228.2** so the 24th moment is controlled once
m ≥ 10^3252, which is implied by L > 0 (m ≥ 10^3315) ✔; and

  log₁₀(Σ_{b∈T}ov(b)/m) ≤ **−945.1** (report: < −940, conservative) ✔.

Case (a) L ≤ 10m^{31/32}: (Sh) closes it ✔. Case (b) L > 10m^{31/32}: 10m^{31/32} ≥ 2·10^{−945}m holds for
log₁₀m ≤ **30297** (report: 10^30000) ✔.

**GAP (minor) in case (c), m > 10³⁰⁰⁰⁰.** The report asserts L ≥ ½·m(Σ_Q 1/q)^65/65! > 10⁻⁹³m. Nothing supplied
implies this: Σ_{k≤m}C(ω_Q(k),65) = Σ_{|A|=65}⌊m/k_A⌋ is *not* a lower bound for Σ_{k≤m}(ω_Q(k)−64)⁺, since
C(ω,65) ≥ (ω−64)⁺, the wrong direction. The claim is true but needs an argument. **Repair (Bonferroni), which I
checked:** for every integer ω ≥ 0, C(ω,65) − 66C(ω,66) ≤ 1[ω = 65] (equality at 65 and 66; ≤ 0 for ω ≥ 66). Hence
L ≥ #{k ≤ m : ω_Q(k) = 65} ≥ m·e₆₅ − C(|Q|,65) − 66(m·e₆₆ + C(|Q|,66)), and 66e₆₆/e₆₅ ≤ Σ_Q 1/q = 0.9954, so
L ≥ 0.0046·m·e₆₅ − 10^8716.6 − 10^8852.1 ≥ **10^−93.4 m** for every m ≥ 10^8950 — which is ≫ 2·10^{−945}m, closing
case (c) for **all** m > 10³⁰⁰⁰⁰ with no upper limit. So the conclusion "(SC_64) on this family for every m" stands;
only the justification was missing.

*Correctly self-flagged:* since this family is a 0/1 system, Theorem 4.1 already proves (SC_64) for it. §6.3 is a
methodological demonstration that the §5 cone closes the brief's proposed crowding adversary — not a new theorem.

### 7.4 §7, §8, §9, §10

§7's necessary shape for T2′ follows from §§2,4,5,6 as stated (with Lemma 6.1 amended as in 7.1). §8's toy LP
outputs are reproduced from `hotset_frac_lp.log` (m = 40, C = 2, reflected, P = {2,3,5,7,11}: L = 1, R = 20,
W_{T=∅} = 16, W_{|T|=1} = 15 ✔; mixed masses, reflected, m = 80: L = 2.5, R = 28.5, W_{t₀=1} = 24 with |T| = 1 ✔),
the MILP encoding does compute max_T W_T (y_b ≤ (Ac)_b, y_b ≤ M(1−z_b), (Ac)_b ≤ cap_b + Mz_b), and the two skipped
"F5 crowding" cases are honestly disclosed as an unmet `sympy` dependency. §9's Lean list and §10's dependency graph
match what is actually proved. **No overclaim found anywhere in the status tags.**

## 8. Citable new theorems

Two items are, in my judgement, publishable in the paper as they stand (after the noted edits):

1. **Theorem 4.1 (0/1 systems).** "For every set Q of pairwise coprime prime powers, every m ≥ 1 and every x ≥ 0,
   Σ_{k≤m}(ω_Q(k)−4)⁺ ≤ Σ_{b∈I}(ω_Q(b)−1)⁺; consequently (SC_64) holds for every 0/1 atom system, every m and every
   window." A natural companion to Theorem `four` (Section `sec:four`), costing ~10 lines (peeling, the pair–triple
   certificate, and the two prime-power adjustments in the dense branch listed in §1(iv) above). Its structural
   corollary — **any counterexample to (SC_64), and any T2′ family, must use fractional atom weights** — is worth
   stating explicitly; it complements remark (c) after Cor. `sparsecore` and narrows the open problem.

2. **The moderate-mass window theorem (currently under-claimed).** Combining Lemma A, Lemma B, Theorem C and
   Prop 5.6 with T = ∅:
   > Let m > 4096 and let the atom system be sparse (H < 17/16). If S₀(b) ≤ S\*(m) for every b in the window I, then
   > Σ_{b∈I}(S₀(b)−1)⁺ ≥ 2Σ_{k≤m}(S₀(k)−64)⁺, where S\*(m) ≥ 1.2·10²⁰ for m ≤ 10³⁰⁰⁰ and S\*(m) ≈ 1.5·10²⁸/(log₂m)²
   > in general; for single-atom-per-prime systems the hypothesis may be taken to be S₀ ≤ 260 for every m.
   This is unconditional, quantitative, and *new*: it is the first positive (SC_64) result that is not restricted by
   the size of m (Thm `shadow` caps at m ≤ 10^2887/10^2942) and not restricted to 0/1 weights. It should be stated
   as a theorem, with the numeric supremum certified in interval arithmetic.

Also worth including as a lemma, because it is what defines the remaining problem: **Prop 5.6's identity**
W_T = λ(L − Σ_{b∈T}ov(b)), and hence "T1′ ⇔ (NC)".

Not citable as new: §6.3 (subsumed by Theorem 4.1), Prop 2.1 (the |T| = 1 escape is already in the round-14 referee
report), §6.2 (broken as written), Lemma 6.1 (needs amendment, and covers only P ≤ 15S\*(m) — a vanishing sliver of
the carrier range P ≤ m/10^117.8).

## 9. What the referee could not check

* w* ≤ 73 on the r13 family and w* ≤ 65 on the centred family (§2): the r13 source was not supplied.
* The CRT construction in §6.2 (tagged SKETCH by the author, and its H is wrong as written).
* All Theorem C numerics are floating point. They are reproducible and conservative, but not certified.
