# Referee report — Erdős #708, round 14 (window-adapted certificate LP)

Source: `/Users/roychen/workspace/claudecode/automath/engine/harvest/erdos708_pro_r14_raw.md`
Brief:  `/Users/roychen/workspace/claudecode/automath/engine/briefs/erdos708_r14_pro.md`
Date: 2026-09-04. All computations exact-integer / certified-rational unless flagged.

## 0. Verdict table

| Claim | Verdict | Note |
|---|---|---|
| Lemma 1 (window 1st moment, \|T_72\| < 1105m/73728) | **PASS** | constants exact |
| Lemma 2 (truncated ℓ-th moment ≤ 2mH^ℓ/ℓ!) | **PASS** | truncation D ≤ m does absorb the +1 |
| Lemma 3 (W(I) ≤ Y(n−1) on I = (m!−m, m!]) | **PASS** | one unstated hypothesis, harmless (§2.3) |
| Lemma 4 (explicit dual cover, cost Y(n−1)) | **PASS** | verified exactly on 3 instances |
| Lemma 5 (L_C ≥ C(n,C+1)) | **PASS** | |
| Theorem 6 (W < L_C, and R ≥ L_C + C − 1) | **PASS** | |
| Lemma 7 (p_{2n} ≤ 10ns, n = 2^s, s ≥ 2048) | **PASS** | every inequality direction correct |
| Theorem 8 (infinite family, W/L_64 → 0) | **PASS** | all hypotheses of (SC_64) genuinely hold |
| Corollary 9 (exactly one hot point) | **PASS** | in fact S₀ ≤ 65 off B |
| Theorem 10 (exact C = 2 witness, gap 1060) | **PASS** | numbers reproduced exactly |
| §8 verdict "A2 refuted as a universal strategy" | **PASS (narrow reading only)** | A2's *literal* recipe fails; see §5 |
| §9/final "the next route must leave the certificate cone" | **GAP — moderate** | refuted: a hot-set-excluded variant of the *same* cone beats L by a factor 64 on this very family (§5) |
| §10 artifacts (sandbox .py + SHA-256) | **GAP — cosmetic** | files not present, hashes unverifiable |

**Overall: ACCEPT the mathematics; REJECT the headline's breadth.** Every lemma and both
main theorems are correct as stated. What is proved is that the *specific* LP
`W(I) ≥ L for every window` (brief's T1/T2, and T4 for C = 2 above m = 326 275 048 607)
is false. The stronger editorial conclusion — that any future route must abandon
nonnegative divisor certificates — is disproved by a two-line modification of the same
certificate cone, which the transcript did not test.

---

## 1. Framework sanity

The counting principle used is
R = Σ_{b∈I}(S₀(b)−1)⁺ ≥ Σ_{b∈I} Σ_{D|b} c_D = Σ_D c_D N_I(D) ≥ Σ_{D≤m} c_D ⌊m/D⌋,
valid for any c ≥ 0 satisfying (F_I). Both inequalities are correct (N_I(D) ≥ ⌊m/D⌋ for
D ≤ m in any window of m consecutive integers). The LP is bounded because every D ≤ m has
a multiple in I. Moduli D > m carry objective coefficient 0 and may be discarded. ✔

---

## 2. Lemmas 3 and 4 (the core)

### 2.1 Lemma 3 — every step checked

- B = m! ∈ I = {B−m+1,…,B}, since x = B−m. ✔
- For D ≤ m: D | m! = B. For D < m: B − D ∈ I and D | B − D. ✔ (D = m gives B−m = x ∉ I —
  correctly singled out.)
- Reflection S₀(B−D) = r(D) := ω_P(D). ✔ For p ∈ P with p ≤ m: p | B, so p | B−D ⟺ p | D.
  For p ∈ P with p > m (not excluded by the stated hypotheses): p ∤ D since D ≤ m < p, and
  B−D ≡ −D (mod p) so p ∤ B−D — the identity survives. ✔
- **Zero forcing (3.1).** D < m, r(D) ≤ 1 ⇒ capacity at B−D is (r(D)−1)⁺ = 0; the constraint
  at B−D reads Σ_{E | B−D} c_E ≤ 0 with c ≥ 0, and D | B−D, D ≤ m ⇒ c_D = 0. ✔ Correct and
  it is the genuinely new ingredient relative to round 13.
- **(3.2).** Surviving D < m have two distinct primes of P, so D ≥ p₁p₂ and ⌊m/D⌋ ≤ Y. ✔
- **D = m.** ⌊m/m⌋ = 1 ≤ Y, which needs Y ≥ 1, i.e. the hypothesis m ≥ p₁p₂. ✔ (Without it
  the lemma is false: c_m alone would give value 1 > 0 = Y(n−1)·0.)
- **(3.3).** Every D ≤ m divides B, so Σ_{D≤m} c_D ≤ (S₀(B)−1)⁺. ✔ (Also valid including the
  D > m dividing B, by nonnegativity.)
- Combination Σ c_D⌊m/D⌋ ≤ Y Σ c_D ≤ Y(n−1). ✔

### 2.2 Lemma 4 — checked

Dual feasibility in all three cases (r(D) ≥ 2 via y_B = Y ≥ ⌊m/D⌋; r(D) ≤ 1, D < m via
y_{B−D} = m ≥ ⌊m/D⌋; D = m via y_B = Y ≥ 1) is correct, and every y-positive point other
than B has S₀ ≤ 1 hence zero hinge cost, so cost = Y·(S₀(B)−1) = Y(n−1). ✔ Weak duality
independently reconfirms Lemma 3.

### 2.3 The one unstated hypothesis (cosmetic)

Lemma 3 asserts "S₀(B) = n" but only assumes m ≥ p₁p₂; this needs p_n ≤ m. **The conclusion
is unaffected** because S₀(B) ≤ n always, and only the upper bound is used. Both applications
(Thm 8: q_t ≤ m_t = q_t^65; Thm 10: 6899 ≤ m) satisfy p_n ≤ m. Lemma 4's cost formula has the
same cosmetic dependence. Severity: editorial only.

### 2.4 Independent numerical verification of Lemma 3/4

Exact LP optima certified by *matching rational primal + dual pairs* (both verified with
`Fraction` arithmetic; scipy/HiGHS used only to produce the candidates), on the true big-integer
windows (m!−m, m!]:

| P | m | exact W(I) | Lemma-3 bound Y(n−1) |
|---|---|---|---|
| {2,3,5,7} | 35 | 10 | 15 |
| **{2,3,5,7,11}** (referee's own instance) | **40** | **13** | **24** |
| {3,5,7,11} | 40 | 4 | 6 |
| {2,3,5,7,11,13} | 45 | 17 | 35 |
| {5,7,11,13} | 60 | 3 | **3 (tight)** |
| {2,3,5,7,11,13,17} | 60 | 25 | 60 |

Also verified exactly on these instances: S₀(B) = n; S₀(B−t) = S₀(t) for 1 ≤ t < m; every
D < m with r(D) ≤ 1 sits under a zero-capacity reflected point; every optimal-support modulus
has r(D) ≥ 2 or D = m; Lemma 4's y is dual-feasible with cost exactly Y(n−1).
Scripts: `ref_r14_indep.py`, `ref_r14_b.py`, `ref_r14_c.py`.

*Tooling note (not a defect of the transcript):* `sympy.solvers.simplex.lpmax` returned 11 and
14 for the first two rows, with negative entries in the returned argmax — i.e. it is wrong here.
The table above uses certified rational primal/dual pairs instead.

---

## 3. Lemmas 5, 7 and Theorems 6, 8, 10

**Lemma 5.** The C(n,C+1) squarefree products of (C+1)-subsets are distinct (unique
factorisation), each ≤ product of the C+1 largest primes ≤ m, each has S₀ = C+1 so hinge 1. ✔

**Theorem 6.** (6.1) ⇒ W < L_C is immediate. (6.2): R = Σ_{t=1}^{m−1} h₁(S₀(t)) + h₁(n) and
L_C = Σ_{t=1}^{m−1} h_C(S₀(t)) + h_C(S₀(m)); pointwise h₁ ≥ h_C; and h₁(n) − h_C(S₀(m)) ≥
(n−1) − (n−C) = C−1 using S₀(m) ≤ n and n ≥ C+1. ✔ Confirmed numerically (R − L_C ≥ C−1 on
reflected test windows for C = 2,3,4).

**Lemma 7 — every inequality direction re-derived (natural logs).**
- (7.1) 4^u/(2u+1) ≤ C(2u,u): central coefficient is the largest of 2u+1 terms summing to 4^u. ✔
- (7.2) Legendre: each bracket ⌊2u/p^j⌋ − 2⌊u/p^j⌋ ∈ {0,1} and vanishes for p^j > 2u, so
  p^{e_p} ≤ 2u and C(2u,u) ≤ (2u)^{π(2u)}. ✔
- (7.3) π(2u) ≥ (u log 4 − log(2u+1))/log(2u) — direction correct. ✔
- s ≥ 2048 ⇒ 10s ≤ 2^s = n (true from s = 6 on). ⇒ 2u = 10ns ≤ n², so
  **log(2u) ≤ 2 log n = 2s·log 2 ≈ 1.386s < 2s** ✔ (the claim log(2u) < 2s is correct and has
  ~30 % slack).
- log 4 > 1 ⇒ first term > u/(2s) = 5n/2; log(2u+1)/log(2u) < 2 (⟺ 2u+1 < (2u)², true) ⇒
  π(2u) > 5n/2 − 2 > 2n for n > 4. ⇒ p_{2n} ≤ 2u = 10ns. ✔
- Numerical sanity outside the stated range: s = 4,6,8,10,12 give p_{2n}/(10ns) ≈ 0.20, 0.19,
  0.18, 0.17, 0.17 — the bound is comfortable, not borderline.

**Theorem 8 — hypotheses of (SC_64) all genuinely hold.**
- α_{p,1} = 1 only ⇒ Σ_j α_{p,j} = 1 ≤ 1, α ∈ [0,1]. ✔
- Support: q_t ≤ m_t/64 ⟺ q_t^64 ≥ 64. ✔
- H = Σ_{p∈P_t} 1/p ≤ n_t/(n_t+2) < 1 < 17/16 (uses p_{k} ≥ k+2). ✔
- m_t = q_t^65 > 4096. ✔
- Lemma 5 hypothesis: product of the 65 largest chosen primes ≤ q_t^65 = m_t. ✔
- Lemma 3 hypothesis m ≥ p₁p₂ and p_n = q_t ≤ m_t. ✔
- t ≥ 11 ⇒ s_t = 2^t ≥ 2048, so Lemma 7 applies. ✔

Growth chain, each step re-checked:
p_{n+1}p_{n+2} > n_t² ✔ ⇒ W ≤ (n_t−1)⌊m/(p_{n+1}p_{n+2})⌋ < m/n_t = q_t^65/n_t ≤
10^65 n_t^64 s_t^65 ✔ (8.2). C(n,65) ≥ (n/2)^65/65! needs n − 64 ≥ n/2 i.e. n ≥ 128; n_t = 2^2048
✔ (8.3). Ratio ≤ 20^65·65!·s_t^65/n_t ✔ (8.1). Numerics: 20^65 < 2^325 ✔; 65! ≈ 2^302.0 < 2^455 ✔;
so numerator < 2^{780+65t} ✔; 2^t > 780+65t at t = 11 (2048 > 1495) ✔ and the induction step
(LHS gains 2^t ≥ 2048, RHS gains 65) ✔. Hence W(x_t) < L_64 and W/L_64 → 0 doubly
exponentially. **PASS.**

**Corollary 9.** n_t > (10 s_t)^65 follows from 2^t > 780+65t (checked: (10·2048)^65 ≈ 2^930.9 <
2^2048) ✔. 66 chosen primes force u ≥ (n_t+2)^66 > n_t^66 > m_t = q_t^65 ≤ n_t^65(10s_t)^65,
contradiction ✔. So S₀ ≤ 65 on [1, m_t], hence on all window points except B_t, where
S₀ = n_t > 72. **PASS** — and in fact the window has S₀ ≤ 65 off B, stronger than "≤ 72".

**Theorem 10 — reproduced exactly with `sympy.primerange`.**
- |primes ∩ [3299, 6899]| = **425**; two smallest 3299, 3301; three largest 6871, 6883, 6899. ✔
- m = 6871·6883·6899 = **326 275 048 607**. ✔
- p₁p₂ = 10 889 999; Y = ⌊m/p₁p₂⌋ = **29 960**. ✔
- W ≤ 29 960·424 = **12 703 040** < C(425,3) = **12 704 100**; gap **1060**. ✔
- Hypotheses: H = Σ1/p = 0.08790 < 17/16 ✔ (transcript's cruder 425/3299 = 0.1288 also < 17/16);
  6899 ≤ m/64 ✔; m > 4096 ✔; Lemma-5 hypothesis holds with equality ✔.
- **Extra robustness check (referee's own).** The obstruction does not depend on the lossy
  ⌊m/D⌋ coefficient. Using the *exact* window counts N_I(D) ≤ ⌊(m−1)/p₁p₂⌋ + 1 = 29 961 for every
  admissible D still gives 29 961·424 = 12 703 464 < 12 704 100. So Theorem 10 survives the
  natural strengthening of the LP to true counts, with 636 to spare.
- Exact L₂ for this instance (computed, not just bounded): since 3299⁴ > m ≥ 3299³, S₀ ≤ 3 on
  [1,m], so L₂ = Σ_{p<q<r} ⌊m/pqr⌋ = **30 287 189** (= 2.38 × C(425,3)).

---

## 4. Does this kill the route? Yes for T1/T2/T4-as-stated

Theorem 8 **is a genuine counterexample** to "W(I) ≥ L for every window in the sparse regime":
the instance satisfies every hypothesis of (SC_64) verbatim, x_t = m_t! − m_t ≥ 0 is a legal
window offset, and W(x_t)/L_64 → 0. So

- **brief's T1** ("for every window an (F_I)-feasible certificate with value ≥ L") — **false**;
- **brief's T2** (dual form: every fractional cover costs ≥ L) — **false**, with the explicit
  cover of Lemma 4;
- **brief's T4 for C = 2** — **false** for any bound reaching m = 326 275 048 607.

The mechanism is clean and, in hindsight, forced: the single point B = m! lies in the window and
is divisible by *every* D ≤ m, so its own capacity S₀(B) − 1 caps the total certificate mass
Σ_D c_D; the reflected points B − D then zero out every modulus of P-rank ≤ 1. This is the
round-13 barrier point (n = lcm(1..m)) moved *inside* the window, which is exactly what the
round-13 result did not cover. The extension is correct and non-trivial.

**It says nothing against (SC_64) itself.** On the same family R ≥ L_64 + 63 (Theorem 6, (6.2)),
so (SC_64) holds there with slack — correctly and prominently stated by the transcript. No
overclaim on this point.

---

## 5. Where the transcript overreaches (the one substantive finding)

§9 and the closing paragraph assert that the next viable route **must leave** the cone "one
nonnegative coefficient c_D acting on all D-multiples in the window". **This is not established,
and is in fact false on the transcript's own family.** The counting principle never required
feasibility at *every* window point:

  R = Σ_{b∈I} h₁(S₀(b)) ≥ Σ_{b∈I∖T} h₁(S₀(b)) ≥ Σ_D c_D · N_{I∖T}(D),   c ≥ 0, (F_{I∖T}) only.

Take T = {B} (legitimate: Corollary 9 proves |T| = 1) and N_{I∖T}(D) ≥ ⌊m/D⌋ − 1.

- **Theorem 8's family, C = 64.** Put c_D = 64 on each of the C(n_t,65) products D of 65 chosen
  primes, 0 elsewhere. Every cold point has S₀ ≤ 65 (Cor. 9), so at most one such D divides it,
  and the constraint reads 64 ≤ (S₀(b)−1)⁺ = 64 — feasible, with equality. Since S₀ ≤ 65 on
  [1,m], L_64 = Σ_A ⌊m/∏A⌋ exactly, and no squarefree 65-product divides m = q^65, so
  Σ_A ⌊(m−1)/∏A⌋ = L_64. Value = **64·L_64 ≫ L_64.**
- **Theorem 10's instance, C = 2 (computed exactly).** c_{pq} = 1/3 on all 90 100 rank-2 moduli is
  (F_{I∖{B}})-feasible (cold points have S₀ ≤ 3, so at most C(3,2)/3 = 1 ≤ 2), with value
  (1/3)·Σ_{p<q}⌊(m−1)/pq⌋ = **1 257 278 711/3 ≈ 4.19·10⁸ = 13.8 × L₂ = 33 × C(425,3)**.

So on precisely the windows the transcript exhibits, a nonnegative divisor certificate inside the
same cone proves (SC_C) with a factor 64 (resp. 13.8) to spare — it merely must not be required
to be feasible at the lcm-rich hot point. The correct conclusion is narrower:

> **What is dead:** requiring (F_I) on the *whole* window, i.e. the LP W(I) exactly as the brief
> defines it, and coordinator plan A2's literal recipe of "scale down coefficients on moduli
> dividing hot points" (useless when a hot point is divisible by all D ≤ m).
> **What is not dead:** the certificate cone itself. The open question the round should have
> asked is whether a family exists with |T| large *and* W_{I∖T} < L — because the escape above
> costs |T| per modulus (N_{I∖T}(D) ≥ ⌊m/D⌋ − |T|), which is worthless once |T| ≫ ⌊m/D⌋, and
> Lemma 1 only gives |T_72| < 0.015 m. This is a real, untouched question; Corollary 9 (|T| = 1)
> makes the exhibited family the *easiest* case for the escape, not the hardest.

Consequently §8's verdict "A2 refuted as a universal strategy" is right only for A2's literal
coefficient-scaling form; and the transcript's own Corollary 9 ("one hot point suffices to break
the LP") should be read as "one hot point suffices to break the *whole-window* LP", which is a
weaker and less alarming statement than the prose suggests.

Secondary, minor: §10 cites `round14_window_lp_obstruction.py` / its output with SHA-256 hashes;
neither file is present, so the hashes are unverifiable. Everything they were meant to certify has
been independently recomputed here, so this does not affect the verdict.

---

## 6. Recommended status tags for the campaign ledger

- **PROVED:** Lemmas 1–5, 7; Theorems 6, 8, 10; Corollary 9.
- **PROVED (refutation):** brief's T1 and T2 as stated; T4 for C = 2 beyond m = 3.26·10¹¹.
  Robust to replacing ⌊m/D⌋ by exact window counts.
- **NOT PROVED / open:** (SC_64) itself (untouched — the family satisfies it with slack 63);
  and whether the hot-set-excluded certificate LP (feasibility on I∖T, counts ⌊m/D⌋ − |T|) also
  fails — this, not "abandon the cone", is the next question.
- **Reproduction:** `ref_r14_indep.py`, `ref_r14_b.py`, `ref_r14_c.py`, `ref_r14_d.py`,
  `ref_r14_e.py` in this scratchpad; all runs < 60 s under
  `venv_milp/bin/python` (sympy 1.14.0, scipy 1.13.1).
