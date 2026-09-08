(A) g ≤ n + β(Γ): **CONFIRMED** — proof is correct; six routine steps are left implicit; strictly stronger than P7/P8 and implies both.
(B) g ≤ 2n − k + β_core, β_core ≤ k ⇒ g ≤ 2n: **CONFIRMED-WITH-REPAIRS** — the inequality is true, but it is *never* stronger than (A) and its corollary is strictly weaker than "β ≤ n ⇒ g ≤ 2n", which the document itself derives from (A). The framing "More precisely, …(2)" is backwards and must be repaired.
(C) Sharpness g((77,91,143),5934) = 4 = n + β: **CONFIRMED** — recomputed exhaustively. The unanswered question is now answered: g = n + β is attained for arbitrarily large n, and even with β = Θ(n) (new K_{2,t} family, exact DP for n = 4,6,8,10,12; g/n → 3/2).
(D) Shortage lemmas δ_p, ρ_p, ρ_p ≤ δ_p, g ≤ |S| + Σ_p ρ_p(S): **CONFIRMED-WITH-REPAIRS** — all four statements are true and the exchange argument is valid, but the *exactness* claims are stated without the feasibility bounds δ_p(S) ≤ |I∖S| and Σ_j N_p(j) ≥ D_p that they need.

---

# Referee report — `pro_708_r22/proof.md` (Erdős–Surányi, Erdős problem 708)

**Referee:** blind adversarial re-derivation. Nothing in `exact_verifier.py` or
`verifier_output.txt` was relied on. All arithmetic, all graph invariants and all
exact optima below were recomputed from scratch by
`/Users/roychen/workspace/claudecode/automath/engine/out/pro_708_r22/referee_checks.py`
(independent 0/1 element-by-element DP over capped valuation vectors, plus
brute-force subset enumeration wherever feasible, plus an independent
union-find/Kuhn computation of β, c, s, W_s, ν). Every displayed number in this
report is my own.

**Novelty baselines used:** `engine/harvest/astra_708_2n.md` (P1–P11, F1–F3) and
`papers/erdos708/{main.tex, sec_chain19.tex, sec_h97.tex, sec_h883.tex,
sec_remains.tex, sec_signed.tex, sec_h17.tex}`. I could not consult the external
literature (offline); the novelty verdicts below are **relative to these two
corpora only** and a literature check is still required before any publication.

---

## 0. Summary of what is and is not established

| Claim in the document | My verdict |
|---|---|
| (1) g(A,x) ≤ n + β(Γ), uniformly | **True and correctly proved.** Genuinely new w.r.t. both baselines. Strictly stronger than P7 and P8. |
| (2) g ≤ 2n − k + β_core | **True but vacuous as an improvement** — it is implied by (1) for *every* instance, never the reverse. |
| (3) β_core ≤ k ⇒ g ≤ 2n | **True, but strictly weaker** than the immediate corollary β ≤ n ⇒ g ≤ 2n of (1). |
| (4) a_n ≥ 8n³ ⇒ g ≤ 2n | **True, NOT NEW** — published Theorem 1.3 of `main.tex`. |
| (5) a_n ≥ 9n² ⇒ g ≤ 3n | **True, NOT NEW** — published Theorem 1.4 (k-split) at k = 3, *verbatim*. |
| Lemma 7 (multiplicative bin packing) | **True, NOT NEW** — hypothesis is identical to published Lemma 6.1. |
| Sharpness n = 3, β = 1, g = 4 | **True**, but the instance is a relabelling of astra F2's {323,391,437}. The *use* (sharpness of the β coefficient) is new. |
| Uniform 2n / 3n / 2n+o(n) | Correctly reported **OPEN**. No hidden claim. |
| "11n / 12n / hinge not used" | **Verified.** The only arithmetic input anywhere is Lemma 1. |
| "No prefix-to-window injection" | **Verified.** See §A.2. |

**Nothing in the document is false.** The mathematical defects are (i) one
result presented as a refinement when it is a weakening, and (ii) two results
(plus their engine lemma) that duplicate the group's own published paper without
attribution.

---

## (A) Theorem 4: g(A,x) ≤ n + β(Γ) — CONFIRMED

### A.1 The proof, step by step

I re-derived the whole chain. It is correct. Restating it in the form a paper
would need:

1. **Anchors exist (Lemma 1).** For every a ∈ A, a ≤ m, so
   #{b ∈ I : a | b} = ⌊(x+m)/a⌋ − ⌊x/a⌋ ≥ ⌊m/a⌋ ≥ 1. Choose *any*
   b(a) ∈ I with a | b(a). Set S = {b(a) : a ∈ A} (a **set**, so |S| = number of
   distinct anchors).
2. **Collision groups.** C_b = {a : b(a) = b}, b ∈ S. These partition A into |S|
   nonempty classes; the map C ↦ b_C is a bijection onto S.
3. **Layer shortage of the anchor set.** With r_{C,p}(j) = #{a ∈ C : p^j | a}:
   if r_{C,p}(j) > 0 then p^j | b_C, so
   s_p(j) ≥ #{C : r_{C,p}(j) > 0} *because the anchors of distinct groups are
   distinct*. Hence c_p(j) − s_p(j) ≤ Σ_C (r_{C,p}(j) − 1)^+ ≤ Σ_C (r_{C,p}(1) − 1)^+,
   using monotonicity of r in j. Taking max over j,
   δ_p(S) ≤ Σ_C (r_{C,p}(1) − 1)^+.
4. **Summation is an equality, not just an inequality:**
   Σ_{p ∈ P(A)} Σ_C (r_{C,p}(1) − 1)^+ = Σ_C ( Σ_{a∈C} ω(a) − |P(C)| ).
5. **Euler identity (14).** H_C has |C| + |P(C)| vertices, Σ_{a∈C} ω(a) edges,
   c_C components, so Σ_{a∈C} ω(a) − |P(C)| = |C| − c_C + β_C.
6. **Lemma 3.** Identify prime vertices across the disjoint H_C's to rebuild H:
   each identification drops V by 1, keeps E, and drops c by 1 (β unchanged) or
   keeps c (β up by 1). Hence Σ_C β_C ≤ β(H).
7. **Private leaves.** β(H) = β(Γ) and c(H) = c(Γ), because each private prime is
   a pendant vertex: +1 vertex, +1 edge, same component count, so
   β = E − V + c is unchanged.
8. Combine: |S| + Σ_p δ_p(S) ≤ Σ_C (1 + |C| − c_C + β_C) ≤ Σ_C (|C| + β_C)
   = n + Σ_C β_C ≤ n + β. Lemma 2 converts the certificate into a cover.

**Every one of these steps checks out.** I verified step 8 numerically for *every*
document instance under three anchor rules (smallest multiple, largest multiple,
random), confirming the document's stronger assertion that **arbitrary**
whole-input anchors work — see §17 of my log: the chain
`cert ≤ n + Σ_C β_C ≤ n + β` held in all 105 anchor configurations tested.

### A.2 The Hensley–Richards trap: correctly avoided

The only arithmetic input is the two-sided count in Lemma 1. There is **no**
injection from a prefix {1,…,m} (or from any subset of it) into the shifted
window, and none is needed: collisions between anchors are not forbidden, they
are *charged* — to the cycle rank of the collision group. This is exactly the
right move, and it is what distinguishes Theorem 4 from the refuted
prefix-transport arguments (`main.tex` Prop 8.7(a), astra P1/P7 disclaimers). The
document's own "sifted-surplus" table is decorative but honest; I reproduced its
numbers exactly: R_{2,3,5,7}([1,105]) = 24 versus 26 at x = 8, and
R_{2,3,5,7,11}([1,165]) = 34 versus 37 at x = 16 — i.e. shifted windows really do
carry more survivors than the prefix, which is precisely why no such injection can
exist.

### A.3 No hypotheses needed — confirmed

The proof uses **no** bound on a_n, **no** primitivity, **no** antichain
condition, **no** squarefreeness, and **no** LP/duality/rounding. I stress-tested
this: my random suite includes non-primitive sets (e.g. A = (75,132), gcd = 3),
non-squarefree sets with repeated prime powers (A = (52,98,121,169),
A = (49,198)), and divisibility chains. 83 random (A,x) pairs, zero violations of
g ≤ n + β.

### A.4 The identity n + β = Ω₀(A) − |P(A)| + c — CONFIRMED

Immediate from β(H) = Ω₀ − (n + |P|) + c and β(H) = β(Γ). Verified numerically on
every instance (my script asserts it). The "private leaves change nothing"
claim is likewise verified for both invariants on every instance.

### A.5 Comparison with P7 and P8 — (A) is strictly stronger and implies both

Since n + β = W_s − s + c, we need ν ≤ n + s − c. **The document asserts this
without proof** (its P7 audit just writes "n + s − ν − c ≥ 0"). The missing step:
a matching is an acyclic edge set, and any acyclic subgraph of Γ has at most
(n + s) − c edges. With that,

* P7: n + W_s − ν − (n + β) = n + s − ν − c ≥ 0 ✔
* P8: 2n − c + β + d − (n + β) = n + s − ν − c ≥ 0 ✔ (d = s − ν)

so **(A) ⇒ P7 and (A) ⇒ P8**, and in particular ⇒ "pseudoforest ⇒ g ≤ 2n"
(β ≤ c ≤ n) and ⇒ "g ≤ 2n + 2β". Verified numerically on all 21 instances. The
improvement is real and often large: on astra's F1 instance (the ten triple
products of {53,59,61,67,71}, n = 10) P7 and P8 both give **35** whereas Theorem 4
gives **26**. Note this equals F1's own certificate value 1 + 5·5 = 26 — so
Theorem 4 is a *sharp* description of the whole-input-anchor route, and it does
**not** contradict F1: that route still exceeds 2n = 20 on that instance. Good.

### A.6 Steps a paper must write out (none is an error; all are one-liners)

1. δ_p(S) ≤ |I∖S|, so the greedy repair set actually exists (see (D)).
2. Feasibility of the minimum defining ρ_p: Σ_j N_p(j) ≥ Σ_j c_p(j) = D_p.
3. Injectivity of C ↦ b_C, used silently in step 3 above.
4. β(H) = β(Γ) and c(H) = c(Γ) via the pendant-vertex argument.
5. ν ≤ n + s − c, needed for the P7/P8 comparison (§A.5).
6. In (17), the summation range p ∈ P(A) and the fact that the inequality is an
   identity on p ∈ P(C).
7. In the *second* (constructive) proof: that the component-by-component ordering
   exists; that q(root) = 0 because distinct components of Γ share no prime at
   all (a shared prime would put them in one component); and Σ_a q(a) =
   Ω₀ − |P(A)|. I checked the constructive proof separately — it is also
   correct, including the "δ_p ≤ 1 for old primes, 0 for new primes" step.

**Verdict (A): CONFIRMED.**

---

## (B) Lemma 5 and the corollary β_core ≤ k ⇒ g ≤ 2n — CONFIRMED-WITH-REPAIRS

### B.1 The reduction to A_core is sound, and it is astra's P9

Inequality (18), g ≤ |C| + β(Γ_C) + Σ_{a∉C} ω(a), is correct. The engine is
δ_{A,p}(S_C) ≤ δ_{C,p}(S_C) + c_{A∖C,p}(1) (from (u+v)^+ ≤ u^+ + v and
c_{A∖C,p}(j) ≤ c_{A∖C,p}(1)), then Σ_p c_{A∖C,p}(1) = Σ_{a∉C} ω(a). This is
**exactly the proof of P9** in `astra_708_2n.md` lines 244–249, with the P7 core
|C| + W_s(C) − ν(C) replaced by the stronger Theorem-4 core |C| + β(Γ_C). So (18)
is a legitimate strengthening of P9, and it matches P9 in structure: discarded
inputs are charged their full ω(a); the deletion is *not* free. Sound.

### B.2 The fatal structural point: (2) is never stronger than (1)

Add the non-core inputs to the core incidence graph one at a time. Adding an
input a contributes 1 vertex, ω(a) edges and t ≤ ω(a) new prime vertices, so
Δβ = ω(a) − 1 − t + Δc ≤ ω(a) − 1. Since ω(a) ≤ 2 off the core,

    β ≤ β_core + Σ_{a ∉ A_core} (ω(a) − 1) ≤ β_core + (n − k),

hence

    **n + β ≤ 2n − k + β_core  for every instance.**

I verified this on 4 000 random instances (max slack observed: 7; minimum: 0) and
on every instance in the document. Consequently:

* Bound (2) is **never** better than bound (1), and is strictly worse whenever any
  non-core input fails to close a new cycle.
* Condition (3), β_core ≤ k, **implies** β ≤ n, so (3) is a strict special case of
  the corollary "β ≤ n ⇒ g ≤ 2n" that the document itself states three lines
  later in the same "Consequences" block.
* Concrete witness (my own): A = (143, 210, 323, 420), x = 0. Here n = 4, β = 3,
  c = 3, k = 2, β_core = 3. Condition (3) **fails** (3 ≰ 2); Lemma 5's bound (19)
  gives **9, worse than 2n = 8**; Theorem 4 gives **7 < 8** outright. Exact
  g = 4.

So the abstract's "More precisely, … (2)" is **backwards**. Repair: state (18)
for general C, note C = A recovers (1), note (1) ⇒ (2), and replace the headline
condition (3) by **β ≤ n**, equivalently Σ_a(ω(a) − 2) ≤ |P(A)| − c.

### B.3 How much weaker is β_core ≤ k than the pseudoforest condition β ≤ c?

**Implication (mine, the document does not state it):** under a pseudoforest each
component carries at most one independent cycle, each cycle inside the core needs
≥ 2 core inputs, and distinct core cycles lie in distinct components; hence
β_core ≤ k/2 ≤ k. So **the new condition is implied by the old one**, and is
strictly weaker.

**Families satisfying the new but not the old condition** (verified):

| A | n | β | c | k | β_core | pseudoforest | β_core ≤ k |
|---|---|---|---|---|---|---|---|
| (30, 42, 70, 165, 273) = D7 | 5 | 5 | 1 | 5 | 5 | no | **yes** |
| (30, 42, 110, 231) | 4 | 4 | 1 | 4 | 4 | no | **yes** |
| (30, 70, 105) = R4 | 3 | 3 | 1 | 3 | 3 | no | **yes** |
| K_{2,t} family of §C.3 (all ω = 2) | 2t | t−1 | 1 | 0 | 0 | no (t ≥ 3) | **yes** |

So the enlargement is genuine. **But quantitatively it is small where it
matters.** Rewriting the conditions exactly:

    pseudoforest β ≤ c        ⇔  Σ_a (ω(a) − 1)        ≤ |P(A)|
    Theorem 4    β ≤ n        ⇔  Σ_a (ω(a) − 2)        ≤ |P(A)| − c
    Lemma 5      β_core ≤ k   ⇔  Σ_{core} (ω(a) − 2)   ≤ |P(core)| − c_core

For all-ω = 3 inputs the last two both read **|P(A)| ≥ n + c**: *there must be
more distinct primes than inputs.* Measured (n inputs, each a product of 3 primes
drawn from the first s primes, 1 500 samples per cell):

| n | s/n = 0.8 | 1.0 | 1.2 | 1.6 | 2.5 |
|---|---|---|---|---|---|
| 6 | 0 % | 0 % | 82 % | 99 % | 100 % |
| 10 | 0 % | 0 % | 89 % | 100 % | 100 % |
| 20 | 0 % | 0 % | 95 % | 100 % | 100 % |
| (pseudoforest, n = 20) | 0 % | 0 % | 0 % | 0 % | 4 % |

There is a sharp threshold at s ≈ n. So the honest statement is: **β_core ≤ k is
a sparsity hypothesis, satisfied by "most" instances only in models where the
prime support already outnumbers the inputs**, and it is not satisfied
"generically" in any sense relevant to the conjecture. Evidence:

* **7 of the document's own 8 adversarial instances D0–D6 fail it** (only D7
  passes). Every one of them has β_core = β > k.
* The known obstruction family (astra F3: n = C(ℓ,3) triple products of ℓ primes,
  β/n → 2) has |P| = ℓ ≈ (6n)^{1/3} ≪ n, so it fails the condition by a factor
  ~n^{2/3}. That family is the whole reason T1 is open.

**Verdict (B): CONFIRMED-WITH-REPAIRS** (statement true; presentation and choice
of headline condition must be repaired).

---

## (C) Sharpness — CONFIRMED, and the open question is now answered

### C.1 Recomputation of the document's witness

A = (77, 91, 143), x = 5934, I = {5935,…,6077}. My independent computation:

* β = 1, c = 1, s = 3, W_s = 6, ν = 3 — confirms the document.
* Elements of I divisible by ≥ 2 of {7,11,13}: **exactly {6006}** — confirms.
* Multiples of p² in I: 49 → {5978, 6027, 6076}; 121 → {6050}; **169 → ∅** —
  confirms the key step of Lemma 6 (the document only exhibits 5978 and 6050 but
  its argument needs only the emptiness at 169, which is correct).
* **Exhaustive** enumeration of all 3-subsets of the 43 elements of I divisible by
  7, 11 or 13: **zero covers**. So g ≥ 4 independently of any DP.
* g = 4 by DP, with my own witness (5936, 5940, 5941, 6006); the document's
  witness (5941, 5954, 5978, 6050) is also valid (I checked the divisibility).

So **g = 4 = n + β. CONFIRMED.** The document's derived claim that
g ≤ n + θβ with θ < 1 is refuted is correct.

The instance is, however, the {7,11,13} relabelling of astra F2's
A = {323, 391, 437} = {17·19, 17·23, 19·23}, x = 74072, which already had g = 4
and n = 3. New use, old instance.

### C.2 Arbitrarily large n with β = 1 — CONSTRUCTED AND VERIFIED

**Construction.** Take primes q_1 < … < q_r all within a factor √2 (precisely:
2q_1q_2 > q_{r−1}q_r), let A = {q_i q_{i+1} : i mod r} (a cycle), so n = r, s = r,
W_s = 2r, c = 1, **β = 1**, m = q_{r−1}q_r. Put M = q_1⋯q_r and place the window
of length m around M so that (i) every pair product q_iq_j exceeds both α and
m−1−α, where M = x+α+1 — then M is the *only* element of I divisible by two
demanded primes — and (ii) some q_i has no multiple of q_i² in I. Then

* using M: 1 unit at every prime, then 1 further element per prime → r + 1;
* not using M: 2 units needed per prime, ≥ 2 elements for the square-free prime →
  ≥ r + 1;

so **g = r + 1 = n + β**. Verified by exact DP for r = 3,…,9:

| r = n | q's | m | β | n+β | **exact g** |
|---|---|---|---|---|---|
| 3 | 11,13,17 | 221 | 1 | 4 | **4** |
| 4 | 13,17,19,23 | 437 | 1 | 5 | **5** |
| 5 | 37,…,53 | 2491 | 1 | 6 | **6** |
| 6 | 67,…,89 | 7387 | 1 | 7 | **7** |
| 7 | 127,…,157 | 23707 | 1 | 8 | **8** |
| 8 | 89,…,127 | 14351 | 1 | 9 | **9** |
| 9 | 103,…,149 | 20711 | 1 | 10 | **10** |

**The sharpness is not an artefact of tiny n.**

### C.3 Sharpness with β = Θ(n) — the K_{2,t} family (new)

The document leaves open whether the *coefficient* of β survives large β. It
does.

**Construction.** Take primes w_1 < … < w_t < q_u < q_v, all within a factor √2,
with **q_u² > m and q_v² > m** where m = w_t q_v (achievable whenever
q_u² > w_t q_v, e.g. 89 < 97 < 101 with 97² = 9409 > 89·101 = 8989). Put

    A = { w_i q_u , w_i q_v : i = 1,…,t }   (the edge set of K_{2,t}),

so n = 2t, s = t + 2, W_s = 4t, c = 1, **β = t − 1**. Place the window around
M = w_1⋯w_t q_u q_v so that M is the unique element of I divisible by two demanded
primes and **neither q_u² nor q_v² has a multiple in I**. Then

* with M: 1 + (t−1) + (t−1) + t = **3t − 1**  (q_u and q_v each still need t−1
  single units, w_i one each);
* without M: t + t + (≥ t) = **≥ 3t**;

so **g = 3t − 1 = n + β with β = n/2 − 1 = Θ(n)**. Verified by exact DP:

| t | n | β | n+β | **exact g** | g/n |
|---|---|---|---|---|---|
| 2 | 4 | 1 | 5 | **5** | 1.250 |
| 3 | 6 | 2 | 8 | **8** | 1.333 |
| 4 | 8 | 3 | 11 | **11** | 1.375 |
| 5 | 10 | 4 | 14 | **14** | 1.400 |
| 6 | 12 | 5 | 17 | **17** | 1.417 |

(e.g. t = 5: primes 67,73,79,83,89,97,101, A = (6499, 6767, 7081, 7373, 7663,
7979, 8051, 8383, 8633, 8989), x = 27963141550437, g = 14.)

Consequences the document should state:

* g ≤ n + θβ + C is **refuted for every θ < 1 and every constant C**, not merely
  for θ < 1 at one instance.
* g/n reaches **3/2 − 1/n** on a family where g = n + β exactly. This also beats
  the campaign's own recorded maxima: astra's best exact ratio was 4/3, and its
  best value at n = 10 was 12; here n = 10 gives **g = 14**, and n = 12 gives 17.
* All ω(a) = 2 in this family, so k = 0, β_core = 0 and Lemma 5's condition (3)
  holds trivially, giving only g ≤ 2n = 4t — while Theorem 4 gives the exact
  value. Another demonstration that (1) dominates (2).

### C.4 How far can exact sharpness go? (structural ceiling — mine)

Inside the "unique-M prime-pair" family (A = {q_iq_j : ij ∈ E(G)}, primes within
√2, window at M = ∏q_i) one gets exactly

    g = 1 + Σ_i max( ⌈(d_i−1)/2⌉ , d_i − 1 − t_i ),   n + β = Σ_i d_i − r + c,

with d_i = deg_G(q_i) and t_i = #{multiples of q_i² in I}. Equality forces c = 1
and t_i = 0 for every prime of degree ≥ 3; t_i = 0 requires q_i² > m = max_{ij∈E}
q_iq_j, i.e. q_i exceeds all of its neighbours. Hence the degree-≥3 primes form an
independent set B all of whose neighbours have degree ≤ 2, so n = |E| ≤ 2(r−|B|)
and β = n − r + 1 ≤ n/2 − |B| + 1, maximised at |B| = 2 — i.e. **K_{2,t} is
optimal inside this family and β ≤ n/2 − 1 is the ceiling there**.

Exact sharpness with β/n → 1 would force g = 2n, i.e. an extremal instance for
Erdős's conjecture; none is known. On the classical (2−o(1))n family (all C(r,2)
pair products) I get g = n + β − O(√n): r = 4 gives n = 6, β = 3, n+β = 9,
**g = 6**; r = 5 gives n = 10, β = 6, n+β = 16, **g = 12** (this reproduces
astra's "maximum n = 10 value found is 12"). So Theorem 4 is asymptotically tight
*in ratio* on the extremal family and *exactly* tight on K_{2,t}.

**Verdict (C): CONFIRMED, and extended.**

---

## (D) The shortage lemmas — CONFIRMED-WITH-REPAIRS

### D.1 δ_p(S) = max_j (c_p(j) − s_p(j))^+ is the exact nested-layer shortage

Correct, given two facts the document uses without stating:

* **N_p(j) ≥ c_p(j)** (Lemma 1) — used, and stated.
* **δ_p(S) ≤ |I∖S|**, so that δ_p(S) additions actually exist. *Not stated.*
  Proof: if the max is attained at j₀ then
  δ_p = c_p(j₀) − s_p(j₀) ≤ N_p(j₀) − s_p(j₀) = #{b ∈ I∖S : p^{j₀}|b} ≤ |I∖S|.
  **This is a required repair**: the sentence "Order the elements of I∖S … if the
  first t are selected" is meaningless without it.

Verified by brute force: for 360 (instance, S, p) triples with S random subsets of
I, my exhaustive minimum-repair search agreed with δ_p in every case where the
search was feasible (δ_p ≤ 3).

### D.2 The exchange/greedy argument — VALID

The claim "the t largest-valuation additions simultaneously maximise every nested
layer" is correct and the reason should be stated: after sorting I∖S by
non-increasing v_p, the set {b : v_p(b) ≥ j} is a **prefix** for every j
simultaneously, so among the top t the count with p^j | b equals
min(t, N_p(j) − s_p(j)), which is the pointwise maximum over all t-subsets.
Summing over j then maximises the total valuation, giving (12) and hence (9).
Nothing hidden; but it is a two-line argument the document compresses to one
assertion.

### D.3 ρ_p(S) is the exact total-valuation shortage — CONFIRMED, with a repair

Correct. **Repair needed:** the minimum in (9) is taken over
t ∈ {0,…,|I∖S|} and the document never checks the set is nonempty. It is:
Σ_j N_p(j) = Σ_{b∈I} v_p(b) ≥ Σ_j c_p(j) = D_p by Lemma 1. State it.

Verified by brute force against an exhaustive minimum-additions search on the same
360 triples: zero disagreements.

### D.4 ρ_p ≤ δ_p — CONFIRMED

With t = δ_p, min(N_p(j), s_p(j)+t) ≥ c_p(j) for every j (needs both N_p(j) ≥
c_p(j) and s_p(j)+t ≥ c_p(j)); summing gives ≥ D_p. Zero violations in 360 tests.

### D.5 g ≤ |S| + Σ_p ρ_p(S): summation across primes is SOUND but LOSSY

The independent-summation question the referee brief raises: **there is no double
counting error**, because the argument is a union bound, not an additivity claim.
Take a minimal repair set R_p ⊆ I∖S for each p and put T = S ∪ ⋃_p R_p. For every
p, T ⊇ S ∪ R_p and adding positive integers never decreases v_p, so v_p(∏T) ≥ D_p;
and |T| ≤ |S| + Σ_p ρ_p. Overlaps only help. Zero violations in my tests.

The price is that the bound is far from tight, exactly as the document's own D5
example shows and as I confirm: A = (105,120,126,140,150,168,180), x = 12510. All
seven inputs have the *single* interval multiple 12600 (I verified this: the
multiple lists are all [12600]), forcing S = {12600}. Then

* δ = (δ_2, δ_3, δ_5, δ_7) = (5, 5, 4, 3), giving |S| + Σδ = **18**;
* ρ = (ρ_2, ρ_3, ρ_5, ρ_7) = (2, 2, 2, 2), giving |S| + Σρ = **9**;
* **exact g = 5.**

All three numbers confirmed independently. So the document's §5 conclusion — that
high prime degree does not by itself reduce the *nested* shortage, while actual
valuations do save a lot — is correct, and its "uniform amortisation is OPEN"
label is honest.

**Verdict (D): CONFIRMED-WITH-REPAIRS** (two feasibility statements must be
supplied; the exchange argument and the union bound are valid).

---

## Exact values — my own computation (independent DP + brute force)

Every row recomputed from scratch. `g` column is my value; all agree with the
document. `brute` is an independent exhaustive subset enumeration where feasible.

| id | A | x | n | s | W_s | ν | c | **β** | claim β | **g** | claim g | n+β | 2n−k+β_core | brute |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| D0 | (30,42,70,105) | 0 | 4 | 4 | 12 | 4 | 1 | **5** | 5 | **4** | 4 | 9 | 9 | 4 |
| D1 | (30,42,70,105) | 113 | 4 | 4 | 12 | 4 | 1 | **5** | 5 | **4** | 4 | 9 | 9 | 4 |
| D2 | (30,42,66,70,105,165) | 151 | 6 | 5 | 18 | 5 | 1 | **8** | 8 | **5** | 5 | 14 | 14 | – |
| D3 | (30,42,66,70,78,105,110,165) | 997 | 8 | 5 | 23 | 5 | 1 | **11** | 11 | **5** | 5 | 19 | 19 | – |
| D4 | (30,42,66,70,105,110,154,165,231,385) | 1009 | 10 | 5 | 30 | 5 | 1 | **16** | 16 | **7** | 7 | 26 | 26 | – |
| D5 | (105,120,126,140,150,168,180) | 12510 | 7 | 4 | 21 | 4 | 1 | **11** | 11 | **5** | 5 | 18 | 18 | – |
| D6 | (330,420,462,630,770,1155) | 13282 | 6 | 5 | 24 | 5 | 1 | **14** | 14 | **4** | 4 | 20 | 20 | 4 |
| D7 | (30,42,70,165,273) | 29900 | 5 | 4 | 13 | 4 | 1 | **5** | 5 | **3** | 3 | 10 | 10 | 3 |
| D8 | (30,42,70,105) | 1207 | 4 | 4 | 12 | 4 | 1 | **5** | 5 | **3** | 3 | 9 | 9 | 3 |
| **T** | (77,91,143) | 5934 | 3 | 3 | 6 | 3 | 1 | **1** | 1 | **4** | 4 | **4** | 6 | 4 |
| H0 | (30,42,70,105) | 8 | 4 | 4 | 12 | 4 | 1 | 5 | – | **4** | 4 | 9 | 9 | 4 |
| H1 | (30,42,66,70,105,165) | 16 | 6 | 5 | 18 | 5 | 1 | 8 | – | **5** | 5 | 14 | 14 | – |
| F | (6,10,21) | 53 | 3 | 2 | 4 | 2 | 1 | 0 | – | **2** | 2 | 3 | 6 | 2 |
| U0 | (6,10,15) | 53 | 3 | 3 | 6 | 3 | 1 | 1 | – | **3** | 3 | 4 | 6 | 3 |
| U1 | (154,273,715) | 29672 | 3 | 3 | 6 | 3 | 1 | 1 | – | **3** | 3 | 4 | 4 | 3 |
| U2 | (154,273,715) | 0 | 3 | 3 | 6 | 3 | 1 | 1 | – | **3** | 3 | 4 | 4 | 3 |
| R0–R3 | (6,10,15),(6,14,21),(15,21,35),(35,55,77) | 0 | 3 | 3 | 6 | 3 | 1 | 1 | – | **3** | 3 | 4 | 6 | 3 |
| R4 | (30,70,105) | 0 | 3 | 4 | 9 | 3 | 1 | 3 | – | **3** | 3 | 6 | 6 | 3 |

**All nine D-instances, the maximum-ratio instance T, and all eleven auxiliary
instances are CONFIRMED, and every claimed cycle rank is CONFIRMED.** The
claimed structural properties of D0–D7 (primitive, divisibility antichain, all
ω ≥ 3, 2n < m < 8n³) are also confirmed for each. The maximum ratio 4/3 over the
document's own retained set is correct *as scoped*; §C.3 gives instances with
larger ratio outside that set.

Other numerics confirmed: Proposition 9's min_{C⊆A5} Θ_A(C) = **20** > 18 = 3n,
attained at C = (330,420) (and also at C = A, since Θ_A(C) = Ω₀ − |P(C)| + c_C =
24 − |P(C)| + c_C with |P(C)| ≤ 5); the sifted-window table; the "8 931 DP
evaluations" arithmetic (31 + 900 + 4·2000); and the Theorem 8 threshold algebra
(h = 2 ⇒ 8n³, h = 3 ⇒ 9n², both instances of m ≥ (hn)^{(h+1)/(h−1)}).

I also independently checked the document's own `exact_verifier.py`: the embedded
listing in §8 is byte-identical to the file, and its grouped-DP cap rule
`min(|group|, max_p ⌈D_p/v_p⌉)` is sound. But nothing above depends on it.

---

## Novelty assessment, result by result

Relative to `astra_708_2n.md` and `papers/erdos708/*.tex` **only**.

| # | Result | New? | Worth publishing? |
|---|---|---|---|
| Lemma 1 | ⌊m/d⌋ sandwich | **No** — published `main.tex` Lemma 2.1, and astra P1's counting step | No |
| Lemma 2, δ_p part | δ_p(S) = max_j(c_p(j)−s_p(j))^+, g ≤ |S|+Σδ_p | **No** — astra **P1** verbatim | No |
| Lemma 2, ρ_p part | total-valuation shortage, ρ_p ≤ δ_p, g ≤ \|S\|+Σρ_p | **Yes** (astra explicitly declines to exploit total valuations) | Only as a lemma inside a larger result; on its own it is a routine greedy exchange |
| Lemma 3 | Σ_i β(H_i) ≤ β(H) under input-disjoint partition | New to these corpora, but **textbook** graph theory (vertex identification never decreases cycle rank) | No, as a stated lemma; keep as a proof step |
| **Theorem 4** | **g ≤ n + β(Γ)** | **Yes** — absent from both corpora; the paper contains *no graph theory at all* | **Yes** — as a section/appendix of the existing paper, not a standalone note. It subsumes P7, P8, "pseudoforest ⇒ 2n", and adds "β = 0 ⇒ g ≤ n". Publish together with the sharpness families of §C. Literature check still required. |
| Theorem 4, 2nd proof | adaptive constructive version | Yes (new) | As a remark/algorithm only |
| Lemma 5 (18) | g ≤ \|C\|+β(Γ_C)+Σ_{a∉C}ω(a) | Partly — it is astra **P9** with the P7 core upgraded to the Theorem-4 core | As a corollary of Theorem 4, one line |
| (2)/(3) | g ≤ 2n−k+β_core; β_core ≤ k ⇒ 2n | Formula is new, **but implied by (1)** | **No** — replace by β ≤ n ⇔ Σ_a(ω(a)−2) ≤ \|P(A)\|−c |
| Lemma 6 | sharpness at (77,91,143), x = 5934 | Instance is astra **F2**'s {323,391,437} relabelled; the *sharpness use* is new | Yes, but cite F2 and replace by the stronger §C.3 family |
| **Lemma 7** | multiplicative bin packing, ∏q_i ≤ T^{(h+1)/2} ⇒ ≤ h groups of product ≤ T | **No** — this is *exactly* published **Lemma 6.1** (A²H^{k+1} ≤ m^{k+1} ⇔ A ≤ T^{(k+1)/2} with T = m/H); published Lemma 5.1 is the h = 2 case | No. (The proof given — minimal partition + pairwise products — is a nice alternative to the published induction+greedy proof; worth at most a remark.) |
| **Theorem 8** | m ≥ 8n³ ⇒ 2n; m ≥ 9n² ⇒ 3n | **No.** m ≥ 8n³ ⇒ 2n is published **Theorem 1.3**. m ≥ 9n² ⇒ 3n is published **Theorem 1.4** (k-split) at k = 3, stated verbatim in `main.tex:135–136` and again in its proof at `main.tex:477`. Both are the same one-parameter family m ≥ (kn)^{(k+1)/(k−1)} | **No — must be attributed, not listed as a result.** astra_708_2n.md itself says "The inherited k-split theorem proves 3n when m ≥ 9n²", so this information was inside the run's own accepted background |
| Proposition 9 | min_C Θ_{A5}(C) = 20 > 3n | The phenomenon is astra **F3**'s second obstruction (which proves it for an infinite family and even gives the n = 4 instance {30,42,70,105} with min = 10 > 8); this is the same statement for the stronger certificate | No — a remark |
| §5 D5 observation | high degree does not reduce the nested shortage | New, minor | No |
| (26) | g(n) ≤ min{max(2n,(n−1)r(8n³)+1), …} | Uses astra P2 (not new) + Theorem 8 (not new); the document itself says it is worse than 11n | **No** |
| Lemma 10 | correctness of the DP | Routine | No |
| §4 audits of P1, P2, P5/P6, P7, P8, P9, P11 | re-verification | Not new (P8's deficiency argument is astra's own proof reproduced) | No |

**Confirmation requested by the brief:** yes — "a_n ≥ 9n² ⇒ g ≤ 3n" is **exactly**
the published k-split theorem at k = 3 (`papers/erdos708/main.tex:133–140`,
Theorem 1.4: "*In particular a_n ≥ 9n² gives 3n*"), and its engine Lemma 7 is
exactly the published Lemma 6.1. **Additional duplication found:** "a_n ≥ 8n³ ⇒
g ≤ 2n" is published Theorem 1.3 (the k = 2 case of the same family), and Lemma 1
is published Lemma 2.1, and Lemma 2's δ_p half is astra P1.

---

## Publication recommendation

1. **Publish** Theorem 4 (g ≤ n + β) with (i) the six implicit steps of §A.6
   written out, (ii) the explicit statement that it implies P7 and P8 (including
   the missing ν ≤ n + s − c), (iii) the corollaries β = 0 ⇒ g ≤ n and
   β ≤ n ⇒ g ≤ 2n stated in the equivalent arithmetic form
   Σ_a(ω(a) − 2) ≤ |P(A)| − c, and (iv) the sharpness families of §C.2–C.3
   showing the coefficient of β cannot be reduced even asymptotically. Subject to
   an external literature check.
2. **Do not publish** (2)/(3) as a separate result; demote to a remark noting
   n + β ≤ 2n − k + β_core always.
3. **Do not publish** Theorem 8 or Lemma 7; cite `main.tex` Theorems 1.3/1.4 and
   Lemma 6.1. If the alternative proof of Lemma 7 is kept, label it as an
   alternative proof of a known lemma.
4. **Do not publish** (26); it is weaker than the refereed 11n.
5. Correct the abstract: (2) is not "more precise" than (1).
6. Add attribution for Lemma 1 (= Lemma 2.1), Lemma 2's δ_p half (= P1), Lemma 5
   (= P9 with a stronger core), Lemma 6's instance (= F2), Proposition 9's
   phenomenon (= F3).

---

## What I did *not* verify

* External literature (offline). Theorem 4 could still be known; the cycle-rank /
  incidence-graph framing is natural enough that a check against van Doorn–Li–Tang
  and the surrounding literature is mandatory before publication.
* The claim that the six finite shift scans are exhaustive over their stated
  ranges: I re-ran only 21 individual instances plus ~4 500 random/constructed
  ones, not the 8 931-evaluation scan.
* Lean formalisation of anything here.

**Scripts:** `/Users/roychen/workspace/claudecode/automath/engine/out/pro_708_r22/referee_checks.py`
(run `python3 referee_checks.py --slow`; sections 1–17 correspond to the sections
of this report).
