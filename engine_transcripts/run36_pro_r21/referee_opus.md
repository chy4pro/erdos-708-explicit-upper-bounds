(A) THEOREM 4 — CONFIRMED
(B) LEMMA 2 — CONFIRMED
(C) THEOREM 5 — CONFIRMED
(D) LEMMA 7 — CONFIRMED

---

# Blind adversarial referee report on `pro_708_r21/proof.md`

Referee: Claude Opus 5 agent, 2026-09-08. Target: the four claims (A)–(D) plus a judgement on
the open Lemma 8. All checks below are **my own**, written from the *statements* in `proof.md`
and not from `exact_verifier.py`; they live in `referee_checks.py` in this directory and run in
exact integer/`Fraction` arithmetic (NumPy is used only for exact `int64` window sweeps).
`python3 referee_checks.py` reports **76 passed, 0 failed** (the one initial failure was a
conjecture of *mine*, not a claim of the author's — see §E).
I read `verifier_output.txt` / `verifier_full_output.txt` but relied on nothing in them; where my
independent rebuild and theirs agree I say so explicitly, because that agreement is evidence and
not an assumption.

Headline: **all four claims are true as stated.** The document is unusually honest — it flags its
own failure to reach its targets, flags the pointwise failure of its own certificate, and marks
Lemma 8 OPEN. I found no false statement in (A)–(D) and no overclaim. What I did find is a
uniform stylistic deficit: the proofs are written at "verifier-adjacent" density and omit roughly
a dozen one-line justifications that a journal referee would insist on. None of them is a repair;
all are listed below.

## Method

| section of `referee_checks.py` | what it does |
|---|---|
| `A0` | re-verifies the accepted four-prime base (Lemma 1) and the convexity increments β_{a,b} ≥ 0 |
| `A1` | the layer identity (5.1) in closed form, on an exact grid, and against a Riemann sum |
| `A2` | `[f(n)>t]` is 0 or a single prime-power divisor indicator, 300 random multilevel primes |
| `A5` | Lemma 3 (4.1)/(4.3) on 1784 (system, c) pairs, all M, all windows; then the (5.2) chain |
| `A4` | full rebuild of the disclosed n = 12705 example, full period D = 25410 |
| `A3` | independent rebuild of the certificate (5.4) + **full** (H₂) sweep (all m ≤ D, all starts) on 14 systems, D up to 508 200 |
| `B1` | exhaustiveness of the nine-row table: **full Q-sweep**, 6 109 259 (quadruple, Q) instances; boundary sweep, 14 240 500 instances; random quadruples to 4000 |
| `B2` | the four b-sub-cases and the row-1 constant, by brute force |
| `C1`–`C3` | the sandwich on fine grids N = 2..7 (56 877 points, twice), the probabilistic identity, the divisor expansion, full (H₂) sweeps |
| `D1`,`D2` | every counting step of Lemma 7, then an **exact rational Farkas certificate** of infeasibility |
| `K` | K₄ audits far beyond the run's own |
| `KW` | wide K₄ scan (opt-in, ~10 min): all 4-subsets of primes < 60, `2 ≤ Q ≤ 400` — 949 620 (P,Q) instances |

---

## (A) Theorem 4 — five primes, at most one multilevel prime. **CONFIRMED**

**Statement checked.** S = T + f with T(n) = Σ_{i≤4} w_i[q_i | n], w_i ∈ [0,1], the q_i powers of
four distinct primes; f(n) = Σ_j α_j[p^j | n], α_j ≥ 0, Σ_j α_j ≤ 1, p a fifth prime. Then (H₂)
holds for every m and every window. The mathematics is correct.

### The layer identity (5.1)

`Δ_a(T,f) = (T+f−a)^+ − (T−a)^+ = ∫_0^1 [f>t][T>a−t] dt` is **exact**, and more robustly so than
the document lets on. The integrand is the indicator of `t ∈ ((a−T)^+ , f)` ∩ [0,1], so the
integral equals `(min(f,1) − (a−T)^+)^+`; splitting on `T ≥ a` versus `T < a` gives `f` and
`(f−(a−T))^+` respectively, which is exactly the hinge difference. Consequences:

* No hypothesis `a ≥ 1` is needed. For `a < 1` the constraint `T > a−t` is vacuous once `t > a`,
  and the identity still holds; likewise for `T + f < a` (both sides are 0) and for `a = 0`
  (both sides equal `f`).
* The *only* hypothesis that matters is **f ∈ [0,1]**, i.e. the per-prime capacity Σ_j α_{p,j} ≤ 1.
  For `f > 1` the identity is false: at `T = 0, f = 2, a = 1` the hinge difference is
  `(0+2−1)^+ − (0−1)^+ = 1` while `∫_0^1[f>t][T>1−t]dt = 0`. `T ≥ 0` is not needed either; any
  real `T` works.
* Verified exactly on a 21 × 7 × 17 rational grid deliberately including `a<1`, `T+f<a`, `T=0`,
  `a=0`, and against a 20 000-point Riemann sum at 400 random rational points.

**Gap (writing):** the identity is asserted, not proved, and its one real hypothesis (f ≤ 1) is not
flagged. Two lines: `(T+f−a)^+−(T−a)^+ = ∫_0^f [T+s>a] ds` and `[s<f] = [f>t]`.

### "For fixed t outside finitely many values, [f(n)>t] is 0 or [d | n]"

Correct, and it uses **exactly** the atom structure: `f(n) = A_{v_p(n)}` where `A_j = Σ_{h≤j} α_h`
is nondecreasing with `A_0 = 0`. Hence `[f(n)>t] = [v_p(n) ≥ j(t)] = [p^{j(t)} | n]` with
`j(t) = min{j : A_j > t}`, and `≡ 0` when the total weight is ≤ t. Since `t > 0 = A_0` we get
`j(t) ≥ 1`, so `d = p^{j(t)} ≥ p ≥ 2` — which the later `⌊m/d⌋` step silently needs.
This is **not** true for an arbitrary multilevel `f`: it is true precisely because a single prime's
contribution is a *cumulative step function of v_p(n)*. Verified on 300 random multilevel primes
(`A2`). **Gap (writing):** the one-line derivation and the `j(t) ≥ 1` remark are missing; the
"outside the finitely many cumulative values" caveat is in fact only needed to make the *cells* of
the finite certificate well defined, not for the slice identity itself.

### T(dk) = T(k), the count (5.2), the reverse inequality, and the window bound

* `T(dk)=T(k)` because `d` is a power of the fifth prime, hence coprime to every `q_i`. Correct.
* `Σ_{k≤m}[d|k][T(k)>2−t] = #{h ≤ ⌊m/d⌋ : T(h) > c+1}` with `c = 1−t ≥ 0`. Correct.
* Lemma 3 with `M = ⌊m/d⌋` gives `≤ ⌊M/Q(t)⌋ = ⌊m/(dQ(t))⌋` (nested-floor identity, unstated).
* `[dQ(t)|n] ≤ [d|n][T(n)>1−t]`: if `dQ | n` then `d | n`, and `Q | n` forces every `q_i` in the
  minimising subset B to divide n, so `T(n) ≥ w_B > 1−t`. Correct.
* `#{b ∈ I : dQ | b} ≥ ⌊m/(dQ)⌋` is the accepted counting fact. Correct.
* Degenerate branch: if no B has `w_B > 1−t`, then in particular `w_{full} ≤ 1−t < 2−t`, so
  **both** integrands vanish; the document asserts this without the reason. Correct.

I verified the whole chain `LHS ≤ ⌊m/(dQ)⌋ ≤ window count` directly on 40 systems and every
`t`-cell (`A5`), and Lemma 3 itself on 1784 (system, c) pairs over all M and all window starts.

### The integration step (5.3)

Fine. For each fixed n the integrand is a step function of t with breakpoints in the finite set
`{A_j} ∪ {1−w_B} ∪ {2−w_B}`; the sums are finite; Tonelli for nonnegative functions applies; and
the pointwise-in-t inequality holds for all but finitely many t, hence a.e. **Gap (writing):** one
sentence of justification is missing (the document says nothing at all about measurability).

### Adding the four-prime inequality

`(S−2)^+ = (T−2)^+ + Δ₂(T,f)` and `(S−1)^+ = (T−1)^+ + Δ₁(T,f)` by definition of Δ; Lemma 1 /
Proposition "four primes" gives `Σ_{k≤m}(T−2)^+ ≤ Σ_{b∈I}(T−1)^+`. Adding (5.3) closes it.
Correct. **Gap (writing):** the decomposition is never displayed, so the reader has to guess that
"adding the four-prime inequality" means adding it to (5.3).

### The explicit certificate (5.4)

I rebuilt (5.4) from the prose, independently of `exact_verifier.py`, and it agrees. Its
correctness proof needs one extra ingredient the document does not name: (5.6) uses **both** (5.1)
*and* the upper half of Lemma 1 (for the pair part). Explicitly
`C = G₄^{pair}(T) + Σ_ℓ(v_ℓ−u_ℓ)[d_ℓQ_ℓ|n] ≤ (T−1)^+ + Δ₁(T,f) = (S−1)^+`.
All coefficients are nonnegative; the layer coefficients are cell lengths and the pair coefficients
are `(w_i+w_j−1)^+/3`.

### The disclosed n = 12705 failure — **reproduced, and the disclosure is honest**

Atoms over denominator 720: (2,257), (3,421), (5,563), (7,611), (11,293), (121,427). Legal system
(prime 11 carries 293+427 = 720/720 = 1 exactly; all others ≤ 1). `12705 = 3·5·7·11²`, not
divisible by 2, so `720·S = 421+563+611+293+427 = 2315` and `2160·(S−2)^+ = 3·(2315−1440) = 2625`.

My rebuild of (5.4) reproduces the published coefficient family **exactly**:

| d | 10 | 14 | 15 | 21 | 35 | 55 | 66 | 110 | 242 | 363 | 605 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 2160·c_d | 100 | 148 | 264 | 312 | 454 | 408 | 345 | 126 | 771 | 492 | 18 |

and the 16 cut numerators `0, 9, 42, 109, 151, 157, 199, 266, 293, 299, 408, 456, 463, 572, 620, 720`.
The divisors of 12705 among these are 15, 21, 35, 55, 363, 605, giving
`2160·C(12705) = 264+312+454+408+492+18 = 1948 < 2625`. **Exact pointwise deficit
C − (S−2)^+ = −677/2160 at n = 12705, and this is the worst deficit over the whole period
D = 25410** — matching the disclosure to the digit. Over the same full period the *usable* bounds
both hold: `C ≤ (S−1)^+` pointwise everywhere, and every prefix sum `Σ_{k≤m}(S−2)^+ ≤ Σ_{k≤m}C(k)`.

**The proof never uses pointwise left domination.** The chain in §5 is
`Σ_{k≤m}(S−2)^+ ≤ Σ_{k≤m}C(k) ≤ Σ_{b∈I}C(b) ≤ Σ_{b∈I}(S−1)^+`, where the first step is a prefix
inequality obtained from `⌊m/D⌋` counts and the third is pointwise. The document states this in
bold and repeats it in the abstract. Honest disclosure, confirmed.

This also matters structurally: because C is *not* a pointwise lower certificate, Lemma 7's
obstruction does not apply to it. The two results are consistent, and the document says so.

### Independent end-to-end verification

Full (H₂) sweeps — every m ≤ D and every window start over the whole period — on 14 systems in the
Theorem 4 class, including the disclosed example (D = 25410), four moduli that are genuine prime
powers (D = 152 460 and D = 508 200), and a case where the *multilevel* prime is 2 (D = 9240). Every
one passes, with the certificate satisfying nonnegativity, the pointwise upper bound and every
prefix lower bound. Worst pointwise deficits found: −677/2160, −8/15, −4/9, −2/9, −1/9, −113/2160.

**Sanity check that the theorem really covers the published barrier.** For five equal half-weights
(atoms 1/2 at 2, 3, 5, 7, 11) my rebuild gives the certificate `C(n) = ½·[66 | n]` — a *single*
divisor term. Then `Σ_{k≤m}(S−2)^+ = ½⌊m/2310⌋ ≤ ½⌊m/66⌋ = Σ_{k≤m}C(k)`, and `66|n ⟹ S(n) ≥ 3/2`
so `C ≤ (S−1)^+`. This is exactly the configuration on which every pair hinge vanishes and which
`sec_remains.tex` cites as the reason the four-prime certificate "does not survive a fifth prime".
Theorem 4 closes it. That is the real content of the result.

### Verdict and gaps for (A)

**CONFIRMED.** Gaps a paper must write out (none is a repair; all are one-liners):
1. Proof of (5.1) and its single hypothesis `f ∈ [0,1]`; note that `a ≥ 1` and `T+f ≥ a` are *not* needed.
2. The derivation `f(n)=A_{v_p(n)} ⟹ [f>t]=[p^{j(t)}|n]`, and `j(t) ≥ 1`.
3. The exact decomposition `(S−a)^+ = (T−a)^+ + Δ_a` for a = 1, 2.
4. In Lemma 3: what "padding with zero-weight coprime moduli" means (adjoin *distinct* primes not
   dividing any q_i) and why it changes neither T nor Q (a zero-weight element only enlarges products).
5. In Lemma 3: `Q ≥ 2` because the minimising subset is nonempty (`w_∅ = 0 ≤ c`), so `Q ≥ min_i q_i ≥ 2`.
6. In Lemma 3: the equivalence `(∀ i ∈ A: ∏A/q_i ≥ Q) ⟺ ∏A/max A ≥ Q`, which is what makes A(k)
   "feasible for the family in Lemma 2".
7. `⌊⌊m/d⌋/Q⌋ = ⌊m/(dQ)⌋`.
8. The reason the degenerate branch ("no such modulus") kills both integrands.
9. One sentence on measurability / Tonelli in (5.3).
10. (5.6) needs the *upper* half of Lemma 1 as well as (5.1).
11. Remark worth adding: the proof never uses that the q_i are prime powers, only that they are
    pairwise coprime and coprime to p; and it stops at five primes because Lemma 2 is false for five
    moduli (2·e₂(1/2,1/3,1/5,1/7,1/11) = 194/165 > 1).

**Worth publishing as stated?** Yes. This is a genuine advance over
`Proposition~\ref{prop:fourprimes}` in `sec_remains.tex`: it closes five arbitrary primes with one
arbitrary prime power each and arbitrary real weights, and it closes the exact five-half-weights
configuration that the published section cites as the obstruction. It also sharpens
`Proposition~\ref{prop:remains}`: the surviving five-prime case now needs **at least two multilevel
primes**. The "after summation, not pointwise" mechanism is itself worth a remark.

---

## (B) Lemma 2 — the four-modulus Boolean antichain bound. **CONFIRMED**

**The nine-row table is genuinely exhaustive.** I enumerated `M_Q` from the definition (not from
the table) and compared against the table's prediction:

* **full Q-sweep** `2 ≤ Q ≤ abc+2` for every pairwise-coprime `2 ≤ a<b<c<d ≤ 30`:
  2534 quadruples, **6 109 259 (quadruple, Q) instances, zero mismatches**;
* boundary sweep (`Q ∈ {2} ∪ {t, t+1 : t ∈ {a,b,c,ab,ac,bc,abc}}` ∪ random) for every
  pairwise-coprime quadruple with `d ≤ 120`: **14 240 500 instances, zero mismatches**;
* 3000 random coprime quadruples with entries up to 4000: zero mismatches.
* All nine rows actually occur.

The derivation is right: singletons are infeasible (`∏A/max A = 1 < 2 ≤ Q`); a pair is feasible iff
its smaller member is ≥ Q; a triple iff the product of its two smaller members is ≥ Q; the quadruple
iff `abc ≥ Q`. **Gap (writing):** the proof does not state the fact it relies on most — feasibility
is *upward closed* (adding any element ≥ 2 to a feasible set keeps it feasible), so every feasible
set contains a minimal one and `M_Q` is an antichain. I verified upward-closedness exhaustively.
Also unstated: the ordering `ab < ac < bc < abc` needed for rows 5–8 to partition `Q > c`, whose last
inequality uses `a ≥ 2`.

**Every numerical bound checks out.** Rows 2–8 give `1/c+2/d`, `1/c+2/d`, `1/d`, `1/c+3/d`, `2/d`,
`1/d`, `1/d`; with `c ≥ 5` (forced by pairwise coprimality — 4 cannot be the third member) and
`d > c`, all are `≤ 4/c ≤ 4/5 < 1`.

**Row 1: `Q·e₂ ≤ a·e₂(1/a,1/b,1/c,1/d) ≤ 1`, four sub-cases.** The case hypotheses `b = 3, 4, 5, ≥ 6`
**are exhaustive**, because `b > a ≥ 2` forces `b ≥ 3`. My exact values:

| case | forced | bound | my exact value |
|---|---|---|---|
| b = 3 | a = 2, c ≥ 5, d ≥ 7 | 2·e₂(1/2,1/3,1/5,1/7) | **101/105** |
| b = 4 | a = 3 (gcd(a,4)=1, 2≤a<4), c ≥ 5, d ≥ 7 | 3·e₂(1/3,1/4,1/5,1/7) | **131/140** |
| b = 5 | a ≤ 4, c ≥ 6, d ≥ 7 | 1/5+1/6+1/7+4(1/30+1/35+1/42) | **179/210** |
| b ≥ 6 | — | each of the six terms < 1/b | ≤ 6/b ≤ 1 |

All confirmed exactly; `max(101/105, 131/140, 179/210, 4/5) = 101/105 < 1`. Yes, `b = 4` forces
`a = 3`; and `a ≥ 2` is a hypothesis, so the degenerate `a = 1` never arises (with `a = 1` the lemma
is false). Brute force over all pairwise-coprime quadruples in range confirms
`max a·e₂ = 101/105`, attained uniquely at `(2,3,5,7)`.

**The global maximum of the whole left side of (3.1), over every coprime quadruple and every Q, is
101/105 = 0.96190…** — i.e. the lemma has only ~3.8% slack, and it is the pair row (Q = 2) that is
extremal. **Coprimality is essential and should be advertised as such**: at `(a,b,c,d) = (2,3,4,5)`,
`Q = 2` one gets `2·e₂ = 71/60 > 1`.

**Small imprecisions worth fixing** (neither affects correctness): in case `b = 5` the true
constraint is `c ≥ 7` (a = 4 forces c ≠ 6), so 179/210 is not tight; and the monotonicity used
there (increasing in a, decreasing in c and d) is not stated.

**Verdict: CONFIRMED. Worth publishing as stated?** Yes, as a lemma. It is elementary but it is the
arithmetic engine of Theorem 4, the statement is clean, and the extremal constant 101/105 is worth
recording because it is exactly what makes the five-modulus analogue fail.

---

## (C) Theorem 5 — per-prime cap 2/(N−1). **CONFIRMED**

**The probabilistic identity.** `G(f) = λ·P(Z_i ≤ f_i ∀i)` with `Z_i = λ{U + i/N}` is exact. Writing
`u = r/N + t` with `t ∈ [0,1/N)` gives `{u+i/N} = a_{ri} + t` (because `a_{ri}` is a multiple of
`1/N` in `[0,1)` and `t < 1/N`), so the branch-r condition is `t ≤ (1/λ)min_i(f_i − λa_{ri})` and the
admissible length is `min(1/N, max(0, (1/λ)min_i(f_i−λa_{ri})))`; multiplying by λ reproduces the
r-th summand of (6.1) verbatim. I verified `G_cyclic = λ·P` exactly at 2400 random rational points
across N = 2..7. **Gap (writing):** "Splitting U into its N subintervals shows directly" is where
`a_{ri}` comes from and deserves the two lines above.

**Union bound.** `P(Z_i > f_i) = 1 − f_i/λ` requires `0 ≤ f_i ≤ λ`; this is the *only* place the cap
is used, and the document does not flag it. It is not a formality: at N = 6 with six weights 1/2
(> λ = 2/5) the certificate gives `G = 2/5 < 1 = (Σf−2)^+`, so the sandwich genuinely fails
without the hypothesis. Given the cap, `G ≥ λ(1 − Σ_i(1−f_i/λ)) = Σf_i − λ(N−1) = Σf_i − 2`, and
`G ≥ 0`. Correct.

**Branch length / upper bound.** `Σ_i a_{ri} = (0+1+…+(N−1))/N = (N−1)/2`, so on branch r any
admissible t satisfies `Σf_i ≥ λ((N−1)/2 + Nt) = 1 + Nλt`; hence the branch length is at most
`min(1/N, (Σf_i−1)^+/(Nλ))`, and summing λ times the N branch lengths gives `(Σf_i−1)^+`. Correct
(the `1/N` cap is dropped, which is legitimate but unremarked; and `Σf_i < 1` makes every branch
empty).

**Finite divisor expansion.** Each cell's event *is* a single divisor condition: on an open cell the
threshold `λ(a_{ri}+τ)` is strictly positive, and `[f_i(n) ≥ θ] = [p_i^{j}|n]` with
`j = min{j : A_{i,j} ≥ θ}` (again the cumulative-step structure), so the conjunction over distinct
primes is `[∏_i p_i^{j_i} | n]`. Coefficients are `λ(v−u) ≥ 0`; distinct cells may produce the same
divisor, in which case coefficients add and stay nonnegative. I built the expansion independently
for 18 random multilevel capped systems (N = 3, 4, 5) and confirmed it is nonnegative and reproduces
`G(f(n))` **exactly** for every n in a full period.

**Numerical sandwich.** Verified on 56 877 grid points for N = 2..7, twice: once with `f_i` capped at
1 (the atom-system regime) and once with `f_i` free in `[0,λ]` (the functional statement (6.2) as
literally written). No violation. Additionally, full (H₂) sweeps (all m ≤ D, all window starts) over
whole periods for random capped multilevel systems at N = 4 and N = 5: all pass.

**Value at five equal half-weights: exactly 1/2** — and the lower hinge there is also exactly 1/2, so
the certificate is *tight* at the configuration that annihilates every pair hinge. Confirmed exactly.

**Scope remark the paper should make.** λ = 2/(N−1) exceeds 1 for N = 2, 3, so the hypothesis is
vacuous there and the theorem is weaker than the known four-prime result for N ≤ 4. The new content
begins at N = 5 (cap 1/2). For k active primes one should take N = k, giving the best cap 2/(k−1).

**Verdict: CONFIRMED. Worth publishing as stated?** Yes, as a proposition, mainly for the N = 5,
cap 1/2 case, which is genuinely multilevel (Theorem 4 is not) and again closes the five-half-weight
barrier. The cyclic/coupling construction is a nice, reusable certificate. Together with Theorem 4
it strengthens `Proposition~\ref{prop:remains}`: the remaining five-prime case needs at least two
multilevel primes **and** a prime of total weight > 1/2.

---

## (D) Lemma 7 — six-prime obstruction to pointwise nonnegative certificates. **CONFIRMED**

**Every counting step verified.**

* Upper bound at states of total weight ≤ 1 kills the constant, the singleton, and the
  (1/2,1/2)-pair coefficients: at such a state the upper hinge is 0 and G is a sum of nonnegative
  active terms. (28 threshold vectors are forced to zero this way.)
* All-ones state: `G = Σ_t c_t = P+T+H ≤ (6−1)^+ = 5`. Correct (it uses that the support-≤1 mass is
  already 0).
* The twenty states with exactly three coordinates 1: each has lower hinge `(3−2)^+ = 1`. A
  threshold vector of support s is dominated by exactly `C(6−s, 3−s)` of them. I computed the
  multiplicity for every one of the 729 threshold vectors and the resulting sets of counts are
  exactly: **support 2 → {4}; support 3 → {1}; support ≥ 4 → {0}** (and support 0 → {20},
  support 1 → {10}, both already zeroed by the previous step). Hence `4P + T ≥ 20`. Confirmed.
* `4P+T = 4(P+T+H) − 3T − 4H ≤ 20 − 3T − 4H ≤ 20`, so equality, `T = H = 0`, `P = 5`.
* All-half state: every surviving support-2 coefficient carries a threshold 1 in some coordinate,
  so `G = 0`, while the lower hinge is `(3−2)^+ = 1`. Contradiction. Confirmed.

**Independent infeasibility proof.** I did not reuse the counting argument. Instead I exhibited an
**exact rational Farkas certificate** for the LP `{c ≥ 0 : (Σf−2)^+ ≤ G(f) ≤ (Σf−1)^+ on {0,½,1}^6}`:

* lower-bound constraints with multiplier 1 at each of the 20 three-ones states, and 1 at the
  all-half state (total right-hand side **21**);
* upper-bound constraints with multiplier 4 at the all-ones state, 7 at each of the 6 states `e_i`,
  and 1 at each of the 15 two-halves states (total right-hand side **4·5 + 0 + 0 = 20**).

For every one of the 729 threshold vectors the aggregated lower multiplier is ≤ the aggregated upper
multiplier (verified exactly), so any feasible c would give `21 ≤ ⟨combination, c⟩ ≤ 20`. Infeasible.
This is a self-contained, machine-checkable, fully rational proof, independent of the paper's route.

**What is ruled out, precisely.** There is no function `G` on `{0,½,1}^6` of the form
`Σ_t c_t ∏_{i:t_i>0}[f_i ≥ t_i]` with **all coefficients nonnegative** that lies **pointwise**
between the two hinges. Equivalently, and slightly more strongly than stated: for the six-prime atom
system with atoms ½ at p and ½ at p² (whose cumulative values realise all 3⁶ patterns by CRT), no
**pointwise nonnegative divisor certificate** `C(n) = Σ_d γ_d[d|n]`, `γ_d ≥ 0`, satisfies
`(S−2)^+ ≤ C ≤ (S−1)^+` — restrict to `n = ∏ p_i^{e_i}` with `e_i ≤ 2` and all higher-power and
foreign-prime terms drop out, leaving exactly a G of the stated form with nonnegative coefficients.
The paper's version does not make this reduction, and could.

**What is NOT ruled out, and does the run say so?** Yes, correctly and prominently: *"This is an
obstruction to a pointwise certificate, not a counterexample to (H₂)."* It rules out nothing about
(H₂) itself; in particular it does not touch (i) certificates that dominate the left hinge only
after summation over `[1,m]` — which is exactly what Theorem 4 uses, and exactly why the n = 12705
example is not a contradiction; (ii) signed certificates; (iii) five-prime pointwise certificates —
I confirmed directly that Lemma 6's q = 6 certificate *does* sandwich on `{0,½,1}^5`, so the
obstruction is genuinely a six-prime phenomenon; (iv) Theorem 5 at N = 6, whose cap 2/5 < 1/2
excludes the offending state. No overclaim anywhere in §8.

**Verdict: CONFIRMED. Worth publishing as stated?** Yes, as a short lemma/remark. It is the piece
that *explains* the shape of Theorem 4 (why the certificate must abandon pointwise left domination),
and it draws a sharp line at six primes. I would add the "any nonnegative divisor certificate"
reduction and the explicit Farkas multipliers, which make it a one-paragraph verifiable proof.

---

## (E) Judgement on the OPEN Lemma 8 (the K₄ bridge)

**The conditional implication (9.2) is correct.** Given `K₄`, the argument reproduces Lemma 3 for an
arbitrary four-prime multilevel system: `Q` = least positive integer with `T(Q) > c` exists and is
`≥ 2` (because `T(1) = 0 ≤ c`) and is P-smooth; if `T(n) > c+1` then deleting any one prime's entire
contribution leaves value `> c` (per-prime capacity ≤ 1), so the P-smooth part `D` of `n` satisfies
`D/p_i^{v_i} ≥ Q` for every i — equivalently `D/max_i p_i^{e_i} ≥ Q` — hence `D` is divisible by some
member of the coordinatewise-minimal family `A_P(Q)`; `K₄` then gives
`#{k ≤ M : T(k)>c+1} ≤ M·Σ 1/D(e) ≤ M/Q`, hence `≤ ⌊M/Q⌋`; and `[Q|n] ≤ [T(n)>c]` because `T` is
monotone under divisibility. Since the four-prime base (Lemma 1) already holds for arbitrary
multilevel systems, the elimination proof of Theorem 4 then runs with an unrestricted fifth prime.
The finiteness proof (`e_i ≤ E_i`) is also correct as written. The same small write-up gaps as in
Lemma 3 apply (why `Q ≥ 2`; the max-versus-all-components equivalence; monotonicity of T).
**Is K₄ plausible?** I audited it far past the run's own scope: all 4-subsets of the primes below 60
with `2 ≤ Q ≤ 400` (**949 620 (P,Q) instances**), plus `P = {2,3,5,7}` for all `2 ≤ Q ≤ 4000`, plus
random prime quadruples — **no violation anywhere**, with global maximum exactly **101/105** at
`(P,Q) = ({2,3,5,7}, 2)`, i.e. only 3.81% of slack, and second-largest value 299/315. So it is very
likely true but genuinely delicate. Two structural warnings. First, the run's own observation that
monotonicity in the primes fails (`K_{2,5,7,11}(3) = 111/220 < 236/385 = K_{3,5,7,11}(3)`) is
correct and blocks any "reduce to the smallest primes" argument. Second — a point the run does not
make, and which I found by scanning — **`Q = 2` is not always the maximising Q**: for `{2,5,7,11}`
the maximum is at `Q = 4`, where `K = 37/55 = 0.6727` against `213/385 = 0.5532` at `Q = 2`; 2275 of
the quadruples I scanned peak away from `Q = 2` (typically at `Q = 4`, whenever `2 ∈ P` and
`3 ∉ P`). That kills the most natural proof strategy, namely "the sup over Q is attained at `Q = 2`,
where `K₄` reduces to row 1 of Lemma 2 restricted to primes". A proof of `K₄` will therefore have to
handle the exponent ladders directly rather than collapse to the Boolean case, which is precisely
why it is still open. Finally, the run is right that `K₄` would not iterate: the five-prime analogue
is refuted by `2·e₂(1/2,1/3,1/5,1/7,1/11) = 194/165 > 1` (I recomputed it exactly), so `K₄` buys the
unrestricted five-prime case and nothing beyond — and the document says exactly that, and marks the
lemma OPEN rather than claiming it.

---

## Constants — my own exact values

| quantity | claimed | my exact value | agrees |
|---|---|---|---|
| row-1 case b = 3 | 101/105 | 101/105 | ✓ |
| row-1 case b = 4 | 131/140 | 131/140 | ✓ |
| row-1 case b = 5 | 179/210 | 179/210 | ✓ |
| max of Lemma 2's left side over all coprime quadruples and all Q | (implicit) | **101/105**, at ((2,3,5,7), 2) | ✓ |
| Theorem 5 at five equal half-weights | 1/2 | 1/2 (= lower hinge, tight) | ✓ |
| 2160·S(12705) − 2160·2 | 2625 | 2625 | ✓ |
| 2160·C(12705) | 1948 | 1948 | ✓ |
| worst pointwise deficit over D = 25410 | (−677 at 12705) | −677/2160 at n = 12705 | ✓ |
| certificate period | 25410 | 25410 = 2·3·5·7·11² | ✓ |
| five-prime K analogue | 194/165 | 194/165 > 1 | ✓ |
| K non-monotonicity | 111/220 < 236/385 | 111/220 < 236/385 | ✓ |
| global max of K₄ over primes < 60, Q ≤ 400 | (not claimed) | **101/105** | — |
| second largest K value for {2,3,5,7} | (not claimed) | 299/315 | — |
| new: K₄ maximiser is not always Q = 2 | (not claimed) | K_{2,5,7,11}(4) = 37/55 > 213/385 | — |

## Overall

Four correct results, honestly labelled, with an honest statement that the run missed its targets
(largest unrestricted N is still 4; no counterexample). (A) and (C) are publishable additions to
`sec_remains.tex`; (B) is the lemma (A) needs; (D) is a short explanatory obstruction. The
write-up needs the ~15 one-line justifications listed above before it is journal-ready, but none of
them is a repair to the mathematics. The one thing I would insist on editorially is that the
"after summation, not pointwise" mechanism of Theorem 4 be stated as a definition-level remark
rather than a footnote, because it is what reconciles (A) with (D).
