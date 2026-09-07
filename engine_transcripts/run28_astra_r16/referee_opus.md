# Adversarial referee report — Erdős 708, round 16 (signed clipped-prefix certificate)

Target: `engine/out/astra_708_r16/report.md` (line numbers below refer to that file).
Accepted inputs read: `papers/erdos708/main.tex` (§`sec:sparse`, Lem `largeatoms`, Thm `dense`, Cor `sparsecore`,
Prop `fano`, Lem `dual`/`round`/`fewprimes`, Thm `cond`), `engine/out/claude_blitz_0905/F1_708/report.md` and
`referee.md`, plus `engine/harvest/erdos708_pro_r13.md`, `erdos708_pro_r14.md`, `erdos708_pro_r14_referee.md`
for the barrier statements. All arithmetic below was recomputed in exact `fractions`; the brute-force checks
(hinge, Lemma 3 count, Lemma 4) were written from scratch, not reused from `exact_checks.py`.

## VERDICT: PASS

I could not find a mathematical error. Every inequality in Lemmas 1–7 and in the composition is correct as
written, and the two barriers that could plausibly apply (rounds 13/14; the paper's Prop `fano`) genuinely do
not. Four load-bearing steps are used without proof but are true and one line each (listed in §11); they are
writing gaps, not repairs. My confidence is limited by §11's last item: I did not build an independent
end-to-end numerical replication at near-critical parameters.

---

## 1. Lemma 1 (L41–67) — **OK**

* Rounding: `A_{p,j} ∈ (0,1]` ⟹ `t = 2^{-h}` with `h ≥ 0` exists and `t ≤ A < 2t`. ✔
* "Retain first exponent attaining each rounded value" (L41): rounded values are non-decreasing in `j`, so the
  first-occurrence list has `q` and `t` both strictly increasing. ✔
* `b_p(k) ≥ t_p` (L57–58): `q_p` = smallest `p^j` with `round(A_{p,j}) = t_p`; since `round` is monotone and
  `round(A_{p,v_p(k)}) = t_p`, we get `j ≤ v_p(k)`, hence `q_p | k`. If `q_p` survives (1) it is a retained level
  *of value exactly* `t_p`, so the largest retained value dividing `k` is `≥ t_p`. ✔ (This is the step the brief
  asked about; it is correct because the retained *pair* is `(q_p, t_p)`, not merely "some level below".)
* Cutoff (1) `q^{16/t} ≤ m` ⟺ `q ≤ m^{t/16}`, and `16/t = 16·2^h ∈ ℤ`. Dropped primes: `a_p(k) < 2t_p < 32 log q_p/log m`;
  the `q_p` sit at distinct primes and `∏ q_p | k ≤ m`, so `Σ log q_p ≤ log m` and the dropped total is `< 32`. ✔
  Kept primes contribute `Σ a_p(k) < Σ 2t_p ≤ 2B(k)`. Hence `S(k) ≤ 2B(k)+32` and `(S−64)^+ ≤ 2(B−16)^+`. ✔
* Mean comparison `H_B ≤ H` (L55): all retained moduli are original moduli, so a common period `Q` exists;
  `avg_{n≤Q} B = Σ increment/q = H_B`, `avg S = H`, and `B ≤ S` pointwise (each `b_p(n) = t ≤ A_{p,j} ≤ a_p(n)`).
  Valid — the objection "rounding can raise individual increments" is correctly bypassed. ✔
* `R_B ≤ R` from `B ≤ S`. ✔ `log q ≤ (t/16) log m` survives pruning because the retained increments telescope to `t` (L67). ✔

Note: the hypothesis `p^j ≤ m/64` is **never used** anywhere in §§1–7. The theorem proved is therefore formally
stronger than Cor `sparsecore` needs. That is not an error, but it should be stated.

## 2. Section 2 / Lemma 2 (L71–99) — **OK**

* `Σ_i w_{k,i} = |[0,B(k)) ∩ (2,3]| = 1` since `B(k) > 16 > 3`; the `P_i(k)` are pairwise distinct (strictly
  increasing), so `Σ_P M(P) = L_B`. ✔
* `w_{k,i} > 0` forces `s_i > 2` **strictly** (if `s_i = 2` the intersection is empty) and `s_{i−1} < 3` **strictly**
  (if `s_{i−1} = 3` the intersection is `{3}`, measure 0). Hence `μ(P) = s_i ∈ (2,4)` and `w_{k,i} ≤ s_i − s_{i−1} = θ`. ✔
* `P < m^{1/4}`: `log P = Σ_{j≤i} log q_j ≤ (μ(P)/16) log m < log m/4`; so `K_P = ⌊m/P⌋ ≥ 1`. ✔
* Splitting `B(k) = μ(P) + Σ_{p∤P} b_p(j)` for a *contributing* `k = Pj`: at `p | P` the effective level of `k` **is**
  the level of `P`; at `p ∤ P`, `v_p(j) = v_p(k)` so `b_p(j) = b_p(k) ≤ θ` by the decreasing-mass order. ✔
  (This is exactly the place where round-15's Lemma 6.1 broke; here it is used only for `k`'s own prefix, which is legitimate.)
* `d_k < Σ_{p∤P} b_p(j) − 12` from `μ(P) < 4`, so `d_k ≤ (Σ − 12)^+`. `C = 12/θ = 12·2^h ∈ ℤ`, `r = C+1`. ✔
* Rescaled hinge `(Σb − 12)^+ ≤ θ^{1−r} e_r(b)` needs `b_p(j) ∈ [0,θ]`, which holds for contributing `k`. ✔
  I re-derived the pair-compression proof at L99 independently: `e_{C+1} = A + (u+v)D + uv·e_{C−1}(rest)` with
  `e_{C−1} ≥ 0`, moving at fixed sum to the box boundary lowers `uv`, terminates at `(1^q, τ, 0…)`, and
  `binom(q,C+1) + τ·binom(q,C) ≥ (q+τ−C)^+` in all three cases. 400 random exact-rational tests, `N ≤ 9`,
  `C ≤ 5`: **0 violations**.
* Moment bound `Σ_{j≤N} e_r((b_p(j))_p) ≤ N H_B^r/r!` : expansion into one retained level per prime, distinct
  primes ⟹ coprime moduli ⟹ `⌊N/∏q⌋ ≤ N/∏q`, then `r! e_r(h) ≤ (Σh)^r`. ✔ Restricting to `p ∤ P` only lowers `e_r`,
  and summing over *all* `j ≤ K_P` (not just contributing ones) is legitimate since `e_r ≥ 0`. ✔
* `k ↦ j = k/P` injective for fixed `P`; `j ≤ ⌊m/P⌋ = K_P`; `M(P) ≤ θ^{2−r}(H_B^r/r!)(m/P)`;
  `a_P = M(P)/K_P ≤ 2ε(θ)` from `u/⌊u⌋ ≤ 2` for `u ≥ 1`. ✔ All correct.

## 3. Lemma 3 (L110–118) — **OK**

Masses `≥ θ` at a prime are `θ·2^j`, `j ≥ 0`, distinct per prime. At `z = 1/2` the per-prime sum is
`Σ_{h≥0} 2^{−2^h} ≤ Σ 2^{−h−1} = 1` (I computed the true value 0.81642). Product over eligible primes gives
`≤ 2^{N_θ(n)}`; each admissible subset (total mass `< 3`) contributes `≥ 2^{−3/θ}`; hence
`count ≤ 2^{3/θ + N_θ(n)} ≤ 2^{(3+T_θ(n))/θ}`. ✔ Unique factorisation makes `P ↦ P/q`'s level set injective. ✔
Over-counting (ignoring the ≺-order, allowing `q`'s own prime) is in the safe direction. ✔
Independent brute force (300 random dyadic configurations, exact DP over `θ`-units, `θ = 2^{-h}`, `h ≤ 4`,
up to 8 primes): no violation; worst observed `count/bound = 0.125`.

## 4. Lemma 4 (L120–124) — **OK**

Retained masses at one prime dividing `n` are distinct dyadic numbers `≤ b_p(n) = 2^{-h_0}`, hence
`Σ ≤ 2^{-h_0}(1+½+¼+…) = 2b_p(n)`. Sum over primes. ✔ 200 random checks pass.

## 5. Lemma 5 (L128–150) — **OK, exact arithmetic reproduced**

`G(θ) = t^{12t} H_B^{12t+1} 2^{23t}/(12t+1)!` with `t = 1/θ`, `r = 12t+1` — algebra verified.
`(12t)! ≥ (12t/e)^{12t}` is the standard `n! ≥ (n/e)^n` (from `e^n ≥ n^n/n!`); `e` appears in the **numerator** of
the resulting bound, so an **upper** bound on `e` is the right direction — `e < 11/4` is used correctly.
`e ≤ 65/24 + 1/100 = 1631/600 < 11/4` ✔ (exact).
`2^23(187/768)^12 = 1828518162230556187140793681/5019318332045454244023631872` — **matches the report digit for
digit**, is `< 1/2`, and the cross-product gap `1362282007584341869742044510 > 0` reproduces (L247–251).
The real content is `187/768 < 192/768 = 1/4`, so the product is `< 2^23·2^{−24} = 1/2`.
Monotonicity: `17/[16(12t+1)2^t]` is decreasing in `t`, maximal `17/416` at `t = 1` ✔.
Direct evaluation: `G(1)=2.96e−3`, `G(1/2)=3.46e−4`, `G(1/4)=6.07e−5`, `G(1/8)=1.26e−5`, all `≤ 17/416 = 0.04087` ✔.

Margin note (not a defect): the binding requirement is `eH/12 ≤ 1/4`, i.e. `H ≤ 3/e = 1.10364`, against the
hypothesis `H < 17/16 = 1.0625` — **3.9 % headroom**. This is the tightest constant in the proof.

## 6. Lemma 6, pointwise feasibility (L159–177) — **OK**

* `B(n) ≤ 2 ⟹ no carrier divides n`: `P | n ⟹ B(n) ≥ B(P) = μ(P) > 2`. ✔
* The identity `U_P(n) = T_{θ_P}(n) − θ_P·ω(P)` for `P | n` (L163) is **exact and is the fix for the round-15
  §7.1 defect**. The brief's question — *can `P | n` while some prime of `P` has `b_p(n) ≠ its level in P`?* —
  answer: **yes it can** (`n` may carry higher powers, so `b_p(n)` can be strictly larger), and it breaks
  nothing, precisely because the cap gives `min(b_p(n), θ_P) = θ_P` either way (`b_p(n) ≥ b_p(P) ≥ θ_P`).
  This is the one place where the previous round was wrong and this round is right.
* `θ_P ω(P) ≤ μ(P) < 4` ⟹ bracket `> 0` ⟹ `U_P < 16` ⟹ `T_{θ_P}(n) < 20` ⟹ Lemma 3 gives `< 2^{23/θ_P}`. ✔
* Chain: `F(n) ≤ 3·Σ_q 2ε(θ_q)·2^{23/θ_q} = 6 Σ_q θ_q G(θ_q) ≤ 6·(17/416)·2B(n) = (51/104)B(n) ≤ B(n)/2 ≤ B(n)−1`,
  the last step needing `B(n) ≥ 2` — supplied by `B(n) > 2`. `51/104 = 0.49038 ≤ 1/2` ✔ (exact).
  Note the grouping is sound: each carrier has exactly one ≺-last level; Lemma 3 over-counts by including
  negative-bracket carriers, which is the safe direction; `q` with no positive-bracket carrier contribute 0.
* Crucially, nothing in Lemma 6 uses `n ≤ m`, so feasibility holds for **every** positive integer, which is what
  `R_B ≥ Σ_I F` requires. ✔
* Slack check: using the *true* `max_θ G(θ) = G(1) = 2.96e−3` instead of `17/416`, the chain gives
  `F(n) ≤ 0.0356 B(n)`, i.e. the feasibility step has a factor ≈14 of real room, not the apparent 51/104 vs 1/2.

## 7. Lemma 7, support and interval value (L187–209) — **OK**

* `min(b_p(·),θ)` telescopes over the retained levels at `p` (they form a prefix under divisibility), giving
  `[P|n]U_P(n) = Σ_{p∤P,e} β^{θ_P}_{p,e}[Pp^e | n]`, with `gcd(P,p^e)=1` so the modulus is exactly `Pp^e`. ✔
* Every retained `q` has `q ≤ m^{v/16} ≤ m^{1/16}`, so `Pq < m^{1/4+1/16} = m^{5/16} ≤ m`. ✔ Both `N_I(d) ≥ ⌊m/d⌋`
  (all `d`) and `N_I(d) ≤ m/d+1 ≤ 2m/d` (`d ≤ m`) are correct for any window of `m` consecutive integers. ✔
* Positive: `3a_P N_I(P) ≥ 3a_P K_P = 3M(P)` (`a_P K_P = M(P)` exactly). ✔
* Negative: `K_P ≥ m/(2P)` ⟹ `a_P N_I(Pq) ≤ (2P M(P)/m)(2m/(Pq)) = 4M(P)/q`; total subtraction
  `≤ (3/16)·4·M(P)·H_{θ_P} ≤ (3/4)M(P)H_B`, using `H_θ ≤ H_B` because `min(·,θ)` is 1-Lipschitz non-decreasing. ✔
* `3(1−H_B/4) ≥ 3(1−17/64) = 141/64` ✔ (exact). Keeping the terms separate before combining equal moduli is
  legitimate: `Σ_I F = Σ_terms coeff·N_I(modulus)` by linearity, independently of coincidences. ✔
* All coefficients depend only on the atom system and `m`, not on `I`. ✔

## 8. Composition (L213–218) — **OK**

`R ≥ R_B` (Lemma 1) `≥ Σ_I F` (Lemma 6, pointwise, valid for every positive integer) `≥ (141/64)L_B` (Lemma 7)
`≥ (141/128)L` — the last step is `L_B ≥ L/2`, i.e. `L ≤ 2L_B`, used in the correct direction. `141/128 = 1.1016 > 1`. ✔

**Barriers.** Round 14's Lemma 3 (the reflected-window obstruction) rests on zero-forcing: "the constraint at
`B−D` reads `Σ_{E|B−D} c_E ≤ 0` **with `c ≥ 0`**, and `D | B−D` ⟹ `c_D = 0`" (r14 referee §2.1). That deduction is
invalid for a signed certificate, so the barrier does not apply. Round 13's T3 is explicitly about "every
**nonnegative** certificate supported on divisors of high points". The report's L24 claim is therefore correct,
and I confirm the source statements carry the nonnegativity restriction.
The paper's Prop `fano` ("two-sided counts alone cannot suffice") is also escaped, and for the right reason:
the proof injects genuine arithmetic through the moment bound `Σ_{j≤N} e_r ≤ N H_B^r/r!` (coprimality of
prime-power moduli plus `⌊N/d⌋ ≤ N/d`), which is **false** in the projective-plane configuration (there a "line"
has `N_μ = 1` while the product of the point-densities is astronomically smaller). So the certificate is not a
counterexample to `fano`. Sanity check on r14's Theorem 8 family (0/1 atoms, `H ≈ ln 2`): the certificate's
guaranteed value is `≈ 2.9 L_B` while the true `R_B ≈ 0.19 m ≫ L_B ≈ 10^{−18} m` — consistent, no contradiction.

## 9. Corollaries 8.1 / 8.2 (L222–237) — **OK**

Cor `sparsecore` (main.tex L1241–1257) reads verbatim:

> "Suppose that for every `m>4096` and every system of atoms `α_{p,j}≥0` with `Σ_j α_{p,j}≤1`, supported on
> `p^j ≤ m/64` and with `Σ α_{p,j}/p^j < 17/16`, the function `S_0` satisfies `Σ_{k≤m}(S_0(k)−64)^+ ≤
> Σ_{b∈I}(S_0(b)−1)^+` for every `x≥0`. Then (eq:th65) holds for all weights, all `m` and all `x`, and
> consequently `g(n) ≤ 81 n` for all `n`."

That is **exactly** the report's hypothesis, no more: universal (SC_64) is the sole open input. Its proof uses
`m ≤ 4096` (left side 0, since `k ≤ 4096 ⟹ Ω(k) ≤ 12 < 65`), Thm `dense` for `H_64 ≥ 17/16`, and Lem `largeatoms`
(`(S−65)^+ ≤ (S_0−64)^+`, `(S_0−1)^+ ≤ (S−1)^+`) otherwise. The transfer to `w_z` is the peel at main.tex L839–840
(`w_z = E+S`, `(w_z−1)^+ = E+(S−1)^+`, `(w_z−c)^+ ≤ E+(S−c)^+`, `Σ_I E ≥ Σ_K E`). All as the report says.
For 8.2: `τ* ≤ 65n` via Lem `dual`, then Lem `round` (`|B| ≤ τ*+|𝒫|`) and Lem `fewprimes` (`|𝒫| < 16n`, which
**requires** `m < 8n^3`, so the split against Thm `long` at `a_n ≥ 8n^3` is necessary, not decorative) give
`|B| ≤ 65n+16n−1 < 81n`. Matches main.tex L1257 ("threshold 65 in place of 2 gives `g(n) ≤ (65+16)n`"). ✔
Nit only: L229's phrasing "at most 81n integers … have product divisible" should read "some set of at most 81n
of the integers"; the paper's at-most convention (main.tex L71) is cited, so this is cosmetic.

## 10. `exact_checks.py` (L241–267) — **OK, genuine but quantitatively slack**

Ran it (copied to a scratch dir so the target directory was not written to): **0.85 s**, all four sections PASS,
and the produced `exact_checks.json` is **byte-identical** to the committed one. Every number quoted in §9 of the
report reproduces: 140 systems / 121 positive threshold-64 hinges; 24 DP cases (max 193 primes); `L_B =
302500000000000000000426`; 11 carriers; 309 combined moduli, 298 negative; 1200 pointwise samples.

It is a real test, not vacuous:
* `run_constants` directly evaluates `G(θ)` at `H_B = 17/16` **exactly** for `t = 1,2,4,8,16,32,64` and asserts
  `≤ 17/416` — this is a genuine test of Lemma 5 at its tight parameter.
* The three negative controls are real: a 31-prime system where the preprocessing loss is `30.5 > 16` (so the
  constant 32 cannot be 16); a `p=2` system with 10 000 distinct cumulative values in `(1/2,1)` producing 10 000
  carriers against the uncompressed bound `2^{10}` (so dyadic compression is essential); and `2^23(17/64)^12 =
  3.94 > 1/2` (so `e < 3` does not certify the constant). I re-checked all three by hand.
* `assert via_formula == via_divisors` genuinely tests Lemma 7's divisor expansion; `assert mass <= eps*m/P`,
  `c <= 2*eps`, `P**4 < m`, `D**16 < m**5` genuinely test Lemma 2 and the modulus-support claims.

Limits a referee must record:
* The one non-vacuous carrier system has `H_B = 0.098`, three orders below the critical `17/16`. Consequently
  `a_P` and `F(n)` there are of order `10^{−1000}`, so `assert via_formula <= max(bval-1,0)` passes with
  astronomical slack: **the suite cannot detect a wrong constant in the Lemma 6 chain** (only Lemma 5 is tested
  at the tight point). Feasibility tightness is established by the proof, not by the suite — which the report
  does say (L267).
* The "five intervals" produce five *distinct* exact rationals, but the ratios agree to 15 significant digits
  (`≈ 2.98563` in every case, against the required `141/64 = 2.20313`). So the window test confirms the value
  bound but does not discriminate window geometry; the claim at L262 is accurate but the discrimination is nil.
* `audit.md` L28 honestly discloses two test-generator repairs before the passing run.

---

## 11. What would have to be true for the proof to fail

Concrete falsifiable conditions, ordered by how much of the proof they would take down. I checked each and
found it *does not* hold; a formaliser must nonetheless discharge the first four, which the report uses
without stating.

1. **If `θ_P`, `μ(P)` and the level set were not functions of the integer `P` alone.** `a_P`, `U_P` and the
   grouping in Lemma 6 are all indexed by the integer `P`; if two hot `k` produced the same product with
   different ≺-last levels, `θ_P` would be ambiguous and Lemma 6 would double count. It is fine — the `p`-part
   of `P` is exactly the effective modulus `q_p`, which is a retained level with a determined mass, and the ≺
   order is global — but **this is never stated** (L71–80).
2. **If `B(P) ≠ μ(P)`.** Used twice (L161 "every prime in `P` contributes at least its carrier mass", and
   `B(n) ≤ 2 ⟹` no carrier). True because the largest retained level dividing `q_j` is `q_j` itself. Unstated.
3. **If `b_p(n) < b_p(P)` were possible for `P | n`.** Would destroy `U_P = T_θ − θω(P)`. False (divisibility is
   downward closed), but unstated.
4. **If the retained levels at a prime dividing `n` did not form a prefix of that prime's retained list.**
   Used for `b_p(n) =` telescoped sum and for the `β` expansion in Lemma 7. True; unstated.
5. **If some retained level had `q > m^{1/16}`**, then `Pq` could exceed `m` and `N_I(Pq) ≤ 2m/(Pq)` would fail,
   killing Lemma 7. Excluded by cutoff (1) together with `t ≤ 1`. Checked.
6. **If `e ≥ 11/4` or `187/768 ≥ 1/4`.** Both false; the whole Lemma 5 constant rests on `eH/12 < 1/4`, i.e.
   `H < 3/e = 1.10364`, only 3.9 % above `17/16`. Any future weakening of the sparse/dense split above
   `H = 3/e` would break this proof at Lemma 5.
7. **If the round-13/14 barriers were not restricted to nonnegative certificates.** They are — r14's zero-forcing
   step explicitly invokes `c ≥ 0`, and r13's T3 says "every nonnegative certificate". Verified in the sources.
8. **If Cor `sparsecore` carried a hypothesis beyond universal (SC_64)** (e.g. a restriction on `I`, or on the
   atom system beyond `p^j ≤ m/64`, `Σ_j α ≤ 1`, `H_64 < 17/16`). It does not — quoted in §9 above.

Assumptions I could **not** fully verify:

* **Accepted inputs outside §`sec:sparse`.** I read but did not re-derive Thm `long` (`a_n ≥ 8n^3 ⟹ 2n`), the
  vertex argument in Lem `round`, and the `E`-peel identity at main.tex L839–840. Corollary 8.2 depends on all
  three. Per the brief these are accepted inputs; a full referee of `g(n) ≤ 81n` would have to check them.
* **No independent end-to-end replication at near-critical parameters.** I verified Lemmas 1–7 symbolically and
  reproduced the author's suite, but I did not construct a system with `H_B ≈ 17/16`, carriers at several
  distinct `θ`, and multi-level primes, and evaluate `F(n)` and `Σ_I F` from scratch. That is the single test
  that would most sharpen this verdict; it is expensive because a non-vacuous hot point needs `B(k) > 16`, hence
  `m` above roughly the 33rd-primorial scale.
* **No machine-checked proof.** The report claims none (L285), and its §10 dependency list matches what is
  actually used, with one addition: item 2 should also record the four unstated facts in 1–4 above.
