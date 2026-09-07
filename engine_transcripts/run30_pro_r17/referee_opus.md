# Referee report — erdos708_r17_pro.md (hinge inequality at threshold 17)

**VERDICT: PASS-WITH-REPAIRS** — every mathematical step re-derived independently checks out and every
constant was reproduced exactly by my own code (not the author's). The "repairs" are editorial: one
displayed intermediate inequality in Lemma 7 is off by a factor 2 (the stated *final* constant 192 is the
correct one, i.e. the error is in the transcript's intermediate line, not in the number that is used), and
three steps are compressed to the point where a reader must reconstruct the justification. No repair
changes any constant, any lemma statement, or the conclusion. I found **no gap and no error in the
mathematics**.

Referee: Claude Opus 5, no internet, exact-fraction Python only. Files read: the harvest, `sec_signed.tex`,
`main.tex`, `verify_constants.py` + log. Working scripts were written only to the session scratchpad;
this report is the only file I created anywhere else.

---

## Item-by-item

### 1. Lemma 1 (hinges (1), (2); moment bound (3); mean identity (4)) — **OK**

**(1) and the positive part.** The hint is correct and the harvest handles it correctly: the multi-affine
argument is applied to the *polynomial* `e_r(u) − Σu + r − 1`, not to `e_r − (Σu − (r−1))^+`. A multi-affine
`f` on `[0,1]^N` satisfies `f(u) = E[f(X)]` for independent Bernoulli(`u_i`), so `f(u) ≥ min over vertices`;
this is exactly the harvest's "convex combination of vertex values". At a vertex with `j` ones the value is
`C(j,r) − j + r − 1`, which is `≥ 0` for every `j ≥ 0`:
`j < r` gives `r−1−j ≥ 0`; `j ≥ r` gives `C(j,r) ≥ j−r+1` (fix `r−1` elements, adjoin one of the other
`j−r+1`). I checked all `r ≤ 59`, `j ≤ 199` exactly — no violation.
The hinge then needs the extra (trivial, *unstated*) remark `e_r(u) ≥ 0` on the nonnegative orthant, so that
`e_r ≥ max(0, Σu − (r−1)) = (Σu − (r−1))^+`. **Repair R1 (editorial):** state that remark.

**(2).** `e_4(u) − 2Σu + 7` is multi-affine; vertex values `C(j,4) − 2j + 7` are
`7,5,3,1,0,2,10,28,61,…` for `j = 0,1,2,…`, all `≥ 0` (minimum 0 at `j = 4`), checked to `j ≤ 299`.
Random exact-rational sweeps over the cube (4000 vectors, `N ≤ 12`) found no violation of (1) or (2).
This lemma is *load-bearing*: with `e_4` instead of `e_4/2` the ℓ=1 term of Lemma 7 would be `1.004`, and
the whole budget (4/5) would fail. It is correct.

**(3), non-distinct prime powers.** The coordinates of `e_r` are indexed by **primes**, one factor
`f_p(n) = Σ_j α_{p,j}[p^j | n]` per prime. Expanding the product therefore selects one atom per prime and
the chosen prime powers are automatically at *distinct* primes, hence coprime, hence
`Σ_{n≤N} [∏q | n] = ⌊N/∏q⌋ ≤ N/∏q`. Two atoms of the same prime can never be multiplied together, which is
exactly the failure mode the item asks about, and it does not occur. Then `e_r(h) ≤ (Σh)^r/r! = H^r/r!`.
Correct. (Same indexing is used consistently in Lemma 3 (`e_8` over primes) and Lemma 5 (`e_{r_ℓ}` over
primes), so the bound is applied legitimately at both sites.)

**(4).** `Σ_{j≥1}(f_p(p^j) − f_p(p^{j−1}))/p^j = (1 − 1/p) Σ_{v≥1} f_p(p^v)/p^v` by Abel summation with
`f_p(1) = 0`; termwise comparison gives monotonicity under pointwise domination. Correct, and it is what
justifies `H(B) ≤ H` (9) and `H(min(b,θ)) ≤ H(B)` used in Lemmas 5 and 8.

### 2. Lemma 2 (split at `m/Q`, `Q = 2^16`; identity (5); `m < 2^48` triviality) — **OK**

If a removed atom `p^j > m/Q` divides `k ≤ m`, then `p^{v_p(k)} ≥ p^j > m/Q`, so
`u = k/p^{v_p(k)} ≤ m/p^{v_p(k)} < Q`. Verified: `2·3·5·7·11·13·17 = 510510 > 65536`, so `ω(u) ≤ 6` and
`ω(k) ≤ 7`. Since `α`-totals per prime are `≤ 1`, `S(k) ≤ ω(k) ≤ 7 ≤ c`, so **both** sides of (5) vanish;
otherwise `S(k) = S_0(k)` identically. Correct, and the hypothesis `c ≥ 7` is exactly what is needed.
Triviality: `∏(first 13 primes) = 304250263527210 > 2^48 = 281474976710656` (verified exactly), so
`m < 2^48 ⇒ ω(k) ≤ 12 ⇒ S(k) ≤ 12 < 17` and the left side is 0.

### 3. Lemma 3 (dense branch, `H ≥ H* = 1025/1024`) — **OK**

`V = (H*/H)S_0` has scale factor `≤ 1`, so per-prime totals stay `≤ 1` and `H(V) = H*`. All atoms of `S_0`
have modulus `d ≤ m/Q`, so `⌊m/d⌋ ≥ (1 − 1/Q)m/d` and `Σ_{k≤m}V(k) ≥ (1 − 1/Q)mH*`.
Eighth moment: (1) with `r = 8` then (3) give `Σ(V−7)^+ ≤ mH*^8/8!`.
Exact check of (6): `(1 − 1/Q)H* − H*^8/8! = 9757905519810012911651885875/9748777809372369664830603264 ≈ 1.000936 > 1`.
The two auxiliary claims are exact: `(1−1/Q)H* − 1 = 64511/2^26` (verified as a Fraction identity), and
`H*^8 < 2 ⇒ H*^8/8! < 1/20160`.
Hence `Σ min(V,7) ≥ m`.

**`min(S_0,17) ≥ min(V,7)` — justified.** `H ≥ H*` makes the scale factor `≤ 1`, so `V ≤ S_0` pointwise;
then `min(V,7) ≤ min(S_0,7) ≤ min(S_0,17)`. (Using threshold 7 for `V` rather than 17 is what lets the
argument use `e_8` instead of `e_18`; the step is valid and is the reason the dense branch is cheap.)

Certificate: `F_dense = S_0 − 1` is the divisor family `c_1 = −1`, `c_{p^j} = α_{p,j}` (`p^j ≤ m/Q ≤ m`).
`F_dense(n) ≤ (S_0(n)−1)^+` trivially. Sign convention on the window is right: `c_1 < 0` and
`N_I(1) = m` exactly, the `c_{p^j} ≥ 0` use `N_I(p^j) ≥ ⌊m/p^j⌋`. So
`Σ_I(S−1)^+ ≥ Σ_I(S_0−1)^+ ≥ Σ_{k≤m}S_0(k) − m = Σ_k min(S_0,17) + Σ_k(S_0−17)^+ − m ≥ Σ_k(S_0−17)^+`,
and (5) converts to `S`. Complete.

### 4. Lemma 4 (dyadic rounding, cutoff `q^{3/t} ≤ m`, loss 6, (11)) — **OK**

`3/t = 3·2^h ∈ ℕ` for dyadic `t = 2^{-h} ≤ 1`, so (8) is well posed; retention forces
`t ≥ 3log2/log m`, hence finitely many levels. `b_p ≤ a_p` because `q_p(t) | n` implies
`a_p(n) = A_{p,v_p(n)} ≥ A_{p,j_0} ≥ t`; (9) then follows from (4).

Loss bound: for each prime with `a_p(k) > 0` let `t` be the largest dyadic `≤ a_p(k)`; then
`j_0 = min{j : A_{p,j} ≥ t} ≤ v_p(k)`, so `q_p(t) | k`. Retained ⇒ `a_p(k) < 2t ≤ 2b_p(k)`. Unretained ⇒
`t < 3 log q_p(t)/log m ≤ 3 v_p(k) log p/log m`, so `a_p(k) < 6 v_p(k) log p / log m`; these primes are
distinct so the sub-sum of `Σ_p v_p(k) log p = log k` gives total `< 6 log k/log m ≤ 6` for `k ≤ m`.
Hence `S_0(k) ≤ 2B(k) + 6`, and `(S_0−17)^+ ≤ (2B−11)^+ = 2(B − 11/2)^+`, which is (11) after summing.
Retained moduli satisfy `q ≤ m^{t/3} ≤ m^{1/3}`; the same holds for the atoms of `min(b_p,θ)`, since
`min(b_p,·)` can only jump where `b_p` jumps, i.e. at a retained modulus.

Small confirmation worth recording: `b_p` jumps at `p^j` **only if** some retained `t` has `q_p(t) = p^j`,
and then `b_p(p^j) = t` (monotonicity of `t ↦ q_p(t)`), so the atom's modulus obeys the cutoff at its own
`t`. This is what makes the `m^{1/3}` claim exact rather than approximate.

### 5. Lemma 5 (carriers of mass exactly `1+θ`; `c_C ≤ ε_ℓ`) — **OK**

*Mass exactly `1+θ`.* Every selected level is `θ·2^i`, hence an integer multiple of `θ`; `1` is too. The
shortest prefix crossing 1 has `s_{i−1} ≤ 1 < s_i ≤ s_{i−1} + θ ≤ 1 + θ`, and `s_i ∈ θℤ` forces
`s_i = 1 + θ` (and `s_{i−1} = 1`, so `i ≥ 2`). I asserted `μ(C) = 1 + θ_C` inside a live computation on a
real instance (11 primes at `z = 1/2`) and it held for every carrier.

*`P_C ≤ m^{(1+θ)/3} ≤ m^{2/3}`* by summing `log q ≤ (t/3)log m` over the levels; with `m ≥ 2^48`,
`m/P_C ≥ m^{1/3} ≥ 2^16` so `ν_C ≥ 1`.

*Assignment.* Each hot `k` (`B(k) > 11/2 > 1`) has exactly one shortest crossing prefix, so it is assigned
to exactly one carrier and `Σ_C M_C = L_B`. Verified numerically on two real instances (see below).

*Residual hinge and the `9ℓ/2` question.* For assigned `k = P_C u`: `b_p(u) = b_p(k)` for `p ∤ P_C` (the
carrier's primes are the only ones whose valuation changes), and `b_p(k) ≤ θ` for `p ∤ P_C` because the
levels are ordered by decreasing value (ties by increasing prime), so everything after position `i` has
value `≤ θ`. Then `B(k) = (1+θ) + Σ_{p∤P_C} b_p(u)` and `d_k = (Σ_{p∤P_C} b_p(u) − (9/2 − θ))^+`.
- `θ = 1`: threshold `7/2`, **not** an integer minus one, which is precisely why (2) is needed rather than
  (1); `d_k ≤ e_4/2` with `u_p = b_p(u) ∈ [0,1]`.
- `θ = 1/ℓ ≤ 1/2`: `(11/2 − (1+1/ℓ))/(1/ℓ) = 9ℓ/2 − 1`. **`9ℓ/2 − 1` is an integer for every dyadic
  `ℓ ≥ 2`**, because dyadic `ℓ ∈ {2,4,8,…}` is even. `ℓ = 1` is the only dyadic value for which it fails,
  and that is exactly the case routed through (2). This is consistent and complete.
  `d_k = θ(Σu_p − (r_ℓ−1))^+ ≤ θ·θ^{−r_ℓ} e_{r_ℓ}((b_p(u))_{p∤P_C}) = ℓ^{r_ℓ−1} e_{r_ℓ}(…)`.

*Injectivity and the moment step.* `k ↦ u = k/P_C` is injective for fixed `C`, and `u ≤ ⌊m/P_C⌋ = ν_C`;
dropping the assignment restriction only adds nonnegative `e_r` terms, so (3) applied to the capped system
`min(b_p,·)` (mean `≤ H(B) ≤ H < H*` by (4)) gives `M_C ≤ ℓ^{r−1} ν_C H*^{r}/r!` and
`c_C ≤ ℓ^{r−1}H*^r/r! = ε_ℓ/γ ≤ ε_ℓ`. The `γ` in (15) is **redundant slack** (it is `γ` that is separately
needed in Lemma 8), not an error; the bound is conservative in the safe direction.
**Repair R2 (editorial):** the transcript never says where `γ` enters `ε_ℓ`; either drop it or say
"we insert a harmless factor `γ ≥ 1`".

*Empirical check.* On the author's own cited instance (18 primes 23…101, `m = ∏p`) I rebuilt the carriers
from scratch: **91 carriers** (matching the audit table), `Σ_C M_C = L_B` exactly, `max c_C/ε_1 = 3.5·10⁻³`.
On an ℓ=2 instance (11 primes 23…67 at `z_p = 1/2`, `m = (∏p)²`, `H = 0.1404 < H*`) I get 55 carriers with
`θ=1` and 11 with `θ=1/2`, `Σ_C M_C = L_B` exactly, `μ(C) = 1+θ_C` for all, and `c_C ≤ ε_ℓ` for all.

### 6. Lemma 6 (certificate (17)/(18); carrier count `C_ℓ(N)`; bounds; (20)) — **OK**

*Divisor form.* `min(b_p(n),θ) = Σ_j δ^{(θ)}_{p,j}[p^j|n]` telescopes with `δ ≥ 0`, and since `p ∤ P_C` the
moduli multiply, giving (18). Negative moduli `P_C p^j ≤ m^{(1+θ)/3}·m^{1/3} ≤ m^{2/3}·m^{1/3} = m`. Correct.

*`C_ℓ(N)` is a valid upper bound.* For a carrier `C | n` with last value `θ = 1/ℓ`: every prime of `P_C`
has `b_p(n) ≥ b_p(P_C) ≥ θ` (monotonicity of `b_p` in the valuation), so it is one of the `N` primes; each
selected level scales to a power of two in `{1,2,4,…,ℓ}` (values lie in `[θ,1]`); the total scaled mass is
`(1+θ)/θ = ℓ+1` **exactly**, by the mass computation in Lemma 5. So carriers inject into vectors in
`({0}∪{1,2,4,…,ℓ})^N` of total `ℓ+1`, counted by `[X^{ℓ+1}](1+X+X²+X⁴+…+X^ℓ)^N`. Dropping the ordering
constraint (which refers to the *hot k*, not to `n`) only enlarges the count.

*Does a set of choices determine at most one carrier?* Yes, but the transcript's stated reason ("the
canonical ordering and unique `q_p(t)`") is thin. The clean argument: a level value `t` at prime `p`
determines the modulus `q_p(t)`, so a choice vector determines `P_C`; conversely `P_C` determines the
levels, since if `q` is the `p`-part of `P_C` then the carrier's level at `p` equals
`max{t retained : q_p(t) | q}` (it lies in that set, and any member has `q_p(t) | q | p^{v_p(k)}` so is
`≤ b_p(k)`). Hence carriers ↔ products ↔ choice vectors, injectively. **Repair R3 (editorial):** include
this two-line identification; without it "a set of choices determines at most one carrier" is asserted, not
proved. (I confirmed the generating-function count against brute-force enumeration of choice vectors for
`ℓ = 1,2,4` and `N ≤ 8`, and against the recurrence (22) for `ℓ = 8,16,32,64`; all three agree.)

*The two bounds.* For `P_C | n`, each prime of `P_C` contributes exactly `θ` to `T_θ(n)`, so
`U_C = T_θ − θω(P_C)`; `T_θ ≥ Nθ` and `θω(P_C) ≤ μ(C) = 1+θ` give `U_C ≥ max(0, Nθ − 1 − θ)`. And
`B(n) ≥ μ(C) = 1+θ` and `B(n) ≥ Nθ` give `B(n) − 1 ≥ max(θ, Nθ − 1) = max(1/ℓ, (N−ℓ)/ℓ)`. Both correct.
Dropping negative summands is legitimate because `c_C = M_C/ν_C ≥ 0`, and replacing the bracket by
`(1 − max(0,(N−ℓ−1)/ℓ)/K)^+` dominates it in both the positive and the negative case.
The restriction `N ≤ ⌊(K+1)ℓ+1⌋` in (19) loses nothing: the clip vanishes as soon as
`N ≥ (K+1)ℓ+1`, and the floor always covers the last `N` with a positive clip. I re-ran each `R_ℓ` with the
range extended by 60 extra values of `N`; the maximum never moved.
Using an independent worst `N` for each `ℓ` while sharing one `(B(n)−1)^+` is a valid over-estimate.

*Sanity.* `B(n) ≤ 1 ⇒ no carrier divides n ⇒ F(n) = 0`, so (20) is not vacuous at the boundary.

### 7. Lemma 7 (`24 Σ_ℓ ε_ℓ R_ℓ < 4/5`) — **OK** (one editorial factor-2 slip, see R4)

I re-ran `verify_constants.py` (all assertions pass, 0.17 s) **and** re-derived every number with my own
independent exact-Fraction code, computing `C_ℓ(N)` by three separate methods (generating function,
brute-force enumeration, and the recurrence (22), which I also re-derived from `f g' = N f' g`):

| ℓ | argmax N | R_ℓ | 24 ε_ℓ R_ℓ (exact→float) | cap |
|---|---|---|---|---|
| 1 | 2 | 1 | 0.50196365 | 51/100 |
| 2 | 3 | 14 | 0.23913218 | 6/25 |
| 4 | 10 | 440.571… | 0.028876423 | 3/100 |
| 8 | 23 | 1.43637e6 | 0.0038936588 | 1/250 |
| 16 | 49 | 3.80058e13 | 0.00049672086 | 1/2000 |
| 32 | 100 | 7.12633e28 | 6.1130432e-05 | 1/16000 |
| 64 | 202 | 6.81231e59 | 7.1139832e-06 | 1/100000 |

All 417 `N`-cases (5+8+14+27+53+104+206 = 417, matching the transcript's count) are exact. Sum of caps
`= 313829/400000`; `+ 1/100 = 317829/400000 = 0.7945725 < 4/5`. ✔

Analytic tail, all verified exactly:
- `Σ_{k≤6} 1/k! = 1957/720` and `Σ_{k≥7}1/k! ≤ (1/5040)(8/7) = 1/4410`, so `e < 1957/720 + 1/4410 =
  2.71828231… < E = 87/32`. ✔
- `g(1/4) = 1 + Σ_i 4^{−2^i} ≤ 1 + 1/4 + 1/16 + 1/256 + 1/65535 = 1.31642151 < f = 2633/2000`; I also
  computed `g(1/4)` exactly for every `ℓ ≤ 1024` and it is `< f` in each case. Hence
  `C_ℓ(N) ≤ g(1/4)^N/(1/4)^{ℓ+1} ≤ 4^{ℓ+1} f^N` (23). ✔
- `r! ≥ (r/e)^r` with `r = 9ℓ/2` gives `ε_ℓ ≤ (γ/ℓ)(2eH*/9)^{9ℓ/2} ≤ (γ/ℓ)ζ^ℓ` (24). ✔
- `2EH*/9 = 29725/49152` exactly. (26a) `4^16 f^51 (2EH*/9)^72 = 0.9936469… < 1`; (26b)
  `16 f^4 (2EH*/9)^9 = 0.5200313… < 9/16`. These are equivalent to (25) by raising to the 16th and 2nd
  powers respectively (both sides positive), which is correct. ✔ **(26a) has only a 0.64 % margin — it is
  the single tightest inequality in the paper.**
- (27): for `N < 2ℓ`, `1/denominator ≤ ℓ`, `clip ≤ 1`, `C_ℓ(N) ≤ 4^{ℓ+1}f^{2ℓ}`, giving
  `24 ε_ℓ R_ℓ(N) ≤ 96γ(4f²ζ)^ℓ ≤ 96γ(3/4)^ℓ`. ✔
- (28): for `N ≥ 2ℓ`, `clip = q/(Kℓ)` with `q = L − N`, `ℓ/(N−ℓ) ≤ 1`, `C_ℓ(N) ≤ 4^{ℓ+1}f^{L−q}`, and
  `q f^{−q} ≤ q(4/5)^q ≤ 1024/625 < 2` (max at `q ∈ {4,5}`; I checked `q ≤ 200`). ✔
- (29): `Σ_{j≥0}(3/4)^{128·2^j} ≤ x/(1−x)` with `x = (3/4)^128` (since `2^j ≥ j+1`), and
  `Σ_{j≥0} 192γf/(K(128·2^j)²) = 256γf/(K·128²)`; total `0.0094037 < 1/100`. ✔

**Repair R4 (the only actual defect).** In (28) the transcript displays
`R_ℓ(N) ≤ 4^{ℓ+1} f^L/(Kℓ)`. That is *false as written* — the correct bound is
`R_ℓ(N) ≤ 2·4^{ℓ+1} f^L/(Kℓ)`, the 2 coming from the `q f^{−q} ≤ 2` stated one clause earlier. The
displayed form would give `96γf/(Kℓ²)`, not `192γf/(Kℓ²)`. **The stated conclusion `192γf/(Kℓ²)` is the
correct one and is what the script and the sum (29) use**, so the slip is confined to the intermediate line
and changes nothing downstream. Fix: insert the factor 2 in that display.

**Independent adversarial check of the tail.** I computed the *true* `24 ε_ℓ R_ℓ` exactly for
`ℓ = 128, 256, 512, 1024, 2048`: `7.55e-7, 6.72e-8, …`, total `8.26e-7`, against the claimed tail bound
`< 1/100`. The tail bound is valid and enormously conservative (the argmax there is `N ≈ 3.17ℓ ≥ 2ℓ`, i.e.
branch (28) is the binding one, as the proof assumes).

### 8. Lemma 8 (window value, sign convention, `62248/30583`) — **OK**

`N_I(P_C) ≥ ⌊m/P_C⌋ = ν_C` for any window of `m` consecutive positive integers, so the positive part gives
`24 Σ_C c_C ν_C = 24 Σ_C M_C = 24 L_B`.
**The sign convention is right.** Positive coefficients are bounded below by `⌊m/d⌋`; negative
coefficients are bounded using an **upper** bound on their multiplicity count,
`N_I(P_C p^j) ≤ m/(P_C p^j) + 1 ≤ 2m/(P_C p^j)` (valid because `P_C p^j ≤ m`, established in Lemma 6). This
is the correct direction for a lower bound on `Σ_I F`; the harvest applies "(32)–(33) to the negative terms
of (18)".
`m/(P_C ν_C) = x/⌊x⌋ ≤ x/(x−1) ≤ Q/(Q−1) = γ` for `x = m/P_C ≥ m^{1/3} ≥ 2^16` (needs `m ≥ 2^48`, supplied
by Lemma 2). The prime-power mean of `U_C`, i.e. `Σ_{p∤P_C,j} δ^{(θ_C)}_{p,j}/p^j`, is
`≤ H(min(b,θ)) ≤ H(B) ≤ H < H*` by (4).
Combining: negative part `≤ (48/K)γH* Σ_C M_C`, hence `Σ_I F ≥ 24(1 − 2γH*/K)L_B`.
Exact: `24(1 − 2·(65536/65535)·(1025/1024)/(35/16)) = 62248/30583 = 2.035379… > 2`. Verified as a Fraction
identity, matching (31).
One step the transcript leaves implicit and that `sec_signed.tex` states explicitly: it is legitimate to
bound the terms *before* combining equal moduli into `λ_d`, because `Σ_I F = Σ_{terms} c·N_I(mod)` is linear
in the terms and each `N_I` is a fixed number. **Repair R5 (editorial):** carry that sentence over.

*Empirical.* On the 18-prime instance I recomputed the certificate's window value on `I = [1,m]` from the
divisor decomposition: `Σ_{k≤m}F = 2.0796e26 ≥ (62248/30583)L_B = 2.0329e25` (ratio 20.8). On the
`z = 1/2` instance: ratio 22.8. Both satisfy (31) with room. I also reproduced the audit table's
**"91 carriers, 819 aggregated coefficients"** exactly (91 positive moduli + 728 distinct negative moduli
`P_C·p` = 819), and the audit's `Σ_{k≤m}(S−17)^+ = 1` at
`m = 24007196555611299010593464005603 = ∏(23…101)`. The author's audit was evidently really run.

### 9. Lemma 9 (composition; exhaustiveness of the three branches) — **OK**

`Σ_{k≤m}(S−17)^+ = Σ(S_0−17)^+` (5) `≤ 2L_B` (11) `≤ (30583/31124)Σ_I F` (from (31))
`≤ (30583/31124)(4/5)Σ_I(B−1)^+` (30) `= (30583/38905)Σ_I(B−1)^+ ≤ Σ_I(S−1)^+`, the last step by
`B ≤ S_0 ≤ S` pointwise (valid for every positive integer, in particular for window elements `> m`).
`2/(62248/30583)·(4/5) = 30583/38905 = 0.78609… ≤ 1`, verified exactly.
Branches: `m < 2^48` (Lemma 2, left side is 0); `m ≥ 2^48` and `H ≥ H*` (Lemma 3); `m ≥ 2^48` and `H < H*`
(Lemmas 4–8). Exhaustive and mutually consistent — `H := H(S_0)` is used with the same meaning in both
branches, and `H < H*` is used exactly where needed (`ε_ℓ` in Lemma 5, `H_θ ≤ H*` in Lemma 8).

*I also ran the end-to-end target inequality on both concrete instances with `I = [1,m]`: LHS 1 vs
RHS ≈ 4.1e30 (18-prime), and LHS 0 (z=1/2 instance). Both hold, as expected — these are weak tests, but they
confirm the bookkeeping.*

### 10. Coverage of the original weights, and `g(n) ≤ 33n` — **OK**

The theorem is stated for arbitrary atom systems `α_{p,j} ≥ 0`, `Σ_j α_{p,j} ≤ 1`, which is strictly more
general than the original weights. `main.tex:1202` defines exactly the required atoms:

> `\alpha_{p,j}:=\min(jz_p,1)-\min((j-1)z_p,1)\ \ (j\ge1),\qquad\text{so that}\qquad \alpha_{p,j}\ge0,\quad \sum_{j}\alpha_{p,j}\le1,\quad`
> `S(n)=\sum_{p}\sum_{j\ge1}\alpha_{p,j}[p^j\mid n].`

and `main.tex:1205`:

> `We call the $\alpha_{p,j}$ the \emph{atoms} of $z$; the results of this section use only $\alpha_{p,j}\ge0$ and $\sum_j\alpha_{p,j}\le1$.`

The atoms are finitely supported in `j` (they vanish once `(j−1)z_p ≥ 1`), so "finite atom system" is
satisfied. So (H_17) for atom systems ⇒ (H_17) for `S(n) = Σ_p min(z_p v_p(n),1)`.

Passage from `S` to `w_z`, `main.tex:1200`:

> `recall that the hinge inequality for $S$ with threshold $c$ implies it for $w_z$ (the peel $w_z=E+S$).`

and the peel identity, `main.tex:847`:

> `$w_z=E+S$ with $S(n)=\sum_p\min(z_p\vp_p(n),1)$ and $E=\sum_p(z_p\vp_p(n)-1)^+$, one has $(w_z-1)^+=E+(S-1)^+$ (if $S<1$ then every $z_p\vp_p<1$, so $E=0$),`
> `$(w_z-c)^+\le E+(S-c)^+$, and $\sum_IE\ge\sum_KE$ because $(z_p\vp_p(n)-1)^+=\sum_{j\ge1}\Delta_{p,j}[p^j\mid n]$ with nonnegative increments`

I checked the peel: `(E+S−c)^+ ≤ E+(S−c)^+` since `E ≥ 0`; `Σ_I E ≥ Σ_{k≤m} E` since `E` is a nonnegative
divisor sum and `N_I(d) ≥ ⌊m/d⌋`. So it is valid for every `c ≥ 1`, in particular `c = 17`.

Conditional theorem, `main.tex:602–608`:

> `If $a_n\ge8n^3$, Theorem~\ref{thm:long} gives $2n\le18n$ elements. Otherwise let $z$ be a maximiser in Lemma~\ref{lem:dual} with $z_p\le1$... Since $w_z(a)\le2+(w_z(a)-2)^+$ and $A\subseteq[1,m]$,`
> `\sum_{a\in A}w_z(a)\le 2n+\sum_{k=1}^{m}\bigl(w_z(k)-2\bigr)^+\le 2n+\sum_{b\in I}\bigl(w_z(b)-1\bigr)^+`
> `by \eqref{eq:TH}, so $\tau^*\le2n$. Lemmas~\ref{lem:round} and~\ref{lem:fewprimes} give $|B|\le 2n+16n-1<18n$.`

and `main.tex:1259` confirms the substitution is licensed:

> `The bound on $g(n)$ follows as in Corollary~\ref{cor:lnln}: the proof of Theorem~\ref{thm:cond} with threshold $65$ in place of $2$ gives $g(n)\le(65+16)n$.`

With `c = 17`: `w_z(a) ≤ 17 + (w_z(a)−17)^+` gives `τ* ≤ 17n`, and `|B| ≤ τ* + |𝒫| ≤ 17n + 16n − 1 < 33n`;
for `a_n ≥ 8n^3`, `2n ≤ 33n`. So **(H_17) ⇒ g(n) ≤ 33n**, as claimed. ✔

---

## What would have to be true for the proof to fail

Concretely, one of the following would have to hold. I probed each and found none.

1. **Lemma 1.** The multi-affine minimum principle (`f(u) = E[f(Bernoulli)]`) would have to fail, or some
   vertex value `C(j,4) − 2j + 7` would have to be negative. (2) is the pressure point: replacing `e_4/2`
   by `e_4` doubles `24ε_1R_1` to `1.004` and blows the 4/5 budget on its own. `j = 4` gives exactly 0 —
   the inequality is tight and has no slack to spare, but it is correct.
2. **Lemma 1 (3).** Two atoms of the *same* prime would have to be multiplied inside the `e_r` expansion
   (their moduli are not coprime and `⌊N/lcm⌋` is much larger than `N/product`). This would break the
   moment bound entirely. It does not happen because `e_r`'s coordinates are indexed by primes.
3. **Lemma 5.** A carrier could have `μ(C) ≠ 1 + θ_C` — this needs the level values to fail to be integer
   multiples of `θ`, i.e. non-dyadic rounding, or `θ` not the minimum of the prefix. If `μ(C)` could exceed
   `1+θ`, the scaled total in `C_ℓ(N)` would exceed `ℓ+1` and the generating-function count would be wrong.
4. **Lemma 5.** Some prime `p ∤ P_C` could have `b_p(k) > θ_C` at an assigned `k`, breaking `u_p ∈ [0,1]`
   in the hinge. This is prevented by the decreasing-value ordering, but it is the step most sensitive to
   the tie-breaking convention.
5. **Lemma 6.** Two distinct carriers with the same `θ` could share a choice vector while both dividing
   `n`, making `C_ℓ(N)` an under-count. This is the step whose written justification is weakest (see R3);
   the reconstruction I give closes it.
6. **Lemma 6.** A carrier could use a prime with `b_p(n) < θ_C` while dividing `n` (then `N` would be too
   small). Excluded by monotonicity of `b_p` in the valuation.
7. **Lemma 8.** A negative modulus `P_C p^j` could exceed `m`, invalidating `N_I ≤ 2m/(P_C p^j)`. This
   needs `P_C ≤ m^{2/3}` and `p^j ≤ m^{1/3}`, i.e. the cutoff exponent `3` in `q^{3/t} ≤ m`. Weakening the
   cutoff to a larger exponent would also raise the loss from 6 in (10); the pair `(3, 6)` is exactly at
   the boundary `m^{2/3}·m^{1/3} = m`.
8. **Lemma 7 numerics.** Three inequalities have thin margins and a mis-stated constant would flip them:
   `4^{16}f^{51}(2EH*/9)^{72} = 0.99365 < 1` (0.64 % margin); the total `0.7945725 < 0.8` (0.7 %);
   `62248/30583 = 2.0354 > 2` (1.8 %). All three are exact rationals and I verified them independently, so
   the only way they fail is if the *derivation* attaching them to `ε_ℓ`, `R_ℓ` or the window count is
   wrong — checked in items 5–8 above.
9. **Branch bookkeeping.** `H` would have to mean something different in Lemma 3 (`H(S_0)` before scaling)
   than in Lemmas 4–8. It does not; and the three branches (`m < 2^48`, `H ≥ H*`, `H < H*`) partition all
   cases.

## Caveats on scope of this review

- I refereed the **transcript** in `erdos708_r17_pro.md`. The chat attachments (`PROOF.md`,
  `audit_independent.py`, SHA-256 manifest) were not present locally and were not reviewed; the audit-table
  claims I could reconstruct (`m`, LHS = 1, 91 carriers, 819 coefficients) all reproduced exactly, which
  raises my confidence in the ones I could not (`19,656` fractional instances, CRT/reflected windows).
- The transcript is a compressed proof sketch, not a paper. Repairs R1–R5 are what a full write-up must
  add; none of them is a mathematical gap, but a Lean formalisation will need all of them spelled out,
  especially R3 (carrier ↔ product ↔ choice-vector bijection) and R5 (bound terms before aggregating
  moduli), which are the two places where the transcript asserts rather than argues.
- There is **no Lean verification of the threshold-17 argument yet** — the Lean development cited in
  `sec_signed.tex` covers threshold 65 only. The claim `g(n) ≤ 33n` is at present machine-checked only at
  the level of the numerical Lemma 7 (which I have now independently re-verified by three methods).
