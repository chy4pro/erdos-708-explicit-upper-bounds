(A) K4 for {2,3,5,7}, every integer Q >= 2 — **CONFIRMED**
(B) Uniform K4 for every four-prime support once Q >= 4900014488437221682 — **CONFIRMED**
(C) (H_2) for arbitrary multilevel atom systems supported on {2,3,5,7,p} (and any subset) — **CONFIRMED**

---

# Blind adversarial referee report

Target: `engine/out/astra_708_h2/report.md`, claims A1–A4 and the refuted intermediates B1, B2.
Referee scripts: `engine/out/astra_708_h2/referee_checks.py` (`python3 -B referee_checks.py all`).
Nothing in `final_verify.py`, `final_constants.json`, `final_verification.log`,
`route_tests.py`, `frontier_complete_2357.json`, `antichain_tail.json` or
`route_obstructions.json` was imported or trusted. Every number below is my own,
in exact integer / `Fraction` arithmetic, from two or three independent
implementations that agree.

The document's third claim (the threshold `280923567/32000000`) is out of scope
and was not refereed; I flag below only the few places where its machinery is
reused verbatim from already published sections.

I did **not** inherit the brief's three scope errors. I confirm all three were
scope errors and that the report's own corrections (its "Claim ledger and
corrections to the brief", and `routes.md` "Source audit") are the correct
readings of the published text:

* `cor:fivesurviving` in `sec_remains.tex` establishes "at least two multilevel
  primes" and "some prime of weight > 1/2" **only for at most five active
  primes**; the general remaining case (`prop:remains`) has neither clause. The
  paper's own nonempty example (m = 210, atoms 2, 4, 3, 13, 19, 23, 29) has six
  active primes and exactly one multilevel prime (2), so it is not in the
  strengthened region — the report is right and the brief was wrong.
* The five-prime certificate of `thm:fiveprimes` is pointwise **at most**
  `(S-1)^+` and dominates `(S-2)^+` **only after prefix summation**
  (`rem:aftersum`). I reproduced the published witness of this exactly: see
  §5.3 below.

---

## 1. Summary table

| Claim | Verdict | My exact value | Independent? |
|---|---|---|---|
| A1 — uniform tail, all quadruples, `Q >= Q0` | CONFIRMED | `Q0 = ceil(A^5) = 4900014488437221682`, `A = 7812500000000/1428073491` | yes, 2 ways |
| A2 — exact frontier sweep for `{2,3,5,7}`, `2 <= Q <= Q0-1` | CONFIRMED | `max = 101/105` at `Q = 2`; 1763328 states, 35109 intervals | yes, 3 ways |
| A1 + A2 — K4 for `{2,3,5,7}`, all `Q >= 2` | CONFIRMED, join is gapless | see §2.4 | yes |
| A3 — four-prime base | CONFIRMED but **already published** verbatim in substance | — | yes |
| A4 — elimination with multilevel `T` and multilevel fifth prime | CONFIRMED | certificate reproduced exactly, incl. the published `n = 12705` deficit | yes |
| B1 — layer majorant refuted | CONFIRMED | 551993 > 500000; `mu = 87143/50000`, `mu - H^2/6 = 1.23660 > 1` | yes |
| B2 — old retention rule refuted at c = 2 | CONFIRMED, and **stronger than stated** | `sup B = 5/256` (old rule); `117/256` (the campaign's *new* table) | yes |
| B3 — six-prime obstruction | correct, but a **verbatim re-proof** of `prop:sixobstruction` | — | proof re-read |

**My own maximum of the K4 left-hand side.** For `P = {2,3,5,7}`,

```
max_{Q >= 2 integer}  Q * sum_{e in A_P(Q)} D(e)^{-1}  =  101/105  =  0.9619047619047619...
```

attained **uniquely at Q = 2**, where `A_P(2)` is exactly the six vectors with
two coordinates equal to 1 and `sum 1/D = 1/6+1/10+1/14+1/15+1/21+1/35 = 101/210`.
The runner-up values are

```
Q=2  101/105 = .961904762     Q=7  1591/1800 = .883888889
Q=4  299/315 = .949206349     Q=6  1811/2100 = .862380952
Q=3  131/140 = .935714286     Q=14 10349/12600 = .821349206
Q=5   65/72  = .902777778     Q=12  3963/4900 = .808775510
```

Note that `Q = 4` beats `Q = 3`: the maximiser is not simply "the smallest Q".
The margin to 1 is `4/105 = 3.81%`, matching `rem:K4`'s "under 4%".

---

## 2. Claim (A): K4 for the fixed support {2,3,5,7}, every integer Q >= 2

### 2.1 Finiteness of `A_P(Q)`

`F(e) = D(e)/max_i p_i^{e_i} = min_i prod_{j != i} p_j^{e_j}`, a minimum of
coordinatewise-nondecreasing functions, hence itself coordinatewise
nondecreasing. `{F >= Q}` is therefore an up-set in `N^4`, and its minimal
elements form a finite antichain (Dickson). The report proves finiteness only
implicitly, through its ladder box for `Q <= B`; the same box argument with a
`Q`-dependent ladder gives it for every `Q`. **Sound; one implicit line.**

### 2.2 The ladder-box lemma

*Claim (A2, as written): a minimal feasible `e` for `Q <= B` has
`p_i^{e_i}` on the ladder `1, p_i, ..., p_i^{L_i}` where `p_i^{L_i}` is the least
power `>= B`.*

I re-derived it and it is correct, with a cleaner one-line proof than the
document's case split. If `e_i > L_i` then `p_i^{e_i-1} >= B >= Q`; write
`e' = e - 1_i`. Then `F(e') = min_k prod_{l != k} p_l^{e'_l}`; the `k = i` term
equals `prod_{l != i} p_l^{e_l} >= F(e) >= Q`, and every `k != i` term contains
the factor `p_i^{e_i-1} >= Q`. So `F(e') >= Q`, contradicting minimality. **Correct.**

Ladder sizes for `B = Q0-1 = 4900014488437221681` are `64 x 41 x 28 x 24 =`
**1763328** states — exactly the document's figure. (Cosmetic: the document says
"exponent ladder from 1"; it must be from 0, and the count confirms it is.)

### 2.3 The sweep, recomputed three independent ways

1. **Definition, box-free.** Enumerate `e` in `{0,...,14}^4`, form the feasible
   up-set, extract its minimal elements directly, sum `Q/D`. This uses no ladder
   lemma at all. Agrees with (2) for every `Q = 2, ..., 80`.
2. **Ladder brute force** (`K_at`), one `Q` at a time. Exhaustive over
   `Q = 2, ..., 4000`: max `101/105` at `Q = 2`. Also computed pointwise at
   `Q = 10^3, 10^4, 10^6, 10^9, 10^12, 10^15, 10^18, Q0-1, Q0, 10^19, 10^20`.
3. **My own event sweep** (independent re-implementation of the interval /
   prefix-sum argument).

Cross-validation against the *published* numbers in `rem:K4`, which I recomputed
from scratch: `K_{2,5,7,11}(3) = 111/220`, `K_{3,5,7,11}(3) = 236/385`,
`K_{2,5,7,11}(4) = 37/55`, `K_{2,3,5,7}(2) = 101/105`. All four match the paper
exactly. The sweep's top-12 list also matches the brute force value for value.

**Sweep results (mine):**

| limit | max | at Q | ladder states | intervals | time |
|---|---|---|---|---|---|
| `10^5` | `101/105` | 2 | 13608 | 1007 | <1 s |
| `Q0-1 = 4900014488437221681` | `101/105` | 2 | **1763328** | **35109** | 1.7 s |
| `10^20` | `101/105` | 2 | 2193000 | 42562 | 2.1 s |
| `10^25` | `101/105` | 2 | 5264730 | 80692 | 5.4 s |
| `10^30` | `101/105` | 2 | 10523392 | 136626 | 11.3 s |
| `10^40` | `101/105` | 2 | 32928490 | 315696 | 41 s |
| `10^60` | `101/105` | 2 | 159901128 | 1038326 | 253 s |

The state and interval counts at `Q0-1` reproduce the document's
`frontier_complete_2357.json` **exactly** (1763328 / 35109 / `101/105` / `Q=2`).
Well beyond the documented range — out to `Q <= 10^60`, twelve orders of
magnitude past `Q0` — the maximum is unchanged.

### 2.4 The join between A2 and A1: no gap, and a large margin

A2 covers integers `2 <= Q <= Q0 - 1`; A1 covers `Q >= Q0`. `Q0 - 1` and `Q0`
are consecutive integers and the sweep's limit is set to exactly `Q0 - 1`.
**No gap.** The join is not even close to tight: my brute force gives

```
K_{2,3,5,7}(Q0-1) = K_{2,3,5,7}(Q0) = 2.318e-6,
```

against A1's guarantee of `<= 1` there — about 5.6 orders of magnitude of slack.
Any `Q0` in a wide range would have done.

### 2.5 A free strengthening the report does not claim

The report states, correctly and cautiously, "The claim 101/105 here is the
finite-range maximum; the analytic tail is only bounded by 1." This is
improvable at zero cost. `Q^{-1/5} A <= 101/105` as soon as
`Q >= ceil((105A/101)^5) = 5950274354636540380`, and my exact sweep to that
(slightly larger) limit still returns `101/105` at `Q = 2`. Hence:

> **The maximum of `K_{2,3,5,7}(Q)` over ALL integers `Q >= 2` is exactly
> `101/105`, attained at `Q = 2` and nowhere else.**

(Same ladder box, 1763328 states, 35571 intervals.) For real `Q >= 2` the same
holds, since `A_P(Q) = A_P(ceil Q)` and `Q <= ceil Q`.

### 2.6 Verdict (A)

**CONFIRMED.** The mathematics is correct, the finite computation is correct and
reproducible, and the join with A1 is gapless with enormous slack. The trust
boundary — an exact big-integer computation over 1.76 million states, not kernel
checked — is stated honestly by the report, and is now discharged by three
mutually independent implementations (mine plus the campaign's) agreeing
exactly.

---

## 3. Claim (B): uniform K4 for `Q >= 4900014488437221682`

Every step re-derived and re-checked:

1. `max_i p_i^{e_i} >= D^{1/4}`, hence `F(e) <= D^{3/4}`. Verified exactly
   (`F^4 <= D^3`) on 20000 random lattice points.
2. `F(e) >= Q` therefore forces `Q^{4/3} <= D`, which is **exactly** equivalent
   to `Q/D <= Q^{-1/5} D^{-1/10}` (both sides to the 15th power: `Q^{12} <= D^9`).
   The document states the conclusion without the equivalence — one implicit line.
   Verified exactly on the same 20000 points.
3. Enlarging the sum over minimal `e` to all of `N^4` and factorising gives
   `K_P(Q) <= Q^{-1/5} prod_{p in P} (1-p^{-1/10})^{-1}`.
4. Rational bounds `p^{-1/10} <= a/10000` with `a = 9331, 8960, 8514, 8232` are
   certified by `p * a^10 > 10000^10`. **All four hold** (I checked; the `p = 7`
   one is the tight one, `7^{-1/10} = 0.82317... < 0.8232`).
5. `A = prod 10000/(10000-a) = 7812500000000/1428073491 = 5470.6568...`, and
   `ceil(A^5) = 4900014488437221682` exactly as claimed, with
   `A^5 <= Q0` and `A^5 > Q0 - 1`.
6. **Implicit step the report only gestures at:** `(1-p^{-1/10})^{-1}` is
   decreasing in `p`, so for four *distinct* primes sorted increasingly
   `p_1 >= 2, p_2 >= 3, p_3 >= 5, p_4 >= 7` and `A` is the extremal value. The
   report writes only "In increasing prime order `p_i >= 2,3,5,7`"; a paper needs
   the monotonicity sentence. I verified numerically that the true
   `{2,3,5,7}` product is `5459.905... <= A`.
7. `Q >= ceil(A^5)` gives `Q^{-1/5} A <= 1`.

**Verdict (B): CONFIRMED.** It is a tail theorem only, as the report says.

**Two things the report leaves on the table (referee additions, verified):**

* *No computation at all is needed for quadruples of large primes.* `31^10 < 10^15`,
  so `p >= 10^15` gives `p^{-1/10} <= 1/31` and `A_P <= (31/30)^4`; and
  `31^20 < 2 * 30^20`, i.e. `A_P^5 <= (31/30)^20 < 2 <= Q`. Hence
  **K4 holds for every `Q >= 2` for every four-prime support all of whose primes
  exceed `10^15`**, with no sweep. What is genuinely open is only the *uniform*
  statement over the infinitely many quadruples containing a prime `<= 10^15`.
* *Every individually named quadruple is decided in about a second.* `Q0` does not
  depend on `P`, and for every quadruple the ladder to `Q0-1` has at most
  `64 x 41 x 28 x 24` states — `{2,3,5,7}` is the *largest* case. I ran the sweep
  to `Q0-1` for **all 70 four-element subsets of `{2,3,5,7,11,13,17,19}`** in 36
  seconds; all pass, with global maximum `101/105` at `{2,3,5,7}`, `Q = 2`.
  So (C) below in fact holds for `{q1,q2,q3,q4,p}` for every one of those 70
  quadruples and every fifth prime `p`, not just for `{2,3,5,7}`. The report's
  sentence "It does not settle K4 for arbitrary prime quadruples" is true but
  undersells the method badly. (Amusing datum consistent with `rem:K4`:
  `{11,13,17,19}` attains its maximum `70/221` at `Q = 11`, not `Q = 2`.)

---

## 4. Claim (C): (H_2) for arbitrary multilevel systems on {2,3,5,7,p}

### 4.1 The layer identity (A4 eq. 27)

`(T+f-a)^+ - (T-a)^+ = int_0^1 [f>t][T>a-t] dt` for `0 <= f <= 1`. Correct:
`u -> (T+u-a)^+` has a.e. derivative `[u > a-T]`, integrate from `0` to `f`, and
`[f>t][T>a-t] = [t<f][t > a-T]`. Equality points are a null set. This is the
identity already in `thm:fiveprimes`.

### 4.2 The coprimality use

`[f(n)>t]` is a single divisor indicator `[d(t) | n]`, `d(t) = p^{j(t)}`, because
`f(n) = A_{v_p(n)}` with `A` nondecreasing and `A_0 = 0`. Since `p` is a *fifth*
prime, `gcd(d(t), 2·3·5·7) = 1` and `T(d(t)k) = T(k)`, which is what turns the
prefix count into a count over `u <= M = floor(m/d(t))`. **Correct, and the only
place coprimality is used.** (Implicit: `p` must not lie in `{2,3,5,7}`; if it
does the system has at most four primes and A3 applies.)

### 4.3 The counting step — the one genuinely new step

This is the whole content of the upgrade, and it does tolerate an arbitrary
multilevel `T`. In detail:

* `c_t = 1-t in (0,1)` for `t in (0,1)`, and `T(1) = 0 < c_t`, so the least
  four-prime divisor `Q(t)` with `T`-value `> c_t` satisfies `Q(t) >= 2` and is an
  **integer** — exactly the hypothesis K4 needs. The report asserts `Q(t) >= 2`
  without the reason; one implicit line.
* If `T(u) > c_t + 1`, let `e_i = min(v_{p_i}(u), J_i)` be the capped valuations.
  Then `T(e) = T(u)` and `D(e) | u`. For each `i`, the divisor
  `d_i = prod_{j != i} p_j^{e_j}` has `T(d_i) = T(e) - f_i(e_i) > c_t + 1 - 1 = c_t`
  **because `f_i <= 1` (the per-prime capacity)** — this is where the multilevel
  generality costs nothing, since `f_i <= 1` holds whatever the level structure
  is. By minimality of `Q(t)`, `d_i >= Q(t)`, so `F(e) = min_i d_i >= Q(t)`, i.e.
  `e` is K4-feasible at `Q = Q(t)`, and it dominates some minimal `e'` with
  `D(e') | D(e) | u`.
* Union bound + K4: `#{u <= M : T(u) > c_t+1} <= sum_{e' min} floor(M/D(e'))
  <= M sum 1/D(e') <= M/Q(t)`, an integer, hence `<= floor(M/Q(t))`.
* `floor(floor(m/d)/Q) = floor(m/(dQ))` (implicit, standard), and
  `N_I(dQ) >= floor(m/(dQ))` for **every** modulus, including `dQ > m` — unlike
  the signed family of G6 there is no modulus-size side condition here, because
  every coefficient is nonnegative. Worth saying explicitly.

I also stress-tested this step in isolation, since it is the crux: 1799
instances of `#{u <= 400000 : T(u) > c+1} <= floor(400000/Q(c))` over random
multilevel `T` on `{2,3,5,7}` with up to three levels per prime and denominators
up to 720. **No violation**; tightest observed ratio `count/bound = 0.6857`.

### 4.4 The cell decomposition

The report partitions `(0,1)` at the cumulative levels of `f` and at the values
`1 - T(e)`. This is exactly right, and the reason deserves a sentence a reader
will otherwise hunt for: the cells only need `d(t)` and `Q(t)` constant, because
the count bound `<= floor(m/(d(t)Q(t)))` is proved *for each `t` separately*.
The count itself is **not** constant on a cell (its breakpoints are at
`t = 2 - T(e)`), and a reader looking for constancy of the count will think the
partition is wrong. It is not.

### 4.5 The four-prime base A3

`G0 = (1/3) sum_{i<j} (f_i+f_j-1)^+` with `G0 >= (S-2)^+` (each `f_i` in three
pairs) and `G0 <= (S-1)^+` (three perfect matchings and
`(a-1)^+ + (b-1)^+ <= (a+b-1)^+`), and the convex mixed-difference telescoping
`beta_{a,b} >= 0`. All correct. **This is `prop:fourprimes` of `sec_remains.tex`
verbatim in substance** (see §6).

### 4.6 Computational verification of (C)

I built the A4 certificate `G = G0 + sum_l (v_l-u_l)[d_l Q_l | n]` from scratch
in exact scaled-integer arithmetic and verified its two defining properties over
**full periods**:

* 40 random multilevel systems on `{2,3,5,7,p}`, `p in {11,13,17}`, up to two
  levels per prime, denominators `6..100`, periods up to 400000: pointwise
  `G <= (S-1)^+` and prefix `sum G >= sum (S-2)^+` — **0 failures**.
* 6 adversarial fixtures including the five-halves-at-`p`-and-`p^2` family
  (period 5336100, the family behind `prop:sixobstruction`) and the
  `(99/100, 1/100)` two-level fixture: all pass.
* Direct `(H_2)` stress: **123120** `(system, m, window)` instances over random
  multilevel systems and 60 random and CRT-aligned offsets, plus **207740**
  further instances on four tight families with `m` up to 200000 and offsets up
  to 200000, including the sieve-rich offsets. **No violation anywhere.**

### 4.7 A cross-check that also validates my own code

For the published `rem:aftersum` system (atoms `257/720, 421/720, 563/720,
611/720` at `2,3,5,7`; `293/720, 427/720` at `11, 11^2`), my independently built
A4 certificate has moduli/coefficients (in units of `1/2160`)

```
10:100  14:148  15:264  21:312  35:454  55:408  66:345  110:126  242:771  363:492  605:18
```

and takes the value `G(12705) = 1948/2160` while `(S(12705)-2)^+ = 2625/2160`.
Both numbers are **exactly** those printed in `rem:aftersum`. This
simultaneously (i) validates my certificate builder against the published
construction, and (ii) confirms the brief's third scope error: the certificate
is pointwise below `(S-1)^+` and above `(S-2)^+` only after summation.

### 4.8 Verdict (C)

**CONFIRMED.** The elimination argument genuinely tolerates an arbitrary
multilevel fifth prime *and* an arbitrary multilevel structure on `{2,3,5,7}`;
the only hypothesis the four base primes must satisfy is K4 at every integer
`Q >= 2`, which A1+A2 supply. The claimed scope ("and on any subset") is right:
subsets of size `<= 4` fall to A3.

**Consequence the report does not draw, worth stating:** `cor:fivesurviving`
sharpens. A five-active-prime failure of `(H_2)` now additionally cannot have
`{2,3,5,7}` (nor, by §3, any of the 70 quadruples of the first eight primes)
among its primes. After the `m/6` truncation the five smallest possible active
primes are `2,3,5,7,11`, so the *densest* five-prime support is now excluded
outright.

---

## 5. The two refuted intermediates

### 5.1 B1 — unrestricted minimum-divisor layer majorant: witness CONFIRMED

Unit weights on the 20 primes `2,...,71`, `M = 10^6`, `c_t = 1/2`, so `Q = 2`.
Direct sieve: `#{k <= 10^6 : T(k) >= 2} = **551993** > 500000 = floor(M/2)`.
Confirmed to the digit. The exact `mu = 87143/50000 = 1.74286` and
`mu - H^2/6 = 1.23660... > 1`, so — as the report correctly insists — the
witness lies in the affine dense branch of `prop:densetwo` and says nothing
about the sparse remaining case. The report's restraint here is appropriate.

### 5.2 B2 — the published eight-mantissa retention rule at c = 2: witness CONFIRMED, and stronger than stated

`q1 = 2^340, q2 = 3^214, q3 = 5^77, q4 = 7^49`, `m = q1q2q3q4` (300 digits).
All four displayed integer inequalities hold: `q1^3 > m`, `q2^3 > m`,
`q3^6 > m`, `q4^15 > m^2`. Every atom `<= m/6`; `H(S) = 0.0016783 < 1`;
`S(m) = 68/25 > 2`; six active primes, two multilevel — genuinely inside the
corrected sparse remaining case.

Recomputing the published table `E_{9,10}=60, E_11=71, E_12=72, E_13=76,
E_14=80, E_15=88, E_16=96, E_{18..28}=120, E_{30,32}=160, E_{36..64}=240`
(`lem:h883-3`): `eta` is nondecreasing along `D` with maximum `1/3`, the
relevant levels are `60/64` (weights `99/100`), `28/64` (weight `46/100`,
`eta = 1/6`) and `16/64` (weight `28/100`, `eta = 2/15`) — exactly the report's
`1/3, 1/6, 2/15`. Retention drops all of `2,3,5,7`, leaving only `11` and `13`
at level `5/512` each:

```
sup B = 5/256 = 0.01953125 <= 1/50,   while the left hinge at k = m is 18/25 > 0.
```

**Confirmed.** (The report's "at most 1/50" is right; the exact value is `5/256`.)

**Referee addition:** the same witness also defeats the campaign's *own new*
retention table (`E_16 = 95`, `E_28 = 145`, ...). Under it, prime 5 is retained
at level `7/16` but `2, 3, 7` are still dropped, so `sup B = 117/256 < 1` and
there is still no carrier of mass `> 1`. So B2 is not an artefact of the old
constants: it obstructs the whole retention/carrier architecture at `c = 2`,
which is a stronger and more useful statement than the one the report makes.

### 5.3 B3 — six-prime obstruction

Re-read line by line. The argument (`P+T+H <= 5` from the all-ones state;
`4P+T >= 20` from the twenty three-ones states, with multiplicities
`binom(6-s,3-s) = 4,1,0` for supports `2,3,>=4`; hence `3T+4H <= 0`; hence every
surviving pair has a threshold `1`; hence `G = 0` at the all-half state whose
lower hinge is `1`) is correct — and is `prop:sixobstruction` of
`sec_remains.tex` **with the same proof**. The report labels it a "recheck",
which is accurate.

---

## 6. Novelty audit against the published sections and `astra_708_2n.md`

### Genuinely new (not in `sec_remains.tex`, `sec_h883.tex`, `sec_h97.tex`, or the harvest)

* **A1**, the uniform tail `K_P(Q) <= Q^{-1/5} prod (1-p^{-1/10})^{-1}` and the
  cutoff `Q0`. New.
* **A2**, the exact frontier sweep proving K4 for `{2,3,5,7}` at every `Q`. New:
  `rem:K4` states this exact conjecture and says "**It is open**", with
  computations only to `Q <= 4000` for `{2,3,5,7}` and `Q <= 400` for quadruples
  below 60.
* **The multilevel upgrade inside A4** — substituting the exponent-vector K4 for
  `lem:antichain`, and capping the valuation vector. This is the entire delta of
  (C).
* **B1** and **B2**, the two refuted intermediates. New (negative results about
  routes, not in the paper).

### Duplicates already published — should not be presented as new

| Report item | Already published as |
|---|---|
| **A3** (four-prime pair certificate, `G0 = (1/3) sum (f_i+f_j-1)^+`, the three matchings, the `beta_{a,b}` convex telescoping) | `sec_remains.tex`, `prop:fourprimes` — same statement, same proof, same notation |
| **A4's layer identity (27)** and the whole elimination scheme (`d(t)`, `Q(t)`, coprimality, union bound, cell integration) | `sec_remains.tex`, `thm:fiveprimes` |
| **B3** | `sec_remains.tex`, `prop:sixobstruction` |
| The value `101/105`, and that it is attained at `({2,3,5,7}, Q=2)` | `sec_remains.tex`, `lem:antichain` (Boolean case) — the *number* is not new, only the exponent-vector proof is |
| The statement of K4 itself, and the claim that it "would give `(H_2)` for five unrestricted primes", and that it does not iterate to five primes | `sec_remains.tex`, `rem:K4` — verbatim |
| **G1** (2) moment bound and (4) `z^f` bound | `sec_h97.tex` `lem:h97-1`; `sec_h883.tex` preamble |
| **G1** (3), the `e_r`-hinge bound `(sum u_i - a)^+ <= (v-a)/binom(v,r) e_r(u)` | `sec_h883.tex` `A_r(a)`; special case in `prop:densetwo` |
| **G2** primorial truncation and dense branch | `sec_remains.tex` `lem:primorial` + `prop:densetwo` (the report re-runs them with `Q_8 = 9699690` and `H_* = 1000003/1000000` in place of `Q_2 = 6`, `h_0 = 179/100` — new *constants*, same lemmas) |
| **G3–G9** architecture (level set `D`, `eta = E_v/720` retention, carriers, `epsilon_{theta,s}`, `A_theta` in both forms, `lambda_theta`, the `a_0` tail) | `sec_h883.tex` `lem:h883-3` … `lem:h883-7`, with retuned constants. Out of scope for this report, but the report should not read as if the architecture is new — its own header sentence ("G1, G2, the four-prime certificate, and the layer identity are proved below before use") acknowledges this for four items only; the h883 lineage of G3–G9 deserves the same explicit sentence |
| The "corrections to the brief" (R8, R4) | These are corrections of the *brief*, not new mathematics; they restate what `sec_remains.tex` already says |

`engine/harvest/astra_708_2n.md` is entirely about `g(A,x) <= 2n`: the anchor
bound, the shared-prime incidence graph, the pseudoforest / cycle-rank theorem
(`thm:incidence`), and the LP fractional-cover refutation. **No overlap** with
(A), (B), (C), B1, B2, B3. The only contact point is the report's CONDITIONAL
`g(n) <= ceil(cn)+2n` line, which explicitly rests on an external supplied
reduction and makes no new claim.

---

## 7. Every implicit step a paper would need

Grouped by claim; none of these is an error, all are one- or two-line gaps a
referee would ask to have filled.

**(A)**
1. `F(e) = min_i prod_{j != i} p_j^{e_j}`, hence coordinatewise nondecreasing (the report states this; keep it, it is load-bearing twice).
2. `A_P(Q)` is a finite antichain for *every* `Q`, not just `Q <= B`.
3. Minimality is equivalent to `F(e - 1_i) < Q` for each `i` with `e_i > 0` — needs monotonicity, used silently.
4. The ladder runs from exponent **0**, not 1 (the state count 1763328 = 64·41·28·24 confirms it does, but the prose says "from 1").
5. `e = 0` has `ell` undefined (max over the empty set); it is excluded because `u(0) = 1 < 2`. One clause.
6. The K4 statement is for **integer** `Q`. Add the remark that real `Q >= 2` follows since `A_P(Q) = A_P(ceil Q)`.
7. The sweep maximum is at the right endpoint of each constant run because the running sum is nonnegative — stated, keep it.
8. Trust boundary: exact big-integer computation over 1763328 states; not Lean. Stated. I would add the two-independent-implementations remark, which is now true.

**(B)**
9. `Q <= F(e) <= D^{3/4}` and the *equivalence* `Q^{4/3} <= D  <=>  Q/D <= Q^{-1/5}D^{-1/10}` (i.e. `Q^{12} <= D^9`). The report gives only the implication's conclusion.
10. `(1-p^{-1/10})^{-1}` is decreasing in `p`, so a sorted quadruple of distinct primes has `p_i >= (2,3,5,7)_i` and `A` is extremal. The report writes only "In increasing prime order".
11. The exponents `1/5` and `1/10` are one admissible choice among the family `(s,t)` with `(3/4)(1+s) <= 1-t`; `Q0` is therefore not canonical. Worth a footnote so nobody tries to interpret `4900014488437221682`.
12. Convergence/factorisation of `sum_{N^4} D^{-1/10}` (trivial, but say `p^{-1/10} < 1`).

**(C)**
13. The layer identity holds a.e.; equality points are null.
14. `[f>t]` is a *single* divisor indicator because `f = A_{v_p(n)}` with `A_0 = 0` nondecreasing.
15. `Q(t) >= 2` because `T(1) = 0 < c_t = 1-t` for `t in (0,1)`.
16. `T(d_i) = T(e) - f_i(e_i) > c_t` uses the per-prime capacity `f_i <= 1` — the one place the multilevel structure could have hurt and does not.
17. `Q(t)` is attained on the capped state space (T depends only on capped exponents), so the minimum is over a finite set.
18. Capping valuations preserves `T` and keeps `D(e) | n`.
19. Well-foundedness of `N^4`: every feasible vector dominates a minimal one.
20. `T(d(t)k) = T(k)` needs `p not in {2,3,5,7}`; if `p` is one of them the system has `<= 4` primes and A3 applies (this is what "and any subset" means).
21. `floor(floor(m/d)/Q) = floor(m/(dQ))`.
22. `N_I(d) >= floor(m/d)` for **every** `d`, including `d > m`; there is no modulus-size condition here because all coefficients are nonnegative (contrast G6, where `P_C q <= m` is load-bearing).
23. The cells only need `d(t), Q(t)` constant; the count bound is proved for each `t` separately, and the count is *not* constant on a cell. Say so, or readers will think the partition points should be `2 - T(e)`.
24. Keep `rem:aftersum`: `G` is pointwise `<= (S-1)^+` but **not** pointwise `>= (S-2)^+`. My reconstruction reproduces the published counterexample value exactly.

---

## 8. Is each worth a paragraph in "what remains"?

**(A) + (B) + (C) together: YES — one substantial paragraph, replacing the last
half of `rem:K4`.** `rem:K4` currently says the K4 statement "is open" and
"would give `(H_2)` for five unrestricted primes". Both halves can now be
rewritten:

> The bound is now proved for `P = {2,3,5,7}` at every integer `Q >= 2`, by an
> exact frontier sweep over the 1763328 exponent states of the ladder to
> `Q_0 - 1` (35109 nonempty minimality intervals) together with the uniform tail
> `K_P(Q) <= Q^{-1/5} prod_{p in P}(1-p^{-1/10})^{-1} <= 1` for
> `Q >= Q_0 = 4900014488437221682`, valid for every quadruple. The maximum over
> all `Q >= 2` is exactly `101/105` at `Q = 2`. Since `Q_0` does not depend on
> `P` and the ladder for every quadruple is at most as large as the one for
> `{2,3,5,7}`, the same finite computation decides any individually named
> quadruple in seconds — it does so for all 70 four-subsets of the first eight
> primes — and no computation at all is needed when every prime of `P` exceeds
> `10^15`, since then `A_P^5 <= (31/30)^{20} < 2`. Consequently
> Theorem (five primes, one multilevel) upgrades: `(H_2)` holds for arbitrary
> multilevel atom systems on `{2,3,5,7,p}` (and on the analogous supports for the
> other 70 quadruples) for every fifth prime `p`, so a five-prime failure cannot
> have `{2,3,5,7}` — in particular not the smallest admissible support
> `{2,3,5,7,11}` — among its primes. What remains open is the *uniform*
> statement over the infinitely many quadruples containing a small prime, and,
> as before, the passage from five primes to six.

**B1: one sentence, not a paragraph.** It is a useful warning that the layer
estimate is intrinsically an "at most four eliminating primes" tool (its
unrestricted form fails already at 20 primes with `551993 > 500000`), but the
witness is in the dense branch and settles nothing about the sparse case.

**B2: one sentence, in the threshold/`h883` discussion rather than in "what
remains".** With the strengthening I verified — the witness kills both the
published and the campaign's own retention table — it is a clean explanation of
why the signed-carrier architecture cannot simply be re-run at `c = 2`, which is
the single most natural thing a reader will propose. Worth recording with the
exact witness `2^340 3^214 5^77 7^49` and `sup B = 5/256` (old) / `117/256` (new).

**B3: nothing.** It is already `prop:sixobstruction`.

---

## 9. Reproduction

```sh
cd engine/out/astra_708_h2
python3 -B referee_checks.py all          # ~7 min without `sweepbig`/`allquads`
python3 -B referee_checks.py sweepbig     # sweep to 10^25 (add larger limits by hand)
python3 -B referee_checks.py allquads     # all 70 quadruples of the first 8 primes, 36 s
```

Parts: `tail boxfree brute sweep globalmax sweepbig quads allquads b1 b2 cert
layer tight h2`. All arithmetic is `int`/`Fraction`; the only floats printed are
for human reading and no comparison uses them. No file other than
`referee_checks.py` and `referee_opus.md` was written.
