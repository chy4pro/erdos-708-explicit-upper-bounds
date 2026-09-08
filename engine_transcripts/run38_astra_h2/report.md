# Erdős 708 hinge campaign — report

Single agent, 2026-09-08. All campaign writes are in this directory; no git, internet, or sub-agents were used. The global-memory recall tool was unavailable, so no presets or user notice were returned. There was no wall-clock cap. The uniform threshold-2 proof and refutation routes were frozen by the brief's two-unchanged-gap rule before work on the fallback began; the decisions are in `routes.md`.

## Outcome

**PROVED, for every finitely supported atom system, every integer m >= 1, and every window I of m consecutive positive integers:**

\[
\boxed{\sum_{k=1}^m(S(k)-c)^+\le\sum_{b\in I}(S(b)-1)^+,
\qquad c=\frac{280923567}{32000000}=8.77886146875.}
\]

This is the smallest global threshold proved in this campaign. It improves the supplied threshold by

\[
\frac{56501}{6400}-c=\frac{1581433}{32000000}=0.04941978125.
\]

It is **not** claimed to be the optimal threshold, or the optimum over all signed certificates. T1, the universal assertion at 2, and T2, a counterexample at 2, remain **OPEN**. No counterexample was found. Under the reduction supplied in the brief, the new constant gives the sharper real bound `g(n) <= ceil(c n) + 2n`, still at most `11n`. That reduction is an external input; no new Lean or kernel-check claim is made here.

A second result is **PROVED**:

> K4 holds for the fixed prime set {2,3,5,7} for every integer Q >= 2. Consequently H2 holds for arbitrary multilevel atom systems supported on {2,3,5,7,p}, for any fifth prime p (and any subset of these primes).

The fixed-support theorem uses an exact finite computation plus an analytic infinite tail. It does not settle K4 for arbitrary prime quadruples.

## Claim ledger and corrections to the brief

| Status | Statement |
|---|---|
| PROVED | The global threshold c displayed above, by Lemmas G1–G9 below. |
| PROVED | Uniform K4 for Q >= 4900014488437221682, for every four distinct primes; Lemma A1. |
| PROVED | K4 for {2,3,5,7}, all Q; Lemma A2. |
| PROVED | Unrestricted multilevel H2 on {2,3,5,7,p}; Lemmas A3–A4. |
| REFUTED | The unrestricted minimum-divisor layer majorant used as a possible induction step; exact witness in B1. |
| REFUTED | Reusing the published eight-mantissa retention/carrier construction at threshold 2; exact sparse witness in B2. |
| PROVED, finite | No H2 violation in the logged 116424000 full-period window instances and 215838 additional sampled windows. These are not exhaustive in weights or m. |
| OPEN | Universal H2, its refutation, arbitrary-support K4, and any global c below the proved value. |
| CONDITIONAL | The advertised Erdős–Surányi consequence uses the supplied hinge-to-g reduction. The hinge theorem itself has no unproved mathematical hypothesis. |

The brief's R8 strengthens the local paper's remaining-case proposition without justification: “at least two multilevel primes” and “some total weight > 1/2” were established there for **five** primes. R6 gives the cap 2/(N−1) at general N, not 1/2. The listed nonempty example has only one multilevel prime, namely 2. Its asserted membership in the brief's strengthened region is therefore false. This does **not** refute the logical equivalence with H2, which remains undecided. The campaign used the broader, justified remaining case and did not exclude six-prime systems on that basis.

The R4 prose also reverses an inequality: its certificate is **at most** the right hinge pointwise; it is at least the left hinge only after prefix summation. The local paper's displayed argument has the correct inequalities. G1, G2, the four-prime certificate, and the layer identity are proved below before use. R7's obstruction is rechecked in B3. R5 and R6 are not inputs to the new global proof.

## Exact constants and reproduction

Run from the repository root:

```sh
python3 -B engine/out/astra_708_h2/final_verify.py --full
```

This recomputes the new retention budgets, the dense branch, prime-count bounds, all 65 finite scales, the infinite tail, the complete fixed-support frontier sweep, and two actual signed families. `verification_summary.json` records the result. `final_verification.log` retains stdout. Parameter discovery used floating point only to choose rational K values; no floating-point comparison is used in the final proof checks.

The main constants are

\[
\rho=9/8,\quad H_* =1000003/1000000,\quad
D_0=28407/10240,\quad T=5337547/1000000,
\quad c=D_0+\rho T.
\]

The new retention knapsack has maximum numerator **255663**, at cost **699** out of 720 and reward **174** out of 64. One maximizing multiset of levels is `{9/64, 1/2, 15/16, 15/16}`. Thus

\[
D_0=174/64+(243/128)(1-699/720)=255663/92160=28407/10240.
\]

All scale bounds in the following table are rounded **upward** to units of 10^-12. The K row is indexed by j=8,...,15, except L=8, which has only j=8.

| L | K values | Upper bound, in units of 10^-12 |
|---|---|---:|
| 8 | 5 | 49202688506 |
| 16 | 31321/10000, 45/16, 25/8, 55/16, 15/4, 65/16, 35/8, 75/16 | 556370080922 |
| 32 | 301/200, 1137/625, 4887/2500, 18189/10000, 19813/10000, 5443/2500, 3037/1250, 22711/10000 | 272295395378 |
| 64 | 12593/10000, 6817/5000, 7141/5000, 7319/5000, 7491/5000, 2887/2000, 351/250, 8223/5000 | 99464241485 |
| 128 | 2843/2500, 2293/2000, 11893/10000, 12031/10000, 5913/5000, 313/250, 297/250, 6131/5000 | 20807335735 |
| 256 | 17/16, 673/625, 10733/10000, 10783/10000, 1373/1250, 688/625, 10937/10000, 5587/5000 | 1823201370 |
| 512 | 1289/1250, 10371/10000, 10361/10000, 10351/10000, 5157/5000, 10411/10000, 10391/10000, 2647/2500 | 33857407 |
| 1024 | 2539/2500, 10133/10000, 2539/2500, 2041/2000, 2039/2000, 10267/10000, 5127/5000, 5127/5000 | 39181 |
| 2048 | 41/40 at all eight positions | 11 |

The remaining scales L >= 4096 contribute at most

\[
230783/500000000000000=0.000000000461566.
\]

The total pointwise multiplier, including every finite scale and the infinite tail, is at most

\[
\kappa=499998420228283/500000000000000<1,
\quad 1-\kappa=1579771717/500000000000000.
\]

The neighboring parameter `T=2668773/500000=5.337546`, smaller by 10^-6, gives a bound already greater than 1 through L=512 with this K table. That fails this verification criterion; it is not a refutation of its hinge inequality. The retention search found no further improvement after 20000 additional trials, and all 176 feasible single-unit increase/decrease neighbors failed to improve its exact loss. These are local stopping decisions, not a proof of global optimality of the parameters.

## Complete proof of the global threshold

Write `N_I(d)=floor((x+m)/d)-floor(x/d)`. For every positive integer d,

\[
\lfloor m/d\rfloor\le N_I(d)\le\lfloor m/d\rfloor+1.
\tag{1}
\]

An atom system has nonnegative increments at finitely many prime powers, with each prime's total at most 1. Its mean is `H(f)=sum beta_(p,j)/p^j`. All sums and certificates below are finite for each input, even where the bounding scale series is infinite.

### G1 — PROVED: moments and optimized hinges

For per-prime functions f_p with nonnegative prime-power increments and values in [0,1],

\[
\sum_{n\le M}e_r((f_p(n))_p)\le M H(f)^r/r!.
\tag{2}
\]

Indeed, expand e_r in distinct primes and then in their increments. Products of powers of distinct primes are coprime products, so their prefix counts are floor(M/d)<=M/d. The resulting mean sum is e_r((H(f_p))_p), at most H(f)^r/r!: expansion of the rth power contains each distinct-prime monomial r! times and only additional nonnegative terms.

If r>=2 and a>=r−1, set `v=floor(ra/(r−1))`. Then

\[
(\sum u_i-a)^+\le\frac{v-a}{\binom vr}e_r(u),\qquad 0\le u_i\le1.
\tag{3}
\]

The right side minus the left side is concave in each coordinate separately, so replacing coordinates successively by endpoints cannot increase its minimum. At a vertex with h ones, the assertion is the scalar bound `(h−a)^+/binom(h,r) <= (v−a)/binom(v,r)`. For h<r the numerator vanishes. For h>=r with positive numerators, comparison at h and h+1 shows that the ratio decreases exactly when `h>=ra/(r−1)−1`. Thus v is a maximizer, including an adjacent tie when present. This proves (3).

Also, for z>1,

\[
M^{-1}\sum_{n\le M}z^{f(n)}\le\exp((z-1)H(f)).
\tag{4}
\]

Use `z^u<=1+(z−1)u` on [0,1], expand the finite product, apply (2), and bound the resulting finite exponential sum by the full exponential series. Finally, prime-by-prime pointwise domination implies mean domination: average over a common prime-power period, where the mean of an increment at p^j is exactly its weight divided by p^j.

### G2 — PROVED: truncation and the dense branch

Let `Q8=2*3*5*7*11*13*17*19=9699690`, and retain in S0 exactly the atoms q with q Q8<=m. At any k<=m divisible by an omitted q, the cofactor k/q<Q8 has at most seven distinct prime factors, so k has at most eight and S(k)<=8. Hence, for c>=8,

\[
(S(k)-c)^+=(S_0(k)-c)^+.
\tag{5}
\]

At other k no omitted atom contributes. Also S0<=S everywhere. This verifies the required primorial truncation in the form used here.

If H(S0)>=H_*, set V=(H_*/H(S0))S0. Every retained q has floor(m/q)>=Q8, so

\[
\sum_{k\le m}V(k)\ge m\frac{Q8}{Q8+1}H_*.
\]

Using (3) with a=8,r=9 and (2),

\[
\sum_{k\le m}\min(V(k),8)\ge
m\left(\frac{Q8}{Q8+1}H_*-\frac{H_*^9}{9!}\right)>m.
\tag{6}
\]

The exact excess in parentheses over 1 is

\[
\frac{496637626800278117001816656668266990958247355430755221982047}
{3519823870080000000000000000000000000000000000000000000000000000000}>0.
\]

Since c>8 and S0>=V, its truncated sum `sum min(S0,c)` is at least m. Consequently

\[
\sum_{k\le m}(S_0(k)-c)^+
\le\sum_{k\le m}S_0(k)-m
\le\sum_{b\in I}(S_0(b)-1)
\le\sum_{b\in I}(S(b)-1)^+.
\]

The middle step uses (1) separately on the nonnegative atom increments. The affine certificate here is the explicit finite signed family `S0−1`: a coefficient −1 on modulus 1 and the S0 weights on their prime powers. It is pointwise below the right hinge. This settles the dense branch. Henceforth assume H(S0)<H_* and m>1; m=1 has zero left side.

### G3 — PROVED: new retention rule and its modulus budget

Use the levels

\[
\mathcal D=\{1\}\cup\{j/2^h:8\le j\le15,\ h\ge4\}.
\]

Adjacent levels have ratio at most rho=9/8. Put eta(t)=16t/27 for t<=1/8. For the remaining levels t=v/64, put eta(t)=E_v/720 with this **complete** table:

| v | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 18 | 20 | 22 | 24 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| E_v | 59 | 65 | 71 | 77 | 80 | 85 | 92 | 95 | 105 | 117 | 118 | 128 |

| v | 26 | 28 | 30 | 32 | 36 | 40 | 44 | 48 | 52 | 56 | 60 | 64 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| E_v | 144 | 145 | 159 | 160 | 190 | 223 | 239 | 240 | 240 | 240 | 240 | 240 |

Let q_p(t) be the least p-power at which the cumulative S0 contribution reaches t; omit nonexistent levels. Retain (p,t) iff `q_p(t)<=m^eta(t)`. Define b_p(n) to be the largest retained t with q_p(t)|n, or zero; let B=sum b_p. These functions have finite nonnegative prime-power increments, B<=S0, and H(B)<=H(S0). Finiteness follows because q_p(t)>=2 whereas m^(16t/27)<2 for sufficiently small t. The table verifies `eta(t)<=1/3` and `eta(t)<=16t/27`; thus every atom of B has modulus at most m^(1/3).

A carrier is a shortest nonincreasing prefix of levels with total mass s>1. If theta is its last level, then

\[
1<s\le1+\theta.
\tag{7}
\]

For theta<=1/8, its total eta budget is at most `(16/27)(1+theta)<=2/3`. Otherwise all its levels are v/64 from the table. Remove the last level v/64; the remaining integer mass w lies between 65−v and 64, and all its levels are at least v/64. The recurrence

\[
D_v(0)=0,\qquad D_v(w)=\max_{u\ge v,\ u\le w}(D_v(w-u)+E_u)
\tag{8}
\]

over reachable w therefore enumerates exactly the possible largest budgets. In ascending v order, the verified maxima of `D_v(w)+E_v`, for 65−v<=w<=64, are

```
478,479,474,480,466,471,476,475,471,479,469,479,
479,480,479,480,430,463,479,480,480,480,480,480.
```

All are at most 480. Induction on w proves that (8) is exact: its last chosen level u leaves precisely the subproblem of mass w−u. Hence every carrier product P_C is at most m^(2/3), and

\[
P_C q\le m\quad\hbox{for every atom q of B.}
\tag{9}
\]

This is the load-bearing bound on every negative modulus.

### G4 — PROVED: the new rounding loss

Fix k<=m. For a positive S0 prime contribution f_p, round down to the largest t_p in D. Then f_p<=rho t_p and q_p(t_p)|k. If this level is retained, f_p−rho b_p(k)<=0. Otherwise

\[
a_p:=v_p(k)\log p/\log m>\eta(t_p),\qquad\sum_p a_p\le1.
\]

For t_p<=1/8, its positive error is at most `rho t_p=(243/128)eta(t_p)<(243/128)a_p`. For larger levels its error is at most its successor, with the top successor capped at 1. Write this reward r_v/64, where r_v is the next entry in the ordered v table, or 64 at the top. The total integer cost w of these large levels is at most 719 by strictness of a_p>eta(t_p). Their total reward is at most R(w), where

\[
R(0)=0,\qquad R(w)=\max_{E_v\le w}(R(w-E_v)+r_v)
\tag{10}
\]

on reachable w. The same last-item induction proves this recurrence exact. The small levels use at most the remaining budget 1−w/720. Direct integer recurrence (10) for w=0,...,719 gives

\[
\max_w\{1440R(w)+243(720-w)\}=255663,
\]

as recorded above. Therefore

\[
S_0(k)\le\rho B(k)+D_0,
\quad L_S:=\sum_{k\le m}(S_0(k)-c)^+
\le\rho L_B,\quad L_B=\sum_{k\le m}(B(k)-T)^+.
\tag{11}
\]

This proof includes arbitrary real atom weights; the finite integer check concerns only the fixed level table.

### G5 — PROVED: carriers and their coefficients

For each k with B(k)>T, order its positive b_p(k) nonincreasingly, with ties by the prime. Assign k to its shortest prefix of mass >1, recording each selected prime, its level t_p and q_p(t_p). This defines a finite family of carriers C with mass s_C, last level theta_C, and product P_C. Every outside prime at an assigned source has level at most theta_C. Set

\[
M_C=\sum_{\substack{k\le m\\k\text{ assigned to }C}}(B(k)-T),\qquad
\nu_C=\lfloor m/P_C\rfloor,\qquad c_C=M_C/\nu_C,
\tag{12}
\]

keeping only M_C>0. Then sum M_C=L_B and nu_C>=1. Define the finite atom system

\[
U_C(n)=\sum_{p\notin C}\min(b_p(n),\theta_C).
\]

At a source k=P_C u, all outside valuations agree with those of u, so its excess is `U_C(u)−(T−s_C)`. With theta=theta_C, s=s_C and a=(T−s)/theta, (2)–(3) give

\[
c_C\le\epsilon_{\theta,s}:=
\min_{2\le r\le\lfloor a\rfloor+1}
\frac{\theta(v_r-a)(H_*/\theta)^r}{(v_r)_r},
\quad v_r=\left\lfloor\frac{ra}{r-1}\right\rfloor.
\tag{13}
\]

Indeed the sum over assigned u is at most the full hinge sum over 1<=u<=nu_C. The capped outside functions divided by theta have values in [0,1] and mean at most H_*/theta. There is no floor-ratio loss.

### G6 — PROVED: prime counts and the exact window value

For all integers nu in the stated ranges,

\[
\frac{\pi(\nu)-2}{\nu}\le
\begin{cases}
45/211,&\nu\ge210,\\
342/2311,&\nu\ge2310,\\
3259/30139,&\nu\ge30030.
\end{cases}
\tag{14}
\]

Here is the complete analytic continuation of the finite sieve check. Let vartheta(x)=sum_(p<=x) log p. Induction using primes dividing central binomial coefficients gives vartheta(x)<=x log 4: for 2r use `(r,2r]` and `binom(2r,r)<=2^(2r−1)`; for 2r+1 use `(r+1,2r+1]` and `binom(2r+1,r)<=2^(2r)`, together with the induction bound at r or r+1. Extension to real x follows by taking its integer part.

Partial summation from 64, where pi(64)=18, yields

\[
\pi(x)\le18+\frac{x\log4}{\log x}+\log4\int_{64}^x\frac{dt}{\log^2t}.
\]

Since log 64>4, the integral is at most 2x/log²x, as follows by differentiating 2x/log²x. The elementary bounds 2/3<log2<7/10 imply, for x>=32768,

\[
\frac{\pi(x)\log x}{x}<7/5+14/50+189/32768<17/10.
\tag{15}
\]

For the last term use that log(x)/x decreases here. The finite sieve verifies (14) at its initial endpoints and at every prime up to 2^15, 2^17 and 2^23, respectively; between primes the ratios decrease. The finite maxima are exactly those in (14), attained at 211, 2311 and 30139. The rational bound log2>693/1000, verified by the positive atanh series, makes (15) strictly smaller than each claimed bound beyond its finite endpoint. This proves (14) for all nu.

Put `Tmin=16/3`. At a carrier source the outside mass exceeds T−1−theta, while every outside level is at most theta. Therefore at least

\[
r(\theta)=\lfloor(T_{\min}-1)/\theta\rfloor
\]

distinct outside primes divide k/P_C. In particular nu_C>=Q_r, the rth primorial, and r>=4. For the finite scales define

\[
\delta_\theta=\min\left\{d_r,
\frac{1700}{693\lfloor\log_2 Q_r\rfloor}\ \text{if }Q_r\ge32768\right\},
\quad d_4=45/211,\ d_5=342/2311,\ d_r=3259/30139\ (r\ge6).
\tag{16}
\]

The second entry follows from (15) and `log Q_r >= floor(log2 Q_r) log2`. For all tail scales L>=4096 use the weaker delta_theta=1/8; (14) suffices there. Thus `(pi(nu_C)−2)/nu_C<=delta_theta` in every case.

Choose K_theta from the finite table above, or K_theta=41/40 in the tail, and put

\[
\lambda_\theta=\frac{\rho K_\theta}{K_\theta-H_*-\delta_\theta\theta}.
\tag{17}
\]

Every denominator is positive, as checked exactly. The explicit signed family is

\[
\boxed{F(n)=\sum_C\lambda_{\theta_C}c_C[P_C\mid n]
\left(1-\frac{U_C(n)}{K_{\theta_C}}\right).}
\tag{18}
\]

In divisor-coefficient form it has coefficient `lambda_theta c_C` at P_C, and coefficient `−lambda_theta c_C beta/K_theta` at P_C q for each prime-power increment beta at q of U_C; add coincident coefficients. This specifies a finite family explicitly for every input. Every negative modulus is at most m by (9).

For its window value, `N_I(P_C)>=nu_C` and

\[
N_I(P_Cq)\le\lfloor\nu_C/q\rfloor+1.
\]

All relevant q are at most nu_C by (9). Each outside prime's increments total at most theta. Moreover **each carrier prime is at most nu_C**: its retained power is at most m^(1/3), whereas m/P_C>=m^(1/3). A carrier has at least two primes. Thus the total +1 error is at most `theta(pi(nu_C)−2)`, not theta pi(nu_C). The mean part is at most nu_C H_*. Consequently

\[
\sum_{b\in I}[P_C\mid b]U_C(b)
\le\nu_C(H_*+\delta_\theta\theta).
\]

Substitution in (18) and (17) gives

\[
\boxed{\sum_{b\in I}F(b)\ge\rho\sum_C M_C=\rho L_B.}
\tag{19}
\]

### G7 — PROVED: pointwise counting reduction

Write theta=j/L, where j=8,...,15 and L>=16 is a power of two, with 1 represented as (8,8). Every D-level >=theta is a multiple of 1/L. A carrier with k primes and last level theta has mass 1+d/L, 1<=d<=j. Set

\[
P_{j,L}(X)=\sum_{t\in\mathcal D,\ t\ge j/L}X^{Lt},\qquad
E_{k,d}=[X^{L+d}]\{P_{j,L}^k-(P_{j,L}-X^j)^k\}.
\]

Fix n and let N be the number of primes with b_p(n)>=theta. A carrier dividing n is determined by its k chosen primes and their levels. The number of such assignments is at most `binom(N,k) E_(k,d)`. Its outside mass U_C(n) is at least (N−k)theta, and B(n)−1 is at least d/L+(N−k)theta. Discarding negative summands in F, (13) gives the bound

\[
A_\theta=\max_{0\le N\le\lfloor K_\theta/\theta\rfloor+\lfloor1/\theta\rfloor+2}
\sum_{k,d}\binom Nk E_{k,d}\epsilon_{\theta,1+d/L}
\frac{(1-(N-k)\theta/K_\theta)^+}{d/L+(N-k)\theta}.
\tag{20}
\]

The sums have `1<=k<=floor((L+j)/j)` and 1<=d<=j. Beyond the displayed N bound all positive parts vanish. If B(n)<=1 no carrier divides n. Otherwise, summing scale by scale proves

\[
F(n)\le\left(\sum_\theta\lambda_\theta A_\theta\right)(B(n)-1)^+.
\tag{21}
\]

For theta>=1/2, a sharper finite bound is used. Carriers have two primes, except triples of halves at theta=1/2. Let `e=epsilon_(theta,2theta)` for theta>1/2 and e=0 otherwise; let `h=epsilon_(1/2,3/2)` at theta=1/2 and h=0 otherwise; define `E(v)=sum_(theta<t<=v) epsilon_(theta,theta+t)` and `p_k=(1−(N−k)theta/K)^+`. Then

\[
A_\theta=\max_{N,v\in\mathcal D,\ v\ge\theta}
\frac{N(N-1)(e/2+E(v))p_2+\binom N3h p_3}{Nv-1},
\tag{22}
\]

with zero-numerator/zero-denominator cases omitted and `2<=N<=floor(K/theta)+3`. To prove (22), give the eligible primes their actual caps v_i=b_p(n). Mixed pairs are bounded by `(N−1)sum_i E(v_i)`; equal pairs contribute binom(N,2)e; half-triples contribute binom(N,3)h. Divide by `sum_i v_i−1`. Distribute the constant numerator equally among the N terms. Each denominator summand v_i−1/N is nonnegative, so the ratio is at most the largest single-coordinate ratio, which is exactly (22). The only zero-denominator case is N=2,v=theta=1/2, where its numerator is zero. This proves the sharper bound, without assuming all actual caps are equal.

### G8 — PROVED: verification of all finite scales

The table in the report evaluates (20), or (22) for theta>=1/2, with (13). Here is the exact arithmetic certificate procedure, including its rounding directions.

For each L,j,d and every `2<=r<=floor(a)+1`, compute `v=floor(ra/(r−1))` and the rational expression in (13) by integers. Select its minimum. Let `b=64+32 ceil(L/j)` and replace it by its ceiling in units of 2^-b. The code keeps the selected r for every mass. Polynomial multiplication by P and P−X^j through degree L+j produces the exact nonnegative E_(k,d). No omitted higher coefficient can affect a lower degree. Enumerate every N in (20); replace each nonnegative rational summand by its ceiling in units of 2^-56 before summing and maximizing. For (22), use Fraction arithmetic directly with the already rounded-up epsilon values. Multiply by the exact positive lambda. Finally round each sum over j upward to units of 10^-12.

These operations give exactly the nine upper bounds printed above. Recurrence multiplication is an induction on k and degree, so it computes the displayed polynomial coefficients; the finite N bound was proved in G7; and every rounding increases its argument. This is a finite exact-arithmetic proof of the stated upper bounds, not numerical optimization evidence. `final_verify.py` additionally compares the coefficient convention with direct ordered-assignment enumeration at the small scales and recomputes each selected moment bound from its defining Fraction formula. The underlying large integer arithmetic is not kernel checked.

### G9 — PROVED: infinite tail and closure

For z>1, the elementary maximum of `y z^(−y)` gives `y^+<=z^y/(e log z)`. Apply this and (4) to the same capped outside system used in G5. Since s<=1+theta,

\[
c_C\le\frac{\theta z}{e\log z}
\left(e^{(z-1)H_*}z^{1-T}\right)^{1/\theta}.
\]

Take z=9/2 and a0=49/1000. Exact Taylor and atanh-series bounds verify

\[
e\log(9/2)>4,\quad e^{7H_*/2}<8279/250,
\quad(8279/250)^3<a_0^3(9/2)^{13}.
\]

As T>=16/3, these imply `c_C<=rho theta a0^(1/theta)`. For L>=4096 set K=41/40 and delta=1/8; direct rational calculation gives lambda<50.

For each j let

\[
\mathcal P_j(X)=\sum_{a=j}^{15}X^a+\sum_{h\ge1}\sum_{a=8}^{15}X^{a2^h}.
\]

Use these x, pbar and sigma values:

| j | x | pbar | sigma |
|---|---|---|---|
| 8 | 473/625 | 421847/1000000 | (157/200)(122500/120347) |
| 9 | 3883/5000 | 42539/100000 | (827/1000)(122500/120347) |
| 10 | 7939/10000 | 42847/100000 | (859/1000)(122500/120347) |
| 11 | 4047/5000 | 107879/250000 | (22/25)(122500/120347) |
| 12 | 8233/10000 | 216251/500000 | (111/125)(122500/120347) |
| 13 | 4181/5000 | 86661/200000 | (441/500)(122500/120347) |
| 14 | 8481/10000 | 215799/500000 | (863/1000)(122500/120347) |
| 15 | 8593/10000 | 213963/500000 | (83/100)(122500/120347) |

The verifier proves `0<sigma<1`, `P_j(x)<=pbar<1` and

\[
(a_0x^{-j})^{40}\le\sigma^{40}(1-\bar P)^{41}.
\tag{23}
\]

For the first check, sum bands h=1,...,4 exactly and dominate the rest by x^256/(1−x); all remaining exponents are distinct integers >=256. The exponential upper bound uses the positive Taylor polynomial through order 40 plus the geometric majorant for its tail. The logarithm lower bound uses the positive atanh series. Thus every asserted transcendental inequality is certified by rational comparisons.

For completeness, (20) has a positive summand only when `n=N−k` satisfies `0<=n<=M=ceil(K/theta)−1`. Bounding its denominator below by d/L, its positive factor by 1, and its coefficient by `x^(−L−d) P_j(x)^k`, the contribution of a scale is at most

\[
50\rho j\sum_{d=1}^j x^{-d}(a_0^{1/j}/x)^L
\sum_{n=0}^{M}\sum_{k\ge0}\binom{n+k}{k}\bar P^k.
\]

Here `theta/(d/L)=j/d<=j`. The inner sum is `(1−pbar)^(−n−1)`, and the n sum is at most `pbar^(-1)(1−pbar)^(−M−1)`. Since M<=41L/(40j), (23) bounds the entire scale by

\[
\frac{50\rho j\sum_{d=1}^j x^{-d}}{\bar P(1-\bar P)}\sigma^{L/j}.
\tag{24}
\]

Sum L=4096*2^h. Because 2^h>=h+1 and sigma<1, its sum is at most the prefactor in (24) times `z/(1−z)` with `z=sigma^floor(4096/j)`. Upward rounding each of the eight resulting rational numbers to units of 10^-15 gives the stated tail total `230783/500000000000000`. Combining G7–G8 with this tail proves

\[
F(n)\le\kappa(B(n)-1)^+\le(S(n)-1)^+.
\tag{25}
\]

Equations (5), (11), (19) and (25) now give

\[
\sum_{k\le m}(S(k)-c)^+
=L_S\le\rho L_B\le\sum_{b\in I}F(b)
\le\sum_{b\in I}(S(b)-1)^+.
\]

If L_B=0, (11) finishes without a carrier. G2 already handled the dense branch and m=1. This proves the global theorem for every atom system, m and window, with no sparse-region restriction left over. ∎

## Complete proof of the fixed-support threshold-2 result

### A1 — PROVED: a uniform large-Q bound for K4

For e in the nonnegative exponent lattice of four primes, write `D=prod p_i^e_i` and `F(e)=D/max_i p_i^e_i`. Since the maximum coordinate is at least D^(1/4), F(e)<=D^(3/4). If F(e)>=Q, then

\[
\frac QD\le Q^{-1/5}D^{-1/10}.
\]

Sum this over minimal feasible e, enlarge to the entire lattice, and use geometric series:

\[
K_P(Q)\le Q^{-1/5}\prod_{p\in P}(1-p^{-1/10})^{-1}.
\tag{26}
\]

In increasing prime order p_i>=2,3,5,7. The rational tenth-root upper bounds 9331/10000, 8960/10000, 8514/10000, 8232/10000 are verified by the integer inequalities `p a^10>10000^10`. Thus the product in (26) is less than

\[
A=\frac{7812500000000}{1428073491}.
\]

The exact integer ceiling of A^5 is

\[
Q_0=4900014488437221682.
\]

For Q>=Q0, (26) is at most 1. This holds for every prime quadruple. It is only a tail theorem, not arbitrary-support K4.

### A2 — PROVED: the exact finite sweep for {2,3,5,7}

Here is why the finite computation covers all Q from 2 through Q0−1, including those too large to iterate one by one.

Set B=Q0−1. For each prime p take the exponent ladder from 1 through the least p-power >=B. No coordinate of a minimal feasible exponent vector for Q<=B can exceed its ladder. Otherwise lowering that coordinate leaves its value at least B>=Q. If it remains a maximum, F is unchanged; if another coordinate is a maximum, the product defining F includes the lowered coordinate and is still at least Q. Either contradicts minimality.

F(e) is coordinatewise nondecreasing because it is the minimum of the four products obtained by omitting one coordinate. For each ladder vector e compute

\[
u(e)=F(e),\qquad \ell(e)=\max_{i:e_i>0}F(e-\mathbf e_i).
\]

Then e is minimal feasible **exactly** for the integer interval `ell(e)<Q<=u(e)`. Intersect this with [2,B]. Let W be the product of the top ladder powers. Every D(e) divides W. Insert the integer coefficient W/D(e) at the interval's first Q and its negative at one past the last Q. A sweep of these finitely many events maintains exactly `W sum_minimal 1/D`. Between successive events that sum is constant and nonnegative, so the maximum of Q times the sum occurs at the last integer before the next event.

The exact sweep visits **1763328** ladder states and finds **35109** nonempty minimality intervals. Its maximum over 2<=Q<=B is **101/105**, attained at Q=2. The algorithm is `frontier_sweep` in `route_tests.py`, independently rerun by `final_verify.py --full`; the latter also compares small unswept frontiers. The integer event proof above shows that no intermediate Q or exponent is omitted. Together with A1, this proves K4 for {2,3,5,7} at every Q. The claim 101/105 here is the finite-range maximum; the analytic tail is only bounded by 1. ∎

### A3 — PROVED: the four-prime base, with an explicit finite certificate

Pad with zero functions and write T=f1+f2+f3+f4. Put

\[
G_0=\frac13\sum_{i<j}(f_i+f_j-1)^+.
\]

Every f_i appears in three pairs, so G0>=(T−2)^+. For the other direction, split the six pairs into three perfect matchings and use `(a−1)^++(b−1)^+<=(a+b−1)^+` for a,b>=0. This gives G0<=(T−1)^+.

For a pair of primes p,q with cumulative levels A_a,B_b, define

\[
\beta_{a,b}=\phi(A_a+B_b)-\phi(A_{a-1}+B_b)
-\phi(A_a+B_{b-1})+\phi(A_{a-1}+B_{b-1}),\quad\phi(u)=(u-1)^+.
\]

Convexity implies beta>=0: for fixed delta>=0, `phi(u+delta)−phi(u)` is nondecreasing. Boundary terms vanish because individual prime contributions are at most 1. Double telescoping therefore expands the pair hinge as the finite nonnegative divisor sum `sum beta_(a,b)[p^a q^b|n]`. Dividing each pair coefficient by 3 gives the explicit divisor family for G0. By (1), its window sum is at least its prefix sum. This proves H2 for four arbitrary multilevel primes.

### A4 — PROVED: elimination on the fixed four-prime support

Let T be an arbitrary multilevel system on {2,3,5,7}, and f be the contribution of a fifth prime p. For real a and 0<=f<=1,

\[
(T+f-a)^+-(T-a)^+=\int_0^1[f>t][T>a-t]\,dt.
\tag{27}
\]

This follows by integrating the slope of u->(T+u−a)^+ from u=0 to f; equality points have measure zero. At t in (0,1), [f(n)>t] is zero or the indicator of one power d(t) of p. Let c_t=1−t. If T ever exceeds c_t, let Q(t) be the smallest divisor supported on these four primes for which its T-value exceeds c_t. It exists because the atom system is finite, and Q(t)>=2.

At a point with T>c_t+1, deleting any one prime contribution, which is at most 1, leaves value >c_t. Take the actual four valuation coordinates, capped at the last atom exponents. Their product after deleting any coordinate is therefore at least Q(t), so their vector is feasible for K4. It dominates a minimal feasible vector. Thus A2 and a union bound give, for every M,

\[
\#\{k\le M:T(k)>c_t+1\}
\le\sum_{e\text{ minimal}}\lfloor M/D(e)\rfloor
\le M/Q(t),
\]

and hence at most floor(M/Q(t)). Since d(t) is coprime to the four support primes, T(d(t)k)=T(k). Taking M=floor(m/d(t)) bounds the prefix layer in (27) at a=2 by floor(m/(d(t)Q(t))). The divisor indicator `[d(t)Q(t)|n]` is pointwise at most `[f(n)>t][T(n)>1−t]`, so its window count supplies that many points in the right layer at a=1.

For explicit finiteness, partition (0,1) at all cumulative levels of f and all values `1−T(e)` that lie there, where e ranges over the finite capped valuation state space of T. On each open cell (u_l,v_l), d and Q are constant or absent. Define

\[
G(n)=G_0(n)+\sum_{l\text{ present}}(v_l-u_l)[d_lQ_l\mid n].
\tag{28}
\]

This is an explicit finite nonnegative divisor family, with G0 expanded as in A3. The layer domination and (27) show pointwise `G<=(T+f−1)^+`; the prefix count just proved and A3 show `sum_prefix G>=sum_prefix(T+f−2)^+`. Its window value is at least its prefix value by (1). Thus (28) proves H2 on {2,3,5,7,p} for all real weights, all m and all windows. It makes no unsupported pointwise lower-hinge assertion. ∎

## Refutation work, method obstructions and verification limits

### B1 — REFUTED: unrestricted minimum-divisor layer bound

Let T count divisibility by the twenty primes

```
2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71.
```

For c_t=1/2 the smallest divisor with T>c_t is Q=2. At M=1000000, direct integer sieving gives **551993** points with T>c_t+1, exceeding floor(M/Q)=**500000**. This refutes the unrestricted layer majorant, not H2. Its mean is about 1.74287, and `mu−H²/6` is about 1.23660: it belongs to the affine dense branch. Exact fractions are in `route_obstructions.json`; no inference about the sparse version is made from these decimals.

### B2 — REFUTED: the old retention construction at threshold 2

Let

\[
q_1=2^{340},\ q_2=3^{214},\ q_3=5^{77},\ q_4=7^{49},\quad m=q_1q_2q_3q_4.
\]

Use weights 99/100 at q1 and q2, 1/100 at q1² and q2², 46/100 at q3, 28/100 at q4, and 1/100 at each of 11 and 13. There are six active primes and two multilevel primes. All atoms are <=m/6, H<1, and S(m)=68/25>2, so this is in the sparse remaining case (`mu<=H<1`).

The exact integer inequalities

\[
q_1^3>m,\quad q_2^3>m,\quad q_3^6>m,\quad q_4^{15}>m^2
\]

show that the **old published** retention rule drops all levels at the first four primes. For the two unit-capacity primes every retention exponent is at most 1/3; for weights 46/100 and 28/100 the largest available old exponent is 1/6 and 2/15 respectively. The two remaining primes contribute at most 1/50 in total. Hence globally B<=1/50 and there is no mass>1 carrier, although the left hinge at k=m is positive. This refutes that threshold-2 construction even inside the corrected sparse case. It is not an H2 counterexample.

### B3 — PROVED: recheck of the six-prime nonnegative obstruction

On {0,1/2,1}^6, suppose a nonnegative upper-orthant certificate lies between the two hinges. The upper bound at total mass <=1 kills constants, singleton coefficients, and pairs with both thresholds 1/2. Let P,T,H be its total coefficient masses of support 2,3,>=4. The all-ones state gives P+T+H<=5. The twenty states with exactly three ones each require certificate value >=1. A support-two coefficient is counted four times, a support-three coefficient once, and larger supports never, giving 4P+T>=20. But `4P+T<=20−3T−4H`, so T=H=0. Every remaining pair needs a threshold 1 in at least one coordinate. The certificate therefore vanishes at the all-half state, whose lower hinge is 1. Contradiction. This is an exact rational infeasibility proof, not evidence against H2 itself.

### Exact search scope and period reduction

The search used positive weights on both 2,4 and 3,9, plus single atoms at the remaining primes among the first eight. Denominators were factorials of the atom counts: 7!, 8!, 9!, 10!. This samples the allowed rational region; it does not enumerate its arrangement vertices. For five/six primes it checked all x modulo D at the selected m and weights: **116424000** windows over **1200** profiles, **1187** with positive LHS. Of these, **106444800** windows over **1140** profiles passed the additionally tested sparse criteria. For seven/eight primes it checked **215838** sampled windows over **3997** profiles, **3987** with positive LHS; **199962** windows over **3703** profiles passed those sparse criteria. No negative gap occurred.

For fixed atoms and weights, D is the lcm of their moduli. Both hinges are periodic. Write m=aD+r. The full-period right-hinge sum is at least the full-period left-hinge sum termwise, so the length-m gap is a times a nonnegative period gap plus the length-r gap at x mod D. Thus checking all 1<=m<=D and 0<=x<D would suffice for a fixed weighted system. We used this to check all offsets in the five/six-prime jobs, but did **not** claim to check all m or all weights. For a fixed m,x, the hinge difference is linear on each cell cut by the hyperplanes S(k)=2 and S(b)=1. A positive maximum over the compact product of prime-capacity simplices has a cell vertex; Cramer's rule and the determinant expansion bound its coordinate denominators by d!, where d is the atom count. This explains rational searches without making the sampled factorial grids exhaustive.

The initial adversarial pass contains **48** exact instances, with five/six equal half weights, six primes each having half at p and half at p², and a five-prime system with two multilevel primes, at lengths 10^4,10^5,10^6. It includes reflected and centred CRT windows and verifies that the chosen sieve-rich windows have more integers avoiding primes through 19 than the prefixes: **1722>1711**, **17115>17103**, **171038>171021**. This explicitly prevents use of prefix-to-window stochastic domination. These counts are finite stress tests, not a theorem about all intervals.

The final signed-family audit has positive global left hinge in both cases, equal to **7076433/32000000**. On nine primes from 5 through 31, the unit-weight family has **10 carriers, 60 aggregated coefficients, and all 512 states checked**. The half-at-p/half-at-p² family has **36 carriers, 372 aggregated coefficients, and all 19683 states checked**. Every coefficient and every window value is retained in `actual_certificate_radix2.json` and `actual_certificate_radix3.json`. Each checks `LHS<=rho L_B<=sum_I F<=RHS` on the prefix, a reflected window, a centred CRT window, and the three stored sieve-rich offsets. The latter offsets are only stress offsets for these different supports; no sieve-rich property for the new supports is asserted. Small-length fallback cases can be trivial after primorial truncation; the two large-period fixtures avoid a zero-LHS audit.

## Final dependency block

**final claim ← lemmas ← unproved items**

- **PROVED global H_(280923567/32000000)** ← G9 closure and infinite tail; G8 exact finite scale bounds; G7 pointwise feasibility; G6 signed window value; G5 coefficient moments; G4 rounding; G3 retention budgets; G2 truncation/dense branch; G1 moments ← **no unproved mathematical items**. Trust boundary: the documented exact integer/Fraction computations, not Lean.
- **PROVED fixed-support K4 for {2,3,5,7}, all Q** ← A2 finite event sweep and its coverage proof; A1 uniform analytic tail ← **no unproved items** under the same explicit computation trust boundary.
- **PROVED H2 on {2,3,5,7,p}, arbitrary levels** ← A4 explicit layer certificate; A3 four-prime base; A2 fixed-support K4; interval counts ← **no unproved items**.
- **REFUTED candidate methods** ← B1 exact prefix count; B2 exact prime-power inequalities; B3 rational obstruction ← **no claim of a counterexample to H2**.
- **CONDITIONAL g(n)<=ceil(c n)+2n<=11n** ← proved H_c ← **external supplied input:** the hinge-to-Erdős–Surányi reduction, not reproved or formalized in this campaign.
- **OPEN T1/T2 and lower global thresholds** ← frozen route gaps ← **unproved:** an all-support threshold-2 argument or an exact counterexample; and any global improvement below the displayed c.

Gap: H2, its refutation, and every global threshold below 280923567/32000000 remain unproved here for all atom systems, all m and all windows.
