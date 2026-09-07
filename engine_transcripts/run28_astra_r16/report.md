# Erdős 708 — round 16 final report

PROVED (campaign record): started 2026-09-07 04:55:15 UTC; hard deadline 2026-09-07 07:55:15 UTC. Completed 2026-09-07 05:28:17 UTC (33 minutes 2 seconds elapsed). The scheduled 30-minute checkpoint was written at 05:25:15 UTC and is preserved as checkpoint_030.md. All campaign writes are confined to this directory. No git operation was performed. The required global-memory tool was absent from the available tool catalog, as disclosed at the start.

## Verdict

| Target | Status | Result |
|---|---|---|
| T1: prove (SC_64) for all m, by (NC) or any rigorous route | **PROVED** | A signed, clipped prefix certificate proves the stronger inequality R >= (141/128)L for every atom system and window in the brief. Complete proof below. |
| Original (NC) for the round-15 nonnegative certificate | **OPEN** | Neither proved nor refuted; it is not used by the new proof. |
| T2: an exact counterexample if T1 fails | **OPEN** | No (NC) counterexample is claimed. This conditional branch is not needed because T1 is proved by its permitted alternative route. |
| T3: precise theorem and Lean dependencies | **PROVED** | The theorem, complete dependency chain, and formalisation requirements are given below. |
| Threshold-65 hinge and g(n) <= 81n, all n | **PROVED** | Corollaries of the sparse-core theorem and the accepted paper reduction. |
| Erdős's sharper target g(n) <= 2n, or (2+o(1))n | **OPEN** | This report does not establish either sharper target. |

PROVED (scope of certification): the mathematical proof is complete as written, with an internal audit and exact arithmetic checks. No external referee or Lean-kernel certification is claimed. The finite checks are supporting validation, not a substitute for the universal proof.

## Route and accepted inputs

PROVED (method): the brief's shared-prime-support suggestion leads to the correction U_P below: it excludes the primes of P and caps every other prime contribution at the last-atom mass. Dyadic rounding controls all higher prime-power levels without an m-dependent level-count factor. A modulus-cost cutoff ensures that every negative correction has modulus below m, so the two-sided interval counts pay for it. This proves (SC_64) directly rather than establishing concentration for the original certificate.

PROVED (accepted inputs): the atom setting, hinge-moment inequality, moment expansion, and signed counting principle are those supplied in [the paper](../../../papers/erdos708/main.tex), [round-15 report](../claude_blitz_0905/F1_708/report.md), and [its referee](../claude_blitz_0905/F1_708/referee.md). The proof below includes the finite moment argument to make its dependencies explicit. It does not use the rejected private-prime budget additivity, the uncorrected arbitrary-multiple identity, floating-point S*(m) thresholds, the shadow theorem, or an unproved lower bound on L.

PROVED (compatibility with the earlier barriers): rounds 13 and 14 rule out the specified **nonnegative** certificates. The present certificate has essential negative coefficients. Thus its window-independent coefficients do not contradict those barrier theorems; the brief's abbreviated phrase “window-independent certificates fail” must retain the nonnegativity restriction present in the source statements.

## Statement and notation

Let m > 4096 be an integer, let I be any m consecutive positive integers, and let

    S(n) = sum_p a_p(n),  a_p(n) = sum_{j: p^j | n} alpha_{p,j},
    alpha_{p,j} >= 0,  sum_j alpha_{p,j} <= 1,
    p^j <= m/64 on the support,  H = sum_{p,j} alpha_{p,j}/p^j < 17/16.

Write L = sum_{k=1}^m (S(k)-64)^+ and R = sum_{n in I} (S(n)-1)^+.
**PROVED — Theorem.** The conclusion is the stronger inequality R >= (141/128)L.

The argument uses signed divisor coefficients. It makes no assertion about the original nonnegative prefix certificate's (NC).

## 1. Dyadic rounding and removal by modulus cost

For each prime, round each positive cumulative value A_{p,j} down to the largest number of the form 2^{-h}, h >= 0, not exceeding it. Retain only the first exponent at which each distinct rounded value occurs. This gives finitely many pairs (q,t), where q is a power of that prime, t is dyadic, and both q and t strictly increase along the list.

Keep a pair (q,t) exactly when

    q^(16/t) <= m.                                      (1)

Define b_p(n) as the largest retained value t with q | n, or zero if there is none, and B(n) = sum_p b_p(n). The positive increments between retained values form a new atom system. Its cumulative values are distinct dyadic numbers, its per-prime total is at most one, and b_p(n) <= a_p(n).

**PROVED — Lemma 1.** H_B <= H, R_B <= R, and L <= 2 L_B, where

    H_B = sum new_increment/q,
    R_B = sum_{n in I} (B(n)-1)^+,
    L_B = sum_{k=1}^m (B(k)-16)^+.

Proof. The right hinge comparison follows from B <= S. To compare means, take a common multiple Q of every original prime-power modulus. Both systems are periodic modulo Q and the average of an atom indicator over 1,...,Q is exactly 1/q. Thus B <= S gives H_B <= H.

Fix k <= m. For each prime with a_p(k) > 0, let t_p be its rounded value, so a_p(k) < 2t_p. Let q_p be the first original exponent attaining that rounded value. Then q_p | k. If q_p satisfies (1), b_p(k) >= t_p. If not, then

    a_p(k) < 2t_p < 32 log(q_p)/log(m).

The q_p belong to distinct primes and their product divides k. Summing over the latter primes gives a total contribution less than or equal to 32; summing over the former gives at most 2B(k). Consequently S(k) <= 2B(k)+32, and

    (S(k)-64)^+ <= 2(B(k)-16)^+.

Sum over k. QED.

Every retained level (q,t) satisfies log q <= (t/16) log m. This remains true after levels have been removed: the retained cumulative value is still t, because the new increments telescope to t.

## 2. Prefixes at threshold 16

Order retained levels by decreasing cumulative mass t, breaking ties lexicographically by (prime, exponent). For k with B(k) > 16, take its effective level at every contributing prime, and list these in that order, with masses a_1 >= ... >= a_s and partial sums s_i. Let P_i be the product of the first i effective moduli and

    w_{k,i} = length([s_{i-1},s_i) intersect (2,3]).

The weights sum to one. A carrier is a P_i with positive weight for some hot k. It has mass mu(P) = B(P) in (2,4), prefix mass before its last atom less than 3, last mass theta = 2^{-h}, and w_{k,i} <= theta. Put

    d_k = B(k)-16,
    M(P) = sum_{k hot, i: P_i=P} d_k w_{k,i}.

Then sum_P M(P) = L_B. Define K_P = floor(m/P) and a_P = M(P)/K_P. The notation a_P for this coefficient is distinct from the original per-prime function a_p.

**PROVED — Lemma 2.** Each carrier has P < m^(1/4), so K_P >= 1. If theta is its last mass and r = 12/theta + 1, then

    M(P) <= theta^(2-r) H_B^r/r! * m/P,
    a_P <= 2 epsilon(theta),
    epsilon(theta) = theta^(2-r) H_B^r/r!.               (2)

Proof. Summing log q <= (t/16)log m over a carrier gives log P <= mu(P)log m/16 < log m/4.

For a contributing k, write k=Pj. At primes in P, the effective level of k is exactly the level in P. At primes outside P, the contribution at j is the contribution at k, and is at most theta by the mass ordering. Thus

    B(k) = mu(P) + sum_{p not dividing P} b_p(j),
    d_k <= (sum_{p not dividing P} b_p(j) - 12)^+.

The rescaled hinge-moment inequality from round-15 Lemma A, with c=12, gives a bound theta^(1-r) e_r((b_p(j))_{p not dividing P}); r is an integer because theta is dyadic. Multiply by w <= theta, sum using the injective map k -> j and the inherited moment bound at length floor(m/P), and replace that length by m/P. This proves the first inequality in (2). Finally floor u >= u/2 for u >= 1 gives the second. QED.

For completeness the two inherited ingredients are: for x_i in [0,1], (sum_i x_i-C)^+ <= e_{C+1}(x) when C is a nonnegative integer; and sum_{j<=N} e_r((b_p(j))_p) <= N H_B^r/r!. The latter follows by expanding into atom choices at distinct primes and applying floor(N/product q) <= N/product q, followed by r! e_r(h) <= (sum h)^r (expand the latter power and discard repeated-index terms).

Here is the finite argument for the hinge inequality, to specify the formalisation dependency completely. With other coordinates fixed, e_{C+1} has the form A+(u+v)D+uv E, with E>=0, in two coordinates u,v (for C=0 it is just their sum plus a constant). Moving u,v at fixed sum until one reaches 0 or 1 decreases uv and does not increase e_{C+1}. Each move reduces the number of strictly fractional coordinates, so finitely many moves leave q=floor(sum x_i) ones, one coordinate tau in [0,1), and zeros. At that vector e_{C+1}=binom(q,C+1)+tau*binom(q,C). It is nonnegative if q<C, equals tau if q=C, and is at least q-C+tau if q>C: binom(q,C+1)>=q-C follows by fixing C elements and adjoining each of the other q-C elements, while binom(q,C)>=1. These are exactly the three cases of the required hinge. Rescale x_i=b_i/theta and C=12/theta to get the inequality used above.

## 3. A carrier count using capped mass, with no level-count factor

For a positive integer n and a dyadic theta, put

    T_theta(n) = sum_p min(b_p(n),theta),
    N_theta(n) = #{p: b_p(n) >= theta}.

Then theta N_theta <= T_theta.

**PROVED — Lemma 3.** Fix a retained level q dividing n, of mass theta. The number of carriers dividing n whose last level is q is at most

    2^((3+T_theta(n))/theta).                           (3)

Proof. Such a carrier is q times a set of earlier levels at distinct other primes, of total mass less than 3. Every such mass is theta times one of 1,2,4,... . At a given eligible prime, distinct masses correspond to distinct retained levels. For z=1/2, the sum of z^(mass/theta) over the available levels at this prime is at most

    sum_{h>=0} 2^(-2^h) <= sum_{h>=0} 2^(-h-1) = 1,

using 2^h >= h+1. Therefore the generating sum over all choices of zero or one available level at each prime is at most 2^{N_theta(n)}. Every choice of total mass at most 3 contributes at least 2^{-3/theta} to that generating sum. Its number is consequently at most 2^{3/theta+N_theta(n)}, proving (3). Ignoring the order restrictions and allowing the prime of q only enlarges this bound. Unique factorisation identifies each carrier with a unique level choice. QED.

**PROVED — Lemma 4.** For every n,

    sum_{retained levels q dividing n} mass(q) <= 2 B(n). (4)

Proof. At a fixed prime these are distinct dyadic numbers bounded by b_p(n). Their sum is at most the full geometric series b_p(n)(1+1/2+1/4+...) = 2b_p(n). Sum over primes. QED.

## 4. An exact uniform numerical bound

**PROVED — Lemma 5.** For theta=2^{-h}, H_B <= 17/16,

    G(theta) := [epsilon(theta)/theta] 2^{23/theta}
               <= 17/416.                             (5)

Proof. Set t=1/theta, a positive integer, so r=12t+1. Then

    G(theta) = t^{12t} H_B^{12t+1} 2^{23t}/(12t+1)!
             <= H_B/(12t+1) * [2^23(e H_B/12)^12]^t,

by (12t)! >= (12t/e)^{12t}. The latter follows from sum_{i=1}^n log i >= integral_1^n log x dx >= n log n-n.

The elementary bound e < 11/4 and exact integer arithmetic give

    2^23 (e H_B/12)^12
       < 2^23 (187/768)^12
       = 1828518162230556187140793681
         / 5019318332045454244023631872
       < 1/2.

For example e < 11/4 follows by summing the exponential series through 1/4! and bounding its tail by (1/120)/(1-1/6)=1/100, giving e < 65/24+1/100=1631/600 < 11/4.

Thus G(theta) <= 17/[16(12t+1)2^t] <= 17/416. All displayed rational comparisons are exact. QED.

## 5. The signed certificate and pointwise feasibility

Define

    U_P(n) = sum_{p not dividing P} min(b_p(n),theta_P),
    F(n) = 3 sum_P a_P [P|n] (1-U_P(n)/16).            (6)

**PROVED — Lemma 6.** For every positive integer n, F(n) <= (B(n)-1)^+.

Proof. If B(n) <= 2, no carrier divides n, so F(n)=0. Suppose B(n)>2. When P|n, every prime in P contributes at least its carrier mass, which is at least theta_P. Therefore

    U_P(n) = T_{theta_P}(n) - theta_P omega(P),
    theta_P omega(P) <= mu(P) < 4.

If the bracket in (6) is positive, U_P(n)<16 and therefore T_{theta_P}(n)<20. Discard nonpositive summands; every remaining bracket is at most one. By grouping the remaining carriers by their last level q, and using (2), (3), (5), and (4), respectively, obtain

    F(n)
      <= 3 sum_{q|n, T_{theta_q}(n)<20}
             2 epsilon(theta_q) * 2^{23/theta_q}
      <= 6*(17/416) sum_{retained q|n} theta_q
      <= 12*(17/416) B(n)
       = (51/104) B(n)
      <= B(n)/2
      <= B(n)-1.

This proves feasibility. The exclusion of primes dividing P in U_P is essential: there is no assumption that the contribution of such a prime at an arbitrary multiple n is its contribution in P. QED.

## 6. Modulus support and value on every interval

For a dyadic theta, min(b_p(n),theta) has nonnegative increments

    beta^{theta}_{p,e} = min(t_{p,e},theta)-min(t_{p,e^-},theta)

at the retained levels; take the preceding value to be zero at the first one. These increments are at most the corresponding increments of b_p. Hence H_theta := sum beta^{theta}_{p,e}/p^e <= H_B.

**PROVED — Lemma 7.** Formula (6) is a finite signed divisor certificate, with every positive carrier modulus < m^(1/4), every negative extension modulus < m^(5/16), and

    sum_{n in I} F(n) >= (141/64) L_B.                 (7)

Proof. Expand U_P using these increments. Because its primes are outside P, the extension modulus is the product Pq, not a product with an overlapping prime. A retained q of cumulative mass v satisfies q <= m^{v/16} <= m^{1/16}; consequently Pq < m^{5/16} <= m.

The coefficient before combining equal moduli is 3a_P at P and -3a_P beta^{theta_P}_{p,e}/16 at Pq. It is legitimate to keep these terms separate when bounding their sum. For any d <= m,

    N_I(d) >= floor(m/d),  N_I(d) <= m/d+1 <= 2m/d.

Thus the positive term associated with P sums to at least 3M(P). Also, since K_P >= m/(2P),

    a_P N_I(Pq) <= [M(P)/K_P] * 2m/(Pq)
                  <= 4 M(P)/q.

The total subtraction belonging to P is at most (3/16)*4M(P)H_theta <= (3/4)M(P)H_B. Therefore

    sum_{n in I} F(n)
       >= 3(1-H_B/4) sum_P M(P)
       >= 3(1-17/64) L_B
        = (141/64) L_B.

This proves (7). All coefficient choices depend only on the atom system and m, not on I. QED.

## 7. PROVED — conclusion of the sparse-core theorem

By Lemmas 1, 6, and 7,

    R >= R_B >= sum_{n in I} F(n)
      >= (141/64) L_B >= (141/128) L >= L.

This proves (SC_64) for all m under the brief's hypotheses. There is no remaining appeal to (NC), a finite range of m, a lower bound on positive weights, a bound on the number of levels at a prime, or a bound on the height of the interval.

## 8. PROVED — consequences for the paper

**PROVED — Corollary 8.1 (threshold-65 hinge).** For every integer m>=1, every integer x>=0, and every finitely supported weight family 0<=z_p<=1, with w_z(n)=sum_p z_p v_p(n),

    sum_{k=1}^m (w_z(k)-65)^+
        <= sum_{b=x+1}^{x+m} (w_z(b)-1)^+.

Proof. Apply the paper's Corollary `sparsecore`, whose sole open hypothesis was universal (SC_64). For clarity, when m<=4096 the capped contribution on the initial segment is below 65; for larger m the paper's dense-branch theorem handles H_64>=17/16, and the theorem proved here handles H_64<17/16. The paper's large-atom lemma costs one unit of threshold, and its nonnegative prime-power peel transfers the capped inequality to w_z. These are precisely the accepted hypotheses and conclusion of that corollary. QED.

**PROVED — Corollary 8.2 (absolute linear bound).** For every integer n>=1, every set 1<a_1<...<a_n of integers, and every integer x>=0, at most 81n integers from {x+1,...,x+a_n} have product divisible by a_1...a_n. Equivalently, with the paper's at-most convention, g(n)<=81n for all n.

Proof. This is the other conclusion of the same accepted sparse-core reduction. More explicitly, put m=a_n. If m>=8n^3, the paper's long-interval theorem supplies at most 2n elements. Otherwise the accepted duality lemma and Corollary 8.1 give an optimum fractional cover of cost at most 65n: for every dual weight z,

    sum_{a in A} w_z(a)
      <= 65n + sum_{k<=m}(w_z(k)-65)^+
      <= 65n + sum_{b in I}(w_z(b)-1)^+.

The accepted vertex-rounding lemma adds at most the number of primes dividing the product of A, which the accepted few-primes lemma bounds by 16n. Hence at most 81n elements suffice. QED.

OPEN (separate problem): neither this proof nor the accepted reduction gives g(n)<=2n or g(n)<=(2+o(1))n. The bound 81n closes the linear sparse-core route requested in the brief.

## 9. PROVED — exact verification record and its limits

The reproducible command is:

    python3 engine/out/astra_708_r16/exact_checks.py

PROVED (checked arithmetic): the exact positive cross-product gap certifying 2^23(187/768)^12<1/2 is

    5019318332045454244023631872
      - 2*1828518162230556187140793681
      = 1362282007584341869742044510 > 0.

PROVED (finite checks): the corrected suite passes all of the following checks, using only Python integers and fractions:

- 140 preprocessing systems, with 121 positive original threshold-64 hinges. The generator explicitly rejects a run in which all original hinges vanish.
- 24 exact dynamic-programming counts of weighted level subsets, including systems with 193 primes; a separate case tests tiny mass 1/64 and unit mass at different levels of the same prime.
- A nonzero threshold-16 system with 33 primes (the first 33 primes starting at 101), one prime having cumulative levels 1/2 and 1, and the other 32 having mass 1/2. The entire hot effective-pattern classification has 34 cases. It gives exactly

      L_B = 302500000000000000000426,

  11 carriers, and 309 combined signed divisor coefficients, of which 298 are negative. All carried-mass bounds and modulus-support bounds are checked exactly.
- Exact certificate values on five intervals, including reflected and centred highly divisible windows, satisfy the proved lower value bound. The test computes certificate values, not the full right hinge sum on these enormous intervals.
- 1,200 direct pointwise comparisons of the expanded signed divisor sum with formula (6) and with the right hinge.

REFUTED (negative controls, not conjecture counterexamples): the suite detects that the preprocessing loss cannot simply be replaced by 16; that the new weighted carrier-count bound fails if dyadic compression is omitted; and that replacing e<11/4 by e<3 does not certify the numerical estimate used here. Thus these checks can fail on incorrect variants of the argument. Exact inputs and output are in [exact_checks.json](exact_checks.json); [audit.md](audit.md) records the two test-generator/endpoint repairs made before the successful run.

PROVED (validation limit): these finite computations check the construction and its arithmetic. The universal theorem is justified by Lemmas 1–7, not by sampling the atom systems or windows. In particular no claim is made that a finite numerical search verified universal (NC).

## 10. Lean formalisation requirements

PROVED (dependency specification): a Lean formalisation of the sparse-core theorem needs the following finite constructions and lemmas. None is an additional unproved mathematical hypothesis; all new inequalities have proofs above.

1. **Finite atom and effective-level data.** Encode the finitely many primes and supported exponents, cumulative masses, divisibility indicators, positive parts, and intervals `Finset.Icc (x+1) (x+m)`. Establish the monotonicity of per-prime contributions and existence/uniqueness of effective retained levels.
2. **Dyadic rounding and pruning.** For each positive real cumulative value in (0,1], choose the largest 2^(-h) below it; prove t<=a<2t. Keep the first occurrence of each distinct value and apply the integer test q^(16*2^h)<=m. Prove that retained increments telescope, that the common-period mean cannot increase, and that the sum of the logarithms of distinct-prime divisors of k is at most log m.
3. **Prefix decomposition.** Define the decreasing-mass order with a deterministic tie break, rational overlap lengths with (2,3], carriers, their last dyadic mass, and M(P). Prove their finite sum is L_B, their masses lie in (2,4), and their moduli are less than m^(1/4).
4. **Hinge and elementary symmetric moments.** Formalise the pair-compression proof given after Lemma 2, the rescaling by theta, the expansion over distinct prime powers, coprimality, the floor bound, and r!e_r(h)<=H_B^r. Derive (2) at r=12/theta+1.
5. **Weighted carrier enumeration.** Use a finite generating sum (or polynomial with natural-number exponents) at 1/2. Prove 2^j>=j+1, the finite geometric bound on available dyadic levels, and the product bound 2^{N_theta}. Relate integer carriers injectively to their prime-level choices. Establish both (3) and (4).
6. **Constants.** Supply n!>=(n/e)^n via a standard factorial estimate or the elementary logarithmic integral above; prove e<11/4 from its series bound. The remaining arithmetic is rational and can be discharged by `norm_num`, including the displayed cross-product gap. An equivalent fully rational factorial lower-bound lemma would avoid analytic constants in the final certificate statement.
7. **Signed feasibility.** Define T_theta and U_P, prove the exact identity U_P=T_theta-theta*omega(P) when P|n, discard only nonpositive summands, and formalise the B<=2/B>2 split. The arbitrary-multiple issue is resolved by the cap at theta; no equality between b_p(n) and b_p(P) is required.
8. **Interval value and support.** Expand clipped increments only at primes outside P, prove gcd(P,q)=1 and Pq<m^(5/16)<=m, establish the two-sided multiple counts and floor(m/P)>=m/(2P), and sum the termwise positive and negative bounds. Combining repeated moduli is a finite-sum rearrangement.
9. **Composition.** Combine L<=2L_B, right-hinge monotonicity, pointwise feasibility, and the value lower bound to obtain R>=(141/128)L. Original real weights cause no limiting step: the derived system and the certificate have dyadic/rational coefficients.

PROVED (additional dependencies for g(n)<=81n): to formalise the final paper corollary as well, import or formalise its large-atom and dense-branch lemmas, prime-power peel, finite LP duality and attainment, vertex rounding, few-primes bound, and long-interval theorem. These are accepted inputs in this campaign, not new obligations left by the sparse-core proof.

OPEN (implementation): no Lean files or machine-checked theorem were produced in this campaign. The original (NC) likewise remains open and is not in the sparse-core theorem's dependency list.

## final claim ← lemmas ← unproved items

**PROVED:** (SC_64), in fact R >= (141/128)L for all m in the brief  
← **PROVED:** dyadic rounding/cost removal (Lemma 1), carried-mass moment bound (Lemma 2), dyadic weighted counting and level-mass sum (Lemmas 3–4), exact constant bound (Lemma 5), signed feasibility (Lemma 6), and interval value/support (Lemma 7)  
← **unproved items: none.** The elementary inherited moment facts are also proved explicitly above; (NC) is not used.

**PROVED:** threshold-65 hinge and g(n)<=81n for all n  
← **PROVED:** (SC_64) above + the accepted paper's sparse-core reduction, duality/rounding, few-primes and long-interval results  
← **unproved items: none within the campaign's accepted setting.** A Lean implementation is still to be written.

**OPEN:** original (NC), g(n)<=2n, and g(n)<=(2+o(1))n  
← no proof or counterexample asserted here  
← **unproved items: those separate statements themselves; none is required by the proved sparse-core theorem.**
