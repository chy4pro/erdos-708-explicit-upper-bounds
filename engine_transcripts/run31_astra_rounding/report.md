# Erdős 708 rounding campaign — final report

Campaign date: 2026-09-07. Started approximately 14:24 UTC. This campaign stops because T2 is proved, using “≫n” in its standard mathematical meaning Ω(n), and because the resulting proofs and exact experiments have been audited. No wall-clock cap was imposed. The success condition arrived before the 45-minute route review points and before a 30-minute periodic checkpoint was due. Initial and closing checkpoints are retained. Unresolved alternatives are marked OPEN, not falsely declared settled or frozen.

## Outcome and claim ledger

Here G=G(A,x) is the optimum for one instance, τ is the **original uncapped** LP of Section 7, and g(n) is the worst-case optimum over n-element inputs.

| Status | Claim | Proof / exact evidence |
|---|---|---|
| **PROVED** | **g(n)≤19n for every n≥1.** | R2: threshold17, strict vertex rounding, r≤n+π(√m), supplied k-split with k=3, and π(3n)≤n+1. |
| **PROVED** | **g(n)≤18n+π((18n)^(19/34))−1=18n+o(n).** In particular the explicit error (18n)^(19/34)−1 suffices. | R2: k-split with k=18 and the same row count. The elementary prime estimate additionally gives O(n^(19/34)/log n). |
| **PROVED** | g(n)≤min{19n,20n−2,18n+π((18n)^(19/34))−1}. | Combine the two displayed theorems with the independent r<3n improvement in m<8n³. |
| **PROVED T2** | For every n and integer K≥2, explicitly computable instances have G=n, τ=n/K, and loss (1−1/K)n. | P1: exact CRT construction and matching rational primal/dual certificates. |
| **REFUTED** | Uniform additive o(n) rounding for the original LP; any fixed G≤ατ+C; any fixed G≤τ+cn+C with c<1. | P1 with K=n, n≥2. |
| **OPEN** | Universal additive-n rounding G≤τ+n. | The constructed losses are strictly below n; no proof or counterexample to this alternative is obtained. |
| **PROVED** | Demand-capped LP is integral-equivalent to the original problem and has value τ_cap≤17n. More general finite monotone prime-valuation cover LPs also have value≤17n. | R3 generalized hinge theorem, derived from the supplied atom-system hinge17. |
| **PROVED / REFUTED equivalence** | Separate prime-power level LP has value≤17n and yields valid original covers, but its integral optimum can be n when the original optimum is 1. | R3, complete one-prime construction. |
| **OPEN** | Additive-n integrality loss for capped or level LPs; lowered T3's universal statement for m≥n^(2+ε). | No unsupported extension is claimed; T3 was not activated after T2 success. |
| **REFUTED** | Automatic laminar/TU incidence; proposed β_H≤G−τ comparison. | F1 explicit crossing sets and determinant; F2 exact τ=3/10, G=1, β_H=5. |
| **PROVED, finite** | 93 logged jobs, 85 distinct instances, all optima settled exactly; maximum observed (G−τ)/n=99/100. | Exact ledger, primal/dual certificates, DP and upper/lower repairs; independent verification. |
| **CONDITIONAL** | If τ_cap's additive integrality gap were≤n, its proved value bound would imply g(n)≤18n. | R3: G≤τ_cap+n≤18n. The rounding premise remains unproved. |

The first two global upper bounds are new mathematical deductions from the supplied proved tools. They do **not** establish a universal instancewise rounding loss n+o(n): long intervals are handled by an absolute cover theorem instead of an LP comparison. The additive-n alternative of T1 remains open. No claim is made of superlinear rounding loss, of loss exceeding n, or of a solution to Erdős's conjectured 2n bound.

These new deductions were independently audited as mathematical proofs. They have **not** been formalized or newly checked by Lean in this campaign. The existing threshold17 and k-split theorems are accepted black boxes as directed by the brief. No internet or git was used, and no publication-priority claim is made.

## Short proof of the principal global bound

Put r=number of demanded primes. Every input a≤m has at most one distinct prime divisor greater than √m, so

    r≤n+π(√m).

The exact vertex rounding argument gives G<τ+r, and the supplied threshold17 gives τ≤17n. If m<9n², this yields

    G<18n+π(3n), hence G≤18n+π(3n)−1.

If m≥9n², the supplied k=3 theorem gives G≤3n, below the same expression. Exactly n integers in [1,3n] are coprime to 6. Removing 1 and adding the primes 2 and 3 gives π(3n)≤n+1. Therefore **g(n)≤19n**.

For the asymptotic refinement, use k=18 instead. If m^(17)≥(18n)^(19), then G≤18n. Otherwise √m<(18n)^(19/34), and the same argument gives

    G≤18n+π((18n)^(19/34))−1.

Since π(t)≤t and 19/34<1, the error is explicitly o(n). The expression is at least 18n for all n≥1, so both interval regimes are covered. These proofs are uniform in x, including the CRT valuation-inflation instances.

## Exact search, witnesses, and reproduction

The refutation agent started first. Its main ledger has 80 attempted jobs on 73 distinct instances; five DP state-space exclusions were later settled by exact rational LP lower bounds whose ceilings match separately verified integral covers. R3 contributes 13 more jobs, with one duplicate of a main-ledger instance. The total is therefore 93 jobs and 85 distinct instances, all settled. Every actual tested instance has its A, x, τ, G and witnesses in `refutation_results.jsonl` or `r3_exact.jsonl`, with a full table and methods in `refutation_log.md`. The maximum 99/100 is attained in all twelve K=100 unique-spike tests.

A largest-n maximizing witness is

    A=[101,103,107,109,113,127,131,137,139,149,151,157],
    n=12, m=157, K=100, t_i=78+i (i=0,...,11),
    x = the least nonnegative solution of
        x≡p_i^100−t_i (mod p_i^101),
    B={x+78,...,x+89},
    τ=3/25, G=12, G−τ=297/25, (G−τ)/n=99/100.

The explicit CRT formula in P1 specifies x exactly without printing thousands of digits; its full integer value is retained in the JSONL. Assigning weight 1/100 to each b∈B is an optimal primal solution, and z_p=1/100 on each input prime is an optimal dual solution. Every demanded prime has exactly one multiple in I, proving the integral lower bound 12.

The largest nonspike normalized loss found was 7/18, at A=[323,391,437], x=88930, τ=17/6 and G=4. The familiar x=74072 for the same A has τ=3 and G=4. Neither the ES lower bound on G nor the earlier τ/n→2 construction alone supplies an integrality-gap lower bound; both optima must be compared on the same instance.

Numerical LP optimization only proposes candidates. Every retained LP optimum is established by rational primal feasibility, rational dual feasibility including the upper-bound hinge penalties, and exact equality of their values. The **LP uses full v_p(b)**. Demand capping is used only by the exact integral DP, where it is equivalent, or in the separately labeled modified LP experiments.

The DP uses the exact recurrence over capped valuation states s:

    F_{j+1}(s)=min(F_j(s), 1+F_j((s−v_j)^+)),
    F_0(0)=0, F_0(s)=infinity for s≠0.

Here F_j(s) is the smallest number of the first j distinct candidate positions covering at least s. Exclusion and inclusion are the two exhaustive possibilities, proving the recurrence by induction. Grouping identical vectors and retaining at most min(available copies,max_{v_p>0}ceil(R_p/v_p)) copies is exact: that many copies already saturate every affected row. The sparse variant stores achieved capped states with the equivalent exclusion/inclusion recurrence. Tracebacks supply the retained covers. The unmodified repository DP was also used on the key small witnesses. For the five repaired HR jobs, a verified cover of size ceil(τ) and the exact rational dual prove optimality without a floating-point MIP lower bound.

Independent verifier commands, from the repository root:

```sh
python3 -B engine/out/astra_708_rounding/final_verify.py
python3 -B engine/out/astra_708_rounding/refutation_verify.py
python3 -B engine/out/astra_708_rounding/r3_verify.py
```

The first checks all original LP certificates, all integral witnesses, unique-spike optimality, repaired HR optimality, and all R3 exact values. It records source hashes in `final_verification.json`. It does not claim to rerun every DP optimum; the other DP lower bounds come from the exhaustive recurrences actually run during the search. The refutation verifier is independent of optimization packages. The search generator and its existing SciPy interpreter are documented in `refutation_log.md`; rerunning search modes appends to the historical ledger.

The global-memory skill was read, but no recall_presets tool was exposed, so no presets or user_notice were retrieved or invented. All campaign outputs are confined to `engine/out/astra_708_rounding/`.

## Complete proofs

The following sections reproduce the complete root, R2 and R3 proof notebooks. Repeated weaker bounds are retained with their proofs; the final strongest claims are those in the ledger above. References to the supplied threshold17, k-split and existing graph criterion are accepted inputs, not new unproved assumptions.


---

# Root proof notebook

Notation: A is a set of n≥1 distinct integers >1, m=max A, I={x+1,…,x+m}, R_p=Σ_{a∈A}v_p(a), G the integral minimum, and τ the paper's original (uncapped) valuation LP optimum. All proofs below are mathematical proofs; no new Lean kernel check is claimed.

## P1 — PROVED: exact linear integrality loss, with arbitrarily small fractional optimum

For every n≥1 and every integer K≥2 there is an explicitly computable instance with

    G=n,    τ=n/K,    G−τ=(1−1/K)n.

Choose n primes p_1<…<p_n in a band [Q,4Q/3), with Q≥6n, and put m=p_n. One deterministic rule is to enumerate Q=ceil((4/3)^j), j≥1, until the half-open band contains at least n primes and Q≥6n, then take its first n primes. Alternatively enumerate every integer Q≥6n; the termination proof below applies to this simpler rule. Put t_i=floor(m/2)+i for i=1,…,n. These are distinct integers in [1,m] and satisfy

    m−p_1 < t_i ≤ p_1.

Indeed p_1>m/2, giving the lower inequality, while t_i≤m/2+n<2Q/3+n≤5Q/6<Q≤p_1. Also n≤m/6, so the offsets are in the interval.

Set M_i=p_i^(K+1), M=∏_i M_i, and choose the least nonnegative solution of

    x ≡ p_i^K−t_i (mod M_i)  for all i.

This is fully explicit: if h_i is the inverse of M/M_i modulo M_i, then

    x = [Σ_i (p_i^K−t_i)(M/M_i)h_i] mod M.

The inverse exists by coprimality, and substitution verifies every congruence. Thus v_{p_i}(x+t_i)=K exactly. The multiples of p_i have offsets congruent to t_i modulo p_i. Because t_i−p_i≤0 and t_i+p_i>m, x+t_i is the **only** multiple of p_i in I. The n designated positions are distinct. Consequently the demanded-prime valuation matrix has precisely n nonzero columns, namely K times the respective unit vectors.

Take A={p_1,…,p_n}. Each demand R_{p_i}=1. Every integral cover must contain all n designated positions, and those positions suffice, so G=n. Each LP row reads K y_{x+t_i}≥1. The primal assignment y=1/K at those n positions and 0 elsewhere has cost n/K. The dual assignment z_{p_i}=1/K has w_z=1 at each designated position and 0 elsewhere, so its upper-bound penalties vanish and its value is n/K. These matching exact certificates prove τ=n/K.

### Termination of the prime-band search

The reciprocal sum of primes diverges. A short proof: if it converged, then −log(1−1/p)≤2/p would bound every finite Euler product ∏_{p≤N}(1−1/p)^−1 uniformly. Expanding its geometric series shows that this product is at least Σ_{k≤N}1/k, which is unbounded, a contradiction.

For any fixed n there are arbitrarily late geometric bands [(4/3)^j,(4/3)^(j+1)) containing at least n primes. Otherwise their reciprocal contributions are eventually at most (n−1)(3/4)^j, a convergent geometric series, again a contradiction. If such a band has n primes, put Q=ceil((4/3)^j). Every prime in the band is at least Q and less than (4/3)Q. Thus the integer-Q search succeeds, and can succeed with Q≥6n.

### Consequences, with precise quantifiers

* **PROVED T2 (Ω(n)):** fix K=100 to get loss 99n/100 for every n. Taking K=n for n≥2 gives τ=1 and G=n, with loss n−1.
* **REFUTED:** there is a uniform h(n)=o(n) such that G≤τ+h(n) for all instances. The K=n family contradicts this.
* **REFUTED:** for fixed finite α,C, G≤ατ+C for all instances. On K=n this would require n≤α+C for all n. This includes the stated (1+ε)τ+C alternative for fixed ε,C.
* **REFUTED:** any uniform additive cn+C comparison with fixed c<1. Again n−1 eventually exceeds cn+C.
* **OPEN:** G≤τ+n for all instances. P1 has G−τ<n and does not refute this alternative.
* P1 does not prove a superlinear loss or any loss exceeding n. The brief's notation “≫n” is used in its standard Ω(n) meaning.

## P2 — PROVED: exact form of vertex rounding

Let r be the number of demanded primes, which is positive since n≥1 and A consists of integers >1. At an optimal vertex y, at most r coordinates are fractional (the paper's vertex argument). If F={b:0<y_b<1}, the support cover has size

    τ + Σ_{b∈F}(1−y_b).

If F is nonempty, this is strictly less than τ+|F|≤τ+r. If F is empty its size is τ<τ+r as well. Thus

    G < τ+r.

This is only a sharpened strict version of the existing rounding lemma; it does not justify loss≤n. P1 exhibits an arithmetic diagonal submatrix K·Id with n fractional coordinates and exact rounding cost n(1−1/K). Hence neither integrality of demands nor prime incidence by itself can yield a sublinear raw-LP rounding theorem.

## F1 — REFUTED: the cross-prime constraint sets are laminar or automatically totally unimodular

For primes 2 and 3 in [1,6], the divisibility sets meet at 6 but have exclusive elements 2 and 3. They are not nested, so they are not laminar. Even restricting to squarefree coefficients, columns 6,10,15 and rows 2,3,5 give the matrix

    [1 1 0]
    [1 0 1]
    [0 1 1]

with determinant −2. Thus a blanket total-unimodularity assertion for the prime incidence matrix is false. This is a matrix obstruction, not a claim that a particular Erdős instance has the generic triangle LP gap; the full interval contains other columns.

## F2 — REFUTED: input cycle excess is bounded by the actual LP rounding loss

Let A={30,42,70,105}, m=105, u=210^10, x=u−1. The demand at each of 2,3,5,7 is 3. The point u alone is an integral cover, so G=1. The fractional assignment y_u=3/10 covers all demands at cost 3/10. For 1≤t≤104, v_2(u+t)=v_2(t)≤6, whereas v_2(u)=10. Therefore the single dual weight z_2=1/10, all others 0, has no upper-bound penalties and value 3/10. Hence

    τ=3/10,   G−τ=7/10.

All four inputs have three distinct prime factors, so none is discarded in the pseudoforest theorem. The shared-prime bipartite incidence graph has 8 vertices, 12 edges, and one connected component, hence cycle rank β_H=12−8+1=5. Consequently β_H≤G−τ is false, by 5>7/10. Even the alternative convention measuring cycles beyond one per component gives excess 4, still greater than 7/10.

This refutes that proposed R5 comparison only. It does not refute the supplied G≤2n+2β_H bound or any unformulated inequality with a different right-hand side.


---

# R2: proved row-count improvements and the exact preprocessing gap

All notation is that of Section 7 of `papers/erdos708/main.tex`: A is a set of n distinct positive inputs, m=max A, I={x+1,...,x+m}, P is the set of demanded primes, r=|P|, R_p=sum_{a in A}v_p(a), tau* is the bounded covering LP optimum, and G is the integral optimum. No assertion here is kernel checked. The threshold-17 theorem and the long-interval 2n theorem are used as the supplied proved black boxes.

## PROVED: a sharper extreme-point rounding inequality

If r>0, then

    G < tau* + r.

Take an optimal LP vertex y. At most r coordinates are strictly between zero and one: otherwise their columns in the r covering rows are linearly dependent, and a sufficiently small perturbation in both directions preserves the covering sums and the box bounds, contradicting extremality. Round those coordinates upward. If there are f>0 fractional coordinates, the increase is sum_{fractional b}(1-y_b)<f<=r. If f=0 the increase is zero<r. This proves the strict inequality. If r=0, then G=tau*=0.

The original non-strict inequality G<=tau*+r also suffices for the uniform 20n-1 result below.

## PROVED: uniformly r<3n when m<8n^3

List the support primes in increasing order. The i-th of them is at least the i-th prime and hence at least 2i-1 (including i=1). Suppose r>=3n. The concavity of log gives, on every interval [i-1,i],

    log(2i-1) >= integral_{i-1}^{i} log(2t) dt.

The improper integral at zero converges. Summing, with k=3n, yields

    log product_{i=1}^{3n}(2i-1)
      >= integral_0^{3n} log(2t) dt
       = 3n log(6n/e)
       > 3n log(2n),

because e<3. Thus product_{p in P}p > (2n)^{3n}=(8n^3)^n. But product_{p in P}p divides product A, so it is at most product A<=m^n<(8n^3)^n, a contradiction. Consequently r<=3n-1.

The inequality e<3 can, if desired, be obtained directly from e=sum_{j>=0}1/j!: the tail from j=2 is strictly less than sum_{j>=2}2^{-(j-1)}=1.

## PROVED: the sharper count r<=2n+pi(m^(1/3))

Set y=m^(1/3). Every a<=m contains at most two distinct prime divisors exceeding y, since a product of three such primes exceeds y^3=m. Consequently the number of distinct demanded primes exceeding y is at most 2n. There are at most pi(y) other primes. Therefore

    r <= 2n + pi(m^(1/3)).

In the critical regime m<8n^3, this implies

    r <= 2n + pi(2n).

This last inequality is obtained just by counting distinct primes; it does not assign any large-prime cover and incurs no unaccounted preprocessing cost. The premise about at most two large-prime valuation units is already recorded as P11 in `engine/harvest/astra_708_2n.md`; the consequence for the rounding constant is immediate but was not drawn there.

More generally, for every integer k>=1,

    r <= k n + pi(m^(1/(k+1))).

This follows by exactly the same product argument. In particular, r<=n+pi(sqrt(m)). It gives additive n+o(n) in the restricted regime pi(sqrt(m))=o(n), for example m<=n^2. It does not imply additive n for arbitrary m.

## PROVED: explicit elementary prime-count error

For t>=2,

    pi(t) <= sqrt(t) + 8 (log 2) t / log t.

Write theta(t)=sum_{p<=t}log p. For each integer j>=1, every prime in (2^{j-1},2^j] divides binomial(2^j,2^{j-1}); hence

    theta(2^j)-theta(2^{j-1}) <= 2^j log 2.

If L=ceil(log_2 t), summing gives

    theta(t)<=theta(2^L)<2^{L+1}log 2<=4t log 2.

There are at most sqrt(t) primes up to sqrt(t); each other prime contributes more than (log t)/2 to theta(t). The claimed estimate follows. In particular pi(t)=o(t), with the displayed completely explicit error.

## PROVED: consequences with the supplied threshold 17

The fractional bound tau*<=17n and the original rounding lemma give, when m<8n^3,

    G <= 20n-1,
    G <= 19n + pi(m^(1/3))
      <= 19n + pi(2n).

The strict rounding statement improves the latter integer bound to

    G <= 19n + pi(m^(1/3)) - 1
      <= 19n + pi(2n) - 1

when P is nonempty. The corresponding statement with r=0 follows separately because G=0 and n>=1. In the long regime m>=8n^3, the supplied theorem gives G<=2n, which is below both uniform expressions. Thus, uniformly in all A and x,

    g(n) <= min(20n-2, 19n+pi(2n)-1)
          <= 19n + sqrt(2n) + 16(log 2)n/log(2n)-1,

and in particular g(n)<=19n+o(n). The strict rounding statement likewise gives G<=20n-2 from r<=3n-1. The non-strict form 19n+pi(2n) is also valid if one prefers to use the paper's rounding lemma exactly as stated.

These are mathematical consequences of the supplied hinge theorem, not claims that the new constants have been formalized or independently established in this note.

## PROVED: exact preprocessing accounting

For any integral set S subset I, let r_p(S)=max(0,R_p-sum_{b in S}v_p(b)), and let tau_S* be the bounded LP on I minus S for those residual demands. Its feasible region is nonempty, since all remaining positions suffice. Let s(S) be the number of positive residual demands. Then

    Delta_S := |S| + tau_S* - tau* >= 0,
    G <= tau* + Delta_S + s(S).

For every optimal original LP solution y,

    0 <= Delta_S <= sum_{b in S}(1-y_b) <= |S|.

Indeed adjoining S to a residual fractional cover gives a feasible original fractional cover, proving the lower bound. Retaining y outside S is feasible for the residual LP, because replacing y by 1 on S can only increase every supplied valuation. Thus tau_S*<=tau* - sum_{b in S}y_b, proving the upper bound. Round a residual optimal vertex with its s(S) rows and adjoin S to prove the covering inequality.

For primes p>sqrt(m), each input contains at most one such prime and its exponent is one. All those demands can be met with some S of cardinality at most n: for each such p, choose R_p distinct multiples of p in I. There are enough because R_p is the number of distinct inputs divisible by p, which is at most floor(m/p), while I has at least floor(m/p) multiples. Unions across primes can overlap. Consequently

    G <= tau* + n + pi(sqrt(m)).

This reproduces the k=1 direct row-count bound, and proves no uniform additive n result because pi(sqrt(m)) need not be o(n) in the full critical regime m<8n^3.

## OPEN / unresolved gap

The route that selects all primes p>2n first only provides the elementary cardinality bound |S|<=2n; it does not prove Delta_S<=n. To obtain additive n+o(n) throughout the critical regime by this route, the missing statement is the existence of S covering those large-prime demands with Delta_S<=n+o(n). To obtain additive n exactly, even the remaining pi(2n) row cost must be absorbed. No claim of such absorption or of a uniform additive n theorem is made here.

Dependency graph: 19n+pi(2n)-1 and 20n-2 <- threshold17 + long-interval2n + extreme-point rounding + the two elementary prime counts; no unproved item in these implications. Universal additive n <- a missing preprocessing/rounding lemma; OPEN.

## PROVED: combining k-split with row counting gives 18n+o(n)

This improvement uses the full supplied k-split theorem, not just its k=2 long-interval special case. That theorem states that G<=kn whenever m^{k-1}>=(kn)^{k+1}, for every integer k>=2. Its exact statement and proof are in `papers/erdos708/main.tex`, Theorem `thm:ksplit` and Section 5 (`sec:ksplit`).

Let k be any integer with 2<=k<=18, and put

    T_k(n)=(kn)^((k+1)/(k-1)),
    Y_k(n)=sqrt(T_k(n))=(kn)^((k+1)/(2(k-1))).

If m>=T_k(n), k-split gives G<=kn<=18n. If m<T_k(n), the already proved count r<=n+pi(sqrt(m)) gives r<=n+pi(Y_k(n)). Apply tau*<=17n and strict rounding to get

    G < 18n+pi(Y_k(n)),
    G <= 18n+pi(Y_k(n))-1.

This expression is at least 18n, because Y_k(n)>2 for n>=1 and 2<=k<=18. It therefore also dominates the outer-regime bound kn. Consequently the global theorem is

    g(n) <= 18n + pi(Y_k(n)) - 1   (2<=k<=18).

In particular k=3 gives the especially simple statement

    g(n) <= 18n + pi(3n) - 1 = 18n+o(n).

Taking k=18 gives a smaller asymptotic error:

    Y=(18n)^(19/34),
    g(n) <= 18n + pi(Y) - 1
          <= 18n + Y - 1,

so the explicit sublinear error can be taken to be (18n)^(19/34)-1. The elementary prime-count estimate above further gives

    g(n) <= 18n + sqrt(Y) + 8(log 2)Y/log(Y) - 1
           =18n+O(n^(19/34)/log n).

For finite n one may minimize over k, without asserting that k=18 is always optimal. Combining all our certified expressions yields

    g(n) <= min(20n-2,
                min_{2<=k<=18} [18n+pi((kn)^((k+1)/(2(k-1))))-1]).

Among fixed choices k<=18, k=18 minimizes the power of n in the displayed error, since (k+1)/(2(k-1)) decreases with k. Choices k>=19 give an outer bound kn>=19n and hence do not by this same argument preserve the leading coefficient 18.

Status distinction: this proves the global conclusion g(n)<=18n+o(n). It proves the instancewise rounding estimate G<=tau*+n+pi(Y) for m<T_18(n). It does NOT prove G<=tau*+n+o(n) for every interval length: the outer regime uses the absolute bound G<=18n, and tau* can be arbitrarily small there. The stronger universal additive-n statement remains OPEN.

Dependency graph: 18n+pi((18n)^(19/34))-1 <- supplied threshold17 + supplied k-split(k=18) + strict vertex rounding + r<=n+pi(sqrt(m)); no unproved item in this implication. These deductions have not been formalized in Lean in this campaign.

## PROVED: a uniform 19n bound, including small n

For every integer n>=1,

    pi(3n)<=n+1.

Among the integers in [1,3n], exactly n are coprime to 6. Indeed, if n=2h then [1,3n]=[1,6h] contains two such integers per block of six, giving 2h=n. If n=2h+1, the additional block [6h+1,6h+3] contributes exactly one, giving 2h+1=n. Every prime other than 2 and 3 belongs to this coprime set, and 1 is in that set but is not prime. Adding the two primes 2 and 3 therefore gives pi(3n)<=n-1+2=n+1. This includes n=1, where pi(3)=2=n+1.

The k=3 global theorem above now yields

    g(n)<=18n+pi(3n)-1<=19n    (n>=1).

For n>=9, the coprime set also contains the nonprime 25, so pi(3n)<=n, and consequently g(n)<=19n-1. No finite computation or prime-density theorem is needed for these statements.

A convenient combined final bound from this note is

    g(n)<=min(19n, 20n-2, 18n+pi((18n)^(19/34))-1).

For n=1 the outer k=3 bound is 3, and the displayed k=3 expression is 18+pi(3)-1=19, so the regime comparison used above is valid. The simpler exact fact g(1)=1 also follows by choosing any multiple of the single input in an interval of that input's length; it is not needed for the uniform coefficient argument.

Dependency graph: uniform19n <- k-split(k=3) + threshold17 + strict vertex rounding + r<=n+pi(sqrt(m)) + the elementary coprime-to-6 count; no unproved item.


---

# R3: demand truncation, level covers, and the threshold bridge

Status: the threshold bridge below is **PROVED** from the supplied atom-system threshold-17 theorem. An additive integrality gap at most n for these modified LPs remains **OPEN**. None of the arguments below proves the original additive-n target.

## 1. A general monotone-valuation hinge theorem — PROVED

Let P be a finite set of primes and let f_p: Z_{≥0} → R_{≥0} be nondecreasing functions with f_p(0)=0. Set

    W(k) = Σ_p f_p(v_p(k)).

For every m≥1 and x≥0, with I={x+1,...,x+m},

    Σ_{k=1}^m (W(k)−17)^+ ≤ Σ_{b∈I} (W(b)−1)^+.

Proof. Write s_p(v)=min(f_p(v),1), e_p(v)=(f_p(v)−1)^+, S(k)=Σ_p s_p(v_p(k)), E(k)=Σ_p e_p(v_p(k)). Then W=S+E. Both s_p and e_p are nondecreasing and vanish at zero. Restrict their increments to j≤J_p, where J_p is the largest valuation appearing among the finitely many integers under consideration. The increments α_{p,j}=s_p(j)−s_p(j−1) are nonnegative and sum to s_p(J_p)≤1 at each prime. Thus S, on all relevant integers, is exactly an atom system covered by Theorem threshold 17 in papers/erdos708/sec_h17.tex (and Erdos708H17.hinge17 in the existing Lean development).

The increments β_{p,j}=e_p(j)−e_p(j−1) are also nonnegative. Every m consecutive integers contain at least floor(m/p^j) multiples of p^j. Expanding E into those increments consequently gives

    Σ_{k=1}^m E(k) ≤ Σ_{b∈I} E(b).

Pointwise, (W−17)^+≤E+(S−17)^+. Also (W−1)^+=E+(S−1)^+: if E>0 then at least one s_p=1, so S≥1; if E=0 the identity is immediate. Sum these relations and apply the atom-system hinge theorem. This proves the assertion. No upper bound on f_p, or on its individual increments, is required.

## 2. A general fractional-cover corollary — PROVED

Fix A={a_1<...<a_n}, m=a_n, and I as above. Take finitely many covering rows indexed by (p,t), with a nonnegative nondecreasing profile h_{p,t}(v), h_{p,t}(0)=0. Suppose their demands d_{p,t} satisfy

    0 ≤ d_{p,t} ≤ Σ_{a∈A} h_{p,t}(v_p(a)).

Consider min Σ_b y_b subject to Σ_b h_{p,t}(v_p(b))y_b≥d_{p,t}, 0≤y_b≤1. It is feasible: the full interval dominates [1,m] separately for every nonnegative prime-power increment. Its value is at most 17n.

Proof. The standard finite LP dual, after eliminating the upper-bound multipliers, has objective

    Σ_{p,t} z_{p,t}d_{p,t} − Σ_{b∈I}(W(b)−1)^+,  z≥0,
    W(k)=Σ_{p,t} z_{p,t}h_{p,t}(v_p(k)).

For each p, f_p(v)=Σ_t z_{p,t}h_{p,t}(v) is a monotone profile. The demand assumption and the generalized hinge imply that this objective is at most

    Σ_{a∈A}W(a) − Σ_{k=1}^m(W(k)−17)^+ ≤ 17n.

The last inequality follows by W(a)≤17+(W(a)−17)^+ and A⊆[1,m]. Strong duality proves the claim. A cube restriction on z is unnecessary.

## 3. Demand-capped LP — PROVED formulation and threshold, OPEN rounding

Put R_p=Σ_{a∈A}v_p(a), c_{p,b}=min(v_p(b),R_p), and let τ_cap minimize Σ_b y_b subject to Σ_b c_{p,b}y_b≥R_p, 0≤y_b≤1.

For a 0/1 vector y, the capped and original covers are equivalent. One direction uses c_{p,b}≤v_p(b). For the converse, if a selected b has v_p(b)≥R_p, its capped contribution alone is sufficient; otherwise all selected contributions are unchanged. This works independently for every demanded prime.

The corollary in Section 2 gives τ_cap≤17n: take h_p(v)=min(v,R_p), and observe h_p(v_p(a))=v_p(a). Therefore

    τ_raw ≤ τ_cap ≤ g(A,x),    τ_cap ≤ 17n.

The original vertex-count rounding argument applies with the same |P| rows, giving g(A,x)≤τ_cap+|P|. No argument here improves |P| to n. On the isolated-prime CRT family supplied by the root agent, each prime has demand one and occurs in exactly one distinct interval position. The capped LP forces those n coordinates to one, so τ_cap=g=n, whereas τ_raw=Σ_i 1/v_{p_i}(x+t_i) can tend to zero. Hence τ_cap cannot be bounded by ατ_raw+C for fixed α,C on all n. The threshold bridge above avoids that false comparison.

Merely adding rows min(v,q) with demand min(R_p,q), 1≤q≤R_p, does not strengthen this capped LP: pointwise min(v,q)/q≥min(v,R_p)/R_p, so the R_p row implies every one of these rows fractionally. Substantial strengthening requires other inequalities, for example knapsack-cover inequalities depending on a preselected set; a threshold bridge for such inequalities is not supplied here.

## 4. Separate prime-power levels — stronger formulation, not equivalent

Let L_p=max_{a∈A}v_p(a) and N_{p,j}=#{a∈A:v_p(a)≥j}. Impose

    Σ_{b∈I:p^j|b} y_b ≥ N_{p,j},  1≤j≤L_p.

The LP is feasible because N_{p,j}≤floor(m/p^j). Summing its rows for one prime shows that every 0/1 feasible solution covers the original valuation demand (indeed the summed coefficient is min(v_p(b),L_p)). The converse fails. The value τ_level≤17n follows from Section 2 with h_{p,j}(v)=[v≥j]. Its general additive integrality gap at most n is **OPEN** here. The number of level rows can exceed the original number of prime rows.

Exact counterexample to integral equivalence: A={2,4}, x=4, I={5,6,7,8}. Original demand R_2=3 is covered by {8}; τ_raw=τ_cap=g=1. The level-1 constraint demands two even selected integers, so τ_level=2 and the level-integral optimum is 2, witnessed by {6,8}.

Unbounded amplification: for n≥1 let A={2,2^2,...,2^n}, R=n(n+1)/2, m=2^n, choose K≥max(R,n), and set x=2^K−2^n. The endpoint 2^K covers the entire original demand. Its valuation K is the largest valuation in I, so

    g=1,  τ_cap=1,  τ_raw=R/K,  τ_level=g_level=n.

The original fractional lower bound is R≤KΣ_b y_b and is attained at the endpoint. The capped lower bound is R≤RΣ_b y_b and is attained there. The first level demands Σ_{2|b}y_b≥n. A level-integral cover of size n consists of the endpoint and 2^K−2^j for 1≤j≤n−1; their valuations are K,1,...,n−1 and they lie in I. Thus every stated optimum is exact. This refutes a uniform comparison τ_level≤τ_raw+o(n), as well as τ_level≤ατ_raw+C for fixed α,C.

The associated flow interpretation is valid but is stronger than the original cover. For each prime, create one unit task per a divisible by p, requiring a position divisible by p^{v_p(a)}. A position has capacity y_b for that prime. The neighborhoods are nested by exponent, and the level inequalities are precisely the nested Hall capacity inequalities. Integral solutions forbid one position from serving two tasks of the same prime, although its valuation could suffice for their sum in the original problem. That distinction is exactly what the counterexample exposes.

## 5. Independent audit of the root's improved support bounds — PROVED

Assume m<8n^3=(2n)^3 and let r be the number of distinct primes in the product of A.

First, an input a≤m has at most two distinct prime factors exceeding 2n, since three would have product >(2n)^3>m. Thus r≤2n+π(2n). Original LP rounding and τ_raw≤17n give

    g(A,x)≤19n+π(2n).

Second, write p_i for the i-th prime. Then p_i≥2i−1 for every i≥1. Concavity of log, applied on [i−1,i] (the improper integral for i=1 converges), gives

    log(2i−1) ≥ ∫_{i−1}^i log(2t) dt.

If r≥3n, then

    log ∏_{p|∏A}p ≥ Σ_{i=1}^{3n}log(2i−1)
       ≥ 3n log(6n/e) > 3n log(2n),

using e<3. But ∏_{p|∏A}p≤∏A≤m^n<(2n)^{3n}, a contradiction. Therefore r≤3n−1 and

    g(A,x)≤20n−1.

In the complementary long-interval range the supplied theorem gives g(A,x)≤2n, which is below both displayed bounds for n≥1. Both bounds therefore hold globally, and their minimum can be taken. The asymptotic 19n+o(n) additionally uses the standard fact π(2n)=o(n). These support improvements do not prove an additive-n rounding loss.

## 6. Independent audit of the stronger k-split combination — PROVED

The supplied Theorem ksplit in papers/erdos708/main.tex states that m^{k−1}≥(kn)^{k+1} suffices for a cover of size at most kn. Take k=18 and define

    T_n=(18n)^{19/34},  M_n=T_n^2=(18n)^{19/17}.

If m≥M_n, ksplit gives G≤18n. If m<M_n, every input a≤m has at most one distinct prime divisor exceeding √m, since two such primes have product >m. Thus the support size satisfies

    r ≤ n+π(√m) ≤ n+π(T_n).

At an optimal vertex of the original LP, the support cover has size τ+Σ_{0<y_b<1}(1−y_b)<τ+r. This remains strict when there are no fractional coordinates because r≥1 (A consists of integers greater than one). Combining with τ≤17n and the integrality of G, n, and π(T_n) gives

    G ≤ 18n+π(T_n)−1.

As T_n≥2 for n≥1, π(T_n)≥1, and this same bound includes the outer ksplit regime. Consequently the global theorem is

    g(n) ≤ 18n+π((18n)^{19/34})−1
         ≤ 18n+floor((18n)^{19/34})−1 = 18n+o(n).

The explicit final inequality requires no prime-distribution estimate. The sharper error O(n^{19/34}/log n) follows from the standard Chebyshev upper bound for π. The simpler split k=3 uses m≥9n^2 to get G≤3n, and below that cutoff r≤n+π(3n), yielding g(n)≤18n+π(3n)−1 globally; its o(n) conclusion uses π(3n)=o(n).

These are global cover bounds. They do not prove a uniform all-instance comparison G≤τ+n+o(n), because the large-m branch uses ksplit in place of a comparison with τ. In the small-m branch alone, the displayed argument does prove G<τ+n+π(T_n).

The simple k=3 bound also gives the uniform inequality g(n)≤19n for every n≥1, without analytic prime estimates. Exactly n integers in [1,3n] are coprime to 6: for n=2q there are q complete blocks of six with two such integers each; for n=2q+1 the extra three integers contribute exactly one. All primes greater than 3 belong to these n integers, and 1 is one of the n but is not prime. As 2 and 3 are both in [1,3n], this yields π(3n)≤(n−1)+2=n+1. Therefore 18n+π(3n)−1≤19n. This audit includes the endpoint n=1.

I also independently checked the current root theory.md arguments P1, P2, F1, and F2: the exact CRT valuation congruences, narrow-band termination proof, strict rounding, non-TU matrix witness, and cycle-excess counterexample are valid as stated.

## Dependency and unresolved gap statement

Modified LP threshold 17 ← generalized monotone-valuation hinge ← existing atom-system hinge17 + elementary prime-power multiple counts + finite LP duality. No unproved item occurs in this chain. Integral equivalence of demand capping is elementary. Additive-n rounding for demand-capped or level LPs remains unproved; the generalized hinge solves the value bridge only.

Gap sentence: demand capping removes the explicit valuation-inflation obstruction while preserving threshold 17, but an additive integrality gap at most n for the capped LP is still OPEN.

---

## Final dependency block

**Final claim ← lemmas ← unproved items**

* **PROVED uniform 19n:** g(n)≤19n ← k=3 split plus G<τ+r and r≤n+π(√m), with π(3n)≤n+1 ← supplied k-split theorem and supplied threshold17, vertex rounding, elementary prime-product and residue counts ← **no unproved items**.
* **PROVED global 18n+o(n):** g(n)≤18n+π((18n)^(19/34))−1 ← k=18 split and the same row count/rounding ← supplied k-split and threshold17, π(t)≤t ← **no unproved items**. The stronger explicit logarithmic error uses the fully proved elementary prime estimate in R2.
* **PROVED linear-loss T2:** G=n and τ=n/K on exact CRT instances ← unique prime multiples at distinct positions with valuation exactly K, matching primal/dual certificates ← elementary CRT and prime-band search termination ← **no unproved items**.
* **REFUTED raw-LP comparisons:** uniform o(n) loss and fixed ατ+C or τ+cn+C with c<1 ← preceding CRT theorem with K=n ← **no unproved items**.
* **PROVED modified value bound:** τ_cap≤17n and τ_level≤17n ← generalized finite monotone-profile LP dual theorem ← generalized monotone-valuation hinge ← supplied atom-system hinge17 and interval prime-power counts ← **no unproved items**. Only demand capping is integral-equivalent; separate levels are explicitly stronger.
* **PROVED finite claims:** 85 distinct exact optima, 93 attempted jobs, maximum normalized loss 99/100 ← exact rational primal/dual verification plus exhaustive DP or matching upper/lower witnesses; all integral covers independently checked ← **no unproved items about these finite instances**. No inference about the maximum over untested instances.
* **CONDITIONAL exact 18n:** G≤18n ← τ_cap≤17n plus additive-n capped rounding ← **unproved:** the rounding hypothesis.
* **OPEN universal additive n / lowered targets:** G≤τ+n, its restricted long-input variant, or additive-n rounding for a modified LP ← **unproved:** a uniform arithmetic rounding argument absorbing the remaining row or forcing cost. No counterexample exceeding additive n is supplied.

The independent final certificate audit passed: `final_verification.json` reports 93 jobs, 85 distinct instances, all optima settled, and maximum normalized loss 99/100. The completed report also passed the independent proof-and-scope audit in `refutation_final_audit.md`, without blockers. Closing checkpoint: 2026-09-07 14:39 UTC. New proof claims are mathematically audited and are not new Lean kernel claims.

Gap: T2 and the global bounds g(n)≤19n and g(n)≤18n+o(n) are proved; the universal instancewise bound G≤τ+n and additive-n rounding for modified LPs remain OPEN.
