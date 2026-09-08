# Result

**A complete T3 theorem survives the audit:**

> **Five-prime theorem.** \((H_2)\) holds for every atom system with at most five active primes, provided **at most one prime carries more than one nonzero atom**.  
> The weights may be arbitrary real numbers. The exceptional prime may carry arbitrarily many prime-power levels.

Thus, in particular, \((H_2)\) holds for five arbitrary primes with one arbitrary prime power per prime—not merely for a finite set of weights.

Two complementary classes with genuinely multilevel prime functions also survive:

- For any \(N\ge2\), \((H_2)\) holds if every prime has total weight at most \(2/(N-1)\).
- For five primes, \((H_2)\) holds if all cumulative weights belong to \(\{0,1/q,\ldots,1\}\), for either \(q=6\) or \(q=8\).

**The largest \(N\) proved here for completely unrestricted atom systems is \(N=4\).** The unrestricted five-prime case remains unclosed. No counterexample to \((H_2)\) was found.

The important distinction enabling the first theorem is that its certificate dominates the left hinge **after summation over \([1,m]\)**, not pointwise. Its right-hand domination is pointwise, and all its divisor coefficients are nonnegative.

---

# 1. Route ledger

The two stated obstructions concerning pairs and triple hinges are valid. However, they do not exhaust the possible certificates: higher-order **threshold rectangles** have nonnegative divisor expansions, and a certificate can have an arithmetic prefix-sum lower bound without having a pointwise lower bound.

| Route | Advantage | Weakness / obstacle | Verification bridge | Judge decision |
|---|---|---|---|---|
| R1: pair and nonnegative certificates | Exact divisor counts immediately transfer nonnegative coefficients to every window | Pure pairs fail at five half-weights. An unrestricted six-prime pointwise certificate is impossible even on \(\{0,\tfrac12,1\}^6\) | Exact rectangle certificates; cyclic construction; exhaustive rational grid checks | Pure-pair extension frozen. Restricted higher-order certificates retained |
| R2: signed certificates | Can represent more hinge functions | No general absorption of the negative counting error was established | Exact signed-count bound, stated below | Frozen; no signed candidate used in a conclusion |
| R3: eliminate one prime | Reduces the new contribution to a tail-counting problem on four primes | Arbitrary multilevel functions lead to an unproved four-prime divisor-antichain bound | A complete Boolean antichain bound closes the one-multilevel-prime theorem | **T3 closed**; unrestricted extension remains conditional |
| R4: exact refutation search | Exhaustive over all window residues for each listed fixture | The selection of weighted systems and, except in the indicated five-prime tests, lengths is not exhaustive | Integer arithmetic; full-period arrays; explicit reflected, CRT-centred, and sieve-rich windows | No counterexample; no inference beyond the searched scope |

For R2, if
\[
F(n)=\sum_d c_d[d\mid n],
\]
then, writing \(K=\{1,\ldots,m\}\),
\[
\sum_{b\in I}F(b)-\sum_{k\in K}F(k)
\ge
-\sum_{\substack{c_d<0\\d\nmid m}}|c_d|.
\]
Indeed, the count of multiples of \(d\) in \(I\), minus \(\lfloor m/d\rfloor\), is either \(0\) or \(1\), and is \(0\) when \(d\mid m\). This bound is exact as a counting statement, but no general compensating slack was proved. It is not used below.

---

# 2. Lemma 1 — PROVED: the four-prime base case

Let \(f_1,\ldots,f_4\in[0,1]\), put \(S=\sum_i f_i\), and define
\[
g_{ij}=(f_i+f_j-1)^+,\qquad
G_4=\frac13\sum_{i<j}g_{ij}.
\]

Then
\[
(S-2)^+\le G_4\le(S-1)^+.
\]

## Proof of the lower bound

Each \(f_i\) occurs in exactly three pairs, so
\[
\sum_{i<j}g_{ij}
\ge
\sum_{i<j}(f_i+f_j-1)
=
3S-6.
\]
The left side is also nonnegative. Dividing by \(3\) proves the lower bound.

## Proof of the upper bound

For \(a,b\ge0\),
\[
(a-1)^++(b-1)^+\le(a+b-1)^+.
\]
The six edges of \(K_4\) split into the three perfect matchings
\[
\{12,34\},\qquad \{13,24\},\qquad \{14,23\}.
\]
Applying the preceding inequality to each matching and averaging gives
\[
G_4\le(S-1)^+.
\]

## Nonnegative divisor expansion

For distinct primes \(p,q\), let
\[
A_a=\sum_{j\le a}\alpha_{p,j},\qquad
B_b=\sum_{j\le b}\alpha_{q,j},\qquad A_0=B_0=0.
\]
Put \(\phi(t)=(t-1)^+\) and
\[
\beta_{a,b}
=
\phi(A_a+B_b)-\phi(A_{a-1}+B_b)
-\phi(A_a+B_{b-1})+\phi(A_{a-1}+B_{b-1}).
\]
Convexity of \(\phi\) implies \(\beta_{a,b}\ge0\): for \(\delta\ge0\), the function
\[
u\longmapsto\phi(u+\delta)-\phi(u)
\]
is nondecreasing.

Since \(A_a,B_b\le1\), the boundary terms vanish. Telescoping therefore gives the finite expansion
\[
(f_p(n)+f_q(n)-1)^+
=
\sum_{a,b}\beta_{a,b}[p^a q^b\mid n].
\]

Every interval of \(m\) consecutive integers contains at least \(\lfloor m/d\rfloor\) multiples of \(d\). Consequently,
\[
\sum_{k\le m}(S(k)-2)^+
\le
\sum_{k\le m}G_4(k)
\le
\sum_{b\in I}G_4(b)
\le
\sum_{b\in I}(S(b)-1)^+.
\]
This proves the base case for arbitrary real weights and arbitrary finite level structures. \(\square\)

---

# 3. Lemma 2 — PROVED: a four-modulus Boolean antichain bound

Let
\[
2\le a<b<c<d
\]
be pairwise coprime integers. They need not be primes.

For an integer \(Q\ge2\), let \(\mathcal M_Q\) be the inclusion-minimal nonempty subsets \(A\subseteq\{a,b,c,d\}\) satisfying
\[
\frac{\prod_{u\in A}u}{\max_{u\in A}u}\ge Q.
\]
Then
\[
\boxed{\quad
Q\sum_{A\in\mathcal M_Q}\frac1{\prod_{u\in A}u}\le1.
\quad}
\tag{3.1}
\]

## Explicit finite family

The following table lists every possible family. An empty range contributes no case.

| Condition | Products corresponding to \(\mathcal M_Q\) | Upper bound for the left side of (3.1) |
|---|---|---:|
| \(Q\le a\) | \(ab,ac,ad,bc,bd,cd\) | \(a\,e_2(1/a,1/b,1/c,1/d)\) |
| \(a<Q\le b\) | \(bc,bd,cd\) | \(1/c+2/d\) |
| \(b<Q\le c,\ Q\le ab\) | \(cd,abc,abd\) | \(1/c+2/d\) |
| \(b<Q\le c,\ Q>ab\) | \(cd\) | \(1/d\) |
| \(Q>c,\ Q\le ab\) | \(abc,abd,acd,bcd\) | \(1/c+3/d\) |
| \(Q>c,\ ab<Q\le ac\) | \(acd,bcd\) | \(2/d\) |
| \(Q>c,\ ac<Q\le bc\) | \(bcd\) | \(1/d\) |
| \(Q>c,\ bc<Q\le abc\) | \(abcd\) | \(1/d\) |
| \(Q>abc\) | none | \(0\) |

## Proof that the table is exhaustive

A pair is feasible precisely when its smaller member is at least \(Q\).

A triple is feasible precisely when the product of its two smaller members is at least \(Q\). It is minimal exactly when it contains no feasible pair.

The quadruple is feasible precisely when \(abc\ge Q\). It is minimal exactly when no triple is feasible; the last triple to cease being feasible is \(bcd\), whose threshold is \(bc\).

These observations give the table directly.

For example, when \(b<Q\le c\), the only feasible pair is \(cd\). The only triples not containing that pair are \(abc\) and \(abd\); both are feasible exactly when \(Q\le ab\).

## Proof of the numerical bounds

All rows except the first follow directly from the indicated upper bounds on \(Q\). For instance,
\[
Q\left(\frac1{cd}+\frac1{abc}+\frac1{abd}\right)
\le
\frac1d+\frac1c+\frac1d
\]
when \(Q\le c\) and \(Q\le ab\).

Because the four integers are pairwise coprime, \(c\ge5\). Hence
\[
\frac1c+\frac3d\le\frac4c\le\frac45<1,
\]
and the other displayed bounds are also at most \(1\).

It remains to prove
\[
a\,e_2(1/a,1/b,1/c,1/d)\le1.
\]

There are four cases.

If \(b=3\), then \(a=2,c\ge5,d\ge7\), so
\[
a e_2\le
2e_2(1/2,1/3,1/5,1/7)
=\frac{101}{105}<1.
\]

If \(b=4\), coprimality forces \(a=3\), and \(c\ge5,d\ge7\). Thus
\[
a e_2\le
3e_2(1/3,1/4,1/5,1/7)
=\frac{131}{140}<1.
\]

If \(b=5\), use \(a\le4,c\ge6,d\ge7\):
\[
a e_2
\le
\frac15+\frac16+\frac17+
4\left(\frac1{30}+\frac1{35}+\frac1{42}\right)
=\frac{179}{210}<1.
\]

Finally, if \(b\ge6\), then
\[
a e_2
=
\frac1b+\frac1c+\frac1d+
\frac a{bc}+\frac a{bd}+\frac a{cd}
\le\frac6b\le1.
\]
This proves (3.1). \(\square\)

---

# 4. Lemma 3 — PROVED: a one-divisor tail certificate

Let \(q_1,\ldots,q_r\), \(r\le4\), be pairwise coprime integers at least \(2\), and let \(0\le w_i\le1\). Define
\[
T(n)=\sum_{i=1}^r w_i[q_i\mid n].
\]

For every \(c\ge0\), every \(M\ge1\), and every interval \(J\) of \(M\) consecutive positive integers,
\[
\boxed{
\#\{k\le M:T(k)>c+1\}
\le
\#\{b\in J:T(b)>c\}.
}
\tag{4.1}
\]

More precisely, if some subset has weight exceeding \(c\), define
\[
Q=\min\left\{
\prod_{i\in A}q_i:
A\subseteq\{1,\ldots,r\},\
\sum_{i\in A}w_i>c
\right\}.
\tag{4.2}
\]
Then
\[
\#\{k\le M:T(k)>c+1\}
\le
\left\lfloor\frac M Q\right\rfloor
\le
\#\{b\in J:T(b)>c\}.
\tag{4.3}
\]

## Proof

Padding with zero-weight, coprime moduli reduces the proof to four moduli.

If no subset has weight exceeding \(c\), both sets in (4.1) are empty. Otherwise \(Q\ge2\).

Suppose \(T(k)>c+1\), and let
\[
A(k)=\{i:q_i\mid k\}.
\]
For every \(i\in A(k)\),
\[
\sum_{j\in A(k)\setminus\{i\}}w_j
=
T(k)-w_i
>
c+1-1=c.
\]
By the definition of \(Q\),
\[
\prod_{j\in A(k)\setminus\{i\}}q_j\ge Q.
\]
Thus \(A(k)\) is feasible for the family in Lemma 2 and contains some minimal feasible subset.

Writing \(q_A=\prod_{i\in A}q_i\), the indicator
\[
F_Q(n)=\sum_{A\in\mathcal M_Q}[q_A\mid n]
\]
therefore satisfies the pointwise bound
\[
[T(n)>c+1]\le F_Q(n).
\]
Consequently,
\[
\begin{aligned}
\#\{k\le M:T(k)>c+1\}
&\le \sum_{A\in\mathcal M_Q}\left\lfloor\frac M{q_A}\right\rfloor\\
&\le M\sum_{A\in\mathcal M_Q}\frac1{q_A}\\
&\le \frac M Q.
\end{aligned}
\]
The left side is an integer, proving the first inequality in (4.3).

Choose a subset attaining \(Q\) in (4.2). Every multiple of \(Q\) has \(T\)-value exceeding \(c\). Therefore
\[
[Q\mid n]\le[T(n)>c],
\]
and \(J\) contains at least \(\lfloor M/Q\rfloor\) such multiples.

This also gives the explicit two-sided arithmetic certificate:
\[
[T>c+1]\le F_Q,\qquad
\sum_{k\le M}F_Q(k)\le\left\lfloor\frac M Q\right\rfloor,\qquad
[Q\mid n]\le[T>c].
\]
\(\square\)

---

# 5. Theorem 4 — PROVED: five primes, at most one multilevel prime

Suppose
\[
S(n)=T(n)+f(n),
\]
where
\[
T(n)=\sum_{i=1}^4 w_i[q_i\mid n],\qquad 0\le w_i\le1,
\]
the \(q_i\) are powers of four distinct primes, and
\[
f(n)=\sum_j\alpha_j[p^j\mid n],\qquad
\alpha_j\ge0,\qquad \sum_j\alpha_j\le1,
\]
for a fifth prime \(p\).

Then \((H_2)\) holds for all \(m,x\).

## Proof by elimination

For \(a\ge0\), define
\[
\Delta_a(T,f)=(T+f-a)^+-(T-a)^+.
\]
The exact layer identity is
\[
\Delta_a(T(n),f(n))
=
\int_0^1 [f(n)>t]\,[T(n)>a-t]\,dt.
\tag{5.1}
\]

Fix \(t\in(0,1)\), outside the finitely many cumulative-weight values of \(f\). Either \([f(n)>t]\) vanishes identically, or there is a power \(d=p^{j(t)}\) such that
\[
[f(n)>t]=[d\mid n].
\]

Let \(c=1-t\ge0\), and let \(Q(t)\) be the modulus from Lemma 3 for \(T,c\). If no such modulus exists, both relevant increment integrands vanish.

Because \(d\) is coprime to every \(q_i\),
\[
T(dk)=T(k).
\]
Applying Lemma 3 with \(M=\lfloor m/d\rfloor\) gives
\[
\begin{aligned}
\sum_{k\le m}[d\mid k][T(k)>2-t]
&=
\#\left\{h\le\left\lfloor\frac md\right\rfloor:T(h)>c+1\right\}\\
&\le
\left\lfloor
\frac{\lfloor m/d\rfloor}{Q(t)}
\right\rfloor\\
&=
\left\lfloor\frac m{dQ(t)}\right\rfloor.
\end{aligned}
\tag{5.2}
\]
On the other hand,
\[
[dQ(t)\mid n]\le[d\mid n][T(n)>1-t],
\]
so the corresponding window sum is at least the last expression in (5.2).

Integrating over \(t\) yields
\[
\sum_{k\le m}\Delta_2(T(k),f(k))
\le
\sum_{b\in I}\Delta_1(T(b),f(b)).
\tag{5.3}
\]
Adding the four-prime inequality for \(T\) proves \((H_2)\) for \(S\). \(\square\)

## Explicit finite nonnegative certificate

The integral proof can be converted into a finite divisor family without approximation.

Write
\[
A_j=\sum_{h\le j}\alpha_h,\qquad
w_B=\sum_{i\in B}w_i.
\]
Partition \([0,1]\) at all points in
\[
\{0,1\}\cup\{A_j\}
\cup\{1-w_B,\ 2-w_B:B\subseteq\{1,2,3,4\}\}
\]
that lie in \([0,1]\).

For each open cell \((u_\ell,v_\ell)\), choose its midpoint \(\tau_\ell\). If the corresponding layer is nonzero, put
\[
d_\ell=p^{\min\{j:A_j>\tau_\ell\}},
\]
and, when the set is nonempty, put
\[
Q_\ell
=
\min\left\{
\prod_{i\in B}q_i:
w_B>1-\tau_\ell
\right\}.
\]
Omit cells for which either choice does not exist.

Define
\[
\boxed{
C(n)=
\frac13\sum_{i<j}(w_i+w_j-1)^+[q_iq_j\mid n]
+
\sum_\ell(v_\ell-u_\ell)[d_\ell Q_\ell\mid n].
}
\tag{5.4}
\]

All coefficients are nonnegative. The preceding proof establishes
\[
\sum_{k\le m}(S(k)-2)^+
\le
\sum_{k\le m}C(k),
\tag{5.5}
\]
while (5.1) gives the pointwise upper bound
\[
C(n)\le(S(n)-1)^+.
\tag{5.6}
\]
Thus
\[
\sum_{k\le m}(S(k)-2)^+
\le\sum_{k\le m}C(k)
\le\sum_{b\in I}C(b)
\le\sum_{b\in I}(S(b)-1)^+.
\]

**There is no claim that \(C(n)\ge(S(n)-2)^+\) pointwise.** In fact, the audited example below explicitly disproves that stronger claim for this construction.

---

# 6. Theorem 5 — PROVED: arbitrary \(N\) under a per-prime cap

Let \(N\ge2\), set
\[
\lambda=\frac2{N-1},
\]
and suppose there are at most \(N\) active primes, each with total weight at most \(\lambda\).

Then \((H_2)\) holds.

In particular, for five primes this proves the arbitrary-multilevel case
\[
\sum_j\alpha_{p,j}\le\frac12\qquad\text{for every }p.
\]

## Pointwise certificate

Pad with zero functions and write \(f_0,\ldots,f_{N-1}\in[0,\lambda]\). For
\[
a_{ri}=\frac{(r+i)\bmod N}{N},
\]
define
\[
G(f)=
\sum_{r=0}^{N-1}
\max\left(
0,\,
\min\left(
\frac{\lambda}{N},
\min_i(f_i-\lambda a_{ri})
\right)
\right).
\tag{6.1}
\]
Then
\[
\boxed{
\left(\sum_i f_i-2\right)^+
\le G(f)\le
\left(\sum_i f_i-1\right)^+.
}
\tag{6.2}
\]

## Proof of the lower bound

Let \(U\) be uniform on \([0,1)\), and define
\[
Z_i=\lambda\left\{U+\frac iN\right\}.
\]
Each \(Z_i\) is uniform on \([0,\lambda)\). Splitting \(U\) into its \(N\) subintervals shows directly that
\[
G(f)=\lambda\,\mathbb P(Z_i\le f_i\text{ for every }i).
\]
The union bound gives
\[
\begin{aligned}
G(f)
&\ge
\lambda\left(1-\sum_i\mathbb P(Z_i>f_i)\right)\\
&=
\lambda\left(1-\sum_i(1-f_i/\lambda)\right)\\
&=
\sum_i f_i-\lambda(N-1)
=
\sum_i f_i-2.
\end{aligned}
\]
Also \(G\ge0\), proving the lower bound.

## Proof of the upper bound

On branch \(r\), write \(U=r/N+t\), \(0\le t<1/N\). If all threshold inequalities hold, then
\[
f_i\ge\lambda(a_{ri}+t)\quad\text{for all }i.
\]
Since
\[
\sum_i a_{ri}=\frac{N-1}{2},
\]
we obtain
\[
\sum_i f_i\ge1+N\lambda t.
\]
Hence the admissible \(t\)-length on each branch is at most
\[
\frac{(\sum_i f_i-1)^+}{N\lambda}.
\]
Multiplying by \(\lambda\) and summing the \(N\) branches proves the upper bound.

## Finite divisor expansion

For each branch \(r\), partition \([0,1/N]\) at
\[
0,\quad\frac1N,\quad
\frac{A_{i,j}}{\lambda}-a_{ri}
\]
whenever these values lie in the interval.

On each resulting open cell \((u,v)\), the event
\[
f_i(n)\ge\lambda(a_{ri}+t)\quad\text{for every }i
\]
is either identically empty or is the divisor condition
\[
\prod_i p_i^{j_i}\mid n,
\]
where \(j_i\) is the first cumulative level reaching the threshold at the cell midpoint.

Assign this divisor coefficient \(\lambda(v-u)\). These finitely many nonnegative coefficients give exactly \(G(S(n))\). Applying divisor counts to (6.2) proves \((H_2)\). \(\square\)

At five equal half-weights, this certificate has value \(1/2\), while every pair hinge is zero.

---

# 7. Lemma 6 — PROVED by exact finite verification: two multilevel grids

For a sorted integer vector \(t=(t_1,\ldots,t_5)\), define
\[
O_t(a)=
\#\{\text{distinct permutations }s\text{ of }t:s_i\le a_i\ \forall i\}.
\]

Let \(f_i=a_i/q\), where \(a_i\in\{0,\ldots,q\}\), and put
\[
P_q(a)=\sum_{i<j}(a_i+a_j-q)^+,\qquad A=\sum_i a_i.
\]

The following are exact finite inequalities.

### Denominator \(6\)

For every \(a\in\{0,\ldots,6\}^5\),
\[
18(A-12)^+
\le
6P_6(a)+O_{(0,1,1,2,3)}(a)
\le
18(A-6)^+.
\tag{7.1}
\]
Equivalently,
\[
G_6(f)=
\frac13\sum_{i<j}(f_i+f_j-1)^+
+\frac1{108}O_{(0,1,1,2,3)}(6f)
\]
lies between the two hinges.

### Denominator \(8\)

For every \(a\in\{0,\ldots,8\}^5\),
\[
\begin{aligned}
180(A-16)^+
\le{}&
60P_8(a)
+4O_{(0,1,1,2,5)}(a)
+3O_{(0,1,1,3,4)}(a)\\
&+O_{(0,1,2,3,3)}(a)
+4O_{(0,1,2,3,4)}(a)
\le180(A-8)^+.
\end{aligned}
\tag{7.2}
\]

Thus the additional orbit coefficients in \(G_8\) are respectively
\[
\frac1{360},\quad\frac1{480},\quad
\frac1{1440},\quad\frac1{360}.
\]

## Exact feasibility verification

The inequalities are permutation-invariant, so it suffices to enumerate nondecreasing \(a\). The numbers of cases are
\[
\binom{11}{5}=462,\qquad \binom{13}{5}=1287.
\]

The verifier below computes every orbit count as an integer, evaluates both slack numerators, and checks every case.

| Grid | Integer scaling | Sorted cases | Minimum lower slack | Minimum upper slack |
|---|---:|---:|---:|---:|
| \(q=6\) | \(108\) | \(462\) | \(0\) | \(0\) |
| \(q=8\) | \(1440\) | \(1287\) | \(0\) | \(0\) |

No floating-point optimization is used in this verification.

## Why these prove multilevel atom results

For a positive threshold \(h/q\),
\[
[f_i(n)\ge h/q]
\]
is either zero or a single prime-power divisor indicator: take the first cumulative level reaching \(h/q\).

Each orbit term is therefore a finite sum of nonnegative divisor indicators. The pair terms have the expansion from Lemma 1. Consequently, (7.1) and (7.2), together with interval divisor counts, prove \((H_2)\) whenever the five cumulative-weight functions take values in the respective grid.

There is **no interpolation claim** from these grids to arbitrary real cumulative levels. \(\square\)

---

# 8. Lemma 7 — PROVED: a six-prime obstruction to pointwise nonnegative certificates

There is no function on \(\{0,\tfrac12,1\}^6\) of the form
\[
G(f)=\sum_t c_t\prod_{i:t_i>0}[f_i\ge t_i],
\qquad c_t\ge0,
\tag{8.1}
\]
satisfying
\[
\left(\sum_i f_i-2\right)^+
\le G(f)\le
\left(\sum_i f_i-1\right)^+
\tag{8.2}
\]
everywhere.

## Proof

The upper bound at states of total weight at most \(1\) forces all constant and singleton coefficients to vanish. It also forces every two-coordinate coefficient with thresholds \((1/2,1/2)\) to vanish.

Let \(P\) be the total coefficient mass with support size \(2\), \(T\) that with support size \(3\), and \(H\) that with support size at least \(4\).

At the all-one state,
\[
P+T+H\le5.
\tag{8.3}
\]
At each state with exactly three coordinates equal to \(1\), the lower bound requires \(G\ge1\). Sum these inequalities over all \(\binom63=20\) states. Each two-coordinate term occurs four times and each three-coordinate term once, so
\[
4P+T\ge20.
\tag{8.4}
\]
But
\[
4P+T
=
4(P+T+H)-3T-4H
\le20.
\]
Equality is forced, giving \(T=H=0\).

At the all-half state, every surviving two-coordinate term vanishes because it has a threshold \(1\) in at least one coordinate. Thus \(G=0\), whereas the lower hinge equals \(1\). Contradiction. \(\square\)

This is an obstruction to a **pointwise certificate**, not a counterexample to \((H_2)\). The three values \(0,1/2,1\) can be realized at each prime using atoms \(1/2\) at \(p\) and \(1/2\) at \(p^2\).

---

# 9. Lemma 8 — CONDITIONAL: the exact unrestricted five-prime bridge

Here is the remaining arithmetic statement exposed by the elimination route.

For four distinct primes \(P=\{p_1,p_2,p_3,p_4\}\) and an integer \(Q\ge2\), define
\[
D(e)=\prod_{i=1}^4p_i^{e_i}.
\]
Let \(\mathcal A_P(Q)\) be the coordinatewise-minimal exponent vectors satisfying
\[
\frac{D(e)}{\max_i p_i^{e_i}}\ge Q.
\]
Consider the statement
\[
\boxed{
K_4:\qquad
Q\sum_{e\in\mathcal A_P(Q)}\frac1{D(e)}\le1
\quad
\text{for every }P,Q.
}
\tag{9.1}
\]

**Status: OPEN in this response.**

## Finiteness of the displayed family — PROVED

Let
\[
E_i=\min\{e:p_i^e\ge Q\}.
\]
Every minimal vector satisfies \(e_i\le E_i\).

Indeed, if \(e_i>E_i\), reduce \(e_i\) by one. The reduced \(i\)-component is still at least \(Q\). Deleting component \(i\) leaves the same product as before, at least \(Q\); deleting any other component leaves a product containing the reduced \(i\)-component, also at least \(Q\). Thus feasibility survives, contradicting minimality.

So (9.1) concerns an explicit finite family for each \(P,Q\).

## Conditional implication — PROVED

Assume \(K_4\). Let \(T\) be an arbitrary atom system on these four primes, and let \(c\ge0\). Let \(Q\) be the least positive integer with \(T(Q)>c\), when one exists.

If \(T(n)>c+1\), deleting the entire contribution of any one prime leaves value exceeding \(c\), because each prime contributes at most \(1\). Therefore, if \(D\) is the \(P\)-smooth part of \(n\),
\[
D/p_i^{v_{p_i}(D)}\ge Q
\]
for every active component. Hence \(D\) is divisible by some \(D(e)\) from \(\mathcal A_P(Q)\).

Exactly as in Lemma 3, \(K_4\) then gives
\[
\#\{k\le M:T(k)>c+1\}
\le\left\lfloor\frac M Q\right\rfloor
\le\#\{b\in J:T(b)>c\}.
\]
The elimination proof of Theorem 4 now applies to an arbitrary fifth prime function. Thus
\[
K_4\quad\Longrightarrow\quad
(H_2)\text{ for unrestricted systems on at most five primes}.
\tag{9.2}
\]

## Audited limits of this bridge

The finite checks established (9.1) for:

\[
P=\{2,3,5,7\},\qquad 2\le Q\le300,
\]
and for all four-element subsets of
\[
\{2,3,5,7,11,13\},\qquad 2\le Q\le60.
\]

These are **finite checks, not a proof of \(K_4\)**.

A tempting monotonicity reduction in the primes is false:
\[
K_{\{2,5,7,11\}}(3)=\frac{111}{220}
<
\frac{236}{385}
=
K_{\{3,5,7,11\}}(3).
\]

Moreover, the direct five-prime analogue of \(K_4\) is **REFUTED**:
\[
K_{\{2,3,5,7,11\}}(2)
=
2e_2(1/2,1/3,1/5,1/7,1/11)
=
\frac{194}{165}>1.
\tag{9.3}
\]
Thus even a proof of \(K_4\) would not by itself complete induction for all \(N\).

---

# 10. Adversarial audit and exact search

## Rejected continuous candidates — REFUTED

Two continuous extensions considered during certificate discovery failed exact pointwise tests.

For
\[
h(x_1,x_2,x_3)
=
\sum_i
\left(
\min(x_i,\tfrac13)
-
\max(0,1-2x_j:j\ne i)
\right)^+,
\]
the candidate
\[
G=\frac13\sum_{i<j}(f_i+f_j-1)^+
+\frac1{20}\sum_{|T|=3}h(f_T)
\]
fails at
\[
f=(1/3,1/3,2/3,2/3,2/3):
\qquad G=\frac{29}{60}<\frac23=(S-2)^+.
\]

The capped-simplex candidate
\[
G=\frac13\sum_{i<j}(f_i+f_j-1)^+
+\frac8{11}
\sum_{T\subseteq[5]}(-1)^{|T|}
\left(1-\sum_{i\in T}\min(f_i,\tfrac12)\right)_+^4
\]
fails at
\[
f=(1/6,1/6,5/6,5/6,5/6):
\qquad G=\frac{670}{891}<\frac56,
\]
with exact slack
\[
G-(S-2)^+=-\frac{145}{1782}.
\]

Neither candidate is used in a theorem.

## An explicit audited five-prime certificate

Take atom numerators over denominator \(720\):
\[
\begin{array}{c|rrrrrr}
\text{modulus}&2&3&5&7&11&121\\ \hline
\text{numerator}&257&421&563&611&293&427
\end{array}
\]

The construction in Theorem 4 gives
\[
C(n)=\frac1{2160}\sum_d c_d[d\mid n],
\]
with the complete coefficient family
\[
\begin{array}{c|rrrrrrrrrrr}
d&10&14&15&21&35&55&66&110&242&363&605\\ \hline
c_d&100&148&264&312&454&408&345&126&771&492&18.
\end{array}
\]

The cut numerators over denominator \(720\) are
\[
0,9,42,109,151,157,199,266,293,299,408,456,463,572,620,720.
\]

The pointwise upper bound and every prefix lower bound were checked over the full period
\[
D=25410.
\]

Importantly, at \(n=12705\),
\[
2160\,C(n)=1948
<
2625
=
2160(S(n)-2)^+.
\]
This confirms why the proof must use the arithmetic prefix-sum bound rather than a nonexistent pointwise lower bound.

## Reflected, CRT-centred, and sieve-rich windows

The same explicit certificate was checked on all three types at
\[
m=10^4,\quad10^5,\quad10^6.
\]

The sieve-rich windows were found by exhaustive residue search for the first eight primes:

| \(m\) | Start \(x\) | Prime-free positions in \([1,m]\) | Prime-free positions in \((x,x+m]\) |
|---:|---:|---:|---:|
| \(10,000\) | \(5,349\) | \(1,711\) | \(1,722\) |
| \(100,000\) | \(3,995,409\) | \(17,103\) | \(17,115\) |
| \(1,000,000\) | \(3,839,019\) | \(171,021\) | \(171,038\) |

Thus the audit explicitly includes windows that invalidate naive prefix extremality for sifted sets.

For example, in the last window the certificate chain, with all quantities multiplied by \(2160\), is
\[
12,559,716
\le
84,360,289
\le
84,362,090
\le
250,188,312.
\]

For the prime-cluster test, use
\[
101,103,107,109,113,127,131,137,139,
\]
all with weight \(1\), and
\[
m=137\cdot139=19043.
\]
The centred window at their product has exactly
\[
L=0,\qquad R=8.
\]
This is consistent with, and does not sharpen, the stated cluster obstruction below threshold \(2\).

## Refutation-search scope

For \(N=5,6,7,8\), let \(D\) be the product of the first \(N\) primes and \(q=N!\). Two one-atom weight profiles were used:
\[
u_i=q-\left\lfloor\frac q{i+2}\right\rfloor,
\qquad
v_i=\left\lfloor\frac{q(i+2)}{N+2}\right\rfloor,
\qquad 0\le i<N.
\]
The weights are \(u_i/q\) or \(v_i/q\).

For \(N=5\), all \(1\le m\le D\) and all \(0\le x<D\) were checked. For \(N=6,7,8\), every \(x\) was checked for \(m=D\) and for the members of
\[
\{66,100,1000,10000,100000,1000000\}
\]
not exceeding \(D\).

A further five-prime, two-level system used denominator \(720\):
\[
\begin{array}{c|rrrrr}
p&2&3&5&7&11\\ \hline
720\alpha_{p,1}&180&240&360&480&540\\
720\alpha_{p,2}&540&480&360&240&180
\end{array}
\]
with full period \(5,336,100\), all starts, and the same selected-length rule.

| Fixtures | Window instances checked | Instances satisfying the listed T2 region conditions |
|---|---:|---:|
| Five primes, two one-level profiles | \(10,672,200\) | \(9,752,820\) |
| Six primes, two profiles | \(300,300\) | \(210,210\) |
| Seven primes, two profiles | \(6,126,120\) | \(3,573,570\) |
| Eight primes, two profiles | \(135,795,660\) | \(87,297,210\) |
| Five primes, two levels each | \(37,352,700\) | \(26,680,500\) |
| **Total** | **\(190,246,980\)** | **\(127,514,310\)** |

All arithmetic was integer or rational. All these fixtures have \(H<1\), so \(H<h_0\) and \(\mu-H^2/6<1\) follow immediately from \(\mu\le H\).

**Selection of weighted systems: HEURISTIC. Enumeration of starts and the specified lengths: EXHAUSTIVE. No counterexample was found.**

Separately, the four-prime tail inequality was checked on denominator-\(3\) and denominator-\(6\) grids, giving \(33,868,800\) and \(635,304,600\) window instances respectively. These grids overlap and are not being counted as disjoint searches.

---

# 11. Complete exact verifier

The standard-library checks verify the certificates, constants, rejected candidates, and explicit full-period certificate. The `--full` option additionally reproduces the long-window and search audits using NumPy integer arrays.

```python
#!/usr/bin/env python3
"""Exact verification for the restricted five-prime hinge results.
Standard-library proof checks: python verifier.py
Long-window/search audits (requires numpy): python verifier.py --full
No floating-point arithmetic is used in any mathematical check.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, combinations_with_replacement, product
from math import factorial, gcd, lcm, prod
import argparse

PRIMES = (2, 3, 5, 7, 11, 13, 17, 19)
P5 = tuple(combinations(range(5), 2))
T5 = tuple(combinations(range(5), 3))
SUB5 = tuple(tuple(i for i in range(5) if mask >> i & 1)
             for mask in range(32))
GRID = {
    6: (108, (((0, 1, 1, 2, 3), 1),)),
    8: (1440, (((0, 1, 1, 2, 5), 4),
               ((0, 1, 1, 3, 4), 3),
               ((0, 1, 2, 3, 3), 1),
               ((0, 1, 2, 3, 4), 4)))
}
T3_ATOMS = ((2, 257), (3, 421), (5, 563), (7, 611),
            (11, 293), (121, 427))
EXPECTED_CERT = ((10, 100), (14, 148), (15, 264), (21, 312),
                 (35, 454), (55, 408), (66, 345), (110, 126),
                 (242, 771), (363, 492), (605, 18))
EXPECTED_CUTS = (0, 9, 42, 109, 151, 157, 199, 266,
                 293, 299, 408, 456, 463, 572, 620, 720)
HR = ((10000, 5349, 1711, 1722),
      (100000, 3995409, 17103, 17115),
      (1000000, 3839019, 171021, 171038))
STRESS = (
    ("reflected", 10000, 40820, 123048, 841864, 845202, 2504340),
    ("CRT-centred", 10000, 45820, 123048, 841864, 842732, 2502102),
    ("sieve-rich", 10000, 5349, 123048, 841864, 843626, 2502018),
    ("reflected", 100000, 27050, 1255602, 8434996, 8438334, 25021431),
    ("CRT-centred", 100000, 77050, 1255602, 8434996, 8435816, 25016892),
    ("sieve-rich", 100000, 3995409, 1255602, 8434996, 8437001, 25021218),
    ("reflected", 1000000, 41810, 12559716, 84360289, 84363627, 250189746),
    ("CRT-centred", 1000000, 541810, 12559716, 84360289, 84362108, 250188414),
    ("sieve-rich", 1000000, 3839019, 12559716, 84360289, 84362090, 250188312),
)

def positive(x):
    return max(x, 0)

def elementary(xs, r):
    return sum(prod(z) for z in combinations(xs, r))

def orbit_count(t, a):
    """Distinct permutations of t that are componentwise <= a."""
    numerator = 1
    for j, threshold in enumerate(reversed(t)):
        numerator *= max(0, sum(v >= threshold for v in a) - j)
    denominator = prod(factorial(c) for c in Counter(t).values())
    assert numerator % denominator == 0
    return numerator // denominator

def verify_base_and_constants():
    for a in product(range(7), repeat=4):
        s = sum(a)
        pair_sum = sum(positive(a[i] + a[j] - 6)
                       for i, j in combinations(range(4), 2))
        assert 3 * positive(s - 12) <= pair_sum <= 3 * positive(s - 6)
    levels = tuple(combinations_with_replacement(range(7), 2))
    for (a0, a1), (b0, b1) in product(levels, repeat=2):
        beta = (positive(a1+b1-6) - positive(a0+b1-6)
                - positive(a1+b0-6) + positive(a0+b0-6))
        assert beta >= 0
    assert 2*elementary(tuple(F(1,q) for q in (2,3,5,7)), 2) == F(101,105)
    assert 3*elementary(tuple(F(1,q) for q in (3,4,5,7)), 2) == F(131,140)
    assert 4*elementary(tuple(F(1,q) for q in (4,5,6,7)), 2) == F(179,210)
    assert max(F(101,105), F(131,140), F(179,210), F(4,5)) < 1
    # (18-sqrt(30))/7 > 1, since sqrt(30) < 11.
    assert 30 < 11**2
    print("base grid:", 7**4, "mixed-difference checks:", len(levels)**2)

def boolean_minimals(qs, Q):
    r = len(qs)
    feasible = {}
    for mask in range(1 << r):
        values = tuple(qs[i] for i in range(r) if mask >> i & 1)
        feasible[mask] = bool(values) and prod(values)//max(values) >= Q
    return tuple(mask for mask in feasible if feasible[mask]
                 and not any(feasible[mask ^ (1 << i)]
                             for i in range(r) if mask >> i & 1))

def boolean_kraft(qs, Q):
    return sum(F(Q, prod(qs[i] for i in range(len(qs))
                         if mask >> i & 1))
               for mask in boolean_minimals(qs, Q))

def verify_boolean_kraft():
    checked = 0
    largest = (F(0), None)
    for qs in combinations(range(2, 31), 4):
        if any(gcd(a,b) != 1 for a,b in combinations(qs,2)):
            continue
        a,b,c,d = qs
        for Q in sorted({a,b,c,a*b,a*c,b*c,a*b*c}):
            value = boolean_kraft(qs,Q)
            assert value <= 1
            checked += 1
            if value > largest[0]:
                largest = (value, (qs,Q))
    assert checked == 17738
    assert largest == (F(101,105), ((2,3,5,7),2))
    assert boolean_kraft((2,3,5,7,11),2) == F(194,165)
    print("Boolean audit:", checked, largest)

def verify_grid_certificates():
    for q,(scale,terms) in GRID.items():
        histogram = {}
        for a in combinations_with_replacement(range(q+1),5):
            A = sum(a)
            P = sum(positive(a[i]+a[j]-q) for i,j in P5)
            G = (scale//(3*q))*P
            G += sum(c*orbit_count(t,a) for t,c in terms)
            lower = G-(scale//q)*positive(A-2*q)
            upper = (scale//q)*positive(A-q)-G
            assert lower >= 0 and upper >= 0, (q,a,lower,upper)
            row = histogram.setdefault(A,[0,10**9,10**9])
            row[0] += 1
            row[1] = min(row[1],lower)
            row[2] = min(row[2],upper)
        count = sum(row[0] for row in histogram.values())
        assert count == {6:462,8:1287}[q]
        assert min(row[1] for row in histogram.values()) == 0
        assert min(row[2] for row in histogram.values()) == 0
        print("grid certificate:", q, scale, count)
        print("sum -> (count, minimum lower slack, minimum upper slack)")
        print(histogram)

def cyclic_certificate(f, lam):
    N = len(f)
    return sum(max(F(0), min(lam/N,
                   min(f[i]-lam*F((r+i)%N,N) for i in range(N))))
               for r in range(N))

def verify_cyclic_certificate():
    count = 0
    for N,q in ((2,4),(3,4),(4,4),(5,4),(6,2),(7,2),(8,2)):
        lam = F(2,N-1)
        for a in product(range(q+1),repeat=N):
            f = tuple(lam*F(v,q) for v in a)
            G = cyclic_certificate(f,lam)
            assert positive(sum(f)-2) <= G <= positive(sum(f)-1)
            count += 1
    assert count == 13377
    assert cyclic_certificate((F(1,2),)*5,F(1,2)) == F(1,2)
    print("cyclic functional-box audit:", count)

def verify_rejected_candidates():
    def third_difference(base, increment):
        return sum((-1)**(3-k)*factorial(3)//(factorial(k)*factorial(3-k))
                   *positive(base+k*increment-1) for k in range(4))
    assert third_difference(F(1,2),F(1,2)) == -F(1,2)
    assert third_difference(F(0),F(1)) == -1
    def h(v):
        return sum(positive(min(v[i],F(1,3)) -
                   max(F(0),*(1-2*v[j] for j in range(3) if j != i)))
                   for i in range(3))
    f = (F(1,3),)*2+(F(2,3),)*3
    G = sum(positive(f[i]+f[j]-1) for i,j in P5)/3
    G += sum(h(tuple(f[i] for i in T)) for T in T5)/20
    assert G == F(29,60) < positive(sum(f)-2) == F(2,3)
    f = (F(1,6),)*2+(F(5,6),)*3
    capped = tuple(min(z,F(1,2)) for z in f)
    CDF = sum((-1)**len(T)*positive(1-sum(capped[i] for i in T))**4
              for T in SUB5)
    G = sum(positive(f[i]+f[j]-1) for i,j in P5)/3 + F(8,11)*CDF
    assert G == F(670,891) < positive(sum(f)-2) == F(5,6)
    assert G-F(5,6) == -F(145,1782)
    print("rejected-candidate witnesses: verified exactly")

def elimination_certificate(qs, weights, p, levels, denominator):
    assert len(qs) == len(weights) == 4
    assert all(gcd(p,q) == 1 for q in qs)
    assert all(gcd(a,b) == 1 for a,b in combinations(qs,2))
    assert all(0 <= w <= denominator for w in weights)
    subsets = tuple((sum(weights[i] for i in range(4) if mask >> i & 1),
                     prod(qs[i] for i in range(4) if mask >> i & 1))
                    for mask in range(16))
    cumulative = []
    total = 0
    for d,a in levels:
        z = d
        while z % p == 0:
            z //= p
        assert z == 1 and a >= 0
        total += a
        cumulative.append((d,total))
    assert total <= denominator
    cuts = {0,denominator} | {a for d,a in cumulative}
    cuts |= {h*denominator-w for h in (1,2) for w,d in subsets
             if 0 <= h*denominator-w <= denominator}
    cuts = tuple(sorted(cuts))
    coefficients = {}
    for i,j in combinations(range(4),2):
        c = positive(weights[i]+weights[j]-denominator)
        if c:
            d = qs[i]*qs[j]
            coefficients[d] = coefficients.get(d,0)+c
    for u,v in zip(cuts,cuts[1:]):
        powers = [d for d,A in cumulative if 2*A > u+v]
        winners = [d for w,d in subsets if 2*w > 2*denominator-u-v]
        if not powers or not winners:
            continue
        d = powers[0]*min(winners)
        coefficients[d] = coefficients.get(d,0)+3*(v-u)
    return 3*denominator,tuple(sorted(coefficients.items())),cuts

def verify_explicit_certificate():
    den,coeff,cuts = elimination_certificate(
        (2,3,5,7),(257,421,563,611),11,((11,293),(121,427)),720)
    assert den == 2160 and coeff == EXPECTED_CERT and cuts == EXPECTED_CUTS
    D = lcm(*(d for d,a in T3_ATOMS))
    accumulated_C = accumulated_L = 0
    minimum_pointwise = (0,0)
    for n in range(1,D+1):
        S = sum(a for d,a in T3_ATOMS if n % d == 0)
        C = sum(a for d,a in coeff if n % d == 0)
        L = 3*positive(S-1440)
        R = 3*positive(S-720)
        assert C <= R
        accumulated_C += C
        accumulated_L += L
        assert accumulated_C >= accumulated_L
        if C-L < minimum_pointwise[0]:
            minimum_pointwise = (C-L,n)
    assert D == 25410 and minimum_pointwise == (-677,12705)
    for name,m,x,L,CK,CI,R in STRESS:
        assert sum(a*(m//d) for d,a in coeff) == CK
        assert sum(a*((x+m)//d-x//d) for d,a in coeff) == CI
        assert L <= CK <= CI <= R
    print("explicit certificate:",den,coeff)
    print("cut numerators:",cuts)
    print("full-period certificate audit:",D,minimum_pointwise)

def projection_frontier(Q, primes):
    ladders = []
    for p in primes:
        values = [1]
        while values[-1] < Q:
            values.append(values[-1]*p)
        ladders.append(values)
    r = len(primes)
    states = tuple(product(*(range(len(v)) for v in ladders)))
    divisors = {s:prod(ladders[i][s[i]] for i in range(r)) for s in states}
    feasible = {s:divisors[s]//max(ladders[i][s[i]] for i in range(r)) >= Q
                for s in states}
    frontier = []
    for s in states:
        if not feasible[s]:
            continue
        predecessors = (tuple(s[j]-(j == i) for j in range(r))
                        for i in range(r) if s[i])
        if not any(feasible[t] for t in predecessors):
            frontier.append(divisors[s])
    return sum(F(Q,d) for d in frontier),tuple(frontier)

def audit_open_projection_bound():
    best = (F(0),None)
    for Q in range(2,301):
        value,ds = projection_frontier(Q,PRIMES[:4])
        assert value <= 1
        if value > best[0]:
            best = (value,Q)
    assert best == (F(101,105),2)
    checked = 0
    for primes in combinations(PRIMES[:6],4):
        for Q in range(2,61):
            value,ds = projection_frontier(Q,primes)
            assert value <= 1
            checked += 1
    assert checked == 885
    assert projection_frontier(3,(2,5,7,11))[0] == F(111,220)
    assert projection_frontier(3,(3,5,7,11))[0] == F(236,385)
    assert F(111,220) < F(236,385)
    print("OPEN-bound finite audits only:",299,checked,best)

def audit_tail_grid(q):
    import numpy as np
    D = 210
    values = np.array([[int(k % p == 0) for p in PRIMES[:4]]
                       for k in range(1,D+1)],dtype=np.int64)
    lengths = np.arange(1,D+1)[:,None]
    starts = np.arange(D)[None,:]
    checked = 0
    for weights in product(range(q+1),repeat=4):
        S = values @ np.array(weights,dtype=np.int64)
        for t in range(1,q+1):
            left = (S > 2*q-t).astype(np.int64)
            right = (S > q-t).astype(np.int64)
            pref = np.concatenate(([0],np.cumsum(np.tile(right,2))))
            windows = pref[starts+lengths]-pref[starts]
            assert np.all(np.cumsum(left) <= windows.min(axis=1))
            checked += 1
    assert checked == q*(q+1)**4
    print("tail grid:",q,checked,"window instances:",checked*D*D)

def period_values(atoms):
    import numpy as np
    D = lcm(*(d for d,a in atoms))
    assert 2*D*sum(a for d,a in atoms) < 2**63
    n = np.arange(1,D+1,dtype=np.int64)
    S = np.zeros(D,dtype=np.int64)
    for d,a in atoms:
        S += (n % d == 0)*a
    return D,S

def period_search(atoms,denominator,all_lengths=False):
    import numpy as np
    D,S = period_values(atoms)
    LP = np.concatenate(([0],np.cumsum(np.maximum(S-2*denominator,0))))
    RP = np.concatenate(([0],np.cumsum(np.tile(
        np.maximum(S-denominator,0),2))))
    lengths = (range(1,D+1) if all_lengths else
               sorted({D} | {m for m in (66,100,1000,10000,100000,1000000)
                             if m <= D}))
    H = sum(F(a,denominator*d) for d,a in atoms)
    assert H < 1
    total = eligible = 0
    records = []
    for m in lengths:
        windows = RP[m:m+D]-RP[:D]
        lhs = int(LP[m])
        rhs = int(windows.min())
        x = int(windows.argmin())
        assert lhs <= rhs,(atoms,denominator,m,x,lhs,rhs)
        total += D
        mu = F(int(S[:m].sum()),m*denominator)
        assert mu <= H
        if (m >= 66 and 6*max(d for d,a in atoms) <= m and
                lhs > 0 and mu-H*H/6 < 1):
            eligible += D
        if not all_lengths or m in (66,100,1000,D):
            records.append((m,lhs,rhs,x))
    return D,total,eligible,H,tuple(records)

def audit_period_search():
    total = eligible = 0
    for N in (5,6,7,8):
        den = factorial(N)
        for kind in (0,1):
            weights = (tuple(den-den//(i+2) for i in range(N)) if kind == 0
                       else tuple(den*(i+2)//(N+2) for i in range(N)))
            result = period_search(tuple(zip(PRIMES[:N],weights)),den,N == 5)
            total += result[1]
            eligible += result[2]
            print("search:",N,kind,den,weights,result)
    atoms = tuple(z for p,a in zip(PRIMES[:5],(180,240,360,480,540))
                  for z in ((p,a),(p*p,720-a)))
    result = period_search(atoms,720)
    total += result[1]
    eligible += result[2]
    assert total == 190246980 and eligible == 127514310
    print("multi-level search:",atoms,result)
    print("search totals:",total,eligible)

def direct_hinges(atoms,denominator,m,x):
    import numpy as np
    n = np.arange(1,m+1,dtype=np.int64)
    left = np.zeros(m,dtype=np.int64)
    right = np.zeros(m,dtype=np.int64)
    for d,a in atoms:
        left += (n % d == 0)*a
        right += ((n+x%d) % d == 0)*a
    return (int(np.maximum(left-2*denominator,0).sum()),
            int(np.maximum(right-denominator,0).sum()))

def audit_special_windows():
    import numpy as np
    D = prod(PRIMES)
    n = np.arange(1,D+1,dtype=np.int64)
    free = np.ones(D,dtype=np.int64)
    for p in PRIMES:
        free[n % p == 0] = 0
    pref = np.concatenate(([0],np.cumsum(np.tile(free,2))))
    for m,x,baseline,maximum in HR:
        windows = pref[m:m+D]-pref[:D]
        assert int(windows.argmax()) == x
        assert int(pref[m]) == baseline
        assert int(windows[x]) == maximum > baseline
    del n,free,pref,windows
    for name,m,x,L,CK,CI,R in STRESS:
        lhs,rhs = direct_hinges(T3_ATOMS,720,m,x)
        assert 3*lhs == L and 3*rhs == R
        assert L <= CK <= CI <= R
    cluster = (101,103,107,109,113,127,131,137,139)
    assert all(all(p % a for a in range(2,p) if a*a <= p) for p in cluster)
    assert all(101 <= p and p*p < 2*101**2 for p in cluster)
    m = cluster[-2]*cluster[-1]
    x = prod(cluster)-m//2
    assert m == 19043 and x == 4343678784233757066
    assert direct_hinges(tuple((p,1) for p in cluster),1,m,x) == (0,8)
    print("sieve-rich windows:",HR)
    print("certificate stress chains:",STRESS)
    print("prime-cluster witness:",m,x,0,8)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--full",action="store_true")
    args = parser.parse_args()
    verify_base_and_constants()
    verify_boolean_kraft()
    verify_grid_certificates()
    verify_cyclic_certificate()
    verify_rejected_candidates()
    verify_explicit_certificate()
    if args.full:
        audit_open_projection_bound()
        audit_tail_grid(3)
        audit_tail_grid(6)
        audit_period_search()
        audit_special_windows()
    print("All requested exact checks passed.")

if __name__ == "__main__":
    main()
```

---

# Final claim ← lemmas ← unproved items

\[
\boxed{
\begin{array}{l}
(H_2)\text{ for unrestricted systems on at most four primes}\\
\qquad\leftarrow\text{Lemma 1}\\
\qquad\leftarrow\text{no unproved items}.
\\[5pt]
(H_2)\text{ for five primes with at most one multilevel prime}\\
\qquad\leftarrow\text{Theorem 4}\\
\qquad\leftarrow\text{Lemmas 1, 2, 3}\\
\qquad\leftarrow\text{no unproved items}.
\\[5pt]
(H_2)\text{ for }N\text{ primes with per-prime cap }2/(N-1)\\
\qquad\leftarrow\text{Theorem 5}\\
\qquad\leftarrow\text{no unproved items}.
\\[5pt]
(H_2)\text{ for five-prime cumulative grids }q=6\text{ or }8\\
\qquad\leftarrow\text{Lemma 6 and its explicit finite certificates}\\
\qquad\leftarrow\text{Lemma 1 and exhaustive exact verification}\\
\qquad\leftarrow\text{no unproved items}.
\\[5pt]
(H_2)\text{ for unrestricted systems on at most five primes}\\
\qquad\leftarrow\text{Lemma 8}\\
\qquad\leftarrow K_4\ \textbf{OPEN}.
\end{array}
}
\]

**Exact remaining gap for the unrestricted five-prime elimination route:** prove (9.1) for every four-prime set and every integer \(Q\ge2\), or replace it by another estimate controlling the fifth-prime increment for arbitrary four-prime multilevel systems.

**For all finite atom systems**, further induction steps are also missing; the direct five-prime antichain analogue already fails by (9.3).

**Largest unrestricted \(N\) proved: \(4\). Complete five-prime T3 theorem: proved above. Counterexample to \((H_2)\): none found.**