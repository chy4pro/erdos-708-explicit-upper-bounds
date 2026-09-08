## Result

**I prove the following stronger incidence-graph bound, uniformly in \(A\) and \(x\):**
\[
\boxed{g(A,x)\le n+\beta(\Gamma).}
\tag{1}
\]

This completes **T3(c)** substantially beyond the pseudoforest case.

More precisely, let
\[
A_{\mathrm{core}}=\{a\in A:\omega(a)\ge3\},\qquad
k=|A_{\mathrm{core}}|,
\]
and form its shared-prime incidence graph anew, with cycle rank \(\beta_{\mathrm{core}}\). Then
\[
\boxed{g(A,x)\le 2n-k+\beta_{\mathrm{core}}.}
\tag{2}
\]
Consequently,
\[
\boxed{\beta_{\mathrm{core}}\le k\quad\Longrightarrow\quad g(A,x)\le2n.}
\tag{3}
\]

These results require **no restriction on \(a_n\)**, no primitivity assumption, no LP, and no prefix-to-window injection.

I also prove, independently of the supplied long-interval black box,
\[
\boxed{a_n\ge8n^3\Longrightarrow g(A,x)\le2n,}
\tag{4}
\]
and the additional range theorem
\[
\boxed{a_n\ge9n^2\Longrightarrow g(A,x)\le3n.}
\tag{5}
\]

**I do not obtain T1, T2, a uniform \(3n\) bound, or a uniform \(2n+o(n)\) bound.** The exact remaining ranges are stated below. The supplied \(11n\) result remains the uniform linear baseline; it is not used in any proof here.

The coefficient of \(\beta\) in (1) is sharp: an explicit primitive connected instance has
\[
n=3,\qquad \beta=1,\qquad g(A,x)=4=n+\beta.
\]

---

# 1. Route ledger and adversarial phase

The route roles below describe the construction and audit passes; they do not assert independent parallel tool agents.

| Route | Advantage | Weakness | Obstacle for the unrestricted target | Verification bridge | Judge decision |
|---|---|---|---|---|---|
| Adaptive anchors and collision groups | Charges only cycles internal to groups sharing an anchor | Still permits a large cycle charge | Obtain an arithmetic saving when \(\beta_{\mathrm{core}}>k\) | Two independent proofs of \(n+\beta\), plus exact constructions | **T3(c) completed**; unrestricted extension frozen |
| Exact prime-power shortages | Uses large valuations that the incidence count discards | Individual-prime repairs can overlap or waste opportunities | Uniformly amortize the total repair cost | Exact shortage formula; nested and actual shortages computed separately | Formula **PROVED**; uniform amortization **OPEN** |
| Multiplicative packing | Handles large \(a_n\) constructively | Does not cover the intermediate-length range | For \(3n\), the remaining range is \(3n<a_n<9n^2\) | Exact factor packing and distinct-multiple selection | Range theorems **PROVED**; uniform \(3n\) **OPEN** |
| Counterexample search and audit | Gives exact optima and explicit witnesses | Finite families cannot certify the universal statement | Find an actual optimum exceeding \(2n\) | Integer-only grouped \(0/1\) dynamic programming | No counterexample; maximum ratio found \(4/3\) |

The support-count reformulation and optimization over retained-input subsets leave the same unrestricted gap:

> Obtain an arithmetic saving for all primitive connected critical-range instances with \(\beta_{\mathrm{core}}>k\).

The graph route is therefore stopped at its proved cycle-rank theorem rather than promoted to a universal \(2n\) assertion.

## Exact adversarial instances

The first five exact computations, D0–D4, preceded the proof development. Subsequent audits added forced-collision, higher-degree, and boundary cases.

The following input sets are all primitive, connected, divisibility antichains, and consist entirely of inputs with at least three distinct prime factors. They satisfy
\[
2n<a_n<8n^3.
\]

| ID | \(A\) | \(x\) | \(n\) | \(\beta\) | Exact \(g(A,x)\) |
|---|---|---:|---:|---:|---:|
| D0 | \((30,42,70,105)\) | 0 | 4 | 5 | 4 |
| D1 | \((30,42,70,105)\) | 113 | 4 | 5 | 4 |
| D2 | \((30,42,66,70,105,165)\) | 151 | 6 | 8 | 5 |
| D3 | \((30,42,66,70,78,105,110,165)\) | 997 | 8 | 11 | 5 |
| D4 | \((30,42,66,70,105,110,154,165,231,385)\) | 1009 | 10 | 16 | 7 |
| D5 | \((105,120,126,140,150,168,180)\) | 12510 | 7 | 11 | 5 |
| D6 | \((330,420,462,630,770,1155)\) | 13282 | 6 | 14 | 4 |
| D7 | \((30,42,70,165,273)\) | 29900 | 5 | 5 | 3 |

**Instance selection is non-exhaustive. Every displayed optimum is an exhaustive exact DP result.** All optimal witnesses, additional retained instances, and the complete verifier appear below.

The maximum ratio among all retained instances and finite scans was
\[
\frac43,
\]
attained by
\[
A=(77,91,143),\qquad x=5934.
\]
A direct proof of its exact optimum is given in Lemma 6.

### Hensley–Richards-type obstruction tests

No specific historical Hensley–Richards fixture was supplied. I constructed and tested the following explicit **sifted-surplus windows**, rather than claiming access to a particular published fixture.

Write
\[
R_P(J)=\#\{b\in J:\gcd(b,\prod_{p\in P}p)=1\}.
\]

The exhaustive searches over one complete squarefree period gave:

| \(P\) | \(m\) | \(R_P([1,m])\) | Shift \(x\) | \(R_P((x,x+m])\) |
|---|---:|---:|---:|---:|
| \(\{2,3,5,7\}\) | 105 | 24 | 8 | 26 |
| \(\{2,3,5,7,11\}\) | 165 | 34 | 16 | 37 |

Both windows were included in the exact cover tests. Their survivor sets are printed in the run transcript. None of the proofs below assumes that these survivors inject into prefix survivors.

---

# 2. Definitions

Throughout,
\[
A=\{a_1,\ldots,a_n\},\qquad 1<a_1<\cdots<a_n=m,
\qquad I=\{x+1,\ldots,x+m\}.
\]

For every demanded prime \(p\), define
\[
c_p(j)=\#\{a\in A:p^j\mid a\},\qquad
D_p=\sum_{a\in A}v_p(a)=\sum_{j\ge1}c_p(j).
\]

For \(S\subseteq I\), put
\[
s_p(j)=\#\{b\in S:p^j\mid b\},\qquad
N_p(j)=\#\{b\in I:p^j\mid b\}.
\]

A set \(S\) is a **layer cover** of \(A\) when
\[
s_p(j)\ge c_p(j)\qquad\text{for every }p,j.
\]
A layer cover is a product cover, but the converse need not hold.

Let
\[
\mathcal P(A)=\{p:p\mid \prod_{a\in A}a\},
\qquad
\Omega_0(A)=\sum_{a\in A}\omega(a).
\]
Here \(\Omega_0\) counts distinct-prime incidences, not valuations.

Besides the shared-prime graph \(\Gamma\), use the full incidence graph \(H\), which includes **all** demanded primes. Adding private-prime leaves does not change either the number of components or the cycle rank. Therefore
\[
\beta(H)=\beta(\Gamma)=\beta,
\]
and
\[
\boxed{n+\beta=\Omega_0(A)-|\mathcal P(A)|+c.}
\tag{6}
\]

---

# 3. Proved lemmas and the main theorem

## Lemma 1 — Divisibility-count domination  
**PROVED.**

For every integer \(d\ge1\),
\[
\#\{a\in A:d\mid a\}
\le \left\lfloor\frac md\right\rfloor
\le \#\{b\in I:d\mid b\}.
\tag{7}
\]

### Proof

The distinct inputs divisible by \(d\) belong to
\[
\{d,2d,\ldots,\lfloor m/d\rfloor d\},
\]
proving the first inequality.

The second count is
\[
\left\lfloor\frac{x+m}{d}\right\rfloor
-\left\lfloor\frac xd\right\rfloor
\ge\left\lfloor\frac md\right\rfloor.
\]
In particular,
\[
N_p(j)\ge c_p(j)
\]
for every \(p,j\). ∎

---

## Lemma 2 — Exact nested shortage and exact valuation shortage  
**PROVED.**

Define
\[
\delta_p(S)=\max_{j\ge1}\bigl(c_p(j)-s_p(j)\bigr)^+.
\tag{8}
\]

Then \(\delta_p(S)\) is the minimum number of elements that must be added to \(S\) to satisfy **all the \(p\)-layer inequalities**.

Define separately
\[
\rho_p(S)=
\min\left\{
t\in\{0,\ldots,|I\setminus S|\}:
\sum_{j\ge1}\min\bigl(N_p(j),s_p(j)+t\bigr)\ge D_p
\right\}.
\tag{9}
\]

Then \(\rho_p(S)\) is the minimum number of additions needed to satisfy the **single total \(p\)-valuation demand**.

Moreover,
\[
\rho_p(S)\le\delta_p(S)
\tag{10}
\]
and
\[
\boxed{
g(A,x)\le |S|+\sum_p\rho_p(S)
\le |S|+\sum_p\delta_p(S).
}
\tag{11}
\]

### Proof

Order the elements of \(I\setminus S\) by nonincreasing \(p\)-valuation. If the first \(t\) are selected, the number of selected additions divisible by \(p^j\) is
\[
\min\bigl(t,N_p(j)-s_p(j)\bigr).
\]
Thus the resulting number of selected elements divisible by \(p^j\) is exactly
\[
s_p(j)+\min\bigl(t,N_p(j)-s_p(j)\bigr)
=\min\bigl(N_p(j),s_p(j)+t\bigr).
\tag{12}
\]

If \(t=\delta_p(S)\), then
\[
s_p(j)+t\ge c_p(j)
\]
for every \(j\), while Lemma 1 gives \(N_p(j)\ge c_p(j)\). Hence (12) is at least \(c_p(j)\).

Conversely, if \(t<\delta_p(S)\), some layer has shortage greater than \(t\), and \(t\) additions cannot repair it. This proves the assertion about \(\delta_p\).

Summing (12) over \(j\) gives the total \(p\)-valuation obtained from the best \(t\) additions. The same \(t\) largest-valuation elements maximize every nested layer simultaneously, so they maximize the total valuation. This proves (9).

A layer cover meets the total valuation demand, giving \(\rho_p\le\delta_p\).

For every prime, choose a minimizing repair set for that prime and take its union with \(S\). The union contains every individual repair set, so it meets every demanded prime valuation. Its cardinality is at most the sum of the individual cardinalities. This proves (11). ∎

**Important distinction:** \(\delta_p\) is exact for nested layer domination; \(\rho_p\) is exact for the actual single-prime product demand. They are not generally equal.

---

## Lemma 3 — Cycle ranks of input-disjoint induced subgraphs  
**PROVED.**

Suppose the input vertices are partitioned into nonempty sets
\[
A=C_1\sqcup\cdots\sqcup C_t.
\]
For each \(i\), let \(H_i\) be the full incidence graph of \(C_i\), and let its cycle rank be \(\beta_i\). Then
\[
\sum_{i=1}^t\beta_i\le\beta(H).
\tag{13}
\]

Also, writing \(c_i\) for the number of components of \(H_i\),
\[
\sum_{a\in C_i}\omega(a)-|\mathcal P(C_i)|
=|C_i|-c_i+\beta_i.
\tag{14}
\]

### Proof

Equation (14) is the identity
\[
\beta_i=|E(H_i)|-|V(H_i)|+c_i.
\]

Start with disjoint copies of the graphs \(H_i\). Recover \(H\) by identifying copies of the same prime vertex.

An identification reduces the vertex count by one and leaves the edge count unchanged. If the identified vertices were in different components, the component count also falls by one, so the cycle rank is unchanged. If they were already in the same component, the component count is unchanged, so the cycle rank increases by one.

Consequently, identifying prime vertices never decreases the cycle rank. The initial cycle rank was \(\sum_i\beta_i\), proving (13). ∎

---

## Theorem 4 — The collision-cycle bound  
**PROVED.**

For every instance,
\[
\boxed{g(A,x)\le n+\beta(\Gamma).}
\tag{15}
\]

In fact, arbitrary whole-input anchors already give a layer-cover certificate of this size.

### Proof

For each \(a\in A\), choose any multiple
\[
b(a)\in I,\qquad a\mid b(a).
\]
Such a multiple exists by Lemma 1.

Let
\[
S=\{b(a):a\in A\}.
\]
Partition \(A\) into the nonempty collision groups
\[
C_b=\{a\in A:b(a)=b\},\qquad b\in S.
\]

For a group \(C\), put
\[
r_{C,p}(j)=\#\{a\in C:p^j\mid a\}.
\]
If \(r_{C,p}(j)>0\), its common anchor is divisible by \(p^j\). Hence
\[
c_p(j)-s_p(j)
\le
\sum_C\bigl(r_{C,p}(j)-1\bigr)^+.
\]
Because \(r_{C,p}(j)\le r_{C,p}(1)\),
\[
\delta_p(S)
\le
\sum_C\bigl(r_{C,p}(1)-1\bigr)^+.
\tag{16}
\]

Summing over primes,
\[
\sum_p\delta_p(S)
\le
\sum_C
\left(
\sum_{a\in C}\omega(a)-|\mathcal P(C)|
\right).
\tag{17}
\]

There is one anchor per collision group. By Lemma 3,
\[
\begin{aligned}
|S|+\sum_p\delta_p(S)
&\le
\sum_C
\left(
1+\sum_{a\in C}\omega(a)-|\mathcal P(C)|
\right)\\
&=
\sum_C\bigl(|C|+\beta_C-c_C+1\bigr)\\
&\le
\sum_C\bigl(|C|+\beta_C\bigr)\\
&\le n+\beta.
\end{aligned}
\]
Here \(c_C\ge1\), and the last inequality is (13).

Lemma 2 now gives (15). ∎

### Independent constructive proof

This second proof also supplies the adaptive algorithm printed below.

Process the inputs component by component. Within each component, order them so that every input after the first shares a prime with an earlier input. Such an ordering exists by connectedness of the incidence graph.

Maintain a layer cover \(S\) of all processed inputs.

When processing a new input \(a\), let \(q(a)\) be the number of its distinct primes already occurring in earlier inputs.

If \(a\) has a multiple in \(I\setminus S\), add one such multiple. This costs one element and preserves layer domination.

Otherwise every interval multiple of \(a\) is already in \(S\). At least one exists. Therefore every prime newly introduced by \(a\) already has its entire new layer demand covered by \(S\).

For an old prime \(p\mid a\), adding \(a\) increases each relevant layer demand by only one. Thus its new nested shortage is at most one. Lemma 2 repairs it with at most one further interval element. Therefore this step costs at most \(q(a)\).

Each component root costs at most one. Every other input has \(q(a)\ge1\), so its cost is at most \(q(a)\) in either case.

Each prime is counted in \(q(a)\) at every occurrence after its first. Consequently,
\[
\sum_a q(a)=\Omega_0(A)-|\mathcal P(A)|.
\]
The total number of selected elements is therefore at most
\[
c+\Omega_0(A)-|\mathcal P(A)|
=n+\beta.
\]
The maintained layer inequalities imply product divisibility. ∎

---

## Lemma 5 — Retained-input and core bounds  
**PROVED.**

For every subset \(C\subseteq A\),
\[
\boxed{
g(A,x)\le
|C|+\beta(\Gamma_C)+\sum_{a\in A\setminus C}\omega(a).
}
\tag{18}
\]
For \(C=\varnothing\), take \(\beta(\Gamma_C)=0\).

In particular, with \(C=A_{\mathrm{core}}\),
\[
\boxed{g(A,x)\le2n-k+\beta_{\mathrm{core}}.}
\tag{19}
\]

### Proof

First suppose \(C\ne\varnothing\). Apply the construction in Theorem 4 to \(C\), obtaining anchors \(S_C\) such that
\[
|S_C|+\sum_p\delta_{C,p}(S_C)
\le |C|+\beta(\Gamma_C).
\tag{20}
\]
The construction works in the full interval \(I\), since its length is at least \(\max C\).

For every \(p,j\),
\[
c_{A,p}(j)
=c_{C,p}(j)+c_{A\setminus C,p}(j),
\]
so
\[
\delta_{A,p}(S_C)
\le
\delta_{C,p}(S_C)+c_{A\setminus C,p}(1).
\]
Summing and using Lemma 2,
\[
g(A,x)
\le
|C|+\beta(\Gamma_C)
+\sum_p c_{A\setminus C,p}(1),
\]
which is (18).

For \(C=\varnothing\), take no anchors and use
\[
\delta_{A,p}(\varnothing)\le c_{A,p}(1).
\]

Finally, every discarded input has at most two distinct prime factors, so
\[
\sum_{a\notin A_{\mathrm{core}}}\omega(a)\le2(n-k).
\]
Substitution gives (19). ∎

### Consequences

For the full graph,
\[
\beta\le n\Longrightarrow g(A,x)\le2n.
\]

After discarding the low-\(\omega\) inputs,
\[
\beta_{\mathrm{core}}\le k
\Longrightarrow g(A,x)\le2n.
\]

More generally, any family satisfying
\[
\beta_{\mathrm{core}}\le k+\varepsilon_n n
\]
satisfies
\[
g(A,x)\le(2+\varepsilon_n)n.
\]
This is a proved **structural-family statement**, not a uniform assertion that \(\varepsilon_n\to0\).

For forests, Theorem 4 improves the stated bound to
\[
\boxed{\beta=0\Longrightarrow g(A,x)\le n.}
\]

---

## Lemma 6 — Exact sharpness witness for \(n+\beta\)  
**PROVED.**

Let
\[
A=(77,91,143),\qquad x=5934,
\qquad I=\{5935,\ldots,6077\}.
\]
Then
\[
\beta=1,\qquad g(A,x)=4.
\]

### Proof

The demanded primes are \(7,11,13\), each with total demand two. Their incidence graph is a six-cycle, so \(\beta=1\).

Put
\[
M=6006=6\cdot7\cdot11\cdot13.
\]
The interval is
\[
I=[M-71,M+71]\cap\mathbb Z.
\]

Each pair product
\[
77,\quad91,\quad143
\]
exceeds \(71\). Since \(M\) is divisible by all three, it is the only interval element divisible by any two of the demanded primes.

Also, \(I\) contains no multiple of \(13^2=169\), because
\[
35\cdot169=5915<5935,\qquad
36\cdot169=6084>6077.
\]

Suppose three elements formed a product cover.

If \(M\) were selected, it would supply one unit at each demanded prime. The two remaining elements would have to supply a positive valuation at all three primes, but each is divisible by at most one of them. Impossible.

If \(M\) were not selected, every selected element would involve at most one demanded prime. Two distinct elements would be needed for the \(13\)-demand, and at least one additional element for each of \(7\) and \(11\). Again at least four elements are needed.

Thus \(g(A,x)\ge4\).

Conversely,
\[
B=(5941,5954,5978,6050)
\]
is a cover, since
\[
5941=13\cdot457,\quad
5954=13\cdot458,\quad
5978=7^2\cdot122,\quad
6050=11^2\cdot50.
\]
All four numbers lie in \(I\). Hence \(g(A,x)=4=n+\beta\). ∎

Thus a universal replacement
\[
g(A,x)\le n+\theta\beta,\qquad \theta<1,
\]
is **REFUTED** by this instance.

---

## Lemma 7 — Multiplicative bin packing  
**PROVED.**

Let \(T>1\), and let \(q_1,\ldots,q_r\in(1,T]\). If
\[
\prod_{i=1}^r q_i\le T^{(h+1)/2},
\]
then these factors can be partitioned into at most \(h\) groups, each having product at most \(T\).

### Proof

Take a partition into the minimum possible number \(u\) of groups with products
\[
b_1,\ldots,b_u\le T.
\]
Such a partition exists by putting every factor in its own group.

No two groups can be merged, so
\[
b_i b_j>T\qquad(i\ne j).
\]
If \(u\ge h+1\), multiplication over all pairs gives
\[
\left(\prod_i b_i\right)^{u-1}
>T^{u(u-1)/2},
\]
hence
\[
\prod_i b_i>T^{u/2}\ge T^{(h+1)/2},
\]
contrary to the hypothesis. Therefore \(u\le h\). ∎

---

## Theorem 8 — Constructive \(2n\) and \(3n\) range bounds  
**PROVED.**

For every instance,
\[
m\ge8n^3\Longrightarrow g(A,x)\le2n,
\]
and
\[
m\ge9n^2\Longrightarrow g(A,x)\le3n.
\]

### Proof

Treat the two cases simultaneously. Let
\[
h\in\{2,3\},\qquad T=\frac{m}{hn}.
\]

Under the respective hypotheses,
\[
T^2\ge m,\qquad T\ge hn,
\tag{21}
\]
and
\[
m\le T^{(h+1)/2}.
\tag{22}
\]

For \(h=2\), (22) is equivalent to \(m\ge8n^3\).  
For \(h=3\), it is equivalent to \(m\ge9n^2\).

Factor every input into its full prime-power atoms
\[
a=\prod_{p\mid a}p^{v_p(a)}.
\]

Call an atom **large** if it exceeds \(T\). By \(T^2\ge m\), an input has at most one large atom.

If an input has a large atom \(q\), its remaining factor is
\[
a/q<m/T=hn\le T.
\]
Thus such an input contributes one large atom and at most one small factor.

If an input has no large atom, all its atoms are at most \(T\), and their product is at most
\[
m\le T^{(h+1)/2}.
\]
Lemma 7 partitions them into at most \(h\) small factors, each at most \(T\).

Suppose \(t\) inputs have a large atom. There are \(t\) large-atom occurrences, and at most
\[
h(n-t)+t\le hn-t
\tag{23}
\]
small factors.

For each prime \(p\), choose as many interval elements with largest \(p\)-valuations as there are large \(p\)-atoms. Lemma 1 guarantees that their sorted valuations dominate the sorted exponents of these large atoms. Their union therefore covers all large atoms using at most \(t\) elements. Overlaps between different primes are harmless.

Now select a fresh interval multiple for each small factor \(f\). Since \(f\le T\),
\[
\#\{b\in I:f\mid b\}
\ge\left\lfloor\frac mf\right\rfloor
\ge hn.
\]
Before any such selection, fewer than \(hn\) elements have been selected. Hence a fresh multiple exists.

All small-factor selections are globally distinct and avoid the large-atom selections. Their products therefore contribute all the required small factors in addition to the already covered large atoms.

By (23), the total cardinality is at most \(hn\). ∎

---

# 4. Audit of the supplied machinery

The new results do not require the published hinge inequality or either published linear bound.

## P1: verified with the necessary distinction

Lemma 2 gives both exact notions of shortage. The proof of the cycle bound uses \(\delta_p\), whose invariant is **layer domination**, not merely total product divisibility.

## P2: verified, and dominated by Theorem 4

Let \(a_*\) maximize \(\omega(a)\). The component containing \(a_*\) contains at least \(\omega(a_*)\) distinct primes. Each other component contains at least one prime. Thus
\[
|\mathcal P(A)|\ge\omega(a_*)+c-1.
\]
By (6) and Theorem 4,
\[
g(A,x)
\le\Omega_0(A)-|\mathcal P(A)|+c
\le\Omega_0(A)-\omega(a_*)+1.
\]

## P5/P6: normalization and disjoint-support decomposition  
**PROVED.**

If \(d\mid a\) for every \(a\in A\), set \(A'=A/d\) and \(m'=m/d\). The multiples of \(d\) in \(I\), divided by \(d\), form the consecutive interval
\[
\left\{\left\lfloor\frac xd\right\rfloor+1,\ldots,
\left\lfloor\frac xd\right\rfloor+m'\right\}.
\]
A cover of \(A'\) can be padded to at least \(n\) elements because \(m'\ge n\). Multiplying those elements by \(d\) then supplies at least \(d^n\), proving
\[
g(A,x)\le
\max\left(n,g\!\left(A',\left\lfloor x/d\right\rfloor\right)\right),
\]
with an input \(1\) carrying no demand.

For components with disjoint demanded prime supports, solve each component in a subinterval of \(I\) of the required length and take the union. Although chosen elements may overlap, demanded primes from different components do not. The union therefore covers all components, with cardinality at most the sum of their cover sizes.

These observations justify primitive connected minimal-counterexample reductions.

## P7: verified as a consequence of the stronger theorem

Since
\[
n+\beta=W_s-s+c,
\]
and
\[
(n+W_s-\nu)-(W_s-s+c)
=n+s-\nu-c\ge0,
\]
Theorem 4 implies P7.

## P8: matching deficiency verified

For completeness, the matching deficiency identity is
\[
s-\nu=\max_{T\subseteq Q}\bigl(|T|-|N(T)|\bigr).
\tag{24}
\]

One inequality follows because at most \(|N(T)|\) vertices of \(T\) can be matched. For the converse, start alternating paths at all unmatched shared-prime vertices in a maximum matching. No reachable input is unmatched, or there would be an augmenting path. The reachable prime set \(T\) consists of the unmatched roots together with the matched partners of its reachable input set \(N(T)\). Hence
\[
|T|-|N(T)|=s-\nu.
\]

For nonempty \(T\), every prime vertex has degree at least two, so
\[
2|T|\le E_T=|T|+|N(T)|-c_T+\beta_T.
\]
The subgraph has \(c_T\ge1\) and \(\beta_T\le\beta\), whence
\[
|T|-|N(T)|\le\beta-1.
\]
Together with the empty set in (24),
\[
s-\nu\le\max(0,\beta-1).
\]
Applying the same argument componentwise gives the stated componentwise version.

The new bound \(n+\beta\) does not depend on this deficiency estimate.

## P9: verified

Lemma 5 proves the deletion operation while preserving the required layer invariant.

## P11: the valuation-unit assertion verified

If \(m<8n^3\), three valuation units at primes exceeding \(2n\) would contribute a factor strictly greater than
\[
(2n)^3=8n^3>m
\]
to an input. Thus at most two such units occur in any input. No asymptotic prime-count estimate is used in the proofs here.

---

# 5. Where the strengthened graph route still fails

## Proposition 9 — The stronger retained-input graph certificate does not prove uniform \(3n\)  
**PROVED.**

Define
\[
\Theta_A(C)=
|C|+\beta(\Gamma_C)+
\sum_{a\in A\setminus C}\omega(a).
\]

For
\[
A=(330,420,462,630,770,1155),
\]
one has
\[
\boxed{\min_{C\subseteq A}\Theta_A(C)=20>18=3n.}
\tag{25}
\]

This is a failure of the **stronger certificate established here**, not a reassertion that the older P8 certificate can fail.

### Proof

Every input has four distinct prime factors, and the total prime support is
\[
\{2,3,5,7,11\}.
\]
Thus
\[
\Omega_0(A)=24.
\]

For nonempty \(C\), the full-incidence cycle identity gives
\[
\Theta_A(C)
=\Omega_0(A)-|\mathcal P(C)|+c_C
=24-|\mathcal P(C)|+c_C.
\]
Since \(|\mathcal P(C)|\le5\) and \(c_C\ge1\),
\[
\Theta_A(C)\ge20.
\]
For \(C=\varnothing\), the value is \(24\). Taking \(C=A\), which is connected, gives \(20\).

The instance is primitive and connected, and
\[
12<1155<8\cdot6^3=1728.
\]
Its cycle rank is
\[
24-6-5+1=14.
\]

At the tested shift \(x=13282\), the actual optimum is only four, with witness
\[
B=(13365,13552,13750,14406).
\]
That exact optimum is certified by the printed DP. Thus (25) is not a counterexample to Erdős's conjecture. ∎

## High degree does not itself reduce the nested shortage

For
\[
A=(105,120,126,140,150,168,180),\qquad x=12510,
\]
every input has exactly one interval multiple, namely \(12600\). Thus the forced whole-input anchor set is
\[
S=\{12600\}.
\]
The nested shortages are
\[
(\delta_2,\delta_3,\delta_5,\delta_7)=(5,5,4,3),
\]
giving
\[
|S|+\sum_p\delta_p=18.
\]

The actual single-prime shortages are instead
\[
(\rho_2,\rho_3,\rho_5,\rho_7)=(2,2,2,2),
\]
giving the upper bound nine. The exact optimum is five.

Therefore the candidate claim that high prime degree automatically saves one more unit in the **nested** shortage is **REFUTED**. Actual valuations do create substantial savings, but a uniform theorem amortizing them remains missing.

---

# 6. Exact remaining gaps and the uniform-bound statement

Let \(k=|A_{\mathrm{core}}|\).

## T1: precise remaining statement — **OPEN**

It remains to prove:
\[
\boxed{
\begin{gathered}
\text{For every primitive connected instance with}\\
2n<m<8n^3,\qquad \beta_{\mathrm{core}}>k,\\
\text{there exists }B\subseteq I,\quad |B|\le2n,\quad
\prod A\mid\prod B.
\end{gathered}}
\tag{G2}
\]

Outside this range, the trivial interval bound, Theorem 8, or Lemma 5 proves \(2n\).

## T3(a): precise remaining statement — **OPEN**

Lemma 5 already proves \(3n\) whenever
\[
\beta_{\mathrm{core}}\le n+k.
\]
Theorem 8 handles \(m\ge9n^2\), and the whole interval handles \(m\le3n\).

Thus the remaining statement for uniform \(3n\) is:
\[
\boxed{
\begin{gathered}
\text{For every primitive connected instance with}\\
3n<m<9n^2,\qquad \beta_{\mathrm{core}}>n+k,\\
\text{there exists a product cover of size at most }3n.
\end{gathered}}
\tag{G3}
\]

## T3(b): **OPEN**

The proved structural estimate is
\[
g(A,x)\le2n+(\beta_{\mathrm{core}}-k).
\]
No uniform \(o(n)\) control of the excess, or uniform arithmetic replacement for that excess, has been proved here.

## Best uniform conclusion actually established here

**No new uniform linear constant is proved.** The main uniform-in-\((A,x)\) improvement is \(n+\beta\), together with its core version.

For an explicit self-contained bound depending only on \(n\), define
\[
r(Y)=\max\left\{r\ge0:\prod_{i=1}^r p_i<Y\right\},
\]
where \(p_i\) is the \(i\)-th prime. The preceding proofs give
\[
g(n)\le
\min\left\{
\max\!\left(2n,(n-1)r(8n^3)+1\right),
\max\!\left(3n,(n-1)r(9n^2)+1\right)
\right\}.
\tag{26}
\]

Indeed, below either cutoff every input has at most the corresponding \(r(Y)\) distinct prime factors, so P2 gives \((n-1)r(Y)+1\); above the cutoff Theorem 8 applies. This is not an improvement over the supplied \(11n\) baseline for large \(n\). The completed target is the substantially enlarged \(2n\) cycle-rank class.

---

# 7. Exact-DP verification theorem

## Lemma 10 — Correctness of the printed optimizer  
**PROVED.**

The function `exact_dp` below returns \(g(A,x)\) exactly.

### Proof

Let \(P=\mathcal P(A)\), and let the demand vector be
\[
D=(D_p)_{p\in P}.
\]
Associate to every \(b\in I\) its capped valuation vector
\[
v(b)=\bigl(\min(D_p,v_p(b))\bigr)_{p\in P}.
\]

A subset covers the demanded product exactly when its componentwise capped vector sum equals \(D\).

Group interval elements with equal nonzero vector \(v\). If a group has \(M_v\) elements, selecting \(t\) of them contributes the capped vector \(tv\) at cost \(t\).

It is sufficient to consider
\[
0\le t\le
\min\left(
M_v,\,
\max_{p:v_p>0}\left\lceil\frac{D_p}{v_p}\right\rceil
\right).
\tag{27}
\]
Beyond this limit, every coordinate affected by \(v\) is already saturated even from the zero state. Extra elements cannot change the capped state and only increase the cardinality.

The DP initially stores only the zero state at cost zero. For each group it considers every count allowed by (27), updating from the previous stage rather than reusing newly updated states. Inductively, it stores the minimum cardinality realizing every reachable capped state.

Groups are disjoint sets of interval elements, and each chosen representative list contains distinct elements. Thus the stored witnesses are genuine \(0/1\) subsets, with no reuse.

After all groups, the value at \(D\) is therefore the minimum cardinality of a product cover. Lemma 1 guarantees feasibility of the full interval. ∎

The six finite shift scans contain **8,931 DP evaluations**, with the exact ranges printed below. They are exhaustive within those ranges, not an exhaustive search over all input sets or all critical instances.

---

# 8. Exact-arithmetic verifier — complete text

```python
"""Exact, standard-library-only verifier. No network, floating point, or LP.
Run with --all-scan-witnesses to print every witness in the finite scans.
"""

from itertools import combinations

from math import gcd, prod

from fractions import Fraction

import sys

def factor(n):
    out = {}
    d = 2
    while d*d <= n:
        while n % d == 0:
            out[d] = out.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out

def valuation(n, p):
    e = 0
    while n % p == 0:
        e += 1
        n //= p
    return e

def graph_data(A):
    fs = [factor(a) for a in A]
    Q = sorted(p for p in set().union(*(set(f) for f in fs))
               if sum(p in f for f in fs) >= 2)
    adj = [[i for i,f in enumerate(fs) if p in f] for p in Q]
    match = {}
    def augment(j, seen):
        for i in adj[j]:
            if i not in seen:
                seen.add(i)
                if i not in match or augment(match[i], seen):
                    match[i] = j
                    return True
        return False
    nu = sum(augment(j, set()) for j in range(len(Q)))
    parent = list(range(len(A)+len(Q)))
    def root(u):
        while parent[u] != u:
            parent[u] = parent[parent[u]]
            u = parent[u]
        return u
    for j, nb in enumerate(adj):
        for i in nb:
            parent[root(i)] = root(len(A)+j)
    c = len({root(i) for i in range(len(parent))})
    W = sum(map(len, adj))
    return Q, W, nu, c, W-len(A)-len(Q)+c

def exact_dp(A, x):
    """0/1 DP; equal capped valuation vectors are grouped without reuse."""
    m = max(A)
    fs = [factor(a) for a in A]
    ps = sorted(set().union(*(set(f) for f in fs)))
    D = tuple(sum(f.get(p,0) for f in fs) for p in ps)
    groups = {}
    for b in range(x+1, x+m+1):
        v = tuple(min(t,valuation(b,p)) for p,t in zip(ps,D))
        if any(v):
            groups.setdefault(v,[]).append(b)
    # A vector never needs more than max ceil(D_p/v_p) identical items.
    dp = {tuple(0 for _ in D): ()}
    for v, bs in sorted(groups.items(), key=lambda kv: (-sum(kv[0]),kv[0])):
        cap = min(len(bs), max((t+e-1)//e for t,e in zip(D,v) if e))
        new = dict(dp)
        for state, witness in dp.items():
            for k in range(1, cap+1):
                ns = tuple(min(t,s+k*e) for t,s,e in zip(D,state,v))
                w = witness + tuple(bs[:k])
                if ns not in new or len(w)<len(new[ns]):
                    new[ns] = w
        dp = new
    B = tuple(sorted(dp[D]))
    assert len(B)==len(set(B)) and all(x<b<=x+m for b in B)
    assert all(sum(valuation(b,p) for b in B)>=t for p,t in zip(ps,D))
    return len(B),B,tuple(ps),D,len(dp)

def anchor_data(A, x):
    fs = [factor(a) for a in A]
    ps = sorted(set().union(*(set(f) for f in fs)))
    groups = {}
    for a in A:
        b = ((x//a)+1)*a
        groups.setdefault(b, []).append(a)
    S = tuple(sorted(groups))
    delta = {}
    for p in ps:
        E = max(f.get(p,0) for f in fs)
        delta[p] = max([0]+[sum(f.get(p,0)>=j for f in fs)
                    - sum(valuation(b,p)>=j for b in S)
                    for j in range(1,E+1)])
    cert = len(S)+sum(delta.values())
    beta = graph_data(A)[-1]
    local_betas = sum(graph_data(tuple(C))[-1] for C in groups.values())
    assert cert <= len(A)+local_betas <= len(A)+beta
    return S,delta,cert,local_betas

def repair_data(A,x,S):
    fs=[factor(a) for a in A]
    ps=sorted(set().union(*(set(f) for f in fs)))
    rho={}
    for p in ps:
        demand=sum(f.get(p,0) for f in fs)
        need=max(0,demand-sum(valuation(b,p) for b in S))
        vals=sorted((valuation(b,p) for b in range(x+1,x+max(A)+1) if b not in S),reverse=True)
        k=0
        while need>0:
            need-=vals[k]; k+=1
        rho[p]=k
    return rho,len(S)+sum(rho.values())

def adaptive_cover(A,x):
    remain=list(A); S=set(); seen=set(); done=[]
    while remain:
        a=next((a for a in remain if set(factor(a))&seen),remain[0])
        remain.remove(a); done.append(a)
        fresh=next((b for b in range((x//a+1)*a,x+max(A)+1,a) if b not in S),None)
        if fresh is not None:
            S.add(fresh)
        else:
            fs=[factor(t) for t in done]
            for p in factor(a):
                E=max(f.get(p,0) for f in fs)
                delta=max([0]+[sum(f.get(p,0)>=j for f in fs)-sum(valuation(b,p)>=j for b in S) for j in range(1,E+1)])
                assert delta<=1
                if delta:
                    b=max((b for b in range(x+1,x+max(A)+1) if b not in S),key=lambda b:(valuation(b,p),-b))
                    S.add(b)
        seen.update(factor(a))
        for p in seen:
            E=max(valuation(t,p) for t in done)
            assert all(sum(valuation(b,p)>=j for b in S)>=sum(valuation(t,p)>=j for t in done) for j in range(1,E+1))
    assert len(S)<=len(A)+graph_data(A)[-1]
    return tuple(sorted(S))

def packed_cover(A,x,k):
    n=len(A); m=max(A); h=k*n
    assert k in (2,3)
    assert m >= (8*n**3 if k==2 else 9*n*n)
    big={}; small=[]
    def pack(atoms):
        bins=[1]*k
        def go(i):
            if i==len(atoms):return True
            tried=set()
            for j in range(k):
                if bins[j] not in tried and bins[j]*atoms[i]*h<=m:
                    tried.add(bins[j]); bins[j]*=atoms[i]
                    if go(i+1):return True
                    bins[j]//=atoms[i]
            return False
        assert go(0)
        return [b for b in bins if b>1]
    for a in A:
        fs=factor(a); large=[(p,e) for p,e in fs.items() if p**e*h>m]
        assert len(large)<=1
        if large:
            p,e=large[0];big.setdefault(p,[]).append(e)
            f=a//p**e
            if f>1:small.append(f)
            assert f*h<=m
        else:
            small.extend(pack(sorted((p**e for p,e in fs.items()),reverse=True)))
    S=set()
    for p,es in big.items():
        bs=sorted(range(x+1,x+m+1),key=lambda b:(-valuation(b,p),b))[:len(es)]
        assert all(valuation(b,p)>=e for b,e in zip(bs,sorted(es,reverse=True)))
        S.update(bs)
    for f in small:
        b=next(b for b in range((x//f+1)*f,x+m+1,f) if b not in S)
        S.add(b)
    assert len(S)<=h
    assert prod(S)%prod(A)==0
    return tuple(sorted(S))


A0 = (30,42,70,105)
A1 = (30,42,66,70,105,165)
A2 = (30,42,66,70,78,105,110,165)
A3 = (30,42,66,70,105,110,154,165,231,385)
A4 = (105,120,126,140,150,168,180)
A5 = (330,420,462,630,770,1155)
A6 = (30,42,70,165,273)
CASES = [
    ("D0", A0, 0, 4, (56,75,84,105)),
    ("D1", A0, 113, 4, (168,189,200,210)),
    ("D2", A1, 151, 5, (176,250,294,297,315)),
    ("D3", A2, 997, 5, (1050,1100,1134,1144,1155)),
    ("D4", A3, 1009, 7, (1029,1100,1155,1188,1232,1375,1386)),
    ("H0", A0, 8, 4, (56,75,84,105)),
    ("H1", A1, 16, 5, (135,147,165,175,176)),
    ("D5", A4, 12510, 5, (12544,12600,12625,12663,12690)),
    ("D6", A5, 13282, 4, (13365,13552,13750,14406)),
    ("D7", A6, 29900, 3, (29988,30000,30030)),
    ("D8", A0, 1207, 3, (1225,1260,1296)),
    ("T", (77,91,143), 5934, 4, (5941,5954,5978,6050)),
    ("F", (6,10,21), 53, 2, (60,63)),
    ("U0", (6,10,15), 53, 3, (54,55,60)),
    ("U1", (154,273,715), 29672, 3, (29744,30030,30135)),
    ("U2", (154,273,715), 0, 3, (462,546,715)),
    ("R0", (6,10,15), 0, 3, (10,12,15)),
    ("R1", (6,14,21), 0, 3, (14,18,21)),
    ("R2", (15,21,35), 0, 3, (15,21,35)),
    ("R3", (35,55,77), 0, 3, (35,55,77)),
    ("R4", (30,70,105), 0, 3, (84,100,105)),
]
SCANS = [
    (A0, range(0,211,7), (4,0,(56,75,84,105))),
    ((6,10,15), range(900), (3,0,(10,12,15))),
    ((6,14,21), range(2000), (3,0,(14,18,21))),
    ((15,21,35), range(2000), (3,0,(15,21,35))),
    ((35,55,77), range(2000), (3,0,(35,55,77))),
    ((30,70,105), range(2000), (3,0,(84,100,105))),
]
PACK_CASES = [
    ((154,273,715),29672,2,(29673,29674,29678,29705,29722,29757)),
    ((30,42,105,200),1009,3,(1010,1011,1015,1016,1020,1022,1035,1125)),
    ((30,105),8,2,(10,15,20,21)),
    ((30,165),16,2,(20,30,33)),
    ((30,42,105),8,3,(9,10,12,14,15,18,21)),
    ((30,42,165),16,3,(18,21,22,28,30,45)),
]

def valid(A,x,B):
    assert len(B)==len(set(B))
    assert all(x<b<=x+max(A) for b in B)
    assert prod(B)%prod(A)==0


def sift(A):
    P=tuple(sorted(set().union(*(set(factor(a)) for a in A))))
    L=prod(P); m=max(A)
    good=[int(gcd(i,L)==1) for i in range(L+m)]
    count=sum(good[1:m+1]); prefix=count; best=(count,0)
    for x in range(1,L):
        count+=good[x+m]-good[x]
        if count>best[0]:best=(count,x)
    survivors=tuple(b for b in range(best[1]+1,best[1]+m+1) if gcd(b,L)==1)
    return P,prefix,best,survivors


def main():
    maximum=Fraction(0)
    for name,A,x,want,B in CASES:
        got=exact_dp(A,x)
        assert got[0]==want and got[1]==B
        valid(A,x,B)
        maximum=max(maximum,Fraction(want,len(A)))
        print("EXACT",name,"A",A,"x",x,"graph",graph_data(A),"DP",got)
    assert maximum==Fraction(4,3)
    print("MAXIMUM_RETAINED_RATIO",maximum)
    for A,beta in [(A0,5),(A1,8),(A2,11),(A3,16),(A4,11),(A5,14),(A6,5)]:
        assert gcd(*A)==1 and all(b%a for a,b in combinations(A,2))
        assert all(len(factor(a))>=3 for a in A)
        assert 2*len(A)<max(A)<8*len(A)**3
        assert graph_data(A)[3:]==(1,beta)
    for A,want in [(A0,(24,(26,8))),(A1,(34,(37,16)))]:
        result=sift(A)
        assert result[1:3]==want
        print("SIFT",result)
    for name,A,x,want,B in CASES:
        data=anchor_data(A,x)
        rho,cost=repair_data(A,x,data[0])
        assert all(rho[p]<=data[1][p] for p in rho)
        adaptive=adaptive_cover(A,x)
        valid(A,x,adaptive)
        print("CERT",name,data,"RHO",rho,cost,"ADAPTIVE",adaptive)
    assert anchor_data(A4,12510)[2]==18
    assert repair_data(A4,12510,(12600,))==({2:2,3:2,5:2,7:2},9)
    for a in A4:
        assert tuple(range((12510//a+1)*a,12691,a))==(12600,)
    best=10**9; minimizer=None
    for mask in range(1<<len(A5)):
        C=tuple(a for i,a in enumerate(A5) if mask>>i&1)
        bound=len(C)+graph_data(C)[-1]+sum(len(factor(a)) for i,a in enumerate(A5) if not(mask>>i&1))
        if bound<best:best,minimizer=bound,C
    assert (best,minimizer)==(20,(330,420))
    print("SUBSET_BOUND_MINIMUM",best,minimizer)
    for A,x,k,B in PACK_CASES:
        assert packed_cover(A,x,k)==B
        valid(A,x,B)
        print("PACK",A,x,k,B)
    all_witnesses="--all-scan-witnesses" in sys.argv
    for A,xs,want in SCANS:
        best=(0,None,None)
        for x in xs:
            ans=exact_dp(A,x)
            if all_witnesses:print("SCAN_WITNESS",A,x,ans[:2])
            if ans[0]>best[0]:best=(ans[0],x,ans[1])
        assert best==want
        print("EXHAUSTIVE_FINITE_SCAN",A,(xs.start,xs.stop,xs.step),len(xs),best)
    assert sum(len(xs) for A,xs,want in SCANS)==8931
    print("ALL_CHECKS_PASSED")


if __name__=="__main__":
    main()
```

---

# 9. Complete retained run transcript

In `graph`, the tuple is
\[
(Q,W_s,\nu,c,\beta).
\]
In `DP`, the tuple is
\[
(g(A,x),B,\mathcal P(A),D,\text{number of reachable final states}).
\]
In `CERT`, the tuple is
\[
(S,\delta,\ |S|+\sum\delta,\ \sum_{\text{collision groups}}\beta_C).
\]

```text
EXACT D0 A (30, 42, 70, 105) x 0 graph ([2, 3, 5, 7], 12, 4, 1, 5) DP (4, (56, 75, 84, 105), (2, 3, 5, 7), (3, 3, 3, 3), 256)
EXACT D1 A (30, 42, 70, 105) x 113 graph ([2, 3, 5, 7], 12, 4, 1, 5) DP (4, (168, 189, 200, 210), (2, 3, 5, 7), (3, 3, 3, 3), 256)
EXACT D2 A (30, 42, 66, 70, 105, 165) x 151 graph ([2, 3, 5, 7, 11], 18, 5, 1, 8) DP (5, (176, 250, 294, 297, 315), (2, 3, 5, 7, 11), (4, 5, 4, 3, 2), 1800)
EXACT D3 A (30, 42, 66, 70, 78, 105, 110, 165) x 997 graph ([2, 3, 5, 7, 11], 23, 5, 1, 11) DP (5, (1050, 1100, 1134, 1144, 1155), (2, 3, 5, 7, 11, 13), (6, 6, 5, 3, 3, 1), 9408)
EXACT D4 A (30, 42, 66, 70, 105, 110, 154, 165, 231, 385) x 1009 graph ([2, 3, 5, 7, 11], 30, 5, 1, 16) DP (7, (1029, 1100, 1155, 1188, 1232, 1375, 1386), (2, 3, 5, 7, 11), (6, 6, 6, 6, 6), 16807)
EXACT H0 A (30, 42, 70, 105) x 8 graph ([2, 3, 5, 7], 12, 4, 1, 5) DP (4, (56, 75, 84, 105), (2, 3, 5, 7), (3, 3, 3, 3), 256)
EXACT H1 A (30, 42, 66, 70, 105, 165) x 16 graph ([2, 3, 5, 7, 11], 18, 5, 1, 8) DP (5, (135, 147, 165, 175, 176), (2, 3, 5, 7, 11), (4, 5, 4, 3, 2), 1800)
EXACT D5 A (105, 120, 126, 140, 150, 168, 180) x 12510 graph ([2, 3, 5, 7], 21, 4, 1, 11) DP (5, (12544, 12600, 12625, 12663, 12690), (2, 3, 5, 7), (12, 8, 6, 4), 4095)
EXACT D6 A (330, 420, 462, 630, 770, 1155) x 13282 graph ([2, 3, 5, 7, 11], 24, 5, 1, 14) DP (4, (13365, 13552, 13750, 14406), (2, 3, 5, 7, 11), (6, 6, 5, 5, 4), 8820)
EXACT D7 A (30, 42, 70, 165, 273) x 29900 graph ([2, 3, 5, 7], 13, 4, 1, 5) DP (3, (29988, 30000, 30030), (2, 3, 5, 7, 11, 13), (3, 4, 3, 3, 1, 1), 1280)
EXACT D8 A (30, 42, 70, 105) x 1207 graph ([2, 3, 5, 7], 12, 4, 1, 5) DP (3, (1225, 1260, 1296), (2, 3, 5, 7), (3, 3, 3, 3), 256)
EXACT T A (77, 91, 143) x 5934 graph ([7, 11, 13], 6, 3, 1, 1) DP (4, (5941, 5954, 5978, 6050), (7, 11, 13), (2, 2, 2), 27)
EXACT F A (6, 10, 21) x 53 graph ([2, 3], 4, 2, 1, 0) DP (2, (60, 63), (2, 3, 5, 7), (2, 2, 1, 1), 30)
EXACT U0 A (6, 10, 15) x 53 graph ([2, 3, 5], 6, 3, 1, 1) DP (3, (54, 55, 60), (2, 3, 5), (2, 2, 2), 27)
EXACT U1 A (154, 273, 715) x 29672 graph ([7, 11, 13], 6, 3, 1, 1) DP (3, (29744, 30030, 30135), (2, 3, 5, 7, 11, 13), (1, 1, 1, 2, 2, 2), 216)
EXACT U2 A (154, 273, 715) x 0 graph ([7, 11, 13], 6, 3, 1, 1) DP (3, (462, 546, 715), (2, 3, 5, 7, 11, 13), (1, 1, 1, 2, 2, 2), 216)
EXACT R0 A (6, 10, 15) x 0 graph ([2, 3, 5], 6, 3, 1, 1) DP (3, (10, 12, 15), (2, 3, 5), (2, 2, 2), 26)
EXACT R1 A (6, 14, 21) x 0 graph ([2, 3, 7], 6, 3, 1, 1) DP (3, (14, 18, 21), (2, 3, 7), (2, 2, 2), 26)
EXACT R2 A (15, 21, 35) x 0 graph ([3, 5, 7], 6, 3, 1, 1) DP (3, (15, 21, 35), (3, 5, 7), (2, 2, 2), 27)
EXACT R3 A (35, 55, 77) x 0 graph ([5, 7, 11], 6, 3, 1, 1) DP (3, (35, 55, 77), (5, 7, 11), (2, 2, 2), 27)
EXACT R4 A (30, 70, 105) x 0 graph ([2, 3, 5, 7], 9, 3, 1, 3) DP (3, (84, 100, 105), (2, 3, 5, 7), (2, 2, 3, 2), 108)
MAXIMUM_RETAINED_RATIO 4/3
SIFT ((2, 3, 5, 7), 24, (26, 8), (11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113))
SIFT ((2, 3, 5, 7, 11), 34, (37, 16), (17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 169, 173, 179, 181))
CERT D0 ((30, 42, 70, 105), {2: 0, 3: 0, 5: 0, 7: 0}, 4, 0) RHO {2: 0, 3: 0, 5: 0, 7: 0} 4 ADAPTIVE (30, 42, 70, 105)
CERT D1 ((120, 126, 140, 210), {2: 0, 3: 0, 5: 0, 7: 0}, 4, 0) RHO {2: 0, 3: 0, 5: 0, 7: 0} 4 ADAPTIVE (120, 126, 140, 210)
CERT D2 ((165, 168, 180, 198, 210), {2: 0, 3: 0, 5: 1, 7: 1, 11: 0}, 7, 1) RHO {2: 0, 3: 0, 5: 1, 7: 1, 11: 0} 7 ADAPTIVE (165, 168, 180, 198, 210, 315)
CERT D3 ((1008, 1014, 1020, 1050, 1056, 1100, 1155), {2: 0, 3: 0, 5: 1, 7: 0, 11: 0, 13: 0}, 8, 1) RHO {2: 0, 3: 0, 5: 0, 7: 0, 11: 0, 13: 0} 7 ADAPTIVE (1000, 1008, 1014, 1020, 1050, 1056, 1100, 1155)
CERT D4 ((1020, 1050, 1056, 1078, 1100, 1155), {2: 1, 3: 2, 5: 2, 7: 3, 11: 2}, 16, 6) RHO {2: 0, 3: 1, 5: 0, 7: 1, 11: 1} 9 ADAPTIVE (1020, 1029, 1050, 1056, 1078, 1100, 1120, 1155, 1320, 1386)
CERT H0 ((30, 42, 70, 105), {2: 0, 3: 0, 5: 0, 7: 0}, 4, 0) RHO {2: 0, 3: 0, 5: 0, 7: 0} 4 ADAPTIVE (30, 42, 70, 105)
CERT H1 ((30, 42, 66, 70, 105, 165), {2: 0, 3: 0, 5: 0, 7: 0, 11: 0}, 6, 0) RHO {2: 0, 3: 0, 5: 0, 7: 0, 11: 0} 6 ADAPTIVE (30, 42, 66, 70, 105, 165)
CERT D5 ((12600,), {2: 5, 3: 5, 5: 4, 7: 3}, 18, 11) RHO {2: 2, 3: 2, 5: 2, 7: 2} 9 ADAPTIVE (12525, 12544, 12550, 12555, 12593, 12600, 12608, 12625, 12636, 12642, 12672)
CERT D6 ((13398, 13440, 13530, 13860), {2: 1, 3: 1, 5: 2, 7: 2, 11: 1}, 11, 5) RHO {2: 0, 3: 1, 5: 1, 7: 1, 11: 1} 8 ADAPTIVE (13398, 13440, 13530, 13750, 13851, 13860, 14336, 14375, 14406)
CERT D7 ((29904, 29910, 29960, 30030), {2: 0, 3: 1, 5: 0, 7: 0, 11: 0, 13: 0}, 5, 0) RHO {2: 0, 3: 1, 5: 0, 7: 0, 11: 0, 13: 0} 5 ADAPTIVE (29904, 29910, 29960, 30030, 30132)
CERT D8 ((1218, 1230, 1260), {2: 0, 3: 0, 5: 1, 7: 1}, 5, 1) RHO {2: 0, 3: 0, 5: 1, 7: 1} 5 ADAPTIVE (1218, 1225, 1230, 1250, 1260)
CERT T ((6006,), {7: 1, 11: 1, 13: 1}, 4, 1) RHO {7: 1, 11: 1, 13: 1} 4 ADAPTIVE (5941, 5978, 6006, 6050)
CERT F ((54, 60, 63), {2: 0, 3: 0, 5: 0, 7: 0}, 3, 0) RHO {2: 0, 3: 0, 5: 0, 7: 0} 3 ADAPTIVE (54, 60, 63)
CERT U0 ((54, 60), {2: 0, 3: 0, 5: 1}, 3, 0) RHO {2: 0, 3: 0, 5: 1} 3 ADAPTIVE (54, 55, 60)
CERT U1 ((29722, 29757, 30030), {2: 0, 3: 0, 5: 0, 7: 0, 11: 0, 13: 0}, 3, 0) RHO {2: 0, 3: 0, 5: 0, 7: 0, 11: 0, 13: 0} 3 ADAPTIVE (29722, 29757, 30030)
CERT U2 ((154, 273, 715), {2: 0, 3: 0, 5: 0, 7: 0, 11: 0, 13: 0}, 3, 0) RHO {2: 0, 3: 0, 5: 0, 7: 0, 11: 0, 13: 0} 3 ADAPTIVE (154, 273, 715)
CERT R0 ((6, 10, 15), {2: 0, 3: 0, 5: 0}, 3, 0) RHO {2: 0, 3: 0, 5: 0} 3 ADAPTIVE (6, 10, 15)
CERT R1 ((6, 14, 21), {2: 0, 3: 0, 7: 0}, 3, 0) RHO {2: 0, 3: 0, 7: 0} 3 ADAPTIVE (6, 14, 21)
CERT R2 ((15, 21, 35), {3: 0, 5: 0, 7: 0}, 3, 0) RHO {3: 0, 5: 0, 7: 0} 3 ADAPTIVE (15, 21, 35)
CERT R3 ((35, 55, 77), {5: 0, 7: 0, 11: 0}, 3, 0) RHO {5: 0, 7: 0, 11: 0} 3 ADAPTIVE (35, 55, 77)
CERT R4 ((30, 70, 105), {2: 0, 3: 0, 5: 0, 7: 0}, 3, 0) RHO {2: 0, 3: 0, 5: 0, 7: 0} 3 ADAPTIVE (30, 70, 105)
SUBSET_BOUND_MINIMUM 20 (330, 420)
PACK (154, 273, 715) 29672 2 (29673, 29674, 29678, 29705, 29722, 29757)
PACK (30, 42, 105, 200) 1009 3 (1010, 1011, 1015, 1016, 1020, 1022, 1035, 1125)
PACK (30, 105) 8 2 (10, 15, 20, 21)
PACK (30, 165) 16 2 (20, 30, 33)
PACK (30, 42, 105) 8 3 (9, 10, 12, 14, 15, 18, 21)
PACK (30, 42, 165) 16 3 (18, 21, 22, 28, 30, 45)
EXHAUSTIVE_FINITE_SCAN (30, 42, 70, 105) (0, 211, 7) 31 (4, 0, (56, 75, 84, 105))
EXHAUSTIVE_FINITE_SCAN (6, 10, 15) (0, 900, 1) 900 (3, 0, (10, 12, 15))
EXHAUSTIVE_FINITE_SCAN (6, 14, 21) (0, 2000, 1) 2000 (3, 0, (14, 18, 21))
EXHAUSTIVE_FINITE_SCAN (15, 21, 35) (0, 2000, 1) 2000 (3, 0, (15, 21, 35))
EXHAUSTIVE_FINITE_SCAN (35, 55, 77) (0, 2000, 1) 2000 (3, 0, (35, 55, 77))
EXHAUSTIVE_FINITE_SCAN (30, 70, 105) (0, 2000, 1) 2000 (3, 0, (84, 100, 105))
ALL_CHECKS_PASSED
```

---

# 10. Final adversarial audit

| Possible failure | Audit result |
|---|---|
| Reusing the same interval element twice for one prime | Excluded: repairs and DP witnesses are subsets, not multisets |
| Summing valuations while claiming layer domination | Excluded: \(\rho_p\) and \(\delta_p\) are distinguished explicitly |
| Extending an arbitrary product cover as though it were a layer cover | Excluded: Theorems 4 and Lemma 5 preserve the stronger layer invariant |
| Counting the same cycle in several collision groups | Excluded by Lemma 3; gluing prime vertices cannot decrease cycle rank |
| Assuming private primes disappear without cost | Excluded: private-prime demands are carried by whole-input anchors; full-incidence identities retain their contribution |
| Assuming a prefix-to-window injection | Not used |
| Treating high cycle rank as evidence of a counterexample | Excluded: dense examples have exact optima far below their graph bounds |
| Promoting finite scans to a universal theorem | Not done |
| Deriving uniform \(3n\) from the strengthened graph certificate | Refuted by Proposition 9 |
| Using the published \(11n\), \(12n\), or hinge results as hidden dependencies | Not used |
| Treating a supplied historical Hensley–Richards example as tested | Not claimed; the explicit sifted-surplus fixtures are identified as such |
| Claiming the \(2n\) conjecture is settled | Not claimed |

## Final claim ← lemmas ← unproved items

```text
PROVED:
  g(A,x) <= n + beta(Gamma)
    <- Lemmas 1, 2, 3 and Theorem 4
    <- unproved items: NONE

  g(A,x) <= 2n - k + beta_core
    <- Theorem 4 and Lemma 5
    <- unproved items: NONE

  beta_core <= k  =>  g(A,x) <= 2n
    <- Lemma 5
    <- unproved items: NONE
    <- completed requested target: T3(c)

  beta = 0  =>  g(A,x) <= n
    <- Theorem 4
    <- unproved items: NONE

  m >= 8n^3  =>  g(A,x) <= 2n
    <- Lemmas 1, 7 and Theorem 8
    <- unproved items: NONE

  m >= 9n^2  =>  g(A,x) <= 3n
    <- Lemmas 1, 7 and Theorem 8
    <- unproved items: NONE

  g((77,91,143),5934) = 4 = n + beta
    <- Lemma 6, with explicit upper and lower witnesses
    <- unproved items: NONE

  All retained exact optima and finite-scan maxima
    <- Lemma 10, printed exact-arithmetic verifier,
       explicit inputs, explicit witnesses, and printed run transcript
    <- unproved mathematical items: NONE
    <- computational scope: only the printed instances and finite ranges

REFUTED:
  A universal bound n + theta*beta with theta < 1
    <- Lemma 6

  The strengthened retained-input graph certificate always proves 3n
    <- Proposition 9

OPEN:
  T1: g(n) <= 2n
    <- exact remaining statement (G2)

  T2: an instance with g(A,x) > 2n
    <- no such instance found

  T3(a): uniform g(n) <= 3n
    <- exact remaining statement (G3)

  T3(b): uniform g(n) <= 2n + o(n)
    <- no uniform control or arithmetic replacement
       of beta_core - k has been proved

UNIFORM LINEAR BASELINE:
  The user-supplied 11n theorem is unchanged.
  It is not a dependency of any result proved in this reply.
```