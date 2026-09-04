## Summary of the answer

* **T1.** For \(N\) groups whose masses are only known to lie in \((\beta,1]\), the largest uniform all-pairs weight is

\[
\lambda_\beta(N)=
\begin{cases}
0, & \beta\le \tfrac12,\\[2mm]
\displaystyle \min_{2\le s\le N}\frac{s\beta-1}{\binom{s}{2}}, & \beta>\tfrac12,
\end{cases}
\]

and for \(\beta>1/2\)

\[
\lambda_\beta(N)=
\min\!\left\{2\beta-1,\ \frac{2(N\beta-1)}{N(N-1)}\right\}.
\]

Equivalently, for \(N\ge 3\),

\[
\lambda_\beta(N)=
\begin{cases}
2\beta-1, & \frac12<\beta<\frac{N+1}{2N},\\[2mm]
\dfrac{2(N\beta-1)}{N(N-1)}, & \frac{N+1}{2N}\le \beta\le 1.
\end{cases}
\]

This condition is **necessary and sufficient** for a uniform guarantee over all mass vectors with \(x_i>\beta\). For a fixed unequal mass vector one can do better by using the exact subset sums; see Lemma 1 below.

* **True grouping guarantee from total mass \(>64\), arbitrary \(a_p\le1\).**  
  From total mass \(>64\) alone:

  * for every \(0<\beta\le 1/2\), one can guarantee **exactly 64** groups of mass in \((\beta,1]\);
  * for every \(\beta>1/2\), one can guarantee **zero** groups of mass in \((\beta,1]\).

  Thus the hoped-for guarantee “\(65\) groups of mass \(>64/65\)” is false for arbitrary unequal masses. It is an equal-mass phenomenon.

* **T2.** Within the \(x_i\in(\beta,1]\) all-pairs framework, there is **no positive universal pair constant** valid for every atom system with \(S_0(k)>64\). In fact, for any fixed \(N\) and any proposed positive constant \(c\), systems with many atoms of mass \(1/2+\delta\) force the pair constant to be \(O(\delta)\to0\).

  Consequently there is **no new universal sparse-core range from unequal masses via this pair certificate**. The best universal monomial bound of the form \(c\,m/k^{2/N}\) already proved in the setup is the 32-shadow bound written with \(N=64\):

\[
\sum_{b\in I}(S_0(b)-1)^+
\ge
\frac{32}{3}(1-6^{-31})\,m\,k^{-1/32}
=
c_{\rm sh}\,m\,k^{-2/64},
\]

with

\[
c_{\rm sh}=\frac{32}{3}(1-6^{-31}).
\]

The corresponding sparse-core inequality

\[
c_{\rm sh} m^{1-2/64}\ge 6.24\cdot 10^{-90}m
\]

gives

\[
\boxed{\log_{10}M
=
32\bigl(\log_{10}c_{\rm sh}+90-\log_{10}6.24\bigr)
=
2887.451\ldots}
\]

So the universal sparse-core endpoint remains \(10^{2887.451\ldots}\), not \(10^{2957\ldots}\).

* **T3.** For \(\ell\)-fold product certificates with uniform lower mass bound \(\beta\),

\[
\mu_\ell \binom{s}{\ell}\le (s\beta-1)^+
\]

is the exact uniform feasibility condition. Positive \(\mu_\ell\) requires \(\ell\beta>1\). Under the true universal guarantee \(\beta\le1/2,\ N\le64\), pairs are impossible, and the smallest positive \(\ell\) is \(\ell=3\), giving exponent \(3/64>1/32\), which is worse than the 32-shadow bound. Thus the heuristic \(N/\ell\approx32.5\) is **not** universally optimal. It is optimal only in the special equal-mass \(65\)-group situation.

---

# T1 — Exact all-pairs feasibility for groups of mass \((\beta,1]\)

## 1. Exact uniform pair weight

Let \(G_1,\dots,G_N\) be disjoint groups of primes, with

\[
x_i=\sum_{p\in G_i}a_p\in(\beta,1],
\qquad
D_i=\prod_{p\in G_i}q_p,
\]

and put a uniform certificate

\[
c_{D_iD_j}=\lambda\qquad (1\le i<j\le N),
\]

all other \(c_D=0\).

For an integer \(n\), let

\[
A(n)=\{i: D_i\mid n\},\qquad s=|A(n)|.
\]

If \(D_i\mid n\), then every active prime power contributing to \(a_p\) for \(p\in G_i\) divides \(n\), hence

\[
S_0(n)\ge \sum_{i\in A(n)}x_i.
\]

Therefore feasibility (F) is implied by

\[
\lambda\binom{s}{2}
\le
\left(\sum_{i\in A}x_i-1\right)^+
\tag{1}
\]

for every subset \(A\subseteq\{1,\dots,N\}\) of size \(s\ge2\).

If the only information is \(x_i>\beta\), then

\[
\sum_{i\in A}x_i>s\beta.
\]

Thus a uniform sufficient condition is

\[
\lambda\binom{s}{2}\le s\beta-1
\qquad\text{for every }s\ge2\text{ with }s\beta>1.
\tag{2}
\]

If \(s\beta\le1\), then the infimum of \((\sum_Ax_i-1)^+\) over all \(x_i>\beta\) is \(0\), so no positive uniform \(\lambda\) can be guaranteed once such an \(s\) is possible. Since \(s=2\) is possible whenever \(N\ge2\), positivity requires \(\beta>1/2\).

### Lemma 1 — largest uniform \(\lambda\) [PROVED]

For \(N\ge2\) and \(\beta\in(0,1]\), the largest uniform \(\lambda\) depending only on \(N,\beta\) and valid for all mass vectors \(x_i\in(\beta,1]\) is

\[
\lambda_\beta(N)=
\begin{cases}
0, & \beta\le \tfrac12,\\[2mm]
\displaystyle \min_{2\le s\le N}\frac{s\beta-1}{\binom{s}{2}}, & \beta>\tfrac12.
\end{cases}
\tag{3}
\]

For \(\beta>1/2\), this equals

\[
\lambda_\beta(N)=
\min\!\left\{2\beta-1,\ \frac{2(N\beta-1)}{N(N-1)}\right\}.
\tag{4}
\]

Equivalently, for \(N\ge3\),

\[
\lambda_\beta(N)=
\begin{cases}
2\beta-1, & \frac12<\beta<\frac{N+1}{2N},\\[2mm]
\dfrac{2(N\beta-1)}{N(N-1)}, & \frac{N+1}{2N}\le\beta\le1.
\end{cases}
\tag{5}
\]

#### Proof

Define

\[
f_s(\beta)=\frac{s\beta-1}{\binom{s}{2}}
=
\frac{2(s\beta-1)}{s(s-1)}.
\]

Sufficiency of \(\lambda\le\min_s f_s(\beta)\) follows from (2).

For necessity, fix \(s\in\{2,\dots,N\}\). Take all masses equal to \(\beta+\varepsilon\), and take \(A\) of size \(s\). Feasibility requires

\[
\lambda\binom{s}{2}
\le
s(\beta+\varepsilon)-1.
\]

Letting \(\varepsilon\downarrow0\) gives

\[
\lambda\le \frac{s\beta-1}{\binom{s}{2}}
\]

when \(s\beta\ge1\). If \(s\beta<1\), the right-hand side becomes negative for all sufficiently small \(\varepsilon\), forcing \(\lambda=0\). If \(s\beta=1\), it tends to \(0\), again forcing \(\lambda=0\). This proves (3).

For \(\beta>1/2\), all \(s\ge2\) satisfy \(s\beta>1\). To minimize \(f_s\), compare consecutive terms:

\[
f_s\ge f_{s+1}
\iff
(s+1)\beta\ge2.
\]

Thus the sequence can only have its minimum at an endpoint \(s=2\) or \(s=N\). Now

\[
f_2=2\beta-1,
\qquad
f_N=\frac{2(N\beta-1)}{N(N-1)}.
\]

Comparing them,

\[
f_2\ge f_N
\iff
\beta\ge \frac{N+1}{2N}
\]

for \(N\ge3\), giving (5). For \(N=2\), both endpoints coincide. ∎

---

## 2. Exact certificate for a fixed unequal mass vector

The \(\beta\)-bound is only a crude uniform lower bound. For a fixed grouping with actual masses \(x_1,\dots,x_N\), sort them:

\[
x_{(1)}\le x_{(2)}\le\cdots\le x_{(N)}.
\]

Let

\[
Y_s=\sum_{i=1}^s x_{(i)}
\]

be the sum of the \(s\) smallest masses. Then the exact largest uniform pair weight is

\[
\lambda_{\rm exact}
=
\min_{2\le s\le N}
\frac{(Y_s-1)^+}{\binom{s}{2}}.
\tag{6}
\]

### Lemma 2 — exact fixed-mass pair weight [PROVED]

For fixed masses \(x_i\), the pair certificate \(c_{D_iD_j}=\lambda\) is feasible iff

\[
\lambda\le
\min_{A:\ |A|\ge2}
\frac{\left(\sum_{i\in A}x_i-1\right)^+}{\binom{|A|}{2}}.
\]

Equivalently, after sorting,

\[
\lambda_{\rm exact}
=
\min_{2\le s\le N}
\frac{(Y_s-1)^+}{\binom{s}{2}}.
\]

#### Proof

For a subset \(A\) of size \(s\), the number of active pair-divisors is \(\binom{s}{2}\), while the available lower bound on \(S_0(n)-1\) is \(\sum_Ax_i-1\). The minimum over all subsets of size \(s\) is attained by the \(s\) smallest masses. Taking the minimum over \(s\) gives (6). ∎

This is the correct object for genuinely unequal masses. The \(\beta\)-formula in Lemma 1 is only a lower bound obtained from \(Y_s>s\beta\).

---

## 3. AM–GM value of the pair certificate

Assume we have \(N\) groups with pairwise coprime \(D_i\) and \(\prod_i D_i\mid k\). Let

\[
P=\prod_{i=1}^N D_i.
\]

Then \(P\le k\). The certificate value is

\[
\lambda\sum_{i<j}\left\lfloor\frac{m}{D_iD_j}\right\rfloor.
\]

### Lemma 3 — AM–GM/floor bound [PROVED]

For every \(m\ge1\),

\[
\sum_{i<j}\left\lfloor\frac{m}{D_iD_j}\right\rfloor
\ge
m\sum_{i<j}\frac1{D_iD_j}
-
\binom{N}{2}.
\tag{7}
\]

Moreover,

\[
\sum_{i<j}\frac1{D_iD_j}
\ge
\binom{N}{2}P^{-2/N}.
\tag{8}
\]

Hence

\[
\sum_{i<j}\left\lfloor\frac{m}{D_iD_j}\right\rfloor
\ge
\binom{N}{2}P^{-2/N}\left(m-P^{2/N}\right).
\tag{9}
\]

If \(m\ge k^{2/N}\), then

\[
\sum_{i<j}\left\lfloor\frac{m}{D_iD_j}\right\rfloor
\ge
\binom{N}{2}
\left(1-\frac{k^{2/N}}{m}\right)
m\,k^{-2/N}.
\tag{10}
\]

Thus, with

\[
\varepsilon=\min\left(1,\frac{k^{2/N}}{m}\right),
\]

we have the explicit bound

\[
\sum_{b\in I}(S_0(b)-1)^+
\ge
\lambda\binom{N}{2}(1-\varepsilon)m\,k^{-2/N}.
\tag{11}
\]

#### Proof

The floor bound (7) is immediate from \(\lfloor x\rfloor\ge x-1\).

For (8), note that

\[
\prod_{i<j}(D_iD_j)=\left(\prod_iD_i\right)^{N-1}=P^{N-1}.
\]

There are \(\binom{N}{2}\) terms, so AM–GM gives

\[
\sum_{i<j}\frac1{D_iD_j}
\ge
\binom{N}{2}
\left(\prod_{i<j}\frac1{D_iD_j}\right)^{1/\binom{N}{2}}
=
\binom{N}{2}
P^{-(N-1)/\binom{N}{2}}.
\]

Since

\[
\frac{N-1}{\binom{N}{2}}=\frac{2}{N},
\]

(8) follows. Combining (7) and (8) gives (9). Since \(P\le k\), if \(m\ge k^{2/N}\) then \(m-P^{2/N}\ge m-k^{2/N}\ge0\), and \(P^{-2/N}\ge k^{-2/N}\), yielding (10). ∎

---

## 4. True guarantee of groups in \((\beta,1]\) from total mass \(>64\)

We now answer the explicit guarantee question.

We have items \(a_p\in[0,1]\) with total mass \(T>64\). We want to know how many disjoint groups of total mass in \((\beta,1]\) can be guaranteed.

### Lemma 4 — true bin guarantee [PROVED]

Let \(T=\sum_p a_p>64\), with each \(a_p\in[0,1]\).

1. If \(0<\beta\le1/2\), one can always form **64** disjoint groups each having mass in \((\beta,1]\).

2. This is sharp: one cannot guarantee 65 groups for any \(\beta>0\).

3. If \(\beta>1/2\), one cannot guarantee even one group. In other words, the guaranteed number is \(0\).

#### Proof

##### Positive guarantee for \(\beta\le1/2\)

We construct groups greedily. Suppose we have already formed \(r<64\) groups, each of mass at most \(1\). The remaining total mass is strictly greater than

\[
64-r.
\]

For \(r\le63\), the remaining total is \(>1\). We claim any multiset of items in \([0,1]\) with total \(>1\) contains a submultiset of total in \((\beta,1]\) when \(\beta\le1/2\).

Indeed:

* If some remaining item has mass \(> \beta\), take that item alone. Its mass is \(\le1\).
* Otherwise every remaining item has mass \(\le\beta\). Add items greedily until the partial sum first exceeds \(\beta\). The previous partial sum is \(\le\beta\), and the last added item has mass \(\le\beta\), so the final sum is \(\le2\beta\le1\).

Thus we can form the next group. Repeating gives 64 groups.

##### Sharpness against 65 groups

Fix any \(\beta>0\). Take 64 atoms of mass \(1\) and one atom of mass \(\varepsilon\), where \(0<\varepsilon<\beta\). The total mass is \(64+\varepsilon>64\).

Any group of mass \(\le1\) containing a mass-\(1\) atom cannot contain anything else. Hence the 64 mass-\(1\) atoms give at most 64 groups. The remaining atom has mass \(\varepsilon<\beta\), so it cannot form another group in \((\beta,1]\). Therefore 65 groups cannot be guaranteed.

##### No guarantee for \(\beta>1/2\)

Fix \(\beta>1/2\). Take many atoms each of mass exactly \(\beta\), enough that the total mass exceeds \(64\). A single atom has mass \(\beta\), not \(>\beta\). Two atoms have mass \(2\beta>1\), and any larger collection has mass \(>1\). Therefore no group has mass in \((\beta,1]\). Hence the guaranteed number is 0. ∎

---

## 5. Consequence for optimizing \(N,\beta\) under arbitrary masses

A positive uniform pair weight in Lemma 1 requires \(\beta>1/2\). But Lemma 4 says that from total mass \(>64\) alone one cannot guarantee even one group with \(\beta>1/2\). Therefore:

### Corollary 5 — no universal positive \(\beta\)-pair certificate [PROVED]

There is no choice of \(N\ge2\) and \(\beta>1/2\) such that every atom system with \(S_0(k)>64\) admits \(N\) groups of mass in \((\beta,1]\) and hence a positive uniform pair certificate of the Lemma 1 type.

The only universal \(\beta\)-guarantee is \(\beta\le1/2\), for which \(\lambda_\beta(N)=0\).

In particular, the bound

\[
\beta=\frac{64}{65},\qquad N=65
\]

is not a consequence of \(S_0(k)>64\) alone. It requires an additional equal-mass or near-equal-mass hypothesis.

---

# T2 — Universal explicit bound and sparse-core range

## 1. No new universal all-pairs bound from the \((\beta,1]\) framework

The obstruction is stronger than the \(\beta\)-guarantee alone.

### Lemma 6 — pair constants collapse near mass \(1/2\) [PROVED]

Fix any \(N\ge2\). For every \(\eta>0\), there exists an atom system with \(S_0(k)>64\) such that any all-pairs certificate using \(N\) groups of mass \(\le1\) has

\[
\lambda\binom{N}{2}<\eta.
\]

#### Proof

Choose \(\delta>0\) so small that

\[
2\delta\binom{N}{2}<\eta.
\]

Take \(n\) distinct primes with

\[
a_p=\frac12+\delta
\]

and \(n(1/2+\delta)>64\). Let all \(q_p=2\), so this is a valid atom system with \(S_0(k)>64\).

Since two atoms together have mass

\[
1+2\delta>1,
\]

any group of mass \(\le1\) can contain at most one atom. Hence every nonempty group has mass exactly \(1/2+\delta\). For any two active groups, the available excess is

\[
2\left(\frac12+\delta\right)-1=2\delta.
\]

Thus feasibility forces

\[
\lambda\le2\delta,
\]

and therefore

\[
\lambda\binom{N}{2}\le2\delta\binom{N}{2}<\eta.
\]

Since \(\eta>0\) was arbitrary, no positive universal constant is possible. ∎

Thus the all-pairs unequal-mass certificate does **not** give a universal improvement over the 32-shadow bound.

---

## 2. Best universal monomial bound currently proved

The proved 32-shadow bound is

\[
\sum_{b\in I}(S_0(b)-1)^+
\ge
\frac{32}{3}(1-6^{-31})\,m\,k^{-1/32}.
\]

Writing the exponent as \(2/N\), take

\[
N=64,
\qquad
c=c_{\rm sh}=\frac{32}{3}(1-6^{-31}).
\]

Then

\[
\sum_{b\in I}(S_0(b)-1)^+
\ge
c_{\rm sh}\,m\,k^{-2/64}.
\]

This is not an all-pairs certificate, but it is the best explicit universal bound of the requested monomial form available from the proved inputs.

The sparse-core inequality is

\[
c_{\rm sh}m^{1-2/64}\ge 6.24\cdot10^{-90}m.
\]

Cancel \(m\) and solve:

\[
c_{\rm sh}m^{-1/32}\ge 6.24\cdot10^{-90},
\]

so

\[
m^{1/32}\le \frac{c_{\rm sh}}{6.24\cdot10^{-90}},
\]

and hence

\[
M=\left(\frac{c_{\rm sh}}{6.24\cdot10^{-90}}\right)^{32}.
\]

Taking base-10 logarithms,

\[
\log_{10}M
=
32\left(\log_{10}c_{\rm sh}+90-\log_{10}6.24\right).
\]

Explicitly,

\[
\log_{10}\frac{32}{3}=1.028028723\ldots,
\]

\[
\log_{10}6.24=0.795184591\ldots,
\]

and

\[
6^{-31}=10^{-24.12268876\ldots}=7.54\ldots\times10^{-25},
\]

so

\[
\log_{10}(1-6^{-31})
=
-3.3\ldots\times10^{-25},
\]

which is negligible at the displayed precision.

Therefore

\[
\log_{10}c_{\rm sh}
=
1.028028723\ldots
\]

and

\[
\boxed{
\log_{10}M
=
32(1.028028723\ldots+89.204815409\ldots)
=
2887.451012\ldots
}
\]

Thus the universal sparse-core endpoint from the proved universal bound is

\[
\boxed{M\approx 10^{2887.451}}.
\]

For comparison, the special 65 equal-mass pair certificate gives

\[
N=65,\qquad c\approx64,
\]

and hence

\[
\log_{10}M
=
\frac{65}{2}
\left(\log_{10}64+90-\log_{10}6.24\right)
=
2957.857\ldots,
\]

but that is **not valid for every atom system**.

---

# T3 — Triples and higher certificates

## 1. General \(\ell\)-fold feasibility

Suppose we have \(N\) groups with masses \(x_i>\beta\), and put a uniform certificate of weight \(\mu_\ell\) on every \(\ell\)-fold product

\[
D_{i_1}\cdots D_{i_\ell}.
\]

If \(s\) groups are active, then the number of active \(\ell\)-fold divisors is \(\binom{s}{\ell}\). The uniform \(\beta\)-feasibility condition is

\[
\mu_\ell\binom{s}{\ell}
\le
(s\beta-1)^+
\qquad
(\ell\le s\le N).
\tag{12}
\]

Thus the largest uniform \(\mu_\ell\) depending only on \(N,\beta\) is

\[
\mu_{\ell,\beta}(N)
=
\begin{cases}
0, & \ell\beta\le1,\\[2mm]
\displaystyle
\min_{\ell\le s\le N}
\frac{s\beta-1}{\binom{s}{\ell}},
& \ell\beta>1.
\end{cases}
\tag{13}
\]

The condition \(\ell\beta>1\) is necessary because \(s=\ell\) is possible.

### Lemma 7 — \(\ell\)-fold AM–GM value [PROVED]

Let

\[
P=\prod_{i=1}^N D_i\le k.
\]

Then

\[
\sum_{1\le i_1<\cdots<i_\ell\le N}
\left\lfloor
\frac{m}{D_{i_1}\cdots D_{i_\ell}}
\right\rfloor
\ge
\binom{N}{\ell}
P^{-\ell/N}
\left(m-P^{\ell/N}\right).
\]

If \(m\ge k^{\ell/N}\), then

\[
\sum_{1\le i_1<\cdots<i_\ell\le N}
\left\lfloor
\frac{m}{D_{i_1}\cdots D_{i_\ell}}
\right\rfloor
\ge
\binom{N}{\ell}
\left(1-\frac{k^{\ell/N}}{m}\right)
m\,k^{-\ell/N}.
\]

Thus

\[
\sum_{b\in I}(S_0(b)-1)^+
\ge
\mu_\ell\binom{N}{\ell}(1-\varepsilon)
m\,k^{-\ell/N},
\qquad
\varepsilon=\min\left(1,\frac{k^{\ell/N}}{m}\right).
\]

#### Proof

The product of all \(\ell\)-fold products is

\[
\prod_{i_1<\cdots<i_\ell}
D_{i_1}\cdots D_{i_\ell}
=
P^{\binom{N-1}{\ell-1}},
\]

because each \(D_i\) appears in exactly \(\binom{N-1}{\ell-1}\) of the \(\ell\)-fold products. Since

\[
\frac{\binom{N-1}{\ell-1}}{\binom{N}{\ell}}
=
\frac{\ell}{N},
\]

AM–GM gives

\[
\sum_{i_1<\cdots<i_\ell}
\frac1{D_{i_1}\cdots D_{i_\ell}}
\ge
\binom{N}{\ell}P^{-\ell/N}.
\]

The floor estimate is identical to the pair case. ∎

---

## 2. Universal guarantee under \((\beta,1]\) groups

From Lemma 4, the only universal positive group guarantee is with \(\beta\le1/2\) and \(N=64\).

### Pairs

For \(\ell=2\), positivity requires \(2\beta>1\), impossible under the universal guarantee \(\beta\le1/2\). Hence there is no universal pair certificate in this \((\beta,1]\) framework.

### Triples

For \(\ell=3\), \(\beta=1/2\) gives

\[
3\beta-1=\frac12>0.
\]

For \(\beta=1/2\),

\[
\frac{s/2-1}{\binom{s}{3}}
=
\frac{(s-2)/2}{s(s-1)(s-2)/6}
=
\frac{3}{s(s-1)},
\]

which is decreasing in \(s\). Hence for \(N=64\),

\[
\mu_{3,1/2}(64)
=
\frac{3}{64\cdot63}
=
\frac1{1344}.
\]

The corresponding constant is

\[
c_3
=
\mu_{3,1/2}(64)\binom{64}{3}
=
31.
\]

The exponent is

\[
\frac{3}{64}=0.046875,
\]

which is worse than \(1/32=0.03125\). The associated sparse-core endpoint would be

\[
\log_{10}M_3
=
\frac{64}{3}
\left(\log_{10}31+90-\log_{10}6.24\right).
\]

Using

\[
\log_{10}31=1.491361694\ldots,
\]

we get

\[
\boxed{
\log_{10}M_3
=
1934.851\ldots
}
\]

which is far weaker than the 32-shadow endpoint.

### Higher \(\ell\)

For \(\ell\ge4\), the exponent \(\ell/64\) is even larger, so these do not improve the universal range.

Thus, under the true universal \((\beta,1]\) grouping guarantee, the optimal positive \(\ell\) is \(\ell=3\), but it is still worse than the existing 32-shadow certificate.

---

## 3. On the heuristic \(N/\ell\approx32.5\)

The value \(N/\ell=32.5\) comes from the special equal-mass configuration

\[
N=65,\qquad x_i=1,\qquad \ell=2.
\]

In that special case, feasibility is

\[
\mu\binom{s}{2}\le s-1,
\]

and the minimum occurs at \(s=65\), giving

\[
\mu=\frac{2}{65},
\qquad
c=\mu\binom{65}{2}=64,
\qquad
\frac{N}{\ell}=32.5.
\]

But this is **not** a universal consequence of \(S_0(k)>64\).

### Lemma 8 — \(N/\ell\approx32.5\) is not universally optimal [PROVED]

For arbitrary masses with only \(S_0(k)>64\):

* one cannot guarantee \(65\) groups of mass close to \(1\);
* one cannot guarantee any positive number of groups with lower bound \(\beta>1/2\);
* the universal \((\beta,1]\) group guarantee is \(N=64\) at \(\beta=1/2\);
* pairs are then impossible, and triples give \(N/\ell=64/3\approx21.33\), not \(32.5\).

Therefore the claim that \(N/\ell\approx32.5\) is optimal for arbitrary unequal masses is false.

#### Remark on abstract exponent minimization

If one ignores bin-packing guarantees and merely assumes the existence of \(N\) groups of mass \(>\beta\) with total mass \(N\beta\le64\), then positive \(\ell\)-fold feasibility requires \(\ell\beta>1\). Formally,

\[
\frac{\ell}{N}\ge \frac{\ell\beta}{64}>\frac1{64}.
\]

Thus the abstract exponent can approach \(1/64\) by taking \(\beta\downarrow1/\ell\) and \(N\approx64\ell\), but the certificate constant tends to \(0\) because the constraint at \(s=\ell\) becomes tight. If one insists on a non-vanishing constant with the minimum at \(s=N\), the optimal pair configuration in the abstract model is not \(N=65\) but closer to \(N=127,\ \beta=64/127\), giving \(N/\ell=63.5\). In any case, the special value \(32.5\) is not a general optimum.

---

# Final explicit answers

## T1

For \(x_i\in(\beta,1]\), the exact uniform pair weight is

\[
\boxed{
\lambda_\beta(N)=
\begin{cases}
0, & \beta\le \tfrac12,\\[2mm]
\displaystyle
\min\!\left\{2\beta-1,\ \frac{2(N\beta-1)}{N(N-1)}\right\},
& \beta>\tfrac12.
\end{cases}
}
\]

The resulting bound, when \(m\ge k^{2/N}\), is

\[
\boxed{
\sum_{b\in I}(S_0(b)-1)^+
\ge
\lambda_\beta(N)\binom{N}{2}
\left(1-\frac{k^{2/N}}{m}\right)
m\,k^{-2/N}.
}
\]

The true guarantee from total mass \(>64\) is:

\[
\boxed{
\begin{array}{c|c}
\beta & \text{guaranteed number of groups in }(\beta,1]\\
\hline
0<\beta\le1/2 & 64\\
\beta>1/2 & 0
\end{array}
}
\]

Thus no positive universal \(\lambda\) follows for arbitrary unequal masses.

## T2

There is no nontrivial universal all-pairs bound of the T1 type for arbitrary unequal masses. The best universal proved monomial bound remains the 32-shadow bound:

\[
\boxed{
N=64,\qquad
c=\frac{32}{3}(1-6^{-31}),\qquad
\text{exponent }2/N=1/32.
}
\]

The sparse-core endpoint is

\[
\boxed{
\log_{10}M=2887.451012\ldots
}
\]

The equal-mass 65-group endpoint

\[
\log_{10}M\approx2957.857
\]

is valid only under the additional hypothesis of 65 mass-\(1\) groups.

## T3

For \(\ell\)-fold certificates,

\[
\boxed{
\mu_{\ell,\beta}(N)=
\begin{cases}
0, & \ell\beta\le1,\\[2mm]
\displaystyle
\min_{\ell\le s\le N}
\frac{s\beta-1}{\binom{s}{\ell}},
& \ell\beta>1.
\end{cases}
}
\]

Under the universal guarantee \(\beta\le1/2,\ N=64\):

* pairs are impossible;
* triples give

\[
\boxed{
N=64,\quad \ell=3,\quad \mu=\frac1{1344},\quad c=31,\quad \text{exponent }3/64;
}
\]

* this is worse than the 32-shadow exponent \(1/32\).

The heuristic \(N/\ell\approx32.5\) is therefore **refuted** as a universal optimum. It is only the special equal-mass \(65\)-group pair value.