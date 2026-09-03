# Result

All logarithms are natural.

**T1 is proved.** More precisely, put

$$
\lambda(t):=\log(1+\log t).
$$

For every \(L\ge 16\), every interval \(J\) of \(L\) consecutive positive integers, and every finitely supported family \(0\le u_q\le1\), define

$$
X(n):=\sum_q \min \bigl(u_qv_q(n),1\bigr).
$$

Then

$$
\boxed{\;
\#\{n\le L:X(n)\ge 149e\,\lambda(L)\}
\le
\#\{n\in J:X(n)\ge1\}.
\;}
\tag{WSL\(_{149}\)}
$$

Consequently, for every \(m\ge16\),

$$
\boxed{\;
\sum_{k\le m}\bigl(w(k)-1-149e\log(1+\log m)\bigr)^+
\le
\sum_{b=x+1}^{x+m}(w(b)-1)^+.
\;}
\tag{1}
$$

Since, for \(m\ge16\),

$$
1+149e\log(1+\log m)<675\log\log m,
$$

we obtain the requested literal form

$$
\boxed{\quad (\mathrm{TH}_{675\log\log m})\qquad(m\ge16).\quad}
\tag{2}
$$

A convenient all-\(m\) regularization is

$$
\boxed{\quad
(\mathrm{TH}_{\,450\log(1+\log m)})\qquad(m\ge1).
\quad}
\tag{3}
$$

The proof is entirely analytic; no finite search or sampled computation is used.

---

## 1. Two-term higher-order Bonferroni inequality — **[PROVED]**

For integers \(r\ge0\), \(k\ge1\),

$$
\mathbf 1_{\{r\ge k\}}
\ge
\binom rk-k\binom r{k+1}.
\tag{4}
$$

Indeed:

* If \(r<k\), both binomial coefficients vanish.
* If \(r=k\) or \(r=k+1\), the right side equals \(1\).
* If \(r\ge k+2\), then

  $$
  \binom rk-k\binom r{k+1}
  =
  \binom rk\left(1-\frac{k(r-k)}{k+1}\right)\le0.
  $$

This is the \(k\)-hit analogue of the two-term Bonferroni estimate used in P1(b).

---

## 2. A gain-\(G\) sieve lemma for pairwise-coprime moduli — **[PROVED]**

Let \(L\ge16\), and write

$$
R:=\lfloor\log_2L\rfloor,\qquad
H:=e\log(1+\log L),\qquad
L_0:=\log(H+2).
\tag{5}
$$

Let \(\mathcal D\) be any finite family of pairwise-coprime integers \(d\ge2\), and put

$$
\nu_{\mathcal D}(n):=\#\{d\in\mathcal D:d\mid n\}.
$$

For \(1\le k\le R-1\), define

$$
\rho(k):=
\left\lceil
16H+
\frac{16kL_0}{\sqrt{\log(2+k/H)}}
\right\rceil,
\qquad
C(k):=2k+\rho(k).
\tag{6}
$$

### Lemma

For every real \(G\) with \(1\le G\le2H\), and every interval \(J\) of \(L\) consecutive integers,

$$
\boxed{\;
G\,\#\{n\le L:\nu_{\mathcal D}(n)\ge C(k)\}
\le
\#\{n\in J:\nu_{\mathcal D}(n)\ge k\}.
\;}
\tag{7}
$$

### Proof

Set

$$
y:=L^{1/(k+1)}\ge2,\qquad
\mathcal D_0:=\{d\in\mathcal D:d\le y\},
\qquad
H_0:=\sum_{d\in\mathcal D_0}\frac1d.
$$

Because the members of \(\mathcal D_0\) are pairwise coprime, choosing one prime divisor \(p_d\mid d\) for each \(d\) gives distinct primes. Hence, using P1(a),

$$
H_0
\le
\sum_{p\le y}\frac1p
\le
e\log(1+\log y)
\le H.
\tag{8}
$$

Let

$$
e_j:=\sum_{\substack{F\subseteq\mathcal D_0\\|F|=j}}
\frac1{\prod_{d\in F}d}
\tag{9}
$$

be the elementary symmetric sums of the numbers \(1/d\).

### 2.1 Lower bound in the arbitrary interval

Independently retain every member of \(\mathcal D_0\) with probability

$$
\theta:=\frac1{8H}.
$$

Call the random retained family \(\mathcal E\).

For a fixed \(\mathcal E\), summing (4) over \(n\in J\) gives

$$
\#\{n\in J:\nu_{\mathcal E}(n)\ge k\}
\ge M_k(\mathcal E)-kM_{k+1}(\mathcal E),
\tag{10}
$$

where

$$
M_j(\mathcal E)
:=
\sum_{\substack{F\subseteq\mathcal E\\|F|=j}}
\#\left\{n\in J:\prod_{d\in F}d\mid n\right\}.
$$

Taking expectations,

$$
\#\{n\in J:\nu_{\mathcal D}(n)\ge k\}
\ge
\theta^k\bigl(M_k-k\theta M_{k+1}\bigr),
\tag{11}
$$

where now \(M_j=M_j(\mathcal D_0)\).

Every product of \(k\) members of \(\mathcal D_0\) is at most

$$
y^k=L/y\le L/2.
$$

Thus, using the exact interval discrepancy

$$
\frac{L}{a}-1
\le \#\{n\in J:a\mid n\}
\le\frac{L}{a}+1,
$$

we have

$$
M_k\ge \frac L2 e_k.
\tag{12}
$$

Every product of \(k+1\) members is at most \(y^{k+1}=L\), so

$$
M_{k+1}\le2Le_{k+1}.
\tag{13}
$$

Expanding \(H_0e_k\) gives

$$
(k+1)e_{k+1}\le H_0e_k,
\tag{14}
$$

and hence

$$
k\theta M_{k+1}
\le
2k\theta Le_{k+1}
\le
2\theta LH_0e_k
\le
\frac L4e_k.
\tag{15}
$$

Therefore

$$
\#\{n\in J:\nu_{\mathcal D}(n)\ge k\}
\ge
\frac{Le_k}{4(8H)^k}.
\tag{16}
$$

### 2.2 Upper tail on \([1,L]\)

An integer \(n\le L\) can be divisible by at most \(k\) members of
\(\mathcal D\setminus\mathcal D_0\): otherwise it would be divisible by the product of \(k+1\) pairwise-coprime integers exceeding \(y\), and that product would exceed \(L\).

Consequently,

$$
\nu_{\mathcal D}(n)\ge2k+\rho(k)
\quad\Longrightarrow\quad
\nu_{\mathcal D_0}(n)\ge k+\rho(k).
$$

By the union bound over \((k+\rho(k))\)-subsets,

$$
\#\{n\le L:\nu_{\mathcal D}(n)\ge C(k)\}
\le
Le_{k+\rho(k)}.
\tag{17}
$$

For any \(r\ge0\),

$$
e_ke_r\ge \binom{k+r}{k}e_{k+r},
\qquad
e_r\le\frac{H_0^r}{r!}.
$$

Therefore

$$
e_{k+r}\le e_k\frac{H^r}{r!}.
\tag{18}
$$

Taking \(r=\rho(k)\),

$$
\#\{n\le L:\nu_{\mathcal D}(n)\ge C(k)\}
\le
Le_k\frac{H^{\rho(k)}}{\rho(k)!}.
\tag{19}
$$

### 2.3 The factorial gain

We use the following elementary analytic inequality. For every \(s\ge0\), with
\(\ell=\log(2+s)\),

$$
\log\left(
\frac{16(1+s/\sqrt\ell)}e
\right)
\ge\frac12\sqrt\ell.
\tag{20}
$$

To verify it, put \(t=\sqrt\ell\).

If \(t\le1\), the left side is at least \(\log(16/e)>1>t/2\).

If \(t\ge1\), then \(s=e^{t^2}-2\), and

$$
1+\frac{s}{t}\ge\frac{e^{t^2}}{2t}.
$$

Hence the difference between the two sides of (20) is at least

$$
\log(8/e)+t^2-\log t-\frac t2.
$$

Its derivative is

$$
2t-\frac1t-\frac12>0
$$

for \(t\ge1\), and its value at \(t=1\) is \(\log8-\tfrac12>0\).

Now set \(s=k/H\) and \(\ell=\log(2+k/H)\). Since \(L\ge16\), one has \(H>3\), hence \(L_0>1\). From (6) and (20),

$$
\log\frac{\rho(k)}{eH}
\ge\frac12\sqrt\ell.
$$

Using \(\rho!\ge(\rho/e)^\rho\),

$$
\log\frac{\rho(k)!}{H^{\rho(k)}}
\ge
\rho(k)\log\frac{\rho(k)}{eH}
\ge
8kL_0.
\tag{21}
$$

On the other hand, \(G\le2H\), so

$$
4G(8H)^k\le(8H)^{k+1}.
$$

Moreover

$$
8H\le(H+2)^3,
$$

and hence

$$
\log\bigl(4G(8H)^k\bigr)
\le
3(k+1)L_0
\le6kL_0.
\tag{22}
$$

Equations (21)–(22) imply

$$
4G(8H)^k\frac{H^{\rho(k)}}{\rho(k)!}\le1.
\tag{23}
$$

Combining (16), (19), and (23) proves (7). ∎

---

## 3. Exact dyadic encoding of fractional valuations — **[PROVED]**

Let

$$
X(n)=\sum_q s_q(n),
\qquad
s_q(n):=\min(u_qv_q(n),1).
$$

For every \(j\ge0\), put

$$
\tau_j:=2^{-j},
\qquad
N_j(n):=\#\{q:s_q(n)\ge\tau_j\}.
\tag{24}
$$

For \(u_q>0\), define

$$
d_{q,j}:=
q^{\left\lceil\tau_j/u_q\right\rceil}.
\tag{25}
$$

Then

$$
s_q(n)\ge\tau_j
\quad\Longleftrightarrow\quad
d_{q,j}\mid n.
\tag{26}
$$

For fixed \(j\), the integers \(d_{q,j}\), as \(q\) varies, are pairwise coprime. Thus every \(N_j\) is exactly a counting function \(\nu_{\mathcal D_j}\) to which Lemma 2 applies.

Also,

$$
X(n)
\le
D(n):=\sum_{j\ge0}2^{-j}N_j(n)
\le2X(n).
\tag{27}
$$

Indeed, for every \(s\in[0,1]\),

$$
s
\le
\sum_{j\ge0}2^{-j}\mathbf1_{\{s\ge2^{-j}\}}
\le2s.
$$

This encoding is exact for arbitrary \(p\)-adic valuations: no squarefree reduction or valuation-error term is introduced.

---

## 4. The weighted sieve lemma — **[PROVED]**

Continue with \(L\ge16\), and retain the notation

$$
R=\lfloor\log_2L\rfloor,\qquad
H=e\log(1+\log L),\qquad
L_0=\log(H+2).
$$

Let

$$
Q:=1+\left\lfloor\log_2(R-1)\right\rfloor.
\tag{28}
$$

Thus

$$
2^j\le R-1\quad(0\le j<Q),
\qquad
2^Q\ge R.
\tag{29}
$$

### 4.1 The overlap count satisfies \(Q\le2H\)

Let \(t=\log L\). Since \(\log2>1/2\),

$$
R<2t.
$$

Therefore

$$
Q
\le1+\log_2R
<1+2\log(2t)
<3+2\log t.
$$

For \(L\ge16\), \(\log(1+t)>1\) and \(\log t<\log(1+t)\), so

$$
Q<5\log(1+t)<2e\log(1+t)=2H.
\tag{30}
$$

Thus Lemma 2 may be used with gain

$$
G=Q.
$$

### 4.2 Dyadic thresholds

For \(0\le j<Q\), put

$$
h_j:=2^j,
\qquad
a_j:=C(h_j)-1.
\tag{31}
$$

For \(j\ge Q\), put

$$
a_j:=R.
\tag{32}
$$

Define the total threshold budget

$$
A:=\sum_{j\ge0}2^{-j}a_j.
\tag{33}
$$

If \(N_j(n)\le a_j\) for every \(j\), then \(D(n)\le A\). Consequently,

$$
X(n)\ge A+1
\quad\Longrightarrow\quad
N_j(n)\ge C(2^j)
\quad\text{for some }j<Q.
\tag{34}
$$

Lemma 2 with \(k=2^j\) and \(G=Q\) gives

$$
Q\,\#\{n\le L:N_j(n)\ge C(2^j)\}
\le
\#\{n\in J:N_j(n)\ge2^j\}.
\tag{35}
$$

But

$$
N_j(n)\ge2^j
\quad\Longrightarrow\quad
X(n)\ge2^{-j}N_j(n)\ge1.
\tag{36}
$$

There are only \(Q\) indices \(j<Q\). Thus

$$
\sum_{j<Q}\#\{n\in J:N_j(n)\ge2^j\}
\le
Q\,\#\{n\in J:X(n)\ge1\}.
\tag{37}
$$

Combining (34)–(37),

$$
\#\{n\le L:X(n)\ge A+1\}
\le
\#\{n\in J:X(n)\ge1\}.
\tag{38}
$$

It remains to bound \(A\).

### 4.3 Bounding the threshold budget

For \(h=2^j\), (6) gives

$$
a_j
\le
2h+16H+
\frac{16hL_0}{\sqrt{\log(2+h/H)}}.
$$

Hence

$$
\sum_{j<Q}2^{-j}a_j
\le
2Q+32H+16L_0S_Q,
\tag{39}
$$

where

$$
S_Q:=
\sum_{j<Q}
\frac1{\sqrt{\log(2+2^j/H)}}.
\tag{40}
$$

We claim

$$
S_Q\le7\sqrt H.
\tag{41}
$$

For the indices with \(2^j\le H\), there are at most
\(1+\log_2H\) terms. Since

$$
\frac1{\sqrt{\log2}}<\frac54,
\qquad
\log_2H\le\frac32\sqrt H,
$$

their contribution is at most

$$
\frac54\left(1+\frac32\sqrt H\right)
\le\frac{21}{8}\sqrt H.
\tag{42}
$$

Let \(j_0\) be the first index with \(2^{j_0}>H\). The \(j_0\)-term is less than \(1\). For \(t\ge1\),

$$
\log\left(2+\frac{2^{j_0+t}}H\right)>t\log2,
$$

so the remaining contribution is at most

$$
1+\frac54\sum_{t=1}^{Q}\frac1{\sqrt t}
\le
1+\frac52\sqrt Q
\le
\frac{21}{5}\sqrt H,
\tag{43}
$$

using \(Q\le2H\). Equations (42)–(43) yield (41).

Also

$$
L_0=\log(H+2)\le\sqrt H
\qquad(H>3).
\tag{44}
$$

Indeed, \(\sqrt H-\log(H+2)\) is increasing for \(H\ge3\), and at \(H=3\),

$$
\sqrt3>\frac53>\log5.
$$

Therefore

$$
16L_0S_Q\le112H.
\tag{45}
$$

The high-level tail satisfies

$$
\sum_{j\ge Q}2^{-j}R
=
\frac{2R}{2^Q}
\le2.
\tag{46}
$$

Using \(Q\le2H\), equations (39), (45), and (46) give

$$
A\le4H+32H+112H+2=148H+2.
\tag{47}
$$

Since \(H>3\),

$$
A+1\le149H.
\tag{48}
$$

Substitution into (38) proves

$$
\boxed{\;
\#\{n\le L:X(n)\ge149H\}
\le
\#\{n\in J:X(n)\ge1\}.
\;}
$$

As \(H=e\log(1+\log L)\), this is exactly
\((\mathrm{WSL}_{149})\). ∎

The elementary numerical facts used above can all be discharged by short rational bounds on the exponential series; for example

$$
\log2>\frac23,\qquad
\log\frac{11}{3}>\frac65,\qquad
\frac52<e<3,\qquad
\log5<\frac53.
$$

They imply in particular \(e\log(1+\log16)>3\).

---

## 5. From WSL to the fractional hinge inequality — **[PROVED]**

Assume first that the weights are rational,

$$
z_p=\frac{a_p}{N}.
$$

Use P3 with

$$
R_Q(i)=\sum_{q\in Q}\min(a_qv_q(i),N)
$$

and normalize by \(N\):

$$
\frac{R_Q(i)}N
=
\sum_{q\in Q}\min(z_qv_q(i),1).
$$

Fix \(m\ge16\), and set

$$
c_m:=1+149e\log(1+\log m).
\tag{49}
$$

Every quotient length occurring in P3 satisfies \(1\le L\le m\).

If \(L\ge16\), monotonicity gives

$$
c_m-1
=
149e\log(1+\log m)
\ge
149e\log(1+\log L),
$$

so \((\mathrm{WSL}_{149})\) gives the required P3 comparison.

If \(L<16\), then for \(i\le L\),

$$
\frac{R_Q(i)}N
\le\omega(i)<4,
$$

whereas \(c_m-1>149\cdot3\); hence the left side of WSL is empty.

Therefore P3 yields

$$
\sum_{k\le m}(S(k)-c_m)^+
\le
\sum_{b\in I}(S(b)-1)^+
\tag{50}
$$

for all rational weights.

Because the support is finite and only finitely many integers \(k\in K\cup I\) occur, both sides of (50) are continuous functions of the weights. Rational approximation extends (50) to all real \(z_p\in[0,1]\).

Finally apply P2:

$$
w=E+S,
\qquad
(w-1)^+=E+(S-1)^+,
\qquad
(w-c_m)^+\le E+(S-c_m)^+.
$$

Since \(\sum_I E\ge\sum_K E\),

$$
\begin{aligned}
\sum_{k\le m}(w(k)-c_m)^+
&\le
\sum_{k\le m}E(k)
+\sum_{k\le m}(S(k)-c_m)^+\\
&\le
\sum_{b\in I}E(b)
+\sum_{b\in I}(S(b)-1)^+\\
&=
\sum_{b\in I}(w(b)-1)^+.
\end{aligned}
\tag{51}
$$

This proves (1).

For \(2\le m\le15\), \(S(k)\le\omega(k)<4\), so P2 directly gives

$$
(\mathrm{TH}_4).
\tag{52}
$$

For \(m=1\), \((\mathrm{TH}_0)\) is immediate.

---

## 6. Explicit \(\log\log m\) constants — **[PROVED]**

Let \(m\ge16\), \(t=\log m\), and \(V=\log t=\log\log m\).

From \(\log2>2/3\),

$$
t\ge\log16>\frac83.
$$

Hence

$$
V>\log(8/3)>\frac34,
\qquad
\frac1t<\frac38<\frac V2.
$$

Therefore

$$
\log(1+\log m)
=
V+\log\left(1+\frac1t\right)
\le
V+\frac1t
<
\frac32V.
\tag{53}
$$

Moreover, since \(H>3\),

$$
1+149H<150H.
$$

Using \(e<3\) and (53),

$$
1+149e\log(1+\log m)
<
150e\log(1+\log m)
<
675\log\log m.
\tag{54}
$$

Increasing the hinge threshold only decreases its left side, proving

$$
(\mathrm{TH}_{675\log\log m})
\qquad(m\ge16).
$$

For an all-\(m\) formula, observe that for \(m\ge16\),

$$
1+149e\lambda(m)<450\lambda(m),
$$

while for \(2\le m\le15\), \(450\lambda(m)>4\). This proves (3).

---

## 7. Consequence for the Erdős–Surányi function — **[PROVED from the stated consequence]**

In the bounded regime \(a_n<8n^3\), the proved consequence in the brief gives

$$
g(n)\le(c+16)n.
$$

Using the sharper threshold (49),

$$
c+16
=
149e\log(1+\log a_n)+17
\le
149e\log(1+\log(8n^3))+17.
$$

In the complementary regime \(a_n\ge8n^3\), the given bound \(g(n)\le2n\) is smaller. Thus

$$
\boxed{\;
g(n)
\le
\Bigl(
149e\log(1+\log(8n^3))+17
\Bigr)n.
\;}
\tag{55}
$$

Since

$$
\log(1+\log(8n^3))
=
\log\log n+\log3+o(1),
$$

this gives

$$
\boxed{\;
g(n)\le149e\,n\log\log n+O(n)
=
O(n\log\log n).
\;}
\tag{56}
$$

Numerically, \(149e\approx405.024\).

---

## 8. Adversarial checks

### Dense-window structure — **[PASSED analytically]**

The arbitrary interval enters Lemma 2 only through the sharp worst-case inequalities

$$
\frac La-1\le N_J(a)\le\frac La+1.
$$

The \(k\)-fold term is used with its lower bound, while the \((k+1)\)-fold correction is used with its upper bound. Thus a Hensley–Richards-type interval cannot invalidate the argument by simultaneously suppressing the first moment and enlarging intersections: both effects are already paid for in (12)–(15).

### Many very light weights — **[PASSED analytically]**

A tiny weight \(u_q\) is not rounded to zero. At dyadic height \(2^{-j}\), it becomes the exact prime-power condition

$$
q^{\lceil2^{-j}/u_q\rceil}\mid n.
$$

There is one modulus per prime at each height, so pairwise coprimality is retained.

The potential overlap loss from summing over the \(Q\) dyadic heights is cancelled exactly by requesting gain \(G=Q\) in Lemma 2. The factorial term in \(\rho(k)\) is strong enough to buy this gain without changing the \(O(\log\log L)\) budget.

### Large valuations — **[PASSED exactly]**

Equation (26) is an equivalence, not an estimate. Prime squares, high powers, and saturation at \(1\) introduce no unaccounted error.

### Large prime powers or moduli — **[PASSED analytically]**

Moduli exceeding \(y=L^{1/(k+1)}\) are not assigned a harmonic-density estimate. Instead, pairwise coprimality implies that at most \(k\) of them can divide an integer \(n\le L\). This is the source of the additive \(2k\) in \(C(k)\).

---

## 9. Lean formalization requirements

A Lean formalization needs the following components:

1. The pointwise binomial inequality (4), using `Nat.choose`.
2. Finite elementary symmetric sums and

   $$
   (k+1)e_{k+1}\le H_0e_k,\qquad
   e_{k+r}\le e_kH_0^r/r!.
   $$
3. The interval multiple-count estimate

   $$
   L/a-1\le N_J(a)\le L/a+1.
   $$
4. Random thinning of a finite family. This can be represented either by a finite probability measure on subsets or by directly summing the Bernoulli weights
   \(\theta^{|E|}(1-\theta)^{s-|E|}\).
5. The scalar real-analysis inequality (20), the factorial estimate
   \(r!\ge(r/e)^r\), and the displayed rational numerical bounds.
6. The dyadic `tsum` in (27); convergence follows from \(N_j(n)\le R\) and the geometric series.
7. Continuity in finitely many weights for the rational-to-real limiting step.
8. The already-proved P2 and P3 transfer lemmas.

No SAT, LP, exhaustive enumeration, or unverified numerical approximation is part of the proof.

---

## Dependency list

$$
\boxed{
\begin{aligned}
(\mathrm{TH}_{450\log(1+\log m)})
&\longleftarrow
(S_{\,1+149e\log(1+\log m)})\\
&\longleftarrow
\text{P3}+\mathrm{WSL}_{149}\\
&\longleftarrow
\text{dyadic prime-power encoding}
+\text{gain-}G\text{ sieve}\\
&\longleftarrow
\text{two-term Bonferroni}
+\text{elementary symmetric bounds}\\
&\qquad
+\text{interval }\pm1\text{ counts}
+\text{P1(a) harmonic bound}.
\end{aligned}}
$$

**Unproved items:** none, relative to P1(a), P2, and P3 supplied in the brief.

**Final status:** **T1 PROVED.** T4 is superseded; T2 and T3 are not needed.
