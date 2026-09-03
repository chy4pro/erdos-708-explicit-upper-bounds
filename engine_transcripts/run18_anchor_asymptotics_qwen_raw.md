## 0. Finite-support convention (matching the displayed \(r=2\) formula)

As written, the coefficients \(c_d\) with one outside prime \(q\notin R\) are infinitely many, so the negative part of the value would diverge unless a finite truncation is specified. The displayed formula for \(r=2\),

\[
V_2(m)=\Big\lfloor\frac m6\Big\rfloor+
\sum_{5\le q\le m/2}
\left(
\Big\lfloor\frac{m}{2q}\Big\rfloor+
\Big\lfloor\frac{m}{3q}\Big\rfloor-
\Big\lfloor\frac{m}{6q}\Big\rfloor-1
\right),
\]

shows the intended truncation: for each outside prime \(q\), include the whole \(q\)-family exactly when \(q\,p_1\le m\), where \(p_1=\min R\). I use this convention throughout. Any other fixed proportional cutoff changes the value by \(O(m/\log m)\), hence does not change the constant \(\kappa_r\).

All logarithms are natural. Let \(M\) denote the Meissel–Mertens constant

\[
M=\lim_{x\to\infty}\left(\sum_{p\le x}\frac1p-\log\log x\right)
=0.261497212847\ldots .
\]

---

## 1. Explicit auxiliary estimates

### Lemma 1.1 — Explicit prime sum / prime counting bounds — **PROVED**

For \(x\ge 285\),

\[
\left|\sum_{p\le x}\frac1p-\log\log x-M\right|\le \frac{4}{\log x}.
\tag{1.1}
\]

For \(x\ge 17\),

\[
\frac{x}{2\log x}\le \pi(x)\le \frac{2x}{\log x}.
\tag{1.2}
\]

Also, for \(y\ge 2\),

\[
\prod_{p\le y}\left(1-\frac1p\right)\ge \frac{1}{4\log y}.
\tag{1.3}
\]

These are standard explicit forms of Mertens’ theorem and Rosser–Schoenfeld prime bounds. The constant \(4\) in (1.1) is not optimal; it is convenient and explicit.

---

### Lemma 1.2 — Turán–Kubilius for \(\omega\) — **PROVED**

For \(x\ge e^e\), writing \(L_x=\log\log x\),

\[
\sum_{n\le x}\bigl(\omega(n)-L_x\bigr)^2
\le 20xL_x.
\tag{1.4}
\]

This is Turán’s inequality for the strongly additive function \(\omega\). The constant \(20\) is again not optimal but explicit and sufficient.

---

## 2. Exact identity for the finite certificate value

Let \(R=\{a_1<\dots<a_r\}\) be any fixed finite set of primes. For \(A\subseteq R\), write

\[
D_A=\prod_{a\in A}a,\qquad D_\varnothing=1.
\]

Let

\[
\Pi_R=\prod_{a\in R}\left(1-\frac1a\right),
\qquad
\alpha_R=1-\Pi_R,
\qquad
S_R=\sum_{a\in R}\frac1a.
\]

Let

\[
E_r=\#\{\varnothing\ne A\subseteq R: |A|\text{ even}\}=2^{r-1}-1,
\]

and

\[
O_r=\#\{A\subseteq R: |A|\ge 3,\ |A|\text{ odd}\}=2^{r-1}-r
\]

(with the convention \(O_1=0\)). Let

\[
Q_R(m)=\{q\text{ prime}:q\notin R,\ q\le m/a_1\}.
\]

The finite certificate value is

\[
\begin{aligned}
V_R(m)
&=
\sum_{\substack{A\subseteq R\\ |A|\ge2}}
\left((-1)^{|A|}\left\lfloor\frac{m}{D_A}\right\rfloor
-\mathbf 1_{\{|A|\text{ odd}\}}\right)
\\
&\quad+
\sum_{q\in Q_R(m)}
\left(
\sum_{\varnothing\ne A\subseteq R}
(-1)^{|A|+1}
\left\lfloor\frac{m}{qD_A}\right\rfloor
-E_r
\right).
\end{aligned}
\tag{2.1}
\]

For \(r=2\), \(R=\{2,3\}\), this is exactly the given formula.

---

### Lemma 2.1 — Exact deficit identity — **PROVED**

Define

\[
W_1(m)=\sum_{n\le m}(\omega(n)-1)^+,
\]

and the \(R\)-rough excess

\[
G_R(m)=
\sum_{\substack{n\le m\\ (n,D_R)=1}}(\omega(n)-1)^+,
\qquad
D_R=\prod_{a\in R}a.
\]

Then

\[
\boxed{
V_R(m)=W_1(m)-G_R(m)-O_r-E_r\,\pi(Q_R(m)),
}
\tag{2.2}
\]

where \(\pi(Q_R(m))=\#Q_R(m)\).

#### Proof

For \(y\ge 0\), define

\[
U_R(y)=
\sum_{\varnothing\ne A\subseteq R}
(-1)^{|A|+1}\left\lfloor\frac{y}{D_A}\right\rfloor.
\]

By inclusion–exclusion, \(U_R(y)\) is exactly the number of integers \(1\le n\le y\) divisible by at least one prime in \(R\).

Now consider first the “anchor-only” part

\[
T_0(m)=
\sum_{\substack{A\subseteq R\\ |A|\ge2}}
(-1)^{|A|}\left\lfloor\frac m{D_A}\right\rfloor.
\]

For a fixed \(n\), let \(a(n)=\#\{a\in R:a\mid n\}\). The contribution of \(n\) to \(T_0(m)\) is

\[
\sum_{\substack{A\subseteq R\cap\{p:p\mid n\}\\ |A|\ge2}}(-1)^{|A|}
=
(a(n)-1)^+,
\]

because \(\sum_{k=2}^{s}\binom sk(-1)^k=s-1\) for \(s\ge1\), and is \(0\) for \(s=0\). Hence

\[
T_0(m)=\sum_{n\le m}(a(n)-1)^+.
\tag{2.3}
\]

For \(q\notin R\), the quantity \(U_R(\lfloor m/q\rfloor)\) counts integers \(n\le m\) divisible by \(q\) and by at least one anchor \(a\in R\). Summing over \(q\in Q_R(m)\) counts, for each \(n\) divisible by at least one anchor, the number of non-anchor prime divisors of \(n\). Indeed, if \(q\mid n\) and some anchor \(a\mid n\), then \(n\ge a_1q\), so \(q\le m/a_1\); hence every such \(q\) is included.

Therefore, writing \(A_0(n)=R\cap\{p:p\mid n\}\) and \(Q_0(n)\) for the other prime divisors of \(n\),

\[
T_0(m)+\sum_{q\in Q_R(m)}U_R(\lfloor m/q\rfloor)
=
\sum_{\substack{n\le m\\ A_0(n)\ne\varnothing}}
\bigl(|A_0(n)|-1+|Q_0(n)|\bigr).
\]

But if \(A_0(n)\ne\varnothing\), then \(|A_0(n)|+|Q_0(n)|=\omega(n)\), so this equals

\[
\sum_{\substack{n\le m\\ A_0(n)\ne\varnothing}}(\omega(n)-1).
\]

Splitting \(W_1(m)\) into numbers with and without an \(R\)-anchor gives

\[
W_1(m)=
\sum_{\substack{n\le m\\ A_0(n)\ne\varnothing}}(\omega(n)-1)
+
G_R(m).
\]

Thus

\[
T_0(m)+\sum_{q\in Q_R(m)}U_R(\lfloor m/q\rfloor)
=
W_1(m)-G_R(m).
\tag{2.4}
\]

Finally, comparing (2.1) with (2.4), the value \(V_R(m)\) subtracts one extra unit for every negative anchor-only coefficient (these are the odd subsets of size at least \(3\), giving \(O_r\)), and one extra unit for every negative \(q\)-family coefficient (the nonempty even subsets, giving \(E_r\) for each \(q\in Q_R(m)\)). Hence (2.2). ∎

---

## 3. T1 — asymptotic for fixed \(r\)

### Lemma 3.1 — Rough excess asymptotic — **PROVED**

For fixed finite \(R\),

\[
G_R(m)
=
\Pi_R\,m\bigl(\log\log m+M-S_R-1\bigr)
+
O_R\!\left(\frac{m}{\log m}\right),
\tag{3.1}
\]

with an explicit bound

\[
\left|
G_R(m)-\Pi_R m(\log\log m+M-S_R-1)
\right|
\le
(4+3\cdot 2^r)\frac{m}{\log m}
\tag{3.2}
\]

for all sufficiently large \(m\) (e.g. \(m\ge \max(285,\max R)\)).

#### Proof

Let

\[
\Phi(x,R)=\#\{n\le x:(n,D_R)=1\}.
\]

By inclusion–exclusion,

\[
\Phi(x,R)=
\sum_{A\subseteq R}(-1)^{|A|}\left\lfloor\frac{x}{D_A}\right\rfloor
=
x\Pi_R+O(2^r),
\tag{3.3}
\]

where the implied constant is at most \(2^r\) in absolute value.

The sum of \(\omega(n)\) over \(R\)-rough \(n\le m\) is

\[
\sum_{\substack{n\le m\\ (n,D_R)=1}}\omega(n)
=
\sum_{\substack{p\le m\\ p\notin R}}
\Phi(m/p,R).
\]

Using (3.3),

\[
\sum_{\substack{n\le m\\ (n,D_R)=1}}\omega(n)
=
m\Pi_R
\sum_{\substack{p\le m\\ p\notin R}}\frac1p
+
O(2^r\pi(m)).
\tag{3.4}
\]

By Lemma 1.1,

\[
\sum_{\substack{p\le m\\ p\notin R}}\frac1p
=
\log\log m+M-S_R+O(1/\log m),
\]

and \(\pi(m)\le 2m/\log m\) for large \(m\). Hence

\[
\sum_{\substack{n\le m\\ (n,D_R)=1}}\omega(n)
=
m\Pi_R(\log\log m+M-S_R)
+
O(2^r m/\log m)
+
O(m/\log m).
\tag{3.5}
\]

Also, by (3.3),

\[
\#\{n\le m:(n,D_R)=1\}
=
m\Pi_R+O(2^r).
\tag{3.6}
\]

For an \(R\)-rough integer \(n\),

\[
(\omega(n)-1)^+=\omega(n)-1
\]

except at \(n=1\), where the left side is \(0\) and the right side is \(-1\). Therefore

\[
G_R(m)=
\sum_{\substack{n\le m\\ (n,D_R)=1}}\omega(n)
-
\#\{n\le m:(n,D_R)=1\}
+1.
\]

Insert (3.5) and (3.6), and absorb \(O(2^r)\) into \(O(2^r m/\log m)\). This gives (3.1) with the explicit error (3.2). ∎

---

### Lemma 3.2 — \(W_1\) asymptotic — **PROVED**

For \(m\ge 285\),

\[
W_1(m)=m\log\log m+(M-1)m+O\left(\frac{m}{\log m}\right),
\tag{3.7}
\]

with the explicit bound

\[
\left|W_1(m)-m\log\log m-(M-1)m\right|
\le
7\frac{m}{\log m}.
\tag{3.8}
\]

#### Proof

For \(n=1\), \((\omega(n)-1)^+=0\), while \(\omega(n)-1=-1\). For \(n\ge2\), \((\omega(n)-1)^+=\omega(n)-1\). Thus

\[
W_1(m)=\sum_{n\le m}\omega(n)-m+1.
\tag{3.9}
\]

Now

\[
\sum_{n\le m}\omega(n)
=
\sum_{p\le m}\left\lfloor\frac mp\right\rfloor
=
m\sum_{p\le m}\frac1p+O(\pi(m)).
\]

Using Lemma 1.1 gives

\[
\sum_{n\le m}\omega(n)
=
m(\log\log m+M)+O\left(\frac{m}{\log m}\right).
\]

The explicit bound follows from \(4m/\log m\) for the reciprocal sum and \(2m/\log m\) for \(\pi(m)\), plus the harmless \(+1\). ∎

---

### Theorem T1 — asymptotic value of the \(r\)-anchor certificate — **PROVED**

Let \(R=\{p_1<\dots<p_r\}\) be fixed. Define

\[
\Pi_R=\prod_{i=1}^r\left(1-\frac1{p_i}\right),
\qquad
\alpha_R=1-\Pi_R,
\qquad
S_R=\sum_{i=1}^r\frac1{p_i}.
\]

Then, as \(m\to\infty\),

\[
\boxed{
V_R(m)=
\alpha_R\,m\log\log m+\kappa_R m
+
O_R\!\left(\frac{m}{\log m}\right),
}
\tag{3.10}
\]

where

\[
\boxed{
\kappa_R
=
(M-1)-\Pi_R(M-S_R-1)
=
\alpha_R M+\Pi_R(1+S_R)-1.
}
\tag{3.11}
\]

Equivalently, in subset-sum notation,

\[
\boxed{
\kappa_R
=
\alpha_R(M-S_R)
+
\sum_{\substack{A\subseteq R\\ |A|\ge2}}
\frac{(-1)^{|A|}}{D_A}.
}
\tag{3.12}
\]

An explicit error bound is: for all sufficiently large \(m\),

\[
\boxed{
\left|
V_R(m)-\alpha_R m\log\log m-\kappa_R m
\right|
\le
(11+5\cdot 2^r)\frac{m}{\log m}.
}
\tag{3.13}
\]

The constant is not optimized; it is fully explicit.

#### Proof

From Lemma 2.1,

\[
V_R(m)=W_1(m)-G_R(m)-O_r-E_r\pi(Q_R(m)).
\]

Lemma 3.2 gives

\[
W_1(m)=m\log\log m+(M-1)m+O(m/\log m).
\]

Lemma 3.1 gives

\[
G_R(m)=
\Pi_R m(\log\log m+M-S_R-1)
+
O(2^r m/\log m).
\]

Also \(O_r\le 2^r\) and

\[
E_r\pi(Q_R(m))
\le
2^{r-1}\pi(m)
\le
2^{r-1}\cdot\frac{2m}{\log m}
=
2^r\frac{m}{\log m}.
\]

Combining,

\[
\begin{aligned}
V_R(m)
&=
m\log\log m+(M-1)m
\\
&\quad-
\Pi_R m(\log\log m+M-S_R-1)
+
O(2^r m/\log m)
\\
&=
(1-\Pi_R)m\log\log m
+
\bigl[(M-1)-\Pi_R(M-S_R-1)\bigr]m
+
O(2^r m/\log m).
\end{aligned}
\]

This gives (3.10)–(3.11). The explicit constant (3.13) follows by adding the explicit constants from Lemma 3.2, Lemma 3.1, \(O_r\), and \(E_r\pi(Q_R(m))\). ∎

---

### Check for \(r=2\)

For \(R=\{2,3\}\),

\[
\Pi_R=\frac13,\qquad
\alpha_R=\frac23,\qquad
S_R=\frac12+\frac13=\frac56.
\]

Then

\[
\kappa_R
=
\frac23M+\frac13\left(1+\frac56\right)-1
=
\frac23M+\frac{11}{18}-1
=
\frac23M-\frac7{18}.
\]

Thus

\[
V_2(m)=\frac23m\log\log m+
\left(\frac23M-\frac7{18}\right)m
+
O\left(\frac{m}{\log m}\right).
\]

Since

\[
W_2(m)=m\log\log m+(M-2)m+o(m),
\]

we get

\[
V_2(m)-W_2(m)
=
-\frac13m\log\log m+
\left(\frac{29}{18}-\frac M3\right)m
+
o(m),
\]

exactly matching the stated known formula.

---

## 4. Asymptotic of \(W_c(m)\)

### Lemma 4.1 — \(W_c\) asymptotic — **PROVED**

Fix \(c\in\mathbb R\). Let \(L=\log\log m\). For all sufficiently large \(m\),

\[
\boxed{
W_c(m)=m\log\log m+(M-c)m+\rho_c(m),
}
\tag{4.1}
\]

where, for \(c\le0\),

\[
|\rho_c(m)|\le 6\frac{m}{\log m},
\tag{4.2}
\]

and for \(c>0\), provided \(L\ge 2c+4\),

\[
|\rho_c(m)|
\le
6\frac{m}{\log m}
+
80(c+1)\frac{m}{\log\log m}.
\tag{4.3}
\]

In particular,

\[
W_c(m)=m\log\log m+(M-c)m+o(m).
\]

#### Proof

Write

\[
(\omega-c)^+=(\omega-c)+(c-\omega)\mathbf 1_{\{\omega<c\}}.
\]

If \(c\le0\), then \(\omega<c\) never happens, so

\[
W_c(m)=\sum_{n\le m}\omega(n)-cm.
\]

The estimate follows from the proof of Lemma 3.2.

Assume \(c>0\). The main term is again

\[
\sum_{n\le m}\omega(n)-cm
=
m\log\log m+(M-c)m+O(m/\log m).
\]

It remains to bound

\[
\sum_{\omega(n)<c}(c-\omega(n)).
\]

Let

\[
N_c(m)=\#\{n\le m:\omega(n)<c\}.
\]

By Lemma 1.2, for \(L=\log\log m\),

\[
\sum_{n\le m}(\omega(n)-L)^2\le 20mL.
\]

If \(L\ge 2c+4\), then for \(\omega(n)<c\),

\[
|\omega(n)-L|\ge L-c\ge L/2.
\]

Thus

\[
N_c(m)
\le
\frac{4}{L^2}\sum_{n\le m}(\omega(n)-L)^2
\le
\frac{80m}{L}.
\]

Since \(0\le c-\omega(n)\le c+1\) on this set, the correction is at most

\[
80(c+1)\frac{m}{L}.
\]

This proves (4.3). ∎

---

## 5. T2 — fixed \(r\), critical constant, and finite range

For fixed \(R\) of size \(r\), put

\[
\beta_R=\Pi_R=\prod_{a\in R}\left(1-\frac1a\right),
\qquad
\alpha_R=1-\beta_R.
\]

Also define

\[
\lambda_R:=M-\kappa_R.
\]

Using (3.11),

\[
\boxed{
\lambda_R
=
1+\beta_R(M-1-S_R).
}
\tag{5.1}
\]

From Theorem T1 and Lemma 4.1,

\[
\begin{aligned}
V_R(m)-W_c(m)
&=
\alpha_R m\log\log m+\kappa_R m
-
\bigl(m\log\log m+(M-c)m\bigr)
+
o(m)
\\
&=
-\beta_R m\log\log m+(c-\lambda_R)m+o(m).
\end{aligned}
\tag{5.2}
\]

More explicitly, for fixed \(r,c\),

\[
\boxed{
\frac{V_R(m)-W_c(m)}{m}
=
-\beta_R\log\log m+c-\lambda_R
+
O_r\left(\frac1{\log m}\right)
+
O_c\left(\frac1{\log\log m}\right).
}
\tag{5.3}
\]

One may take

\[
O_r(1/\log m)+O_c(1/\log\log m)
\le
\frac{11+5\cdot2^r}{\log m}
+
\frac{6+80(\max(c,0)+1)}{\log\log m}
\]

for large \(m\).

---

### 5.1 Critical constant

For fixed \(m,r\), the function \(c\mapsto W_c(m)\) is nonincreasing. Therefore if \(W_c(m)\le V_R(m)\) holds for some \(c\), it holds for every larger \(c\). Hence there is no finite “largest” \(c\) in the literal sense; the meaningful sharp quantity is the smallest admissible \(c\). Define

\[
c_{R,*}(m):=\inf\{c: W_c(m)\le V_R(m)\}.
\]

From (5.3),

\[
\boxed{
c_{R,*}(m)=\beta_R\log\log m+\lambda_R+o(1).
}
\tag{5.4}
\]

Thus for fixed \(r\), the required \(c\) grows like \(\beta_R\log\log m\). Since \(\beta_R>0\) for every fixed finite \(R\), no fixed finite \(c\) works for all large \(m\).

---

### 5.2 Range of validity for fixed \(c\)

Assume \(c\) is fixed.

If \(c\le\lambda_R\), then (5.3) gives

\[
V_R(m)-W_c(m)<0
\]

for all sufficiently large \(m\). Thus the certificate can only work, at best, on a bounded initial interval.

If \(c>\lambda_R\), then (5.3) implies that the inequality \(V_R(m)\ge W_c(m)\) can hold only when

\[
\boxed{
\log\log m
\le
\frac{c-\lambda_R}{\beta_R}
+
o(1).
}
\tag{5.5}
\]

Equivalently,

\[
\boxed{
m
\le
\exp\left(
\exp\left(
\frac{c-\lambda_R}{\beta_R}+o(1)
\right)
\right).
}
\tag{5.6}
\]

This is the asymptotic range forced by the main terms.

---

### 5.3 Example: \(r=2\), \(c=2\)

For \(R=\{2,3\}\),

\[
\beta_R=\frac13,
\qquad
S_R=\frac56,
\]

and

\[
\lambda_R
=
1+\frac13\left(M-1-\frac56\right)
=
1+\frac13\left(M-\frac{11}{6}\right)
=
\frac{7}{18}+\frac M3.
\]

Numerically,

\[
\lambda_R\approx 0.388888+0.087166=0.476054.
\]

For \(c=2\),

\[
\frac{c-\lambda_R}{\beta_R}
=
3\left(2-\frac{7}{18}-\frac M3\right)
=
\frac{29}{6}-M
\approx 4.571836.
\]

Thus the asymptotic range is

\[
\log\log m\lesssim 4.571836,
\]

so

\[
m\lesssim \exp(\exp(4.571836)).
\]

Now

\[
\exp(4.571836)\approx 96.72,
\]

and

\[
\log_{10}m\approx \frac{96.72}{\log 10}\approx 42.0.
\]

Thus the asymptotic predicts failure beyond roughly

\[
\boxed{m\approx 10^{42}},
\]

matching the known finite computation.

---

### 5.4 Fixed anchors cannot give an absolute constant

From (5.4), for every fixed finite \(R\),

\[
c_{R,*}(m)=\beta_R\log\log m+\lambda_R+o(1)\to\infty.
\]

Therefore:

\[
\boxed{
\text{For every fixed }r\text{ and every fixed }c,\ 
W_c(m)\le V_r(m)\text{ fails for all sufficiently large }m.
}
\]

This is **PROVED**.

---

## 6. Growing anchors: why \(r=r(m)\) cannot save a fixed \(c\)

We now show that for the full subset certificate, no function \(r(m)\) can keep

\[
V_{r(m)}(m)\ge W_c(m)
\]

for all large \(m\), for any fixed \(c\). The obstruction is exactly the exponential number of subset terms.

Let \(R_r\) be the first \(r\) primes. Recall the exact identity

\[
V_r(m)=W_1(m)-G_r(m)-O_r-E_r\pi(Q_r(m)),
\tag{6.1}
\]

where \(G_r(m)\) is the excess over primes not divisible by any of the first \(r\) primes, \(O_r=2^{r-1}-r\), and \(E_r=2^{r-1}-1\).

Since the left-hand deficits are nonnegative, if \(V_r(m)\ge W_c(m)\), then

\[
G_r(m)+O_r+E_r\pi(Q_r(m))
\le
W_1(m)-W_c(m).
\tag{6.2}
\]

For fixed \(c\),

\[
W_1(m)-W_c(m)=
\begin{cases}
(c-1)m+o(m), & c>1,\\
o(m), & c=1,\\
-(1-c)m+o(m), & c<1.
\end{cases}
\tag{6.3}
\]

If \(c<1\), the right side is eventually negative, while the left side is nonnegative. Hence no \(r(m)\) works for \(c<1\).

Assume henceforth \(c\ge1\). Then the right side of (6.2) is \(O(m)\). Thus we must have

\[
G_r(m)+O_r+E_r\pi(Q_r(m))=O(m).
\tag{6.4}
\]

We show this is impossible.

---

### Step 1: the negative subset penalties force \(2^r=O(\log m)\)

Suppose first that

\[
r>\frac12\pi(m/2).
\]

By Lemma 1.1, \(\pi(m/2)\ge m/(4\log m)\) for large \(m\). Hence

\[
r\gg \frac{m}{\log m}.
\]

Then

\[
O_r=2^{r-1}-r
\]

is exponentially larger than \(m\), contradicting (6.4). Therefore any admissible \(r\) must satisfy

\[
r\le \frac12\pi(m/2)
\]

for all large \(m\). Then at least half of the primes \(\le m/2\) are outside \(R_r\), so

\[
\pi(Q_r(m))\ge \frac12\pi(m/2)
\gg \frac{m}{\log m}.
\]

Using \(E_r\pi(Q_r(m))=O(m)\), we obtain

\[
E_r=O(\log m).
\]

Since \(E_r=2^{r-1}-1\),

\[
\boxed{
2^r=O(\log m).
}
\tag{6.5}
\]

Equivalently,

\[
r\le \log_2\log m+O(1).
\tag{6.6}
\]

This is already much too small to make the rough density negligible.

---

### Step 2: with \(2^r=O(\log m)\), the rough excess is still too large

From Lemma 3.1, uniformly in the present regime,

\[
G_r(m)=
\Pi_r m(\log\log m+M-S_r-1)
+
O\left(2^r\frac{m}{\log m}\right).
\tag{6.7}
\]

By (6.5), the error term is \(O(m)\).

Now \(r\le \log_2\log m+O(1)\). By Rosser’s bound \(p_r\ll r\log r\), we have

\[
\log p_r\le \log\log\log m+O(1).
\]

Using Lemma 1.1,

\[
S_r=\sum_{i=1}^r\frac1{p_i}
\le
\log\log p_r+O(1)
\le
\log\log\log m+O(1).
\tag{6.8}
\]

Also, by the product lower bound (1.3),

\[
\Pi_r=
\prod_{i=1}^r\left(1-\frac1{p_i}\right)
\ge
\frac{1}{4\log p_r}
\ge
\frac{c_0}{\log\log\log m}
\tag{6.9}
\]

for some absolute explicit \(c_0>0\) (e.g. \(c_0=1/8\) for large \(m\)).

Therefore

\[
\begin{aligned}
G_r(m)
&\ge
m\cdot
\frac{c_0}{\log\log\log m}
\left(
\log\log m-\log\log\log m-O(1)
\right)
-
O(m)
\\
&=
m\cdot
\frac{c_0\log\log m}{\log\log\log m}
\,(1-o(1)).
\end{aligned}
\tag{6.10}
\]

This tends to infinity times \(m\). In particular,

\[
G_r(m)\gg m,
\]

contradicting (6.4).

Thus no choice of \(r=r(m)\) can satisfy \(V_r(m)\ge W_c(m)\) for all large \(m\), for any fixed \(c\).

We have proved:

\[
\boxed{
\text{For the full }2^r\text{-subset certificate, no }r(m)
\text{ keeps }V_{r(m)}(m)\ge W_c(m)
\text{ for fixed }c.
}
\]

The reason is explicit: making \(r\) large enough to reduce the rough density forces \(2^r\) subset penalties to be far too large.

---

## 7. T3 — arbitrary prime set \(P\subseteq[2,m]\)

Now let \(P\subseteq\{ \text{primes}\le m\}\) be arbitrary, and let \(R\) be the \(r\) smallest primes of \(P\). Write

\[
a_1=\min R,\qquad x=\frac{m}{a_1}.
\]

Define

\[
H_P(m)=\sum_{\substack{p\in P\\ p\le m}}\frac1p.
\]

Only outside primes \(q\in P\setminus R\) with \(q\le x\) can appear in a nontrivial \(q\)-family, because if \(q>x=m/a_1\), then \(qa_1>m\) and all floors in that family vanish.

Let

\[
H_{P\setminus R}^{\mathrm{elig}}(m)
=
\sum_{\substack{q\in P\setminus R\\ q\le m/a_1}}\frac1q.
\]

The same inclusion–exclusion argument gives the following uniform estimate.

---

### Theorem T3 — arbitrary \(P\) — **PROVED**

For fixed \(r\), fixed anchor set \(R\) (the \(r\) smallest elements of \(P\)), and arbitrary \(P\subseteq[2,m]\),

\[
\boxed{
V_R^P(m)
=
\alpha_R\,m\,
H_{P\setminus R}^{\mathrm{elig}}(m)
+
mB_R
+
O\left(2^r\frac{m}{\log m}\right),
}
\tag{7.1}
\]

where

\[
\alpha_R=1-\prod_{a\in R}\left(1-\frac1a\right),
\]

and

\[
B_R=
\sum_{\substack{A\subseteq R\\ |A|\ge2}}
\frac{(-1)^{|A|}}{D_A}
=
\Pi_R-1+S_R.
\tag{7.2}
\]

Equivalently,

\[
B_R-\alpha_R S_R
=
\Pi_R(1+S_R)-1.
\tag{7.3}
\]

Thus, if \(m/a_1\) is large enough that the tail of primes in \(P\) beyond \(m/a_1\) is negligible, one may write

\[
\boxed{
V_R^P(m)
=
\alpha_R\,m\,H_P(m)
+
m\bigl(\Pi_R(1+S_R)-1\bigr)
+
O\left(2^r\frac{m}{\log m}\right)
-
\alpha_R m\,T_P(m),
}
\tag{7.4}
\]

where the explicit tail is

\[
T_P(m)
=
\sum_{\substack{p\in P\\ p>m/a_1}}\frac1p
+
\sum_{\substack{a\in R\\ a>m/a_1}}\frac1a.
\tag{7.5}
\]

In the important case where \(a_1\) is fixed (or more generally \(T_P(m)=o(1)\)), the main term is simply

\[
\boxed{
\alpha_R\,m\sum_{p\in P}\frac1p.
}
\tag{7.6}
\]

When \(P\) is the set of all primes \(\le m\), \(H_P(m)=\log\log m+M+O(1/\log m)\), and (7.4) reduces to Theorem T1.

#### Proof sketch

For \(q\in P\setminus R\), \(q\le m/a_1\), the \(q\)-family floor sum is

\[
U_R(\lfloor m/q\rfloor)
=
\alpha_R\frac{m}{q}+O(2^r),
\]

by inclusion–exclusion. Summing over eligible \(q\) gives

\[
\alpha_R m H_{P\setminus R}^{\mathrm{elig}}(m)
+
O(2^r\#P).
\]

Since \(\#P\le\pi(m)\le 2m/\log m\), the error is \(O(2^r m/\log m)\). The anchor-only part contributes \(mB_R+O(2^r)\), and the negative corrections contribute at most \(E_r\#P=O(2^r m/\log m)\). This proves (7.1). The reformulation (7.4) follows by adding and subtracting the ineligible primes and anchors. ∎

---

## 8. Summary of main constants

For fixed \(R=\{p_1,\dots,p_r\}\), define

\[
\Pi_R=\prod_{i=1}^r\left(1-\frac1{p_i}\right),
\qquad
\alpha_R=1-\Pi_R,
\qquad
S_R=\sum_{i=1}^r\frac1{p_i}.
\]

Then

\[
\boxed{
V_R(m)=
\alpha_R m\log\log m+\kappa_R m+O_R\left(\frac{m}{\log m}\right),
}
\]

with

\[
\boxed{
\kappa_R=
\alpha_R M+\Pi_R(1+S_R)-1.
}
\]

Also

\[
\boxed{
W_c(m)=m\log\log m+(M-c)m+o(m).
}
\]

Therefore

\[
\boxed{
V_R(m)-W_c(m)=
-\Pi_R m\log\log m+(c-\lambda_R)m+o(m),
}
\]

where

\[
\boxed{
\lambda_R=M-\kappa_R=1+\Pi_R(M-1-S_R).
}
\]

The asymptotic critical constant is

\[
\boxed{
c_{R,*}(m)=\Pi_R\log\log m+\lambda_R+o(1).
}
\]

For fixed \(r\), \(\Pi_R>0\), so \(c_{R,*}(m)\to\infty\). Hence fixed anchors cannot prove an absolute constant \(c\).

If one tries to let \(r=r(m)\to\infty\), the full subset certificate still fails for every fixed \(c\): making \(\Pi_R\) small enough forces \(r\) so large that the negative subset penalties of size \(2^r\) overwhelm the main term. This completes the requested derivation.