# Answer — T1 is proved with an explicit constant slightly above 20

I prove the requested two-layer interval sieve lemma (TL) with

\[
t(L)=5+\max\Bigl(6,\Bigl\lceil 23\ln\Bigl(1+\frac{\ln L}{6}\Bigr)\Bigr\rceil\Bigr),
\qquad
L_0=17^6=24\,137\,569 .
\]

Thus \(t(L)=23\ln\ln L+O(1)\). The constant \(23\) is explicit and is safely larger than the threshold constant \(20\) mentioned in T3. I also give the immediate weighted corollaries needed for weights \(1/2\), and a precise partial weighted lower bound. I do **not** claim a T3 counterexample; its status is stated at the end.

---

## 0. Notation and allowed inputs

All logarithms are natural. For a finite prime set \(Q\),

\[
\omega_Q(n):=\#\{q\in Q:q\mid n\}.
\]

For a finite set of primes \(S\), write

\[
H(S):=\sum_{q\in S}\frac1q,
\qquad
e_2(S):=\sum_{\{q,r\}\subset S}\frac1{qr},
\qquad
e_3(S):=\sum_{\{q,r,u\}\subset S}\frac1{qru}.
\]

For an interval \(J\) of \(L\) consecutive integers and integer \(d\ge1\), let \(N_J(d)\) be the number of multiples of \(d\) in \(J\). We use freely the given interval estimate

\[
\frac Ld-1 < N_J(d) < \frac Ld+1 .
\tag{0.1}
\]

In particular we may use the non-strict inequalities

\[
N_J(d)\ge \frac Ld-1,
\qquad
N_J(d)\le \frac Ld+1 .
\tag{0.2}
\]

For the initial interval \([1,L]\),

\[
N_{[1,L]}(d)=\left\lfloor \frac Ld\right\rfloor\le \frac Ld .
\tag{0.3}
\]

We also use the given Mertens-type bound, valid for \(y\ge2\):

\[
\sum_{p\le y}\frac1p\le e\ln(1+\ln y).
\tag{0.4}
\]

Status: PROVED (given in the problem statement).

---

## 1. Upper bound for high \(\omega_R\) on \([1,L]\)

### Lemma 1 — binomial moment upper bound with an \(e_2\) factor

**Status: PROVED.**

Let \(R\) be a finite set of primes, all \(\le y\), and let \(s\ge2\). Put

\[
H=H(R)=\sum_{q\in R}\frac1q,
\qquad
E_2=e_2(R)=\sum_{\{q,r\}\subset R}\frac1{qr}.
\]

Then

\[
\#\{n\le L:\omega_R(n)\ge s\}
\le
L\cdot \frac{2E_2H^{s-2}}{s!}.
\tag{1.1}
\]

In particular, since \(E_2\le H^2/2\),

\[
\#\{n\le L:\omega_R(n)\ge s\}
\le
L\frac{H^s}{s!}.
\tag{1.2}
\]

#### Proof

For each \(n\le L\), put \(k=\omega_R(n)\). If \(k\ge s\), then \(1\le \binom{k}{s}\). Hence

\[
\#\{n\le L:\omega_R(n)\ge s\}
\le
\sum_{n\le L}\binom{\omega_R(n)}{s}.
\]

Expanding the binomial coefficient over \(s\)-subsets of \(R\),

\[
\sum_{n\le L}\binom{\omega_R(n)}{s}
=
\sum_{\substack{S\subset R\\ |S|=s}}
N_{[1,L]}\!\left(\prod_{q\in S}q\right).
\]

Using (0.3),

\[
\le
L
\sum_{\substack{S\subset R\\ |S|=s}}
\prod_{q\in S}\frac1q
=
L e_s(R),
\]

where \(e_s(R)\) is the \(s\)-th elementary symmetric sum of the numbers \(x_q=1/q\).

Now for \(s\ge2\),

\[
\binom{s}{2}e_s(R)
=
\sum_{\{q,r\}\subset R}
\frac1{qr}
\sum_{\substack{T\subset R\setminus\{q,r\}\\ |T|=s-2}}
\prod_{u\in T}\frac1u.
\]

The inner sum is at most

\[
\frac{H^{s-2}}{(s-2)!}.
\]

Therefore

\[
\binom{s}{2}e_s(R)
\le
E_2\frac{H^{s-2}}{(s-2)!}.
\]

Since \(\binom{s}{2}=s(s-1)/2\),

\[
e_s(R)\le \frac{2E_2H^{s-2}}{s!}.
\]

This proves (1.1). Finally, \(E_2\le H^2/2\) gives (1.2). ∎

---

## 2. Lower bound for at least two hits in an arbitrary interval

### Lemma 2 — pair/triple Bonferroni lower bound

**Status: PROVED.**

Let \(S\) be a finite set of \(m\) primes, all \(\le y\). Let \(J\) be any interval of \(L\) consecutive integers. Define

\[
M_S(J):=\#\{n\in J:\omega_S(n)\ge2\}.
\]

Then

\[
M_S(J)
\ge
L\,e_2(S)\left(1-\frac{2H(S)}3\right)
-
\left[\binom m2+2\binom m3\right].
\tag{2.1}
\]

If \(m\le y\), then the error term satisfies

\[
\binom m2+2\binom m3\le y^3.
\tag{2.2}
\]

#### Proof of the pointwise inequality

For an integer \(k\ge0\), we claim

\[
\mathbf 1_{k\ge2}
\ge
\binom{k}{2}-2\binom{k}{3}.
\tag{2.3}
\]

Check cases:

- \(k=0,1\): both sides are \(0\).
- \(k=2\): RHS \(=1\).
- \(k=3\): RHS \(=3-2=1\).
- \(k\ge4\): RHS \(\le0\), while LHS \(=1\).

Thus (2.3) holds for every \(k\).

Now sum (2.3) over \(n\in J\), with \(k=\omega_S(n)\). The sum of \(\binom{\omega_S(n)}2\) over \(n\in J\) is

\[
\sum_{\{q,r\}\subset S}N_J(qr),
\]

and the sum of \(\binom{\omega_S(n)}3\) is

\[
\sum_{\{q,r,u\}\subset S}N_J(qru).
\]

Therefore

\[
M_S(J)
\ge
\sum_{\{q,r\}\subset S}N_J(qr)
-
2
\sum_{\{q,r,u\}\subset S}N_J(qru).
\tag{2.4}
\]

Using (0.2),

\[
\sum_{\{q,r\}\subset S}N_J(qr)
\ge
L e_2(S)-\binom m2,
\]

and

\[
\sum_{\{q,r,u\}\subset S}N_J(qru)
\le
L e_3(S)+\binom m3.
\]

Hence

\[
M_S(J)
\ge
L e_2(S)-\binom m2
-
2L e_3(S)-2\binom m3.
\tag{2.5}
\]

We need \(e_3(S)\le H(S)e_2(S)/3\). Indeed,

\[
3e_3(S)
=
\sum_{\{q,r\}\subset S}
\frac1{qr}
\sum_{\substack{u\in S\\u\ne q,r}}\frac1u
\le
H(S)e_2(S).
\]

Substituting into (2.5) gives (2.1).

For (2.2), since \(m\le y\),

\[
\binom m2+2\binom m3
\le
\frac{m^2}{2}+\frac{m^3}{3}
\le
\frac{y^2}{2}+\frac{y^3}{3}
\le y^3
\]

for \(y\ge2\). In all applications below \(y\ge17\). ∎

---

## 3. Explicit constants and the splitting point \(17\)

We fix the splitting point

\[
z=17.
\]

The finite set of primes below \(17\) is

\[
\{2,3,5,7,11,13\}.
\]

Its largest two-prime product is \(11\cdot13=143\).

We also fix

\[
L_0:=17^6=24\,137\,569.
\]

For \(L\ge L_0\), put

\[
y:=L^{1/6}\ge17.
\]

The following elementary numerical checks are used repeatedly.

1. Since \(L\ge17^6\), we have \(y\ge17\).

2. Since \(L^{1/2}=y^3\),

\[
y^3\le \frac{L}{289}
\iff
L^{1/2}\ge289.
\]

At \(L=L_0\), \(L^{1/2}=17^3=4913\ge289\). Thus for all \(L\ge L_0\),

\[
y^3\le \frac{L}{289}.
\tag{3.1}
\]

3. If \(E_2\ge1/y^2\), then

\[
y^3\le \frac{L E_2}{3}
\]

holds whenever \(L^{1/6}\ge3\). Since \(y\ge17\), this holds.

4. If \(E_2\ge1/(13y)\), then

\[
y^3\le \frac{L E_2}{6}
\]

is implied by

\[
L^{1/3}\ge78.
\]

At \(L=L_0\), \(L^{1/3}=17^2=289\ge78\). Thus this holds for all \(L\ge L_0\).

5. For \(L\ge L_0\),

\[
\frac{L}{143}-1\ge \frac{L}{286}
\]

because this is equivalent to \(L\ge286\).

All of these are finite explicit computations.

---

## 4. Definition of the threshold

Define, for \(L\ge L_0\),

\[
A(L):=\ln\left(1+\frac{\ln L}{6}\right).
\]

Set

\[
s(L):=\max\left(6,\left\lceil 23A(L)\right\rceil\right),
\tag{4.1}
\]

and finally

\[
t(L):=s(L)+5.
\tag{4.2}
\]

The constant \(23\) is chosen so that

\[
3e^2<23.
\tag{4.3}
\]

Explicitly, using \(e<2.719\),

\[
3e^2<3(2.719)^2=22.178883<23.
\]

Thus for every \(L\ge L_0\), if

\[
R:=Q\cap[2,y],
\qquad
H:=H(R),
\]

then by (0.4),

\[
H\le e\ln(1+\ln y)
=e\ln\left(1+\frac{\ln L}{6}\right)
=eA(L).
\]

Therefore

\[
3eH\le 3e^2A(L)<23A(L)\le s(L).
\tag{4.4}
\]

Using the standard inequality \(s!\ge (s/e)^s\), we get

\[
\frac{H^s}{s!}
\le
\left(\frac{eH}{s}\right)^s
\le
3^{-s}
\le
3^{-6}
=
\frac1{729}.
\tag{4.5}
\]

Status of definitions and elementary numerical inequalities: PROVED.

---

## 5. Main theorem (T1)

### Theorem 3 — two-layer sieve lemma (TL)

**Status: PROVED.**

Let \(L\ge L_0=24\,137\,569\). Let \(Q\) be any finite set of primes. Let \(J\) be any interval of \(L\) consecutive integers. With

\[
t(L)=5+\max\left(6,\left\lceil 23\ln\left(1+\frac{\ln L}{6}\right)\right\rceil\right),
\]

we have

\[
\#\{i\le L:\omega_Q(i)\ge t(L)\}
\le
\#\{i\in J:\omega_Q(i)\ge2\}.
\]

#### Proof

Let

\[
y=L^{1/6},
\qquad
R:=\{q\in Q:q\le y\}.
\]

An integer \(n\le L\) can have at most five prime divisors from \(Q\setminus R\), because six primes \(>y=L^{1/6}\) would have product \(>L\). Hence

\[
\omega_Q(n)\ge s(L)+5=t(L)
\implies
\omega_R(n)\ge s(L).
\]

Therefore

\[
\#\{i\le L:\omega_Q(i)\ge t(L)\}
\le
\#\{i\le L:\omega_R(i)\ge s(L)\}.
\tag{5.1}
\]

We bound the right-hand side using Lemma 1, and we bound

\[
M_Q(J):=\#\{i\in J:\omega_Q(i)\ge2\}
\]

from below by a case analysis.

Let

\[
T:=\{q\in R:q\ge17\},
\qquad
P:=\{q\in R:q<17\}.
\]

Thus \(P\subset\{2,3,5,7,11,13\}\). Put

\[
H_T:=H(T)=\sum_{q\in T}\frac1q.
\]

We consider two main cases.

---

### Case 1: \(H_T\ge1/2\)

Choose a subset \(S\subset T\) whose reciprocal sum first reaches at least \(1/2\). Since every prime in \(T\) is at least \(17\), each reciprocal is at most \(1/17\). Hence

\[
\frac12\le H(S)\le \frac12+\frac1{17}=\frac{19}{34}.
\tag{5.2}
\]

Also every \(q\in S\) satisfies \(q\ge17\), so

\[
\sum_{q\in S}\frac1{q^2}
\le
\frac1{17}H(S).
\]

Therefore

\[
e_2(S)
=
\frac12\left(H(S)^2-\sum_{q\in S}\frac1{q^2}\right)
\ge
\frac12 H(S)\left(H(S)-\frac1{17}\right).
\]

Since \(H(S)\ge1/2\), this gives

\[
e_2(S)
\ge
\frac12\cdot\frac12\left(\frac12-\frac1{17}\right)
=
\frac{15}{136}.
\tag{5.3}
\]

Now apply Lemma 2 to \(S\). By (5.2),

\[
1-\frac{2H(S)}3
\ge
1-\frac{2}{3}\cdot\frac{19}{34}
=
\frac{32}{51}.
\tag{5.4}
\]

Thus

\[
M_S(J)
\ge
L\cdot\frac{15}{136}\cdot\frac{32}{51}
-
y^3.
\]

The constant simplifies:

\[
\frac{15}{136}\cdot\frac{32}{51}
=
\frac{20}{289}.
\]

Using (3.1), \(y^3\le L/289\). Hence

\[
M_S(J)
\ge
\frac{20L}{289}-\frac{L}{289}
=
\frac{19L}{289}.
\]

Since

\[
\frac{19}{289}>\frac1{16},
\]

we obtain

\[
M_Q(J)\ge M_S(J)\ge \frac{L}{16}.
\tag{5.5}
\]

On the other hand, by Lemma 1 and (4.5),

\[
\#\{i\le L:\omega_R(i)\ge s(L)\}
\le
L\frac{H^{s(L)}}{s(L)!}
\le
\frac{L}{729}.
\tag{5.6}
\]

Since \(1/729<1/16\), (5.1), (5.5), and (5.6) prove the theorem in Case 1.

---

### Case 2: \(H_T<1/2\)

Let \(a:=|P|\).

---

#### Case 2A: \(a\ge2\)

There are at least two primes of \(Q\) below \(17\). Choose two of them, say \(p<r\). Their product satisfies

\[
pr\le 11\cdot13=143.
\]

Every multiple of \(pr\) in \(J\) is counted in \(M_Q(J)\). By (0.1),

\[
M_Q(J)\ge N_J(pr)
\ge
\frac{L}{pr}-1
\ge
\frac{L}{143}-1.
\]

Since \(L\ge L_0\ge286\),

\[
\frac{L}{143}-1\ge \frac{L}{286}.
\]

Thus

\[
M_Q(J)\ge \frac{L}{286}.
\tag{5.7}
\]

Again by Lemma 1 and (4.5),

\[
\#\{i\le L:\omega_R(i)\ge s(L)\}
\le
\frac{L}{729}.
\]

Since \(1/729<1/286\), the theorem follows in Case 2A.

---

#### Case 2B: \(a=0\)

Then \(R=T\), and

\[
H(R)=H_T<\frac12.
\]

Let

\[
E_2:=e_2(R).
\]

If \(E_2=0\), then \(R\) has at most one prime, so \(\omega_R(n)\le1\) for all \(n\). Since \(s(L)\ge6\), the left side of (5.1) is \(0\), and we are done.

Assume \(E_2>0\). Since all primes in \(R\) are at most \(y\), any pair contributes at least \(1/y^2\), so

\[
E_2\ge\frac1{y^2}.
\tag{5.8}
\]

Apply Lemma 2 with \(S=R\). Since \(H(R)<1/2\),

\[
1-\frac{2H(R)}3>\frac23.
\]

Thus

\[
M_R(J)
\ge
\frac{2}{3}L E_2-y^3.
\]

By the numerical check in Section 3 and (5.8),

\[
y^3\le \frac{L E_2}{3}.
\]

Therefore

\[
M_Q(J)\ge M_R(J)\ge \frac{L E_2}{3}.
\tag{5.9}
\]

Now use Lemma 1 in the sharper form (1.1):

\[
\#\{i\le L:\omega_R(i)\ge s(L)\}
\le
L\frac{2E_2H(R)^{s(L)-2}}{s(L)!}.
\]

Since \(s(L)\ge6\), \(s(L)!\ge720\), and \(H(R)^{s(L)-2}\le1\), we get

\[
\#\{i\le L:\omega_R(i)\ge s(L)\}
\le
L E_2\frac{2}{720}
=
\frac{L E_2}{360}.
\tag{5.10}
\]

Since \(1/360<1/3\), (5.9) and (5.10) prove Case 2B.

---

#### Case 2C: \(a=1\)

Let \(P=\{p\}\), where \(p\in\{2,3,5,7,11,13\}\). Then

\[
H(R)=\frac1p+H_T
<
\frac1p+\frac12
\le1.
\tag{5.11}
\]

Let again \(E_2=e_2(R)\). If \(E_2=0\), then \(R\) has at most one prime, and the left side of (5.1) is \(0\) because \(s(L)\ge6\). So assume \(E_2>0\). Then \(T\) is nonempty, and any \(q\in T\) satisfies \(q\le y\). Hence the pair \(\{p,q\}\) gives

\[
E_2\ge \frac1{pq}\ge\frac1{13y}.
\tag{5.12}
\]

Apply Lemma 2 with \(S=R\). Since \(H(R)\le1\),

\[
1-\frac{2H(R)}3\ge \frac13.
\]

Therefore

\[
M_R(J)\ge \frac13 L E_2-y^3.
\]

By the numerical check in Section 3 and (5.12),

\[
y^3\le \frac{L E_2}{6}.
\]

Thus

\[
M_Q(J)\ge M_R(J)\ge \frac{L E_2}{6}.
\tag{5.13}
\]

Again by Lemma 1 and \(H(R)\le1\),

\[
\#\{i\le L:\omega_R(i)\ge s(L)\}
\le
L\frac{2E_2}{s(L)!}
\le
\frac{L E_2}{360}.
\tag{5.14}
\]

Since \(1/360<1/6\), (5.13) and (5.14) prove Case 2C.

---

All cases are exhausted. Combining (5.1) with the case estimates gives

\[
\#\{i\le L:\omega_Q(i)\ge t(L)\}
\le
\#\{i\in J:\omega_Q(i)\ge2\}.
\]

∎

---

## 6. Weighted versions

The problem also asks for a weighted version. I give precise proved statements for the cases needed in the motivation, especially weights equal to \(1/2\), and a precise partial result for general weights.

Throughout this section, use the simpler squarefree weighted sum

\[
U(n):=\sum_{\substack{q\in Q\\q\mid n}}u_q,
\qquad
0\le u_q\le1.
\]

This is explicitly allowed in the prompt.

---

### Lemma 4 — weighted theorem when all positive weights are at least \(1/2\)

**Status: PROVED.**

Suppose that for every \(q\in Q\), either \(u_q=0\) or \(u_q\ge1/2\). Let \(t(L)\) be the threshold from Theorem 3. Then for every \(L\ge L_0\) and every interval \(J\) of length \(L\),

\[
\#\{i\le L:U(i)\ge t(L)\}
\le
\#\{i\in J:U(i)\ge1\}.
\tag{6.1}
\]

#### Proof

If \(U(i)\ge t(L)\), since each \(u_q\le1\), we must have

\[
\omega_Q(i)\ge t(L).
\]

Therefore, by Theorem 3,

\[
\#\{i\le L:U(i)\ge t(L)\}
\le
\#\{i\le L:\omega_Q(i)\ge t(L)\}
\le
\#\{i\in J:\omega_Q(i)\ge2\}.
\]

But if \(\omega_Q(i)\ge2\) and all positive weights are at least \(1/2\), then

\[
U(i)\ge 2\cdot\frac12=1.
\]

Thus

\[
\#\{i\in J:\omega_Q(i)\ge2\}
\le
\#\{i\in J:U(i)\ge1\}.
\]

This proves (6.1). ∎

---

### Corollary 5 — the case \(u_q\equiv1/2\)

**Status: PROVED.**

Let \(u_q=1/2\) for every \(q\in Q\). Then

\[
U(n)=\frac12\omega_Q(n).
\]

Define

\[
\tau(L):=\left\lceil \frac{t(L)}2\right\rceil.
\]

Then for every \(L\ge L_0\) and every interval \(J\) of length \(L\),

\[
\#\{i\le L:U(i)\ge \tau(L)\}
\le
\#\{i\in J:U(i)\ge1\}.
\tag{6.2}
\]

Equivalently,

\[
\#\{i\le L:\omega_Q(i)\ge 2\tau(L)\}
\le
\#\{i\in J:\omega_Q(i)\ge2\}.
\]

#### Proof

If \(U(i)\ge\tau(L)\), then

\[
\omega_Q(i)\ge 2\tau(L)\ge t(L).
\]

Also \(U(i)\ge1\) is equivalent to \(\omega_Q(i)\ge2\). The result follows immediately from Theorem 3. ∎

This is the exact weighted case mentioned in the prompt as the motivating case.

---

### Lemma 6 — explicit lower bound for arbitrary weights via heavy primes

**Status: PROVED as a lower-bound statement; full arbitrary-weight inequality not claimed.**

For arbitrary weights \(u_q\in[0,1]\), define the heavy set

\[
Q_{\ge1/2}:=\{q\in Q:u_q\ge1/2\},
\]

and the unit-weight set

\[
Q_{=1}:=\{q\in Q:u_q=1\}.
\]

Then for every interval \(J\),

\[
\#\{i\in J:U(i)\ge1\}
\ge
\max\Bigl(
\#\{i\in J:\omega_{Q_{=1}}(i)\ge1\},
\#\{i\in J:\omega_{Q_{\ge1/2}}(i)\ge2\}
\Bigr).
\tag{6.3}
\]

Moreover, the second term on the right can be bounded from below by the explicit machinery of Lemmas 2 and Theorem 3 after replacing \(Q\) by \(Q_{\ge1/2}\). In particular, in the notation of the proof of Theorem 3, if

\[
R_{\ge1/2}:=Q_{\ge1/2}\cap[2,L^{1/6}],
\]

then the same case analysis gives one of the following explicit lower bounds:

- if the tail reciprocal sum of \(R_{\ge1/2}\) above \(17\) is at least \(1/2\), then

  \[
  \#\{i\in J:\omega_{Q_{\ge1/2}}(i)\ge2\}
  \ge
  \frac{L}{16};
  \]

- if there are at least two primes of \(Q_{\ge1/2}\) below \(17\), then

  \[
  \#\{i\in J:\omega_{Q_{\ge1/2}}(i)\ge2\}
  \ge
  \frac{L}{286};
  \]

- in the remaining cases, with \(E_2=e_2(R_{\ge1/2})\),

  \[
  \#\{i\in J:\omega_{Q_{\ge1/2}}(i)\ge2\}
  \ge
  \frac{L E_2}{3}
  \quad\text{or}\quad
  \frac{L E_2}{6},
  \]

  exactly as in Cases 2B and 2C of Theorem 3.

#### Proof

If \(i\) is divisible by a prime \(q\in Q_{=1}\), then \(U(i)\ge1\). This gives the first term in the maximum.

If \(i\) is divisible by at least two primes from \(Q_{\ge1/2}\), then

\[
U(i)\ge \frac12+\frac12=1.
\]

This gives the second term.

The quantitative bounds for the second term are just Theorem 3’s lower-bound case analysis applied to the prime set \(Q_{\ge1/2}\). ∎

For fully arbitrary weights with many very small \(u_q\), the corresponding multi-layer inequality is not proved here. The statements above are the explicit weighted consequences I can prove without additional assumptions.

---

## 7. Target T3

**Status: NOT PROVED HERE / NO COUNTEREXAMPLE CLAIMED.**

The theorem above proves (TL) with coefficient \(23\) in front of \(\ln\ln L\). This does not rule out counterexamples for thresholds with coefficient \(\le20\). I have not found a rigorous explicit counterexample satisfying the required adversarial audit, so I do not assert one.

---

## 8. Summary of explicit constants

- \(L_0=17^6=24\,137\,569\).
- \(y=L^{1/6}\).
- \(A(L)=\ln(1+\ln L/6)\).
- \(s(L)=\max(6,\lceil 23A(L)\rceil)\).
- \(t(L)=s(L)+5\).
- Large-prime overflow allowance: at most \(5\) primes \(>L^{1/6}\) can divide an integer \(\le L\).
- Heavy/light split point: \(17\).
- Main lower-bound constants:
  \[
  \frac{20}{289},\quad \frac{19}{289},\quad \frac1{16},\quad \frac1{286},\quad \frac1{360},\quad \frac13,\quad \frac16.
  \]
- Key numerical inequalities used:
  \[
  3e^2<23,
  \qquad
  17^6=24\,137\,569,
  \qquad
  17^3=4913\ge289,
  \qquad
  17^2=289\ge78.
  \]

The main result, Theorem 3, is fully proved.