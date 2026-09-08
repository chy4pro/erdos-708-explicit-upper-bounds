## Results

The threshold proved here is
\[
\boxed{c=\frac{56501}{6400}=8.82828125<\frac{97}{10}.}
\]

For every atom system in the question, every \(m\ge1\), and every \(x\ge0\),
\[
\boxed{
\sum_{k=1}^{m}\left(S(k)-\frac{56501}{6400}\right)^+
\le
\sum_{b=x+1}^{x+m}(S(b)-1)^+.
}
\]

Using the transfer supplied in the question, this gives
\[
\boxed{
g(n)\le \left\lceil\frac{56501}{6400}n\right\rceil+2n
\le 11n.
}
\]

There is also an explicit counterexample to \(H_{19/10}\), with
\[
\boxed{m=404471,\qquad L=21>20=R.}
\]
The construction is given in Lemma 10. Its generalization proves that **every absolute threshold \(c<2\) fails**.

I do not claim a proof of \(H_7\) or \(H_6\), or a counterexample to \(H_2\) or \(H_3\).

### Route table and judge decisions

| Route | Advantage | Weakness / obstacle | Verification bridge | Decision |
|---|---|---|---|---|
| R1: eight mantissas | Reduces the multiplicative rounding loss to \(9/8\) | Enlarges the carrier-level family; an initially proposed retention rule had invalid negative moduli | Exact retention-budget and rounding knapsacks | **PROVED** with the repaired rule below |
| R2: threshold below \(7\) | Only omitted-atom source points obstruct the current truncation | Their positive contribution cannot simply be discarded | A separate large-atom certificate would be needed | **OPEN; frozen; not used** |
| R3: joint certificate optimization | Prime-counting controls the floor errors; cardinality-aware counting improves feasibility | The resulting estimates do not reach the parameters needed for \(c=7\) | 57 finite scales plus an analytic infinite tail, all constants checked exactly | **PROVED** at \(T=401/75\) |
| R4: CRT refutation | Both hinge sums can be counted exactly | The construction approaches \(2\) from below, not above | Explicit 21-prime example and direct integer verification | **REFUTED:** \(H_{19/10}\) |

The proof below does **not** assume the truth of a newly proposed intermediate inequality. The finite computations are exhaustive coefficient calculations, not numerical sampling.

---

# Complete proof

Write
\[
H(f)=\sum_{p,j}\frac{\beta_{p,j}}{p^j}
\]
when
\[
f(n)=\sum_{p,j}\beta_{p,j}[p^j\mid n],
\qquad
\beta_{p,j}\ge0,\qquad
\sum_j\beta_{p,j}\le1.
\]

The constants used throughout are
\[
Q=2^{16},\qquad H_*=\frac{1025}{1024},\qquad
\rho=\frac98,\qquad
T=\frac{401}{75},\qquad
D_0=\frac{3601}{1280}.
\]
Thus
\[
D_0+\rho T
=\frac{3601}{1280}+\frac{1203}{200}
=\frac{56501}{6400}.
\tag{1}
\]

## Lemma 1 — PROVED: moments, optimized hinges, and exponential moments

Let \(f_p\) be nonnegative prime-power atom functions, each bounded by \(1\), and put
\[
H=\sum_p H(f_p).
\]
Then
\[
\sum_{n\le N}e_r((f_p(n))_p)\le \frac{NH^r}{r!}.
\tag{2}
\]

For \(a\ge r-1\), put
\[
v=\left\lfloor\frac{ra}{r-1}\right\rfloor.
\]
Then, for \(u_i\in[0,1]\),
\[
\left(\sum_i u_i-a\right)^+
\le
\frac{v-a}{\binom vr}\,e_r(u).
\tag{3}
\]

For \(z>1\),
\[
\frac1N\sum_{n\le N}z^{\sum_p f_p(n)}
\le \exp((z-1)H).
\tag{4}
\]

**Proof.** For distinct primes \(p_1,\ldots,p_r\), expanding their atom functions and counting multiples gives
\[
\sum_{n\le N}\prod_{i=1}^r f_{p_i}(n)
\le N\prod_{i=1}^r H(f_{p_i}).
\]
Sum over prime subsets and use \(e_r(H(f_p))\le H^r/r!\).

For (3), the difference between the right side and the left side is concave in each coordinate separately. Its minimum on the cube occurs at a vertex. At a vertex with \(h\) ones, the required inequality is
\[
(h-a)^+\le \frac{v-a}{\binom vr}\binom hr.
\]
For integers \(h>a\), the ratio
\[
\frac{h-a}{\binom hr}
\]
increases precisely while \(h+1\le ra/(r-1)\), and then decreases. Its maximum is therefore attained at \(v\).

Finally,
\[
z^u\le1+(z-1)u\qquad(0\le u\le1).
\]
Expand the product over primes, apply the same multiple-counting argument, and bound the resulting product by an exponential. ∎

## Lemma 2 — PROVED: large-atom truncation and the dense branch

Let \(S_0\) contain exactly the atoms with
\[
p^j\le m/Q.
\]
For every \(c\ge7\),
\[
\sum_{k\le m}(S(k)-c)^+
=
\sum_{k\le m}(S_0(k)-c)^+.
\tag{5}
\]

Moreover, if \(H(S_0)\ge H_*\), then \(H_c\) holds for every \(c\ge7\).

**Proof.** Suppose an omitted atom \(q=p^j>m/Q\) divides \(k\le m\). If \(\omega(k)\ge8\), then \(k/q\) contains at least seven other distinct prime factors, so
\[
\frac{k}{q}\ge2\cdot3\cdot5\cdot7\cdot11\cdot13\cdot17
=510510>Q,
\]
a contradiction. Thus \(S(k)\le\omega(k)\le7\), proving (5).

For the dense branch, set
\[
V=\frac{H_*}{H(S_0)}S_0.
\]
Its per-prime parts remain bounded by \(1\), and \(H(V)=H_*\). Since every atom satisfies \(q\le m/Q\),
\[
\sum_{k\le m}V(k)\ge m(1-1/Q)H_*.
\]
By Lemma 1 with \(r=8,a=7\),
\[
\sum_{k\le m}(V(k)-7)^+\le \frac{mH_*^8}{8!}.
\]
Consequently,
\[
\sum_{k\le m}\min(V(k),7)
\ge
m\left((1-1/Q)H_*-\frac{H_*^8}{8!}\right)>m.
\tag{6}
\]
The last strict rational inequality is checked by the verifier.

Because \(S_0\ge V\) and \(c\ge7\),
\[
\sum_{k\le m}\min(S_0(k),c)\ge m.
\]
Every length-\(m\) window contains at least \(\lfloor m/q\rfloor\) multiples of each \(q\). Hence
\[
\begin{aligned}
\sum_{k\le m}(S_0(k)-c)^+
&\le \sum_{k\le m}S_0(k)-m\\
&\le \sum_{b\in I}S_0(b)-m\\
&\le \sum_{b\in I}(S_0(b)-1)^+.
\end{aligned}
\]
Now use (5) and \(S_0\le S\). ∎

Henceforth assume
\[
H(S_0)<H_*.
\tag{7}
\]

## Lemma 3 — PROVED: the repaired eight-mantissa retention rule

Use the levels
\[
\mathcal D=\{1\}\cup
\left\{\frac{j}{2^h}:j=8,\ldots,15,\ h\ge4\right\}.
\tag{8}
\]
Consecutive levels have ratio at most \(\rho=9/8\).

For \(t\le1/8\), define
\[
\eta(t)=\frac{16t}{27}.
\tag{9}
\]
For \(t>1/8\), write \(t=v/64\) and define
\[
\eta(v/64)=E_v/720
\]
by this complete table:

| \(v\) | \(E_v\) |
|---|---:|
| \(9,10\) | \(60\) |
| \(11\) | \(71\) |
| \(12\) | \(72\) |
| \(13\) | \(76\) |
| \(14\) | \(80\) |
| \(15\) | \(88\) |
| \(16\) | \(96\) |
| \(18,20,22,24,26,28\) | \(120\) |
| \(30,32\) | \(160\) |
| \(36,40,44,48,52,56,60,64\) | \(240\) |

For each prime \(p\), let \(q_p(t)\) be the least prime power at which its cumulative \(S_0\)-part reaches \(t\), or \(\infty\) if it never does. Retain \((p,t)\) exactly when
\[
q_p(t)\le m^{\eta(t)}.
\]
Define
\[
b_p(n)=\max\bigl(\{t\in\mathcal D:(p,t)\text{ retained},\ q_p(t)\mid n\}\cup\{0\}\bigr),
\qquad B(n)=\sum_p b_p(n).
\tag{10}
\]

Then \(B\le S_0\), \(H(B)\le H(S_0)\), and every atom of \(B\) has modulus at most \(m^{1/3}\).

Furthermore, for every shortest nonincreasing prefix of levels whose mass exceeds \(1\), its modulus product satisfies
\[
P_C\le m^{2/3}.
\tag{11}
\]

**Proof.** The inequalities \(B\le S_0\) and \(H(B)\le H(S_0)\) follow prime by prime. Mean monotonicity can be seen by averaging over a common period. Retained levels are finite: for sufficiently small \(t\), \(m^{16t/27}<2\).

The table satisfies
\[
\eta(t)\le\frac13,\qquad
\eta(t)\le\frac{16t}{27}
\tag{12}
\]
at every level.

Let \(\theta\) be the last—and smallest—level of the prefix, and \(s\) its mass. Then
\[
1<s\le1+\theta.
\tag{13}
\]
If \(\theta\le1/8\), (12) gives
\[
\sum_{p\in C}\eta(t_p)
\le \frac{16}{27}s
\le \frac{16}{27}\frac98
=\frac23.
\tag{14}
\]

For \(\theta>1/8\), all levels are integer multiples of \(1/64\). The remaining verification is the following finite integer knapsack.

For each minimum \(v\), let \(D_v(w)\) be the maximum total \(E\)-weight of a multiset of levels \(u\ge v\) with total \(u\)-mass \(w\). It is computed by
\[
D_v(0)=0,\qquad
D_v(w)=\max_{\substack{u\ge v\\u\le w}}
\bigl(D_v(w-u)+E_u\bigr),
\tag{15}
\]
with unattainable states omitted.

Removing the last minimum level from a shortest carrier leaves a mass
\[
65-v\le w\le64.
\]
For **every one of the 24 possible \(v\)**, the exact result is
\[
\max_{65-v\le w\le64}\bigl(D_v(w)+E_v\bigr)=480.
\tag{16}
\]
The verifier evaluates (15) exhaustively. Dividing (16) by \(720\) proves the exponent budget \(2/3\), and therefore (11). ∎

This repairs the negative-modulus issue: **every** atom \(q\) of any capped outside function satisfies \(q\le m^{1/3}\), so
\[
\boxed{P_Cq\le m}
\tag{17}
\]
without assuming that capping at \(\theta\) preserves a cutoff \(m^{\eta(\theta)}\).

## Lemma 4 — PROVED: rounding loss \(3601/1280\)

For every \(k\le m\),
\[
S_0(k)\le \rho B(k)+\frac{3601}{1280}.
\tag{18}
\]
Consequently, with \(c=D_0+\rho T\),
\[
\sum_{k\le m}(S_0(k)-c)^+
\le \rho L_B,\qquad
L_B=\sum_{k\le m}(B(k)-T)^+.
\tag{19}
\]

**Proof.** The case \(m=1\) is immediate; assume \(m\ge2\).

For each prime contributing a positive error \(S_{0,p}(k)-\rho b_p(k)\), let \(t_p\) be the largest level at most \(S_{0,p}(k)\). This level must be unretained. Therefore
\[
a_p:=\frac{\log p^{v_p(k)}}{\log m}>\eta(t_p),
\qquad
\sum_p a_p\le1.
\tag{20}
\]

For \(t_p\le1/8\), the error is at most the successor level and hence at most
\[
\rho t_p=\frac{243}{128}\eta(t_p).
\tag{21}
\]

For larger levels, the cost \(720\eta(t_p)=E_v\) is integral, and the error is bounded by the successor level. In units of \(1/64\), let its reward be \(r_v\): the next \(v\) in the table, with reward \(64\) at the top.

Let \(R(w)\) be the maximum total reward at exact cost \(w\):
\[
R(0)=0,\qquad
R(w)=\max_{E_v\le w}\bigl(R(w-E_v)+r_v\bigr).
\tag{22}
\]
By the strict inequality in (20), the total large-level cost is at most \(719\).

The complete finite check is
\[
\max_{\substack{0\le w\le719\\R(w)\text{ attainable}}}
\left\{1440R(w)+243(720-w)\right\}
=259272.
\tag{23}
\]
Its maximum occurs at \(w=696\), with \(R(w)=176\). The maximizing large-level pattern is
\[
1,\ 1,\ 7/16,\ 1/4.
\]
Dividing (23) by \(92160\), and using (21) for the remaining cost, yields
\[
\frac{259272}{92160}=\frac{3601}{1280}.
\]
This proves (18), and (19) follows by taking positive parts. ∎

## Lemma 5 — PROVED: the explicit finite carrier family

At every hot source \(k\le m\), meaning \(B(k)>T\), order its positive \(b_p(k)\) nonincreasingly, breaking ties by increasing prime. Assign \(k\) to the shortest prefix \(C\) of mass exceeding \(1\).

A carrier records its primes and their levels. Define
\[
\theta_C=\min_{p\in C}t_p,\qquad
s_C=\sum_{p\in C}t_p,\qquad
P_C=\prod_{p\in C}q_p(t_p),
\]
\[
\nu_C=\left\lfloor\frac m{P_C}\right\rfloor,
\qquad
M_C=\sum_{\substack{k\le m\\k\text{ assigned to }C}}(B(k)-T)^+,
\qquad
c_C=\frac{M_C}{\nu_C}.
\tag{24}
\]
Discard carriers with \(M_C=0\).

This is an explicit finite family, with at most \(m\) members. It satisfies
\[
\sum_C M_C=L_B.
\tag{25}
\]

Put
\[
U_C(n)=\sum_{p\notin C}\min(b_p(n),\theta_C).
\tag{26}
\]
For
\[
a=\frac{T-s_C}{\theta_C},
\]
we have
\[
c_C\le \varepsilon_{\theta_C,s_C},
\tag{27}
\]
where
\[
\varepsilon_{\theta,s}
=
\min_{2\le r\le\lfloor a\rfloor+1}
\frac{\theta(v_r-a)(H_*/\theta)^r}{(v_r)_r},
\quad
v_r=\left\lfloor\frac{ra}{r-1}\right\rfloor,
\quad
(v)_r=v(v-1)\cdots(v-r+1).
\tag{28}
\]

**Proof.** At an assigned source, every outside level is at most \(\theta_C\). Writing \(k=P_Cu\), outside primes are coprime to \(P_C\), so
\[
B(k)-T=U_C(u)-(T-s_C).
\]
Thus \(M_C\) is bounded by the corresponding hinge sum over all genuine integers \(u\le\nu_C\). Apply Lemma 1 to
\[
\frac{\min(b_p(u),\theta_C)}{\theta_C}\in[0,1].
\]
Their total mean is at most \(H_*/\theta_C\). This gives (27)–(28), with no floor-ratio loss. ∎

## Lemma 6 — PROVED: prime-density bounds and certificate value

For integer \(\nu\),
\[
\begin{array}{c|c}
\nu\ge210 & \pi(\nu)/\nu\le9/40\\
\nu\ge2310 & \pi(\nu)/\nu\le3/20\\
\nu\ge30030 & \pi(\nu)/\nu\le1/8.
\end{array}
\tag{29}
\]

Define
\[
\delta(\theta)=
\begin{cases}
9/40,&\theta\ge7/8,\\
3/20,&3/4\le\theta<7/8,\\
1/8,&\theta<3/4.
\end{cases}
\tag{30}
\]
For every carrier,
\[
\pi(\nu_C)/\nu_C\le\delta(\theta_C).
\tag{31}
\]

For any \(K_\theta>H_*+\delta(\theta)\theta\), define
\[
\lambda_\theta
=\frac{\rho K_\theta}{K_\theta-H_*-\delta(\theta)\theta}
\tag{32}
\]
and the finite certificate
\[
\boxed{
F(n)=
\sum_C
\lambda_{\theta_C}c_C[P_C\mid n]
\left(1-\frac{U_C(n)}{K_{\theta_C}}\right).
}
\tag{33}
\]
Then every length-\(m\) window satisfies
\[
\boxed{\sum_{b\in I}F(b)\ge\rho L_B.}
\tag{34}
\]

**Proof of the prime bounds.** Write \(\vartheta(x)=\sum_{p\le x}\log p\). The central-binomial-coefficient induction gives
\[
\vartheta(x)\le x\log4.
\]
For completeness: for \(2r\), use the primes in \((r,2r]\) dividing \(\binom{2r}{r}\le2^{2r-1}\); for \(2r+1\), use the primes in \((r+1,2r+1]\) dividing \(\binom{2r+1}{r}\le2^{2r}\).

Partial summation from \(64\), where \(\pi(64)=18\), gives
\[
\pi(x)\le18+\frac{x\log4}{\log x}
+\log4\int_{64}^{x}\frac{dt}{\log^2t}.
\]
Since \(\log64>4\),
\[
\int_{64}^{x}\frac{dt}{\log^2t}\le \frac{2x}{\log^2x}.
\]
Using \(2/3<\log2<7/10\), for \(x\ge32768\),
\[
\frac{\pi(x)\log x}{x}
<
\frac75+\frac{14}{50}+\frac{189}{32768}
<\frac{17}{10}.
\tag{35}
\]

Equation (35), together with exact sieve checks on
\[
[210,32768),\quad [2310,2^{17}),\quad [30030,2^{21}),
\]
proves (29). The verifier checks only primes and the initial endpoints, which suffices because \(\pi(n)/n\) decreases between primes.

At a hot source,
\[
\sum_{p\notin C}b_p(k)>T-1-\theta_C.
\]
Because \(T>41/8\), this forces at least four outside primes in the first class of (30), five in the second, and six in the third. Thus
\[
\nu_C\ge210,\quad2310,\quad30030,
\]
respectively, proving (31).

**Proof of the certificate value.** Every atom \(q\) of \(U_C\) satisfies \(P_Cq\le m\), by Lemma 3. If \(\nu=\lfloor m/P_C\rfloor\), then
\[
\#\{b\in I:P_Cq\mid b\}
\le \left\lfloor\frac{\nu}{q}\right\rfloor+1.
\tag{36}
\]
The total atom weight of each prime-part of \(U_C\) is at most \(\theta_C\). All these primes are at most \(\nu\). Therefore
\[
\sum_{b\in I}[P_C\mid b]U_C(b)
\le \nu H_*+\theta_C\pi(\nu).
\tag{37}
\]
Also \(\sum_I[P_C\mid b]\ge\nu\). Equations (31)–(32) imply
\[
\sum_{b\in I}
\lambda_{\theta_C}c_C[P_C\mid b]
\left(1-\frac{U_C(b)}{K_{\theta_C}}\right)
\ge \rho M_C.
\]
Sum over the finite carrier family and use (25). ∎

## Lemma 7 — PROVED: pointwise feasibility, including the high-level improvement

Fix a level \(\theta=j/L\), where \(j=8,\ldots,15\), \(L\ge16\) is a power of two; the exceptional top level \(1\) is represented by \((j,L)=(8,8)\).

At a point \(n\), let
\[
N=\#\{p:b_p(n)\ge\theta\}.
\]
For an active carrier of cardinality \(k\), mass \(s=1+d/L\), and minimum \(\theta\),
\[
U_C(n)\ge(N-k)\theta,
\qquad
B(n)-1\ge d/L+(N-k)\theta.
\tag{38}
\]

Put
\[
P_{j,L}(X)=\sum_{\substack{t\in\mathcal D\\t\ge j/L}}X^{Lt},
\]
and
\[
E_{k,d}
=[X^{L+d}]
\left(P_{j,L}(X)^k-(P_{j,L}(X)-X^j)^k\right).
\tag{39}
\]
A valid normalized bound for this level is
\[
A_\theta=
\max_N
\sum_{k,d}
\binom Nk E_{k,d}\varepsilon_{\theta,1+d/L}
\frac{\left(1-(N-k)\theta/K_\theta\right)^+}
{d/L+(N-k)\theta}.
\tag{40}
\]
The maximum only needs
\[
N\le\left\lfloor K_\theta/\theta\right\rfloor
+\left\lfloor1/\theta\right\rfloor+2.
\tag{41}
\]

For \(\theta\ge1/2\), the following smaller bound is valid. Define
\[
e_\theta=
\begin{cases}
\varepsilon_{\theta,2\theta},&\theta>1/2,\\
0,&\theta=1/2,
\end{cases}
\qquad
h_\theta=
\begin{cases}
\varepsilon_{1/2,3/2},&\theta=1/2,\\
0,&\theta>1/2,
\end{cases}
\]
\[
E_\theta(v)=
\sum_{\substack{t\in\mathcal D\\\theta<t\le v}}
\varepsilon_{\theta,\theta+t},
\qquad
p_k=\left(1-(N-k)\theta/K_\theta\right)^+.
\]
Then one may replace (40) by
\[
A_\theta=
\max_{N,v}
\frac{
N(N-1)(e_\theta/2+E_\theta(v))p_2
+\binom N3h_\theta p_3
}{Nv-1}.
\tag{42}
\]
Zero-denominator, zero-numerator cases are omitted.

With these bounds,
\[
F(n)\le
\left(\sum_\theta\lambda_\theta A_\theta\right)(B(n)-1)^+,
\tag{43}
\]
where the tail levels may instead use the direct bound in Lemma 8.

**Proof.** If \(B(n)\le1\), no carrier can be active, because its prescribed levels already sum to more than \(1\).

Otherwise, discard negative carrier contributions. Equation (38), the coefficient bound (27), and the count (39) give (40). Positive terms require \(N-k<K_\theta/\theta\), while \(k\theta\le1+\theta\), proving (41).

For \(\theta>1/2\), carriers have exactly two primes. If the eligible prime caps at \(n\) are \(v_1,\ldots,v_N\), their total coefficient bound is
\[
\binom N2 e_\theta+(N-1)\sum_iE_\theta(v_i).
\]
For \(\theta=1/2\), add the triples with all three levels \(1/2\), contributing
\[
\binom N3\varepsilon_{1/2,3/2}.
\]
For fixed \(N\), the resulting numerator is an affine sum of functions of the individual \(v_i\), and the denominator is
\[
\sum_i(v_i-1/N).
\]
The ratio is bounded by the maximum individual ratio, equivalently the configuration with all caps equal to some \(v\). This is precisely (42). The only possible zero denominator has zero numerator. ∎

## Lemma 8 — PROVED: the 57 finite scales and the infinite tail

Choose \(K_\theta\) by the following table. Entries in the middle column are \(40K_\theta\), in increasing order \(j=8,\ldots,15\); the top row has only \(j=8\).

| \(L\) | \(40K_\theta\) | Upper bound for \(\sum_j\lambda_\theta A_\theta\), in units \(10^{-6}\) |
|---:|---|---:|
| 8 | 200 | 48879 |
| 16 | 125, 113, 125, 138, 150, 162, 175, 187 | 549612 |
| 32 | 61, 72, 78, 73, 79, 87, 97, 91 | 271163 |
| 64 | 50, 54, 57, 58, 60, 58, 57, 66 | 99084 |
| 128 | 45, 46, 47, 48, 47, 50, 48, 49 | 20073 |
| 256 | 43, 43, 43, 43, 44, 44, 44, 45 | 1577 |
| 512 | 41, 41, 42, 42, 42, 42, 42, 42 | 26 |
| 1024 | 41, 41, 41, 41, 41, 41, 41, 41 | 1 |

The total finite contribution is less than
\[
\frac{990415}{10^6}.
\tag{44}
\]

For every remaining scale \(L\ge2048\), take
\[
K_\theta=\frac{41}{40}.
\]
Their combined contribution is less than \(1/1000\). Consequently,
\[
\boxed{
F(n)\le\frac{198283}{200000}(B(n)-1)^+.
}
\tag{45}
\]

**Proof of the finite calculation.** The verifier computes the coefficients (39) by integer polynomial multiplication. It computes (28) by exact integer comparison of rational values. It then evaluates (40) or (42) over the complete finite range.

For efficiency, moment bounds are rounded **upward** to a common power-of-two denominator. Individual terms of (40) are again rounded upward. Thus every displayed bound is an upper bound, including rounding error. No floating-point arithmetic is used.

**Proof of the infinite tail.** For \(z>1\),
\[
(y-a)^+\le\frac{z^{y-a}}{e\log z}.
\]
Apply Lemma 1’s exponential-moment bound directly to the carrier mass. Since \(s_C\le1+\theta\), at \(z=9/2\) we obtain
\[
c_C\le \rho\theta\,a_0^{1/\theta},
\qquad
a_0=\frac{120347}{2500000}.
\tag{46}
\]
Here the exact checks are
\[
e\log(9/2)>4,\qquad
\exp\!\left(\frac72H_*\right)<\frac{133}{4},
\]
\[
\left(\frac{133}{4}\right)^{75}
<a_0^{75}\left(\frac92\right)^{326}.
\tag{47}
\]
The verifier supplies rational series bounds for the transcendental inequalities.

For the tail, \(\lambda_\theta<50\). Define
\[
\mathcal P_j(X)=
\sum_{a=j}^{15}X^a+
\sum_{h\ge1}\sum_{a=8}^{15}X^{a2^h}.
\tag{48}
\]

The following rational data are used:

| \(j\) | \(x_j\) | \(\overline P_j\ge\mathcal P_j(x_j)\) | \(\sigma_j\) |
|---:|---:|---:|---:|
| 8 | \(473/625\) | \(421847/10^6\) | \(157/200\) |
| 9 | \(3883/5000\) | \(42539/10^5\) | \(827/1000\) |
| 10 | \(7939/10000\) | \(42847/10^5\) | \(859/1000\) |
| 11 | \(4047/5000\) | \(107879/250000\) | \(22/25\) |
| 12 | \(8233/10000\) | \(216251/500000\) | \(111/125\) |
| 13 | \(4181/5000\) | \(86661/200000\) | \(441/500\) |
| 14 | \(8481/10000\) | \(215799/500000\) | \(863/1000\) |
| 15 | \(8593/10000\) | \(213963/500000\) | \(83/100\) |

The defining checks are
\[
0<\mathcal P_j(x_j)\le\overline P_j<1,
\qquad
(a_0x_j^{-j})^{40}
\le \sigma_j^{40}(1-\overline P_j)^{41}.
\tag{49}
\]
For the first check, terms through \(h=4\) are summed exactly, and the remainder is bounded by \(x_j^{256}/(1-x_j)\).

Here is the counting argument for the tail. In (40), write \(n=N-k\), discard the penalty, use the denominator bound \(1/L\), and replace the maximum over \(N\) by a sum. The generating identity
\[
\sum_{k\ge0}\binom{n+k}{k}P(X)^k
=(1-P(X))^{-n-1}
\tag{50}
\]
and
\[
\sum_{n=0}^{M}(1-\overline P)^{-n-1}
\le
\frac{(1-\overline P)^{-M-1}}{\overline P}
\tag{51}
\]
give the following normalized contribution at \(L,j\):
\[
50\rho j\,
\frac{\sum_{d=1}^{j}x_j^{-d}}
{\overline P_j(1-\overline P_j)}
\,\sigma_j^{L/j}.
\tag{52}
\]
This uses the **direct carrier bound** (46); no comparison between that bound and the optimized moment envelope is assumed.

Let
\[
z_j=\sigma_j^{\lfloor2048/j\rfloor}.
\]
Summing over \(L=2048\cdot2^h\), and using \(2^h\ge h+1\), bounds the entire tail by
\[
\sum_{j=8}^{15}
50\rho j\,
\frac{\sum_{d=1}^{j}x_j^{-d}}
{\overline P_j(1-\overline P_j)}
\frac{z_j}{1-z_j}
<\frac1{1000}.
\tag{53}
\]
This last inequality is entirely rational and is checked exactly.

Combining (44) and (53),
\[
\frac{990415}{10^6}+\frac1{1000}
=\frac{198283}{200000}<1,
\]
proving (45). ∎

## Lemma 9 — PROVED: closure for every atom system and every window

For
\[
c=\frac{56501}{6400},
\]
the inequality \(H_c\) holds universally.

**Proof.** The dense branch is Lemma 2. In the sparse branch, Lemmas 2, 4, 6, and 8 give
\[
\begin{aligned}
\sum_{k\le m}(S(k)-c)^+
&=\sum_{k\le m}(S_0(k)-c)^+\\
&\le \rho L_B\\
&\le \sum_{b\in I}F(b)\\
&\le \frac{198283}{200000}
       \sum_{b\in I}(B(b)-1)^+\\
&\le \sum_{b\in I}(S(b)-1)^+.
\end{aligned}
\]
All branches, including \(m=1\), are covered. ∎

The transfer supplied in the question now yields
\[
g(n)\le\left\lceil\frac{56501}{6400}n\right\rceil+2n\le11n.
\]

## Lemma 10 — PROVED: explicit refutation of \(H_{19/10}\), and the barrier \(c\ge2\)

Take the 21 primes
\[
\begin{split}
P=\{&
503,509,521,523,541,547,557,563,569,571,577,\\
&587,593,599,601,607,613,617,619,631,641\},
\end{split}
\]
with \(\alpha_{p,1}=1\), and no other atoms. Set
\[
m=631\cdot641=404471,\qquad Q_P=\prod_{p\in P}p,
\]
\[
x=Q_P-202236
=
8741863184546118987302153833068330864675030899050452812141.
\tag{54}
\]
Thus
\[
I=\{Q_P-202235,\ldots,Q_P+202235\}.
\]

Then
\[
\boxed{
\sum_{k\le m}(S(k)-19/10)^+=21,
\qquad
\sum_{b\in I}(S(b)-1)^+=20.
}
\tag{55}
\]

**Proof.** The smallest pair product is
\[
503\cdot509=256027,
\]
and the smallest triple product is
\[
503\cdot509\cdot521=133390067.
\]
Therefore
\[
m<2\cdot256027,\qquad m<133390067.
\]
In \([1,m]\), each of the \(\binom{21}{2}=210\) pair products occurs exactly once, and no integer has three chosen prime factors. Hence the left side of (55) is
\[
210(2-19/10)=21.
\]

Every pair product divides \(Q_P\), and the window radius \(202235\) is smaller than every pair product. Thus the only point in \(I\) divisible by two chosen primes is \(Q_P\) itself. At that point \(S(Q_P)=21\), giving right side \(20\). ∎

More generally, take \(r\) primes in a sufficiently large interval \([M,\sqrt2M)\), let \(m\) be the largest pair product, and center the length-\(m\) window at their product. The same argument gives
\[
L=\binom r2(2-c),\qquad R=r-1,
\]
so failure occurs whenever
\[
c<2-\frac2r.
\tag{56}
\]

Such clusters exist for arbitrarily large \(r\). Otherwise the numbers of primes in the geometric intervals \([2^{j/2},2^{(j+1)/2})\) would eventually be uniformly bounded, forcing \(\sum_p1/p<\infty\). Euler’s elementary argument rules this out: bounded \(\sum_p1/p\) would bound the finite Euler products, while
\[
\sum_{n\le y}\frac1n
\le\prod_{p\le y}(1-1/p)^{-1}.
\]
Thus every \(c<2\) is refuted by this family.

---

# Adversarial audit

**REFUTED — the discarded retention shortcut.** The earlier proposal \(\eta(1/2)=1/4\), together with \(\eta(1)=1/3\), does not justify the negative-modulus bound after capping.

Take
\[
m=2^{132},\quad
P=2^{33}3^{20}5^{13},\quad q=7^{15},
\]
and
\[
k=P(11\cdot13\cdot17\cdot19\cdot23\cdot29\cdot31\cdot37).
\]
Give the three carrier atoms and the eight displayed outside primes weight \(1/2\), and give \(7^{15}\) weight \(1\). Then
\[
k\le m<Pq,
\]
the source is hot with \(B(k)=11/2\), and its shortest carrier consists of the three \(1/2\)-level atoms. Capping the \(7\)-part at \(1/2\) still introduces modulus \(q\), so the negative modulus is \(Pq>m\). The final retention rule avoids this defect by proving \(P_C\le m^{2/3}\) independently of the cap.

**EXHAUSTIVE finite refutation search.** The verifier checked all 81 half-weight systems on \(2,3,5,7\), every \(1\le m\le420\), and every window residue \(0\le x<210\): **7,144,200 windows**. No \(H_2\) or \(H_3\) counterexample occurs in that finite family. This is not used as a universal theorem.

**HEURISTIC construction, EXACT verification — Hensley–Richards-type audit.** A deterministic residue search produces 2,268 admissible offsets in \([1,20000]\), versus \(\pi(20000)=2262\). Admissibility is checked against every prime up to \(2498\); larger primes exceed the number of offsets. The complete object is reproduced by the verifier, with SHA-256
```text
5c9905c4ee137dbf7ca6b789bba7f226cf84fd3aec06777c68947cd816280ab4
```
The certificate kernel is also checked on reflected-window residues, centered CRT windows, and the resulting HR window, at lengths \(10^4,10^5,10^6,10^7\).

## Dependency closure

```text
H_(56501/6400)
  ← large-atom truncation/dense branch
  ← repaired retention and exact rounding knapsack
  ← finite carrier certificate and its window value
  ← pointwise carrier counting
  ← 57 exact finite-scale bounds + rigorously bounded infinite tail
  ← Lemmas 1–9.

g(n) ≤ ceil((56501/6400)n) + 2n ≤ 11n
  ← H_(56501/6400)
  ← the transfer supplied in the question.

H_(19/10) is false; every c<2 fails
  ← Lemma 10.

Unproved items used in these claims: NONE.

Not established here, and not used:
H_7, H_6, or a counterexample to H_2 or H_3.
```