# A complete proof of \(H_{97/10}\)

**Result.** For every finite atom system in the question, every integer \(m\ge1\), and every integer \(x\ge0\),
\[
\sum_{k=1}^m(S(k)-97/10)^+
\le \sum_{n=x+1}^{x+m}(S(n)-1)^+.
\]
Using the transfer to \(g\) supplied in the question, this gives
\[
g(n)\le \lfloor 257n/10\rfloor.
\]
Every lemma below is **PROVED**. The numerical verification uses exact integers and fractions; no proof-assistant/kernel formalization is claimed.

## Route table

| Route | Advantage | Obstacle and resolution | Decision / verification bridge |
|---|---|---|---|
| R1: finer rounding | Four mantissas per dyadic band give factor \(5/4\) | A nonuniform retention rule must still bound every carrier modulus; Lemmas 3–4 do this | PROVED; retention multiset audit also supplied |
| R2: mass-graded coefficients | Optimize the elementary-symmetric order separately for each carrier mass | The carrier overshoot is no longer exactly its last level; count every possible mass separately | PROVED; 29 finite scales plus an analytic infinite tail |
| R3: dense and large-atom branches | They already work above threshold 7 | Remove any large-\(m\) proviso from the floor-ratio bound | PROVED: a nonzero carrier has cofactor at least 210 |
| R4: exact refutation search | Tests arithmetic window structure directly | A finite search cannot establish a universal theorem | No \(H_2/H_3\) counterexample in the reported finite family; not used in the proof |

## Constants
\[
Q=65536,\quad H_*=\frac{1025}{1024},\quad
\Gamma=\frac{211}{210},\quad K=\frac83,\quad
\lambda=\frac{51}{10},
\]
\[
\rho=\frac54,\qquad D_0=\frac{47}{16},\qquad
T=\frac{541}{100},\qquad
c=D_0+\rho T=\frac{97}{10}.
\]

## Lemma 1 — PROVED: moments and optimized hinge majorants

For a finite nonnegative prime-power atom function \(f=\sum_p f_p\), write
\[
\mathcal H(f)=\sum_{p,j}\frac{\beta_{p,j}}{p^j},
\qquad f_p(n)=\sum_j\beta_{p,j}[p^j\mid n].
\]
If each \(f_p\le1\), then
\[
\sum_{n\le N}e_r((f_p(n))_p)
\le N\frac{\mathcal H(f)^r}{r!}.                                      \tag{1}
\]
Indeed, expansion of \(e_r\) only uses distinct primes. Each term has
modulus equal to the product of its prime powers. Its count is at most
\(N\) divided by that product. Summing gives
\(N e_r((\mathcal H(f_p))_p)\le N\mathcal H(f)^r/r!\).

Pointwise domination of finite atom functions implies domination of
\(\mathcal H\), by averaging over a common period.

For \(a\ge r-1\), \(r\ge2\), set
\[
v=\left\lfloor\frac{ra}{r-1}\right\rfloor,\qquad
A_r(a)=\frac{v-a}{\binom vr}.
\]
Then, for every finite vector \(u_i\in[0,1]\),
\[
\left(\sum_i u_i-a\right)^+\le A_r(a)e_r(u).                            \tag{2}
\]
To prove this, the difference between the right side and left side is
concave separately in each coordinate, so its minimum occurs at a cube
vertex. At a vertex with \(h\) ones, the assertion is trivial for \(h<r\).
For \(h\ge r\), the ratio
\[
g(h)=\frac{(h-a)^+}{\binom hr}
\]
is maximized at \(h=v\): where both numerators are positive,
\[
g(h+1)\le g(h)
\quad\Longleftrightarrow\quad
h\ge\frac{ra}{r-1}-1.
\]
Possible equality between adjacent maximizing integers does not change
the bound. This proves (2).

In particular, \((\sum u_i-7)^+\le e_8(u)\).

## Lemma 2 — PROVED: large atoms and the dense branch

Let \(S_0\) retain exactly the atoms \(p^j\le m/Q\), and put
\(H=\mathcal H(S_0)\).

Suppose an omitted atom \(q=p^j>m/Q\) divides \(k\le m\). Then
\(k/q<Q\). Since
\[
2\cdot3\cdot5\cdot7\cdot11\cdot13\cdot17=510510>Q,
\]
the cofactor has at most six distinct prime factors. Thus \(k\) has at
most seven, and \(S(k)\le7\). Consequently, for every \(c\ge7\),
\[
(S(k)-c)^+=(S_0(k)-c)^+ \qquad(k\le m).                                \tag{3}
\]

If \(H\ge H_*\), put \(V=(H_*/H)S_0\). Each retained modulus is at most
\(m/Q\), hence
\[
\sum_{k\le m}V(k)\ge(1-Q^{-1})mH_*.
\]
Using (1),
\[
\sum_{k\le m}\min(V(k),7)
\ge m\left((1-Q^{-1})H_*-\frac{H_*^8}{8!}\right)>m.                     \tag{4}
\]
The strict rational inequality is checked in `exact_verifier.py`.
Since \(c=97/10>7\), \(S_0\ge V\) gives
\(\sum_{k\le m}\min(S_0(k),c)\ge m\). Therefore
\[
\begin{aligned}
\sum_{k\le m}(S_0(k)-c)^+
&\le \sum_{k\le m}S_0(k)-m\\
&\le \sum_{n\in I}S_0(n)-m\\
&\le \sum_{n\in I}(S(n)-1)^+.
\end{aligned}
\]
Here each atom has at least as many multiples in \(I\) as in \([1,m]\).
Together with (3), this proves the theorem in the dense case.

Henceforth \(H<H_*\). The case \(m=1\) is immediate.

## Lemma 3 — PROVED: four-mantissa rounding with loss \(47/16\)

Use the fixed level set
\[
\mathcal D=\{1\}\cup
\bigcup_{h\ge3}\left\{\frac4{2^h},\frac5{2^h},
                         \frac6{2^h},\frac7{2^h}\right\}.
\]
Adjacent levels have ratio at most \(5/4\).

For \(t\in\mathcal D\), let \(q_p(t)\) be the least power of \(p\) at which
the cumulative \(p\)-part of \(S_0\) reaches \(t\), when such a power exists.
Retain \((p,t)\) exactly when
\[
q_p(t)\le m^{\eta(t)},\qquad
\eta(t)=
\begin{cases}
1/3,&t>1/2,\\
4t/9,&0<t\le1/2.
\end{cases}                                                        \tag{5}
\]
Define
\[
b_p(n)=\max\bigl(\{t:(p,t)\text{ retained},\ q_p(t)\mid n\}\cup\{0\}\bigr),
\qquad B(n)=\sum_pb_p(n).
\]
This is finite: for \(t\le1/2\), retention and \(q_p(t)\ge2\) imply
\(t\ge9\log2/(4\log m)\). The functions \(b_p\) are nondecreasing in the
valuation, so have finite nonnegative prime-power increment expansions.
Also \(B\le S_0\), and \(\mathcal H(B)\le H<H_*\).

For \(k\le m\), set \(f_p=S_{0,p}(k)\), and round positive \(f_p\) down to
its largest \(\mathcal D\)-level \(t_p\). Thus \(f_p\le(5/4)t_p\).
If this level was retained, its contribution to \(S_0(k)-\rho B(k)\)
is nonpositive.

For an unretained level define
\[
a_p=\frac{v_p(k)\log p}{\log m};
\qquad \sum_pa_p\le1.
\]
If \(t_p>1/2\), then \(a_p>1/3\), and \(f_p\le1\).
There can be at most two such primes; call their number \(h\).
For every other unretained level,
\[
t_p<\frac94a_p,\qquad f_p\le\frac54t_p<\frac{45}{16}a_p.
\]
Dropping all nonpositive contributions gives
\[
\begin{aligned}
S_0(k)-\rho B(k)
&\le h+\frac{45}{16}\left(1-\frac h3\right)\\
&\le \frac{47}{16}.
\end{aligned}
\]
Thus
\[
S_0(k)\le\frac54B(k)+\frac{47}{16},\qquad
\sum_{k\le m}(S_0(k)-c)^+\le\frac54 L_B,                              \tag{6}
\]
where \(L_B=\sum_{k\le m}(B(k)-T)^+\).

## Lemma 4 — PROVED: carrier support, with no small-\(m\) exception

For every hot \(k\), meaning \(B(k)>T\), order its positive effective
levels \(b_p(k)\) in nonincreasing order, breaking ties by the prime.
Take the shortest prefix of total mass greater than 1. A carrier \(C\)
records the primes, their effective levels, and their moduli \(q_p(t)\).
Write
\[
s_C=\sum_{p\in C}t_p,\qquad \theta_C=\min_{p\in C}t_p,\qquad
P_C=\prod_{p\in C}q_p(t_p).
\]
Then
\[
1<s_C\le1+\theta_C\le2,                                               \tag{7}
\]
and every outside effective level at its source point is at most
\(\theta_C\).

The retention rule ensures
\[
P_C\le m^{2/3}.                                                       \tag{8}
\]
Here is the complete case check.

If \(\theta_C>1/2\), the carrier has exactly two primes, each with exponent
budget \(1/3\).

If \(\theta_C\le1/2\) and there is no level above \(1/2\), the total exponent
budget is
\[
\frac49s_C\le\frac49(1+\theta_C)\le\frac23.
\]

Otherwise there is exactly one high level \(a\ge5/8\). If
\(\theta_C\le3/8\), the remaining mass is at most
\(1+3/8-5/8=3/4\), so its exponent budget is at most
\(1/3+(4/9)(3/4)=2/3\).
If \(3/8<\theta_C\le1/2\), every low level before termination is at least
\(7/16\). Its sum with \(a\ge5/8\) already exceeds 1, so there is only one
low level. The exponent budget is at most \(1/3+2/9<2/3\).
This proves (8).

Every atom in \(B\), and in every capped function
\(\min(b_p,\theta)\), has modulus at most \(m^{1/3}\).
Consequently every negative modulus used below satisfies
\[
P_Cq\le m.                                                          \tag{9}
\]
No inference that capping at \(\theta\) shrinks the original modulus
support is used.

Define
\[
M_C=\sum_{\substack{k\le m\\\operatorname{carrier}(k)=C}}(B(k)-T),
\quad \nu_C=\lfloor m/P_C\rfloor,\quad c_C=M_C/\nu_C.
\]
Use only carriers with \(M_C>0\). Then
\[
\sum_CM_C=L_B,\qquad \nu_C\ge210,\qquad
\frac{m}{P_C\nu_C}<1+\frac1{\nu_C}\le\Gamma.                           \tag{10}
\]
Indeed, at any source point, the mass outside the carrier exceeds
\(T-s_C\ge T-2=341/100>3\). At least four distinct outside primes divide
\(k/P_C\), so that cofactor is at least \(2\cdot3\cdot5\cdot7=210\).
This proves (10) for every \(m\), without a large-\(m\) assumption.

## Lemma 5 — PROVED: mass-dependent coefficient bounds

For \(\theta=\theta_C\), \(s=s_C\), put
\[
a=\frac{T-s}{\theta}.
\]
Then
\[
c_C\le\epsilon_{\theta,s}:=
\min_{2\le r\le\lfloor a\rfloor+1}
\left\{\theta A_r(a)\frac{(H_*/\theta)^r}{r!}\right\}.                 \tag{11}
\]

Write a source point as \(k=P_Cu\), with \(u\le\nu_C\).
Outside the carrier the valuations at \(k\) and \(u\) agree, and the
effective source levels are at most \(\theta\). Therefore
\[
M_C\le
\sum_{u\le\nu_C}
\left(\sum_{p\notin C}\min(b_p(u),\theta)-(T-s)\right)^+.
\]
Apply Lemma 1 to the capped functions divided by \(\theta\); their mean
is at most \(H_*/\theta\). Dividing by \(\nu_C\) proves (11).

There is **no floor-loss factor \(\Gamma\)** in (11): the moment estimate
is taken over the actual integer range \(u\le\nu_C\). The factor
\(\Gamma\) is used only for the later interval value estimate.

## Lemma 6 — PROVED: the explicit certificate and its pointwise reduction

Put
\[
U_C(n)=\sum_{p\notin C}\min(b_p(n),\theta_C),
\qquad
F(n)=\lambda\sum_Cc_C[P_C\mid n]\left(1-\frac{U_C(n)}K\right).          \tag{12}
\]
This is an explicit finite signed atom family. Its positive atom for a
carrier has modulus \(P_C\). Expand \(U_C\) into its nonnegative
prime-power increments; every negative atom then has modulus \(P_Cq\),
which is at most \(m\) by (9).

To prove pointwise feasibility, represent a level other than 1 uniquely
as \(\theta=j/L\), where \(j\in\{4,5,6,7\}\) and \(L=8,16,\ldots\).
Represent level 1 by \((j,L)=(4,4)\).
Every carrier level at least \(\theta\) is an integer multiple of \(1/L\),
so (7) gives
\[
s=1+d/L,\qquad 1\le d\le j.
\]

Define the finite polynomial
\[
G_{j,L}(X)=1+\sum_{\substack{t\in\mathcal D\\t\ge j/L}}X^{Lt}
\]
and the integer counts
\[
D_{j,L,d}(N)=[X^{L+d}]
\left(G_{j,L}(X)^N-(G_{j,L}(X)-X^j)^N\right).                          \tag{13}
\]
For fixed \(n\), let \(N=\#\{p:b_p(n)\ge\theta\}\).
A dividing carrier of mass \(1+d/L\) injects into an assignment counted
by (13): assign each of these \(N\) primes either zero or its selected
level; at least one selected level is \(\theta\).
Ignoring unavailable levels or moduli only increases this count.

For such a carrier,
\[
U_C(n)\ge\max(0,N\theta-s),\qquad
B(n)-1\ge\max(s-1,N\theta-1).
\]
The first follows from
\(U_C\ge\theta(N-|C|)\) and \(|C|\theta\le s\).

Set
\[
A_{j,L}=
\max_{\substack{N\in\mathbb Z_{\ge0}\\
 N\le\lfloor(K+1)L/j+1\rfloor}}
\sum_{d=1}^j
D_{j,L,d}(N)\epsilon_{\theta,1+d/L}
\frac{\left(1-\max(0,N\theta-1-d/L)/K\right)^+}
{\max(d/L,N\theta-1)}.                                                \tag{14}
\]
Beyond the stated \(N\)-range every numerator is zero.
Discard negative summands of \(F\), apply (11), and then (13)–(14).
If \(B(n)\le1\), no carrier divides \(n\). Thus for every positive integer
\(n\),
\[
F(n)\le\lambda
\left(A_{4,4}+\sum_{L=8,16,\ldots}\sum_{j=4}^7 A_{j,L}\right)
(B(n)-1)^+.                                                         \tag{15}
\]

## Lemma 7 — PROVED: all 29 finite scales

Exact integer coefficient extraction and rational maximization in
(11)–(14) give the following strict upper bounds. All entries in the
right column have denominator \(10^6\).

| \(L\) | Upper numerator for \(\sum_j A_{j,L}\) |
|---:|---:|
| 4 (only \(j=4\)) | 24680 |
| 8 | 128711 |
| 16 | 25773 |
| 32 | 5665 |
| 64 | 1025 |
| 128 | 150 |
| 256 | 21 |
| 512 | 3 |

The numerators sum to 186028. In particular,
\[
A_{4,4}+\sum_{L=8,\ldots,512}\sum_{j=4}^7 A_{j,L}<187/1000.            \tag{16}
\]

For reproducibility, `exact_verifier.py` computes every coefficient of
\(G^N-(G-X^j)^N\) through degree \(L+j\), all the integers \(N\) in (14),
and every integer \(r\) in (11). It stores the exact maximizing \(N\),
the chosen moment order for every mass, and each exact rational bound
in `constants.json`. It uses no floating-point arithmetic.
The exact finite sum lies in
\[
[186024001631/10^{12},\ 186024001632/10^{12}].
\]

## Lemma 8 — PROVED: the whole infinite tail

First obtain a uniform coefficient bound. For \(z>1\) and \(u_i\in[0,1]\),
\[
z^{\sum_i u_i}\le\prod_i(1+(z-1)u_i).
\]
Expand and use (1), then use
\(y^+\le z^y/(e\log z)\). The proof of Lemma 5 yields
\[
c_C\le
\frac{\theta z}{e\log z}
\left(\frac{\exp((z-1)H_*)}{z^{T-1}}\right)^{1/\theta}.
\]
Exactly the same is therefore a valid uniform substitute for the
coefficient bound (11).

Take \(z=9/2\) and \(a_0=4377/100000\).
The exact rational checks
\[
e<87/32,\quad (87/32)^3<(9/2)^2,\quad e>8/3
\]
give \(e\log(9/2)>4\).
A Taylor-series remainder bound gives
\[
\exp((7/2)H_*)<133/4,
\]
and
\[
(133/4)^{100}<a_0^{100}(9/2)^{441}.
\]
Thus
\[
\epsilon_{\theta,s}\ \text{may be replaced, for upper bounds, by}\
\frac{9\theta}{8}a_0^{1/\theta}.                                    \tag{17}
\]
More precisely, both (11) and (17) separately bound \(c_C\); wherever
(17) is used below it bounds the same carrier coefficients directly.
One may also replace \(\epsilon_{\theta,s}\) throughout by the minimum
of the two bounds. This avoids assuming that the particular finite
minimum in (11) is always below (17).

For \(j=4,5,6,7\), let
\[
\mathcal G_j(x)=1+\sum_{a=j}^7x^a+
                    \sum_{r\ge1}\sum_{a=4}^7x^{a2^r}.
\]
Use the following rational pairs:

| \(j\) | \(x_j\) | \(F_j\) |
|---:|---:|---:|
| 4 | \(583/1000\) | \(632591/500000\) |
| 5 | \(321/500\) | \(159089/125000\) |
| 6 | \(69/100\) | \(1278827/1000000\) |
| 7 | \(73/100\) | \(639137/500000\) |

They satisfy
\[
\mathcal G_j(x_j)\le F_j,\quad F_j\ge5/4,\quad
a_0^3x_j^{-3j}F_j^{11}<1.                                             \tag{18}
\]
For the first inequality, sum the \(r=1,\ldots,4\) bands and bound the
remaining distinct exponents, all at least 128, by \(x^{128}/(1-x)\).
All assertions in (18) are exact rational comparisons.

For clarity, for the remainder of this lemma let \(A^{\rm tail}_{j,L}\)
mean the expression (14) with every coefficient upper bound replaced by
(17). Inequality (15) holds with \(A^{\rm tail}_{j,L}\) on these scales.
Put
\[
D_j=\sum_{d=1}^j x_j^{-d},\quad \theta=j/L,\quad
q_j=a_0x_j^{-j}F_j^{11/3}<1,\quad h=4/3.
\]
Every coefficient in (13) is at most
\(x_j^{-(L+d)}F_j^N\).

Write \(y=N\theta-1\).
If \(y\le h\), then \(N\le7/(3\theta)\), the numerator in (14) is at most
1, and its denominator is at least \(1/L\). Hence
\[
A^{\rm low}_{j,L}
\le \frac{9j}{8}D_j
       \left(a_0x_j^{-j}F_j^{7/3}\right)^{L/j}
\le \frac{9j}{8}D_j(3/4)^{L/j}.                                      \tag{19}
\]
The final inequality uses (18) and
\((4/5)^4<(3/4)^3\).

If \(y>h\), the denominator is at least \(h\), and for
\(L\ge1024\) one has \(h>\theta\), so the numerator is at most
\((K+\theta-y)^+/K\). Maximizing \(wF_j^{-w/\theta}\) over \(w\ge0\)
gives \(\theta/(e\log F_j)\). Therefore
\[
A^{\rm high}_{j,L}
\le \frac{9}{8eKh\log F_j}\theta^2F_jD_jq_j^{L/j}
\le \frac{2187}{4096}\theta^2F_jD_j.                                 \tag{20}
\]
For the last inequality use \(e>8/3\) and
\[
\log F_j\ge\log(5/4)>2/9.
\]
The latter follows from
\(\log u\ge2(u-1)/(u+1)\) for \(u\ge1\), proved by differentiating the
difference.

Each \(N\) belongs to one of these two ranges, so the maximum in (14) is
at most the sum of the two bounds. Sum (19)–(20) over
\(L=1024\cdot2^r\), \(r\ge0\). With \(t=(3/4)^{146}\), because
\(1024/j\ge146\) and \(2^r\ge r+1\), the whole tail is at most
\[
\frac98\left(\sum_{j=4}^7jD_j\right)\frac{t}{1-t}
+
\frac{2187}{4096}\frac4{3\cdot1024^2}
\sum_{j=4}^7j^2F_jD_j
<\frac3{1000}.                                                       \tag{21}
\]
This is a single exact rational inequality, checked in the verifier.

Combining (16) and (21), with the finite coefficient bounds on the finite
scales and the exponential bounds on the tail scales, proves
\[
F(n)\le\frac{51}{10}\frac{19}{100}(B(n)-1)^+
       =\frac{969}{1000}(B(n)-1)^+
       \le(S(n)-1)^+.                                                \tag{22}
\]

## Lemma 9 — PROVED: certificate value and completion

For an integer modulus \(d\), write
\(N_I(d)=\#\{n\in I:d\mid n\}\).
Then
\[
N_I(P_C)\ge\nu_C.
\]
Every negative modulus \(P_Cq\) is at most \(m\), so
\[
N_I(P_Cq)\le\frac{m}{P_Cq}+1\le\frac{2m}{P_Cq}.
\]
The mean of \(U_C\) is at most \(H_*\). Thus (10) gives
\[
\begin{aligned}
\sum_{n\in I}F(n)
&\ge\lambda\sum_Cc_C
  \left(\nu_C-\frac{2mH_*}{KP_C}\right)\\
&\ge\lambda(1-2\Gamma H_*/K)L_B\\
&=\frac{718539}{573440}L_B
>\frac54L_B,
\end{aligned}                                                        \tag{23}
\]
since the excess coefficient over \(5/4\) is
\(1739/573440>0\).

By (3), (6), (22), and (23),
\[
\sum_{k\le m}(S(k)-97/10)^+
\le\frac54L_B
\le\sum_{n\in I}F(n)
\le\frac{969}{1000}\sum_{n\in I}(B(n)-1)^+
\le\sum_{n\in I}(S(n)-1)^+.
\]
If there are no hot points, \(L_B=0\), and the same conclusion follows
directly from (6). Lemma 2 covers the dense case, and \(m=1\) was trivial.
This completes the proof for all atom systems, all \(m\), and all windows.

## Adversarial audit and reproducible objects

`adversarial_audit.py` independently constructs actual finite carrier
coefficients, rather than merely their upper bounds, on two nonempty
certificate fixtures. It exhausts 1024 binary valuation patterns and
729 prime-power valuation patterns. The full carrier lists, negative
atoms, exact window values, and rational coefficients are in `audit.json`.

It additionally checks actual carriers at levels \(1/2,3/8,1/8,7/64\);
291600 quarter-weight one/two-prime edge instances; and reflected,
common-collision CRT, and staggered CRT windows at
\(m=10^4,10^5,10^6\).

The separate lower-threshold search is EXHAUSTIVE only for the fixed
prime system \(\{2,3,5,7,11,13,17\}\), unit weights, all \(510510\) shifts
in its period, and ten listed lengths: 5105100 windows total.
No \(H_2/H_3\) counterexample was found there.
This is not evidence of a universal \(H_2\) or \(H_3\) proof.

For a sieve-rich (Hensley–Richards-type obstruction) stress fixture,
this same period search finds \(m=10000,x=74769\): the number avoiding
these seven primes is 1812, compared with 1806 in \([1,10000]\).
This is an explicitly constructed sieve-rich window, not a claim to
reproduce a particular historical Hensley–Richards example.

Run:
```sh
python exact_verifier.py --output constants.json
python adversarial_audit.py --output audit.json
```

The exact verifier reports:
- finite-scale total between \(186024001631/10^{12}\) and \(186024001632/10^{12}\);
- analytic tail bound between \(2846921822/10^{12}\) and \(2846921823/10^{12}\);
- their sum times \(\lambda\) between \(963241709618/10^{12}\) and \(963241709619/10^{12}\);
- window coefficient \(718539/573440>5/4\).

## Final dependency block
\[
(H_{97/10})\ \longleftarrow\ \text{Lemmas 1--9 (PROVED)}
\ \longleftarrow\ \varnothing.
\]
\[
g(n)\le\lfloor257n/10\rfloor
\ \longleftarrow\ (H_{97/10})+\text{the transfer supplied in the question}
\ \longleftarrow\ \text{no additional unproved item}.
\]