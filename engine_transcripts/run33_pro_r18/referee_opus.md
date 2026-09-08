PASS

# Adversarial referee report — `pro_708_r18/proof.md`, the hinge inequality \(H_{97/10}\)

**Referee:** Claude Opus 5, blind/hostile mode. Every numerical constant below was
recomputed **from the manuscript's definitions** by a script I wrote myself
(`referee_checks.py`, in this directory), in `fractions.Fraction` / big-integer
arithmetic only. No floating point enters any decision. I did not look at the
author's verifier until after my own numbers were finished; when
`exact_verifier.py` / `constants.json` appeared in the directory mid-session I
compared and found **bit-for-bit agreement** (see §5).

**Claim refereed.** For every finite atom system (\(\alpha_{p,j}\ge0\),
\(\sum_j\alpha_{p,j}\le1\) per prime, \(S(n)=\sum\alpha_{p,j}[p^j\mid n]\)), every
\(m\ge1\) and every window \(I=\{x+1,\dots,x+m\}\),
\[\sum_{k\le m}\bigl(S(k)-\tfrac{97}{10}\bigr)^+\;\le\;\sum_{b\in I}\bigl(S(b)-1\bigr)^+.\]

**Verdict: PASS.** I found **no mathematical error and no numerical error.** The
architecture is sound, every lemma is correct as stated, and all 29 finite scales
plus the analytic tail reproduce exactly under independent recomputation. The
proof is *complete* in the sense that every step is true and derivable, but the
manuscript leaves **six one-line justifications implicit** (§6, G1–G6); all six
are true and I verified each. A formalizer will have to supply them, so if the
house convention is that "PASS" means *ready to formalize verbatim*, downgrade to
PASS-WITH-REPAIRS and apply G1–G6. There is also one deliverable gap (G7: a cited
audit script is absent) touching a section the proof does not use.

---

## 1. Lemma-by-lemma verdicts

| Lemma | Verdict | Notes |
|---|---|---|
| 1 — moments + \(A_r(a)\) | **correct** | see §1.1 |
| 2 — large atoms, dense branch | **correct** | see §1.2 |
| 3 — four-mantissa rounding, loss \(47/16\) | **correct** | see §1.3 |
| 4 — carrier support, cofactor \(\ge210\) | **correct**, and this is the good new idea | see §1.4 |
| 5 — mass-graded coefficients | **correct** | see §1.5 |
| 6 — certificate + counting reduction | **correct** | see §1.6 |
| 7 — 29 finite scales | **correct**, recomputed exactly | see §1.7, §4 |
| 8 — analytic tail | **correct**, recomputed exactly | see §1.8, §4 |
| 9 — window value + closing chain | **correct** | see §1.9 |

### 1.1 Lemma 1

*Moment bound (1).* Expanding \(e_r\) over distinct primes gives coprime moduli;
\(\#\{n\le N: d\mid n\}\le N/d\) is exact with no floor loss, so
\(\sum_{n\le N}e_r\le N\,e_r((\mathcal H(f_p))_p)\le N\mathcal H(f)^r/r!\) by Maclaurin.
Correct. (The hypothesis "each \(f_p\le1\)" is not needed for (1); harmless.)

*Vertex bound (2).* \(A_r(a)e_r(u)-(\sum u_i-a)^+\) is multi-affine minus convex,
hence **concave in each coordinate separately**, so its minimum on \([0,1]^n\) is at
a vertex. At a vertex with \(h\) ones the claim is \((h-a)^+\le A_r(a)\binom hr\).
I re-derived the monotonicity condition independently:
\[
g(h+1)\le g(h)\iff (h+1-a)(h+1-r)\le(h-a)(h+1)\iff h\ge\frac{ra}{r-1}-1,
\]
exactly the manuscript's criterion; hence the maximum sits at
\(\lceil \frac{ra}{r-1}-1\rceil=\lfloor\frac{ra}{r-1}\rfloor=v\) (with a harmless tie at
\(v-1\) when \(\frac{ra}{r-1}\in\mathbb Z\), as the manuscript says).
For \(h<r\) the claim is trivial *because* \(h\le r-1\le a\) — the manuscript just says
"trivial" (G6). I also checked \(A_r(a)=\max_{h\ge r}(h-a)^+/\binom hr\) numerically
by brute force at eight sampled \((a,r)\); all agreed. \(A_8(7)=1\). **Correct.**

### 1.2 Lemma 2

\(k/q<Q=65536<510510=2\cdot3\cdots17\) forces \(\omega(k/q)\le6\), so \(\omega(k)\le7\)
and \(S(k)\le\omega(k)\le7\) (each prime contributes \(\le\sum_j\alpha_{p,j}\le1\)).
Hence (3) holds for every \(c\ge7\), and \(97/10>7\). **Correct.**

Dense branch: \(V=(H_*/H)S_0\le S_0\) has \(V_p\le1\) and \(\mathcal H(V)=H_*\);
\(\lfloor m/d\rfloor\ge(1-1/Q)m/d\) for \(d\le m/Q\); \((\sum u-7)^+\le e_8\) gives
\(\sum(V-7)^+\le mH_*^8/8!\). **Exact check:**
\[(1-1/Q)H_*-H_*^8/8!-1=\frac{9127710437643246821282611}{9748777809372369664830603264}\approx 9.3629\cdot10^{-4}>0.\]
Then \(\min(S_0,c)\ge\min(V,7)\) since \(S_0\ge V,\ c\ge7\) — task item (c) checks out.
The transfer \(\sum_{k\le m}S_0(k)\le\sum_{n\in I}S_0(n)\) uses only
\(N_I(d)\ge\lfloor m/d\rfloor\). \(m=1\) is trivial (\(S(1)=0\)). **Correct.**

### 1.3 Lemma 3

\(\mathcal D=\{1\}\cup\bigcup_{h\ge3}\{4,5,6,7\}/2^h\). I verified by exact enumeration
that the **largest adjacent ratio in \(\mathcal D\) is exactly \(5/4\)** (attained at
\((5/2^h)/(4/2^h)\)); the ratios \(1{:}\tfrac78\) and \(\tfrac{4/2^h}{7/2^{h+1}}\) are \(8/7\).
So rounding down loses at most the factor \(\rho=5/4\).

Retention (5) with \(\eta(t)=1/3\) for \(t>1/2\) and \(4t/9\) for \(t\le1/2\):
\(\max\eta=1/3\), so **every retained modulus is \(\le m^{1/3}\)** — task item (f)
confirmed (\(4t/9\le2/9<1/3\) on \(t\le1/2\)).

Pointwise bound. \(b_p\le t_p\le f_p=S_{0,p}(k)\le1\); if \(t_p\) is retained then
\(q_p(t_p)\mid k\) (minimality of \(q_p\)) so the contribution \(f_p-\rho b_p(k)\le0\).
For unretained levels, \(p^{v_p(k)}\ge q_p(t_p)>m^{\eta(t_p)}\) gives \(a_p>\eta(t_p)\);
so \(t_p>1/2\Rightarrow a_p>1/3\) (at most \(h\le2\) such primes, since \(\sum a_p\le1\)),
and \(t_p\le1/2\Rightarrow t_p<\tfrac94a_p\Rightarrow f_p<\tfrac{45}{16}a_p\).
The case analysis \(h\in\{0,1,2\}\) gives
\(h+\tfrac{45}{16}(1-\tfrac h3)=\tfrac{h}{16}+\tfrac{45}{16}\), increasing in \(h\), so the
maximum is at \(h=2\): \(\;\boxed{47/16}\). **All three cases check.**
Then \(D_0+\rho T=\tfrac{47}{16}+\tfrac54\cdot\tfrac{541}{100}=\tfrac{97}{10}\) exactly, so
\((S_0-\tfrac{97}{10})^+\le\tfrac54(B-T)^+\) and (9)/(6) follows. **Correct.**
(Uses \(k\le m\) via \(\sum_p a_p=\log k/\log m\le1\); \(m\ge2\) is implicit, see G2.)

### 1.4 Lemma 4 — the new ingredient

\((7)\): the prefix before the last level has mass \(\le1\), so \(1<s_C\le1+\theta_C\le2\).

\((8)\) \(P_C\le m^{2/3}\). I audited the exponent budget \(\sum_{p\in C}\eta(t_p)\) by
**exhaustive enumeration of 14176 admissible carrier level-multisets** (all
\(\mathcal D\)-levels down to \(1/16\)); the maximum is **exactly \(2/3\)**, attained by the
two-prime carrier at level 1. Each of the manuscript's four cases is right:
\(\theta_C>1/2\Rightarrow|C|=2\), budget \(2/3\); no level \(>1/2\Rightarrow\frac49s_C\le\frac49\cdot\frac32=\frac23\);
one high level \(a\ge5/8\) with \(\theta_C\le3/8\Rightarrow\frac13+\frac49\cdot\frac34=\frac23\);
with \(3/8<\theta_C\le1/2\) the only \(\mathcal D\)-levels in \((3/8,1/2]\) are \(7/16,1/2\) and
\(5/8+7/16=17/16>1\) forces a single low level, budget \(\frac13+\frac29=\frac59\).
Hence \((9)\) \(P_Cq\le m^{2/3}m^{1/3}=m\) — task item (a) confirmed.

\((10)\) **The cofactor argument is correct and it does remove every small-\(m\)
proviso.** At a source point, \(\sum_{p\notin C}b_p(k)=B(k)-s_C>T-2=341/100>3\); since
\(b_p\le S_{0,p}\le\sum_j\alpha_{p,j}\le1\) (task item (e): yes, \(b_p\le1\) holds), at
least four distinct primes outside \(C\) divide \(k\), and they divide \(k/P_C\), so
\(k/P_C\ge2\cdot3\cdot5\cdot7=210\), whence \(\nu_C=\lfloor m/P_C\rfloor\ge k/P_C\ge210\) and
\(m/(P_C\nu_C)<1+1/\nu_C\le\Gamma=211/210\). No lower bound on \(m\) is used anywhere
else in the proof (task item (d)). *Slack check:* the window step needs only
\(\Gamma<315392/313650\), i.e. \(\nu_C\ge181\); 210 leaves room.

*(Aside, not needed: with threshold \(97/10<10\) the left-hand side also vanishes
outright for \(m<2\cdot3\cdots29=6469693230\), since then \(\omega(k)\le9\). The
cofactor argument is strictly stronger; noting the elementary fallback would give
a second independent route for a formalizer.)*

### 1.5 Lemma 5

\(k=P_Cu\), \(u\le\nu_C\), \(k\mapsto u\) injective, and for \(p\notin C\) the valuations at
\(k\) and \(u\) agree (\(P_C\) is supported on \(C\)'s primes) with \(b_p(k)\le\theta_C\).
So \(B(k)-T=\sum_{p\notin C}\min(b_p(u),\theta)-(T-s)\) exactly, and summing the
positive part over **all** \(u\le\nu_C\) dominates \(M_C\). Applying (2) with
\(u_p=\min(b_p,\theta)/\theta\in[0,1]\) and \(a=(T-s)/\theta\), then (1) with
\(\mathcal H(\min(b_p,\theta)/\theta)\le\mathcal H(B)/\theta\le H/\theta<H_*/\theta\), gives (11).
The range \(2\le r\le\lfloor a\rfloor+1\) always satisfies \(a\ge r-1\) (and
\(a\ge T-2=3.41\) always, so it is non-empty). **There is genuinely no \(\Gamma\) loss
here** — the moment sum runs over the true integer range \(u\le\nu_C\). **Correct.**

### 1.6 Lemma 6

*Negative moduli.* Increments of \(\min(b_p,\theta)\) sit at moduli \(q_p(t)\le m^{1/3}\)
(capping never enlarges the support, as the manuscript notes), so every negative
atom has modulus \(P_Cq\le m\). ✔

*The \((j,L)\) representation.* \(\theta=j/L\), \(j\in\{4,\dots,7\}\), \(L=2^h\), \(h\ge3\), is
unique because the intervals \([4/2^h,7/2^h]\) are disjoint. The claim "every
carrier level \(\ge\theta\) is a multiple of \(1/L\)" is **true and load-bearing** but
unproved in the text (G3): a level \(j'/2^{h'}\) with \(2^{h'}>L\) satisfies
\(j'/2^{h'}\le7/(2L)<4/L\le\theta\), so it is excluded; the survivors have
\(2^{h'}\le L\). Hence \(s=1+d/L\) with \(1\le d\le j\) by (7). ✔

*The counting polynomial (13).* I checked the injection claim in detail. A carrier
\(C\) with \(P_C\mid n\) has every \(p\in C\) among the \(N\) primes with \(b_p(n)\ge\theta\)
(because \(q_p(t_p)\mid P_C\mid n\) and \(t_p\ge\theta\)); the assignment
\(p\mapsto X^{Lt_p}\) (or \(1\)) has total degree \(Ls=L+d\) and uses \(X^{j}\) at least once
(the minimum \(\theta\) is attained). \(C\) is recovered from the assignment because
\(q_p(t)\) is a function of \((p,t)\) alone (G5 — unstated but true), so the map is
injective, and \(G^N-(G-X^j)^N\) counts exactly the degree-\((L+d)\) assignments using
\(X^j\) at least once. **I verified this independently by brute-force enumeration of
all level assignments** for \((j,L)\in\{(4,4),(4,8),(5,8),(6,8),(7,8),(4,16),(5,16),(7,16)\}\)
and \(0\le N\le5\), all \(d\): **zero mismatches** with the polynomial coefficients.

*(17)-type bounds.* \(U_C(n)\ge\theta(N-|C|)\ge N\theta-s\) (using \(|C|\theta\le s\)) and
\(B(n)-1\ge\max(s-1,N\theta-1)\) (using \(b_p(n)\ge t_p\) on \(C\), \(b_p(n)\ge\theta\) on the
\(N\) primes). Both correct.

*The \(N\)-range in (14).* The manuscript's one-liner "beyond the stated \(N\)-range
every numerator is zero" is correct: if \(N>\lfloor(K+1)L/j+1\rfloor\) then
\(N\theta>K+1+j/L\ge K+1+d/L\), so \(N\theta-1-d/L>K\) and the numerator vanishes. I
also confirmed this numerically by evaluating six extra values of \(N\) beyond
\(N_{\max}\) at **all 29 scales**: every one gave exactly \(0\).

*Task item (b) — is (15) valid at \(n\in I\) with \(n>m\)?* **Yes.** \(b_p,B,U_C\) are
globally defined functions of \(n\); the carriers are a fixed finite set determined
by source points \(k\le m\); nothing in the derivation of (15) uses \(n\le m\). And if
\(B(n)\le1\) no carrier divides \(n\), so \(F(n)=0\).

*Task item (g) — no bound is transported across \(k\le m\) / \(n\in I\).* The only
\(k\le m\) facts are (3) and the Lemma-3 pointwise bound, and both are used only on
the left-hand side. The carrier facts (7),(8),(10) are properties of \(C\), not of
\(n\). Clean.

### 1.7 / 1.8 Lemmas 7 and 8 — see §4 for my exact recomputation

Both derivations are correct. In Lemma 8 I re-derived
\(c_C\le\frac{\theta z}{e\log z}\bigl(e^{(z-1)H_*}z^{-(T-1)}\bigr)^{1/\theta}\) (the extra
factor \(z\) comes from \(s\le1+\theta\)); \(e\log(9/2)>4\) via
\((87/32)^3<(9/2)^2\) and \(e>8/3\); \(\mathcal G_j\ge G_{j,L}\) because the exponent
multiset of \(G_{j,L}\) embeds in \(\mathcal G_j\) — the level \(1\) contributes
\(L=4\cdot2^{h_0-2}\), supplied by the \(r\)-band with \(a=4\), \(r=h_0-2\) (G4, unstated);
the low/high split at \(y=N\theta-1\) vs \(h=4/3\); \(wF^{-w/\theta}\le\theta/(e\log F)\);
\(\frac{9}{8eKh\log F}\le\frac{9}{8\cdot\frac83\cdot\frac83\cdot\frac43\cdot\frac29}=\frac{2187}{4096}\)
(exact); and the geometric sums with \(1024/j\ge146\), \(2^r\ge r+1\),
\(\sum_r4^{-r}=4/3\). All correct.

### 1.9 Lemma 9

\(N_I(P_C)\ge\lfloor m/P_C\rfloor=\nu_C\); \(P_Cq\le m\Rightarrow N_I(P_Cq)\le m/(P_Cq)+1\le2m/(P_Cq)\);
\(\mathcal H(U_C)\le\mathcal H(B)\le H<H_*\). Hence
\(\sum_IF\ge\lambda\sum_Cc_C(\nu_C-2mH_*/(KP_C))\ge\lambda(1-2\Gamma H_*/K)L_B\).
**Exact:** \(\lambda(1-2\Gamma H_*/K)=\frac{51}{10}\cdot\frac{422670}{1720320}=\frac{718539}{573440}\),
and \(\frac{718539}{573440}-\frac54=\frac{1739}{573440}>0\). Both match the manuscript
to the digit. The closing chain
\(\sum_{k\le m}(S-\frac{97}{10})^+\overset{(3)}{=}\sum(S_0-\frac{97}{10})^+\overset{(6)}{\le}\frac54L_B\overset{(23)}{\le}\sum_IF\overset{(22)}{\le}\frac{969}{1000}\sum_I(B-1)^+\le\sum_I(S-1)^+\)
is valid (the last step because \(B\le S_0\le S\) globally and \(969/1000<1\)).
The degenerate cases (no hot points, dense branch, \(m=1\)) are covered.

---

## 2. Classical failure modes — explicit answers to the referral

| Probe | Answer |
|---|---|
| (a) every negative modulus \(\le m\)? | **Yes.** \(P_C\le m^{2/3}\) (audited exhaustively) and every atom of \(\min(b_p,\theta)\) has modulus \(q_p(t)\le m^{\eta(t)}\le m^{1/3}\). |
| (b) does (15) hold for \(n\in I\) with \(n>m\)? | **Yes** — see §1.6. All objects are globally defined; carriers are fixed; \(P_C\mid n\) counts are consistent. |
| (c) dense branch with \(c<17\) | **Fine.** \(\min(S_0,c)\ge\min(V,7)\) needs only \(S_0\ge V\) and \(c\ge7\); \(97/10>7\). |
| (d) small \(m\) | **No hidden assumption.** \(m=1\) trivial; for \(m\ge2\) the cofactor-\(\ge210\) argument gives \(\nu_C\ge210\) with no size condition. (Independent fallback: LHS \(=0\) for \(m<6469693230\).) I also confirmed by randomized synthetic simulation at \(m=10^{18},7\cdot10^{18},10^{20}\). |
| (e) hot points with \(<4\) external primes | **Impossible.** \(T-s_C\ge3.41>3\) and \(b_p\le1\) (which holds: \(b_p\le S_{0,p}\le\sum_j\alpha_{p,j}\le1\)). |
| (f) retained moduli \(\le m^{1/3}\) | **Yes.** \(\eta\le1/3\) everywhere: \(4t/9\le2/9<1/3\) on \(t\le1/2\), and \(1/3\) above. |
| (g) \(k\le m\) bounds used at \(n\in I\) or vice versa | **None found.** See §1.6. |

Additional probes I ran that the referral did not ask for, all clean:
does \(\eta\) being non-monotone across \(t=1/2\) break \(b_p\le t_p\)? (No — \(q_p(t)\mid n\)
forces \(t\le S_{0,p}(n)\).) Can a carrier be double-counted across scales? (No —
\(\theta_C\) is unique.) Is the "shortest prefix" enumeration in my hostile test
complete? (Yes — if \(s\le1+\theta\) then every proper sub-prefix has mass \(\le1\).)

---

## 3. Independent end-to-end tests (beyond arithmetic)

1. **Pointwise certificate test.** For arbitrary level profiles \((b_p(n))_p\) I
   enumerated by exact DP **every** carrier that can divide \(n\), gave each the
   largest coefficient the proof allows (\(c_C=\varepsilon_{\theta,s}\)), and formed
   \(\sum_Cc_C(1-U_C(n)/K)^+/(B(n)-1)^+\). Over **14,701 profiles** at level floors
   \(1/2,1/4,1/8,1/16\) the **worst observed ratio was \(0.097767\)** against the proved
   constant \(0.188871\) — a factor \(1.93\) of headroom. No profile came close to
   violating (15).
2. **Lemmas 3–4 on real synthetic atom systems.** I built genuine \(\alpha_{p,j}\)
   (30 primes, \(\sum_j\alpha_{p,j}\le1\)), the true \(S_0\) (atoms \(p^j\le m/Q\)), the true
   \(q_p(t)\), the retention rule tested by exact integer comparison
   \(q^{9\cdot\mathrm{den}(t)}\le m^{4\,\mathrm{num}(t)}\), the true \(b_p,B\), and the true carriers,
   at \(m=10^{18},7\cdot10^{18},10^{20}\). Over **2,476 hot points** in the shipped run
   (4,638 in a longer standalone run) every one of
   \(S_0\le\frac54B+\frac{47}{16}\), (7), \(P_C^3\le m^2\), \(P_C\mid k\), \(k/P_C\ge210\),
   \(\nu_C\ge210\), \(q^3\le m\) held. **Zero violations.**
3. **Counting polynomial** validated against brute-force assignment enumeration
   (§1.6): zero mismatches.
4. **Manuscript's sieve-rich fixture**, the one audit claim I could check without
   the missing script: at \(m=10^4,\ x=74769\) the count of integers coprime to
   \(2\cdot3\cdot5\cdot7\cdot11\cdot13\cdot17\) in the window is **1812** vs **1806** in \([1,10^4]\).
   Confirmed exactly.

---

## 4. My own exact values for every numerical constant

All computed by `referee_checks.py` from the definitions; every comparison is a
rational/integer comparison.

| Quantity | Manuscript's claim | **My exact value** | OK? |
|---|---|---|---|
| \(D_0+\rho T\) | \(97/10\) | \(\frac{47}{16}+\frac54\cdot\frac{541}{100}=\frac{97}{10}\) | ✔ |
| \((1-\tfrac1Q)H_*-\tfrac{H_*^8}{8!}-1\) | \(>0\) | \(\frac{9127710437643246821282611}{9748777809372369664830603264}=9.36287\ldots\times10^{-4}\) | ✔ |
| max adjacent \(\mathcal D\)-ratio | \(\le5/4\) | \(=5/4\) exactly | ✔ |
| \(\max_C\sum_{p\in C}\eta(t_p)\) | \(\le2/3\) | \(=2/3\) exactly (14176 multisets enumerated) | ✔ |
| \(A_{4,4}\) | \(<24680/10^6\) | \(0.024679502737730747\ldots\) | ✔ |
| \(\sum_jA_{j,8}\) | \(<128711/10^6\) | \(0.128710364873749\ldots\) | ✔ |
| \(\sum_jA_{j,16}\) | \(<25773/10^6\) | \(0.025772699015960\ldots\) | ✔ |
| \(\sum_jA_{j,32}\) | \(<5665/10^6\) | \(0.005664227647457\ldots\) | ✔ |
| \(\sum_jA_{j,64}\) | \(<1025/10^6\) | \(0.001024464798524\ldots\) | ✔ |
| \(\sum_jA_{j,128}\) | \(<150/10^6\) | \(0.000149656637103\ldots\) | ✔ |
| \(\sum_jA_{j,256}\) | \(<21/10^6\) | \(2.0675585145946\times10^{-5}\) | ✔ |
| \(\sum_jA_{j,512}\) | \(<3/10^6\) | \(2.4103362606152\times10^{-6}\) | ✔ |
| finite total (16) | \(<187/1000\); \(\in[186024001631,186024001632]/10^{12}\) | \(0.186024001631934\ldots\) (exact rational, 1692-digit numerator / 1693-digit denominator) | ✔ both |
| \(e<87/32\), \(e>8/3\) | — | \(e<2.7182818285\), \(e>2.7083\ldots\) (rigorous series bounds) | ✔ |
| \((87/32)^3<(9/2)^2\) | — | \(20.0959167\ldots<20.25\) | ✔ |
| \(\exp(\tfrac72H_*)\) | \(<133/4=33.25\) | \(<33.2288331950\ldots\) (Taylor + geometric remainder) | ✔ (0.065% margin) |
| \((133/4)^{100}\) vs \(a_0^{100}(9/2)^{441}\) | \(<\) | ratio \(=0.988079133\ldots<1\) | ✔ **(only 0.012% margin in the base)** |
| \(\mathcal G_4(583/1000)\le F_4\) | \(\le1.265182\) | \(\le1.265181886531\) | ✔ |
| \(\mathcal G_5(321/500)\le F_5\) | \(\le1.272712\) | \(\le1.272711973509\) | ✔ |
| \(\mathcal G_6(69/100)\le F_6\) | \(\le1.278827\) | \(\le1.278826623958\) | ✔ |
| \(\mathcal G_7(73/100)\le F_7\) | \(\le1.278274\) | \(\le1.278273002849\) | ✔ |
| \(a_0^3x_j^{-3j}F_j^{11}<1\) | \(<1\) | \(0.723086,\ 0.917351,\ \mathbf{0.998104}\ (j=6),\ 0.926004\) | ✔ **(\(j=6\) margin 0.19%)** |
| \((4/5)^4<(3/4)^3\) | — | \(256/625<27/64\) | ✔ |
| \(\frac{9}{8eKh\log F}\) | \(\le2187/4096\) | \(=2187/4096\) exactly under \(e>\frac83,\log F\ge\frac29\) | ✔ |
| tail low part | — | \(3.592442\times10^{-16}\) | — |
| tail high part | — | \(0.002846921822764\ldots\) | — |
| tail (21) | \(<3/1000\); \(\in[2846921822,2846921823]/10^{12}\) | \(0.0028469218227642\ldots\) | ✔ both |
| \(A_{4,4}+\Sigma+\text{tail}\) | \(\le19/100\) | \(0.188870923454698\ldots\) | ✔ (0.60% margin) |
| \(\lambda\cdot(\text{finite}+\text{tail})\) | \(\in[963241709618,963241709619]/10^{12}\), \(\le1\) | \(0.963241709618960\ldots\) | ✔ |
| \(\lambda(1-2\Gamma H_*/K)\) | \(718539/573440>5/4\) | \(=\frac{718539}{573440}=1.2530325753348\ldots\); excess \(=\frac{1739}{573440}\) | ✔ **(0.24% margin)** |

**Master slack.** Eliminating \(\lambda\), the whole proof closes iff
\(\text{CONST}\le\frac45\bigl(1-\frac{2\Gamma H_*}{K}\bigr)=\frac{14089}{71680}=0.196554129\ldots\).
We have \(\text{CONST}=0.188870923\ldots\), a **3.91% margin**, and the admissible
\(\lambda\)-window is \([5.087657,\,5.294621]\), comfortably containing \(\lambda=51/10\).
So the proof is not knife-edge overall, but three individual steps are (see G9).

---

## 5. Cross-check against the author's verifier

`exact_verifier.py` and `constants.json` were **not present** when I began; they
appeared in the directory mid-session. After finishing my own numbers I compared:

* My per-\(L\) sums equal the author's `finite_groups` **exactly** (Fraction equality,
  not float).
* My finite total equals the author's `finite_total` **exactly**: same 1692-digit
  numerator over the same 1693-digit denominator.
* My tail, \(\lambda\cdot(\text{finite}+\text{tail})\), and window coefficient match to the digit.

I also read the author's script for definitional drift and found none: its
`exponents(j,L)` reproduces \(\{Lt:t\in\mathcal D,\ t\ge j/L\}\) (its `a*D<=L` loop bound
plus the `v<=L` filter is exactly what admits the level-1 exponent \(L\) and nothing
spurious); `epsilon` is (11); `scale_bound` is (14) with \(N_{\max}=\lfloor(K+1)/\theta+1\rfloor\);
`retention_knapsack` is an honest exhaustive DP audit of (8). Its one omission is
that it never evaluates \(N>N_{\max}\); I did (and proved the bound analytically).

---

## 6. Complete list of gaps

None of G1–G6 is an error; each is a true statement used without proof. G7–G9 are
editorial/robustness.

* **G1 (Lemma 4, load-bearing).** "At least four distinct outside primes divide
  \(k/P_C\)" silently needs \(b_p(k)\le1\) for every \(p\). True
  (\(b_p\le S_{0,p}\le\sum_j\alpha_{p,j}\le1\)) but never stated at the point of use. This
  is the hinge of the entire small-\(m\) removal, so state it.
* **G2 (Lemma 3).** Two implicit steps: (i) \(p^{v_p(k)}\ge q_p(t_p)\) — from
  \(S_{0,p}(k)=f_p\ge t_p\) and minimality of \(q_p(t_p)\) — which is what turns
  non-retention into \(a_p>\eta(t_p)\); (ii) \(\log m>0\), i.e. \(m\ge2\). The \(m=1\)
  disposal sits at the end of Lemma 2, so the logic is fine, but say so.
* **G3 (Lemma 6).** "Every carrier level at least \(\theta\) is an integer multiple of
  \(1/L\)" is asserted without proof and is exactly what makes (13) well-formed.
  One line: a level \(j'/2^{h'}\) with \(2^{h'}>L\) is \(\le7/(2L)<4/L\le\theta\).
* **G4 (Lemma 8).** \(\mathcal G_j(x)\ge G_{j,L}(x)\) is used without justification. One
  line: the \(h=h_0\) band gives exponents \(a\in\{j,\dots,7\}\), the \(h<h_0\) bands give
  \(a2^r\) with \(r\ge1\), and level \(1\) gives \(L=4\cdot2^{h_0-2}\), i.e. \(a=4,r=h_0-2\);
  no exponent of \(G_{j,L}\) escapes \(\mathcal G_j\), and \(\mathcal G_j\) has distinct exponents.
* **G5 (Lemma 6).** "Carriers are determined by their level assignment" needs the
  remark that \(q_p(t)\) depends only on \((p,t)\); without it the injection into (13)
  is unjustified.
* **G6 (Lemma 1).** Two half-lines: the minimum of a coordinatewise-concave
  function on a box is at a vertex (iterate one coordinate at a time); and the
  \(h<r\) case is trivial *because* \(h\le r-1\le a\).
* **G7 (deliverables).** `adversarial_audit.py` and `audit.json` — cited in the
  "Adversarial audit and reproducible objects" section together with specific
  numbers (1024 binary valuation patterns, 729 prime-power patterns, 291600
  quarter-weight instances, CRT windows at \(m=10^4,10^5,10^6\)) — **are not in the
  directory.** Nothing in the proof depends on them, but as written the section
  asserts computations no reader can reproduce. Either ship the script or delete
  the section. (The one claim I could check independently, the sieve-rich window
  \(m=10^4,x=74769\) giving 1812 vs 1806, is **correct**.)
* **G8 (statement alignment).** The manuscript's corollary is
  \(g(n)\le\lfloor257n/10\rfloor\) (\(=9.7n+16n\), the §15 rounding route), not the
  \(g(n)\le12n\) in the referral. \(12n\) requires the "\(2n\) suffices when \(a_n\ge8n^3\)"
  branch of the transfer. Say which transfer is intended.
* **G9 (robustness warning, not a gap).** Three steps have sub-percent margins and
  **must never be re-derived in floating point**:
  \(\lambda(1-2\Gamma H_*/K)-\frac54=\frac{1739}{573440}\) (0.24%);
  \(a_0^3x_6^{-18}F_6^{11}=0.998104\) (0.19%);
  and \((133/4)/(9/2)^{441/100}<a_0\), which holds by only **0.012%** — the choice
  \(a_0=4377/100000\) is essentially optimal to four digits. The four
  \(\mathcal G_j(x_j)\le F_j\) comparisons hold with relative margins \(\sim10^{-6}\)–\(10^{-7}\).
  All are exact rational facts and all verified, but a formalization must carry
  the exact fractions.

---

## 7. Bottom line

The route table's three claims hold up: R1 (four-mantissa \(\mathcal D\) with maximal
adjacent ratio \(5/4\)) is exactly right and yields \(D_0=47/16\); R2 (mass-graded
moment order) is correctly implemented and the 29 finite scales reproduce to the
last digit; R3 (cofactor \(\ge210\)) genuinely removes the \(m\ge2^{48}\) proviso of the
accepted §15 argument, which is the substantive advance over the \(H_{17}\) proof.
The tail is a valid, convergent, exactly-checked majorant. The closing chain is
airtight and the overall slack is 3.91%.

I could not break it. **PASS**, with G1–G6 to be inserted before formalization and
G7 to be resolved before publication.

*Artifacts:* `referee_checks.py` (this directory) — my independent exact-arithmetic
verifier, 39 checks, all passing (runtime ~7 min). Run `python3 referee_checks.py`.
