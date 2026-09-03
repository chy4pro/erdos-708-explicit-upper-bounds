## Audit outcome

I do **not** have a complete audited proof of T1, T2, T3, or a verified T4 counterexample.  
The strongest statement below is an unconditional, fully elementary theorem which survives the G9/capacity audit. It extends the long-interval method from the \(8n^{3}\)-threshold to a family of explicit linear bounds, in particular lowering the threshold for a linear bound to a quadratic regime:

\[
m=a_n\ge 9n^2 \quad\Longrightarrow\quad g(n)\le 3n.
\]

More generally, for every integer \(k\ge 2\),

\[
m^{\,k-1}\ge (kn)^{\,k+1}
\quad\Longrightarrow\quad
g(n)\le kn.
\]

For \(k=2\) this recovers the proved long-interval case \(m\ge 8n^3\Rightarrow g(n)\le 2n\).  
For \(k=3\) it gives the new explicit quadratic threshold \(m\ge 9n^2\Rightarrow g(n)\le 3n\).

What remains for T1/T2 is precisely identified after the proof.

---

# 1. Notation and elementary counting fact

Let

\[
A=\{a_1<\dots<a_n\},\qquad m=a_n,\qquad P=\prod_{i=1}^n a_i,
\]
and let

\[
I=\{x+1,x+2,\dots,x+m\}
\]

be an arbitrary interval of length \(m\).

For each \(a_i\) and prime \(p\mid a_i\), write the **atom**

\[
q_p(a_i)=p^{v_p(a_i)}.
\]

Atoms belonging to the same \(a_i\) are pairwise coprime, and their product is \(a_i\).

We use only the following elementary interval-counting fact, which is G1 in the form needed here.

### Fact 1.1 — multiples in an interval

If \(1\le d\le m\), then any interval of length \(m\) contains at least \(\lfloor m/d\rfloor\) multiples of \(d\).

**Proof.** Among any \(m\) consecutive integers, the number of multiples of \(d\) is either \(\lfloor m/d\rfloor\) or \(\lceil m/d\rceil\). ∎

---

# 2. A splitting lemma with explicit integer inequalities

The following is the core combinatorial split. It is written entirely with integer inequalities, so it can be checked without real numbers or logarithms.

---

## Lemma 2.1 — \(k\split rule

Let \(k\ge 1\), and let \(H,m\) be positive integers with \(H\le m\).  
Let \(Q\) be a finite multiset of integers \(>1\), with product \(A=\prod_{q\in Q}q\). Suppose

\[
A^2 H^{k+1}\le m^{k+1}. \tag{2.1}
\]

Then \(Q\) can be partitioned into at most \(k\) pieces such that every piece is either:

1. a **singleton atom** \(q\in Q\), or  
2. a **bin** \(f\), the product of a nonempty submultiset of \(Q\), satisfying

\[
fH\le m. \tag{2.2}
\]

Moreover, such a partition is produced by the explicit algorithm in §7.

---

### Proof

We prove a slightly algorithmic statement by induction on \(k\).

#### Base case: \(k=1\)

Inequality (2.1) becomes

\[
A^2H^2\le m^2,
\]

so \(AH\le m\). Thus the whole multiset \(Q\) may be put into one bin \(f=A\), and (2.2) holds.

---

#### Induction step: \(k\ge 2\)

Assume (2.1).

There are two cases.

---

### Case 1: some atom is larger than \(\sqrt{m/H}\)

Equivalently, suppose there exists \(q\in Q\) such that

\[
q^2H>m. \tag{2.3}
\]

Make \(q\) a singleton piece. Let \(Q'=Q\setminus\{q\}\), and let \(A'=A/q\). Then

\[
(A')^2H^k
=
\frac{A^2H^{k+1}}{q^2H}
<
\frac{m^{k+1}}{m}
=
m^k.
\]

Since all quantities are integers, this gives

\[
(A')^2H^k\le m^k.
\]

This is exactly the induction hypothesis for \(k-1\), because for \(k-1\) the required inequality is

\[
(A')^2 H^{(k-1)+1}\le m^{(k-1)+1}.
\]

Thus the remaining atoms can be partitioned into at most \(k-1\) further pieces. Together with the singleton \(q\), we obtain at most \(k\) pieces.

---

### Case 2: all atoms are at most \(\sqrt{m/H}\)

Now suppose

\[
q^2H\le m \qquad\text{for every }q\in Q. \tag{2.4}
\]

We build one bin greedily.

Start with \(f=1\). While \(Q\) is nonempty and

\[
f^2H<m, \tag{2.5}
\]

remove any atom \(q\) from \(Q\) and replace \(f\) by \(fq\).

We claim that throughout this greedy construction,

\[
fH\le m. \tag{2.6}
\]

Initially \(f=1\), and \(H\le m\), so (2.6) holds. Suppose before adding \(q\) we have \(f^2H<m\), and \(q^2H\le m\) by (2.4). Then

\[
(fqH)^2
=
(f^2H)(q^2H)
<
m\cdot m
=
m^2.
\]

Therefore \(fqH<m\), hence certainly \(fqH\le m\). This proves the invariant.

There are two subcases.

---

#### Subcase 2a: the greedy process exhausts \(Q\)

Then the final \(f\) is the product of all remaining atoms, and by the invariant \(fH\le m\). We output one bin \(f\), and we are done.

---

#### Subcase 2b: the greedy process stops with \(Q\) nonempty

Then the stopping condition is

\[
f^2H\ge m. \tag{2.7}
\]

Output \(f\) as one bin. By the invariant, \(fH\le m\).

Let \(Q'=Q\setminus\{\text{atoms used in }f\}\), and let \(A'\) be the product of the remaining atoms. Since the original product was \(A\) and the bin product is \(f\), we have \(A'=A/f\). Using (2.1) and (2.7),

\[
(A')^2H^k
=
\frac{A^2H^{k+1}}{f^2H}
\le
\frac{m^{k+1}}{m}
=
m^k.
\]

Again this is the induction hypothesis for \(k-1\). Therefore the remaining atoms can be partitioned into at most \(k-1\) pieces. Adding the bin \(f\), we obtain at most \(k\) pieces.

This completes the induction and the proof of Lemma 2.1. ∎

---

# 3. Placing large singleton atoms

A singleton atom \(q=p^e\) with \(qH>m\) cannot be treated as a small bin. We place such atoms by the per-prime greedy argument underlying G2.

---

## Lemma 3.1 — per-prime placement of large atoms

Let \(\mathcal L\) be a finite multiset of prime powers \(q=p^e\), each \(q\le m\), obtained as atoms from distinct elements of \(A\) for each fixed prime \(p\). Thus for a fixed prime \(p\), no two atoms in \(\mathcal L_p\) come from the same \(a_i\).

Then one can assign to each \(q=p^e\in\mathcal L\) an element \(b_q\in I\) such that:

1. \(p^e\mid b_q\);
2. for each fixed prime \(p\), the assigned elements \(b_q\) for \(q\in\mathcal L_p\) are distinct;
3. elements assigned for different primes may coincide.

Consequently the set

\[
U=\{b_q:q\in\mathcal L\}
\]

satisfies

\[
|U|\le |\mathcal L|.
\]

---

### Proof

Fix a prime \(p\). Let the large \(p\)-atoms in \(\mathcal L_p\) be

\[
p^{e_1},p^{e_2},\dots,p^{e_s},
\]

ordered so that

\[
e_1\ge e_2\ge\dots\ge e_s.
\]

For each \(j\), the \(j\) atoms \(p^{e_1},\dots,p^{e_j}\) come from \(j\) distinct elements of \(A\), and all those elements are divisible by \(p^{e_j}\). Since these are \(j\) distinct integers \(\le m\), we have

\[
\left\lfloor \frac{m}{p^{e_j}}\right\rfloor\ge j.
\]

By Fact 1.1, the interval \(I\) contains at least \(j\) multiples of \(p^{e_j}\).

Now assign greedily in the order \(j=1,2,\dots,s\). At step \(j\), at least \(j\) elements of \(I\) are divisible by \(p^{e_j}\), and only \(j-1\) of them have already been used for this same prime \(p\). Hence an unused multiple remains. Choose one.

This gives distinct assignments for the same prime. Assignments for different primes are independent and may coincide. ∎

---

# 4. Placing small bins

A **bin** is an integer \(f\) satisfying \(fH\le m\). Such an \(f\) has at least \(H\) multiples in \(I\), and can therefore be placed greedily once the total number of demands is at most \(H\).

---

## Lemma 4.1 — greedy bin placement

Let \(H\) be a positive integer. Let \(U\subset I\) be a set of already occupied positions with

\[
|U|\le L.
\]

Let \(f_1,\dots,f_t\) be positive integers satisfying

\[
f_jH\le m \qquad (1\le j\le t),
\]

and suppose

\[
L+t\le H.
\]

Then there exist distinct elements

\[
b_1,\dots,b_t\in I\setminus U
\]

such that

\[
f_j\mid b_j
\]

for every \(j\).

---

### Proof

Proceed greedily. Suppose \(b_1,\dots,b_{j-1}\) have already been chosen. The set of forbidden positions before choosing \(b_j\) has size at most

\[
|U|+(j-1)\le L+j-1.
\]

Because \(f_jH\le m\), we have \(m/f_j\ge H\). By Fact 1.1, \(I\) contains at least

\[
\left\lfloor \frac{m}{f_j}\right\rfloor\ge H
\]

multiples of \(f_j\). Since

\[
L+j-1\le L+t-1\le H-1,
\]

not all multiples of \(f_j\) can be forbidden. Choose one unused multiple as \(b_j\). ∎

---

# 5. The main threshold theorem

We now combine the split rule with the two placement lemmas.

---

## Theorem 5.1 — explicit linear bounds in long-ish regimes

Let \(k\ge 2\) be an integer. Suppose

\[
m^{\,k-1}\ge (kn)^{\,k+1}. \tag{5.1}
\]

Then for every set \(A=\{a_1<\dots<a_n\}\) with largest element \(m\), and every interval \(I\) of length \(m\), there exists a subset \(B\subset I\) such that

\[
|B|\le kn
\]

and

\[
P=\prod_{i=1}^n a_i \mid \prod_{b\in B} b.
\]

Consequently,

\[
g(n)\le kn. \tag{5.2}
\]

---

### Proof

Put

\[
H=kn.
\]

Condition (5.1) is

\[
m^{k-1}\ge H^{k+1}. \tag{5.3}
\]

First observe that (5.3) implies \(H\le m\). Indeed, if \(H>m\), then

\[
H^{k+1}>m^{k+1}>m^{k-1},
\]

contradicting (5.3).

For each \(a_i\), we have \(a_i\le m\), so

\[
a_i^2H^{k+1}
\le
m^2H^{k+1}
\le
m^2m^{k-1}
=
m^{k+1}.
\]

Thus Lemma 2.1 applies to the atoms of \(a_i\) with parameter \(k\). Therefore the atoms of each \(a_i\) can be partitioned into at most \(k\) pieces, each piece being either:

- a singleton atom \(q\), or
- a bin \(f\) with \(fH\le m\).

Across all \(i\), the total number of pieces is at most

\[
kn=H.
\]

Now classify singleton atoms:

- if \(qH>m\), call \(q\) a **large atom**;
- if \(qH\le m\), treat \(q\) as a bin of product \(f=q\).

Let \(L\) be the number of large atoms, and let \(t\) be the number of bins after this reclassification. Then

\[
L+t\le H. \tag{5.4}
\]

---

### Large atoms

By Lemma 3.1, the large atoms can be assigned to elements of \(I\) such that same-prime atoms receive distinct elements, while different primes may coincide. Let \(U\subset I\) be the set of occupied large positions. Then

\[
|U|\le L. \tag{5.5}
\]

---

### Bins

Every bin \(f\) satisfies \(fH\le m\). By Lemma 4.1, using \(U\) as the forbidden set and using (5.4), all bins can be assigned distinct elements of \(I\setminus U\). Let the set of these bin positions be \(V\). Then

\[
|V|=t.
\]

Define

\[
B=U\cup V.
\]

Then

\[
|B|\le |U|+|V|\le L+t\le H=kn. \tag{5.6}
\]

---

### Divisibility

We check divisibility prime by prime.

Fix a prime \(p\). The \(p\)-part of \(P\) is the sum of the \(p\)-exponents of all atoms of all \(a_i\). Each such atom belongs to exactly one demand:

- either it is a large \(p\)-atom;
- or it is contained in a bin \(f\).

For large \(p\)-atoms, Lemma 3.1 assigned distinct elements of \(I\), each carrying the required \(p\)-valuation.

For bins containing a \(p\)-atom, Lemma 4.1 assigned distinct elements of \(I\setminus U\), each divisible by the whole bin and hence by the required \(p\)-power.

A large \(p\)-position and a bin position containing \(p\) cannot coincide, because bins were chosen outside \(U\). Two bin positions containing \(p\) are distinct. Two large \(p\)-positions are distinct. Therefore all contributions to the \(p\)-valuation are carried by distinct elements of \(B\), and their valuations add.

Thus for every prime \(p\),

\[
v_p\!\left(\prod_{b\in B}b\right)
\ge
v_p(P).
\]

Hence

\[
P\mid \prod_{b\in B}b.
\]

Together with (5.6), this proves the theorem. ∎

---

# 6. Explicit corollaries

All constants below are explicit.

---

## Corollary 6.1 — recovery of the long-interval case

Take \(k=2\). Condition (5.1) becomes

\[
m\ge (2n)^3=8n^3.
\]

Therefore

\[
m\ge 8n^3
\quad\Longrightarrow\quad
g(n)\le 2n.
\]

This is the already-proved long-interval case G6, recovered with an explicit split/assignment algorithm.

---

## Corollary 6.2 — quadratic threshold for a linear bound

Take \(k=3\). Condition (5.1) is

\[
m^2\ge (3n)^4=81n^4,
\]

i.e.

\[
m\ge 9n^2.
\]

Therefore

\[
m\ge 9n^2
\quad\Longrightarrow\quad
g(n)\le 3n.
\]

This gives an explicit quadratic threshold for a linear bound.

---

## Corollary 6.3 — a \(5/3\)-threshold

Take \(k=4\). Condition (5.1) is

\[
m^3\ge (4n)^5=1024n^5.
\]

Equivalently,

\[
m\ge \lceil 1024^{1/3}n^{5/3}\rceil.
\]

Then

\[
g(n)\le 4n.
\]

---

## Corollary 6.4 — any fixed superlinear exponent gives a linear bound

Let \(\delta>0\). Choose an integer \(k\ge 2\) such that

\[
\delta(k-1)>2.
\]

For example,

\[
k=\left\lceil 1+\frac{2}{\delta}\right\rceil+1
\]

works.

If

\[
m\ge n^{1+\delta}
\]

and

\[
n^{\delta(k-1)-2}\ge k^{k+1},
\]

then (5.1) holds, and therefore

\[
g(n)\le kn.
\]

Thus for every fixed \(\delta>0\), there is an explicit constant \(k(\delta)\) such that for all sufficiently large \(n\),

\[
m\ge n^{1+\delta}
\quad\Longrightarrow\quad
g(n)\le k(\delta)n.
\]

---

## Corollary 6.5 — an explicit linear bound for \(m\ge n^2\)

For all \(n\) and all \(m\ge n^2\),

\[
g(n)\le 17n.
\]

### Proof

If \(n\ge 1024\), then \(m\ge n^2\) implies

\[
m^3\ge n^6\ge 1024n^5=(4n)^5,
\]

so Corollary 6.3 gives \(g(n)\le 4n\).

If \(1\le n\le 1023\), use G4. Here

\[
r=\lceil \log_2(2n)\rceil\le 11,
\]
and
\[
s=\lceil \log_2 r\rceil\le 4.
\]

Thus G4 gives

\[
g(n)\le n(r+s+2)\le 17n.
\]

Therefore in all cases \(m\ge n^2\) implies \(g(n)\le 17n\). ∎

---

# 7. Machine-checkable algorithms

The following algorithms are written using only integer arithmetic. They implement the proof exactly.

---

## 7.1. Split rule

Input: the list \(Q\) of prime-power atoms of one integer \(a\), the allowed number of pieces \(k\), and the global parameters \(H,m\).

Output: a list of demands. A demand is either:

- `large_atom(q)`, meaning \(qH>m\);
- `bin(f)`, meaning \(fH\le m\).

The algorithm asserts its own invariants. If the theorem hypothesis holds, no assertion fails.

```python
def split_atoms(Q, H, m, k):
    """
    Q : list of prime-power atoms of one a_i
    H : allowed number of demands, e.g. k*n in the theorem
    m : a_n
    k : maximum number of pieces for this a_i

    Returns a list of demands:
       ('large', q)  if q*H > m
       ('bin', f)    if f*H <= m
    """
    Q = list(Q)
    demands = []

    while Q:
        assert k >= 1

        if k == 1:
            f = 1
            for q in Q:
                f *= q
            assert f * H <= m
            demands.append(('bin', f))
            return demands

        # Case 1: some atom q is larger than sqrt(m/H)
        idx = None
        for i, q in enumerate(Q):
            if q * q * H > m:
                idx = i
                break

        if idx is not None:
            q = Q.pop(idx)

            if q * H > m:
                demands.append(('large', q))
            else:
                demands.append(('bin', q))

            k -= 1
            continue

        # Case 2: all remaining atoms satisfy q^2 H <= m
        f = 1

        while Q and f * f * H < m:
            q = Q.pop()          # arbitrary choice is valid
            f *= q
            assert f * H <= m

        demands.append(('bin', f))

        if f * f * H < m:
            # The whole remainder was below sqrt(m/H).
            # Since Q is now empty, we are done.
            assert not Q
            return demands

        k -= 1

    return demands
```

### Explanation of the integer tests

The threshold \(C=m/H\) is never computed.

- \(q>\sqrt C\) is tested as

\[
q^2H>m.
\]

- \(q>C\) is tested as

\[
qH>m.
\]

- \(f\le C\) is tested as

\[
fH\le m.
\]

Thus the split rule is exact over integers.

---

## 7.2. Assignment rule

Input:

- interval \(I=\{x+1,\dots,x+m\}\);
- large atoms, each as a pair \((p,e)\), representing \(p^e\);
- bins \(f_1,\dots,f_t\), each satisfying \(f_jH\le m\).

Output: a set \(B\subset I\) of size at most \(H\).

```python
def assign(I, large_atoms, bins):
    """
    I          : iterable of interval elements
    large_atoms: list of pairs (p,e), representing p^e
    bins       : list of integers f with f*H <= m

    Returns B, a set of interval elements.
    """

    B = set()

    # Step 1: place large atoms, separately for each prime.
    # For a fixed prime p, assigned elements must be distinct.
    # Across different primes, coincidence is allowed.

    large_by_prime = {}
    for p, e in large_atoms:
        large_by_prime.setdefault(p, []).append(e)

    for p, exps in large_by_prime.items():
        exps.sort(reverse=True)
        used_for_this_prime = set()

        for e in exps:
            pe = p ** e

            chosen = None
            for b in I:
                if b % pe == 0 and b not in used_for_this_prime:
                    chosen = b
                    break

            assert chosen is not None

            used_for_this_prime.add(chosen)
            B.add(chosen)

    # Step 2: place bins, avoiding all large positions and previous bins.
    for f in bins:
        chosen = None
        for b in I:
            if b % f == 0 and b not in B:
                chosen = b
                break

        assert chosen is not None
        B.add(chosen)

    return B
```

### Why this is safe

- For the same prime, large atoms receive distinct interval elements, so their \(p\)-valuations add.
- For different primes, large atoms may land on the same element. This is safe because valuations for different primes are independent.
- Bins avoid all large positions and avoid each other, so their contributions are additive.
- If a bin contains several primes, the chosen element is divisible by the whole bin, hence covers all those prime powers at once.

---

# 8. Exact remaining gap

The theorem above proves the desired conclusion whenever the per-a splitting condition holds. For \(g(n)\le 2n\) we need \(k=2\), i.e. \(H=2n\). The condition becomes

\[
m\ge (2n)^3=8n^3.
\]

Equivalently, with \(H=2n\), Lemma 2.1 applies to every \(a_i\) whenever

\[
a_i^2H^3\le m^3
\]

for all \(i\), which is guaranteed by \(m\ge 8n^3\).

For the bounded regime \(m<8n^3\), the exact missing lemma is the following.

---

## Missing Lemma ML(2)

Let \(H=2n\). For every \(A\) with \(m<8n^3\), there exists a collection of at most \(H\) demands covering all atoms of all \(a_i\), such that:

1. every demand is either a singleton prime-power atom or an integer \(f\);
2. every non-singleton demand satisfies \(fH\le m\), or is otherwise placed by a verified sharing argument;
3. for each prime \(p\), the demands containing \(p\)-powers can be assigned distinct interval elements with the required \(p\)-valuation;
4. all bins can be assigned outside the large-atom positions;
5. the resulting set \(B\subset I\) has size at most \(H\) and satisfies \(P\mid \prod_{b\in B}b\).

Lemma 2.1 proves ML(2) when \(m\ge 8n^3\). The bounded regime requires a replacement for the per-a split rule that allows **global sharing of medium atoms belonging to different \(a_i\)**. This is exactly the obstruction identified in G8.

The minimal local obstruction to the per-a split rule is an integer \(a_i\) with three atoms

\[
q_1,q_2,q_3
\]

such that

\[
q_j^2H>m
\]

and

\[
q_iq_jH>m\qquad(i\ne j).
\]

Then no two of these atoms can lie in the same bin of product \(f\le m/H\), so a per-a two-piece split is impossible. Any proof of T1 must either show that such local obstructions cannot occur in a globally dangerous configuration, or must share their atoms across different \(a_i\).

For a general constant \(C\), the same theorem gives \(g(n)\le Cn\) whenever

\[
m^{C-1}\ge (Cn)^{C+1}.
\]

The remaining gap for a global linear bound is the near-linear regime

\[
Cn<m<(Cn)^{(C+1)/(C-1)}.
\]

---

# 9. Machine-checkable artefacts

## 9.1. Exact DP verifier for finite instances

For a concrete instance \((A,x)\) and a proposed bound \(G\), the exact minimum can be checked by dynamic programming over capped valuation vectors.

Let the primes dividing \(P\) be \(p_1,\dots,p_r\), and let

\[
T_j=v_{p_j}(P).
\]

For each \(b\in I\), define the capped vector

\[
v(b)=\bigl(\min(v_{p_1}(b),T_1),\dots,\min(v_{p_r}(b),T_r)\bigr).
\]

A subset \(B\) works iff the componentwise capped sum of the vectors \(v(b)\), \(b\in B\), equals \((T_1,\dots,T_r)\).

A DP can maintain reachable capped vectors using at most \(c\) elements, for \(0\le c\le G\). This is finite and exact for any concrete instance.

---

## 9.2. A concrete stress instance for the naive two-split rule

This instance is not claimed to be a counterexample to \(g(n)\le 2n\). It is a small explicit instance where the per-a two-split rule necessarily fails, and therefore it is a useful DP test case for any attempted proof of S.

Take

\[
n=8,\qquad x=0,
\]
and

\[
A=\{2,4,8,16,32,64,128,1287\}.
\]

Then

\[
m=1287,
\]
and

\[
8n^3=4096,
\]

so this lies inside the bounded regime.

Now

\[
1287=3^2\cdot 11\cdot 13,
\]

so its atoms are

\[
9,\ 11,\ 13.
\]

For \(H=2n=16\), we have

\[
C=\frac{m}{H}=\frac{1287}{16}=80.4375.
\]

Check:

\[
9^2\cdot 16=1296>1287,
\]
\[
11^2\cdot 16=1936>1287,
\]
\[
13^2\cdot 16=2704>1287.
\]

Thus each atom is larger than \(\sqrt C\). Also,

\[
9\cdot 11\cdot 16=1584>1287,
\]
\[
9\cdot 13\cdot 16=1872>1287,
\]
\[
11\cdot 13\cdot 16=2288>1287.
\]

Thus no two of these atoms can be placed in the same bin of product \(f\le C\). Therefore any per-a split into at most two bins fails for \(1287\).

The exact DP question is:

\[
\text{Does there exist }B\subset\{1,\dots,1287\},\ |B|\le 16,
\]
such that

\[
\prod_{a\in A}a \mid \prod_{b\in B}b?
\]

If the DP returns “no”, this would be a T4 counterexample. Under the working assumption that S is true in the bounded regime, the DP should return “yes”.

---

## 9.3. Parametric stress family

A natural family to search for T4 counterexamples is obtained by forcing many integers \(a_i\) to have three medium atoms.

Choose a parameter \(Y\), and choose disjoint triples of prime powers

\[
(q_{i,1},q_{i,2},q_{i,3})
\]

such that, for a desired \(H=2n\),

\[
q_{i,j}^2H>m
\]

and

\[
q_{i,j}q_{i,k}H>m\qquad(j\ne k),
\]

but

\[
q_{i,1}q_{i,2}q_{i,3}\le m.
\]

Let

\[
a_i=q_{i,1}q_{i,2}q_{i,3}.
\]

Add filler integers if necessary to reach size \(n\) and make \(a_n=m\). Such families stress exactly the gap between per-a splitting and global sharing.

---

# 10. What a Lean formalisation needs

A Lean formalisation of the proved theorem needs the following components.

## 10.1. Basic objects

- A finite strictly increasing sequence \(A\) of natural numbers \(>1\).
- \(m=\max A\).
- An interval \(I=\{x+1,\dots,x+m\}\) as a `Finset ℕ`.
- Prime-power atoms \(q_p(a)=p^{v_p(a)}\).

## 10.2. Integer interval counting

Prove:

```lean
lemma multiples_in_interval_lower_bound
  (d : ℕ) (hd : 1 ≤ d) (hdm : d ≤ m) :
  H ≤ (I.filter (λ b, d ∣ b)).card
```

under the hypothesis `d * H ≤ m`.

This is the only external counting fact needed.

## 10.3. Splitting lemma

Formalise Lemma 2.1 as a recursive function on multisets of atoms, with integer invariant:

```lean
A^2 * H^(k+1) ≤ m^(k+1)
```

and output demands of two types:

```lean
inductive Demand
| large : ℕ → Demand
| bin   : ℕ → Demand
```

with proofs:

- number of demands \(\le k\);
- every bin demand \(f\) satisfies `f * H ≤ m`;
- every large demand \(q\) satisfies `q * H > m`;
- the product of all atoms is preserved.

## 10.4. Large-atom placement

For each prime \(p\), formalise the greedy assignment of distinct multiples in \(I\), using the fact that the \(j\)-th largest exponent has at least \(j\) multiples in \(I\).

Required statement:

```lean
∀ p, ∃ assign_p : LargeAtom_p → I,
  (∀ q, p^(exponent q) ∣ assign_p q) ∧
  injective assign_p
```

Across different primes, do not require injectivity.

## 10.5. Bin placement

Formalise Lemma 4.1 as a finite greedy choice:

```lean
∀ f, f * H ≤ m →
  H ≤ (I.filter (λ b, f ∣ b)).card
```

and then choose distinct bin positions outside the large-position set.

## 10.6. Divisibility proof

Prove prime-by-prime:

```lean
∀ p,
  v_p (∏ b in B, b) ≥ v_p (∏ a in A, a)
```

using distinctness of assigned positions for demands involving the same prime.

## 10.7. Cardinality bound

Prove:

```lean
B.card ≤ H
```

using

```lean
B.card ≤ large_positions.card + bin_positions.card
       ≤ number_of_large_demands + number_of_bin_demands
       ≤ H.
```

---

# 11. Summary of what is proved and what remains

### Proved rigorously

For every integer \(k\ge 2\),

\[
m^{k-1}\ge (kn)^{k+1}
\quad\Longrightarrow\quad
g(n)\le kn.
\]

In particular:

\[
m\ge 8n^3 \Rightarrow g(n)\le 2n,
\]

\[
m\ge 9n^2 \Rightarrow g(n)\le 3n,
\]

\[
m^3\ge 1024n^5 \Rightarrow g(n)\le 4n,
\]

and

\[
m\ge n^2 \Rightarrow g(n)\le 17n.
\]

All constants are explicit. The split rule and assignment rule are given as implementable integer algorithms.

### Remaining exact gap

For T1, one must prove the missing lemma ML(2) for \(H=2n\) and all \(m<8n^3\). Equivalently, one must replace the per-a splitting rule by a global assignment that allows medium atoms from different \(a_i\) to share interval elements without violating same-prime capacity.

For T2 with an absolute constant \(C\), the theorem gives \(g(n)\le Cn\) above the explicit threshold

\[
m^{C-1}\ge (Cn)^{C+1}.
\]

The remaining gap is the near-linear regime

\[
Cn<m<(Cn)^{(C+1)/(C-1)},
\]

where the current bin-packing bound can demand more than \(Cn\) elements and the G5 bound is not yet linear.