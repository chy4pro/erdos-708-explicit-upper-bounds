# Q23 HARVEST — Erdős #708 round 3 (bounded regime), Qwen3.8-Max, chat c8ddef4f, harvested 2026-09-04 00:4x CDT via Copy+pbpaste (raw: erdos708_qwen_r3_raw.md, 24.9KB)
# VERDICT (dialogue audit): CORRECT — Theorem D generalises Theorem C. No T1/T2 for the full bounded regime; the linear-bound question is now confined to a_n ≤ n^{1+o(1)}.

## Theorem D. For every integer k ≥ 2: if a_n^{k−1} ≥ (kn)^{k+1} then some kn integers of the interval have product divisible by ∏A, i.e. g ≤ kn on that regime.
Corollaries: k=2: a_n ≥ 8n³ ⇒ 2n (Theorem C). k=3: a_n ≥ 9n² ⇒ 3n. k=4: a_n ≥ 1024^{1/3} n^{5/3} ⇒ 4n. For fixed δ > 0 and
k ≥ 1 + 2/δ with n^{δ(k−1)−2} ≥ k^{k+1}: a_n ≥ n^{1+δ} ⇒ g ≤ kn (linear). Explicit: a_n ≥ n² ⇒ g ≤ 17n for all n (k=4 for
n ≥ 1024; Theorem A for n ≤ 1023 gives ≤ 17n).

## Clean transcription (dialogue)
k-split lemma. Let k ≥ 1, integers H ≤ m, Q a multiset of integers > 1 with product A and A²H^{k+1} ≤ m^{k+1}. Then Q
splits into ≤ k pieces, each a singleton atom or a bin f (product of a sub-multiset) with fH ≤ m.
  Proof by induction on k. k=1: A²H² ≤ m² ⇒ AH ≤ m, one bin. k ≥ 2: (Case 1) some q with q²H > m: singleton q, and
  A' = A/q has A'²H^k = A²H^{k+1}/(q²H) < m^k — induction with k−1. (Case 2) all q²H ≤ m: greedy bin f: while f²H < m
  multiply in the next atom; invariant fH ≤ m because (fqH)² = (f²H)(q²H) < m²; if atoms are exhausted, one bin; else
  stop with f²H ≥ m, and A' = A/f has A'²H^k = A²H^{k+1}/(f²H) ≤ m^k — induction with k−1. ∎
Theorem D proof. H = kn; the hypothesis gives H ≤ m and a_i²H^{k+1} ≤ m²H^{k+1} ≤ m^{k+1} for every a_i, so each a_i's
atoms split into ≤ k pieces; ≤ kn = H pieces in all. Singletons with qH > m are "large" and are placed per prime
(distinct multiples for atoms of the same prime, sharing across primes allowed — our Lemma 2.3); every other piece is a
bin f with fH ≤ m, hence ≥ ⌊m/f⌋ ≥ H multiples in I, and ≤ H−1 forbidden positions (large positions plus earlier bins):
private multiples. |B| ≤ (large) + (bins) ≤ H = kn; divisibility as in the assembly lemma. ∎

## Machine verification (dialogue): problems/erdos708/es_bound4.py implements the k-split + construction; random instances
above the threshold for k = 2..6 (n ≤ 8, structured smooth sets included): 0 failures. Every k-split hypothesis and every
"fH ≤ m" is asserted inside the code.

## Consequence for the programme
The set of (n, a_n) without a linear bound is now a_n ≤ n^{1+o(1)} (precisely: for a_n ≥ n^{1+δ}, g ≤ (2/δ + O(1)) n).
The Erdős–Surányi extremal family has a_n ≈ n (ln n)², inside this regime. The global bound is unchanged
(the worst case a_n ≈ n·e^{√(ln n ln ln n)} still gives ≈ n√(ln n/ln ln n) by either method), but the structure of the
hard instances is now sharp: a_n barely larger than n, i.e. A is a dense subset of [2, a_n].
