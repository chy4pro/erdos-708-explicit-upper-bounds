# Explicit upper bounds for the Erdős–Surányi function g(n) — Erdős Problem #708

**Result.** Let g(n) be the least g such that for every set {a_1 < … < a_n} of integers > 1 and every x ≥ 0, some
(at most) g of the integers x+1, …, x+a_n have product divisible by a_1⋯a_n (Erdős–Surányi 1959; Erdős asked, for
$100, whether g(n) ≤ (2+o(1))n or even 2n — [erdosproblems.com/708](https://www.erdosproblems.com/708)). We prove

* g(n) ≤ n(⌈log₂ 2n⌉ + ⌈log₂⌈log₂ 2n⌉⌉ + 2) for n ≥ 2  (e.g. g(10) ≤ 100, g(100) ≤ 1300);
* g(n) ≤ ⌈48 n √((81 + ln n)/ln(81 + ln n))⌉ for n ≥ 1, and g(n) ≤ (2 + o(1)) n √(ln n / ln ln n);
* if a_n ≥ 8n³ then 2n integers always suffice (the conjecture holds for long intervals; Erdős's question reduces to a_n < 8n³);
* (v2) for every integer k ≥ 2, kn integers suffice whenever a_n ≤ kn or a_n^{k−1} ≥ (kn)^{k+1} — e.g. a_n ≥ 9n² ⇒ 3n, a_n ≥ n² ⇒ 12n, a_n ≥ n^{7/4} ⇒ 15n; for every fixed δ > 0 a linear bound holds when a_n ≥ n^{1+δ}.
* (v3) a **conditional linear bound**: a single inequality about additive functions on intervals (the "hinge inequality",
  Conjecture 7.1: Σ_{k≤m}(w(k)−2)⁺ ≤ Σ_{b∈I}(w(b)−1)⁺ for w = Σ_p z_p v_p, 0 ≤ z_p ≤ 1) implies g(n) ≤ 18n, by LP duality
  and rounding. The inequality is proved for a single prime and in an explicit large-parameter regime, has no counterexample
  among 2.1·10⁶ instances, and three natural strengthenings of it are shown to be **false** with explicit certificates
  (windows of length up to 10⁶ containing more integers free of small primes than [1,m]; Hensley–Richards). It remains open.
* (v4) **counting certificates and the 0/1 case**: the hinge inequality follows from the two-sided count ⌊m/d⌋ ≤ N_I(d) ≤ ⌊m/d⌋+1 of
  multiples alone via LP duality in every instance we could compute (fractional weights, m ≤ 200; 0/1 weights, all primes ≤ m, m ≤ 1000);
  an explicit certificate family proves the 0/1 case for every m ≤ 10⁷ (and, by the asymptotics, up to about 10⁴² but not beyond);
  and **Theorem A**: for 0/1 weights the hinge inequality holds for ALL m with the threshold 2 replaced by c*(m) ≤ 20 ln ln m
  (an explicit, elementary sieve lemma). Fractional weights — the case the linear bound needs — reduce to an explicit integer statement.
* (v5) **g(n) = O(n ln ln n)**: for arbitrary weights the hinge inequality holds for every m with threshold c_m = 1 + 149e·ln(1+ln m)
  (a weighted sieve lemma: random thinning, a k-th order two-term Bonferroni inequality, an exact dyadic encoding of fractional valuations,
  and the two-sided count of multiples in an interval); through the LP duality this gives **g(n) ≤ (17 + 149e·ln(1+ln(8n³)))·n**,
  the first bound linear up to a ln ln n factor. The constant ≈ 405 is poor (the bound beats the √ bound only for astronomically large n);
  the conjectured 2n, and the threshold-2 hinge inequality that would give 18n, remain open.
* (v6) **Improved constant**: the hinge inequality holds for all weights and all m ≥ 3 with threshold 20 ln ln m (geometric levels of
  ratio 51/50 + a factorial inversion with arbitrary gain, so the ln ln L baseline is paid once); hence g(n) ≤ (16 + 20 ln ln(8n³))·n for all n,
  below the √ bound for every n and below the log bound for n ≳ 10^35. Budget verified independently (`src/r9_budget_check.py`: sup (B_L+3)/h = 17.90 < 19.24).
* (v7) **Correction (Section 8)**: the affine certificate c₁ = −1, c_{p^j} = z_p gives Σ_I (w−1)⁺ ≥ Σ_{k≤m} w(k) − m for every weight and
  window, so the hinge inequality is trivial unless low-weight integers dominate [1,m]; for 0/1 weights with P = all primes ≤ m it holds for
  every m (V − W = m − 2 − Π(m) ≥ 0). The earlier sentence 'whether certificates exist for every m is open' was wrong for the full set of primes;
  the anchor family remains needed for prime sets without small primes (P = [53,653], m = 10⁸: affine bound −52,364,805 < 0). The quoted LP
  values 223.5/407.4/907 are values of the programme restricted to pairs and triples (`src/graph_cert.py`); see `src/affine_check.py`. No theorem is affected.
* (v8) **0/1 case with an absolute threshold** (Section 11): for every finite prime set P, every m and every window of m consecutive
  integers, Σ_{k≤m}(Ω_P(k)−4)⁺ ≤ Σ_{b∈I}(Ω_P(b)−1)⁺ — two explicit counting certificates (pair–triple with coefficients 11/21, −1/7 on the primes
  ≤ m^{1/3} when their harmonic mass η ≤ 2; the affine certificate when η > 2). Replaces the 20 ln ln m of Theorem A by 4. Does not improve
  the bound on g(n) (fractional weights needed; naive threshold averaging fails). Independent referee: `src/referee_c4_cert.py`, `src/referee_c4_scan.py`.
* (v9) **Fractional case: reduction to a sparse core** (Section 12): with prime-power atoms, the hinge inequality holds with threshold 65
  whenever the atoms of modulus ≤ m/64 have mean ≥ 17/16 (dense branch); hence g(n) ≤ 81n follows from a 'sparse core' statement (mean < 17/16),
  which is vacuous below the 65th primorial (≈ 6·10^127), has left side ≤ 6.24·10^−90·m, and remains OPEN. Projective-plane configurations show
  that the two-sided interval counts alone (without the values ⌊m/d⌋) cannot prove it. Referee scripts: `src/referee_fractional_check*.py`.
* (v10) **g(n) ≤ 81n for all n ≤ 10^962** (Section 12, 'arithmetic shadows'): a single k ≤ m with atom mass > 64 yields 32 pairwise coprime
  moduli D_r | k (group mass > 4/3) and the nonnegative certificate c_{D_r} = 1/3, giving Σ_I(S_0−1)⁺ ≥ (32/3)(1−6^−31) m/k^{1/32}; with the
  factorial-moment bound this proves the sparse core for 4096 < m ≤ 10^2887 (exact range 10^2887.45), hence the hinge inequality with threshold 65
  for all m ≤ 10^2887 and g(n) ≤ 81n for n ≤ 10^962. Beyond that only O(n ln ln n) is known. Referee scripts: `src/referee_shadow_*.py`.
* (repo-only, 2026-09-05; not yet a Zenodo version) Two items verified by an independent referee run on the round-13 transcript (`run24_*`):
  (a) the sparse-core range extends to 4096 < m ≤ 10^2942 (a mean bifurcation on top of the shadow theorem), hence g(n) ≤ 81n for n ≤ 10^980;
  (b) a wording gap in the packing lemma (the odd large item must be placed first in its group) — fixed in `paper/main.tex`. The transcript's
  claim that window-independent certificates refute the multi-point route only concerns certificates feasible at every integer; the
  certificate principle needs feasibility on the window only, and window-adapted certificates beat the transcript's barrier family
  (referee scripts `src/referee_r13_*.py`). These will enter the paper with its next (final) version.
* (repo-only, 2026-09-05; not yet a Zenodo version) Round 14 (`run26_*`, refereed): a barrier for window-adapted divisor certificates.
  On the reflected windows I = (m! − m, m!] with P a set of n primes (weights α_{p,1} = 1) every certificate c_D ≥ 0 feasible on the whole
  window has value at most (n − 1)⌊m/(p₁p₂)⌋, while L_64 ≥ C(n, 65); an explicit infinite family (n_t = 2^{2^t}, t ≥ 11) has W/L → 0, and an
  exact finite witness for threshold 2 uses the 425 primes in [3299, 6899] with m = 326,275,048,607 (12,703,040 < 12,704,100). The
  sparse-core inequality itself holds on these windows (R ≥ L + 63 by reflection). The referee further showed that the certificate cone
  survives if the (few) hot points are excluded from feasibility (value 64·L on the same family) — the open question is now that
  hot-set-excluded LP. Check script: `src/referee_r14_check.py`.
* (repo-only, 2026-09-05; not yet a Zenodo version) Round 15 (`run27_*`, Claude Fable, refereed): (a) the sparse-core inequality (SC_64) holds for
  EVERY m when all atom weights are 0 or 1 (a companion of the paper's threshold-4 theorem; hence any counterexample must use fractional
  weights); (b) an exact identity reduces the hot-set-excluded certificate question to one inequality (NC) about crowded window points;
  (c) if every window point has S₀ ≤ S*(m) ≈ 1.4·10^20 (m ≤ 10^3000; S₀ ≤ 262 for single-atom-per-prime systems, for all m) then R ≥ 2L —
  the first positive (SC_64) statement with no cap on m and no 0/1 restriction. Referee amendments to §6 are recorded in the referee file.
  These will enter the paper with its next (final) version. Scripts: `src/run27/`.

To our knowledge these are the first upper bounds for g(n) depending on n alone (none is recorded in Erdős's 1992
paper or on the problem's page; the 1959 original, in Hungarian, was not accessible to us). The conjectured 2n is
**not** proved; the problem remains open. We also record g(4) ≥ 5 and g(5) ≥ 6 (exact computation).

**Paper.** `paper/main.pdf` (source `paper/main.tex`) — always the current version. Archived on Zenodo as ONE record under the concept DOI [10.5281/zenodo.22267395](https://doi.org/10.5281/zenodo.22267395), which resolves to the latest version; the version history (v1–v10) is the record's changelog, and earlier versions are marked as superseded.

## Verification
* `src/gn_dp.py` — exact minimum |B| for a concrete (A, x) by dynamic programming over capped valuation vectors; reproduces
  the Erdős–Surányi lower-bound instances (l=3 → 4, l=4 → 6) and the g(4) ≥ 5, g(5) ≥ 6 instances.
* `src/es_bound.py` — checks every numerical inequality of the explicit √-bound over a grid of (n, N), and implements
  the construction (large atoms / merged bins / assembly), verifying divisibility, range and |B| ≤ K on 1.4·10⁶ random instances.
* `src/es_bound2.py` — implements the log-bound construction (per-prime greedy, next-fit bins, globally distinct bin
  representatives), checks the budget conditions (B1), (B2) for n = 2..1999 and larger n, and verifies the output on
  2·10⁶ random instances.
* `src/es_bound3.py` — implements the long-interval construction (a_n ≥ 8n³ ⇒ 2n elements) and verifies it on 2.4·10⁵ random instances.
* `src/es_bound4.py` — implements the k-split construction (Theorem D) and verifies it for k = 2..6 on 4.3·10⁶ random instances; `src/linear_constants.py` computes the best linear constants per exponent.
* `src/split_assign.py`, `src/search_S_omega3.py` — exact feasibility test for the split-assignment conjecture of the paper
  (§5); no counterexample among >10⁶ random instances.

* (v3) `src/hinge_test2.py`, `src/pq_test.py`, `src/layer_test.py`, `src/lap_test.py` — adversarial random tests of the hinge inequality,
  of the per-prime-power inequality (7.5) and of two candidate strengthenings; `src/hr_construct.py`, `src/hr_tail21.py`, `src/adv_window*.py`
  build the dense windows of Proposition 7.7 by a centred sieve + CRT and verify the failures from x; `src/bigwindow_eval.py`, `src/lap_window.py`
  evaluate all inequalities on a stored window. The windows themselves are in `certificates/` (see `certificates/README.md`).

* (v4) `src/abstract_count_lp2.py`, `src/abstract_count_cert.py` — the counting-certificate LP for general weights (needs scipy);
  `src/graph_cert.py` — 0/1 weights, pairs/triples with constraint generation (needs scipy); `src/cert_family.py` — the explicit family C_r;
  `src/thmA_check.py` — numerical checks of Theorem A and its sieve lemma; `src/af_flow_test.py` — flow relaxation of the forest-transfer statement.

Run: `python3 src/es_bound.py`, `python3 src/es_bound2.py`, `python3 src/gn_dp.py 3`.

## Provenance (honest)
The proofs of the two bounds were produced by OpenAI GPT-5.6 (Pro effort, web interface) in two independent runs (90 and 26 minutes), and the long-interval theorem and its k-parameter generalisation (v2) by Qwen3.8-Max (web interface, two runs),
inside an autonomous pipeline coordinated by Claude Fable 5.1 (Anthropic), which selected the problem, pinned the
statement to Erdős's text, verified the lower-bound construction by exact computation, re-derived every step of both
proofs, commissioned independent referee runs (four Claude Opus 5 agents in fresh contexts, one per theorem; a Qwen3.8-Max adversarial
audit), wrote the verification scripts and drafted the paper. Two earlier engine attempts (Qwen3.8-Max, in a dual-response chat) produced
invalid proofs of stronger claims (3n, 2n) — they double-counted shared interval elements or assumed a distinct-multiples
matching that van Doorn–Li–Tang (arXiv:2603.28636) show to be false; they are kept in `engine_transcripts/` as a record.
(v3) The LP reduction of a linear bound to the hinge inequality is due to a GPT-5.6 Pro run (4 h); the matching and forest reformulations
and the large-parameter case to two further Pro runs (2.4 h and 3.7 h); the one-prime case to Qwen3.8-Max; the per-prime-power sufficient
condition, the counterexample constructions and all verification code to the coordinating Claude Fable 5.1 seat, which also refuted the two
reduction targets and the Laplace candidate proposed by the engines. Transcripts: `engine_transcripts/run5_…` to `run9_…`. (v4) Theorem A and its sieve lemma are due to a GPT-5.6 Pro run (93 min, `run10_…`);
the counting-certificate principle, the explicit family, the LP computations and the exact asymptotic reduction are the coordinating seat's
and a Qwen3.8-Max run (`run12_…`); a further Pro run (`run11_…`) showed that the number of anchors must depend on the prime set.
An independent Claude Opus referee run checked the new section line by line; its corrections are incorporated.
(v5) The weighted sieve lemma and the O(n ln ln n) theorem are due to a GPT-5.6 Pro run of 31 minutes (`run14_…`), building on the
weighted ordering identity supplied by the coordinating seat; a second independent Claude Opus referee run verified every step (with
numerical checks up to L = 2^200000) and found no gap; a Qwen3.8-Max run (`run15_…`) proved a special case independently.
No human supplied any mathematics. License: CC0.
(v6) The improved constant 20 ln ln m is due to a GPT-5.6 Pro run of 61 minutes (`run16_constant20_pro*.md`), following a Qwen3.8-Max
micro-lemma on the thinning probability (`run17_theta_budget_qwen*.md`) and the coordinator's exact budget computation (`src/constant_check.py`);
the proof was checked item by item by an independent Claude Opus referee run (one transcription slip, a spurious square root in s(A), was
corrected; every constant recomputed) and the budget by `src/r9_budget_check.py`.
(v8) The threshold-4 theorem for 0/1 weights is due to a GPT-5.6 Pro run of 65 minutes (`run19_zero_one_threshold4_pro*.md`), answering a
coordinator brief that asked whether counting with both interval bounds can give an absolute constant; checked step by step by an independent
Claude Opus referee run (68,251 exhaustive instances m ≤ 43, structured/random/deep-window scans, an abstract-adversary LP), which found no
error. The Qwen3.8-Max micro-lemma runs of the same day (`run18_*`, anchor asymptotics; single-scale certificate) are recorded but not used.
(v9) The dense fractional branch and the reduction to the sparse core come from a GPT-5.6 Pro run of 168 minutes (`run20_*`), the
projective-plane obstruction and the quantitative remarks from a further run of 141 minutes (`run21_*`); both were checked by independent
Claude Opus referee runs (scripts in `src/`), which also corrected the scope of the obstruction (it excludes arguments that ignore the
values ⌊m/d⌋, not the certificate method itself) and rejected two intermediate claims of the engine (a 'reduction' that was a strengthening,
and the necessity of the lcm structure). No theorem about g(n) is affected; the linear bound remains open.
(v10) The arithmetic-shadow theorem and the range 10^2887 come from a GPT-5.6 Pro run of about 105 minutes (`run23_*`), answering a
coordinator brief that asked for arithmetic input after the counting limit; the coordinator's own proof of the packing lemma is used in the
paper. An independent Claude Opus referee run verified every step (exact rationals; scaled-threshold numerics; an exhaustive scan over window
residues) and found no error; it also showed that the multiples-only charging route proposed in the brief fails, as the engine had claimed.
