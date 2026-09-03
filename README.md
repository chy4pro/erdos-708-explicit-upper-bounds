# Explicit upper bounds for the Erdős–Surányi function g(n) — Erdős Problem #708

**Result.** Let g(n) be the least g such that for every set {a_1 < … < a_n} of integers > 1 and every x ≥ 0, some
(at most) g of the integers x+1, …, x+a_n have product divisible by a_1⋯a_n (Erdős–Surányi 1959; Erdős asked, for
$100, whether g(n) ≤ (2+o(1))n or even 2n — [erdosproblems.com/708](https://www.erdosproblems.com/708)). We prove

* g(n) ≤ n(⌈log₂ 2n⌉ + ⌈log₂⌈log₂ 2n⌉⌉ + 2) for n ≥ 2  (e.g. g(10) ≤ 100, g(100) ≤ 1300);
* g(n) ≤ ⌈48 n √((81 + ln n)/ln(81 + ln n))⌉ for n ≥ 1, and g(n) ≤ (2 + o(1)) n √(ln n / ln ln n);
* if a_n ≥ 8n³ then 2n integers always suffice (the conjecture holds for long intervals; Erdős's question reduces to a_n < 8n³).

To our knowledge these are the first upper bounds for g(n) depending on n alone (none is recorded in Erdős's 1992
paper or on the problem's page; the 1959 original, in Hungarian, was not accessible to us). The conjectured 2n is
**not** proved; the problem remains open. We also record g(4) ≥ 5 and g(5) ≥ 6 (exact computation).

**Paper.** `paper/main.pdf` (source `paper/main.tex`).

## Verification
* `src/gn_dp.py` — exact minimum |B| for a concrete (A, x) by dynamic programming over capped valuation vectors; reproduces
  the Erdős–Surányi lower-bound instances (l=3 → 4, l=4 → 6) and the g(4) ≥ 5, g(5) ≥ 6 instances.
* `src/es_bound.py` — checks every numerical inequality of the explicit √-bound over a grid of (n, N), and implements
  the construction (large atoms / merged bins / assembly), verifying divisibility, range and |B| ≤ K on 1.4·10⁶ random instances.
* `src/es_bound2.py` — implements the log-bound construction (per-prime greedy, next-fit bins, globally distinct bin
  representatives), checks the budget conditions (B1), (B2) for n = 2..1999 and larger n, and verifies the output on
  2·10⁶ random instances.
* `src/es_bound3.py` — implements the long-interval construction (a_n ≥ 8n³ ⇒ 2n elements) and verifies it on 2.4·10⁵ random instances.
* `src/split_assign.py`, `src/search_S_omega3.py` — exact feasibility test for the split-assignment conjecture of the paper
  (§5); no counterexample among >10⁶ random instances.

Run: `python3 src/es_bound.py`, `python3 src/es_bound2.py`, `python3 src/gn_dp.py 3`.

## Provenance (honest)
The proofs of the two bounds were produced by OpenAI GPT-5.6 (Pro effort, web interface) in two independent runs (90 and 26 minutes), and the long-interval theorem by Qwen3.8-Max (web interface),
inside an autonomous pipeline coordinated by Claude Fable 5.1 (Anthropic), which selected the problem, pinned the
statement to Erdős's text, verified the lower-bound construction by exact computation, re-derived every step of both
proofs, commissioned independent referee runs (Claude Opus 5 agents in fresh contexts; a Qwen3.8-Max adversarial
audit), wrote the verification scripts and drafted the paper. Two earlier engine attempts (Qwen3.8-Max, in a dual-response chat) produced
invalid proofs of stronger claims (3n, 2n) — they double-counted shared interval elements or assumed a distinct-multiples
matching that van Doorn–Li–Tang (arXiv:2603.28636) show to be false; they are kept in `engine_transcripts/` as a record.
No human supplied any mathematics. License: CC0.
