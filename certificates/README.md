# Certificates for Proposition 7.7 (three strengthenings of the hinge inequality that fail)

Each file gives an explicit window I = {x+1, …, x+m} (x is written out in full) on which a natural strengthening of the
hinge inequality (Conjecture 7.1 of the paper) fails. All claims are re-verifiable from x alone.

* `nm_counterexample_m20000.txt` — m = 20000: I contains 2270 integers with no prime factor ≤ m/2, more than π(m)+1 = 2263.
  Hence no injection φ: [1,m] → I with (k/p) | φ(k) for some prime p | k exists (Hall's condition fails on those integers).
  Verify: `python3 src/hr_construct.py 20000` rebuilds and checks it; or count directly from x.
* `nm_counterexample_m100000.txt` — m = 100000: 9735 such integers (π(m)+1 = 9593). On this window the single-threshold
  level-set inequality #{k ≤ m : w(k) ≥ 2τ} ≤ #{b ∈ I : w(b) ≥ τ} (z ≡ 1 on primes ≤ m/2) fails at τ = 1 and τ = 1/2, and the
  two-layer statement #{n ≤ m : ω(n) ≥ 2} ≤ #{b ∈ I : ω(b) ≥ 1} fails (90299 > 90265), while the hinge inequality and the
  per-prime-power inequality hold with room. Verify: `python3 src/bigwindow_eval.py certificates/nm_counterexample_m100000.txt`.
* `lap_counterexample_L1000000.txt` — L = 10^6, z ≡ 1 on all primes ≤ L: the window contains 80436 integers free of all primes
  ≤ L (π(L)+1 = 78499) and the Laplace-form inequality s·Σ_{b∈I} s^{w(b)} ≤ Σ_{k≤L} s^{w(k)} fails for s ∈ [0.005, 0.015]
  (at s = 0.005: 405.03 > 398.77). Verify: `python3 src/adv_window3.py 1000000 0.01 0.005 0.01` rebuilds it (about 12 minutes),
  or evaluate from x with `src/lap_window.py`-style code (valuations from residues of x; spot checks by gcd with the primorial).

Construction (all three): centred coordinates n ∈ [−m/2, m/2); residue class 0 modulo every prime p ≤ √m (this keeps ±1 and
±primes), then for each larger prime the residue class containing the fewest surviving (or, for the Laplace case, the least
weighted) positions; the Chinese remainder theorem gives x. The mechanism is the Hensley–Richards phenomenon: dense admissible
patterns have more elements than π(m) for m ≥ 3159.
