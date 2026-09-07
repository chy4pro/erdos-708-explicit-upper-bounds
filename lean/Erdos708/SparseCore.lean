import Mathlib

/-!
# Erdős Problem 708 — the sparse-core inequality (statement cards)

Source: H. Chen, *Explicit upper bounds for the Erdős–Surányi function g(n)*, v11 (2026-09-07),
Zenodo 10.5281/zenodo.22636084, Section 14, Theorem 14.1 (signed certificate), with the two
inherited lemmas 14.3 (hinge) and 14.4 (moment bound) and the numerical Lemma 14.8.

An *atom system* is a finite set of prime powers `p^j` (`j ≥ 1`) with real weights
`α(p,j) ∈ [0,1]` whose sum over `j` is at most `1` for every prime `p`.  It defines
`S₀(n) = Σ_{p^j ∣ n} α(p,j)`, the mean `H = Σ α(p,j)/p^j`, and for an integer `m` the two hinge sums
`L = Σ_{k ≤ m} (S₀(k) − 64)⁺` and `R = Σ_{b = x+1}^{x+m} (S₀(b) − 1)⁺`.
-/

namespace Erdos708SparseCore

open Finset BigOperators

/-- A finitely supported system of prime-power atoms with weights in `[0,1]` and per-prime total
weight at most `1`.  `atoms` lists the pairs `(p, j)` carrying weight; `weight` gives `α(p,j)`. -/
structure AtomSystem where
  atoms : Finset (ℕ × ℕ)
  weight : ℕ × ℕ → ℝ
  prime_of_mem : ∀ a ∈ atoms, Nat.Prime a.1 ∧ 1 ≤ a.2
  weight_nonneg : ∀ a ∈ atoms, 0 ≤ weight a
  perPrime_le_one : ∀ p : ℕ, ∑ a ∈ atoms.filter (fun a => a.1 = p), weight a ≤ 1

/-- `S₀(n) = Σ_{(p,j) ∈ atoms, p^j ∣ n} α(p,j)`. -/
noncomputable def S0 (A : AtomSystem) (n : ℕ) : ℝ :=
  ∑ a ∈ A.atoms.filter (fun a => a.1 ^ a.2 ∣ n), A.weight a

/-- The mean `H = Σ α(p,j) / p^j` of `S₀` over the integers. -/
noncomputable def mean (A : AtomSystem) : ℝ :=
  ∑ a ∈ A.atoms, A.weight a / ((a.1 : ℝ) ^ a.2)

/-- Left hinge sum `L = Σ_{k=1}^{m} (S₀(k) − 64)⁺`. -/
noncomputable def L (A : AtomSystem) (m : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 m, max (S0 A k - 64) 0

/-- Right hinge sum `R = Σ_{b=x+1}^{x+m} (S₀(b) − 1)⁺` over the window of `m` consecutive
integers starting after `x`. -/
noncomputable def R (A : AtomSystem) (x m : ℕ) : ℝ :=
  ∑ b ∈ Icc (x + 1) (x + m), max (S0 A b - 1) 0

/-- **Theorem 14.1 (signed certificate).**  For every atom system of mean below `17/16`, every
`m > 4096` and every window of `m` consecutive positive integers,
`(141/128) · L ≤ R`.  In particular the sparse-core inequality `L ≤ R` holds. -/
theorem sparse_core (A : AtomSystem) (m : ℕ) (hm : 4096 < m) (hH : mean A < 17 / 16) (x : ℕ) :
    (141 / 128 : ℝ) * L A m ≤ R A x m := by
  sorry

/-- **Lemma 14.3 (hinge inequality).**  For `x_i ∈ [0,1]` and an integer `C ≥ 0`,
`(Σ x_i − C)⁺ ≤ e_{C+1}(x)`, where `e_{C+1}(x) = Σ_{|T| = C+1} Π_{i ∈ T} x_i` is the elementary
symmetric polynomial (written out as a sum over `powersetCard`). -/
theorem hinge_le_esymm {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ 1)
    (C : ℕ) :
    max (∑ i ∈ s, x i - C) 0 ≤ ∑ t ∈ s.powersetCard (C + 1), ∏ i ∈ t, x i := by
  sorry

/-- **Lemma 14.4 (moment bound), abstract form.**  Let `q : ι → ℕ` assign pairwise coprime moduli
(`q i ≥ 1`) to a finite index set and `h : ι → ℝ` nonnegative weights with `H = Σ h i`.  For
`b(n) := Σ_{q i ∣ n} h i · q i` (so that the mean of `b` is `H`)… stated here in the form used in
the paper: for every `N ≥ 1` and `r ≥ 1`, the sum over `j ≤ N` of the elementary symmetric
polynomial `e_r` of the per-prime contributions is at most `N · H^r / r!`.
Formalization: primes `p ∈ P`, for each prime a finite list of levels `(q, inc)` with `q` a power
of `p` and `inc ≥ 0`; `b_p(j) = Σ_{q ∣ j} inc`, `H = Σ inc / q`. -/
theorem moment_bound (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (levels : ℕ → Finset (ℕ × ℝ))
    (hlev : ∀ p ∈ P, ∀ l ∈ levels p, (∃ e : ℕ, 1 ≤ e ∧ l.1 = p ^ e) ∧ 0 ≤ l.2)
    (N r : ℕ) (hN : 1 ≤ N) (hr : 1 ≤ r) :
    ∑ j ∈ Icc 1 N,
        ∑ T ∈ P.powersetCard r, ∏ p ∈ T, (∑ l ∈ (levels p).filter (fun l => l.1 ∣ j), l.2)
      ≤ (N : ℝ) * (∑ p ∈ P, ∑ l ∈ levels p, l.2 / (l.1 : ℝ)) ^ r / (Nat.factorial r : ℝ) := by
  sorry

/-- **Lemma 14.8 (a uniform numerical bound).**  For every integer `t ≥ 1` and `0 ≤ H ≤ 17/16`,
`t^{12t} · H^{12t+1} · 2^{23t} / (12t+1)! ≤ 17/416`. -/
theorem numerical_bound (t : ℕ) (ht : 1 ≤ t) (H : ℝ) (hH0 : 0 ≤ H) (hH : H ≤ 17 / 16) :
    (t : ℝ) ^ (12 * t) * H ^ (12 * t + 1) * 2 ^ (23 * t) / (Nat.factorial (12 * t + 1) : ℝ)
      ≤ 17 / 416 := by
  sorry

end Erdos708SparseCore
