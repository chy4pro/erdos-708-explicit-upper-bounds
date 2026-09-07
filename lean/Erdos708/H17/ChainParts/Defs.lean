import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Tauto

namespace Erdos708H17Chain

open Finset BigOperators

attribute [local instance] Classical.propDecidable

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

/-- The sole external hypothesis, verbatim type of the independent Section-14 theorem. -/
def sparse_core_hyp : Prop :=
  ∀ (A : AtomSystem) (m : ℕ) (hm : 4096 < m) (hH : mean A < 17 / 16) (x : ℕ),
    (141 / 128 : ℝ) * L A m ≤ R A x m

noncomputable def restrict (A : AtomSystem) (P : ℕ × ℕ → Prop) : AtomSystem where
  atoms := A.atoms.filter P
  weight := A.weight
  prime_of_mem a ha := A.prime_of_mem a (mem_filter.mp ha).1
  weight_nonneg a ha := A.weight_nonneg a (mem_filter.mp ha).1
  perPrime_le_one p := le_trans (sum_le_sum_of_subset_of_nonneg
    (by intro a ha; simp_all only [mem_filter]; tauto)
    (by intro a ha _; exact A.weight_nonneg a (mem_filter.mp ha).1)) (A.perPrime_le_one p)

noncomputable def small (A : AtomSystem) (m : ℕ) : AtomSystem :=
  restrict A (fun a => 64 * a.1 ^ a.2 ≤ m)
noncomputable def large (A : AtomSystem) (m : ℕ) : AtomSystem :=
  restrict A (fun a => ¬ 64 * a.1 ^ a.2 ≤ m)
noncomputable def S (A : AtomSystem) (k : ℕ) : ℝ := S0 A k
noncomputable def S1 (A : AtomSystem) (m k : ℕ) : ℝ := S0 (large A m) k
noncomputable def H64 (A : AtomSystem) (m : ℕ) : ℝ := mean (small A m)
noncomputable def hingeSum (f : ℕ → ℝ) (c : ℝ) (x m : ℕ) : ℝ :=
  ∑ k ∈ Icc (x + 1) (x + m), max (f k - c) 0

/-- Finite support is explicit; values off `primes` are ignored. -/
structure Weight where
  primes : Finset ℕ
  z : ℕ → ℝ
  isPrime : ∀ p ∈ primes, Nat.Prime p
  bounds : ∀ p ∈ primes, 0 ≤ z p ∧ z p ≤ 1

noncomputable def weightedValuation (P : Finset ℕ) (z : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ p ∈ P, z p * (k.factorization p : ℝ)
noncomputable def w (z : Weight) (k : ℕ) : ℝ := weightedValuation z.primes z.z k
noncomputable def capped (z : Weight) (k : ℕ) : ℝ :=
  ∑ p ∈ z.primes, min (z.z p * (k.factorization p : ℝ)) 1
noncomputable def alpha (z : Weight) (p j : ℕ) : ℝ :=
  min ((j : ℝ) * z.z p) 1 - min (((j - 1 : ℕ) : ℝ) * z.z p) 1
/-- Truncation sufficient on `[1,N]`; atom weights do not depend on N. -/
noncomputable def weightAtoms (z : Weight) (N : ℕ) : Finset (ℕ × ℕ) :=
  z.primes ×ˢ Icc 1 N
noncomputable def weightH64 (z : Weight) (m : ℕ) : ℝ :=
  ∑ a ∈ (weightAtoms z m).filter (fun a => 64 * a.1 ^ a.2 ≤ m),
    alpha z a.1 a.2 / ((a.1 : ℝ) ^ a.2)

def Hinge17 : Prop := ∀ (z : Weight) (m : ℕ), 1 ≤ m → ∀ x : ℕ,
  hingeSum (w z) 17 0 m ≤ hingeSum (w z) 1 x m

/-- Distinct integers ≥ 2 and a window; n = A.card, m = max A. -/
structure Problem where
  A : Finset ℕ
  nonempty : A.Nonempty
  two_le : ∀ a ∈ A, 2 ≤ a
  x : ℕ

noncomputable def Problem.m (D : Problem) : ℕ := D.A.max' D.nonempty
def Problem.n (D : Problem) : ℕ := D.A.card
noncomputable def Problem.interval (D : Problem) : Finset ℕ := Icc (D.x + 1) (D.x + D.m)
noncomputable def Problem.product (D : Problem) : ℕ := ∏ a ∈ D.A, a
noncomputable def Problem.primes (D : Problem) : Finset ℕ := D.product.primeFactors
noncomputable def demand (D : Problem) (p : ℕ) : ℝ := ∑ a ∈ D.A, (a.factorization p : ℝ)
def FractionalCover (D : Problem) (y : ℕ → ℝ) : Prop :=
  (∀ b ∈ D.interval, 0 ≤ y b ∧ y b ≤ 1) ∧
  ∀ p ∈ D.primes, demand D p ≤ ∑ b ∈ D.interval, (b.factorization p : ℝ) * y b
noncomputable def coverCost (D : Problem) (y : ℕ → ℝ) : ℝ := ∑ b ∈ D.interval, y b
noncomputable def fractionalValue (D : Problem) : ℝ :=
  sInf {t : ℝ | ∃ y : ℕ → ℝ, FractionalCover D y ∧ coverCost D y = t}
noncomputable def dualObjective (D : Problem) (z : ℕ → ℝ) : ℝ :=
  (∑ a ∈ D.A, weightedValuation D.primes z a) -
    hingeSum (weightedValuation D.primes z) 1 D.x D.m
noncomputable def fractionalCount (D : Problem) (y : ℕ → ℝ) : ℕ :=
  (D.interval.filter (fun b => 0 < y b ∧ y b < 1)).card
noncomputable def roundedSet (D : Problem) (y : ℕ → ℝ) : Finset ℕ :=
  D.interval.filter (fun b => 0 < y b)
def Covers (D : Problem) (B : Finset ℕ) : Prop :=
  B ⊆ D.interval ∧ D.product ∣ ∏ b ∈ B, b

end Erdos708H17Chain
