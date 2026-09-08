import Erdos708.H17.Chain

/- Statement cards only. Proof modules do not import this file. -/
open Finset BigOperators
open Erdos708H17Chain
namespace Erdos708H17Chain.Chain19.Cards

theorem primes_card_le (D : Problem) : D.primes.card ≤ D.n +
    ((Finset.range (Nat.sqrt D.m + 1)).filter Nat.Prime).card := by sorry

theorem pi_le (n : ℕ) : ((Finset.range (3*n+1)).filter Nat.Prime).card ≤ n + 1 := by sorry

theorem strict_rounding (D : Problem) :
    ∃ B, Covers D B ∧ (B.card : ℝ) < fractionalValue D + D.primes.card := by sorry

theorem ksplit3 (D : Problem) (hm : 9 * D.n^2 ≤ D.m) :
    ∃ B, Covers D B ∧ B.card ≤ 3 * D.n := by sorry

theorem bound_of_hinge (c : ℝ) (hc : 1 ≤ c)
    (hhinge : ∀ (z : Weight) (m : ℕ), 1 ≤ m → ∀ x : ℕ,
      hingeSum (w z) c 0 m ≤ hingeSum (w z) 1 x m) (D : Problem) :
    ∃ B, Covers D B ∧ B.card ≤ ⌈c * D.n⌉₊ + 2 * D.n := by sorry

theorem g_le_19n :
    ∀ (n : ℕ) (hn : 1 ≤ n), ∀ (A : Finset ℕ) (hA : A.card = n)
      (h2 : ∀ a ∈ A, 2 ≤ a) (x : ℕ),
      ∃ B ⊆ Finset.Icc (x+1) (x + A.max' (Finset.card_pos.mp (by omega))),
        B.card ≤ 19*n ∧ (∏ a ∈ A, a) ∣ (∏ b ∈ B, b) := by sorry

theorem g_le_12n_of_hinge
    (h : ∀ (z : Weight) (m : ℕ), 1 ≤ m → ∀ x : ℕ,
      hingeSum (w z) (97/10 : ℝ) 0 m ≤ hingeSum (w z) 1 x m) :
    ∀ (n : ℕ) (hn : 1 ≤ n), ∀ (A : Finset ℕ) (hA : A.card = n)
      (h2 : ∀ a ∈ A, 2 ≤ a) (x : ℕ),
      ∃ B ⊆ Finset.Icc (x+1) (x + A.max' (Finset.card_pos.mp (by omega))),
        B.card ≤ 12*n ∧ (∏ a ∈ A, a) ∣ (∏ b ∈ B, b) := by sorry

end Erdos708H17Chain.Chain19.Cards
