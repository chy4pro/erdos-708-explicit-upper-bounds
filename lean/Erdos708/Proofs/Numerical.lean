import Mathlib

open Finset BigOperators

namespace Erdos708SparseCore

 theorem numerical_bound (t : ℕ) (ht : 1 ≤ t) (H : ℝ) (hH0 : 0 ≤ H) (hH : H ≤ 17 / 16) :
    (t : ℝ) ^ (12 * t) * H ^ (12 * t + 1) * 2 ^ (23 * t) / (Nat.factorial (12 * t + 1) : ℝ)
      ≤ 17 / 416 := by
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hnR : (1 : ℝ) ≤ (12 * t : ℕ) := by push_cast; linarith
  have he : Real.exp 1 ≤ (11 : ℝ) / 4 := by linarith [Real.exp_one_lt_d9]
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * (12 * t : ℕ)) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [Real.pi_gt_three]
  have hb : (t : ℝ) * 48 / 11 ≤ (12 * t : ℕ) / Real.exp 1 := by
    apply (le_div_iff₀ (Real.exp_pos 1)).2
    push_cast
    nlinarith
  have hfac : ((t : ℝ) * 48 / 11) ^ (12 * t) ≤ (Nat.factorial (12 * t) : ℝ) := by
    calc
      _ ≤ ((12 * t : ℕ) / Real.exp 1 : ℝ) ^ (12 * t) :=
        pow_le_pow_left₀ (by positivity) hb _
      _ ≤ Real.sqrt (2 * Real.pi * (12 * t : ℕ)) *
          ((12 * t : ℕ) / Real.exp 1 : ℝ) ^ (12 * t) := by
        exact le_mul_of_one_le_left (by positivity) hsqrt
      _ ≤ _ := Stirling.le_factorial_stirling (12 * t)
  let b : ℝ := (187 / 768 : ℝ) ^ 12 * 2 ^ 23
  have hb0 : 0 ≤ b := by norm_num [b]
  have hbhalf : b ≤ (1 : ℝ) / 2 := by norm_num [b]
  have hbt : b ^ t ≤ (1 : ℝ) / 2 := by
    calc
      b ^ t ≤ b ^ 1 := pow_le_pow_of_le_one hb0 (hbhalf.trans (by norm_num)) ht
      _ ≤ _ := by simpa using hbhalf
  have hid : (t : ℝ) ^ (12 * t) * (17 / 16 : ℝ) ^ (12 * t) * 2 ^ (23 * t) =
      ((t : ℝ) * 48 / 11) ^ (12 * t) * b ^ t := by
    simp only [pow_mul, ← mul_pow]
    congr 1
    dsimp [b]
    ring
  have hnum : (t : ℝ) ^ (12 * t) * H ^ (12 * t + 1) * 2 ^ (23 * t) ≤
      (17 / 32 : ℝ) * (Nat.factorial (12 * t) : ℝ) := by
    calc
      _ ≤ (t : ℝ) ^ (12 * t) * (17 / 16 : ℝ) ^ (12 * t + 1) * 2 ^ (23 * t) := by
        gcongr
      _ = ((t : ℝ) * 48 / 11) ^ (12 * t) * b ^ t * (17 / 16 : ℝ) := by
        rw [pow_succ]
        nlinarith [hid]
      _ ≤ (Nat.factorial (12 * t) : ℝ) * (1 / 2 : ℝ) * (17 / 16 : ℝ) := by
        gcongr
      _ = _ := by ring
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < Nat.factorial (12 * t + 1))).2
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_mul]
  norm_num only [Nat.cast_ofNat, Nat.cast_one]
  have hf0 : (0 : ℝ) ≤ Nat.factorial (12 * t) := by positivity
  nlinarith

#print axioms numerical_bound

end Erdos708SparseCore
