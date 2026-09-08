import Erdos708.H97.Proofs.RoundedBasics
open Finset BigOperators
open scoped NNReal
namespace Erdos708H97.Rounded
noncomputable section

lemma eta_pos {t : ℝ} (ht : 0 < t) : 0 < eta t := by
  unfold eta
  split_ifs <;> positivity
lemma eta_le_third {t : ℝ} (ht : t ≤ 1) : eta t ≤ 1/3 := by
  unfold eta
  split_ifs with h <;> linarith
lemma eta_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    eta s ≤ eta t := by
  unfold eta
  split_ifs <;> linarith

lemma retained_modulus_gt_one (A : AtomSystem) (m : ℕ) {a : ℕ × ℕ}
    (ha : a ∈ retained A m) : 1 < modulus a := by
  have hp := A.prime_of_mem a (rounding_retained_mem_atoms A m ha)
  exact hp.1.one_lt.trans_le (by simpa [modulus] using Nat.pow_le_pow_right hp.1.pos hp.2)

lemma retained_m_ge_two (A : AtomSystem) (m : ℕ) {a : ℕ × ℕ}
    (ha : a ∈ retained A m) : 2 ≤ m := by
  by_contra h
  have hm : (m : ℝ) ≤ 1 := by exact_mod_cast (show m ≤ 1 by omega)
  have hη : 0 ≤ eta (levelValue A a) := (eta_pos (by exact_mod_cast level_pos (levelHeight A a))).le
  have hh := (mem_filter.mp ha).2.trans (Real.rpow_le_one (Nat.cast_nonneg m) hm hη)
  have hq : (1 : ℝ) < modulus a := by exact_mod_cast retained_modulus_gt_one A m ha
  linarith

lemma retained_log_bound (A : AtomSystem) (m : ℕ) {a : ℕ × ℕ}
    (ha : a ∈ retained A m) :
    Real.log (modulus a : ℝ) ≤ eta (levelValue A a)*Real.log (m : ℝ) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by have := retained_m_ge_two A m ha; omega)
  have hq : (0 : ℝ) < modulus a := by exact_mod_cast (show 0 < modulus a by have := retained_modulus_gt_one A m ha; omega)
  have hh := Real.log_le_log hq (mem_filter.mp ha).2
  rwa [Real.log_rpow hm] at hh

lemma retained_cube_le (A : AtomSystem) (m : ℕ) (a : ℕ × ℕ)
    (ha : a ∈ retained A m) : modulus a^3 ≤ m := by
  have hm : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by have := retained_m_ge_two A m ha; omega)
  have hq : (0 : ℝ) < modulus a := by exact_mod_cast (show 0 < modulus a by have := retained_modulus_gt_one A m ha; omega)
  have he : eta (levelValue A a) ≤ 1/3 := eta_le_third (by exact_mod_cast level_le_one (levelHeight A a))
  have hh := (retained_log_bound A m ha).trans
    (mul_le_mul_of_nonneg_right he (Real.log_natCast_nonneg m))
  have hl : Real.log ((modulus a : ℝ)^3) ≤ Real.log (m : ℝ) := by
    rw [Real.log_pow]; norm_num; linarith
  exact_mod_cast (Real.log_le_log_iff (pow_pos hq 3) hm).mp hl

#print axioms retained_cube_le
end
end Erdos708H97.Rounded
