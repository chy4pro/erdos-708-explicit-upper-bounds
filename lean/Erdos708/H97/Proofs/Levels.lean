import Erdos708.H97.Defs
import Erdos708.H17.Proofs.Lemma4
open Finset BigOperators
open scoped NNReal
namespace Erdos708H97.Rounded
noncomputable section

@[simp] lemma level_zero : level 0 = 1 := by simp [level]
lemma level_succ (i : ℕ) : level (i+1) =
    ((7-i%4 : ℕ) : ℝ≥0) / 2^(i/4+3) := by simp [level]
lemma level_pos (i : ℕ) : 0 < level i := by
  cases i with
  | zero => simp
  | succ i =>
    rw [level_succ]
    have h : 0 < 7-i%4 := by omega
    positivity

lemma level_adjacent (i : ℕ) :
    level (i+1) < level i ∧ level i ≤ (5/4 : ℝ≥0)*level (i+1) := by
  suffices hr : (level (i+1) : ℝ) < level i ∧
      (level i : ℝ) ≤ (5/4 : ℝ)*(level (i+1) : ℝ) by exact_mod_cast hr
  cases i with
  | zero => norm_num [level]
  | succ i =>
    rw [level_succ i, level_succ (i+1)]
    simp only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat]
    have hmod : i%4 < 4 := Nat.mod_lt _ (by omega)
    by_cases h : i%4 = 3
    · have hm : (i+1)%4 = 0 := by omega
      have hd : (i+1)/4 = i/4+1 := by omega
      rw [h, hm, hd, show i/4+1+3 = (i/4+3)+1 by omega, pow_succ]
      norm_num only [Nat.reduceSub, Nat.cast_ofNat]
      have hp : (0 : ℝ) < 2^(i/4+3) := by positivity
      constructor
      · apply (div_lt_div_iff₀ (by positivity) hp).mpr
        nlinarith
      · rw [← mul_div_assoc]
        apply (div_le_div_iff₀ hp (by positivity)).mpr
        nlinarith
    · have hm : (i+1)%4 = i%4+1 := by omega
      have hd : (i+1)/4 = i/4 := by omega
      rw [hm, hd]
      have he : 7-(i%4+1) = (7-i%4)-1 := by omega
      have hi : 4 ≤ 7-(i%4+1) := by omega
      have hr : ((7-i%4 : ℕ) : ℝ) = (7-(i%4+1) : ℕ)+1 := by
        norm_cast; omega
      rw [hr]
      constructor
      · exact (div_lt_div_iff_of_pos_right (by positivity)).mpr (by simp)
      · rw [← mul_div_assoc]
        apply (div_le_div_iff_of_pos_right (by positivity)).mpr
        have hi' : (4 : ℝ) ≤ (7-(i%4+1) : ℕ) := by exact_mod_cast hi
        nlinarith

lemma level_strictAnti : StrictAnti level := strictAnti_nat_of_succ_lt (fun i => (level_adjacent i).1)
lemma level_antitone : Antitone level := level_strictAnti.antitone
lemma level_le_one (i : ℕ) : level i ≤ 1 := by simpa using level_antitone (Nat.zero_le i)

lemma exists_level_le {u : ℝ} (hu : 0 < u) : ∃ i : ℕ, (level i : ℝ) ≤ u := by
  obtain ⟨h, hh⟩ := Erdos708H17.Rounded.exists_dyadic_le hu
  refine ⟨4*h+4, ?_⟩
  have he : level (4*h+4) = (2 : ℝ≥0)⁻¹^(h+1) := by
    rw [show 4*h+4 = (4*h+3)+1 by omega, level_succ]
    have hm : (4*h+3)%4 = 3 := by omega
    have hd : (4*h+3)/4 = h := by omega
    rw [hm, hd]
    norm_num only [Nat.reduceSub, Nat.cast_ofNat]
    rw [pow_add]
    norm_num
    simp [inv_pow, pow_succ]
    <;> field_simp <;> norm_num
  rw [he]
  simp only [NNReal.coe_pow, NNReal.coe_inv, NNReal.coe_ofNat]
  exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ h)).trans hh

lemma rounded_le {u : ℝ} (hu : 0 < u) : (level (roundIndex u) : ℝ) ≤ u := by
  rw [roundIndex, dif_pos (exists_level_le hu)]
  exact Nat.find_spec (exists_level_le hu)

lemma rounding_factor {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    u ≤ (5/4 : ℝ)*(level (roundIndex u) : ℝ) := by
  rw [roundIndex, dif_pos (exists_level_le hu)]
  generalize he : Nat.find (exists_level_le hu) = i
  cases i with
  | zero => simp; linarith
  | succ i =>
    have hlt : u < (level i : ℝ) := lt_of_not_ge (Nat.find_min (exists_level_le hu) (by omega))
    have had : (level i : ℝ) ≤ (5/4 : ℝ)*(level (i+1) : ℝ) := by
      exact_mod_cast (level_adjacent i).2
    exact hlt.le.trans had

lemma roundIndex_antitone {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    roundIndex v ≤ roundIndex u := by
  rw [roundIndex, dif_pos (exists_level_le (hu.trans_le huv)),
    roundIndex, dif_pos (exists_level_le hu)]
  exact Nat.find_min' _ ((Nat.find_spec (exists_level_le hu)).trans huv)

lemma level_mem (i : ℕ) : (level i : ℝ) ∈ levels := by
  cases i with
  | zero => exact Or.inl (by simp)
  | succ i =>
    refine Or.inr ⟨i/4+3, by omega, 7-i%4, mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    simp only [level_succ, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat]

lemma level_high_gap (i : ℕ) (hi : (1/2 : ℝ) < level i) :
    (5/8 : ℝ) ≤ level i := by
  have hn : i < 4 := by
    by_contra h
    have hh := level_antitone (show 4 ≤ i by omega)
    have hh' : (level i : ℝ) ≤ level 4 := by exact_mod_cast hh
    rw [show (level 4 : ℝ) = 1/2 by norm_num [level]] at hh'
    linarith
  have hh := level_antitone (show i ≤ 3 by omega)
  have hh' : (level 3 : ℝ) ≤ level i := by exact_mod_cast hh
  rw [show (level 3 : ℝ) = 5/8 by norm_num [level]] at hh'
  exact hh'

lemma level_middle_gap (i : ℕ) (hi : (3/8 : ℝ) < level i) :
    (7/16 : ℝ) ≤ level i := by
  have hn : i < 6 := by
    by_contra h
    have hh := level_antitone (show 6 ≤ i by omega)
    have hh' : (level i : ℝ) ≤ level 6 := by exact_mod_cast hh
    rw [show (level 6 : ℝ) = 3/8 by norm_num [level]] at hh'
    linarith
  have hh := level_antitone (show i ≤ 5 by omega)
  have hh' : (level 5 : ℝ) ≤ level i := by exact_mod_cast hh
  rw [show (level 5 : ℝ) = 7/16 by norm_num [level]] at hh'
  exact hh'

#print axioms rounding_factor
end
end Erdos708H97.Rounded
