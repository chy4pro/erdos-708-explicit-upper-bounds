import Erdos708.H97.Proofs.CarrierCore
open Finset BigOperators
namespace Erdos708H97.Rounded
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000

def scaleH (i : ℕ) : ℕ := if i=0 then 2 else (i-1)/4+3
def scaleJ (i : ℕ) : ℕ := if i=0 then 4 else 7-(i-1)%4
def scaleL (i : ℕ) : ℕ := 2^scaleH i
lemma scaleH_ge_two (i : ℕ) : 2 ≤ scaleH i := by unfold scaleH; split_ifs <;> omega
lemma scaleJ_bounds (i : ℕ) : 4 ≤ scaleJ i ∧ scaleJ i ≤ 7 := by unfold scaleJ; split_ifs <;> omega
lemma scaleL_pos (i : ℕ) : 0 < scaleL i := by unfold scaleL; positivity
lemma scaleH_mono {i h : ℕ} (hih : i ≤ h) : scaleH i ≤ scaleH h := by
  unfold scaleH
  split_ifs <;> omega
lemma level_scale (i : ℕ) : (level i : ℝ) = (scaleJ i : ℝ)/(scaleL i : ℝ) := by
  by_cases hi : i=0
  · subst i; norm_num [scaleJ,scaleL,scaleH]
  · simp only [level,if_neg hi,NNReal.coe_div,NNReal.coe_natCast,NNReal.coe_pow,NNReal.coe_ofNat,
      scaleJ,scaleL,scaleH,if_neg hi,Nat.cast_pow,Nat.cast_ofNat]

def levelDegree (h i : ℕ) : ℕ := scaleJ i*2^(scaleH h-scaleH i)

/-- G3: every larger level is an integral multiple of the scale's reciprocal. -/
lemma levelDegree_eq (h i : ℕ) (hih : i ≤ h) :
    (levelDegree h i : ℝ) = (level i : ℝ)*(scaleL h : ℝ) := by
  have hH := scaleH_mono hih
  rw [levelDegree,level_scale,scaleL,scaleL]
  push_cast
  have hp : (2 : ℝ)^scaleH h = 2^(scaleH h-scaleH i)*2^scaleH i := by
    rw [← pow_add,Nat.sub_add_cancel hH]
  rw [hp]
  field_simp
  <;> ring

lemma levelDegree_pos (h i : ℕ) : 0 < levelDegree h i := by
  have hh := (scaleJ_bounds i).1
  unfold levelDegree
  positivity

lemma levelDegree_injective (h : ℕ) : Set.InjOn (levelDegree h) (Iic h : Set ℕ) := by
  intro i hi k hk he
  have heR : (level i : ℝ)*(scaleL h : ℝ) = (level k : ℝ)*(scaleL h : ℝ) := by
    rw [← levelDegree_eq h i (mem_Iic.mp hi),← levelDegree_eq h k (mem_Iic.mp hk),he]
  have hh : (level i : ℝ) = level k := mul_right_cancel₀ (by exact_mod_cast (scaleL_pos h).ne') heR
  exact level_strictAnti.injective (NNReal.coe_injective hh)

lemma levelDegree_mem (h i : ℕ) (hih : i ≤ h) : levelDegree h i ∈ exponents (scaleJ h) (scaleL h) := by
  have hH := scaleH_mono hih
  have hL : (0 : ℝ) < scaleL h := by exact_mod_cast scaleL_pos h
  have hlo : (scaleJ h : ℝ) ≤ levelDegree h i := by
    rw [levelDegree_eq h i hih]
    have hh : (level h : ℝ) ≤ level i := by exact_mod_cast level_antitone hih
    have he : (level h : ℝ)*(scaleL h : ℝ) = scaleJ h := by rw [level_scale]; field_simp
    rw [← he]
    exact mul_le_mul_of_nonneg_right hh hL.le
  have hhi : (levelDegree h i : ℝ) ≤ scaleL h := by
    rw [levelDegree_eq h i hih]
    exact mul_le_of_le_one_left hL.le (by exact_mod_cast level_le_one i)
  have hpow : scaleH h-scaleH i < scaleL h+1 := by
    have hh := Nat.lt_two_pow_self (n := scaleH h)
    change scaleH h-scaleH i < 2^scaleH h+1
    omega
  simp only [exponents,mem_filter]
  exact ⟨mem_Icc.mpr ⟨by exact_mod_cast hlo,by exact_mod_cast hhi⟩,
    scaleJ i,mem_Icc.mpr (scaleJ_bounds i),scaleH h-scaleH i,mem_range.mpr hpow,rfl⟩

lemma self_degree (h : ℕ) : levelDegree h h = scaleJ h := by simp [levelDegree]

/-- G5: the first crossing modulus is determined by its prime and level. -/
lemma carrier_height_injective (A : AtomSystem) (m p : ℕ) :
    Set.InjOn (levelHeight A) {a | a ∈ retained A m ∧ a.1 = p} := by
  intro a ha b hb hab
  have ha' := (mem_filter.mp (mem_filter.mp ha.1).1).2
  have hb' := (mem_filter.mp (mem_filter.mp hb.1).1).2
  apply Prod.ext (ha.2.trans hb.2.symm)
  exact le_antisymm
    (ha'.2 b (rounding_retained_mem_atoms A m hb.1) (hb.2.trans ha.2.symm) hb'.1 hab.symm)
    (hb'.2 a (rounding_retained_mem_atoms A m ha.1) (ha.2.trans hb.2.symm) ha'.1 hab)
end
end Erdos708H97.Rounded

namespace Erdos708H97.Proofs
noncomputable section
attribute [local instance] Classical.propDecidable

def carrierHeight (A : AtomSystem) (m P : ℕ) : ℕ := Rounded.levelHeight (small A m) (lastLevel A m P)
def carrierDegree (A : AtomSystem) (m P : ℕ) : ℕ :=
  ∑ a ∈ Rounded.effective (small A m) m P, Rounded.levelDegree (carrierHeight A m P) (Rounded.levelHeight (small A m) a)
def carrierMassIndex (A : AtomSystem) (m P : ℕ) : ℕ := carrierDegree A m P-Rounded.scaleL (carrierHeight A m P)

lemma theta_scale (A : AtomSystem) (m P : ℕ) :
    theta A m P = (Rounded.scaleJ (carrierHeight A m P) : ℝ)/Rounded.scaleL (carrierHeight A m P) :=
  Rounded.level_scale _

lemma carrierDegree_eq (A : AtomSystem) (m P : ℕ) (hP : P ∈ carriers A m) :
    (carrierDegree A m P : ℝ) = mu A m P*(Rounded.scaleL (carrierHeight A m P) : ℝ) := by
  rw [carrierDegree,Nat.cast_sum]
  calc
    _ = ∑ a ∈ Rounded.effective (small A m) m P,
        (Rounded.levelValue (small A m) a : ℝ)*(Rounded.scaleL (carrierHeight A m P) : ℝ) := by
      apply sum_congr rfl
      intro a ha
      exact Rounded.levelDegree_eq _ _ ((carrier_data A m P hP).2.2.2 a ha)
    _ = _ := by
      rw [← sum_mul,← Rounded.B_eq_effective_sum]
      rfl

lemma carrier_degree_bounds (A : AtomSystem) (m P : ℕ) (hP : P ∈ carriers A m) :
    1 ≤ carrierMassIndex A m P ∧ carrierMassIndex A m P ≤ Rounded.scaleJ (carrierHeight A m P) ∧
    carrierDegree A m P = Rounded.scaleL (carrierHeight A m P)+carrierMassIndex A m P := by
  let h := carrierHeight A m P
  have hL : (0 : ℝ) < Rounded.scaleL h := by exact_mod_cast Rounded.scaleL_pos h
  have hlo : (Rounded.scaleL h : ℝ) < carrierDegree A m P := by
    rw [carrierDegree_eq A m P hP]
    exact lt_mul_of_one_lt_left hL (carrier_mu_gt_one A m P hP)
  have hhi : (carrierDegree A m P : ℝ) ≤ (Rounded.scaleL h : ℝ)+Rounded.scaleJ h := by
    rw [carrierDegree_eq A m P hP]
    have hh := mul_le_mul_of_nonneg_right (carrier_mu_upper A m P hP) hL.le
    have ht : theta A m P*(Rounded.scaleL h : ℝ) = Rounded.scaleJ h := by
      rw [theta_scale]
      change ((Rounded.scaleJ h : ℝ)/Rounded.scaleL h)*Rounded.scaleL h = _
      exact div_mul_cancel₀ _ hL.ne'
    nlinarith
  have hlon : Rounded.scaleL h < carrierDegree A m P := by exact_mod_cast hlo
  have hhin : carrierDegree A m P ≤ Rounded.scaleL h+Rounded.scaleJ h := by exact_mod_cast hhi
  dsimp only [carrierMassIndex]
  change 1 ≤ carrierDegree A m P-Rounded.scaleL h ∧
    carrierDegree A m P-Rounded.scaleL h ≤ Rounded.scaleJ h ∧
    carrierDegree A m P = Rounded.scaleL h+(carrierDegree A m P-Rounded.scaleL h)
  omega

#print axioms Rounded.levelDegree_mem
#print axioms carrier_degree_bounds
end
end Erdos708H97.Proofs
