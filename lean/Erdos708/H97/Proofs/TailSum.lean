import Erdos708.H97.Proofs.TailScale
open Finset BigOperators
namespace Erdos708H97.Proofs
noncomputable section
set_option maxHeartbeats 2000000

def tailT : ℝ := (3/4)^146
def lowConstant : ℝ := (9/8)*(∑ j ∈ Icc (4:ℕ) 7, (j:ℝ)*tailD j)
def highConstant : ℝ := (2187/4096)/1024^2*(∑ j ∈ Icc (4:ℕ) 7, (j:ℝ)^2*tailF j*tailD j)
def tailMajorant (r : ℕ) : ℝ := lowConstant*tailT*tailT^r+highConstant*(1/4)^r

lemma tail_constants_nonneg : 0 ≤ lowConstant ∧ 0 ≤ highConstant := by
  have hd (j : ℕ) (hj : j ∈ Icc 4 7) : 0 ≤ tailD j :=
    sum_nonneg (fun d hd => pow_nonneg (inv_nonneg.mpr (tail_parameters j hj).1.le) d)
  have hF (j : ℕ) (hj : j ∈ Icc 4 7) : 0 ≤ tailF j :=
    (show (0:ℝ)≤5/4 by norm_num).trans (tail_parameters j hj).2.2.1
  constructor
  · exact mul_nonneg (by norm_num) (sum_nonneg (fun j hj => mul_nonneg (Nat.cast_nonneg _) (hd j hj)))
  · exact mul_nonneg (by norm_num) (sum_nonneg (fun j hj => mul_nonneg (mul_nonneg (sq_nonneg _) (hF j hj)) (hd j hj)))

lemma dyadic_low (j r : ℕ) (hj : j ∈ Icc 4 7) :
    (3/4:ℝ)^((1024*2^r:ℕ)/j:ℝ) ≤ tailT*tailT^r := by
  have hj0 : (0:ℝ)<j := by exact_mod_cast (show 0<j by have := (mem_Icc.mp hj).1; omega)
  have hp : r+1 ≤ 2^r := Nat.lt_two_pow_self
  have hnat : 146*(r+1)*j ≤ 1024*2^r := by
    have h1 := Nat.mul_le_mul_left (146*(r+1)) (mem_Icc.mp hj).2
    nlinarith
  have hfrac : ((146*(r+1):ℕ):ℝ) ≤ ((1024*2^r:ℕ):ℝ)/j :=
    (le_div_iff₀ hj0).mpr (by exact_mod_cast hnat)
  apply (Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0:ℝ)<3/4) (by norm_num : (3/4:ℝ)≤1) hfrac).trans_eq
  rw [Real.rpow_natCast,pow_mul,pow_succ]
  dsimp only [tailT]
  ring

lemma dyadic_square (j r : ℕ) :
    (((j:ℝ)/(1024*2^r:ℕ))^2) = (j:ℝ)^2/1024^2*(1/4:ℝ)^r := by
  have hp : (2:ℝ)^r ≠ 0 := by positivity
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,div_pow,mul_pow,pow_right_comm (2:ℝ) r 2]
  norm_num only [show (2:ℝ)^2=4 by norm_num,one_div_pow]
  ring

lemma tailTerm_le_majorant (r : ℕ) : tailTerm r ≤ tailMajorant r := by
  have hL : 1024 ≤ 1024*2^r := by have := Nat.one_le_pow r 2 (by omega); nlinarith
  have hpoint (j : ℕ) (hj : j ∈ Icc 4 7) :
      tailAScale j (1024*2^r) ≤
      (9*(j:ℝ)/8)*tailD j*(tailT*tailT^r)+
        (2187/4096)*((j:ℝ)^2/1024^2*(1/4:ℝ)^r)*tailF j*tailD j := by
    have hd : 0 ≤ tailD j := sum_nonneg (fun d hd => pow_nonneg (inv_nonneg.mpr (tail_parameters j hj).1.le) d)
    apply (tail_scale_bound j (1024*2^r) hj hL).trans
    rw [dyadic_square]
    exact add_le_add (mul_le_mul_of_nonneg_left (dyadic_low j r hj)
      (show 0 ≤ (9*(j:ℝ)/8)*tailD j by positivity)) le_rfl
  apply (sum_le_sum hpoint).trans_eq
  simp only [tailMajorant,lowConstant,highConstant,sum_add_distrib,mul_sum,sum_mul]
  congr 1 <;> apply sum_congr rfl <;> intro j hj <;> ring

lemma majorant_summable : Summable tailMajorant := by
  have ht0 : 0 ≤ tailT := by unfold tailT; positivity
  have ht1 : tailT < 1 := pow_lt_one₀ (by norm_num : (0:ℝ)≤3/4) (by norm_num : (3/4:ℝ)<1) (by decide)
  exact ((summable_geometric_of_lt_one ht0 ht1).mul_left (lowConstant*tailT)).add
    ((summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/4) (by norm_num : (1/4:ℝ)<1)).mul_left highConstant)

lemma majorant_sum : (∑' r, tailMajorant r) = tailBound := by
  have ht0 : 0 ≤ tailT := by unfold tailT; positivity
  have ht1 : tailT < 1 := pow_lt_one₀ (by norm_num : (0:ℝ)≤3/4) (by norm_num : (3/4:ℝ)<1) (by decide)
  have hl := (summable_geometric_of_lt_one ht0 ht1).mul_left (lowConstant*tailT)
  have hh := (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/4) (by norm_num : (1/4:ℝ)<1)).mul_left highConstant
  rw [show (∑' r, tailMajorant r) = (∑' r, lowConstant*tailT*tailT^r)+(∑' r, highConstant*(1/4:ℝ)^r) by exact hl.tsum_add hh,
    tsum_mul_left,tsum_mul_left,tsum_geometric_of_lt_one ht0 ht1,
    tsum_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/4) (by norm_num : (1/4:ℝ)<1)]
  unfold lowConstant highConstant tailT tailBound
  ring

lemma tail_summable_and_bound : Summable tailTerm ∧ (∑' r, tailTerm r) ≤ tailBound := by
  have hn (r : ℕ) : 0 ≤ tailTerm r := sum_nonneg (fun j hj => tailAScale_nonneg j _)
  have hs := majorant_summable.of_nonneg_of_le hn tailTerm_le_majorant
  exact ⟨hs,(hs.tsum_le_tsum tailTerm_le_majorant majorant_summable).trans_eq majorant_sum⟩

#print axioms tail_summable_and_bound
end
end Erdos708H97.Proofs
