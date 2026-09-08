import Erdos708.H97.Proofs.GeneratingSeries
import Erdos708.H97.Proofs.Chernoff
open Finset BigOperators Polynomial
namespace Erdos708H97.Proofs
noncomputable section
set_option maxHeartbeats 2000000

lemma coefficient_envelope (j L d N : ℕ) (hj : j ∈ Icc 4 7) :
    (carrierCount j L d N : ℝ) ≤ (tailX j)⁻¹^(L+d)*(tailF j)^N := by
  let x := tailX j
  let p : Polynomial ℝ := ((countingPolynomial j L)^N).map (Nat.castRingHom ℝ)
  have hx : 0 < x := (tail_parameters j hj).1
  have hx1 : x < 1 := (tail_parameters j hj).2.1
  have hc : ∀ s, 0 ≤ p.coeff s := by intro s; simp only [p,coeff_map]; exact Nat.cast_nonneg _
  have he : p.eval x = (1+∑ e ∈ exponents j L, x^e)^N := by
    simp [p,countingPolynomial,Polynomial.map_sum,eval_finsetSum]
  have hb : p.coeff (L+d)*x^(L+d) ≤ p.eval x := by
    rw [eval_eq_sum,Polynomial.sum]
    by_cases hm : L+d ∈ p.support
    · exact single_le_sum (fun s _ => mul_nonneg (hc s) (pow_nonneg hx.le s)) hm
    · simp only [notMem_support_iff.mp hm,zero_mul]
      exact sum_nonneg (fun s _ => mul_nonneg (hc s) (pow_nonneg hx.le _))
  have hF := (finite_generating_le j L hj x hx.le hx1).trans (generating_series_bound j hj)
  have hb' := hb.trans (he ▸ pow_le_pow_left₀ (by positivity) hF N)
  have hcount : (carrierCount j L d N : ℝ) ≤ p.coeff (L+d) := by
    simp only [p,coeff_map,carrierCount]
    exact Nat.cast_le.mpr (Nat.sub_le (((countingPolynomial j L)^N).coeff (L+d)) (((omittedPolynomial j L)^N).coeff (L+d)))
  have hh := (mul_le_mul_of_nonneg_right hcount (pow_nonneg hx.le _)).trans hb'
  have hmul := mul_le_mul_of_nonneg_left hh (pow_nonneg (inv_nonneg.mpr hx.le) (L+d))
  calc
    _ = x⁻¹^(L+d)*((carrierCount j L d N : ℝ)*x^(L+d)) := by
      rw [mul_left_comm,← mul_pow,inv_mul_cancel₀ hx.ne',one_pow,mul_one]
    _ ≤ _ := hmul

lemma log_F_lower (j : ℕ) (hj : j ∈ Icc 4 7) : (2/9 : ℝ) < Real.log (tailF j) := by
  have hb := Real.exp_bound' (by norm_num : (0:ℝ)≤2/9) (by norm_num : (2/9:ℝ)≤1) (by norm_num : 0<(8:ℕ))
  have he : Real.exp (2/9) < (5/4:ℝ) := by
    norm_num [sum_range_succ] at hb
    linarith
  have hh := Real.log_lt_log (Real.exp_pos _) he
  rw [Real.log_exp] at hh
  exact hh.trans_le (Real.log_le_log (by norm_num) (tail_parameters j hj).2.2.1)

lemma tail_log_bases (j : ℕ) (hj : j ∈ Icc 4 7) :
    Real.log a0-(j:ℝ)*Real.log (tailX j)+(11/3)*Real.log (tailF j) < 0 ∧
    Real.log a0-(j:ℝ)*Real.log (tailX j)+(7/3)*Real.log (tailF j) ≤ Real.log (3/4) := by
  have hx := (tail_parameters j hj).1
  have hF : 0 < tailF j := lt_of_lt_of_le (by norm_num : (0:ℝ)<5/4) (tail_parameters j hj).2.2.1
  have ha0 : 0 < a0 := by norm_num [a0]
  have hbase := (tail_parameters j hj).2.2.2.2
  have hlog := Real.log_lt_log (by positivity : (0:ℝ)<a0^3*(tailX j)⁻¹^(3*j)*(tailF j)^11) hbase
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
    Real.log_pow,Real.log_pow,Real.log_pow,Real.log_inv,Real.log_one] at hlog
  push_cast at hlog
  have hq : Real.log a0-(j:ℝ)*Real.log (tailX j)+(11/3)*Real.log (tailF j) < 0 := by linarith
  refine ⟨hq,?_⟩
  have hlow : (1:ℝ) < (3/4:ℝ)^3*(5/4:ℝ)^4 := by norm_num
  have hh := Real.log_lt_log (by norm_num : (0:ℝ)<1) hlow
  rw [Real.log_mul (by norm_num) (by norm_num),Real.log_pow,Real.log_pow,Real.log_one] at hh
  have hf := Real.log_le_log (by norm_num : (0:ℝ)<5/4) (tail_parameters j hj).2.2.1
  norm_num only [Nat.cast_ofNat] at hh
  linarith

#print axioms coefficient_envelope
#print axioms tail_log_bases
end
end Erdos708H97.Proofs
