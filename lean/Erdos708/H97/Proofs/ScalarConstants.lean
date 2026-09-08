import Erdos708.H97.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
open Finset BigOperators
namespace Erdos708H97.Proofs
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 1024

lemma threshold_identity : D0+rho*T = (97/10 : ℝ) := by norm_num [D0,rho,T]
lemma dense_margin : 1 < (1-(Q : ℝ)⁻¹)*Hstar-Hstar^8/(Nat.factorial 8 : ℝ) := by
  norm_num [Q,Hstar]
lemma window_margin : lambda*(1-2*gamma*Hstar/K) = (718539/573440 : ℝ) ∧
    (718539/573440 : ℝ)-rho = 1739/573440 ∧ rho < (718539/573440 : ℝ) := by
  norm_num [lambda,gamma,Hstar,K,rho]
lemma exp_one_bounds : (8/3 : ℝ) < Real.exp 1 ∧ Real.exp 1 < 87/32 := by
  constructor <;> linarith [Real.exp_one_gt_d9,Real.exp_one_lt_d9]
lemma log_z_aux : (87/32 : ℝ)^3 < (9/2)^2 := by norm_num
lemma chernoff_base_rational : (133/4 : ℝ)^100 < a0^100*(9/2)^441 := by norm_num [a0]
lemma low_base_rational : (4/5 : ℝ)^4 < (3/4)^3 := by norm_num

/-- Taylor's theorem at one quarter of the argument, then the fourth power. -/
lemma exp_Hstar_upper : Real.exp ((7/2)*Hstar) < 133/4 := by
  let u : ℝ := (7/8)*Hstar
  let b : ℝ := (∑ k ∈ range 12, u^k/(Nat.factorial k : ℝ)) + u^12*13/(Nat.factorial 12*12)
  have hu0 : 0 ≤ u := by norm_num [u,Hstar]
  have hu1 : u ≤ 1 := by norm_num [u,Hstar]
  have he : Real.exp u ≤ b := by
    simpa only [b,Nat.cast_ofNat,show (12 : ℝ)+1 = 13 by norm_num] using Real.exp_bound' hu0 hu1 (by norm_num : 0 < (12 : ℕ))
  have hpow : (Real.exp u)^4 ≤ b^4 := pow_le_pow_left₀ (Real.exp_pos u).le he 4
  have hb : b^4 < (133/4 : ℝ) := by norm_num [b,u,Hstar,sum_range_succ]
  have hid : (Real.exp u)^4 = Real.exp ((7/2)*Hstar) := by
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp [u]
    ring
  rw [hid] at hpow
  exact hpow.trans_lt hb

/-- The finite four bands and a geometric remainder for all omitted degrees >=128. -/
def generatingUpper (j : ℕ) (x : ℝ) : ℝ :=
  1+(∑ a ∈ Icc j 7, x^a)+
    (∑ r ∈ Icc 1 4, ∑ a ∈ Icc 4 7, x^(a*2^r))+x^128/(1-x)

lemma tail_parameters (j : ℕ) (hj : j ∈ Icc 4 7) :
    0 < tailX j ∧ tailX j < 1 ∧ (5/4 : ℝ) ≤ tailF j ∧
    generatingUpper j (tailX j) ≤ tailF j ∧
    a0^3*(tailX j)⁻¹^(3*j)*(tailF j)^11 < 1 := by
  obtain ⟨hlo,hhi⟩ := mem_Icc.mp hj
  interval_cases j <;> norm_num [tailX,tailF,a0,generatingUpper,sum_Icc_succ_top]

lemma tail_scalar_bound : tailBound < (3/1000 : ℝ) := by
  norm_num [tailBound,tailD,tailX,tailF,sum_Icc_succ_top]

lemma finite_numerator_sum :
    (24680+128711+25773+5665+1025+150+21+3 : ℕ) = 186028 := by norm_num
lemma pointwise_margin : lambda*(187/1000+3/1000) = (969/1000 : ℝ) ∧ (969/1000 : ℝ) < 1 := by
  norm_num [lambda]

#print axioms chernoff_base_rational
#print axioms exp_Hstar_upper
#print axioms tail_parameters
#print axioms tail_scalar_bound
end
end Erdos708H97.Proofs
