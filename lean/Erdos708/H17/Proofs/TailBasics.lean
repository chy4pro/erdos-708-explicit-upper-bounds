import Erdos708.H17.Proofs.Pointwise
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Real.Pi.Bounds
open Finset BigOperators
namespace Erdos708H17.Proofs
noncomputable section
set_option maxHeartbeats 2000000

def tailF : ℝ := 2633/2000
def tailQ : ℝ := (3/4:ℝ)^128
def tailA : ℝ := 192*gamma*tailF/(K*128^2)
def tailMajorant (j : ℕ) : ℝ := 96*gamma*tailQ^(j+1) + tailA*(1/4:ℝ)^j

lemma exp_le_tailE : Real.exp 1 ≤ 87/32 := by linarith [Real.exp_one_lt_d9]
lemma factorial_lower (r : ℕ) (hr : 1 ≤ r) : ((r:ℝ)/(87/32))^r ≤ (Nat.factorial r : ℝ) := by
  have he := exp_le_tailE
  have hrR : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hs : 1 ≤ Real.sqrt (2*Real.pi*r) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [Real.pi_gt_three]
  calc
    _ ≤ ((r:ℝ)/Real.exp 1)^r := by gcongr
    _ ≤ Real.sqrt (2*Real.pi*r)*((r:ℝ)/Real.exp 1)^r := by
      have hh := mul_le_mul_of_nonneg_right hs (show 0 ≤ ((r:ℝ)/Real.exp 1)^r by positivity)
      simpa using hh
    _ ≤ _ := Stirling.le_factorial_stirling r

lemma tail_base_bounds :
    (4:ℝ)^16 * tailF^51 * (29725/49152:ℝ)^72 < 1 ∧
    (16:ℝ)*tailF^4*(29725/49152:ℝ)^9 < 9/16 := by norm_num [tailF]
lemma tail_scalar_bound : 96*gamma*tailQ/(1-tailQ) + 256*gamma*tailF/(K*128^2) < (1/100:ℝ) := by
  norm_num [gamma,tailQ,tailF,K]


#print axioms factorial_lower
#print axioms tail_base_bounds
#print axioms tail_scalar_bound
end
end Erdos708H17.Proofs
