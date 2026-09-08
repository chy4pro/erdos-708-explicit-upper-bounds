import Erdos708.H97.Proofs.Capped
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
open Finset BigOperators
namespace Erdos708H97.Proofs
noncomputable section
set_option maxHeartbeats 2000000

lemma product_esymm {ι : Type*} [DecidableEq ι] (s : Finset ι) (u : ι → ℝ) (t : ℝ) :
    (∏ i ∈ s, (1+t*u i)) = ∑ r ∈ range (s.card+1), t^r*esymm s u r := by
  have he : (∏ i ∈ s, (1+t*u i)) = ∏ i ∈ s, (t*u i+1) := by
    apply prod_congr rfl
    intro i hi
    ring
  rw [he,prod_add]
  simp only [prod_const_one,mul_one,prod_mul_distrib,prod_const]
  rw [sum_powerset]
  apply sum_congr rfl
  intro r hr
  rw [Erdos708H17.esymm,mul_sum]
  apply sum_congr rfl
  intro v hv
  rw [(mem_powersetCard.mp hv).2]

lemma exp_chord (t u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.exp (t*u) ≤ 1+(Real.exp t-1)*u := by
  have hh := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ t)
    (sub_nonneg.mpr hu1) hu0 (show 1-u+u=1 by ring)
  simp only [smul_eq_mul,mul_zero,zero_add,Real.exp_zero,mul_one] at hh
  simpa only [mul_comm t u,show (1-u)+u*Real.exp t = 1+(Real.exp t-1)*u by ring] using hh

lemma finite_exponential_moment (s : Finset ℕ) (u : ℕ → ℕ → ℝ) (N : ℕ) (μ t : ℝ)
    (hμ : 0 ≤ μ) (ht : 0 ≤ t)
    (hu : ∀ n ∈ Icc 1 N, ∀ p ∈ s, 0 ≤ u n p ∧ u n p ≤ 1)
    (hmom : ∀ r : ℕ, (∑ n ∈ Icc 1 N, esymm s (u n) r) ≤ (N : ℝ)*μ^r/(Nat.factorial r : ℝ)) :
    (∑ n ∈ Icc 1 N, Real.exp (t*∑ p ∈ s, u n p)) ≤ (N : ℝ)*Real.exp ((Real.exp t-1)*μ) := by
  have hz : 0 ≤ Real.exp t-1 := by have := Real.one_le_exp_iff.mpr ht; linarith
  have hpoint (n : ℕ) (hn : n ∈ Icc 1 N) : Real.exp (t*∑ p ∈ s, u n p) ≤
      ∑ r ∈ range (s.card+1), (Real.exp t-1)^r*esymm s (u n) r := by
    rw [← product_esymm,mul_sum,Real.exp_sum]
    apply prod_le_prod (fun p hp => (Real.exp_pos _).le)
    intro p hp
    exact exp_chord t (u n p) (hu n hn p hp).1 (hu n hn p hp).2
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ∑ r ∈ range (s.card+1), (Real.exp t-1)^r*esymm s (u n) r := sum_le_sum hpoint
    _ = ∑ r ∈ range (s.card+1), (Real.exp t-1)^r*∑ n ∈ Icc 1 N, esymm s (u n) r := by
      rw [sum_comm]
      simp only [mul_sum]
    _ ≤ ∑ r ∈ range (s.card+1), (Real.exp t-1)^r*((N : ℝ)*μ^r/(Nat.factorial r : ℝ)) :=
      sum_le_sum (fun r _ => mul_le_mul_of_nonneg_left (hmom r) (pow_nonneg hz r))
    _ = (N : ℝ)*∑ r ∈ range (s.card+1), ((Real.exp t-1)*μ)^r/(Nat.factorial r : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro r hr
      rw [mul_pow]
      ring
    _ ≤ (N : ℝ)*∑' r : ℕ, ((Real.exp t-1)*μ)^r/(Nat.factorial r : ℝ) :=
      mul_le_mul_of_nonneg_left ((Real.summable_pow_div_factorial _).sum_le_tsum _
        (fun r _ => div_nonneg (pow_nonneg (mul_nonneg hz hμ) r) (Nat.cast_nonneg _))) (Nat.cast_nonneg _)
    _ = _ := by
      congr 1
      rw [Real.exp_eq_exp_ℝ,NormedSpace.exp_eq_tsum_div]

lemma hinge_exp_bound (y t : ℝ) (ht : 0 < t) :
    max y 0 ≤ Real.exp (t*y)/(Real.exp 1*t) := by
  have he := Real.add_one_le_exp (t*y-1)
  rw [Real.exp_sub] at he
  have he1 := Real.exp_pos 1
  apply max_le
  · apply (le_div_iff₀ (mul_pos he1 ht)).mpr
    have hh : t*y*Real.exp 1 ≤ Real.exp (t*y) :=
      (le_div_iff₀ he1).mp (by linarith : t*y ≤ Real.exp (t*y)/Real.exp 1)
    nlinarith
  · positivity

#print axioms finite_exponential_moment
#print axioms hinge_exp_bound
end
end Erdos708H97.Proofs
