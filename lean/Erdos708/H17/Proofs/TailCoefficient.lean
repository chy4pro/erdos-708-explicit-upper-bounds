import Erdos708.H17.Proofs.Pointwise
open Finset BigOperators Polynomial
namespace Erdos708H17.Proofs
noncomputable section
set_option maxHeartbeats 2000000

def tailPoly (h : ℕ) : Polynomial ℝ := (countingPolynomial h).map (Nat.castRingHom ℝ)

lemma tailPoly_eval (h : ℕ) : (tailPoly h).eval (1/4) = 1 + ∑ j ∈ range (h+1), (1/4:ℝ)^(2^j) := by
  simp [tailPoly,countingPolynomial,Polynomial.map_sum,eval_finsetSum]

lemma sparse_geometric_bound (h : ℕ) :
    (∑ j ∈ range (h+1), (1/4:ℝ)^(2^j)) < (633/2000:ℝ) := by
  have htail : ∀ j : ℕ, (1/4:ℝ)^(2^(j+3)) ≤ (1/65536:ℝ)*(1/65536:ℝ)^j := by
    intro j
    have hn : 8*(j+1) ≤ 2^(j+3) := by
      rw [pow_add]
      have hj : j+1 ≤ 2^j := Nat.lt_two_pow_self
      nlinarith
    calc
      _ ≤ (1/4:ℝ)^(8*(j+1)) := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
      _ = _ := by rw [pow_mul,pow_succ]; norm_num; ring
  have ht : ∀ k : ℕ, (∑ j ∈ range k, (1/4:ℝ)^(2^(j+3))) ≤ 1/65535 := by
    intro k
    calc
      _ ≤ ∑ j ∈ range k, (1/65536:ℝ)*(1/65536:ℝ)^j := sum_le_sum (fun j _ => htail j)
      _ ≤ ∑' j : ℕ, (1/65536:ℝ)*(1/65536:ℝ)^j :=
        Summable.sum_le_tsum _ (fun j _ => by positivity)
          ((summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/65536) (by norm_num : (1/65536:ℝ) < 1)).mul_left _)
      _ = _ := by rw [tsum_mul_left,tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/65536) (by norm_num : (1/65536:ℝ) < 1)]; norm_num
  by_cases hh : h+1 ≤ 3
  · have hh' : (∑ j ∈ range (h+1), (1/4:ℝ)^(2^j)) ≤ ∑ j ∈ range 3, (1/4:ℝ)^(2^j) :=
      sum_le_sum_of_subset_of_nonneg (range_mono hh) (fun _ _ _ => by positivity)
    norm_num [sum_range_succ] at hh' ⊢
    linarith
  · have heq : h+1 = 3+(h-2) := by omega
    rw [heq,sum_range_add]
    have hh' := ht (h-2)
    simp only [add_comm 3] at *
    norm_num [sum_range_succ] at *
    linarith

lemma tailPoly_eval_lt (h : ℕ) : (tailPoly h).eval (1/4) < (2633/2000:ℝ) := by
  rw [tailPoly_eval]
  linarith [sparse_geometric_bound h]

lemma coefficient_envelope (h N : ℕ) :
    (carrierCount h N : ℝ) ≤ (4:ℝ)^(2^h+1)*(2633/2000:ℝ)^N := by
  let p : Polynomial ℝ := ((countingPolynomial h)^N).map (Nat.castRingHom ℝ)
  have hc : ∀ s, 0 ≤ p.coeff s := by intro s; simp only [p,coeff_map]; exact Nat.cast_nonneg _
  have he : p.eval (1/4) = (tailPoly h).eval (1/4)^N := by simp [p,tailPoly]
  have hb : p.coeff (2^h+1)*(1/4:ℝ)^(2^h+1) ≤ p.eval (1/4) := by
    rw [eval_eq_sum,Polynomial.sum]
    by_cases hm : 2^h+1 ∈ p.support
    · exact single_le_sum (fun s _ => mul_nonneg (hc s) (by positivity)) hm
    · simp only [(notMem_support_iff.mp hm),zero_mul]
      exact sum_nonneg (fun s _ => mul_nonneg (hc s) (by positivity))
  have hp0 : 0 ≤ (tailPoly h).eval (1/4) := by rw [tailPoly_eval]; positivity
  have hb' := hb.trans (he ▸ pow_le_pow_left₀ hp0 (tailPoly_eval_lt h).le N)
  have heq : p.coeff (2^h+1) = (carrierCount h N : ℝ) := by simp only [p,carrierCount,coeff_map]; rfl
  rw [heq] at hb'
  have hmul := mul_le_mul_of_nonneg_left hb' (show 0 ≤ (4:ℝ)^(2^h+1) by positivity)
  calc
    _ = (4:ℝ)^(2^h+1)*((carrierCount h N:ℝ)*(1/4:ℝ)^(2^h+1)) := by
      rw [mul_left_comm,← mul_pow]; norm_num
    _ ≤ _ := hmul

#print axioms sparse_geometric_bound
#print axioms coefficient_envelope
end
end Erdos708H17.Proofs
