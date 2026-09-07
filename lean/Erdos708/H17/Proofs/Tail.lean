import Erdos708.H17.Proofs.TailLarge
open Finset BigOperators
namespace Erdos708H17.Proofs
noncomputable section
set_option maxHeartbeats 2000000

/-- The analytic tail follows from the two coefficient-count ranges. -/
theorem analytic_tail_envelope : ∀ j : ℕ, numericTerm (j+7) ≤ tailMajorant j := by
  intro j
  obtain ⟨N,hN,heq⟩ := exists_mem_eq_sup' (show (range (countLimit (j+7)+1)).Nonempty by simp) (countRatio (j+7))
  have hN' : N ≤ countLimit (j+7) := by have := mem_range.mp hN; omega
  change 24*epsilon (j+7)*Rscale (j+7) ≤ _
  unfold Rscale
  rw [heq]
  by_cases hn : N < 2*2^(j+7)
  · have hs := small_scale_bound (j+7) (by omega) N hn
    have hp : (3/4:ℝ)^(2^(j+7)) ≤ tailQ^(j+1) := by
      unfold tailQ
      rw [← pow_mul]
      apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
      rw [(tail_scales j).1]
      have hj : j+1 ≤ 2^j := Nat.lt_two_pow_self
      omega
    calc
      _ ≤ 96*gamma*(3/4:ℝ)^(2^(j+7)) := hs
      _ ≤ 96*gamma*tailQ^(j+1) := mul_le_mul_of_nonneg_left hp (by unfold gamma; positivity)
      _ ≤ _ := le_add_of_nonneg_right (by unfold tailA gamma tailF K; positivity)
  · have hs := large_scale_bound j N (by omega) hN'
    have he : 192*gamma*tailF/(K*((2:ℝ)^(j+7))^2) = tailA*(1/4:ℝ)^j := by
      unfold tailA
      rw [pow_add]
      norm_num
      rw [mul_pow,← pow_mul, Nat.mul_comm j 2,pow_mul]
      norm_num
      rw [div_pow]
      field_simp <;> ring
    rw [he] at hs
    exact hs.trans (le_add_of_nonneg_left (by unfold gamma tailQ; positivity))

lemma analytic_tail : Summable (fun j => numericTerm (j+7)) ∧
    (∑' j, numericTerm (j+7)) < (1/100:ℝ) := by
  have hq0 : 0 ≤ tailQ := by norm_num [tailQ]
  have hq1 : tailQ < 1 := by norm_num [tailQ]
  have hq := summable_geometric_of_lt_one hq0 hq1
  have hr := summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num : (1/4:ℝ) < 1)
  have hmajor : Summable tailMajorant := by
    have hfirst : Summable (fun j : ℕ => 96*gamma*tailQ^(j+1)) := by
      exact ((hq.mul_right tailQ).mul_left (96*gamma)).congr (fun j => by rw [pow_succ])
    exact hfirst.add (hr.mul_left tailA)
  have hs := Summable.of_nonneg_of_le (fun j => numericTerm_nonneg (j+7)) analytic_tail_envelope hmajor
  refine ⟨hs, ?_⟩
  apply (hs.tsum_le_tsum analytic_tail_envelope hmajor).trans_lt
  have heq : (∑' j, tailMajorant j) = 96*gamma*tailQ/(1-tailQ) + 256*gamma*tailF/(K*128^2) := by
    simp only [tailMajorant,pow_succ]
    rw [Summable.tsum_add (by exact (hq.mul_right tailQ).mul_left (96*gamma)) (hr.mul_left tailA)]
    simp only [tsum_mul_left,tsum_mul_right,tsum_geometric_of_lt_one hq0 hq1,
      tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num : (1/4:ℝ) < 1),tailA]
    ring
  rw [heq]
  exact tail_scalar_bound

#print axioms analytic_tail_envelope
#print axioms analytic_tail
end
end Erdos708H17.Proofs
