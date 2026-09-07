import Erdos708.H17.Proofs.NumericTables
import Erdos708.H17.Proofs.Tail
open Finset BigOperators
namespace Erdos708H17.Proofs
noncomputable section
attribute [local instance] Classical.propDecidable

lemma epsilonQ_cast (h : ℕ) : (epsilonQ h : ℝ) = epsilon h := by
  unfold epsilonQ epsilon gamma Hstar
  split_ifs <;> push_cast <;> rfl
lemma ratioQ_cast (h N c : ℕ) : (ratioQ h N c : ℝ) =
    (c:ℝ)*max (1-max 0 (((N:ℝ)-2^h-1)/2^h)/K) 0 /
      max (1/2^h) (((N:ℝ)-2^h)/2^h) := by
  unfold ratioQ K
  push_cast
  rfl
lemma numericRows_coeff (h N : ℕ) (hh : h < 7) (hN : N ≤ countLimit h) :
    (((numericRows h)[N]?.getD [])[2^h+1]?.getD 0) = carrierCount h N := by
  exact row_certificate_correct h (countLimit h) (numericRows h)
    (numericRows_valid h hh).1 (numericRows_valid h hh).2 N hN _ (by omega)

lemma finite_scale_bound (h : ℕ) (hh : h < 7) : numericTerm h < (capQ h : ℝ) := by
  obtain ⟨N,hN,heq⟩ := exists_mem_eq_sup' (show (range (countLimit h+1)).Nonempty by simp) (countRatio h)
  have hq := numericRows_bound h hh N hN
  have hreal : (24:ℝ)*(epsilonQ h : ℝ)*(ratioQ h N (((numericRows h)[N]?.getD [])[2^h+1]?.getD 0) : ℝ) < (capQ h : ℝ) := by exact_mod_cast hq
  rw [epsilonQ_cast, ratioQ_cast,numericRows_coeff h N hh (by have := mem_range.mp hN; omega)] at hreal
  simpa only [numericTerm, Rscale, heq,countRatio] using hreal

lemma finite_sum_bound : (∑ h ∈ range 7, numericTerm h) < (313829/400000:ℝ) := by
  have hs : (∑ h ∈ range 7, numericTerm h) < ∑ h ∈ range 7, (capQ h : ℝ) :=
    sum_lt_sum (fun h hh => (finite_scale_bound h (mem_range.mp hh)).le)
      ⟨0, by simp, finite_scale_bound 0 (by omega)⟩
  convert hs using 1 <;> norm_num [sum_range_succ,capQ]

lemma numerical_sum : Summable numericTerm ∧ (∑' h, numericTerm h) < (4/5:ℝ) := by
  have ht := analytic_tail
  have hs : Summable numericTerm := (summable_nat_add_iff 7).mp ht.1
  refine ⟨hs, ?_⟩
  rw [← hs.sum_add_tsum_nat_add 7]
  linarith [finite_sum_bound,ht.2]

#print axioms finite_scale_bound
#print axioms finite_sum_bound
#print axioms numerical_sum
end
end Erdos708H17.Proofs
