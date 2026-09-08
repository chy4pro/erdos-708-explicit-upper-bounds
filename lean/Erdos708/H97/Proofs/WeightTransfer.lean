import Erdos708.H17.ChainParts.Weights
open Finset BigOperators Erdos708H17Chain Erdos708H17Chain.Proofs
namespace Erdos708H97.Proofs

lemma capped_to_weight (z : Weight) (m x : ℕ) (c : ℝ)
    (hc : hingeSum (capped z) c 0 m ≤ hingeSum (capped z) 1 x m) :
    hingeSum (w z) c 0 m ≤ hingeSum (w z) 1 x m := by
  have hL : hingeSum (w z) c 0 m ≤ (∑ k ∈ Icc 1 m, excess z k) + hingeSum (capped z) c 0 m := by
    have h := sum_le_sum (s := Icc 1 m) (fun k _ => peel_left z k c)
    rw [sum_add_distrib] at h
    simpa only [hingeSum, zero_add] using h
  have hR : hingeSum (w z) 1 x m = (∑ b ∈ Icc (x+1) (x+m), excess z b) + hingeSum (capped z) 1 x m := by
    unfold hingeSum
    simp_rw [peel_right, sum_add_distrib]
  have he := excess_window z m x
  rw [hR]
  linarith

lemma atoms_to_capped (z : Weight) (m x : ℕ) (c : ℝ)
    (ha : hingeSum (S (ofWeight z m)) c 0 m ≤ hingeSum (S (ofWeight z m)) 1 x m) :
    hingeSum (capped z) c 0 m ≤ hingeSum (capped z) 1 x m := by
  have hL : hingeSum (S (ofWeight z m)) c 0 m = hingeSum (capped z) c 0 m := by
    apply sum_congr rfl
    intro k hk
    rw [ofWeight_capped_eq z m k (by simpa using hk)]
  have hR : hingeSum (S (ofWeight z m)) 1 x m ≤ hingeSum (capped z) 1 x m := by
    apply sum_le_sum
    intro b hb
    apply max_le_max _ le_rfl
    exact sub_le_sub_right (ofWeight_capped_le z m b (by have := (mem_Icc.mp hb).1; omega)) 1
  rw [hL] at ha
  exact ha.trans hR


#print axioms capped_to_weight
#print axioms atoms_to_capped
end Erdos708H97.Proofs
