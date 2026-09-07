import Erdos708.H17.Proofs.NumericRows1
open Finset BigOperators
namespace Erdos708H17.Proofs
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024

lemma rows1_ratio_bound : ∀ N ∈ range (countLimit 1+1),
    ratioQ 1 N ((rows1[N]?.getD [])[3]?.getD 0) ≤ (14/1:ℚ) := by
  intro N hN
  norm_num [countLimit,mem_range] at hN
  interval_cases N
  · change ratioQ 1 0 0 ≤ (14/1:ℚ)
    norm_num [ratioQ]
  · change ratioQ 1 1 0 ≤ (14/1:ℚ)
    norm_num [ratioQ]
  · change ratioQ 1 2 2 ≤ (14/1:ℚ)
    norm_num [ratioQ]
  · change ratioQ 1 3 7 ≤ (14/1:ℚ)
    norm_num [ratioQ]
  · change ratioQ 1 4 16 ≤ (14/1:ℚ)
    norm_num [ratioQ]
  · change ratioQ 1 5 30 ≤ (14/1:ℚ)
    norm_num [ratioQ]
  · change ratioQ 1 6 50 ≤ (14/1:ℚ)
    norm_num [ratioQ]
  · change ratioQ 1 7 77 ≤ (14/1:ℚ)
    norm_num [ratioQ]

theorem rows1_bound : ∀ N ∈ range (countLimit 1+1),
    24*epsilonQ 1*ratioQ 1 N ((rows1[N]?.getD [])[3]?.getD 0) < capQ 1 := by
  have he : 0 ≤ 24*epsilonQ 1 := by norm_num [epsilonQ,momentOrder]
  have hb : 24*epsilonQ 1*(14/1:ℚ) < capQ 1 := by norm_num [epsilonQ,momentOrder,capQ]
  intro N hN
  exact (mul_le_mul_of_nonneg_left (rows1_ratio_bound N hN) he).trans_lt hb
#print axioms rows1_ratio_bound
#print axioms rows1_bound
end Erdos708H17.Proofs
