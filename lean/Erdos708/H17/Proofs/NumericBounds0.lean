import Erdos708.H17.Proofs.NumericRows0
open Finset BigOperators
namespace Erdos708H17.Proofs
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024

lemma rows0_ratio_bound : ∀ N ∈ range (countLimit 0+1),
    ratioQ 0 N ((rows0[N]?.getD [])[2]?.getD 0) ≤ (1/1:ℚ) := by
  intro N hN
  norm_num [countLimit,mem_range] at hN
  interval_cases N
  · change ratioQ 0 0 0 ≤ (1/1:ℚ)
    norm_num [ratioQ]
  · change ratioQ 0 1 0 ≤ (1/1:ℚ)
    norm_num [ratioQ]
  · change ratioQ 0 2 1 ≤ (1/1:ℚ)
    norm_num [ratioQ]
  · change ratioQ 0 3 3 ≤ (1/1:ℚ)
    norm_num [ratioQ]
  · change ratioQ 0 4 6 ≤ (1/1:ℚ)
    norm_num [ratioQ]

theorem rows0_bound : ∀ N ∈ range (countLimit 0+1),
    24*epsilonQ 0*ratioQ 0 N ((rows0[N]?.getD [])[2]?.getD 0) < capQ 0 := by
  have he : 0 ≤ 24*epsilonQ 0 := by norm_num [epsilonQ,momentOrder]
  have hb : 24*epsilonQ 0*(1/1:ℚ) < capQ 0 := by norm_num [epsilonQ,momentOrder,capQ]
  intro N hN
  exact (mul_le_mul_of_nonneg_left (rows0_ratio_bound N hN) he).trans_lt hb
#print axioms rows0_ratio_bound
#print axioms rows0_bound
end Erdos708H17.Proofs
