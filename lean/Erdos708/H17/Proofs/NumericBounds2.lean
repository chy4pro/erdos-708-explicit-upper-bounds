import Erdos708.H17.Proofs.NumericRows2
open Finset BigOperators
namespace Erdos708H17.Proofs
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024

lemma rows2_ratio_bound : ∀ N ∈ range (countLimit 2+1),
    ratioQ 2 N ((rows2[N]?.getD [])[5]?.getD 0) ≤ (3084/7:ℚ) := by
  intro N hN
  norm_num [countLimit,mem_range] at hN
  interval_cases N
  · change ratioQ 2 0 0 ≤ (3084/7:ℚ)
    norm_num [ratioQ]
  · change ratioQ 2 1 0 ≤ (3084/7:ℚ)
    norm_num [ratioQ]
  · change ratioQ 2 2 2 ≤ (3084/7:ℚ)
    norm_num [ratioQ]
  · change ratioQ 2 3 9 ≤ (3084/7:ℚ)
    norm_num [ratioQ]
  · change ratioQ 2 4 28 ≤ (3084/7:ℚ)
    norm_num [ratioQ]
  · change ratioQ 2 5 71 ≤ (3084/7:ℚ)
    norm_num [ratioQ]
  · change ratioQ 2 6 156 ≤ (3084/7:ℚ)
    norm_num [ratioQ]
  · change ratioQ 2 7 308 ≤ (3084/7:ℚ)
    norm_num [ratioQ]
  · change ratioQ 2 8 560 ≤ (3084/7:ℚ)
    norm_num [ratioQ]
  · change ratioQ 2 9 954 ≤ (3084/7:ℚ)
    norm_num [ratioQ]
  · change ratioQ 2 10 1542 ≤ (3084/7:ℚ)
    norm_num [ratioQ]
  · change ratioQ 2 11 2387 ≤ (3084/7:ℚ)
    norm_num [ratioQ]
  · change ratioQ 2 12 3564 ≤ (3084/7:ℚ)
    norm_num [ratioQ]
  · change ratioQ 2 13 5161 ≤ (3084/7:ℚ)
    norm_num [ratioQ]

theorem rows2_bound : ∀ N ∈ range (countLimit 2+1),
    24*epsilonQ 2*ratioQ 2 N ((rows2[N]?.getD [])[5]?.getD 0) < capQ 2 := by
  have he : 0 ≤ 24*epsilonQ 2 := by norm_num [epsilonQ,momentOrder]
  have hb : 24*epsilonQ 2*(3084/7:ℚ) < capQ 2 := by norm_num [epsilonQ,momentOrder,capQ]
  intro N hN
  exact (mul_le_mul_of_nonneg_left (rows2_ratio_bound N hN) he).trans_lt hb
#print axioms rows2_ratio_bound
#print axioms rows2_bound
end Erdos708H17.Proofs
