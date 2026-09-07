import Erdos708.H17.Proofs.NumericRows3
open Finset BigOperators
namespace Erdos708H17.Proofs
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024

lemma rows3_ratio_bound : ∀ N ∈ range (countLimit 3+1),
    ratioQ 3 N ((rows3[N]?.getD [])[9]?.getD 0) ≤ (4309096/3:ℚ) := by
  intro N hN
  norm_num [countLimit,mem_range] at hN
  interval_cases N
  · change ratioQ 3 0 0 ≤ (4309096/3:ℚ)
    norm_num [ratioQ]
  · change ratioQ 3 1 0 ≤ (4309096/3:ℚ)
    norm_num [ratioQ]
  · change ratioQ 3 2 2 ≤ (4309096/3:ℚ)
    norm_num [ratioQ]
  · change ratioQ 3 3 9 ≤ (4309096/3:ℚ)
    norm_num [ratioQ]
  · change ratioQ 3 4 36 ≤ (4309096/3:ℚ)
    norm_num [ratioQ]
  · change ratioQ 3 5 135 ≤ (4309096/3:ℚ)
    norm_num [ratioQ]
  · change ratioQ 3 6 446 ≤ (4309096/3:ℚ)
    norm_num [ratioQ]
  · change ratioQ 3 7 1295 ≤ (4309096/3:ℚ)
    norm_num [ratioQ]
  · change ratioQ 3 8 3368 ≤ (4309096/3:ℚ)
    norm_num [ratioQ]
  · change ratioQ 3 9 7999 ≤ (4309096/3:ℚ)
    norm_num [ratioQ]
  · change ratioQ 3 10 17620 ≤ (4309096/3:ℚ)
    norm_num [ratioQ]
  · change ratioQ 3 11 36432 ≤ (4309096/3:ℚ)
    norm_num [ratioQ]
  · change ratioQ 3 12 71368 ≤ (4309096/3:ℚ)
    norm_num [ratioQ]
  · change ratioQ 3 13 133432 ≤ (4309096/3:ℚ)
    norm_num [ratioQ]
  · change ratioQ 3 14 239512 ≤ (4309096/3:ℚ)
    norm_num [ratioQ]
  · change ratioQ 3 15 414780 ≤ (4309096/3:ℚ)
    norm_num [ratioQ]
  · change ratioQ 3 16 695808 ≤ (4309096/3:ℚ)
    norm_num [ratioQ]
  · change ratioQ 3 17 1134546 ≤ (4309096/3:ℚ)
    norm_num [ratioQ]
  · change ratioQ 3 18 1803326 ≤ (4309096/3:ℚ)
    norm_num [ratioQ]
  · change ratioQ 3 19 2801075 ≤ (4309096/3:ℚ)
    norm_num [ratioQ]
  · change ratioQ 3 20 4260940 ≤ (4309096/3:ℚ)
    norm_num [ratioQ]
  · change ratioQ 3 21 6359549 ≤ (4309096/3:ℚ)
    norm_num [ratioQ]
  · change ratioQ 3 22 9328154 ≤ (4309096/3:ℚ)
    norm_num [ratioQ]
  · change ratioQ 3 23 13465925 ≤ (4309096/3:ℚ)
    norm_num [ratioQ]
  · change ratioQ 3 24 19155688 ≤ (4309096/3:ℚ)
    norm_num [ratioQ]
  · change ratioQ 3 25 26882425 ≤ (4309096/3:ℚ)
    norm_num [ratioQ]
  · change ratioQ 3 26 37254880 ≤ (4309096/3:ℚ)
    norm_num [ratioQ]

theorem rows3_bound : ∀ N ∈ range (countLimit 3+1),
    24*epsilonQ 3*ratioQ 3 N ((rows3[N]?.getD [])[9]?.getD 0) < capQ 3 := by
  have he : 0 ≤ 24*epsilonQ 3 := by norm_num [epsilonQ,momentOrder]
  have hb : 24*epsilonQ 3*(4309096/3:ℚ) < capQ 3 := by norm_num [epsilonQ,momentOrder,capQ]
  intro N hN
  exact (mul_le_mul_of_nonneg_left (rows3_ratio_bound N hN) he).trans_lt hb
#print axioms rows3_ratio_bound
#print axioms rows3_bound
end Erdos708H17.Proofs
