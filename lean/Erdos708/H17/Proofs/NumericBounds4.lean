import Erdos708.H17.Proofs.NumericRows4
open Finset BigOperators
namespace Erdos708H17.Proofs
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024

lemma rows4_ratio_bound : ∀ N ∈ range (countLimit 4+1),
    ratioQ 4 N ((rows4[N]?.getD [])[17]?.getD 0) ≤ (418064119044656/11:ℚ) := by
  intro N hN
  norm_num [countLimit,mem_range] at hN
  interval_cases N
  · change ratioQ 4 0 0 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 1 0 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 2 2 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 3 9 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 4 36 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 5 175 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 6 870 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 7 3829 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 8 14840 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 9 51939 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 10 167650 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 11 505967 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 12 1440252 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 13 3889769 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 14 10011834 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 15 24649695 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 16 58241552 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 17 132454719 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 18 290739492 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 19 617505776 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 20 1272011240 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 21 2546739216 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 22 4965634828 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 23 9445881500 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 24 17559053760 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 25 31944972000 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 26 56956389880 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 27 99647354952 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 28 171266050704 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 29 289478453096 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 30 481637681100 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 31 789532375920 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 32 1276204420864 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 33 2035632507810 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 34 3206346655534 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 35 4990385951075 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 36 7679457203292 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 37 11690719711237 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 38 17615339685194 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 39 26283861450639 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 40 38853572498120 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 41 56924444508657 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 42 82691970387894 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 43 119147356045277 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 44 170338144892916 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 45 241705546016715 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 46 340518612254006 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 47 476430098027933 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 48 662184464576400 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 49 914515260410185 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 50 1255277180948000 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 51 1712867725249410 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]
  · change ratioQ 4 52 2324004773468352 ≤ (418064119044656/11:ℚ)
    norm_num [ratioQ]

theorem rows4_bound : ∀ N ∈ range (countLimit 4+1),
    24*epsilonQ 4*ratioQ 4 N ((rows4[N]?.getD [])[17]?.getD 0) < capQ 4 := by
  have he : 0 ≤ 24*epsilonQ 4 := by norm_num [epsilonQ,momentOrder]
  have hb : 24*epsilonQ 4*(418064119044656/11:ℚ) < capQ 4 := by norm_num [epsilonQ,momentOrder,capQ]
  intro N hN
  exact (mul_le_mul_of_nonneg_left (rows4_ratio_bound N hN) he).trans_lt hb
#print axioms rows4_ratio_bound
#print axioms rows4_bound
end Erdos708H17.Proofs
