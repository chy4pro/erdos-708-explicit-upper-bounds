import Erdos708.H97.Proofs.Numeric4_16Rows
open Finset BigOperators
namespace Erdos708H97.Proofs.Numeric4_16
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
def eps : List ℚ := [(155565993272951/1000000000000000000000:ℚ),(10966127394651/50000000000000000000:ℚ),(7076977562827/25000000000000000000:ℚ),(206571236969/500000000000000000:ℚ)]
lemma eps_bound : ∀ d ∈ (Icc 1 4 : Finset ℕ), epsilon ((4:ℝ)/16) (1+(d:ℝ)/16) ≤ (eps[d-1]?.getD 0:ℚ) := by
  intro d hd
  obtain ⟨hd0,hd1⟩ := mem_Icc.mp hd
  interval_cases d
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(1:ℝ)/16))/((4:ℝ)/16)⌋₊ = 17 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(1:ℝ)/16))/((4:ℝ)/16)) 14 = 18 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((4:ℝ)/16) (1+(1:ℝ)/16) 14 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 18 14 = 3060 by decide,show Nat.factorial 14 = 87178291200 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(2:ℝ)/16))/((4:ℝ)/16)⌋₊ = 17 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(2:ℝ)/16))/((4:ℝ)/16)) 14 = 18 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((4:ℝ)/16) (1+(2:ℝ)/16) 14 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 18 14 = 3060 by decide,show Nat.factorial 14 = 87178291200 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(3:ℝ)/16))/((4:ℝ)/16)⌋₊ = 16 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(3:ℝ)/16))/((4:ℝ)/16)) 14 = 18 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((4:ℝ)/16) (1+(3:ℝ)/16) 14 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 18 14 = 3060 by decide,show Nat.factorial 14 = 87178291200 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(4:ℝ)/16))/((4:ℝ)/16)⌋₊ = 16 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(4:ℝ)/16))/((4:ℝ)/16)) 14 = 17 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((4:ℝ)/16) (1+(4:ℝ)/16) 14 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 17 14 = 680 by decide,show Nat.factorial 14 = 87178291200 by decide]
    norm_num [T,Hstar,eps]
lemma value_bound : ∀ N ∈ range (15+1), rowValueQ 4 16 N (countsFromRows 4 16 N frows orows) eps ≤ (148044587/62500000000:ℚ) := by
  intro N hN
  have hN' : N < 15+1 := mem_range.mp hN
  interval_cases N
  · change rowValueQ 4 16 0 [0,0,0,0] eps ≤ (148044587/62500000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 16 1 [0,0,0,0] eps ≤ (148044587/62500000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 16 2 [0,2,0,2] eps ≤ (148044587/62500000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 16 3 [12,18,12,18] eps ≤ (148044587/62500000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 16 4 [52,70,68,94] eps ≤ (148044587/62500000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 16 5 [140,190,220,311] eps ≤ (148044587/62500000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 16 6 [300,420,540,786] eps ≤ (148044587/62500000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 16 7 [560,812,1120,1673] eps ≤ (148044587/62500000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 16 8 [952,1428,2072,3164] eps ≤ (148044587/62500000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 16 9 [1512,2340,3528,5490] eps ≤ (148044587/62500000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 16 10 [2280,3630,5640,8922] eps ≤ (148044587/62500000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 16 11 [3300,5390,8580,13772] eps ≤ (148044587/62500000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 16 12 [4620,7722,12540,20394] eps ≤ (148044587/62500000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 16 13 [6292,10738,17732,29185] eps ≤ (148044587/62500000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 16 14 [8372,14560,24388,40586] eps ≤ (148044587/62500000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 16 15 [10920,19320,32760,55083] eps ≤ (148044587/62500000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
lemma scale_bound : AScale 4 16 ≤ (148044587/62500000000:ℝ) := by
  have hh := numeric_scale_bound 4 16 (148044587/62500000000:ℚ) (fun N => countsFromRows 4 16 N frows orows) eps
    (countsFromRows_correct 4 16 15 frows orows fbase fstep obase ostep) eps_bound value_bound
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hh
  exact hh
#print axioms scale_bound
end Erdos708H97.Proofs.Numeric4_16
