import Erdos708.H97.Proofs.Numeric6_16Rows
open Finset BigOperators
namespace Erdos708H97.Proofs.Numeric6_16
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
def eps : List ℚ := [(29230032226867/2500000000000000000:ℚ),(82419107262641/5000000000000000000:ℚ),(26594537517887/1250000000000000000:ℚ),(260674385760911/10000000000000000000:ℚ),(12343698855149/400000000000000000:ℚ),(80136616909271/2000000000000000000:ℚ)]
lemma eps_bound : ∀ d ∈ (Icc 1 6 : Finset ℕ), epsilon ((6:ℝ)/16) (1+(d:ℝ)/16) ≤ (eps[d-1]?.getD 0:ℚ) := by
  intro d hd
  obtain ⟨hd0,hd1⟩ := mem_Icc.mp hd
  interval_cases d
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(1:ℝ)/16))/((6:ℝ)/16)⌋₊ = 11 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(1:ℝ)/16))/((6:ℝ)/16)) 10 = 12 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((6:ℝ)/16) (1+(1:ℝ)/16) 10 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 12 10 = 66 by decide,show Nat.factorial 10 = 3628800 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(2:ℝ)/16))/((6:ℝ)/16)⌋₊ = 11 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(2:ℝ)/16))/((6:ℝ)/16)) 10 = 12 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((6:ℝ)/16) (1+(2:ℝ)/16) 10 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 12 10 = 66 by decide,show Nat.factorial 10 = 3628800 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(3:ℝ)/16))/((6:ℝ)/16)⌋₊ = 11 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(3:ℝ)/16))/((6:ℝ)/16)) 10 = 12 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((6:ℝ)/16) (1+(3:ℝ)/16) 10 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 12 10 = 66 by decide,show Nat.factorial 10 = 3628800 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(4:ℝ)/16))/((6:ℝ)/16)⌋₊ = 11 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(4:ℝ)/16))/((6:ℝ)/16)) 10 = 12 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((6:ℝ)/16) (1+(4:ℝ)/16) 10 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 12 10 = 66 by decide,show Nat.factorial 10 = 3628800 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(5:ℝ)/16))/((6:ℝ)/16)⌋₊ = 10 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(5:ℝ)/16))/((6:ℝ)/16)) 10 = 12 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((6:ℝ)/16) (1+(5:ℝ)/16) 10 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 12 10 = 66 by decide,show Nat.factorial 10 = 3628800 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(6:ℝ)/16))/((6:ℝ)/16)⌋₊ = 10 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(6:ℝ)/16))/((6:ℝ)/16)) 9 = 12 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((6:ℝ)/16) (1+(6:ℝ)/16) 9 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 12 9 = 220 by decide,show Nat.factorial 9 = 362880 by decide]
    norm_num [T,Hstar,eps]
lemma value_bound : ∀ N ∈ range (10+1), rowValueQ 6 16 N (countsFromRows 6 16 N frows orows) eps ≤ (1032450531/125000000000:ℚ) := by
  intro N hN
  have hN' : N < 10+1 := mem_range.mp hN
  interval_cases N
  · change rowValueQ 6 16 0 [0,0,0,0,0,0] eps ≤ (1032450531/125000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 16 1 [0,0,0,0,0,0] eps ≤ (1032450531/125000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 16 2 [0,2,0,2,0,2] eps ≤ (1032450531/125000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 16 3 [0,7,3,12,6,12] eps ≤ (1032450531/125000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 16 4 [0,16,12,36,24,36] eps ≤ (1032450531/125000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 16 5 [0,30,30,80,60,80] eps ≤ (1032450531/125000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 16 6 [0,50,60,150,120,150] eps ≤ (1032450531/125000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 16 7 [0,77,105,252,210,252] eps ≤ (1032450531/125000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 16 8 [0,112,168,392,336,392] eps ≤ (1032450531/125000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 16 9 [0,156,252,576,504,576] eps ≤ (1032450531/125000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 16 10 [0,210,360,810,720,810] eps ≤ (1032450531/125000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
lemma scale_bound : AScale 6 16 ≤ (1032450531/125000000000:ℝ) := by
  have hh := numeric_scale_bound 6 16 (1032450531/125000000000:ℚ) (fun N => countsFromRows 6 16 N frows orows) eps
    (countsFromRows_correct 6 16 10 frows orows fbase fstep obase ostep) eps_bound value_bound
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hh
  exact hh
#print axioms scale_bound
end Erdos708H97.Proofs.Numeric6_16
