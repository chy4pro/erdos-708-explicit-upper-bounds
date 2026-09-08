import Erdos708.H97.Proofs.Numeric7_16Rows
open Finset BigOperators
namespace Erdos708H97.Proofs.Numeric7_16
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
def eps : List ℚ := [(200128941058501/5000000000000000000:ℚ),(45405598455209/1000000000000000000:ℚ),(66590818820561/1000000000000000000:ℚ),(889758680851/10000000000000000:ℚ),(22968189203363/200000000000000000:ℚ),(14070602394853/100000000000000000:ℚ),(33314220376049/200000000000000000:ℚ)]
lemma eps_bound : ∀ d ∈ (Icc 1 7 : Finset ℕ), epsilon ((7:ℝ)/16) (1+(d:ℝ)/16) ≤ (eps[d-1]?.getD 0:ℚ) := by
  intro d hd
  obtain ⟨hd0,hd1⟩ := mem_Icc.mp hd
  interval_cases d
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(1:ℝ)/16))/((7:ℝ)/16)⌋₊ = 9 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(1:ℝ)/16))/((7:ℝ)/16)) 9 = 11 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((7:ℝ)/16) (1+(1:ℝ)/16) 9 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 11 9 = 55 by decide,show Nat.factorial 9 = 362880 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(2:ℝ)/16))/((7:ℝ)/16)⌋₊ = 9 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(2:ℝ)/16))/((7:ℝ)/16)) 9 = 11 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((7:ℝ)/16) (1+(2:ℝ)/16) 9 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 11 9 = 55 by decide,show Nat.factorial 9 = 362880 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(3:ℝ)/16))/((7:ℝ)/16)⌋₊ = 9 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(3:ℝ)/16))/((7:ℝ)/16)) 8 = 11 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((7:ℝ)/16) (1+(3:ℝ)/16) 8 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 11 8 = 165 by decide,show Nat.factorial 8 = 40320 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(4:ℝ)/16))/((7:ℝ)/16)⌋₊ = 9 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(4:ℝ)/16))/((7:ℝ)/16)) 8 = 10 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((7:ℝ)/16) (1+(4:ℝ)/16) 8 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 10 8 = 45 by decide,show Nat.factorial 8 = 40320 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(5:ℝ)/16))/((7:ℝ)/16)⌋₊ = 9 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(5:ℝ)/16))/((7:ℝ)/16)) 8 = 10 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((7:ℝ)/16) (1+(5:ℝ)/16) 8 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 10 8 = 45 by decide,show Nat.factorial 8 = 40320 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(6:ℝ)/16))/((7:ℝ)/16)⌋₊ = 9 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(6:ℝ)/16))/((7:ℝ)/16)) 8 = 10 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((7:ℝ)/16) (1+(6:ℝ)/16) 8 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 10 8 = 45 by decide,show Nat.factorial 8 = 40320 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(7:ℝ)/16))/((7:ℝ)/16)⌋₊ = 9 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(7:ℝ)/16))/((7:ℝ)/16)) 8 = 10 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((7:ℝ)/16) (1+(7:ℝ)/16) 8 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 10 8 = 45 by decide,show Nat.factorial 8 = 40320 by decide]
    norm_num [T,Hstar,eps]
lemma value_bound : ∀ N ∈ range (9+1), rowValueQ 7 16 N (countsFromRows 7 16 N frows orows) eps ≤ (10552534671/1000000000000:ℚ) := by
  intro N hN
  have hN' : N < 9+1 := mem_range.mp hN
  interval_cases N
  · change rowValueQ 7 16 0 [0,0,0,0,0,0,0] eps ≤ (10552534671/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 16 1 [0,0,0,0,0,0,0] eps ≤ (10552534671/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 16 2 [2,0,2,0,2,0,2] eps ≤ (10552534671/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 16 3 [6,0,6,0,7,3,9] eps ≤ (10552534671/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 16 4 [12,0,12,0,16,12,24] eps ≤ (10552534671/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 16 5 [20,0,20,0,30,30,50] eps ≤ (10552534671/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 16 6 [30,0,30,0,50,60,90] eps ≤ (10552534671/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 16 7 [42,0,42,0,77,105,147] eps ≤ (10552534671/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 16 8 [56,0,56,0,112,168,224] eps ≤ (10552534671/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 16 9 [72,0,72,0,156,252,324] eps ≤ (10552534671/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
lemma scale_bound : AScale 7 16 ≤ (10552534671/1000000000000:ℝ) := by
  have hh := numeric_scale_bound 7 16 (10552534671/1000000000000:ℚ) (fun N => countsFromRows 7 16 N frows orows) eps
    (countsFromRows_correct 7 16 9 frows orows fbase fstep obase ostep) eps_bound value_bound
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hh
  exact hh
#print axioms scale_bound
end Erdos708H97.Proofs.Numeric7_16
