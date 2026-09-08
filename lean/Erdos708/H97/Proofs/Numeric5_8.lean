import Erdos708.H97.Proofs.Numeric5_8Rows
open Finset BigOperators
namespace Erdos708H97.Proofs.Numeric5_8
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
def eps : List ℚ := [(4826354442117/10000000000000000:ℚ),(17997462635103/25000000000000000:ℚ),(1138444148081/1000000000000000:ℚ),(77849489537887/50000000000000000:ℚ),(39510708668691/20000000000000000:ℚ)]
lemma eps_bound : ∀ d ∈ (Icc 1 5 : Finset ℕ), epsilon ((5:ℝ)/8) (1+(d:ℝ)/8) ≤ (eps[d-1]?.getD 0:ℚ) := by
  intro d hd
  obtain ⟨hd0,hd1⟩ := mem_Icc.mp hd
  interval_cases d
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(1:ℝ)/8))/((5:ℝ)/8)⌋₊ = 6 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(1:ℝ)/8))/((5:ℝ)/8)) 7 = 7 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((5:ℝ)/8) (1+(1:ℝ)/8) 7 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 7 7 = 1 by decide,show Nat.factorial 7 = 5040 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(2:ℝ)/8))/((5:ℝ)/8)⌋₊ = 6 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(2:ℝ)/8))/((5:ℝ)/8)) 6 = 7 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((5:ℝ)/8) (1+(2:ℝ)/8) 6 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 7 6 = 7 by decide,show Nat.factorial 6 = 720 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(3:ℝ)/8))/((5:ℝ)/8)⌋₊ = 6 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(3:ℝ)/8))/((5:ℝ)/8)) 6 = 7 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((5:ℝ)/8) (1+(3:ℝ)/8) 6 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 7 6 = 7 by decide,show Nat.factorial 6 = 720 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(4:ℝ)/8))/((5:ℝ)/8)⌋₊ = 6 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(4:ℝ)/8))/((5:ℝ)/8)) 6 = 7 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((5:ℝ)/8) (1+(4:ℝ)/8) 6 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 7 6 = 7 by decide,show Nat.factorial 6 = 720 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(5:ℝ)/8))/((5:ℝ)/8)⌋₊ = 6 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(5:ℝ)/8))/((5:ℝ)/8)) 6 = 7 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((5:ℝ)/8) (1+(5:ℝ)/8) 6 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 7 6 = 7 by decide,show Nat.factorial 6 = 720 by decide]
    norm_num [T,Hstar,eps]
lemma value_bound : ∀ N ∈ range (6+1), rowValueQ 5 8 N (countsFromRows 5 8 N frows orows) eps ≤ (29684153863/1000000000000:ℚ) := by
  intro N hN
  have hN' : N < 6+1 := mem_range.mp hN
  interval_cases N
  · change rowValueQ 5 8 0 [0,0,0,0,0] eps ≤ (29684153863/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 8 1 [0,0,0,0,0] eps ≤ (29684153863/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 8 2 [0,1,2,2,2] eps ≤ (29684153863/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 8 3 [0,3,6,6,6] eps ≤ (29684153863/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 8 4 [0,6,12,12,12] eps ≤ (29684153863/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 8 5 [0,10,20,20,20] eps ≤ (29684153863/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 8 6 [0,15,30,30,30] eps ≤ (29684153863/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
lemma scale_bound : AScale 5 8 ≤ (29684153863/1000000000000:ℝ) := by
  have hh := numeric_scale_bound 5 8 (29684153863/1000000000000:ℚ) (fun N => countsFromRows 5 8 N frows orows) eps
    (countsFromRows_correct 5 8 6 frows orows fbase fstep obase ostep) eps_bound value_bound
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hh
  exact hh
#print axioms scale_bound
end Erdos708H97.Proofs.Numeric5_8
