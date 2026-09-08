import Erdos708.H97.Proofs.Numeric6_8Rows
open Finset BigOperators
namespace Erdos708H97.Proofs.Numeric6_8
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
def eps : List ℚ := [(162158604911421/100000000000000000:ℚ),(9998380302829/5000000000000000:ℚ),(68371277070813/25000000000000000:ℚ),(86750652627483/25000000000000000:ℚ),(21026005636831/5000000000000000:ℚ),(494037614963293/100000000000000000:ℚ)]
lemma eps_bound : ∀ d ∈ (Icc 1 6 : Finset ℕ), epsilon ((6:ℝ)/8) (1+(d:ℝ)/8) ≤ (eps[d-1]?.getD 0:ℚ) := by
  intro d hd
  obtain ⟨hd0,hd1⟩ := mem_Icc.mp hd
  interval_cases d
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(1:ℝ)/8))/((6:ℝ)/8)⌋₊ = 5 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(1:ℝ)/8))/((6:ℝ)/8)) 5 = 7 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((6:ℝ)/8) (1+(1:ℝ)/8) 5 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 7 5 = 21 by decide,show Nat.factorial 5 = 120 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(2:ℝ)/8))/((6:ℝ)/8)⌋₊ = 5 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(2:ℝ)/8))/((6:ℝ)/8)) 5 = 6 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((6:ℝ)/8) (1+(2:ℝ)/8) 5 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 6 5 = 6 by decide,show Nat.factorial 5 = 120 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(3:ℝ)/8))/((6:ℝ)/8)⌋₊ = 5 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(3:ℝ)/8))/((6:ℝ)/8)) 5 = 6 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((6:ℝ)/8) (1+(3:ℝ)/8) 5 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 6 5 = 6 by decide,show Nat.factorial 5 = 120 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(4:ℝ)/8))/((6:ℝ)/8)⌋₊ = 5 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(4:ℝ)/8))/((6:ℝ)/8)) 5 = 6 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((6:ℝ)/8) (1+(4:ℝ)/8) 5 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 6 5 = 6 by decide,show Nat.factorial 5 = 120 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(5:ℝ)/8))/((6:ℝ)/8)⌋₊ = 5 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(5:ℝ)/8))/((6:ℝ)/8)) 5 = 6 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((6:ℝ)/8) (1+(5:ℝ)/8) 5 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 6 5 = 6 by decide,show Nat.factorial 5 = 120 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(6:ℝ)/8))/((6:ℝ)/8)⌋₊ = 4 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(6:ℝ)/8))/((6:ℝ)/8)) 5 = 6 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((6:ℝ)/8) (1+(6:ℝ)/8) 5 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 6 5 = 6 by decide,show Nat.factorial 5 = 120 by decide]
    norm_num [T,Hstar,eps]
lemma value_bound : ∀ N ∈ range (5+1), rowValueQ 6 8 N (countsFromRows 6 8 N frows orows) eps ≤ (20353688079/500000000000:ℚ) := by
  intro N hN
  have hN' : N < 5+1 := mem_range.mp hN
  interval_cases N
  · change rowValueQ 6 8 0 [0,0,0,0,0,0] eps ≤ (20353688079/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 8 1 [0,0,0,0,0,0] eps ≤ (20353688079/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 8 2 [0,0,0,1,2,2] eps ≤ (20353688079/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 8 3 [0,0,0,3,6,6] eps ≤ (20353688079/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 8 4 [0,0,0,6,12,12] eps ≤ (20353688079/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 8 5 [0,0,0,10,20,20] eps ≤ (20353688079/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
lemma scale_bound : AScale 6 8 ≤ (20353688079/500000000000:ℝ) := by
  have hh := numeric_scale_bound 6 8 (20353688079/500000000000:ℚ) (fun N => countsFromRows 6 8 N frows orows) eps
    (countsFromRows_correct 6 8 5 frows orows fbase fstep obase ostep) eps_bound value_bound
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hh
  exact hh
#print axioms scale_bound
end Erdos708H97.Proofs.Numeric6_8
