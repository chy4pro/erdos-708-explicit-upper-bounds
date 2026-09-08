import Erdos708.H97.Proofs.Numeric4_8Rows
open Finset BigOperators
namespace Erdos708H97.Proofs.Numeric4_8
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
def eps : List ℚ := [(30543074344563/200000000000000000:ℚ),(24150337853841/100000000000000000:ℚ),(165145692677/500000000000000:ℚ),(419079392169583/1000000000000000000:ℚ)]
lemma eps_bound : ∀ d ∈ (Icc 1 4 : Finset ℕ), epsilon ((4:ℝ)/8) (1+(d:ℝ)/8) ≤ (eps[d-1]?.getD 0:ℚ) := by
  intro d hd
  obtain ⟨hd0,hd1⟩ := mem_Icc.mp hd
  interval_cases d
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(1:ℝ)/8))/((4:ℝ)/8)⌋₊ = 8 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(1:ℝ)/8))/((4:ℝ)/8)) 7 = 9 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((4:ℝ)/8) (1+(1:ℝ)/8) 7 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 9 7 = 36 by decide,show Nat.factorial 7 = 5040 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(2:ℝ)/8))/((4:ℝ)/8)⌋₊ = 8 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(2:ℝ)/8))/((4:ℝ)/8)) 7 = 9 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((4:ℝ)/8) (1+(2:ℝ)/8) 7 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 9 7 = 36 by decide,show Nat.factorial 7 = 5040 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(3:ℝ)/8))/((4:ℝ)/8)⌋₊ = 8 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(3:ℝ)/8))/((4:ℝ)/8)) 7 = 9 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((4:ℝ)/8) (1+(3:ℝ)/8) 7 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 9 7 = 36 by decide,show Nat.factorial 7 = 5040 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(4:ℝ)/8))/((4:ℝ)/8)⌋₊ = 7 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(4:ℝ)/8))/((4:ℝ)/8)) 7 = 9 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((4:ℝ)/8) (1+(4:ℝ)/8) 7 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 9 7 = 36 by decide,show Nat.factorial 7 = 5040 by decide]
    norm_num [T,Hstar,eps]
lemma value_bound : ∀ N ∈ range (8+1), rowValueQ 4 8 N (countsFromRows 4 8 N frows orows) eps ≤ (13846045723/1000000000000:ℚ) := by
  intro N hN
  have hN' : N < 8+1 := mem_range.mp hN
  interval_cases N
  · change rowValueQ 4 8 0 [0,0,0,0] eps ≤ (13846045723/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 8 1 [0,0,0,0] eps ≤ (13846045723/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 8 2 [2,2,2,2] eps ≤ (13846045723/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 8 3 [6,6,6,7] eps ≤ (13846045723/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 8 4 [12,12,12,16] eps ≤ (13846045723/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 8 5 [20,20,20,30] eps ≤ (13846045723/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 8 6 [30,30,30,50] eps ≤ (13846045723/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 8 7 [42,42,42,77] eps ≤ (13846045723/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 8 8 [56,56,56,112] eps ≤ (13846045723/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
lemma scale_bound : AScale 4 8 ≤ (13846045723/1000000000000:ℝ) := by
  have hh := numeric_scale_bound 4 8 (13846045723/1000000000000:ℚ) (fun N => countsFromRows 4 8 N frows orows) eps
    (countsFromRows_correct 4 8 8 frows orows fbase fstep obase ostep) eps_bound value_bound
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hh
  exact hh
#print axioms scale_bound
end Erdos708H97.Proofs.Numeric4_8
