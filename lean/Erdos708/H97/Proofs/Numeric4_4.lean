import Erdos708.H97.Proofs.Numeric4_4Rows
open Finset BigOperators
namespace Erdos708H97.Proofs.Numeric4_4
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
def eps : List ℚ := [(70273838304047/10000000000000000:ℚ),(911886711326323/100000000000000000:ℚ),(142220863234381/10000000000000000:ℚ),(61698756844327/2500000000000000:ℚ)]
lemma eps_bound : ∀ d ∈ (Icc 1 4 : Finset ℕ), epsilon ((4:ℝ)/4) (1+(d:ℝ)/4) ≤ (eps[d-1]?.getD 0:ℚ) := by
  intro d hd
  obtain ⟨hd0,hd1⟩ := mem_Icc.mp hd
  interval_cases d
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(1:ℝ)/4))/((4:ℝ)/4)⌋₊ = 4 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(1:ℝ)/4))/((4:ℝ)/4)) 4 = 5 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((4:ℝ)/4) (1+(1:ℝ)/4) 4 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 5 4 = 5 by decide,show Nat.factorial 4 = 24 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(2:ℝ)/4))/((4:ℝ)/4)⌋₊ = 3 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(2:ℝ)/4))/((4:ℝ)/4)) 4 = 5 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((4:ℝ)/4) (1+(2:ℝ)/4) 4 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 5 4 = 5 by decide,show Nat.factorial 4 = 24 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(3:ℝ)/4))/((4:ℝ)/4)⌋₊ = 3 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(3:ℝ)/4))/((4:ℝ)/4)) 4 = 4 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((4:ℝ)/4) (1+(3:ℝ)/4) 4 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 4 4 = 1 by decide,show Nat.factorial 4 = 24 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(4:ℝ)/4))/((4:ℝ)/4)⌋₊ = 3 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(4:ℝ)/4))/((4:ℝ)/4)) 4 = 4 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((4:ℝ)/4) (1+(4:ℝ)/4) 4 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 4 4 = 1 by decide,show Nat.factorial 4 = 24 by decide]
    norm_num [T,Hstar,eps]
lemma value_bound : ∀ N ∈ range (4+1), rowValueQ 4 4 N (countsFromRows 4 4 N frows orows) eps ≤ (12339751369/500000000000:ℚ) := by
  intro N hN
  have hN' : N < 4+1 := mem_range.mp hN
  interval_cases N
  · change rowValueQ 4 4 0 [0,0,0,0] eps ≤ (12339751369/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 4 1 [0,0,0,0] eps ≤ (12339751369/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 4 2 [0,0,0,1] eps ≤ (12339751369/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 4 3 [0,0,0,3] eps ≤ (12339751369/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 4 4 [0,0,0,6] eps ≤ (12339751369/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
lemma scale_bound : AScale 4 4 ≤ (12339751369/500000000000:ℝ) := by
  have hh := numeric_scale_bound 4 4 (12339751369/500000000000:ℚ) (fun N => countsFromRows 4 4 N frows orows) eps
    (countsFromRows_correct 4 4 4 frows orows fbase fstep obase ostep) eps_bound value_bound
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hh
  exact hh
#print axioms scale_bound
end Erdos708H97.Proofs.Numeric4_4
