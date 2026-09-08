import Erdos708.H97.Proofs.Numeric5_16Rows
open Finset BigOperators
namespace Erdos708H97.Proofs.Numeric5_16
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
def eps : List ℚ := [(18197729331947/10000000000000000000:ℚ),(240852299981651/100000000000000000000:ℚ),(3822306419221/1000000000000000000:ℚ),(53888254434919/10000000000000000000:ℚ),(17388361169407/2500000000000000000:ℚ)]
lemma eps_bound : ∀ d ∈ (Icc 1 5 : Finset ℕ), epsilon ((5:ℝ)/16) (1+(d:ℝ)/16) ≤ (eps[d-1]?.getD 0:ℚ) := by
  intro d hd
  obtain ⟨hd0,hd1⟩ := mem_Icc.mp hd
  interval_cases d
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(1:ℝ)/16))/((5:ℝ)/16)⌋₊ = 13 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(1:ℝ)/16))/((5:ℝ)/16)) 12 = 15 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((5:ℝ)/16) (1+(1:ℝ)/16) 12 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 15 12 = 455 by decide,show Nat.factorial 12 = 479001600 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(2:ℝ)/16))/((5:ℝ)/16)⌋₊ = 13 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(2:ℝ)/16))/((5:ℝ)/16)) 12 = 14 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((5:ℝ)/16) (1+(2:ℝ)/16) 12 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 14 12 = 91 by decide,show Nat.factorial 12 = 479001600 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(3:ℝ)/16))/((5:ℝ)/16)⌋₊ = 13 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(3:ℝ)/16))/((5:ℝ)/16)) 11 = 14 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((5:ℝ)/16) (1+(3:ℝ)/16) 11 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 14 11 = 364 by decide,show Nat.factorial 11 = 39916800 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(4:ℝ)/16))/((5:ℝ)/16)⌋₊ = 13 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(4:ℝ)/16))/((5:ℝ)/16)) 11 = 14 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((5:ℝ)/16) (1+(4:ℝ)/16) 11 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 14 11 = 364 by decide,show Nat.factorial 11 = 39916800 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(5:ℝ)/16))/((5:ℝ)/16)⌋₊ = 13 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(5:ℝ)/16))/((5:ℝ)/16)) 11 = 14 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((5:ℝ)/16) (1+(5:ℝ)/16) 11 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 14 11 = 364 by decide,show Nat.factorial 11 = 39916800 by decide]
    norm_num [T,Hstar,eps]
lemma value_bound : ∀ N ∈ range (12+1), rowValueQ 5 16 N (countsFromRows 5 16 N frows orows) eps ≤ (2295923353/500000000000:ℚ) := by
  intro N hN
  have hN' : N < 12+1 := mem_range.mp hN
  interval_cases N
  · change rowValueQ 5 16 0 [0,0,0,0,0] eps ≤ (2295923353/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 16 1 [0,0,0,0,0] eps ≤ (2295923353/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 16 2 [2,0,2,0,2] eps ≤ (2295923353/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 16 3 [12,9,15,9,15] eps ≤ (2295923353/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 16 4 [36,36,48,37,52] eps ≤ (2295923353/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 16 5 [80,90,110,95,130] eps ≤ (2295923353/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 16 6 [150,180,210,195,270] eps ≤ (2295923353/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 16 7 [252,315,357,350,497] eps ≤ (2295923353/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 16 8 [392,504,560,574,840] eps ≤ (2295923353/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 16 9 [576,756,828,882,1332] eps ≤ (2295923353/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 16 10 [810,1080,1170,1290,2010] eps ≤ (2295923353/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 16 11 [1100,1485,1595,1815,2915] eps ≤ (2295923353/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 16 12 [1452,1980,2112,2475,4092] eps ≤ (2295923353/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
lemma scale_bound : AScale 5 16 ≤ (2295923353/500000000000:ℝ) := by
  have hh := numeric_scale_bound 5 16 (2295923353/500000000000:ℚ) (fun N => countsFromRows 5 16 N frows orows) eps
    (countsFromRows_correct 5 16 12 frows orows fbase fstep obase ostep) eps_bound value_bound
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hh
  exact hh
#print axioms scale_bound
end Erdos708H97.Proofs.Numeric5_16
