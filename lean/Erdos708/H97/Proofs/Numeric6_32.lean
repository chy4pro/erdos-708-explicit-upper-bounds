import Erdos708.H97.Proofs.Numeric6_32Rows
open Finset BigOperators
namespace Erdos708H97.Proofs.Numeric6_32
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
def eps : List ℚ := [(155305708876221/100000000000000000000000:ℚ),(48833238357987/25000000000000000000000:ℚ),(9414407919507/4000000000000000000000:ℚ),(27538744254341/10000000000000000000000:ℚ),(177247668067413/50000000000000000000000:ℚ),(12956174721679/2500000000000000000000:ℚ)]
lemma eps_bound : ∀ d ∈ (Icc 1 6 : Finset ℕ), epsilon ((6:ℝ)/32) (1+(d:ℝ)/32) ≤ (eps[d-1]?.getD 0:ℚ) := by
  intro d hd
  obtain ⟨hd0,hd1⟩ := mem_Icc.mp hd
  interval_cases d
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(1:ℝ)/32))/((6:ℝ)/32)⌋₊ = 23 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(1:ℝ)/32))/((6:ℝ)/32)) 19 = 24 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((6:ℝ)/32) (1+(1:ℝ)/32) 19 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 24 19 = 42504 by decide,show Nat.factorial 19 = 121645100408832000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(2:ℝ)/32))/((6:ℝ)/32)⌋₊ = 23 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(2:ℝ)/32))/((6:ℝ)/32)) 19 = 24 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((6:ℝ)/32) (1+(2:ℝ)/32) 19 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 24 19 = 42504 by decide,show Nat.factorial 19 = 121645100408832000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(3:ℝ)/32))/((6:ℝ)/32)⌋₊ = 23 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(3:ℝ)/32))/((6:ℝ)/32)) 19 = 24 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((6:ℝ)/32) (1+(3:ℝ)/32) 19 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 24 19 = 42504 by decide,show Nat.factorial 19 = 121645100408832000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(4:ℝ)/32))/((6:ℝ)/32)⌋₊ = 22 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(4:ℝ)/32))/((6:ℝ)/32)) 19 = 24 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((6:ℝ)/32) (1+(4:ℝ)/32) 19 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 24 19 = 42504 by decide,show Nat.factorial 19 = 121645100408832000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(5:ℝ)/32))/((6:ℝ)/32)⌋₊ = 22 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(5:ℝ)/32))/((6:ℝ)/32)) 18 = 24 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((6:ℝ)/32) (1+(5:ℝ)/32) 18 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 24 18 = 134596 by decide,show Nat.factorial 18 = 6402373705728000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(6:ℝ)/32))/((6:ℝ)/32)⌋₊ = 22 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(6:ℝ)/32))/((6:ℝ)/32)) 18 = 23 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((6:ℝ)/32) (1+(6:ℝ)/32) 18 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 23 18 = 33649 by decide,show Nat.factorial 18 = 6402373705728000 by decide]
    norm_num [T,Hstar,eps]
lemma value_bound : ∀ N ∈ range (20+1), rowValueQ 6 32 N (countsFromRows 6 32 N frows orows) eps ≤ (436926779/250000000000:ℚ) := by
  intro N hN
  have hN' : N < 20+1 := mem_range.mp hN
  interval_cases N
  · change rowValueQ 6 32 0 [0,0,0,0,0,0] eps ≤ (436926779/250000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 32 1 [0,0,0,0,0,0] eps ≤ (436926779/250000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 32 2 [0,2,0,0,0,2] eps ≤ (436926779/250000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 32 3 [6,21,0,15,6,21] eps ≤ (436926779/250000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 32 4 [72,136,60,142,84,160] eps ≤ (436926779/250000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 32 5 [330,540,370,655,480,770] eps ≤ (436926779/250000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 32 6 [1020,1590,1320,2101,1746,2631] eps ≤ (436926779/250000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 32 7 [2520,3857,3570,5397,4872,7154] eps ≤ (436926779/250000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 32 8 [5376,8176,8120,11928,11424,16604] eps ≤ (436926779/250000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 32 9 [10332,15696,16380,23646,23688,34344] eps ≤ (436926779/250000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 32 10 [18360,27930,30240,43170,44820,65100] eps ≤ (436926779/250000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 32 11 [30690,46805,52140,73887,79002,115247] eps ≤ (436926779/250000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 32 12 [48840,74712,85140,120054,131604,193116] eps ≤ (436926779/250000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 32 13 [74646,114556,132990,186901,209352,309322] eps ≤ (436926779/250000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 32 14 [110292,169806,200200,280735,320502,477113] eps ≤ (436926779/250000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 32 15 [158340,244545,292110,409045,475020,712740] eps ≤ (436926779/250000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 32 16 [221760,343520,414960,580608,684768,1035848] eps ≤ (436926779/250000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 32 17 [303960,472192,575960,805596,963696,1469888] eps ≤ (436926779/250000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 32 18 [408816,636786,783360,1095684,1328040,2042550] eps ≤ (436926779/250000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 32 19 [540702,844341,1046520,1464159,1796526,2786217] eps ≤ (436926779/250000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 32 20 [704520,1102760,1375980,1926030,2390580,3738440] eps ≤ (436926779/250000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
lemma scale_bound : AScale 6 32 ≤ (436926779/250000000000:ℝ) := by
  have hh := numeric_scale_bound 6 32 (436926779/250000000000:ℚ) (fun N => countsFromRows 6 32 N frows orows) eps
    (countsFromRows_correct 6 32 20 frows orows fbase fstep obase ostep) eps_bound value_bound
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hh
  exact hh
#print axioms scale_bound
end Erdos708H97.Proofs.Numeric6_32
