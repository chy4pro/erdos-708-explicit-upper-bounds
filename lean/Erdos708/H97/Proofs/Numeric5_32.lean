import Erdos708.H97.Proofs.Numeric5_32Rows
open Finset BigOperators
namespace Erdos708H97.Proofs.Numeric5_32
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
def eps : List ℚ := [(11063507421143/250000000000000000000000:ℚ),(26661239195213/500000000000000000000000:ℚ),(19294119939247/250000000000000000000000:ℚ),(59113899388331/500000000000000000000000:ℚ),(159279117796337/1000000000000000000000000:ℚ)]
lemma eps_bound : ∀ d ∈ (Icc 1 5 : Finset ℕ), epsilon ((5:ℝ)/32) (1+(d:ℝ)/32) ≤ (eps[d-1]?.getD 0:ℚ) := by
  intro d hd
  obtain ⟨hd0,hd1⟩ := mem_Icc.mp hd
  interval_cases d
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(1:ℝ)/32))/((5:ℝ)/32)⌋₊ = 28 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(1:ℝ)/32))/((5:ℝ)/32)) 23 = 29 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((5:ℝ)/32) (1+(1:ℝ)/32) 23 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 29 23 = 475020 by decide,show Nat.factorial 23 = 25852016738884976640000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(2:ℝ)/32))/((5:ℝ)/32)⌋₊ = 27 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(2:ℝ)/32))/((5:ℝ)/32)) 23 = 29 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((5:ℝ)/32) (1+(2:ℝ)/32) 23 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 29 23 = 475020 by decide,show Nat.factorial 23 = 25852016738884976640000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(3:ℝ)/32))/((5:ℝ)/32)⌋₊ = 27 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(3:ℝ)/32))/((5:ℝ)/32)) 22 = 28 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((5:ℝ)/32) (1+(3:ℝ)/32) 22 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 28 22 = 376740 by decide,show Nat.factorial 22 = 1124000727777607680000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(4:ℝ)/32))/((5:ℝ)/32)⌋₊ = 27 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(4:ℝ)/32))/((5:ℝ)/32)) 22 = 28 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((5:ℝ)/32) (1+(4:ℝ)/32) 22 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 28 22 = 376740 by decide,show Nat.factorial 22 = 1124000727777607680000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(5:ℝ)/32))/((5:ℝ)/32)⌋₊ = 27 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(5:ℝ)/32))/((5:ℝ)/32)) 22 = 28 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((5:ℝ)/32) (1+(5:ℝ)/32) 22 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 28 22 = 376740 by decide,show Nat.factorial 22 = 1124000727777607680000 by decide]
    norm_num [T,Hstar,eps]
lemma value_bound : ∀ N ∈ range (24+1), rowValueQ 5 32 N (countsFromRows 5 32 N frows orows) eps ≤ (227927301/200000000000:ℚ) := by
  intro N hN
  have hN' : N < 24+1 := mem_range.mp hN
  interval_cases N
  · change rowValueQ 5 32 0 [0,0,0,0,0] eps ≤ (227927301/200000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 32 1 [0,0,0,0,0] eps ≤ (227927301/200000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 32 2 [2,0,0,0,2] eps ≤ (227927301/200000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 32 3 [21,3,18,6,21] eps ≤ (227927301/200000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 32 4 [180,114,188,120,204] eps ≤ (227927301/200000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 32 5 [955,835,1120,965,1335] eps ≤ (227927301/200000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 32 6 [3476,3480,4482,4475,5886] eps ≤ (227927301/200000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 32 7 [9884,10710,13805,15057,19642] eps ≤ (227927301/200000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 32 8 [23744,27188,35512,41132,53928] eps ≤ (227927301/200000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 32 9 [50514,60354,80172,97062,128466] eps ≤ (227927301/200000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 32 10 [98070,121320,163980,205470,274890] eps ≤ (227927301/200000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 32 11 [177287,225885,310464,399960,540947] eps ≤ (227927301/200000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 32 12 [302676,395670,552420,728244,995412] eps ≤ (227927301/200000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 32 13 [493077,659373,934076,1255683,1733745] eps ≤ (227927301/200000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 32 14 [772408,1054144,1513486,2069249,2884518] eps ≤ (227927301/200000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 32 15 [1170470,1627080,2365155,3281915,4616640] eps ≤ (227927301/200000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 32 16 [1723808,2436840,3582896,5037480,7147408] eps ≤ (227927301/200000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 32 17 [2476628,3555380,5282920,7515836,10751412] eps ≤ (227927301/200000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 32 18 [3481770,5069808,7607160,10938684,15770322] eps ≤ (227927301/200000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 32 19 [4801737,7084359,10726830,15575706,22623585] eps ≤ (227927301/200000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 32 20 [6509780,9722490,14846220,21751200,31820060] eps ≤ (227927301/200000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 32 21 [8691039,13129095,20206728,29851185,43970619] eps ≤ (227927301/200000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 32 22 [11443740,17472840,27091130,40330983,59801742] eps ≤ (227927301/200000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 32 23 [14880448,22948618,35828089,53723285,80170134] eps ≤ (227927301/200000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 32 24 [19129376,29780124,46796904,70646708,106078392] eps ≤ (227927301/200000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
lemma scale_bound : AScale 5 32 ≤ (227927301/200000000000:ℝ) := by
  have hh := numeric_scale_bound 5 32 (227927301/200000000000:ℚ) (fun N => countsFromRows 5 32 N frows orows) eps
    (countsFromRows_correct 5 32 24 frows orows fbase fstep obase ostep) eps_bound value_bound
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hh
  exact hh
#print axioms scale_bound
end Erdos708H97.Proofs.Numeric5_32
