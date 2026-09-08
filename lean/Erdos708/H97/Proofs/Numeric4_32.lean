import Erdos708.H97.Proofs.Numeric4_32Rows
open Finset BigOperators
namespace Erdos708H97.Proofs.Numeric4_32
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
def eps : List ℚ := [(32656242729091/125000000000000000000000000:ℚ),(164291200533983/500000000000000000000000000:ℚ),(56907686600317/100000000000000000000000000:ℚ),(871777326643147/1000000000000000000000000000:ℚ)]
lemma eps_bound : ∀ d ∈ (Icc 1 4 : Finset ℕ), epsilon ((4:ℝ)/32) (1+(d:ℝ)/32) ≤ (eps[d-1]?.getD 0:ℚ) := by
  intro d hd
  obtain ⟨hd0,hd1⟩ := mem_Icc.mp hd
  interval_cases d
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(1:ℝ)/32))/((4:ℝ)/32)⌋₊ = 35 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(1:ℝ)/32))/((4:ℝ)/32)) 28 = 36 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((4:ℝ)/32) (1+(1:ℝ)/32) 28 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 36 28 = 30260340 by decide,show Nat.factorial 28 = 304888344611713860501504000000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(2:ℝ)/32))/((4:ℝ)/32)⌋₊ = 34 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(2:ℝ)/32))/((4:ℝ)/32)) 28 = 36 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((4:ℝ)/32) (1+(2:ℝ)/32) 28 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 36 28 = 30260340 by decide,show Nat.factorial 28 = 304888344611713860501504000000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(3:ℝ)/32))/((4:ℝ)/32)⌋₊ = 34 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(3:ℝ)/32))/((4:ℝ)/32)) 27 = 35 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((4:ℝ)/32) (1+(3:ℝ)/32) 27 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 35 27 = 23535820 by decide,show Nat.factorial 27 = 10888869450418352160768000000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(4:ℝ)/32))/((4:ℝ)/32)⌋₊ = 34 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(4:ℝ)/32))/((4:ℝ)/32)) 27 = 35 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((4:ℝ)/32) (1+(4:ℝ)/32) 27 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 35 27 = 23535820 by decide,show Nat.factorial 27 = 10888869450418352160768000000 by decide]
    norm_num [T,Hstar,eps]
lemma value_bound : ∀ N ∈ range (30+1), rowValueQ 4 32 N (countsFromRows 4 32 N frows orows) eps ≤ (366923771/1000000000000:ℚ) := by
  intro N hN
  have hN' : N < 30+1 := mem_range.mp hN
  interval_cases N
  · change rowValueQ 4 32 0 [0,0,0,0] eps ≤ (366923771/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 32 1 [0,0,0,0] eps ≤ (366923771/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 32 2 [0,0,0,2] eps ≤ (366923771/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 32 3 [6,18,6,24] eps ≤ (366923771/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 32 4 [168,232,168,262] eps ≤ (366923771/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 32 5 [1570,1890,1790,2220] eps ≤ (366923771/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 32 6 [8450,10122,10770,12866] eps ≤ (366923771/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 32 7 [32305,39536,45031,54376] eps ≤ (366923771/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 32 8 [98344,123516,147624,182358] eps ≤ (366923771/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 32 9 [254760,328176,407304,515779] eps ≤ (366923771/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 32 10 [585300,771960,988500,1282150] eps ≤ (366923771/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 32 11 [1225620,1651914,2172720,2881857] eps ≤ (366923771/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 32 12 [2383920,3277692,4413552,5975860] eps ≤ (366923771/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 32 13 [4366362,6114394,8407542,11601317] eps ≤ (366923771/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 32 14 [7607782,10835370,15183350,21320026] eps ≤ (366923771/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 32 15 [12708215,18386160,26211705,37404915] eps ≤ (366923771/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 32 16 [20475760,30060776,43538800,63070148] eps ≤ (366923771/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 32 17 [31976320,47591568,69945888,102750754] eps ≤ (366923771/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 32 18 [48590760,73253952,109137960,162438026] eps ≤ (366923771/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 32 19 [72080034,109987314,165964506,250077278] eps ≤ (366923771/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 32 20 [104658840,161533440,246675480,376034890] eps ≤ (366923771/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 32 21 [149078370,232593858,359215710,553641914] eps ≤ (366923771/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 32 22 [208718730,329007514,513561114,799821858] eps ≤ (366923771/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 32 23 [287691613,457950240,722100203,1135810610] eps ≤ (366923771/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 32 24 [390953816,628157508,1000064472,1587976810] eps ≤ (366923771/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 32 25 [524432200,850172000,1366011400,2188751325] eps ≤ (366923771/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 32 26 [695160700,1136617560,1842363900,2977674830] eps ≤ (366923771/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 32 27 [911430000,1502501130,2456010180,4002572847] eps ≤ (366923771/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 32 28 [1182950496,1965544308,3238968096,5320867944] eps ≤ (366923771/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 32 29 [1521029178,2546546202,4229118198,7001039147] eps ≤ (366923771/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 32 30 [1938761070,3269779290,5471009790,9124238970] eps ≤ (366923771/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
lemma scale_bound : AScale 4 32 ≤ (366923771/1000000000000:ℝ) := by
  have hh := numeric_scale_bound 4 32 (366923771/1000000000000:ℚ) (fun N => countsFromRows 4 32 N frows orows) eps
    (countsFromRows_correct 4 32 30 frows orows fbase fstep obase ostep) eps_bound value_bound
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hh
  exact hh
#print axioms scale_bound
end Erdos708H97.Proofs.Numeric4_32
