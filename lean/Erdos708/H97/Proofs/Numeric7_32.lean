import Erdos708.H97.Proofs.Numeric7_32Rows
open Finset BigOperators
namespace Erdos708H97.Proofs.Numeric7_32
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
def eps : List ℚ := [(34152711197677/2000000000000000000000:ℚ),(19558384028903/1000000000000000000000:ℚ),(6020795598547/250000000000000000000:ℚ),(328051998018117/10000000000000000000000:ℚ),(55244867721801/1250000000000000000000:ℚ),(555865885530699/10000000000000000000000:ℚ),(669772829286989/10000000000000000000000:ℚ)]
lemma eps_bound : ∀ d ∈ (Icc 1 7 : Finset ℕ), epsilon ((7:ℝ)/32) (1+(d:ℝ)/32) ≤ (eps[d-1]?.getD 0:ℚ) := by
  intro d hd
  obtain ⟨hd0,hd1⟩ := mem_Icc.mp hd
  interval_cases d
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(1:ℝ)/32))/((7:ℝ)/32)⌋₊ = 20 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(1:ℝ)/32))/((7:ℝ)/32)) 17 = 21 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((7:ℝ)/32) (1+(1:ℝ)/32) 17 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 21 17 = 5985 by decide,show Nat.factorial 17 = 355687428096000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(2:ℝ)/32))/((7:ℝ)/32)⌋₊ = 19 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(2:ℝ)/32))/((7:ℝ)/32)) 17 = 21 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((7:ℝ)/32) (1+(2:ℝ)/32) 17 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 21 17 = 5985 by decide,show Nat.factorial 17 = 355687428096000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(3:ℝ)/32))/((7:ℝ)/32)⌋₊ = 19 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(3:ℝ)/32))/((7:ℝ)/32)) 16 = 21 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((7:ℝ)/32) (1+(3:ℝ)/32) 16 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 21 16 = 20349 by decide,show Nat.factorial 16 = 20922789888000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(4:ℝ)/32))/((7:ℝ)/32)⌋₊ = 19 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(4:ℝ)/32))/((7:ℝ)/32)) 16 = 20 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((7:ℝ)/32) (1+(4:ℝ)/32) 16 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 20 16 = 4845 by decide,show Nat.factorial 16 = 20922789888000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(5:ℝ)/32))/((7:ℝ)/32)⌋₊ = 19 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(5:ℝ)/32))/((7:ℝ)/32)) 16 = 20 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((7:ℝ)/32) (1+(5:ℝ)/32) 16 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 20 16 = 4845 by decide,show Nat.factorial 16 = 20922789888000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(6:ℝ)/32))/((7:ℝ)/32)⌋₊ = 19 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(6:ℝ)/32))/((7:ℝ)/32)) 16 = 20 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((7:ℝ)/32) (1+(6:ℝ)/32) 16 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 20 16 = 4845 by decide,show Nat.factorial 16 = 20922789888000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(7:ℝ)/32))/((7:ℝ)/32)⌋₊ = 19 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(7:ℝ)/32))/((7:ℝ)/32)) 16 = 20 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((7:ℝ)/32) (1+(7:ℝ)/32) 16 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 20 16 = 4845 by decide,show Nat.factorial 16 = 20922789888000 by decide]
    norm_num [T,Hstar,eps]
lemma value_bound : ∀ N ∈ range (17+1), rowValueQ 7 32 N (countsFromRows 7 32 N frows orows) eps ≤ (2409960257/1000000000000:ℚ) := by
  intro N hN
  have hN' : N < 17+1 := mem_range.mp hN
  interval_cases N
  · change rowValueQ 7 32 0 [0,0,0,0,0,0,0] eps ≤ (2409960257/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 32 1 [0,0,0,0,0,0,0] eps ≤ (2409960257/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 32 2 [0,0,2,0,0,0,2] eps ≤ (2409960257/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 32 3 [12,3,21,0,12,3,21] eps ≤ (2409960257/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 32 4 [64,30,100,24,92,42,132] eps ≤ (2409960257/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 32 5 [200,120,311,125,350,195,495] eps ≤ (2409960257/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 32 6 [480,330,756,390,960,600,1380] eps ≤ (2409960257/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 32 7 [980,735,1568,945,2170,1470,3192] eps ≤ (2409960257/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 32 8 [1792,1428,2912,1960,4312,3108,6496] eps ≤ (2409960257/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 32 9 [3024,2520,4986,3654,7812,5922,12042] eps ≤ (2409960257/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 32 10 [4800,4140,8022,6300,13200,10440,20790] eps ≤ (2409960257/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 32 11 [7260,6435,12287,10230,21120,17325,33935] eps ≤ (2409960257/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 32 12 [10560,9570,18084,15840,32340,27390,52932] eps ≤ (2409960257/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 32 13 [14872,13728,25753,23595,47762,41613,79521] eps ≤ (2409960257/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 32 14 [20384,19110,35672,34034,68432,61152,115752] eps ≤ (2409960257/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 32 15 [27300,25935,48258,47775,95550,87360,164010] eps ≤ (2409960257/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 32 16 [35840,34440,63968,65520,130480,121800,227040] eps ≤ (2409960257/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 32 17 [46240,44880,83300,88060,174760,166260,307972] eps ≤ (2409960257/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
lemma scale_bound : AScale 7 32 ≤ (2409960257/1000000000000:ℝ) := by
  have hh := numeric_scale_bound 7 32 (2409960257/1000000000000:ℚ) (fun N => countsFromRows 7 32 N frows orows) eps
    (countsFromRows_correct 7 32 17 frows orows fbase fstep obase ostep) eps_bound value_bound
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hh
  exact hh
#print axioms scale_bound
end Erdos708H97.Proofs.Numeric7_32
