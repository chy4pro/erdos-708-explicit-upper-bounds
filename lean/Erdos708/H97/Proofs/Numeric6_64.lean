import Erdos708.H97.Proofs.Numeric6_64Rows
open Finset BigOperators
namespace Erdos708H97.Proofs.Numeric6_64
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
def eps : List ℚ := [(14889529942579/400000000000000000000000000000:ℚ),(440226390843773/10000000000000000000000000000000:ℚ),(68323795992249/1000000000000000000000000000000:ℚ),(18615758908033/200000000000000000000000000000:ℚ),(117833793088081/1000000000000000000000000000000:ℚ),(35647197908999/250000000000000000000000000000:ℚ)]
lemma eps_bound : ∀ d ∈ (Icc 1 6 : Finset ℕ), epsilon ((6:ℝ)/64) (1+(d:ℝ)/64) ≤ (eps[d-1]?.getD 0:ℚ) := by
  intro d hd
  obtain ⟨hd0,hd1⟩ := mem_Icc.mp hd
  interval_cases d
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(1:ℝ)/64))/((6:ℝ)/64)⌋₊ = 46 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(1:ℝ)/64))/((6:ℝ)/64)) 38 = 48 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((6:ℝ)/64) (1+(1:ℝ)/64) 38 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 48 38 = 6540715896 by decide,show Nat.factorial 38 = 523022617466601111760007224100074291200000000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(2:ℝ)/64))/((6:ℝ)/64)⌋₊ = 46 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(2:ℝ)/64))/((6:ℝ)/64)) 37 = 48 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((6:ℝ)/64) (1+(2:ℝ)/64) 37 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 48 37 = 22595200368 by decide,show Nat.factorial 37 = 13763753091226345046315979581580902400000000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(3:ℝ)/64))/((6:ℝ)/64)⌋₊ = 46 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(3:ℝ)/64))/((6:ℝ)/64)) 37 = 47 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((6:ℝ)/64) (1+(3:ℝ)/64) 37 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 47 37 = 5178066751 by decide,show Nat.factorial 37 = 13763753091226345046315979581580902400000000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(4:ℝ)/64))/((6:ℝ)/64)⌋₊ = 46 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(4:ℝ)/64))/((6:ℝ)/64)) 37 = 47 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((6:ℝ)/64) (1+(4:ℝ)/64) 37 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 47 37 = 5178066751 by decide,show Nat.factorial 37 = 13763753091226345046315979581580902400000000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(5:ℝ)/64))/((6:ℝ)/64)⌋₊ = 46 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(5:ℝ)/64))/((6:ℝ)/64)) 37 = 47 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((6:ℝ)/64) (1+(5:ℝ)/64) 37 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 47 37 = 5178066751 by decide,show Nat.factorial 37 = 13763753091226345046315979581580902400000000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(6:ℝ)/64))/((6:ℝ)/64)⌋₊ = 46 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(6:ℝ)/64))/((6:ℝ)/64)) 37 = 47 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((6:ℝ)/64) (1+(6:ℝ)/64) 37 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 47 37 = 5178066751 by decide,show Nat.factorial 37 = 13763753091226345046315979581580902400000000 by decide]
    norm_num [T,Hstar,eps]
lemma value_bound : ∀ N ∈ range (40+1), rowValueQ 6 64 N (countsFromRows 6 64 N frows orows) eps ≤ (194999323/500000000000:ℚ) := by
  intro N hN
  have hN' : N < 40+1 := mem_range.mp hN
  interval_cases N
  · change rowValueQ 6 64 0 [0,0,0,0,0,0] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 1 [0,0,0,0,0,0] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 2 [0,0,0,0,0,2] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 3 [0,18,0,9,6,27] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 4 [72,284,36,246,108,324] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 5 [1340,3090,1190,3230,1500,3425] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 6 [14340,24446,14940,27045,16590,28836] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 7 [101094,146202,113575,167923,128114,187005] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 8 [517328,688920,614264,822752,722512,960716] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 9 [2081664,2664606,2590128,3310713,3183396,4042791] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 10 [6980862,8779750,9049710,11329390,11585920,14409742] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 11 [20325822,25406283,27327971,33955856,36301705,44803495] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 12 [52903620,66124356,73493772,91268958,100926408,124480092] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 13 [125727888,157669590,179907156,224136913,254598058,314998840] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 14 [277174898,349391952,407461054,510296059,592604194,737002084] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 15 [573707316,727656995,864522750,1089553920,1289200185,1613409891] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 16 [1125433296,1436996176,1735157008,2201794448,2647800720,3336261592] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 17 [2108026928,2710244652,3319871656,4242457270,5175182432,6566614378] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 18 [3792848580,4910395668,6092884116,7841317932,9688069344,12379495914] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 19 [6587451924,8587453712,10780770354,13971724499,17462485952,22468942043] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 20 [11089049952,14554187340,18468332500,24098959510,30438577220,39431671812] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 21 [18153936612,23985370290,30738614466,40378107336,51496232760,67152000867] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 22 [28986325368,38545859530,49855212792,65913727649,84819836486,111315212228] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 23 [45250572554,60553694544,78996379209,105095778249,136373815820,180081832953] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 24 [69211303392,93185316776,122551898568,164028607248,214514409120,284961149508] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 25 [103906553520,140731005050,186495357400,251072457975,330767229700,441928877945] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 26 [153359680370,208909705290,278846201010,377519812410,500804803200,672841232310] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 27 [222836488290,305253604305,410237917245,558432053010,745663315995,1007205752007] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 28 [319154750460,439574061108,594610789500,813665361054,1093243359936,1484378202972] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 29 [451054100952,624521868534,850049936736,1169118504771,1580145517398,2156264706194] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 30 [629635113270,876256276140,1199791810890,1658239215255,2253898225050,3090619018980] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 31 [868877278920,1215238765841,1673424958680,2323830215310,3175642509915,4375036648911] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 32 [1186246552544,1667169237792,2308313682080,3220200668768,4423345932384,6121760268080] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 33 [1603404140448,2264084039000,3151276256304,4415713868412,6095626423392,8473424767236] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 34 [2147029278504,3045637154376,4260552592648,5995787392408,8316275692736,11609885298066] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 35 [2849769874952,4060587882750,5708099672660,8066407745165,11239581538570,15756287850107] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 36 [3751336085112,5368520442108,7582256736516,10758227671926,15056558730780,21192559350660] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 37 [4899753139980,7041823192306,9990826088862,14231320910338,20002209199828,28264513016437] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 38 [6352791070668,9167957533110,13064619496436,18680676130013,26363944064638,37396784780260] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 39 [8179590357198,11852049033942,16961524500219,24342519225999,34491312605334,49107838121589] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 6 64 40 [10462503984816,15219835982520,21871149557400,31501560987520,44807196656560,64027297603516] eps ≤ (194999323/500000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
lemma scale_bound : AScale 6 64 ≤ (194999323/500000000000:ℝ) := by
  have hh := numeric_scale_bound 6 64 (194999323/500000000000:ℚ) (fun N => countsFromRows 6 64 N frows orows) eps
    (countsFromRows_correct 6 64 40 frows orows fbase fstep obase ostep) eps_bound value_bound
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hh
  exact hh
#print axioms scale_bound
end Erdos708H97.Proofs.Numeric6_64
