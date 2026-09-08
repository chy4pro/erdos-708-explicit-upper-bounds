import Erdos708.H97.Proofs.Numeric7_64Rows
open Finset BigOperators
namespace Erdos708H97.Proofs.Numeric7_64
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
def eps : List ℚ := [(57248430473579/10000000000000000000000000000:ℚ),(8398424262183/1250000000000000000000000000:ℚ),(1542527154427/200000000000000000000000000:ℚ),(17413064269047/2000000000000000000000000000:ℚ),(15361662177077/1250000000000000000000000000:ℚ),(16741985445163/1000000000000000000000000000:ℚ),(211946411486627/10000000000000000000000000000:ℚ)]
lemma eps_bound : ∀ d ∈ (Icc 1 7 : Finset ℕ), epsilon ((7:ℝ)/64) (1+(d:ℝ)/64) ≤ (eps[d-1]?.getD 0:ℚ) := by
  intro d hd
  obtain ⟨hd0,hd1⟩ := mem_Icc.mp hd
  interval_cases d
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(1:ℝ)/64))/((7:ℝ)/64)⌋₊ = 40 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(1:ℝ)/64))/((7:ℝ)/64)) 32 = 41 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((7:ℝ)/64) (1+(1:ℝ)/64) 32 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 41 32 = 350343565 by decide,show Nat.factorial 32 = 263130836933693530167218012160000000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(2:ℝ)/64))/((7:ℝ)/64)⌋₊ = 40 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(2:ℝ)/64))/((7:ℝ)/64)) 32 = 41 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((7:ℝ)/64) (1+(2:ℝ)/64) 32 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 41 32 = 350343565 by decide,show Nat.factorial 32 = 263130836933693530167218012160000000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(3:ℝ)/64))/((7:ℝ)/64)⌋₊ = 39 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(3:ℝ)/64))/((7:ℝ)/64)) 32 = 41 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((7:ℝ)/64) (1+(3:ℝ)/64) 32 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 41 32 = 350343565 by decide,show Nat.factorial 32 = 263130836933693530167218012160000000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(4:ℝ)/64))/((7:ℝ)/64)⌋₊ = 39 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(4:ℝ)/64))/((7:ℝ)/64)) 32 = 41 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((7:ℝ)/64) (1+(4:ℝ)/64) 32 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 41 32 = 350343565 by decide,show Nat.factorial 32 = 263130836933693530167218012160000000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(5:ℝ)/64))/((7:ℝ)/64)⌋₊ = 39 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(5:ℝ)/64))/((7:ℝ)/64)) 31 = 40 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((7:ℝ)/64) (1+(5:ℝ)/64) 31 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 40 31 = 273438880 by decide,show Nat.factorial 31 = 8222838654177922817725562880000000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(6:ℝ)/64))/((7:ℝ)/64)⌋₊ = 39 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(6:ℝ)/64))/((7:ℝ)/64)) 31 = 40 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((7:ℝ)/64) (1+(6:ℝ)/64) 31 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 40 31 = 273438880 by decide,show Nat.factorial 31 = 8222838654177922817725562880000000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(7:ℝ)/64))/((7:ℝ)/64)⌋₊ = 39 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(7:ℝ)/64))/((7:ℝ)/64)) 31 = 40 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((7:ℝ)/64) (1+(7:ℝ)/64) 31 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 40 31 = 273438880 by decide,show Nat.factorial 31 = 8222838654177922817725562880000000 by decide]
    norm_num [T,Hstar,eps]
lemma value_bound : ∀ N ∈ range (34+1), rowValueQ 7 64 N (countsFromRows 7 64 N frows orows) eps ≤ (427779289/1000000000000:ℚ) := by
  intro N hN
  have hN' : N < 34+1 := mem_range.mp hN
  interval_cases N
  · change rowValueQ 7 64 0 [0,0,0,0,0,0,0] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 1 [0,0,0,0,0,0,0] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 2 [0,0,0,0,0,0,2] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 3 [6,0,18,0,6,3,27] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 4 [180,36,268,12,184,54,312] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 5 [2040,630,2480,455,2310,720,2875] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 6 [13230,5640,15552,5295,16490,6705,19260] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 7 [60186,32347,71883,34650,82061,42462,96537] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 8 [214488,135744,263760,157710,317192,195972,383320] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 9 [640188,456213,812394,561339,1018008,715347,1269171] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 10 [1670940,1302090,2185620,1674630,2835060,2192581,3644290] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 11 [3927330,3281025,5283894,4374975,7062660,5879621,9341860] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 12 [8486412,7496544,11718036,10306890,16084992,14193960,21842832] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 13 [17117100,15828813,24206182,22350900,34031998,31484167,47342308] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 14 [32596746,31321290,47121620,45286241,67707822,65140166,96298020] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 15 [59125950,58697730,87227595,86697975,127865075,127148658,185604720] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 16 [102860400,105036880,154639776,158186340,230909360,236210848,341563600] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 17 [172580328,180635166,264061884,276943770,401130368,420557594,603843162] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 18 [280519992,300090732,436344984,467773020,673568424,721616238,1030657266] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 19 [443381454,483645342,700426146,765628218,1097638626,1198703711,1705417409] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 20 [683558820,758823900,1095707580,1218769440,1741648680,1934942026,2745149640] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 21 [1030601040,1162414680,1674942948,1892630565,2698361190,3044614986,4311001905] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 22 [1522943334,1742836788,2507703352,2874509715,4091766514,4682208839,6621205052] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 23 [2209939314,2562944901,3684501491,4279201520,6085248345,7053404710,9966890219] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 24 [3154227912,3703324944,5321658672,6255700770,8891340920,10428316932,14731206888] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 25 [4434471300,5266138075,7567005750,8995117725,12783294200,15157298885,21412229525] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 26 [6148502100,7379574150,10606515660,12739956450,18108681500,21689666635,30650186450] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 27 [8416920330,10202979735,14671971990,17794919025,25305302880,30595720545,43259592402] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 28 [11387182716,13932729720,20049785028,24539410350,34919657136,42592476108,60266916192] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 29 [15238229220,18808915671,27091073898,33441930522,47628275454,58573547529,82954466882] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 30 [20185693890,25122928230,36223140780,45076554405,64262230710,79643661060,112911236100] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 31 [26487749430,33226015140,47962470787,60141711045,85835158015,107158309770,152091490410] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 32 [34451637216,43538900832,62929398848,79481489000,113575144416,142769097312,202881966112] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 33 [44440936848,56562557964,81864592920,104109707460,148960868672,188475355332,268178579460] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 7 64 34 [56883631728,72890225848,105647511024,135237007224,193762395728,246682657452,351473628066] eps ≤ (427779289/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
lemma scale_bound : AScale 7 64 ≤ (427779289/1000000000000:ℝ) := by
  have hh := numeric_scale_bound 7 64 (427779289/1000000000000:ℚ) (fun N => countsFromRows 7 64 N frows orows) eps
    (countsFromRows_correct 7 64 34 frows orows fbase fstep obase ostep) eps_bound value_bound
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hh
  exact hh
#print axioms scale_bound
end Erdos708H97.Proofs.Numeric7_64
