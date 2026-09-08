import Erdos708.H97.Proofs.Numeric5_64Rows
open Finset BigOperators
namespace Erdos708H97.Proofs.Numeric5_64
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
def eps : List ℚ := [(968625202917/20000000000000000000000000000000:ℚ),(61311914439959/1000000000000000000000000000000000:ℚ),(18548142183517/250000000000000000000000000000000:ℚ),(4034145525963/40000000000000000000000000000000:ℚ),(15815684164287/100000000000000000000000000000000:ℚ)]
lemma eps_bound : ∀ d ∈ (Icc 1 5 : Finset ℕ), epsilon ((5:ℝ)/64) (1+(d:ℝ)/64) ≤ (eps[d-1]?.getD 0:ℚ) := by
  intro d hd
  obtain ⟨hd0,hd1⟩ := mem_Icc.mp hd
  interval_cases d
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(1:ℝ)/64))/((5:ℝ)/64)⌋₊ = 56 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(1:ℝ)/64))/((5:ℝ)/64)) 45 = 57 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((5:ℝ)/64) (1+(1:ℝ)/64) 45 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 57 45 = 707285522580 by decide,show Nat.factorial 45 = 119622220865480194561963161495657715064383733760000000000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(2:ℝ)/64))/((5:ℝ)/64)⌋₊ = 56 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(2:ℝ)/64))/((5:ℝ)/64)) 45 = 57 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((5:ℝ)/64) (1+(2:ℝ)/64) 45 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 57 45 = 707285522580 by decide,show Nat.factorial 45 = 119622220865480194561963161495657715064383733760000000000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(3:ℝ)/64))/((5:ℝ)/64)⌋₊ = 55 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(3:ℝ)/64))/((5:ℝ)/64)) 45 = 57 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((5:ℝ)/64) (1+(3:ℝ)/64) 45 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 57 45 = 707285522580 by decide,show Nat.factorial 45 = 119622220865480194561963161495657715064383733760000000000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(4:ℝ)/64))/((5:ℝ)/64)⌋₊ = 55 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(4:ℝ)/64))/((5:ℝ)/64)) 44 = 56 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((5:ℝ)/64) (1+(4:ℝ)/64) 44 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 56 44 = 558383307300 by decide,show Nat.factorial 44 = 2658271574788448768043625811014615890319638528000000000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(5:ℝ)/64))/((5:ℝ)/64)⌋₊ = 55 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(5:ℝ)/64))/((5:ℝ)/64)) 44 = 56 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((5:ℝ)/64) (1+(5:ℝ)/64) 44 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 56 44 = 558383307300 by decide,show Nat.factorial 44 = 2658271574788448768043625811014615890319638528000000000 by decide]
    norm_num [T,Hstar,eps]
lemma value_bound : ∀ N ∈ range (47+1), rowValueQ 5 64 N (countsFromRows 5 64 N frows orows) eps ≤ (179755833/1000000000000:ℚ) := by
  intro N hN
  have hN' : N < 47+1 := mem_range.mp hN
  interval_cases N
  · change rowValueQ 5 64 0 [0,0,0,0,0] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 1 [0,0,0,0,0] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 2 [0,0,0,0,2] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 3 [18,3,12,6,27] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 4 [316,102,300,120,336] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 5 [4040,2240,4110,2195,4215] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 6 [38982,29925,41370,30885,43770] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 7 [294840,269430,326508,294357,359982] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 8 [1787352,1794380,2069488,2060786,2379216] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 9 [8836848,9385416,10707246,11297313,12850365] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 10 [36544492,40333905,46277970,50758615,57956890] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 11 [129946971,147671898,171536024,193725697,223747832] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 12 [407339868,474072148,558789804,646295760,757156676] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 13 [1149223947,1365019955,1633331947,1927998813,2292606433] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 14 [2967426112,3588328016,4357147522,5236291606,6318370240] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 15 [7107297666,8733460190,10754218995,13133681925,16071467440] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 16 [15960761472,19900534384,24831574832,30772260356,38158421536] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 17 [33900780724,42837654884,54122148328,67975588034,85351820474] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 18 [68590122768,87749040318,112170968964,142639530642,181221208938] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 19 [132970816988,172078230297,222410221128,286100127284,367535231621] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 20 [248207343372,324673753890,424026900700,551357453840,715736021480] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 21 [447938391390,591872637398,780625439664,1025350396707,1344254679607] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 22 [784291221098,1046193968743,1392733677170,1846860271179,2444028768566] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 23 [1336231638480,1798524724634,2415501549914,3232094607753,4315321985966] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 24 [2220963942456,3014907871804,4083306195264,5510580898182,7419858199568] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 25 [3609261672420,4939313417900,6743413898950,9174699818875,12453395214575] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 26 [5745804530780,7924092041255,10901368348390,14947026148145,20445209372770] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 27 [8975822614605,12470184001080,17281386656820,23870642589495,32892574832442] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 28 [13779609399948,19279589460768,26905761126972,37428768007176,51940238901852] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 29 [20816763317721,29323106809857,41198098121205,57701419922685,80617158285041] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 30 [30982357981620,43926920142090,62116188993210,87568436081220,123145415329740] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 31 [45477627125722,64882273281570,92321416040505,130970037935865,185339326884000] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 32 [65898186244160,94583213648000,135392864043168,193238258437832,275116343635392] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 33 [94343303177112,136198233287160,196095751339488,281515008022116,403145471379156] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 34 [133550279057088,193882585517676,280715430751176,405275348706228,583663688353650] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 35 [187058613943782,273039123307055,397470058258420,576977721523490,835496249836815] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 36 [259409313191196,380636699641758,557017105469004,812866464095112,1183322932462272] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 37 [356385446398228,525596501268108,773071221068754,1133956002339715,1659239250810631] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 38 [485300906222862,719258166252825,1063153548168362,1567230644861953,2304669557335538] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 39 [655345235162712,975939174385006,1449495501533352,2147098994669421,3172697798300030] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 40 [877993400640216,1313602809609740,1960123225063120,2917147667309850,4330891633141840] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 41 [1167490508649832,1754651988106784,2630152510770382,3932245316700181,5864706728062561] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 42 [1541422660353324,2326868437542509,3503327892369018,5261054971944219,7881570407825674] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 43 [2021386481133663,3064519116255478,4633843957168544,6989020435199117,10515757599792508] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 44 [2633771294788348,4009654390112492,6088491678388108,9221901039907424,13934187244209716] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 45 [3410669484077607,5213625354532815,7949177786692575,12089938481154765,18343284194008305] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 46 [4390932280333160,6738850815388788,10315870906559634,15752749769255042,23997070211629592] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 5 64 47 [5621390067147138,8660867841453558,13310034413274175,20405051690713469,31206668122022336] eps ≤ (179755833/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
lemma scale_bound : AScale 5 64 ≤ (179755833/1000000000000:ℝ) := by
  have hh := numeric_scale_bound 5 64 (179755833/1000000000000:ℚ) (fun N => countsFromRows 5 64 N frows orows) eps
    (countsFromRows_correct 5 64 47 frows orows fbase fstep obase ostep) eps_bound value_bound
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hh
  exact hh
#print axioms scale_bound
end Erdos708H97.Proofs.Numeric5_64
