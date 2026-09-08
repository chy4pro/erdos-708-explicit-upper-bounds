import Erdos708.H97.Proofs.Numeric4_64Rows
open Finset BigOperators
namespace Erdos708H97.Proofs.Numeric4_64
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
def eps : List ℚ := [(188625040006421/100000000000000000000000000000000000000:ℚ),(256967445805849/100000000000000000000000000000000000000:ℚ),(2033186572533/625000000000000000000000000000000000:ℚ),(5332334534991/1000000000000000000000000000000000000:ℚ)]
lemma eps_bound : ∀ d ∈ (Icc 1 4 : Finset ℕ), epsilon ((4:ℝ)/64) (1+(d:ℝ)/64) ≤ (eps[d-1]?.getD 0:ℚ) := by
  intro d hd
  obtain ⟨hd0,hd1⟩ := mem_Icc.mp hd
  interval_cases d
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(1:ℝ)/64))/((4:ℝ)/64)⌋₊ = 70 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(1:ℝ)/64))/((4:ℝ)/64)) 55 = 71 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((4:ℝ)/64) (1+(1:ℝ)/64) 55 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 71 55 = 3201570572795084 by decide,show Nat.factorial 55 = 12696403353658275925965100847566516959580321051449436762275840000000000000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(2:ℝ)/64))/((4:ℝ)/64)⌋₊ = 70 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(2:ℝ)/64))/((4:ℝ)/64)) 55 = 71 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((4:ℝ)/64) (1+(2:ℝ)/64) 55 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 71 55 = 3201570572795084 by decide,show Nat.factorial 55 = 12696403353658275925965100847566516959580321051449436762275840000000000000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(3:ℝ)/64))/((4:ℝ)/64)⌋₊ = 69 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(3:ℝ)/64))/((4:ℝ)/64)) 55 = 71 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((4:ℝ)/64) (1+(3:ℝ)/64) 55 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 71 55 = 3201570572795084 by decide,show Nat.factorial 55 = 12696403353658275925965100847566516959580321051449436762275840000000000000 by decide]
    norm_num [T,Hstar,eps]
  · simp only [Nat.cast_ofNat,Nat.cast_one]
    have ha : ⌊(T-(1+(4:ℝ)/64))/((4:ℝ)/64)⌋₊ = 69 := (Nat.floor_eq_iff (by norm_num [T])).mpr (by norm_num [T])
    have hv : maximizingVertex ((T-(1+(4:ℝ)/64))/((4:ℝ)/64)) 54 = 70 := by
      unfold maximizingVertex
      apply (Nat.floor_eq_iff (by norm_num [T])).mpr
      norm_num [T]
    apply (epsilon_le_moment ((4:ℝ)/64) (1+(4:ℝ)/64) 54 (by rw [momentRange,ha]; norm_num)).trans
    unfold momentBound hingeMajorant
    rw [hv,show Nat.choose 70 54 = 2480089880334220 by decide,show Nat.factorial 54 = 230843697339241380472092742683027581083278564571807941132288000000000000 by decide]
    norm_num [T,Hstar,eps]
lemma value_bound : ∀ N ∈ range (59+1), rowValueQ 4 64 N (countsFromRows 4 64 N frows orows) eps ≤ (26931033/1000000000000:ℚ) := by
  intro N hN
  have hN' : N < 59+1 := mem_range.mp hN
  interval_cases N
  · change rowValueQ 4 64 0 [0,0,0,0] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 1 [0,0,0,0] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 2 [0,0,0,2] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 3 [6,12,6,27] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 4 [156,312,132,376] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 5 [3280,4990,3160,5385] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 6 [50130,61680,51750,65796] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 7 [541282,608958,584864,663061] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 8 [4446792,4879560,5007576,5492544] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 9 [29241036,32181558,34345368,37661049] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 10 [158899440,177397200,194892760,216428620] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 11 [732235581,832730789,937761649,1059806770] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 12 [2928137520,3395827622,3910736412,4504493874] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 13 [10369466575,12260292382,14414425623,16921140236] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 14 [33088290144,39852802003,47764463656,57107809864] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 15 [96528227943,118315971040,144367035570,175639163670] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 16 [260578238032,324698934648,402870173968,498259437788] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 17 [657467183604,832023767724,1048596624596,1317094716499] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 18 [1563432395976,2007491987796,2567371156920,3272044934124] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 19 [3528392575752,4592949896406,5955297945620,7694654115716] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 20 [7601700381972,10023640479940,13166379555380,17233371483060] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 21 [15712094204982,20971979262598,27886563184998,36949592235696] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 22 [31288334894894,42247138726166,56830682838138,76177720664694] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 23 [60246360752336,82243097907190,111855331585360,151592119330874] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 24 [112522412428152,155213128726496,213315442585704,292135089889740] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 25 [204403493249680,284764400468850,395277166675500,546753095021250] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 26 [362001615651000,509121001018500,713449218866800,996288451559570] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 27 [626342395189095,888907522811895,1257027251537655,1771411867165917] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 28 [1060698662946216,1518470859231522,2166082885810956,3079195668292422] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 29 [1761004119242781,2542099818537222,3656697152452797,5241864820010561] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 30 [2870440328792940,4176938139434865,6056768762161260,8752478870820510] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 31 [4599613860877725,6744937143726360,9856358233875330,14353859802980341] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 32 [7254142223705632,10716883756216528,15777603557658784,23149068134181576] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 33 [11271962572153272,16772396078791320,24870713459544216,36754236676422474] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 34 [17273283379162096,25880834669191128,38644370758854608,57507708751993294] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 35 [26126836249322970,39409370632581600,59241130708175010,88753324679095545] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 36 [39036975477175116,59266024572154704,89671158343758564,135220507289647920] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 37 [57657242515071900,88087392450213102,134121007589030932,203529688090634779] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 38 [84237290263661130,129483061315707932,198358209427325518,302858790871734256] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 39 [121811580745610574,188351452928896478,290257328088286416,445815179107405419] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 40 [174440065991607208,271285088010620440,420479000573856120,649567940324498120] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 41 [247513176949816452,387087118589644078,603340451891855248,937307924159445823] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 42 [348135924776463264,547425520966154824,857924252016964776,1340117910999325584] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 43 [485608813993553761,767656678128775401,1209481848815219485,1899353049418005764] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 44 [672026634328079712,1067856320720151006,1691199896010829820,2669652696780238906] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 45 [923020100252426187,1474103065216571790,2346410845157360355,3722729516119584810] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 46 [1258669813548515832,2020068226039881423,3231344962660193648,5152110670666420796] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 47 [1704627210893113059,2748975338970745696,4418539175643299138,7079039826992880624] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 48 [2293483109376095856,3716004086760904840,6001039286332509360,9659788111214053764] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 49 [3066431270044528652,4991226251980366916,8097556503007748364,13094667919743472965] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 50 [4075282163796199160,6663176143429050700,10858767335782093000,17639096410376441000] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 51 [5384890955392626300,8843174877686249450,14474978160020002800,23617116525746193690] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 52 [7076073740229366340,11670547195124386140,19185412668268147860,31437853563072402732] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 53 [9249097405726757826,15318891421893328182,25289422572563369506,41615465742190664042] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 54 [12027841287175984806,20003588052941970882,33159969896429808162,54793239194344530546] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 55 [15564743201192219100,25990760549839239990,43259783681460651360,71772582678175226760] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 56 [20046658636188981720,33607933673394566640,56160655661202698760,93547796642311182836] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 57 [25701780039925558632,43256670387863115498,72566409226150524804,121347626656275876816] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 58 [32807783465316384552,55427508496494633180,93340154690696806656,156684764539065571654] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
  · change rowValueQ 4 64 59 [41701392529048850731,70717563147760100923,119536532425201023523,201414633710748784839] eps ≤ (26931033/1000000000000:ℚ)
    norm_num [rowValueQ,ratioQ,eps,sum_Icc_succ_top]
lemma scale_bound : AScale 4 64 ≤ (26931033/1000000000000:ℝ) := by
  have hh := numeric_scale_bound 4 64 (26931033/1000000000000:ℚ) (fun N => countsFromRows 4 64 N frows orows) eps
    (countsFromRows_correct 4 64 59 frows orows fbase fstep obase ostep) eps_bound value_bound
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hh
  exact hh
#print axioms scale_bound
end Erdos708H97.Proofs.Numeric4_64
