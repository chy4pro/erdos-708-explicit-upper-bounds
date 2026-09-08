import Erdos708.H97.Proofs.NumericDefs
open Finset BigOperators
namespace Erdos708H97.Proofs.Numeric7_32
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
def degrees : Finset ℕ := {7,8,10,12,14,16,20,24,28,32}
lemma degrees_eq : exponentsExec 7 32 = degrees := by decide
def f0 : List ℕ := [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def f1 : List ℕ := [1,0,0,0,0,0,0,1,1,0,1,0,1,0,1,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0]
def f2 : List ℕ := [1,0,0,0,0,0,0,2,2,0,2,0,2,0,3,2,3,2,2,2,5,2,4,2,7,0,4,2,7,0,4,2,7,0,4,2,6,0,4,2]
def f3 : List ℕ := [1,0,0,0,0,0,0,3,3,0,3,0,3,0,6,6,6,6,6,6,12,7,15,9,22,6,18,15,27,12,25,21,33,12,33,21,40,12,39,21]
def f4 : List ℕ := [1,0,0,0,0,0,0,4,4,0,4,0,4,0,10,12,10,12,12,12,22,16,36,24,50,24,48,48,71,52,82,80,107,64,130,100,158,92,182,132]
def f5 : List ℕ := [1,0,0,0,0,0,0,5,5,0,5,0,5,0,15,20,15,20,20,20,35,30,70,50,95,60,100,110,150,140,200,210,270,200,360,311,455,350,575,495]
def f6 : List ℕ := [1,0,0,0,0,0,0,6,6,0,6,0,6,0,21,30,21,30,30,30,51,50,120,90,161,120,180,210,276,300,410,450,576,480,810,756,1070,960,1440,1380]
def f7 : List ℕ := [1,0,0,0,0,0,0,7,7,0,7,0,7,0,28,42,28,42,42,42,70,77,189,147,252,210,294,357,462,560,749,847,1092,980,1589,1568,2191,2170,3094,3192]
def f8 : List ℕ := [1,0,0,0,0,0,0,8,8,0,8,0,8,0,36,56,36,56,56,56,92,112,280,224,372,336,448,560,722,952,1260,1456,1898,1792,2828,2912,4060,4312,5964,6496]
def f9 : List ℕ := [1,0,0,0,0,0,0,9,9,0,9,0,9,0,45,72,45,72,72,72,117,156,396,324,525,504,648,828,1071,1512,1992,2340,3087,3024,4680,4986,6978,7812,10602,12042]
def f10 : List ℕ := [1,0,0,0,0,0,0,10,10,0,10,0,10,0,55,90,55,90,90,90,145,210,540,450,715,720,900,1170,1525,2280,3000,3570,4765,4800,7320,8022,11310,13200,17700,20790]
def f11 : List ℕ := [1,0,0,0,0,0,0,11,11,0,11,0,11,0,66,110,66,110,110,110,176,275,715,605,946,990,1210,1595,2101,3300,4345,5225,7051,7260,10945,12287,17490,21120,28105,33935]
def f12 : List ℕ := [1,0,0,0,0,0,0,12,12,0,12,0,12,0,78,132,78,132,132,132,210,352,924,792,1222,1320,1584,2112,2817,4620,6094,7392,10077,10560,15774,18084,26026,32340,42834,52932]
def f13 : List ℕ := [1,0,0,0,0,0,0,13,13,0,13,0,13,0,91,156,91,156,156,156,247,442,1170,1014,1547,1716,2028,2730,3692,6292,8320,10166,13988,14872,22048,25753,37505,47762,63089,79521]
def f14 : List ℕ := [1,0,0,0,0,0,0,14,14,0,14,0,14,0,105,182,105,182,182,182,287,546,1456,1274,1925,2184,2548,3458,4746,8372,11102,13650,18942,20384,30030,35672,52598,68432,90272,115752]
def f15 : List ℕ := [1,0,0,0,0,0,0,15,15,0,15,0,15,0,120,210,120,210,210,210,330,665,1785,1575,2360,2730,3150,4305,6000,10920,14525,17955,25110,27300,40005,48258,72065,95550,126000,164010]
def f16 : List ℕ := [1,0,0,0,0,0,0,16,16,0,16,0,16,0,136,240,136,240,240,240,376,800,2160,1920,2856,3360,3840,5280,7476,14000,18680,23200,32676,35840,52280,63968,96760,130480,172120,227040]
def f17 : List ℕ := [1,0,0,0,0,0,0,17,17,0,17,0,17,0,153,272,153,272,272,272,425,952,2584,2312,3417,4080,4624,6392,9197,17680,23664,29512,41837,46240,67184,83300,127636,174760,230724,307972]
lemma fstep0 : f1 = rowStep (degrees) 39 f0 := by decide
lemma fstep1 : f2 = rowStep (degrees) 39 f1 := by decide
lemma fstep2 : f3 = rowStep (degrees) 39 f2 := by decide
lemma fstep3 : f4 = rowStep (degrees) 39 f3 := by decide
lemma fstep4 : f5 = rowStep (degrees) 39 f4 := by decide
lemma fstep5 : f6 = rowStep (degrees) 39 f5 := by decide
lemma fstep6 : f7 = rowStep (degrees) 39 f6 := by decide
lemma fstep7 : f8 = rowStep (degrees) 39 f7 := by decide
lemma fstep8 : f9 = rowStep (degrees) 39 f8 := by decide
lemma fstep9 : f10 = rowStep (degrees) 39 f9 := by decide
lemma fstep10 : f11 = rowStep (degrees) 39 f10 := by decide
lemma fstep11 : f12 = rowStep (degrees) 39 f11 := by decide
lemma fstep12 : f13 = rowStep (degrees) 39 f12 := by decide
lemma fstep13 : f14 = rowStep (degrees) 39 f13 := by decide
lemma fstep14 : f15 = rowStep (degrees) 39 f14 := by decide
lemma fstep15 : f16 = rowStep (degrees) 39 f15 := by decide
lemma fstep16 : f17 = rowStep (degrees) 39 f16 := by decide
def frows : List (List ℕ) := [f0,f1,f2,f3,f4,f5,f6,f7,f8,f9,f10,f11,f12,f13,f14,f15,f16,f17]
lemma fbase : frows[0]?.getD [] = rowBase 39 := by decide
lemma fstep : ∀ N ∈ range 17, frows[N+1]?.getD [] = rowStep (exponentsExec 7 32) 39 (frows[N]?.getD []) := by
  intro N hN
  rw [degrees_eq]
  have hN' : N < 17 := mem_range.mp hN
  interval_cases N
  · exact fstep0
  · exact fstep1
  · exact fstep2
  · exact fstep3
  · exact fstep4
  · exact fstep5
  · exact fstep6
  · exact fstep7
  · exact fstep8
  · exact fstep9
  · exact fstep10
  · exact fstep11
  · exact fstep12
  · exact fstep13
  · exact fstep14
  · exact fstep15
  · exact fstep16
def o0 : List ℕ := [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def o1 : List ℕ := [1,0,0,0,0,0,0,0,1,0,1,0,1,0,1,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0]
def o2 : List ℕ := [1,0,0,0,0,0,0,0,2,0,2,0,2,0,2,0,3,0,2,0,5,0,4,0,7,0,4,0,7,0,4,0,7,0,4,0,6,0,4,0]
def o3 : List ℕ := [1,0,0,0,0,0,0,0,3,0,3,0,3,0,3,0,6,0,6,0,12,0,12,0,19,0,15,0,24,0,22,0,33,0,30,0,40,0,36,0]
def o4 : List ℕ := [1,0,0,0,0,0,0,0,4,0,4,0,4,0,4,0,10,0,12,0,22,0,24,0,38,0,36,0,58,0,64,0,95,0,100,0,134,0,140,0]
def o5 : List ℕ := [1,0,0,0,0,0,0,0,5,0,5,0,5,0,5,0,15,0,20,0,35,0,40,0,65,0,70,0,115,0,140,0,210,0,240,0,330,0,380,0]
def o6 : List ℕ := [1,0,0,0,0,0,0,0,6,0,6,0,6,0,6,0,21,0,30,0,51,0,60,0,101,0,120,0,201,0,260,0,396,0,480,0,680,0,840,0]
def o7 : List ℕ := [1,0,0,0,0,0,0,0,7,0,7,0,7,0,7,0,28,0,42,0,70,0,84,0,147,0,189,0,322,0,434,0,672,0,854,0,1246,0,1624,0]
def o8 : List ℕ := [1,0,0,0,0,0,0,0,8,0,8,0,8,0,8,0,36,0,56,0,92,0,112,0,204,0,280,0,484,0,672,0,1058,0,1400,0,2100,0,2856,0]
def o9 : List ℕ := [1,0,0,0,0,0,0,0,9,0,9,0,9,0,9,0,45,0,72,0,117,0,144,0,273,0,396,0,693,0,984,0,1575,0,2160,0,3324,0,4680,0]
def o10 : List ℕ := [1,0,0,0,0,0,0,0,10,0,10,0,10,0,10,0,55,0,90,0,145,0,180,0,355,0,540,0,955,0,1380,0,2245,0,3180,0,5010,0,7260,0]
def o11 : List ℕ := [1,0,0,0,0,0,0,0,11,0,11,0,11,0,11,0,66,0,110,0,176,0,220,0,451,0,715,0,1276,0,1870,0,3091,0,4510,0,7260,0,10780,0]
def o12 : List ℕ := [1,0,0,0,0,0,0,0,12,0,12,0,12,0,12,0,78,0,132,0,210,0,264,0,562,0,924,0,1662,0,2464,0,4137,0,6204,0,10186,0,15444,0]
def o13 : List ℕ := [1,0,0,0,0,0,0,0,13,0,13,0,13,0,13,0,91,0,156,0,247,0,312,0,689,0,1170,0,2119,0,3172,0,5408,0,8320,0,13910,0,21476,0]
def o14 : List ℕ := [1,0,0,0,0,0,0,0,14,0,14,0,14,0,14,0,105,0,182,0,287,0,364,0,833,0,1456,0,2653,0,4004,0,6930,0,10920,0,18564,0,29120,0]
def o15 : List ℕ := [1,0,0,0,0,0,0,0,15,0,15,0,15,0,15,0,120,0,210,0,330,0,420,0,995,0,1785,0,3270,0,4970,0,8730,0,14070,0,24290,0,38640,0]
def o16 : List ℕ := [1,0,0,0,0,0,0,0,16,0,16,0,16,0,16,0,136,0,240,0,376,0,480,0,1176,0,2160,0,3976,0,6080,0,10836,0,17840,0,31240,0,50320,0]
def o17 : List ℕ := [1,0,0,0,0,0,0,0,17,0,17,0,17,0,17,0,153,0,272,0,425,0,544,0,1377,0,2584,0,4777,0,7344,0,13277,0,22304,0,39576,0,64464,0]
lemma ostep0 : o1 = rowStep (degrees.erase 7) 39 o0 := by decide
lemma ostep1 : o2 = rowStep (degrees.erase 7) 39 o1 := by decide
lemma ostep2 : o3 = rowStep (degrees.erase 7) 39 o2 := by decide
lemma ostep3 : o4 = rowStep (degrees.erase 7) 39 o3 := by decide
lemma ostep4 : o5 = rowStep (degrees.erase 7) 39 o4 := by decide
lemma ostep5 : o6 = rowStep (degrees.erase 7) 39 o5 := by decide
lemma ostep6 : o7 = rowStep (degrees.erase 7) 39 o6 := by decide
lemma ostep7 : o8 = rowStep (degrees.erase 7) 39 o7 := by decide
lemma ostep8 : o9 = rowStep (degrees.erase 7) 39 o8 := by decide
lemma ostep9 : o10 = rowStep (degrees.erase 7) 39 o9 := by decide
lemma ostep10 : o11 = rowStep (degrees.erase 7) 39 o10 := by decide
lemma ostep11 : o12 = rowStep (degrees.erase 7) 39 o11 := by decide
lemma ostep12 : o13 = rowStep (degrees.erase 7) 39 o12 := by decide
lemma ostep13 : o14 = rowStep (degrees.erase 7) 39 o13 := by decide
lemma ostep14 : o15 = rowStep (degrees.erase 7) 39 o14 := by decide
lemma ostep15 : o16 = rowStep (degrees.erase 7) 39 o15 := by decide
lemma ostep16 : o17 = rowStep (degrees.erase 7) 39 o16 := by decide
def orows : List (List ℕ) := [o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11,o12,o13,o14,o15,o16,o17]
lemma obase : orows[0]?.getD [] = rowBase 39 := by decide
lemma ostep : ∀ N ∈ range 17, orows[N+1]?.getD [] = rowStep ((exponentsExec 7 32).erase 7) 39 (orows[N]?.getD []) := by
  intro N hN
  rw [degrees_eq]
  have hN' : N < 17 := mem_range.mp hN
  interval_cases N
  · exact ostep0
  · exact ostep1
  · exact ostep2
  · exact ostep3
  · exact ostep4
  · exact ostep5
  · exact ostep6
  · exact ostep7
  · exact ostep8
  · exact ostep9
  · exact ostep10
  · exact ostep11
  · exact ostep12
  · exact ostep13
  · exact ostep14
  · exact ostep15
  · exact ostep16
end Erdos708H97.Proofs.Numeric7_32
