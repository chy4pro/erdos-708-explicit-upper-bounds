import Erdos708.H97.Proofs.NumericDefs
open Finset BigOperators
namespace Erdos708H97.Proofs.Numeric4_16
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
def degrees : Finset ℕ := {4,5,6,7,8,10,12,14,16}
lemma degrees_eq : exponentsExec 4 16 = degrees := by decide
def f0 : List ℕ := [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def f1 : List ℕ := [1,0,0,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,0,0,0]
def f2 : List ℕ := [1,0,0,0,2,2,2,2,3,2,5,4,7,4,7,4,7,4,6,4,7]
def f3 : List ℕ := [1,0,0,0,3,3,3,3,6,6,12,12,19,15,24,22,33,30,40,36,48]
def f4 : List ℕ := [1,0,0,0,4,4,4,4,10,12,22,24,38,36,58,64,95,100,134,140,185]
def f5 : List ℕ := [1,0,0,0,5,5,5,5,15,20,35,40,65,70,115,140,210,240,330,380,516]
def f6 : List ℕ := [1,0,0,0,6,6,6,6,21,30,51,60,101,120,201,260,396,480,680,840,1176]
def f7 : List ℕ := [1,0,0,0,7,7,7,7,28,42,70,84,147,189,322,434,672,854,1246,1624,2338]
def f8 : List ℕ := [1,0,0,0,8,8,8,8,36,56,92,112,204,280,484,672,1058,1400,2100,2856,4214]
def f9 : List ℕ := [1,0,0,0,9,9,9,9,45,72,117,144,273,396,693,984,1575,2160,3324,4680,7056]
def f10 : List ℕ := [1,0,0,0,10,10,10,10,55,90,145,180,355,540,955,1380,2245,3180,5010,7260,11157]
def f11 : List ℕ := [1,0,0,0,11,11,11,11,66,110,176,220,451,715,1276,1870,3091,4510,7260,10780,16852]
def f12 : List ℕ := [1,0,0,0,12,12,12,12,78,132,210,264,562,924,1662,2464,4137,6204,10186,15444,24519]
def f13 : List ℕ := [1,0,0,0,13,13,13,13,91,156,247,312,689,1170,2119,3172,5408,8320,13910,21476,34580]
def f14 : List ℕ := [1,0,0,0,14,14,14,14,105,182,287,364,833,1456,2653,4004,6930,10920,18564,29120,47502]
def f15 : List ℕ := [1,0,0,0,15,15,15,15,120,210,330,420,995,1785,3270,4970,8730,14070,24290,38640,63798]
lemma fstep0 : f1 = rowStep (degrees) 20 f0 := by decide
lemma fstep1 : f2 = rowStep (degrees) 20 f1 := by decide
lemma fstep2 : f3 = rowStep (degrees) 20 f2 := by decide
lemma fstep3 : f4 = rowStep (degrees) 20 f3 := by decide
lemma fstep4 : f5 = rowStep (degrees) 20 f4 := by decide
lemma fstep5 : f6 = rowStep (degrees) 20 f5 := by decide
lemma fstep6 : f7 = rowStep (degrees) 20 f6 := by decide
lemma fstep7 : f8 = rowStep (degrees) 20 f7 := by decide
lemma fstep8 : f9 = rowStep (degrees) 20 f8 := by decide
lemma fstep9 : f10 = rowStep (degrees) 20 f9 := by decide
lemma fstep10 : f11 = rowStep (degrees) 20 f10 := by decide
lemma fstep11 : f12 = rowStep (degrees) 20 f11 := by decide
lemma fstep12 : f13 = rowStep (degrees) 20 f12 := by decide
lemma fstep13 : f14 = rowStep (degrees) 20 f13 := by decide
lemma fstep14 : f15 = rowStep (degrees) 20 f14 := by decide
def frows : List (List ℕ) := [f0,f1,f2,f3,f4,f5,f6,f7,f8,f9,f10,f11,f12,f13,f14,f15]
lemma fbase : frows[0]?.getD [] = rowBase 20 := by decide
lemma fstep : ∀ N ∈ range 15, frows[N+1]?.getD [] = rowStep (exponentsExec 4 16) 20 (frows[N]?.getD []) := by
  intro N hN
  rw [degrees_eq]
  have hN' : N < 15 := mem_range.mp hN
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
def o0 : List ℕ := [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def o1 : List ℕ := [1,0,0,0,0,1,1,1,1,0,1,0,1,0,1,0,1,0,0,0,0]
def o2 : List ℕ := [1,0,0,0,0,2,2,2,2,0,3,2,5,4,5,4,5,4,4,4,5]
def o3 : List ℕ := [1,0,0,0,0,3,3,3,3,0,6,6,12,12,12,13,15,18,22,24,30]
def o4 : List ℕ := [1,0,0,0,0,4,4,4,4,0,10,12,22,24,22,28,34,48,64,72,91]
def o5 : List ℕ := [1,0,0,0,0,5,5,5,5,0,15,20,35,40,35,50,65,100,140,160,205]
def o6 : List ℕ := [1,0,0,0,0,6,6,6,6,0,21,30,51,60,51,80,111,180,260,300,390]
def o7 : List ℕ := [1,0,0,0,0,7,7,7,7,0,28,42,70,84,70,119,175,294,434,504,665]
def o8 : List ℕ := [1,0,0,0,0,8,8,8,8,0,36,56,92,112,92,168,260,448,672,784,1050]
def o9 : List ℕ := [1,0,0,0,0,9,9,9,9,0,45,72,117,144,117,228,369,648,984,1152,1566]
def o10 : List ℕ := [1,0,0,0,0,10,10,10,10,0,55,90,145,180,145,300,505,900,1380,1620,2235]
def o11 : List ℕ := [1,0,0,0,0,11,11,11,11,0,66,110,176,220,176,385,671,1210,1870,2200,3080]
def o12 : List ℕ := [1,0,0,0,0,12,12,12,12,0,78,132,210,264,210,484,870,1584,2464,2904,4125]
def o13 : List ℕ := [1,0,0,0,0,13,13,13,13,0,91,156,247,312,247,598,1105,2028,3172,3744,5395]
def o14 : List ℕ := [1,0,0,0,0,14,14,14,14,0,105,182,287,364,287,728,1379,2548,4004,4732,6916]
def o15 : List ℕ := [1,0,0,0,0,15,15,15,15,0,120,210,330,420,330,875,1695,3150,4970,5880,8715]
lemma ostep0 : o1 = rowStep (degrees.erase 4) 20 o0 := by decide
lemma ostep1 : o2 = rowStep (degrees.erase 4) 20 o1 := by decide
lemma ostep2 : o3 = rowStep (degrees.erase 4) 20 o2 := by decide
lemma ostep3 : o4 = rowStep (degrees.erase 4) 20 o3 := by decide
lemma ostep4 : o5 = rowStep (degrees.erase 4) 20 o4 := by decide
lemma ostep5 : o6 = rowStep (degrees.erase 4) 20 o5 := by decide
lemma ostep6 : o7 = rowStep (degrees.erase 4) 20 o6 := by decide
lemma ostep7 : o8 = rowStep (degrees.erase 4) 20 o7 := by decide
lemma ostep8 : o9 = rowStep (degrees.erase 4) 20 o8 := by decide
lemma ostep9 : o10 = rowStep (degrees.erase 4) 20 o9 := by decide
lemma ostep10 : o11 = rowStep (degrees.erase 4) 20 o10 := by decide
lemma ostep11 : o12 = rowStep (degrees.erase 4) 20 o11 := by decide
lemma ostep12 : o13 = rowStep (degrees.erase 4) 20 o12 := by decide
lemma ostep13 : o14 = rowStep (degrees.erase 4) 20 o13 := by decide
lemma ostep14 : o15 = rowStep (degrees.erase 4) 20 o14 := by decide
def orows : List (List ℕ) := [o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11,o12,o13,o14,o15]
lemma obase : orows[0]?.getD [] = rowBase 20 := by decide
lemma ostep : ∀ N ∈ range 15, orows[N+1]?.getD [] = rowStep ((exponentsExec 4 16).erase 4) 20 (orows[N]?.getD []) := by
  intro N hN
  rw [degrees_eq]
  have hN' : N < 15 := mem_range.mp hN
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
end Erdos708H97.Proofs.Numeric4_16
