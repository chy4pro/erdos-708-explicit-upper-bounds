import Erdos708.H97.Proofs.NumericDefs
open Finset BigOperators
namespace Erdos708H97.Proofs.Numeric5_16
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
def degrees : Finset ℕ := {5,6,7,8,10,12,14,16}
lemma degrees_eq : exponentsExec 5 16 = degrees := by decide
def f0 : List ℕ := [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def f1 : List ℕ := [1,0,0,0,0,1,1,1,1,0,1,0,1,0,1,0,1,0,0,0,0,0]
def f2 : List ℕ := [1,0,0,0,0,2,2,2,2,0,3,2,5,4,5,4,5,4,4,4,5,4]
def f3 : List ℕ := [1,0,0,0,0,3,3,3,3,0,6,6,12,12,12,13,15,18,22,24,30,28]
def f4 : List ℕ := [1,0,0,0,0,4,4,4,4,0,10,12,22,24,22,28,34,48,64,72,91,92]
def f5 : List ℕ := [1,0,0,0,0,5,5,5,5,0,15,20,35,40,35,50,65,100,140,160,205,220]
def f6 : List ℕ := [1,0,0,0,0,6,6,6,6,0,21,30,51,60,51,80,111,180,260,300,390,440]
def f7 : List ℕ := [1,0,0,0,0,7,7,7,7,0,28,42,70,84,70,119,175,294,434,504,665,784]
def f8 : List ℕ := [1,0,0,0,0,8,8,8,8,0,36,56,92,112,92,168,260,448,672,784,1050,1288]
def f9 : List ℕ := [1,0,0,0,0,9,9,9,9,0,45,72,117,144,117,228,369,648,984,1152,1566,1992]
def f10 : List ℕ := [1,0,0,0,0,10,10,10,10,0,55,90,145,180,145,300,505,900,1380,1620,2235,2940]
def f11 : List ℕ := [1,0,0,0,0,11,11,11,11,0,66,110,176,220,176,385,671,1210,1870,2200,3080,4180]
def f12 : List ℕ := [1,0,0,0,0,12,12,12,12,0,78,132,210,264,210,484,870,1584,2464,2904,4125,5764]
lemma fstep0 : f1 = rowStep (degrees) 21 f0 := by decide
lemma fstep1 : f2 = rowStep (degrees) 21 f1 := by decide
lemma fstep2 : f3 = rowStep (degrees) 21 f2 := by decide
lemma fstep3 : f4 = rowStep (degrees) 21 f3 := by decide
lemma fstep4 : f5 = rowStep (degrees) 21 f4 := by decide
lemma fstep5 : f6 = rowStep (degrees) 21 f5 := by decide
lemma fstep6 : f7 = rowStep (degrees) 21 f6 := by decide
lemma fstep7 : f8 = rowStep (degrees) 21 f7 := by decide
lemma fstep8 : f9 = rowStep (degrees) 21 f8 := by decide
lemma fstep9 : f10 = rowStep (degrees) 21 f9 := by decide
lemma fstep10 : f11 = rowStep (degrees) 21 f10 := by decide
lemma fstep11 : f12 = rowStep (degrees) 21 f11 := by decide
def frows : List (List ℕ) := [f0,f1,f2,f3,f4,f5,f6,f7,f8,f9,f10,f11,f12]
lemma fbase : frows[0]?.getD [] = rowBase 21 := by decide
lemma fstep : ∀ N ∈ range 12, frows[N+1]?.getD [] = rowStep (exponentsExec 5 16) 21 (frows[N]?.getD []) := by
  intro N hN
  rw [degrees_eq]
  have hN' : N < 12 := mem_range.mp hN
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
def o0 : List ℕ := [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def o1 : List ℕ := [1,0,0,0,0,0,1,1,1,0,1,0,1,0,1,0,1,0,0,0,0,0]
def o2 : List ℕ := [1,0,0,0,0,0,2,2,2,0,2,0,3,2,5,2,5,2,4,2,5,2]
def o3 : List ℕ := [1,0,0,0,0,0,3,3,3,0,3,0,6,6,12,6,12,6,13,9,21,13]
def o4 : List ℕ := [1,0,0,0,0,0,4,4,4,0,4,0,10,12,22,12,22,12,28,24,54,40]
def o5 : List ℕ := [1,0,0,0,0,0,5,5,5,0,5,0,15,20,35,20,35,20,50,50,110,90]
def o6 : List ℕ := [1,0,0,0,0,0,6,6,6,0,6,0,21,30,51,30,51,30,80,90,195,170]
def o7 : List ℕ := [1,0,0,0,0,0,7,7,7,0,7,0,28,42,70,42,70,42,119,147,315,287]
def o8 : List ℕ := [1,0,0,0,0,0,8,8,8,0,8,0,36,56,92,56,92,56,168,224,476,448]
def o9 : List ℕ := [1,0,0,0,0,0,9,9,9,0,9,0,45,72,117,72,117,72,228,324,684,660]
def o10 : List ℕ := [1,0,0,0,0,0,10,10,10,0,10,0,55,90,145,90,145,90,300,450,945,930]
def o11 : List ℕ := [1,0,0,0,0,0,11,11,11,0,11,0,66,110,176,110,176,110,385,605,1265,1265]
def o12 : List ℕ := [1,0,0,0,0,0,12,12,12,0,12,0,78,132,210,132,210,132,484,792,1650,1672]
lemma ostep0 : o1 = rowStep (degrees.erase 5) 21 o0 := by decide
lemma ostep1 : o2 = rowStep (degrees.erase 5) 21 o1 := by decide
lemma ostep2 : o3 = rowStep (degrees.erase 5) 21 o2 := by decide
lemma ostep3 : o4 = rowStep (degrees.erase 5) 21 o3 := by decide
lemma ostep4 : o5 = rowStep (degrees.erase 5) 21 o4 := by decide
lemma ostep5 : o6 = rowStep (degrees.erase 5) 21 o5 := by decide
lemma ostep6 : o7 = rowStep (degrees.erase 5) 21 o6 := by decide
lemma ostep7 : o8 = rowStep (degrees.erase 5) 21 o7 := by decide
lemma ostep8 : o9 = rowStep (degrees.erase 5) 21 o8 := by decide
lemma ostep9 : o10 = rowStep (degrees.erase 5) 21 o9 := by decide
lemma ostep10 : o11 = rowStep (degrees.erase 5) 21 o10 := by decide
lemma ostep11 : o12 = rowStep (degrees.erase 5) 21 o11 := by decide
def orows : List (List ℕ) := [o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11,o12]
lemma obase : orows[0]?.getD [] = rowBase 21 := by decide
lemma ostep : ∀ N ∈ range 12, orows[N+1]?.getD [] = rowStep ((exponentsExec 5 16).erase 5) 21 (orows[N]?.getD []) := by
  intro N hN
  rw [degrees_eq]
  have hN' : N < 12 := mem_range.mp hN
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
end Erdos708H97.Proofs.Numeric5_16
