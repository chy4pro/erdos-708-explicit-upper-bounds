import Erdos708.H97.Proofs.NumericDefs
open Finset BigOperators
namespace Erdos708H97.Proofs.Numeric6_16
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
def degrees : Finset ℕ := {6,7,8,10,12,14,16}
lemma degrees_eq : exponentsExec 6 16 = degrees := by decide
def f0 : List ℕ := [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def f1 : List ℕ := [1,0,0,0,0,0,1,1,1,0,1,0,1,0,1,0,1,0,0,0,0,0,0]
def f2 : List ℕ := [1,0,0,0,0,0,2,2,2,0,2,0,3,2,5,2,5,2,4,2,5,2,6]
def f3 : List ℕ := [1,0,0,0,0,0,3,3,3,0,3,0,6,6,12,6,12,6,13,9,21,13,27]
def f4 : List ℕ := [1,0,0,0,0,0,4,4,4,0,4,0,10,12,22,12,22,12,28,24,54,40,72]
def f5 : List ℕ := [1,0,0,0,0,0,5,5,5,0,5,0,15,20,35,20,35,20,50,50,110,90,150]
def f6 : List ℕ := [1,0,0,0,0,0,6,6,6,0,6,0,21,30,51,30,51,30,80,90,195,170,270]
def f7 : List ℕ := [1,0,0,0,0,0,7,7,7,0,7,0,28,42,70,42,70,42,119,147,315,287,441]
def f8 : List ℕ := [1,0,0,0,0,0,8,8,8,0,8,0,36,56,92,56,92,56,168,224,476,448,672]
def f9 : List ℕ := [1,0,0,0,0,0,9,9,9,0,9,0,45,72,117,72,117,72,228,324,684,660,972]
def f10 : List ℕ := [1,0,0,0,0,0,10,10,10,0,10,0,55,90,145,90,145,90,300,450,945,930,1350]
lemma fstep0 : f1 = rowStep (degrees) 22 f0 := by decide
lemma fstep1 : f2 = rowStep (degrees) 22 f1 := by decide
lemma fstep2 : f3 = rowStep (degrees) 22 f2 := by decide
lemma fstep3 : f4 = rowStep (degrees) 22 f3 := by decide
lemma fstep4 : f5 = rowStep (degrees) 22 f4 := by decide
lemma fstep5 : f6 = rowStep (degrees) 22 f5 := by decide
lemma fstep6 : f7 = rowStep (degrees) 22 f6 := by decide
lemma fstep7 : f8 = rowStep (degrees) 22 f7 := by decide
lemma fstep8 : f9 = rowStep (degrees) 22 f8 := by decide
lemma fstep9 : f10 = rowStep (degrees) 22 f9 := by decide
def frows : List (List ℕ) := [f0,f1,f2,f3,f4,f5,f6,f7,f8,f9,f10]
lemma fbase : frows[0]?.getD [] = rowBase 22 := by decide
lemma fstep : ∀ N ∈ range 10, frows[N+1]?.getD [] = rowStep (exponentsExec 6 16) 22 (frows[N]?.getD []) := by
  intro N hN
  rw [degrees_eq]
  have hN' : N < 10 := mem_range.mp hN
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
def o0 : List ℕ := [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def o1 : List ℕ := [1,0,0,0,0,0,0,1,1,0,1,0,1,0,1,0,1,0,0,0,0,0,0]
def o2 : List ℕ := [1,0,0,0,0,0,0,2,2,0,2,0,2,0,3,2,3,2,2,2,3,2,4]
def o3 : List ℕ := [1,0,0,0,0,0,0,3,3,0,3,0,3,0,6,6,6,6,6,6,9,7,15]
def o4 : List ℕ := [1,0,0,0,0,0,0,4,4,0,4,0,4,0,10,12,10,12,12,12,18,16,36]
def o5 : List ℕ := [1,0,0,0,0,0,0,5,5,0,5,0,5,0,15,20,15,20,20,20,30,30,70]
def o6 : List ℕ := [1,0,0,0,0,0,0,6,6,0,6,0,6,0,21,30,21,30,30,30,45,50,120]
def o7 : List ℕ := [1,0,0,0,0,0,0,7,7,0,7,0,7,0,28,42,28,42,42,42,63,77,189]
def o8 : List ℕ := [1,0,0,0,0,0,0,8,8,0,8,0,8,0,36,56,36,56,56,56,84,112,280]
def o9 : List ℕ := [1,0,0,0,0,0,0,9,9,0,9,0,9,0,45,72,45,72,72,72,108,156,396]
def o10 : List ℕ := [1,0,0,0,0,0,0,10,10,0,10,0,10,0,55,90,55,90,90,90,135,210,540]
lemma ostep0 : o1 = rowStep (degrees.erase 6) 22 o0 := by decide
lemma ostep1 : o2 = rowStep (degrees.erase 6) 22 o1 := by decide
lemma ostep2 : o3 = rowStep (degrees.erase 6) 22 o2 := by decide
lemma ostep3 : o4 = rowStep (degrees.erase 6) 22 o3 := by decide
lemma ostep4 : o5 = rowStep (degrees.erase 6) 22 o4 := by decide
lemma ostep5 : o6 = rowStep (degrees.erase 6) 22 o5 := by decide
lemma ostep6 : o7 = rowStep (degrees.erase 6) 22 o6 := by decide
lemma ostep7 : o8 = rowStep (degrees.erase 6) 22 o7 := by decide
lemma ostep8 : o9 = rowStep (degrees.erase 6) 22 o8 := by decide
lemma ostep9 : o10 = rowStep (degrees.erase 6) 22 o9 := by decide
def orows : List (List ℕ) := [o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10]
lemma obase : orows[0]?.getD [] = rowBase 22 := by decide
lemma ostep : ∀ N ∈ range 10, orows[N+1]?.getD [] = rowStep ((exponentsExec 6 16).erase 6) 22 (orows[N]?.getD []) := by
  intro N hN
  rw [degrees_eq]
  have hN' : N < 10 := mem_range.mp hN
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
end Erdos708H97.Proofs.Numeric6_16
