import Erdos708.H97.Proofs.NumericDefs
open Finset BigOperators
namespace Erdos708H97.Proofs.Numeric4_8
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
def degrees : Finset ℕ := {4,5,6,7,8}
lemma degrees_eq : exponentsExec 4 8 = degrees := by decide
def f0 : List ℕ := [1,0,0,0,0,0,0,0,0,0,0,0,0]
def f1 : List ℕ := [1,0,0,0,1,1,1,1,1,0,0,0,0]
def f2 : List ℕ := [1,0,0,0,2,2,2,2,3,2,3,4,5]
def f3 : List ℕ := [1,0,0,0,3,3,3,3,6,6,9,12,16]
def f4 : List ℕ := [1,0,0,0,4,4,4,4,10,12,18,24,34]
def f5 : List ℕ := [1,0,0,0,5,5,5,5,15,20,30,40,60]
def f6 : List ℕ := [1,0,0,0,6,6,6,6,21,30,45,60,95]
def f7 : List ℕ := [1,0,0,0,7,7,7,7,28,42,63,84,140]
def f8 : List ℕ := [1,0,0,0,8,8,8,8,36,56,84,112,196]
lemma fstep0 : f1 = rowStep (degrees) 12 f0 := by decide
lemma fstep1 : f2 = rowStep (degrees) 12 f1 := by decide
lemma fstep2 : f3 = rowStep (degrees) 12 f2 := by decide
lemma fstep3 : f4 = rowStep (degrees) 12 f3 := by decide
lemma fstep4 : f5 = rowStep (degrees) 12 f4 := by decide
lemma fstep5 : f6 = rowStep (degrees) 12 f5 := by decide
lemma fstep6 : f7 = rowStep (degrees) 12 f6 := by decide
lemma fstep7 : f8 = rowStep (degrees) 12 f7 := by decide
def frows : List (List ℕ) := [f0,f1,f2,f3,f4,f5,f6,f7,f8]
lemma fbase : frows[0]?.getD [] = rowBase 12 := by decide
lemma fstep : ∀ N ∈ range 8, frows[N+1]?.getD [] = rowStep (exponentsExec 4 8) 12 (frows[N]?.getD []) := by
  intro N hN
  rw [degrees_eq]
  have hN' : N < 8 := mem_range.mp hN
  interval_cases N
  · exact fstep0
  · exact fstep1
  · exact fstep2
  · exact fstep3
  · exact fstep4
  · exact fstep5
  · exact fstep6
  · exact fstep7
def o0 : List ℕ := [1,0,0,0,0,0,0,0,0,0,0,0,0]
def o1 : List ℕ := [1,0,0,0,0,1,1,1,1,0,0,0,0]
def o2 : List ℕ := [1,0,0,0,0,2,2,2,2,0,1,2,3]
def o3 : List ℕ := [1,0,0,0,0,3,3,3,3,0,3,6,9]
def o4 : List ℕ := [1,0,0,0,0,4,4,4,4,0,6,12,18]
def o5 : List ℕ := [1,0,0,0,0,5,5,5,5,0,10,20,30]
def o6 : List ℕ := [1,0,0,0,0,6,6,6,6,0,15,30,45]
def o7 : List ℕ := [1,0,0,0,0,7,7,7,7,0,21,42,63]
def o8 : List ℕ := [1,0,0,0,0,8,8,8,8,0,28,56,84]
lemma ostep0 : o1 = rowStep (degrees.erase 4) 12 o0 := by decide
lemma ostep1 : o2 = rowStep (degrees.erase 4) 12 o1 := by decide
lemma ostep2 : o3 = rowStep (degrees.erase 4) 12 o2 := by decide
lemma ostep3 : o4 = rowStep (degrees.erase 4) 12 o3 := by decide
lemma ostep4 : o5 = rowStep (degrees.erase 4) 12 o4 := by decide
lemma ostep5 : o6 = rowStep (degrees.erase 4) 12 o5 := by decide
lemma ostep6 : o7 = rowStep (degrees.erase 4) 12 o6 := by decide
lemma ostep7 : o8 = rowStep (degrees.erase 4) 12 o7 := by decide
def orows : List (List ℕ) := [o0,o1,o2,o3,o4,o5,o6,o7,o8]
lemma obase : orows[0]?.getD [] = rowBase 12 := by decide
lemma ostep : ∀ N ∈ range 8, orows[N+1]?.getD [] = rowStep ((exponentsExec 4 8).erase 4) 12 (orows[N]?.getD []) := by
  intro N hN
  rw [degrees_eq]
  have hN' : N < 8 := mem_range.mp hN
  interval_cases N
  · exact ostep0
  · exact ostep1
  · exact ostep2
  · exact ostep3
  · exact ostep4
  · exact ostep5
  · exact ostep6
  · exact ostep7
end Erdos708H97.Proofs.Numeric4_8
