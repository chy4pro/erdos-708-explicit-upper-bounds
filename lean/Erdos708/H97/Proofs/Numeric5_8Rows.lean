import Erdos708.H97.Proofs.NumericDefs
open Finset BigOperators
namespace Erdos708H97.Proofs.Numeric5_8
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
def degrees : Finset ℕ := {5,6,7,8}
lemma degrees_eq : exponentsExec 5 8 = degrees := by decide
def f0 : List ℕ := [1,0,0,0,0,0,0,0,0,0,0,0,0,0]
def f1 : List ℕ := [1,0,0,0,0,1,1,1,1,0,0,0,0,0]
def f2 : List ℕ := [1,0,0,0,0,2,2,2,2,0,1,2,3,4]
def f3 : List ℕ := [1,0,0,0,0,3,3,3,3,0,3,6,9,12]
def f4 : List ℕ := [1,0,0,0,0,4,4,4,4,0,6,12,18,24]
def f5 : List ℕ := [1,0,0,0,0,5,5,5,5,0,10,20,30,40]
def f6 : List ℕ := [1,0,0,0,0,6,6,6,6,0,15,30,45,60]
lemma fstep0 : f1 = rowStep (degrees) 13 f0 := by decide
lemma fstep1 : f2 = rowStep (degrees) 13 f1 := by decide
lemma fstep2 : f3 = rowStep (degrees) 13 f2 := by decide
lemma fstep3 : f4 = rowStep (degrees) 13 f3 := by decide
lemma fstep4 : f5 = rowStep (degrees) 13 f4 := by decide
lemma fstep5 : f6 = rowStep (degrees) 13 f5 := by decide
def frows : List (List ℕ) := [f0,f1,f2,f3,f4,f5,f6]
lemma fbase : frows[0]?.getD [] = rowBase 13 := by decide
lemma fstep : ∀ N ∈ range 6, frows[N+1]?.getD [] = rowStep (exponentsExec 5 8) 13 (frows[N]?.getD []) := by
  intro N hN
  rw [degrees_eq]
  have hN' : N < 6 := mem_range.mp hN
  interval_cases N
  · exact fstep0
  · exact fstep1
  · exact fstep2
  · exact fstep3
  · exact fstep4
  · exact fstep5
def o0 : List ℕ := [1,0,0,0,0,0,0,0,0,0,0,0,0,0]
def o1 : List ℕ := [1,0,0,0,0,0,1,1,1,0,0,0,0,0]
def o2 : List ℕ := [1,0,0,0,0,0,2,2,2,0,0,0,1,2]
def o3 : List ℕ := [1,0,0,0,0,0,3,3,3,0,0,0,3,6]
def o4 : List ℕ := [1,0,0,0,0,0,4,4,4,0,0,0,6,12]
def o5 : List ℕ := [1,0,0,0,0,0,5,5,5,0,0,0,10,20]
def o6 : List ℕ := [1,0,0,0,0,0,6,6,6,0,0,0,15,30]
lemma ostep0 : o1 = rowStep (degrees.erase 5) 13 o0 := by decide
lemma ostep1 : o2 = rowStep (degrees.erase 5) 13 o1 := by decide
lemma ostep2 : o3 = rowStep (degrees.erase 5) 13 o2 := by decide
lemma ostep3 : o4 = rowStep (degrees.erase 5) 13 o3 := by decide
lemma ostep4 : o5 = rowStep (degrees.erase 5) 13 o4 := by decide
lemma ostep5 : o6 = rowStep (degrees.erase 5) 13 o5 := by decide
def orows : List (List ℕ) := [o0,o1,o2,o3,o4,o5,o6]
lemma obase : orows[0]?.getD [] = rowBase 13 := by decide
lemma ostep : ∀ N ∈ range 6, orows[N+1]?.getD [] = rowStep ((exponentsExec 5 8).erase 5) 13 (orows[N]?.getD []) := by
  intro N hN
  rw [degrees_eq]
  have hN' : N < 6 := mem_range.mp hN
  interval_cases N
  · exact ostep0
  · exact ostep1
  · exact ostep2
  · exact ostep3
  · exact ostep4
  · exact ostep5
end Erdos708H97.Proofs.Numeric5_8
