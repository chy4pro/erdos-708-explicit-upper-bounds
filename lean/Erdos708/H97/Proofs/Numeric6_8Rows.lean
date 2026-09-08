import Erdos708.H97.Proofs.NumericDefs
open Finset BigOperators
namespace Erdos708H97.Proofs.Numeric6_8
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
def degrees : Finset ℕ := {6,7,8}
lemma degrees_eq : exponentsExec 6 8 = degrees := by decide
def f0 : List ℕ := [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def f1 : List ℕ := [1,0,0,0,0,0,1,1,1,0,0,0,0,0,0]
def f2 : List ℕ := [1,0,0,0,0,0,2,2,2,0,0,0,1,2,3]
def f3 : List ℕ := [1,0,0,0,0,0,3,3,3,0,0,0,3,6,9]
def f4 : List ℕ := [1,0,0,0,0,0,4,4,4,0,0,0,6,12,18]
def f5 : List ℕ := [1,0,0,0,0,0,5,5,5,0,0,0,10,20,30]
lemma fstep0 : f1 = rowStep (degrees) 14 f0 := by decide
lemma fstep1 : f2 = rowStep (degrees) 14 f1 := by decide
lemma fstep2 : f3 = rowStep (degrees) 14 f2 := by decide
lemma fstep3 : f4 = rowStep (degrees) 14 f3 := by decide
lemma fstep4 : f5 = rowStep (degrees) 14 f4 := by decide
def frows : List (List ℕ) := [f0,f1,f2,f3,f4,f5]
lemma fbase : frows[0]?.getD [] = rowBase 14 := by decide
lemma fstep : ∀ N ∈ range 5, frows[N+1]?.getD [] = rowStep (exponentsExec 6 8) 14 (frows[N]?.getD []) := by
  intro N hN
  rw [degrees_eq]
  have hN' : N < 5 := mem_range.mp hN
  interval_cases N
  · exact fstep0
  · exact fstep1
  · exact fstep2
  · exact fstep3
  · exact fstep4
def o0 : List ℕ := [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def o1 : List ℕ := [1,0,0,0,0,0,0,1,1,0,0,0,0,0,0]
def o2 : List ℕ := [1,0,0,0,0,0,0,2,2,0,0,0,0,0,1]
def o3 : List ℕ := [1,0,0,0,0,0,0,3,3,0,0,0,0,0,3]
def o4 : List ℕ := [1,0,0,0,0,0,0,4,4,0,0,0,0,0,6]
def o5 : List ℕ := [1,0,0,0,0,0,0,5,5,0,0,0,0,0,10]
lemma ostep0 : o1 = rowStep (degrees.erase 6) 14 o0 := by decide
lemma ostep1 : o2 = rowStep (degrees.erase 6) 14 o1 := by decide
lemma ostep2 : o3 = rowStep (degrees.erase 6) 14 o2 := by decide
lemma ostep3 : o4 = rowStep (degrees.erase 6) 14 o3 := by decide
lemma ostep4 : o5 = rowStep (degrees.erase 6) 14 o4 := by decide
def orows : List (List ℕ) := [o0,o1,o2,o3,o4,o5]
lemma obase : orows[0]?.getD [] = rowBase 14 := by decide
lemma ostep : ∀ N ∈ range 5, orows[N+1]?.getD [] = rowStep ((exponentsExec 6 8).erase 6) 14 (orows[N]?.getD []) := by
  intro N hN
  rw [degrees_eq]
  have hN' : N < 5 := mem_range.mp hN
  interval_cases N
  · exact ostep0
  · exact ostep1
  · exact ostep2
  · exact ostep3
  · exact ostep4
end Erdos708H97.Proofs.Numeric6_8
