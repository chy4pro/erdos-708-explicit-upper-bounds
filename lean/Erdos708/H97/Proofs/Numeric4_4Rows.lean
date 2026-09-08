import Erdos708.H97.Proofs.NumericDefs
open Finset BigOperators
namespace Erdos708H97.Proofs.Numeric4_4
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
def degrees : Finset ℕ := {4}
lemma degrees_eq : exponentsExec 4 4 = degrees := by decide
def f0 : List ℕ := [1,0,0,0,0,0,0,0,0]
def f1 : List ℕ := [1,0,0,0,1,0,0,0,0]
def f2 : List ℕ := [1,0,0,0,2,0,0,0,1]
def f3 : List ℕ := [1,0,0,0,3,0,0,0,3]
def f4 : List ℕ := [1,0,0,0,4,0,0,0,6]
lemma fstep0 : f1 = rowStep (degrees) 8 f0 := by decide
lemma fstep1 : f2 = rowStep (degrees) 8 f1 := by decide
lemma fstep2 : f3 = rowStep (degrees) 8 f2 := by decide
lemma fstep3 : f4 = rowStep (degrees) 8 f3 := by decide
def frows : List (List ℕ) := [f0,f1,f2,f3,f4]
lemma fbase : frows[0]?.getD [] = rowBase 8 := by decide
lemma fstep : ∀ N ∈ range 4, frows[N+1]?.getD [] = rowStep (exponentsExec 4 4) 8 (frows[N]?.getD []) := by
  intro N hN
  rw [degrees_eq]
  have hN' : N < 4 := mem_range.mp hN
  interval_cases N
  · exact fstep0
  · exact fstep1
  · exact fstep2
  · exact fstep3
def o0 : List ℕ := [1,0,0,0,0,0,0,0,0]
def o1 : List ℕ := [1,0,0,0,0,0,0,0,0]
def o2 : List ℕ := [1,0,0,0,0,0,0,0,0]
def o3 : List ℕ := [1,0,0,0,0,0,0,0,0]
def o4 : List ℕ := [1,0,0,0,0,0,0,0,0]
lemma ostep0 : o1 = rowStep (degrees.erase 4) 8 o0 := by decide
lemma ostep1 : o2 = rowStep (degrees.erase 4) 8 o1 := by decide
lemma ostep2 : o3 = rowStep (degrees.erase 4) 8 o2 := by decide
lemma ostep3 : o4 = rowStep (degrees.erase 4) 8 o3 := by decide
def orows : List (List ℕ) := [o0,o1,o2,o3,o4]
lemma obase : orows[0]?.getD [] = rowBase 8 := by decide
lemma ostep : ∀ N ∈ range 4, orows[N+1]?.getD [] = rowStep ((exponentsExec 4 4).erase 4) 8 (orows[N]?.getD []) := by
  intro N hN
  rw [degrees_eq]
  have hN' : N < 4 := mem_range.mp hN
  interval_cases N
  · exact ostep0
  · exact ostep1
  · exact ostep2
  · exact ostep3
end Erdos708H97.Proofs.Numeric4_4
