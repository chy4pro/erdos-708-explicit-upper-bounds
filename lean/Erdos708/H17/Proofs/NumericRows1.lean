import Erdos708.H17.Proofs.NumericDefs
open Finset BigOperators
namespace Erdos708H17.Proofs
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024

def rows1 : List (List ℕ) := [
[1,0,0,0],
[1,1,1,0],
[1,2,3,2],
[1,3,6,7],
[1,4,10,16],
[1,5,15,30],
[1,6,21,50],
[1,7,28,77]
]

theorem rows1_valid :
    rows1[0]?.getD [] = rowBase 1 ∧
      ∀ N ∈ range (countLimit 1), rows1[N+1]?.getD [] = rowStep 1 (rows1[N]?.getD []) := by decide
#print axioms rows1_valid
end Erdos708H17.Proofs
