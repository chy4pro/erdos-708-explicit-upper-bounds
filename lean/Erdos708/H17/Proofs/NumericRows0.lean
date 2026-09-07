import Erdos708.H17.Proofs.NumericDefs
open Finset BigOperators
namespace Erdos708H17.Proofs
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024

def rows0 : List (List ℕ) := [
[1,0,0],
[1,1,0],
[1,2,1],
[1,3,3],
[1,4,6]
]

theorem rows0_valid :
    rows0[0]?.getD [] = rowBase 0 ∧
      ∀ N ∈ range (countLimit 0), rows0[N+1]?.getD [] = rowStep 0 (rows0[N]?.getD []) := by decide
#print axioms rows0_valid
end Erdos708H17.Proofs
