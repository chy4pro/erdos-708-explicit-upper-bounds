/-
Reference statement for Erdős problem 708, phrased using ONLY Mathlib notions.

This file imports Mathlib and nothing else. It is the statement a sceptic should read: no definition
from this project appears in it. `Erdos708/FinalCheck.lean` proves `g_le 12` (and the weaker
constants) from the project's theorems and freezes the resulting axiom set, which is the local
analogue of the Lean FRO comparator step in the Fermat's Last Theorem verification stack.

`g_le c` says: for every finite set A of integers ≥ 2 with maximum M, and every x, some at most
c * |A| of the integers x+1, …, x+M have product divisible by the product of A.
-/
import Mathlib

namespace Erdos708Statement

def g_le (c : ℕ) : Prop :=
  ∀ (A : Finset ℕ) (M : ℕ), M ∈ A → (∀ a ∈ A, a ≤ M) → (∀ a ∈ A, 2 ≤ a) → ∀ x : ℕ,
    ∃ B ⊆ Finset.Icc (x + 1) (x + M),
      B.card ≤ c * A.card ∧ (∏ a ∈ A, a) ∣ (∏ b ∈ B, b)

end Erdos708Statement
