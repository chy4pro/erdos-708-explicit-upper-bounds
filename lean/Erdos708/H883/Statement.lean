import Erdos708.Statement
import Erdos708.H17.Defs

/-!
Exact targets for Section 18, "Threshold 56501/6400 and the barrier at 2".

This is a definitions-only statement file awaiting the coordinator's audit.
It asserts no theorem. The shared atom system is the existing H17/H97 one:
finite prime-power support, positive exponents, nonnegative real weights,
and total weight at most one at each prime. No restriction to rational
weights, to sparse systems, or to sufficiently large windows is imposed.

The eventual declarations are `Erdos708H883.hinge883 : Hinge883`,
`Erdos708H883.bound883 : CeilingBound883`, and
`Erdos708H883.g_le_11n : Erdos708Statement.g_le 11`.
Every resulting top-level theorem must receive an exact axiom guard in
`Erdos708/FinalCheck.lean`; this file does not stand in for those proofs.

The optional barrier below threshold 2 is outside these main targets.
-/

open Finset BigOperators

namespace Erdos708H883

export Erdos708H17 (AtomSystem S hingeSum)

/-- Theorem 18.1: every positive-length window of consecutive positive
integers, with the exact rational threshold. The start parameter `x` is
natural, so the window starts at `x + 1 >= 1`. -/
def Hinge883 : Prop :=
  ∀ (A : AtomSystem) (m x : ℕ), 1 ≤ m →
    hingeSum (S A) ((56501 : ℝ) / 6400) 0 m ≤
      hingeSum (S A) 1 x m

/-- The exact intermediate bound from Section 16 at `c = 56501/6400`.
Membership of the maximum ensures `A` is nonempty, hence `A.card >= 1`.
Both the product and the interval use the same conventions as `g_le`.
The ceiling is a natural ceiling of a real quotient; no natural-number
division occurs in its argument. -/
def CeilingBound883 : Prop :=
  ∀ (A : Finset ℕ) (M : ℕ), M ∈ A →
    (∀ a ∈ A, a ≤ M) → (∀ a ∈ A, 2 ≤ a) → ∀ x : ℕ,
      ∃ B ⊆ Finset.Icc (x + 1) (x + M),
        B.card ≤ ⌈((56501 : ℝ) / 6400) * (A.card : ℝ)⌉₊ + 2 * A.card ∧
          (∏ a ∈ A, a) ∣ (∏ b ∈ B, b)

/-- Corollary 18.2: `g(n) <= 11n` for every `n >= 1`, stated by reusing
the existing Mathlib-only reference proposition without changing it. -/
def Bound11 : Prop := Erdos708Statement.g_le 11

end Erdos708H883
