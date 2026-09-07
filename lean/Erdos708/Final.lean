import Erdos708.Signed.Cards
import Erdos708.Chain.Cards

/-!
# Erdős 708: the unconditional linear bound, kernel-checked end to end

`Erdos708SparseCore.sparse_core` (Section 14, signed clipped-prefix certificate) supplies the single
hypothesis `Erdos708Chain.sparse_core_hyp` of the reduction chain `Erdos708Chain.linear_bound`
(Sections 5, 7, 13).  The two developments carry verbatim copies of the base definitions
(`AtomSystem`, `S0`, `mean`, `L`, `R`), so the transfer is definitional.
-/

open Finset BigOperators

namespace Erdos708Final

/-- Transport an atom system of the chain development to the Section-14 development. -/
def toCore (A : Erdos708Chain.AtomSystem) : Erdos708SparseCore.AtomSystem :=
  ⟨A.atoms, A.weight, A.prime_of_mem, A.weight_nonneg, A.perPrime_le_one⟩

theorem S0_eq (A : Erdos708Chain.AtomSystem) (n : ℕ) :
    Erdos708SparseCore.S0 (toCore A) n = Erdos708Chain.S0 A n := rfl

theorem mean_eq (A : Erdos708Chain.AtomSystem) :
    Erdos708SparseCore.mean (toCore A) = Erdos708Chain.mean A := rfl

theorem L_eq (A : Erdos708Chain.AtomSystem) (m : ℕ) :
    Erdos708SparseCore.L (toCore A) m = Erdos708Chain.L A m := rfl

theorem R_eq (A : Erdos708Chain.AtomSystem) (x m : ℕ) :
    Erdos708SparseCore.R (toCore A) x m = Erdos708Chain.R A x m := rfl

/-- The Section-14 theorem, in the form the reduction chain assumes. -/
theorem sparse_core_hyp : Erdos708Chain.sparse_core_hyp := by
  intro A m hm hH x
  have h := Erdos708SparseCore.sparse_core (toCore A) m hm (by rw [mean_eq]; exact hH) x
  rw [L_eq, R_eq] at h
  exact h

/-- **Erdős 708, linear bound.** For every `n ≥ 1`, every set `A` of `n` integers `≥ 2` and every
`x`, some at most `81 n` of the integers `x+1, …, x + max A` have product divisible by `∏ A`. -/
theorem g_le_81n :
    ∀ (n : ℕ) (hn : 1 ≤ n), ∀ (A : Finset ℕ) (hA : A.card = n) (h2 : ∀ a ∈ A, 2 ≤ a) (x : ℕ),
      ∃ B ⊆ Finset.Icc (x+1) (x + A.max' (by
        have hp : 0 < A.card := by omega
        exact Finset.card_pos.mp hp)), B.card ≤ 81 * n ∧ (∏ a ∈ A, a) ∣ (∏ b ∈ B, b) :=
  Erdos708Chain.linear_bound sparse_core_hyp

#print axioms g_le_81n

end Erdos708Final
