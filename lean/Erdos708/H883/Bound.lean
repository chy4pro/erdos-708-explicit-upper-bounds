import Erdos708.H883.Statement
import Erdos708.H97.Chain

/-!
Section 18, the reduction steps (no hinge proof here):

* `bound883_of_hinge : Hinge883 → CeilingBound883` is Theorem 16.1 (`bound_of_hinge`) at
  `c = 56501/6400`, through the threshold-generic weight transfer of Section 17.
* `g_le_11n_of_bound : CeilingBound883 → Bound11` is Corollary 18.2's arithmetic,
  `⌈(56501/6400) n⌉ + 2n ≤ 9n + 2n`.

`Statement.lean` is frozen (audited, AUT-137).
-/

open Finset BigOperators

namespace Erdos708H883

/-- The atom-system hinge at `56501/6400` gives the weighted hinge used by `bound_of_hinge`. -/
lemma weighted_hinge883 (hh : Hinge883) :
    ∀ (z : Erdos708H17Chain.Weight) (m : ℕ), 1 ≤ m → ∀ x : ℕ,
      Erdos708H17Chain.hingeSum (Erdos708H17Chain.w z) ((56501 : ℝ) / 6400) 0 m ≤
      Erdos708H17Chain.hingeSum (Erdos708H17Chain.w z) 1 x m := by
  intro z m hm x
  apply Erdos708H97.Proofs.capped_to_weight
  apply Erdos708H97.Proofs.atoms_to_capped
  have ha := hh (Erdos708H17.toCore (Erdos708H17Chain.Proofs.ofWeight z m)) m x hm
  simpa only [hingeSum, Erdos708H17.toCore_value, Erdos708H17Chain.hingeSum] using ha

/-- Theorem 16.1 at `c = 56501/6400`. -/
theorem bound883_of_hinge (hh : Hinge883) : CeilingBound883 := by
  intro A M hM hub h2 x
  have hne : A.Nonempty := ⟨M, hM⟩
  let D : Erdos708H17Chain.Problem := ⟨A, hne, h2, x⟩
  obtain ⟨B, hB, hcard⟩ := Erdos708H17Chain.Chain19.bound_of_hinge ((56501 : ℝ) / 6400)
    (by norm_num) (weighted_hinge883 hh) D
  have hmax : A.max' hne = M :=
    le_antisymm (Finset.max'_le _ _ _ hub) (Finset.le_max' _ _ hM)
  have hsub : B ⊆ Finset.Icc (x + 1) (x + A.max' hne) := hB.1
  have hdvd : (∏ a ∈ A, a) ∣ ∏ b ∈ B, b := hB.2
  have hcard' : B.card ≤ ⌈((56501 : ℝ) / 6400) * (A.card : ℝ)⌉₊ + 2 * A.card := hcard
  rw [hmax] at hsub
  exact ⟨B, hsub, hcard', hdvd⟩

/-- Corollary 18.2's arithmetic: `⌈(56501/6400) n⌉ + 2n ≤ 11n`. -/
theorem g_le_11n_of_bound (hb : CeilingBound883) : Bound11 := by
  intro A M hM hub h2 x
  obtain ⟨B, hBsub, hBcard, hdvd⟩ := hb A M hM hub h2 x
  refine ⟨B, hBsub, ?_, hdvd⟩
  have hceil : ⌈((56501 : ℝ) / 6400) * (A.card : ℝ)⌉₊ ≤ 9 * A.card := by
    apply Nat.ceil_le.mpr
    push_cast
    nlinarith [Nat.cast_nonneg A.card (α := ℝ)]
  omega

/-- The conditional headline: the Section 18 hinge inequality implies `g(n) ≤ 11n`. -/
theorem g_le_11n_of_hinge (hh : Hinge883) : Bound11 :=
  g_le_11n_of_bound (bound883_of_hinge hh)

end Erdos708H883
