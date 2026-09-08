import Erdos708.H17.Chain19.Packing

open Finset BigOperators
namespace Erdos708H17Chain.Chain19
open Erdos708H17Chain.Proofs

/-- Three demands per element suffice when the window length is at least `9 n²`. -/
theorem ksplit3 (D : Problem) (hm : 9 * D.n ^ 2 ≤ D.m) :
    ∃ B : Finset ℕ, Covers D B ∧ B.card ≤ 3 * D.n := by
  classical
  have hn : 0 < D.n := card_pos.mpr D.nonempty
  let H := 3 * D.n
  have hH : 1 ≤ H := by dsimp [H]; omega
  have hmH : H ^ 2 ≤ D.m := by dsimp [H]; nlinarith
  have hs (a : D.A) := split_integer3 a.val H D.m
    (by have := D.two_le a.val a.property; omega) (le_max' _ _ a.property) hH hmH
  choose d e t hmul he ht hcase using hs
  have hpos (a : D.A) : 0 < d a ∧ 0 < e a ∧ 0 < t a := by
    have ha := D.two_le a.val a.property
    have hh := hmul a
    have hprod : 0 < d a * e a * t a := hh ▸ (by omega : 0 < a.val)
    have hde := Nat.pos_of_mul_pos_right hprod
    exact ⟨Nat.pos_of_mul_pos_right hde, Nat.pos_of_mul_pos_left hde,
      Nat.pos_of_mul_pos_left hprod⟩
  have hpick (a : D.A) : ∃ p : ℕ, p.Prime ∧ (d a * H ≤ D.m ∨ d a = p ^ a.val.factorization p) := by
    rcases hcase a with h | ⟨p, hp, hq⟩
    · exact ⟨2, Nat.prime_two, Or.inl h⟩
    · exact ⟨p, hp, Or.inr hq⟩
  choose p hp hdp using hpick
  let tr (p : ℕ) (hp : p.Prime) : D.A → ℕ := Classical.choose (prime_transport D p hp)
  have htr (p : ℕ) (hp : p.Prime) : Function.Injective (tr p hp) ∧
      ∀ a : D.A, tr p hp a ∈ D.interval ∧ p ^ a.val.factorization p ∣ tr p hp a :=
    Classical.choose_spec (prime_transport D p hp)
  let q : D.A ⊕ (D.A ⊕ D.A) → ℕ := Sum.elim d (Sum.elim e t)
  let f : D.A ⊕ (D.A ⊕ D.A) → ℕ := Sum.elim (fun a => tr (p a) (hp a) a) (fun _ => 0)
  let Lg : Finset (D.A ⊕ (D.A ⊕ D.A)) := univ.filter (fun i => ¬ q i * H ≤ D.m)
  have hLg (i : D.A ⊕ (D.A ⊕ D.A)) : i ∈ Lg ↔ ¬ q i * H ≤ D.m := by simp [Lg]
  have hd (a : D.A) (ha : Sum.inl a ∈ Lg) : d a = (p a) ^ a.val.factorization (p a) := by
    exact (hdp a).resolve_left ((hLg _).mp ha)
  have hright (a : D.A ⊕ D.A) : Sum.inr a ∉ Lg := by
    cases a with
    | inl a => simpa [Lg, q] using he a
    | inr a => simpa [Lg, q] using ht a
  have hlarge : ∀ i ∈ Lg, f i ∈ Icc (D.x+1) (D.x+D.m) ∧ q i ∣ f i := by
    intro i hi
    cases i with
    | inl a =>
      have hh := (htr (p a) (hp a)).2 a
      exact ⟨hh.1, by simpa [q, f, hd a hi] using hh.2⟩
    | inr a => exact False.elim (hright a hi)
  have hcop : ∀ i ∈ Lg, ∀ j ∈ Lg, i ≠ j → f i = f j → (q i).Coprime (q j) := by
    intro i hi j hj hne heq
    cases i with
    | inr a => exact False.elim (hright a hi)
    | inl a =>
      cases j with
      | inr b => exact False.elim (hright b hj)
      | inl b =>
        change (d a).Coprime (d b)
        rw [hd a hi, hd b hj]
        apply Nat.coprime_pow_primes _ _ (hp a) (hp b)
        intro hab
        have hsub : (⟨p a, hp a⟩ : {p : ℕ // p.Prime}) = ⟨p b, hp b⟩ := Subtype.ext hab
        have hfun : tr (p a) (hp a) = tr (p b) (hp b) :=
          congrArg (fun z : {p : ℕ // p.Prime} => tr z.val z.property) hsub
        have heq' : tr (p a) (hp a) a = tr (p a) (hp a) b := by
          simpa only [f, Sum.elim_inl, ← hfun] using heq
        exact hne (congrArg Sum.inl ((htr (p a) (hp a)).1 heq'))
  have hsmall : ∀ i ∈ (univ : Finset (D.A ⊕ (D.A ⊕ D.A))) \ Lg, 0 < q i ∧ q i * H ≤ D.m := by
    intro i hi
    have hnL := (mem_sdiff.mp hi).2
    have hbound : q i * H ≤ D.m := by simpa only [hLg, not_not] using hnL
    refine ⟨?_, hbound⟩
    cases i with
    | inl a => exact (hpos a).1
    | inr a =>
      cases a with
      | inl a => exact (hpos a).2.1
      | inr a => exact (hpos a).2.2
  have hcard : (univ : Finset (D.A ⊕ (D.A ⊕ D.A))).card = 3 * D.n := by simp [Problem.n]; omega
  obtain ⟨B, hBI, hBc, hBprod⟩ := assemble_demands univ Lg (subset_univ _) q f D.x D.m H
    (by rw [hcard]) hlarge hcop hsmall
  have hprod : (∏ i : D.A ⊕ (D.A ⊕ D.A), q i) = D.product := by
    simp only [q, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [← prod_mul_distrib, ← prod_mul_distrib]
    have hh : (fun a : D.A => d a * (e a * t a)) = (fun a => a.val) := by funext a; simpa only [mul_assoc] using (hmul a).symm
    rw [hh]
    exact prod_coe_sort D.A id
  exact ⟨B, ⟨hBI, hprod ▸ hBprod⟩, hcard ▸ hBc⟩

#print axioms ksplit3
end Erdos708H17Chain.Chain19
