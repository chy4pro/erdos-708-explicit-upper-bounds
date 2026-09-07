import Erdos708.Chain.Arithmetic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Sqrt

namespace Erdos708Chain.Proofs
open Finset BigOperators

/-- Stop a finite product when it first crosses a target. -/
lemma product_crossing {ι : Type*} (s : Finset ι) (f : ι → ℝ) (t K : ℝ)
    (ht : 1 < t) (hK : 0 < K) (hf : ∀ i ∈ s, 1 ≤ f i ∧ f i ≤ K)
    (hp : t ≤ ∏ i ∈ s, f i) :
    ∃ u ⊆ s, t ≤ ∏ i ∈ u, f i ∧ (∏ i ∈ u, f i) < t * K := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [prod_empty] at hp; linarith
  | @insert a s ha ih =>
    by_cases hs : t ≤ ∏ i ∈ s, f i
    · obtain ⟨u, hu, ht', hbound⟩ := ih (fun i hi => hf i (mem_insert_of_mem hi)) hs
      exact ⟨u, hu.trans (subset_insert a s), ht', hbound⟩
    · refine ⟨insert a s, subset_rfl, hp, ?_⟩
      rw [prod_insert ha]
      have hprod : 0 ≤ ∏ i ∈ s, f i := prod_nonneg (fun i hi => (hf i (mem_insert_of_mem hi)).1.trans' zero_le_one)
      have haK := (hf a (mem_insert_self a s)).2
      nlinarith

/-- Section 5, two-bin packing, with P² ≤ C³ expressing P ≤ C^(3/2). -/
lemma two_bin_packing {ι : Type*} [DecidableEq ι] (s : Finset ι) (q : ι → ℝ) (C : ℝ)
    (hC : 1 ≤ C) (hq : ∀ i ∈ s, 1 < q i ∧ q i ≤ C)
    (hP : (∏ i ∈ s, q i) ^ 2 ≤ C ^ 3) :
    ∃ u ⊆ s, (∏ i ∈ u, q i) ≤ C ∧ (∏ i ∈ s \ u, q i) ≤ C := by
  classical
  let P := ∏ i ∈ s, q i
  have hPpos : 0 < P := prod_pos (fun i hi => lt_trans zero_lt_one (hq i hi).1)
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have finish (u : Finset ι) (hu : u ⊆ s) (hlo : P / C ≤ ∏ i ∈ u, q i)
      (hhi : (∏ i ∈ u, q i) ≤ C) :
      (∏ i ∈ u, q i) ≤ C ∧ (∏ i ∈ s \ u, q i) ≤ C := by
    refine ⟨hhi, ?_⟩
    have hpU : 0 < ∏ i ∈ u, q i := prod_pos (fun i hi => lt_trans zero_lt_one (hq i (hu hi)).1)
    have hid : (∏ i ∈ s \ u, q i) * (∏ i ∈ u, q i) = P := prod_sdiff hu
    have hlo' : P ≤ (∏ i ∈ u, q i) * C := (div_le_iff₀ hCp).mp hlo
    nlinarith
  by_cases hsmall : P ≤ C
  · refine ⟨s, subset_rfl, hsmall, ?_⟩
    simp only [sdiff_self, prod_empty]
    exact hC
  have ht : 1 < P / C := (lt_div_iff₀ hCp).mpr (by linarith)
  have hsqrt : 0 < Real.sqrt C := Real.sqrt_pos.2 hCp
  have hsqrt2 := Real.sq_sqrt hCp.le
  have htroot : P / C ≤ Real.sqrt C := by
    apply (div_le_iff₀ hCp).mpr
    have hsq : (C * Real.sqrt C) ^ 2 = C ^ 3 := by rw [mul_pow, hsqrt2]; ring
    change P ^ 2 ≤ C ^ 3 at hP
    nlinarith [mul_pos hCp hsqrt]
  by_cases hbig : ∃ i ∈ s, Real.sqrt C < q i
  · obtain ⟨i, hi, hlarge⟩ := hbig
    refine ⟨{i}, singleton_subset_iff.mpr hi, finish {i} (singleton_subset_iff.mpr hi) ?_ ?_⟩
    · simpa using htroot.trans hlarge.le
    · simpa using (hq i hi).2
  · have hbounded : ∀ i ∈ s, 1 ≤ q i ∧ q i ≤ Real.sqrt C := by
      intro i hi
      exact ⟨(hq i hi).1.le, le_of_not_gt (fun h => hbig ⟨i, hi, h⟩)⟩
    have htarget : P / C ≤ ∏ i ∈ s, q i := div_le_self hPpos.le hC
    obtain ⟨u, hu, hlo, hhi⟩ := product_crossing s q (P / C) (Real.sqrt C) ht hsqrt hbounded htarget
    refine ⟨u, hu, finish u hu hlo ?_⟩
    have : P / C * Real.sqrt C ≤ C := by nlinarith
    exact hhi.le.trans this

/-- Split an integer into two demands, the second small and the first either
small or a full prime-power factor of the original integer. -/
lemma split_integer (a H m : ℕ) (ha : 0 < a) (ham : a ≤ m)
    (hH : 1 ≤ H) (hm : H ^ 3 ≤ m) :
    ∃ d e : ℕ, a = d * e ∧ e * H ≤ m ∧
      (d * H ≤ m ∨ ∃ p : ℕ, p.Prime ∧ d = p ^ (a.factorization p)) := by
  classical
  let C : ℝ := (m : ℝ) / H
  have hHr : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hmr : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le ha ham)
  have hHM : (H : ℝ) ^ 3 ≤ m := by exact_mod_cast hm
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hH2 : (H : ℝ) ^ 2 ≤ m := by nlinarith [mul_nonneg (sq_nonneg (H : ℝ)) (sub_nonneg.mpr hH1)]
  have hC : 1 ≤ C := by
    apply (le_div_iff₀ hHr).mpr
    nlinarith [sq_nonneg ((H : ℝ) - 1)]
  have hC2 : (m : ℝ) ≤ C ^ 2 := by
    dsimp [C]
    rw [div_pow]
    apply (le_div_iff₀ (sq_pos_of_pos hHr)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hH2 hmr.le]
  have hC3 : (m : ℝ) ^ 2 ≤ C ^ 3 := by
    dsimp [C]
    rw [div_pow]
    apply (le_div_iff₀ (pow_pos hHr 3)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hHM (sq_nonneg (m : ℝ))]
  let q : ℕ → ℕ := fun p => p ^ a.factorization p
  have hprod : (∏ p ∈ a.primeFactors, q p) = a := (Nat.prod_primeFactors_pow_factorization ha.ne').symm
  have hqpos : ∀ p ∈ a.primeFactors, 1 < q p := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have he := hprime.factorization_pos_of_dvd ha.ne' (Nat.dvd_of_mem_primeFactors hp)
    exact Nat.one_lt_pow (by omega) hprime.one_lt
  have finish (u : Finset ℕ) (hu : u ⊆ a.primeFactors)
      (he : (∏ p ∈ a.primeFactors \ u, (q p : ℝ)) ≤ C)
      (hd : (∏ p ∈ u, (q p : ℝ)) ≤ C ∨
        ∃ p : ℕ, p.Prime ∧ (∏ p ∈ u, q p) = q p) :
      ∃ d e : ℕ, a = d * e ∧ e * H ≤ m ∧
        (d * H ≤ m ∨ ∃ p : ℕ, p.Prime ∧ d = p ^ (a.factorization p)) := by
    refine ⟨∏ p ∈ u, q p, ∏ p ∈ a.primeFactors \ u, q p, ?_, ?_, ?_⟩
    · rw [mul_comm, prod_sdiff hu, hprod]
    · have hh := (le_div_iff₀ hHr).mp he
      exact_mod_cast hh
    · rcases hd with hd | hd
      · left
        have hh := (le_div_iff₀ hHr).mp hd
        exact_mod_cast hh
      · exact Or.inr hd
  by_cases hbig : ∃ p ∈ a.primeFactors, C < (q p : ℝ)
  · obtain ⟨p, hp, hlarge⟩ := hbig
    apply finish {p} (singleton_subset_iff.mpr hp)
    · have hid := prod_sdiff (f := q) (singleton_subset_iff.mpr hp)
      rw [prod_singleton, hprod] at hid
      have hidR : (∏ r ∈ a.primeFactors \ {p}, (q r : ℝ)) * (q p : ℝ) = a := by exact_mod_cast hid
      have haR : (a : ℝ) ≤ m := by exact_mod_cast ham
      have hnon : 0 ≤ ∏ r ∈ a.primeFactors \ {p}, (q r : ℝ) := prod_nonneg (by intros; positivity)
      nlinarith
    · exact Or.inr ⟨p, Nat.prime_of_mem_primeFactors hp, by simp⟩
  · have hb : ∀ p ∈ a.primeFactors, 1 < (q p : ℝ) ∧ (q p : ℝ) ≤ C := by
      intro p hp
      exact ⟨by exact_mod_cast hqpos p hp, le_of_not_gt (fun h => hbig ⟨p, hp, h⟩)⟩
    have hprodR : (∏ p ∈ a.primeFactors, (q p : ℝ)) = a := by exact_mod_cast hprod
    have hbound : (∏ p ∈ a.primeFactors, (q p : ℝ)) ^ 2 ≤ C ^ 3 := by
      rw [hprodR]
      have haR : (a : ℝ) ≤ m := by exact_mod_cast ham
      nlinarith
    obtain ⟨u, hu, hd, he⟩ := two_bin_packing a.primeFactors (fun p => (q p : ℝ)) C hC hb hbound
    exact finish u hu he (Or.inl hd)

/-- Exact restatement of the long-interval card. -/
theorem long_interval (D : Problem) (hm : 8 * D.n ^ 3 ≤ D.m) :
    ∃ B : Finset ℕ, Covers D B ∧ B.card ≤ 2 * D.n := by
  classical
  have hn : 0 < D.n := card_pos.mpr D.nonempty
  let H := 2 * D.n
  have hH : 1 ≤ H := by dsimp [H]; omega
  have hmH : H ^ 3 ≤ D.m := by dsimp [H]; nlinarith
  have hs (a : D.A) := split_integer a.val H D.m
    (by have := D.two_le a.val a.property; omega) (le_max' _ _ a.property) hH hmH
  choose d e hmul he hcase using hs
  have hpos (a : D.A) : 0 < d a ∧ 0 < e a := by
    have ha := D.two_le a.val a.property
    have hh := hmul a
    constructor <;> nlinarith
  have hpick (a : D.A) : ∃ p : ℕ, p.Prime ∧ (d a * H ≤ D.m ∨ d a = p ^ a.val.factorization p) := by
    rcases hcase a with h | ⟨p, hp, hq⟩
    · exact ⟨2, Nat.prime_two, Or.inl h⟩
    · exact ⟨p, hp, Or.inr hq⟩
  choose p hp hdp using hpick
  let tr (p : ℕ) (hp : p.Prime) : D.A → ℕ := Classical.choose (prime_transport D p hp)
  have htr (p : ℕ) (hp : p.Prime) : Function.Injective (tr p hp) ∧
      ∀ a : D.A, tr p hp a ∈ D.interval ∧ p ^ a.val.factorization p ∣ tr p hp a :=
    Classical.choose_spec (prime_transport D p hp)
  let q : D.A ⊕ D.A → ℕ := Sum.elim d e
  let f : D.A ⊕ D.A → ℕ := Sum.elim (fun a => tr (p a) (hp a) a) (fun _ => 0)
  let Lg : Finset (D.A ⊕ D.A) := univ.filter (fun i => ¬ q i * H ≤ D.m)
  have hLg (i : D.A ⊕ D.A) : i ∈ Lg ↔ ¬ q i * H ≤ D.m := by simp [Lg]
  have hd (a : D.A) (ha : Sum.inl a ∈ Lg) : d a = (p a) ^ a.val.factorization (p a) := by
    exact (hdp a).resolve_left ((hLg _).mp ha)
  have hright (a : D.A) : Sum.inr a ∉ Lg := by simpa [Lg, q] using he a
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
  have hsmall : ∀ i ∈ (univ : Finset (D.A ⊕ D.A)) \ Lg, 0 < q i ∧ q i * H ≤ D.m := by
    intro i hi
    have hnL := (mem_sdiff.mp hi).2
    have hbound : q i * H ≤ D.m := by simpa only [hLg, not_not] using hnL
    refine ⟨?_, hbound⟩
    cases i with
    | inl a => exact (hpos a).1
    | inr a => exact (hpos a).2
  have hcard : (univ : Finset (D.A ⊕ D.A)).card = 2 * D.n := by simp [Problem.n]; omega
  obtain ⟨B, hBI, hBc, hBprod⟩ := assemble_demands univ Lg (subset_univ _) q f D.x D.m H
    (by rw [hcard]) hlarge hcop hsmall
  have hprod : (∏ i : D.A ⊕ D.A, q i) = D.product := by
    simp only [q, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [← prod_mul_distrib]
    have hh : (fun a : D.A => d a * e a) = (fun a => a.val) := by funext a; exact (hmul a).symm
    rw [hh]
    exact prod_coe_sort D.A id
  exact ⟨B, ⟨hBI, hprod ▸ hBprod⟩, hcard ▸ hBc⟩

#print axioms product_crossing
#print axioms two_bin_packing
#print axioms split_integer
#print axioms long_interval
end Erdos708Chain.Proofs
