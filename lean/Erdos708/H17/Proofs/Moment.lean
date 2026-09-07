import Erdos708.H17.Defs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Totient
open Finset BigOperators
namespace Erdos708H17.Proofs
noncomputable section
lemma moment_esymm_insert {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (x : ι → ℝ) (a : ι) (ha : a ∉ s) (k : ℕ) :
    (∑ t ∈ (insert a s).powersetCard (k + 1), ∏ i ∈ t, x i) =
      (∑ t ∈ s.powersetCard (k + 1), ∏ i ∈ t, x i) +
      x a * ∑ t ∈ s.powersetCard k, ∏ i ∈ t, x i := by
  rw [powersetCard_succ_insert ha, sum_union]
  · congr 1
    rw [sum_image, mul_sum]
    · apply sum_congr rfl
      intro t ht
      exact prod_insert (fun hat => ha ((mem_powersetCard.mp ht).1 hat))
    · intro t ht u hu heq
      have hat : a ∉ t := fun h => ha ((mem_powersetCard.mp ht).1 h)
      have hau : a ∉ u := fun h => ha ((mem_powersetCard.mp hu).1 h)
      simpa [hat, hau] using congrArg (erase · a) heq
  · apply disjoint_left.mpr
    intro t ht ht'
    obtain ⟨u, hu, rfl⟩ := mem_image.mp ht'
    exact ha ((mem_powersetCard.mp ht).1 (mem_insert_self _ _))

lemma factorial_mul_esymm_le {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (r : ℕ) :
    (Nat.factorial r : ℝ) * (∑ t ∈ s.powersetCard r, ∏ i ∈ t, x i) ≤
      (∑ i ∈ s, x i) ^ r := by
  classical
  induction s using Finset.induction_on generalizing r with
  | empty =>
    cases r with
    | zero => simp [powersetCard_zero]
    | succ r =>
      have hempty : (∅ : Finset ι).powersetCard (r + 1) = ∅ :=
        powersetCard_eq_empty.mpr (by simp)
      simp [hempty]
  | @insert a s ha ih =>
    have hxa : 0 ≤ x a := hx a (mem_insert_self _ _)
    have hxs : ∀ i ∈ s, 0 ≤ x i := fun i hi => hx i (mem_insert_of_mem hi)
    have hs : 0 ≤ ∑ i ∈ s, x i := sum_nonneg hxs
    cases r with
    | zero => simp [powersetCard_zero]
    | succ r =>
      rw [moment_esymm_insert s x a ha r, sum_insert ha]
      calc
        _ = (Nat.factorial (r + 1) : ℝ) *
              (∑ t ∈ s.powersetCard (r + 1), ∏ i ∈ t, x i) +
            ((r + 1 : ℕ) : ℝ) * x a *
              ((Nat.factorial r : ℝ) * (∑ t ∈ s.powersetCard r, ∏ i ∈ t, x i)) := by
          rw [Nat.factorial_succ, Nat.cast_mul]
          ring
        _ ≤ (∑ i ∈ s, x i) ^ (r + 1) +
            ((r + 1 : ℕ) : ℝ) * x a * (∑ i ∈ s, x i) ^ r :=
          add_le_add (ih hxs (r + 1))
            (mul_le_mul_of_nonneg_left (ih hxs r) (by positivity))
        _ ≤ (x a + ∑ i ∈ s, x i) ^ (r + 1) := by
          simpa [mul_assoc, mul_left_comm, mul_comm, add_comm] using
            (pow_add_mul_le_add_pow hs (by positivity : 0 ≤ 2 * (∑ i ∈ s, x i) + x a)
              (r + 1))

lemma coprime_indicator_sum_le {ι : Type*} (s : Finset ι)
    (q : ι → ℕ) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hcop : ∀ i ∈ s, ∀ k ∈ s, i ≠ k → Nat.Coprime (q i) (q k)) (N : ℕ) :
    (∑ j ∈ Icc 1 N, ∏ i ∈ s, if q i ∣ j then w i else 0) ≤
      (N : ℝ) * ∏ i ∈ s, w i / (q i : ℝ) := by
  classical
  have hdvd (j : ℕ) : (∏ i ∈ s, q i) ∣ j ↔ ∀ i ∈ s, q i ∣ j := by
    constructor
    · intro h i hi
      exact (dvd_prod_of_mem q hi).trans h
    · exact prod_dvd_of_isRelPrime
        (fun i hi k hk hik => Nat.coprime_iff_isRelPrime.mp (hcop i hi k hk hik))
  have hc : #((Icc 1 N).filter (fun j => (∏ i ∈ s, q i) ∣ j)) = N / (∏ i ∈ s, q i) := by
    have heq : (Icc 1 N).filter (fun j => (∏ i ∈ s, q i) ∣ j) =
        (range N.succ).filter (fun j => j ≠ 0 ∧ (∏ i ∈ s, q i) ∣ j) := by
      ext j
      simp only [mem_filter, mem_Icc, mem_range]
      omega
    rw [heq, Nat.card_multiples']
  calc
    _ = ((N / (∏ i ∈ s, q i) : ℕ) : ℝ) * ∏ i ∈ s, w i := by
      simp_rw [prod_ite_zero, ← hdvd]
      rw [← sum_filter, sum_const, nsmul_eq_mul, hc]
    _ ≤ ((N : ℝ) / (∏ i ∈ s, q i : ℕ)) * ∏ i ∈ s, w i :=
      mul_le_mul_of_nonneg_right Nat.cast_div_le (prod_nonneg hw)
    _ = _ := by
      rw [prod_div_distrib, Nat.cast_prod]
      ring

lemma average_divisor_sum {ι : Type*} (s : Finset ι) (q : ι → ℕ) (w : ι → ℝ)
    (Q : ℕ) (hQ : 0 < Q) (hdiv : ∀ a ∈ s, q a ∣ Q) :
    (∑ n ∈ Icc 1 Q, ∑ a ∈ s.filter (fun a => q a ∣ n), w a) =
      (Q : ℝ) * ∑ a ∈ s, w a / (q a : ℝ) := by
  classical
  simp_rw [sum_filter]
  rw [sum_comm, mul_sum]
  apply sum_congr rfl
  intro a ha
  have hq : 0 < q a := Nat.pos_of_dvd_of_pos (hdiv a ha) hQ
  have hc : #((Icc 1 Q).filter (fun n => q a ∣ n)) = Q / q a := by
    have heq : (Icc 1 Q).filter (fun n => q a ∣ n) =
        (range Q.succ).filter (fun n => n ≠ 0 ∧ q a ∣ n) := by
      ext n
      simp only [mem_filter, mem_Icc, mem_range]
      omega
    rw [heq, Nat.card_multiples']
  rw [← sum_filter, sum_const, nsmul_eq_mul, hc, Nat.cast_div (hdiv a ha) (by positivity)]
  ring


lemma component_expansion (A : AtomSystem) (p n : ℕ) :
    component A p n = ∑ a ∈ A.atoms.filter (fun a => a.1 = p),
      if a.1^a.2 ∣ n then A.weight a else 0 := by
  classical
  rw [component, sum_filter, sum_filter]
  apply sum_congr rfl
  intro a ha
  by_cases hp : a.1 = p <;> by_cases hn : a.1^a.2 ∣ n <;> simp [hp, hn]

lemma component_product_moment (A : AtomSystem) (N : ℕ) (T : Finset ℕ) :
    (∑ n ∈ Icc 1 N, ∏ p ∈ T, component A p n) ≤
      (N : ℝ) * ∏ p ∈ T, ∑ a ∈ A.atoms.filter (fun a => a.1 = p),
        A.weight a / (a.1^a.2 : ℕ) := by
  classical
  simp_rw [component_expansion, prod_sum]
  rw [sum_comm, mul_sum]
  apply sum_le_sum
  intro f hf
  apply coprime_indicator_sum_le
  · intro p hp
    exact A.weight_nonneg _ (mem_filter.mp (mem_pi.mp hf p.1 p.2)).1
  · intro p hp q hq hpq
    have hpa := mem_filter.mp (mem_pi.mp hf p.1 p.2)
    have hqa := mem_filter.mp (mem_pi.mp hf q.1 q.2)
    have hpp : Nat.Prime p.1 := hpa.2 ▸ (A.prime_of_mem _ hpa.1).1
    have hqp : Nat.Prime q.1 := hqa.2 ▸ (A.prime_of_mem _ hqa.1).1
    rw [hpa.2, hqa.2]
    exact Nat.coprime_pow_primes _ _ hpp hqp (fun he => hpq (Subtype.ext he))

lemma component_mean (A : AtomSystem) :
    (∑ p ∈ Rounded.primes A, ∑ a ∈ A.atoms.filter (fun a => a.1 = p),
      A.weight a / (a.1^a.2 : ℕ)) = mean A := by
  unfold Rounded.primes
  rw [sum_fiberwise_of_maps_to (fun a ha => mem_image_of_mem Prod.fst ha)]
  simp only [mean, Nat.cast_pow]

lemma atom_moment (A : AtomSystem) (N r : ℕ) :
    (∑ n ∈ Icc 1 N, esymm (Rounded.primes A) (fun p => component A p n) r) ≤
      (N : ℝ) * mean A ^ r / (Nat.factorial r : ℝ) := by
  classical
  let h : ℕ → ℝ := fun p => ∑ a ∈ A.atoms.filter (fun a => a.1 = p),
    A.weight a / (a.1^a.2 : ℕ)
  have hh : ∀ p ∈ Rounded.primes A, 0 ≤ h p := fun p hp =>
    sum_nonneg (fun a ha => div_nonneg (A.weight_nonneg a (mem_filter.mp ha).1) (Nat.cast_nonneg _))
  unfold esymm
  calc
    _ = ∑ T ∈ (Rounded.primes A).powersetCard r, ∑ n ∈ Icc 1 N, ∏ p ∈ T, component A p n := sum_comm
    _ ≤ ∑ T ∈ (Rounded.primes A).powersetCard r, (N : ℝ) * ∏ p ∈ T, h p := by
      apply sum_le_sum
      intro T hT
      exact component_product_moment A N T
    _ = (N : ℝ) * ∑ T ∈ (Rounded.primes A).powersetCard r, ∏ p ∈ T, h p := (mul_sum _ _ _).symm
    _ ≤ (N : ℝ) * (∑ p ∈ Rounded.primes A, h p) ^ r / (Nat.factorial r : ℝ) := by
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < Nat.factorial r)).2
      simpa only [mul_comm] using factorial_mul_esymm_le (Rounded.primes A) h hh r
    _ = _ := by rw [show (∑ p ∈ Rounded.primes A, h p) = mean A from component_mean A]

lemma sum_components (A : AtomSystem) (n : ℕ) :
    (∑ p ∈ Rounded.primes A, component A p n) = S A n := by
  classical
  have hmap : ∀ a ∈ A.atoms.filter (fun a => a.1^a.2 ∣ n), a.1 ∈ Rounded.primes A :=
    fun a ha => mem_image_of_mem Prod.fst (mem_filter.mp ha).1
  unfold S
  rw [← sum_fiberwise_of_maps_to hmap A.weight]
  unfold component
  apply sum_congr rfl
  intro p hp
  apply sum_congr
  · ext a
    simp only [mem_filter]
    tauto
  · intros; rfl

lemma component_nonneg (A : AtomSystem) (p n : ℕ) : 0 ≤ component A p n :=
  sum_nonneg (fun a ha => A.weight_nonneg a (mem_filter.mp ha).1)

lemma component_eq_zero_of_not_mem (A : AtomSystem) (p n : ℕ) (hp : p ∉ Rounded.primes A) :
    component A p n = 0 := by
  apply sum_eq_zero
  intro a ha
  have h := mem_filter.mp ha
  exact False.elim (hp (h.2.1 ▸ mem_image_of_mem Prod.fst h.1))

lemma component_valuation (A : AtomSystem) (p n : ℕ) (hp : p.Prime) (hn : 0 < n) :
    component A p n = component A p (p^(n.factorization p)) := by
  apply sum_congr
  · ext a
    simp only [mem_filter]
    constructor <;> rintro ⟨ha, hap, hd⟩
    · refine ⟨ha, hap, ?_⟩
      rw [hap] at hd ⊢
      exact pow_dvd_pow p ((hp.pow_dvd_iff_le_factorization hn.ne').mp hd)
    · refine ⟨ha, hap, ?_⟩
      rw [hap] at hd ⊢
      exact hd.trans (Nat.ordProj_dvd n p)
  · intros; rfl

lemma mean_mono (A G : AtomSystem)
    (h : ∀ p v : ℕ, component A p (p^v) ≤ component G p (p^v)) : mean A ≤ mean G := by
  classical
  let Q := ∏ a ∈ A.atoms ∪ G.atoms, a.1^a.2
  have hQ : 0 < Q := by
    apply prod_pos
    intro a ha
    rcases mem_union.mp ha with ha | ha
    · exact pow_pos (A.prime_of_mem a ha).1.pos _
    · exact pow_pos (G.prime_of_mem a ha).1.pos _
  have hdivA : ∀ a ∈ A.atoms, a.1^a.2 ∣ Q := fun a ha => dvd_prod_of_mem _ (mem_union_left _ ha)
  have hdivG : ∀ a ∈ G.atoms, a.1^a.2 ∣ Q := fun a ha => dvd_prod_of_mem _ (mem_union_right _ ha)
  have hpoint (n : ℕ) (hn : 0 < n) : S A n ≤ S G n := by
    rw [← sum_components, ← sum_components]
    calc
      _ ≤ ∑ p ∈ Rounded.primes A, component G p n := by
        apply sum_le_sum
        intro p hp
        obtain ⟨a, ha, hap⟩ := mem_image.mp hp
        have hprime : p.Prime := hap ▸ (A.prime_of_mem a ha).1
        rw [component_valuation A p n hprime hn, component_valuation G p n hprime hn]
        exact h p _
      _ ≤ ∑ p ∈ Rounded.primes A ∪ Rounded.primes G, component G p n :=
        sum_le_sum_of_subset_of_nonneg (subset_union_left) (fun p _ _ => component_nonneg G p n)
      _ = _ := by
        symm
        apply sum_subset subset_union_right
        intro p hp hpn
        exact component_eq_zero_of_not_mem G p n hpn
  have hs : (∑ n ∈ Icc 1 Q, S A n) ≤ ∑ n ∈ Icc 1 Q, S G n :=
    sum_le_sum (fun n hn => hpoint n (by have := (mem_Icc.mp hn).1; omega))
  unfold S at hs
  rw [average_divisor_sum _ _ _ Q hQ hdivA, average_divisor_sum _ _ _ Q hQ hdivG] at hs
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hh := (_root_.mul_le_mul_iff_right₀ hQr).mp hs
  simpa only [mean, Nat.cast_pow] using hh

#print axioms atom_moment
#print axioms mean_mono
end
end Erdos708H17.Proofs
