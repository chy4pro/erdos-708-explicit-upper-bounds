import Erdos708.H97.Proofs.CarrierCore
open Finset BigOperators
namespace Erdos708H97.Proofs
noncomputable section
set_option maxHeartbeats 2000000

lemma pair_mass_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) {a b : ι} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    w a+w b ≤ ∑ i ∈ s, w i := by
  have hh : ({a,b} : Finset ι) ⊆ s := by simp only [insert_subset_iff,singleton_subset_iff]; exact ⟨ha,hb⟩
  have hs := sum_le_sum_of_subset_of_nonneg hh (fun i hi _ => hw i hi)
  simpa [hab] using hs

/-- The four retention-budget cases, using the actual gaps in the level set. -/
lemma prefix_eta_budget {ι : Type*} [DecidableEq ι] (s : Finset ι) (idx : ι → ℕ)
    (a : ι) (ha : a ∈ s)
    (hprev : (∑ b ∈ s.erase a, (Rounded.level (idx b) : ℝ)) ≤ 1)
    (horder : ∀ b ∈ s, idx b ≤ idx a) :
    (∑ b ∈ s, eta (Rounded.level (idx b))) ≤ 2/3 := by
  let w := fun b => (Rounded.level (idx b) : ℝ)
  let θ := w a
  let t := s.erase a
  have hw0 (b : ι) : 0 ≤ w b := (Rounded.level (idx b)).coe_nonneg
  have hw1 (b : ι) : w b ≤ 1 := by exact_mod_cast Rounded.level_le_one (idx b)
  have hord (b : ι) (hb : b ∈ s) : θ ≤ w b := by exact_mod_cast Rounded.level_antitone (horder b hb)
  have hmass : (∑ b ∈ s, w b) ≤ 1+θ := by
    rw [← sum_erase_add _ _ ha]
    change (∑ b ∈ s.erase a, w b) + θ ≤ 1+θ
    linarith
  have hp : (∑ b ∈ t, w b) ≤ 1 := hprev
  by_cases hθ : (1/2 : ℝ) < θ
  · have hc : t.card ≤ 1 := by
      by_contra hn
      have hs : (t.card : ℝ)*θ ≤ ∑ b ∈ t, w b := by
        calc
          _ = ∑ _b ∈ t, θ := by simp
          _ ≤ _ := sum_le_sum (fun b hb => hord b (mem_erase.mp hb).2)
      have hr : (2 : ℝ) ≤ t.card := by exact_mod_cast (show 2 ≤ t.card by omega)
      nlinarith
    have he : (∑ b ∈ s, eta (w b)) = (s.card : ℝ)/3 := by
      have ht : ∀ b ∈ s, eta (w b) = 1/3 := by
        intro b hb
        exact if_pos (hθ.trans_le (hord b hb))
      rw [sum_congr rfl ht]
      simp [div_eq_mul_inv]
    change (∑ b ∈ s, eta (w b)) ≤ _
    rw [he]
    have hcard : s.card ≤ 2 := by have := card_erase_of_mem ha; change t.card = s.card-1 at this; omega
    have hr : (s.card : ℝ) ≤ 2 := by exact_mod_cast hcard
    linarith
  · have hθle : θ ≤ 1/2 := le_of_not_gt hθ
    let high := s.filter (fun b => 1/2 < w b)
    have high_sub : high ⊆ t := by
      intro b hb
      refine mem_erase.mpr ⟨?_,(mem_filter.mp hb).1⟩
      intro he
      subst b
      exact hθ (mem_filter.mp hb).2
    have hc : high.card ≤ 1 := by
      by_contra hn
      have hne : high.Nonempty := card_pos.mp (by omega)
      have hh : (high.card : ℝ)*(1/2) < ∑ b ∈ high, w b := by
        have hs := sum_lt_sum (s := high)
          (fun b hb => (mem_filter.mp hb).2.le)
          (by obtain ⟨b,hb⟩ := hne; exact ⟨b,hb,(mem_filter.mp hb).2⟩)
        simpa using hs
      have hs : (∑ b ∈ high, w b) ≤ ∑ b ∈ t, w b :=
        sum_le_sum_of_subset_of_nonneg high_sub (fun b _ _ => hw0 b)
      have hr : (2 : ℝ) ≤ high.card := by exact_mod_cast (show 2 ≤ high.card by omega)
      linarith
    by_cases he : high.Nonempty
    · obtain ⟨b,hb⟩ := he
      have hbS := (mem_filter.mp hb).1
      have hbT := high_sub hb
      have hbhi := (mem_filter.mp hb).2
      have hbgap : (5/8 : ℝ) ≤ w b := Rounded.level_high_gap (idx b) hbhi
      have high_eq : high = {b} := by
        apply eq_singleton_iff_unique_mem.mpr
        refine ⟨hb, ?_⟩
        intro c hc'
        have hh : high.card = 1 := by have := card_pos.mpr (show high.Nonempty from ⟨b,hb⟩); omega
        exact (card_eq_one.mp hh).choose_spec ▸ hc' |> mem_singleton.mp |>.trans
          ((card_eq_one.mp hh).choose_spec ▸ hb |> mem_singleton.mp).symm
      by_cases hsmall : θ ≤ 3/8
      · have hbθ : eta (w b) = 1/3 := if_pos hbhi
        have hlo : ∀ c ∈ s.erase b, eta (w c) = 4*w c/9 := by
          intro c hc'
          apply if_neg
          intro hh
          have hm : c ∈ high := mem_filter.mpr ⟨(mem_erase.mp hc').2,hh⟩
          rw [high_eq] at hm
          exact (mem_erase.mp hc').1 (mem_singleton.mp hm)
        have hm : (∑ c ∈ s.erase b, w c) ≤ 3/4 := by
          have hh := sum_erase_add (s := s) w hbS
          linarith
        change (∑ c ∈ s, eta (w c)) ≤ _
        rw [← sum_erase_add _ _ hbS,hbθ,sum_congr rfl hlo,← sum_div,← mul_sum]
        linarith
      · have ht_eq : t = {b} := by
          apply eq_singleton_iff_unique_mem.mpr
          refine ⟨hbT, ?_⟩
          intro c hc'
          by_contra hcb
          have hcgap : (7/16 : ℝ) ≤ w c := Rounded.level_middle_gap (idx c)
            ((lt_of_not_ge hsmall).trans_le (hord c (mem_erase.mp hc').2))
          have hh := pair_mass_le t w (fun c _ => hw0 c) hbT hc' (fun h => hcb h.symm)
          linarith
        have heta : eta θ = 4*θ/9 := if_neg hθ
        change (∑ c ∈ s, eta (w c)) ≤ _
        rw [← sum_erase_add _ _ ha]
        change (∑ c ∈ t, eta (w c)) + eta θ ≤ _
        rw [ht_eq,sum_singleton,show eta (w b) = 1/3 from if_pos hbhi,heta]
        linarith
    · have hlo : ∀ b ∈ s, eta (w b) = 4*w b/9 := by
        intro b hb
        apply if_neg
        intro hh
        exact he ⟨b,mem_filter.mpr ⟨hb,hh⟩⟩
      change (∑ b ∈ s, eta (w b)) ≤ _
      rw [sum_congr rfl hlo,← sum_div,← mul_sum]
      linarith

lemma carrier_log_bound (A : AtomSystem) (m P : ℕ) (hP : P ∈ carriers A m) :
    Real.log (P : ℝ) ≤ (2/3)*Real.log (m : ℝ) := by
  obtain ⟨ha,hfactor,hprev,horder⟩ := carrier_data A m P hP
  have hbudget := prefix_eta_budget (Rounded.effective (small A m) m P)
    (Rounded.levelHeight (small A m)) (lastLevel A m P) ha hprev horder
  have he : Real.log (P : ℝ) = ∑ a ∈ Rounded.effective (small A m) m P,
      Real.log (Rounded.modulus a : ℝ) := by
    conv_lhs => rw [hfactor,Nat.cast_prod]
    exact Real.log_prod (fun a ha => by exact_mod_cast (Rounded.retained_modulus_pos (small A m) m (mem_filter.mp ha).1).ne')
  rw [he]
  calc
    _ ≤ ∑ a ∈ Rounded.effective (small A m) m P,
        eta (Rounded.levelValue (small A m) a)*Real.log (m : ℝ) :=
      sum_le_sum (fun a ha => Rounded.retained_log_bound (small A m) m (mem_filter.mp ha).1)
    _ = (∑ a ∈ Rounded.effective (small A m) m P, eta (Rounded.levelValue (small A m) a))*Real.log (m : ℝ) := (sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hbudget (Real.log_natCast_nonneg m)

lemma carrier_cube (A : AtomSystem) (m P : ℕ) (hP : P ∈ carriers A m) : P^3 ≤ m^2 := by
  have hpR : (0 : ℝ) < P := by exact_mod_cast carrier_pos A m P hP
  have hm : 2 ≤ m := Rounded.retained_m_ge_two (small A m) m (mem_filter.mp (carrier_data A m P hP).1).1
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hh := carrier_log_bound A m P hP
  have he : Real.log ((P : ℝ)^3) ≤ Real.log ((m : ℝ)^2) := by
    rw [Real.log_pow,Real.log_pow]
    norm_num
    linarith
  exact_mod_cast (Real.log_le_log_iff (pow_pos hpR 3) (pow_pos hmR 2)).mp he

#print axioms prefix_eta_budget
#print axioms carrier_cube
end
end Erdos708H97.Proofs
