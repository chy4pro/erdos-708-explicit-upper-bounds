import Erdos708.H17.Proofs.ExactCount
open Finset BigOperators
open scoped NNReal
namespace Erdos708H17.Proofs
noncomputable section
attribute [local instance] Classical.propDecidable

def carrierHeight (A : AtomSystem) (m P : ℕ) : ℕ := Rounded.levelHeight (small A m) (lastLevel A m P)
def scaleCarriers (A : AtomSystem) (m n h : ℕ) : Finset ℕ :=
  (carriers A m).filter (fun P => P ∣ n ∧ carrierHeight A m P = h)
def activePrimes (A : AtomSystem) (m n h : ℕ) : Finset ℕ :=
  (Rounded.primes (small A m)).filter (fun p => (2:ℝ)⁻¹^h ≤ bp A m p n)

lemma theta_eq_height (A : AtomSystem) (m P : ℕ) :
    theta A m P = (2:ℝ)⁻¹^(carrierHeight A m P) := by simp [theta, Rounded.levelValue, carrierHeight]

lemma scaled_carrier_mass (A : AtomSystem) (m P h : ℕ) (hP : P ∈ carriers A m)
    (hheight : carrierHeight A m P = h) :
    (∑ a ∈ Rounded.effective (small A m) m P, 2^(h - Rounded.levelHeight (small A m) a)) = 2^h+1 := by
  have ht : theta A m P = (2:ℝ)⁻¹^h := by rw [theta_eq_height,hheight]
  have horder (a : ℕ × ℕ) (ha : a ∈ Rounded.effective (small A m) m P) :
      Rounded.levelHeight (small A m) a ≤ h := by
    have hh := (carrier_data A m P hP).2.2.2 a ha
    change Rounded.levelHeight (small A m) a ≤ carrierHeight A m P at hh
    rwa [hheight] at hh
  have heq : (∑ a ∈ Rounded.effective (small A m) m P, (2:ℝ)^(h - Rounded.levelHeight (small A m) a)) =
      mu A m P / theta A m P := by
    change _ = Rounded.B (small A m) m P / theta A m P
    rw [Rounded.B_eq_effective_sum, sum_div]
    apply sum_congr rfl
    intro a ha
    rw [ht]
    simpa only [Rounded.levelValue, NNReal.coe_pow, NNReal.coe_inv, NNReal.coe_ofNat] using
      (Rounded.dyadic_ratio h (Rounded.levelHeight (small A m) a) (horder a ha)).symm
  have hr : mu A m P / theta A m P = (2:ℝ)^h+1 := by
    rw [carrier_mu_exact A m P hP, ht]
    simp [add_div, inv_pow, add_mul]
  exact_mod_cast heq.trans hr

lemma carrier_count_exact (A : AtomSystem) (m n h : ℕ) :
    (scaleCarriers A m n h).card ≤ carrierCount h (activePrimes A m n h).card := by
  classical
  let D := scaleCarriers A m n h
  let Q := activePrimes A m n h
  let E := fun P => Rounded.effective (small A m) m P
  let enc : ℕ → ∀ p ∈ Q, Option ℕ := fun P p _ =>
    (selectedAt (E P) p).map (fun a => h - Rounded.levelHeight (small A m) a)
  have hdata (P : ℕ) (hP : P ∈ D) :
      Set.InjOn Prod.fst (E P : Set (ℕ × ℕ)) ∧
      ∀ a ∈ E P, a.1 ∈ Q ∧ Rounded.levelHeight (small A m) a ≤ h := by
    have hp := mem_filter.mp hP
    refine ⟨Rounded.effective_fst_injective (small A m) m P, ?_⟩
    intro a ha
    have har := (mem_filter.mp ha).1
    have han := (mem_filter.mp ha).2.1.trans hp.2.1
    have hheight := (carrier_data A m P hp.1).2.2.2 a ha
    change Rounded.levelHeight (small A m) a ≤ carrierHeight A m P at hheight
    rw [hp.2.2] at hheight
    have hval : (2:ℝ)⁻¹^h ≤ (Rounded.levelValue (small A m) a : ℝ) := by
      simpa only [Rounded.levelValue, NNReal.coe_pow, NNReal.coe_inv, NNReal.coe_ofNat] using
        pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 2⁻¹) (by norm_num : (2:ℝ)⁻¹ ≤ 1) hheight
    have hbp : (Rounded.levelValue (small A m) a : ℝ) ≤ bp A m a.1 n := by
      exact_mod_cast (le_sup (f := Rounded.levelValue (small A m)) (mem_filter.mpr ⟨har,rfl,han⟩) :
        Rounded.levelValue (small A m) a ≤ Rounded.bpNN (small A m) m a.1 n)
    exact ⟨mem_filter.mpr ⟨mem_image_of_mem Prod.fst (Rounded.rounding_retained_mem_atoms (small A m) m har),
      hval.trans hbp⟩, hheight⟩
  have hrecover (P R : ℕ) (hP : P ∈ D) (hR : R ∈ D) (he : enc P = enc R) : E P ⊆ E R := by
    intro a ha
    have haq := (hdata P hP).2 a ha |>.1
    have hsel := (selectedAt_some_iff (E P) (hdata P hP).1 a.1 a).mpr ⟨ha,rfl⟩
    have hh := congrArg (fun f => f a.1 haq) he
    change (selectedAt (E P) a.1).map _ = (selectedAt (E R) a.1).map _ at hh
    rw [hsel] at hh
    cases hs : selectedAt (E R) a.1 with
    | none => simp [hs] at hh
    | some b =>
      have hb := (selectedAt_some_iff (E R) (hdata R hR).1 a.1 b).mp hs
      have hheights : Rounded.levelHeight (small A m) a = Rounded.levelHeight (small A m) b := by
        have haH := (hdata P hP).2 a ha |>.2
        have hbH := (hdata R hR).2 b hb.1 |>.2
        simp only [hs, Option.map_some, Option.some.injEq] at hh
        omega
      have heq : a = b := Rounded.carrier_height_injective (small A m) m a.1
        ⟨(mem_filter.mp ha).1,rfl⟩ ⟨(mem_filter.mp hb.1).1,hb.2⟩ hheights
      exact heq ▸ hb.1
  apply family_count D Q h enc
  · intro P hP R hR he
    have heff := Subset.antisymm (hrecover P R hP hR he) (hrecover R P hR hP he.symm)
    calc
      P = ∏ a ∈ E P, Rounded.modulus a := (carrier_data A m P (mem_filter.mp hP).1).2.1
      _ = ∏ a ∈ E R, Rounded.modulus a := congrArg (fun s => ∏ a ∈ s, Rounded.modulus a) heff
      _ = R := (carrier_data A m R (mem_filter.mp hR).1).2.1.symm
  · intro P hP
    apply mem_pi.mpr
    intro p hp
    change (selectedAt (E P) p).map _ ∈ levelChoices h
    cases hs : selectedAt (E P) p with
    | none => simp [levelChoices]
    | some a =>
      simp only [Option.map_some]
      apply mem_insert_of_mem
      apply mem_image_of_mem
      exact mem_range.mpr (by omega)
  · intro P hP
    have hsum := selectedAt_sum Q (E P) (fun a => 2^(h-Rounded.levelHeight (small A m) a))
      (hdata P hP).1 (fun a ha => (hdata P hP).2 a ha |>.1)
    have hmass := scaled_carrier_mass A m P h (mem_filter.mp hP).1 (mem_filter.mp hP).2.2
    rw [← hmass, ← hsum, ← sum_attach Q]
    apply sum_congr rfl
    intro p hp
    dsimp only [enc, choiceDegree]
    cases selectedAt (E P) p.val <;> rfl

#print axioms carrier_count_exact
end
end Erdos708H17.Proofs
