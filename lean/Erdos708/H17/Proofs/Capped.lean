import Erdos708.H17.Proofs.Lemma4
import Erdos708.H17.Proofs.Lemma3
open Finset BigOperators
open scoped NNReal
namespace Erdos708H17.Rounded
noncomputable section
attribute [local instance] Classical.propDecidable

def capIncrement (A : AtomSystem) (m : ℕ) (θ : ℝ) (a : ℕ × ℕ) : ℝ :=
  min (levelValue A a : ℝ) θ - min (previousValue A m a : ℝ) θ

lemma capIncrement_bounds (A : AtomSystem) (m : ℕ) (θ : ℝ) (a : ℕ × ℕ)
    (ha : a ∈ retained A m) : 0 ≤ capIncrement A m θ a ∧ capIncrement A m θ a ≤ increment A m a := by
  have hprev : (previousValue A m a : ℝ) ≤ levelValue A a := sub_nonneg.mp (increment_nonneg A m ha)
  constructor
  · exact sub_nonneg.mpr (min_le_min hprev le_rfl)
  · dsimp only [capIncrement, increment]
    by_cases hv : (levelValue A a : ℝ) ≤ θ
    · rw [min_eq_left hv, min_eq_left (hprev.trans hv)]
    · rw [min_eq_right (le_of_not_ge hv)]
      by_cases hp : (previousValue A m a : ℝ) ≤ θ
      · rw [min_eq_left hp]
        linarith
      · rw [min_eq_right (le_of_not_ge hp)]
        linarith

lemma capIncrement_telescope (A : AtomSystem) (m p n : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∑ a ∈ (retained A m).filter (fun a => a.1 = p ∧ modulus a ∣ n), capIncrement A m θ a) =
      min (bp A m p n) θ := by
  classical
  let s := (retained A m).filter (fun a => a.1 = p ∧ modulus a ∣ n)
  have hinj : Set.InjOn Prod.snd (s : Set (ℕ × ℕ)) := by
    intro a ha b hb hab
    exact Prod.ext ((mem_filter.mp ha).2.1.trans (mem_filter.mp hb).2.1.symm) hab
  have hmono : ∀ a ∈ s, ∀ b ∈ s, a.2 ≤ b.2 → levelValue A a ≤ levelValue A b := by
    intro a ha b hb hab
    exact retained_value_mono A m (mem_filter.mp ha).1 (mem_filter.mp hb).1
      ((mem_filter.mp ha).2.1.trans (mem_filter.mp hb).2.1.symm) hab
  have hprev (a : ℕ × ℕ) (ha : a ∈ s) :
      previousValue A m a = (s.filter (fun b => b.2 < a.2)).sup (levelValue A) := by
    apply congrArg (fun t : Finset (ℕ × ℕ) => t.sup (levelValue A))
    ext b
    constructor
    · intro hb
      obtain ⟨hb, hbp, hbj⟩ := mem_filter.mp hb
      apply mem_filter.mpr
      refine ⟨mem_filter.mpr ⟨hb, hbp.trans (mem_filter.mp ha).2.1, ?_⟩, hbj⟩
      simpa only [modulus, hbp] using
        (Nat.pow_dvd_pow a.1 hbj.le).trans (mem_filter.mp ha).2.2
    · intro hb
      obtain ⟨hb, hbj⟩ := mem_filter.mp hb
      exact mem_filter.mpr ⟨(mem_filter.mp hb).1,
        (mem_filter.mp hb).2.1.trans (mem_filter.mp ha).2.1.symm, hbj⟩
  let Θ : ℝ≥0 := ⟨θ, hθ⟩
  have hclip (t : Finset (ℕ × ℕ)) :
      ((t.sup (fun a => min (levelValue A a) Θ) : ℝ≥0) : ℝ) =
        min ((t.sup (levelValue A) : ℝ≥0) : ℝ) θ := by
    rw [← Finset.sup_inf_distrib_right]
    rfl
  calc
    _ = ∑ a ∈ s, (((min (levelValue A a) Θ : ℝ≥0) : ℝ) -
        (((s.filter (fun b => b.2 < a.2)).sup (fun a => min (levelValue A a) Θ) : ℝ≥0) : ℝ)) := by
      apply sum_congr rfl
      intro a ha
      rw [capIncrement, hprev a ha, hclip]
      rfl
    _ = ((s.sup (fun a => min (levelValue A a) Θ) : ℝ≥0) : ℝ) :=
      sum_jumps_eq_sup s Prod.snd (fun a => min (levelValue A a) Θ) hinj
        (fun a ha b hb hab => min_le_min (hmono a ha b hb hab) le_rfl)
    _ = _ := hclip s


/-- Normalize the capped rounded component by theta; its per-prime mass is at most one. -/
def unitCap (A : AtomSystem) (m : ℕ) (θ : ℝ) (hθ : 0 < θ) : AtomSystem where
  atoms := retained A m
  weight a := capIncrement A m θ a / θ
  prime_of_mem a ha := A.prime_of_mem a (rounding_retained_mem_atoms A m ha)
  weight_nonneg a ha := div_nonneg (capIncrement_bounds A m θ a ha).1 hθ.le
  perPrime_le_one p := by
    rw [← sum_div]
    have heq : (∑ a ∈ (retained A m).filter (fun a => a.1 = p), capIncrement A m θ a) =
        min (bp A m p 0) θ := by
      simpa only [dvd_zero, and_true] using capIncrement_telescope A m p 0 θ hθ.le
    rw [heq]
    exact (div_le_one hθ).mpr (min_le_right _ _)

lemma unitCap_component (A : AtomSystem) (m p n : ℕ) (θ : ℝ) (hθ : 0 < θ) :
    component (unitCap A m θ hθ) p n = min (bp A m p n) θ / θ := by
  simp only [component, unitCap, ← sum_div]
  convert congrArg (fun t : ℝ => t / θ) (capIncrement_telescope A m p n θ hθ.le) using 1 <;> congr 3

lemma unitCap_mean (A : AtomSystem) (m : ℕ) (θ : ℝ) (hθ : 0 < θ) :
    mean (unitCap A m θ hθ) ≤ HB A m / θ := by
  simp only [mean, unitCap, HB, sum_div]
  apply sum_le_sum
  intro a ha
  have hh := div_le_div_of_nonneg_right (capIncrement_bounds A m θ a ha).2
    (show 0 ≤ (modulus a : ℝ) by positivity)
  have hhh := div_le_div_of_nonneg_right hh hθ.le
  simpa only [modulus, Nat.cast_pow, div_right_comm] using hhh

lemma cap_moment (A : AtomSystem) (m N r : ℕ) (θ : ℝ) (hθ : 0 < θ)
    (s : Finset ℕ) (hs : s ⊆ primes A) :
    (∑ n ∈ Icc 1 N, esymm s (fun p => min (bp A m p n) θ / θ) r) ≤
      (N : ℝ) * (HB A m / θ)^r / (Nat.factorial r : ℝ) := by
  classical
  let C := unitCap A m θ hθ
  have hcomp (p n : ℕ) : min (bp A m p n) θ / θ = component C p n :=
    (unitCap_component A m p n θ hθ).symm
  have hmono (n : ℕ) : esymm s (fun p => component C p n) r ≤
      esymm (primes C) (fun p => component C p n) r := by
    let t := s ∪ primes C
    have hst : s.powersetCard r ⊆ t.powersetCard r := powersetCard_mono subset_union_left
    have hCt : (primes C).powersetCard r ⊆ t.powersetCard r := powersetCard_mono subset_union_right
    apply le_trans (sum_le_sum_of_subset_of_nonneg hst
      (fun u hu _ => prod_nonneg (fun p hp => Proofs.component_nonneg C p n)))
    apply le_of_eq
    symm
    apply sum_subset hCt
    intro u hu hnot
    have hn : ¬ u ⊆ primes C := by
      intro hh
      exact hnot (mem_powersetCard.mpr ⟨hh,(mem_powersetCard.mp hu).2⟩)
    obtain ⟨p,hpu,hpC⟩ := not_subset.mp hn
    exact prod_eq_zero hpu (Proofs.component_eq_zero_of_not_mem C p n hpC)
  simp_rw [hcomp]
  apply (sum_le_sum (fun n hn => hmono n)).trans
  apply (Proofs.atom_moment C N r).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply pow_le_pow_left₀
  · exact sum_nonneg (fun a ha => div_nonneg (C.weight_nonneg a ha) (by positivity))
  · exact unitCap_mean A m θ hθ

#print axioms unitCap_component
#print axioms unitCap_mean
#print axioms cap_moment
end
end Erdos708H17.Rounded
