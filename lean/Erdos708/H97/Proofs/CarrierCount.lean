import Erdos708.H97.Proofs.ExactCount
open Finset BigOperators
namespace Erdos708H97.Proofs
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000

def scaleCarriers (A : AtomSystem) (m n h d : ℕ) : Finset ℕ :=
  (carriers A m).filter (fun P => P ∣ n ∧ carrierHeight A m P = h ∧ carrierMassIndex A m P = d)
def activePrimes (A : AtomSystem) (m n h : ℕ) : Finset ℕ :=
  (Rounded.primes (small A m)).filter (fun p => (Rounded.level h : ℝ) ≤ bp A m p n)

lemma carrier_count_exact (A : AtomSystem) (m n h d : ℕ) :
    (scaleCarriers A m n h d).card ≤ carrierCount (Rounded.scaleJ h) (Rounded.scaleL h) d (activePrimes A m n h).card := by
  classical
  let D := scaleCarriers A m n h d
  let Q := activePrimes A m n h
  let E := fun P => Rounded.effective (small A m) m P
  let deg := fun a => Rounded.levelDegree h (Rounded.levelHeight (small A m) a)
  let enc : ℕ → ∀ p ∈ Q, ℕ := fun P p _ => (selectedAt (E P) p).elim 0 deg
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
    rw [hp.2.2.1] at hheight
    have hval : (Rounded.level h : ℝ) ≤ Rounded.levelValue (small A m) a := by
      exact_mod_cast Rounded.level_antitone hheight
    have hbp : (Rounded.levelValue (small A m) a : ℝ) ≤ bp A m a.1 n := by
      exact_mod_cast (le_sup (f := Rounded.levelValue (small A m)) (mem_filter.mpr ⟨har,rfl,han⟩) :
        Rounded.levelValue (small A m) a ≤ Rounded.bpNN (small A m) m a.1 n)
    exact ⟨mem_filter.mpr ⟨mem_image_of_mem Prod.fst (Rounded.rounding_retained_mem_atoms (small A m) m har),hval.trans hbp⟩,hheight⟩
  have hrecover (P R : ℕ) (hP : P ∈ D) (hR : R ∈ D) (he : enc P = enc R) : E P ⊆ E R := by
    intro a ha
    have haq := ((hdata P hP).2 a ha).1
    have hsel := (selectedAt_some_iff (E P) (hdata P hP).1 a.1 a).mpr ⟨ha,rfl⟩
    have hh := congrArg (fun f => f a.1 haq) he
    change (selectedAt (E P) a.1).elim 0 deg = (selectedAt (E R) a.1).elim 0 deg at hh
    rw [hsel] at hh
    cases hs : selectedAt (E R) a.1 with
    | none =>
      simp only [hs,Option.elim_some,Option.elim_none] at hh
      have hpos := Rounded.levelDegree_pos h (Rounded.levelHeight (small A m) a)
      change 0 < deg a at hpos
      omega
    | some b =>
      have hb := (selectedAt_some_iff (E R) (hdata R hR).1 a.1 b).mp hs
      have hheights : Rounded.levelHeight (small A m) a = Rounded.levelHeight (small A m) b := by
        have haH := ((hdata P hP).2 a ha).2
        have hbH := ((hdata R hR).2 b hb.1).2
        simp only [hs,Option.elim_some] at hh
        exact Rounded.levelDegree_injective h (mem_Iic.mpr haH) (mem_Iic.mpr hbH) hh
      have heq : a = b := Rounded.carrier_height_injective (small A m) m a.1
        ⟨(mem_filter.mp ha).1,rfl⟩ ⟨(mem_filter.mp hb.1).1,hb.2⟩ hheights
      exact heq ▸ hb.1
  apply family_count D Q (Rounded.scaleJ h) (Rounded.scaleL h) d (by have := (Rounded.scaleJ_bounds h).1; omega) enc
  · intro P hP R hR he
    have heff := Subset.antisymm (hrecover P R hP hR he) (hrecover R P hR hP he.symm)
    calc
      P = ∏ a ∈ E P, Rounded.modulus a := (carrier_data A m P (mem_filter.mp hP).1).2.1
      _ = ∏ a ∈ E R, Rounded.modulus a := congrArg (fun s => ∏ a ∈ s, Rounded.modulus a) heff
      _ = R := (carrier_data A m R (mem_filter.mp hR).1).2.1.symm
  · intro P hP
    apply mem_pi.mpr
    intro p hp
    change (selectedAt (E P) p).elim 0 deg ∈ _
    cases hs : selectedAt (E P) p with
    | none => simp
    | some a =>
      simp only [Option.elim_some]
      apply mem_insert_of_mem
      exact Rounded.levelDegree_mem h _ ((hdata P hP).2 a ((selectedAt_some_iff (E P) (hdata P hP).1 p a).mp hs).1).2
  · intro P hP
    have hp := mem_filter.mp hP
    have hsum := selectedAt_sum Q (E P) deg (hdata P hP).1 (fun a ha => ((hdata P hP).2 a ha).1)
    have hmass := (carrier_degree_bounds A m P hp.1).2.2
    rw [hp.2.2.1,hp.2.2.2] at hmass
    have hdeg : (∑ a ∈ E P, deg a) = carrierDegree A m P := by
      unfold carrierDegree
      rw [hp.2.2.1]
    rw [← hmass,← hdeg,← hsum,← sum_attach Q]
  · intro P hP
    let a := lastLevel A m P
    have ha : a ∈ E P := (carrier_data A m P (mem_filter.mp hP).1).1
    have hap := ((hdata P hP).2 a ha).1
    refine ⟨a.1,hap,?_⟩
    change (selectedAt (E P) a.1).elim 0 deg = _
    rw [(selectedAt_some_iff (E P) (hdata P hP).1 a.1 a).mpr ⟨ha,rfl⟩]
    change Rounded.levelDegree h (carrierHeight A m P) = _
    rw [(mem_filter.mp hP).2.2.1,Rounded.self_degree]

#print axioms carrier_count_exact
end
end Erdos708H97.Proofs
