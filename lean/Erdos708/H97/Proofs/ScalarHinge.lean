import Erdos708.H97.Proofs.CubeReduction
open Finset BigOperators
namespace Erdos708H97.Proofs
noncomputable section
set_option maxHeartbeats 2000000

def vertexRatio (a : ℝ) (r h : ℕ) : ℝ := ((h : ℝ)-a)/(h.choose r : ℝ)

lemma vertexRatio_step (a : ℝ) (r h : ℕ) (hrh : r ≤ h) :
    (vertexRatio a r h ≤ vertexRatio a r (h+1) ↔
      ((r : ℝ)-1)*((h : ℝ)+1) ≤ (r : ℝ)*a) ∧
    (vertexRatio a r (h+1) ≤ vertexRatio a r h ↔
      (r : ℝ)*a ≤ ((r : ℝ)-1)*((h : ℝ)+1)) := by
  have hb : (0 : ℝ) < h.choose r := by exact_mod_cast Nat.choose_pos hrh
  have hb' : (0 : ℝ) < (h+1).choose r := by exact_mod_cast Nat.choose_pos (show r ≤ h+1 by omega)
  have hpos : 0 < (h : ℝ)+1-r := by
    have hrR : (r : ℝ) ≤ h := by exact_mod_cast hrh
    linarith
  have he : (h.choose r : ℝ)*((h : ℝ)+1) = ((h+1).choose r : ℝ)*((h : ℝ)+1-r) := by
    have hh := congrArg (fun n : ℕ => (n : ℝ)) (Nat.choose_mul_succ_eq h r)
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_sub (show r ≤ h+1 by omega)] using hh
  have hid : ((h : ℝ)+1-r)*(((h : ℝ)+1-a)*(h.choose r : ℝ)-((h : ℝ)-a)*((h+1).choose r : ℝ)) =
      (h.choose r : ℝ)*((r : ℝ)*a-((r : ℝ)-1)*((h : ℝ)+1)) := by
    linear_combination ((h : ℝ)-a)*he
  unfold vertexRatio
  push_cast
  rw [div_le_div_iff₀ hb hb',div_le_div_iff₀ hb' hb]
  constructor
  · constructor
    · intro hh
      have hmul := mul_nonneg hpos.le (sub_nonneg.mpr hh)
      rw [hid] at hmul
      exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hb).mp hmul)
    · intro hh
      have hmul := mul_nonneg hb.le (sub_nonneg.mpr hh)
      rw [← hid] at hmul
      exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hpos).mp hmul)
  · constructor
    · intro hh
      have hmul := mul_nonpos_of_nonneg_of_nonpos hpos.le (sub_nonpos.mpr hh)
      rw [hid] at hmul
      nlinarith
    · intro hh
      have hmul := mul_nonpos_of_nonneg_of_nonpos hb.le (sub_nonpos.mpr hh)
      rw [← hid] at hmul
      nlinarith

lemma maximizingVertex_bounds (a : ℝ) (r : ℕ) (hr : 2 ≤ r) (ha : (r : ℝ)-1 ≤ a) :
    r ≤ maximizingVertex a r ∧ a < (maximizingVertex a r : ℝ) ∧
    (maximizingVertex a r : ℝ) ≤ (r : ℝ)*a/(r-1) ∧
    (r : ℝ)*a/(r-1) < (maximizingVertex a r : ℝ)+1 := by
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hd : 0 < (r : ℝ)-1 := by linarith
  have ha0 : 0 ≤ a := by linarith
  have hz : 0 ≤ (r : ℝ)*a/(r-1) := by positivity
  have hlo := Nat.floor_le hz
  have hhi := Nat.lt_floor_add_one ((r : ℝ)*a/(r-1))
  have hra : (r : ℝ) ≤ (r : ℝ)*a/(r-1) := (le_div_iff₀ hd).mpr (by nlinarith)
  have hrn : r ≤ ⌊(r : ℝ)*a/(r-1)⌋₊ := Nat.le_floor hra
  have haa : a+1 ≤ (r : ℝ)*a/(r-1) := (le_div_iff₀ hd).mpr (by nlinarith)
  exact ⟨hrn,by change a < (⌊(r : ℝ)*a/(r-1)⌋₊ : ℝ); linarith,hlo,hhi⟩

lemma vertexRatio_max (a : ℝ) (r : ℕ) (hr : 2 ≤ r) (ha : (r : ℝ)-1 ≤ a)
    (h : ℕ) (hh : r ≤ h) : vertexRatio a r h ≤ hingeMajorant a r := by
  let v := maximizingVertex a r
  obtain ⟨hrv,hav,hvlo,hvhi⟩ := maximizingVertex_bounds a r hr ha
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hd : 0 < (r : ℝ)-1 := by linarith
  have hinc : ∀ k : ℕ, r ≤ k → k < v → vertexRatio a r k ≤ vertexRatio a r (k+1) := by
    intro k hk hkv
    apply (vertexRatio_step a r k hk).1.mpr
    have hkR : (k : ℝ)+1 ≤ v := by exact_mod_cast (show k+1 ≤ v by omega)
    have hvR : (v : ℝ)*((r : ℝ)-1) ≤ (r : ℝ)*a := (le_div_iff₀ hd).mp hvlo
    nlinarith
  have hdec : ∀ k : ℕ, v ≤ k → vertexRatio a r (k+1) ≤ vertexRatio a r k := by
    intro k hk
    apply (vertexRatio_step a r k (hrv.trans hk)).2.mpr
    have hkR : (v : ℝ)+1 ≤ (k : ℝ)+1 := by exact_mod_cast Nat.add_le_add_right hk 1
    have hvR : (r : ℝ)*a < ((v : ℝ)+1)*((r : ℝ)-1) := (div_lt_iff₀ hd).mp hvhi
    nlinarith
  change vertexRatio a r h ≤ vertexRatio a r v
  by_cases hhv : h ≤ v
  · have hm : ∀ k : ℕ, h ≤ k → k ≤ v → vertexRatio a r h ≤ vertexRatio a r k := by
      intro k hhk
      induction k, hhk using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ k hk ih =>
        intro hkv
        exact (ih (by omega)).trans (hinc k (by omega) (by omega))
    exact hm v hhv le_rfl
  · have hvh : v ≤ h := by omega
    clear hhv
    induction h, hvh using Nat.le_induction with
    | base => exact le_rfl
    | succ h hvh ih => exact (hdec h hvh).trans (ih (by omega))

/-- G6's h<r case follows from h <= r-1 <= a. -/
lemma optimized_vertex_bound (a : ℝ) (r : ℕ) (hr : 2 ≤ r) (ha : (r : ℝ)-1 ≤ a)
    (h : ℕ) : max ((h : ℝ)-a) 0 ≤ hingeMajorant a r*(h.choose r : ℝ) := by
  have hb := maximizingVertex_bounds a r hr ha
  have hC : 0 ≤ hingeMajorant a r := div_nonneg (sub_nonneg.mpr hb.2.1.le) (Nat.cast_nonneg _)
  apply max_le
  · by_cases hhr : r ≤ h
    · have hp : (0 : ℝ) < h.choose r := by exact_mod_cast Nat.choose_pos hhr
      exact (div_le_iff₀ hp).mp (vertexRatio_max a r hr ha h hhr)
    · have hle : (h : ℝ) ≤ (r : ℝ)-1 := by
        have he : (h : ℝ)+1 ≤ r := by exact_mod_cast (show h+1 ≤ r by omega)
        linarith
      exact (sub_nonpos.mpr (hle.trans ha)).trans (mul_nonneg hC (Nat.cast_nonneg _))
  · exact mul_nonneg hC (Nat.cast_nonneg _)

lemma optimized_hinge {ι : Type*} [DecidableEq ι] (s : Finset ι) (u : ι → ℝ)
    (hu : ∀ i ∈ s, 0 ≤ u i ∧ u i ≤ 1) (a : ℝ) (r : ℕ)
    (hr : 2 ≤ r) (ha : (r : ℝ)-1 ≤ a) :
    max (∑ i ∈ s, u i-a) 0 ≤ hingeMajorant a r*esymm s u r :=
  hinge_of_vertex_bound s u hu a (hingeMajorant a r) r (optimized_vertex_bound a r hr ha)

#print axioms optimized_hinge
end
end Erdos708H97.Proofs
