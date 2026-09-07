import Erdos708.H17.ChainParts.Defs
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Tactic.FunProp

namespace Erdos708H17Chain.Proofs
open Finset BigOperators
open scoped Pointwise

lemma functional_coordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) →L[ℝ] ℝ) (u : ι → ℝ) :
    f u = ∑ i, f (Pi.single i 1) * u i := by
  have heq : u = ∑ i, u i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  conv_lhs => rw [heq, map_sum]
  apply sum_congr rfl
  intro i hi
  simp only [map_smul, smul_eq_mul]
  ring

/-- Strict finite-dimensional LP separation, with nonnegative dual multipliers. -/
lemma separating_dual {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : κ → ι → ℝ) (b : κ → ℝ) (r : ℝ)
    (hfeas : ∃ y : ι → ℝ, (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ ∀ p, b p ≤ ∑ i, M p i * y i)
    (hr : ∀ y : ι → ℝ, (∀ i, 0 ≤ y i ∧ y i ≤ 1) →
      (∀ p, b p ≤ ∑ i, M p i * y i) → r < ∑ i, y i) :
    ∃ z : κ → ℝ, (∀ p, 0 ≤ z p) ∧
      r < (∑ p, z p * b p) - ∑ i, max ((∑ p, z p * M p i) - 1) 0 := by
  classical
  let F : (ι → ℝ) → (Option κ → ℝ) := fun y i => match i with
    | none => ∑ j, y j
    | some p => b p - ∑ j, M p j * y j
  let K : Set (ι → ℝ) := Set.Icc 0 1
  let C : Set (Option κ → ℝ) := F '' K + Set.Ici 0
  let v : Option κ → ℝ := Pi.single none r
  have hFcont : Continuous F := by
    apply continuous_pi
    intro i
    cases i <;> dsimp [F] <;> fun_prop
  have hKcomp : IsCompact K := isCompact_Icc
  have hFconv : Convex ℝ (F '' K) := by
    intro u hu v hv a c ha hc hac
    obtain ⟨y, hy, rfl⟩ := hu
    obtain ⟨z, hz, rfl⟩ := hv
    refine ⟨a • y + c • z, (convex_Icc (0 : ι → ℝ) 1) hy hz ha hc hac, ?_⟩
    ext i
    cases i with
    | none => simp [F, sum_add_distrib, ← mul_sum]
    | some p =>
      simp only [F, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, sum_add_distrib]
      simp_rw [mul_left_comm (M p _)]
      rw [← mul_sum, ← mul_sum]
      have hh : (a+c)*b p = b p := by rw [hac, one_mul]
      nlinarith [hh]
  have hCclosed : IsClosed C := isClosed_Ici.add_left_of_isCompact (hKcomp.image hFcont)
  have hCconv : Convex ℝ C := hFconv.add (convex_Ici 0)
  have hvnot : v ∉ C := by
    rintro ⟨fy, ⟨y, hy, rfl⟩, u, hu, hsum⟩
    have hcover : ∀ p, b p ≤ ∑ i, M p i * y i := by
      intro p
      have hh := congrFun hsum (some p)
      have hu0 : 0 ≤ u (some p) := hu (some p)
      simp only [F, v, Pi.single_eq_of_ne (Option.some_ne_none p), Pi.add_apply] at hh
      linarith
    have hy' : ∀ i, 0 ≤ y i ∧ y i ≤ 1 := fun i => ⟨hy.1 i, hy.2 i⟩
    have hcost := hr y hy' hcover
    have hh := congrFun hsum none
    have hu0 : 0 ≤ u none := hu none
    simp only [F, v, Pi.single_eq_same, Pi.add_apply] at hh
    linarith
  obtain ⟨l, u, hlu, hul⟩ := geometric_hahn_banach_point_closed hCconv hCclosed hvnot
  have hsep : ∀ c ∈ C, l v < l c := fun c hc => hlu.trans (hul c hc)
  let coeff : Option κ → ℝ := fun i => l (Pi.single i 1)
  have heval (w : Option κ → ℝ) : l w = ∑ i, coeff i * w i := functional_coordinates l w
  have hbase : F 0 ∈ C := by
    exact ⟨F 0, ⟨0, ⟨le_rfl, by intro i; norm_num⟩, rfl⟩, 0, by simp, add_zero _⟩
  have hcoeff : ∀ i, 0 ≤ coeff i := by
    intro i
    by_contra hi
    have hi' : coeff i < 0 := lt_of_not_ge hi
    have hgap : 0 < l (F 0) - l v + 1 := by have := hsep _ hbase; linarith
    let t := (l (F 0) - l v + 1) / (-coeff i)
    have ht : 0 < t := div_pos hgap (neg_pos.mpr hi')
    have hmem : F 0 + t • Pi.single i 1 ∈ C := by
      refine ⟨F 0, ⟨0, ⟨le_rfl, by intro j; norm_num⟩, rfl⟩, t • Pi.single i 1, ?_, rfl⟩
      intro j
      simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      split_ifs <;> positivity
    have hs := hsep _ hmem
    rw [map_add, map_smul] at hs
    change l v < l (F 0) + t * coeff i at hs
    have hid : t * (-coeff i) = l (F 0) - l v + 1 := div_mul_cancel₀ _ (ne_of_gt (neg_pos.mpr hi'))
    nlinarith
  have hcostpos : 0 < coeff none := by
    have hnon := hcoeff none
    by_contra hn
    have hz : coeff none = 0 := by linarith
    obtain ⟨y, hy, hcover⟩ := hfeas
    let w : Option κ → ℝ := Pi.single none (∑ i, y i)
    have hw : w ∈ C := by
      refine ⟨F y, ⟨y, ⟨fun i => (hy i).1, fun i => (hy i).2⟩, rfl⟩, w - F y, ?_, ?_⟩
      · intro i
        cases i with
        | none => simp [w, F]
        | some p => simpa [w, F] using sub_nonneg.mpr (hcover p)
      · abel
    have hs := hsep w hw
    rw [heval w, heval v] at hs
    simp [w, v, hz] at hs
  let z : κ → ℝ := fun p => coeff (some p) / coeff none
  have hz : ∀ p, 0 ≤ z p := fun p => div_nonneg (hcoeff _) hcostpos.le
  let y : ι → ℝ := fun i => if 1 < ∑ p, z p * M p i then 1 else 0
  have hy : y ∈ K := by constructor <;> intro i <;> dsimp [y] <;> split_ifs <;> norm_num
  have hFy : F y ∈ C := ⟨F y, ⟨y,hy,rfl⟩, 0, by simp, add_zero _⟩
  have hs := hsep _ hFy
  have hc (p : κ) : coeff (some p) = coeff none * z p := by
    dsimp [z]
    rw [mul_div_cancel₀ _ (ne_of_gt hcostpos)]
  have hdouble : (∑ p, z p * ∑ i, M p i * y i) = ∑ i, (∑ p, z p * M p i) * y i := by
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    rw [sum_mul]
    apply sum_congr rfl
    intro p hp
    ring
  have hmin : ∀ i, y i * (1 - ∑ p, z p * M p i) = -max ((∑ p, z p * M p i) - 1) 0 := by
    intro i
    dsimp [y]
    split_ifs with hi
    · rw [one_mul, max_eq_left (by linarith)]
      ring
    · rw [zero_mul, max_eq_right (by linarith), neg_zero]
  have hid : (∑ i, y i) + ∑ p, z p * (b p - ∑ i, M p i * y i) =
      (∑ p, z p * b p) - ∑ i, max ((∑ p, z p * M p i) - 1) 0 := by
    simp only [mul_sub, sum_sub_distrib]
    rw [hdouble]
    have h := congrArg (fun g : ι → ℝ => ∑ i, g i) (funext hmin)
    simp only [mul_sub, mul_one, sum_sub_distrib, sum_neg_distrib] at h
    have heq : (∑ i, y i * ∑ p, z p * M p i) = ∑ i, (∑ p, z p * M p i) * y i := by
      apply sum_congr rfl
      intro i hi
      ring
    rw [heq] at h
    linarith
  have hlv : l v = coeff none * r := by rw [heval]; simp [v]
  have hlF : l (F y) = coeff none * ((∑ i, y i) + ∑ p, z p * (b p - ∑ i, M p i * y i)) := by
    rw [heval, Fintype.sum_option]
    simp only [F, hc]
    rw [mul_add]
    congr 1
    rw [mul_sum]
    apply sum_congr rfl
    intro p hp
    ring
  refine ⟨z, hz, ?_⟩
  rw [hlv, hlF, hid] at hs
  nlinarith

#print axioms functional_coordinates
#print axioms separating_dual
end Erdos708H17Chain.Proofs
