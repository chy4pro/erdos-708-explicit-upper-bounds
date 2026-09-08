import Erdos708.H97.Proofs.Retention
open Finset BigOperators
open scoped NNReal
namespace Erdos708H97.Rounded
noncomputable section

/-- The descending enumeration is exactly the manuscript's infinite level set. -/
lemma level_enumerates {t : ℝ} : t ∈ levels ↔ ∃ i : ℕ, (level i:ℝ)=t := by
  constructor
  · rintro (ht | ⟨h,hh,j,hj,ht⟩)
    · exact ⟨0,by simpa using ht.symm⟩
    · refine ⟨4*(h-3)+(7-j)+1,?_⟩
      have hj' := mem_Icc.mp hj
      have hm : (4*(h-3)+(7-j))%4 = 7-j := by omega
      have hd : (4*(h-3)+(7-j))/4+3 = h := by omega
      rw [level_succ,hm,hd,show 7-(7-j)=j by omega]
      exact ht.symm
  · rintro ⟨i,rfl⟩
    exact level_mem i

lemma rounded_greatest {u t : ℝ} (ht : t ∈ levels) (htu : t ≤ u) :
    t ≤ (level (roundIndex u):ℝ) := by
  obtain ⟨i,rfl⟩ := level_enumerates.mp ht
  have hi0 : (0:ℝ)<level i := by exact_mod_cast level_pos i
  have hu : 0<u := hi0.trans_le htu
  have hi : roundIndex u ≤ i := by
    rw [roundIndex,dif_pos (exists_level_le hu)]
    exact Nat.find_min' _ htu
  exact_mod_cast level_antitone hi

lemma first_rounded_representative (A : AtomSystem) (a : ℕ × ℕ) (ha : a ∈ A.atoms)
    (hc : 0 < cumulative A a.1 a.2) :
    ∃ b ∈ roundedLevels A, b.1=a.1 ∧ b.2≤a.2 ∧ levelHeight A b=levelHeight A a := by
  classical
  let t := A.atoms.filter (fun b => b.1=a.1 ∧ 0<cumulative A b.1 b.2 ∧ levelHeight A b=levelHeight A a)
  have hat : a∈t := mem_filter.mpr ⟨ha,rfl,hc,rfl⟩
  obtain ⟨b,hb,hmin⟩ := t.exists_min_image Prod.snd ⟨a,hat⟩
  obtain ⟨hba,hbp,hbc,hbh⟩ := mem_filter.mp hb
  refine ⟨b,mem_filter.mpr ⟨hba,hbc,?_⟩,hbp,hmin a hat,hbh⟩
  intro c hca hcp hcc hch
  exact hmin c (mem_filter.mpr ⟨hca,hcp.trans hbp,hcc,hch.trans hbh⟩)

/-- Keeping only first occurrences of maximal rounded cumulative values preserves
all retained levels, including levels between two cumulative atom weights. -/
lemma retained_level_dominated (A : AtomSystem) (m n : ℕ) (hm : 1≤m)
    (a : ℕ × ℕ) (ha : a∈A.atoms) (han : modulus a ∣ n)
    (t : ℝ) (ht : t∈levels) (htc : t≤cumulative A a.1 a.2)
    (hq : (modulus a:ℝ)≤(m:ℝ)^eta t) : t≤bp A m a.1 n := by
  classical
  have ht0 : 0<t := by obtain ⟨i,rfl⟩ := level_enumerates.mp ht; exact_mod_cast level_pos i
  have hc : 0<cumulative A a.1 a.2 := ht0.trans_le htc
  obtain ⟨b,hb,hbp,hbe,hbh⟩ := first_rounded_representative A a ha hc
  have hv : (levelValue A b:ℝ)=(levelValue A a:ℝ) := by simp only [levelValue,hbh]
  have htv : t≤(levelValue A b:ℝ) := hv ▸ rounded_greatest ht htc
  have hpow : modulus b≤modulus a := by
    have hp := (A.prime_of_mem a ha).1.pos
    simpa only [modulus,hbp] using Nat.pow_le_pow_right hp hbe
  have hret : b∈retained A m := by
    apply mem_filter.mpr
    refine ⟨hb, (show (modulus b:ℝ)≤modulus a by exact_mod_cast hpow).trans (hq.trans ?_)⟩
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm)
      (eta_mono ht0.le htv (by exact_mod_cast level_le_one (levelHeight A b)))
  have hbn : modulus b∣n := by
    apply dvd_trans _ han
    simpa only [modulus,hbp] using Nat.pow_dvd_pow a.1 hbe
  apply htv.trans
  exact_mod_cast (le_sup (f:=levelValue A) (mem_filter.mpr ⟨hret,hbp,hbn⟩) :
    levelValue A b≤bpNN A m a.1 n)

#print axioms retained_level_dominated
end
end Erdos708H97.Rounded
