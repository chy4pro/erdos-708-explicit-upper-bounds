/-
Permanent verification file for the Erdős 708 development.

Purpose (verification-stack item 4.4 of notes/case_intel/case_colombo_flt_2609.md, taken from the
Fermat's Last Theorem formalisation's verification stack): freeze the axiom set of every headline
theorem INSIDE the build. Each `#guard_msgs` below states the expected `#print axioms` output as its
docstring, so if any dependency ever acquires a `sorry`, a new axiom, or `native_decide`, this file
stops compiling instead of silently changing what "kernel-verified" means.

Build:  cd lean/proofenv && LEAN_PATH=. lake env lean Erdos708/FinalCheck.lean
Success = no output at all.
-/
import Erdos708.Statement
import Erdos708.Final
import Erdos708.H17.Chain
import Erdos708.H17.Chain19.Results
import Erdos708.H97.Chain

-- Section 14: g(n) ≤ 81n for all n.
/--
info: 'Erdos708Final.g_le_81n' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Erdos708Final.g_le_81n

-- Section 15: g(n) ≤ 33n for all n (hinge threshold 17).
/--
info: 'Erdos708H17.g_le_33n' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Erdos708H17.g_le_33n

-- Section 16: g(n) ≤ 19n for all n (the (c+2)n reduction at threshold 17).
/--
info: 'Erdos708H17Chain.Chain19.g_le_19n' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Erdos708H17Chain.Chain19.g_le_19n

-- Section 17: g(n) ≤ 12n for all n (hinge threshold 97/10).
/--
info: 'Erdos708H97.g_le_12n' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Erdos708H97.g_le_12n

-- The atom-system hinge inequality at threshold 97/10 itself.
/--
info: 'Erdos708H97.hinge97' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Erdos708H97.hinge97

/-!
### The headline bound in Mathlib-only language

`Erdos708/Statement.lean` imports Mathlib and nothing from this project. The theorems below derive
its statements from ours, so the axiom audits above certify exactly the sentence a reader can check
without reading any definition of this development. This is the local analogue of the comparator
step of the Fermat's Last Theorem verification stack.
-/

theorem reference_g_le_12 : Erdos708Statement.g_le 12 := by
  intro A M hM hub h2 x
  have hne : A.Nonempty := ⟨M, hM⟩
  have hcard : 1 ≤ A.card := Finset.card_pos.mpr hne
  have hmax : A.max' hne = M := le_antisymm (Finset.max'_le _ _ _ hub) (Finset.le_max' _ _ hM)
  obtain ⟨B, hBsub, hBcard, hdvd⟩ := Erdos708H97.g_le_12n A.card hcard A rfl h2 x
  exact ⟨B, by rwa [hmax] at hBsub, hBcard, hdvd⟩

theorem reference_g_le_19 : Erdos708Statement.g_le 19 := by
  intro A M hM hub h2 x
  have hne : A.Nonempty := ⟨M, hM⟩
  have hcard : 1 ≤ A.card := Finset.card_pos.mpr hne
  have hmax : A.max' hne = M := le_antisymm (Finset.max'_le _ _ _ hub) (Finset.le_max' _ _ hM)
  obtain ⟨B, hBsub, hBcard, hdvd⟩ :=
    Erdos708H17Chain.Chain19.g_le_19n A.card hcard A rfl h2 x
  exact ⟨B, by rwa [hmax] at hBsub, hBcard, hdvd⟩

/--
info: 'reference_g_le_12' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms reference_g_le_12

/--
info: 'reference_g_le_19' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms reference_g_le_19
