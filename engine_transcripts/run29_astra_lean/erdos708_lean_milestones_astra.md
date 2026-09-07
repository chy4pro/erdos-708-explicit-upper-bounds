# PROOF CAMPAIGN (Lean 4) — Erdős 708 sparse-core mission: three milestone lemmas

Project: /Users/roychen/workspace/claudecode/automath/lean/proofenv (Lean v4.34.0-rc1, Mathlib de5ce8a9; run `lake env lean <file>` from that directory; Mathlib is already built — never run `lake update` or `lake build` on Mathlib).
Statements (already compiling with `sorry`): /Users/roychen/workspace/claudecode/automath/lean/proofenv/Erdos708/SparseCore.lean — theorems `hinge_le_esymm`, `numerical_bound`, `moment_bound` in namespace `Erdos708SparseCore`.

Task: produce complete, sorry-free Lean proofs of the three theorems, with EXACTLY the same statements (same names, binders, hypotheses and conclusions; do not weaken or restate). Write each proof in its own file
  Erdos708/Proofs/Hinge.lean      (theorem Erdos708SparseCore.hinge_le_esymm)
  Erdos708/Proofs/Numerical.lean  (theorem Erdos708SparseCore.numerical_bound)
  Erdos708/Proofs/Moment.lean     (theorem Erdos708SparseCore.moment_bound)
each starting with `import Mathlib` and `open Finset BigOperators`, self-contained (helper lemmas allowed in the same file), and ending with `#print axioms <theorem>` whose output must list only propext, Classical.choice and Quot.sound. Do not use `native_decide`, `decide` on large terms, `sorry`, `admit`, custom axioms, or `unsafe`.

Order: Numerical first (pure real arithmetic; use (12t)! ≥ (12t/e)^{12t} or an explicit induction on t with a ratio bound; e < 11/4; note the exact inequality 2^23·(187/768)^12 < 1/2 which norm_num can check), then Hinge (induction on the number of coordinates in (0,1), or induction on s using the recursion e_{k}(x ∪ {a}) = e_k(x) + a·e_{k−1}(x)), then Moment (expand the elementary symmetric sum over powersetCard r, swap sums, bound each indicator sum by N/∏q using coprimality of prime powers of distinct primes, and finish with r!·e_r(h) ≤ (Σh)^r).

Mathematical facts you may rely on (all standard): powers of distinct primes are coprime; the number of j ≤ N divisible by d ≥ 1 is ⌊N/d⌋ ≤ N/d; Finset.sum_powersetCard / Finset.prod over powersetCard lemmas in Mathlib (search with `exact?`/`apply?` and grep Mathlib for `powersetCard`, `esymm`, `Multiset.esymm`).

Process: compile after every change; keep a log of what compiled; if a theorem resists after ~40 minutes, write down the exact remaining goal state and move to the next one. Wall-clock cap 2 hours. Write progress to /Users/roychen/workspace/claudecode/automath/engine/out/astra_708_lean/checkpoint.md every 30 minutes and a final /Users/roychen/workspace/claudecode/automath/engine/out/astra_708_lean/report.md listing, per theorem: PROVED (file, `#print axioms` output) or OPEN (remaining goal). Touch nothing outside Erdos708/Proofs/ and the output directory; no git.
