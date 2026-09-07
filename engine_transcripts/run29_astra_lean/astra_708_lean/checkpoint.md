# Erdős 708 Lean campaign checkpoint

Started: 2026-09-07 07:33:48 UTC. Hard deadline: 09:33:48 UTC.

Scope: exactly the three milestone statements in Erdos708/SparseCore.lean;
standalone proof files under Erdos708/Proofs/. No git or Mathlib build/update.

Initial state: only Numerical.lean existed, with an unproved stub.
Global-memory recall is unavailable (no recall_presets tool exposed).

07:37 UTC: Numerical proof written using Stirling's lower bound and
`2^23 * (187/768)^12 ≤ 1/2`. First compile found a namespace error and
one local inequality elaboration issue; second compile in progress.
Compiler logs: numerical_01.log, numerical_02.log.

07:43 UTC:
- Numerical: PROVED. `numerical_02.log` records
  `[propext, Classical.choice, Quot.sound]`.
- Hinge: PROVED. `hinge_02.log` records
  `[propext, Classical.choice, Quot.sound]`.
- Moment: full candidate written; first compile in progress (`moment_01.log`).
- Statement audit passes for all three names, binders, hypotheses and conclusions
  (comparison ignores only whitespace). No forbidden tokens in any proof file.
- All source edits so far were immediately followed by `lake env lean`.

## Completion — 2026-09-07 07:44 UTC

All three milestones are PROVED with exactly their original statements:

| Theorem | Final source | Successful compile log | Axioms |
| --- | --- | --- | --- |
| numerical_bound | Erdos708/Proofs/Numerical.lean | numerical_02.log | propext, Classical.choice, Quot.sound |
| hinge_le_esymm | Erdos708/Proofs/Hinge.lean | hinge_02.log | propext, Classical.choice, Quot.sound |
| moment_bound | Erdos708/Proofs/Moment.lean | moment_01.log | propext, Classical.choice, Quot.sound |

No remaining goals. Moment has only unused-variable warnings for the unchanged
hypotheses `hN` and `hr`. Statement and forbidden-token audits passed.
Final report: `report.md`. Proof completion elapsed: 10 minutes 12 seconds;
the campaign finished before the first 30-minute checkpoint was due.
