# Erdős 708 Section 14 campaign

Started: 2026-09-07 08:15:03 UTC. Original deadline lifted by the user; no wall-clock cap remains.

Section 14 (`papers/erdos708/sec_signed.tex`) has been read in full.
First deliverable: concrete definitions, faithful lemma cards, and the sparse-core
composition proved from the cards. Then leaf attempts in the specified order.
Global-memory recall is unavailable in this session.

User update during the campaign: the two-hour wall-clock cap is LIFTED.
Continue until every Section 14 card is proved or approaches are genuinely exhausted.
All other rules, including 30-minute checkpoints and leaf order, remain in force.

08:25 UTC: first required deliverable exists and compiles.
- Defs.lean: checked concrete definitions; defs_02.log is clean.
- Cards.lean: all nine Section 14 lemma cards and the composition theorem compile.
  cards_01.log lists the explicit open cards and the composition axioms including
  sorryAx. The composition proof body itself has no proof hole; it is conditional
  on the rounding, feasibility and window-value cards.
- cards_readback.md records a one-line read-back for every card and the theorem.
- First leaf (14.7, Values.lean) is written and compiling.

## 08:44 UTC checkpoint (29 minutes elapsed)

- **14.7 values_at_point: PROVED.** Final leaf `Signed/Proofs/Values.lean`,
  successful log `values_03.log`, axioms exactly
  `[propext, Classical.choice, Quot.sound]`. Integrated into Cards.lean;
  `cards_02.log` confirms its axiom output there as well.
- **14.2 rounding: full proof candidate written; fifth compile running.**
  `Signed/Proofs/Rounding.lean` has no explicit placeholders. The previous compile
  left three elaboration issues, all corrected in the current candidate. The proof
  includes dyadic approximation, retained increments telescoping, periodic mean
  comparison, original/retained pointwise domination, and the logarithmic cutoff
  estimate for the left hinge. Do not mark PROVED until `rounding_05.log` passes.
- Other cards remain explicit OPEN cards in the compiling Cards.lean deliverable.
  Next requested leaf: 14.6 carrier_count.
- The cap remains lifted. No git, internet, lake build, or lake update has been used.

08:45 UTC update: **14.2 rounding is PROVED**.
`rounding_05.log` reports exactly `[propext, Classical.choice, Quot.sound]`.
The proof is in `Signed/Proofs/Rounding.lean`, with no placeholders.
It has been integrated into Cards.lean; `cards_03.log` is compiling.
Next: 14.6 carrier_count (first attempt starts 08:45 UTC).

09:10 UTC update:
- 14.6 first pass is OPEN, with its exact goal and remaining assembly recorded in
  `carrier_count_remaining.md`. `carrier_count_07.log` compiles successfully with
  the intentional card placeholder. Its five printed helper theorems (prefix
  recovery, carrier mass range, carrier data, weighted-choice product bound,
  per-prime geometric bound) all have only the three standard axioms.
- 14.10 first pass starts now. `Signed/Proofs/Window.lean` copies the proved rounding
  and carrier-geometry helpers, adds window counting bounds and coefficient
  nonnegativity, and is compiling in `window_01.log`.
- The requested remaining first-pass order is: 14.10 Window, 14.5 CarriedMass,
  14.9 Feasibility. Then revisit 14.6 and any other open cards, and connect/reuse the
  prior milestone proofs for the concrete 14.3/14.4/14.8 cards.

## 09:19 UTC checkpoint (64 minutes elapsed)

- Cards 14.2 and 14.7 remain PROVED and integrated; Cards.lean compiled in cards_03.log.
- Window first pass: window_02.log compiles. Checked helpers prove all interval
  counting estimates, carrier positivity, carrier modulus < m^(1/4), retained
  modulus <= m^(1/16), negative modulus < m^(5/16), positive floor quotient,
  the factor-two quotient bound, and 0 <= beta <= increment. Printed helper
  axioms are exactly the three standard axioms. Main window card remains OPEN.
- Next work: clipped telescoping and support identities; then the prescribed
  CarriedMass and Feasibility first passes, before revisiting unfinished leaves.

09:30 UTC update: **14.10 value_on_window is PROVED**.
`window_06.log` confirms `[propext, Classical.choice, Quot.sound]` for the full
four-conjunct card. It includes clipped telescoping, mass conservation, the signed
coefficient expansion, both support assertions, and the 141/64 window lower bound.
Integration into Cards.lean is compiling in cards_04.log.
Next prescribed leaf: 14.5 CarriedMass, first pass begins 09:30 UTC.

09:39 UTC update: **14.3 hinge_le_esymm and 14.4 moment_retained are PROVED**.
Standalone files Hinge.lean and Moment.lean passed in hinge_01.log and moment_01.log,
both with exactly the three standard axioms. The moment statement uses the actual
retained bp and HB, via the checked increment telescoping identity.
Integration into Cards.lean is compiling in cards_05.log.
CarriedMass first pass continues; occurrence geometry and scaled hinge are being checked.

09:43 UTC update: **14.5 carried_mass is PROVED** in carried_mass_04.log.
The exact card and all printed helpers have only `[propext, Classical.choice, Quot.sound]`.
The proof obtains the stronger M <= epsilon*K via an injective quotient map,
then derives both requested estimates. Cards.lean integration is compiling in cards_06.log.
First pass on the last requested leaf, 14.9 Feasibility, starts now.
Six lemma cards are proved: 14.2, 14.3, 14.4, 14.5, 14.7, 14.10.
The numerical adapter is compiling separately; the carrier-count assembly remains open.

## 09:48 UTC checkpoint (93 minutes elapsed)

- Seven of nine lemma cards are PROVED: 14.2 rounding, 14.3 hinge, 14.4 retained
  moment, 14.5 carried mass, 14.7 values, 14.8 uniform numerical, 14.10 window.
  Numerical.lean passed in numerical_01.log with the three standard axioms.
- Cards.lean integration through carried mass passed in cards_06.log. Numerical
  integration is now compiling in cards_07.log.
- Feasibility.lean has a complete proof candidate, with carrier_count explicitly
  OPEN as its prerequisite; feasibility_01.log is compiling. It is NOT yet proved.
- CarrierCount.lean return pass: the full generating-function and cardinality
  assembly is written and compiling in carrier_count_08.log. Its earlier checked
  helpers are reused. Do not mark the card PROVED before the final axiom check.
- The composition body remains proved from cards; sparse_core still has sorryAx
  while carrier count / feasibility are not closed. No cap is active.

09:51 UTC update: **14.6 carrier_count is PROVED** in carrier_count_08.log,
with exactly the three standard axioms. The first Feasibility proof passed in
feasibility_02.log conditional on that card. Its open prerequisite has now been
replaced with the checked count proof; feasibility_03.log is compiling.
All nine proofs have been assembled in Cards.lean with no explicit proof holes,
and final card/composition axiom checks are compiling in cards_08.log.
Do not claim final completion until both integration compiles finish successfully.

## Final checkpoint — 09:52:21 UTC

**COMPLETE. All nine Section 14 lemma cards and sparse_core are PROVED sorry-free.**
- feasibility_03.log: success, pointwise_feasibility has only the three standard axioms.
- cards_08.log: success, all nine cards and sparse_core print exactly
  `[propext, Classical.choice, Quot.sound]`; no sorryAx.
- statement_audit.txt: every leaf signature matches its card; all canonical
  definitions match; original atom system, target quantities and theorem are preserved.
- report.md gives the final per-card status and validation evidence.
- No outstanding proof goals remain. Elapsed time to final checked compile: 97m18s.
