# Erdős 708 threshold-17 Lean campaign

Completed: 2026-09-07T13:18:03.387349+00:00

All nine cards, the threshold-17 hinge inequality, the complete analytic tail, the parameterized conditional reduction, and `Erdos708H17.g_le_33n` are **PROVED**. Every audited theorem uses only `propext`, `Classical.choice`, and `Quot.sound` (or a subset). There are no open cards or admitted proof obligations.

## Formal statements and files

The development is confined to `lean/proofenv/Erdos708/H17/`. `Defs.lean` contains the copied atom system and the exact threshold-17 constructions. `Cards.lean` contains one statement per harvest lemma and the composition proof. `cards_readback.md` contains the nine blind readback lines. `Chain.lean` contains the parameterized `(c+16)n` reduction, its threshold-17 specialization, and the final theorem.

`hinge17` states, for every finite nonnegative prime-power atom system with per-prime total at most one and all natural `m,x`,

`∑ k ∈ Icc 1 m, max (S A k - 17) 0 ≤ ∑ b ∈ Icc (x+1) (x+m), max (S A b - 1) 0`.

`g_le_33n` states that for every `n ≥ 1`, every `n`-element finite set `A` of integers at least two, and every natural `x`, there exists a subset `B` of `Icc (x+1) (x+max A)` with `B.card ≤ 33*n` and `∏ A ∣ ∏ B`.

The original `Signed`, `Chain`, `Proofs`, `Final.lean`, and `SparseCore.lean` files were not edited. Required chain material was copied into `H17/ChainParts/` under a separate namespace. The weight-to-atom bridge uses threshold 17; the conditional proof is parameterized by the natural threshold `c`.

## Card status

Paths below are relative to `lean/proofenv/Erdos708/H17/`.

| Card | Status | Content | Main proof files |
|---|---|---|---|
| 1 | PROVED | Cube hinges, atom moments, mean monotonicity | `Proofs/Lemma1.lean; Proofs/Moment.lean` |
| 2 | PROVED | Deletion at 65536 and the small-m branch | `Proofs/Lemma2.lean` |
| 3 | PROVED | Dense branch and truncated first moment | `Proofs/Lemma3.lean` |
| 4 | PROVED | Dyadic rounding, loss six, cube cutoff | `Proofs/Lemma4.lean` |
| 5 | PROVED | Shortest carriers, exact mass, scale moments | `Proofs/Lemma5.lean and carrier helpers` |
| 6 | PROVED | Signed expansion, negative support, exact counting | `Proofs/Certificate.lean; Proofs/CarrierCount.lean; Proofs/Pointwise.lean` |
| 7 | PROVED | Seven finite scales and the complete analytic tail | `Proofs/Lemma7.lean; Proofs/NumericTables.lean; Proofs/Tail.lean` |
| 8 | PROVED | Window factor 62248/30583 | `Proofs/Lemma8.lean` |
| 9 | PROVED | Sparse completion | `Proofs/Lemma9.lean` |

Actual card and composition axiom output:

```text
'Erdos708H17.lemma1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos708H17.lemma2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos708H17.lemma3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos708H17.lemma4' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos708H17.lemma5' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos708H17.lemma6' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos708H17.lemma7' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos708H17.lemma8' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos708H17.lemma9' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos708H17.hinge17' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Exact numerical leaf

The polynomial coefficient recurrence is proved in `Proofs/CoefficientRecurrence.lean`. Generated integer rows are checked with `decide`; each of the 417 coefficient-ratio cases is checked with exact rational arithmetic by `norm_num`. Each scale then has one exact factorial-expression check. `exponentiation.threshold` is set to 1024 for the finite arithmetic, covering the required exponent 288. No `native_decide` or additional axioms are used.

| ell | N cases | Strict bound on 24 epsilon R |
|---|---:|---:|
| 1 | 5 | 51/100 |
| 2 | 8 | 6/25 |
| 4 | 14 | 3/100 |
| 8 | 27 | 1/250 |
| 16 | 53 | 1/2000 |
| 32 | 104 | 1/16000 |
| 64 | 206 | 1/100000 |

The seven-scale sum is below `313829/400000`. The analytic tail for `ell = 128*2^j` is fully proved, including the coefficient envelope, factorial lower bound, rational base inequalities, both counting ranges, geometric summability, and the strict tail bound `1/100`. Thus the full sum is below `317829/400000 < 4/5`.

Tail files: `Proofs/TailBasics.lean`, `Proofs/TailCoefficient.lean`, `Proofs/TailEstimates.lean`, `Proofs/TailLarge.lean`, and `Proofs/Tail.lean`. The separate tail card has been discharged.

The harvest's trailing strict inequality in Lemma 8 is false when `LB=0`. The formal card retains the exact factor bound `62248/30583 * LB ≤ window sum`, which holds also at zero and is sufficient for the completion. No positive-mass assumption was introduced.

## Chain audit

```text
'Erdos708H17Chain.Proofs.conditional_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos708H17.weighted_hinge17' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos708H17.conditional_33' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos708H17.g_le_33n' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Validation and reproduction

Compilation used the installed Lean `v4.34.0-rc1` directly with the existing mathlib objects. No internet, git, `lake update`, or `lake build` was used. Checkpoints were refreshed during the campaign; there was no wall-clock cap.

From the workspace root, reproduce the complete local dependency graph with:

```sh
python3 engine/out/astra_708_lean4/rebuild.py
```

To regenerate the explicit finite certificates and compile their separate scales:

```sh
python3 engine/out/astra_708_lean4/generate_numeric_tables.py
python3 engine/out/astra_708_lean4/compile.py Erdos708/H17/Proofs/NumericDefs.lean
python3 engine/out/astra_708_lean4/compile_numeric.py
```

`Cards.log`, `Chain.log`, `Lemma7.log`, `Tail.log`, and `NumericBounds0.log` through `NumericBounds6.log` contain the final compiler audits. `axiom_audit.json` records the checked theorem dependencies; `source_sha256.json` records hashes of the Lean sources and readback file. The earlier working logs are historical, not the final status.
