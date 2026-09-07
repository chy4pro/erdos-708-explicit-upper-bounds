# Erdős 708 sparse-core Lean campaign — final report

**Result: all three milestone theorems PROVED, with their exact original statements.**

Started: 2026-09-07 07:33:48 UTC.
Proofs complete: 2026-09-07 07:44:00 UTC.
Proof campaign elapsed: 10 minutes 12 seconds (hard cap: 2 hours).

Environment: Lean 4.34.0-rc1, project `lean/proofenv`.
Each file starts with `import Mathlib`, opens `Finset BigOperators`, is self-contained,
and includes a final `#print axioms` for its milestone theorem.

## Numerical — PROVED

File: `lean/proofenv/Erdos708/Proofs/Numerical.lean`

Theorem: `Erdos708SparseCore.numerical_bound`

Proof: use `Stirling.le_factorial_stirling`, bound `exp 1 ≤ 11/4`, and check
`(187/768)^12 * 2^23 ≤ 1/2` by `norm_num`. Factor the numerator into a factorial-bound
term and a geometric term. Use `t ≥ 1` and the factorial successor identity to obtain
`17/416`.

Successful command, from `lean/proofenv`:

```text
lake env lean Erdos708/Proofs/Numerical.lean
```

Exact axiom output (`numerical_02.log`):

```text
'Erdos708SparseCore.numerical_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Hinge — PROVED

File: `lean/proofenv/Erdos708/Proofs/Hinge.lean`

Theorem: `Erdos708SparseCore.hinge_le_esymm`

Proof: establish the elementary-symmetric insertion recurrence directly using
`powersetCard_succ_insert`. Induct on the finite coordinate set, generalizing the
threshold. Combine the two adjacent-threshold induction hypotheses with nonnegative
coefficients `1 - x a` and `x a`; finish with nonnegativity of the symmetric sums.

Successful command, from `lean/proofenv`:

```text
lake env lean Erdos708/Proofs/Hinge.lean
```

Exact axiom output (`hinge_02.log`):

```text
'Erdos708SparseCore.hinge_le_esymm' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Moment — PROVED

File: `lean/proofenv/Erdos708/Proofs/Moment.lean`

Theorem: `Erdos708SparseCore.moment_bound`

Proof:

1. Prove `r! * e_r(x) ≤ (Σ x)^r` by finite-set induction, the insertion recurrence,
   and `pow_add_mul_le_add_pow`.
2. For pairwise coprime moduli, identify simultaneous divisibility with divisibility
   by their product. Count the relevant positive integers using `Nat.card_multiples'`
   and bound natural division by real division using `Nat.cast_div_le`.
3. Expand products of level sums with `Finset.prod_sum`, swap sums, and apply
   `Nat.coprime_pow_primes` to each choice of levels.
4. Sum over `P.powersetCard r` and apply the symmetric-sum estimate.

Successful command, from `lean/proofenv`:

```text
lake env lean Erdos708/Proofs/Moment.lean
```

Exact axiom output (`moment_01.log`):

```text
'Erdos708SparseCore.moment_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The compiler emits only unused-variable warnings for `hN` and `hr`: the proof works
without these restrictions. Their names, binders, and hypotheses are preserved exactly
as required.

## Validation and compilation log

`statement_audit.txt` records that all three theorem declarations match
`Erdos708/SparseCore.lean`, ignoring only whitespace. Names, binders, hypotheses,
and conclusions are unchanged. The audit found no occurrences of `sorry`, `admit`,
`native_decide`, `decide`, `axiom`, or `unsafe` in any of the three proof files.
The axiom outputs above independently confirm the absence of unproved dependencies.

Every source change was immediately followed by `lake env lean`:

| Log | Result |
| --- | --- |
| `numerical_01.log` | Failed: Stirling namespace and one local inequality argument. |
| `numerical_02.log` | Passed; final Numerical file. |
| `hinge_01.log` | Failed: empty-set base case required an explicit powerset-cardinality argument. |
| `hinge_02.log` | Passed; final Hinge file. |
| `moment_01.log` | Passed; final Moment file, with the two unused-hypothesis warnings noted above. |

No milestone remains open. No changes were made to the original statement file.
All authored files are under `Erdos708/Proofs/` or `engine/out/astra_708_lean/`.
No git commands, `lake update`, or `lake build` were run.

`checkpoint.md` was initialized and updated during the campaign, with a completion
checkpoint below the 30-minute reporting interval. Global-memory recall could not
run because the session exposed no `recall_presets` tool; this was disclosed before
proof work.
