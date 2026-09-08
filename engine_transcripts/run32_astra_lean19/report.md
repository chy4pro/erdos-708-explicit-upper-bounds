# Erdős 708 Lean 19 campaign report

Completed: 2026-09-07 15:34:33 UTC. Started: 2026-09-07 15:21 UTC.

All seven targets are proved with their requested statements. In particular, `g_le_19n` is unconditional, while `g_le_12n_of_hinge` retains exactly the requested threshold-97/10 hinge hypothesis. No statement was weakened; strict rounding was proved.

## Modules

All new sources and their `.olean` files are under `lean/proofenv/Erdos708/H17/Chain19/`. Proved declarations use namespace `Erdos708H17Chain.Chain19`.

| Module | Contents | Validation |
| --- | --- | --- |
| Cards.lean | T1–T7 statement cards in namespace `Erdos708H17Chain.Chain19.Cards` | Compiled before proof development; seven intentional `sorry` bodies |
| Primes.lean | T1 `primes_card_le`, T2 `pi_le` | Compiled; allowed axioms only |
| Rounding.lean | Attainment of the fractional minimum, strict cube rounding, T3 `strict_rounding` | Compiled; allowed axioms only |
| Packing.lean | Three-bin packing and `split_integer3` | Compiled; allowed axioms only |
| Ksplit.lean | T4 `ksplit3` | Compiled; allowed axioms only |
| Bound.lean | Real-threshold dual estimate and T5 `bound_of_hinge` | Compiled; allowed axioms only |
| Results.lean | T6 `g_le_19n` and T7 `g_le_12n_of_hinge` | Compiled; allowed axioms only |

The proof modules do not import the new statement cards. Their source scan contains no `sorry`, `admit`, new `axiom` declaration, or `native_decide`.

## Proof details

- T1: choose a member of A divisible by each prime exceeding √m. Distinct such primes are coprime, and their product exceeds m, so the choice map is injective. Count the remaining primes in the initial range.
- T2: remove the prime 3 and map each remaining prime p ≤ 3n to p / 3 in `range n`. Primality, nondivisibility by 3, and parity make this map injective. This implements the elementary residue-counting argument; n = 0 is handled separately.
- T3: the feasible fractional covers form a nonempty compact subset of a finite cube, so their cost has a minimum. Apply the existing `cube_round` to a minimizer. A fractional coordinate makes the rounded-cardinality inequality strict; if there are no fractional coordinates, the positive number of prime constraints supplies strictness.
- T4: for C = m/H and m ≥ H², one has m ≤ C². If an atom exceeds C, isolate it and put the complementary product in a small bin. Otherwise, choose a first bin with product between √C and C; the remaining product satisfies the existing two-bin bound. This yields three demands per a, with only the first possibly a large atom. Existing prime transport and demand assembly give at most 3n representatives when H = 3n.
- T5: reproduce the dual estimate for real c. In the short-window case, T1 and T2 give r ≤ 2n + 1 and strict rounding gives |B| < cn + 2n + 1, hence |B| ≤ ⌈cn⌉ + 2n. In the long-window case, T4 gives 3n and c ≥ 1 completes the comparison.
- T6: instantiate T5 at c = 17 using the existing proved Hinge17 and its weighted conversion.
- T7: instantiate T5 at c = 97/10. `Nat.ceil_le` gives ⌈9.7n⌉ ≤ 10n for every natural n, so the final integer bound is 12n. No n = 1 or n = 2 exception is needed.

## Final axiom output

```text
'Erdos708H17Chain.Chain19.g_le_19n' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos708H17Chain.Chain19.g_le_12n_of_hinge' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All eleven printed proof declarations have the same allowed axiom set. Full output is in [axioms.txt](axioms.txt).

## Compilation and reproduction

The existing project `.olean` files are beside their source files. Plain `lake env lean` initially failed to find the Erdos708 prefix; setting `LEAN_PATH=.` resolves the imports without changing project configuration.

Run from `lean/proofenv`, in the module order listed above:

```sh
LEAN_PATH=. lake env lean -o Erdos708/H17/Chain19/<Module>.olean Erdos708/H17/Chain19/<Module>.lean
```

Every module was compiled individually during development and again in a final sequential pass. All seven final exit codes were zero. See [compile-summary.txt](compile-summary.txt) and the corresponding `<Module>.log` files. The card warnings are intentional; Results.lean reports only two harmless unused-variable-name warnings in its quantified statement binders.

## Scope and checkpoint record

Single agent throughout; no sub-agents, git commands, internet, new axioms, or native_decide. Existing Lean source modules were not edited. Deliverables are confined to Chain19/ and this output directory.

An initial checkpoint and progress/final updates were written to [checkpoint.md](checkpoint.md). Completion occurred before the first 30-minute deadline, so no periodic 30-minute checkpoint fell due.

Global-memory recall was unavailable because no `recall_presets` tool was exposed; this was disclosed before proof development.

Open targets: none. Weakened targets: none.
