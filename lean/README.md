# Lean 4 formalisation of `g(n) ≤ 81 n` (Erdős Problem #708)

Kernel-checked development of the paper's main linear bound, produced on 2026-09-07 by GPT-6 Astra (OpenAI, via the
codex CLI) in three campaigns driven by the orchestrating agent (Claude Fable 5.1), and independently recompiled by the
orchestrator. Every theorem below depends only on Lean's three standard axioms `propext`, `Classical.choice`, `Quot.sound`;
no `sorry`, `admit`, `native_decide` or custom axiom occurs anywhere.

Toolchain: `leanprover/lean4:v4.34.0-rc1`, Mathlib commit `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11` (see `lean-toolchain`).

## Layout

| Path | Content | Paper |
|---|---|---|
| `Erdos708/SparseCore.lean` | statement cards: `AtomSystem`, `S0`, `mean`, `L`, `R`, the sparse-core theorem and three milestone lemmas (with `sorry`) | §14, Thm 14.1, Lemmas 14.3/14.4/14.8 |
| `Erdos708/Proofs/{Numerical,Hinge,Moment}.lean` | standalone proofs of the three milestone lemmas | Lemmas 14.8, 14.3, 14.4 |
| `Erdos708/Signed/Defs.lean` | dyadic rounding, retained levels, carriers, the signed certificate `F` | §14 definitions |
| `Erdos708/Signed/Proofs/*.lean` | standalone proofs of Lemmas 14.2, 14.5, 14.6, 14.7, 14.9, 14.10 (and 14.3/14.4/14.8 again) | §14 |
| `Erdos708/Signed/Cards.lean` | **self-contained** (`import Mathlib` only): all nine lemmas and `Erdos708SparseCore.sparse_core` | Thm 14.1 |
| `Erdos708/Chain/*.lean` | the reduction chain: large atoms, dense branch, LP duality, rounding, few primes, long intervals, the threshold-65 conditional theorem; `Erdos708Chain.linear_bound` from the hypothesis `sparse_core_hyp` | §5, §7, §13 |
| `Erdos708/Final.lean` | bridge: `sparse_core` ⇒ `sparse_core_hyp`, hence the unconditional `Erdos708Final.g_le_81n` | Thm 14.11 |
| `Erdos708/H17/` | the threshold-17 development (Section 15): `Defs.lean`, `Cards.lean` (nine lemma cards + `hinge17`), `Proofs/*.lean` (incl. the exact numerical tables and the analytic tail), `ChainParts/` (copy of the reduction chain in its own namespace) and `Chain.lean` with the parametrised `(c+16)n` reduction and `Erdos708H17.g_le_33n` | §15, Thm 15.1 |
| `Erdos708/H17/Chain19/` | the (c+2)n reduction (Section 16): `Primes.lean` (r ≤ n + π(√m), π(3n) ≤ n+1), `Rounding.lean` (strict vertex rounding), `Packing.lean`/`Ksplit.lean` (k = 3 split), `Bound.lean` (`bound_of_hinge` for real c ≥ 1: ⌈cn⌉ + 2n), `Results.lean` (`g_le_19n`, conditional `g_le_12n_of_hinge` at threshold 97/10); build with `LEAN_PATH=. lake env lean` in the listed order | §16, Thm 16.1, Cor 16.2 |
| `Erdos708/H97/` | the threshold-97/10 development (Section 17): `Defs.lean`, `Cards.lean` (nine lemma cards + `hinge97`; planning file with `sorry`, imported by nothing), `Proofs/*.lean` (lemmas, exact numeric certificates `Numeric{j}_{L}Rows.lean`/`Numeric{j}_{L}.lean` for the 29 scales — the L = 256/512 rows are tens of MB — `PackedRecurrence`, `ShortExponents`, `Closing`, `Hinge`, `WeightTransfer`), `Chain.lean` (`Erdos708H97.g_le_12n`), `Audit.lean`, `Replay.lean`; build in import order with `LEAN_PATH=. lake env lean` (about 70 min, the large scales take minutes each) | §17, Thm 17.1, Cor 17.2 |

The final statement (`Erdos708Final.g_le_81n`): for every `n ≥ 1`, every set `A` of `n` integers `≥ 2` and every `x`,
there is `B ⊆ {x+1, …, x + max A}` with `|B| ≤ 81 n` and `∏ A ∣ ∏ B`.

## Rebuild

```
# inside a Lake project with the pinned Mathlib built (e.g. `lake exe cache get`), copy Erdos708/ to the project root
lake env lean Erdos708/Signed/Cards.lean          # self-contained; prints the axioms of all §14 theorems
LEAN=$(lake env which lean); LP="$(pwd):$(pwd)/.lake/build/lib/lean:$(ls -d .lake/packages/*/.lake/build/lib/lean | tr '\n' ':')"
for m in Defs Arithmetic Proofs/LargeAtoms Atoms Proofs/FewPrimes Proofs/LongInterval Proofs/Rounding LP Proofs/Dual Weights Proofs/Dense Proofs/Conditional81 Proofs/Hinge65 Cards; do
  LEAN_PATH=$LP $LEAN -o Erdos708/Chain/$m.olean Erdos708/Chain/$m.lean; done
LEAN_PATH=$LP $LEAN -o Erdos708/Signed/Cards.olean Erdos708/Signed/Cards.lean
LEAN_PATH=$LP $LEAN Erdos708/Final.lean             # prints: 'Erdos708Final.g_le_81n' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Provenance and checks

Campaign briefs, checkpoints, reports and blind read-backs of every statement card are in
`../engine_transcripts/run29_astra_lean/`. The three milestone lemmas and the sparse-core theorem were also verified
server-side by the Prove2Me platform (mission "Erdős 708: the sparse-core inequality", theorems
`Erdos708SparseCore.{hinge_le_esymm, moment_bound, numerical_bound, sparse_core}`).
Definitions were read against the paper by the orchestrator; the composition theorems contain no proof holes; the axiom
audit above is the whole trust basis.
