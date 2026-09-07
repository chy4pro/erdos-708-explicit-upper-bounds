# Erdős 708 Lean reduction campaign — complete

Completed: 2026-09-07 09:44 UTC. Started 2026-09-07 08:49 UTC. No wall-clock cap was imposed; all cards were discharged.

## Result

**PROVED:** `Erdos708Chain.linear_bound`, conditional on the explicit proposition `sparse_core_hyp`.

```lean
theorem Erdos708Chain.linear_bound (hsc : sparse_core_hyp) :
  ∀ (n : ℕ) (hn : 1 ≤ n), ∀ (A : Finset ℕ)
    (hA : A.card = n) (h2 : ∀ a ∈ A, 2 ≤ a) (x : ℕ),
    ∃ B ⊆ Finset.Icc (x+1) (x + A.max' ...),
      B.card ≤ 81 * n ∧ (∏ a ∈ A, a) ∣ (∏ b ∈ B, b)
```

The actual source supplies the nonemptiness proof in `A.max'`; the ellipsis above only abbreviates that proof for display. Section 1 explicitly uses **at most g(n)**, so no padding or exact-cardinality convention is imposed.

The sole external hypothesis has exactly the independent Section-14 theorem's type:

```lean
∀ (A : AtomSystem) (m : ℕ) (hm : 4096 < m)
  (hH : mean A < 17 / 16) (x : ℕ),
  (141 / 128 : ℝ) * L A m ≤ R A x m
```

`AtomSystem`, `S0`, `mean`, `L`, and `R`, including their documentation and bodies, were copied verbatim into `Erdos708Chain`. The audit verifies that exact block. The sparse-core theorem itself remains the explicit input to this independent reduction campaign.

Entry point: `lean/proofenv/Erdos708/Chain/Cards.lean`.

## Card status

All seven requested leaves and the sparse-core reduction card are proved. There are **no OPEN cards** and no remaining proof goals.

| Card | Leaf | Status | Axiom output |
|---|---|---|---|
| `large_atoms` | `Proofs/LargeAtoms.lean` | PROVED | `[propext, Classical.choice, Quot.sound]` |
| `few_primes` | `Proofs/FewPrimes.lean` | PROVED | `[propext, Classical.choice, Quot.sound]` |
| `long_interval` | `Proofs/LongInterval.lean` | PROVED | `[propext, Classical.choice, Quot.sound]` |
| `rounding` | `Proofs/Rounding.lean` | PROVED | `[propext, Classical.choice, Quot.sound]` |
| `dual` | `Proofs/Dual.lean` | PROVED | `[propext, Classical.choice, Quot.sound]` |
| `dense` | `Proofs/Dense.lean` | PROVED | `[propext, Classical.choice, Quot.sound]` |
| `conditional_81` | `Proofs/Conditional81.lean` | PROVED | `[propext, Classical.choice, Quot.sound]` |
| `hinge_65_of_sparse_core` | `Proofs/Hinge65.lean` | PROVED | `[propext, Classical.choice, Quot.sound]` |
| `linear_bound` | `Cards.lean` | PROVED | `[propext, Classical.choice, Quot.sound]` |

Final assembled axiom output:

```text
'Erdos708Chain.large_atoms' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos708Chain.dense' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos708Chain.hinge_65_of_sparse_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos708Chain.dual' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos708Chain.rounding' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos708Chain.few_primes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos708Chain.long_interval' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos708Chain.conditional_81' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos708Chain.linear_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Each leaf ends with its own `#print axioms` checks. The corresponding `LargeAtoms.log`, `FewPrimes.log`, `LongInterval.log`, `Rounding.log`, `Dual.log`, `Dense.log`, `Conditional81.log`, and `Hinge65.log` contain the leaf outputs. `Cards.log` and `axioms.txt` contain the assembled outputs.

## Proof details

- **Large atoms:** two powers of distinct primes above m/64 cannot both divide a positive k ≤ m when m ≥ 4096. Grouping the active atoms by prime gives the unit bound and both hinge comparisons.
- **Few primes:** an elementary tail-product estimate replaces logarithms and Stirling estimates. If there were at least 16n primes, at least 4n would exceed 4n, forcing a product at least `(4n)^(4n) > (8n^3)^n`.
- **Long intervals:** the two-bin packing lemma is proved using the equivalent squared hypothesis `P² ≤ C³`. It yields two demands per input. Hall's theorem provides primewise injective representatives for large demands and separate representatives for small demands. Coprime products within fibers establish divisibility by the product of a set, with cardinality at most 2n.
- **Rounding:** linear dependence supplies a nonzero direction preserving the covering rows and not increasing cost. Moving to a cube boundary and inducting on the fractional-coordinate count leaves at most |P| fractional coordinates. Rounding the support gives the exact cardinality bound. A minimum-cardinality covering subset and the infimum property finish the LP-value statement.
- **Duality:** a finite-dimensional separation proof establishes the required strong-duality inequality. The feasible cube's affine image plus the nonnegative orthant is closed and convex; separation produces nonnegative multipliers with positive cost coefficient. Coordinatewise clipping at 1 does not decrease the dual objective. Compactness of the unit cube supplies a maximizer for the full nonnegative dual.
- **Dense branch:** the exact first-moment formulas, coprime mixed moments, and per-prime unit bound give `Σ T² ≤ m(H+H²)`. Greedy selection gives `17/16 ≤ H ≤ 25/16`. The lower first moment and `min(t,64) ≥ t - t²/256` give `Σ min(S0,64) ≥ m`, completing the affine certificate.
- **Weights and peel:** finite atoms use the exact alpha increments. Telescoping valuations proves agreement with the capped weight on the initial interval and domination by the capped weight on the window. Nonnegative excess increments give the window inequality for E, and the identities for `w = E + S` transfer the threshold-65 hinge.
- **Composition:** small windows are handled by the prime-factor-count bound; large windows split at mean 17/16 between the dense leaf and `sparse_core_hyp`. The latter's factor 141/128 is weakened using nonnegativity of L. The threshold-65 conditional theorem uses the proved duality, rounding, few-primes, and long-interval leaves to obtain 81n.

## Statement-first and validation

`cards_initial.lean.txt` preserves the initial statement-first cards and the composition proof; `cards_initial.log` records their initial compilation. `cards_readback.md` gives one readback line per card. The final card types are textually identical to the initial types, and all eight leaf theorem types match their cards exactly. These checks are recorded in `audit.json`, together with SHA-256 hashes of the final sources.

All 14 source files (2126 lines) were freshly compiled in dependency order using the installed Lean 4.34.0-rc1 and already-built Mathlib. Compilation succeeded. Remaining compiler messages are deprecation/style/unused-variable notices; every requested theorem's axiom check is exactly the standard three axioms.

Reproduce from the repository root:

```sh
python3 engine/out/astra_708_lean3/compile.py \
  Defs Proofs/LargeAtoms Proofs/FewPrimes Arithmetic \
  Proofs/LongInterval Proofs/Rounding LP Proofs/Dual \
  Atoms Weights Proofs/Dense Proofs/Conditional81 Proofs/Hinge65 Cards
```

The helper sets `LEAN_PATH` to the project and existing dependency olean directories and invokes the installed Lean binary directly. It does not build or update dependencies.

The source audit found no `sorry`, `admit`, `native_decide`, `sorryAx`, or custom axiom declaration in `Chain/`. All Erdős-708 imports stay within `Erdos708.Chain`. No edits were made to `Erdos708/Signed/`, `Erdos708/Proofs/`, or `Erdos708/SparseCore.lean`. No git commands, internet access, or subagents were used. Global-memory recall was unavailable because its tool was not exposed in this session.
