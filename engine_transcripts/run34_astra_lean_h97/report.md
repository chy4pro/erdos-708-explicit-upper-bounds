# Erdős 708: completed H97 Lean campaign

Completed 2026-09-07 20:02 UTC. Single agent; no sub-agents, git, or internet. Existing project files were not edited. All new Lean sources are under `lean/proofenv/Erdos708/H97/`; campaign artifacts are in this report's directory.

`Erdos708H97.hinge97` proves the requested atom-system inequality at threshold **97/10**, for every atom system and all natural `m` and `x`, including `m = 0`. `Erdos708H97.weighted_hinge97` transfers it to the weighted formulation. `Erdos708H97.g_le_12n` applies the existing `Erdos708H17Chain.Chain19.g_le_12n_of_hinge` and proves the exact requested product-divisibility conclusion with `B.card ≤ 12*n`.

All **108 new modules** have compiled from their current source with Lean **v4.34.0-rc1** and Mathlib **de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11**. All nine proved lemma statements and the final hinge statement are checked again in `Audit.lean`; its statement signatures exactly match the original cards.

## Axioms and sorry disclosure

Actual output from `Chain.lean`:

```text
'Erdos708H97.hinge97' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos708H97.weighted_hinge97' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos708H97.g_le_12n' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every lemma audited in `Audit.lean` has the same three standard axioms. There are **no new axioms, no `native_decide`, and no proof-module `sorry` bodies**. As required, the separately compiled planning file `Cards.lean` retains **ten intentional `sorry` bodies**. No proof module imports it, and none of these placeholders is a dependency of the completed theorems.

No final statement was weakened. Lemmas 4 and 9 have no large-`m` hypothesis; the cofactor bound 210 replaces that assumption. The `m ≥ 2` condition is confined to the logarithmic rounding argument; the closing proof handles `m = 0,1` separately.

One interface detail is explicit: the counting reduction takes the exponential coefficient bound and tail summability as hypotheses, both subsequently proved in Lemma 8 and discharged in `Closing.lean`. The exponential substitute is proved directly for carrier coefficients, without assuming an inequality between it and the finite minimum of moment bounds. The weight-transfer helpers are restated for an arbitrary real threshold because the existing H17 helper statements themselves fix the threshold at 17.

## Exact numerical proof

All 29 finite scales are kernel-checked. Each `Numericj_LRows` certifies exact truncated polynomial coefficient rows for the full polynomial and the polynomial with exponent `j` omitted. Its paired `Numericj_L` verifies the selected admissible moment orders and rational bounds for every integer `N` up to the proved cutoff. Python generates candidate integer certificates and rational upper bounds; Lean verifies them and proves their connection to the mathematical definitions.

The large scales use `PackedRecurrence.lean`: polynomial rows are encoded as natural-number digits, with a proved carry bound, and each convolution is checked by exact multiplication and reduction modulo a power of the base. `ShortExponents.lean` proves that the shortened exponent enumeration is identical to the original one. These are ordinary kernel-checked proofs using `decide`/`decide +kernel`, not native evaluation.

`Lemma7.lean` proves the strict grouped bounds below and `finiteTotal < 187/1000`.

| h | L | Strict group bound |
|---|---|---|
| 2 | 4 | 24680 / 10^6 |
| 3 | 8 | 128711 / 10^6 |
| 4 | 16 | 25773 / 10^6 |
| 5 | 32 | 5665 / 10^6 |
| 6 | 64 | 1025 / 10^6 |
| 7 | 128 | 150 / 10^6 |
| 8 | 256 | 21 / 10^6 |
| 9 | 512 | 3 / 10^6 |

The infinite tail is summable and strictly below `3/1000`. The proof includes every requested exponential/rational constant, the four generating-series bounds, and inequality (21). The final margins are exact: `lambda*(187/1000+3/1000) = 969/1000 < 1`, and the window coefficient is `718539/573440 > 5/4`.

## Referee clarifications

All G1–G6 are proved where needed; see [gap_crosswalk.md](gap_crosswalk.md) for theorem locations and their uses. `LevelModel.lean` additionally proves that the finite representation preserves the retained levels of the manuscript's infinite level set.

## Build and audit evidence

A separate `Replay.lean` audit replays every imported H97 kernel declaration into a fresh environment containing only Mathlib and the existing H17 chain. This verifies reused proof terms against the current definitions. Lean’s replay API excludes compiler execution helpers such as `_unsafe_rec`; all mathematical declarations are checked by the kernel. The original Cards are outside this import closure. See [final_Replay.log](final_Replay.log) for the declaration count and explicit PASS result.

- [build_manifest.json](build_manifest.json): every new module, source hash, and compilation status. Completed current-source artifacts were reused in the final composition pass rather than rerunning expensive certificates.
- [inventory.json](inventory.json): complete source inventory, hashes, imports, current compiled-artifact checks, and the ten disclosed planning placeholders.
- [final_Chain.log](final_Chain.log), [final_Audit.log](final_Audit.log): final theorem and statement-card axiom output.
- `Numeric*.log`: numerical compilation logs.
- [numeric_caps.json](numeric_caps.json): exact per-scale rational upper bounds.
- [checkpoint.md](checkpoint.md): final checkpoint; it was updated during the campaign at intervals of at most 30 minutes.

Rebuild all new modules sequentially from source, from the repository root:

```sh
python3 engine/out/astra_708_lean_h97/build_all.py
python3 engine/out/astra_708_lean_h97/audit_campaign.py
```

The builder invokes `LEAN_PATH=. lake env lean -o <module>.olean <module>.lean` from `lean/proofenv`, in dependency order. The checked certificate sources are already present; regeneration is unnecessary for a rebuild. `generate_numeric.py` and `generate_packed.py` preserve the certificate-generation procedure.

## Complete module list

Paths below are relative to `lean/proofenv/Erdos708/H97/`. Each name denotes one compiled `.lean` file.

- `Audit.lean`
- `Cards.lean`
- `Chain.lean`
- `Defs.lean`
- `Proofs/Aggregation.lean`
- `Proofs/Capped.lean`
- `Proofs/CarrierBudget.lean`
- `Proofs/CarrierCore.lean`
- `Proofs/CarrierCount.lean`
- `Proofs/CarrierResidual.lean`
- `Proofs/Certificate.lean`
- `Proofs/Chernoff.lean`
- `Proofs/Closing.lean`
- `Proofs/CoefficientRecurrence.lean`
- `Proofs/Cofactor.lean`
- `Proofs/CountBounds.lean`
- `Proofs/CubeReduction.lean`
- `Proofs/ExactCount.lean`
- `Proofs/ExponentialMoment.lean`
- `Proofs/FastRecurrence.lean`
- `Proofs/GeneratingSeries.lean`
- `Proofs/Geometry.lean`
- `Proofs/Hinge.lean`
- `Proofs/Lemma1.lean`
- `Proofs/Lemma2.lean`
- `Proofs/Lemma3.lean`
- `Proofs/Lemma4.lean`
- `Proofs/Lemma5.lean`
- `Proofs/Lemma7.lean`
- `Proofs/Lemma8.lean`
- `Proofs/Lemma9.lean`
- `Proofs/LevelModel.lean`
- `Proofs/Levels.lean`
- `Proofs/MomentBasics.lean`
- `Proofs/Numeric4_128.lean`
- `Proofs/Numeric4_128Rows.lean`
- `Proofs/Numeric4_16.lean`
- `Proofs/Numeric4_16Rows.lean`
- `Proofs/Numeric4_256.lean`
- `Proofs/Numeric4_256Rows.lean`
- `Proofs/Numeric4_32.lean`
- `Proofs/Numeric4_32Rows.lean`
- `Proofs/Numeric4_4.lean`
- `Proofs/Numeric4_4Rows.lean`
- `Proofs/Numeric4_512.lean`
- `Proofs/Numeric4_512Rows.lean`
- `Proofs/Numeric4_64.lean`
- `Proofs/Numeric4_64Rows.lean`
- `Proofs/Numeric4_8.lean`
- `Proofs/Numeric4_8Rows.lean`
- `Proofs/Numeric5_128.lean`
- `Proofs/Numeric5_128Rows.lean`
- `Proofs/Numeric5_16.lean`
- `Proofs/Numeric5_16Rows.lean`
- `Proofs/Numeric5_256.lean`
- `Proofs/Numeric5_256Rows.lean`
- `Proofs/Numeric5_32.lean`
- `Proofs/Numeric5_32Rows.lean`
- `Proofs/Numeric5_512.lean`
- `Proofs/Numeric5_512Rows.lean`
- `Proofs/Numeric5_64.lean`
- `Proofs/Numeric5_64Rows.lean`
- `Proofs/Numeric5_8.lean`
- `Proofs/Numeric5_8Rows.lean`
- `Proofs/Numeric6_128.lean`
- `Proofs/Numeric6_128Rows.lean`
- `Proofs/Numeric6_16.lean`
- `Proofs/Numeric6_16Rows.lean`
- `Proofs/Numeric6_256.lean`
- `Proofs/Numeric6_256Rows.lean`
- `Proofs/Numeric6_32.lean`
- `Proofs/Numeric6_32Rows.lean`
- `Proofs/Numeric6_512.lean`
- `Proofs/Numeric6_512Rows.lean`
- `Proofs/Numeric6_64.lean`
- `Proofs/Numeric6_64Rows.lean`
- `Proofs/Numeric6_8.lean`
- `Proofs/Numeric6_8Rows.lean`
- `Proofs/Numeric7_128.lean`
- `Proofs/Numeric7_128Rows.lean`
- `Proofs/Numeric7_16.lean`
- `Proofs/Numeric7_16Rows.lean`
- `Proofs/Numeric7_256.lean`
- `Proofs/Numeric7_256Rows.lean`
- `Proofs/Numeric7_32.lean`
- `Proofs/Numeric7_32Rows.lean`
- `Proofs/Numeric7_512.lean`
- `Proofs/Numeric7_512Rows.lean`
- `Proofs/Numeric7_64.lean`
- `Proofs/Numeric7_64Rows.lean`
- `Proofs/Numeric7_8.lean`
- `Proofs/Numeric7_8Rows.lean`
- `Proofs/NumericDefs.lean`
- `Proofs/PackedRecurrence.lean`
- `Proofs/PointwiseSupport.lean`
- `Proofs/Retention.lean`
- `Proofs/RoundedBasics.lean`
- `Proofs/Rounding.lean`
- `Proofs/ScalarConstants.lean`
- `Proofs/ScalarHinge.lean`
- `Proofs/ScaleEstimates.lean`
- `Proofs/ScaleGeometry.lean`
- `Proofs/ShortExponents.lean`
- `Proofs/TailCoefficient.lean`
- `Proofs/TailScale.lean`
- `Proofs/TailSum.lean`
- `Proofs/WeightTransfer.lean`
- `Replay.lean`
