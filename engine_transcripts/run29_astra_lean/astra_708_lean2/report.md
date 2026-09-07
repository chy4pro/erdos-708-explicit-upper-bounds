**Completed: all nine Section 14 lemma cards and Theorem 14.1 `sparse_core` are PROVED, sorry-free.**

Campaign start: 2026-09-07 08:15:03 UTC. Final successful compilation checked:
2026-09-07 09:52:21 UTC. Elapsed: 1 hour 37 minutes 18 seconds.
The user lifted the original two-hour cap during the campaign.

The complete self-contained development is
[Cards.lean](../../../lean/proofenv/Erdos708/Signed/Cards.lean).
It proves the original statement
`(141 / 128 : ℝ) * L A m ≤ R A x m`
for every original atom system, `m > 4096`, `mean A < 17/16`, and natural `x`.
No extra assumptions were added to the target theorem.

| Card | Declaration | Status | Standalone leaf | Successful log |
|---|---|---|---|---|
| 14.2 | `rounding` | **PROVED** | [Rounding.lean](../../../lean/proofenv/Erdos708/Signed/Proofs/Rounding.lean) | [rounding_05.log](rounding_05.log) |
| 14.3 | `hinge_le_esymm` | **PROVED** | [Hinge.lean](../../../lean/proofenv/Erdos708/Signed/Proofs/Hinge.lean) | [hinge_01.log](hinge_01.log) |
| 14.4 | `moment_retained` | **PROVED** | [Moment.lean](../../../lean/proofenv/Erdos708/Signed/Proofs/Moment.lean) | [moment_01.log](moment_01.log) |
| 14.5 | `carried_mass` | **PROVED** | [CarriedMass.lean](../../../lean/proofenv/Erdos708/Signed/Proofs/CarriedMass.lean) | [carried_mass_04.log](carried_mass_04.log) |
| 14.6 | `carrier_count` | **PROVED** | [CarrierCount.lean](../../../lean/proofenv/Erdos708/Signed/Proofs/CarrierCount.lean) | [carrier_count_08.log](carrier_count_08.log) |
| 14.7 | `values_at_point` | **PROVED** | [Values.lean](../../../lean/proofenv/Erdos708/Signed/Proofs/Values.lean) | [values_03.log](values_03.log) |
| 14.8 | `uniform_numerical` | **PROVED** | [Numerical.lean](../../../lean/proofenv/Erdos708/Signed/Proofs/Numerical.lean) | [numerical_01.log](numerical_01.log) |
| 14.9 | `pointwise_feasibility` | **PROVED** | [Feasibility.lean](../../../lean/proofenv/Erdos708/Signed/Proofs/Feasibility.lean) | [feasibility_03.log](feasibility_03.log) |
| 14.10 | `value_on_window` | **PROVED** | [Window.lean](../../../lean/proofenv/Erdos708/Signed/Proofs/Window.lean) | [window_06.log](window_06.log) |
| 14.1 | `sparse_core` | **PROVED** | [Cards.lean](../../../lean/proofenv/Erdos708/Signed/Cards.lean) | [cards_08.log](cards_08.log) |

Final `#print axioms` output from `cards_08.log`:

```text
'Erdos708SparseCore.rounding' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos708SparseCore.hinge_le_esymm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos708SparseCore.moment_retained' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos708SparseCore.carried_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos708SparseCore.carrier_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos708SparseCore.values_at_point' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos708SparseCore.uniform_numerical' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos708SparseCore.pointwise_feasibility' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos708SparseCore.value_on_window' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos708SparseCore.sparse_core' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The development follows the concrete construction in `papers/erdos708/sec_signed.tex`:
cumulative-weight dyadic rounding; first occurrence of each rounded value;
the integer cutoff `q^(16*2^h) ≤ m`; retained increments and effective levels;
ordered prefixes and interval-length weights; carrier masses and coefficients;
and the clipped signed divisor certificate. The window card includes the finite
signed expansion, both modulus-support assertions, coefficient independence from
the window, and the `141/64` lower bound. The composition applies rounding,
pointwise feasibility, and the window card.

CarriedMass proves the stronger intermediate inequality `M(P) ≤ epsilon * K(P)`
by injecting occurrences into quotient integers and applying the retained moment
bound. CarrierCount uses the weighted subset family bound and the per-prime
dyadic generating sum. Its first pass was left OPEN at approximately 25 minutes;
the recorded goal was fully resolved on the return pass.

Validation used `lake env lean <file>` from `lean/proofenv` after every Lean
change. The final standalone leaf and integrated Cards compilations all succeeded.
Remaining compiler messages are deprecation and unused-tactic/variable lint warnings.
There are no open cards, proof holes, `admit`, `native_decide`, or custom axioms.

[statement_audit.txt](statement_audit.txt) confirms that every leaf has the exact
card signature and the same canonical definitions. It also confirms that
`AtomSystem`, `S0`, `mean`, `L`, `R`, and the target theorem statement preserve the
original statement card exactly, ignoring whitespace. The initial blind read-backs
are in [cards_readback.md](cards_readback.md). SHA-256 hashes of the eleven campaign deliverables are in
[artifact_hashes.txt](artifact_hashes.txt).

[checkpoint.md](checkpoint.md) records the campaign progress and final state.
Only `Erdos708/Signed/` and this output directory were written. No git commands,
internet access, `lake build`, or `lake update` were used. The original
`Erdos708/SparseCore.lean` statement-card file remains untouched, as required by the
write-scope restriction. The completed proof is delivered in `Signed/Cards.lean`.
Global-memory recall was unavailable in the session, as disclosed at the start.
