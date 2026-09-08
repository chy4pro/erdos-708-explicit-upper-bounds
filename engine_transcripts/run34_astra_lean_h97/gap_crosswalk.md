# Referee clarification crosswalk

All paths below are relative to `lean/proofenv/Erdos708/H97/Proofs/`.

| Gap | Formal facts and use |
|---|---|
| G1 | `RoundedBasics.bp_le_one` proves every rounded prime component is at most one. `Cofactor.source_cofactor_ge_210` uses it to obtain four distinct outside primes and cofactor at least 210. `Lemma4` has no large-m hypothesis. |
| G2 | `RoundedBasics.rounded_current_level` constructs a first rounded crossing whose modulus divides the source integer, using the maximal occurring exponent and the minimal crossing exponent. `Rounding.local_rounding_cost` and `S_le_rounded` explicitly require `2 ≤ m`, establishing positive logarithms. `Lemma2.tiny_hinge_zero` disposes of m=0 and m=1. `LevelModel.retained_level_dominated` checks preservation of all retained levels by the finite representation. |
| G3 | `ScaleGeometry.levelDegree_eq` proves the exact integer multiple of 1/L; `levelDegree_mem` places it in the exponent set. `carrier_degree_bounds` proves total mass is 1+d/L with 1 ≤ d ≤ j. |
| G4 | `GeneratingSeries.finite_generating_le` embeds every exponent of the finite polynomial into the series, including the exponent L from level 1. `generating_series_upper` bounds the remaining bands by a geometric series through an explicit ordered exponent lower bound; it does not need to assume distinctness. `generating_series_bound` verifies the four requested rational bounds. |
| G5 | `ScaleGeometry.carrier_height_injective` proves uniqueness at a given prime and level. `CarrierCount.carrier_count_exact` uses it to recover the selected atoms and the carrier modulus from the assignment. |
| G6 | `CubeReduction.cube_lower` iterates endpoint replacement one coordinate at a time. `ScalarHinge.optimized_vertex_bound` handles h<r via h≤r−1≤a. `optimized_hinge` combines this with the exact maximizing vertex floor. |

The tail bound is applied directly to carrier coefficients, separately from the finite minimum of moment bounds. No claim that the finite minimum is bounded by the exponential substitute is used.

The final transfer uses `Erdos708H17Chain.Chain19.g_le_12n_of_hinge`, as required by the brief; this is the existing 12n chain, addressing the referee's G8 distinction from the older 16n rounding cost.
