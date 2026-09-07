# PROOF CAMPAIGN (Lean 4) — Erdős 708: formalise the threshold-17 hinge inequality and derive g(n) ≤ 33n (no wall-clock cap)

Source of the mathematics: /Users/roychen/workspace/claudecode/automath/engine/harvest/erdos708_r17_pro.md (Lemmas 1–9, a proof of
(H_17): Σ_{k≤m}(S(k) − 17)^+ ≤ Σ_{b∈I}(S(b) − 1)^+ for every finite nonnegative prime-power atom system with per-prime total ≤ 1, every m ≥ 1
and every window of m consecutive positive integers). Its constants are verified by engine/out/pro_708_r17/verify_constants.py. It mirrors
the Section-14 development you already formalised (lean/proofenv/Erdos708/Signed/Cards.lean) with tightened constants: split at p^j ≤ m/2^16,
cutoff q^{3/t} ≤ m (loss 6), carriers of mass exactly 1+θ, exact carrier count C_ℓ(N) = [X^{ℓ+1}](1+X+X²+X⁴+…+X^ℓ)^N, certificate
F = 24 Σ c_C [P_C | n](1 − U_C/K) with K = 35/16, pointwise F ≤ (4/5)(B−1)^+, window value ≥ (62248/30583) L_B.

Project lean/proofenv (never lake update/build). Your directory: Erdos708/H17/ (create). Do not touch Erdos708/Signed, Chain, Proofs, Final.lean,
SparseCore.lean; you may READ and COPY from them (the AtomSystem/S0 definitions, the hinge/moment lemmas, the rounding and counting techniques).

Method (statement-first, as before):
1. Erdos708/H17/Defs.lean: the atom system (reuse Erdos708SparseCore.AtomSystem by verbatim copy into namespace Erdos708H17), S, S_0 (split at
   2^16 · p^j ≤ m), H, the rounding with cutoff q^(3/t) ≤ m (3·2^h exponent), b_p, B, L_B = Σ_{k≤m}(B(k) − 11/2)^+, carriers (shortest prefix with
   mass > 1), θ_C, P_C, ν_C, M_C, c_C, U_C, F, the counting polynomial coefficient C_ℓ(N), R_ℓ, ε_ℓ.
2. Erdos708/H17/Cards.lean: one card per Lemma 1–9 of the harvest (faithful; `:= by sorry`), plus the theorem
   `hinge17 : ∀ A m x, Σ_{k∈Icc 1 m}(S A k − 17)^+ ≤ Σ_{b∈Icc (x+1) (x+m)}(S A b − 1)^+` proved from the cards (no sorry in the composition),
   and cards_readback.md (one blind line per card).
3. Leaves in order: Lemma 1 (reuse your hinge/moment proofs), Lemma 2, Lemma 4, Lemma 3, Lemma 5, Lemma 6, Lemma 8, Lemma 7 (exact rationals:
   norm_num/decide on the seven finite cases via the recurrence, and the analytic tail — this is the hardest leaf; if it resists, leave the
   TAIL as a separate card with the exact remaining goal), Lemma 9.
4. Chain variant: in Erdos708/H17/Chain.lean copy the reduction from Erdos708/Chain (Problem, FractionalCover, dual, rounding, few_primes,
   long_interval, conditional) but with threshold 17 in place of 65: `conditional_33 : Hinge17 → ∀ D, ∃ B, Covers D B ∧ B.card ≤ 33 * D.n`, and
   the final `Erdos708H17.g_le_33n` from hinge17 (bridge like Erdos708/Final.lean). The paper's Theorem cond with threshold c gives (c+16)n —
   check where 65 enters your existing Conditional81.lean and parametrise.
Rules: compile after every change; PROVED only sorry-free with the three standard axioms; checkpoint.md every 30 minutes and report.md at the end
under engine/out/astra_708_lean4/ (per card PROVED with axiom output / OPEN with the remaining goal); no wall-clock cap; no git; no internet.
