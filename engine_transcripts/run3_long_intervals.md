# Q21 HARVEST — Erdős #708 Conjecture-S single-shot, Qwen3.8-Max, chat 177765a1, harvested 2026-09-03 23:1x CDT via Copy+pbpaste (raw: erdos708_qwen_S_raw.md, 17.4KB)
# VERDICT (dialogue audit): CORRECT. Theorem C: if a_n ≥ 8n³ then S holds with ≤ 2n elements (so g ≤ 2n in that regime); with the whole-interval fallback, g(n) ≤ 8n³. One written slip (Lemma 3 step 1: "C² ≥ 16n⁴ > M" should read C² = M²/(4n²) ≥ M since M ≥ 4n²); conclusion unaffected.

## Clean transcription
Assume M = a_n ≥ 8n³ and put C = M/(2n) (so C ≥ M^{2/3} and C ≥ 4n² ≥ 2n).
L2 (two-bin packing). If q_1..q_r > 1 are integers ≤ C with product P ≤ C^{3/2}, some subproduct s satisfies P/C ≤ s ≤ C
(if some q_i > √C take s = q_i, since √C ≥ P/C; otherwise multiply in any order until the partial product first reaches
P/C: then s < (P/C)√C = P/√C ≤ C). Hence the q_i split into two classes with products ≤ C.
L3 (split). Each a ∈ A has at most one prime-power factor > C (two would give a > C² ≥ M). If q = p^e > C is that factor,
split a = q · (a/q) with a/q < M/C = 2n ≤ C. Otherwise all prime-power factors are ≤ C and a ≤ M ≤ C^{3/2}, so L2 splits
them into two coprime parts ≤ C. Demands: ≤ 2n in total; large ones are prime powers > C, small ones are ≤ C.
L4 (large demands). Per prime, assign the p-power demands injectively to multiples with enough valuation (nested Hall /
greedy by exponent: the j largest exponents come from j distinct a's divisible by p^{e_j}, so ≥ j multiples exist).
Different primes may share an element.
L5 (small demands). Each small d ≤ C has ≥ ⌊M/d⌋ ≥ 2n multiples in I; at most 2n − 1 elements are forbidden (large image
plus earlier small choices), so every small demand gets a private fresh multiple.
Capacity holds (one demand per prime at large positions; one demand at small positions), ∏ demands of a = a, so ∏A | ∏B
and |B| ≤ 2n. With Lemma 1 (whole interval when M < 8n³): g(n) ≤ 8n³.
Gap statement (theirs): S for a_n < 8n³ is exactly what remains for T1.

## Machine verification (dialogue): problems/erdos708/es_bound3.py implements the construction; random instances with
a_n ≥ 8n³ (n ≤ 7): 0 failures, |B| ≤ 2n always. Two-bin packing lemma asserted on every split.
