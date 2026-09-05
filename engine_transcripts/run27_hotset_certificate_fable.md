# Erdős #708 — round 15 (T1', hot-set-excluded certificates for the sparse core)
Core prover report, F1_708. Run 20:05–23:00 CDT 2026-09-04. All files in this directory.
Scripts: `hotset_frac_lp.py` (→ `hotset_frac_lp.log`), `constants_check.py`, `constants_check2.py`, `constants_check3.py`, inline check 4 (→ `constants_check*.log`).

## 0. Verdict table

| Item | Status | Where |
|---|---|---|
| Both refereed barrier families (B2 = m!-windows, r13 congruence windows) and the new centred-lcm family are handled by the hot-set-excluded cone with \|T\| = 1 | PROVED | §2 |
| Transport with edges "k \| b" (coordinator note (i): full pattern D_k as carrier) violates Hall on centred-lcm windows | PROVED (refutes note (i) as the carrier rule) | §3 |
| 0/1 atom systems (one atom per prime, α ∈ {0,1}): (SC_64) for every m > 4096 and every window | PROVED (verbatim adaptation of paper Thm `four`) | §4 |
| Lemma A: adapted-order carried-mass bound M_w(P) ≤ θ_P^{2−r}(H^r/r!)(m/P), r = ⌊60/θ_P⌋+1 | PROVED (new) | §5.3 |
| Lemma B: count of carriers dividing a window point | PROVED | §5.4 |
| Theorem C: the unit-window prefix certificate (moduli ≤ m, c ≥ 0) is feasible with factor λ = 2 at every b ∈ I with S₀(b) ≤ S*(m); S*(m) ≈ 1.5·10^28/(log₂ m)^2: S*(10^3000) ≥ 1.2·10^20, S*(10^{10^10}) ≥ 10^7, S*(10^{10^12}) ≥ 10^3; general atom systems incl. multi-level (linear) weights (for SAP systems the m-free threshold 260) | PROVED | §5.5 |
| Identity: W_T ≥ L ⟺ (NC): Σ_{b∈T} ov(b) ≤ L/2, T = {b : 2·ov(b) > cap(b)} ⊆ {S₀ > S*(m)} | PROVED (exact) | §5.6 |
| T1' (hence (SC_64)) for every sparse window | CONDITIONAL on (NC) | §5.6 |
| Carriers P ≤ 15·S*(m) are never half-swallowed (f_P ≤ 1/2) | PROVED | §6.1 |
| A single large carrier can be fully swallowed (CRT window with private atoms); private-atom swallowing loses < 10^−122 m of mass | necessary conditions PROVED; realisation SKETCHED | §6.2 |
| (SC_64) on the natural crowding family (0/1 atoms on the primes in (10^51, 10^138], every m, every x) via the §5 cone + (Sh) | PROVED | §6.3 |
| (NC) in general; a T2' family with W_{I∖T} < L for every T | OPEN — no family found; necessary shape given | §6.4, §7 |
| Toy LPs (C = 2, 3; m ≤ 150; masses 1, 1/2, mixed): W* = R in every instance; T = one point suffices | computed | §8 |

Bottom line. The hot-set-excluded cone is alive: with the right carrier rule (mass-ordered prefixes of the hot integers, of mass in (2,4),
weighted by a unit window in the cumulative mass) its feasibility is automatic at every window point of mass ≤ S*(m) ≥ 10^{20}
(m ≤ 10^{3000}; ≈ 1.5·10^{28}/(log₂ m)² in general, ≥ 260 for SAP systems for every m); tiny atoms are harmless because the carried mass of a prefix ending in an atom of mass θ is ≤ θ^{2−r}H^r/r! per multiple,
r ≈ 60/θ (Lemma A), which beats the (1+SE/θ)^{3/θ} count of such prefixes. What is left is one mass-concentration statement (NC): the crowded
points (mass > S*(m), each divisible by > 10^{100} carriers) do not absorb half of the certificate mass. (NC) is proved for small carriers,
for the crowding family the brief singled out, and is open in general; the obstruction is again the ±1 freedom of N_I(d) for moduli d > m
at ≤ 1.07 m/S*(m) points.

## 1. Setting (verbatim from the brief, with the notation used below)

Atoms (p,e) with weights α_{p,e} ∈ [0,1], p^e ≤ m/64, Σ_e α_{p,e} ≤ 1; a_p(n) := Σ_{e : p^e | n} α_{p,e} ∈ [0,1]; S₀(n) := Σ_p a_p(n);
H := Σ α_{p,e}/p^e < 17/16; m > 4096; K = [1,m], I = (x, x+m]; L := Σ_{k≤m}(S₀(k)−64)⁺, R := Σ_{b∈I}(S₀(b)−1)⁺; cap(b) := (S₀(b)−1)⁺.
A system is SAP (single atom per prime) if every prime has at most one e with α_{p,e} > 0 (0/1 systems are SAP with α ∈ {0,1}). The
application (paper, Cor. `sparsecore`) needs the linear multi-level systems α_{p,e} = min(e z_p,1) − min((e−1)z_p,1); everything in §5 covers them.
For a positive integer D put μ(D) := S₀(D). Monotonicity: D | n ⇒ a_p(n) ≥ a_p(D) for all p, hence S₀(n) ≥ μ(D).
N_I(D) := #{b ∈ I : D | b}; ⌊m/D⌋ ≤ N_I(D) ≤ ⌊m/D⌋+1; for D ≤ m: N_I(D) ≥ 1 and (m/D)/N_I(D) ≤ 2.
Hot-set-excluded LP (referee addendum): T ⊆ I, c_D ≥ 0 (D ≤ m), Σ_{D|b} c_D ≤ cap(b) for b ∈ I∖T, value W_T := Σ_D c_D N_{I∖T}(D) ≤ R.
Two refereed facts from the paper: (M) Σ_{j≤N} e_r((a_p(j))_p) ≤ N e_r((h_p)_p) ≤ N H^r/r! for all N ≥ 1, r ≥ 1, h_p := Σ_e α_{p,e}/p^e
(expand e_r; ⌊N/D⌋ ≤ N/D for the coprime moduli); (Sh) Theorem `shadow`: if L > 0 then R ≥ (32/3)(1−6^{−31}) m^{31/32} > 10 m^{31/32}.
Also from r14 Lemma 1: #{b ∈ I : S₀(b) > S} < (1105/1024) m/S.

## 2. The known barriers are escaped by one excluded point (PROVED)

**Proposition 2.1.** Let the atoms be α_{p,1} = 1 for p in a finite prime set P (a 0/1 system), and let the window contain a point B with
p | B for all p ∈ P (reflected window I = (m!−m, m!]; centred window I = (B−m/2, B+m/2], B = ∏P; r13 window I = [B, B+m), B = ∏P).
Put T = {B}, w* := max_{b ∈ I∖T} ω_P(b), and c_{pq} := 2/w* for all p < q in P with pq ≤ m, all other c_D = 0. Then c is feasible on I∖T and
W_T ≥ (2/w*) Σ_{pq ≤ m} (⌊m/pq⌋ − 1).
*Proof.* At b ∈ I∖T with ω_P(b) = w ≤ w*: Σ_{pq|b} c_{pq} = C(w,2)·2/w* ≤ w(w−1)/w* ≤ w − 1 = cap(b) (w ≥ 1; for w = 0 both sides vanish).
Value: N_{I∖T}(pq) ≥ N_I(pq) − 1 ≥ ⌊m/pq⌋ − 1. ∎
On the r14 family (m = q^65, n primes in (n, 10 n log₂ n)) w* ≤ 65 (r14 Cor. 9); on the r13 family (m = 2^{65(M+1)}, primes in (Q^{9/10}, 2Q])
w* ≤ 65(M+1)/(0.9 log₂ Q) ≤ 73; on the centred family w* = max_{t<m/2} ω_P(t) ≤ 65. In all three cases W_T ≥ mH²/74 − n² while L ≤ mH^{65}/65!,
so W_T/L > 10^{80}. Every refereed barrier is a "one super-hot point divisible by everything" barrier, escaped by T = {that point}.
Consequently a T2' family must have crowded points that are *not* divisible by all moduli ≤ m (§7).

## 3. The naive transport (carrier = full pattern D_k, coordinator note (i)) fails Hall (PROVED)

**Proposition 3.1.** P = primes in [p₀, 2p₀] (n = |P| ≥ 200), α_{p,1} = 1, m ∈ [p₀^65, (2p₀)^65] chosen so that the dyadic interval (m/2, m]
contains ≥ C(n,65)/65 of the 65-products k_A (one of the 65 dyadic intervals covering [p₀^65,(2p₀)^65] does), B = ∏P, I = (B − m/2, B + m/2].
Every k_A ∈ (m/2, m] is hot with d_k = 1 and has exactly one multiple in I, namely B (B ± k_A ∉ I as k_A > m/2). So for the flow with edges
k → b iff k | b (equivalently D_k | b with D_k = k the full pattern), the set A of these k has N(A) = {B}, cap(B) = n − 1 < C(n,65)/65 ≤ Σ_{k∈A} d_k:
Hall fails. Yet (SC_64) holds on this window with room (S₀(B ± t) = S₀(t), so R ≥ 2#{t < m/2 : ω_P(t) ≥ 2} ≥ m(Σ1/p)²/3 ≫ L), and routing each
k_A through a 2-atom sub-pattern pq | k_A is the certificate of Prop. 2.1. ∎  Carriers must be sub-patterns of *controlled mass* (§5).

## 4. 0/1 systems: (SC_64) holds for all m (PROVED; adaptation of the paper's Theorem `four`)

**Theorem 4.1.** If every atom weight is 0 or 1 and each prime carries at most one atom (so S₀ = ω_Q for a set Q of pairwise coprime prime
powers q ≤ m/64), then Σ_{k≤m}(ω_Q(k) − 4)⁺ ≤ Σ_{b∈I}(ω_Q(b) − 1)⁺ for every m ≥ 1 and x ≥ 0; a fortiori (SC_64).
*Proof.* The paper's proof of Theorem `four` uses only: (i) cube-root peeling — three pairwise coprime moduli > y := ⌊m^{1/3}⌋ have product
> m, so ω_{Q_L}(k) ≤ 2 for Q_L := {q ∈ Q : q > y} and (ω_Q(k)−4)⁺ ≤ (ω_{Q_S}(k)−2)⁺, Q_S := Q∖Q_L; (ii) the sparse-branch certificate
c_{qq'} = 11/21, c_{qq'q''} = −1/7 (q,q',q'' ∈ Q_S), feasible because Σ_{d|n} c_d = r(r−1)(13−r)/42 ≤ (r−1)⁺ ≤ (ω_Q(n)−1)⁺ with r = ω_{Q_S}(n)
(purely combinatorial in the number of coprime moduli dividing n); (iii) the value bound V(c) ≥ E₂/3 which uses only qq' ≤ y², qq'q'' ≤ y³ ≤ m
and η := (1+1/y)Σ_{q∈Q_S}1/q ≤ 2; (iv) the dense branch η > 2 with the affine certificate. Each step is verbatim with ω_Q in place of Ω_P and
the repeated-prime term E_P ≡ 0. In the sparse core Σ_{q∈Q_S}1/q ≤ H < 17/16, so η ≤ (17/16)(17/16) < 2 and only branch (ii) is used. ∎
Consequence: any T2' family and any counterexample to (SC_64) must use fractional atoms; and (paper remark (c)) no certificate of bounded rank
is pointwise feasible for fractional atoms, so the certificate must follow the mass structure. That is §5.

## 5. The unit-window prefix certificate

### 5.1 Global order and prefixes
𝒜 := {(p,e) : α_{p,e} > 0}, A_{p,e} := Σ_{e' ≤ e} α_{p,e'} (cumulative mass ≤ 1). Order 𝒜 by ≺: (p,e) ≺ (p',e') iff A_{p,e} > A_{p',e'}, or
A_{p,e} = A_{p',e'} and (p,e) < (p',e') lexicographically ("heavier first"). For an integer n and a prime p with a_p(n) > 0 let
e*_p(n) := max{e : (p,e) ∈ 𝒜, p^e | n}; the *effective atom* of n at p is u = (p, e*_p(n)), modulus p^{e*}, mass A_{p,e*} = a_p(n).
For a hot k (S₀(k) > 64) list its effective atoms in ≺-order u₁ ≺ … ≺ u_A, masses a₁ ≥ … ≥ a_A, S₀(k) = Σ a_l, s_i := a₁+…+a_i (s₀ = 0), and
prefixes P_i(k) := ∏_{l≤i} p_l^{e_l}. Then μ(P_i(k)) = s_i, P_i(k) | k, P_i(k) ≤ m.

### 5.2 Carriers, weights, certificate (σ = 3)
For u ∈ (2,3] let i_k(u) := min{i : s_i > u} (exists since s_A > 64). Weight of P_i(k): w_{k,i} := |[s_{i−1}, s_i) ∩ (2,3]| ≤ a_i; Σ_i w_{k,i} = 1.
If w_{k,i} > 0 then s_{i−1} ≤ 3 and s_i > 2, so μ(P_i(k)) = s_i ∈ (2,4) (as s_i ≤ s_{i−1}+1). Such a P_i(k) is a *carrier* of k with last atom
u_i and θ_P := a_i (a function of P: the ≺-last atom of P has mass A_{p_i,e_i}). Carried mass M_w(P) := Σ_{k hot} d_k Σ_{i: P_i(k)=P} w_{k,i},
d_k := S₀(k)−64 (at most one i per k, prefixes of one k being distinct). Σ_P M_w(P) = Σ_k d_k = L.
Certificate: c_P := λ M_w(P)/N_I(P) on carriers (λ ≥ 1), c_D = 0 otherwise. Carriers are ≤ m (they divide some k ≤ m), so N_I(P) ≥ 1 and
this lies in the referee's cone. Overload: ov(b) := Σ_{P | b} M_w(P)/N_I(P); Σ_{b∈I} ov(b) = L.

### 5.3 Lemma A (carried mass, adapted moment order) — PROVED
**Lemma A.** For every carrier P with last-atom mass θ = θ_P and r := ⌊60/θ⌋+1:
  M_w(P) ≤ θ^{2−r}(H^r/r!)(m/P),   hence   M_w(P)/N_I(P) ≤ 2ε(θ),   ε(θ) := θ^{2−r}H^r/r!.
*Proof.* Let k be hot with P_i(k) = P, w_{k,i} > 0, and j := k/P. For p | P, a_p(k) = A_{p,e_p} is P's mass at p; for p ∤ P, v_p(j) = v_p(k) so
a_p(j) = a_p(k). Hence S₀(k) = μ(P) + S₀^{(P)}(j), S₀^{(P)}(j) := Σ_{p∤P} a_p(j). As μ(P) < 4: d_k < S₀^{(P)}(j) − 60 ≤ (S₀^{(P)}(j) − 60)⁺.
The effective atoms of k at primes p ∤ P come after u_i in ≺, so a_p(j) = a_p(k) ≤ a_i = θ for every p ∤ P.
Rescaled hinge–moment inequality: for a ∈ [0,θ]^N with sum t, c > 0, r = ⌊c/θ⌋+1: (t − c)⁺ ≤ θ^{1−r} e_r(a). [Apply the paper's
(T − C)⁺ ≤ e_{C+1}(x) (x ∈ [0,1]^N, C ∈ ℤ_{≥0}) with C = ⌊c/θ⌋ to x = a/θ: (t−c)⁺/θ = (t/θ − c/θ)⁺ ≤ (t/θ − ⌊c/θ⌋)⁺ ≤ e_r(a/θ) = θ^{−r}e_r(a).
Proof of the paper's inequality: e_{C+1} is Schur-concave on ℝ^N_{≥0} and the vector (1^{⌊T⌋}, {T}, 0, …) majorises every x ∈ [0,1]^N of sum T,
so e_{C+1}(x) ≥ C(⌊T⌋,C+1) + {T}C(⌊T⌋,C) ≥ (⌊T⌋−C)⁺ + {T}·1[⌊T⌋ ≥ C] ≥ (T−C)⁺, using C(n,C+1) ≥ n−C for n ≥ C+1 (induction on n).]
Checked exactly on 3000 random and adversarial rational instances: 0 violations, max ratio 1 (`constants_check.log`, item (1)).
Apply it with c = 60 to (a_p(j))_{p∤P} ∈ [0,θ]: d_k ≤ θ^{1−r} e_r((a_p(j))_{p∤P}). The map k ↦ j is injective, j ≤ m/P, w_{k,i} ≤ θ; by (M)
with N = m/P (dropping the primes p | P only lowers e_r(h)): M_w(P) ≤ θ·θ^{1−r}·(m/P)·H^r/r!. Finally (m/P)/N_I(P) ≤ 2 as P ≤ m. ∎
Numerics (`constants_check2.log`, block c = 60): log₁₀ ε(1) = −82.1, and log₁₀ ε(θ) ≈ −78.6/θ — super-exponentially small in 1/θ. This is
what makes "junk" atoms harmless: a prefix ending in an atom of mass θ carries only hot k whose residual mass > 60 consists of atoms of
mass ≤ θ, and (M) at order r ≈ 60/θ sees how rare those are; the fixed-order bound H^{32}/32! of the brief does not.
Two by-products: the residual j has ≥ 60/θ_P distinct prime factors, so j ≥ 2^{60/θ_P} and j ≤ m/P give **θ_P ≥ 60/log₂(m/P) ≥ 60/log₂ m**
for every carrier; and N_I(P) ≥ ⌊m/P⌋ ≥ j ≥ (product of the first 61 primes) = 10^{117.8} > 10^{113}.

### 5.4 Lemma B (carriers dividing a point) — PROVED
Fix b ∈ I, S := S₀(b), E := max number of atom levels of a prime (≤ log₂(m/64)), and a sub-atom q = (p,e) ∈ 𝒜 with p^e | b, θ_q := A_{p,e}.
**Lemma B.** #{carriers P : P | b, last atom of P = q} ≤ Σ_{l ≤ 3/θ_q} C(⌊S/θ_q⌋E, l) ≤ (1 + SE/θ_q)^{3/θ_q}; for SAP systems also ≤ 2^{S/θ_q}.
*Proof.* Write P = P'p^e. Each atom (p',e') of P' precedes q in ≺, so A_{p',e'} ≥ θ_q; p'^{e'} | b gives a_{p'}(b) ≥ A_{p',e'} ≥ θ_q, so at most
S/θ_q primes p' occur, each with ≤ E admissible exponents. μ(P') = s_{i−1} ≤ 3 and each atom of P' has mass ≥ θ_q, so |P'| ≤ 3/θ_q.
For SAP, P' is a set of effective atoms of b of mass ≥ θ_q. ∎

### 5.5 Theorem C (feasibility at every point of moderate mass) — PROVED
**Theorem C.** For every atom system (multi-level allowed), every window and every b ∈ I with S := S₀(b):
  ov(b) ≤ 2ES · sup_{θ ∈ [60/log₂ m, 1]} G_S(θ),   G_S(θ) := θ^{1−r}(H^r/r!)(1 + SE/θ)^{3/θ},  r = ⌊60/θ⌋+1.
Hence 2·ov(b) ≤ cap(b) for every b with S₀(b) ≤ S*(m), where (`constants_check3.log`, with a safety factor 10 covering the r- and S-grids)
S*(m) ≥ 1.2·10^{20} for m ≤ 10^{3000}, ≥ 1.1·10^{19} (m ≤ 10^{10^4}), ≥ 10^{17} (m ≤ 10^{10^5}), ≥ 10^{15} (m ≤ 10^{10^6}), ≥ 1.1·10^{11} (m ≤ 10^{10^8}),
≥ 10^7 (m ≤ 10^{10^{10}}), ≥ 1.1·10^3 (m ≤ 10^{10^{12}}); asymptotically S*(m) ≈ 1.5·10^{28}/(log₂ m)² (the factor E = log₂(m/64) from multi-level
atoms enters twice: through Σ_q θ_q ≤ ES and through the count of Lemma B), so for multi-level systems the theorem is void beyond
m ≈ 10^{10^{13}}; for SAP systems the m-free bound below applies for every m.
For SAP systems the 2^{S/θ} count gives the m-free bound ov(b) ≤ 2S sup_θ 2^{S/θ}ε(θ)/θ and 2·ov(b) ≤ cap(b) for all S₀(b) ≤ 260
(`constants_check2.log` and `constants_check4.log`, c = 60, λ = 2: the sup over r ≤ 10^7 and the asymptotic slope S·log₁₀2 − 60·log₁₀(60/(eH))
per unit of 1/θ, negative up to S = 262; we state 260 for margin).
*Proof.* ov(b) = Σ_{P|b} M_w(P)/N_I(P) ≤ Σ_q 2ε(θ_q)·#{P | b : last(P) = q} (Lemma A) ≤ Σ_q 2ε(θ_q)(1+SE/θ_q)^{3/θ_q} (Lemma B), q ranging over
sub-atoms of b with θ_q ≥ 60/log₂ m (§5.3: no carrier ends in a lighter atom). Write ε(θ_q) = θ_q·θ_q^{1−r}H^r/r! and Σ_q θ_q ≤ Σ_pΣ_e A_{p,e} ≤ ES.
On each piece θ ∈ (60/r, 60/(r−1)] (r fixed) log G_S is decreasing in θ, so the sup is the max over r ≥ 61 of G_S(60/r), which the scripts
enumerate (r ∈ {61,…,2000} ∪ a geometric grid of ratio 1.0005 up to r_max = ⌊log₂ m⌋+1 ∪ {r_max}; asymptotically log₁₀G_S(60/r) ≈
r[log₁₀(e/60) + log₁₀H + (1/20)log₁₀(SEr/60)], whose bracket changes sign at SEr ≈ 60·10^{26.4}, which is where S*(m) comes from).
Feasibility: 4ES·supG_S ≤ (S−1)/10 is checked for S on a geometric grid of ratio 1.2 up to the reported S*(m); the factor 10 covers the
r-grid error (< 10^{0.0005·|log G|}) and the S-grid (4ES supG_S is increasing in S and S₂ − 1 ≤ 1.25(S − 1) for S ≥ 5 between grid points).
For S ≤ 2 no carrier divides b (μ(P) > 2), so ov(b) = 0. ∎

### 5.6 The exact reduction (λ-trick) — PROVED
**Proposition 5.6.** T := {b ∈ I : λ ov(b) > cap(b)}, c_P := λM_w(P)/N_I(P). Then c is feasible on I∖T and
  W_T = λ(L − Σ_{b∈T} ov(b)),   so   W_T ≥ L ⟺ Σ_{b∈T} ov(b) ≤ (1 − 1/λ)L.   With λ = 2 this is  (NC): Σ_{b∈T} ov(b) ≤ L/2.
*Proof.* Feasibility off T is the definition of T. W_T = Σ_{b∉T}Σ_{P|b} c_P = λΣ_P M_w(P)N_{I∖T}(P)/N_I(P) = λΣ_P M_w(P)(1 − t_P/N_I(P)) with
t_P := |T ∩ Pℤ|, and Σ_P M_w(P)t_P/N_I(P) = Σ_{b∈T}Σ_{P|b}M_w(P)/N_I(P) = Σ_{b∈T}ov(b); Σ_P M_w(P) = L. ∎
By Theorem C, T ⊆ {b : S₀(b) > S*(m)}, so |T| < (1105/1024)m/S*(m) ≤ 10^{−20}m for m ≤ 10^{3000}.
**Corollary 5.7 (CONDITIONAL on (NC)).** If (NC) holds on a window then R ≥ W_T ≥ L there; T1' for all sparse windows ⟸ (NC) for all sparse
windows. All other statements of §5 are unconditional.

## 6. (NC): what it says, what is proved, where it is open
Write f_P := t_P/N_I(P) (fraction of P's multiples that are crowded, i.e. in T). Then Σ_{b∈T}ov(b) = Σ_P M_w(P)f_P, so (NC) ⟸ f_P ≤ 1/2 for all
carriers, and (NC) fails only if carriers holding ≥ half of the mass L have most of their multiples crowded. A crowded point has
S₀(b) > S*(m) and, by Lemma A, is divisible by > (S*(m)−1)/(4ε(1)) > 10^{100} carriers (m ≤ 10^{3000}).

### 6.1 Small carriers are never half-swallowed — PROVED
**Lemma 6.1.** f_P < H(1 + P/32)/(S*(m) − 4) for every carrier P; in particular f_P ≤ 1/2 for P ≤ 15·S*(m) (≈ 2·10^{21} for m ≤ 10^{3000}).
*Proof.* For b = Pj ∈ T: S₀^{(P)}(j) = S₀(b) − μ(P) > S*(m) − 4. Summing over the multiples Pj of P in I: t_P(S*(m)−4) < Σ_j S₀^{(P)}(j)
≤ Σ_{(p,e)} α_{p,e}(N_I(P)/p^e + 1) ≤ N_I(P)H + (m/64)H, using p^e ≤ m/64 ⇒ 1 ≤ m/(64p^e). Divide by N_I(P) ≥ m/(2P) (valid as m/P ≥ 2). ∎

### 6.2 A single large carrier can be fully swallowed — CONSTRUCTION (sketch; sizes checked by hand, to be re-verified); (NC) is genuinely global
Necessary conditions first (PROVED). A point b = Pj is crowded only if 2ov(b) > cap(b); atoms of modulus > N := N_I(P) ("private": each divides
at most one multiple of P in I) can contribute to ov(b) only through carriers P' ∋ q, and any carrier satisfies P' ≤ m/10^{113} (§5.3), so
q ≤ m/10^{113}; as q > N ≥ m/(2P) this forces P > 10^{113}/2. If W private unit atoms crowd b through private triples alone, then
4ε(1)C(W,3) > W − 1, i.e. W > 1.3·10^{41}; the WN private primes have Σ1/q ≥ WN·64/m ≥ 32W/P, so H < 17/16 forces W < P/30 and hence
P > 4·10^{42}. Consequently the private-atom mechanism can only swallow carriers P > 4·10^{42} (consistent with Lemma 6.1), each swallowed
carrier costs reciprocal budget ≥ 32·10^{41}/P, so Σ_{P swallowed} 1/P ≤ 3.3·10^{−41} and the mass lost to this mechanism is
Σ_{P sw} M_w(P) ≤ Σ ε(1) m/P < 10^{−122} m — below L/2 whenever L > 10m^{31/32} (else (Sh) applies) and m ≤ 10^{3900}.
Realisation (sketch). 0/1 base systems cannot realise it (a carrier is then a product of the 3 smallest of ≥ 65 unit atoms of a hot k ≤ m, so
P ≤ m^{3/65}, N ≥ m^{0.95}, and private q > N cannot lie in any hot k ≤ m). Fractional base atoms can: take α = 0.3 on all primes in [p₀, p₀^{20}]
(H ≈ 0.3·ln 20 = 0.9), p₀ = 10^{50}, m = p₀^{250}; hot k need ≥ 214 base atoms; carriers have 7–13 base atoms and can be as large as p₀^{260};
choose a carrier P ≈ p₀^{240} (twelve primes near p₀^{20}), so N ≈ p₀^{10} = 10^{500} ≥ 2^{60/0.3}. Private unit primes q in (N, N^{1.4}] ⊆ (10^{500}, 10^{700}]
(≤ m/64; Σ1/q ≤ 0.34, total H ≤ 1.0625 − ε): a private triple is the ≺-prefix (unit atoms precede mass-0.3 atoms) of the hot integer
q₁q₂q₃·(204 base primes near p₀) ≤ 10^{2100+10200} ≤ m, so private triples are carriers; W := 10^{196} private primes per multiple of P need
WN = 10^{696} primes in (N, N^{1.4}] (available: 10^{700}/1600), and W < P/30 = 10^{12000}/30 holds. CRT on j₀ + t ≡ 0 (mod q_{t,l}) and x := Pj₀ − 1
make every multiple of P carry W private unit atoms; Lemma A is sharp up to the completion density (≈ (0.9)^{204}/204! ≈ 10^{−390}) for the
private triples, so ov(Pj) ≈ 2·10^{−390}·C(W,3) ≈ 10^{197} > cap(Pj)/2 ≈ W/2: every multiple of P is crowded, f_P = 1, M_w(P) is lost.
All hypotheses of (SC_64) hold; the window is not an (SC_64) counterexample (R ≥ WN). So (NC) cannot be proved carrier by carrier — it must use
that swallowed carriers hold little of L, which for this mechanism is the 10^{−122}m bound above. Mixed mechanisms (shared atoms of modulus
≤ N plus private ones) are not closed — §6.4.

### 6.3 (SC_64) on the crowding family the brief singled out — PROVED (every m > 4096, every x)
Family: Q := all primes in (10^{51}, 10^{138}], α_{q,1} = 1 (Σ_{q∈Q}1/q ≈ ln(138/51) = 0.995 < 17/16; q ≤ m/64 requires m ≥ 10^{140}, and L > 0
requires m ≥ 10^{3315}; for smaller m either the hypotheses fail or L = 0). All atoms have mass 1, E = 1, ε(1) = H^{61}/61! < 10^{−82}, every carrier
is a product of three atoms, and ov(b) ≤ 2ε(1)·C(ω_Q(b),3). Crowded ⇒ 4ε(1)C(ω,3) > ω−1 ⇒ ω_Q(b) > 10^{41}.
24th-moment control: Σ_{b∈I} C(ω_Q(b),24) = Σ_{|A|=24} N_I(k_A) ≤ Σ_A(m/k_A + 1) ≤ m/24! + C(|Q|,24) ≤ 2m/24! for m ≥ 10^{3252} (C(|Q|,24) ≤ 10^{3228},
`constants_check.log` item (5)). Since C(ω,3)/C(ω,24) is decreasing in ω,
  Σ_{b∈T} ov(b) ≤ 2ε(1)·[C(10^{41},3)/C(10^{41},24)]·Σ_b C(ω_b,24) ≤ 2·10^{−82}·(24!/3!)·10^{−861}·2m/24! < 10^{−940} m.
Now either L ≤ 10m^{31/32}, and (Sh) gives R ≥ L; or L > 10m^{31/32} ≥ 2·10^{−940}m (true for m ≤ 10^{30000}), and (NC) holds, so R ≥ L by Cor. 5.7;
or m > 10^{30000} > 10^{8970}, all 65-products of Q are ≤ m and L ≥ (1/2)m(Σ_Q 1/q)^{65}/65! > 10^{−93}m ≥ 2·10^{−940}m, and again (NC) holds. ∎
(For 0/1 systems Theorem 4.1 already gives (SC_64); the point is that the cone of §5 closes the family the brief proposed as the crowding
adversary, with room 10^{800}.) The same three-way argument works for any 0/1 family with C(|Q|,24) ≤ m/24! (24th moment controlled).

### 6.4 Why (NC) is open in general
The absolute bound Σ_{b∈T}ov(b) ≤ 2Σ_{b∈T}Σ_q ε(θ_q)N_q(b) is controlled by window moments of order ≈ 3/θ_min + 2 *when the products of that
many atoms are ≤ m* (so the +1 terms of N_I are absorbed, as in §6.3). If atoms are as large as m^{1/4}, only moments of order ≤ 4 are
controlled, and points with ω ≈ 10^{41} may number up to m·10^{−164} (4th moment), carrying up to 10^{−164}·2ε(1)·C(10^{41},3) ≈ 10^{−124}m of
certificate mass — below L/2 only if L ≥ 2·10^{−124}m, which (Sh) guarantees only for m ≤ 10^{3990}. For fractional systems the needed order 3/θ_min+2 is larger and
the controlled range shorter. So (NC) is OPEN exactly where the r14/r13/r12 barriers lived: windows of length m ≥ 10^{3000}-ish with atoms
so large that the +1 freedom in N_I(d), d > m, is not absorbed by moments — now at ≤ 1.07m/S*(m) points of mass > 10^{20} each divisible by
> 10^{100} carriers. I found no CRT construction realising this with half of L swallowed (the private-atom mechanism of §6.2 is budget-limited
to < 10^{−122}m of swallowed mass), but I also cannot exclude it.

## 7. T2' (a family with W_{I∖T} < L for every T): not found; necessary shape
By §2, §4, §5, §6 such a family must: use fractional atoms (Thm 4.1 — note the §5 cone also closes 0/1 crowding families like §6.3);
have crowded points not divisible by all moduli ≤ m (else T = {one point} frees everything, Prop. 2.1); have crowded points of mass > S*(m) ≥ 10^{20} (m ≤ 10^{3000}) — at most 1.07m/S*(m) of them, each divisible by > 10^{100} carriers —, hosting ≥ half of the §5 certificate mass (Prop. 5.6);
swallow only carriers P > 15 S*(m) (Lemma 6.1); and defeat every other c ≥ 0 certificate on I∖T. The brief's "every multiple of every hot
pattern is hot" is impossible for small carriers (Lemma 6.1) and, for large ones, costs reciprocal-sum budget ∝ 1/P per carrier (§6.2).

## 8. Exact experiments (`hotset_frac_lp.py` → `hotset_frac_lp.log`)
Hot-set-excluded LP (HiGHS) with T_{t₀} = {S₀ > C+t₀}, and the MILP over all T (binary z_b, big-M, HiGHS) for C ∈ {2,3}, m ≤ 150, reflected
m!-windows, centred ∏P-windows, x = 0, atoms 1, 1/2 and mixed {1,1/2,1/3}. In every instance W* (optimum over all T) = R exactly, and
T = {the single hot point} already gives W_T ≥ L (e.g. reflected, P = {2,3,5,7,11}, m = 40, C = 2: L = 1, R = 20, W_{T=∅} = 16, W_{T={B}} = 15;
mixed masses, reflected, m = 80: L = 2.5, R = 28.5, W_{t₀=1} = 24 with |T| = 1). Toy scale is uninformative about T2' (L ≤ 2.5), as predicted. (The last two 'F5 crowding' cases of the script did not run: the venv lacks
sympy for the CRT helper; the log ends with that ImportError. They are toy-scale and would not change the conclusion.)
Constants: `constants_check.log` (rescaled inequality 3000/3000, ε(θ) table for c = 31, 131#), `constants_check2.log` (exact sup over θ, S* for
c ∈ {31,40,50,60}: 106/151/205/262), `constants_check4.log` (SAP c = 60 threshold with r ≤ 10^7 and asymptotic slope; 61-primorial = 10^{117.8}),
`constants_check3.log` (S*(m) for general multi-level systems, full r-range, safety factor 10).

## 9. Lean / next round
PROVED items are elementary and finite: divisibility monotonicity of S₀; Schur-concavity of e_r (or the direct majorisation step); the
moment identity (M); the sub-atom count (Lemma B); the λ-trick identity; Theorem C's numeric part is a finite maximisation over
r ∈ [61, log₂m + 1] of an explicit expression (interval arithmetic). The open item is the single window inequality
(NC): Σ_{b∈I : 2ov(b) > cap(b)} ov(b) ≤ L/2. Suggested attack: charge every crowded multiple Pj to the reciprocal-sum budget of the atoms that
crowd it (private atoms cost ≥ 32·10^{41}/P per swallowed carrier, §6.2; shared atoms of modulus ≤ N_I(P) are controlled by moments over J_P),
and compare Σ_P M_w(P)f_P with L using that carriers are ≤ m/10^{113}. If the mixed case can be closed, T1' and g(n) ≤ 81n for all n follow.

## 10. Dependency graph
T1' for all sparse windows [OPEN]  ←  (NC) for all windows [OPEN]  +  Prop. 5.6 [PROVED]  +  Theorem C [PROVED]
Theorem C [PROVED]  ←  Lemma A [PROVED]  ←  rescaled hinge–moment inequality [PROVED] + (M) [paper] ;  ←  Lemma B [PROVED]  ;  ←  finite sup enumeration (scripts)
(SC_64) on the §6.3 crowding family, all m [PROVED]  ←  Theorem C + Prop. 5.6 + 24th-moment control + (Sh) [paper]
(SC_64) for 0/1 SAP systems, all m [PROVED]  ←  paper Theorem `four` (verbatim adaptation, §4)
Escape of B2 / r13 / centred families with |T| = 1 [PROVED]  ←  Prop. 2.1 ;   "carrier = full pattern" refuted [PROVED]  ←  Prop. 3.1
Lemma 6.1 (small carriers safe) [PROVED]; §6.2 necessary conditions and the 10^{−122}m budget bound [PROVED], realisation [SKETCH].
Unproved: (NC) in general ⇒ T1', (SC_64) for m > 10^{2942}, (TH_65), g(n) ≤ 81n for all n remain OPEN. Nothing here contradicts the
refereed barriers (all are |T| = 1 escapes) and nothing is claimed beyond its tag.
