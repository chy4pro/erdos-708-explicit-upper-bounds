# Erdős 708 round 16 — 30-minute checkpoint

Written: 2026-09-07T05:25:15.011503+00:00. Deadline: 2026-09-07 07:55:15 UTC.

# Live campaign notes

PROVED (inherited): use the paper's atom and hinge setting, moment bound, shadow theorem, the round-15 prefix identity, and corrected referee conclusions.

PROVED (local proof completed): a signed certificate proves the full fractional sparse core, without (NC). Round cumulative prime contributions down to dyadic values, retain a level of mass a and modulus q only when q^(16/a) <= m, and call the resulting sum B. The reduction is L_64(S_0) <= 2 L_16(B), with H_B <= H. Prefixes for B use the original unit interval (2,3], hence mass < 4 and moduli < m^(1/4).

PROVED: with theta the last mass, c_P = M(P)/floor(m/P), use the signed function 3 sum_P c_P [P|n] (1 - sum_{p not dividing P} min(b_p(n),theta)/16). All negative extension moduli are < m^(5/16). Its value is at least (141/64) L_16(B), yielding R >= (141/128) L_64(S_0).

PROVED (exact arithmetic): 2^23 (187/768)^12 = 1828518162230556187140793681 / 5019318332045454244023631872 < 1/2; 12*(17/416) = 51/104 < 1/2. The full exact-check suite now passes; see exact_checks.json and audit.md. It includes nonzero hot systems and negative controls. No external referee or Lean certification is claimed.

OPEN: original (NC) remains unproved; no counterexample is claimed. It is not a dependency of the new proof. Final report and Lean dependency list are being prepared. The sharp Erdos target g(n)<=2n remains OPEN; the accepted paper reduction gives g(n)<=81n from the proved sparse core.
