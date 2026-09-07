# Section 14 card read-backs

These lines describe the Lean declarations, without relying on the paper's proofs.
`A` is the original finite atom system; all rounded and certificate objects are
concrete definitions computed from `A` and `m`, not assumed auxiliary data.

- **14.2 `rounding`:** If `m > 4096`, the retained mean is at most the original mean, the retained threshold-one hinge sum on the window starting after `x` is at most the original one, and the original threshold-64 hinge sum on `1..m` is at most twice the retained threshold-16 hinge sum.
- **14.3 `hinge_le_esymm`:** For any finite family of real numbers in `[0,1]` and natural threshold `C`, the positive part of their sum minus `C` is bounded by the sum of products over its `(C+1)`-element subsets.
- **14.4 `moment_retained`:** For positive natural `N,r`, summing the `r`th elementary symmetric polynomial of the concrete retained per-prime contributions over `1..N` is bounded by `N * HB^r / r!`.
- **14.5 `carried_mass`:** For each concrete carrier when `m > 4096`, its modulus is less than the real fourth root of `m`, its integer quotient `K` is at least one, its carried mass is at most `epsilon * m/P`, and its normalized coefficient is at most twice `epsilon`, evaluated at its last level's dyadic index.
- **14.6 `carrier_count`:** Given a retained level dividing a positive integer `n`, the number of carrier moduli dividing `n` whose last level is exactly that level is at most the real power `2^((3 + Ttheta(n))/theta)`.
- **14.7 `values_at_point`:** At every natural integer `n`, including zero, the sum of the values of all retained levels whose moduli divide `n` is at most twice `B(n)`.
- **14.8 `uniform_numerical`:** For any nonnegative real `H ≤ 17/16` and natural dyadic index `h`, the explicitly defined `G(H,h)` is at most `17/416`.
- **14.9 `pointwise_feasibility`:** If `m > 4096` and the original mean is below `17/16`, the concrete signed certificate at every positive integer `n` is at most the positive part of `B(n)-1`.
- **14.10 `value_on_window`:** Under those same assumptions, the concrete certificate equals its finite signed divisor expansion; a positive combined coefficient has a carrier modulus below `m^(1/4)`; a negative combined coefficient has an outside-prime modulus `P*q < m^(5/16)`; and its sum on the length-`m` window after `x` is at least `(141/64) * LB`. The coefficients have no window parameter.
- **14.1 `sparse_core`:** For the original atom system, `m > 4096`, original mean below `17/16`, and any natural window start `x`, `(141/128) * L ≤ R`; its proof composes the rounding, pointwise-feasibility, and window-value cards.

Construction conventions: a level is its pair `(p,j)` and its modulus is `p^j`;
its value is `2^(-h)` with `h` the least index below the positive cumulative weight.
Only the first exponent of each rounded value is kept, then the integer cutoff
`(p^j)^(16 * 2^h) ≤ m` is applied. Carriers are deduplicated natural moduli arising
from positive-weight prefixes of hot integers. Prefix interval weights are real
lengths, so the open/closed endpoint convention does not affect their formula.
