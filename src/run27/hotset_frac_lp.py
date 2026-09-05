"""Hot-set-excluded window LP with FRACTIONAL atoms (Erdos #708, round 15, T3-type experiments).

Model: atoms = list of (q, alpha) with q a prime power (one atom per prime here), alpha in (0,1].
S0(n) = sum_{q | n} alpha_q.  Threshold C (analogue of 64) on K = [1,m], threshold 1 on I = (x, x+m].
L = sum_{k<=m} (S0(k)-C)^+ ,  R = sum_{b in I} (S0(b)-1)^+.
W_T = max sum_{D<=m} c_D * #{b in I\T : D | b}  s.t. c >= 0, sum_{D|b} c_D <= (S0(b)-1)^+ for b in I\T.
  - T_t0 = {b : S0(b) > C + t0}  (LP)
  - W* = max over ALL T (MILP: binary z_b, big-M), only for m <= MILP_MAX.
Outputs L, R, W_{T_t0}, W*, and the (approximate) optimal T size.
All divisor tests are exact big-integer; LP/MILP through scipy HiGHS (floating point, reported to 6 digits).
"""
import sys, time
from math import factorial, comb
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog, milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix, csr_matrix

T0 = time.time()
MILP_MAX = int(sys.argv[1]) if len(sys.argv) > 1 else 160
TIME_LIMIT = float(sys.argv[2]) if len(sys.argv) > 2 else 900.0

def S0(n, atoms):
    return sum(a for q, a in atoms if n % q == 0)

def window_lp(atoms, m, x, C, t0s, do_milp=True):
    I = [x + i for i in range(1, m + 1)]
    Ds = list(range(1, m + 1))
    sI = [S0(b, atoms) for b in I]
    capI = [max(v - 1.0, 0.0) for v in sI]
    L = sum(max(S0(k, atoms) - C, 0.0) for k in range(1, m + 1))
    R = sum(capI)
    # incidence matrix (b, D) for D | b
    A = lil_matrix((m, m))
    for i, b in enumerate(I):
        for j, D in enumerate(Ds):
            if b % D == 0:
                A[i, j] = 1.0
    A = csr_matrix(A)
    out = {"L": L, "R": R}
    for t0 in t0s:
        keep = [i for i in range(m) if sI[i] <= C + t0]
        if not keep:
            out[t0] = (None, m); continue
        Ak = A[keep, :]
        cnt = np.asarray(Ak.sum(axis=0)).ravel()
        rhs = np.array([capI[i] for i in keep])
        res = linprog(-cnt, A_ub=Ak, b_ub=rhs, bounds=[(0, None)] * m, method="highs")
        out[t0] = (round(-res.fun, 6) if res.status == 0 else None, m - len(keep))
    if do_milp and m <= MILP_MAX:
        # variables: c_D (m), z_b (m, binary), y_b (m)
        # max sum y_b ; y_b <= A c ; y_b <= M(1-z_b) ; A c <= cap + M z_b
        M = max(capI) + 1.0 if capI else 1.0
        # bound on c_D: c_D <= max cap (any feasible non-excluded multiple) -- if all multiples excluded c_D is useless
        Mc = M * m  # crude
        nvar = 3 * m
        cost = np.zeros(nvar); cost[2 * m:] = -1.0
        rows = []; lo = []; hi = []
        # y - A c <= 0
        B1 = lil_matrix((m, nvar))
        for i in range(m):
            B1[i, 2 * m + i] = 1.0
        B1 = csr_matrix(B1)
        from scipy.sparse import hstack, eye, vstack
        Zm = csr_matrix((m, m))
        Im = eye(m, format="csr")
        C1 = hstack([-A, Zm, Im]).tocsr()          # y - A c <= 0
        C2 = hstack([Zm, M * Im, Im]).tocsr()       # y + M z <= M
        C3 = hstack([A, -M * Im, Zm]).tocsr()       # A c - M z <= cap
        Acons = vstack([C1, C2, C3]).tocsr()
        ub = np.concatenate([np.zeros(m), M * np.ones(m), np.array(capI)])
        lb = -np.inf * np.ones(3 * m)
        integrality = np.concatenate([np.zeros(m), np.ones(m), np.zeros(m)])
        bounds = Bounds(np.zeros(nvar), np.concatenate([Mc * np.ones(m), np.ones(m), M * np.ones(m)]))
        res = milp(c=cost, constraints=LinearConstraint(Acons, lb, ub), integrality=integrality, bounds=bounds,
                   options={"time_limit": 120.0})
        if res.x is not None:
            z = res.x[m:2 * m]
            out["Wstar"] = (round(-res.fun, 6), int(round(z.sum())), res.status)
        else:
            out["Wstar"] = (None, None, res.status)
    return out

def prod(lst):
    r = 1
    for v in lst: r *= v
    return r

def report(name, atoms, m, x, C, t0s=(0, 1, 2, 10**6)):
    if time.time() - T0 > TIME_LIMIT:
        print("TIME LIMIT"); return
    r = window_lp(atoms, m, x, C, t0s)
    s = f"{name:34s} m={m:4d} C={C}: L={r['L']:.3f} R={r['R']:.3f}"
    for t0 in t0s:
        v = r[t0]
        s += f" | t0={t0 if t0<10**5 else 'inf'}: W={v[0]} |T|={v[1]}"
    if "Wstar" in r:
        s += f" | W*={r['Wstar'][0]} |T*|={r['Wstar'][1]} st={r['Wstar'][2]}"
    print(s, flush=True)
    return r

if __name__ == "__main__":
    # ---- F1: reflected m!-windows, 0/1 atoms (sanity vs referee table) ----
    for P, m, C in [([2,3,5,7,11], 40, 2), ([3,5,7,11], 40, 2), ([5,7,11,13], 60, 2)]:
        atoms = [(p, 1.0) for p in P]
        report("F1 reflect m!, 0/1", atoms, m, factorial(m) - m, C)
    # ---- F2: centred lcm windows, 0/1 atoms ----
    for P, m, C in [([2,3,5,7,11], 40, 2), ([3,5,7,11,13], 100, 2), ([3,5,7,11,13,17], 120, 3)]:
        atoms = [(p, 1.0) for p in P]
        B = prod(P)
        report("F2 centred B=prod P, 0/1", atoms, m, B - m // 2, C)
    # ---- F3: fractional atoms (all 1/2), reflected and centred windows ----
    for P, m, C in [([2,3,5,7,11,13], 60, 2), ([2,3,5,7,11,13,17,19], 100, 2), ([3,5,7,11,13,17,19,23], 150, 2)]:
        atoms = [(p, 0.5) for p in P]
        report("F3 all 1/2, reflect m!", atoms, m, factorial(m) - m, C)
        report("F3 all 1/2, centred", atoms, m, prod(P) - m // 2, C)
        report("F3 all 1/2, x=0", atoms, m, 0, C)
    # ---- F4: mixed masses ----
    for P, al, m, C in [([2,3,5,7,11,13], [1,1,.5,.5,.5,.5], 80, 2), ([2,3,5,7,11,13,17], [1,.5,.5,1/3,1/3,1/3,1/3], 120, 2)]:
        atoms = list(zip(P, al))
        report("F4 mixed, reflect m!", atoms, m, factorial(m) - m, C)
        report("F4 mixed, centred", atoms, m, prod(P) - m // 2, C)
    # ---- F5: crowding windows: x chosen by CRT so that several disjoint hot patterns hit distinct residues ----
    # atoms 1/2 on primes; hot pattern = 5 primes (S0=2.5>C=2); place multiples of pattern products near many points
    from sympy.ntheory.modular import crt
    P = [3,5,7,11,13,17,19,23,29,31]
    atoms = [(p, 0.5) for p in P]
    m = 150; C = 2
    # want x+ r_i divisible by product of pattern A_i, with r_i spread in [1,m]
    pats = [[3,5,7,11,13],[17,19,23,29,31]]
    mods = [prod(A) for A in pats]
    rems = [(-10) % mods[0], (-140) % mods[1]]
    x = int(crt(mods, rems)[0])
    report("F5 two disjoint hot pats", atoms, m, x, C)
    pats = [[3,5,7,11,13],[3,5,7,17,19],[3,5,7,23,29]]
    # overlapping patterns cannot be at different residues (share 3,5,7 -> residues congruent mod 105); use one CRT point with all
    x = int(crt([prod(set(sum(pats, [])))], [(-75) % prod(set(sum(pats, [])))])[0])
    report("F5 overlapping hot pats (1 pt)", atoms, m, x, C)
    print("done in %.1fs" % (time.time() - T0))
