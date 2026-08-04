#!/usr/bin/env python3
"""empty_pe2_ext.py — EMPTY-PE2 (hostile round-2) INDEPENDENT instrument.

Fresh implementation by the PE2 verifier, written WITHOUT consulting
empty_pe1_ext.py's code (decorrelation leg: the E-r1 repair is PE1's own
derivation, so this round's machine leg must not inherit PE1's implementation).

Checks the ARITHMETIC CORE of the repaired S7 of EMPTY_PROOF_2026-08-08.md
(commit 7ebd9c8) on an exhaustive grid, all in exact Fraction arithmetic:

  PE2-EL4      E-L4 exact unroll identity + remainder bound <= 1 - w0.
  PE2-EL5i     E-L5(i)  c+_{m-1}(0) <= c_{m-1} always.
  PE2-EL5cap   E-L5(ii) cap c+_{m-1}(1) <= c_{m-1} + 1 always.
  PE2-EL5cls   E-L5(ii) EXACT classification: c+_{m-1}(1) = c_{m-1}+1  <=>
               Y-tight (tight0 AND maximal c-chain remainders at 2..m-1).
  PE2-EL8      E-L8 on the Y-tight stratum: c+_l(1) = c_l + 1 at EVERY level
               and rho+_l = 0 at every l >= 2 (headroom EXACTLY 0).
  PE2-R3       the R3 exact identity  w1 c+_1(Y) + sum t_l w_{l-1}
               = c+_{m-1}(Y) + sum rho+_l w_{l-1}   (both Y).
  PE2-HEAD     headroom bound sum rho+_l w_{l-1} <= 1 - w1.
  PE2-R6       on Y-tight with e0 >= 2: every single level-0 removal
               (P0 - e0 k - y, k <= g0-1, y admissible) drops the worst-case
               level-0 floor with the +1 to <= c+_1(1) - 1; double removals too.
  PE2-W1a      sanity: the WITHDRAWN unconditional -1[CE0] step is refuted at
               the note's own witness (e0=2,g0=2,t1=4,t=1,k=1,y=1).

Grid: m in {2,3,4}; e in {1,2,3}^{m-1}; g0 in {1,2,3};
t1 in [0, 3*P0 - 1]; t_l in [0, 3*e_{l-1} - 1] for 2 <= l <= m-1.
"""
from fractions import Fraction
from itertools import product

fails = []


def chains(m, e, g0, ts):
    """ts = (t_1, ..., t_{m-1}) 1-indexed as ts[l-1]. Returns (c, cp0, cp1)
    where c[l], cp0[l], cp1[l] are the level-l values (index 0 unused ->
    c[0] = carry-in 0 for c; cp uses its own level-1 seed)."""
    P0 = e[0] * g0
    c = [0] * m          # c[l] for l = 0..m-1 ; c[0] = 0
    for l in range(1, m):
        c[l] = (ts[l - 1] + c[l - 1]) // e[l - 1]
    cp = {}
    for Y in (0, 1):
        v = [None] * m
        v[1] = (ts[0] + (g0 - 1) * e[0] + Y) // P0
        for l in range(2, m):
            v[l] = (ts[l - 1] + v[l - 1]) // e[l - 1]
        cp[Y] = v
    return c, cp[0], cp[1]


def weights(m, e):
    """w[l] for l = 0..m-1 with w[m-1] = 1, w[l-1] = w[l]/e[l-1]."""
    w = [Fraction(0)] * m
    w[m - 1] = Fraction(1)
    for l in range(m - 1, 0, -1):
        w[l - 1] = w[l] / e[l - 1]
    return w


def is_tight(m, e, g0, ts, c):
    if g0 == 1:
        t0 = (ts[0] % e[0]) == e[0] - 1
    else:
        t0 = ts[0] == e[0] - 1
    if not t0:
        return False
    for l in range(2, m):
        if (ts[l - 1] + c[l - 1]) % e[l - 1] != e[l - 1] - 1:
            return False
    return True


n_pts = n_tight = 0
for m in (2, 3, 4):
    for e in product((1, 2, 3), repeat=m - 1):
        for g0 in (1, 2, 3):
            P0 = e[0] * g0
            ranges = [range(0, 3 * P0)] + \
                     [range(0, 3 * e[l - 1]) for l in range(2, m)]
            w = weights(m, e)
            for ts in product(*ranges):
                n_pts += 1
                c, cp0, cp1 = chains(m, e, g0, ts)
                top = m - 1
                # PE2-EL4
                rho = [(ts[l - 1] + c[l - 1]) % e[l - 1] for l in range(1, m)]
                lhs4 = sum(ts[l - 1] * w[l - 1] for l in range(1, m))
                r4 = sum(rho[l - 1] * w[l - 1] for l in range(1, m))
                if lhs4 - r4 != c[top]:
                    fails.append(("PE2-EL4", m, e, g0, ts))
                if r4 > 1 - w[0]:
                    fails.append(("PE2-EL4b", m, e, g0, ts))
                # PE2-EL5i / cap
                if cp0[top] > c[top]:
                    fails.append(("PE2-EL5i", m, e, g0, ts))
                if cp1[top] > c[top] + 1:
                    fails.append(("PE2-EL5cap", m, e, g0, ts))
                # PE2-EL5cls
                tight = is_tight(m, e, g0, ts, c)
                if (cp1[top] == c[top] + 1) != tight:
                    fails.append(("PE2-EL5cls", m, e, g0, ts, cp1[top], c[top], tight))
                # PE2-EL8
                if tight:
                    n_tight += 1
                    for l in range(1, m):
                        if cp1[l] != c[l] + 1:
                            fails.append(("PE2-EL8c", m, e, g0, ts, l))
                    for l in range(2, m):
                        if (ts[l - 1] + cp1[l - 1]) % e[l - 1] != 0:
                            fails.append(("PE2-EL8r", m, e, g0, ts, l))
                # PE2-R3 + PE2-HEAD  (both Y)
                for Y, cp in ((0, cp0), (1, cp1)):
                    rhop = [(ts[l - 1] + cp[l - 1]) % e[l - 1]
                            for l in range(2, m)]
                    lhs3 = w[1 if m > 2 else top] * cp[1] + \
                        sum(ts[l - 1] * w[l - 2] for l in range(2, m))
                    # careful: w_{l-1} in the note's 1-indexed display is w[l-1]
                    # of THIS array; t_l pairs with w[l-1].
                    lhs3 = (w[0] * 0)  # recompute cleanly below
                    w1 = w[1] if m > 2 else Fraction(1)  # w_1; = 1 at m = 2
                    lhs3 = w1 * cp[1] + sum(ts[l - 1] * w[l - 1]
                                            for l in range(2, m))
                    rhs3 = cp[top] + sum(rhop[l - 2] * w[l - 1]
                                         for l in range(2, m))
                    if lhs3 != rhs3:
                        fails.append(("PE2-R3", Y, m, e, g0, ts))
                    head = sum(rhop[l - 2] * w[l - 1] for l in range(2, m))
                    if head > 1 - w1:
                        fails.append(("PE2-HEAD", Y, m, e, g0, ts))
                # PE2-R6 (single and double removals), tight corner, e0 >= 2
                if tight and e[0] >= 2:
                    rems = [P0 - e[0] * k - y
                            for k in range(0, g0) for y in (0, 1)]
                    for t in range(0, g0):
                        base = ts[0] + t * e[0] + 1
                        for R in rems:
                            if R < 1:
                                fails.append(("PE2-R6neg", m, e, g0, ts, R))
                            if (base - R) // P0 > cp1[1] - 1:
                                fails.append(("PE2-R6", m, e, g0, ts, t, R))
                        for Ra in rems:
                            for Rb in rems:
                                if (base - Ra - Rb) // P0 > cp1[1] - 1:
                                    fails.append(("PE2-R6d", m, e, g0, ts))

# PE2-W1a: the withdrawn unconditional step's refutation witness
e0, g0, t1, t, k, y = 2, 2, 4, 1, 1, 1
P0 = e0 * g0
rem = P0 - e0 * k - y
line1 = (t1 + t * e0 + 0 + 0 - rem) // P0        # true-ledger floor, Y2 = 0
cplus10 = (t1 + (g0 - 1) * e0 + 0) // P0
withdrawn_rhs = cplus10 - 1                       # unconditional -1[CE0]
w1a_refuted = line1 > withdrawn_rhs               # must be True (step false)

print(f"grid points: {n_pts}  (Y-tight among them: {n_tight})")
print(f"PE2-W1a withdrawn-step refutation at the note's witness: "
      f"line1={line1} > withdrawn_rhs={withdrawn_rhs} : {w1a_refuted}")
print(f"failures: {len(fails)}")
for f in fails[:20]:
    print("  FAIL:", f)
if not w1a_refuted:
    print("  FAIL: PE2-W1a (withdrawn step NOT refuted at witness)")
print("VERDICT:", "ALL GREEN" if (not fails and w1a_refuted) else "FAILURES")
