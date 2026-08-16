#!/usr/bin/env python3
"""OM-3 certification leg 3 (HYP.32, the CS-1 count-fibration's order-1 shadow):
LEMMA W12-S2.1, the level-0 product structure, checked as a BIJECTION by exact enumeration.

CLAIM CERTIFIED: over R = O/π^N, for a level-0 configuration f̄ = Π_i P̄_i^{m_i} (P̄_i distinct
monic irreducibles over the residue field k = O/π), the multiplication map
    (F_1, …, F_s) ↦ Π_i F_i
from  Π_i {monic F_i of degree m_i·d_i over R with reduction P̄_i^{m_i}}
onto  {monic f of degree n over R with reduction f̄}
is a bijection.  (The σ-branchwise clause of S2.1 is NOT exercised here — this leg certifies the
count-fibration transport only; stated in the unit note.)

Since |Π_i branches| = |target fiber| = |k|^{(N−1)n} holds by construction, the content is
INJECTIVITY + fiber membership, both checked exhaustively.

Rings: mixed characteristic R = ℤ/p^N (p = 2, 3) AND equal characteristic R = F_q[t]/(t^N)
(q = 2, 3, 4 — prime-power residue field included).  Degrees n ≤ 4, windows N ≤ 3 (N ≤ 4 at the
smallest cells).  All arithmetic exact.

Exit 0 iff every check passes.
"""

import sys
from itertools import product

from om3_residual_census_check import FF, pmul as ffpmul, pnorm as ffpnorm

# ---------------------------------------------------------------------------------------------
# Ring abstraction: elements hashable; ops (add, mul, neg); residue map; lifts of a residue.
# ---------------------------------------------------------------------------------------------


class ZmodPN:
    """ℤ/p^N with residue field F_p."""

    def __init__(self, p, N):
        self.p, self.N, self.mod = p, N, p ** N
        self.zero, self.one = 0, 1
        self.name = f"Z/{p}^{N}"

    def add(self, a, b):
        return (a + b) % self.mod

    def mul(self, a, b):
        return (a * b) % self.mod

    def res(self, a):
        return a % self.p

    def lifts(self, r):
        return [r + self.p * j for j in range(self.p ** (self.N - 1))]

    def res_elts(self):
        return list(range(self.p))


class SeriesQN:
    """F_q[t]/(t^N) with residue field F_q (q = p^k via FF)."""

    def __init__(self, p, k, N):
        self.F = FF(p, k)
        self.N = N
        self.zero = (self.F.zero,) * N
        self.one = (self.F.one,) + (self.F.zero,) * (N - 1)
        self.name = f"F{self.F.q}[[t]]/t^{N}"

    def add(self, a, b):
        return tuple(self.F.add(x, y) for x, y in zip(a, b))

    def mul(self, a, b):
        F, N = self.F, self.N
        out = [F.zero] * N
        for i, x in enumerate(a):
            if x != F.zero:
                for j, y in enumerate(b):
                    if i + j < N:
                        out[i + j] = F.add(out[i + j], F.mul(x, y))
        return tuple(out)

    def res(self, a):
        return a[0]

    def lifts(self, r):
        return [(r,) + tail for tail in product(self.F.elts, repeat=self.N - 1)]

    def res_elts(self):
        return list(self.F.elts)


# ---------------------------------------------------------------------------------------------
# Polynomials over R: tuples low→high of fixed length deg+1, leading coefficient = R.one.
# ---------------------------------------------------------------------------------------------


def polmul(R, a, b):
    out = [R.zero] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = R.add(out[i + j], R.mul(x, y))
    return tuple(out)


def polres(R, a):
    return tuple(R.res(c) for c in a)


def monic_lifts(R, resid_poly):
    """All monic polys over R of the residue poly's degree reducing to it."""
    deg = len(resid_poly) - 1
    choices = [R.lifts(resid_poly[i]) for i in range(deg)]
    for lower in product(*choices):
        yield tuple(lower) + (R.one,)


# residue-field polynomial helpers (residue elements are R.res-images; for ZmodPN they are ints
# mod p — multiply via a SeriesQN-free path: reuse FF for series case, ints for Zmod case).


def respoly_mul(R, a, b):
    if isinstance(R, ZmodPN):
        out = [0] * (len(a) + len(b) - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                out[i + j] = (out[i + j] + x * y) % R.p
        return tuple(out)
    F = R.F
    return tuple(x for x in ffpmul(F, tuple(a), tuple(b))) if a and b else ()


def respoly_pow(R, a, m):
    out = a
    for _ in range(m - 1):
        out = respoly_mul(R, out, a)
    return out


def check_shape(R, branches, label):
    """branches: list of residue polys P̄_i (coeff tuples over residue field, monic) with
    multiplicities m_i.  Verifies the S2.1 bijection for f̄ = Π P̄_i^{m_i}."""
    # residue-branch polys P̄_i^{m_i}
    rbranch = [respoly_pow(R, P, m) for (P, m) in branches]
    fbar = rbranch[0]
    for rb in rbranch[1:]:
        fbar = respoly_mul(R, fbar, rb)
    n = len(fbar) - 1
    # branch lift sets
    sets = [list(monic_lifts(R, rb)) for rb in rbranch]
    sizes = [len(s) for s in sets]
    # multiplication map
    seen = {}
    dup = None
    for combo in product(*sets):
        f = combo[0]
        for g in combo[1:]:
            f = polmul(R, f, g)
        if f in seen:
            dup = (seen[f], combo)
            break
        seen[f] = combo
        if polres(R, f) != fbar:
            print(f"[FAIL] {label}: product leaves the fiber")
            return False
    total = 1
    for s in sizes:
        total *= s
    fiber_size = len(list(monic_lifts(R, fbar)))
    inj = dup is None and len(seen) == total
    surj = len(seen) == fiber_size
    ok = inj and surj
    print(f"[{'OK ' if ok else 'FAIL'}] {label}: R={R.name} n={n} branch sizes={sizes} "
          f"products={len(seen)} fiber={fiber_size} inj={inj} surj={surj}")
    return ok


def lin(R, c):
    """Residue linear poly x − c ≡ x + (−c): low→high (−c, 1) over the residue field."""
    if isinstance(R, ZmodPN):
        return ((-c) % R.p, 1)
    F = R.F
    return (tuple((-x) % F.p for x in c), F.one)


def main():
    okall = True
    # ---- mixed characteristic ----
    for p, N in [(2, 2), (2, 3), (3, 2)]:
        R = ZmodPN(p, N)
        x0, x1 = lin(R, 0), lin(R, 1)
        # n = 2: split (x)(x−1)
        okall &= check_shape(R, [(x0, 1), (x1, 1)], "n2 split")
        # n = 3: double branch (x)²·(x−1)
        okall &= check_shape(R, [(x0, 2), (x1, 1)], "n3 dbl+lin")
        # n = 3: (x)·(irreducible quadratic)
        irrq = (1, 1, 1) if p == 2 else (1, 0, 1)  # x²+x+1 / x²+1
        okall &= check_shape(R, [(x0, 1), (irrq, 1)], "n3 lin+quad")
        if N <= 2 or p == 2:
            # n = 4: two double branches (x)²(x−1)² — the two-same-(d,m)-branch shape
            okall &= check_shape(R, [(x0, 2), (x1, 2)], "n4 dbl·dbl")
            # n = 4: triple + linear
            okall &= check_shape(R, [(x0, 3), (x1, 1)], "n4 tpl+lin")
            # n = 4: (x)(x−1)(irr quad) — three branches, mixed degrees
            okall &= check_shape(R, [(x0, 1), (x1, 1), (irrq, 1)], "n4 lin·lin·quad")
    # deeper window at the smallest cell
    R = ZmodPN(2, 4)
    okall &= check_shape(R, [(lin(R, 0), 2), (lin(R, 1), 1)], "n3 dbl+lin deepN")
    # ---- equal characteristic ----
    for p, k, N in [(2, 1, 2), (2, 1, 3), (3, 1, 2), (2, 2, 2)]:
        R = SeriesQN(p, k, N)
        F = R.F
        elts = F.elts
        c0, c1 = elts[0], elts[1]  # 0 and 1 (as F-tuples? elts[0] is all-zero, elts[1] = (1,0..)?)
        # find zero and one explicitly
        c0 = F.zero
        c1 = F.one
        x0, x1 = lin(R, c0), lin(R, c1)
        okall &= check_shape(R, [(x0, 1), (x1, 1)], "n2 split")
        okall &= check_shape(R, [(x0, 2), (x1, 1)], "n3 dbl+lin")
        if F.q == 2:
            irrq = ((F.zero if False else F.one), F.one, F.one)  # x²+x+1 over F_2
            irrq = (F.one, F.one, F.one)
            okall &= check_shape(R, [(x0, 1), (irrq, 1)], "n3 lin+quad")
            if N <= 3:
                okall &= check_shape(R, [(x0, 2), (x1, 2)], "n4 dbl·dbl")
        if F.q == 4 and N == 2:
            # three distinct linear branches over F_4 — needs |k| ≥ 3 letters
            c2 = elts[2] if elts[2] not in (c0, c1) else elts[3]
            okall &= check_shape(R, [(x0, 2), (lin(R, c1), 1), (lin(R, c2), 1)], "n4 dbl·lin·lin F4")
    print("\nRESULT:", "ALL CHECKS PASS" if okall else "FAILURES PRESENT")
    sys.exit(0 if okall else 1)


if __name__ == "__main__":
    main()
