#!/usr/bin/env python3
"""chapE_gate_q2.py — the retained executable regression for NODE E.65 (GC-8).

Mirror of every numeric expectation checked in
`leanfinal/Uniformity/ChapE/E65.lean` (the `q = 2` gate: the `n = 8` frame of
`EFF.HE7.57`, end-to-end).  Nothing here is a proof; it is the decorrelated
arithmetic leg, so that a drifted recursion in the Lean defs and a drifted
transcription in this script cannot agree by accident.

Frame (`EFF.HE7.57`):  level 1 `(e1, f1, h) = (2, 1, 1)`,
                       level 2 `(l, d_r) = (2, 1)` with slope numerator `u = 5`.
In E.01's letters a rung is `(l, g, u, T)`:
    base rung   = (2, 1, 1, 0)
    level-2 rung= (2, 1, 5, 2)      (T2 = D'h = 2 = base.nextT)

Recursions re-implemented from the blueprint, NOT read out of Lean:
    slotCount(l, g)        = l * g                       (E.02)
    nextT(R)               = slotCount * u               (E.02)
    nextBound(R, b)        = (slotCount - 1) * u + l * b (E.02)
    degAt(D0, 0)           = D0 * slotCount(base)        (E.05)
    degAt(D0, i+1)         = degAt(D0, i) * slotCount(rungs[i])   [1 if absent]
    boundAt(0)             = nextBound(base, 0)          (E.05)
    boundAt(i+1)           = nextBound(rungs[i] or base, boundAt(i))

Run:  python3 leanfinal/verification/chapE_gate_q2.py
Exit code 0 = all checks pass; 1 = a mismatch (a stop-the-line event per GC-11).
"""

from math import gcd

FAILURES = []


def check(label, got, want):
    ok = got == want
    print(f"  [{'ok' if ok else 'FAIL'}] {label}: got {got!r}, want {want!r}")
    if not ok:
        FAILURES.append(label)


# ---------------------------------------------------------------- rung layer

class Rung:
    """E.01's `RungDatum`, with its four field conditions re-checked."""

    def __init__(self, l, g, u, T):
        assert 1 <= l, "hl"
        assert 1 <= g, "hg"
        assert gcd(u, l) == 1, "hcop: Nat.Coprime u l"
        assert l * T < u, "hnode: l*T < u"
        self.l, self.g, self.u, self.T = l, g, u, T

    @property
    def slot_count(self):
        return self.l * self.g

    @property
    def next_T(self):
        return self.slot_count * self.u

    def next_bound(self, b):
        return (self.slot_count - 1) * self.u + self.l * b


class Ladder:
    """E.05's `LadderData` (base at threshold 0, rungs chained by `rungFollows`)."""

    def __init__(self, base, rungs):
        assert base.T == 0, "hbase"
        prev = base
        for r in rungs:
            assert r.T == prev.next_T, "hchain: rungFollows"
            prev = r
        self.base, self.rungs = base, rungs

    def deg_at(self, D0, i):
        d = D0 * self.base.slot_count
        for j in range(i):
            d *= self.rungs[j].slot_count if j < len(self.rungs) else 1
        return d

    def bound_at(self, i):
        b = self.base.next_bound(0)
        for j in range(i):
            r = self.rungs[j] if j < len(self.rungs) else self.base
            b = r.next_bound(b)
        return b


# ------------------------------------------------------- leg 1: the rungs

print("E.65 leg 1 — the rung recursions (E.02), frame EFF.HE7.57")
base = Rung(2, 1, 1, 0)
rung = Rung(2, 1, 5, 2)

check("D' = e1*f1 = base.slotCount", base.slot_count, 2)
check("T2 = D'h  = base.nextT", base.next_T, 2)
check("bound1 = (D'-1)h = base.nextBound(0)", base.next_bound(0), 1)
check("the level-2 rung sits at T2", rung.T, base.next_T)
check("T3 = L*u = 2*1*5 = rung.nextT", rung.next_T, 10)
check("bound2 = (L-1)u + l*bound1 = 1*5 + 2*1", rung.next_bound(1), 7)
check("off-by-one sentinel: rung.nextBound(0)", rung.next_bound(0), 5)

# ------------------------------------------------------ leg 2: the ladder

print("E.65 leg 2 — the same frame through the ladder (E.05)")
lad = Ladder(base, [rung])
check("degAt(1, 0) = D' ", lad.deg_at(1, 0), 2)
check("degAt(1, 1) = D'' = D'*l*d_r", lad.deg_at(1, 1), 4)
check("degAt(1, 2) stalls past the top rung", lad.deg_at(1, 2), 4)
check("boundAt(0)", lad.bound_at(0), 1)
check("boundAt(1)", lad.bound_at(1), 7)

# ------------------------------------------- leg 3: the mu2 = 2 dictionary

print("E.65 leg 3 — the mu2 = 2 dictionary at the frame (E.49/E.50, EFF.HE7.58)")
# rows 1-4 and 6 are decided; row 5 (alpha-refine) is a POINTER, value None.
mu2_sigma = {
    "oneSideHalf": [(8, 1)],
    "oneSideInert": [(4, 2)],
    "oneSideSplit": [(4, 1), (4, 1)],
    "twoSides": [(4, 1), (4, 1)],
    "refineRow": None,
    "peelRow": [(4, 1), (4, 1)],
}


def degree(sigma):
    return sum(e * f for e, f in sigma)


for row, val in mu2_sigma.items():
    if val is None:
        check(f"row {row} is a pointer (none)", val, None)
    else:
        check(f"row {row} has degree 8", degree(val), 8)

alphabet = {tuple(sorted(v)) for v in mu2_sigma.values() if v is not None}
check(
    "three letters, no fourth (EFF.HE7.61)",
    alphabet,
    {((8, 1),), ((4, 2),), ((4, 1), (4, 1))},
)

# ------------------------------------------- leg 4: the jump bounds at mu0=4

print("E.65 leg 4 — the jump bounds at mu0 = 4 (E.60 clause 2, E.07(ii))")
check(
    "2^(J+1) <= 4  ==>  J <= 1, on 0 <= J <= 8",
    all(J <= 1 for J in range(9) if 2 ** (J + 1) <= 4),
    True,
)
check(
    "2*m <= 4  ==>  m <= 2, on 0 <= m <= 8",
    all(m <= 2 for m in range(9) if 2 * m <= 4),
    True,
)
# the frame's own mass sequence: mu = 4 -> 2, one jump.
mu = [4, 2]
check("frame mass mu0", mu[0], 4)
check("frame halving 2*mu1 <= mu0", 2 * mu[1] <= mu[0], True)
check("frame attains mu2 = 2 (2*2 <= 4)", 2 * 2 <= 4, True)
check("n = D'' * mu2 = 4*2", lad.deg_at(1, 1) * mu[1], 8)

# a second jump at mu0 = 4 is impossible: it would need 4 <= mu1 and 2*mu1 <= 4.
check(
    "no J = 2 at mu0 = 4 (E.60 clause 2, contradiction form)",
    [m for m in range(1, 100) if 4 <= m and 2 * m <= 4],
    [],
)

print()
if FAILURES:
    print(f"FAILED ({len(FAILURES)}): " + ", ".join(FAILURES))
    raise SystemExit(1)
print("chapE_gate_q2: all checks pass (E.65 mirror).")
