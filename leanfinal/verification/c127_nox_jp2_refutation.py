#!/usr/bin/env python3
"""C.127 clause (a) — REFUTATION of the UNFENCED stub signature (`j' ≥ 2 admitted).

Chapter C, NODE C.127 (LAW E-W, amendment A-C.4).  The blueprint STATEMENT fences the
member class at `j′ ≤ 1` ("the single-entry member `f = Φ₂^{μ₂} + c·π^α·x^a·Φ′^b·Φ₂^{j′}`
(`j′ ≤ 1`)"), and the node's TEETH row carries an explicit SCOPE FENCE ("`j′ ≥ 2` members
DEVIATE — no fleet agent may generalize the statement over `j′`").  The elaborated stub
`Leanspec.ChapC.lawEW_faithful_of_nox`, however, binds `(α a b j' : ℕ)` with NO `j′ ≤ 1`
hypothesis, i.e. it IS the forbidden generalization.  This script refutes it.

WHAT IS REFUTED (the stub's exact claim, all its other hypotheses satisfied):

    j' = 2, hnox holds through its right disjunct (`a + i₂ < D′`),
    yet  shadowDev T f j ≠ dev (composedKey T) f j  at coordinates j = 0, 1 (and 2).

WITNESS FRAME (F1)-(F5) with `μ₂ ≥ 3` so that `j′ = 2 < μ₂` is live:

    p ∈ {2, 3},  D′ = e₁ = 5,  f₁ = h = 1,  e₂ = 1,  m = f₂ = 5,
    i₂ = 1, v₂ = 2  ⇒  u₂ = D′v₂ + i₂ = 11,  v₀ = 11  (D′v₀ = 55 = m·u₂ ✓ on-side),
    δ = u₂ − D′ = 6 ≥ 1 ✓,  μ₂ = 3,  μ₂i₂ = 3 < 5 = D′ ✓ in-grid (F5),
    Φ′ = x⁵ − p,  Φ₂ = Φ′⁵ + p²x·Φ′⁴ + p¹¹.

WITNESS MEMBER: `c = 1, α = 0, a = 3, b ∈ {0,1,2}, j′ = 2`, i.e.

    f = Φ₂³ + x³·Φ′^b·Φ₂²,     a + i₂ = 4 < 5 = D′   (so `hnox` HOLDS)

but `a + 2i₂ = 5 ≥ D′`: the SECOND seed `E′P²` is over-grid, so the `Φ′`-digits of
`f` are not the coefficients of `E′Y^bK²`, a wrap is born, and the shadow read
separates from the honest read.  This is exactly the mechanism the proof note
(`lean/notes/openmath/LAWEW_PROOF_2026-08-16.md`, §5 item 1) names as OPEN: "the wrap
then spawns a SECOND seed (`E′P²` also over-grid)".  The note's §3 Step 1 uses
`a + i₂ < 2D′` and the single over-grid coefficient — both fail at `j′ ≥ 2`.

DECORRELATION.  The reads below are an INDEPENDENT implementation of the LEAN
definitions (C.71's `biRead`/`devQ`/`shadowDev` and B.02's `dev`), not of the paper
instrument: `shadow` runs the whole `Φ₂`-division inside `(ℤ[x]/Φ′)[Z]` and maps back
through the canonical degree-`< D′` representative, which is C.71 (iii) literally.
Leg 2 cross-checks every row against the certified battery
`verification/openmath/ewbs2_lawew_cert.py` (route E) when that file is importable.

Run: python3 leanfinal/verification/c127_nox_jp2_refutation.py
"""

import os
import sys

# ----------------------------------------------------------------------
# integer polynomial arithmetic (coefficient lists, low degree first)
# ----------------------------------------------------------------------


def strip(a):
    while a and a[-1] == 0:
        a = a[:-1]
    return a


def add(a, b):
    n = max(len(a), len(b))
    return strip([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
                  for i in range(n)])


def neg(a):
    return [-x for x in a]


def mul(a, b):
    if not a or not b:
        return []
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return strip(out)


def power(a, n):
    out = [1]
    for _ in range(n):
        out = mul(out, a)
    return out


def divmod_monic(f, g):
    """f = q*g + r with deg r < deg g, g monic (integer arithmetic is exact)."""
    assert g and g[-1] == 1
    f = list(strip(f))
    dg = len(g) - 1
    q = [0] * max(0, len(f) - dg)
    while len(strip(f)) - 1 >= dg and strip(f):
        f = strip(f)
        if len(f) - 1 < dg:
            break
        k = len(f) - 1 - dg
        c = f[-1]
        q[k] += c
        f = add(f, neg(mul([0] * k + [c], g)))
    return strip(q), strip(f)


def dev(f, phi, jmax):
    """B.02's development: dev phi f j for j = 0 .. jmax."""
    out = []
    cur = list(f)
    for _ in range(jmax + 1):
        q, r = divmod_monic(cur, phi)
        out.append(r)
        cur = q
    return out


# ----------------------------------------------------------------------
# the LEAN shadow read, implemented from C.71's body
# ----------------------------------------------------------------------


def bi_read(g, phi, m_hint):
    """C.71 (ii): the Z-polynomial whose Z^b coefficient is the class mod phi of the
    b-th phi-adic digit of g.  Classes are canonical (degree < deg phi) reps."""
    digits = dev(g, phi, max(m_hint, len(g)))
    return [d for d in digits]  # each already reduced mod phi


def z_strip(S):
    while S and not strip(S[-1]):
        S = S[:-1]
    return S


def z_mul_coeff(u, v, phi):
    return divmod_monic(mul(u, v), phi)[1]


def z_divmod_monic(A, K, phi):
    """monic division inside (Z[x]/phi)[Z]: A = Q*K + R, deg_Z R < deg_Z K."""
    A = z_strip([list(c) for c in A])
    K = z_strip([list(c) for c in K])
    assert K and strip(K[-1]) == [1], 'divisor must be Z-monic'
    dk = len(K) - 1
    Q = [[] for _ in range(max(0, len(A) - dk))]
    while len(A) - 1 >= dk and A:
        k = len(A) - 1 - dk
        c = A[-1]
        Q[k] = add(Q[k], c)
        for i, kc in enumerate(K):
            A[k + i] = add(A[k + i], neg(z_mul_coeff(c, kc, phi)))
        A = z_strip(A)
    return z_strip(Q), z_strip(A)


def dev_q(A, K, phi, jmax):
    """C.71 (i) `devQ` at the transported key."""
    out = []
    cur = [list(c) for c in A]
    for _ in range(jmax + 1):
        q, r = z_divmod_monic(cur, K, phi)
        out.append(r)
        cur = q
    return out


def reass(S, phi):
    """C.71 (iii)'s reassembly: canonical reps against the powers of phi."""
    out = []
    for b, c in enumerate(S):
        out = add(out, mul(divmod_monic(c, phi)[1], power(phi, b)))
    return strip(out)


def shadow_dev(f, phi, phi2, jmax):
    K = bi_read(phi2, phi, jmax + 4)
    A = bi_read(f, phi, jmax + 4)
    return [reass(S, phi) for S in dev_q(A, K, phi, jmax)]


# ----------------------------------------------------------------------
# the witness frame and the sweep
# ----------------------------------------------------------------------


def frame(p, Dp=5, i2=1, m=5, v2=2, v0=11, mu2=3, omega=1, c2h=1, c0h=1):
    u2 = Dp * v2 + i2
    assert Dp * v0 == m * u2, 'entry not on-side'
    assert mu2 * i2 < Dp, 'pure power not in-grid (F5)'
    assert u2 - Dp >= 1, 'margin delta < 1 (F4)'
    phi = [-p * omega] + [0] * (Dp - 1) + [1]
    P = [0] * i2 + [c2h * p ** v2]
    phi2 = add(add(power(phi, m), mul(P, power(phi, m - 1))), [c0h * p ** v0])
    return dict(p=p, Dp=Dp, i2=i2, m=m, u2=u2, mu2=mu2, phi=phi, phi2=phi2)


def member(fr, jp, a, b, alpha=0, c=1):
    C = mul([c * fr['p'] ** alpha], mul(power([0, 1], a), power(fr['phi'], b)))
    return add(power(fr['phi2'], fr['mu2']), mul(C, power(fr['phi2'], jp)))


def deltas(fr, f):
    jmax = fr['mu2'] - 1
    hon = dev(f, fr['phi2'], jmax)
    sh = shadow_dev(f, fr['phi'], fr['phi2'], jmax)
    return [strip(add(s, neg(h))) for s, h in zip(sh, hon)]


def main():
    violations, controls, rows = [], 0, 0
    print('C.127 clause (a): REFUTATION of the unfenced stub (no `j\' <= 1` fence)')
    print('=' * 74)
    for p in (2, 3):
        fr = frame(p)
        print('frame p=%d  D\'=%d i2=%d m=%d u2=%d mu2=%d delta=%d'
              % (p, fr['Dp'], fr['i2'], fr['m'], fr['u2'], fr['mu2'],
                 fr['u2'] - fr['Dp']))
        for a in (1, 3):
            for b in (0, 1, 2):
                for jp in (0, 1, 2):
                    rows += 1
                    f = member(fr, jp, a, b)
                    d = deltas(fr, f)
                    nz = [j for j, dd in enumerate(d) if dd]
                    nox = (jp == 0 or a + fr['i2'] < fr['Dp'])
                    if nox and nz:
                        violations.append((p, a, b, jp, nz))
                        tag = '  <== CLAUSE-(a) FALSE at the stub signature'
                    else:
                        tag = ''
                        if nox:
                            controls += 1
                    print('  a=%d b=%d j\'=%d | a+i2=%d a+2i2=%d | hnox=%s | '
                          'nonzero coords=%s%s'
                          % (a, b, jp, a + fr['i2'], a + 2 * fr['i2'], nox, nz, tag))
    print('-' * 74)
    print('rows read              : %d' % rows)
    print('hnox rows FAITHFUL     : %d  (the fenced law, j\' <= 1, and the in-grid j\'=2)'
          % controls)
    print('hnox rows VIOLATING    : %d  (all of them j\' = 2 with a + 2i2 >= D\')'
          % len(violations))
    for p, a, b, jp, nz in violations:
        print('   p=%d a=%d b=%d j\'=%d : Delta nonzero at coordinates %s' % (p, a, b, jp, nz))

    # ---------------- leg 2: cross-check against the certified battery ---------
    cross = 'SKIPPED (battery not importable from here)'
    try:
        here = os.path.dirname(os.path.abspath(__file__))
        batt = os.path.abspath(os.path.join(here, '..', '..', 'verification', 'openmath'))
        sys.path.insert(0, batt)
        import ewbs2_lawew_cert as ew  # noqa: E402
        agree = disagree = 0
        for p in (2, 3):
            frx = ew.trinomial_frame('J2p%d' % p, p, 5, 1, 5, 2, 11, 3)
            fr = frame(p)
            for a in (1, 3):
                for b in (0, 1, 2):
                    for jp in (0, 1, 2):
                        memb, _ = ew.entry_member(frx, jp, a, b, 0, 1)
                        theirs = [bool(dd) for dd in ew.measured_deltas(frx, memb)]
                        mine = [bool(dd) for dd in deltas(fr, member(fr, jp, a, b))]
                        if theirs == mine:
                            agree += 1
                        else:
                            disagree += 1
        cross = ('battery route E agrees on %d/%d rows (disagreements: %d)'
                 % (agree, agree + disagree, disagree))
    except Exception as exc:  # pragma: no cover - environment dependent
        cross = 'SKIPPED (%s)' % exc
    print('cross-check (leg 2)    : %s' % cross)
    print('-' * 74)
    ok = len(violations) > 0
    print('VERDICT: %s' % ('REFUTED — the stub signature admits false instances'
                           if ok else 'no violation found (unexpected)'))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
