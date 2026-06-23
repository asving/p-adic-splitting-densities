"""Exact p-adic factorization-type oracle for degrees <= 3 over Q_p.

All inputs are exact Python integers; the only truncation is the Newton lift
precision NEWTON_DIGITS, with an explicit UND (undecided) escape that callers
must count (expected frequency ~ p^-50 with 60-digit sampling: effectively 0).

Type codes (n=3): '111', '12', '3', '1r1' (=(1)(1^2)), '1c' (=(1^3)).
Type codes (n=2): 'split', 'inert', 'ram'.
Every step is a theorem: Hensel (coprime reduction), Newton polygons,
quadratic discriminant square classes (incl. the p=2 mod-8 classification).
No step assumes p is tame.
"""

NEWTON_DIGITS = 240


def vp(n, p):
    """p-adic valuation of a nonzero integer; None for 0."""
    if n == 0:
        return None
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def quad_type(a, b, p, prec=None):
    """Type of x^2 + a x + b over Q_p, exact. prec: trust a,b mod p^prec only."""
    D = a * a - 4 * b
    if D == 0:
        return 'UND'
    v = vp(D, p)
    if prec is not None and v >= 2 * prec - 20:
        return 'UND'
    if v % 2 == 1:
        return 'ram'
    u = D // p ** v
    if p == 2:
        m = u % 8
        return 'split' if m == 1 else ('inert' if m == 5 else 'ram')
    return 'split' if pow(u % p, (p - 1) // 2, p) == 1 else 'inert'


def _residue_roots_mults(coeffs, p):
    """Roots with multiplicities over F_p of a monic poly given by int coeffs
    [c_{d-1},...,c_0] (descending, monic implied). Multiplicity by repeated
    synthetic division (char-blind)."""
    d = len(coeffs)
    out = {}
    for r in range(p):
        cur = [1] + [c % p for c in coeffs]
        mult = 0
        while True:
            # synthetic division of cur by (x - r) mod p
            q = [cur[0]]
            for c in cur[1:]:
                q.append((q[-1] * r + c) % p)
            rem = q.pop()
            if rem != 0:
                break
            mult += 1
            cur = q
            if len(cur) == 1:
                break
        if mult:
            out[r] = mult
    return out


def _newton_lift_simple_root(c2, c1, c0, r0, p):
    """Lift simple residue root r0 of x^3+c2x^2+c1x+c0 to mod p^NEWTON_DIGITS."""
    target = p ** NEWTON_DIGITS
    pk = p
    r = r0 % p
    while pk < target:
        pk = min(pk * pk, target)
        fr = ((r + c2) * r + c1) * r + c0
        dfr = (3 * r + 2 * c2) * r + c1
        r = (r - fr * pow(dfr, -1, pk)) % pk
    return r


def cubic_type_monic(c2, c1, c0, p, depth=0):
    """Factorization type of x^3 + c2 x^2 + c1 x + c0 over Q_p (exact ints)."""
    if depth > 60:
        return 'UND'
    roots = _residue_roots_mults([c2, c1, c0], p)
    if not roots:
        # rootless cubic over F_p is irreducible -> unramified cubic
        return '3'
    mults = sorted(roots.values())
    if mults == [1, 1, 1]:
        return '111'
    if mults == [1]:
        return '12'  # simple rational + irreducible quadratic, both Hensel
    if mults == [1, 2]:
        # lift the SIMPLE root, divide it out, classify the pair cluster
        rs = [r for r, m in roots.items() if m == 1][0]
        u = _newton_lift_simple_root(c2, c1, c0, rs, p)
        # f = (x-u)(x^2 + a x + b): a = c2+u, b = c1+u*a  (exact mod p^N)
        pN = p ** NEWTON_DIGITS
        a = (c2 + u) % pN
        b = (c1 + u * a) % pN
        qt = quad_type(a, b, p, prec=NEWTON_DIGITS)
        return {'split': '111', 'inert': '12', 'ram': '1r1', 'UND': 'UND'}[qt]
    # triple residue root at r: translate exactly (r is a small exact integer)
    r = next(iter(roots))
    A = c2 + 3 * r
    B = c1 + 2 * c2 * r + 3 * r * r
    C = c0 + c1 * r + c2 * r * r + r ** 3
    if C == 0 or B == 0 and False:
        pass
    if C == 0:
        return 'UND'  # exact root collision; measure zero, resample
    vC = vp(C, p)
    vB = vp(B, p)  # None == +infinity
    if vC == 1:
        return '1c'                       # W1: slope 1/3
    if vC == 2:
        if vB == 1:
            return '1r1'                  # W2: slopes (1, 1/2)
        return '1c'                       # W3: slope 2/3
    # vC >= 3
    if vB == 1:
        return '1r1'                      # W4: slopes (>=2, 1/2)
    # W5: vA>=1, vB>=2, vC>=3: all roots in m, rescale exactly and recurse
    return cubic_type_monic(A // p, B // p ** 2, C // p ** 3, p, depth + 1)


# ---------- projective (binary cubic forms / P^3 normalization) ----------

def _translate_form(co, c):
    """[a3,a2,a1,a0] -> coefficients of F(x+c) (dehomogenized translate)."""
    a3, a2, a1, a0 = co
    return [a3,
            a2 + 3 * a3 * c,
            a1 + 2 * a2 * c + 3 * a3 * c * c,
            a0 + a1 * c + a2 * c * c + a3 * c ** 3]


def cubic_type_proj(co, p):
    """Type of a binary cubic form [a3,a2,a1,a0] (primitive) over Q_p."""
    rb = [a % p for a in co]
    if all(v == 0 for v in rb):
        return 'IMPRIM'
    # find P0 in P^1(F_p) with Fbar(P0) != 0, move it to infinity
    if rb[0] != 0:
        w = co  # infinity already a non-root (leading unit)
    else:
        c_found = None
        for c in range(p):
            val = ((rb[0] * c + rb[1]) * c + rb[2]) * c + rb[3]
            if val % p != 0:
                c_found = c
                break
        if c_found is None:
            # Fbar vanishes on all of P^1(F_p): only possible as 3 simple
            # roots (p=2, xy(x+y)) -> Hensel -> three rational roots
            return '111'
        # translate c_found -> 0, then swap 0 <-> infinity
        w = _translate_form(co, c_found)[::-1]
    a3, a2, a1, a0 = w
    # monicize by root-scaling (a3 a unit): G = x^3+a2x^2+(a1a3)x+(a0a3^2)
    return cubic_type_monic(a2, a1 * a3, a0 * a3 * a3, p)


# ---------- formulas (derived 2026-06-13, see ASSERTIONS.md A7) ----------

from fractions import Fraction as Fr


def monic_quad_pred(q):
    q = Fr(q)
    return {'split': q / (2 * (q + 1)), 'inert': q / (2 * (q + 1)),
            'ram': 1 / (q + 1)}


def monic_cubic_pred(q):
    q = Fr(q)
    d = q ** 5 - 1
    return {
        '111': q ** 3 * (q - 1) * (q * q - q + 1) / (6 * (q + 1) * d),
        '12':  q ** 3 * (q ** 3 - 1) / (2 * (q + 1) * d),
        '3':   q ** 3 * (q * q - 1) / (3 * d),
        '1r1': q * (q - 1) * (q ** 3 + q + 1) / ((q + 1) * d),
        '1c':  (q - 1) * (q * q + 1) / d,
    }


def proj_cubic_pred(q):
    """Projective system: residue configs + cluster couplings into monic unknowns."""
    q = Fr(q)
    x = 1 / q
    P3 = q ** 3 + q ** 2 + q + 1
    s = monic_quad_pred(q)
    t = monic_cubic_pred(q)
    cfg = {
        '111': q * (q + 1) * (q - 1) / 6,
        '12':  (q + 1) * q * (q - 1) / 2,
        '3':   (q ** 3 - q) / 3,
        '1r1': 0,
        '1c':  0,
    }
    dbl = (q + 1) * q   # double+simple configs
    tri = (q + 1)       # triple configs
    out = {}
    out['111'] = (cfg['111'] + dbl * x * s['split'] + tri * x ** 3 * t['111']) / P3
    out['12'] = (cfg['12'] + dbl * x * s['inert'] + tri * x ** 3 * t['12']) / P3
    out['3'] = (cfg['3'] + tri * x ** 3 * t['3']) / P3
    out['1r1'] = (dbl * ((1 - x) + x * s['ram']) + tri * (x * (1 - x))
                  + tri * x ** 3 * t['1r1']) / P3
    out['1c'] = (tri * ((1 - x) * (1 + x * x)) + tri * x ** 3 * t['1c']) / P3
    return out


def paper_111_pred(q):
    q = Fr(q)
    Phi = q ** 4 + q ** 3 + q ** 2 + q + 1
    return (q * q + 1) ** 2 / (6 * Phi)
