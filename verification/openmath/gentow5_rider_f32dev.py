#!/usr/bin/env python3
"""GENTOW5 rider (post-PE4) helper — PE4-F-2 machine leg.

Exact-integer verification that S9's f32 "digit expansion" display,
once completed with the key relation Phi_2^2 = Phi_3 + 16 Phi_1,
yields the CANONICAL Phi_3-adic development

    f32 = Phi_3^4 - 512 Phi_2 Phi_3^2 + 2^20 Phi_1

(the +2^16 Phi_3 from the completion cancels the displayed
-2^16 Phi_3 term), whose slot pins reproduce the committed artifact
row "f32@Phi3: pins [340, 'inf', 186, 'inf', 0]"
(gentow5_output_exact.txt, byte-frozen md5 dc499a49...).

Sealed artifacts are NOT touched: this is a standalone reader-side
check, pure integer polynomial arithmetic (no sympy, no PARI).
Ladder values consumed: v(Phi_1) = 5/4, v(Phi_2) = 21/8 at f32's
roots (S4.2, artifact-exact); dv_4 = 16*v.
"""
from fractions import Fraction as F

def padd(f, g):
    n = max(len(f), len(g))
    return [(f[i] if i < len(f) else 0) + (g[i] if i < len(g) else 0)
            for i in range(n)]

def pscale(c, f):
    return [c * a for a in f]

def pmul(f, g):
    r = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        if a:
            for j, b in enumerate(g):
                r[i + j] += a * b
    return r

def psub(f, g):
    return padd(f, pscale(-1, g))

def norm(f):
    while len(f) > 1 and f[-1] == 0:
        f = f[:-1]
    return f

def deg(f):
    return len(norm(f)) - 1

X = [0, 1]
P1 = psub(pmul(X, X), [2])                # Phi_1 = x^2 - 2
P2 = psub(pmul(P1, P1), pscale(4, X))     # Phi_2 = Phi_1^2 - 4x
P3 = psub(pmul(P2, P2), pscale(16, P1))   # Phi_3 = Phi_2^2 - 16 Phi_1
P4 = psub(pmul(P3, P3), pscale(256, P2))  # Phi_4 = Phi_3^2 - 256 Phi_2
f32 = psub(pmul(P4, P4), pscale(2**16, P3))

checks = []
P3_2 = pmul(P3, P3)
P3_4 = pmul(P3_2, P3_2)

# 1. the S9 halfway identity, as displayed, is exact
halfway = padd(padd(psub(P3_4, pscale(512, pmul(P2, P3_2))),
                    pscale(-2**16, P3)),
               pscale(2**16, pmul(P2, P2)))
checks.append(("halfway identity exact", norm(psub(f32, halfway)) == [0]))

# 2. the completion relation (Phi_3's defining relation, re-arranged)
checks.append(("Phi_2^2 == Phi_3 + 16 Phi_1",
               norm(psub(pmul(P2, P2), padd(P3, pscale(16, P1)))) == [0]))

# 3. the canonical dev: -2^16 Phi_3 cancels
canon = padd(psub(P3_4, pscale(512, pmul(P2, P3_2))), pscale(2**20, P1))
checks.append(("canonical dev f32 == Phi_3^4 - 512 Phi_2 Phi_3^2 + 2^20 Phi_1",
               norm(psub(f32, canon)) == [0]))

# 4. slot legality: canonical coefficient degrees < deg Phi_3 = 8
checks.append(("slot degrees (C_2, C_0) = (4, 2) < 8",
               (deg(pscale(-512, P2)), deg(pscale(2**20, P1)), deg(P3))
               == (4, 2, 8)))

# 5. pins on dv_4 = 16*v: C_0 = 2^20 Phi_1 -> 340; C_2 = -512 Phi_2
#    -> 186; C_1 = C_3 = 0 -> inf; C_4 = 1 -> 0 (= artifact row)
p0 = 16 * (20 + F(5, 4))
p2 = 16 * (9 + F(21, 8))
checks.append(("pins (340, inf, 186, inf, 0) reproduced",
               (p0, p2) == (340, 186)))

# 6. j = 2 strictly above the chord (0,340)->(4,0): chord@2 = 170
checks.append(("j = 2 clearance: 186 > chord 170", p2 > F(340 * 2, 4)))

# 7. the OTHER S9 display (Phi_4 @ Phi_2) is already canonical
phi4dev = padd(psub(pmul(pmul(P2, P2), pmul(P2, P2)),
                    pscale(32, pmul(P1, pmul(P2, P2)))),
               pscale(1024, X))
checks.append(("Phi_4 == Phi_2^4 - 32 Phi_1 Phi_2^2 + 1024x (canonical)",
               norm(psub(P4, phi4dev)) == [0]))

bad = 0
for name, ok in checks:
    print(("PASS" if ok else "FAIL"), "-", name)
    bad += (not ok)
print(f"{len(checks) - bad}/{len(checks)} checks passed, {bad} violations")
raise SystemExit(1 if bad else 0)
