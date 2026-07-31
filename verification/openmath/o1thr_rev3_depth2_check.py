#!/usr/bin/env python3
"""O1thr REV-3 falsifier: T-F -- window-harvest completeness (M6c) at DEPTH 2.

The pass-2 verifier found that depth-1 checks are structurally blind to the
window-harvest completeness content (at depth 1 the root window is global,
so there are no beyond-window slots).  This script probes depth-2 states --
states o = [nu_0] reached by one root read -- where the full Phi_1-adic
development of f has slots BEYOND the window width mu.

Setup per (box, depth-1 site): f = decode of the box (monic, f-bar = X^n,
one X-track), site = (face (j0,v0)-(j1,v1), e, h, pat, psi, mu, L) harvested
from the root polygon, Phi_1 = standard key lift
    Phi_1 = sum_k psihat_k p^((g-k)h) X^(ek)   (deg = e*g),
(C_k) = the full Phi_1-adic development of f (exact integers), and

  sloped heights (the OM-faithful window convention pinned at rev 3):
    V(B)   := min_t ( e*v_p(b_t) + t*h )   (the nu_0-sloped Gauss valuation),
    gammahat := V(Phi_1)  (= e*g*h for the standard lift; asserted),
    u_k    := V(C_k) + k*gammahat          (window points: (k, u_k), k <= mu),

  plain heights (the rev-2 literal reading, probed for comparison):
    Wp_k   := e * w0(C_k)                  (w0 = min v_p over coefficients).

Checks (pass/fail unless marked REPORT):

  T-F.1 (vertex law / Lemma WGEO(b)): min_k u_k over ALL slots k equals
        gamma (the recorded side value), first attained EXACTLY at k = mu.
        In particular C_mu != 0 -- (M6b)(i) rederived -- and
        V(C_mu) = gamma - mu*gammahat exactly (Corollary VTX).
  T-F.2 ((M6c)(i), sloped): every face of the window hull (slots 0..mu of
        the u-points) has strictly negative slope, and every beyond-window
        point (k > mu, C_k != 0) lies STRICTLY ABOVE every window face's
        extended side line -- (R1) at all slots for every harvested child.
  T-F.3 ((M6c)(ii) polygon content): the strictly-negative-slope (principal)
        part of the FULL u-polygon (all slots) coincides with the window
        hull -- no phantom principal face uses beyond-window support.
  T-F.4 ((N4) upper bound rederived): vhtx := w0(C_mu) <= V(C_mu)/e
        = (gamma - mu*gammahat)/e <= I = gamma/e.
  T-F.5 (REPORT -- the plain reading): T-F.2/T-F.3 recomputed with the
        plain heights Wp_k.  Violations are tallied and exhibited, not
        failed: a positive count REFUTES the plain reading of the window
        convention (the depth-2 countermodel motivating the rev-3 pin);
        zero means the plain reading survives these configs numerically.
        Also tallied: (box, site) instances where the two conventions
        harvest DIFFERENT depth-2 face data (e', h') -- convention
        divergence even without an (M6c) violation.

Coverage requires beyond-window slots: floor(n / (e*g)) > mu; instances
without them are counted but only T-F.1/T-F.4 apply (window-only states
still test the vertex law).
"""
import os
import sys
from fractions import Fraction
from itertools import product

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import o1thr_persite_check as base
from o1thr_rev2_checks import v_int, development, w0


def V_sloped(c, p, e, h):
    """nu_0-sloped Gauss valuation min_t(e*v_p(c_t) + t*h); None for 0."""
    vals = [e * v_int(x, p) + t * h for t, x in enumerate(c) if x != 0]
    return min(vals) if vals else None


def hull_faces(pts):
    """Faces of the lower hull of integer points [(k, u)], k increasing."""
    hull = base.lower_hull(sorted(pts))
    return list(zip(hull, hull[1:]))


def principal(faces):
    """Strictly-negative-slope faces."""
    return [((x1, y1), (x2, y2)) for (x1, y1), (x2, y2) in faces if y2 < y1]


def strictly_above(k, u, face):
    """Is (k, u) strictly above the extended line of face? Exact integers."""
    (x1, y1), (x2, y2) = face
    return u * (x2 - x1) > y1 * (x2 - x1) + (k - x1) * (y2 - y1)


def run_TF(p, n, M):
    boxes = [tuple(p * t for t in tup)
             for tup in product(range(p ** (M - 1)), repeat=n)]
    stats = dict(inst=0, beyond=0, f1=0, f2=0, f3=0, f4=0,
                 plain2=0, plain3=0, diverge=0)
    ex = {}
    for a in boxes:
        f = list(a) + [1]
        for (j0, j1, e, h, pat, psi, mu, L) in base.sites_of_box(a, p, n, M):
            g = len(psi) - 1
            v1 = 0 if j1 == n else v_int(a[j1], p)
            v0 = v1 + ((j1 - j0) // e) * h
            gamma = e * v0 + j0 * h
            Phi1 = [0] * (e * g + 1)
            for k in range(g + 1):
                Phi1[e * k] = psi[k] * p ** ((g - k) * h)
            gammahat = V_sloped(Phi1, p, e, h)
            assert gammahat == e * g * h, (a, j0, j1, gammahat)
            C = development(f, Phi1)
            stats['inst'] += 1
            nslots = len(C) - 1               # top slot (monic => C top != 0)
            upts = [(k, V_sloped(C[k], p, e, h) + k * gammahat)
                    for k in range(len(C)) if any(C[k])]
            udict = dict(upts)
            # T-F.1 vertex law
            umin = min(u for _, u in upts)
            argmins = [k for k, u in upts if u == umin]
            if not (umin == gamma and min(argmins) == mu and mu in udict):
                stats['f1'] += 1
                ex.setdefault('f1', (a, (j0, j1, e, h, psi, mu), upts))
            # window hull (sloped) and its faces
            wpts = [(k, u) for k, u in upts if k <= mu]
            wfaces = hull_faces(wpts)
            if any(y2 >= y1 for (x1, y1), (x2, y2) in wfaces):
                stats['f2'] += 1        # a non-descending window face
                ex.setdefault('f2', (a, (j0, j1, e, h, psi, mu), wpts))
            beyond = [(k, u) for k, u in upts if k > mu]
            if beyond:
                stats['beyond'] += 1
                # T-F.2 beyond-window strictly above every window face line
                if any(not strictly_above(k, u, F)
                       for k, u in beyond for F in wfaces):
                    stats['f2'] += 1
                    ex.setdefault('f2', (a, (j0, j1, e, h, psi, mu),
                                         wpts, beyond))
                # T-F.3 full principal part == window hull
                if principal(hull_faces(upts)) != principal(wfaces):
                    stats['f3'] += 1
                    ex.setdefault('f3', (a, (j0, j1, e, h, psi, mu), upts))
            # T-F.4 (N4)-upper rederived
            vhtx = w0(C[mu], p) if mu < len(C) and any(C[mu]) else None
            VCmu = udict.get(mu)
            if (vhtx is None or VCmu is None
                    or not (Fraction(vhtx) <= Fraction(VCmu - mu * gammahat, e)
                            <= Fraction(gamma, e))):
                stats['f4'] += 1
                ex.setdefault('f4', (a, (j0, j1, e, h, psi, mu), vhtx, VCmu))
            # T-F.5 plain-reading probe (REPORT)
            ppts = [(k, e * w0(C[k], p)) for k in range(len(C)) if any(C[k])]
            pw = [(k, u) for k, u in ppts if k <= mu]
            pwf = hull_faces(pw)
            pbeyond = [(k, u) for k, u in ppts if k > mu]
            if any(not strictly_above(k, u, F)
                   for k, u in pbeyond for F in principal(pwf)):
                stats['plain2'] += 1
                ex.setdefault('plain2', (a, (j0, j1, e, h, psi, mu),
                                         pw, pbeyond))
            elif pbeyond and principal(hull_faces(ppts)) != principal(pwf):
                stats['plain3'] += 1
                ex.setdefault('plain3', (a, (j0, j1, e, h, psi, mu), ppts))
            if ([( (x2-x1, y1-y2) ) for (x1,y1),(x2,y2) in principal(pwf)]
                    != [((x2-x1, y1-y2)) for (x1,y1),(x2,y2) in
                        principal(wfaces)]):
                stats['diverge'] += 1
    hard = stats['f1'] + stats['f2'] + stats['f3'] + stats['f4']
    print(f"p={p} n={n} M={M}: boxes={len(boxes)} "
          f"site-instances={stats['inst']} with-beyond-window={stats['beyond']}"
          f"\n   T-F.1 vertex-law violations: {stats['f1']}"
          f" | T-F.2 (M6c)(i) sloped violations: {stats['f2']}"
          f" | T-F.3 (M6c)(ii) sloped violations: {stats['f3']}"
          f" | T-F.4 (N4)-upper violations: {stats['f4']}"
          f"\n   REPORT plain reading: (M6c)(i)-analogue violations:"
          f" {stats['plain2']} | (M6c)(ii)-analogue violations:"
          f" {stats['plain3']} | face-data divergence (e',h') sloped vs"
          f" plain: {stats['diverge']}")
    for key in ('f1', 'f2', 'f3', 'f4', 'plain2', 'plain3'):
        if key in ex and (key.startswith('f') and stats[key]
                          or key.startswith('plain') and stats[key]):
            print(f"   first {key} instance:", ex[key])
    return hard == 0, stats


if __name__ == "__main__":
    ok, tot = True, dict()
    for (p, n, M) in [(2, 3, 4), (2, 4, 4), (3, 3, 4), (3, 4, 3), (2, 6, 3)]:
        good, st = run_TF(p, n, M)
        ok = ok and good
        for k, v in st.items():
            tot[k] = tot.get(k, 0) + v
    print("TOTALS:", tot)
    print("OVERALL:", "ALL PASS" if ok else "FAILURES FOUND")
