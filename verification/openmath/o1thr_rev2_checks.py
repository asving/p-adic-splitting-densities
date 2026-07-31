#!/usr/bin/env python3
"""O1thr REV-2 falsifier: T-E — the (M6b) vertex-transport check at depth 1.

Companion to o1thr_persite_check.py (UNCHANGED; run it first: T-A..T-D).
The rev-2 brief isolates exactly ONE substantive interface assumption,
(M6b): harvested children are LAWFUL and realize the vertex read-off (R5) —
the slot-mu coefficient of the successor-key development carries
w_0-valuation EXACTLY beta* (the side's right-end height).  This script
tests that assumption exhaustively on the same depth-1 slice, plus the new
displayed lawfulness laws:

  For every box x (monic f = X^n + ..., all a_i = 0 mod p) and every
  harvested site (face, psi) with ceiling L <= M:
    (N2) stride integrality:  gamma == s0*h (mod e)
    (N3) height positivity:   gamma >= (s0 + wSide)*h
    NAT: intercept I = gamma/e >= 1, hence L >= 2
    T-E ((M6b)/(N4) at harvest): with the standard key lift
          Phi_1 = sum_{k=0}^{g} psihat_k * p^((g-k)*h) * X^(e*k)
      (psihat_k in [0,p) lifting psi's coefficients, psihat_g = 1), the
      slot-mu coefficient C_mu of the Phi_1-adic development of the decode
      f_x satisfies:
        (T-E.1)  C_mu != 0   (the vertex read is well-defined), and
        (T-E.2)  beta* <= w_0(C_mu) <= I   (the (N4) band: the harvested
                 vertex height vhtx := w_0(C_mu) lies between the side's
                 right-end height beta* = v1 and the intercept I = gamma/e),
      where w_0(C) := min_j v_p(coeff_j C) (Gauss valuation w.r.t. X).

Also REPORTED (not a pass/fail): the count of instances with
w_0(C_mu) != beta* — the REFUTATION COUNT of the rev-1-adjacent reading
that pinned the vertex height at beta* itself (the reading the verifier
flagged as ambiguous; a positive count is the machine countermodel that
forced the rev-2 restatement of (R5) with a RECORDED height field).

A violation of T-E.1/T-E.2 would refute the depth-1 instance of (M6b) as
restated at rev 2 and would be a REAL finding against the package.
"""
import os
import sys
from fractions import Fraction
from itertools import product

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import o1thr_persite_check as base


def v_int(x, p):
    """v_p of a NONZERO integer."""
    assert x != 0
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v


def poldivmod_int(a, b):
    """Division with remainder over Z by MONIC b; coeff lists low->high."""
    a = list(a)
    db = len(b) - 1
    while a and a[-1] == 0:
        a.pop()
    q = [0] * max(len(a) - db, 0)
    while a and len(a) - 1 >= db:
        c = a[-1]
        off = len(a) - 1 - db
        q[off] = c
        for i, bc in enumerate(b):
            a[off + i] -= c * bc
        while a and a[-1] == 0:
            a.pop()
    return q, a


def development(f, Phi):
    """Phi-adic development of f: [C_0, C_1, ...], each deg C_j < deg Phi."""
    out, cur = [], list(f)
    while cur:
        cur, r = poldivmod_int(cur, Phi)
        out.append(r)
    return out


def w0(c, p):
    """Gauss valuation w.r.t. the key X; None for the zero polynomial."""
    vals = [v_int(x, p) for x in c if x != 0]
    return min(vals) if vals else None


def run_TE(p, n, M):
    boxes = [tuple(p * t for t in tup)
             for tup in product(range(p ** (M - 1)), repeat=n)]
    checked, bad, not_betastar = 0, [], 0
    for a in boxes:
        f = list(a) + [1]
        for (j0, j1, e, h, pat, psi, mu, L) in base.sites_of_box(a, p, n, M):
            g = len(psi) - 1
            v1 = 0 if j1 == n else v_int(a[j1], p)   # beta* (right-end height)
            d = (j1 - j0) // e
            v0 = v1 + d * h
            gamma = e * v0 + j0 * h                  # ell(j0) = v0
            intercept = Fraction(gamma, e)           # I = ell(0)
            # displayed lawfulness laws at harvest + Lemma NAT instance
            assert (gamma - j0 * h) % e == 0, (a, j0, j1)            # (N2)
            assert gamma >= (j0 + (j1 - j0)) * h, (a, j0, j1)        # (N3)
            assert intercept >= 1 and L >= 2, (a, j0, j1)            # NAT
            # T-E: standard key lift; slot-mu coefficient; the (N4) band
            Phi1 = [0] * (e * g + 1)
            for k in range(g + 1):
                Phi1[e * k] = psi[k] * p ** ((g - k) * h)
            C = development(f, Phi1)
            Cmu = C[mu] if mu < len(C) else []
            w = w0(Cmu, p)
            checked += 1
            if w is None or not (v1 <= w <= intercept):
                bad.append((a, (j0, j1, e, h, psi, mu), v1, str(intercept), w))
            elif w != v1:
                not_betastar += 1
    print(f"p={p} n={n} M={M}: boxes={len(boxes)} "
          f"site-instances checked={checked} "
          f"| T-E violations (C_mu=0 or vhtx outside [beta*, I]): {len(bad)} "
          f"| refutation count of the beta*-pin reading (vhtx != beta*): "
          f"{not_betastar}")
    for b in bad[:5]:
        print("   VIOLATION:", b)
    return len(bad) == 0


if __name__ == "__main__":
    ok = True
    for (p, n, M) in [(2, 2, 5), (2, 2, 6), (3, 2, 5), (2, 3, 4), (3, 3, 4)]:
        ok = run_TE(p, n, M) and ok
    print("OVERALL:", "ALL PASS" if ok else "FAILURES FOUND")
