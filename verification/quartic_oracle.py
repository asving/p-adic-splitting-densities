"""Trusted quartic (and general low-degree) p-adic factorization oracle via PARI factorpadic
(cypari2). Calibrated 2026-06-14 against 9 known cases incl. Q_2(zeta_8)=(4,1) totally ramified.

Returns the factorization type as the sorted multiset of (e_i, f_i) over the irreducible Q_p
factors, sum e_i f_i = n. Coarse type (factor-degree multiset) is fast (factorpadic only);
(e,f) refinement uses a Krasner lift + idealprimedec (slower; used where needed).

Run with: /workspace-vast/asving/envs/padic/bin/python
"""
from cypari2 import Pari
from cypari2.handle_error import PariError

pari = Pari(size=1 << 28)            # 256 MB stack; grows on overflow via _nfinit
pari.allocatemem(1 << 28, silent=True)


def _nfinit(G, p):
    """nfinit at p only (partial discriminant factorization [G,[p]]) — avoids factoring the
    huge full quartic discriminant. Auto-grows the stack on overflow."""
    for _ in range(6):
        try:
            return pari.nfinit([G, [p]])
        except PariError:
            pari.allocatemem(0, silent=True)   # double the stack and retry
    return pari.nfinit([G, [p]])


def _ef_of_factor(g, p, prec):
    """(e,f) of Q_p[x]/(g), g irreducible over Q_p (t_POL with t_PADIC coeffs)."""
    d = int(pari.poldegree(g))
    if d == 1:
        return (1, 1)
    G = pari.liftall(g)                 # monic integer poly congruent to g mod p^prec
    nf = _nfinit(G, p)
    dec = pari.idealprimedec(nf, p)
    for pr in dec:
        e, f = int(pr[2]), int(pr[3])
        if e * f == d:                  # the unique prime matching our irreducible local factor
            return (e, f)
    return (int(dec[0][2]), int(dec[0][3]))


def coarse_type(coeffs_or_poly, p, prec=30):
    """Multiset of irreducible-factor DEGREES over Q_p (fast: factorpadic only).
    coeffs_or_poly: a PARI poly string, or list of int coeffs LOW->HIGH (monic implied if leading
    omitted? no: pass full coeffs incl leading)."""
    f = _as_pol(coeffs_or_poly)
    fac = pari.factorpadic(f, p, prec)
    return tuple(sorted(int(pari.poldegree(g)) for g in fac[0]))


def full_type(coeffs_or_poly, p, prec=30):
    """Sorted multiset of (e_i,f_i). Trustworthy but slower (idealprimedec per nonlinear factor)."""
    f = _as_pol(coeffs_or_poly)
    fac = pari.factorpadic(f, p, prec)
    return tuple(sorted(_ef_of_factor(g, p, prec) for g in fac[0]))


def _as_pol(x):
    if isinstance(x, str):
        return pari(x)
    # list of int coeffs low->high
    return pari.Pol(list(reversed([int(c) for c in x])))


if __name__ == '__main__':
    cal = [('x^4+4', 2), ('x^4+12', 2), ('x^4+4*x+4', 2), ('x^4-2', 2),
           ('x^4+1', 2), ('x^2-2', 2), ('x^2-5', 2), ('x^3-2', 3), ('x^2-3', 3)]
    for poly, p in cal:
        print(f"{poly:12s}/Q_{p}: coarse={coarse_type(poly,p)} full={full_type(poly,p)}")
