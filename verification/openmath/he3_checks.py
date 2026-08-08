#!/usr/bin/env python3
r"""HE3 -- the mu = 3 stage sigma battery ([GENHN-HE(mu >= 3)]).

*** WIP AT COMMIT 1 (survival discipline: this file is committed
    PRELIMINARY, before any full run, together with the note skeleton
    lean/notes/openmath/HE3_PROOF_2026-08-08.md).  The DESIGN and the
    PREREGISTERED PREDICTIONS below are sealed as of this commit; legs
    are wired in subsequent commits, and the verdict is appended to the
    note only FROM the committed artifacts he3_checks_output.txt /
    he3_checks_results.json. ***

WHAT THIS TESTS.  THEOREM HE3.A (the stage-sigma recursion): at a
DECIDED stage leaf of a composite stage of multiplicity mu over the
stage ring R (complete DVR, e = e1, f = f1, residue K), with stage type
tau = {(e_s^i, f_s^i)}, Sum_i e_s^i f_s^i = mu, every disc != 0 lift
factors over O into exactly k irreducibles with

    sigma(f) = { (e1 * e_s^i , f1 * f_s^i) }_i .

First live case: mu = 3.  The battery works the genre

    E3(h) = (Q; e1 = 2, f1 = 1, mu = 3; h)   key Phi' = x^2 - z*pi^h,
            residual (y - z)^3, D' = e1 f1 = 2, deg f = D' mu = 6,

i.e. SEXTIC members with a degree-2 ramified key carrying a
multiplicity-3 residual -- exactly the "local degree budget 6" slice of
the charge -- plus the n = 7 embedded slice (sextic block times a split
linear sibling, extracted by GENIND-3's Hensel step).

MEMBER MODEL.  By LEMMA GENHN-1 the Phi'-adic development is a digit
bijection, so we enumerate STAGE COORDINATES directly:

    f = Phi'^3 + A2 Phi'^2 + A1 Phi' + A0 ,  A_j = a_j1 x + a_j0 ,
    dv := e1 v = 2 v ,   S := e1 h = 2h ,
    node: dv(A_j) >= (3 - j) S + 1     (entry floors)
    dv(A_j) = min(2 v(a_j0), 2 v(a_j1) + h).

Enumeration is over the window: digits of a_ji at heights < N.  Both
characteristics: O = Z_p (p in {2, 3}) and O = F_q[[t]] (q in {2, 3}),
the latter read by the same integer ladder with F_q[t]-arithmetic.
PARI factorpadic is available only on the Z_p side (that is the oracle
asymmetry disclosed by every prior unit); the F_q[[t]] rows are scored
against the label read plus the internal resultant identity.

THE FOUR LEGS.

 HE-NORM  LEMMA HE3-1 (the resultant identity), the engine of the whole
          proof, tested at EVERY test key:
              Sum_rho dv(Phi''(rho)) = D' * dv(B0),  f = B0 mod Phi''
          checked as  v(Res(f, Phi'')) == f1 * dv(B0)  with exact
          integer resultants (Bareiss on the Sylvester matrix), for
          Phi'' = Phi' and for every refined test key Phi' + s*n(kappa).

 HE-PSI   LEMMA HE3-3 (Psi-inversion): sample
              Psi(kappa) = Sum_rho dv(Phi'_{kappa,s}(rho))
          over integer kappa at generic letters, invert on the KNOWN
          slope set, and check the recovered slope counts equal
          D' * L_lambda (the polygon side lengths scaled by D').
          Cross-checked against the DIRECT count of root slopes read
          off PARI's factorization (per irreducible factor g:
          Sum_{rho in g} v(Phi'(rho)) = v(Res(g, Phi'))).

 HE-SIG   THEOREM HE3.A's dictionary: PARI sig(f, p) vs the stage-type
          prediction {(e1 e_s, f1 f_s)}, on every decided leaf, gated
          (embedded rows only) at the GENHN-S11.F extraction-certified
          perimeter.  At (e1, f1) = (2, 1), mu = 3 the five stage types
          and their predicted sigma:
              (3,1)               -> {(6,1)}
              (1,3)               -> {(2,3)}
              (1,1)+(2,1)         -> {(2,1),(4,1)}
              (1,1)+(1,2)         -> {(2,1),(2,2)}
              (1,1)+(1,1)+(1,1)   -> {(2,1),(2,1),(2,1)}   <-- 3 labels

 HE-BND   the sigma-resolution boundary: per row, the exact q-power of
          the sigma-UNDECIDED mass (members whose stage read does not
          decide at the window: repeated residuals still alive at the
          cap, plus the conservative drain), reported as a law and
          compared with the E3 species totals committed by GENHN
          (UND3/RAM3/ALPHA3).

TEETH (each must fire >= 1 or the verdict is RED).

 HE-T-UNDET  THE MECHANISM TOOTH.  On a 3-label member (stage type
             (1,1)^3, all three labels on ONE side), exhibit two
             DISTINCT nonnegative count vectors satisfying both
             identities that GENHN.C's mu = 2 proof uses (root count
             Sum n = D' mu, and the single resultant identity
             Sum n_lambda lambda = D' dv(A0)).  Their existence is the
             numerical certificate that the mu = 2 argument cannot
             reach mu = 3; the tooth FAILS (RED) if the mu = 2 system
             turns out to determine the counts after all.
 HE-T-SIG    dictionary flip: predicting {(6,1)} where the stage type is
             (1,1)^3 (or {(2,1)^3} where it is (3,1)) must be caught by
             PARI on >= 1 member.
 HE-T-NODE   entry-floor off-by-one: lowering one a_ji floor by 1 must
             break the genre parse (member leaves the opening locus) --
             the constructed loci are not accidentally floor-blind.
 HE-T-PSI    inversion with a corrupted slope set (one slope perturbed)
             must fail to reproduce the measured Psi.
 HE-T-CERT   on embedded (n = 7) rows, the uncertified tail must be
             NONEMPTY and must contain at least one PARI disagreement
             (the S11.F perimeter is real on both sides).

PREREGISTERED PREDICTIONS (sealed at this commit).

 Q1  HE-NORM: 0 violations at every test key of every member, both
     characteristics.  (If this fails, LEMMA HE3-1 is false and the
     whole proof collapses -- this is the single most load-bearing
     prediction of the unit.)
 Q2  HE-PSI: recovered slope counts == D' * L_lambda for every member;
     0 violations; and the PARI-direct slope census agrees.
 Q3  HE-SIG: 0 bad on every certified job; all five mu = 3 stage types
     realized at >= 1 member each across the rows (in particular the
     3-label type (1,1)^3, whose predicted sigma at (2,1) is
     {(2,1),(2,1),(2,1)}: a sextic splitting into three ramified
     quadratics).
 Q4  HE-BND: the sigma-undecided mass per row is an exact q-power
     (reported); the decided mass matches GENHN's committed E3 species
     totals on the shared rows (39,366 / 32,768 / 32,768 for
     (Z3,4,1) / (Z2,5,1) / (F2t,5,1)).
 Q5  all five teeth fire; verdict GREEN iff 0 violations and all teeth.

PINS (md5, checked as family HE-PIN at run time): genhn_checks.py,
genhn_checks_results.json, w12_checks.py, w10_checks.py.

PROVENANCE / DISCLOSURE.  The PARI oracle question is the pinned
w12_checks.GP_FUN `sig(f, p)` (factorpadic at precision 200 +
idealprimedec), reused verbatim with the same per-miss retry ladder
that GENHN's re-seal 2 introduced.  The E3 stage reader is written
FRESH here (independent of GENHN's) and tied to GENHN's committed E3
species totals on the shared rows -- a decorrelated second reader, not
a re-use.
"""

import sys, os, json, time, hashlib, itertools
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

WIP = True   # commit 1: legs not yet wired; main() prints the design

# ---------------------------------------------------------------- pins
PINS = ['genhn_checks.py', 'genhn_checks_results.json',
        'w12_checks.py', 'w10_checks.py']


def md5(path):
    with open(os.path.join(HERE, path), 'rb') as fh:
        return hashlib.md5(fh.read()).hexdigest()


# --------------------------------------------- exact integer resultant
def bareiss(M):
    """Exact determinant of an integer matrix (fraction-free)."""
    n = len(M)
    if n == 0:
        return 1
    A = [row[:] for row in M]
    sign, prev = 1, 1
    for k in range(n - 1):
        if A[k][k] == 0:
            piv = None
            for i in range(k + 1, n):
                if A[i][k] != 0:
                    piv = i
                    break
            if piv is None:
                return 0
            A[k], A[piv] = A[piv], A[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) // prev
        prev = A[k][k]
    return sign * A[n - 1][n - 1]


def resultant(f, g):
    """f, g : coefficient lists LOW-to-HIGH over Z.  Sylvester det."""
    m, n = len(f) - 1, len(g) - 1
    if m < 0 or n < 0:
        return 0
    N = m + n
    M = [[0] * N for _ in range(N)]
    for i in range(n):
        for j, c in enumerate(f):
            M[i][i + (m - j)] = c
    for i in range(m):
        for j, c in enumerate(g):
            M[n + i][i + (n - j)] = c
    return bareiss(M)


# ------------------------------------------------------------- main
def main():
    print('HE3 battery -- WIP at commit 1 (design sealed, legs pending)')
    print('pins:')
    for p in PINS:
        try:
            print('  %-32s %s' % (p, md5(p)))
        except OSError as e:
            print('  %-32s MISSING (%s)' % (p, e))
    return 0


if __name__ == '__main__':
    sys.exit(main())
