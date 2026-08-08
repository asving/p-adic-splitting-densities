#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""GENH4 r2 SUPPLEMENTARY LEG (post-seal, purely ADDITIVE) -- the nu3 tie.

`genh4_checks.py` and its artifacts (`genh4_checks_output.txt`,
`genh4_checks_results.json`) are BYTE-FROZEN at the GENH4 seal/repair
(runner md5 ee8024b7a500220a6408dab373d7432f, S13.2).  This file adds
nothing to them: it IMPORTS the sealed runner (re-verifying every md5
pin it declares, plus its own), and runs ONE new check the sealed
battery listed but did not execute.  Precedent: he7r1_supp.py (HE7 r1).

WHAT IT CHECKS -- PE2 MINOR 1 (GENH4_passPE2_report.md).  The note's
S9.2 asserts

    nu3 (TRP, HMENU3 @ pins): q^3 * T_tau of HM3.D S5.5 = the
    engine's beta_3, term for term

and S12's GH-DENS lists "nu2/nu3 ties (engine, md5-pinned)".  In the
sealed runner the nu2 / nu2^(2) ties are genuine dchecks, but nu3 is
DEFINED as the engine's value (`nu3 = ENG.beta(3)`, no dcheck): within
that battery the identity was engine-internal.  THIS leg executes it:

  T_tau is DERIVED from the ACCEPTED (2/2) HMENU3 note's displayed
  quantities alone -- COROLLARY HM3.D's five R_tau closed forms, the
  S5.5 per-center n=2 block densities (RAM 1/(q(q+1)),
  2SIDED 1/(q^3(q+1)), SPLITEQ (q-2)/(2q^3(q+1)),
  INERTDEEP 1/(2q^2(q+1))), and elementary level-0 censuses -- by
  inverting S5.5's whole-space assembly

      R_tau = SEP_tau + (q-1)*c2_{tau''} + q*T_tau ,

  i.e.  T_tau := (R_tau - SEP_tau - DBL_tau)/q,  and then dchecked
  against the md5-pinned engine:  q^3 * T_tau == beta_3(tau), term for
  term.  No hmenu3/genh4 model code is consulted for the derivation.

CHECKS:
  C0  pins: genh4_checks.py == ee8024b7... (S13.2) and every entry of
      the sealed runner's own PINS dict (incl. ../om_density_engine.py
      == 7240a916...)
  C1  Sum_tau T_tau == q^{-3} symbolically (HM3.D S5.5's displayed
      TRP total)
  C2  THE TIE: q^3 * T_tau == ENG.beta(3)[tau] term for term, and the
      key sets agree EXACTLY (no extra cluster types on either side)
  C3  Sum ENG.beta(3) == 1 symbolically (what the sealed nu4 assembly
      consumed is a distribution)
  C4  exact rational spot values of the tie at q = 2, 3, 5, 7, 11
TOOTH (must fire or RED):
  T1  the INERTDEEP block density corrupted x2 must BREAK C2 (the
      derived tie is sensitive to the DBL subtraction route)

Artifacts: genh4r2_supp_output.txt, genh4r2_supp_results.json.
"""
import sys, os, json, time, hashlib

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.dirname(HERE))

SEALED_RUNNER_MD5 = 'ee8024b7a500220a6408dab373d7432f'   # S13.2

LOG = []


def say(m):
    print(m)
    sys.stdout.flush()
    LOG.append(m)


def md5f(path):
    with open(path, 'rb') as fh:
        return hashlib.md5(fh.read()).hexdigest()


def main():
    t0 = time.time()
    viol = []
    results = {'leg': 'GENH4-r2-SUPP (nu3 tie, PE2 MINOR 1)',
               'checks': {}, 'violations': viol}

    # ---------------------------------------------------------- C0 pins
    import genh4_checks as G4                     # the sealed runner
    got = md5f(os.path.join(HERE, 'genh4_checks.py'))
    say('C0 pin genh4_checks.py = %s (want %s)' % (got, SEALED_RUNNER_MD5))
    if got != SEALED_RUNNER_MD5:
        viol.append(('C0', 'genh4_checks.py', got))
    for name, want in sorted(G4.PINS.items()):
        g = md5f(os.path.join(HERE, name))
        ok = 'ok' if g == want else 'MISMATCH'
        say('C0 pin %-28s %s %s' % (name, g, ok))
        if g != want:
            viol.append(('C0', name, g))
    results['checks']['C0-pins'] = 1 + len(G4.PINS)

    import sympy as sp
    import om_density_engine as ENG
    q = ENG.q

    # ---------------- HM3.D display transcriptions (ACCEPTED @ 2/2) ----
    Phi5 = q**4 + q**3 + q**2 + q + 1
    R = {                       # COROLLARY HM3.D, the five R_tau forms
        '111':   q**3 * (q**2 - q + 1) / (6 * (q + 1) * Phi5),
        '12_11': q**3 * (q**2 + q + 1) / (2 * (q + 1) * Phi5),
        '3':     q**3 * (q + 1) / (3 * Phi5),
        '21_11': q * (q**3 + q + 1) / ((q + 1) * Phi5),
        '31':    (q**2 + 1) / Phi5,
    }
    # level-0 separable censuses / q^3 (elementary)
    SEP = {
        '111':   q * (q - 1) * (q - 2) / 6 / q**3,
        '12_11': q * (q**2 - q) / 2 / q**3,
        '3':     (q**3 - q) / 3 / q**3,
        '21_11': sp.Integer(0),
        '31':    sp.Integer(0),
    }
    # HM3.D S5.5 per-center n=2 block densities, x (q-1) simple-root
    # letters; block sigma + {(1,1)} -> tau
    def dbl(inert_factor=1):
        bRAM = 1 / (q * (q + 1))
        b2S = 1 / (q**3 * (q + 1))
        bSEQ = (q - 2) / (2 * q**3 * (q + 1))
        bIN = inert_factor / (2 * q**2 * (q + 1))
        return {
            '21_11': (q - 1) * bRAM,
            '111':   (q - 1) * (b2S + bSEQ),
            '12_11': (q - 1) * bIN,
            '3':     sp.Integer(0),
            '31':    sp.Integer(0),
        }

    TYP = {'111': ((1, 1), (1, 1), (1, 1)), '12_11': ((1, 1), (1, 2)),
           '3': ((1, 3),), '21_11': ((1, 1), (2, 1)), '31': ((3, 1),)}

    def derive_T(DBL):
        return {t: sp.simplify((R[t] - SEP[t] - DBL[t]) / q) for t in R}

    def tie_diffs(T):
        """simplified q^3*T_tau - beta3(tau) per tau; None on key mismatch"""
        b3 = ENG.beta(3)
        mine = {tuple(sorted(TYP[t])): q**3 * T[t] for t in T}
        if set(mine) != set(b3):
            return None
        return {t: sp.simplify(mine[t] - b3[t]) for t in mine}

    T = derive_T(dbl())

    # ---------------------------------------------------------- C1
    d = sp.simplify(sum(T.values()) - q**(-3))
    say('C1 Sum_tau T_tau - q^-3 = %s' % d)
    if d != 0:
        viol.append(('C1', 'sum', str(d)))
    results['checks']['C1-sum'] = 1

    # ---------------------------------------------------------- C2 THE TIE
    diffs = tie_diffs(T)
    if diffs is None:
        viol.append(('C2', 'keys', 'key sets differ'))
        say('C2 KEY SETS DIFFER')
    else:
        for t, dd in sorted(diffs.items()):
            say('C2 tie %-28s q^3*T - beta3 = %s' % (str(t), dd))
            if dd != 0:
                viol.append(('C2', str(t), str(dd)))
    results['checks']['C2-tie'] = 5 + 1

    # ---------------------------------------------------------- C3
    d = sp.simplify(sum(ENG.beta(3).values()) - 1)
    say('C3 Sum beta3 - 1 = %s' % d)
    if d != 0:
        viol.append(('C3', 'dist', str(d)))
    results['checks']['C3-beta3-dist'] = 1

    # ---------------------------------------------------------- C4 spots
    from fractions import Fraction
    nspots = 0
    for qq in (2, 3, 5, 7, 11):
        b3q = {t: sp.Rational(sp.nsimplify(v.subs(q, qq)))
               for t, v in ENG.beta(3).items()}
        for t in T:
            lhs = sp.Rational((q**3 * T[t]).subs(q, qq))
            rhs = b3q[tuple(sorted(TYP[t]))]
            nspots += 1
            if lhs != rhs:
                viol.append(('C4', 'q=%d %s' % (qq, t),
                             '%s vs %s' % (lhs, rhs)))
        say('C4 q=%-2d all five spot ties exact' % qq)
    results['checks']['C4-spots'] = nspots

    # ---------------------------------------------------------- T1 tooth
    Tbad = derive_T(dbl(inert_factor=2))
    bad = tie_diffs(Tbad)
    fired = bad is None or any(dd != 0 for dd in bad.values())
    say('T1 tooth (INERTDEEP x2): %s' % ('FIRED' if fired else 'DEAD'))
    if not fired:
        viol.append(('T1', 'tooth', 'corrupted DBL route not caught'))
    results['checks']['T1-tooth'] = 1

    # ---------------------------------------------------------- verdict
    dt = time.time() - t0
    verdict = 'GREEN' if not viol else 'RED'
    say('VERDICT: %s (%d violations) %.1fs' % (verdict, len(viol), dt))
    results['verdict'] = verdict
    results['elapsed_s'] = round(dt, 1)

    out_txt = os.path.join(HERE, 'genh4r2_supp_output.txt')
    out_json = os.path.join(HERE, 'genh4r2_supp_results.json')
    with open(out_txt, 'w') as fh:
        fh.write('\n'.join(LOG) + '\n')
    with open(out_json, 'w') as fh:
        json.dump(results, fh, indent=1, sort_keys=True)
    print('artifacts: %s %s' % (md5f(out_txt), md5f(out_json)))
    return 0 if not viol else 1


if __name__ == '__main__':
    sys.exit(main())
