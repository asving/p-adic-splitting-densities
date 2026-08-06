#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
grt_jc_r2_checks.py -- THE r2 SUPPLEMENTARY BATTERY for lean/notes/openmath/
GRTJC_PROOF_2026-08-08.md, repair round r2 (applied against the hostile pass
GRTJC_passPE2_report.md, commit 4a76d52: 0 CRITICAL + 9 gaps).

OWN TWO-COMMIT MINI-SEAL (the r1 protocol): commit 1 = this runner ALONE,
SEALED and UNRUN (this docstring is the authoritative preregistration; the
note's SS9.4 table was committed one commit earlier with the verdict PENDING);
commit 2 = the verdict written FROM the committed artifacts
(grt_jc_r2_output.txt, grt_jc_r2_results.json).

WHAT THIS IS NOT.  It is NOT a re-run of the r0 battery (grt_jc_checks.py),
the r1 battery (grt_jc_r1_checks.py) or the instrument (grt_jc_probe.py).
All three runners and ALL their artifacts are BYTE-FROZEN at r2 and are not
touched.  This runner IMPORTS the instrument's roster/stage builder
(grt_jc_probe.ROSTER / Stage -- the same 29 rows) and the r1 helpers
(Rpoly / pmul / pshift / delta_of / surj_build / samples -- imported from the
frozen module, NOT re-typed, so the (DMULT) predicate here is byte-identical
to the one PE2 audited as a genuinely independent test), and tests ONLY what
PE2's GAP 2 found missing.

================================ WHY (GAP 2) ==================================
PE2's code audit of R1-DMULT: the r1 per-row sample list has SEVEN elements,
SIX of which have MONOMIAL (single-slot) digit polynomials, and the one
non-monomial x non-monomial pair (Phi_{m+1}, Phi_{m+1}) is `continue`d without
disclosure.  So in every one of R1-DMULT's 2,784 scored samples at least one
factor is a shift-and-scale and the identity's genuinely BILINEAR content
(the cross-term convolution Sum_{i+j=k} a_i b_j of two multi-slot digit
polynomials) was never exercised.  This battery exercises it:

  * both factors are built by the note's own LEMMA JC-BSURJ construction
    (surj_build) with DENSE multi-slot targets -- degree-2 all-coefficients-
    nonzero ("ones2"), a mixed variant ("mix2"), and a degree-3 dense attempt
    ("ones3", censused) -- so every scored pair is multi-slot x multi-slot
    with occupied interior slots on both sides;
  * the r1-skipped pair (Phi_{m+1}, Phi_{m+1}) is scored on every row;
  * the r1 sample-composition facts are SCORED, not asserted;
  * a new tooth U2 (the cross-term drop) is provably SILENT on every
    r1-TESTED pair and must fire on the new dense pairs -- machine proof that
    the r1 leg had zero resolution against exactly this mutation class.

============================= PREREGISTERED LEGS ==============================
(violation counts; a family whose observed count differs from its sealed
prediction is RED.  Deterministic, exact arithmetic, no randomness.)

EXT-GATE   engine_ext install() + check_pins() + agreement_gate() re-run
           (standing in-unit rule).                          PREDICTED 0.

R2-BIL     (DMULT-s) -- R_{lam+mu}(fg) == y^{delta}, R_lam(f), R_mu(g) EXACT
           dict equality, together with w(fg) == w(f)+w(g) -- on every ordered
           pair (f,g) from the row's DENSE set D = {ones2, mix2 [, ones3]}:
           degree-2 dense targets realize on every row (R1-SURJ census:
           minimal k <= 34; cap here 80) and are SCORED; the degree-3 dense
           target is attempted with the same cap and its element joins D
           where realized (per-row census printed; absence is a disclosed
           resolution limit, not a skip of a scored prediction).  Each dense
           element is itself verified (w == n+kE, R == target on the nose)
           before any pair is scored.                        PREDICTED 0.

R2-PHI     the pair r1 silently skipped, scored on every row: f = g =
           Phi_{m+1}.  Predicates: R_{wPhi}(Phi_{m+1}) == psi_m coefficient-
           wise (JC-PSIKER(i)); w(Phi_{m+1}^2) == 2*wPhi_NR; and the (DMULT)
           identity on the pair, i.e. R_{2wPhi}(Phi^2) == y^{delta(wPhi,wPhi)}
           * psi_m(y)^2 exactly.  Census: r1 skipped exactly this ONE pair
           per row; the rows where the skipped pair has genuine bilinear
           content (psi_m with an occupied interior slot) are named.
                                                             PREDICTED 0.

R2-MONO    SS9.3 [r2, G-2]'s disclosure as SCORED fact:
           (a) exactly ONE element of the r1 sample list per row has a
               multi-slot digit polynomial (Phi_{m+1}; the other six are
               single-slot: JC-ANCHMON(c), JC-SCAL(b), JC-SPAN, pi-scaling);
           (b) every r1-TESTED DMULT pair (the (PhiTop, PhiTop) skip
               excluded, exactly as the frozen r1 loop excludes it) has
               >= 1 single-slot factor;
           (c) the U2 mutation, replayed on those r1-tested pairs, fires
               ZERO times -- the r1 leg could never have caught it.
                                                             PREDICTED 0.

TEETH (both must fire; a silent tooth is RED):
  U1  the y^{delta+1} shift mutation (r1's T3, re-armed on the new dense
      pairs, proving the r2 predicate is live).     PREDICTED >= 1 per row.
  U2  the CROSS-TERM DROP: the mutated product keeps only terms a_i b_j with
      i in {min supp, max supp} of R(f) OR j in {min supp, max supp} of R(g)
      -- i.e. it deletes exactly the interior x interior convolution terms.
      Provably equal to the true product whenever either factor has <= 2
      occupied slots or no occupied interior slot (all its indices are then
      extremal), hence silent on every r1-TESTED pair (scored as R2-MONO(c));
      provably different on a dense deg-2 x dense deg-2 pair over a field
      (the dropped a_1 b_1 != 0 moves the slot-(2+delta) coefficient).
                                                    PREDICTED >= 1 per row.
Per-row tooth obligations are scored as their own family TOOTH-ROW.
Exit code = (violations + silent teeth).

FENCE HYGIENE (note SS3.5 [r1, G8]).  This runner calls Tower.constants ONLY
inside delta_of (imported from the frozen r1 module: the integer delta from
split data; the closed-form c_T field is never read) and Tower.read_coeffs /
Tower.read for the digit data the statements are ABOUT.  No family compares
against the [ILN] closed form.

PRE-SEAL SMOKE DISCLOSURE (honest, part of this seal).  One read-only /tmp
design probe ran BEFORE this seal on rows C2A/C2I/C4H and found: dense
degree-2 targets realize at k = 5/5/19 and degree-3 at k = 8/8/27 (cap 80);
(DMULT) held exactly on all probe dense pairs; U2 fired on all 4 dense pairs
per probe row and was SILENT on all r1-TESTED pairs there -- firing exactly
once on C2I's (PhiTop, PhiTop) pair, which is the pair r1 SKIPPED (psi_m is
dense of degree 2 there): on the g_m = 2 rows the single r1 pair with true
bilinear content was the continue'd one.  No scored predicate was weakened by
the probe.

Outputs: grt_jc_r2_output.txt (stdout, tee'd by the caller) and
grt_jc_r2_results.json.
"""
import sys, os, json, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import grt_jc_probe as PR
import engine_ext as EE
from grt_jc_r1_checks import (Rpoly, pmul, pshift, delta_of, surj_build,
                              samples)

VIOL = []
COUNTS = {}
TEETH = {}
ROWTEETH = {}
RESULTS = {'rows': {}, 'families': {}}


def note(fam, n=1):
    COUNTS[fam] = COUNTS.get(fam, 0) + n


def viol(fam, tag, detail):
    VIOL.append((fam, tag, str(detail)))


def fire(t, n=1):
    TEETH[t] = TEETH.get(t, 0) + n
    ROWTEETH[t] = ROWTEETH.get(t, 0) + n


def mut_pmul(Km, a, b):
    """U2's CROSS-TERM DROP: keep terms with i extremal in supp(a) OR j
    extremal in supp(b); equals pmul iff no interior x interior term with
    nonzero product is dropped."""
    ia, ib = sorted(a), sorted(b)
    exA = {ia[0], ia[-1]}
    exB = {ib[0], ib[-1]}
    out = {}
    for i, x in a.items():
        for j, y in b.items():
            if i not in exA and j not in exB:
                continue
            k = i + j
            out[k] = Km.add(out.get(k, Km.zero()), Km.mul(x, y))
    return {k: v for k, v in out.items() if not Km.is_zero(v)}


def build_dense(S):
    """the row's dense multi-slot set D, via the frozen JC-BSURJ builder."""
    T = S.T
    Km = T.K[S.NR - 1]
    elems = [c for c in Km.elems() if not Km.is_zero(c)]
    alt = elems[1] if len(elems) > 1 else elems[0]
    targets = [('ones2', 2, {j: Km.one() for j in range(3)}),
               ('mix2', 2, {0: Km.one(), 1: alt, 2: Km.one()}),
               ('ones3', 3, {j: Km.one() for j in range(4)})]
    D, ks = [], {}
    for (name, d, tg) in targets:
        got = surj_build(S, tg, d)
        if got is None:
            ks[name] = None
            if d == 2:            # degree-2 IS a scored prediction
                note('R2-BIL')
                viol('R2-BIL', S.spec['id'],
                     'dense degree-2 target %s not realizable within cap'
                     % name)
            continue
        k, lam, f, recs = got
        ks[name] = k
        tgt = {j: c for j, c in tg.items() if not Km.is_zero(c)}
        note('R2-BIL')
        if T.wlev(S.NR, f) != lam:
            viol('R2-BIL', S.spec['id'], 'w(dense %s) != n+kE' % name)
            continue
        note('R2-BIL')
        if Rpoly(S, lam, f) != tgt:
            viol('R2-BIL', S.spec['id'], 'R(dense %s) != target' % name)
            continue
        D.append((name, f, lam))
    return D, ks


def run_row(S):
    T, P, K, NR, E = S.T, S.P, S.K, S.NR, S.E
    Km = T.K[NR - 1]
    rid = S.spec['id']
    gm, em = T.g[NR - 1], T.e[NR - 1]
    rec = {'id': rid, 'm': S.m, 'E': E, 'nK': S.nK, 'g_m': gm, 'e_m': em}

    # ---------------- R2-BIL : dense x dense (DMULT) ----------------------
    D, ks = build_dense(S)
    rec['dense_k'] = ks
    pairs = 0
    for (n1, f, lf) in D:
        for (n2, g, lg) in D:
            fg = P.mul(f, g)
            note('R2-BIL')
            if T.wlev(NR, fg) != lf + lg:
                viol('R2-BIL', rid, 'w(fg) != w(f)+w(g) on (%s,%s)'
                     % (n1, n2))
                continue
            d = delta_of(S, lf, lg)
            Rf, Rg = Rpoly(S, lf, f), Rpoly(S, lg, g)
            lhs = Rpoly(S, lf + lg, fg)
            rhs = pshift(pmul(Km, Rf, Rg), d)
            note('R2-BIL')
            if lhs != rhs:
                viol('R2-BIL', rid, '(DMULT) fails on dense (%s,%s): %s vs %s'
                     % (n1, n2, sorted(lhs), sorted(rhs)))
            pairs += 1
            # U1 tooth: the y^{delta+1} shift
            note('U1')
            if lhs != pshift(rhs, 1):
                fire('U1')
            # U2 tooth: the cross-term drop
            note('U2')
            if lhs != pshift(mut_pmul(Km, Rf, Rg), d):
                fire('U2')
    rec['bil_pairs'] = pairs

    # ---------------- R2-PHI : the r1-skipped pair ------------------------
    psi = T.psi[NR - 1]
    wphi = S.wPhiTop
    Rphi = Rpoly(S, wphi, S.PhiTop)
    want_psi = {i: c for i, c in enumerate(psi) if not Km.is_zero(c)}
    note('R2-PHI')
    if Rphi != want_psi:
        viol('R2-PHI', rid, 'R(Phi_top) != psi_m coefficientwise')
    ff = P.mul(S.PhiTop, S.PhiTop)
    note('R2-PHI')
    if T.wlev(NR, ff) != 2 * wphi:
        viol('R2-PHI', rid, 'w(Phi_top^2) != 2 wPhi_NR')
    d = delta_of(S, wphi, wphi)
    note('R2-PHI')
    lhs = Rpoly(S, 2 * wphi, ff)
    rhs = pshift(pmul(Km, Rphi, Rphi), d)
    if lhs != rhs:
        viol('R2-PHI', rid,
             'R(Phi^2) != y^%d psi_m^2: %s vs %s'
             % (d, sorted(lhs), sorted(rhs)))
    interior = [i for i in Rphi if sorted(Rphi)[0] < i < sorted(Rphi)[-1]]
    rec['phi'] = {'delta': d, 'slots': sorted(Rphi),
                  'bilinear_content': bool(interior)}

    # ---------------- R2-MONO : the r1 sample-composition facts -----------
    smp = samples(S)
    multi = [(f, lam) for (f, lam) in smp if len(Rpoly(S, lam, f)) >= 2]
    note('R2-MONO')
    if len(multi) != 1:
        viol('R2-MONO', rid, '%d multi-slot r1 sample elements (expected 1)'
             % len(multi))
    tested_bad = 0
    u2_fired_r1 = 0
    skipped = 0
    for (f, lf) in smp:
        for (g, lg) in smp:
            if f == S.PhiTop and g == S.PhiTop:
                skipped += 1        # exactly the frozen r1 loop's skip
                continue
            Rf, Rg = Rpoly(S, lf, f), Rpoly(S, lg, g)
            note('R2-MONO')
            if len(Rf) >= 2 and len(Rg) >= 2:
                tested_bad += 1
                viol('R2-MONO', rid,
                     'an r1-TESTED pair has two multi-slot factors')
            note('R2-MONO')
            if pmul(Km, Rf, Rg) != mut_pmul(Km, Rf, Rg):
                u2_fired_r1 += 1
                viol('R2-MONO', rid, 'U2 fired on an r1-TESTED pair')
    rec['mono'] = {'multi_slot_samples': len(multi),
                   'tested_pairs_both_multi': tested_bad,
                   'u2_fires_on_r1_tested': u2_fired_r1,
                   'r1_skipped_pairs': skipped}

    # ---------------- per-row tooth obligations ---------------------------
    for t in ('U1', 'U2'):
        note('TOOTH-ROW')
        if ROWTEETH.get(t, 0) == 0:
            viol('TOOTH-ROW', rid, 'tooth %s SILENT on this row' % t)
    rec['teeth'] = dict(ROWTEETH)
    return rec


def main(smoke=False):
    t0 = time.time()
    print('grt_jc_r2_checks.py -- GRTJC r2 SUPPLEMENTARY battery '
          '(the bilinearity leg)%s' % (' [SMOKE]' if smoke else ''))
    v0 = len(EE.VIOL)
    EE.install()
    EE.check_pins()
    gate_new = EE.agreement_gate(full=False)
    note('EXT-GATE')
    if gate_new or len(EE.VIOL) > v0:
        viol('EXT-GATE', 'engine_ext', '%d new violations'
             % (len(EE.VIOL) - v0))
    print('  [%6.1fs] EXT-GATE done (new: %d)'
          % (time.time() - t0, len(EE.VIOL) - v0))

    roster = PR.ROSTER if not smoke else \
        [s for s in PR.ROSTER if s['id'] in ('C2A', 'C2I', 'C4H')]
    for spec in roster:
        tA = time.time()
        try:
            S = PR.Stage(spec)
        except Exception as ex:
            note('BUILD')
            viol('BUILD', spec['id'], 'stage build failed: %r' % ex)
            continue
        ROWTEETH.clear()
        rec = run_row(S)
        RESULTS['rows'][spec['id']] = rec
        print('  [%6.1fs] %-6s m=%d E=%-3d |K|=%-3d g_m=%d e_m=%d  '
              'dense k=%s  BIL pairs %d  phi delta=%d bilinear=%s  U1 %d U2 %d'
              '  (%.1fs)'
              % (time.time() - t0, rec['id'], rec['m'], rec['E'], rec['nK'],
                 rec['g_m'], rec['e_m'],
                 [rec['dense_k'].get(n) for n in ('ones2', 'mix2', 'ones3')],
                 rec['bil_pairs'], rec['phi']['delta'],
                 rec['phi']['bilinear_content'],
                 rec['teeth'].get('U1', 0), rec['teeth'].get('U2', 0),
                 time.time() - tA))

    fam = {}
    for (f, tag, det) in VIOL:
        fam[f] = fam.get(f, 0) + 1
    RESULTS['families'] = {'counts': COUNTS, 'violations': fam}
    RESULTS['teeth'] = TEETH
    RESULTS['violations'] = [list(v) for v in VIOL]

    print()
    print('=' * 78)
    print('FAMILY TABLE (samples / violations; sealed predictions in the '
          'docstring)')
    for f in ['EXT-GATE', 'R2-BIL', 'R2-PHI', 'R2-MONO', 'TOOTH-ROW',
              'BUILD']:
        if f in COUNTS or f in fam:
            print('  %-10s samples %6d   violations %4d'
                  % (f, COUNTS.get(f, 0), fam.get(f, 0)))
    print()
    print('TEETH (each MUST fire)')
    for t in ['U1', 'U2']:
        print('  %-3s fired %6d times (opportunities %d)%s'
              % (t, TEETH.get(t, 0), COUNTS.get(t, 0),
                 '' if TEETH.get(t, 0) > 0
                 else '   *** SILENT TOOTH = RED ***'))

    tot = {'bil': 0, 'd3': 0, 'skip': 0, 'bilphi': 0, 'u2r1': 0}
    for rid, rec in RESULTS['rows'].items():
        tot['bil'] += rec['bil_pairs']
        tot['d3'] += 1 if rec['dense_k'].get('ones3') is not None else 0
        tot['skip'] += rec['mono']['r1_skipped_pairs']
        tot['bilphi'] += 1 if rec['phi']['bilinear_content'] else 0
        tot['u2r1'] += rec['mono']['u2_fires_on_r1_tested']
    RESULTS['totals'] = tot
    print()
    print('R2-BIL: %d dense multi-slot x multi-slot ordered pairs scored; '
          'degree-3 dense realized on %d/%d rows (censused)'
          % (tot['bil'], tot['d3'], len(RESULTS['rows'])))
    print('R2-PHI census: r1 skipped exactly %d pair(s) per row (total %d); '
          'the skipped pair has genuine bilinear content (interior psi_m '
          'slot) on %d row(s): %s'
          % (1, tot['skip'], tot['bilphi'],
             sorted(r for r, rec in RESULTS['rows'].items()
                    if rec['phi']['bilinear_content'])))
    print('R2-MONO: U2 fired %d times on the r1-TESTED pairs across the '
          'roster (predicted 0 -- the r1 leg had zero resolution against '
          'the cross-term class)' % tot['u2r1'])
    if VIOL:
        print()
        print('VIOLATIONS (first 60):')
        for (f, tag, det) in VIOL[:60]:
            print('  [%s] %s: %s' % (f, tag, det))
    silent = [t for t in ['U1', 'U2'] if TEETH.get(t, 0) == 0]
    print()
    print('elapsed %.1fs;  total violations %d;  silent teeth %s'
          % (time.time() - t0, len(VIOL), silent if silent else 'NONE'))
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                       'grt_jc_r2_results.json')
    with open(out, 'w') as fh:
        json.dump(RESULTS, fh, indent=1, sort_keys=True, default=str)
    print('wrote %s' % out)
    return len(VIOL) + len(silent)


if __name__ == '__main__':
    sys.exit(0 if main(smoke=('--smoke' in sys.argv)) == 0 else 1)
