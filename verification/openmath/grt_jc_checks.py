#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
grt_jc_checks.py -- THE COMPOSER'S BATTERY for lean/notes/openmath/
GRTJC_PROOF_2026-08-08.md (J-C, W-6..W-9).  Two-commit seal: this runner +
the note's sealed predictions (note SS9.1) are committed BEFORE the battery
runs; the verdict is written FROM the artifacts.

WHAT THIS IS NOT.  It is not a re-run of the J-C instrument
(grt_jc_probe.py, seal 7212e56 / verdict fc89b03).  It imports that runner's
tower/stage construction (roster, Stage, the certifiers) and then tests THE
COMPOSED NOTE'S OWN CLAUSES -- the lemmas the note proves, several of which
the instrument never measured:

  JC1  LEMMA JC-PER  (SS2.3): phi_{gamma+kE} == pi^k * phi_gamma BYTE-for-byte
       for k = 1,2,3; the split's s-tuple is E-periodic and u_1 -> u_1 + k;
       and w(pi) == E (LEMMA JC-DOM's degree computation).
  JC2  LEMMA JC-FIB (SS2.4): gamma -> (s_1..s_NR) is injective on E
       consecutive gammas (hence a bijection Z/E -> prod Z/e_j), every
       s_{j+1} in [0,e_j), and E-periodic.
  JC3  THEOREM JC-SPAN (SS2.7) -- THE NEW SHARP PREDICTION: for every
       in-window pair, the ON-LINE SLOT SET of phi_gamma*phi_gamma' at its own
       weight is EXACTLY {delta}, with delta in {0,1}, and the slot-delta
       coefficient u is a nonzero element of K_m.  [e_m = 1 rows: the note
       proves only slots subset {0,1} with 0 attained -- JC-BOX-4 -- so those
       rows are a CENSUS: the sharp form is measured, not scored.]
  JC4  LEMMA JC-SCAL (SS2.6) + SS4.1's normalization: slot set of Lam_N(c) is
       exactly {i : c_i != 0} subset {0..g_m-1} with slot-i digit == c_i (the
       K_m-coordinates of c), and R_N(X_N) == 1 EXACTLY (single slot 0,
       coefficient 1).
  JC5  LEMMA JC-ANCHMON (SS2.5): sum_{j<m} s_{j+1} deg Phi_j < deg Phi_m; the
       Phi_m-development of an anchor has exactly ONE nonzero digit, at
       abscissa s_NR; its slot set is {0} and a_lambda != 0.
  JC6  COROLLARY JC-PSIKER (SS2.9): w(Phi_{m+1}) == wPhi_NR exactly,
       R(Phi_{m+1}) == psi_m(y) coefficient-for-coefficient, read == 0, and
       (when the line is in the window) Phi_{m+1} + phi_lambda vs phi_lambda
       are two DIFFERENT classes with EQUAL reads.
  JC7  COROLLARY W-9 (SS5): the mod-E 2-cocycle identity
       c(r,s)c(r+s,t) == c(s,t)c(r,s+t) on the uniform reps (E | G0, so the
       classes match), the integer carry identity
       delta(r,s)+delta(r+s,t) == delta(s,t)+delta(r,s+t), and the E-FOLD
       CHAIN c_direct(phi^E) == prod_{k=1}^{E-1} c_val(gamma_1, k gamma_1)
       (the monodromy = the gauge period, computed two ways).
  JC8  LAW JC-CYC (SS6) + FINDING JC-F1: a CYCLIC verdict implies the
       twist-blind/collapse geography (|K| = 2 or g_m = 1 or e_0 = 1); every
       structure constant is a UNIT (so JC-F1's power basis 1,v,..,v^{E-1}
       exists at every stage).  Fresh transcription of the (CYC) adjudication.

TEETH (five planted mutations; EVERY one must fire -- a silent tooth is RED):
  MJ1  "TC-3 is never load-bearing": the claim that a pre-TC-3 (RAW) scalar
       exists on EVERY pair.  Must FAIL (JC-LOAD says it fails exactly at
       delta >= g_m).                            PREDICTED >= 1 failure.
  MJ2  mutated periodicity phi_{gamma+E} == pi^2 phi_gamma.
                                                PREDICTED >= 1 per row.
  MJ3  mutated scalar image "slot set of Lam_N(c) subset {0}" -- must FAIL on
       every g_m >= 2 row (some c has c_1 != 0).  PREDICTED >= 1 per g_m>=2 row.
  MJ4  "the read is injective on a graded piece", operationalized as
       read(wPhi, Phi_{m+1}) != 0.  Must FAIL on every row (the read is 0).
                                                PREDICTED >= 1 per row.
  MJ5  mutated span law "slot set == {delta+1}".  PREDICTED >= 1 per row.

EXT-GATE: engine_ext install() + check_pins() + agreement_gate() re-run
(standing rule, mandatory in-unit).                     PREDICTED 0.

SEALED PREDICTIONS (violation counts; identical to note SS9.1):
  EXT-GATE 0 | JC1 0 | JC2 0 | JC3 0 (scored: rows with e_m >= 2; e_m = 1 rows
  censused, with the measured claim "0 pairs of max slot > 0" reported but NOT
  scored) | JC4 0 | JC5 0 | JC6 0 | JC7 0 | JC8 0 | and all five teeth FIRE.
  Deterministic, exact arithmetic, no randomness.  Roster: the instrument's 29
  rows verbatim (grt_jc_probe.ROSTER).

BUILD-PHASE SMOKE DISCLOSURE (pre-seal, part of this seal): a 3-row smoke
(C2A/C2I/C3A) of this runner was executed during construction; its findings
and any pre-seal corrections are recorded in note SS9.1.  The sealed
predictions are the NOTE's identities, not sanitized to the smoke.

Outputs: grt_jc_checks_output.txt (stdout, tee'd) + grt_jc_checks_results.json.
"""
import sys, os, json, time, itertools

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import iterlawn_pe_reimpl as ITL
from iterlawn_pe_reimpl import fpow
import engine_ext as EE
import grt_jc_probe as PR

VIOL = []
COUNTS = {}
TEETH = {}
RESULTS = {'rows': {}, 'families': {}, 'teeth': {}, 'census': {}}

PAIRCAP_SPAN = 24      # pairs per row for JC3/MJ5 (the probe's own grid)
RAWCAP = 8             # pairs per row for the MJ1 tooth (exhaustive RAW search)
TRIPCAP = 12           # triples per row for JC7's cocycle identity


def note(fam, n=1):
    COUNTS[fam] = COUNTS.get(fam, 0) + n


def viol(fam, tag, detail):
    VIOL.append((fam, tag, str(detail)))


ROWTEETH = {}


def fire(t, n=1):
    TEETH[t] = TEETH.get(t, 0) + n
    ROWTEETH[t] = ROWTEETH.get(t, 0) + n


# ----------------------------------------------------------------- helpers
def slots(S, lam, f):
    """on-line slot set -> dict slot -> digit in K_m, at line lam."""
    return S.T.read_coeffs(S.NR, lam, f)


def kmcoords(S, c):
    """the K_m-coordinate tuple of c in K = K_m[y]/(psi_m)."""
    return list(c)


def run_row(S):
    T, P, K, NR, E, N = S.T, S.P, S.K, S.NR, S.E, S.N
    Km = T.K[NR - 1]
    gm = T.g[NR - 1]
    em = T.e[NR - 1]
    rec = {'id': S.spec['id'], 'm': S.m, 'E': E, 'nK': S.nK, 'g_m': gm,
           'e_m': em, 'G0': S.G0, 'N': N, 'p': S.spec['p'],
           'd0': S.spec['d0'], 'ring': S.spec['ring']}

    # ---------------- JC1 : JC-PER + w(pi) = E ----------------------------
    note('JC1')
    if T.wlev(NR, S.pi1) != E:
        viol('JC1', S.spec['id'], 'w(pi) = %s != E = %d'
             % (T.wlev(NR, S.pi1), E))
    for r in range(E):
        g0 = S.gam_of[r]
        sp0 = T.split(g0)
        for k in (1, 2, 3):
            note('JC1')
            lhs = T.tanch(g0 + k * E, NR - 1)
            rhs = P.mul(P.pow(S.pi1, k), S.ph[r])
            if lhs != rhs:
                viol('JC1', S.spec['id'],
                     'phi_{%d+%dE} != pi^%d phi (byte)' % (g0, k, k))
            spk = T.split(g0 + k * E)
            note('JC1')
            if [spk['s'][j] for j in range(1, NR + 1)] != \
               [sp0['s'][j] for j in range(1, NR + 1)]:
                viol('JC1', S.spec['id'], 's-tuple not E-periodic at %d' % g0)
            note('JC1')
            if spk['u'][1] != sp0['u'][1] + k:
                viol('JC1', S.spec['id'], 'u_1 shift wrong at %d (+%d)' % (g0, k))
        # MJ2 tooth: pi^2 must NOT work
        note('MJ2')
        if T.tanch(g0 + E, NR - 1) != P.mul(P.pow(S.pi1, 2), S.ph[r]):
            fire('MJ2')

    # ---------------- JC2 : JC-FIB ----------------------------------------
    seen = {}
    for r in range(E):
        g0 = S.gam_of[r]
        sp = T.split(g0)
        tup = tuple(sp['s'][j] for j in range(1, NR + 1))
        note('JC2')
        for j in range(NR):
            if not (0 <= tup[j] < T.e[j]):
                viol('JC2', S.spec['id'], 's_%d = %d outside [0,e_%d)'
                     % (j + 1, tup[j], j))
        note('JC2')
        if tup in seen:
            viol('JC2', S.spec['id'], 'tuple collision %s at r=%d and r=%d'
                 % (tup, seen[tup], r))
        seen[tup] = r
    rec['fib_tuples'] = len(seen)

    # ---------------- JC5 : JC-ANCHMON -----------------------------------
    degPhim = P.deg(T.Phi[NR - 1])
    for r in range(E):
        g0 = S.gam_of[r]
        sp = T.split(g0)
        note('JC5')
        low = sum(sp['s'][j + 1] * P.deg(T.Phi[j]) for j in range(NR - 1))
        if not low < degPhim:
            viol('JC5', S.spec['id'],
                 'sum s_j deg Phi_j = %d >= deg Phi_m = %d' % (low, degPhim))
        dv = P.dev(S.ph[r], T.Phi[NR - 1])
        nz = [a for a, A in enumerate(dv) if A]
        note('JC5')
        if nz != [sp['s'][NR]]:
            viol('JC5', S.spec['id'],
                 'anchor dev support %s != {s_NR = %d}' % (nz, sp['s'][NR]))
        sl = slots(S, g0, S.ph[r])
        note('JC5')
        if sorted(sl.keys()) != [0] or Km.is_zero(sl[0]):
            viol('JC5', S.spec['id'], 'anchor slot set %s (a_lambda = %s)'
                 % (sorted(sl.keys()), sl.get(0)))

    # ---------------- JC4 : JC-SCAL + the X_N normalization ---------------
    slX = slots(S, N, S.X)
    note('JC4')
    if sorted(slX.keys()) != [0] or slX[0] != Km.one():
        viol('JC4', S.spec['id'], 'R_N(X_N) = %s (slots %s) != 1'
             % (slX.get(0), sorted(slX.keys())))
    for c in S.elems:
        if K.is_zero(c):
            continue
        co = kmcoords(S, c)
        sl = slots(S, N, S.lam[c])
        want = {i: co[i] for i in range(len(co)) if not Km.is_zero(co[i])}
        note('JC4')
        if sorted(sl.keys()) != sorted(want.keys()):
            viol('JC4', S.spec['id'], 'Lam_N(c) slots %s != support %s'
                 % (sorted(sl.keys()), sorted(want.keys())))
        else:
            note('JC4')
            for i in want:
                if sl[i] != want[i]:
                    viol('JC4', S.spec['id'],
                         'Lam_N slot %d digit != c_%d' % (i, i))
                    break
        note('JC4')
        if any(i >= gm for i in sl):
            viol('JC4', S.spec['id'], 'Lam_N(c) has a slot >= g_m = %d' % gm)
        # MJ3 tooth: "slots subset {0}" must fail somewhere when g_m >= 2
        if gm >= 2:
            note('MJ3')
            if any(i != 0 for i in sl):
                fire('MJ3')

    # ---------------- JC6 : JC-PSIKER ------------------------------------
    lam = T.wPhi[NR]
    wtop = T.wlev(NR, S.PhiTop)
    note('JC6')
    if wtop != lam:
        viol('JC6', S.spec['id'], 'w(Phi_{m+1}) = %s != wPhi_NR = %d'
             % (wtop, lam))
    else:
        sl = slots(S, lam, S.PhiTop)
        want = {k: T.psi[NR - 1][k] for k in range(gm + 1)
                if not Km.is_zero(T.psi[NR - 1][k])}
        note('JC6')
        if sorted(sl.keys()) != sorted(want.keys()) or \
           any(sl[k] != want[k] for k in want):
            viol('JC6', S.spec['id'],
                 'R(Phi_{m+1}) slots %s != psi_m support %s'
                 % (sorted(sl.keys()), sorted(want.keys())))
        rd = T.read(NR, lam, S.PhiTop)
        note('JC6')
        if not K.is_zero(rd):
            viol('JC6', S.spec['id'], 'read(Phi_{m+1}) = %s != 0' % (rd,))
        # MJ4 tooth: the injectivity claim must fail
        note('MJ4')
        if K.is_zero(rd):
            fire('MJ4')
        # the two-element non-injectivity witness
        if T.inW(lam):
            phil = T.tanch(lam, NR - 1)
            if T.wlev(NR, phil) == lam:
                f2 = P.add(S.PhiTop, phil)
                note('JC6')
                if T.wlev(NR, f2) != lam:
                    viol('JC6', S.spec['id'], 'w(Phi+phi) != lambda')
                elif T.read(NR, lam, f2) != T.read(NR, lam, phil):
                    viol('JC6', S.spec['id'], 'reads of Phi+phi and phi differ')
                elif f2 == phil:
                    viol('JC6', S.spec['id'], 'Phi_{m+1} + phi == phi (!)')
                rec['psiker_witness'] = True

    # ---------------- JC3 / MJ5 : THE SLOT-SPAN THEOREM -------------------
    grid = PR.pair_grid(E)[:PAIRCAP_SPAN]
    span = dict(scored=0, sharp=0, bad=0, flat_census=0, flat_maxgt0=0)
    delta_bad = 0
    for (r, s) in grid:
        ga, gb = S.gam_of[r], S.gam_of[s]
        if not (T.inW(ga) and T.inW(gb) and T.inW(ga + gb)):
            continue
        cst = T.constants(ga, gb)
        d = cst['delta']
        note('JC3')
        if d not in (0, 1):
            delta_bad += 1
            viol('JC3', S.spec['id'], 'delta = %d not in {0,1} at (%d,%d)'
                 % (d, r, s))
        f = P.mul(S.ph[r], S.ph[s])
        lamf = T.wlev(NR, f)
        note('JC3')
        if lamf != ga + gb:
            viol('JC3', S.spec['id'], 'w(phi phi) = %s != %d (multiplicativity)'
                 % (lamf, ga + gb))
            continue
        sl = slots(S, lamf, f)
        ks = sorted(sl.keys())
        if em >= 2:
            span['scored'] += 1
            note('JC3')
            if ks != [d]:
                span['bad'] += 1
                viol('JC3', S.spec['id'],
                     'slot set %s != {delta = %d} at (%d,%d)' % (ks, d, r, s))
            else:
                span['sharp'] += 1
                u = sl[d]
                note('JC3')
                if Km.is_zero(u):
                    viol('JC3', S.spec['id'], 'u = 0 at (%d,%d)' % (r, s))
        else:
            span['flat_census'] += 1
            note('JC3-FLAT-census')
            if ks and max(ks) > 0:
                span['flat_maxgt0'] += 1
            if (not ks) or min(ks) != 0:
                viol('JC3', S.spec['id'],
                     'e_m = 1: min slot %s != 0 at (%d,%d)' % (ks, r, s))
        # MJ5 tooth: the mutated span law {delta+1} must fail
        note('MJ5')
        if ks != [d + 1]:
            fire('MJ5')
    rec['span'] = span

    # ---------------- MJ1 tooth : RAW solvability is NOT universal --------
    raw = dict(tested=0, nosol=0, nosol_load=0, sol_nonload=0)
    load_pairs = [(r, s) for (r, s) in grid
                  if T.inW(S.gam_of[r] + S.gam_of[s]) and
                  T.constants(S.gam_of[r], S.gam_of[s])['delta'] >= gm]
    other = [(r, s) for (r, s) in grid if (r, s) not in load_pairs and
             T.inW(S.gam_of[r] + S.gam_of[s])]
    for (r, s) in (load_pairs[:4] + other[:RAWCAP]):
        ga, gb = S.gam_of[r], S.gam_of[s]
        base = S.anchor(ga + gb)
        LHS = P.mul(P.mul(S.ph[r], S.ph[s]), S.X)
        tgt = ga + gb + N
        if T.wlev(NR, LHS) != tgt or T.wlev(NR, base) != ga + gb:
            continue
        sols, _, _ = S.solve(LHS, base, tgt, mode='raw')
        raw['tested'] += 1
        note('MJ1')
        d = T.constants(ga, gb)['delta']
        if not sols:
            raw['nosol'] += 1
            fire('MJ1')
            if d >= gm:
                raw['nosol_load'] += 1
            else:
                viol('MJ1', S.spec['id'],
                     'RAW fails at delta = %d < g_m = %d (JC-LOAD refuted!)'
                     % (d, gm))
        else:
            if d >= gm:
                raw['sol_nonload'] += 1
                viol('MJ1', S.spec['id'],
                     'RAW SUCCEEDS at delta = %d >= g_m = %d (JC-LOAD refuted!)'
                     % (d, gm))
    rec['raw'] = raw

    # ---------------- JC7 : the cocycle identity + the E-fold chain -------
    # c(r,s) := c_val(gamma_r, gamma_s); classes match because E | G0.
    note('JC7')
    if S.G0 % E != 0:
        viol('JC7', S.spec['id'], 'G0 = %d not a multiple of E = %d'
             % (S.G0, E))
    cval = {}
    dlt = {}
    # full E^2 table when E <= 8 (so the (CYC) adjudication sees the whole
    # table); otherwise the probe's designed subset -- at E > 8 the adjudicator
    # returns UNDECIDED anyway, so a truncated table can never produce a
    # spurious CYCLIC verdict.
    cgrid = [(r, s) for r in range(E) for s in range(E)] if E <= 8 \
        else PR.pair_grid(E)
    for (r, s) in cgrid:
        if True:
            ga, gb = S.gam_of[r], S.gam_of[s]
            if not T.inW(ga + gb):
                continue
            base = S.anchor(ga + gb)
            v = S.cval(ga, gb, S.ph[r], S.ph[s], base)
            if v is None or K.is_zero(v):
                continue
            cval[(r, s)] = v
            dlt[(r, s)] = T.constants(ga, gb)['delta']
    trip = 0
    for (r, s) in sorted(cval):
        if trip >= TRIPCAP:
            break
        for t in range(min(E, 3)):
            key = [(r, s), ((r + s) % E, t), (s, t), (r, (s + t) % E)]
            if any(k not in cval for k in key):
                continue
            trip += 1
            note('JC7')
            lhs = K.mul(cval[(r, s)], cval[((r + s) % E, t)])
            rhs = K.mul(cval[(s, t)], cval[(r, (s + t) % E)])
            if lhs != rhs:
                viol('JC7', S.spec['id'],
                     '2-cocycle identity fails at (%d,%d,%d)' % (r, s, t))
            note('JC7')
            if dlt[(r, s)] + dlt[((r + s) % E, t)] != \
               dlt[(s, t)] + dlt[(r, (s + t) % E)]:
                viol('JC7', S.spec['id'],
                     'carry cocycle identity fails at (%d,%d,%d)' % (r, s, t))
            break
    rec['cocycle_triples'] = trip
    # the E-fold chain (monodromy = the gauge period), E <= 8 for cost
    chain = None
    if E <= 8:
        g1 = S.gam_of[1] if E > 1 else None
        if g1 is not None and all(T.inW(k * g1) for k in range(1, E + 1)):
            prod = K.one()
            ok = True
            for k in range(1, E):
                A = S.anchor(g1)
                B = S.anchor(k * g1)
                base = S.anchor((k + 1) * g1)
                v = S.cval(g1, k * g1, A, B, base)
                if v is None or K.is_zero(v):
                    ok = False
                    break
                prod = K.mul(prod, v)
            if ok:
                f = P.pow(S.anchor(g1), E)
                lam2 = T.wlev(NR, f)
                note('JC7')
                if lam2 != E * g1:
                    viol('JC7', S.spec['id'], 'w(phi_1^E) = %s != E*gamma_1'
                         % (lam2,))
                else:
                    num = T.read(NR, lam2, f)
                    den = T.read(NR, lam2, S.anchor(lam2))
                    note('JC7')
                    if K.is_zero(den):
                        viol('JC7', S.spec['id'], 'a_lambda = 0 in the chain')
                    else:
                        direct = K.mul(num, K.inv(den))
                        chain = (PR.krepr(S, direct), PR.krepr(S, prod))
                        if direct != prod:
                            viol('JC7', S.spec['id'],
                                 'E-fold chain: direct %s != prod %s'
                                 % chain)
    rec['chain'] = chain

    # ---------------- JC8 : the cyclic-genre law + JC-F1 ------------------
    vals = {}
    for k, v in cval.items():
        note('JC8')
        if K.is_zero(v):
            viol('JC8', S.spec['id'], 'structure constant 0 at %s' % (k,))
        if v != K.one():
            vals[PR.krepr(S, v)] = v
    verdict, cyclic = adjudicate(S, cval, vals)
    collapse = (S.nK == 2) or (gm == 1) or (T.e[0] == 1)
    note('JC8')
    if cyclic is True and not collapse:
        viol('JC8', S.spec['id'],
             'CYCLIC verdict OFF the collapse geography (|K|=%d, g_m=%d, e_0=%d)'
             % (S.nK, gm, T.e[0]))
    rec['cyc'] = {'verdict': verdict, 'cyclic': cyclic, 'collapse': collapse,
                  'nvals': len(vals), 'values': sorted(vals)}
    rec['teeth'] = dict(ROWTEETH)
    # per-row tooth obligations (sealed): MJ2/MJ4/MJ5 must fire on EVERY row;
    # MJ3 on every g_m >= 2 row; MJ1 at least once on the roster.
    for t in ('MJ2', 'MJ4', 'MJ5'):
        note('TOOTH-ROW')
        if ROWTEETH.get(t, 0) == 0:
            viol('TOOTH-ROW', S.spec['id'], 'tooth %s SILENT on this row' % t)
    if gm >= 2:
        note('TOOTH-ROW')
        if ROWTEETH.get('MJ3', 0) == 0:
            viol('TOOTH-ROW', S.spec['id'], 'tooth MJ3 SILENT on a g_m>=2 row')
    return rec


def adjudicate(S, cval, vals):
    """(CYC): image(c) subset {1, zeta'} AND an integer relabeling sigma with
    sigma_r + sigma_s = sigma_{r+s} + E*carry.  Fresh transcription."""
    K, E = S.K, S.E
    if not cval:
        return 'UNDECIDED (empty table)', None
    if not vals:
        return 'CYCLIC (c == 1 identically)', True
    if len(vals) > 1:
        return ('NOT-CYCLIC (%d distinct non-1 values: %s)'
                % (len(vals), ', '.join(sorted(vals)))), False
    zname, zeta = next(iter(vals.items()))
    kap = {k: (1 if cval[k] == zeta else 0) for k in cval}
    if E > 8:
        return ('UNDECIDED (E = %d > 8: relabeling search skipped; single '
                'value %s)' % (E, zname)), None
    for perm in itertools.permutations(range(1, E)):
        sig = (0,) + perm
        if all(sig[r] + sig[s] == sig[(r + s) % E] + E * kap[(r, s)]
               for (r, s) in cval):
            return ('CYCLIC zeta = %s, sigma = %s' % (zname, sig)), True
    return ('NOT-CYCLIC (single value %s, carry pattern not realizable)'
            % zname), False


def main(smoke=False):
    t0 = time.time()
    print('grt_jc_checks.py -- GRTJC COMPOSER battery (W-6..W-9)%s'
          % (' [SMOKE]' if smoke else ''))
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
        [s for s in PR.ROSTER if s['id'] in ('C2A', 'C2I', 'C3A')]
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
        print('  [%6.1fs] %-6s m=%d E=%-3d |K|=%-3d g_m=%d e_m=%d  span %d/%d'
              '  raw nosol %d/%d  trip %d  cyc=%s  (%.1fs)'
              % (time.time() - t0, rec['id'], rec['m'], rec['E'], rec['nK'],
                 rec['g_m'], rec['e_m'], rec['span']['sharp'],
                 rec['span']['scored'], rec['raw']['nosol'],
                 rec['raw']['tested'], rec['cocycle_triples'],
                 'Y' if rec['cyc']['cyclic'] else
                 ('?' if rec['cyc']['cyclic'] is None else 'N'),
                 time.time() - tA))

    fam = {}
    for (f, tag, det) in VIOL:
        fam[f] = fam.get(f, 0) + 1
    RESULTS['families'] = {'counts': COUNTS, 'violations': fam}
    RESULTS['teeth'] = TEETH
    RESULTS['violations'] = [list(v) for v in VIOL]

    print()
    print('=' * 78)
    print('FAMILY TABLE (samples / violations; sealed predictions in the docstring)')
    for f in ['EXT-GATE', 'JC1', 'JC2', 'JC3', 'JC3-FLAT-census', 'JC4', 'JC5',
              'JC6', 'JC7', 'JC8', 'BUILD']:
        if f in COUNTS or f in fam:
            print('  %-16s samples %6d   violations %4d'
                  % (f, COUNTS.get(f, 0), fam.get(f, 0)))
    print()
    print('TEETH (each MUST fire)')
    for t in ['MJ1', 'MJ2', 'MJ3', 'MJ4', 'MJ5']:
        print('  %-4s fired %5d times (opportunities %d)%s'
              % (t, TEETH.get(t, 0), COUNTS.get(t, 0),
                 '' if TEETH.get(t, 0) > 0 else '   *** SILENT TOOTH = RED ***'))
    tot = dict(sharp=0, scored=0, bad=0, flat=0, flat_max=0, nosol=0,
               nosol_load=0, tested=0, trip=0)
    cyc = {'Y': 0, 'N': 0, '?': 0}
    for rec in RESULTS['rows'].values():
        for k in ('sharp', 'scored', 'bad'):
            tot[k] += rec['span'][k]
        tot['flat'] += rec['span']['flat_census']
        tot['flat_max'] += rec['span']['flat_maxgt0']
        for k in ('nosol', 'nosol_load', 'tested'):
            tot[k] += rec['raw'][k]
        tot['trip'] += rec['cocycle_triples']
        c = rec['cyc']['cyclic']
        cyc['Y' if c is True else ('N' if c is False else '?')] += 1
    RESULTS['totals'] = tot
    RESULTS['cyc_split'] = cyc
    print()
    print('JC3 SLOT-SPAN (the note\'s new sharp prediction): %d/%d pairs with '
          'slot set == {delta} on e_m >= 2 rows; %d violations'
          % (tot['sharp'], tot['scored'], tot['bad']))
    print('JC3 e_m = 1 CENSUS (JC-BOX-4, measured not scored): %d pairs, '
          '%d with a slot > 0' % (tot['flat'], tot['flat_max']))
    print('MJ1 RAW census: %d/%d tested pairs have NO pre-TC-3 scalar, of which '
          '%d are the delta >= g_m load set' % (tot['nosol'], tot['tested'],
                                                tot['nosol_load']))
    print('JC7 cocycle triples checked: %d' % tot['trip'])
    print('JC8 CYCLIC split: CYCLIC %d / NOT-CYCLIC %d / UNDECIDED %d '
          '(law: CYCLIC => collapse geography)'
          % (cyc['Y'], cyc['N'], cyc['?']))
    print()
    print('CYCLIC ADJUDICATION + COLLAPSE GEOGRAPHY (per row)')
    for rid, rec in RESULTS['rows'].items():
        print('  %-6s collapse=%-5s nvals=%d  %s'
              % (rid, rec['cyc']['collapse'], rec['cyc']['nvals'],
                 rec['cyc']['verdict']))
    print()
    print('E-FOLD CHAIN (monodromy vs orbit product, E <= 8)')
    for rid, rec in RESULTS['rows'].items():
        if rec.get('chain'):
            print('  %-6s direct %-12s prod %-12s'
                  % (rid, rec['chain'][0], rec['chain'][1]))
    if VIOL:
        print()
        print('VIOLATIONS (first 60):')
        for (f, tag, det) in VIOL[:60]:
            print('  [%s] %s: %s' % (f, tag, det))
    silent = [t for t in ['MJ1', 'MJ2', 'MJ3', 'MJ4', 'MJ5']
              if TEETH.get(t, 0) == 0]
    print()
    print('elapsed %.1fs;  total violations %d;  silent teeth %s'
          % (time.time() - t0, len(VIOL), silent if silent else 'NONE'))
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                       'grt_jc_checks_results.json')
    with open(out, 'w') as fh:
        json.dump(RESULTS, fh, indent=1, sort_keys=True, default=str)
    print('wrote %s' % out)
    return len(VIOL) + len(silent)


if __name__ == '__main__':
    sys.exit(0 if main(smoke=('--smoke' in sys.argv)) == 0 else 1)
