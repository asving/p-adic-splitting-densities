#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
grt_jc_r1_checks.py -- THE r1 SUPPLEMENTARY BATTERY for lean/notes/openmath/
GRTJC_PROOF_2026-08-08.md, repair round r1 (applied against the hostile pass
GRTJC_passPE1_report.md, commit 1a27be3: 2 CRITICAL + 8 gaps).

OWN TWO-COMMIT MINI-SEAL: commit 1 = this runner + the note's SS9.3
preregistration table, battery NOT yet run; commit 2 = the verdict written FROM
the committed artifacts (grt_jc_r1_output.txt, grt_jc_r1_results.json).

WHAT THIS IS NOT.  It is NOT a re-run of the r0 composer battery
(grt_jc_checks.py, seal 6ad01d1 -> verdict 8f07904) nor of the instrument
(grt_jc_probe.py, seal 7212e56 -> verdict fc89b03).  Both of those runners and
all of their artifacts are BYTE-FROZEN at r1 and are not touched.  This runner
imports the instrument's roster and stage builder (grt_jc_probe.ROSTER / Stage
-- the same 29 rows) and tests ONLY the statements repair round r1 introduced
or repaired.

============================ WHAT r1 REPAIRED ================================
PE1's CRITICAL 1: the note's SS2.10 (COORD) asserted that the digit map
R_lam : gr_lam(w) -> Delta = K_m[y] is a K_m-linear ISOMORPHISM (citing FGMN
Thm 4.2 through (IN-3)(c)).  FALSE on the note's own gr(w): the ambient ring is
O[x] and w >= 0 there, so an on-line abscissa at level lam obeys
a*gam_{m+1} <= lam and the on-line slot set is bounded by

    maxslot(lam) = floor((floor(lam/gam_{m+1}) - s_NR(lam))/e_m),

which is 0 at the note's own window base G0 on all 29 rows.  r1 restates the
coordinate calculus on the POST-TC-1 pieces B_n = union_k in(pi)^{-k}
gr_{n+kE} (the note's own JC-DOM object, which by the new LEMMA JC-LOC is
gr_{K[x]}(w) -- the object FGMN's theorems are about), with:
  JC-PIINV   R_{lam+E}(pi f) = c_pi * R_lam(f) for ONE row constant c_pi,
             hence rho_{lam+E}(pi f) = rho_lam(f) EXACTLY (rho := R/a_lam);
  JC-BSURJ   the colimit coordinate is ONTO Delta, by an explicit REALIZE-(m)
             construction (PROVED in-note, no longer cited);
  (DMULT)    R_{lam+mu}(fg) = y^{delta(lam,mu)} R_lam(f) R_mu(g) -- the single
             remaining CITED input (composite-stage residual multiplicativity),
             from which (COORD-B)(2) (B_n free of rank one over B_0 = Delta)
             follows;
  JC-COB     hence JC-SPAN's slot-delta unit is u = a_gamma * a_gamma'.
PE1's CRITICAL 2: JC-PSIKER's closing sentence ("TC-3 has a nonzero kernel on
every graded piece") is FALSE for lam < wPhi_NR (all 29 rows at their base);
r1 re-quantifies: ZERO for lam < wPhi_NR, NONZERO for lam in wPhi_NR + W, and
nonzero on EVERY graded piece of B (where TC-3 is actually applied).

============================= PREREGISTERED LEGS =============================
(violation counts; a family whose observed count differs from its sealed
prediction is RED.  Deterministic, exact arithmetic, no randomness.)

EXT-GATE     engine_ext install() + check_pins() + agreement_gate() re-run
             (standing in-unit rule).                        PREDICTED 0.

R1-BND       the slot bound of SS2.10 [r1]: maxslot(G0) == 0 on every row, i.e.
             the r0 (COORD)'s surjectivity onto Delta is FALSE at the note's own
             window base (PE1's counter-instance, reproduced as a SCORED fact).
             Census: maxslot(G0 + kE) for k = 0..3 per row.   PREDICTED 0.
R1-PER       LEMMA JC-PIINV: for k = 1,2 and every sampled (f,lam),
             R_{lam+kE}(pi^k f) == c_pi^k * R_lam(f) with ONE c_pi per row
             (independent of f, lam, slot and k), and -- on window lines --
             rho_{lam+kE}(pi^k f) == rho_lam(f) EXACTLY.      PREDICTED 0.
R1-INJ       SS1's injectivity in both directions: R_lam(f) != 0 at lam = w(f),
             and R_lam(f) == 0 (empty slot set) at lam = w(f) - E, w(f) - 2E.
                                                             PREDICTED 0.
R1-SURJ      LEMMA JC-BSURJ: for target digit polynomials of y-degree 0,1,2
             (all-ones and a mixed target) the REALIZE construction at the
             predicted minimal k yields an INTEGRAL f with w(f) == n+kE and
             R(f) == the target ON THE NOSE, and each digit satisfies REALIZE's
             own R2/R3 laws (w_m(A_j) == beta_j, read_m == eps^{-1}c_j).
             Census: the minimal k per (row, degree).         PREDICTED 0.
R1-DMULT     (DMULT) EXACTLY (not up to a unit) on sampled pairs, together with
             w(fg) == w(f)+w(g).  This is the Delta-module half of (COORD-B) --
             the leg PE1 correctly noted NEITHER prior runner had.
                                                             PREDICTED 0.
R1-COB       COROLLARY JC-COB: R_{gamma+gamma'}(phi_gamma phi_gamma') ==
             a_gamma * a_gamma' * y^delta on the FULL anchor grid of every row
             (a sharp consequence of (DMULT): a failure refutes (COORD-B)(2)).
             Scored on ALL 29 rows, including the e_m = 1 row C4H, where it is
             also the sharp form JC-BOX-4 boxes.              PREDICTED 0.
R1-PSIK-LO   JC-PSIKER(ii), lower half: at window lines lam < wPhi_NR no class
             is certified dead by TC-3 (the kernel is 0 there).  DISCLOSED
             one-sidedness: the TC-3 certifier tries only the canonical
             quotient plus the pi-ladder, so "not certified dead" is weaker
             than "does not die" -- the zero half is PROVED arithmetically in
             the note and this leg is a consistency check.    PREDICTED 0.
R1-PSIK-HI   JC-PSIKER(iii): for every residue nu in Z/E (capped at 8 per row
             for cost), at a line lam = nu mod E with lam - wPhi_NR in W, the
             witness Phi_{m+1} * phi_{lam-wPhi_NR} has w == lam exactly, digit
             polynomial == a_{lam-wPhi_NR} * y^delta * psi_m(y), read == 0, and
             its death IS certified.                          PREDICTED 0.
R1-UNIT      GAP 3's falsifiable replacement for the r0 JC8 "every structure
             constant is a UNIT" check (which was vacuous as coded: zeros were
             filtered before the predicate existed and skipped pairs were never
             censused).  Every pair of the full grid is CLASSIFIED as
             unit / zero / den0 (undefined denominator) / oow (out of window);
             scored = no 'zero' and no 'den0' among in-window pairs, with the
             full skipped-pair census printed.                PREDICTED 0.

TEETH (five planted mutations, EVERY one must fire; a silent tooth is RED):
  T1  the REFUTED r0 universal claim "TC-3 has a nonzero kernel on every graded
      piece of gr", operationalized at the window base as lam - wPhi_NR >= 0 at
      lam = G0.                                     PREDICTED >= 1 per row.
  T2  "no k-shift is needed": the claim that a y-degree-1 target is realizable
      already at k = 0, i.e. maxslot(G0) >= 1.       PREDICTED >= 1 per row.
  T3  mutated (DMULT) with the shift y^{delta+1}.    PREDICTED >= 1 per row.
  T4  a PLANTED ZERO injected into the constant table, to prove R1-UNIT's
      predicate can fire at all (the exact defect GAP 3 found in JC8).
                                                    PREDICTED >= 1 per row.
  T5  mutated JC-PIINV "rho_{lam+E}(pi f) == y * rho_lam(f)" (a slot shift,
      always false).                                PREDICTED >= 1 per row.
Per-row tooth obligations are scored as their own family TOOTH-ROW.
Exit code = (violations + silent teeth).

FENCE HYGIENE (note SS3.5 [r1, G8]).  This runner calls Tower.constants ONLY
for the integer delta = (s_a[NR]+s_b[NR])//e_m (pure split arithmetic, exactly
SS1's definition; the closed-form c_T field of the same dict is never read) and
Tower.read / Tower.read_coeffs for the digit data the repaired statements are
ABOUT.  No family compares against the [ILN] closed form at all: r1's claims
are gr-side/B-side statements, so the c_T-vs-c_val comparison of the r0 battery
does not arise here.

PRE-SEAL SMOKE DISCLOSURE (honest, part of this seal).  Two read-only /tmp
scripts were run BEFORE this seal, to fix the design and the cost, and their
findings are why the predictions above are stated in this exact form:
 (a) a 6-row mechanism probe (C2A/C2I/C3A/C3I/C4H/C4I) which found: c_pi is a
     single row constant with values in {1, zbar, zbar^2}; rho-invariance is
     EXACT; (DMULT) holds with multiplier exactly 1 (hence JC-COB's sharp form
     u = a_gamma a_gamma'); the REALIZE construction reproduces degree-1 and
     degree-2 targets on the nose (at k = 3..20 on those rows); and the PSIKER
     witness behaves as JC-PSIKER(iii) states.
 (b) a 29-row cost probe fixing the search caps: the minimal k for a degree-2
     target is <= 34 (cap here 80), and the PSIKER-HI line offset is <= 14
     E-steps (cap here 80).  Only C4H needs k > 0 for a degree-0 target.
No scored predicate was weakened by either probe, and teeth T1/T2 are the r0
text's own refuted claims, fixed before the probes were written.

Outputs: grt_jc_r1_output.txt (stdout, tee'd by the caller) and
grt_jc_r1_results.json.
"""
import sys, os, json, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import grt_jc_probe as PR
import engine_ext as EE

KSHIFT_CAP = 80      # k-search cap for R1-SURJ / R1-PSIK-HI (smoke: <= 34)
NU_CAP = 8           # residue classes probed per row in R1-PSIK-HI
SAMP_CAP = 6         # sampled elements per row for R1-PER/INJ/DMULT

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


# ------------------------------------------------------------------ helpers
def Rpoly(S, lam, f):
    """the digit polynomial R_lam(f) as dict slot -> K_m coefficient."""
    return dict(S.T.read_coeffs(S.NR, lam, f))


def pmul(Km, a, b):
    out = {}
    for i, x in a.items():
        for j, y in b.items():
            k = i + j
            out[k] = Km.add(out.get(k, Km.zero()), Km.mul(x, y))
    return {k: v for k, v in out.items() if not Km.is_zero(v)}


def pshift(a, d):
    return {k + d: v for k, v in a.items()}


def pscale(Km, a, c):
    return {k: Km.mul(v, c) for k, v in a.items()}


def prop(Km, a, b):
    """the unique c in K_m^* with a == c*b, or None."""
    if set(a) != set(b) or not a:
        return None
    c = None
    for k in a:
        if Km.is_zero(b[k]):
            return None
        r = Km.mul(a[k], Km.inv(b[k]))
        if c is None:
            c = r
        elif c != r:
            return None
    return c


def maxslot(S, lam):
    """largest on-line slot allowed by integrality (w >= 0 on O[x])."""
    T = S.T
    em, gam = T.e[S.NR - 1], T.gam[S.NR]
    s = T.split(lam)['s'][S.NR]
    amax = lam // gam
    return -1 if amax < s else (amax - s) // em


def delta_of(S, lam, mu):
    T = S.T
    sA = T.split(lam)['s'][S.NR]
    sB = T.split(mu)['s'][S.NR]
    sC = T.split(lam + mu)['s'][S.NR]
    return (sA + sB - sC) // T.e[S.NR - 1]


def samples(S):
    """assorted INTEGRAL f with their exact weights (deterministic)."""
    T, P = S.T, S.P
    cands = [S.ph[r] for r in range(min(S.E, 3))]
    cands.append(S.X)
    cands.append(P.mul(S.ph[0], S.ph[1 % S.E]))
    cands.append(P.add(S.ph[0], P.mul(S.pi1, S.ph[0])))
    cands.append(S.PhiTop)
    out = []
    for f in cands[:SAMP_CAP + 1]:
        if not f:
            continue
        lam = T.wlev(S.NR, f)
        if lam is None:
            continue
        out.append((f, lam))
    return out


def surj_build(S, target, d):
    """LEMMA JC-BSURJ's construction.  target: dict slot -> K_m coeff, slots
    0..d.  Returns (k, lam, f, per-digit records) or None if no k <= cap."""
    T, P = S.T, S.P
    Km = T.K[S.NR - 1]
    em, gam = T.e[S.NR - 1], T.gam[S.NR]
    for k in range(KSHIFT_CAP):
        lam = S.G0 + k * S.E
        s = T.split(lam)['s'][S.NR]
        betas, ok = [], True
        for j in range(d + 1):
            a = s + j * em
            num = lam - a * gam
            if num % em or num // em < T.wPhi[S.NR - 1]:
                ok = False
                break
            betas.append((j, a, num // em))
        if not ok:
            continue
        f = P.zero()
        recs = []
        for (j, a, b) in betas:
            cj = target.get(j, Km.zero())
            if Km.is_zero(cj):
                recs.append((j, a, b, None))
                continue
            tau = Km.mul(Km.inv(T.eps(S.NR - 1, b)), cj)
            A = T.realize(S.NR - 1, tau, b, check=False)
            recs.append((j, a, b, (A, tau)))
            f = P.add(f, P.mul(A, P.pow(T.Phi[S.NR - 1], a)))
        return k, lam, f, recs
    return None


def classify(S, num, den):
    K = S.K
    if den is None or K.is_zero(den):
        return 'den0'
    if num is None or K.is_zero(num):
        return 'zero'
    return 'unit'


def score_table(tab, sink, rid):
    """R1-UNIT's scoring predicate, applied to a (possibly mutated) table."""
    for key, cls in sorted(tab.items()):
        if cls in ('zero', 'den0'):
            sink.append(('R1-UNIT', rid, 'structure constant %s at %s'
                         % (cls, key)))


# ------------------------------------------------------------------ per row
def run_row(S):
    T, P, K, NR, E = S.T, S.P, S.K, S.NR, S.E
    Km = T.K[NR - 1]
    gm, em = T.g[NR - 1], T.e[NR - 1]
    rid = S.spec['id']
    rec = {'id': rid, 'm': S.m, 'E': E, 'nK': S.nK, 'g_m': gm, 'e_m': em,
           'G0': S.G0, 'wPhiTop': S.wPhiTop, 'gam': T.gam[NR], 'N': S.N,
           'p': S.spec['p'], 'd0': S.spec['d0'], 'ring': S.spec['ring']}

    # ---------------- R1-BND : the slot bound (PE1's counter-instance) -----
    note('R1-BND')
    ms0 = maxslot(S, S.G0)
    if ms0 != 0:
        viol('R1-BND', rid, 'maxslot(G0) = %d != 0' % ms0)
    rec['maxslot'] = [maxslot(S, S.G0 + k * E) for k in range(4)]
    # T2 tooth: "no k-shift needed" == maxslot(G0) >= 1
    note('T2')
    if not (ms0 >= 1):
        fire('T2')
    # T1 tooth: the refuted universal kernel claim at the window base
    note('T1')
    if not (S.G0 - S.wPhiTop >= 0):
        fire('T1')

    smp = samples(S)
    rec['nsamples'] = len(smp)

    # ---------------- R1-PER : JC-PIINV -----------------------------------
    cpi = set()
    for (f, lam) in smp:
        base = Rpoly(S, lam, f)
        for k in (1, 2):
            note('R1-PER')
            got = Rpoly(S, lam + k * E, P.mul(P.pow(S.pi1, k), f))
            c = prop(Km, got, base)
            if c is None:
                viol('R1-PER', rid,
                     'R_{lam+%dE}(pi^%d f) not a K_m^*-multiple of R_lam(f) '
                     'at lam=%d' % (k, k, lam))
                continue
            if k == 1:
                cpi.add(c)
            else:
                if not any(c == Km.mul(c1, c1) for c1 in cpi):
                    viol('R1-PER', rid, 'c_pi^2 mismatch at lam=%d' % lam)
        # rho-invariance, exactly, on window lines
        for k in (1, 2):
            if not (T.inW(lam) and T.inW(lam + k * E)):
                continue
            note('R1-PER')
            a0 = Rpoly(S, lam, S.anchor(lam)).get(0)
            a1 = Rpoly(S, lam + k * E, S.anchor(lam + k * E)).get(0)
            if a0 is None or a1 is None or Km.is_zero(a0) or Km.is_zero(a1):
                viol('R1-PER', rid, 'anchor constant missing at lam=%d' % lam)
                continue
            lhs = pscale(Km, Rpoly(S, lam, f), Km.inv(a0))
            rhs = pscale(Km, Rpoly(S, lam + k * E,
                                   P.mul(P.pow(S.pi1, k), f)), Km.inv(a1))
            if lhs != rhs:
                viol('R1-PER', rid,
                     'rho not pi-invariant at lam=%d (k=%d)' % (lam, k))
            # T5 tooth: the y-shifted mutation
            note('T5')
            if rhs != pshift(lhs, 1):
                fire('T5')
    note('R1-PER')
    if len(cpi) != 1:
        viol('R1-PER', rid, 'c_pi is not a single row constant: %d values'
             % len(cpi))
    rec['c_pi'] = [PR.krepr(S, T.embed(c, NR - 1, NR)) for c in cpi]

    # ---------------- R1-INJ : injectivity, both directions ---------------
    for (f, lam) in smp:
        note('R1-INJ')
        if not Rpoly(S, lam, f):
            viol('R1-INJ', rid, 'R_lam(f) = 0 at lam = w(f) = %d' % lam)
        for j in (1, 2):
            if lam - j * E < 0:
                continue
            note('R1-INJ')
            if Rpoly(S, lam - j * E, f):
                viol('R1-INJ', rid,
                     'R_{lam-%dE}(f) != 0 although w(f) = %d > lam-%dE'
                     % (j, lam, j))

    # ---------------- R1-SURJ : JC-BSURJ ----------------------------------
    elems = [c for c in Km.elems() if not Km.is_zero(c)]
    alt = elems[1] if len(elems) > 1 else elems[0]
    rec['surj'] = {}
    for d in (0, 1, 2):
        for tname, target in (('ones', {j: Km.one() for j in range(d + 1)}),
                              ('mixed', dict([(0, Km.one()), (d, alt)]))):
            note('R1-SURJ')
            got = surj_build(S, target, d)
            if got is None:
                viol('R1-SURJ', rid,
                     'no k <= %d for degree %d (%s)' % (KSHIFT_CAP, d, tname))
                continue
            k, lam, f, recs = got
            rec['surj']['%d-%s' % (d, tname)] = k
            note('R1-SURJ')
            if T.wlev(NR, f) != lam:
                viol('R1-SURJ', rid, 'w(f) != n+kE for degree %d (%s)'
                     % (d, tname))
                continue
            note('R1-SURJ')
            tgt = {j: c for j, c in target.items() if not Km.is_zero(c)}
            if Rpoly(S, lam, f) != tgt:
                viol('R1-SURJ', rid, 'R(f) != target for degree %d (%s)'
                     % (d, tname))
            for (j, a, b, made) in recs:
                if made is None:
                    continue
                A, tau = made
                note('R1-SURJ')
                if T.wlev(NR - 1, A) != b or T.read(NR - 1, b, A) != tau:
                    viol('R1-SURJ', rid,
                         'REALIZE R2/R3 fails at slot %d (degree %d)' % (j, d))

    # ---------------- R1-DMULT : (DMULT) ----------------------------------
    for (f, lf) in smp:
        for (g, lg) in smp:
            if f == S.PhiTop and g == S.PhiTop:
                continue
            fg = P.mul(f, g)
            note('R1-DMULT')
            if T.wlev(NR, fg) != lf + lg:
                viol('R1-DMULT', rid, 'w(fg) != w(f)+w(g) at (%d,%d)'
                     % (lf, lg))
                continue
            d = delta_of(S, lf, lg)
            lhs = Rpoly(S, lf + lg, fg)
            rhs = pshift(pmul(Km, Rpoly(S, lf, f), Rpoly(S, lg, g)), d)
            note('R1-DMULT')
            if lhs != rhs:
                viol('R1-DMULT', rid,
                     '(DMULT) fails at (%d,%d): %s vs %s'
                     % (lf, lg, sorted(lhs), sorted(rhs)))
            # T3 tooth: the y^{delta+1} mutation
            note('T3')
            if lhs != pshift(rhs, 1):
                fire('T3')

    # ---------------- R1-COB : JC-COB on the full anchor grid -------------
    grid = [(r, s) for r in range(E) for s in range(E)] if E <= 8 \
        else PR.pair_grid(E)
    cob = {'tested': 0, 'oow': 0}
    for (r, s) in grid:
        ga, gb = S.gam_of[r], S.gam_of[s]
        if not T.inW(ga + gb):
            cob['oow'] += 1
            continue
        lam = ga + gb
        f = P.mul(S.ph[r], S.ph[s])
        note('R1-COB')
        if T.wlev(NR, f) != lam:
            viol('R1-COB', rid, 'w(phi_a phi_b) != a+b at (%d,%d)' % (r, s))
            continue
        aa = Rpoly(S, ga, S.ph[r]).get(0)
        ab = Rpoly(S, gb, S.ph[s]).get(0)
        note('R1-COB')
        if aa is None or ab is None:
            viol('R1-COB', rid, 'anchor digit constant missing at (%d,%d)'
                 % (r, s))
            continue
        d = delta_of(S, ga, gb)
        note('R1-COB')
        if Rpoly(S, lam, f) != {d: Km.mul(aa, ab)}:
            viol('R1-COB', rid,
                 'R(phi_a phi_b) != a_a a_b y^%d at (%d,%d)' % (d, r, s))
        cob['tested'] += 1
    rec['cob'] = cob

    # ---------------- R1-PSIK-LO : the kernel is zero below wPhi_NR -------
    lo = {'lines': 0, 'certified_dead': 0}
    for r in range(min(E, NU_CAP)):
        lam = S.gam_of[r]
        if lam >= S.wPhiTop:
            continue
        note('R1-PSIK-LO')
        if lam - S.wPhiTop >= 0:
            viol('R1-PSIK-LO', rid, 'line %d not below wPhi_NR' % lam)
            continue
        lo['lines'] += 1
        for f in (S.ph[r], P.add(S.ph[r], P.mul(S.pi1, S.ph[r]))):
            if T.wlev(NR, f) != lam:
                continue
            note('R1-PSIK-LO')
            if S.zero_cert(f, lam):
                lo['certified_dead'] += 1
                viol('R1-PSIK-LO', rid,
                     'a class at line %d < wPhi_NR is certified DEAD' % lam)
    rec['psik_lo'] = lo

    # ---------------- R1-PSIK-HI : nonzero kernel on every piece of B -----
    psi = T.psi[NR - 1]
    hi = {'nu': 0, 'lines': []}
    for r in range(min(E, NU_CAP)):
        lam = None
        for k in range(KSHIFT_CAP):
            cand = S.gam_of[r] + k * E
            if T.inW(cand) and cand - S.wPhiTop >= 0 \
               and T.inW(cand - S.wPhiTop):
                lam = cand
                break
        note('R1-PSIK-HI')
        if lam is None:
            viol('R1-PSIK-HI', rid,
                 'no line in residue %d with lam-wPhi_NR in W' % r)
            continue
        nu = lam - S.wPhiTop
        f = P.mul(S.PhiTop, S.anchor(nu))
        hi['nu'] += 1
        hi['lines'].append(lam)
        note('R1-PSIK-HI')
        if T.wlev(NR, f) != lam:
            viol('R1-PSIK-HI', rid, 'w(Phi_top phi_nu) != lam at nu=%d' % nu)
            continue
        note('R1-PSIK-HI')
        if not K.is_zero(T.read(NR, lam, f)):
            viol('R1-PSIK-HI', rid, 'read != 0 at lam=%d' % lam)
        R = Rpoly(S, lam, f)
        note('R1-PSIK-HI')
        if not R:
            viol('R1-PSIK-HI', rid, 'digit polynomial 0 at lam=%d' % lam)
            continue
        anu = Rpoly(S, nu, S.anchor(nu)).get(0)
        d = delta_of(S, S.wPhiTop, nu)
        want = {}
        for i, c in enumerate(psi):
            if not Km.is_zero(c):
                want[d + i] = Km.mul(anu, c)
        note('R1-PSIK-HI')
        if R != want:
            viol('R1-PSIK-HI', rid,
                 'digit polynomial != a_nu y^%d psi_m(y) at lam=%d' % (d, lam))
        note('R1-PSIK-HI')
        if not S.zero_cert(f, lam):
            viol('R1-PSIK-HI', rid,
                 'the psi-kernel witness at lam=%d is NOT certified dead' % lam)
    rec['psik_hi'] = hi

    # ---------------- R1-UNIT : the falsifiable unit check + census -------
    tab, census = {}, {'unit': 0, 'zero': 0, 'den0': 0, 'oow': 0}
    for (r, s) in grid:
        ga, gb = S.gam_of[r], S.gam_of[s]
        if not T.inW(ga + gb):
            census['oow'] += 1
            continue
        base = S.anchor(ga + gb)
        num = T.read(NR, ga + gb, P.mul(S.ph[r], S.ph[s]))
        den = T.read(NR, ga + gb, base)
        cls = classify(S, num, den)
        tab[(r, s)] = cls
        census[cls] += 1
        note('R1-UNIT')
    sink = []
    score_table(tab, sink, rid)
    for v in sink:
        VIOL.append(v)
    # T4 tooth: plant a zero and require the SAME predicate to report it
    note('T4')
    if tab:
        mut = dict(tab)
        mut[sorted(mut)[0]] = 'zero'
        probe = []
        score_table(mut, probe, rid)
        if len(probe) > len(sink):
            fire('T4')
    rec['unit_census'] = census
    rec['grid'] = len(grid)

    # ---------------- per-row tooth obligations ---------------------------
    for t in ('T1', 'T2', 'T3', 'T4', 'T5'):
        note('TOOTH-ROW')
        if ROWTEETH.get(t, 0) == 0:
            viol('TOOTH-ROW', rid, 'tooth %s SILENT on this row' % t)
    rec['teeth'] = dict(ROWTEETH)
    return rec


def main(smoke=False):
    t0 = time.time()
    print('grt_jc_r1_checks.py -- GRTJC r1 SUPPLEMENTARY battery%s'
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
        print('  [%6.1fs] %-6s m=%d E=%-3d |K|=%-3d g_m=%d e_m=%d  maxslot(G0)=%d'
              '  c_pi=%s  COB %d/%d  psik lo %d hi %d  units %d/%d  (%.1fs)'
              % (time.time() - t0, rec['id'], rec['m'], rec['E'], rec['nK'],
                 rec['g_m'], rec['e_m'], rec['maxslot'][0],
                 ','.join(rec['c_pi']), rec['cob']['tested'],
                 rec['cob']['tested'] + rec['cob']['oow'],
                 rec['psik_lo']['lines'], rec['psik_hi']['nu'],
                 rec['unit_census']['unit'], rec['grid'],
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
    for f in ['EXT-GATE', 'R1-BND', 'R1-PER', 'R1-INJ', 'R1-SURJ', 'R1-DMULT',
              'R1-COB', 'R1-PSIK-LO', 'R1-PSIK-HI', 'R1-UNIT', 'TOOTH-ROW',
              'BUILD']:
        if f in COUNTS or f in fam:
            print('  %-12s samples %6d   violations %4d'
                  % (f, COUNTS.get(f, 0), fam.get(f, 0)))
    print()
    print('TEETH (each MUST fire)')
    for t in ['T1', 'T2', 'T3', 'T4', 'T5']:
        print('  %-3s fired %6d times (opportunities %d)%s'
              % (t, TEETH.get(t, 0), COUNTS.get(t, 0),
                 '' if TEETH.get(t, 0) > 0 else '   *** SILENT TOOTH = RED ***'))

    tot = {'cob': 0, 'oow': 0, 'unit': 0, 'zero': 0, 'den0': 0, 'uoow': 0,
           'lo': 0, 'hi': 0, 'grid': 0}
    print()
    print('PER-ROW CENSUS (R1-CEN: the r1 repair\'s own geography)')
    print('  %-6s %2s %4s %4s %3s %3s %7s %8s  %-14s %-10s %s'
          % ('row', 'm', 'E', '|K|', 'gm', 'em', 'G0', 'wPhi_NR',
             'maxslot k=0..3', 'c_pi', 'minK d=0,1,2 (ones)'))
    for rid, rec in RESULTS['rows'].items():
        tot['cob'] += rec['cob']['tested']
        tot['oow'] += rec['cob']['oow']
        for k in ('unit', 'zero', 'den0'):
            tot[k] += rec['unit_census'][k]
        tot['uoow'] += rec['unit_census']['oow']
        tot['lo'] += rec['psik_lo']['lines']
        tot['hi'] += rec['psik_hi']['nu']
        tot['grid'] += rec['grid']
        print('  %-6s %2d %4d %4d %3d %3d %7d %8d  %-14s %-10s %s'
              % (rid, rec['m'], rec['E'], rec['nK'], rec['g_m'], rec['e_m'],
                 rec['G0'], rec['wPhiTop'], rec['maxslot'],
                 ','.join(rec['c_pi']),
                 [rec['surj'].get('%d-ones' % d) for d in (0, 1, 2)]))
    RESULTS['totals'] = tot
    print()
    print('R1-COB: %d anchor pairs scored (%d out-of-window skipped) -- '
          'u == a_gamma a_gamma\' y^delta' % (tot['cob'], tot['oow']))
    print('R1-UNIT census: %d unit / %d zero / %d undefined-denominator / '
          '%d out-of-window, over %d grid pairs (GAP 3\'s missing census)'
          % (tot['unit'], tot['zero'], tot['den0'], tot['uoow'], tot['grid']))
    print('R1-PSIK: %d window lines below wPhi_NR with kernel 0; %d residue '
          'classes with a certified nonzero kernel witness'
          % (tot['lo'], tot['hi']))
    if VIOL:
        print()
        print('VIOLATIONS (first 60):')
        for (f, tag, det) in VIOL[:60]:
            print('  [%s] %s: %s' % (f, tag, det))
    silent = [t for t in ['T1', 'T2', 'T3', 'T4', 'T5'] if TEETH.get(t, 0) == 0]
    print()
    print('elapsed %.1fs;  total violations %d;  silent teeth %s'
          % (time.time() - t0, len(VIOL), silent if silent else 'NONE'))
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                      'grt_jc_r1_results.json')
    with open(out, 'w') as fh:
        json.dump(RESULTS, fh, indent=1, sort_keys=True, default=str)
    print('wrote %s' % out)
    return len(VIOL) + len(silent)


if __name__ == '__main__':
    sys.exit(0 if main(smoke=('--smoke' in sys.argv)) == 0 else 1)
