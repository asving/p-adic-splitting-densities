#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
open2attack_checks.py -- W2-OPEN-2 ATTACK unit (examples-first battery on the
weld's one open lemma), machine leg of
lean/notes/openmath/OPEN2ATTACK_2026-08-08.md.

TARGET.  W2-OPEN-2/OPEN-2a (GRTW2_PROOF_2026-08-08.md Sec 5.2, ACCEPTED AS A
BOX): at a junction at level m+1 with m >= 2, keys below byte-shared and
recorded xi = 1, is the raw print key byte-equal to the harness key?  Proved
at m = 1 (LEMMA W2-ID1); OPEN at m >= 2.  This runner builds a targeted
battery of m >= 2 junctions probing WHY the identification holds, keyed on
the slot calculus (all quantities per shared-key junction at GMN order r,
slot level M = r-2, c = Thm-phir's constant, psi = psi_M, fm = g_M):

    rho_j   := (level-M read of print slot P_j)/(level-M read of harness
               slot C_j)     [W2-C2's slot ratio; actual_ratios]
    Rl      := rres(r-1, Phi^har)  (the print residual of the harness lift)
    delta_j := Rl[j] * rho_j / (c * psi_j)   [the GAUGE DISCREPANCY: how
               differently the print evaluator prices the two builders'
               slot bytes; delta_j = 1 <=> Rl[j] = c psi_j / rho_j]
    STRICT  := Rl = w * psi coefficientwise for some unit w
    sigma'  := the interior-twist coordinate map z_q -> theta_q z_q,
               theta_q = z_{q-1}^{A_{q-1} e_{q-1}}, q = 2..M (at M = 2 a
               K_1-algebra automorphism of K_2 exactly when the below-key
               byte-share law theta^{g_1} = 1 holds)

    Derived reduction (note Sec 1): STRICT <=> delta_j = rho_j on supp;
    byte-equal <=> rho_j = 1 on supp.  So a counter-instance to the
    OPEN-2a forward direction (strict version) is EXACTLY a junction with
    delta_j = rho_j != 1 simultaneously on every supported slot -- the
    simultaneous-defeat equations.  The battery measures delta, rho, and
    the candidate mechanism law delta_j = rho_j / sigma'(rho_j).

ROSTER + BATTERY (all deterministic; engine = committed iterlawn_pe_reimpl
imported verbatim; classifier = the sealed probe's GmnLeg imported verbatim;
junction helpers orbit_scan / actual_ratios / junction_data imported verbatim
from the sealed grt_w2_checks; the ONLY fresh engine code is TowerX, a
disclosed copy of ITL.Tower.__init__ with the psi-degree validation
generalized from the hard-coded g <= 2 to a brute-force irreducibility
test, plus RAW coefficient specs a la GWP.SpecTower):

  B5-ROSTER   the 16 committed towers (GWP.TOWERS), all junctions.
  B1  F9 exhaustive slice: chamber Z3, reads (2,1,1)+(3,1,2), psi0 = y+1,
      psi1 = y^2+1 -- interior char theta = z1^{A1 e1} = -1 nontrivial,
      support-invisible (r=3 byte-equal): the I4B invisible-twist genre
      engineered at M = 2.  Top read (e2,h2) in {(1,1),(2,1),(3,1),(3,2),
      (2,3)} x psi2 over K2 = F9: ALL 8 monic deg-1, ALL irreducible
      deg-2 (on the wrap-active eh rows; 12-sample elsewhere), deg-3
      y^3+by+c sample, deg-4 binomials y^4+c (the PE4 (F9, g=4, supp
      {0,4}) spurious geography, now one level up).
  B1f flat control: same chamber with read1 = (1,1,2) (wrap-dead, interior
      char still -1): separates wrap-activity from theta-nontriviality.
  B4  (C-coll) control: read0 = (1,1,1) (A1 = 0, interior trivial).
  B2  F64 slice: chamber Z2, reads (2,1,2)+(2,1,3), psi0 = y^2+y+1,
      psi1 = y^3 + z1 (the PE3 counter-instance chamber genre, g1 = 3,
      theta of order 3): deg-1/2/3 psi2 samples; the y^3+c rows are the
      cube-root-stabilizer spurious genre at M = 2.
  B3  stacked (M = 3): the I4B chamber (3,2,1)+(2,1,1)+(1,1,2) with read-3
      swept (the EXACT geography of GRTW2's two instance-warranted
      junction-levels I4A/I4B r=5); the I4A chamber likewise; and the B1
      chamber extended by (2,1,1)/psi2 = y+z2 (byte-equal, doubly twisted)
      with read-3 swept.

CHECK FAMILIES (preregistered where derived; EXPLORATORY labelled):
  OA-ADM      vok+onesided at every shared-below junction     PREDICT 0
  OA-PHIR     rres(phi^cls) = c*psi (Thm-phir reproduction)   PREDICT 0
  OA-TOPRES   Rl[fm] = c (top slot byte-triviality)           PREDICT 0
  OA-RHOBYTE  byte-equal <=> rho_j = 1 at all slots           PREDICT 0
  OA-BWD      byte-equal ==> STRICT                           PREDICT 0
  OA-GAUGE    theta-trivial (C-coll) rows: delta_j = 1        PREDICT 0
  OA-XI       theta-trivial rows: the GRTW2 Sec 3.4 formula pair
              satisfies the orbit equations (sealed CK-XI
              semantics reproduced; also the TEETH-2 surface)   PREDICT 0
  OA-FWD-M1   m=1: STRICT ==> byte-equal (W2-ID1 strict form) PREDICT 0
  OA-FWD-M2 / OA-FWD-M3   m>=2: STRICT ==> byte-equal.  THE QUESTION.
              No confident preregistration -- mechanism-derived expectation
              is 0 violations on gap-free rows (see OA-SIGMA); ANY violation
              is the OPEN-2a counter-instance and is the deliverable.
  OA-FWD-REC  recorded xi = 1 ==> byte-equal (the box's literal premise
              clause; recorded = sealed enumeration-order scan)  same status
  OA-SIGMA    on M=2 gap-free rows: delta_j = rho_j / sigma'(rho_j)
              (mechanism candidate; PREDICT 0 on gap-free M=2 rows;
              EXPLORATORY at M>=3 and on gap rows -- both variants
              rho^{1-sigma'} and rho^{sigma'-1} recorded, sign to be fixed
              by the note's derivation)
  OA-SPURGEO  spurious recording (byte-equal & recorded xi != 1) happens
              IFF d := gcd of pairwise differences of supp(psi) u {g_m}
              has a d-torsion unit preceding 1 in F.elems() order (PE4's
              m=1 selection geography, lifted)                 PREDICT 0
  OA-SPUR     census of spurious rows at m >= 2; PREDICT >= 1 (the
              F64 y^3+c genre or the F9 y^4-gen genre) -- extends PE3's
              converse boundary to m >= 2
  TEETH-1     print leg garbled (GmnLeg mut_droptwist) on T2C+T3C:
              PREDICT caught (>= 1 violation) on both
  TEETH-2     harness eps garbled (GWP.MutHTower refuted reading) on
              T2A+T2B: PREDICT caught on both

SMOKE RECORD (disclosed): before sealing, the runner was smoke-run with
--smoke (roster subset T2A/T2C/I4B + ~20 battery rows + both teeth) to
shake out indexing errors; the full battery was NOT run before commit 1.
Exploratory rows are labelled in the families above; nothing in the smoke
subset was used to tune predictions except as disclosed in the note.

Outputs: open2attack_output.txt, open2attack_results.json.
"""
import sys, os, json, time, itertools, collections
from math import gcd

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import iterlawn_pe_reimpl as ITL
import grt_weld_probe as GWP
import grt_w2_checks as W2

VIOL = []                      # active violation sink (switched for teeth)
COUNTS = collections.defaultdict(int)
ROWS = []
RES = {'rows': None, 'families': {}, 'teeth': {}, 'censuses': {}}

def note(fam, n=1):
    COUNTS[fam] += n

def viol(fam, tag, msg):
    VIOL.append((fam, tag, str(msg)))

# ------------------------------------------------ field polynomial helpers
def poly_divmod_field(K, f, g):
    """f, g coefficient lists over field K, g monic; returns (q, r)."""
    f = list(f)
    dg = len(g) - 1
    q = [K.zero()]*max(1, len(f))
    while True:
        while f and K.is_zero(f[-1]):
            f.pop()
        if len(f) - 1 < dg:
            break
        c = f[-1]; d = len(f) - 1 - dg
        q[d] = c
        for i in range(dg + 1):
            f[d + i] = K.add(f[d + i], K.neg(K.mul(c, g[i])))
    return q, f

def poly_irr(K, coeffs):
    """monic coeffs over the finite field K: irreducible?  brute-force
    monic-divisor test up to degree g//2 (fields here are tiny)."""
    g = len(coeffs) - 1
    if g == 1:
        return True
    els = list(K.elems())
    for d in range(1, g//2 + 1):
        for tail in itertools.product(els, repeat=d):
            div = list(tail) + [K.one()]
            _, rem = poly_divmod_field(K, list(coeffs), div)
            if not rem or all(K.is_zero(c) for c in rem):
                return False
    return True

# ------------------------------------------------------------------ TowerX
class TowerX(ITL.Tower):
    """The committed engine with TWO disclosed changes, both in the psi
    validation of __init__ (body otherwise copied line-for-line from the
    committed ITL.Tower.__init__):
      (1) psi irreducibility checked by the general poly_irr above for any
          degree g >= 2 (the committed engine hard-codes the deg-2 no-root
          test and asserts g in {1,2});
      (2) coefficient specs may be ('RAW', element) (GWP.SpecTower's
          mechanism), so battery moduli can be arbitrary field elements.
    REALIZE, reads, weights, lifts, eps: inherited verbatim."""

    def __init__(self, name, R, d0, Phi0_spec, reads, psi_specs):
        self.name = name; self.R = R; self.P = ITL.PolyO(R)
        self.reads = reads; self.NR = len(reads); self.n = self.NR - 1
        self.e = [r[0] for r in reads]; self.h = [r[1] for r in reads]
        self.g = [r[2] for r in reads]
        for (e, h, g) in reads:
            assert e >= 1 and h >= 1 and g >= 1
            assert gcd(e, h) == 1
        self.l = [0]*self.NR; self.lp = [0]*self.NR
        for j in range(self.NR):
            self.l[j], self.lp[j] = ITL.bez(self.e[j], self.h[j])
        self.gam = [None]*(self.NR+1); self.wPhi = [0]*(self.NR+1)
        self.gam[1] = self.h[0]
        self.wPhi[1] = self.e[0]*self.g[0]*self.gam[1]
        for j in range(1, self.NR):
            self.gam[j+1] = self.e[j]*self.wPhi[j] + self.h[j]
            if j+1 <= self.NR:
                self.wPhi[j+1] = self.e[j]*self.g[j]*self.gam[j+1] \
                    if j+1 <= self.NR else None
        p = R.p
        self.k0 = ITL.GFp(p)
        Phi0 = tuple(R.liftk(c) for c in Phi0_spec)
        assert len(Phi0) == d0+1 and Phi0[-1] == R.one()
        self.d0 = d0
        phibar = tuple(R.res(c, 0) for c in Phi0)
        assert phibar[-1] == 1
        if d0 >= 2:
            assert d0 <= 3
            for a in self.k0.elems():
                v = 0
                for c in reversed(phibar):
                    v = (v*a + c) % p
                assert v != 0, "phibar reducible"
        self.K = [None]*(self.NR+1)
        self.K[0] = ITL.Ext(self.k0, phibar)
        self.z = [None]*(self.NR+1)
        self.psi = [None]*self.NR
        for j in range(self.NR):
            Kj = self.K[j]
            spec = psi_specs[j]
            cands = spec[1] if (isinstance(spec, tuple) and spec
                                and spec[0] == 'TRY') else [spec]
            psi = None
            for cand in cands:
                assert len(cand) == self.g[j] + 1
                trial = tuple(self._coeff(Kj, sp, j) for sp in cand)
                if trial[-1] != Kj.one():
                    continue
                if Kj.is_zero(trial[0]):
                    continue
                if self.g[j] >= 2:                       # [disclosed change]
                    if not poly_irr(Kj, list(trial)):
                        continue
                psi = trial
                break
            assert psi is not None, "no valid psi_%d candidate" % j
            self.psi[j] = psi
            self.K[j+1] = ITL.Ext(Kj, psi)
            self.z[j+1] = self.K[j+1].reduce_list(
                [Kj.zero(), Kj.one()])
        self._wmemo = {}; self._rmemo = {}; self._ememo = {}
        self._amemo = {}; self._smemo = {}
        self.ct_Im = 0; self.ct_R123 = 0
        self.Phi = [None]*self.NR
        self.Phi[0] = Phi0
        for m in range(0, self.n):
            self.Phi[m+1] = self._build_lift(m)
        for m in range(1, self.n+1):
            assert self.wlev(m, self.Phi[m]) == self.wPhi[m], \
                "wPhi gate fails at level %d" % m

    def _coeff(self, Kj, sp, j):                          # [disclosed change]
        if isinstance(sp, tuple) and sp and sp[0] == 'RAW':
            return sp[1]
        return ITL.Tower._coeff(self, Kj, sp, j)

def build_tower_x(spec):
    R = ITL.Zp(spec['p']) if spec['ring'] == 'Zp' else ITL.Fpt(spec['p'])
    name = '%s,p=%d,%s' % (spec['ring'], spec['p'], spec['id'])
    return TowerX(name, R, spec['d0'], spec['Phi0'], spec['reads'],
                  list(spec['psi']))

# ------------------------------------------------------- sigma' twist map
def sigma_twist(T, M, x, inverse=False):
    """candidate interior-twist coordinate map on K_M: recursively
    z_q -> theta_q z_q (q = 2..M), theta_q = z_{q-1}^{A_{q-1} e_{q-1}},
    A_{q-1} = l_{q-2} g_{q-2} gamma_{q-1}; inverse=True twists by
    theta_q^{-1}.  A K_1-linear coordinate map always; an automorphism
    exactly when each theta_q stabilizes psi_{q-1}'s support law."""
    def rec(q, y):
        if q <= 1:
            return y
        K = T.K[q]; Km1 = T.K[q-1]
        A = T.l[q-2]*T.g[q-2]*T.gam[q-1]
        expo = A*T.e[q-1]*(-1 if inverse else 1)
        th = ITL.fpow(Km1, T.z[q-1], expo)
        out = K.zero()
        for i, yi in enumerate(y):
            yi2 = rec(q-1, yi)
            yi2 = Km1.mul(yi2, ITL.fpow(Km1, th, i))
            out = K.add(out, K.mul(K.from_base(yi2),
                                   ITL.fpow(K, T.z[q], i)))
        return out
    return rec(M, x)

# ----------------------------------------------------------- gap ledger
def gap_scan(T, q, A, beta):
    """support-gap ledger of an on-line level-q object A at weight beta:
    counts nodes of the dev tree whose attained initial grid abscissa
    exceeds the eq12 grid start s (the piecewise terms of the gauge)."""
    if q == 0 or not A:
        return 0
    dv = T.P.dev(list(A), T.Phi[q-1])
    s, u = ITL.eq12(beta, T.e[q-1], T.h[q-1])
    gaps = 0
    first_online = None
    for a in range(s, len(dv), T.e[q-1]):
        dig = dv[a] if a < len(dv) else ()
        if not dig:
            continue
        num = beta - a*T.gam[q]
        if num % T.e[q-1] != 0:
            continue
        sw = num // T.e[q-1]
        wA = T.wlev(q-1, dig)
        if wA == sw:
            if first_online is None:
                first_online = a
            gaps += gap_scan(T, q-1, list(dig), sw)
    if first_online is not None and first_online != s:
        gaps += 1
    return gaps

# ------------------------------------------------------ junction analysis
def elt(x):
    return repr(x)

def analyze_tower(T, G, tag, genre):
    """walk junctions r = 3..NR+1; full slot-calculus record per shared-
    below junction; SKIP above the first byte divergence."""
    for r in range(3, T.NR + 2):
        m = r - 1
        M = r - 2
        har = tuple(T.Phi[m]) if m <= T.n else GWP.top_lift(T)
        cls = tuple(G.phi[r])
        shared_below = all(tuple(G.phi[q]) == tuple(T.Phi[q-1])
                           for q in range(2, r))
        row = {'tag': tag, 'genre': genre, 'r': r, 'M': M,
               'shared_below': shared_below, 'byte_equal': har == cls}
        if not shared_below:
            row['status'] = 'SKIP'
            note('OA-SKIP')
            ROWS.append(row)
            continue
        F = G.Kc[r-2]
        fm = G.f[r-1]
        psi = G.psis[r-1]
        c = G.thm_c(r)
        # OA-ADM + residual + scan (sealed enumeration-order semantics)
        note('OA-ADM')
        try:
            sc = W2.orbit_scan(G, r, list(har))
        except (AssertionError, ZeroDivisionError) as ex:
            viol('OA-ADM', tag, 'orbit_scan hard-fails at r=%d: %s' % (r, ex))
            row['status'] = 'ADM-HARD-FAIL'
            ROWS.append(row)
            continue
        row['vok'] = sc['vok']; row['onesided'] = sc['onesided']
        if not (sc['vok'] and sc['onesided']):
            viol('OA-ADM', tag, 'vok/onesided fails at r=%d (vok=%s os=%s)'
                 % (r, sc['vok'], sc['onesided']))
            row['status'] = 'ADM-FAIL'
            ROWS.append(row)
            continue
        Rl = G.rres(r-1, list(har))
        strict = sc['strict'] is not None
        row['strict'] = strict
        row['orbit'] = (elt(sc['orbit'][0]), elt(sc['orbit'][1])) \
            if sc['orbit'] else None
        rec_triv = sc['orbit'] is not None and sc['orbit'][0] == F.one()
        row['recorded_trivial'] = rec_triv
        # OA-PHIR
        note('OA-PHIR')
        try:
            Rc = G.rres(r-1, list(cls))
            phir_ok = (len(Rc) == fm+1 and
                       all(Rc[j] == F.mul(c, psi[j]) for j in range(fm+1)))
        except AssertionError as ex:
            phir_ok = False
        if not phir_ok:
            viol('OA-PHIR', tag, 'Thm-phir residual fails at r=%d' % r)
        # OA-TOPRES
        note('OA-TOPRES')
        if len(Rl) != fm+1 or Rl[fm] != c:
            viol('OA-TOPRES', tag, 'top rres slot != c at r=%d' % r)
            row['status'] = 'TOPRES-FAIL'
            ROWS.append(row)
            continue
        # slot ratios
        act = W2.actual_ratios(T, G, r)
        if isinstance(act, tuple):
            note('OA-RHOBYTE')
            viol('OA-ADM', tag, 'WEIGHT/SUPPORT split at shared-below '
                 'junction r=%d (%s@%d)' % (r, act[0], act[1]))
            row['status'] = 'SPLIT'
            ROWS.append(row)
            continue
        supp = [j for j in range(fm) if not F.is_zero(psi[j])]
        row['supp'] = supp
        row['g_m'] = fm
        rho = {j: act[j] for j in supp}
        rho_triv = all(v == F.one() for v in act.values())
        # OA-RHOBYTE
        note('OA-RHOBYTE')
        if row['byte_equal'] != rho_triv:
            viol('OA-RHOBYTE', tag, 'byte law != rho-triviality at r=%d' % r)
        # delta_j
        deltas = {}
        for j in supp:
            deltas[j] = F.mul(F.mul(Rl[j], rho[j]),
                              F.inv(F.mul(c, psi[j])))
        row['rho'] = {j: elt(rho[j]) for j in supp}
        row['delta'] = {j: elt(deltas[j]) for j in supp}
        row['rho_nontriv'] = [j for j in supp if rho[j] != F.one()]
        row['delta_nontriv'] = [j for j in supp if deltas[j] != F.one()]
        row['defeat_slots'] = [j for j in supp
                               if deltas[j] == rho[j] and rho[j] != F.one()]
        # OA-BWD: byte-equal ==> STRICT
        note('OA-BWD')
        if row['byte_equal'] and not strict:
            viol('OA-BWD', tag, 'byte-equal but NOT strict at r=%d' % r)
        # theta perimeter + formula pair
        jd = W2.junction_data(T, G, r)
        row['theta_trivial'] = jd['theta_trivial']
        # OA-GAUGE on (C-coll) rows
        if jd['theta_trivial']:
            note('OA-GAUGE')
            if row['delta_nontriv']:
                viol('OA-GAUGE', tag,
                     'delta != 1 on theta-trivial row r=%d' % r)
            # OA-XI: the GRTW2 Sec 3.4 closed form (sealed CK-XI semantics:
            # the PREDICTED pair must satisfy the orbit equations)
            note('OA-XI')
            if not W2.orbit_satisfies(G, r, list(har),
                                      jd['xi_pred'], jd['w_pred']):
                viol('OA-XI', tag,
                     'Sec 3.4 formula pair fails orbit equations at r=%d' % r)
        # gap ledger (harness + print slot digits)
        gaps = 0
        dvh = T.P.dev(list(har), T.Phi[m-1])
        dvc = T.P.dev(list(cls), T.Phi[m-1])
        for j in supp:
            kk = j*T.e[M]
            bj = (fm - j)*T.gam[M+1]
            if kk < len(dvh) and dvh[kk]:
                gaps += gap_scan(T, M, list(dvh[kk]), bj)
            if kk < len(dvc) and dvc[kk]:
                gaps += gap_scan(T, M, list(dvc[kk]), bj)
        row['gaps'] = gaps
        # OA-FWD (strict version) + OA-FWD-REC (the box's literal premise)
        fam = 'OA-FWD-M1' if M == 1 else ('OA-FWD-M2' if M == 2
                                          else 'OA-FWD-M3')
        note(fam)
        if strict and not row['byte_equal']:
            viol(fam, tag, 'STRICT but byte-RED at r=%d '
                 '<-- OPEN-2a COUNTER-INSTANCE' % r)
        note('OA-FWD-REC')
        if rec_triv and not row['byte_equal']:
            viol('OA-FWD-REC', tag, 'recorded xi=1 but byte-RED at r=%d '
                 '<-- OPEN-2a COUNTER-INSTANCE (recorded form)' % r)
        # OA-SIGMA mechanism law (both sign variants recorded)
        if M >= 2:
            okA = all(deltas[j] ==
                      F.mul(rho[j], F.inv(sigma_twist(T, M, rho[j])))
                      for j in supp)
            okB = all(deltas[j] ==
                      F.mul(sigma_twist(T, M, rho[j]), F.inv(rho[j]))
                      for j in supp)
            row['sigma_law_A'] = okA          # delta = rho / sigma'(rho)
            row['sigma_law_B'] = okB          # delta = sigma'(rho) / rho
            if M == 2 and gaps == 0:
                note('OA-SIGMA')
                if not (okA or okB):
                    viol('OA-SIGMA', tag,
                         'sigma law fails on gap-free M=2 row r=%d' % r)
            else:
                note('OA-SIGMA-EXPL')
        # OA-SPUR + OA-SPURGEO
        if row['byte_equal']:
            d = 0
            pts = sorted(set(supp + [fm]))
            for i in range(len(pts)):
                for j2 in range(i+1, len(pts)):
                    d = gcd(d, pts[j2] - pts[i])
            first_tor = None
            for xi in F.elems():
                if F.is_zero(xi):
                    continue
                if ITL.fpow(F, xi, d) == F.one():
                    first_tor = xi
                    break
            geo_spur = (first_tor is not None and first_tor != F.one())
            spur = (not rec_triv)
            row['spurious'] = spur
            row['spur_d'] = d
            note('OA-SPURGEO')
            if spur != geo_spur:
                viol('OA-SPURGEO', tag, 'selection geography law fails at '
                     'r=%d (spur=%s geo=%s d=%d)' % (r, spur, geo_spur, d))
            if spur:
                note('OA-SPUR-ROW')
        ROWS.append(row)

# ------------------------------------------------------- battery generation
def k_chain(spec):
    """build the chamber tower for spec (all reads), return it."""
    return build_tower_x(spec)

def enum_psi_cands(K, degs, mode):
    """candidate monic moduli over field K as RAW coefficient lists.
    mode: 'full' (deg-1 all units, deg-2 all irreducible), 'sample'
    (deg-1 all units, deg-2 12-sample), plus optional deg-3 / deg-4
    entries per degs flags."""
    els = list(K.elems())
    units = [x for x in els if not K.is_zero(x)]
    out = []
    if 1 in degs:
        for c in units:
            out.append([('RAW', c), ('RAW', K.one())])
    if 2 in degs:
        cands = []
        for c0 in units:
            for c1 in els:
                cand = [c0, c1, K.one()]
                if poly_irr(K, cand):
                    cands.append(cand)
        if mode == 'sample':
            cands = cands[::max(1, len(cands)//12)][:12]
        out += [[('RAW', c) for c in cand] for cand in cands]
    if 3 in degs:
        # sparse + trinomial sample: y^3+c and y^3+by+c
        cands = []
        for c0 in units:
            cand = [c0, K.zero(), K.zero(), K.one()]
            if poly_irr(K, cand):
                cands.append(cand)
        tri = 0
        for c0 in units:
            for b in units[:2]:
                cand = [c0, b, K.zero(), K.one()]
                if poly_irr(K, cand):
                    cands.append(cand); tri += 1
                if tri >= 8:
                    break
            if tri >= 8:
                break
        out += [[('RAW', c) for c in cand] for cand in cands]
    if 4 in degs:
        for c0 in units:
            cand = [c0, K.zero(), K.zero(), K.zero(), K.one()]
            if poly_irr(K, cand):
                out.append([('RAW', c) for c in cand])
    return out

def gen_battery():
    """(spec, genre) list; deterministic order."""
    out = []
    for s in GWP.TOWERS:
        out.append((dict(s), 'ROSTER'))
    # ---- B1: F9 invisible-twist chamber
    ch = dict(id='B1CH', ring='Zp', p=3, d0=1, Phi0=[0, 1],
              reads=[(2, 1, 1), (3, 1, 2)], psi=[[1, 1], [1, 0, 1]])
    T = k_chain(ch)
    K2 = T.K[2]
    for (e2, h2) in [(1, 1), (2, 1), (3, 1), (3, 2), (2, 3)]:
        wrap_active = (e2, h2) in [(2, 1), (3, 2)]
        degs = {1, 2} if wrap_active else {1, 2}
        mode = 'full' if wrap_active else 'sample'
        cands = enum_psi_cands(K2, degs, mode)
        if (e2, h2) in [(1, 1), (2, 1)]:
            cands += enum_psi_cands(K2, {3}, 'sample')
        if (e2, h2) in [(1, 1), (2, 1)]:
            cands += enum_psi_cands(K2, {4}, 'sample')
        for i, cand in enumerate(cands):
            g2 = len(cand) - 1
            if e2*g2 > 8:
                continue
            out.append((dict(id='B1-%d%d-%02d' % (e2, h2, i), ring='Zp',
                             p=3, d0=1, Phi0=[0, 1],
                             reads=[(2, 1, 1), (3, 1, 2), (e2, h2, g2)],
                             psi=[[1, 1], [1, 0, 1], cand]), 'B1'))
    # ---- B1f: flat (wrap-dead) control
    chf = dict(id='B1FCH', ring='Zp', p=3, d0=1, Phi0=[0, 1],
               reads=[(2, 1, 1), (1, 1, 2)], psi=[[1, 1], [1, 0, 1]])
    Tf = k_chain(chf)
    K2f = Tf.K[2]
    for (e2, h2) in [(2, 1), (3, 1)]:
        for i, cand in enumerate(enum_psi_cands(K2f, {1, 2}, 'sample')):
            g2 = len(cand) - 1
            out.append((dict(id='B1F-%d%d-%02d' % (e2, h2, i), ring='Zp',
                             p=3, d0=1, Phi0=[0, 1],
                             reads=[(2, 1, 1), (1, 1, 2), (e2, h2, g2)],
                             psi=[[1, 1], [1, 0, 1], cand]), 'B1F'))
    # ---- B4: (C-coll) control (A1 = 0)
    chc = dict(id='B4CH', ring='Zp', p=3, d0=1, Phi0=[0, 1],
               reads=[(1, 1, 1), (3, 1, 2)], psi=[[1, 1], [1, 0, 1]])
    Tc = k_chain(chc)
    K2c = Tc.K[2]
    for (e2, h2) in [(2, 1), (3, 2)]:
        for i, cand in enumerate(enum_psi_cands(K2c, {1, 2}, 'sample')):
            g2 = len(cand) - 1
            out.append((dict(id='B4-%d%d-%02d' % (e2, h2, i), ring='Zp',
                             p=3, d0=1, Phi0=[0, 1],
                             reads=[(1, 1, 1), (3, 1, 2), (e2, h2, g2)],
                             psi=[[1, 1], [1, 0, 1], cand]), 'B4'))
    # ---- B2: F64 chamber (PE3 genre one level up)
    ch64 = dict(id='B2CH', ring='Zp', p=2, d0=1, Phi0=[0, 1],
                reads=[(2, 1, 2), (2, 1, 3)],
                psi=[[1, 1, 1], [('z', 1, 1), 0, 0, 1]])
    T64 = k_chain(ch64)
    K64 = T64.K[2]
    z2 = T64.z[2]
    zeta = T64.embed(T64.z[1], 1, 2)
    picks1 = []
    x = K64.one()
    for k in range(6):
        picks1.append(x)
        x = K64.mul(x, z2)
    picks1.append(K64.mul(zeta, z2))
    picks1.append(K64.mul(zeta, K64.mul(z2, z2)))
    for (e2, h2) in [(1, 1), (2, 1), (3, 1)]:
        cands = [[('RAW', c), ('RAW', K64.one())] for c in picks1]
        if (e2, h2) != (3, 1):
            q2 = []
            for c in picks1[:4]:
                cand = [c, K64.zero(), K64.one()]
                if poly_irr(K64, cand):
                    q2.append(cand)
                cand = [c, z2, K64.one()]
                if poly_irr(K64, cand):
                    q2.append(cand)
            cands += [[('RAW', cc) for cc in cand] for cand in q2]
        if (e2, h2) in [(1, 1), (2, 1)]:
            c3 = []
            for c in picks1[:6]:
                cand = [c, K64.zero(), K64.zero(), K64.one()]
                if poly_irr(K64, cand):
                    c3.append(cand)
            cands += [[('RAW', cc) for cc in cand] for cand in c3]
        for i, cand in enumerate(cands):
            g2 = len(cand) - 1
            if e2*g2 > 6:
                continue
            out.append((dict(id='B2-%d%d-%02d' % (e2, h2, i), ring='Zp',
                             p=2, d0=1, Phi0=[0, 1],
                             reads=[(2, 1, 2), (2, 1, 3), (e2, h2, g2)],
                             psi=[[1, 1, 1], [('z', 1, 1), 0, 0, 1], cand]),
                        'B2'))
    # ---- B3: stacked M=3 (the I4A/I4B r=5 geography + a doubly-twisted B1)
    chI4B = dict(id='I4BCH', ring='Zp', p=3, d0=1, Phi0=[0, 1],
                 reads=[(3, 2, 1), (2, 1, 1), (1, 1, 2)],
                 psi=[[1, 1], [1, 1], [1, 0, 1]])
    TI = k_chain(chI4B)
    K3I = TI.K[3]
    for (e3, h3) in [(2, 1), (1, 1), (3, 1), (1, 2)]:
        for i, cand in enumerate(enum_psi_cands(K3I, {1}, 'full')
                                 + enum_psi_cands(K3I, {2}, 'sample')[:6]):
            g3 = len(cand) - 1
            if e3*g3 > 4:
                continue
            out.append((dict(id='B3B-%d%d-%02d' % (e3, h3, i), ring='Zp',
                             p=3, d0=1, Phi0=[0, 1],
                             reads=[(3, 2, 1), (2, 1, 1), (1, 1, 2),
                                    (e3, h3, g3)],
                             psi=[[1, 1], [1, 1], [1, 0, 1], cand]), 'B3B'))
    chI4A = dict(id='I4ACH', ring='Zp', p=2, d0=1, Phi0=[0, 1],
                 reads=[(2, 1, 1), (2, 1, 1), (1, 1, 2)],
                 psi=[[1, 1], [1, 1], [1, 1, 1]])
    TA = k_chain(chI4A)
    K3A = TA.K[3]
    for (e3, h3) in [(3, 2), (2, 1), (1, 1)]:
        for i, cand in enumerate(enum_psi_cands(K3A, {1}, 'full')
                                 + enum_psi_cands(K3A, {2}, 'sample')[:4]):
            g3 = len(cand) - 1
            if e3*g3 > 4:
                continue
            out.append((dict(id='B3A-%d%d-%02d' % (e3, h3, i), ring='Zp',
                             p=2, d0=1, Phi0=[0, 1],
                             reads=[(2, 1, 1), (2, 1, 1), (1, 1, 2),
                                    (e3, h3, g3)],
                             psi=[[1, 1], [1, 1], [1, 1, 1], cand]), 'B3A'))
    # doubly-twisted stack over the B1 chamber (psi2 = y + z2 byte-equal)
    chD = dict(id='B3DCH', ring='Zp', p=3, d0=1, Phi0=[0, 1],
               reads=[(2, 1, 1), (3, 1, 2), (2, 1, 1)],
               psi=[[1, 1], [1, 0, 1], [('z', 2, 1), 1]])
    TD = k_chain(chD)
    K3D = TD.K[3]
    for (e3, h3) in [(1, 1), (2, 1), (3, 1)]:
        for i, cand in enumerate(enum_psi_cands(K3D, {1}, 'full')[:6]
                                 + enum_psi_cands(K3D, {2}, 'sample')[:4]):
            g3 = len(cand) - 1
            if e3*g3 > 3:
                continue
            out.append((dict(id='B3D-%d%d-%02d' % (e3, h3, i), ring='Zp',
                             p=3, d0=1, Phi0=[0, 1],
                             reads=[(2, 1, 1), (3, 1, 2), (2, 1, 1),
                                    (e3, h3, g3)],
                             psi=[[1, 1], [1, 0, 1], [('z', 2, 1), 1],
                                  cand]), 'B3D'))
    return out

# ------------------------------------------------------------------ teeth
def run_teeth():
    """TEETH-1: print leg garbled (mut_droptwist) on T2C+T3C.
    TEETH-2: harness eps garbled (MutHTower) on T2A+T2B.
    A tooth is CAUGHT if the analysis raises >= 1 violation or hard-fails."""
    global VIOL
    teeth = {}
    for tid in ('T2C', 'T3C'):
        spec = next(s for s in GWP.TOWERS if s['id'] == tid)
        tag = 'TOOTH1/%s' % tid
        saved = VIOL
        VIOL = []
        try:
            T = build_tower_x(spec)
            G = GWP.gmn_from_tower(T, mut=True)
            analyze_tower(T, G, tag, 'TOOTH1')
            caught = len(VIOL)
        except (AssertionError, ZeroDivisionError, KeyError) as ex:
            caught = 1
        # drop teeth rows from the main table
        while ROWS and ROWS[-1]['tag'] == tag:
            ROWS.pop()
        VIOL = saved
        teeth[tag] = caught
        note('TEETH-1')
        if caught == 0:
            viol('TEETH-1', tag, 'garbled print leg NOT caught')
    for tid in ('T2A', 'T2B'):
        spec = next(s for s in GWP.TOWERS if s['id'] == tid)
        tag = 'TOOTH2/%s' % tid
        saved = VIOL
        VIOL = []
        try:
            R = ITL.Zp(spec['p']) if spec['ring'] == 'Zp' \
                else ITL.Fpt(spec['p'])
            name = '%s,p=%d,%s/mutH' % (spec['ring'], spec['p'], spec['id'])
            T = GWP.MutHTower(name, R, spec['d0'], spec['Phi0'],
                              spec['reads'], list(spec['psi']))
            G = GWP.gmn_from_tower(T)
            analyze_tower(T, G, tag, 'TOOTH2')
            caught = len(VIOL)
        except (AssertionError, ZeroDivisionError, KeyError) as ex:
            caught = 1
        while ROWS and ROWS[-1]['tag'] == tag:
            ROWS.pop()
        VIOL = saved
        teeth[tag] = caught
        note('TEETH-2')
        if caught == 0:
            viol('TEETH-2', tag, 'garbled harness eps NOT caught')
    RES['teeth'] = teeth

# ------------------------------------------------------------------- main
FAMS = [
    ('OA-ADM',     'vok+onesided at shared-below junctions',       '0'),
    ('OA-PHIR',    'rres(phi^cls) = c*psi (Thm-phir)',              '0'),
    ('OA-TOPRES',  'top rres slot of Phi^har = c',                  '0'),
    ('OA-RHOBYTE', 'byte-equal <=> rho == 1',                       '0'),
    ('OA-BWD',     'byte-equal ==> STRICT',                         '0'),
    ('OA-GAUGE',   'theta-trivial rows: delta == 1',                '0'),
    ('OA-XI',      'theta-trivial rows: Sec 3.4 pair satisfies',    '0'),
    ('OA-FWD-M1',  'm=1 STRICT ==> byte-equal (W2-ID1 strict)',     '0'),
    ('OA-FWD-M2',  'm=2 STRICT ==> byte-equal  [THE QUESTION]',     '?'),
    ('OA-FWD-M3',  'm=3 STRICT ==> byte-equal  [THE QUESTION]',     '?'),
    ('OA-FWD-REC', 'recorded xi=1 ==> byte-equal (box premise)',    '?'),
    ('OA-SIGMA',   'gap-free M=2: delta = rho^{1-sigma} (a sign)',  '0'),
    ('OA-SPURGEO', 'spurious <=> d-torsion precedes 1 in enum',     '0'),
    ('TEETH-1',    'garbled print leg caught on both rows',         '0'),
    ('TEETH-2',    'garbled harness eps caught on both rows',       '0'),
]

def main(argv):
    smoke = '--smoke' in argv
    t0 = time.time()
    lines = []

    def emit(s=''):
        print(s)
        lines.append(s)

    emit('open2attack_checks -- W2-OPEN-2 ATTACK battery (m >= 2 junction '
         'identification)')
    emit('engine: iterlawn_pe_reimpl (committed, verbatim) + TowerX '
         '(disclosed general-g init)')
    emit('classifier: grt_weld_probe.GmnLeg (sealed transcription, verbatim)')
    emit('junction helpers: grt_w2_checks orbit_scan/actual_ratios/'
         'junction_data (sealed, verbatim)')
    emit('mode: %s' % ('SMOKE' if smoke else 'FULL'))
    emit()
    battery = gen_battery()
    if smoke:
        keep = [i for i, (s, g) in enumerate(battery)
                if s.get('id') in ('T2A', 'T2C', 'I4B')
                or (g == 'B1' and i % 40 == 0)
                or (g == 'B2' and i % 30 == 0)
                or (g == 'B3B' and i % 20 == 0)]
        battery = [battery[i] for i in keep]
    emit('battery: %d tower specs' % len(battery))
    built = 0
    rejects = 0
    for spec, genre in battery:
        tag = '%s,p=%d,%s' % (spec['ring'], spec['p'], spec['id'])
        try:
            T = build_tower_x(spec)
            G = GWP.gmn_from_tower(T)
        except AssertionError as ex:
            rejects += 1
            continue
        built += 1
        analyze_tower(T, G, tag, genre)
        if built % 50 == 0:
            emit('  [%6.1fs] %d towers analyzed...' % (time.time()-t0, built))
    emit('  built %d towers (%d spec rejects), %d junction rows'
         % (built, rejects, len(ROWS)))
    run_teeth()
    emit()
    # ---------------- census
    cens = collections.defaultdict(int)
    for row in ROWS:
        if row.get('status') == 'SKIP':
            cens['skip'] += 1
            continue
        if 'strict' not in row:
            cens['degenerate'] += 1
            continue
        M = row['M']
        key = 'M%d' % min(M, 3)
        cens['walked_' + key] += 1
        if row['strict']:
            cens['strict_' + key] += 1
        if row['byte_equal']:
            cens['byte_eq_' + key] += 1
        if row['strict'] and row['byte_equal']:
            cens['strict_and_byte_' + key] += 1
        if row['strict'] and not row['byte_equal']:
            cens['STRICT_BYTE_RED_' + key] += 1
        if row.get('recorded_trivial') and not row['byte_equal']:
            cens['RECTRIV_BYTE_RED_' + key] += 1
        if row['delta_nontriv']:
            cens['delta_nontriv_' + key] += 1
        if row.get('defeat_slots'):
            cens['partial_defeat_rows_' + key] += 1
        if row.get('spurious'):
            cens['spurious_' + key] += 1
        if M >= 2:
            if row.get('sigma_law_A'):
                cens['sigmaA_' + key] += 1
            if row.get('sigma_law_B'):
                cens['sigmaB_' + key] += 1
            if row.get('gaps'):
                cens['gap_rows_' + key] += 1
    RES['censuses'] = dict(cens)
    emit('censuses: %s' % json.dumps(dict(sorted(cens.items())), indent=1))
    emit()
    emit('=' * 78)
    emit('PREREGISTERED vs OBSERVED (violations; samples in parens; '
         "'?' = THE QUESTION, no confident preregistration)")
    emit('=' * 78)
    hard_fail = False
    for fam, desc, pred in FAMS:
        obs = sum(1 for v in VIOL if v[0] == fam)
        nsm = COUNTS.get(fam, 0)
        if pred == '0' and obs > 0:
            hard_fail = True
            verdict = 'RED'
        elif pred == '?':
            verdict = 'FINDING' if obs > 0 else 'GREEN'
        else:
            verdict = 'GREEN'
        emit('%-11s %-48s pred %-2s obs %4d (%5d)  %s'
             % (fam, desc, pred, obs, nsm, verdict))
    spurn = COUNTS.get('OA-SPUR-ROW', 0)
    emit('-' * 78)
    emit('OA-SPUR census rows (byte-equal & recorded xi != 1, PREDICT >= 1 '
         'at m >= 2): %d' % spurn)
    if VIOL:
        emit('%d VIOLATIONS/FINDINGS (first 60):' % len(VIOL))
        for v in VIOL[:60]:
            emit('   %s' % (v,))
    RES['families'] = {fam: {'obs': sum(1 for v in VIOL if v[0] == fam),
                             'samples': COUNTS.get(fam, 0), 'pred': pred}
                       for fam, desc, pred in FAMS}
    RES['violations'] = [list(v) for v in VIOL]
    RES['spur_rows'] = spurn
    RES['rows'] = ROWS
    RES['elapsed_s'] = round(time.time() - t0, 1)
    RES['mode'] = 'smoke' if smoke else 'full'
    here = os.path.dirname(os.path.abspath(__file__))
    if not smoke:
        with open(os.path.join(here, 'open2attack_results.json'), 'w') as fh:
            json.dump(RES, fh, indent=1, default=repr)
        with open(os.path.join(here, 'open2attack_output.txt'), 'w') as fh:
            fh.write('\n'.join(lines) + '\n')
    emit()
    q_findings = sum(1 for v in VIOL if v[0] in
                     ('OA-FWD-M2', 'OA-FWD-M3', 'OA-FWD-REC'))
    emit('OPEN-2a ATTACK VERDICT:')
    emit('  preregistered-0 families: %s' % ('ALL GREEN' if not hard_fail
                                             else 'RED (runner-level)'))
    emit('  THE QUESTION (m>=2 strict/recorded ==> byte-equal): %s'
         % ('0 violations on %d m>=2 walked rows -- identification HOLDS '
            'on the battery' % (cens.get('walked_M2', 0)
                                + cens.get('walked_M3', 0))
            if q_findings == 0 else
            '%d COUNTER-INSTANCE ROWS FOUND (see violations)' % q_findings))
    emit('  elapsed %.1fs   total samples %d' % (time.time()-t0,
                                                 sum(COUNTS.values())))
    return 0 if not hard_fail else 1

if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
