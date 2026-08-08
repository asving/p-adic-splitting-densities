#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
sigmalaw_checks.py -- SIGMALAW unit machine leg
(lean/notes/openmath/SIGMALAW_PROOF_2026-08-08.md).

TARGET.  THE Sigma-LAW (OPEN2ATTACK Sec 6 box), proved in the note in the
per-coordinate ledger form and machine-keyed here:

    (Sigma-LEDGER)  Prnt_j(A) = u_j * Sigma_m( R_m v(A) )
        for BOTH builders' slot digits A in {C_j, P_j} at every
        shared-below junction at level m+1, every m >= 1, where
        u_j = z_m^{-k_j A_m} * eps_m(beta_j) * U_m(beta_j)      (closed form)
        U_1 = 1;  U_m(beta) = z_{m-1}^{-s(beta) A_{m-1}} * chi_{m-1}^{-w0(beta)}
        s(beta) = l_{m-1} beta mod e_{m-1}, w0(beta) = (beta - s gamma_m)/e_{m-1}
    (DELTA law)     delta_j = rho_j / Sigma_m(rho_j)
    Sigma_m = the xi-FORMULA composite twist: Sigma_1 = id,
        Sigma_q(sum y_nu z_q^nu) = sum Sigma_{q-1}(y_nu) xi_q^nu z_q^nu,
        xi_q = chi_{q-1}^{gamma_q} z_{q-1}^{-e_{q-1} A_{q-1}}  (GRTW2 Sec 3.4)
    -- NOT the bare interior twist theta_q = z_{q-1}^{A_{q-1}e_{q-1}} of
    open2attack_checks.sigma_twist: at q = 2 the letters are INVERSE, at
    q >= 3 the chi-chain correction chi_{q-1}^{gamma_q} enters.  Both boxed
    variants rho^{1 -/+ sigma'} are FALSE in general; the separator
    families below witness this by construction.

ENGINE/HELPERS (verbatim imports, never edited): iterlawn_pe_reimpl (Tower,
fields, eq12); open2attack_checks (TowerX general-psi tower, gap_scan,
sigma_twist [as the REFUTED comparison map], enum helpers); grt_weld_probe
(GmnLeg classifier, gmn_from_tower, top_lift); grt_w2_checks
(actual_ratios).  Fresh code: chi/xi ledgers, Sigma, u_j, families, teeth.

BATTERY (deterministic):
  OA   the FULL OPEN2ATTACK battery reproduced (gen_battery(): roster 16
       towers + B1/B1F/B4/B2/B3A/B3B/B3D) -- every walked shared-below
       junction, m = 1..3.
  SEPA m=2 separator genre: Z3, (2,1,2)+(e1,h1,4), psi0 = y^2+y+2 (z1
       primitive ord 8), psi1 = y^4+z1^k (supp {0,4}: xi_2 = z1^{-2e1}
       ORDER 4, support-invisible => m=1 junction byte-equal), top moduli
       with NON-MONOMIAL K2 coefficients (1+z2 etc.) -- both z2-parities
       in the read defeat the W2-L2 parity collapse and separate the maps.
  SEPB m=3 separator genre: Z3, (2,1,1)+(2,1,2)+(2,1,2) with psi2 = y^2+c,
       c a nonsquare of F9: chi_2 = -1, gamma_3 odd => xi_3 = -z2^{-e2 A2}
       while z2^{e2 A2} = 1 -- the chi-chain correction is the WHOLE map;
       psi3 non-monomial over K3 = F81.

CHECK FAMILIES (preregistered):
  SL-VDM     (Sigma-LEDGER) with closed-form u_j, both legs   PREDICT 0
  SL-DELTA   delta_j = rho_j / Sigma_m(rho_j)                 PREDICT 0
  SL-GAP     SL-VDM/SL-DELTA on gap slots (gap_scan > 0)      PREDICT 0
             (census expected > 100 gap slots)
  SL-PHIR    Prnt_j(P_j) = c psi_j (Thm-phir leg)             PREDICT 0
  SL-SEP2    census m=2: Sigma(rho) != sigma_twist(rho) and BOTH bare-theta
             variants fail while SL-DELTA holds               PREDICT >= 8
  SL-SEP3    same at m=3 (chi-correction live)                PREDICT >= 6
  SL-INVREC  census: OA-battery delta!=1 rows where Sigma(rho) ==
             sigma_twist(rho) (the involution reconciliation -- explains
             the sealed unit's 0-violation record)            PREDICT = all
  TEETH-US   u_j garbled (U_m := 1) on designated towers      caught both
  TEETH-SB   Sigma garbled (bare-theta forward composite = the boxed
             candidate law) on designated separator towers    caught both
  TEETH-PR   print leg garbled (mut_droptwist) on T2C + T3C   caught both

SMOKE DISCLOSURE: four throwaway pre-note scripts (/tmp/sl_smoke.py,
/tmp/sl_hunt*.py, disclosed in the note Sec 6) validated the derivation
(66 ledger + 33 delta checks, 0 bad; incl. 24 gap slots) and FOUND the
separator genres (8 SEP-A + 6 SEP-B rows) after two non-separating hunts
(monomial genres: the parity-collapse observation).  The runner's --smoke
re-runs a subset + teeth.  The full battery is UNRUN at commit 1.

Outputs: sigmalaw_output.txt, sigmalaw_results.json.
"""
import sys, os, json, time, collections

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import iterlawn_pe_reimpl as ITL
import grt_weld_probe as GWP
import grt_w2_checks as W2
import open2attack_checks as OA

VIOL = []
COUNTS = collections.defaultdict(int)
ROWS = []
RES = {'rows': None, 'families': {}, 'teeth': {}, 'censuses': {}}

def note(fam, n=1):
    COUNTS[fam] += n

def viol(fam, tag, msg):
    VIOL.append((fam, tag, str(msg)))

# ---------------------------------------------------------- ledger objects
def chi_chain(T, M):
    """chi[m] in K[m-1], m = 1..M (the Sec 3.4 recursion; fresh)."""
    chi = {1: T.K[0].one()}
    for m in range(2, M+1):
        Km1 = T.K[m-1]
        Wm1 = T.e[m-2]*T.g[m-2]*T.gam[m-1]          # w_{m-1}Phi_{m-1}
        expo = T.lp[m-1] - T.l[m-1]*Wm1
        prev = T.embed(chi[m-1], m-2, m-1)
        A = T.l[m-2]*T.g[m-2]*T.gam[m-1]            # A_{m-1}
        chi[m] = Km1.mul(ITL.fpow(Km1, prev, expo),
                         ITL.fpow(Km1, T.z[m-1], A*T.l[m-1]))
    return chi

def xi_ledger(T, M):
    """(chi, xi): xi[q] in K[q-1], q = 2..M -- the formula characters."""
    chi = chi_chain(T, M)
    xi = {}
    for q in range(2, M+1):
        Kq1 = T.K[q-1]
        cprev = T.embed(chi[q-1], q-2, q-1)
        A = T.l[q-2]*T.g[q-2]*T.gam[q-1]            # A_{q-1}
        xi[q] = Kq1.mul(ITL.fpow(Kq1, cprev, T.gam[q]),
                        ITL.fpow(Kq1, T.z[q-1], -T.e[q-1]*A))
    return chi, xi

def Sigma(T, M, xi, x):
    """the xi-composite coordinate twist on K_M (Sigma-DEF; fresh)."""
    def rec(q, y):
        if q <= 1:
            return y
        K = T.K[q]; Km1 = T.K[q-1]
        out = K.zero()
        for i, yi in enumerate(y):
            yi2 = rec(q-1, yi)
            yi2 = Km1.mul(yi2, ITL.fpow(Km1, xi[q], i))
            out = K.add(out, K.mul(K.from_base(yi2), ITL.fpow(K, T.z[q], i)))
        return out
    return rec(M, x)

def u_slot(T, M, chi, j, mut_dropU=False):
    """the closed-form slot constant u_j in K_M (note Sec 3)."""
    F = T.K[M]
    kj = j*T.e[M]
    bj = (T.g[M] - j)*T.gam[M+1]
    AM = T.l[M-1]*T.g[M-1]*T.gam[M]                 # A_M
    epsm = T.eps(M, bj)
    if M >= 2 and not mut_dropU:
        s = (T.l[M-1]*bj) % T.e[M-1]
        w0 = (bj - s*T.gam[M])//T.e[M-1]
        Am1 = T.l[M-2]*T.g[M-2]*T.gam[M-1]          # A_{M-1}
        Km1 = T.K[M-1]
        U = Km1.mul(ITL.fpow(Km1, T.z[M-1], -s*Am1),
                    ITL.fpow(Km1, T.embed(chi[M-1], M-2, M-1), -w0))
        U = T.embed(U, M-1, M)
    else:
        U = F.one()
    return F.mul(ITL.fpow(F, T.z[M], -kj*AM), F.mul(epsm, U))

# --------------------------------------------------------- junction analysis
def analyze_tower(T, G, tag, genre, mut_dropU=False, mut_bareSigma=False,
                  c_true_leg=None):
    """walk junctions r = 3..NR+1 on the shared-below perimeter; key the
    families.  mut_dropU / mut_bareSigma implement the teeth."""
    for r in range(3, T.NR + 2):
        m = r - 1
        M = r - 2
        har = tuple(T.Phi[m]) if m <= T.n else GWP.top_lift(T)
        cls = tuple(G.phi[r])
        shared = all(tuple(G.phi[q]) == tuple(T.Phi[q-1])
                     for q in range(2, r))
        row = {'tag': tag, 'genre': genre, 'r': r, 'M': M,
               'shared_below': shared, 'byte_equal': har == cls}
        if not shared:
            row['status'] = 'SKIP'
            note('SL-SKIP')
            ROWS.append(row)
            continue
        F = T.K[M]
        fm = T.g[M]
        psi = T.psi[M]
        Gc = c_true_leg if c_true_leg is not None else G
        c = Gc.thm_c(r)
        try:
            Rl = G.rres(r-1, list(har))
            Rc = G.rres(r-1, list(cls))
        except AssertionError as ex:
            note('SL-VDM')
            viol('SL-VDM', tag, 'rres hard-fails at r=%d: %s' % (r, ex))
            row['status'] = 'RRES-FAIL'
            ROWS.append(row)
            continue
        act = W2.actual_ratios(T, G, r)
        if isinstance(act, tuple):
            row['status'] = 'SPLIT(%s@%d)' % act
            note('SL-SPLIT')
            ROWS.append(row)
            continue
        supp = [j for j in range(fm) if not F.is_zero(psi[j])]
        row['supp'] = supp
        chi, xi = xi_ledger(T, M)
        dvh = T.P.dev(list(har), T.Phi[M])
        dvc = T.P.dev(list(cls), T.Phi[M])
        sep_row = False
        gap_slots = 0
        for j in supp:
            kj = j*T.e[M]
            bj = (fm - j)*T.gam[M+1]
            uj = u_slot(T, M, chi, j, mut_dropU=mut_dropU)
            gap_h = OA.gap_scan(T, M, list(dvh[kj]), bj) \
                if kj < len(dvh) and dvh[kj] else 0
            gap_c = OA.gap_scan(T, M, list(dvc[kj]), bj) \
                if kj < len(dvc) and dvc[kj] else 0
            gappy = (gap_h + gap_c) > 0
            if gappy:
                gap_slots += 1
            # SL-VDM: both legs
            for (dv, Rx, who) in ((dvh, Rl, 'har'), (dvc, Rc, 'cls')):
                A = dv[kj] if kj < len(dv) else ()
                if not A:
                    continue
                H = T.read(M, bj, A)
                sig = OA.sigma_twist(T, M, H) if mut_bareSigma \
                    else Sigma(T, M, xi, H)
                note('SL-VDM')
                if gappy:
                    note('SL-GAP')
                ok = (Rx[j] == F.mul(uj, sig))
                if not ok:
                    viol('SL-VDM', tag, 'ledger identity fails r=%d j=%d %s'
                         '(gaps h%d c%d)' % (r, j, who, gap_h, gap_c))
                    if gappy:
                        viol('SL-GAP', tag, 'gap-slot ledger fails r=%d j=%d'
                             % (r, j))
            # SL-PHIR
            note('SL-PHIR')
            if Rc[j] != F.mul(c, psi[j]):
                viol('SL-PHIR', tag, 'Thm-phir slot fails r=%d j=%d' % (r, j))
            # SL-DELTA (+ separator censuses)
            rho = act[j]
            delta = F.mul(F.mul(Rl[j], rho), F.inv(F.mul(c, psi[j])))
            sig_rho = OA.sigma_twist(T, M, rho) if mut_bareSigma \
                else Sigma(T, M, xi, rho)
            note('SL-DELTA')
            mine = (delta == F.mul(rho, F.inv(sig_rho)))
            if not mine:
                viol('SL-DELTA', tag, 'delta law fails r=%d j=%d' % (r, j))
                if gappy:
                    viol('SL-GAP', tag, 'gap-slot delta fails r=%d j=%d'
                         % (r, j))
            if not (mut_dropU or mut_bareSigma):
                sigA = OA.sigma_twist(T, M, rho)
                runA = (delta == F.mul(rho, F.inv(sigA)))
                runB = (delta == F.mul(sigA, F.inv(rho)))
                if M >= 2 and Sigma(T, M, xi, rho) != sigA:
                    if mine and not runA and not runB:
                        sep_row = True
                        note('SL-SEP%d-ROW' % min(M, 3))
                if delta != F.one() and sigA == Sigma(T, M, xi, rho):
                    note('SL-INVREC-ROW')
                    if genre.startswith(('ROSTER', 'B')):
                        note('SL-INVREC-OA')
        row['gap_slots'] = gap_slots
        row['separator'] = sep_row
        ROWS.append(row)

# ------------------------------------------------------------ battery gen
def gen_sepA():
    """m=2 separator genre (capped deterministic sweep)."""
    out = []
    base = dict(ring='Zp', p=3, d0=1, Phi0=[0, 1])
    n = 0
    for e1h1 in [(3, 1), (1, 1)]:
        for k in (1, 3, 5):
            ch = dict(base, id='SEPACH', reads=[(2, 1, 2), e1h1 + (4,)],
                      psi=[[2, 1, 1], [('z', 1, k), 0, 0, 0, 1]])
            try:
                T = OA.build_tower_x(ch)
            except AssertionError:
                continue
            K2 = T.K[2]
            z2 = T.z[2]
            z1e = T.embed(T.z[1], 1, 2)
            one = K2.one()
            cands = [K2.add(one, z2), K2.add(one, K2.neg(z2)),
                     K2.add(z1e, z2), K2.add(one, ITL.fpow(K2, z2, 3)),
                     K2.add(z2, ITL.fpow(K2, z2, 2)),
                     K2.add(K2.mul(z1e, z2), one)]
            for read2 in [(1, 1, 1), (2, 1, 1), (3, 1, 1), (1, 2, 1)]:
                for c0 in cands[:4]:
                    n += 1
                    out.append((dict(base, id='SEPA-%03d' % n,
                                     reads=[(2, 1, 2), e1h1 + (4,), read2],
                                     psi=[[2, 1, 1],
                                          [('z', 1, k), 0, 0, 0, 1],
                                          [('RAW', c0), ('RAW', one)]]),
                                'SEPA'))
    return out

def gen_sepB():
    """m=3 separator genre (chi-chain correction; capped sweep)."""
    out = []
    base = dict(ring='Zp', p=3, d0=1, Phi0=[0, 1])
    ch2 = dict(base, id='SEPBCH', reads=[(2, 1, 1), (2, 1, 2)],
               psi=[[1, 1], [1, 0, 1]])
    T2 = OA.build_tower_x(ch2)
    K2 = T2.K[2]
    nsq = []
    for el in K2.elems():
        if K2.is_zero(el):
            continue
        if OA.poly_irr(K2, [el, K2.zero(), K2.one()]):
            nsq.append(el)
    n = 0
    for read2 in [(2, 1, 2), (1, 1, 2)]:
        for c2raw in nsq[:3]:
            ch = dict(base, id='SEPBCH2',
                      reads=[(2, 1, 1), (2, 1, 2), read2],
                      psi=[[1, 1], [1, 0, 1],
                           [('RAW', c2raw), ('RAW', K2.zero()),
                            ('RAW', K2.one())]])
            try:
                T = OA.build_tower_x(ch)
            except AssertionError:
                continue
            K3 = T.K[3]
            z3 = T.z[3]
            z2e = T.embed(T.z[2], 2, 3)
            one3 = K3.one()
            cands = [K3.add(one3, z3), K3.add(one3, K3.neg(z3)),
                     K3.add(z2e, z3), K3.add(one3, K3.mul(z2e, z3))]
            for read3 in [(1, 1, 1), (2, 1, 1), (1, 2, 1)]:
                for c0 in cands[:3]:
                    n += 1
                    out.append((dict(base, id='SEPB-%03d' % n,
                                     reads=[(2, 1, 1), (2, 1, 2), read2,
                                            read3],
                                     psi=[[1, 1], [1, 0, 1],
                                          [('RAW', c2raw),
                                           ('RAW', K2.zero()),
                                           ('RAW', K2.one())],
                                          [('RAW', c0), ('RAW', one3)]]),
                                'SEPB'))
    return out

# ------------------------------------------------------------------- teeth
TEETH_US_DESIG = None      # filled in main from built specs
TEETH_SB_DESIG = None

def run_tooth(spec, genre, fam, **mutkw):
    """run analyze_tower under a mutation; caught = >= 1 violation."""
    global VIOL
    tag = '%s/%s' % (fam, spec['id'])
    saved = VIOL
    VIOL = []
    try:
        T = OA.build_tower_x(spec)
        if mutkw.pop('mut_print', False):
            G = GWP.gmn_from_tower(T, mut=True)
            Gt = GWP.gmn_from_tower(T)
            analyze_tower(T, G, tag, 'TOOTH', c_true_leg=Gt, **mutkw)
        else:
            G = GWP.gmn_from_tower(T)
            analyze_tower(T, G, tag, 'TOOTH', **mutkw)
        caught = len(VIOL)
    except (AssertionError, ZeroDivisionError, KeyError):
        caught = 1
    while ROWS and ROWS[-1]['tag'] == tag:
        ROWS.pop()
    VIOL = saved
    note(fam)
    if caught == 0:
        viol(fam, tag, 'mutation NOT caught')
    return caught

# -------------------------------------------------------------------- main
FAMS = [
    ('SL-VDM',    'ledger identity, closed-form u_j, both legs',   '0'),
    ('SL-DELTA',  'delta = rho / Sigma(rho)',                      '0'),
    ('SL-GAP',    'ledger/delta on gap slots',                     '0'),
    ('SL-PHIR',   'Thm-phir slot reproduction',                    '0'),
    ('TEETH-US',  'u_j garbled (U dropped) caught on both',        '0'),
    ('TEETH-SB',  'Sigma garbled (bare-theta) caught on both',     '0'),
    ('TEETH-PR',  'print leg garbled caught on both',              '0'),
]

def main(argv):
    smoke = '--smoke' in argv
    t0 = time.time()
    lines = []

    def emit(s=''):
        print(s)
        lines.append(s)

    emit('sigmalaw_checks -- THE Sigma-LAW machine leg (ledger identity + '
         'delta law + separators)')
    emit('engine: iterlawn_pe_reimpl + open2attack TowerX/gap_scan '
         '(committed, verbatim)')
    emit('classifier: grt_weld_probe.GmnLeg (sealed, verbatim); ratios: '
         'grt_w2_checks.actual_ratios (sealed, verbatim)')
    emit('comparison map sigma_twist (the REFUTED bare-theta composite): '
         'open2attack_checks (sealed, verbatim)')
    emit('mode: %s' % ('SMOKE' if smoke else 'FULL'))
    emit()
    battery = [(s, g) for (s, g) in OA.gen_battery()]
    sepA = gen_sepA()
    sepB = gen_sepB()
    battery = battery + sepA + sepB
    if smoke:
        keep = [i for i, (s, g) in enumerate(battery)
                if s.get('id') in ('T2A', 'T2C', 'I4B')
                or (g == 'B1' and i % 60 == 0)
                or (g == 'B3D' and i % 10 == 0)
                or s.get('id') in ('SEPA-001', 'SEPB-001')]
        battery = [battery[i] for i in keep]
    emit('battery: %d tower specs (%d SEPA + %d SEPB)'
         % (len(battery), len(sepA), len(sepB)))
    built = 0
    rejects = 0
    first_sepA = None
    first_sepB = None
    for spec, genre in battery:
        tag = '%s,p=%d,%s' % (spec['ring'], spec['p'], spec['id'])
        try:
            T = OA.build_tower_x(spec)
            G = GWP.gmn_from_tower(T)
        except AssertionError:
            rejects += 1
            continue
        built += 1
        analyze_tower(T, G, tag, genre)
        if genre == 'SEPA' and first_sepA is None:
            first_sepA = spec
        if genre == 'SEPB' and first_sepB is None:
            first_sepB = spec
        if built % 100 == 0:
            emit('  [%6.1fs] %d towers analyzed...' % (time.time()-t0, built))
    emit('  built %d towers (%d rejects), %d junction rows'
         % (built, rejects, len(ROWS)))
    # ---- teeth (designated: visibility disclosed in the note's smoke) ----
    b1spec = next((s for (s, g) in battery if g == 'B1'), None)
    for spec in [x for x in (b1spec, first_sepB) if x is not None]:
        run_tooth(spec, 'TOOTH', 'TEETH-US', mut_dropU=True)
    for spec in [x for x in (first_sepA, first_sepB) if x is not None]:
        run_tooth(spec, 'TOOTH', 'TEETH-SB', mut_bareSigma=True)
    for tid in ('T2C', 'T3C'):
        spec = next(s for s in GWP.TOWERS if s['id'] == tid)
        run_tooth(spec, 'TOOTH', 'TEETH-PR', mut_print=True)
    emit()
    # ---- census ----
    cens = collections.defaultdict(int)
    for row in ROWS:
        if row.get('status') == 'SKIP':
            cens['skip'] += 1
            continue
        if 'supp' not in row:
            cens['degenerate'] += 1
            continue
        key = 'M%d' % min(row['M'], 3)
        cens['walked_' + key] += 1
        if row.get('gap_slots'):
            cens['gap_rows_' + key] += 1
            cens['gap_slots_total'] += row['gap_slots']
        if row.get('separator'):
            cens['separator_' + key] += 1
    cens['SEP2_rows'] = COUNTS.get('SL-SEP2-ROW', 0)
    cens['SEP3_rows'] = COUNTS.get('SL-SEP3-ROW', 0)
    cens['INVREC_rows'] = COUNTS.get('SL-INVREC-ROW', 0)
    cens['INVREC_OA_rows'] = COUNTS.get('SL-INVREC-OA', 0)
    RES['censuses'] = dict(cens)
    emit('censuses: %s' % json.dumps(dict(sorted(cens.items())), indent=1))
    emit()
    emit('=' * 78)
    emit('PREREGISTERED vs OBSERVED')
    emit('=' * 78)
    hard_fail = False
    for fam, desc, pred in FAMS:
        obs = sum(1 for v in VIOL if v[0] == fam)
        nsm = COUNTS.get(fam, 0)
        verdict = 'GREEN'
        if obs > 0:
            hard_fail = True
            verdict = 'RED'
        emit('%-9s %-50s pred %-2s obs %4d (%5d)  %s'
             % (fam, desc, pred, obs, nsm, verdict))
    sep2 = COUNTS.get('SL-SEP2-ROW', 0)
    sep3 = COUNTS.get('SL-SEP3-ROW', 0)
    emit('-' * 78)
    emit('SL-SEP2 separator rows (PREDICT >= 8): %d  %s'
         % (sep2, 'GREEN' if sep2 >= 8 else 'RED'))
    emit('SL-SEP3 separator rows (PREDICT >= 6): %d  %s'
         % (sep3, 'GREEN' if sep3 >= 6 else 'RED'))
    if not smoke and (sep2 < 8 or sep3 < 6):
        hard_fail = True
    if VIOL:
        emit('%d VIOLATIONS (first 40):' % len(VIOL))
        for v in VIOL[:40]:
            emit('   %s' % (v,))
    RES['families'] = {fam: {'obs': sum(1 for v in VIOL if v[0] == fam),
                             'samples': COUNTS.get(fam, 0), 'pred': pred}
                       for fam, desc, pred in FAMS}
    RES['violations'] = [list(v) for v in VIOL]
    RES['rows'] = ROWS
    RES['elapsed_s'] = round(time.time() - t0, 1)
    RES['mode'] = 'smoke' if smoke else 'full'
    here = os.path.dirname(os.path.abspath(__file__))
    if not smoke:
        with open(os.path.join(here, 'sigmalaw_results.json'), 'w') as fh:
            json.dump(RES, fh, indent=1, default=repr)
        with open(os.path.join(here, 'sigmalaw_output.txt'), 'w') as fh:
            fh.write('\n'.join(lines) + '\n')
    emit()
    emit('SIGMA-LAW VERDICT: %s' % ('ALL FAMILIES GREEN'
                                    if not hard_fail else 'RED'))
    emit('  elapsed %.1fs   total samples %d' % (time.time()-t0,
                                                 sum(COUNTS.values())))
    return 0 if not hard_fail else 1

if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
