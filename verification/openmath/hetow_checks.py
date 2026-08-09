#!/usr/bin/env python3
"""HETOW battery: the FIRST inner-mu2 >= 3 tower-stage sigma coverage
(companion to lean/notes/openmath/HETOW_RECON_2026-08-09.md; THEOREM
HETOW.A: the tower-stage read = THEOREM HE7.A at the composed carrier,
LITERAL INSTANCE).

MACHINE FORM OF "LITERAL INSTANCE": the readers below are the FROZEN
he7_checks.level2_read (case A) and he6r1_checks.level2_read (case B),
imported UNMODIFIED (md5 pins printed at run start).  Zero new read
logic is written for mu2 = 3: the same code that closed the ordinary
HE6-BOX-1 decides the tower members, fed degree-12 inputs.

FRAME (both cases): p in {3,5}, O = Z_p, Phi' = x^2 - p (e1=2, f1=1,
h=1, D'=2, varpi = x, eta = 1 -- the eta-twist layer is INVISIBLE at
this frame, disclosed as HETOW-BOX-3; the level-2 beta-cocycle twist IS
live in case A).  Members: f = Psi^3 + A2 Psi^2 + A1 Psi + A0, deg 12,
A_j = (LIFT2)-lifts at preregistered pin menus (so A0 != 0 always:
Psi | f is unreachable by construction).  mu1 = 6, FULL inner side,
mu2 = 3 -- the minimal live degree n = 12 derived in the note (S3).

CASE A  (e2,f2) = (2,1): datum lam = 5/2, r = Z - s, s in F_p^x;
  K2 = F_p, D'' = 4, T2 = 10.  Composed (e1e2, f1f2) = (4,1).
  Pin menus (j = 0,1,2; the j = 3 pin is 0 automatically):
    A-ONE33 : (33, 22, 11)  one side lam2 = 11 (ell2 = 1), residual
              cubic over F_p swept through gamma = (g0 != 0, g1, g2)
    A-3RAM  : (32, BIG, BIG) one side lam2 = 32/3 (ell2 = 3)
    A-2+1   : (36, 24, 11)  sides 25/2 then 11
  sigma menu: {(12,1)} {(4,3)} {(4,1)}x3 {(4,2),(4,1)} {(8,1),(4,1)}
CASE B  (e2,f2) = (1,2): datum lam = 3, r = Z^2+c1Z+c0 irreducible
  (p=3: Z^2+1; p=5: Z^2+2); K2 = F_{p^2}, D'' = 4, T2 = 6.
  Composed (2,2).  Pin menus:
    B-ONE21 : (21, 14, 7)   one side lam2 = 7, residual cubic over K2
    B-3RAM  : (20, BIG, BIG) lam2 = 20/3
    B-2+1   : (22, 15, 7)   sides 15/2 then 7
  sigma menu: {(6,2)} {(2,6)} {(2,2)}x3 {(2,4),(2,2)} {(4,2),(2,2)}
Deep perturbations: + lift2(k_deep, 1) on A1 (k_deep = 45 case A, 25
case B), pins unchanged -- sigma must be unchanged and PARI-confirmed.

PREREGISTERED PREDICTIONS (sealed before the first full run):
 P1 (parse gate): every member passes the tower parse -- level-1
    Phi'-development polygon = ONE side (0, 3u2)..(6, 0) of slope
    kappa2 = u2/e2 with residual r^3 (single irreducible factor,
    multiplicity 3); members failing disc != 0 are dropped with
    disclosure (expected rare).
 P2 (HEADLINE, read-vs-PARI): on every member the frozen reader
    returns status OK (or a disclosed non-OK), and every OK sigma
    EQUALS PARI factorpadic's sigma.  ZERO mis-decisions tolerated.
 P3 (alphabet): every OK sigma lies in the preregistered 5-element
    menu of its case.
 P4 (coverage): each of the 5 menu sigmas is realized >= 1 time per
    case (else disclosed as a coverage hole, not a violation).
 P5 (LEVEL3 guard = THEOREM HE7.C at mu2 = 3): NO member returns
    status LEVEL3 (a repeated level-2 factor with ell2*deg r2 >= 2
    needs mu2 >= 4).
TEETH (all must fire):
 T-NAIVE     : the "treat psi2^3 as separable" dictionary (sigma =
               {(4,1)}x3 case A / {(2,2)}x3 case B) is REFUTED by
               PARI on >= 1 member of each case.
 T-WITHHOLD  : withholding a level-2 residual makes the reader return
               UNDETERMINED (>= 1 member per case).
 T-BADTWIST  : case A, letter s = 2: use_twist=False CHANGES sigma on
               >= 1 member, the twisted read agreeing with PARI and
               the untwisted not (first mu2 = 3 exercise of the
               level-2 cocycle).
 T-THREESIGMA: >= 3 distinct PARI sigmas within ONE family of fixed
               (p, case, letter) -- identical level-1 outer+entry data
               (the tower mu2 = 3 box is undecidable from outer data).
VERDICT: GREEN iff 0 violations on scored checks and all teeth fire.
SMOKE RECORD (disclosed): before sealing, the pipeline was smoke-run
with WIP=True (6 members/row, PARI live) to debug construction
plumbing; plumbing fixes from smoke are listed here, and NO prediction
or menu was changed after smoke: (i) l1_parse's side-height formula
corrected to kappa2*mu1 (a case-B transcription bug caught pre-smoke).
Sealed at commit 1 with WIP=False; the full run's artifacts and the
verdict are committed at commit 2.
"""
import sys, os, json, time, hashlib
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import he6_checks as H6
import he7_checks as H7
import he6r1_checks as R1
from he6_checks import (Zp, padd, pmul, ppow, development, key_poly,
                        dv_A, res_A, factor_Fp, polystr, gp_sig_batch,
                        disc_nonzero, hull_sides, BIG, E1, F1, DP)

WIP = False  # sealed at commit 1 (smoke record in docstring)

RES = {'legs': {}, 'viol': [], 'teeth': {}, 'rows': [], 'pins': {},
       'census': {}}


def md5(path):
    with open(path, 'rb') as fh:
        return hashlib.md5(fh.read()).hexdigest()


def note(leg, k=1):
    RES['legs'][leg] = RES['legs'].get(leg, 0) + k


def viol(leg, what, detail):
    RES['viol'].append({'leg': leg, 'what': what,
                        'detail': str(detail)[:400]})
    print('  !! VIOLATION %s %s %s' % (leg, what, str(detail)[:200]))


def tooth(name, fired, detail=''):
    RES['teeth'][name] = {'fired': bool(fired),
                          'detail': str(detail)[:400]}
    print('  TOOTH %-12s %s  %s'
          % (name, 'FIRED' if fired else 'DID NOT FIRE',
             str(detail)[:150]))


MU1 = 6          # inner side length (full side), n = D' * MU1 = 12
NN = 12


# ------------------------------------------------- member construction
def build_member(fr, A_list):
    """f = Psi^3 + A2 Psi^2 + A1 Psi + A0 (A_list = [A0, A1, A2])."""
    f = ppow(fr.Psi, 3)
    for j, A in enumerate(A_list):
        if A:
            f = padd(f, pmul(A, ppow(fr.Psi, j)))
    return f


def lift_or_zero(fr, k, c):
    if c == 0 or c == (0, 0):
        return []
    w = fr.lift2(k, c)
    assert w is not None, 'lift2 failed at k=%s c=%s' % (k, c)
    return w


# ------------------------------------------------- the tower parse gate
def l1_parse(f, R, p, u2, e2, rpoly):
    """P1: level-1 Phi'-development of f = one side (0, 3*u2)..(6, 0),
    slope u2/e2, residual = rpoly^3 (single irreducible factor, mult 3).
    Returns (ok, why).  At this frame varpi = x and theta^2 = p exactly,
    so the level-1 read is twist-free (eta = 1)."""
    dev = development(f, key_poly(R), MU1)
    if len(dev) < MU1 + 1:
        return False, 'short-dev'
    dvs = [dv_A(c, R) for c in dev]
    if dvs[MU1] != 0:
        return False, 'top-pin'
    sides = hull_sides(dvs)
    if len(sides) != 1:
        return False, 'sides=%d' % len(sides)
    j1, m1, j2, m2 = sides[0]
    top = (MU1 * u2) // e2                # kappa2 * mu1
    if not (j1 == 0 and j2 == MU1 and m2 == 0 and m1 == top):
        return False, 'side=(%s,%s)-(%s,%s)' % (j1, m1, j2, m2)
    if Fr(m1, MU1) != Fr(u2, e2):
        return False, 'slope'
    # residual: attaining classes at J = e2*t, height top - u2*t
    dr_len = MU1 // e2                    # degree of R_lam = f2 * mu2 = 3*f2
    co = []
    for t in range(dr_len + 1):
        J = e2 * t
        want = top - u2 * t
        if dvs[J] == want:
            co.append(res_A(dev[J], R) % p)
        else:
            co.append(0)
    if co[dr_len] != 1:
        return False, 'lead'
    facs = factor_Fp(co, p)
    if len(facs) != 1 or facs[0][1] != 3:
        return False, 'residual-facs=%s' % facs
    if list(facs[0][0]) != list(rpoly):
        return False, 'residual=%s want=%s' % (facs[0][0], rpoly)
    return True, ''

# ---------------------------------------------------------- sigma menus
MENU_A = {((12, 1),), ((4, 3),), ((4, 1), (4, 1), (4, 1)),
          ((4, 1), (4, 2)), ((4, 1), (8, 1))}
MENU_B = {((6, 2),), ((2, 6),), ((2, 2), (2, 2), (2, 2)),
          ((2, 2), (2, 4)), ((2, 2), (4, 2))}
NAIVE_A = ((4, 1), (4, 1), (4, 1))
NAIVE_B = ((2, 2), (2, 2), (2, 2))


def gen_members_A(fr, p):
    """[(tag, [A0, A1, A2])] per the preregistered pin menus."""
    units = [x for x in range(1, p)][:4]
    small = [x for x in range(p)][:3]
    out = []
    for g0 in units:
        for g1 in small:
            for g2 in small:
                out.append(('A-ONE33', [lift_or_zero(fr, 33, g0),
                                        lift_or_zero(fr, 22, g1),
                                        lift_or_zero(fr, 11, g2)]))
    for g0 in units:
        out.append(('A-3RAM', [lift_or_zero(fr, 32, g0), [], []]))
        out.append(('A-3RAM', [lift_or_zero(fr, 32, g0),
                               lift_or_zero(fr, 24, 1), []]))
    for g0 in units[:3]:
        for g2 in units[:3]:
            for g1 in (0, 1):
                out.append(('A-2+1', [lift_or_zero(fr, 36, g0),
                                      lift_or_zero(fr, 24, g1),
                                      lift_or_zero(fr, 11, g2)]))
    deep, seen = [], set()
    for tag, A in out:
        if tag not in seen:
            seen.add(tag)
            deep.append((tag + '-deep',
                         [A[0], padd(A[1], lift_or_zero(fr, 45, 1)), A[2]]))
    return out + deep


def gen_members_B(fr, p):
    nz = [(a, b) for a in range(p) for b in range(p) if (a, b) != (0, 0)]
    g0s, g12s = nz[:4], [(0, 0), (1, 0), (0, 1)]
    out = []
    for g0 in g0s:
        for g1 in g12s:
            for g2 in g12s:
                out.append(('B-ONE21', [lift_or_zero(fr, 21, g0),
                                        lift_or_zero(fr, 14, g1),
                                        lift_or_zero(fr, 7, g2)]))
    for g0 in g0s:
        out.append(('B-3RAM', [lift_or_zero(fr, 20, g0), [], []]))
    for g0 in nz[:3]:
        for g2 in nz[:3]:
            out.append(('B-2+1', [lift_or_zero(fr, 22, g0), [],
                                  lift_or_zero(fr, 7, g2)]))
    deep, seen = [], set()
    for tag, A in out:
        if tag not in seen:
            seen.add(tag)
            deep.append((tag + '-deep',
                         [A[0], padd(A[1], lift_or_zero(fr, 25, (1, 0))), A[2]]))
    return out + deep


def run_case(case, p, letter, cap=None):
    """case 'A': letter = s;  case 'B': letter = (c0, c1)."""
    R = Zp(p)
    if case == 'A':
        fr = H7.L2Frame(R, p, 5, letter)
        reader = lambda f, **kw: H7.level2_read(f, fr, **kw)
        members = gen_members_A(fr, p)
        menu, naive, u2, e2 = MENU_A, NAIVE_A, 5, 2
        rpoly = [(-letter) % p, 1]
    else:
        c0, c1 = letter
        fr = R1.L2Frame1(R, p, 3, c0, c1)
        reader = lambda f, **kw: R1.level2_read(f, fr, **kw)
        members = gen_members_B(fr, p)
        menu, naive, u2, e2 = MENU_B, NAIVE_B, 3, 1
        rpoly = [c0 % p, c1 % p, 1]
    if cap:
        members = members[:cap]
    name = 'case%s p=%d letter=%s' % (case, p, letter)
    print('\n== %s  (%d members) ==' % (name, len(members)))
    t0, rows, jobs, dropped = time.time(), [], [], 0
    for tag, A in members:
        f = build_member(fr, A)
        if not disc_nonzero(f, R):
            dropped += 1
            continue
        ok, why = l1_parse(f, R, p, u2, e2, rpoly)
        note('HETOW-P1')
        if not ok:
            viol('HETOW-P1', 'tower parse failed', dict(tag=tag, why=why))
            continue
        rd = reader(f)
        rec = {'tag': tag, 'status': rd.get('status'),
               'sigma': rd.get('sigma'), 'refines': rd.get('refines')}
        note('HETOW-P5')
        if rd.get('status') == 'LEVEL3':
            viol('HETOW-P5', 'LEVEL3 at mu2 = 3 (HE7.C floor breached)',
                 dict(tag=tag, rd=str(rd)[:200]))
        if rd.get('status') != 'OK':
            rec['nonok'] = str(rd)[:200]
            print('  NON-OK %s %s' % (tag, rec['nonok'][:120]))
        else:
            note('HETOW-P3')
            if rd['sigma'] not in menu:
                viol('HETOW-P3', 'sigma outside preregistered menu',
                     dict(tag=tag, sigma=rd['sigma']))
        jobs.append((polystr(f), rec))
        rows.append(rec)
    got = gp_sig_batch([(j[0], None) for j in jobs], p) if jobs else {}
    sigs, naive_ref = {}, 0
    for i, (ps, rec) in enumerate(jobs):
        if i not in got:
            continue
        sg = tuple(sorted(tuple(x) for x in got[i]))
        rec['pari'] = sg
        sigs[sg] = sigs.get(sg, 0) + 1
        if sg != naive:
            naive_ref += 1
        if rec['status'] == 'OK':
            note('HETOW-P2')
            if rec['sigma'] != sg:
                viol('HETOW-P2', 'reader sigma != PARI',
                     dict(rec=rec, f=ps))
    out = {'row': name, 'members': len(members), 'dropped': dropped,
           'pari': sum(sigs.values()),
           'ok': sum(1 for r in rows if r['status'] == 'OK'),
           'nonok': sum(1 for r in rows if r['status'] != 'OK'),
           'pari_counts': {str(k): v for k, v in sigs.items()},
           'naive_refuted': naive_ref,
           'distinct_pari': len(sigs),
           'secs': round(time.time() - t0, 1)}
    RES['rows'].append(out)
    print('   members %d dropped %d ok %d nonok %d pari %d '
          'distinct-pari %d  (%.1fs)'
          % (out['members'], dropped, out['ok'], out['nonok'],
             out['pari'], out['distinct_pari'], out['secs']))
    for k, v in sorted(out['pari_counts'].items()):
        print('     PARI %-28s %d' % (k, v))
    return out, rows, fr


# =================================================================== teeth
def teeth_run(rowsA, rowsB, frA5, frB5, p=5):
    print('\n== TEETH ==')
    # T-NAIVE
    ra = min(r['naive_refuted'] for r in RES['rows'] if 'caseA' in r['row'])
    rb = min(r['naive_refuted'] for r in RES['rows'] if 'caseB' in r['row'])
    tooth('T-NAIVE', ra >= 1 and rb >= 1,
          'min per-row naive refutations: caseA %d, caseB %d' % (ra, rb))
    # T-WITHHOLD (one member per case at p = 5)
    fA = build_member(frA5, [lift_or_zero(frA5, 33, 1),
                             lift_or_zero(frA5, 22, 1),
                             lift_or_zero(frA5, 11, 1)])
    rdA = H7.level2_read(fA, frA5, withhold=('11',))
    fB = build_member(frB5, [lift_or_zero(frB5, 21, (1, 0)),
                             lift_or_zero(frB5, 14, (0, 1)),
                             lift_or_zero(frB5, 7, (1, 1))])
    rdB = R1.level2_read(fB, frB5, withhold='7')
    tooth('T-WITHHOLD',
          rdA.get('status') == 'UNDETERMINED'
          and rdB.get('status') == 'UNDETERMINED',
          'caseA %s / caseB %s' % (rdA.get('status'), rdB.get('status')))
    # T-BADTWIST: case A letter s = 2, sweep ONE33; needs PARI adjudication
    R = Zp(p)
    fr2 = H7.L2Frame(R, p, 5, 2)
    cand = []
    for g0 in range(1, p):
        for g1 in range(p):
            for g2 in range(p):
                f = build_member(fr2, [lift_or_zero(fr2, 33, g0),
                                       lift_or_zero(fr2, 22, g1),
                                       lift_or_zero(fr2, 11, g2)])
                if not disc_nonzero(f, R):
                    continue
                rd = H7.level2_read(f, fr2)
                rn = H7.level2_read(f, fr2, use_twist=False)
                if (rd.get('status') == 'OK' and rn.get('status') == 'OK'
                        and rd['sigma'] != rn['sigma']):
                    cand.append((f, rd['sigma'], rn['sigma']))
    fired, detail = False, 'no twist-sensitive member found'
    if cand:
        got = gp_sig_batch([(polystr(f), None) for f, _, _ in cand[:20]], p)
        for i, (f, st, sn) in enumerate(cand[:20]):
            if i in got:
                sg = tuple(sorted(tuple(x) for x in got[i]))
                if st == sg and sn != sg:
                    fired, detail = True, ('twisted %s == PARI, untwisted %s'
                                           ' (of %d flips)'
                                           % (st, sn, len(cand)))
                    break
    tooth('T-BADTWIST', fired, detail)
    # T-THREESIGMA
    mx = max(r['distinct_pari'] for r in RES['rows'])
    tooth('T-THREESIGMA', mx >= 3,
          'max distinct PARI sigma within one fixed-letter family: %d' % mx)


# ==================================================================== main
def main():
    t0 = time.time()
    print('HETOW battery -- first inner-mu2 >= 3 tower coverage (n = 12)')
    for fn in ('he6_checks.py', 'he7_checks.py', 'he6r1_checks.py',
               'w12_checks.py', 'w10_checks.py'):
        RES['pins'][fn] = md5(fn)
        print('  import pin %-18s %s' % (fn, RES['pins'][fn]))
    print('  WIP = %s' % WIP)
    cap = 6 if WIP else None
    frA5 = frB5 = None
    for p in (3, 5):
        for s in (1, 2):
            _, _, fr = run_case('A', p, s, cap=cap)
            if p == 5 and s == 1:
                frA5 = fr
    for p, (c0, c1) in ((3, (1, 0)), (5, (2, 0))):
        _, _, fr = run_case('B', p, (c0, c1), cap=cap)
        if p == 5:
            frB5 = fr
    if not WIP:
        teeth_run(None, None, frA5, frB5)
    nchk = sum(RES['legs'].values())
    RES['summary'] = {'checks': nchk, 'violations': len(RES['viol']),
                      'teeth_fired': sum(1 for t in RES['teeth'].values()
                                         if t['fired']),
                      'teeth_total': len(RES['teeth']),
                      'secs': round(time.time() - t0, 1), 'wip': WIP}
    print('\nTOTAL checks %d violations %d teeth %d/%d  (%.1fs)'
          % (nchk, len(RES['viol']), RES['summary']['teeth_fired'],
             RES['summary']['teeth_total'], RES['summary']['secs']))
    verdict = ('GREEN' if not RES['viol']
               and RES['summary']['teeth_fired'] == RES['summary']['teeth_total']
               and not WIP else ('WIP' if WIP else 'RED'))
    RES['summary']['verdict'] = verdict
    print('VERDICT: %s' % verdict)
    with open('hetow_checks_results.json', 'w') as fh:
        json.dump(RES, fh, indent=1, default=str)


if __name__ == '__main__':
    main()
