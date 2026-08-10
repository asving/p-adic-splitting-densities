#!/usr/bin/env python3
"""GENTOW6-BOX-4 machine leg: the SEALED BATTERY-grade x-ful-digit
certificate rows (f1 = 2, eta != 1: c_0 * eta^{W(0)} not in F_Q) —
two-commit seal (this docstring preregistered at commit 1 BEFORE the
first run). Note: lean/notes/openmath/GENTOW6_BOXES_2026-08-10.md S5.
The box's ask (GENTOW6_PROOF S5 + post-PE3 fold): a sealed
battery-grade x-ful-digit certificate row — the PE2/PE3 legs were
hostile-arc verifier instruments, not sealed apparatus.

COMMITTED CODE PATHS REUSED (cited, never edited):
 * gentow6_pe2_fresh.py (md5 061639c322dfd98a48dc399f07e6dd04) —
   its integer primitives (dev/pdivmod_monic/vp) echo-check my
   level-1 devs, and its gp bridge pattern carries the PARI leg;
   the R1/R2 frame data and their ShC_0/dev wants are its LEG A
   committed measurements.
 * gentow6_box1_mu3.py (md5 c98cb423ce3acecf65a6e6a02a979b2d,
   verdict commit a646c7c9) — its Frame class (f1-blind by
   construction: Dp = deg Phi' = e1 f1) supplies the dual R/E
   shadow routes, the chk/tooth harness, and the gp sig/disc jobs.

GEOMETRY (PE2 LEG A): Q2, Phi' = x^4 + 2x^2 + 4 (e1 = 2, f1 = 2,
h = 1, D' = 4; eta = res(x^2/2), eta^2 + eta + 1 = 0, K = F_4).
FOUR ROWS at mu2 = 2 (all with T = {0}, t* = 0, f2 = 1, e2 = 2):
 R1 u2 = 9,  c_0 = eta:   L = 8x^3;         Phi2 = Phi'^2 - 8x^3
 R2 u2 = 9,  c_0 = 1+eta: L = 8x^3 + 16x;   Phi2 = Phi'^2 - 8x^3 - 16x
 R3 u2 = 11, c_0 = eta:   L = 16x^3;        Phi2 = Phi'^2 - 16x^3   [NEW]
 R4 u2 = 11, c_0 = 1+eta: L = 16x^3 + 32x;  Phi2 = Phi'^2 - 16x^3 - 32x [NEW]
Constants: R1/R2: nhat(9): i_0 = 1, a_0 = 4; I_0 = i_0 + e1 r* = 3
(r* = 1); E2 = 18, delta = 1, THETA_0 = 37; w(a,b) = 2a + 9b.
R3/R4: nhat(11): i_0 = 1, a_0 = 5; I_0 = 3; E2 = 22, delta = 3,
THETA_0 = 47; w(a,b) = 2a + 11b. Certificate (ANNEX-6.3'(b')):
slot (a*, b*) = (2 I_0 - D', 1) = (2, 1) at j* = 0, digit
lift(lambda_{0,r*})^2 * 2^{2(a_0 - r* h)} — 64 (v = 6) at R1/R2,
256 (v = 8) at R3/R4 — height = THETA_0 EXACTLY.

PREREGISTERED PREDICTIONS (R1/R2 wants = PE2's committed LEG A
measurements; R3/R4 wants = my hand ledgers, derived pre-seal from
the S6.1 (LIFT) displays and disclosed as ledger-derived):
 Q-DUAL  route R == route E on every scored member, every coord.
 Q-DEV   level-1 dev of Phi2^2: R1 [512, 64x^2-128, -16x^3, 0, 1];
   R2 [-256x^2-512, 64x^2+128, -16x^3-32x, 0, 1];
   R3 [2048, 256x^2-512, -32x^3, 0, 1];
   R4 [-1024x^2-2048, 256x^2+512, -32x^3-64x, 0, 1] — checked by my
   dev, by pe2.dev (committed path echo), AND by gp divrem chains.
 Q-CERT  honest DRAIN; ShC_0 exact dicts: R1 {(2,1): 64,
   (0,1): -128}; R2 {(2,1): 64, (0,1): 128}; R3 {(2,1): 256,
   (0,1): -512}; R4 {(2,1): 256, (0,1): 512}; cert slot (2,1)
   v = 6/6/8/8 with graded height-THETA_0 digit NONZERO; both slots
   sit at height THETA_0: pin(ShC_0) = 37/37/47/47 EXACTLY on the
   floor; ShC_1 == {} (the above-top face: B* + 1 = 1 < 2 = e2 f2).
 Q-PERS  10 perturbation rows per frame (seed 20260810, g = c *
   2^50 * x^alpha * Phi2^{j'}, row 0 pinned j' = 0): honest
   non-DRAIN; mindiff_0 == the self-shadow pin; mindiff_1 None or
   >= ee*45 = 180.
 Q-PARI  sig carriers via the committed nfinit/idealprimedec job:
   Phi' {(2,2)}; each of the four Phi2 {(4,2)} (e = e1 e2 = 4,
   f = f1 f2 = 2 — R3/R4 are NEW keys, theory-derived wants);
   poldisc != 0 at the j' = 0 perturbed member per row (4 jobs).
TEETH (kill counts asserted):
 T-F1EVAL the f1 = 1-evaluation mutant (digit read as scalar
   monomial chat pi^a x^{i_0}, i_0 = 1: 2 i_0 = 2 < 4 = D' predicts
   NO overflow, shadow-exact ShC == 0) — 4 kills (measured ShC_0
   nonzero at every row).
 T-VAL2  v* - 1 at the certificate slot — 4 kills.
 T-SLOT  mutant certificate slot b* = 0 (Y-exponent 2 e2 t* without
   the extraction's +1): slot (2,0)'s graded THETA_0 digit must be
   ZERO while (2,1)'s is nonzero — 4 kills.

RUN-1 RED DISCLOSURE (4 violations = ONE gp want-string literal,
RED artifact kept at gentow6_box4_row_output_run1_RED.txt md5
0269e02e; sealed md5 c0fbd1e4 at 90b23648): my
raw-job want rendered the zero dev slot as [0], but gp's
Vecrev(0) prints [] — the four DEV_R* jobs mismatched on that
single token while every printed coefficient was identical to the
want. Fix: render empty slots as [] in the want string. All 24
QCERT, 8 QDEV (python + pe2 echo), 88 QDUAL, 120 QPERS, 12 teeth,
and the 9 non-DEV GP checks (sig carriers + poldiscs) were GREEN
on run 1; no prediction changed.
"""
import random
import gentow6_pe2_fresh as pe2
import gentow6_box1_mu3 as b1

PHI1 = [4, 0, 2, 0, 1]
PH2SQ = b1.pmul(PHI1, PHI1)                    # Phi'^2
ROWS = []
for (name, u2, lift) in [
        ('R1', 9, [0, 0, 0, 8]),
        ('R2', 9, [0, 16, 0, 8]),
        ('R3', 11, [0, 0, 0, 16]),
        ('R4', 11, [0, 32, 0, 16])]:
    PHI2 = b1.padd(list(PH2SQ), b1.pneg(lift))
    ROWS.append(b1.Frame(name, 2, PHI1, 1, 2, 2, 1, 2, u2, PHI2))
assert (ROWS[0].E2, ROWS[0].delta, ROWS[0].theta(0)) == (18, 1, 37)
assert (ROWS[2].E2, ROWS[2].delta, ROWS[2].theta(0)) == (22, 3, 47)
assert all(F.Dp == 4 and F.D2 == 8 and F.mu1 == 4 for F in ROWS)

DEVW = {
    'R1': [[512], [-128, 0, 64], [0, 0, 0, -16], [], [1]],
    'R2': [[-512, 0, -256], [128, 0, 64], [0, -32, 0, -16], [], [1]],
    'R3': [[2048], [-512, 0, 256], [0, 0, 0, -32], [], [1]],
    'R4': [[-2048, 0, -1024], [512, 0, 256], [0, -64, 0, -32], [], [1]],
}
SHCW = {
    'R1': ({(2, 1): 64, (0, 1): -128}, 6, 37),
    'R2': ({(2, 1): 64, (0, 1): 128}, 6, 37),
    'R3': ({(2, 1): 256, (0, 1): -512}, 8, 47),
    'R4': ({(2, 1): 256, (0, 1): 512}, 8, 47),
}

random.seed(20260810)

def gp_dev(tag, f, want):
    """gp divrem chain: dev slots of f by Phi' as Vecrev lists."""
    outs = []
    src = 'k=%s; f=%s;' % (b1.poly_str(PHI1), b1.poly_str(f))
    for s in range(5):
        src += 'd%d = f %% k; f = (f - d%d)/k;' % (s, s)
        outs.append('Vecrev(d%d)' % s)
    b1.GP_JOBS.append('%s print("%s ", [%s])'
                      % (src, tag, ','.join(outs)))
    # [run-1 fix, disclosed]: gp Vecrev(0) prints [], not [0]
    b1.GP_META[tag] = ('raw', str([list(w) for w in want]))

def run_row(F):
    name = F.name
    print('== row %s (u2=%d) ==' % (name, F.u2))
    want, vstar, TH = SHCW[name]
    f = b1.ppow(F.PHI2, 2)
    # Q-DEV: my dev + the committed pe2.dev path echo
    A = F.level1(f)
    wantdev = DEVW[name]
    b1.chk('QDEV', [list(a) for a in A] == [list(w) for w in wantdev],
           '%s dev = %s want %s' % (name, A, wantdev))
    A2 = pe2.dev(list(f), list(PHI1))
    A2 = A2 + [[]] * (5 - len(A2))
    b1.chk('QDEV', [b1.pstrip(list(a)) for a in A2] ==
           [b1.pstrip(list(a)) for a in A],
           '%s pe2.dev echo mismatch: %s' % (name, A2))
    gp_dev('DEV_%s' % name, f, wantdev)
    # Q-CERT
    hs = F.honest(f)
    b1.chk('QCERT', all(not b1.pstrip(list(c)) for c in hs),
           '%s honest not DRAIN' % name)
    sR, sE = F.shadow_R(f), F.shadow_E(f)
    for j in range(2):
        b1.chk('QDUAL', F.slotdict(sR[j]) == F.slotdict(sE[j]),
               '%s R != E at j=%d' % (name, j))
    d0 = F.slotdict(sR[0])
    b1.chk('QCERT', d0 == want, '%s ShC_0 = %s want %s'
           % (name, d0, want))
    c0 = d0.get((2, 1), 0)
    b1.chk('QCERT', c0 != 0 and b1.vp(c0, 2) == vstar
           and pe2.vp(abs(c0), 2) == vstar,
           '%s cert v = %s want %d' % (name,
                                       b1.vp(c0, 2) if c0 else None,
                                       vstar))
    b1.chk('QCERT', F.graded_nonzero(sR[0], 2, 1, TH),
           '%s graded THETA_0 = %d digit at (2,1) zero' % (name, TH))
    b1.chk('QCERT', F.pin(sR[0]) == TH,
           '%s pin = %s want %d (floor attained)'
           % (name, F.pin(sR[0]), TH))
    b1.chk('QCERT', F.slotdict(sR[1]) == {},
           '%s ShC_1 = %s want {}' % (name, F.slotdict(sR[1])))
    # Q-PERS
    for r in range(10):
        c = random.randrange(1, 64)
        if c % 2 == 0:
            c += 1
        alpha = random.randrange(F.D2)
        jp = 0 if r == 0 else random.randrange(2)
        g = b1.pscale(b1.pmul([0] * alpha + [1], b1.ppow(F.PHI2, jp)),
                      c * 2 ** 50)
        fp = b1.padd(list(f), g)
        hp = F.honest(fp)
        b1.chk('QPERS', any(b1.pstrip(list(x)) for x in hp),
               '%s pert %d honest DRAIN' % (name, r))
        spR, spE = F.shadow_R(fp), F.shadow_E(fp)
        for j in range(2):
            b1.chk('QDUAL', F.slotdict(spR[j]) == F.slotdict(spE[j]),
                   '%s pert %d R != E at j=%d' % (name, r, j))
        md0 = F.mindiff(hp[0], spR[0])
        b1.chk('QPERS', md0 == TH, '%s pert %d mindiff_0 = %s want %d'
               % (name, r, md0, TH))
        md1 = F.mindiff(hp[1], spR[1])
        b1.chk('QPERS', md1 is None or md1 >= F.ee * 45,
               '%s pert %d mindiff_1 = %s' % (name, r, md1))
        if r == 0:
            b1.gp_disc('PD_%s' % name, fp)
    # teeth
    b1.tooth('T-F1EVAL', d0 != {},
             '%s f1=1-evaluation mutant (shadow-exact) survived' % name)
    b1.tooth('T-VAL2', c0 != 0 and b1.vp(c0, 2) != vstar - 1,
             '%s v*-1 mutant survived' % name)
    b1.tooth('T-SLOT', (not F.graded_nonzero(sR[0], 2, 0, TH))
             and F.graded_nonzero(sR[0], 2, 1, TH),
             '%s b*=0 mutant survived' % name)

def resolve_gp_raw():
    """extend b1.resolve_gp to handle 'raw' compare jobs."""
    raw = {t: w for t, (k, w) in b1.GP_META.items() if k == 'raw'}
    for t in raw:
        del b1.GP_META[t]
    import subprocess
    hdr = 'default(parisizemax, 2000000000);\n'
    src = hdr + '\n'.join(j for j in b1.GP_JOBS
                          if any(j.find('"%s ' % t) >= 0 for t in raw)) \
        + '\nquit\n'
    out = subprocess.run(['gp', '-q', '-f'], input=src,
                         capture_output=True, text=True, timeout=600)
    got = {}
    for line in out.stdout.splitlines():
        parts = line.split(' ', 1)
        if len(parts) == 2 and parts[0] in raw:
            got[parts[0]] = parts[1].strip().replace(' ', '')
    for t, w in raw.items():
        wantstr = w.replace(' ', '')
        b1.chk('GP', got.get(t) == wantstr,
               'gp %s: got %s want %s' % (t, got.get(t), wantstr))
    b1.GP_JOBS[:] = [j for j in b1.GP_JOBS
                     if not any(j.find('"%s ' % t) >= 0 for t in raw)]

def main():
    for F in ROWS:
        run_row(F)
    b1.gp_sig('EF_PHI1', PHI1, 2, [(2, 2)])
    for F in ROWS:
        b1.gp_sig('EF_%s' % F.name, F.PHI2, 2, [(4, 2)])
    resolve_gp_raw()
    b1.resolve_gp()
    print('== TALLY ==')
    for k in sorted(b1.TALLY):
        print('  %-6s %d' % (k, b1.TALLY[k]))
    print('  teeth kills: %s' % sorted(b1.KILLS.items()))
    ok_teeth = (b1.KILLS.get('T-F1EVAL', 0) == 4
                and b1.KILLS.get('T-VAL2', 0) == 4
                and b1.KILLS.get('T-SLOT', 0) == 4)
    if not ok_teeth:
        print('TEETH COUNT MISMATCH (want F1EVAL 4 / VAL2 4 / SLOT 4)')
    print('RESULT: %d checks, %d violations, teeth %s'
          % (b1.NCHK, b1.NVIO, 'OK' if ok_teeth else 'MISMATCH'))
    return 0 if (b1.NVIO == 0 and ok_teeth) else 1

if __name__ == '__main__':
    raise SystemExit(main())
