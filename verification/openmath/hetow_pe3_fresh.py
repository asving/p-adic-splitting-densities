#!/usr/bin/env python3
"""HETOW passPE3 FRESH-ROUTE instrument (hostile verifier; zero reader
imports; exact residue algebra + dual PARI oracle routes).

DISJOINT from all 10 prior contacts: the sealed battery's two eta=1
frames, PE1's X/Y, r1's Z/W, PE2's V/U/S/R/T.  Fresh frames (h = 1):

 M (p = 13, ord(eta) = 12 -- the first ord >= 12 frame anywhere; f2 = 4
   -- the first f2 = 4 wrap, W = (2,1,1,0) with THREE live wrap units,
   the first wrap value W(t) = 2 anywhere): Phi' = x^2 - 26, e1 = 2,
   f1 = 1, eta = 2 (primitive root mod 13); (e2,f2) = (1,4), u2 = 3
   (kappa2 = 3 > D'h = 2), i(3) = 1, Q(3) = 1, T2 = 12, D2 = 8.
   nhat: n(3) = 13x, n(6) = 13^3, n(9) = 13^4 x, n(12) = 13^6.
   Two psi2 sub-frames (design-phase gp search, disclosed; sealed here):
   M1 psi2 = Z^4+10Z^3+11Z^2+12Z+12  (c0,c1,c2,c3) = (1,1,2,3)
      rt   = Z^4+5Z^3+6Z^2+8Z+4 (minpoly(beta), irreducible)
      N    = Z^4+5Z^3+3Z^2+4Z+1 = (Z+7)(Z^3+11Z^2+4Z+2) SEPARABLE 1+3
      -> the sigma-VISIBLE naive tooth at f2 = 4.
   M2 psi2 = Z^4+9Z^3+11Z^2+12Z+11   (c0,c1,c2,c3) = (2,1,2,4)
      rt   = Z^4+11Z^3+6Z^2+8Z+8
      N    = Z^4+11Z^3+3Z^2+4Z+2 IRREDUCIBLE over F_13
      -> the first f2 >= 4 sigma-BLIND face (naive sigma = carrier
      sigma; only the letter clause detects -- rider C-B's mechanism
      at a frame with genuinely non-affine W); beta NONSQUARE in
      F_13^4 (Euler criterion, design-checked) -> INERT member live.
      N_eta2-form (coherent-normalizer variable) = Z^4+9Z^3+12Z^2+6Z+6;
      M1 N_eta2-form = Z^4+10Z^3+12Z^2+6Z+3.
   Keys (f1 = 1 LIFT): Phi2 = Phi'^4 - lift(c3 eta^W(3)) n(3) Phi'^3
     - lift(c2 eta^W(2)) n(6) Phi'^2 - lift(c1 eta^W(1)) n(9) Phi'
     - lift(c0 eta^W(0)) n(12);  naive = plain lifts (W dropped).
 N (e1 = 4 -- the first e1 = 4 wrap contact anywhere): p = 5,
   Phi' = x^4 - 10, f1 = 1, eta = 2 (ord 4); (e2,f2) = (1,2), u2 = 6
   (kappa2 = 6 > D'h = 4), i(6) = 2, Q(6) = 1, W = (1,0), T2 = 12,
   D2 = 8.  nhat: n(6) = 5x^2, n(12) = 5^3.
   psi2 = Z^2+Z+1 ((c0,c1) = (4,4));  rt = Z^2+3Z+4 irreducible;
   N = Z^2+3Z+2 = (Z+1)(Z+2) separable split; N_eta2 = Z^2+Z+3.
   coh key  = Phi'^2 - 4*5x^2*Phi' - 3*125   (c0 eta^W(0) = 8 = 3)
   naive    = Phi'^2 - 4*5x^2*Phi' - 4*125

PREREGISTERED PREDICTIONS (scored; any miss = RED):
 E1 W-two-ways: at M, Q((4-t)*3) - (4-t)*Q(3) == W(t) == (2,1,1,0)_t
    for t = 0,1,2,3 (the first TRIPLE-live wrap telescope, incl. the
    first W = 2); at N, Q(12) - 2*Q(6) == W(0) == 1.
 E2 corrected slot residues == rt at M1, M2, N (exact Z[x] algebra:
    Phi'-development + exact-height extraction + eta-wrap residue).
 E3 naive slot residues == N at M1, M2, N; factorization facts as
    pinned above (M1 sep 1+3; M2 irreducible; N sep 1+1).
 G1 sigma(coh) = composed carrier {(e1e2, f1f2)}: M1 {(2,4)},
    M2 {(2,4)}, N {(4,2)} -- both oracle routes.
 G2 sigma(naive): M1 {(2,1),(2,3)} (TOOTH: the derived 1+3 shape);
    M2 {(2,4)} SCORED AS EQUAL (the f2 = 4 sigma-BLIND face; the
    tooth at M2 is the letter job G2L only);
    N {(4,1),(4,1)} (TOOTH at e1 = 4).
 G2L LETTER jobs (route 1, nfmodpr; per prime above p, all primes):
    eta2bar := res(Phi'(x)^{e2}/n(u2)(x));  score [psi2(eta2bar)==0,
    N_eta2(eta2bar)==0] per prime:  M2-coh [1,0]; M2-naive [0,1];
    N-coh [1,0] (1 prime); N-naive [0,1] at EACH of the predicted 2
    primes.  (The letter clause = the load-bearing detector, scored
    at the sigma-blind frame M2 where no sigma symptom exists.)
 G2C coset factors at the M2 corrected key's field (route 1):
    res(n(k)(x)/x^k) == eta^{-Q(k)} for k = 3, 6, 9, 12:
    7, 5, 9, 12 (Q = 1, 3, 4, 6) -- the wrap-telescope residue layer
    machine-read in the field itself, four heights.
 G3 mu2 = 2 members at M2 (n = 16, T2 = 12, 2*T2 = 24; the first
    f2 = 4 tower members anywhere), f = Phi2^2 + A0, dual routes:
    RAM    A0 = x*13^12        (dv2 = 25, lambda2 = 25/2) -> {(4,4)}
    SPLITEQ A0 = 11*13^13      (dv2 = 26, digit -1, Z^2-1 splits)
                                                  -> {(2,4),(2,4)}
    INERT  A0 = 6*x*13^11*Phi' (dv2 = 26, digit -beta, Z^2-beta
           irreducible since beta nonsquare)      -> {(2,8)}
 All sigma jobs run BOTH oracle routes (factorpadic + per-factor
 nfinit-lift + idealprimedec vs factor/Q + idealprimedec); letter and
 coset jobs are route-1 only (disclosed).  SMOKE record: exact legs
 E1-E3 smoke-run before the gp battery (HETOWPE3_SMOKE=1); no gp
 sigma/letter/coset/member result seen before seal.
 [INSTRUMENT ERRATA, disclosed post-seal 2026-08-09 (two gp input-
 line-plumbing defects; zero predictions or derived values touched;
 same class as PE1's disclosed parisize stack fix):
 (1) the sealed GP_HDR put default(parisize, ...) and the sig
 definitions on ONE input line; gp's stack-resize discards the rest
 of its input line, so run 1's gp leg died with KeyError before ANY
 scored gp value was produced.  Fix: newline after default(...).
 (2) after fix (1), the two brace-body definitions sig1/sig2 still
 shared one input line, which gp mis-parses (sig1 printed as a
 closure instead of being applied); run 2 scored the letter jobs
 [[1,0]]/[[0,1]]/[[1,0]]/[[0,1],[0,1]] and the coset job [1,1,1,1]
 GREEN (all at their sealed predictions) and, of the sigma layer,
 only sig2 (factor/Q route) values printed -- each equal to its
 sealed prediction ([[2,4]] x2, [[4,2]], [[2,1],[2,3]],
 [[4,1],[4,1]], [[4,4]], [[2,4],[2,4]], [[2,8]]); the route-1 slots
 were the closure text, tallied as 18 plumbing violations.  Fix:
 newline between the definitions.  The committed run is the first
 with BOTH routes live.]
VERDICT: GREEN iff 0 violations."""
import json, os, subprocess, time

T0 = time.time()
VIOL = []
def check(leg, ok, detail):
    print('  %-36s %s  %s' % (leg, 'ok' if ok else '!! VIOLATION', detail))
    if not ok: VIOL.append((leg, str(detail)[:300]))

# ---------------------------------------------------- exact Z[x] core
def padd(a, b):
    n = max(len(a), len(b)); out = [0]*n
    for i, c in enumerate(a): out[i] += c
    for i, c in enumerate(b): out[i] += c
    while out and out[-1] == 0: out.pop()
    return out

def pscal(k, a): return [k*c for c in a] if k else []

def pmul(a, b):
    if not a or not b: return []
    out = [0]*(len(a)+len(b)-1)
    for i, c in enumerate(a):
        for j, d in enumerate(b): out[i+j] += c*d
    while out and out[-1] == 0: out.pop()
    return out

def ppow(a, k):
    out = [1]
    for _ in range(k): out = pmul(out, a)
    return out

def pdivmod(a, b):
    a = list(a); q = []
    while len(a) >= len(b) and a:
        c = a[-1]; d = len(a)-len(b)
        q = padd(q, [0]*d + [c])
        a = padd(a, pscal(-c, [0]*d + b))
    return q, a

def polystr(f):
    return '+'.join('(%d)*x^%d' % (c, i) for i, c in enumerate(f) if c) or '0'

def vp(n, p):
    if n == 0: return 10**9
    k = 0
    while n % p == 0: n //= p; k += 1
    return k

# ------------------------------------------------------------ frames
class Fr:
    """f1 = 1, h = 1, i0 = 1 (varpi = x) frames."""
    def __init__(self, name, p, e1, phip, eta, e2, f2, u2, cs):
        self.name, self.p, self.e1, self.phip = name, p, e1, phip
        self.eta, self.e2, self.f2, self.u2, self.cs = eta, e2, f2, u2, cs
    def i(self, k): return k % self.e1
    def Q(self, k): return (k - self.i(k)) // self.e1
    def W(self, t): return ((self.f2 - t)*self.i(self.u2)) // self.e1
    def nhat(self, k): return [0]*self.i(k) + [self.p**self.Q(k)]
    def key(self, corrected):
        f = ppow(self.phip, self.e2*self.f2)
        for t in range(self.f2):
            c = self.cs[t] * (self.eta**self.W(t) if corrected else 1) % self.p
            f = padd(f, pscal(-1, pmul(pscal(c, self.nhat((self.f2-t)*self.u2)),
                                       ppow(self.phip, self.e2*t))))
        return f
    def slot_res(self, c, k):
        """exact-height-k varpi-residue of a slot coefficient c in Z[x]:
        monomial u*p^g*x^a at height e1*g + a; res = u*eta^{-g}."""
        p, r, seen = self.p, 0, False
        for a, ca in enumerate(c):
            if ca == 0: continue
            hgt = self.e1*vp(ca, p) + a
            if hgt < k: return None
            if hgt == k:
                seen = True
                g = vp(ca, p); u = ca // p**g
                r = (r + u*pow(self.eta, (-g) % (p-1) if g else 0, p)) % p
        return r % p if seen else 0
    def killed(self, key):
        """assembled slot polynomial Z^{f2} - sum res_t Z^t (varpi-read)."""
        f, coeffs = list(key), []
        for t in range(self.f2):
            _, rem = pdivmod(f, self.phip)
            q, _ = pdivmod(f, self.phip)
            r = self.slot_res(rem, (self.f2 - t)*self.u2)
            coeffs.append(r % self.p if r is not None else None)
            f = q
        return coeffs  # [Z^0-coeff, ..., Z^{f2-1}-coeff] of the monic poly
        # (HETOW-1(c): the slot coefficient's varpi-residue IS the
        #  assembled polynomial's t-coefficient, sign included)

M_phip = [-26, 0, 1]
M1 = Fr('M1', 13, 2, M_phip, 2, 1, 4, 3, (1, 1, 2, 3))
M2 = Fr('M2', 13, 2, M_phip, 2, 1, 4, 3, (2, 1, 2, 4))
FN = Fr('N', 5, 4, [-10, 0, 0, 0, 1], 2, 1, 2, 6, (4, 4))

RT = {'M1': [4, 8, 6, 5], 'M2': [8, 8, 6, 11], 'N': [4, 3]}      # low->high
NV = {'M1': [1, 4, 3, 5], 'M2': [2, 4, 3, 11], 'N': [2, 3]}

def exact_legs():
    # E1: wrap telescope
    for fr, wpred in ((M1, (2, 1, 1, 0)), (FN, (1, 0))):
        got = tuple(fr.Q((fr.f2-t)*fr.u2) - (fr.f2-t)*fr.Q(fr.u2)
                    for t in range(fr.f2))
        wv = tuple(fr.W(t) for t in range(fr.f2))
        check('E1-W-two-ways-%s' % fr.name, got == wv == wpred,
              'Q-route %s vs floor %s vs pred %s' % (got, wv, wpred))
    # E2/E3: slot residues of both keys
    for fr in (M1, M2, FN):
        kc, kn = fr.killed(fr.key(True)), fr.killed(fr.key(False))
        check('E2-coh-slotres-eq-rt-%s' % fr.name, kc == RT[fr.name],
              '%s vs rt %s' % (kc, RT[fr.name]))
        check('E3-naive-slotres-eq-N-%s' % fr.name, kn == NV[fr.name],
              '%s vs N %s' % (kn, NV[fr.name]))
        check('E3-diverge-%s' % fr.name, kc != kn, '%s vs %s' % (kc, kn))

# ------------------------------------------------------------ gp leg
GP_HDR = ('default(parisize, 2000000000);\n'
          'sig1(f, p) = { my(fa = factorpadic(f, p, 60), out = List()); '
          ' for(i = 1, matsize(fa)[1], '
          '  my(g = Pol(apply(centerlift, Vec(fa[i,1]))), '
          '  nf = nfinit([g, [p]]), dec = idealprimedec(nf, p)); '
          '  if(#dec != 1, error("KRASNER")); '
          '  for(m = 1, fa[i,2], listput(out, [dec[1].e, dec[1].f]))); '
          ' vecsort(Vec(out)) };\n'
          'sig2(f, p) = { my(fa = factor(f), out = List()); '
          ' for(i = 1, matsize(fa)[1], my(nf = nfinit([fa[i,1], [p]]), '
          '  dec = idealprimedec(nf, p)); '
          '  for(m = 1, fa[i,2], for(j = 1, #dec, '
          '   listput(out, [dec[j].e, dec[j].f])))); '
          ' vecsort(Vec(out)) };\n')

def run_gp(script):
    r = subprocess.run(['gp', '-q'], input=script.encode(),
                       capture_output=True, timeout=3600)
    if r.returncode != 0:
        raise RuntimeError('gp failed: %s' % r.stderr.decode()[:500])
    return r.stdout.decode()

def gp_legs():
    jobs = []          # (tag, poly, p, pred-sigma or None)
    jobs.append(('G1-coh-M1', M1.key(True), 13, [[2, 4]]))
    jobs.append(('G1-coh-M2', M2.key(True), 13, [[2, 4]]))
    jobs.append(('G1-coh-N', FN.key(True), 5, [[4, 2]]))
    jobs.append(('G2-TOOTH-naive-M1', M1.key(False), 13, [[2, 1], [2, 3]]))
    jobs.append(('G2-naive-M2-SIGMABLIND', M2.key(False), 13, [[2, 4]]))
    jobs.append(('G2-TOOTH-naive-N', FN.key(False), 5, [[4, 1], [4, 1]]))
    # G3 members at M2: f = Phi2^2 + A0
    K2 = M2.key(True)
    ram = padd(pmul(K2, K2), [0, 13**12])
    spl = padd(pmul(K2, K2), [11*13**13])
    inr = padd(pmul(K2, K2), pmul([0, 6*13**11], M_phip))
    jobs.append(('G3-RAM-M2', ram, 13, [[4, 4]]))
    jobs.append(('G3-SPLITEQ-M2', spl, 13, [[2, 4], [2, 4]]))
    jobs.append(('G3-INERT-M2', inr, 13, [[2, 8]]))
    lines = [GP_HDR]
    for i, (tag, f, p, pred) in enumerate(jobs):
        ps = polystr(f)
        lines.append('print("R %d ", sig1(Pol(%s), %d), " | ", sig2(Pol(%s), %d))'
                     % (i, ps, p, ps, p))
    # letters: per-prime [psi2(eta2bar)==0, Neta2(eta2bar)==0]
    lines.append(
        'lm(f) = { my(nf = nfinit([f, [13]]), dec = idealprimedec(nf, 13),'
        ' X = Mod(x, f), out = List()); for(j = 1, #dec,'
        ' my(e2b = nfmodpr(nf, nfeltdiv(nf, X^2 - 26, 13*X), dec[j]));'
        ' listput(out, [e2b^4+9*e2b^3+11*e2b^2+12*e2b+11 == 0,'
        ' e2b^4+9*e2b^3+12*e2b^2+6*e2b+6 == 0])); Vec(out) }')
    lines.append('print("L M2-coh ", lm(Pol(%s)))' % polystr(M2.key(True)))
    lines.append('print("L M2-naive ", lm(Pol(%s)))' % polystr(M2.key(False)))
    lines.append(
        'ln(f) = { my(nf = nfinit([f, [5]]), dec = idealprimedec(nf, 5),'
        ' X = Mod(x, f), out = List()); for(j = 1, #dec,'
        ' my(e2b = nfmodpr(nf, nfeltdiv(nf, X^4 - 10, 5*X^2), dec[j]));'
        ' listput(out, [e2b^2+e2b+1 == 0, e2b^2+e2b+3 == 0])); Vec(out) }')
    lines.append('print("L N-coh ", ln(Pol(%s)))' % polystr(FN.key(True)))
    lines.append('print("L N-naive ", ln(Pol(%s)))' % polystr(FN.key(False)))
    # coset factors in the M2 corrected field
    lines.append(
        'cf() = { my(f = Pol(%s), nf = nfinit([f, [13]]),'
        ' pr = idealprimedec(nf, 13)[1], X = Mod(x, f));'
        ' [nfmodpr(nf, nfeltdiv(nf, 13*X, X^3), pr) == 7,'
        '  nfmodpr(nf, nfeltdiv(nf, 13^3, X^6), pr) == 5,'
        '  nfmodpr(nf, nfeltdiv(nf, 13^4*X, X^9), pr) == 9,'
        '  nfmodpr(nf, nfeltdiv(nf, 13^6, X^12), pr) == 12] }'
        % polystr(M2.key(True)))
    lines.append('print("C M2 ", cf())')
    lines.append('quit')
    out = run_gp('\n'.join(lines))
    got, letters, cosets = {}, {}, None
    for line in out.splitlines():
        line = line.strip()
        if line.startswith('R '):
            idx, rest = line[2:].split(' ', 1)
            got[int(idx)] = rest.strip()
        elif line.startswith('L '):
            tag, rest = line[2:].split(' ', 1)
            letters[tag] = rest.strip()
        elif line.startswith('C M2 '):
            cosets = line[5:].strip()
    res = {}
    for i, (tag, f, p, pred) in enumerate(jobs):
        r1, r2 = [s.strip() for s in got[i].split('|')]
        check(tag + '-routes-agree', r1 == r2, '%s vs %s' % (r1, r2))
        ps = str(pred).replace(' ', '')
        check(tag, r1.replace(' ', '') == ps, 'sigma = %s (pred %s)' % (r1, ps))
        res[tag] = r1
    for tag, pred in (('M2-coh', '[[1, 0]]'), ('M2-naive', '[[0, 1]]'),
                      ('N-coh', '[[1, 0]]'), ('N-naive', '[[0, 1], [0, 1]]')):
        check('G2L-' + tag, letters.get(tag, '').replace(' ', '')
              == pred.replace(' ', ''), '%s (pred %s)' % (letters.get(tag), pred))
        res['G2L-' + tag] = letters.get(tag)
    check('G2C-cosets-M2', cosets is not None and
          cosets.replace(' ', '') == '[1,1,1,1]',
          '%s (pred all-1: res(n(k)(x)/x^k) == eta^{-Q(k)} = 7, 5, 9, 12'
          ' at k = 3, 6, 9, 12)' % cosets)
    res['G2C'] = cosets
    return res

def main():
    print('HETOW passPE3 fresh route: frames M1/M2 (p=13 ord12 f2=4 '
          'triple-wrap) + N (e1=4) + letters + cosets + M2 members')
    exact_legs()
    res = {}
    if not os.environ.get('HETOWPE3_SMOKE'):
        res = gp_legs()
    print('\nTOTAL violations %d (%.1fs)' % (len(VIOL), time.time() - T0))
    print('VERDICT: %s' % ('GREEN' if not VIOL else 'RED'))
    if not os.environ.get('HETOWPE3_SMOKE'):
        with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                               'hetow_pe3_fresh_results.json'), 'w') as fh:
            json.dump({'viol': VIOL, 'res': res}, fh, indent=1, sort_keys=True)

if __name__ == '__main__':
    main()
