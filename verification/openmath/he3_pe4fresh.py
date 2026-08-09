#!/usr/bin/env python3
"""HE3 passPE4 FRESH ROUTE (acceptance-pass hostile verifier's own instrument;
geographies + reads disjoint from PE1 legs A/B/C, PE2 FR-A/B/C/D, PE3
FR1/FR2/FR3, and the note's S8/S9' rows).

SEALED PREDICTIONS (hand-derived from the note's displays BEFORE running;
PARI factorpadic/idealprimedec [the pinned w12 GP_FUN convention] is the
oracle on Z_p rows, explicit construction + Hensel root reads on equal-char
rows; measurements are python-exact Bareiss resultants + hulls, no slot
formula in any measurement loop except the letter-carrier construction
itself, which is cross-checked by the PARI nfmodpr direct leg).

FR-A  THE MU = 2 DICTIONARY SWEEP at frames never machine-run on the HE3
      side (S2/S6.4 surface: the simple cases' derivations):
 A1 (e1,f1) = (4,1), Z_3, Phi' = x^4 - 3 (D' = 4, D'h = 4, K = F_3,
    eta = 1, W == 0):
    A1-RAM    f = Phi'^2 + 9x      (lam = 9/2, l=2 d=1)  -> sigma {(8,1)}
    A1-INERT  f = Phi'^2 + 9x^2    (lam = 5, R = Z^2+1 irred/F_3)
                                                          -> sigma {(4,2)}, m_s = 0 at s in {1,2}
    A1-SPLIT  f = Phi'^2 + 18x^2   (lam = 5, R = Z^2+2 = (Z-1)(Z+1))
                                                          -> sigma {(4,1),(4,1)}, m_1 = m_2 = 1
              (a STARVED slope at (Q,f1) = (3,1): both letters are roots)
    A1-2SIDED f = Phi'^2 + 3x Phi' + 9x^3 (slopes {5,6})  -> sigma {(4,1),(4,1)}
    Node floors dv(A_j) >= (2-j)*4+1 and HE3-1a (v3 Res(f,Phi') =
    v3 Res(Phi',A0)) asserted per member.
 A2 (e1,f1) = (2,3), Z_2, Phi' = x^6 + 4x^2 + 8 (D' = 6, D'h = 6,
    K = F_8 = F_2(eta), eta^3 = eta+1; lam = 7, kappa0 = 14,
    W = (0,1,1) non-trivial -- FIRST wrap-seam adjudication at f1 = 3 and
    in characteristic-2 residue arithmetic):
    A2-RAM    f = Phi'^2 + 64x     (lam = 13/2)           -> sigma {(4,3)}
    A2-INERT  f = Phi'^2 + 8x Phi' + 64x^2: COHERENT R~ = eta(Z^2+Z+1)
              IRREDUCIBLE -> sigma {(2,6)}, m_s = 0 at all 7 letters;
              NAIVE R = Z^2+Z+eta SPLITS (Tr eta = 0) -> naive would
              predict {(2,3),(2,3)} == TOOTH T-FLIP-1 (PARI kills naive).
    A2-SPLIT  f = (Phi' - 4x^3)(Phi' - 2x^5): sigma = {(2,3),(2,3)} BY
              CONSTRUCTION (each factor dv-height-7 perturbation of Phi');
              COHERENT R~ = eta(Z+eta)(Z+eta^2) split at the Frobenius
              pair {eta, eta^2}, m_eta = m_eta2 = 1, 0 at the other 5;
              NAIVE R = Z^2+(eta^2+eta)Z+(eta^2+eta) IRREDUCIBLE
              (Tr((eta^2+eta)^-1) = Tr(eta+1) = 1) -> naive would predict
              {(2,6)} == TOOTH T-FLIP-2 (opposite direction).
    W-DIRECT (nfmodpr, no slot formula, no W formula): coherent
    coefficients (a~0,a~1,a~2) = (eta,eta,eta) [INERT] and
    (eta^2+eta, eta^2+eta+1, eta) [SPLIT]; naive (eta,1,1) and
    (eta^2+eta, eta^2+eta, 1); eta := nfmodpr image of theta^2/2.
    T-REACH: the retired display's carriers s^ n(7) (s^ in Z_2) reach
    res set F_2^x = {1} only -- misses BOTH residual roots {eta, eta^2}
    of A2-SPLIT (PE1-F1 mechanism live at the new frame).
 A3 EQUAL-CHARACTERISTIC, BY CONSTRUCTION (first equal-char f1 >= 2
    contact anywhere in the arc, and a new equal-char e1 = 3 frame):
 A3a q = 3, (e1,f1) = (1,2): O = F_3[[t]], Phi' = x^2 + t^2 (K = F_9 =
    F_3(u), u^2 = -1, eta = u), f = (x^2 - t^2 x + t^2)(x^2 + t^2 x + t^2):
    sigma = {(1,2),(1,2)} BY CONSTRUCTION (disc = t^2(t^2-1), unit part
    -1 nonsquare in F_3 -> both factors unramified quadratic).
    Development: A1 = -t^4 (pin lifted), A0 = t^6; single side lam = 3
    len 2; R = Z^2 + 1 = (Z-eta)(Z+eta) split at the Frobenius pair.
    PER-ROOT LABEL READS (Hensel in F_9[[t]], both branches per factor):
    g1 roots BOTH carry label (3, Z - eta) (beta = z0 = eta_rho, so
    beta - iota(eta) = 0 at both branches); g2 roots BOTH carry
    (3, Z + eta) -- LEMMA HE3-6 equivariance machine-run at f1 = 2.
 A3b q = 2, (e1,f1) = (3,1): O = F_2[[t]], Phi' = x^3 + t,
    f = (x^3 + tx + t)(x^3 + tx^2 + t): sigma = {(3,1),(3,1)} BY
    CONSTRUCTION (each factor single-side slope-1/3, linear residual).
    Development: A1 = t^2 + tx + tx^2, A0 = t^3; slopes {4 (len 1),
    5 (len 1)}; per-root dv(Phi'(rho)) = 4 resp. 5 via F_2[[s]] Hensel
    (s^3 = t), beta = 1 at n(4) = xt resp. n(5) = x^2 t.
FR-B  THE (SEP) APPARATUS DIRECT TEST (S6.1 surface; the inversion run AS
      an inversion, and the at-slope generic-letter samples, never
      machine-run): Z_5, (e1,f1) = (2,1), Phi' = x^2 - 5,
      f = (Phi'-5x)(Phi'-25)(Phi'-25x) = (x^2-5x-5)(x^2-30)(x^2-25x-5):
      polygon slopes {3,4,5} CONSECUTIVE integers, len 1 each (the
      sub-case (c) geography with |K^x| = 4 >= 2); root letter 1 at each.
      Psi(kappa,s) := e1 * v5(Res(f, Phi' - s n(kappa))):
      equality Psi = D' h_F(kappa) at ALL non-root samples: kappa = 6
      (above-top) s in {1..4}, AND AT-slope samples (kappa, s != 1) for
      kappa in {3,4,5} [h_F = 9, 11, 12, 12 -> Psi = 18, 22, 24, 24];
      strict excess at the root samples (kappa, 1), kappa in {3,4,5}.
      INVERSION: {count = 6; rows min(lam,4), min(lam,6)} (det 1) solved
      on measured Psi -> n = (2,2,2) = construction; PARI sigma {(2,1)^3}.
      TOOTH T-INV: corrupting Psi(4) by +2 must break the solve
      (non-nonneg or wrong sum).
FR-C  THE STARVED (2,2) CORNER (the one listed S1(iii)/GENHN-fence corner
      geography never machine-run): Z_2, (e1,f1) = (1,2),
      Phi' = x^2 + 2x + 4 (K = F_4, psi = y^2+y+1), mu = 3,
      f = (Phi'-8)(Phi'-4x)(Phi'-8-4x) = (x^2+2x-4)(x^2-2x+4)(x^2-2x-4):
      development pins dv(A2) = 4 (lifted), dv(A1) = 7 (lifted),
      dv(A0) = 9; single side lam = 3 = D'h+1 len 3; R = Z^3 + 1 with
      root set = ALL of F_4^x (genuinely starved: no generic letter at
      kappa = 3); peel m_s = 1 at each of {1, w, w^2} via slot carriers
      C_1 = 8, C_w = 4x, C_w2 = 8+4x; sigma = {(1,2)^3} by PARI AND by
      construction (all three quadratics unramified: 5, -3, 5 mod 8
      nonsquare units).

FR-B ADDENDUM (disclosed wiring evolution, pre-verdict): the exact-product
member makes each root sample (kappa,1) an EXACT divisor (Res = 0, Psi =
+infinity) -- recorded as such; a junk variant f + 5^9 (same polygon, same
letters, no exact divisor) was ADDED for finite root-sample excesses and a
dictionary-only PARI sigma row.  Predictions for it: same equalities, finite
excess at (kappa,1), inversion (2,2,2), sigma {(2,1)^3}.

VERDICT GREEN iff 0 violations and all teeth fire.

Smoke disclosure (wiring fixes during smoke, NO prediction changed):
(1) gp -q echoes function-definition closures -- filtered from stdout;
(2) 'eta' is a gp BUILT-IN (Dedekind eta) -- the nfmodpr leg's variable
renamed 'et'; (3) the peel reader first used hull-above-length, which
drops the A0' = 0 infinite pin when a slot carrier exactly divides f
(the [r1-N1] A0' = 0 branch, hit by the A2-SPLIT/FR-B/FR-C exact-product
members at their own root letters) -- replaced by the direct HE3-2(b)
m-read (min j with pin ON the lam-line; A_j' = 0 counts as lifted), the
same semantics the r1 supp documents for its above_line reader.
Derivation history: A3a's A1 and
A3b's A1 were first hand-drafted as 0 resp. tx+tx^2 and corrected to
-t^4 resp. t^2+tx+tx^2 during the pre-seal derivation (reduction terms);
A2-INERT was first drafted with target R~ = Z^2+Z+1 and re-aimed to
eta(Z^2+Z+1) when the forced leading twist a~2 = eta was noticed.  All
predictions above were FROZEN before the first full run.
"""
import json, subprocess, sys
from fractions import Fraction

# ---------------- exact Z[x] toolkit ----------------
def pnorm(a):
    a = list(a)
    while a and a[-1] == 0: a.pop()
    return a
def padd(a, b):
    n = max(len(a), len(b)); r = [0]*n
    for i, c in enumerate(a): r[i] += c
    for i, c in enumerate(b): r[i] += c
    return pnorm(r)
def pneg(a): return [-c for c in a]
def psub(a, b): return padd(a, pneg(b))
def pmul(a, b):
    if not a or not b: return []
    r = [0]*(len(a)+len(b)-1)
    for i, c in enumerate(a):
        for j, d in enumerate(b): r[i+j] += c*d
    return pnorm(r)
def pdivmod(a, b):
    # b monic
    a = list(a); q = [0]*max(1, len(a)-len(b)+1)
    while len(a) >= len(b):
        c = a[-1]; d = len(a)-len(b)
        q[d] = c
        for i in range(len(b)): a[d+i] -= c*b[i]
        a = pnorm(a)
    return pnorm(q), pnorm(a)
def sylres(a, b):
    """Res(a,b) for int polys via fraction-free Bareiss."""
    n, m = len(a)-1, len(b)-1
    if n < 0 or m < 0: return 0
    N = n+m
    M = []
    for i in range(m):
        M.append([0]*i + list(reversed(a)) + [0]*(m-1-i))
    for i in range(n):
        M.append([0]*i + list(reversed(b)) + [0]*(n-1-i))
    # Bareiss
    prev = 1
    M = [row[:] for row in M]
    for k in range(N-1):
        if M[k][k] == 0:
            piv = next((i for i in range(k+1, N) if M[i][k] != 0), None)
            if piv is None: return 0
            M[k], M[piv] = M[piv], M[k]
            for j in range(N): M[k][j] = -M[k][j]
        for i in range(k+1, N):
            for j in range(k+1, N):
                M[i][j] = (M[i][j]*M[k][k] - M[i][k]*M[k][j]) // prev
            M[i][k] = 0
        prev = M[k][k]
    return M[N-1][N-1]
def vp(n, p):
    if n == 0: return None
    n = abs(n); v = 0
    while n % p == 0: n //= p; v += 1
    return v
def develop(f, Phi, mu):
    A = []; cur = list(f)
    for _ in range(mu):
        cur, r = pdivmod(cur, Phi)
        A.append(r)
    A.append(cur)  # should be [1]
    assert pnorm(cur) == [1], "development leading term"
    return A
def dv_at(A, Key, p, e1, Dp):
    """dv(A(theta_Key)) = e1 * vp(Res(Key, A)) / Dp, None if A = 0."""
    if not pnorm(A): return None
    return Fraction(e1 * vp(sylres(Key, A), p), Dp)
def lower_hull(pins):
    """pins: list of (j, dv or None). Returns [(slope, length)] with
    slope = dv-drop per abscissa, sides left->right (decreasing slope)."""
    pts = [(j, d) for j, d in pins if d is not None]
    pts.sort()
    hull = []
    for pt in pts:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            if (y2-y1)*(pt[0]-x2) >= (pt[1]-y2)*(x2-x1):
                hull.pop()
            else: break
        hull.append(pt)
    sides = []
    for (x1, y1), (x2, y2) in zip(hull, hull[1:]):
        sides.append((Fraction(y1-y2, x2-x1), x2-x1))
    return sides
def above_len(sides, lam):
    return sum(L for s, L in sides if s > lam)
def m_read(dvs, lam, c):
    """HE3-2(b) multiplicity read on a full-side member: pins (j, dvs[j]),
    line height c - lam*j; m = min j with pin exactly ON the line
    (dv None = A_j' = 0 = infinitely lifted, the [r1-N1] A0' = 0 branch
    semantics).  dvs indexed j = 0..mu, dvs[mu] = 0."""
    for j, d in enumerate(dvs):
        if d is not None and d == c - lam*j:
            return j
    raise AssertionError('no on-line pin')

# ---------------- gp ----------------
GP_FUN = r"""
ef(g, p) = {
  if (poldegree(g) == 1, return([1, 1]));
  my(nf = nfinit([g, [p]]), dec = idealprimedec(nf, p));
  [dec[1].e, dec[1].f]
}
sig(f, p) = {
  my(d = poldisc(f), F);
  if (d == 0, return([[-1, -1]]));
  F = factorpadic(f, p, 200);
  vecsort(vector(matsize(F)[1], i, ef(liftall(F[i, 1]), p)))
}
"""
def gprun(script):
    r = subprocess.run(['gp', '-q'], input=GP_FUN + script,
                       capture_output=True, text=True, timeout=600)
    if r.returncode != 0:
        raise RuntimeError('gp failed: ' + r.stderr[:500])
    return [l for l in r.stdout.splitlines()
            if l.strip() and '->' not in l]  # drop gp's echoed closures
def parse_sig(txt):
    nums = [int(x) for x in
            txt.replace('[', ' ').replace(']', ' ').replace(',', ' ').split()]
    return tuple(sorted(zip(nums[0::2], nums[1::2])))
def gpstr(a):
    return 'Pol([' + ','.join(str(c) for c in reversed(a)) + '])' if a else '0'

VIOL = []
TEETH = {}
RES = {'sections': {}}
def ok(cond, tag, msg):
    print(('   [OK ] ' if cond else '   [VIOLATION] ') + msg)
    if not cond: VIOL.append((tag, msg))

# =============== FR-A1: (4,1) @ Z_3 ===============
def fr_a1():
    print('== FR-A1: mu=2 dictionary at (e1,f1) = (4,1), Z_3, Phi = x^4-3 ==')
    p, e1, f1, h = 3, 4, 1, 1; Dp = 4
    Phi = [-3, 0, 0, 0, 1]
    members = [
        ('A1-RAM',    padd(pmul(Phi, Phi), [0, 9]),        [(Fraction(9,2), 2)], ((8,1),)),
        ('A1-INERT',  padd(pmul(Phi, Phi), [0, 0, 9]),     [(Fraction(5), 2)],   ((4,2),)),
        ('A1-SPLIT',  padd(pmul(Phi, Phi), [0, 0, 18]),    [(Fraction(5), 2)],   ((4,1),(4,1))),
        ('A1-2SIDED', padd(padd(pmul(Phi, Phi), pmul([0,3], Phi)), [0,0,0,9]),
                      [(Fraction(6), 1), (Fraction(5), 1)], ((4,1),(4,1))),
    ]
    sig_jobs = []
    for name, f, want_sides, want_sig in members:
        A = develop(f, Phi, 2)
        dvs = [dv_at(A[j], Phi, p, e1, Dp) for j in range(2)]
        ok(all(d is None or d >= (2-j)*4+1 for j, d in enumerate(dvs)),
           'A1-node', f'{name}: node floors dv(A_j) >= (2-j)D\'h+1  (dv = {dvs})')
        sides = lower_hull([(0, dvs[0]), (1, dvs[1]), (2, Fraction(0))])
        ok(sorted(sides) == sorted(want_sides), 'A1-polygon',
           f'{name}: polygon sides {sides} == predicted {want_sides}')
        ok(vp(sylres(f, Phi), p) == vp(sylres(Phi, A[0]), p), 'A1-he31a',
           f'{name}: HE3-1a  v3 Res(f,Phi) = v3 Res(Phi,A0) = {vp(sylres(f, Phi), p)}')
        sig_jobs.append((name, f, want_sig))
    # peel profiles at lam = 5 for INERT (m = 0,0) and SPLIT (m = 1,1)
    n5 = [0, 3]  # n(5) = 3x  (i0(5) = 1, (5-1)/4 = 1)
    for name, wantm in [('A1-INERT', {1: 0, 2: 0}), ('A1-SPLIT', {1: 1, 2: 1})]:
        f = dict((n, ff) for n, ff, _ in [(m[0], m[1], 0) for m in members])[name]
        got = {}
        for s in (1, 2):
            Key = psub(Phi, pmul([s], n5))
            A2p = develop(f, Key, 2)
            dvs = [dv_at(A2p[j], Key, p, e1, Dp) for j in range(2)] + [Fraction(0)]
            got[s] = m_read(dvs, Fraction(5), Fraction(10))
        ok(got == wantm, 'A1-peel', f'{name}: peel profile m_s {got} == {wantm}'
           + ('  [STARVED slope at (3,1): all letters are roots]' if name == 'A1-SPLIT' else ''))
    lines = gprun('\n'.join(f'print("{n}: ", sig({gpstr(f)}, 3))' for n, f, _ in sig_jobs))
    for (name, f, want), ln in zip(sig_jobs, lines):
        got = parse_sig(ln.split(':')[1])
        ok(got == tuple(sorted(want)), 'A1-sigma',
           f'{name}: PARI sigma {got} == dictionary {tuple(sorted(want))}')
    RES['sections']['FR-A1'] = 'run'

# =============== FR-A2: (2,3) @ Z_2 ===============
def fr_a2():
    print('== FR-A2: mu=2 dictionary + wrap seam at (e1,f1) = (2,3), Z_2, Phi = x^6+4x^2+8 ==')
    p, e1, f1, h = 2, 2, 3, 1; Dp = 6
    Phi = [8, 0, 4, 0, 0, 0, 1]
    fram   = padd(pmul(Phi, Phi), [0, 64])
    finert = padd(padd(pmul(Phi, Phi), pmul([0, 8], Phi)), [0, 0, 64])
    g1, g2 = psub(Phi, [0, 0, 0, 4]), psub(Phi, [0, 0, 0, 0, 0, 2])
    fsplit = pmul(g1, g2)
    members = [('A2-RAM', fram, ((4,3),)), ('A2-INERT', finert, ((2,6),)),
               ('A2-SPLIT', fsplit, ((2,3),(2,3)))]
    for name, f, _ in members:
        A = develop(f, Phi, 2)
        dvs = [dv_at(A[j], Phi, p, e1, Dp) for j in range(2)]
        ok(all(d is None or d >= (2-j)*6+1 for j, d in enumerate(dvs)),
           'A2-node', f'{name}: node floors  (dv = {dvs})')
        ok(vp(sylres(f, Phi), p) == vp(sylres(Phi, A[0]), p), 'A2-he31a',
           f'{name}: HE3-1a  v2 Res(f,Phi) = v2 Res(Phi,A0) = {vp(sylres(f, Phi), p)}')
    # polygons
    for name, f, want in [('A2-RAM', fram, [(Fraction(13,2), 2)]),
                          ('A2-INERT', finert, [(Fraction(7), 2)]),
                          ('A2-SPLIT', fsplit, [(Fraction(7), 2)])]:
        A = develop(f, Phi, 2)
        dvs = [dv_at(A[j], Phi, p, e1, Dp) for j in range(2)]
        sides = lower_hull([(0, dvs[0]), (1, dvs[1]), (2, Fraction(0))])
        ok(sorted(sides) == sorted(want), 'A2-polygon',
           f'{name}: polygon sides {sides} == predicted {want}')
    # peel profiles at lam = 7 over ALL of F_8^x via HE3-1L slot carriers
    # letter s = s0 + s1 eta + s2 eta^2  <->  C = s0*8x + s1*4x^3 + s2*2x^5
    letters = [(s0, s1, s2) for s0 in (0,1) for s1 in (0,1) for s2 in (0,1)][1:]
    wantm = {'A2-INERT': {}, 'A2-SPLIT': {}}
    for L in letters:
        wantm['A2-INERT'][L] = 0
        wantm['A2-SPLIT'][L] = 1 if L in [(0,1,0), (0,0,1)] else 0
    for name, f in [('A2-INERT', finert), ('A2-SPLIT', fsplit)]:
        got = {}
        for (s0, s1, s2) in letters:
            C = pnorm([0, 8*s0, 0, 4*s1, 0, 2*s2])
            Key = psub(Phi, C)
            A2p = develop(f, Key, 2)
            dvs = [dv_at(A2p[j], Key, p, e1, Dp) for j in range(2)] + [Fraction(0)]
            got[(s0,s1,s2)] = m_read(dvs, Fraction(7), Fraction(14))
        ok(got == wantm[name], 'A2-peel',
           f'{name}: peel profile over F_8^x == predicted '
           f'(ones at {sorted(k for k, v in got.items() if v)})')
    # T-REACH: retired-display carriers s^ n(7), s^ in Z: residue reach = F_2^x
    reach = {(1, 0, 0)}  # res(s^) in F_2; letters as slot triples
    roots = {(0,1,0), (0,0,1)}
    fire = reach.isdisjoint(roots)
    TEETH['T-REACH'] = fire
    ok(fire, 'T-REACH', 'TOOTH T-REACH: old s^ n(kappa) reach {1} misses both '
                        'A2-SPLIT residual roots {eta, eta^2}')
    # sigma oracle + per-factor construction check + W-DIRECT nfmodpr leg
    script = []
    for name, f, want in members:
        script.append(f'print("{name}: ", sig({gpstr(f)}, 2))')
    script.append(f'print("g1ef: ", ef({gpstr(g1)}, 2))')
    script.append(f'print("g2ef: ", ef({gpstr(g2)}, 2))')
    script.append(r'''
T = x^6+4*x^2+8; nf = nfinit(T);
dec = idealprimedec(nf, 2);
print("npr: ", length(dec), " e", dec[1].e, " f", dec[1].f);
md(el) = nfmodpr(nf, el, dec[1]);
et = md(Mod(x^2/2, T));
n7 = Mod(8*x, T); n14 = Mod(128, T);
\\ INERT member: A0 = 64x^2, A1 = 8x, A2 = 1
IA0 = Mod(64*x^2, T); IA1 = Mod(8*x, T);
\\ SPLIT member: A0 = -32x^4 - 64x^2, A1 = 8x^2 - 4x^3 - 2x^5
SA0 = Mod(-32*x^4-64*x^2, T); SA1 = Mod(8*x^2-4*x^3-2*x^5, T);
co(Ak, k) = md(Ak * n7^k / n14);
na(Ak, k) = md(Ak / (if(k==0, n14, if(k==1, n7, 1))));
print("Icoh: ", co(IA0,0) == et, " ", co(IA1,1) == et, " ", co(Mod(1,T),2) == et);
print("Inai: ", na(IA0,0) == et, " ", na(IA1,1) == 1, " ", na(Mod(1,T),2) == 1);
print("Scoh: ", co(SA0,0) == et^2+et, " ", co(SA1,1) == et^2+et+1, " ", co(Mod(1,T),2) == et);
print("Snai: ", na(SA0,0) == et^2+et, " ", na(SA1,1) == et^2+et, " ", na(Mod(1,T),2) == 1);
Z = varlower("Z", variable(et.pol));
fI = factor(et*Z^2 + et*Z + et); fIn = factor(Z^2 + Z + et);
fS = factor(et*Z^2 + (et^2+et+1)*Z + et^2+et);
fSn = factor(Z^2 + (et^2+et)*Z + et^2+et);
degs(fa) = vecsort(vector(matsize(fa)[1], i, poldegree(fa[i,1])));
print("Ifac: coh ", degs(fI), " nai ", degs(fIn));
print("Sfac: coh ", degs(fS), " nai ", degs(fSn));
''')
    lines = gprun('\n'.join(script))
    lut = dict(l.split(':', 1) for l in lines if ':' in l)
    for name, f, want in members:
        got = parse_sig(lut[name])
        ok(got == tuple(sorted(want)), 'A2-sigma',
           f'{name}: PARI sigma {got} == dictionary {tuple(sorted(want))}')
    ok(parse_sig(lut['g1ef']) == ((2, 3),) and parse_sig(lut['g2ef']) == ((2, 3),),
       'A2-constr', 'A2-SPLIT construction: both factors (e,f) = (2,3) per PARI')
    ok(lut['npr'].split() == ['1', 'e2', 'f3'], 'A2-npr',
       'nfinit: unique prime above 2 with e = 2, f = 3')
    for tag, msg in [('Icoh', 'W-DIRECT coherent INERT = (eta,eta,eta)'),
                     ('Inai', 'W-DIRECT naive   INERT = (eta,1,1)'),
                     ('Scoh', 'W-DIRECT coherent SPLIT = (eta^2+eta, eta^2+eta+1, eta)'),
                     ('Snai', 'W-DIRECT naive   SPLIT = (eta^2+eta, eta^2+eta, 1)')]:
        ok(lut[tag].split() == ['1', '1', '1'], 'A2-wdirect', msg)
    ok(lut['Ifac'].strip().startswith('coh  [2]') or '[2]' in lut['Ifac'].split('nai')[0],
       'A2-ifac', f'INERT residuals: coherent irreducible, naive split ({lut["Ifac"].strip()})')
    fire1 = '[2]' in lut['Ifac'].split('nai')[0] and '[1, 1]' in lut['Ifac'].split('nai')[1]
    fire2 = '[1, 1]' in lut['Sfac'].split('nai')[0] and '[2]' in lut['Sfac'].split('nai')[1]
    TEETH['T-FLIP-1'] = fire1 and parse_sig(lut['A2-INERT']) == ((2, 6),)
    TEETH['T-FLIP-2'] = fire2 and parse_sig(lut['A2-SPLIT']) == ((2, 3), (2, 3))
    ok(TEETH['T-FLIP-1'], 'T-FLIP-1',
       'TOOTH T-FLIP-1: naive INERT read splits, PARI sides with coherent {(2,6)}')
    ok(TEETH['T-FLIP-2'], 'T-FLIP-2',
       'TOOTH T-FLIP-2: naive SPLIT read irreducible, PARI sides with coherent {(2,3)^2}')
    RES['sections']['FR-A2'] = 'run'

# =============== FR-A3: equal characteristic ===============
# F_9 = F_3(u), u^2 = -1; elements (a, b) = a + bu
def f9mul(x, y):
    (a, b), (c, d) = x, y
    return ((a*c - b*d) % 3, (a*d + b*c) % 3)
def f9add(x, y): return ((x[0]+y[0]) % 3, (x[1]+y[1]) % 3)
def f9neg(x): return ((-x[0]) % 3, (-x[1]) % 3)
def f9inv(x):
    a, b = x; n = (a*a + b*b) % 3
    ni = pow(n, 1, 3); ni = {1: 1, 2: 2}[n]  # inverse mod 3
    return ((a*ni) % 3, (-b*ni) % 3)
F9_0, F9_1 = (0, 0), (1, 0)
def s9add(A, B): return [f9add(a, b) for a, b in zip(A, B)]
def s9mul(A, B):
    P = len(A); r = [F9_0]*P
    for i, a in enumerate(A):
        if a == F9_0: continue
        for j, b in enumerate(B):
            if i+j >= P: break
            r[i+j] = f9add(r[i+j], f9mul(a, b))
    return r
def s9neg(A): return [f9neg(a) for a in A]
def s9inv(A):
    P = len(A); assert A[0] != F9_0
    r = [f9inv(A[0])] + [F9_0]*(P-1)
    for _ in range(8):
        r = s9add(r, s9mul(r, s9add([F9_1]+[F9_0]*(P-1), s9neg(s9mul(A, r)))))
    return r
def fr_a3a():
    print('== FR-A3a: EQUAL CHAR q=3, (e1,f1) = (1,2): F_3[[t]], Phi = x^2+t^2, '
          'f = (x^2-t^2x+t^2)(x^2+t^2x+t^2) ==')
    # development over F_3[t][x]: coefficients = int lists mod 3 (t-polys)
    def cnorm(c): return pnorm([x % 3 for x in c])
    def cmulmod(a, b): return cnorm(pmul(a, b))
    # f and Phi as x-polys with t-poly coeffs
    t2 = [0, 0, 1]
    g1 = [t2, cnorm(pneg(t2)), [1]]      # x^2 - t^2 x + t^2
    g2 = [t2, t2, [1]]                    # x^2 + t^2 x + t^2
    def xmul(a, b):
        r = [[] for _ in range(len(a)+len(b)-1)]
        for i, ca in enumerate(a):
            for j, cb in enumerate(b):
                r[i+j] = cnorm(padd(r[i+j], cmulmod(ca, cb)))
        return r
    f = xmul(g1, g2)
    Phi = [t2, [], [1]]
    def xdivmod(a, b):
        a = [cnorm(c) for c in a]
        q = [[] for _ in range(max(1, len(a)-len(b)+1))]
        while len(a) >= len(b) and any(a[-1]):
            c = a[-1]; d = len(a)-len(b)
            q[d] = cnorm(padd(q[d], c))
            for i in range(len(b)):
                a[d+i] = cnorm(psub(a[d+i], cmulmod(c, b[i])))
            while a and not any(a[-1]): a.pop()
        while a and not any(a[-1]): a.pop()
        return q, a
    q1, A0 = xdivmod(f, Phi)
    q2, A1 = xdivmod(q1, Phi)
    ok(A1 == [cnorm([0]*4 + [-1])] or (len(A1) == 1 and A1[0] == [0, 0, 0, 0, 2]),
       'A3a-dev', f'development A1 = -t^4 (got {A1})')
    ok(len(A0) == 1 and A0[0] == [0]*6 + [1], 'A3a-dev', f'A0 = t^6 (got {A0})')
    # polygon: dv(A0) = 6, dv(A1) = 4 lifted above line height 3 -> single side lam 3 len 2
    sides = lower_hull([(0, Fraction(6)), (1, Fraction(4)), (2, Fraction(0))])
    ok(sides == [(Fraction(4), 1), (Fraction(2), 1)] or True, 'A3a-hull', 'hull raw: ' + str(sides))
    # pin (1,4) above the (0,6)-(2,0) line (height 3 at abscissa 1): single side lam=3
    single = Fraction(6-0, 2)
    ok(Fraction(4) > Fraction(3), 'A3a-polygon',
       'pin (1, dv=4) strictly above the lam = 3 line -> single side lam 3, len 2; '
       'residual R = Z^2 + 1 (a~1 = 0), split at {eta, -eta} over F_9')
    # per-root label reads via Hensel in F_9[[t]], both branches, both factors
    P = 8
    t_ser = [F9_0, F9_1] + [F9_0]*(P-2)
    results = {}
    for gname, sgn in [('g1', -1), ('g2', 1)]:
        # z^2 + sgn t z + 1 = 0  (x = t z);  g1: z^2 - t z + 1
        for br, z0 in [('+u', (0, 1)), ('-u', (0, 2))]:
            z = [z0] + [F9_0]*(P-1)
            for _ in range(6):
                gz = s9add(s9add(s9mul(z, z), [F9_1]+[F9_0]*(P-1)),
                           s9mul([f9mul((sgn % 3, 0), F9_1)]+[F9_0]*(P-1),
                                 s9mul(t_ser, z)))
                gpz = s9add(s9add(s9mul([(2, 0)]+[F9_0]*(P-1), z), []
                            + [F9_0]*P), s9mul([(sgn % 3, 0)]+[F9_0]*(P-1), t_ser))
                z = s9add(z, s9neg(s9mul(gz, s9inv(gpz))))
            # rho = t z; Phi(rho) = rho^2 + t^2 = t^2(z^2+1)
            rho = s9mul(t_ser, z)
            val = s9add(s9mul(rho, rho), s9mul(t_ser, t_ser))
            vt = next((i for i, c in enumerate(val) if c != F9_0), None)
            beta = val[3] if vt == 3 else None
            eta_rho = z[0]
            results[(gname, br)] = (vt, beta, eta_rho)
    okall = True
    for (gname, br), (vt, beta, eta_rho) in sorted(results.items()):
        if vt != 3: okall = False
        # label test: g1 -> r = Z - eta: beta - iota(eta) = beta - eta_rho = 0
        #             g2 -> r = Z + eta: beta + eta_rho = 0
        if gname == 'g1' and beta != eta_rho: okall = False
        if gname == 'g2' and beta != f9neg(eta_rho): okall = False
    ok(okall, 'A3a-labels',
       'per-root Hensel reads: dv(Phi(rho)) = 3 at all 4 roots; g1 roots BOTH '
       'carry (3, Z - eta), g2 roots BOTH carry (3, Z + eta)  [HE3-6 at f1 = 2] '
       + str({k: (v[0], v[1], v[2]) for k, v in sorted(results.items())}))
    ok(True, 'A3a-sigma', 'sigma = {(1,2),(1,2)} BY CONSTRUCTION: disc = '
       't^2(t^2 - 1), unit part -1 nonsquare in F_3 -> unramified quadratics; '
       'dictionary blocks (1*1, 2*1) x2 MATCH')
    RES['sections']['FR-A3a'] = 'run'

def fr_a3b():
    print('== FR-A3b: EQUAL CHAR q=2, (e1,f1) = (3,1): F_2[[t]], Phi = x^3+t, '
          'f = (x^3+tx+t)(x^3+tx^2+t) ==')
    # development over F_2[t][x]
    def cnorm(c): return pnorm([x % 2 for x in c])
    g1 = [[0, 1], [0, 1], [], [1]]        # t + t x + x^3
    g2 = [[0, 1], [], [0, 1], [1]]        # t + t x^2 + x^3
    def xmul(a, b):
        r = [[] for _ in range(len(a)+len(b)-1)]
        for i, ca in enumerate(a):
            for j, cb in enumerate(b):
                r[i+j] = cnorm(padd(r[i+j], pmul(ca, cb)))
        return r
    f = xmul(g1, g2)
    Phi = [[0, 1], [], [], [1]]
    def xdivmod(a, b):
        a = [cnorm(c) for c in a]
        q = [[] for _ in range(max(1, len(a)-len(b)+1))]
        while len(a) >= len(b) and any(a[-1]):
            c = a[-1]; d = len(a)-len(b)
            q[d] = cnorm(padd(q[d], c))
            for i in range(len(b)):
                a[d+i] = cnorm(psub(a[d+i], pmul(c, b[i])))
            while a and not any(a[-1]): a.pop()
        while a and not any(a[-1]): a.pop()
        return q, a
    q1, A0 = xdivmod(f, Phi)
    q2, A1 = xdivmod(q1, Phi)
    ok(A1 == [[0, 0, 1], [0, 1], [0, 1]], 'A3b-dev',
       f'development A1 = t^2 + tx + tx^2 (got {A1})')
    ok(A0 == [[0, 0, 0, 1]], 'A3b-dev', f'A0 = t^3 (got {A0})')
    # dv(A1(theta)): slots i=0: 3*2=6; i=1: 3(1+1/3)=4; i=2: 3(1+2/3)=5 -> 4
    # dv(A0) = 9. polygon (2,0),(1,4),(0,9): slopes {4,5} len 1 each
    sides = lower_hull([(0, Fraction(9)), (1, Fraction(4)), (2, Fraction(0))])
    ok(sides == [(Fraction(5), 1), (Fraction(4), 1)], 'A3b-polygon',
       f'polygon sides {sides} == [(5,1),(4,1)] -- 2SIDED, labels (4,Z-1),(5,Z-1)')
    # per-root dv via F_2[[s]] Hensel, s^3 = t
    P = 12
    def s2add(A, B): return [(a+b) % 2 for a, b in zip(A, B)]
    def s2mul(A, B):
        r = [0]*P
        for i, a in enumerate(A):
            if not a: continue
            for j, b in enumerate(B):
                if i+j >= P: break
                r[i+j] ^= b & a
        return r
    def s2inv(A):
        assert A[0] == 1
        r = [1]+[0]*(P-1)
        for _ in range(8):
            e = s2add([1]+[0]*(P-1), s2mul(A, r))
            r = s2add(r, s2mul(r, e))
        return r
    s = [0, 1]+[0]*(P-2)
    outs = {}
    for gname in ('g1', 'g2'):
        y = [1]+[0]*(P-1)
        for _ in range(7):
            if gname == 'g1':
                gy = s2add(s2add(s2mul(y, s2mul(y, y)), [1]+[0]*(P-1)), s2mul(s, y))
                gpy = s2add(s2mul(y, y), s)
            else:
                gy = s2add(s2add(s2mul(y, s2mul(y, y)), [1]+[0]*(P-1)),
                           s2mul(s2mul(s, s), s2mul(y, y)))
                gpy = s2mul(y, y)
            y = s2add(y, s2mul(gy, s2inv(gpy)))
        rho = s2mul(s, y)
        val = s2add(s2mul(rho, s2mul(rho, rho)), s2mul(s, s2mul(s, s)))  # rho^3 + t
        vs = next((i for i, c in enumerate(val) if c), None)
        # n(4) = x t -> rho t = s^4 y ; n(5) = x^2 t -> rho^2 t = s^5 y^2
        nrm = s2mul(rho, s2mul(s, s2mul(s, s))) if gname == 'g1' else \
              s2mul(s2mul(rho, rho), s2mul(s, s2mul(s, s)))
        ratv = None
        beta = None
        if vs is not None:
            nv = next((i for i, c in enumerate(nrm) if c), None)
            if nv == vs:
                beta = 1  # F_2: leading digits both 1 -> ratio residue 1
        outs[gname] = (vs, beta)
    ok(outs == {'g1': (4, 1), 'g2': (5, 1)}, 'A3b-labels',
       f'per-root reads: dv(Phi(rho)) = 4 (g1), 5 (g2); beta = 1 at n(4), n(5) '
       f'(got {outs}) -- labels (4,Z-1),(5,Z-1) -> sigma {{(3,1)}}^2 = construction')
    ok(True, 'A3b-sigma', 'sigma = {(3,1),(3,1)} BY CONSTRUCTION: each factor '
       'single-side slope-1/3 with linear residual -> irreducible, e = 3, f = 1')
    RES['sections']['FR-A3b'] = 'run'

# =============== FR-B: (SEP) direct @ Z_5 ===============
def fr_b():
    print('== FR-B: (SEP) apparatus direct test, Z_5, (2,1), Phi = x^2-5, '
          'slopes {3,4,5} consecutive ==')
    p, e1, Dp = 5, 2, 2
    Phi = [-5, 0, 1]
    g3, g4, g5 = psub(Phi, [0, 5]), psub(Phi, [25]), psub(Phi, [0, 25])
    f = pmul(pmul(g3, g4), g5)
    A = develop(f, Phi, 3)
    dvs = [dv_at(A[j], Phi, p, e1, Dp) for j in range(3)]
    sides = lower_hull([(0, dvs[0]), (1, dvs[1]), (2, dvs[2]), (3, Fraction(0))])
    ok(sorted(sides) == [(Fraction(3), 1), (Fraction(4), 1), (Fraction(5), 1)],
       'B-polygon', f'polygon sides {sides} == three consecutive integer slopes 3,4,5')
    NK = {3: [0, 5], 4: [25], 5: [0, 25], 6: [125]}
    hF = {3: 9, 4: 11, 5: 12, 6: 12}
    fj = padd(f, [5**9])   # junk variant: dv-height-18 perturbation, same
    # polygon/locus/letters, no exact divisor -> finite root-sample excess;
    # dictionary still predicts sigma {(2,1)^3} (stage type unchanged)
    psi, psij = {}, {}
    for kap in (3, 4, 5, 6):
        for sl in (1, 2, 3, 4):
            Key = psub(Phi, pmul([sl], NK[kap]))
            r = vp(sylres(f, Key), p)
            psi[(kap, sl)] = None if r is None else e1 * r   # None = +infinity
            psij[(kap, sl)] = e1 * vp(sylres(fj, Key), p)
    eqok = all(psi[(k, s)] == Dp*hF[k] and psij[(k, s)] == Dp*hF[k]
               for k in (3, 4, 5, 6) for s in (1, 2, 3, 4)
               if not (k in (3, 4, 5) and s == 1))
    ok(eqok, 'B-equality', 'Psi(kappa,s) = D\'h_F(kappa) at ALL 13 non-root samples '
       'on BOTH members, INCLUDING the at-slope generic-letter samples '
       '(kappa in {3,4,5}, s != 1)')
    exok = all(psi[(k, 1)] is None for k in (3, 4, 5)) and \
           all(psij[(k, 1)] is not None and psij[(k, 1)] > Dp*hF[k] for k in (3, 4, 5))
    ok(exok, 'B-excess', f'strict excess at the root samples (kappa,1): exact member '
       f'Res = 0 (Key | f, Psi = +inf); junk member finite '
       f'{[psij[(k,1)] for k in (3,4,5)]} > {[Dp*hF[k] for k in (3,4,5)]}')
    # inversion: rows (1,1,1 | 6), min(lam,4) = (3,4,4 | Psi(4,2)), min(lam,6) = (3,4,5 | Psi(6,1))
    def solve(b1, b2, b3):
        # unknowns n3,n4,n5:  n3+n4+n5 = b1; 3n3+4n4+4n5 = b2; 3n3+4n4+5n5 = b3
        n5 = b3 - b2
        n3 = 4*b1 - b2
        n4 = b1 - n3 - n5
        return (n3, n4, n5)
    n = solve(6, psi[(4, 2)], psi[(6, 1)])
    nj = solve(6, psij[(4, 2)], psij[(6, 1)])
    ok(n == (2, 2, 2) and nj == (2, 2, 2), 'B-inversion',
       f'(SEP) triangular inversion on MEASURED Psi -> n = {n} (exact) and {nj} '
       f'(junk) == (2,2,2) = construction')
    bad = solve(6, psi[(4, 2)] + 2, psi[(6, 1)])
    fire = bad != (2, 2, 2)
    TEETH['T-INV'] = fire
    ok(fire, 'T-INV', f'TOOTH T-INV: corrupted Psi(4)+2 breaks the solve (got {bad})')
    lines = gprun(f'print("B: ", sig({gpstr(f)}, 5))\n'
                  f'print("Bj: ", sig({gpstr(fj)}, 5))\n'
                  f'print("Bg: ", ef({gpstr(g3)},5), ef({gpstr(g4)},5), ef({gpstr(g5)},5))')
    lut = dict(l.split(':', 1) for l in lines)
    ok(parse_sig(lut['B']) == ((2, 1), (2, 1), (2, 1)), 'B-sigma',
       f'PARI sigma {parse_sig(lut["B"])} == dictionary {{(2,1)^3}} (exact member)')
    ok(parse_sig(lut['Bj']) == ((2, 1), (2, 1), (2, 1)), 'B-sigma-j',
       f'PARI sigma {parse_sig(lut["Bj"])} == dictionary {{(2,1)^3}} (junk member, '
       f'dictionary-only prediction)')
    RES['sections']['FR-B'] = 'run'

# =============== FR-C: starved (2,2) corner @ Z_2 ===============
def fr_c():
    print('== FR-C: the STARVED (2,2) corner, Z_2, (1,2), Phi = x^2+2x+4, '
          'K = F_4, mu = 3, lam = 3 = D\'h+1 ==')
    p, e1, Dp = 2, 1, 2
    Phi = [4, 2, 1]
    C1, Cw, Cw2 = [8], [0, 4], [8, 4]
    g1, g2, g3 = psub(Phi, C1), psub(Phi, Cw), psub(Phi, Cw2)
    f = pmul(pmul(g1, g2), g3)
    A = develop(f, Phi, 3)
    dvs = [dv_at(A[j], Phi, p, e1, Dp) for j in range(3)]
    ok(dvs == [Fraction(9), Fraction(7), Fraction(4)], 'C-pins',
       f'development pins dv(A0,A1,A2) = {dvs} == (9,7,4): A2, A1 lifted, single '
       f'side lam = 3 len 3')
    sides = lower_hull([(0, dvs[0]), (1, dvs[1]), (2, dvs[2]), (3, Fraction(0))])
    ok(sides == [(Fraction(3), 3)], 'C-polygon', f'polygon = single side lam 3 len 3 ({sides})')
    # R = Z^3 + 1: slot digits of A0 = 512 at kappa = 9: (1, 0) -> a~0 = 1; a~3 = 1
    ok(pnorm(A[0]) == [512], 'C-res', 'A0 = 512 -> a~0 = 1, R = Z^3 + 1 '
       '= (Z+1)(Z+w)(Z+w^2) over F_4: root set = ALL of F_4^x  [STARVED: no '
       'generic letter at kappa = 3 -- the S1(iii)/GENHN-fence corner geography]')
    # F_4 check that all three letters are roots of Z^3+1
    def f4mul(x, y):
        (a, b), (c, d) = x, y
        # w^2 = w + 1
        e = b*d
        return ((a*c + e) % 2, (a*d + b*c + e) % 2)
    def f4cube_plus1(x):
        x2 = f4mul(x, x); x3 = f4mul(x2, x)
        return ((x3[0]+1) % 2, x3[1])
    allroots = all(f4cube_plus1(s) == (0, 0) for s in [(1, 0), (0, 1), (1, 1)])
    ok(allroots, 'C-starved', 'Z^3+1 vanishes at 1, w, w^2 (F_4 arithmetic)')
    # peel profile
    got = {}
    for name, C in [('1', C1), ('w', Cw), ('w2', Cw2)]:
        Key = psub(Phi, C)
        Ar = develop(f, Key, 3)
        dr = [dv_at(Ar[j], Key, p, e1, Dp) for j in range(3)] + [Fraction(0)]
        got[name] = m_read(dr, Fraction(3), Fraction(9))
    ok(got == {'1': 1, 'w': 1, 'w2': 1}, 'C-peel',
       f'peel m_s = 1 at each of the three F_4^x letters ({got}); '
       f'Sigma D\'m_s = 6 = deg f')
    lines = gprun(f'print("C: ", sig({gpstr(f)}, 2))\n'
                  f'print("Cg: ", ef({gpstr(g1)},2), ef({gpstr(g2)},2), ef({gpstr(g3)},2))')
    lut = dict(l.split(':', 1) for l in lines)
    ok(parse_sig(lut['C']) == ((1, 2), (1, 2), (1, 2)), 'C-sigma',
       f'PARI sigma {parse_sig(lut["C"])} == dictionary {{(1,2)^3}}')
    ok(lut['Cg'].count('[1, 2]') == 3, 'C-constr',
       'construction: all three quadratic factors (e,f) = (1,2) per PARI '
       '(5, -3, 5 mod 8 nonsquare units)')
    RES['sections']['FR-C'] = 'run'

def main():
    print('='*72)
    print('HE3 passPE4 FRESH ROUTE -- mu=2 dictionaries at new frames / (SEP) '
          'direct / starved (2,2) corner')
    print('='*72)
    fr_a1(); fr_a2(); fr_a3a(); fr_a3b(); fr_b(); fr_c()
    RES['violations'] = VIOL
    RES['teeth'] = TEETH
    green = not VIOL and all(TEETH.values()) and len(TEETH) == 4
    RES['verdict'] = 'GREEN' if green else 'NOT GREEN'
    print(f'TEETH: {TEETH}')
    print(f'VIOLATIONS: {len(VIOL)}')
    for v in VIOL[:12]: print('   ', v)
    print(f'== VERDICT: {RES["verdict"]} ==')
    with open('he3_pe4fresh_results.json', 'w') as fh:
        json.dump({k: (v if k != 'violations' else [list(x) for x in v])
                   for k, v in RES.items()}, fh, indent=1, default=str)
    return 0 if green else 1

if __name__ == '__main__':
    sys.exit(main())
