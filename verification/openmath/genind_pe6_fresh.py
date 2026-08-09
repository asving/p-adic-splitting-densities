"""GENIND passPE6 FRESH ROUTE (hostile verifier; runs in /tmp only).

Route disclosed: differs from seal (n<=5 rosters, 163,536), PE1
(symbolic+exact n<=5), PE2 (n=6 census + first n=6 PARI), r2 supp
(M6 fibration 2,128,163), PE3 (M7T n=7 + TWOCHILD + SS6, 705,133),
PE4 (PSTEEP + THREECHILD + N8MIX, 6,507), PE5 (NINEMIX n=9 +
SAMESIDE co-children + STEEPSCAN, 109,146).

THIS route: the r5's f-first entry laws (6k same-side / 2k+4h
distinct-side) attacked by CONSTRUCTION -- the FIRST MACHINE
REALIZATION of the same-side f-first genre (disclosed at S15 as
machine-unrealized corpus-wide), EXHAUSTIVE at its first-visible
window; plus BOTH distinct-side f-first cells, including the
never-realized f-first-STEEPER cap regime (a composite psi^2 block
STEEPER than the extracted child -- SS6/PE5 realized only E-type
steeper stages); plus the child+E family's k=2 boundary cell (the
r5 grammar's "k >= 2 gives >= 6" cell, never realized -- M6 is k=1).

ALL PREDICTIONS HAND-DERIVED BEFORE THIS RUN (derivations in the
PE6 report S7). Genre grammar used (re-derived independently):
m=6 mixed = one (2,1) child at integer slope k + one composite
block with e*mu*degpsi = 4, i.e. (e,degpsi,mu) in {(2,1,2) E-type,
(1,2,2) f-first}; no decided pieces fit the 2+4=6 abscissa budget.

FR-A SSF (SAME-SIDE F-FIRST; q=2, m=6, k=1, N=8, EXHAUSTIVE):
  one side (0,6)-(6,0) slope 1, residual (y-w)^2 psi(y)^2 with
  w=1, psi=y^2+y+1 (both FORCED at q=2); over F_2 the residual is
  y^6+1 -- every interior lattice pin is the J-D0-degenerate 0
  (v(a_j) >= 7-j for j=1..5), digit6(a0)=1. Free digits: a0 h7 (1),
  a_j h(7-j)..h7 (j+1 each): LOCUS = 2^21 = 2,097,152 exhaustive.
  Prereg: v(a0) = 6 = 6k (THE 6k LAW); sig [(0,6,1,1)] all; top
  event ('CS', ('CSOTHER',6,(0,6),1,2,2,1)) all (key from
  cs_genre_key source: m=6 -> CSOTHER, gam=2, mu=2); verdict CS
  all; extract_child(k=1,z=1) Wc = N-6 = 2 all (D = 2*1 +
  4*min(1,1) = 6 = min_j(v(a_j)+j), same-slope: cap degenerate);
  cofactor reduction Bbar = psi^2 = [1,0,1,0,1] all (the same-side
  COMPOSITE co-block of [r5, PE5-m2], repeated NON-linear factor);
  its child-recenter shift B(y+1) has constant residue psi(1)^2 =
  1 != 0 (coprime to ybar -- psi has no F_q root) all; child-class
  map (b0,b1 mod pi^2) ONTO 4 with CONSTANT fiber 2^19 = 524,288
  (GENIND-6(c); drivers a4h3/a5h2 have images y^4,y^5 mod (y-1)^2
  = (1,0),(1,1), det z^8 != 0); child-DEC count (digit1(b0)=1) =
  2^20 = 1,048,576.
FR-A2 (N=7 EXHAUSTIVE, 2^15 = 32,768): the first-visible window
  (v(a0) = 6 = N-1): same key/sig all; Wc = 1; single child class.
FR-A3 (N=6 floor): the pinned frame has v(a0) = 6 >= N: 20 members
  all DRAIN (the N >= 7 visibility floor of the 6k law).
FR-A4 (k=2 cell of the 6k law; N=14, 200 samples): v(a0) = 12 =
  6k; sig [(0,6,1,2)]; key ('CSOTHER',6,(0,6),1,2,2,2); Wc =
  14-12 = 2; Bbar = psi^2.
FR-A5 (char p mirror, Fqt): (Fqt q=2 N=8, 200 samples) + (Fqt q=3
  N=8, 100 samples, letters (w,psi) random per member): same
  key/sig/Wc=2/Bbar/shift-coprime as the Zp cells.
FR-B (q=3 Zp N=8, ALL SIX letter slices (w,psi), 60 samples each):
  psi in {y^2+1, y^2+y+2, y^2+2y+2}, w in {1,2}; residual
  (y-w)^2 psi(y)^2 has live odd-q pins; same key/sig; Wc = 2;
  Bbar = psi^2 coeffs; shift constant psi(w)^2 != 0 (the [r5]
  parenthetical's psi(zhat) != 0, machine-real at odd q); exercises
  the reader's gcd branch (dC != 0), vs the p=2 Frobenius branch.
FR-C DS-A (DISTINCT-SIDE, child STEEPER: k=2, h=1 -- the 2k+4h
  minimum cell v(a0)=8, N=9 floor; run at N=10): hull
  (0,8)-(2,4)-(6,0), child on [0,2] slope 2 (residual
  psi(0)^2 (y-w)^2), psi^2-block on [2,6] slope 1. 200 samples q=2
  + 6x20 q=3. Prereg: v(a0) = 8 = 2k+4h; sig [(0,2,1,2),(2,6,1,1)];
  key ('CSOTHER',6,(2,6),1,2,2,1); extract(k=2,z=w): D = 2*2 +
  4*min(1,2) = 8 (min_j: j=0: 8 = j=2: 4+4), Wc = 2; cofactor =
  DEGREE-DROP form (shallower co-block): Bbar = [psi(0)^2 w^0...] =
  constant psi(0)^2, all higher residues 0.
FR-D DS-B (DISTINCT-SIDE, f-first block STEEPER: k=1, h=2 --
  v(a0) = 2k+4h = 10, N=11 floor; run at N=11): hull
  (0,10)-(4,2)-(6,0), psi^2-block on [0,4] slope 2 (residual
  w^2 psi(y)^2), child on [4,6] slope 1 (residual (y-w)^2). THE NEW
  CAP REGIME: a COMPOSITE (f-first) co-block steeper than the
  extracted child -- capped D = 2*1 + 4*min(2,1) = 6 (min_j: j=4:
  2+4 = j=5: 1+5 = j=6: 6); UNCAPPED (own slope-mass) would say
  2+8 = 10 -> Wc = 1 (single child class). 300 samples q=2 + 6x20
  q=3. Prereg: sig [(0,4,1,2),(4,6,1,1)]; key
  ('CSOTHER',6,(0,4),1,2,2,2); Wc = 11-6 = 5; cofactor = COLLAPSE
  form (steeper co-block leaves the reduction): Bbar = y^4 =
  [0,0,0,0,1], child-recenter shift constant w^4 != 0.
  BOX q=2: a4 heights {3,4,5,6} x a5 heights {2,3,4,5} (2^8 = 256
  members over the base member): child classes mod pi^5 all
  DISTINCT = BIJECTION onto the full 256-class window-5 space
  (first-order images per scaled order h: y^4 -> (z^4, 4z^3),
  y^5 -> (z^5, 5z^4) in the {1,(y-z)} basis; det = z^8 != 0 BOTH
  characteristics; strictly triangular across orders). BOX q=3:
  a4{3,4} x a5{2,3} (3^4 = 81) -> 81 DISTINCT classes truncated
  mod pi^3.
FR-E CHILD+E k=2 BOUNDARY CELL (the r5 grammar's first family at
  its "k >= 2 gives >= 6" boundary; never realized -- M6 is k=1):
  hull (0,6)-(2,2)-(6,0), child on [0,2] slope 2, E-block (e=2,
  h=1) on [2,6] slope 1/2; v(a0) = 2k+2h = 6, N=7 floor; run at
  N=8: 100 samples q=2 + 60 q=3. Prereg: sig
  [(0,2,1,2),(2,6,2,1)]; key ('CSOTHER',6,(2,6),2,1,2,1);
  extract(k=2,z=w): D = 4 + 4*min(1/2,2) = 6, Wc = 2.
FR-F PARI (mechanism-free; global nfinit/idealprimedec on
  irreducible disc!=0 lifts, PARI never sees the reader):
  (i) SSF child-DEC members (digit1(b0)=1 => child = ramified
  quadratic CERTIFIED): 15 lifts q=2 + 10 q=3: odd-f primes =
  exactly {(e,f) = (2,1)} (the child), even-f prime mass
  Sum e*f = 4 (the psi-block: residue field contains F_{q^2});
  factorpadic root-valuation partition {1: 6}.
  (ii) DS-B 10 lifts q=2: partition {2: 4, 1: 2} (4 roots at val
  2 = the steeper psi^2-block, 2 at val 1 = the child) -- the cap
  regime's fracture read confirmed with no shared mechanism.
FR-G TOOTH (preregistered fire count): 10 random SSF members at
  N=8, corrupt the single nonzero pin (digit6(a0): 1 -> 0,
  digit7(a0) := 1): v(a0) = 7, gcd(6,7)=1 forces the one-side
  e=6 g=1 read -> top event ('DEC',) with sigma ((6,1),): 10/10
  exit the genre.

Sealed runner imported READ-ONLY, md5-asserted. Exact integers.
"""
import sys, os, json, time, hashlib, random
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.append(os.path.expanduser(
    '~/.local/lib/python3.10/site-packages'))
RUNNER_MD5 = 'e7ca150b1b5cb13ad4f3350ac776aca2'
md5 = hashlib.md5(open(os.path.join(HERE, 'genind_checks.py'), 'rb')
                  .read()).hexdigest()
assert md5 == RUNNER_MD5, 'sealed runner md5 mismatch: %s' % md5
import genind_checks as G

VIOL, TALLY, T0 = [], {}, time.time()


def say(m):
    print(m)
    sys.stdout.flush()


def note(f, n=1):
    TALLY[f] = TALLY.get(f, 0) + n


def viol(f, d):
    VIOL.append((f, str(d)[:220]))
    say('VIOLATION [%s] %s' % (f, d))


def sig_of(R, N, st, m):
    return [(s[0], s[2], s[4], s[5]) for s in G.sides_of(R, N, st, m)]


def kp_shift_const(R, B, w):
    """residue at 0 of the constant coeff of B(y+w)."""
    Bs = G.poly_shift(R, list(B), R.lift(w))
    return R.res(Bs[0], 0)


def psi2_coeffs(psi, p):
    return G.kp_mul(list(psi), list(psi), p)


def check_member(R, N, st, m, want_sig, want_key, k, z, want_Wc,
                 want_Bbar, shift_z, tag, collect=None):
    """the shared per-member gate; returns child (or None on sig/key
    violation)."""
    p = R.p
    if sig_of(R, N, st, m) != want_sig:
        viol(tag, 'sig %s' % (sig_of(R, N, st, m),))
        return None
    ev = []
    ctx = {'p': p, 'cs_events': []}
    v, _ = G.read_cluster(R, N, list(st), ctx, top_events=ev)
    if v != 'CS' or ev[0] != ('CS', want_key):
        viol(tag, 'verdict/key %s %s' % (v, ev))
        return None
    child, Wc = G.extract_child(R, N, list(st), m, k, z, p)
    if Wc != want_Wc:
        viol(tag, 'Wc %d != %d [law refuted]' % (Wc, want_Wc))
    _, _, B, _ = G.extract_child.last
    Bbar = [R.res(c, 0) for c in B]
    while Bbar and Bbar[-1] == 0:
        Bbar.pop()
    if Bbar != want_Bbar:
        viol(tag, 'Bbar %s != %s' % (Bbar, want_Bbar))
    if shift_z is not None:
        sc = kp_shift_const(R, B, shift_z)
        if sc == 0:
            viol(tag, 'shifted cofactor constant = 0 (not coprime)')
    if collect is not None:
        collect(child, Wc)
    note(tag)
    return child


# ------------------------------------------------------------ builders
def build(R, p, N, pins, free, rng):
    """pins: list of (j, height, digit); free: list of (j, [heights]).
    Returns coeff list a0..a5 (m=6)."""
    st = [R.zero()] * 6
    for (j, h, d) in pins:
        if d % p:
            st[j] = R.add(st[j], R.mul(R.rint(d), R.pipw(h)))
    for (j, hs) in free:
        for h in hs:
            d = rng.randrange(p)
            if d:
                st[j] = R.add(st[j], R.mul(R.rint(d), R.pipw(h)))
    return st


def ssf_spec(p, N, k, w, psi):
    """same-side f-first pins/free at slope k."""
    Rc = G.kp_mul(G.kp_mul([(-w) % p, 1], [(-w) % p, 1], p),
                  psi2_coeffs(psi, p), p)
    pins = [(j, (6 - j) * k, Rc[j]) for j in range(6)]
    free = [(j, list(range((6 - j) * k + 1, N))) for j in range(6)]
    return pins, free


def dsa_spec(p, N, w, psi):
    """distinct-side, child steeper (k=2, h=1)."""
    p0 = psi[0]
    L = G.kp_mul([(-w) % p, 1], [(-w) % p, 1], p)     # (y-w)^2
    L = [(c * p0 * p0) % p for c in L]
    P2 = psi2_coeffs(psi, p)
    pins = [(0, 8, L[0]), (1, 6, L[1]), (2, 4, L[2]),
            (3, 3, P2[1]), (4, 2, P2[2]), (5, 1, P2[3])]
    hts = {0: 8, 1: 6, 2: 4, 3: 3, 4: 2, 5: 1}
    free = [(j, list(range(hts[j] + 1, N))) for j in range(6)]
    return pins, free


def dsb_spec(p, N, w, psi):
    """distinct-side, f-first block steeper (k=1, h=2)."""
    P2 = psi2_coeffs(psi, p)
    W2 = [(c * w * w) % p for c in P2]                # w^2 psi^2
    pins = [(j, 10 - 2 * j, W2[j]) for j in range(5)]
    pins.append((5, 1, (-2 * w) % p))
    hts = {j: 10 - 2 * j for j in range(5)}
    hts[5] = 1
    free = [(j, list(range(hts[j] + 1, N))) for j in range(6)]
    return pins, free


def ecell_spec(p, N, w, z):
    """child+E family at its k=2 boundary (h=1)."""
    pins = [(0, 6, (z * z * w * w) % p), (1, 4, (-2 * z * z * w) % p),
            (2, 2, (z * z) % p), (4, 1, (-2 * z) % p)]
    hts = {0: 6, 1: 4, 2: 2, 3: 1, 4: 1, 5: 0}
    # off-lattice budgets: v(a3) >= 2, v(a5) >= 1
    free = [(0, list(range(7, N))), (1, list(range(5, N))),
            (2, list(range(3, N))), (3, list(range(2, N))),
            (4, list(range(2, N))), (5, list(range(1, N)))]
    return pins, free


PSI2_2 = [1, 1, 1]                       # y^2+y+1 over F_2
PSIS_3 = [[1, 0, 1], [2, 1, 1], [2, 2, 1]]   # irreducible /F_3


# ------------------------------------------------------------ FR-A
def fra_exhaustive():
    p, N = 2, 8
    R = G.Zp(p, N)
    key = ('CSOTHER', 6, (0, 6), 1, 2, 2, 1)
    sig = [(0, 6, 1, 1)]
    bbar = [1, 0, 1, 0, 1]
    # bit layout: (j, height) free slots
    slots = [(0, 7)]
    for j in range(1, 6):
        slots += [(j, h) for h in range(7 - j, 8)]
    assert len(slots) == 21
    adds = [(j, 1 << h) for (j, h) in slots]
    base = [0] * 6
    base[0] = 1 << 6
    hist = {}
    decs = 0
    tot = 0
    for idx in range(1 << 21):
        st = list(base)
        x = idx
        for (j, pw) in adds:
            if x & 1:
                st[j] += pw
            x >>= 1
        cls = [None]

        def coll(child, Wc, cls=cls):
            cls[0] = (child[0] % 4, child[1] % 4)
        ch = check_member(R, N, st, 6, sig, key, 1, 1, 2, bbar, 1,
                          'FRA-ssf-exh', collect=coll)
        if ch is None:
            continue
        hist[cls[0]] = hist.get(cls[0], 0) + 1
        if (ch[0] >> 1) & 1:
            decs += 1
        tot += 1
        if tot % 500000 == 0:
            say('   ... %d members [%.1fs]' % (tot, time.time() - T0))
    fib = sorted(set(hist.values()))
    if tot != 1 << 21:
        viol('FRA-ssf-exh', 'locus %d != 2^21' % tot)
    if len(hist) != 4 or fib != [1 << 19]:
        viol('FRA-ssf-exh', 'classes %d fibers %s != 4 x [2^19]'
             % (len(hist), fib))
    if decs != 1 << 20:
        viol('FRA-ssf-exh', 'child-DEC %d != 2^20' % decs)
    say('-- FRA-ssf-exh (2,6,N=8) SAME-SIDE F-FIRST, first machine '
        'realization: locus %d, ONTO %d fibers %s, child-DEC %d '
        '[%.1fs]' % (tot, len(hist), fib, decs, time.time() - T0))


def fra2_n7():
    p, N = 2, 7
    R = G.Zp(p, N)
    key = ('CSOTHER', 6, (0, 6), 1, 2, 2, 1)
    sig = [(0, 6, 1, 1)]
    bbar = [1, 0, 1, 0, 1]
    slots = []
    for j in range(1, 6):
        slots += [(j, h) for h in range(7 - j, 7)]
    assert len(slots) == 15
    adds = [(j, 1 << h) for (j, h) in slots]
    base = [0] * 6
    base[0] = 1 << 6
    hist = {}
    tot = 0
    for idx in range(1 << 15):
        st = list(base)
        x = idx
        for (j, pw) in adds:
            if x & 1:
                st[j] += pw
            x >>= 1
        cls = [None]

        def coll(child, Wc, cls=cls):
            cls[0] = (child[0] % 2, child[1] % 2)
        ch = check_member(R, N, st, 6, sig, key, 1, 1, 1, bbar, 1,
                          'FRA2-ssf-N7', collect=coll)
        if ch is None:
            continue
        hist[cls[0]] = hist.get(cls[0], 0) + 1
        tot += 1
    if tot != 1 << 15 or len(hist) != 1:
        viol('FRA2-ssf-N7', 'locus %d classes %d' % (tot, len(hist)))
    say('-- FRA2-ssf-N7: first-visible window, locus %d exhaustive, '
        'Wc=1, single class [%.1fs]' % (tot, time.time() - T0))


def fra3_floor():
    p, N = 2, 6
    R = G.Zp(p, N)
    rng = random.Random(606)
    for i in range(20):
        st = [0] * 6
        for j in range(1, 6):
            for h in range(7 - j, 6):
                if rng.randrange(2):
                    st[j] += 1 << h
        ev = []
        ctx = {'p': p, 'cs_events': []}
        v, _ = G.read_cluster(R, N, list(st), ctx, top_events=ev)
        if v != 'DRAIN' or ev[0] != ('DRAIN',):
            viol('FRA3-floor', 'verdict %s %s' % (v, ev))
        note('FRA3-floor')
    say('-- FRA3-floor: N=6 sits below the 6k law floor: DRAIN 20/20 '
        '[%.1fs]' % (time.time() - T0))


def fra4_k2():
    p, N = 2, 14
    R = G.Zp(p, N)
    rng = random.Random(707)
    key = ('CSOTHER', 6, (0, 6), 1, 2, 2, 2)
    sig = [(0, 6, 1, 2)]
    bbar = [1, 0, 1, 0, 1]
    pins, free = ssf_spec(p, N, 2, 1, [1, 1, 1])
    for i in range(200):
        st = build(R, p, N, pins, free, rng)
        if R.val(st[0], N) != 12:
            viol('FRA4-k2', 'v(a0) != 12 = 6k')
        check_member(R, N, st, 6, sig, key, 2, 1, 2, bbar, 1,
                     'FRA4-k2')
    say('-- FRA4-k2 (2,6,N=14): the 6k law at k=2 (v(a0)=12, Wc=2), '
        '200 samples [%.1fs]' % (time.time() - T0))


def fra5_fqt():
    for (p, ns) in ((2, 200), (3, 100)):
        R = G.Fqt(p, 8)
        rng = random.Random(808 + p)
        key = ('CSOTHER', 6, (0, 6), 1, 2, 2, 1)
        sig = [(0, 6, 1, 1)]
        tag = 'FRA5-fqt-q%d' % p
        for i in range(ns):
            if p == 2:
                w, psi = 1, [1, 1, 1]
            else:
                w, psi = rng.choice((1, 2)), rng.choice(PSIS_3)
            pins, free = ssf_spec(p, 8, 1, w, psi)
            st = build(R, p, 8, pins, free, rng)
            check_member(R, 8, st, 6, sig, key, 1, w, 2,
                         psi2_coeffs(psi, p), w, tag)
        say('-- %s: char-p mirror, %d samples, Wc=2 exact [%.1fs]'
            % (tag, ns, time.time() - T0))


def frb_q3():
    p, N = 3, 8
    R = G.Zp(p, N)
    rng = random.Random(909)
    key = ('CSOTHER', 6, (0, 6), 1, 2, 2, 1)
    sig = [(0, 6, 1, 1)]
    for w in (1, 2):
        for psi in PSIS_3:
            pins, free = ssf_spec(p, N, 1, w, psi)
            for i in range(60):
                st = build(R, p, N, pins, free, rng)
                if R.val(st[0], N) != 6:
                    viol('FRB-q3', 'v(a0) != 6')
                check_member(R, N, st, 6, sig, key, 1, w, 2,
                             psi2_coeffs(psi, p), w, 'FRB-q3')
    say('-- FRB-q3: all 6 letter slices x 60, gcd-branch reader, '
        'Wc=2, Bbar=psi^2, psi(w)!=0 [%.1fs]' % (time.time() - T0))


# ------------------------------------------------------------ FR-C/D/E
def frc_dsa():
    for (p, ns, combos) in ((2, 200, [(1, [1, 1, 1])]),
                            (3, 20, [(w, ps) for w in (1, 2)
                                     for ps in PSIS_3])):
        R = G.Zp(p, 10)
        rng = random.Random(111 + p)
        key = ('CSOTHER', 6, (2, 6), 1, 2, 2, 1)
        sig = [(0, 2, 1, 2), (2, 6, 1, 1)]
        tag = 'FRC-dsa-q%d' % p
        for (w, psi) in combos:
            pins, free = dsa_spec(p, 10, w, psi)
            bbar = [(psi[0] * psi[0]) % p]
            for i in range(ns):
                st = build(R, p, 10, pins, free, rng)
                if R.val(st[0], 10) != 8:
                    viol(tag, 'v(a0) != 8 = 2k+4h')
                check_member(R, 10, st, 6, sig, key, 2, w, 2,
                             bbar, w, tag)
        say('-- %s: distinct-side minimum cell (v(a0)=8), degree-'
            'drop cofactor, Wc=2 [%.1fs]' % (tag, time.time() - T0))


def frd_dsb():
    for (p, ns, combos) in ((2, 300, [(1, [1, 1, 1])]),
                            (3, 20, [(w, ps) for w in (1, 2)
                                     for ps in PSIS_3])):
        R = G.Zp(p, 11)
        rng = random.Random(222 + p)
        key = ('CSOTHER', 6, (0, 4), 1, 2, 2, 2)
        sig = [(0, 4, 1, 2), (4, 6, 1, 1)]
        bbar = [0, 0, 0, 0, 1]
        tag = 'FRD-dsb-q%d' % p
        classes = set()
        for (w, psi) in combos:
            pins, free = dsb_spec(p, 11, w, psi)
            for i in range(ns):
                st = build(R, p, 11, pins, free, rng)
                if R.val(st[0], 11) != 10:
                    viol(tag, 'v(a0) != 10 = 2k+4h')
                cls = [None]

                def coll(child, Wc, cls=cls):
                    cls[0] = tuple(c % p ** 5 for c in child)
                check_member(R, 11, st, 6, sig, key, 1, w, 5,
                             bbar, w, tag, collect=coll)
                classes.add(cls[0])
        if len(classes) < 2:
            viol(tag, 'single child class (uncapped reading?)')
        say('-- %s: f-first-STEEPER cap regime: Wc=5 (uncapped 1), '
            '%d distinct window-5 classes seen, collapse cofactor '
            'y^4 [%.1fs]' % (tag, len(classes), time.time() - T0))


def frd_box():
    for (p, hs4, hs5, trunc, want) in (
            (2, (3, 4, 5, 6), (2, 3, 4, 5), 5, 256),
            (3, (3, 4), (2, 3), 3, 81)):
        R = G.Zp(p, 11)
        key = ('CSOTHER', 6, (0, 4), 1, 2, 2, 2)
        sig = [(0, 4, 1, 2), (4, 6, 1, 1)]
        w, psi = 1, ([1, 1, 1] if p == 2 else [1, 0, 1])
        pins, _ = dsb_spec(p, 11, w, psi)
        rng0 = random.Random(0)
        base = build(R, p, 11, pins, [], rng0)
        tag = 'FRD-box-q%d' % p
        seen = set()
        tot = 0
        for m4 in range(p ** len(hs4)):
            for m5 in range(p ** len(hs5)):
                st = list(base)
                x4, x5 = m4, m5
                for h in hs4:
                    st[4] = (st[4] + (x4 % p) * p ** h) % p ** 11
                    x4 //= p
                for h in hs5:
                    st[5] = (st[5] + (x5 % p) * p ** h) % p ** 11
                    x5 //= p
                if sig_of(R, 11, st, 6) != sig:
                    viol(tag, 'box member left genre')
                    continue
                child, Wc = G.extract_child(R, 11, st, 6, 1, w, p)
                if Wc != 5:
                    viol(tag, 'box Wc %d != 5' % Wc)
                seen.add(tuple(c % p ** trunc for c in child))
                tot += 1
                note(tag)
        if len(seen) != want or tot != want:
            viol(tag, 'box %d/%d != %d (bijection refuted)'
                 % (len(seen), tot, want))
        say('-- %s: driving box ONTO %d/%d distinct classes '
            '(bijection) [%.1fs]' % (tag, len(seen), want,
                                     time.time() - T0))


def fre_ecell():
    for (p, ns, combos) in ((2, 100, [(1, 1)]),
                            (3, 15, [(w, z) for w in (1, 2)
                                     for z in (1, 2)])):
        R = G.Zp(p, 8)
        rng = random.Random(333 + p)
        key = ('CSOTHER', 6, (2, 6), 2, 1, 2, 1)
        sig = [(0, 2, 1, 2), (2, 6, 2, 1)]
        tag = 'FRE-ecell-q%d' % p
        for (w, z) in combos:
            pins, free = ecell_spec(p, 8, w, z)
            bbar = [(z * z) % p]
            for i in range(ns):
                st = build(R, p, 8, pins, free, rng)
                if R.val(st[0], 8) != 6:
                    viol(tag, 'v(a0) != 6 = 2k+2h')
                check_member(R, 8, st, 6, sig, key, 2, w, 2,
                             bbar, w, tag)
        say('-- %s: child+E family k=2 boundary cell (entry 6, '
            'Wc=2) [%.1fs]' % (tag, time.time() - T0))


# ------------------------------------------------------------ FR-F PARI
def val_partition(pari, coeffs, p):
    fx = pari.Polrev(coeffs)
    if pari.poldisc(fx) == 0:
        return None
    fac = pari.factorpadic(fx, p, 60)
    parts = {}
    nfac = int(fac.matsize()[0])
    for i in range(nfac):
        gj = fac[0][i]
        dg = int(pari.poldegree(gj))
        try:
            c0 = pari.polcoef(gj, 0)
        except AttributeError:
            c0 = pari.polcoeff(gj, 0)
        v0 = int(pari.valuation(c0, p))
        parts[Fraction(v0, dg)] = parts.get(Fraction(v0, dg), 0) + dg
    return parts


def frf_pari():
    import cypari2
    pari = cypari2.Pari()
    pari.default('parisizemax', 512 * 1024 * 1024)
    # (i) SSF child-DEC members
    for (p, N, ns) in ((2, 8, 15), (3, 8, 10)):
        R = G.Zp(p, N)
        rng = random.Random(444 + p)
        tag = 'FRF-ssf-q%d' % p
        got = 0
        tries = 0
        while got < ns and tries < 60 * ns:
            tries += 1
            if p == 2:
                w, psi = 1, [1, 1, 1]
            else:
                w, psi = rng.choice((1, 2)), rng.choice(PSIS_3)
            pins, free = ssf_spec(p, N, 1, w, psi)
            st = build(R, p, N, pins, free, rng)
            child, Wc = G.extract_child(R, N, list(st), 6, 1, w, p)
            if R.res(child[0], 1) == 0:
                continue                      # want child-DEC
            L = [c + p ** N * rng.randrange(p ** 6) for c in st]
            L.append(1)
            fx = pari.Polrev(L)
            if pari.poldisc(fx) == 0 or not pari.polisirreducible(fx):
                continue
            parts = val_partition(pari, L, p)
            if parts != {Fraction(1): 6}:
                viol(tag, 'partition %s != {1:6}' % parts)
            K = pari.nfinit(fx)
            dec = pari.idealprimedec(K, p)
            efs = sorted((int(P[2]), int(P[3])) for P in dec)
            oddf = [ef for ef in efs if ef[1] % 2 == 1]
            evenmass = sum(e * f for (e, f) in efs if f % 2 == 0)
            if oddf != [(2, 1)] or evenmass != 4:
                viol(tag, 'sigma %s (odd-f %s, even mass %d)'
                     % (efs, oddf, evenmass))
            note(tag)
            got += 1
        if got < ns:
            viol(tag, 'only %d lifts' % got)
        say('-- %s: %d irreducible disc!=0 lifts: partition {1:6}, '
            'child (2,1) the only odd-f prime, even-f mass 4 '
            '[%.1fs]' % (tag, got, time.time() - T0))
    # (ii) DS-B partition
    p, N = 2, 11
    R = G.Zp(p, N)
    rng = random.Random(555)
    pins, free = dsb_spec(p, N, 1, [1, 1, 1])
    tag = 'FRF-dsb-q2'
    want = {Fraction(2): 4, Fraction(1): 2}
    got = 0
    tries = 0
    while got < 10 and tries < 200:
        tries += 1
        st = build(R, p, N, pins, free, rng)
        L = [c + p ** N * rng.randrange(p ** 6) for c in st]
        L.append(1)
        parts = val_partition(pari, L, p)
        if parts is None:
            continue
        if parts != want:
            viol(tag, 'partition %s != {2:4,1:2}' % parts)
        note(tag)
        got += 1
    if got < 10:
        viol(tag, 'only %d lifts' % got)
    say('-- %s: %d lifts, partition {2:4, 1:2} exact (the cap '
        'regime fracture, mechanism-free) [%.1fs]'
        % (tag, got, time.time() - T0))


# ------------------------------------------------------------ FR-G tooth
def frg_tooth():
    p, N = 2, 8
    R = G.Zp(p, N)
    rng = random.Random(666)
    pins, free = ssf_spec(p, N, 1, 1, [1, 1, 1])
    fired = 0
    for i in range(10):
        st = build(R, p, N, pins, free, rng)
        st[0] = (st[0] & ~((1 << 6) | (1 << 7))) | (1 << 7)
        ev = []
        ctx = {'p': p, 'cs_events': []}
        v, sg = G.read_cluster(R, N, list(st), ctx, top_events=ev)
        if ev[0] == ('DEC',) and v == 'DEC' and sg == ((6, 1),):
            fired += 1
        note('FRG-tooth')
    if fired != 10:
        viol('FRG-tooth', 'fired %d/10' % fired)
    say('-- FRG-tooth: a0-pin corruption -> one-side e=6 DEC read, '
        'fired %d/10 [%.1fs]' % (fired, time.time() - T0))


# ------------------------------------------------------------ main
def main():
    say('GENIND passPE6 FRESH ROUTE (same-side f-first realization '
        '+ the f-first entry/cap laws)')
    say('sealed runner md5 %s VERIFIED; imported read-only'
        % RUNNER_MD5)
    fra3_floor()
    fra2_n7()
    fra4_k2()
    fra5_fqt()
    frb_q3()
    frc_dsa()
    frd_dsb()
    frd_box()
    fre_ecell()
    frf_pari()
    frg_tooth()
    fra_exhaustive()
    total = sum(TALLY.values())
    say('')
    for f in sorted(TALLY):
        say('  %-16s %d' % (f, TALLY[f]))
    verdict = 'GREEN' if not VIOL else 'RED'
    say('VERDICT: %s -- %d checks, %d violations, %.1f s'
        % (verdict, total, len(VIOL), time.time() - T0))
    out = {'verdict': verdict, 'checks': total,
           'violations': VIOL, 'tally': TALLY,
           'elapsed_s': round(time.time() - T0, 1),
           'runner_md5': RUNNER_MD5}
    with open(os.path.join(HERE, 'genind_pe6_fresh_results.json'),
              'w') as fh:
        json.dump(out, fh, indent=1, sort_keys=True)
    return 0 if not VIOL else 1


if __name__ == '__main__':
    sys.exit(main())
