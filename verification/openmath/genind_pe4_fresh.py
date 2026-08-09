"""GENIND passPE4 FRESH ROUTE (hostile verifier; runs in /tmp only).

Route disclosed: differs from seal (n<=5 rosters), PE1 (exact n<=5 law
legs), PE2 (n=6 census + first n=6 oracle), r2 supp (M6 fibration),
PE3 (M7T n=7 + TWOCHILD + SS6 + per-coeff sharpness).
THIS route:
(FR-1) PSTEEP -- the SEALED-WINDOW disagreeing-regime genres the r3
  concordance sentences deny exist: a decided PIECE STEEPER than the
  extracted child, live at (2,5,n3) (a sealed n=3 control row!) and
  (2,6,n4) (a sealed n=4 row). Exhaustive census, capped-window
  adjudication, onto/fiber, verdict split (the uncapped reading would
  force 100% child-drain -- the split refutes it), lift stability.
(FR-2) THREECHILD -- the first THREE-child three-distinct-slope genre
  (n=6, N=13, both characteristics): the middle child B has BOTH a
  steeper co-block (capped) and a shallower one (own slope) in one
  D_B -- the mixed-cap regime never exercised by any leg. Windows
  (W_A,W_B,W_C) = (1,3,7) preregistered from the capped formula
  (uncapped predicts (1,1,1)); child-C 12-dim box BIJECTION onto all
  4,096 window-7 classes; child-B 4-dim box onto 16; PARI valuation
  partition {3:2, 2:2, 1:2} on disc!=0 lifts (mechanism-free).
(FR-3) N8MIX -- the corpus's FIRST n=8 composite-bearing instance:
  (4,1)-child (first mu=4 child in a mixed frame; the tower-live
  child degree) + CS4-E stage at (2,8). Child window N-6=2, 4-dim box
  onto all 16 (4,1,2)-classes, stage division-ledger budgets, PARI
  valuation partition {1:4, 1/2:4}, pin-corruption tooth.

ALL PREDICTIONS HAND-DERIVED BEFORE THIS RUN (report S7):

FR-1a PSTEEP3 (q=2, N=5, m=3): hull (0,4)-(1,2)-(3,0); piece [0,1]
  slope 2 STEEPER than child [1,3] slope 1 residual (y+1)^2.
  Pins: d4(a0)=1 (v=4 exact), d2(a1)=1 & d1(a1)=0 (v=2 exact),
  v(a2)>=2 (d1(a2)=-2z=0 char 2). LOCUS = 32 (a1 free h3,4; a2 free
  h2..4). Sides sig [(0,1,1,2),(1,3,1,1)]. CAPPED D = 2*1+1*min(2,1)
  = 3 = min_j(v(a_j)+j) (j=1: 2+1; j=3: 0+3), Wc = N-3 = 2; UNCAPPED
  display D = 2+2 = 4, Wc = 1. Prereg: Wc=2 on all 32; ONTO 4 child
  classes, constant fiber 8; verdict split DEC 16 / DRAIN 16 (v(b0)
  =1 vs >=2; UNCAPPED would force 32/32 child-drain); stability
  16 members x 3 independent lifts agree mod pi^2; one-deeper
  (mod pi^3) unstable on >= 1 member.
FR-1a-q3 (q=3, N=5, m=3): odd-q pins live: d4(a0)=c, d2(a1)=z^2,
  d1(a2)=-2z (v(a2)=1 exact, ON the side). LOCUS = 2*2*9*27 = 972.
  D = min(4, 3, 1+2, 3) = 3, Wc = 2. ONTO 9 classes fiber 108;
  verdict DEC 648 / DRAIN 324.
FR-1b PSTEEP4 (q=2, N=6, m=4): hull (0,5)-(1,3)-(4,0); piece slope 2
  steeper than (3,1)-child slope 1 residual (y+1)^3. Pins: d5(a0)=1,
  d3(a1)=1 (v=3), d2(a2)=1 (v=2), d1(a3)=1 (v=1). LOCUS = 4*8*16 =
  512. Sig [(0,1,1,2),(1,4,1,1)]. CAPPED D = 3*1+1*min(2,1) = 4
  (min_j: j=1: 3+1 = 4 = j=4: 0+4), Wc = 2; UNCAPPED D = 3+2 = 5.
  Prereg: Wc=2 all; ONTO 8 classes fiber 64; verdict DEC 256 /
  DRAIN 256; reduction gbar = y(y+1)^3.
FR-2 THREECHILD (q, N=13, m=6): hull (0,12)-(2,6)-(4,2)-(6,0), slopes
  3 > 2 > 1, three (2,1)-children (y-w)^2/(y-u)^2/(y-z)^2. q=2 pins:
  d12(a0)=1; v(a1)>=10; d6(a2)=1; v(a3)>=5; d2(a4)=1; v(a5)>=2.
  q=3 pins: d12(a0)=z^2u^2w^2, d9(a1)=-2z^2u^2w (v=9 exact),
  d6(a2)=z^2u^2, d4(a3)=-2z^2u (v=4), d2(a4)=z^2, d1(a5)=-2z (v=1).
  Sig [(0,2,1,3),(2,4,1,2),(4,6,1,1)]. CAPPED windows: D_A = 2*3+2*2
  +2*1 = 12 (Wc 1); D_B = 2*2+2*min(3,2)+2*min(1,2) = 10 (Wc 3) --
  the MIXED cap; D_C = 2*1+2*1+2*1 = 6 (Wc 7). UNCAPPED: D_B = D_C
  = 12 (Wc 1 both). Prereg: (1,3,7) every member, both q; C-box
  (a5{2..7} x a4{3..8}) -> BIJECTION onto 4,096 C-classes; B-box
  (a3{5,6} x a2{7,8}) -> onto 16 B-classes (per-height linearized
  images 1 vs t+1 independent, triangular); stability 20 x 3 lifts
  at (C mod pi^7, B mod pi^3); one-deeper C unstable >= 1; PARI
  {3:2, 2:2, 1:2} on every disc!=0 lift.
FR-3 N8MIX (q=2, N=8, m=8): hull (0,6)-(4,2)-(8,0); (4,1)-child
  slope 1 (y+1)^4 + CS4-E(1) stage slope 1/2. Pins: d6(a0)=1 (v=6),
  v(a1)>=6, v(a2)>=5, v(a3)>=4, d2(a4)=1, v(a5)>=2, v(a6)>=2
  (d1(a6)=-2z=0 char 2), v(a7)>=1. Sig [(0,4,1,1),(4,8,2,1)];
  verdict CS every member. Child D = 4*1+4*min(1/2,1) = 6 (min_j:
  j=0: 6 = j=4: 2+4), Wc = 2; gbar = (y+1)^4 (stage degree-dropped:
  the AGREEING regime -- this leg is n=8 existence + mu=4 child).
  Child-box (a1{6},a2{5},a3{4},a4{3}) -> onto all 16 classes
  (images y..y^4 mod t^4 rank 4). Stage division u3=a7-g3,
  u2=a6-g2-g3u3, u1=a5-g1-g2u3-g3u2, u0=a4-g0-g1u3-g2u2-g3u1;
  budgets v(u0)=2 & d2(u0)=1, v(u1)>=2, v(u2)>=2, v(u3)>=1.
  PARI {1:4, 1/2:4}; T-PIN corrupt d2(a4) -> sig breaks 10/10.

Sealed runner imported READ-ONLY, md5-asserted. Exact integers.
"""
import sys, os, json, time, hashlib, random

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
BUF = 4


def say(m):
    print(m)
    sys.stdout.flush()


def note(f, n=1):
    TALLY[f] = TALLY.get(f, 0) + n


def viol(f, d):
    VIOL.append((f, str(d)[:200]))
    say('VIOLATION [%s] %s' % (f, d))


def free(p, lo, N):
    vals = [0]
    for h in range(lo, N):
        vals = [v + b * p ** h for v in vals for b in range(p)]
    return vals


def rnd_free(p, lo, N, rng):
    return sum(rng.randrange(p) * p ** h for h in range(lo, N))


def sig_of(R, N, st, m):
    return [(s[0], s[2], s[4], s[5]) for s in G.sides_of(R, N, st, m)]


def lift_state(p, st, N, rng):
    return [c + rnd_free(p, N, N + BUF, rng) for c in st]


# ------------------------------------------------------------ FR-1
def fr1_run(p, N, m, mk_states, sig_want, k, z, Wc_want, n_want,
            ncl_want, fib_want, dec_want, drn_want, tag):
    R = G.Zp(p, N)
    Rh = G.Zp(p, N + 2 * BUF)
    ctx = {'p': p, 'cs_events': []}
    rng = random.Random(707)
    hist, verd = {}, {'DEC': 0, 'DRAIN': 0, 'CS': 0}
    ev0 = None
    n = 0
    stab_bad, deeper_unst = 0, 0
    states = mk_states()
    for st in states:
        n += 1
        if sig_of(R, N, st, m) != sig_want:
            viol(tag, 'sides %s' % (st,))
            continue
        ev = []
        v, sg = G.read_cluster(R, N, list(st), ctx, top_events=ev)
        verd[v] = verd.get(v, 0) + 1
        if ev0 is None:
            ev0 = ev[0]
            say('-- %s: top event = %s' % (tag, (ev0,)))
        elif ev[0] != ev0:
            viol(tag, 'event moved %s' % (ev,))
        child, Wc = G.extract_child(R, N, st, m, k, z, p)
        if Wc != Wc_want:
            viol(tag, 'Wc=%d != %d (capped window refuted?)'
                 % (Wc, Wc_want))
        key = tuple(c % p ** Wc_want for c in child)
        hist[key] = hist.get(key, 0) + 1
        note(tag)
    if n != n_want:
        viol(tag, 'locus %d != %d' % (n, n_want))
    fibs = set(hist.values())
    if len(hist) != ncl_want or fibs != {fib_want}:
        viol(tag, 'onto %d (want %d) fibers %s (want {%d})'
             % (len(hist), ncl_want, sorted(fibs)[:5], fib_want))
    if verd['DEC'] != dec_want or verd['DRAIN'] != drn_want:
        viol(tag, 'verdict split %s != DEC %d / DRAIN %d'
             % (verd, dec_want, drn_want))
    # stability: 16 members x 3 independent lifts
    for st in states[::max(1, len(states) // 16)][:16]:
        kids = []
        for _ in range(3):
            stl = lift_state(p, st, N, rng)
            ch, _W = G.extract_child(Rh, N + BUF, stl, m, k, z, p)
            kids.append(ch)
        base = [c % p ** Wc_want for c in kids[0]]
        for ch in kids[1:]:
            if [c % p ** Wc_want for c in ch] != base:
                stab_bad += 1
        deep = [c % p ** (Wc_want + 1) for c in kids[0]]
        for ch in kids[1:]:
            if [c % p ** (Wc_want + 1) for c in ch] != deep:
                deeper_unst += 1
        note(tag + '-stab')
    if stab_bad:
        viol(tag, 'capped-window lift instability x%d' % stab_bad)
    if deeper_unst < 1:
        viol(tag, 'TOOTH one-deeper never fired')
    say('-- %s: locus %d, ONTO %d fibers %s, verdicts %s, '
        'stab 0 bad, one-deeper fired %dx [%.1fs]'
        % (tag, n, len(hist), sorted(fibs), verd, deeper_unst,
           time.time() - T0))


def fr1a_states():
    out = []
    for f1 in free(2, 3, 5):
        for f2 in free(2, 2, 5):
            out.append([16, 4 + f1, f2])
    return out


def fr1a3_states(c, z):
    out = []
    for f1 in free(3, 3, 5):
        for f2 in free(3, 2, 5):
            out.append([c * 81, (z * z % 3) * 9 + f1,
                        ((-2 * z) % 3) * 3 + f2])
    return out


def fr1b_states():
    out = []
    for f1 in free(2, 4, 6):
        for f2 in free(2, 3, 6):
            for f3 in free(2, 2, 6):
                out.append([32, 8 + f1, 4 + f2, 2 + f3])
    return out


# ------------------------------------------------------------ FR-2
def tc_pins(p, N, z, u, w):
    if p == 2:
        return [2 ** 12, 0, 2 ** 6, 0, 2 ** 2, 0]
    return [(z*z*u*u*w*w % p) * p**12, ((-2*z*z*u*u*w) % p) * p**9,
            (z*z*u*u % p) * p**6, ((-2*z*z*u) % p) * p**4,
            (z*z % p) * p**2, ((-2*z) % p) * p**1]


TC_LOS = [13, 10, 7, 5, 3, 2]
TC_LOS3 = [13, 10, 7, 5, 3, 2]
TC_SIG = [(0, 2, 1, 3), (2, 4, 1, 2), (4, 6, 1, 1)]


def tc_state(p, N, z, u, w, rng):
    ps = tc_pins(p, N, z, u, w)
    los = TC_LOS if p == 2 else TC_LOS3
    return [ps[j] + rnd_free(p, los[j], N, rng) for j in range(6)]


def fr2_samples(p, ns, tag):
    N = 13
    R = G.Zp(p, N)
    ctx = {'p': p, 'cs_events': []}
    rng = random.Random(1311)
    ev0 = None
    for i in range(ns):
        if p == 2:
            z = u = w = 1
        else:
            z, u, w = (rng.choice((1, 2)) for _ in range(3))
        st = tc_state(p, N, z, u, w, rng)
        if sig_of(R, N, st, 6) != TC_SIG:
            viol(tag, 'sides %s' % (st,))
            continue
        ev = []
        v, sg = G.read_cluster(R, N, list(st), ctx, top_events=ev)
        if ev0 is None:
            ev0 = (ev[0][0],)
            say('-- %s: top event class = %s (verdict sample %s)'
                % (tag, ev[0], v))
        _, WA = G.extract_child(R, N, st, 6, 3, w % p, p)
        _, WB = G.extract_child(R, N, st, 6, 2, u % p, p)
        _, WC = G.extract_child(R, N, st, 6, 1, z % p, p)
        if (WA, WB, WC) != (1, 3, 7):
            viol(tag, 'windows %s != (1,3,7) [capped refuted?]'
                 % ((WA, WB, WC),))
        note(tag)
    say('-- %s: %d samples, windows (1,3,7) exact [%.1fs]'
        % (tag, ns, time.time() - T0))


def fr2_boxes():
    p, N = 2, 13
    R = G.Zp(p, N)
    tag = 'FR2-box'
    ps = tc_pins(p, N, 1, 1, 1)
    # C-box: a5 digits 2..7, a4 digits 3..8 -> predicted BIJECTION
    # onto all 4096 child-C classes at window 7
    hist = {}
    for f5 in free(2, 2, 8):
        for f4 in free(2, 3, 9):
            st = [ps[0], 0, ps[2], 0, ps[4] + f4, f5]
            ch, Wc = G.extract_child(R, N, st, 6, 1, 1, p)
            if Wc != 7:
                viol(tag, 'C Wc=%d' % Wc)
            key = tuple(c % 2 ** 7 for c in ch)
            hist[key] = hist.get(key, 0) + 1
            note(tag)
    if len(hist) != 4096 or set(hist.values()) != {1}:
        viol(tag, 'C-box: %d classes, fibers %s (want 4096 x {1})'
             % (len(hist), sorted(set(hist.values()))[:5]))
    say('-- %s: C-box 4096 -> %d classes, fibers %s [%.1fs]'
        % (tag, len(hist), sorted(set(hist.values())),
           time.time() - T0))
    # B-box: a3 digits 5,6; a2 digits 7,8 -> onto all 16 B-classes
    histB = {}
    for f3 in free(2, 5, 7):
        for f2 in free(2, 7, 9):
            st = [ps[0], 0, ps[2] + f2, f3, ps[4], 0]
            ch, Wc = G.extract_child(R, N, st, 6, 2, 1, p)
            if Wc != 3:
                viol(tag, 'B Wc=%d' % Wc)
            key = tuple(c % 2 ** 3 for c in ch)
            histB[key] = histB.get(key, 0) + 1
            note(tag)
    if len(histB) != 16 or set(histB.values()) != {1}:
        viol(tag, 'B-box: %d classes, fibers %s (want 16 x {1})'
             % (len(histB), sorted(set(histB.values()))[:5]))
    say('-- %s: B-box 16 -> %d classes, fibers %s [%.1fs]'
        % (tag, len(histB), sorted(set(histB.values())),
           time.time() - T0))


def fr2_stab(p, ns, tag):
    N = 13
    Rh = G.Zp(p, N + 2 * BUF)
    rng = random.Random(1717)
    deeper = 0
    for i in range(ns):
        if p == 2:
            z = u = w = 1
        else:
            z, u, w = (rng.choice((1, 2)) for _ in range(3))
        st = tc_state(p, N, z, u, w, rng)
        kidsC, kidsB = [], []
        for _ in range(3):
            stl = lift_state(p, st, N, rng)
            cC, _ = G.extract_child(Rh, N + BUF, stl, 6, 1, z % p, p)
            cB, _ = G.extract_child(Rh, N + BUF, stl, 6, 2, u % p, p)
            kidsC.append(cC)
            kidsB.append(cB)
        bC = [c % p ** 7 for c in kidsC[0]]
        bB = [c % p ** 3 for c in kidsB[0]]
        for cC in kidsC[1:]:
            if [c % p ** 7 for c in cC] != bC:
                viol(tag, 'C unstable at capped window')
        for cB in kidsB[1:]:
            if [c % p ** 3 for c in cB] != bB:
                viol(tag, 'B unstable at capped window')
        dC = [c % p ** 8 for c in kidsC[0]]
        for cC in kidsC[1:]:
            if [c % p ** 8 for c in cC] != dC:
                deeper += 1
        note(tag)
    if deeper < 1:
        viol(tag, 'TOOTH one-deeper-C never fired')
    say('-- %s: %d x 3 lifts stable at (7,3); one-deeper C fired %dx'
        % (tag, ns, deeper))


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
        from fractions import Fraction
        sl = Fraction(v0, dg)
        parts[sl] = parts.get(sl, 0) + dg
    return parts


def fr2_pari(p, ns, tag):
    import cypari2
    from fractions import Fraction
    pari = cypari2.Pari()
    N = 13
    rng = random.Random(4242)
    want = {Fraction(3): 2, Fraction(2): 2, Fraction(1): 2}
    done = 0
    while done < ns:
        if p == 2:
            z = u = w = 1
        else:
            z, u, w = (rng.choice((1, 2)) for _ in range(3))
        st = tc_state(p, N, z, u, w, rng)
        stl = lift_state(p, st, N, rng)
        parts = val_partition(pari, [int(c) for c in stl] + [1], p)
        if parts is None:
            continue
        done += 1
        note(tag)
        if parts != want:
            viol(tag, 'val partition %s != %s' % (parts, want))
    say('-- %s: %d disc!=0 lifts, val partition {3:2,2:2,1:2} exact'
        % (tag, done))


# ------------------------------------------------------------ FR-3
N8_SIG = [(0, 4, 1, 1), (4, 8, 2, 1)]


def n8_state(rng, corrupt=False):
    p, N = 2, 8
    st = [2 ** 6 + rnd_free(p, 7, N, rng),
          rnd_free(p, 6, N, rng),
          rnd_free(p, 5, N, rng),
          rnd_free(p, 4, N, rng),
          2 ** 2 + rnd_free(p, 3, N, rng),
          rnd_free(p, 2, N, rng),
          rnd_free(p, 2, N, rng),
          rnd_free(p, 1, N, rng)]
    if corrupt:
        st[4] ^= 2 ** 2      # kill the stage vertex pin d2(a4)
    return st


def fr3_run(ns, tag):
    p, N = 2, 8
    R = G.Zp(p, N)
    Rh = G.Zp(p, N + 2 * BUF)
    ctx = {'p': p, 'cs_events': []}
    rng = random.Random(888)
    ev0 = None
    for i in range(ns):
        st = n8_state(rng)
        if sig_of(R, N, st, 8) != N8_SIG:
            viol(tag, 'sides %s' % (st,))
            continue
        ev = []
        v, sg = G.read_cluster(R, N, list(st), ctx, top_events=ev)
        if v != 'CS':
            viol(tag, 'verdict %s' % v)
        if ev0 is None:
            ev0 = ev[0]
            say('-- %s: CS key = %s' % (tag, (ev0,)))
        elif ev[0] != ev0:
            viol(tag, 'key moved %s' % (ev,))
        child, Wc = G.extract_child(R, N, st, 8, 1, 1, p)
        if Wc != 2:
            viol(tag, 'child Wc=%d != 2' % Wc)
        # stage ledger at a buffered lift (need headroom for products)
        stl = lift_state(p, st, N, rng)
        chl, Wcl = G.extract_child(Rh, N + BUF, stl, 8, 1, 1, p)
        ghat, A, B, _ = G.extract_child.last
        g3 = Rh.mul(A[3], Rh.pipw(1))
        g2 = Rh.mul(A[2], Rh.pipw(2))
        g1 = Rh.mul(A[1], Rh.pipw(3))
        g0 = Rh.mul(A[0], Rh.pipw(4))
        u3 = Rh.sub(stl[7], g3)
        u2 = Rh.sub(Rh.sub(stl[6], g2), Rh.mul(g3, u3))
        u1 = Rh.sub(Rh.sub(stl[5], g1),
                    Rh.add(Rh.mul(g2, u3), Rh.mul(g3, u2)))
        u0 = Rh.sub(Rh.sub(stl[4], g0),
                    Rh.add(Rh.mul(g1, u3),
                           Rh.add(Rh.mul(g2, u2), Rh.mul(g3, u1))))
        ok = (Rh.val(u0, N) == 2 and Rh.res(u0, 2) == 1
              and (Rh.val(u1, N) or N) >= 2
              and (Rh.val(u2, N) or N) >= 2
              and (Rh.val(u3, N) or N) >= 1)
        if not ok:
            viol(tag, 'stage budgets broke at %s' % (st,))
        note(tag)
    say('-- %s: %d samples CS, child Wc=2, stage budgets exact [%.1fs]'
        % (tag, ns, time.time() - T0))
    # child-box: onto all 16 (4,1,2)-classes
    hist = {}
    base = n8_state(random.Random(1))
    for b1 in (0, 1):
        for b2 in (0, 1):
            for b3 in (0, 1):
                for b4 in (0, 1):
                    st = list(base)
                    st[1] = b1 * 2 ** 6
                    st[2] = b2 * 2 ** 5
                    st[3] = b3 * 2 ** 4
                    st[4] = 2 ** 2 + b4 * 2 ** 3
                    ch, Wc = G.extract_child(R, N, st, 8, 1, 1, p)
                    key = tuple(c % 4 for c in ch)
                    hist[key] = hist.get(key, 0) + 1
                    note(tag + '-box')
    if len(hist) != 16 or set(hist.values()) != {1}:
        viol(tag, 'child-box %d classes fibers %s (want 16 x {1})'
             % (len(hist), sorted(set(hist.values()))[:5]))
    say('-- %s: child-box 16 -> %d classes fibers %s'
        % (tag, len(hist), sorted(set(hist.values()))))
    # T-PIN tooth
    fired = 0
    rng2 = random.Random(999)
    for i in range(10):
        st = n8_state(rng2, corrupt=True)
        if sig_of(R, N, st, 8) != N8_SIG:
            fired += 1
        note(tag + '-tooth')
    if fired != 10:
        viol(tag, 'T-PIN fired %d/10' % fired)
    say('-- %s: T-PIN fired %d/10' % (tag, fired))


def fr3_pari(ns, tag):
    import cypari2
    from fractions import Fraction
    pari = cypari2.Pari()
    p, N = 2, 8
    rng = random.Random(555)
    want = {Fraction(1): 4, Fraction(1, 2): 4}
    done = 0
    while done < ns:
        st = n8_state(rng)
        stl = lift_state(p, st, N, rng)
        parts = val_partition(pari, [int(c) for c in stl] + [1], p)
        if parts is None:
            continue
        done += 1
        note(tag)
        if parts != want:
            viol(tag, 'val partition %s != %s' % (parts, want))
    say('-- %s: %d disc!=0 lifts, val partition {1:4,1/2:4} exact'
        % (tag, done))


def main():
    say('GENIND passPE4 fresh route (sealed runner md5 %s)' % md5)
    fr1_run(2, 5, 3, fr1a_states, [(0, 1, 1, 2), (1, 3, 1, 1)],
            1, 1, 2, 32, 4, 8, 16, 16, 'FR1a-psteep3-q2N5')
    for c in (1, 2):
        for z in (1, 2):
            fr1_run(3, 5, 3, lambda c=c, z=z: fr1a3_states(c, z),
                    [(0, 1, 1, 2), (1, 3, 1, 1)], 1, z, 2,
                    243, 9, 27, 162, 81,
                    'FR1a-psteep3-q3N5-c%dz%d' % (c, z))
    fr1_run(2, 6, 4, fr1b_states, [(0, 1, 1, 2), (1, 4, 1, 1)],
            1, 1, 2, 512, 8, 64, 256, 256, 'FR1b-psteep4-q2N6')
    fr2_samples(2, 250, 'FR2-tc-q2')
    fr2_samples(3, 150, 'FR2-tc-q3')
    fr2_boxes()
    fr2_stab(2, 20, 'FR2-stab-q2')
    fr2_stab(3, 12, 'FR2-stab-q3')
    fr2_pari(2, 30, 'FR2-pari-q2')
    fr2_pari(3, 20, 'FR2-pari-q3')
    fr3_run(250, 'FR3-n8mix')
    fr3_pari(25, 'FR3-n8mix-pari')
    total = sum(TALLY.values())
    say('')
    for k in sorted(TALLY):
        say('  %-28s %d' % (k, TALLY[k]))
    verdict = 'GREEN' if not VIOL else 'RED'
    say('VERDICT: %s — %d checks, %d violations, %.1f s'
        % (verdict, total, len(VIOL), time.time() - T0))
    json.dump({'tally': TALLY, 'violations': VIOL,
               'elapsed_s': round(time.time() - T0, 1)},
              open(os.path.join(HERE, 'genind_pe4_fresh_results.json'),
                   'w'), indent=1, sort_keys=True)
    return 0 if not VIOL else 1


if __name__ == '__main__':
    sys.exit(main())
