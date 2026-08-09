"""GENIND passPE5 FRESH ROUTE (hostile verifier; runs in /tmp only).

Route disclosed: differs from seal (n<=5 rosters, 163,536), PE1
(symbolic+exact n<=5), PE2 (n=6 census + first n=6 PARI), r2 supp
(M6 fibration 2,128,163), PE3 (M7T n=7 + TWOCHILD + SS6, 705,133),
PE4 (PSTEEP + THREECHILD + N8MIX, 6,507).
THIS route:
(FR-A) NINEMIX -- the corpus's FIRST n >= 9 instance, and the first
  genre carrying ALL FOUR block types of LEMMA GENIND-6's grammar at
  once: decided piece (slope 3) + child A (2,1)@slope 2 + child B
  (2,1)@slope 1 + CS4-E(1) stage (slope 1/2), hull
  (0,11)-(1,8)-(3,4)-(5,2)-(9,0), N = 12, both characteristics.
  D_B = 2*1 + 1*min(3,1) + 2*min(2,1) + 4*min(1/2,1) = 7 (Wc 5) is
  the first D_l ever exercised containing a capped steeper PIECE, a
  capped steeper CO-CHILD, and an own-slope shallower STAGE at once;
  D_A = 4 + min(3,2) + 2*min(1,2) + 4*min(1/2,2) = 10 (Wc 2).
  UNCAPPED display would give D_A = 11, D_B = 11 (Wc 1 both).
(FR-B) SAMESIDE -- the r4 trichotomy's SAME-SIDE CO-CHILDREN leg
  ("same-side co-CHILDREN as repeated factors (ybar-(z'-zhat))^mu"),
  never realized anywhere: q = 3 forced (two distinct unit residues;
  q = 2 CANNOT carry it -- why no sealed q=2 row ever saw it; the
  sealed q>=3 rows sit below its visibility v(a0)=4: (3,4) N-1=3,
  (3,3), (5,3) likewise). Exhaustive 59,049 at (3,4-cluster,N=6).
(FR-C) STEEPSCAN -- systematic steeper-decided-piece coverage beyond
  PE4's two cells: C1 = deeper-window s=3 piece (2,6,n3); C2 = TWO
  steeper pieces at distinct slopes (2,8,n4), never constructed;
  C3 = piece SANDWICH steeper+shallower around the child (2,9,n4),
  the decided-piece analogue of THREECHILD's mixed cap; C1q3 odd-q
  companion. All exhaustive except C1q3 (100 product samples).

ALL PREDICTIONS HAND-DERIVED BEFORE THIS RUN (derivations in the
PE5 report S-FRESH):

FR-A NINEMIX (q in {2,3}, m=9, N=12): product-constructed members
  (x-C)(x-U1)(x-U2)(x-Z1)(x-Z2)S(x), C = c p^3+O(p^4),
  U_i = u p^2+O(p^3), Z_i = z p+O(p^2), S = (x^2-s p+O(p^2))^2
  + p^3*(deg<=3 perturbation); hull by Gauss additivity.
  Prereg: sig [(0,1,1,3),(1,3,1,2),(3,5,1,1),(5,9,2,1)]; verdict CS
  every member (composite stage present); extract(k=2,z=u) Wc=2;
  extract(k=1,z=z) Wc=5. 200 samples q=2, 120 q=3.
  BOX q=2 (base letters all 1): a3 heights {5..8} x a4 heights
  {4..7} (2^8 members) -> child-B classes mod 2^5: 256 DISTINCT =
  BIJECTION onto the full window-5 space (first-order images of
  (j=3,h)/(j=4,h) per height h are ybar^3, ybar^4 mod (ybar-1)^2 =
  (1,1),(1,0) in the {1,(ybar-1)} basis at char 2 -- invertible;
  strictly triangular across heights). BOX q=3: a3{5,6} x a4{4,5}
  (3^4) -> 81 DISTINCT truncated (mod 3^3) classes (images swap by
  J-D0 degeneration: (1,0),(1,1) at char 3 -- still invertible).
  PARI (mechanism-free): disc != 0 lifts, root-valuation partition
  {3:1, 2:2, 1:2, 1/2:4}; 15 lifts q=2 (wild p=2, deg 9), 10 q=3.
  TOOTH: corrupt the (3,4) vertex pin (a3 += p^4 at q=2, flipping
  digit4(a3) = 1 -> 0): sig breaks 10/10.
FR-B SAMESIDE (q=3, m=4, N=6): single side (0,4)-(4,0) slope 1,
  residual (y-1)^2(y-2)^2 = y^4+y^2+1 over F_3 (letters {1,2}
  FORCED). Pinned locus: a0 = pin h4 + free h5 (3); a1 v>=4, free
  h4,5 (9); a2 pin h2 + free h3..5 (27); a3 v>=2, free h2..5 (81):
  LOCUS = 59,049 exhaustive. Prereg: sig [(0,4,1,1)] all; both
  children extract at Wc = 2 (D = 4 = 2*1+2*min(1,1), capped =
  uncapped -- the same-slope leg, not the cap leg); joint
  (class_z=1, class_z=2) ONTO 9 x 9 = 81 with CONSTANT fiber 729;
  cofactor reduction after extracting z=1 is (ybar-2)^2 = [1,2,1]
  and its z-shift B(y+1) reduces to (ybar-1)^2 = [1,1,1] -- the r4
  parenthetical's (ybar-(z'-zhat))^mu with z'-zhat = 1, checked on
  every member; verdict split DEC 26,244 / DRAIN 32,805 (frame DEC
  iff BOTH children DEC; child (2,1,2) DEC classes 6/9, drain 3/9
  [v(b0) >= 2], product fraction 4/9). PARI: 25 fully-DEC members
  (both children v(b0)=1): factorpadic p=3 gives EXACTLY two
  quadratic factors, each root-val 1, each disc-valuation ODD
  (= two ramified quadratics, sigma {(2,1),(2,1)}).
FR-C STEEPSCAN (q=2 exhaustive):
  C1 (2,6,m=3) hull (0,5)-(1,2)-(3,0), piece s=3 over (2,1)-child
   k=1 (y+1)^2: locus a0 = 2^5 pinned exactly; a1 pin h2 free
   h3,4,5 (8); a2 v>=2 free h2..5 (16): LOCUS 128. Sig
   [(0,1,1,3),(1,3,1,1)]; capped D = 2+min(3,1) = 3 = min_j(v+j)
   (j=1: 3, j=3: 3), Wc = 3 (UNCAPPED D = 5, Wc = 1); ONTO 16
   window-3 classes fiber 8; DEC 80 / DRAIN 48 (u_2(3) = 6/16:
   drain 4 + alpha(1)->window-1 2).
  C2 (2,8,m=4) hull (0,7)-(1,4)-(2,2)-(4,0), pieces s=3 AND s=2
   over (2,1)-child k=1: locus a0 = 2^7; a1 pin h4 free h5,6,7 (8);
   a2 pin h2 free h3..7 (32); a3 v>=2 free h2..7 (64): LOCUS
   16,384. Sig [(0,1,1,3),(1,2,1,2),(2,4,1,1)]; capped D = 2 +
   min(3,1) + min(2,1) = 4 (min_j: j=2: 2+2 = j=4: 4), Wc = 4
   (UNCAPPED 7 -> 1); ONTO 64 fiber 256; DRAIN 3,072 / DEC 13,312
   (u_2(4) = q^3 + (q-1)q*u_2(2) = 8+4 = 12 of 64).
  C3 (2,9,m=4) hull (0,8)-(1,5)-(3,1)-(4,0), piece s=3 STEEPER +
   piece s=1 SHALLOWER around the (2,1)-child k=2 -- the sandwich:
   locus a0 = 2^8; a1 pin h5 free h6,7,8 (8); a2 v>=4 free h4..8
   (32); a3 pin h1 free h2..8 (128): LOCUS 32,768. Sig
   [(0,1,1,3),(1,3,1,2),(3,4,1,1)]; capped D = 4 + min(3,2) +
   min(1,2) = 7 (min_j: j=1: 5+2 = j=3: 1+6 = 7), Wc = 2 (UNCAPPED
   8 -> 1); ONTO 4 fiber 8,192; DEC 16,384 / DRAIN 16,384
   (u_2(2) = 2/4).
  C1q3 (3,6,m=3): product samples, odd-q pin digit1(a2) = -2z != 0
   (v(a2) = 1 ON the side; D unchanged: j=2 gives 1+2 = 3): sig +
   Wc = 3 on 100 samples.

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
    VIOL.append((f, str(d)[:200]))
    say('VIOLATION [%s] %s' % (f, d))


def sig_of(R, N, st, m):
    return [(s[0], s[2], s[4], s[5]) for s in G.sides_of(R, N, st, m)]


def pmul(a, b, PB):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x == 0:
            continue
        for j, y in enumerate(b):
            out[i + j] = (out[i + j] + x * y) % PB
    return out


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


# ---------------------------------------------------------- FR-A
NM_N = 12
NM_SIG = [(0, 1, 1, 3), (1, 3, 1, 2), (3, 5, 1, 1), (5, 9, 2, 1)]


def nm_member(p, c, u, z, s, rng):
    PB = p ** NM_N
    r = lambda k: rng.randrange(p ** (NM_N - k)) * p ** k
    f = [(-(c * p ** 3 + r(4))) % PB, 1]
    for _ in range(2):
        f = pmul(f, [(-(u * p ** 2 + r(3))) % PB, 1], PB)
    for _ in range(2):
        f = pmul(f, [(-(z * p + r(2))) % PB, 1], PB)
    T = [(-(s * p + r(2))) % PB, 0, 1]
    S = pmul(T, T, PB)
    for j in range(4):
        S[j] = (S[j] + r(3)) % PB
    f = pmul(f, S, PB)
    assert f[9] == 1
    return f[:9]


def fra_samples(p, ns, tag):
    R = G.Zp(p, NM_N)
    ctx = {'p': p, 'cs_events': []}
    rng = random.Random(505 + p)
    key0 = None
    for i in range(ns):
        if p == 2:
            c = u = z = s = 1
        else:
            c, u, z, s = (rng.choice((1, 2)) for _ in range(4))
        st = nm_member(p, c, u, z, s, rng)
        if sig_of(R, NM_N, st, 9) != NM_SIG:
            viol(tag, 'sides %s' % (st,))
            continue
        ev = []
        v, sg = G.read_cluster(R, NM_N, list(st), ctx, top_events=ev)
        if v != 'CS':
            viol(tag, 'verdict %s != CS' % v)
        k = (ev[0][0],) if ev else None
        if key0 is None:
            key0 = ev[0]
            say('-- %s: top event = %s' % (tag, (key0,)))
        elif ev[0][0] != key0[0]:
            viol(tag, 'event class moved %s' % (ev[0],))
        _, WA = G.extract_child(R, NM_N, st, 9, 2, u % p, p)
        _, WB = G.extract_child(R, NM_N, st, 9, 1, z % p, p)
        if (WA, WB) != (2, 5):
            viol(tag, 'windows %s != (2,5) [capped refuted?]'
                 % ((WA, WB),))
        note(tag)
    say('-- %s: %d samples, windows (2,5) exact [%.1fs]'
        % (tag, ns, time.time() - T0))


def fra_box(p, hs3, hs4, trunc, want, tag):
    R = G.Zp(p, NM_N)
    rng = random.Random(99)
    base = nm_member(p, 1, 1, 1, 1, rng)
    seen = set()
    tot = 0
    for m3 in range(p ** len(hs3)):
        for m4 in range(p ** len(hs4)):
            st = list(base)
            x3, x4 = m3, m4
            for h in hs3:
                st[3] = (st[3] + (x3 % p) * p ** h) % p ** NM_N
                x3 //= p
            for h in hs4:
                st[4] = (st[4] + (x4 % p) * p ** h) % p ** NM_N
                x4 //= p
            if sig_of(R, NM_N, st, 9) != NM_SIG:
                viol(tag, 'box member left genre')
                continue
            child, WB = G.extract_child(R, NM_N, st, 9, 1, 1, p)
            if WB != 5:
                viol(tag, 'box Wc %d != 5' % WB)
            seen.add(tuple(c % p ** trunc for c in child))
            tot += 1
            note(tag)
    if len(seen) != want or tot != want:
        viol(tag, 'box classes %d / %d != %d (bijection refuted)'
             % (len(seen), tot, want))
    say('-- %s: %d box members -> %d distinct classes (want %d) '
        '[%.1fs]' % (tag, tot, len(seen), want, time.time() - T0))


def fra_pari(p, ns, tag):
    import cypari2
    pari = cypari2.Pari()
    pari.default('parisizemax', 512 * 1024 * 1024)
    rng = random.Random(4242 + p)
    want = {Fraction(3): 1, Fraction(2): 2, Fraction(1): 2,
            Fraction(1, 2): 4}
    got = 0
    tries = 0
    while got < ns and tries < 4 * ns:
        tries += 1
        if p == 2:
            c = u = z = s = 1
        else:
            c, u, z, s = (rng.choice((1, 2)) for _ in range(4))
        st = nm_member(p, c, u, z, s, rng)
        parts = val_partition(pari, [int(x) for x in st] + [1], p)
        if parts is None:
            continue
        got += 1
        if parts != want:
            viol(tag, 'partition %s != %s' % (parts, want))
        note(tag)
    if got < ns:
        viol(tag, 'only %d disc!=0 lifts' % got)
    say('-- %s: %d lifts, partition {3:1,2:2,1:2,1/2:4} exact '
        '[%.1fs]' % (tag, got, time.time() - T0))


def fra_tooth(tag):
    p = 2
    R = G.Zp(p, NM_N)
    rng = random.Random(77)
    fired = 0
    for i in range(10):
        st = nm_member(p, 1, 1, 1, 1, rng)
        assert sig_of(R, NM_N, st, 9) == NM_SIG
        st[3] = (st[3] + p ** 4) % p ** NM_N
        if sig_of(R, NM_N, st, 9) != NM_SIG:
            fired += 1
        note(tag)
    if fired != 10:
        viol(tag, 'tooth fired %d/10' % fired)
    say('-- %s: TOOTH FIRED %d/10 (corrupted (3,4) vertex pin exits '
        'the genre)' % (tag, fired))


# ---------------------------------------------------------- FR-B
def frb_run():
    p, N, m = 3, 6, 4
    tag = 'FRB-sameside'
    R = G.Zp(p, N)
    ctx = {'p': p, 'cs_events': []}
    PB = p ** N
    hist = {}
    verd = {'DEC': 0, 'DRAIN': 0}
    tot = 0
    for f0 in range(3):        # a0 = 3^4 + f0*3^5
        a0 = p ** 4 + f0 * p ** 5
        for f1 in range(9):    # a1 = (f1 digits h4,h5)
            a1 = (f1 % 3) * p ** 4 + (f1 // 3) * p ** 5
            for f2 in range(27):   # a2 = 3^2 + digits h3..h5
                x, a2 = f2, p ** 2
                for h in (3, 4, 5):
                    a2 += (x % 3) * p ** h
                    x //= 3
                for f3 in range(81):  # a3 = digits h2..h5
                    x, a3 = f3, 0
                    for h in (2, 3, 4, 5):
                        a3 += (x % 3) * p ** h
                        x //= 3
                    st = [a0 % PB, a1 % PB, a2 % PB, a3 % PB]
                    tot += 1
                    if sig_of(R, N, st, m) != [(0, 4, 1, 1)]:
                        viol(tag, 'sides %s' % (st,))
                        continue
                    v, sg = G.read_cluster(R, N, list(st), ctx)
                    verd[v] = verd.get(v, 0) + 1
                    ch1, W1 = G.extract_child(R, N, st, m, 1, 1, p)
                    _g, _A, B1, _W = G.extract_child.last
                    ch2, W2 = G.extract_child(R, N, st, m, 1, 2, p)
                    if (W1, W2) != (2, 2):
                        viol(tag, 'windows %s != (2,2)' % ((W1, W2),))
                    # r4 trichotomy same-side leg: cofactor reduction
                    Bbar = tuple(c % p for c in B1)
                    if Bbar != (1, 2, 1):
                        viol(tag, 'cofactor red %s != (ybar-2)^2'
                             % (Bbar,))
                    Bsh = G.poly_shift(R, list(B1), 1)
                    if tuple(c % p for c in Bsh) != (1, 1, 1):
                        viol(tag, 'shifted red != (ybar-1)^2')
                    key = (tuple(c % p ** 2 for c in ch1),
                           tuple(c % p ** 2 for c in ch2))
                    hist[key] = hist.get(key, 0) + 1
                    note(tag)
    if tot != 59049:
        viol(tag, 'locus %d != 59049' % tot)
    fibs = set(hist.values())
    if len(hist) != 81 or fibs != {729}:
        viol(tag, 'onto %d (want 81) fibers %s (want {729})'
             % (len(hist), sorted(fibs)[:5]))
    if verd.get('DEC') != 26244 or verd.get('DRAIN') != 32805:
        viol(tag, 'verdict %s != DEC 26244 / DRAIN 32805' % verd)
    say('-- %s: 59,049 exhaustive; ONTO 9x9 fiber 729; DEC/DRAIN '
        '%s; trichotomy same-side leg exact [%.1fs]'
        % (tag, verd, time.time() - T0))


def frb_pari():
    import cypari2
    pari = cypari2.Pari()
    p, N, m = 3, 6, 4
    tag = 'FRB-pari'
    R = G.Zp(p, N)
    rng = random.Random(31)
    got = 0
    tries = 0
    while got < 25 and tries < 200:
        tries += 1
        a0 = p ** 4 + rng.randrange(3) * p ** 5
        a1 = rng.randrange(3) * p ** 4 + rng.randrange(3) * p ** 5
        a2 = p ** 2 + sum(rng.randrange(3) * p ** h for h in (3, 4, 5))
        a3 = sum(rng.randrange(3) * p ** h for h in (2, 3, 4, 5))
        st = [a0, a1, a2, a3]
        ch1, _ = G.extract_child(R, N, st, m, 1, 1, p)
        ch2, _ = G.extract_child(R, N, st, m, 1, 2, p)
        if R.val(ch1[0], 2) != 1 or R.val(ch2[0], 2) != 1:
            continue  # want fully-DEC members
        fx = pari.Polrev([int(x) for x in st] + [1])
        if pari.poldisc(fx) == 0:
            continue
        fac = pari.factorpadic(fx, p, 60)
        nfac = int(fac.matsize()[0])
        degs, ok = [], True
        for i in range(nfac):
            gj = fac[0][i]
            dg = int(pari.poldegree(gj))
            degs.append(dg)
            if dg != 2:
                ok = False
                continue
            vd = int(pari.valuation(pari.poldisc(gj), p))
            if vd % 2 == 0:
                ok = False
        if sorted(degs) != [2, 2] or not ok:
            viol(tag, 'sigma degs %s (want two ramified quadratics)'
                 % (degs,))
        got += 1
        note(tag)
    if got < 25:
        viol(tag, 'only %d DEC disc!=0 members' % got)
    say('-- %s: %d fully-DEC lifts -> two ramified quadratics each '
        '(sigma {(2,1),(2,1)}) [%.1fs]' % (tag, got, time.time() - T0))


# ---------------------------------------------------------- FR-C
def frc_cell(tag, p, N, m, mk, sig_want, k, z, Wc_want, ncl, fib,
             dec_want, drn_want):
    R = G.Zp(p, N)
    ctx = {'p': p, 'cs_events': []}
    hist = {}
    verd = {'DEC': 0, 'DRAIN': 0}
    tot = 0
    for st in mk():
        tot += 1
        if sig_of(R, N, st, m) != sig_want:
            viol(tag, 'sides %s' % (st,))
            continue
        v, sg = G.read_cluster(R, N, list(st), ctx)
        verd[v] = verd.get(v, 0) + 1
        child, Wc = G.extract_child(R, N, st, m, k, z, p)
        if Wc != Wc_want:
            viol(tag, 'Wc %d != %d [capped refuted?]' % (Wc, Wc_want))
        key = tuple(c % p ** Wc_want for c in child)
        hist[key] = hist.get(key, 0) + 1
        note(tag)
    fibs = set(hist.values())
    if len(hist) != ncl or fibs != {fib}:
        viol(tag, 'onto %d (want %d) fibers %s (want {%d})'
             % (len(hist), ncl, sorted(fibs)[:5], fib))
    if verd.get('DEC') != dec_want or verd.get('DRAIN') != drn_want:
        viol(tag, 'verdict %s != DEC %d / DRAIN %d'
             % (verd, dec_want, drn_want))
    say('-- %s: %d exhaustive; Wc=%d; ONTO %d fiber %d; DEC %d / '
        'DRAIN %d [%.1fs]' % (tag, tot, Wc_want, len(hist), fib,
                              verd.get('DEC'), verd.get('DRAIN'),
                              time.time() - T0))


def c1_states():
    p, N = 2, 6
    for f1 in range(8):
        a1 = p ** 2 + sum(((f1 >> i) & 1) * p ** (3 + i)
                          for i in range(3))
        for f2 in range(16):
            a2 = sum(((f2 >> i) & 1) * p ** (2 + i) for i in range(4))
            yield [p ** 5, a1, a2]


def c2_states():
    p, N = 2, 8
    for f1 in range(8):
        a1 = p ** 4 + sum(((f1 >> i) & 1) * p ** (5 + i)
                          for i in range(3))
        for f2 in range(32):
            a2 = p ** 2 + sum(((f2 >> i) & 1) * p ** (3 + i)
                              for i in range(5))
            for f3 in range(64):
                a3 = sum(((f3 >> i) & 1) * p ** (2 + i)
                         for i in range(6))
                yield [p ** 7, a1, a2, a3]


def c3_states():
    p, N = 2, 9
    for f1 in range(8):
        a1 = p ** 5 + sum(((f1 >> i) & 1) * p ** (6 + i)
                          for i in range(3))
        for f2 in range(32):
            a2 = sum(((f2 >> i) & 1) * p ** (4 + i) for i in range(5))
            for f3 in range(128):
                a3 = p + sum(((f3 >> i) & 1) * p ** (2 + i)
                             for i in range(7))
                yield [p ** 8, a1, a2, a3]


def c1q3(tag):
    p, N, m = 3, 6, 3
    R = G.Zp(p, N)
    PB = p ** N
    rng = random.Random(13)
    for i in range(100):
        c, z = rng.choice((1, 2)), rng.choice((1, 2))
        f = [(-(c * p ** 3 + rng.randrange(p ** 2) * p ** 4)) % PB, 1]
        for _ in range(2):
            f = pmul(f, [(-(z * p + rng.randrange(p ** 4) * p ** 2))
                         % PB, 1], PB)
        st = f[:3]
        if sig_of(R, N, st, m) != [(0, 1, 1, 3), (1, 3, 1, 1)]:
            viol(tag, 'sides %s' % (st,))
            continue
        if R.val(st[2], N) != 1:
            viol(tag, 'odd-q pin dead: v(a2) != 1')
        _, Wc = G.extract_child(R, N, st, m, 1, z, p)
        if Wc != 3:
            viol(tag, 'Wc %d != 3' % Wc)
        note(tag)
    say('-- %s: 100 samples, odd-q pin live, Wc=3 exact [%.1fs]'
        % (tag, time.time() - T0))


def main():
    say('GENIND passPE5 FRESH ROUTE (NINEMIX n=9 + SAMESIDE + '
        'STEEPSCAN)')
    say('sealed runner md5 %s VERIFIED; imported read-only' % md5)
    fra_samples(2, 200, 'FRA-nm-q2')
    fra_samples(3, 120, 'FRA-nm-q3')
    fra_box(2, (5, 6, 7, 8), (4, 5, 6, 7), 5, 256, 'FRA-box-q2')
    fra_box(3, (5, 6), (4, 5), 3, 81, 'FRA-box-q3')
    fra_pari(2, 15, 'FRA-pari-q2')
    fra_pari(3, 10, 'FRA-pari-q3')
    fra_tooth('FRA-tooth')
    frb_run()
    frb_pari()
    frc_cell('FRC-C1', 2, 6, 3, c1_states,
             [(0, 1, 1, 3), (1, 3, 1, 1)], 1, 1, 3, 16, 8, 80, 48)
    frc_cell('FRC-C2', 2, 8, 4, c2_states,
             [(0, 1, 1, 3), (1, 2, 1, 2), (2, 4, 1, 1)], 1, 1, 4,
             64, 256, 13312, 3072)
    frc_cell('FRC-C3', 2, 9, 4, c3_states,
             [(0, 1, 1, 3), (1, 3, 1, 2), (3, 4, 1, 1)], 2, 1, 2,
             4, 8192, 16384, 16384)
    c1q3('FRC-C1q3')
    n = sum(TALLY.values())
    verdict = 'GREEN' if not VIOL else 'RED (%d violations)' % len(VIOL)
    say('')
    for k in sorted(TALLY):
        say('  %-14s %d' % (k, TALLY[k]))
    say('VERDICT: %s — %d checks, %d violations, %.1f s'
        % (verdict, n, len(VIOL), time.time() - T0))
    out = {'tally': TALLY, 'violations': VIOL,
           'elapsed_s': round(time.time() - T0, 1),
           'verdict': verdict, 'n_checks': n}
    with open(os.path.join(os.path.dirname(
            os.path.abspath(sys.argv[0])) if False else '.',
            'genind_pe5_fresh_results.json'), 'w') as fh:
        json.dump(out, fh, indent=1, sort_keys=True)
    return 0 if not VIOL else 1


if __name__ == '__main__':
    sys.exit(main())
