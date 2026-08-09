"""GENIND passPE3 FRESH ROUTE (hostile verifier; runs in /tmp only).

Route disclosed: differs from seal (n<=5 rosters), PE1 (exact n<=5 law
legs), PE2 (n=6 census + first n=6 oracle), r2 supp (M6 fibration).
THIS route: the corpus's FIRST n=7 composite evidence (constructed
mixed genre M7T with a (3,1)-child -- a child degree never seen in any
mixed frame), a DISTINCT-SLOPE two-child window adjudication (TWOCHILD,
n=4 N=7: beyond every sealed window), the STAGE-STEEPER-than-child
mixed genre SS6 (the honesty box's named blind spot), the wild p=3
child pins (3w = 0) in a mixed frame, and a PER-COEFFICIENT split of
the M6 sharpness tooth T1.

ALL PREDICTIONS HAND-DERIVED BEFORE THIS RUN (report S-legs):

M7T at (q,7,1): hull (0,5)-(3,2)-(7,0); left [0,3] slope 1 e=1
  residual z^2(y-w)^3 (the (3,1) beta-child); right [3,7] slope 1/2
  e=2 h=1 residual (y-z)^2 (the CS4-E stage). Pins: digit_5(a0)=-w^3z^2
  (v=5 exact), digit_4(a1)=3w^2z^2 (0 at p=3), digit_3(a2)=-3wz^2
  (0 at p=3), digit_2(a3)=z^2, v(a4)>=2, digit_1(a5)=-2z (0 at p=2),
  v(a6)>=1.  LOCUS = (q-1)^2 q^{7N-23}, visible iff N>=6.
  P-M7T-CHILD: extraction (sealed extract_child, k=1, root w) has
    D = 3*1 + 4*(1/2) = 5, Wc = N+BUF-5 on EVERY member (the capped/
    min reading of the M_l window formula).
  P-M7T-STAGE: division ledger u=f/g (g cubic): u3=a6-g2,
    u2=a5-g1-g2u3, u1=a4-g0-g1u3-g2u2, u0=a3-g0u3-g1u2-g2u1; entry
    budgets v(u0)=2 & digit_2(u0)=z^2, v(u1)>=2, digit_1(u2)=-2z
    (v>=2 at p=2, =1 odd p), v(u3)>=1.
  P-M7T-WIN: certified (coarse) windows from g_i known mod
    p^{Wc+3-i}: p=2: (u0,u1,u2,u3) mod (N-2,N-2,N-3,N-4);
    p=3: (N-2,N-3,N-3,N-4).
  P-M7T-FIB at (2,6): 524,288 states ONTO 1 child class x 32 stage
    classes with CONSTANT fiber 2^14 (exponent 14 = (7N-23)-3(N-6)
    -(4N-19), N-independent).
  P-M7T-STAB: exact-factor lift-stable at the coarse windows,
    (2,7) and (3,6) sampled.

TWOCHILD at (q,4,1): hull (0,6)-(2,2)-(4,0); TWO children at DISTINCT
  slopes: side A [0,2] slope 2 residual (y-w)^2, side B [2,4] slope 1
  residual (y-z)^2 (unit-twisted). Pins: digit_6(a0)=w^2z^2 (v=6),
  digit_4(a1)=-2wz^2 (0 at p=2 -> v>=5), digit_2(a2)=z^2,
  digit_1(a3)=-2z (0 at p=2 -> v>=2). LOCUS = (q-1)^2 q^{4N-17},
  visible iff N>=7 -- BEYOND every sealed roster window.
  P-TC-WINDOW (the adjudication): the shallower child B extracts at
    D = 2*1 + 2*min(2,1) = 4, Wc = N+BUF-4 -- the GENIND-3 statement
    display "M_l = N - (Sum_j mu_j k_j + ...)" read literally gives
    D = 2*2+2*1 = 6, M_B = N-6: REFUTED if Wc = N+BUF-4. The steeper
    child A extracts at D = 6 (both readings agree: control).
  P-TC-FIB at (2,7): 2,048 states ONTO 16 B-classes x 1 A-class,
    constant fiber 2^7; at (3,7): 177,147 ONTO 81 x 1, fiber 3^7.

SS6 at (q,6,1): hull (0,8)-(4,2)-(6,0); the stage STEEPER than the
  child: left [0,4] slope 3/2 e=2 h=3 residual (y-z)^2 (the CS4-E(3)
  stage), right [4,6] slope 1 e=1 residual (y-w)^2. (Refutes the
  honesty-box line "first live n >= 7 arrangements": live at n=6,
  N>=9.) Pins p=2: digit_8(a0)=z^2w^2, v(a1)>=7, v(a2)>=6,
  v(a3)>=4, digit_2(a4)=w^2, v(a5)>=2.
  P-SS6-CHILD: child extraction at k=1 root w: D = 2*1 + 4*min(3/2,1)
    = 6, Wc = N+BUF-6 (capped; uncapped reading would say 8).
  P-SS6-STAGE: ledger (g quadratic): budgets v(u0)=6 &
    digit_6(u0)=z^2, v(u1)>=5, v(u2)>=4 (p=2), v(u3)>=2.
  P-SS6-WIN p=2: (u0,u1,u2,u3) mod (N-2,N-3,N-4,N-5) lift-stable.

M6-SPLIT (per-coefficient sharpness of the r2 note's SHARP windows):
  the note claims "one further digit (u0 -> pi^N or u2 -> pi^{N-1}) is
  lift-UNSTABLE". Bezout first-order at p=2 gives Delta(u0) >= N
  (all four terms >= N), so u0-ONLY-deeper is predicted STABLE at
  (2,6) -- the u0 disjunct would then be machine-unsupported at p=2 --
  while u2-only-deeper fires (Delta g0 = N-2 exactly). Odd q: both
  fire (Delta g0*u2 = N-1 hits u0's height N-1). Measured, gated only
  on the DERIVED directions (u2-only fires everywhere; u0-only fires
  at odd q).
"""
import sys, os, json, time, hashlib, random

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
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
    VIOL.append((f, d))
    say('VIOLATION [%s] %s' % (f, d))


def free(p, lo, N):
    vals = [0]
    for h in range(lo, N):
        vals = [v + b * p ** h for v in vals for b in range(p)]
    return vals


def rnd_free(p, lo, N, rng):
    return sum(rng.randrange(p) * p ** h for h in range(lo, N))


def pin(p, h, d):
    return (d % p) * p ** h


# ---------------------------------------------------------------- M7T
def m7t_pins(p, N, z, w):
    return [pin(p, 5, -w**3 * z*z), pin(p, 4, 3*w*w*z*z),
            pin(p, 3, -3*w*z*z), pin(p, 2, z*z), 0, pin(p, 1, -2*z), 0]


M7T_LOS = [6, 5, 4, 3, 2, 2, 1]
M7T_SIG = [(0, 3, 1, 1), (3, 7, 2, 1)]


def m7t_state(p, N, z, w, rng):
    ps = m7t_pins(p, N, z, w)
    return [ps[j] + rnd_free(p, M7T_LOS[j], N, rng) for j in range(7)]


def m7t_split(N, st, p, z, w, tag):
    Rh = G.Zp(p, N + 2 * BUF)
    child, Wch = G.extract_child(Rh, N + BUF, st, 7, 1, w % p, p)
    if Wch != N + BUF - 5:
        viol(tag, 'Wc=%d != N+BUF-5 (capped window refuted?)' % Wch)
    ghat, A, B, _ = G.extract_child.last
    g2 = Rh.mul(A[2], Rh.pipw(1))
    g1 = Rh.mul(A[1], Rh.pipw(2))
    g0 = Rh.mul(A[0], Rh.pipw(3))
    u3 = Rh.sub(st[6], g2)
    u2 = Rh.sub(Rh.sub(st[5], g1), Rh.mul(g2, u3))
    u1 = Rh.sub(st[4], Rh.add(g0, Rh.add(Rh.mul(g1, u3), Rh.mul(g2, u2))))
    u0 = Rh.sub(st[3], Rh.add(Rh.mul(g0, u3),
                              Rh.add(Rh.mul(g1, u2), Rh.mul(g2, u1))))
    ok = (Rh.val(u0, N) == 2 and Rh.res(u0, 2) == (z*z) % p
          and (Rh.val(u1, N) or N) >= 2
          and Rh.res(u2, 1) == (-2*z) % p
          and (Rh.val(u2, N) or N) >= (2 if p == 2 else 1)
          and (Rh.val(u3, N) or N) >= 1)
    if not ok:
        viol(tag, 'stage budgets broke')
    return child, (u0, u1, u2, u3)


def m7t_wins(p, N):
    return ((N-2, N-2, N-3, N-4) if p == 2 else (N-2, N-3, N-3, N-4))


def m7t_key(p, N, child, us):
    return (tuple(c % p ** (N - 5) for c in child),
            tuple(u % p ** wd for u, wd in zip(us, m7t_wins(p, N))))


def m7t_fib(p, N, z, w):
    tag = 'FR-A-m7t-fib-q%dN%d' % (p, N)
    R = G.Zp(p, N)
    ctx = {'cs_events': [], 'p': p}
    hist = {}
    n = 0
    ps = m7t_pins(p, N, z, w)
    key0 = None
    for f0 in free(p, 6, N):
        for f1 in free(p, 5, N):
            for f2 in free(p, 4, N):
                for f3 in free(p, 3, N):
                    for f4 in free(p, 2, N):
                        for f5 in free(p, 2, N):
                            for f6 in free(p, 1, N):
                                st = [ps[0]+f0, ps[1]+f1, ps[2]+f2,
                                      ps[3]+f3, f4, ps[5]+f5, f6]
                                n += 1
                                sides = G.sides_of(R, N, st, 7)
                                if [(s[0], s[2], s[4], s[5])
                                        for s in sides] != M7T_SIG:
                                    viol(tag, 'sides %s' % (st,))
                                    continue
                                ev = []
                                v, _ = G.read_cluster(R, N, list(st),
                                                      ctx, top_events=ev)
                                if v != 'CS':
                                    viol(tag, 'verdict %s at %s' % (v, st))
                                if key0 is None:
                                    key0 = ev[0]
                                    say('-- %s: CS key read = %s'
                                        % (tag, (key0,)))
                                elif ev[0] != key0:
                                    viol(tag, 'key moved %s' % (ev,))
                                child, us = m7t_split(N, st, p, z, w, tag)
                                k = m7t_key(p, N, child, us)
                                hist[k] = hist.get(k, 0) + 1
                                note(tag)
    pred_n = p ** (7 * N - 23)
    pred_c = p ** (3 * (N - 6))
    pred_s = p ** ((4*N - 19) if p == 2 else (4*N - 20))
    fib_e = 14 if p == 2 else 15
    ncl = len(set(k[0] for k in hist))
    nst = len(set(k[1] for k in hist))
    fibs = set(hist.values())
    if n != pred_n:
        viol(tag, 'locus %d != %d' % (n, pred_n))
    if ncl != pred_c or nst != pred_s or len(hist) != pred_c * pred_s:
        viol(tag, 'classes %dx%d/%d != %dx%d'
             % (ncl, nst, len(hist), pred_c, pred_s))
    if fibs != {p ** fib_e}:
        viol(tag, 'fibers %s != {q^%d}' % (sorted(fibs)[:4], fib_e))
    say('-- %s: locus %d ONTO %d x %d, fibers %s (= q^%d) [%.1fs]'
        % (tag, n, ncl, nst, sorted(fibs), fib_e, time.time() - T0))


def m7t_sample(p, N, z, w, ns, tag):
    R = G.Zp(p, N)
    ctx = {'cs_events': [], 'p': p}
    rng = random.Random(101)
    for i in range(ns):
        st = m7t_state(p, N, z, w, rng)
        sides = G.sides_of(R, N, st, 7)
        if [(s[0], s[2], s[4], s[5]) for s in sides] != M7T_SIG:
            viol(tag, 'sides %s' % (st,))
        v, _ = G.read_cluster(R, N, list(st), ctx)
        if v != 'CS':
            viol(tag, 'verdict %s' % v)
        m7t_split(N, st, p, z, w, tag)
        note(tag)
    say('-- %s: %d sampled states: signature+read+budgets OK [%.1fs]'
        % (tag, ns, time.time() - T0))


def m7t_stab(p, N, z, w, ns, nl, tag):
    rng = random.Random(7)
    bad = 0
    for i in range(ns):
        st = m7t_state(p, N, z, w, rng)
        base = None
        for t in range(nl):
            st2 = [c + p ** N * rng.randrange(p ** 4) for c in st]
            child, us = m7t_split(N, st2, p, z, w, tag)
            k = m7t_key(p, N, child, us)
            if base is None:
                base = k
            elif k != base:
                bad += 1
                break
        note(tag)
    if bad:
        viol(tag, '%d/%d unstable at coarse windows' % (bad, ns))
    else:
        say('-- %s: %d x %d exact-factor-STABLE at coarse windows'
            % (tag, ns, nl))


# ----------------------------------------------------------- TWOCHILD
TC_SIG = [(0, 2, 1, 2), (2, 4, 1, 1)]


def tc_pins(p, z, w):
    return [pin(p, 6, w*w*z*z), pin(p, 4, -2*w*z*z),
            pin(p, 2, z*z), pin(p, 1, -2*z)]


TC_LOS = [7, 5, 3, 2]


def tc_split(N, st, p, z, w, tag):
    Rh = G.Zp(p, N + 2 * BUF)
    chB, WB = G.extract_child(Rh, N + BUF, st, 4, 1, z % p, p)
    if WB != N + BUF - 4:
        viol(tag + '-ADJ', 'child-B Wc=%d != N+BUF-4: capped reading '
             'REFUTED (literal display predicts N+BUF-6=%d)'
             % (WB, N + BUF - 6))
    chA, WA = G.extract_child(Rh, N + BUF, st, 4, 2, w % p, p)
    if WA != N + BUF - 6:
        viol(tag, 'child-A Wc=%d != N+BUF-6' % WA)
    return (tuple(c % p ** (N - 4) for c in chB),
            tuple(c % p ** (N - 6) for c in chA))


def tc_fib(p, N, z, w):
    tag = 'FR-B-twochild-q%dN%d' % (p, N)
    R = G.Zp(p, N)
    hist = {}
    n = 0
    ps = tc_pins(p, z, w)
    for f0 in free(p, TC_LOS[0], N):
        for f1 in free(p, TC_LOS[1], N):
            for f2 in free(p, TC_LOS[2], N):
                for f3 in free(p, TC_LOS[3], N):
                    st = [ps[0]+f0, ps[1]+f1, ps[2]+f2, ps[3]+f3]
                    n += 1
                    sides = G.sides_of(R, N, st, 4)
                    if [(s[0], s[2], s[4], s[5]) for s in sides] != TC_SIG:
                        viol(tag, 'sides %s' % (st,))
                        continue
                    k = tc_split(N, st, p, z, w, tag)
                    hist[k] = hist.get(k, 0) + 1
                    note(tag)
    pred_n = p ** (4 * N - 17)
    pred_B = p ** (2 * (N - 5))
    pred_A = p ** (2 * (N - 7))
    nB = len(set(k[0] for k in hist))
    nA = len(set(k[1] for k in hist))
    fibs = set(hist.values())
    fib_e = 7
    if n != pred_n:
        viol(tag, 'locus %d != %d' % (n, pred_n))
    if nB != pred_B or nA != pred_A or len(hist) != pred_B * pred_A:
        viol(tag, 'classes %dx%d/%d != %dx%d'
             % (nB, nA, len(hist), pred_B, pred_A))
    if fibs != {p ** fib_e}:
        viol(tag, 'fibers %s != {q^7}' % sorted(fibs)[:4])
    say('-- %s: locus %d ONTO %d B-classes x %d A-classes, fibers %s '
        '(= q^7) [%.1fs]' % (tag, n, nB, nA, sorted(fibs),
                             time.time() - T0))


def tc_stab(p, N, ns, nl, tag):
    """child-B class mod p^{N-4} (the CAPPED window) must be
    lift-stable: certifies the capped window as content, not merely
    as the extractor's arithmetic."""
    z = w = 1
    rng = random.Random(19)
    ps = tc_pins(p, z, w)
    bad = 0
    for i in range(ns):
        st = [ps[j] + rnd_free(p, TC_LOS[j], N, rng) for j in range(4)]
        base = None
        for t in range(nl):
            st2 = [c + p ** N * rng.randrange(p ** 4) for c in st]
            k = tc_split(N, st2, p, z, w, tag)
            if base is None:
                base = k
            elif k != base:
                bad += 1
                break
        note(tag)
    if bad:
        viol(tag, '%d/%d unstable at capped windows (N-4, N-6)'
             % (bad, ns))
    else:
        say('-- %s: %d x %d lift-STABLE at capped windows '
            '(child-B mod p^{N-4}, child-A mod p^{N-6})' % (tag, ns, nl))


# ---------------------------------------------------------------- SS6
SS6_SIG = [(0, 4, 2, 3), (4, 6, 1, 1)]


def ss6_state(p, N, z, w, rng):
    ps = [pin(p, 8, z*z*w*w), 0, pin(p, 5, -2*z*w*w) if p != 2 else 0,
          0, pin(p, 2, w*w), pin(p, 1, -2*w)]
    los = [9, 7, 6, 4, 3, 2]
    return [ps[j] + rnd_free(p, los[j], N, rng) for j in range(6)]


def ss6_leg(p, N, ns, nl, tag):
    z = w = 1
    R = G.Zp(p, N)
    ctx = {'cs_events': [], 'p': p}
    rng = random.Random(31)
    wins = (N-2, N-3, N-4, N-5)

    def split(st):
        Rh = G.Zp(p, N + 2 * BUF)
        child, Wch = G.extract_child(Rh, N + BUF, st, 6, 1, w % p, p)
        if Wch != N + BUF - 6:
            viol(tag + '-ADJ', 'child Wc=%d != N+BUF-6: capped reading '
                 'refuted? (uncapped display predicts N+BUF-8=%d)'
                 % (Wch, N + BUF - 8))
        ghat, A, B, _ = G.extract_child.last
        g1 = Rh.mul(A[1], Rh.pipw(1))
        g0 = Rh.mul(A[0], Rh.pipw(2))
        u3 = Rh.sub(st[5], g1)
        u2 = Rh.sub(Rh.sub(st[4], g0), Rh.mul(g1, u3))
        u1 = Rh.sub(st[3], Rh.add(Rh.mul(g0, u3), Rh.mul(g1, u2)))
        u0 = Rh.sub(st[2], Rh.add(Rh.mul(g0, u2), Rh.mul(g1, u1)))
        ok = (Rh.val(u0, N) == 6 and Rh.res(u0, 6) == (z*z) % p
              and (Rh.val(u1, N) or N) >= 5
              and (Rh.val(u2, N) or N) >= (4 if p == 2 else 3)
              and (Rh.val(u3, N) or N) >= 2)
        if not ok:
            viol(tag, 'stage budgets broke')
        return (tuple(c % p ** (N - 6) for c in child),
                tuple(u % p ** wd for u, wd in zip((u0, u1, u2, u3),
                                                   wins)))

    for i in range(ns):
        st = ss6_state(p, N, z, w, rng)
        sides = G.sides_of(R, N, st, 6)
        if [(s[0], s[2], s[4], s[5]) for s in sides] != SS6_SIG:
            viol(tag, 'sides %s' % (st,))
        v, _ = G.read_cluster(R, N, list(st), ctx)
        if v != 'CS':
            viol(tag, 'verdict %s' % v)
        base = None
        for t in range(nl):
            st2 = [c + p ** N * rng.randrange(p ** 4) for c in st]
            k = split(st2)
            if base is None:
                base = k
            elif k != base:
                viol(tag, 'unstable at derived windows')
                break
        note(tag)
    say('-- %s: %d states (sig+read+budgets+Wc) x %d lifts stable at '
        'windows %s [%.1fs]' % (tag, ns, nl, wins, time.time() - T0))


# ----------------------------------------- M6 per-coefficient T1 split
def m6_split_tooth(p, N, ns, nl, tag):
    z = w = 1
    rng = random.Random(53)
    W_SHARP = (N-1, N-1, N-2, N-2)
    variants = {'u0-only': (N, N-1, N-2, N-2),
                'u2-only': (N-1, N-1, N-1, N-2)}
    out = {}
    for lab, ws in variants.items():
        bad = 0
        for i in range(ns):
            st = G and None
            st = [0]*6
            c = (z*z) % p
            st = [pin(p, 4, c*w*w) + rnd_free(p, 5, N, rng),
                  pin(p, 3, -2*c*w) + rnd_free(p, 4, N, rng),
                  pin(p, 2, c) + rnd_free(p, 3, N, rng),
                  rnd_free(p, 2, N, rng),
                  pin(p, 1, -2*z) + rnd_free(p, 2, N, rng),
                  rnd_free(p, 1, N, rng)]
            base = None
            for t in range(nl):
                st2 = [cc + p ** N * rng.randrange(p ** 4) for cc in st]
                Rh = G.Zp(p, N + 2 * BUF)
                child, Wch = G.extract_child(Rh, N + BUF, st2, 6, 1,
                                             w % p, p)
                ghat, A, B, _ = G.extract_child.last
                g1 = Rh.mul(A[1], Rh.pipw(1))
                g0 = Rh.mul(A[0], Rh.pipw(2))
                u3 = Rh.sub(st2[5], g1)
                u2 = Rh.sub(Rh.sub(st2[4], g0), Rh.mul(g1, u3))
                u1 = Rh.sub(st2[3], Rh.add(Rh.mul(g0, u3),
                                           Rh.mul(g1, u2)))
                u0 = Rh.sub(st2[2], Rh.add(Rh.mul(g0, u2),
                                           Rh.mul(g1, u1)))
                k = (tuple(cc % p ** (N - 4) for cc in child),
                     tuple(u % p ** wd for u, wd in
                           zip((u0, u1, u2, u3), ws)))
                if base is None:
                    base = k
                elif k != base:
                    bad += 1
                    break
            note(tag)
        out[lab] = bad
        say('-- %s [%s]: %d/%d states unstable' % (tag, lab, bad, ns))
    # gates: derived directions only
    if out['u2-only'] == 0:
        viol(tag, 'u2-only-deeper STABLE: contradicts my derivation '
             'AND the note sharpness at u2')
    if p != 2 and out['u0-only'] == 0:
        viol(tag, 'u0-only-deeper stable at odd q: contradicts '
             'derivation Delta(g0)*u2 = N-1')
    return out


def main():
    say('pe3_fresh: GENIND passPE3 fresh route (n=7 M7T + TWOCHILD '
        'adjudication + SS6 + M6 split tooth)')
    # FR-B first (cheap, decisive window adjudication)
    tc_fib(2, 7, 1, 1)
    tc_fib(3, 7, 1, 1)
    tc_stab(2, 7, 80, 5, 'FR-B-tc-stab-q2N7')
    tc_stab(3, 7, 60, 4, 'FR-B-tc-stab-q3N7')
    # FR-A: M7T
    m7t_fib(2, 6, 1, 1)
    m7t_sample(2, 7, 1, 1, 400, 'FR-A-m7t-class-q2N7')
    m7t_sample(3, 6, 1, 1, 300, 'FR-A-m7t-class-q3N6-WILDp3')
    m7t_stab(2, 7, 1, 1, 120, 5, 'FR-A-m7t-stab-q2N7')
    m7t_stab(3, 6, 1, 1, 80, 4, 'FR-A-m7t-stab-q3N6-WILDp3')
    # FR-C: SS6 stage-steeper
    ss6_leg(2, 9, 250, 4, 'FR-C-ss6-q2N9')
    ss6_leg(3, 9, 120, 3, 'FR-C-ss6-q3N9')
    # FR-D: M6 per-coefficient tooth split
    r26 = m6_split_tooth(2, 6, 40, 6, 'FR-D-m6split-q2N6')
    r25 = m6_split_tooth(2, 5, 40, 6, 'FR-D-m6split-q2N5')
    r35 = m6_split_tooth(3, 5, 40, 6, 'FR-D-m6split-q3N5')
    res = {'tallies': TALLY, 'violations': VIOL,
           'm6_split': {'q2N6': r26, 'q2N5': r25, 'q3N5': r35},
           'elapsed_s': round(time.time() - T0, 1),
           'checks_total': sum(TALLY.values()),
           'verdict': 'GREEN' if not VIOL else 'RED'}
    with open(os.path.join(HERE, 'pe3_fresh_results.json'), 'w') as f:
        json.dump(res, f, indent=1, sort_keys=True, default=str)
    say('== %s: %d checks, %d violations, %.1fs =='
        % (res['verdict'], res['checks_total'], len(VIOL),
           res['elapsed_s']))
    return 0 if not VIOL else 1


if __name__ == '__main__':
    sys.exit(main())
