"""GENIND r2 supplementary leg (ADDITIVE; sealed runner + artifacts BYTE-FROZEN).

Machine support for LEMMA GENIND-6 [r2, PE2-G1] (the mixed-opening
transport): a composite-stage opening whose polygon ALSO carries a
repeated-linear e=1 child fibers as
    (letter census) x q^9 x [child (2,1) system at window N-4]
                         x [stage coordinates at the certified windows],
verified on the ENTIRE first-live mixed family: genre M6 at
(q, m, d) = (q, 6, 1) -- hull (0,4)-(2,2)-(6,0), left side [0,2] slope 1
e=1 residual c(y-w)^2 (the beta-child), right side [2,6] slope 1/2 e=2
residual (y-z)^2, c = z^2 (the (mu,E,K) = (2,2,F_q) stage, h = 1) -- the
constructed instance of the GENIND passPE2 report (PE2-G1).

HAND-DERIVED PREDICTIONS (derived in the note's S4.3 [r2] BEFORE this
leg ran; smoke disclosure below):
  P-LAW    locus = (q-1)^2 q^{6N-17}; every member classifies CS with the
           key ('CSOTHER', 6, (2,6), 2, 1, 2, 1) AND the child side
           present ([(0,2) e=1 h=1] + [(2,6) e=2 h=1] side signature).
  P-CHILD  the sealed extract_child (factor-generic Hensel, non-unit-lead
           cofactor) applies verbatim at the mixed frame: D = 4,
           child window Wc = N-4; the child state ranges over the FULL
           (2,1,Wc) cluster space, q^{2(Wc-1)} classes.
  P-STAGE  the division ledger u = f/g certifies the stage cofactor at
           the RAGGED windows (u0,u1,u2,u3) mod
           (pi^{N-1}, pi^{N-2}, pi^{N-2}, pi^{N-3}), with entry budgets
           v(u0) = 2 & digit_2(u0) = z^2; v(u1) >= 2;
           digit_1(u2) = -2z (so v(u2) >= 2 at char 2, = 1 at odd q);
           v(u3) >= 1: q^{4(N-5)+4} classes per letter pair.
  P-SHARP  the Bezout refinement (v(r1) >= 2 forced by the u1-budget,
           r = u mod g; adjugate solve of u*Dg = delta mod g) certifies
           the SHARP windows (pi^{N-1}, pi^{N-1}, pi^{N-2}, pi^{N-2}),
           and these are sharp: ONE-DEEPER (u0 -> N, u2 -> N-1) must be
           lift-UNSTABLE (tooth T1).
  P-FIB    state -> (child class, stage class) is ONTO the full product
           with CONSTANT fiber, at BOTH window sets: fiber q^9 at the
           division-ledger windows (stage classes q^{4(N-5)+4}), fiber
           q^7 at the sharp windows (stage classes q^{4(N-5)+6});
           letters (q-1)^2; totals = the locus law both ways.
  P-STAB   child + stage classes at BOTH displayed window sets are
           LIFT-STABLE as EXACT-FACTOR data: the factors are Hensel-
           computed to the full precision of each lift and compared
           across independent lifts (see the instrument-arc disclosure
           below), not merely reproduced by a truncating pipeline.
  P-SIGMA  (read composition, child leg, mechanism-free): for states whose
           extracted child is DECIDED in its own (2,1,Wc) read
           (sigma_child = {(2,1)}), EVERY disc != 0 lift has val-1 block =
           ONE ramified quadratic under PARI factorpadic, and the val-1/2
           block has total degree 4 (block sizes lift-uniform).
  TEETH    T1 one-deeper-than-sharp windows (u0 -> N, u2 -> N-1) must
           BREAK exact-factor lift-stability (the sharpness tooth);
           T2 corrupting the vertex pin digit_2(a_2) must exit the genre;
           T4 the counter-prediction sigma_child = (1,2) (unramified) must
           be REFUTED by every PARI sample.

BLOCKS: B1 q=2 N=5 full locus (8,192); B2 q=2 N=6 full (524,288);
B3 q=3 N=5 full (z,w)=(1,1) letter slice (1,594,323; odd-q pins live);
B4 q=2 N=7 sampled (classification+budgets+stability);
B5 PARI sigma leg at (2,6,6) + drain-honesty diagnostic; B6 teeth.

INSTRUMENT-ARC DISCLOSURE (RED run 1 -> redesign -> this version).
Run 1 of this leg armed T1 as 'u3 one deeper than the division ledger
(pi^{N-2}) must be unstable' and tested stability by re-running the
TRUNCATING pipeline (Hensel to Wc = N-4) on perturbed lifts. T1 did
NOT fire (sole RED item; every mathematical check was green). Diagnosis,
in two parts, both disclosed because both are findings: (i) the
division-ledger window for u3 is CERTIFIED BUT NOT SHARP -- the Bezout
solve refines it one deeper (P-SHARP above; v(r1) >= 2 is forced by the
stage budget v(u1) >= 2, at every q); (ii) the run-1 stability test was
measuring ALGORITHM DETERMINISM, not certification: a pipeline that
truncates at Wc reproduces its own deeper digits on every lift because
they are zero-filled, so deep-window 'stability' was an artifact. The
redesigned test (this file) Hensel-lifts the factors to the FULL
precision of each independent random lift (near-exact factors) and
compares truncations -- under it the sharp windows are stable and the
one-deeper tooth fires (scratch: 56-58/60 states unstable at q=2 N=5,6
and q=3 N=5). Lesson recorded for the corpus: certified-window claims
must be tested against exact factors of INDEPENDENT lifts, never
against a truncating extraction's own reproducibility.

SMOKE DISCLOSURE: /tmp scratches (not committed) ran the fibration,
stability, and sharpness probes first (q=2 N=5,6; q=3 N=5) and
confirmed P-FIB/P-STAB/P-SHARP exactly; all predictions above were
hand-derived before the machine runs, per the note's S4.3 derivation.
The sealed runner genind_checks.py is imported READ-ONLY, md5-pinned.
"""
import sys, os, json, time, hashlib, random, itertools

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
RUNNER_MD5 = 'e7ca150b1b5cb13ad4f3350ac776aca2'

md5 = hashlib.md5(open(os.path.join(HERE, 'genind_checks.py'), 'rb')
                  .read()).hexdigest()
assert md5 == RUNNER_MD5, 'sealed runner md5 mismatch: %s' % md5
import genind_checks as G

VIOL = []
TALLY = {}
T0 = time.time()


def say(msg):
    print(msg)
    sys.stdout.flush()


def note(fam, n=1):
    TALLY[fam] = TALLY.get(fam, 0) + n


def viol(fam, detail):
    VIOL.append((fam, detail))
    say('VIOLATION [%s] %s' % (fam, detail))


# ------------------------------------------------------- the M6 locus
def m6_free(p, lo, N):
    """all values Sum_{h=lo..N-1} b_h p^h, b_h in F_p."""
    vals = [0]
    for h in range(lo, N):
        vals = [v + b * p ** h for v in vals for b in range(p)]
    return vals


def m6_states(p, N, z, w):
    """genre-M6 states (a0..a5) mod p^N at letters (z, w), d=1, q=p."""
    c = (z * z) % p
    pin = lambda h, d: (d % p) * p ** h
    a0s = [pin(4, c * w * w) + t for t in m6_free(p, 5, N)]
    a1s = [pin(3, -2 * c * w) + t for t in m6_free(p, 4, N)]
    a2s = [pin(2, c) + t for t in m6_free(p, 3, N)]
    a3s = m6_free(p, 2, N)
    a4s = [pin(1, -2 * z) + t for t in m6_free(p, 2, N)]
    a5s = m6_free(p, 1, N)
    for a0 in a0s:
        for a1 in a1s:
            for a2 in a2s:
                for a3 in a3s:
                    for a4 in a4s:
                        for a5 in a5s:
                            yield [a0, a1, a2, a3, a4, a5]


def m6_random_state(p, N, z, w, rng):
    c = (z * z) % p
    pin = lambda h, d: (d % p) * p ** h
    rnd = lambda lo: sum(rng.randrange(p) * p ** h for h in range(lo, N))
    return [pin(4, c * w * w) + rnd(5), pin(3, -2 * c * w) + rnd(4),
            pin(2, c) + rnd(3), rnd(2), pin(1, -2 * z) + rnd(2),
            rnd(1)]


M6_SIDES_SIG = [(0, 2, 1, 1), (2, 6, 2, 1)]   # (j0, j1, e, h) per side
M6_KEY = ('CS', ('CSOTHER', 6, (2, 6), 2, 1, 2, 1))


BUF = 4          # extraction runs at window N+BUF in ring p^{N+2*BUF}
W_COARSE = lambda N: (N - 1, N - 2, N - 2, N - 3)   # division ledger
W_SHARP = lambda N: (N - 1, N - 1, N - 2, N - 2)    # Bezout refinement
W_DEEPER = lambda N: (N, N - 1, N - 1, N - 2)       # tooth T1 target


def split_state(N, st, p, z, w, tag=''):
    """NEAR-EXACT factors of the given integer lift: the SEALED
    extract_child (factor-generic Hensel at the scaled frame) run at
    window N+BUF, then the stage cofactor u = f/g by the triangular
    division ledger at full lift precision. Returns (child_coeffs,
    (u0,u1,u2,u3)) as ring elements, after checking Wc and the stage
    entry budgets (P-CHILD/P-STAGE)."""
    Rh = G.Zp(p, N + 2 * BUF)
    child, Wch = G.extract_child(Rh, N + BUF, st, 6, 1, w % p, p)
    if Wch != N + BUF - 4:
        viol('SUP-CHILD', tag + ' Wc=%d != N+BUF-4' % Wch)
    ghat, A, B, _ = G.extract_child.last     # A = child factor PRE-recenter
    g1 = Rh.mul(A[1], Rh.pipw(1))            # g(x) = p^2 A(x/p)
    g0 = Rh.mul(A[0], Rh.pipw(2))
    u3 = Rh.sub(st[5], g1)
    u2 = Rh.sub(Rh.sub(st[4], g0), Rh.mul(g1, u3))
    u1 = Rh.sub(st[3], Rh.add(Rh.mul(g0, u3), Rh.mul(g1, u2)))
    u0 = Rh.sub(st[2], Rh.add(Rh.mul(g0, u2), Rh.mul(g1, u1)))
    ok = (Rh.val(u0, N) == 2 and Rh.res(u0, 2) == (z * z) % p
          and (Rh.val(u1, N) or N) >= 2
          and Rh.res(u2, 1) == (-2 * z) % p
          and (Rh.val(u2, N) or N) >= (2 if p == 2 else 1)
          and (Rh.val(u3, N) or N) >= 1)
    if not ok:
        viol('SUP-BUDGET', tag + ' u=%s' % ([u0, u1, u2, u3],))
    return child, (u0, u1, u2, u3)


def key_at(p, N, child, us, Wins):
    """truncate near-exact factor data to the claimed windows: child at
    the uniform window N-4, stage coefficients at Wins."""
    return (tuple(cc % p ** (N - 4) for cc in child),
            tuple(u % p ** wd for u, wd in zip(us, Wins)))


def fib_block(name, p, N, z, w, do_read=True):
    """full-locus fibration histograms at letters (z, w), BOTH window
    sets (coarse: fiber q^9; sharp: fiber q^7), from the canonical
    lift's near-exact factors."""
    R = G.Zp(p, N)
    ctx = {'cs_events': [], 'p': p}
    hist_c, hist_s = {}, {}
    n = 0
    for st in m6_states(p, N, z, w):
        n += 1
        sides = G.sides_of(R, N, st, 6)
        if [(s[0], s[2], s[4], s[5]) for s in sides] != M6_SIDES_SIG:
            viol(name, 'sides signature broke at %s' % (st,))
            continue
        if do_read:
            ev = []
            v, _ = G.read_cluster(R, N, list(st), ctx, top_events=ev)
            if v != 'CS' or ev[0] != M6_KEY:
                viol(name, 'classification %s %s at %s' % (v, ev, st))
        child, us = split_state(N, st, p, z, w, tag=name)
        kc = key_at(p, N, child, us, W_COARSE(N))
        ks = key_at(p, N, child, us, W_SHARP(N))
        hist_c[kc] = hist_c.get(kc, 0) + 1
        hist_s[ks] = hist_s.get(ks, 0) + 1
        note(name)
    pred_n = p ** (6 * N - 17)
    pred_c = p ** (2 * (N - 5))
    if n != pred_n:
        viol(name, 'locus %d != %d' % (n, pred_n))
    for hist, pred_s, fib_e, lab in (
            (hist_c, p ** (4 * (N - 5) + 4), 9, 'coarse'),
            (hist_s, p ** (4 * (N - 5) + 6), 7, 'sharp')):
        fibs = set(hist.values())
        ncl = len(set(k[0] for k in hist))
        nst = len(set(k[1] for k in hist))
        if ncl != pred_c or nst != pred_s or len(hist) != pred_c * pred_s:
            viol(name, '%s classes %dx%d/%d != %dx%d' %
                 (lab, ncl, nst, len(hist), pred_c, pred_s))
        if fibs != {p ** fib_e}:
            viol(name, '%s fibers %s != {%d}' %
                 (lab, sorted(fibs)[:5], p ** fib_e))
        say('-- %s [%s windows]: locus %d; ONTO %d x %d product; fibers'
            ' %s (= q^%d); %.1fs'
            % (name, lab, n, ncl, nst, sorted(fibs), fib_e,
               time.time() - T0))
    return hist_c


def stab_block(name, p, N, z, w, n_states, n_lifts, windows='both',
               expect_fail=False, seed=11):
    """EXACT-FACTOR lift-stability (P-STAB / P-SHARP / tooth T1): the
    factors are Hensel-computed to each independent lift's full
    precision and their truncations compared; windows in
    {'both','deeper'}."""
    rng = random.Random(seed)
    wsets = ([W_COARSE(N), W_SHARP(N)] if windows == 'both'
             else [W_DEEPER(N)])
    bad = 0
    for i in range(n_states):
        st = m6_random_state(p, N, z, w, rng)
        base = None
        for t in range(n_lifts):
            st2 = [cc + p ** N * rng.randrange(p ** 4) for cc in st]
            child, us = split_state(N, st2, p, z, w, tag=name)
            key = tuple(key_at(p, N, child, us, ws) for ws in wsets)
            if base is None:
                base = key
            elif key != base:
                bad += 1
                break
        note(name)
    if expect_fail:
        if bad == 0:
            viol(name, 'TOOTH DID NOT FIRE (one-deeper-than-sharp'
                 ' windows looked stable)')
        else:
            say('-- %s: TOOTH FIRED: %d/%d states exact-factor-UNSTABLE'
                ' one window deeper than sharp (sharpness confirmed)'
                % (name, bad, n_states))
    else:
        if bad:
            viol(name, '%d/%d states exact-factor-UNSTABLE at displayed'
                 ' windows' % (bad, n_states))
        else:
            say('-- %s: %d states x %d lifts exact-factor-STABLE at both'
                ' displayed window sets (coarse + sharp)'
                % (name, n_states, n_lifts))
    return bad


# --------------------------------------------------- PARI sigma leg (B5)
def pari_block(name, N=6, n_dec=120, n_lifts=3, n_drain=8, seed=23):
    """P-SIGMA: mechanism-free read-composition check on the child leg.
    For child-DECIDED states, every disc != 0 lift must carry the val-1
    block as ONE RAMIFIED QUADRATIC (= sigma_child {(2,1)} composed into
    the ambient), and the val-1/2 (stage) block must have total degree 4.
    T4 tooth: the counter-prediction 'unramified (1,2)' must be refuted
    by every sample. Plus the drain-honesty diagnostic (ungated)."""
    sys.path.insert(0, os.path.expanduser(
        '~/.local/lib/python3.10/site-packages'))
    import cypari2
    pari = cypari2.Pari()
    pari.allocatemem(1 << 28, silent=True)
    p, z, w = 2, 1, 1
    R = G.Zp(p, N)
    rng = random.Random(seed)
    Wc = N - 4

    def lift_groups(st):
        F = pari.Pol(list(reversed(
            [(cc + p ** N * rng.randrange(p ** 16)) for cc in st] + [1])))
        if pari.poldisc(F) == 0:
            return None
        fa = pari.factorpadic(F, p, 60)
        v1, v12deg = [], 0
        for i in range(len(fa[0])):
            h, mult = fa[0][i], int(fa[1][i])
            if mult != 1:
                return None
            d = int(pari.poldegree(h))
            v0 = int(pari.valuation(h.polcoef(0), p))
            if v0 * 2 == d:                       # root val 1/2
                v12deg += d
            elif v0 == d:                          # root val 1
                if d == 2:
                    b1v = (int(pari.valuation(h.polcoef(1), p))
                           if h.polcoef(1) != 0 else 99)
                    v1.append('ram2' if b1v >= 2 else 'unram2')
                else:
                    v1.append('lin%d' % d)
            else:
                return ('BADVAL', d, v0)
        return tuple(sorted(v1)), v12deg

    got_dec, t4_refuted = 0, 0
    while got_dec < n_dec:
        st = m6_random_state(p, N, z, w, rng)
        child, _ = split_state(N, st, p, z, w, tag=name)
        cclass = tuple(cc % p ** Wc for cc in child)
        ctx = {'cs_events': [], 'p': p}
        v, sig = G.read_cluster(G.Zp(p, Wc), Wc, list(cclass), ctx)
        if v != 'DEC':
            continue
        got_dec += 1
        if sig != ((2, 1),):
            viol(name, 'child DEC sigma %s != ((2,1),) at %s'
                 % (sig, cclass))
        done = 0
        while done < n_lifts:
            gr = lift_groups(st)
            if gr is None:
                continue
            if gr and gr[0] == 'BADVAL':
                viol(name, 'unexpected root valuation %s' % (gr,))
                break
            shapes, v12deg = gr
            done += 1
            note(name + '-lift')
            if shapes != ('ram2',):
                viol(name, 'val-1 block %s != one ramified quadratic'
                     ' (child-DEC state %s)' % (shapes, st))
            else:
                t4_refuted += 1          # refutes 'unram2' counter-claim
            if v12deg != 4:
                viol(name, 'val-1/2 (stage) block degree %d != 4'
                     % v12deg)
    if t4_refuted != n_dec * n_lifts:
        viol(name + '-T4', 'tooth: unramified counter-prediction only'
             ' refuted %d/%d times' % (t4_refuted, n_dec * n_lifts))
    else:
        say('-- %s: %d child-DEC states x %d lifts: val-1 block = ONE'
            ' RAMIFIED QUADRATIC every time (T4 counter-prediction'
            ' refuted %d/%d); stage block degree 4 every time'
            % (name, n_dec, n_lifts, t4_refuted, n_dec * n_lifts))
    # drain-honesty diagnostic (UNGATED): child-DRAIN states should show
    # sigma variety across lifts (the conservative drain is honest)
    variety = []
    got = 0
    while got < n_drain:
        st = m6_random_state(p, N, z, w, rng)
        child, _ = split_state(N, st, p, z, w, tag=name)
        cclass = tuple(cc % p ** Wc for cc in child)
        if cclass[0] != 0:                # want v(b0) >= Wc: child DRAIN
            continue
        got += 1
        shapes = set()
        tries = 0
        while len(shapes) < 2 and tries < 30:
            gr = lift_groups(st)
            tries += 1
            if gr is None or gr[0] == 'BADVAL':
                continue
            shapes.add(gr[0])
        variety.append(sorted(shapes))
    say('-- %s: drain-honesty diagnostic (ungated): child-DRAIN val-1'
        ' shapes across lifts: %s' % (name, variety))


# ------------------------------------------------------------- teeth
def tooth_pin(name, N=6, n=20, seed=31):
    """T2: corrupting the vertex pin digit_2(a_2) must exit the genre."""
    p, z, w = 2, 1, 1
    R = G.Zp(p, N)
    rng = random.Random(seed)
    fired = 0
    for i in range(n):
        st = m6_random_state(p, N, z, w, rng)
        st[2] -= G.Zp(p, N).res(st[2], 2) * p ** 2     # kill the vertex pin
        sides = G.sides_of(R, N, st, 6)
        if [(s[0], s[2], s[4], s[5]) for s in sides] != M6_SIDES_SIG:
            fired += 1
    if fired != n:
        viol(name, 'tooth fired only %d/%d' % (fired, n))
    else:
        say('-- %s: TOOTH FIRED %d/%d (corrupted vertex pin exits the'
            ' genre signature)' % (name, fired, n))


# --------------------------------------------------------------- main
def main():
    say('genindr2_supp: LEMMA GENIND-6 (mixed-opening transport) leg')
    say('sealed runner md5 %s VERIFIED; artifacts untouched' % RUNNER_MD5)
    results = {'runner_md5': RUNNER_MD5, 'blocks': {}}

    fib_block('B1-fib-q2N5', 2, 5, 1, 1)
    fib_block('B2-fib-q2N6', 2, 6, 1, 1)
    fib_block('B3-fib-q3N5', 3, 5, 1, 1, do_read=False)
    say('-- B3 note: odd-q pins live (digit_1(u2) = -2z = 1, v(u2) = 1)')

    stab_block('B1-stab-q2N5', 2, 5, 1, 1, 80, 6)
    stab_block('B2-stab-q2N6', 2, 6, 1, 1, 80, 6)
    stab_block('B3-stab-q3N5', 3, 5, 1, 1, 60, 5)

    # B4: q=2 N=7 sampled (beyond enumerable windows)
    p, N = 2, 7
    R = G.Zp(p, N)
    rng = random.Random(41)
    ctx = {'cs_events': [], 'p': p}
    for i in range(400):
        st = m6_random_state(p, N, 1, 1, rng)
        ev = []
        v, _ = G.read_cluster(R, N, list(st), ctx, top_events=ev)
        if v != 'CS' or ev[0] != M6_KEY:
            viol('B4-class-q2N7', '%s %s at %s' % (v, ev, st))
        note('B4-class-q2N7')
    say('-- B4-class-q2N7: 400 sampled states all classify to the M6 key')
    stab_block('B4-stab-q2N7', 2, 7, 1, 1, 300, 4)

    pari_block('B5-pari-q2N6')

    stab_block('T1-deepwindow-q2N6', 2, 6, 1, 1, 40, 6,
               windows='deeper', expect_fail=True)
    stab_block('T1-deepwindow-q3N5', 3, 5, 1, 1, 40, 6,
               windows='deeper', expect_fail=True, seed=13)
    tooth_pin('T2-pin')

    elapsed = time.time() - T0
    results['tallies'] = TALLY
    results['violations'] = VIOL
    results['elapsed_s'] = round(elapsed, 1)
    results['checks_total'] = sum(TALLY.values())
    verdict = 'GREEN' if not VIOL else 'RED'
    results['verdict'] = verdict
    with open(os.path.join(HERE, 'genindr2_supp_results.json'), 'w') as f:
        json.dump(results, f, indent=1, sort_keys=True)
    say('== %s: %d checks, %d violations, %.1fs =='
        % (verdict, results['checks_total'], len(VIOL), elapsed))
    return 0 if not VIOL else 1


if __name__ == '__main__':
    sys.exit(main())
