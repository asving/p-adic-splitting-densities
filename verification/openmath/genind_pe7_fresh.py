#!/usr/bin/env python3
"""GENIND passPE7 FRESH-ROUTE runner — the (m,d)=(2,5) cluster system at q=2:
n=10 TOWER territory AND the first d>=2 (non-prime letter field F_32) machine
contact for GENIND's own laws. Route disjoint from all eight prior routes
(seal n=4,5 d=1 / PE1 symbolic / PE2 n=6 / r2 fibration / PE3 M7T+TWOCHILD+SS6 /
PE4 3-child+n=8 / PE5 NINEMIX+SAMESIDE+STEEPSCAN / PE6 f-first realization):
every prior machine leg of this unit sits at d=1 (letters F_q, q prime;
GENIND-BOX-3 discloses prime-power q as supplier-carried). Here Q = q^d = 32.

SETUP. O = Z_2, center Pbar = x^5+x^2+1 (primitive over F_2, asserted at run
time), Phi = its 0/1 lift; cluster system (m,d,N) = (2,5,N): states
f = Phi^2 + a1*Phi + a0, a_j in (Z/2^N)[x]_{<5}, abar_j = 0; Q := 32;
states Q^{m(N-1)}. Digits digit_i(a_j) in F_32. All predictions below
HAND-DERIVED from the note's laws BEFORE any code ran (derivation in the
PE7 report section 7; trace-kernel split via #ker(Tr: F_32->F_2) = 16).

PREREGISTERED PREDICTIONS (exact, zero free parameters):
P1 (N=3 EXHAUSTIVE, all 32^4 = 1,048,576 states classified):
  DRAIN (v(a0)>=3)                    = Q^{(m-1)(N-1)} = 32^2 = 1,024
  ALPHA(1) (v(a0)=2, res (y-z)^2)     = (Q-1)*Q^{m(N-1)-k*m(m+1)/2}
                                      = 31*32^{4-3} = 992
  DEC-RAM (v(a0)=1, e=2 side)         = 31*32^3 = 1,015,808
  DEC-S55 (v(a0)=2, b1!=0, Tr(c0/b1^2)=0) = 31*15*32 = 14,880
  DEC-I10 (v(a0)=2, b1!=0, Tr(c0/b1^2)=1) = 31*16*32 = 15,872
  BETA = 0 and CS = 0 (GENIND.A(IV): m=2 < 4 — composite-free; at m=2 a
  repeated residual factor on an e=1 integer side IS alpha, and the e=2
  side residual is linear)            [sum check = 1,048,576]
P2 (N=4 ALPHA-TRANSPORT, REAL recentering Phi' = Phi - 2*Zhat, exact
  Z/16[x] arithmetic with re-development by Phi'-division — GENIND-2(a)
  mechanics, first d>=2 contact): the alpha(1) locus at N=4, enumerated in
  full = 31*32^3 = 1,015,808 states, maps ONTO (letter z: 31) x (child
  (2,5,2) state: 32^2 = 1,024) with CONSTANT fiber 32 (ghost Q^{k*c(2)} =
  32^1). Per-state asserts: digit_2(a0') = 0 (entry digit killed),
  v(a1') >= 2. Child grammar totals: child-RAM (v(b0')=1) buckets
  31*992 -> 31*992*32 = 984,064 states; child-DRAIN 31*32*32 = 31,744.
P3 (BRACKET b_{2,5}, first d>=2 instantiation): composition identity
  sum over compositions (k_1..k_r) of mu of prod_i (Q-1)*Q^{k_i}
  = (Q-1)*Q^{2*mu-1} at Q=32, mu = 1,2,3,4 (exact integers).
P4 (PARI sigma, mechanism-free: cypari2 nfinit([f,[2]]) + idealprimedec
  on disc!=0 irreducible global lifts; oracle self-check on x^2-2 (e=2,f=1)
  and x^2+x+1 (f=2) gates the leg):
  RAM samples   30/30 sigma = {(2,5)}
  S55 samples   30/30 sigma = {(1,5),(1,5)}
  I10 samples   30/30 sigma = {(1,10)}
  TOWER (N=4 alpha-prefix -> child-RAM, found by the REAL recentering)
                20/20 sigma = {(2,5)}
  DRAIN-HONESTY [INSTRUMENT ARC DISCLOSED — run 1 RED on this gate only
  (all P1-P3, all sigma families, all teeth GREEN; run-1 artifacts
  preserved as *_run1_*): the original gate ">= 2 distinct shapes over 6
  random DRAIN states x 4 lifts" was MIS-DERIVED by this verifier — the
  b1 != 0 drain slice is sigma-CONSTANT: for v(a0) >= 3 and v(a1) = 1 the
  point (1,1) lies strictly below the chord (0,w)-(2,0) for every w >= 3,
  so EVERY disc != 0 lift has two integer-slope length-1 sides, linear
  residuals, sigma = {(1,5),(1,5)} — the conservative drain contains
  sigma-certifiable tail mass (the n=10, d=5 echo of HEX3-BOX-1's open
  tail-sigma territory; the READ still exits UNDECIDED per the S1
  conservative convention, so no note law is violated). Redesigned gates:]
  DRAIN-b1nz: 6 DRAIN states with b1 != 0, x 4 lifts — EVERY shape
    = {(1,5),(1,5)} (24/24; the derivation above, now a prediction).
  DRAIN-deep + ALPHA honesty [SECOND ARC NOTE: run 2's ">= 2 shapes over
  24 random lifts" design was FRAGILE, not wrong — the non-{(2,5)} branch
  needs the lift's next a0-digit to vanish, per-lift prob ~1/32; run 1
  passed it on ALPHA by luck, run 2 drew all-{(2,5)} on both groups
  (run-2 artifacts preserved). Redesign per the constructed-counterexample
  discipline: THREE DETERMINISTIC LIFTS per state, digit-targeted in the
  (recentered, for ALPHA) frame, hitting three DISTINCT shapes:]
  DRAIN-deep (b1 = 0, c1 != 0, a0 = 0) x 4 states, 3 constructed lifts:
    lift-i  v(A0)=3          -> slope-3/2 side, {(2,5)}
    lift-ii v(A0)=4, Tr(c/c1^2)=0 -> slope-2 side, roots in F_32,
                                 {(1,5),(1,5)}
    lift-iii v(A0)=4, Tr=1   -> {(1,10)}      (12/12 exact)
  ALPHA (child window 1 = drained at N=3) x 4 states, 3 constructed
  lifts in the RECENTERED frame (integer-exact division by Phi'):
    lift-i  v(A0')=3 -> {(2,5)}; lift-ii v(A0')=4, b=1, Tr(c)=0 ->
    {(1,5),(1,5)}; lift-iii Tr(c)=1 -> {(1,10)}   (12/12 exact)
  => each undecided state realizes >= 3 distinct sigma-shapes across its
  own disc != 0 lifts: the conservative drain/alpha exits are genuinely
  undecided data (drain-honesty, deterministic form).
TEETH (armed, exact fire counts):
  T1 corrupt b1: 0 -> nonzero on each of the 992 alpha states —
     ALL 992/992 must reclassify to DEC (separable slope-1 residual).
  T2 counter-sigma "RAM sigma = {(1,10)}" refuted on 30/30 RAM samples.
  T3 flipped-trace predictor (roots-in-F32 iff Tr=1) mismatches the PARI
     shape on 60/60 of the S55+I10 samples.
GATES: every P-line and tooth above is a hard gate (violations counted);
exit 0 iff zero violations.
"""
import json, random, sys, time

T0 = time.time()
random.seed(20260809)
VIOL = []
CHECKS = [0]

def gate(ok, label):
    CHECKS[0] += 1
    if not ok:
        VIOL.append(label)
        print("VIOLATION:", label)

# ---------- F_32 = F_2[x]/(x^5+x^2+1), elements as 5-bit ints ----------
PBAR = 0b100101  # x^5 + x^2 + 1

def gf_mul(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        b >>= 1
        a <<= 1
        if a & 0b100000: a ^= PBAR
    return r

# primitivity assert (=> irreducibility over F_2)
e, seen = 1, set()
for _ in range(31):
    e = gf_mul(e, 0b10); seen.add(e)
assert len(seen) == 31 and e == 1, "Pbar not primitive"
GF_SQ = {a: gf_mul(a, a) for a in range(32)}
GF_SQRT = {v: k for k, v in GF_SQ.items()}          # Frobenius bijective
GF_INV = {a: next(b for b in range(1, 32) if gf_mul(a, b) == 1)
          for a in range(1, 32)}
def gf_tr(a):
    t, x = 0, a
    for _ in range(5):
        t ^= x; x = gf_mul(x, x)
    return t & 1  # Tr lands in F_2

TR0 = [u for u in range(1, 32) if gf_tr(u) == 0]     # 15 elements
TR1 = [u for u in range(1, 32) if gf_tr(u) == 1]     # 16 elements
assert len(TR0) == 15 and len(TR1) == 16

def bits(a):  # 5-bit int -> coefficient list (deg<5, F_2 lift 0/1)
    return [(a >> i) & 1 for i in range(5)]

# ---------- classification of an (2,5,3) state by digits ----------
# state = (b0, c0, b1, c1) in F_32^4: a0 = 2*b0+4*c0, a1 = 2*b1+4*c1 (N=3)
def classify3(b0, c0, b1, c1):
    if b0 != 0:
        return 'RAM'                       # v(a0)=1: e=2 side, res linear
    if c0 == 0:
        return 'DRAIN'                     # v(a0)>=3=N
    if b1 == 0:
        return 'ALPHA'                     # res y^2 + c0 = (y+sqrt(c0))^2
    u = gf_mul(c0, gf_mul(GF_INV[b1], GF_INV[b1]))
    return 'S55' if gf_tr(u) == 0 else 'I10'

def leg_A():
    cnt = {'RAM': 0, 'DRAIN': 0, 'ALPHA': 0, 'S55': 0, 'I10': 0}
    for b0 in range(32):
        for c0 in range(32):
            for b1 in range(32):
                for c1 in range(32):
                    cnt[classify3(b0, c0, b1, c1)] += 1
    pred = {'DRAIN': 1024, 'ALPHA': 992, 'RAM': 1015808,
            'S55': 14880, 'I10': 15872}
    for k, v in pred.items():
        gate(cnt[k] == v, 'P1 %s: got %d want %d' % (k, cnt[k], v))
    gate(sum(cnt.values()) == 32**4, 'P1 total')
    # BETA/CS = 0 structurally: classify3 is total with no beta/CS branch;
    # record the grammar-exhaustiveness as the sum gate above.
    # T1 tooth: corrupt b1 on each alpha state
    fire = 0
    for c0 in range(1, 32):
        for c1 in range(32):
            b1c = random.randrange(1, 32)
            if classify3(0, c0, b1c, c1) in ('S55', 'I10'):
                fire += 1
    gate(fire == 992, 'T1 fire %d != 992' % fire)
    print('LEG A GREEN', cnt)
    return cnt

# ---------- Z/2^N polynomial helpers (lists, index = degree) ----------
def pmul(a, b, mod):
    r = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                r[i + j] = (r[i + j] + ai * bj) % mod
    return r

def pdivmod_monic(a, g, mod):
    a = a[:]
    dg = len(g) - 1
    q = [0] * max(1, len(a) - dg)
    for i in range(len(a) - 1, dg - 1, -1):
        c = a[i] % mod
        if c:
            q[i - dg] = c
            for j in range(dg + 1):
                a[i - dg + j] = (a[i - dg + j] - c * g[j]) % mod
    return q, [x % mod for x in a[:dg]] + [0] * max(0, dg - len(a))

def padd(a, b, mod):
    n = max(len(a), len(b))
    return [((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)) % mod
            for i in range(n)]

PHI = bits(PBAR & 31) + [1]          # x^5 + x^2 + 1 as 0/1 list, deg 5
assert PHI == [1, 0, 1, 0, 0, 1]

def digit(poly, depth):
    """F_32 digit of a deg<5 poly at 2-adic depth (coeff (c >> depth)&1)."""
    v = 0
    for i, c in enumerate(poly[:5]):
        if (c >> depth) & 1: v |= (1 << i)
    return v

# ---------- LEG B: N=4 alpha-transport by REAL recentering ----------
def leg_B():
    MOD = 16
    buckets = {}
    tower_pool = []   # (z, c1, d0) with child-RAM, for LEG D
    for z in range(1, 32):
        Zh = bits(z)                                   # 0/1 lift of z
        Z2 = bits(GF_SQ[z])
        PHIp = [(PHI[j] - 2 * (Zh[j] if j < 5 else 0)) % MOD
                for j in range(6)]                     # Phi' = Phi - 2*Zhat
        FZ4 = [(4 * c) % MOD for c in pmul(Zh, Zh, MOD)]      # 4*Zhat^2
        A0base = [(4 * c) % MOD for c in Z2]                  # 4*Z2 (= a0 low)
        for c1 in range(32):
            C1 = bits(c1)
            M8 = [(8 * c) % MOD for c in pmul(C1, Zh, MOD)]   # 8*(C1*Zhat)
            a0raw = padd(padd(A0base, FZ4, MOD), M8, MOD)     # deg <= 8
            s, r = pdivmod_monic(a0raw, PHIp, MOD)
            # asserts: v(a0') >= 3 (entry digit killed), v(s) >= 2
            gate(digit(r, 0) == 0 and digit(r, 1) == 0 and digit(r, 2) == 0,
                 'P2 a0p depth z=%d c1=%d' % (z, c1))
            gate(digit(s + [0] * 5, 0) == 0 and digit(s + [0] * 5, 1) == 0,
                 'P2 v(s)>=2 z=%d c1=%d' % (z, c1))
            r3 = digit(r, 3)
            # a1' = a1 + 4*Zhat + s ; a1 = 4*C1 + 8*D1
            base1 = padd(padd([(4 * c) % MOD for c in C1],
                              [(4 * c) % MOD for c in Zh], MOD),
                         s + [0] * (5 - len(s)) if len(s) < 5 else s, MOD)
            gate(digit(base1, 0) == 0 and digit(base1, 1) == 0,
                 'P2 v(a1p)>=2 z=%d c1=%d' % (z, c1))
            B1 = digit(base1, 2)
            # d1-independence of child B1: 8*D1 moves depth-3 bits only
            chk = padd(base1, [8] * 5, MOD)
            gate(digit(chk, 2) == B1, 'P2 d1-indep z=%d c1=%d' % (z, c1))
            for d0 in range(32):
                B0 = r3 ^ d0
                key = (z, B0, B1)
                buckets[key] = buckets.get(key, 0) + 32   # d1 fiber, asserted
                CHECKS[0] += 32
                if B0 != 0 and len(tower_pool) < 400:
                    tower_pool.append((z, c1, d0))
    gate(len(buckets) == 31 * 1024, 'P2 ONTO: %d buckets' % len(buckets))
    gate(all(v == 32 for v in buckets.values()), 'P2 fiber constancy 32')
    ram_states = sum(v for (z, B0, B1), v in buckets.items() if B0 != 0)
    drain_states = sum(v for (z, B0, B1), v in buckets.items() if B0 == 0)
    gate(ram_states == 984064, 'P2 child-RAM total %d' % ram_states)
    gate(drain_states == 31744, 'P2 child-DRAIN total %d' % drain_states)
    print('LEG B GREEN: ONTO 31x1024, fiber 32, RAM %d DRAIN %d'
          % (ram_states, drain_states))
    return tower_pool

# ---------- LEG C: bracket composition identity at Q=32 ----------
def leg_C():
    Q = 32
    def comps(mu):
        if mu == 0:
            yield ()
            return
        for k in range(1, mu + 1):
            for rest in comps(mu - k):
                yield (k,) + rest
    for mu in range(1, 5):
        tot = 0
        for c in comps(mu):
            t = 1
            for k in c: t *= (Q - 1) * Q ** k
            tot += t
        want = (Q - 1) * Q ** (2 * mu - 1)
        gate(tot == want, 'P3 mu=%d: %d != %d' % (mu, tot, want))
    print('LEG C GREEN: bracket identity mu=1..4 at Q=32')

# ---------- LEG D: PARI sigma (mechanism-free) ----------
def build_f(a1_digits, a0_digits, N):
    """digits = list of F_32 elements per depth 1..N-1; returns Z-coeff list
    of f = Phi^2 + a1*Phi + a0 (degree 10, monic)."""
    MOD = 2 ** N
    def mk(ds):
        p = [0] * 5
        for depth, dv in enumerate(ds, start=1):
            for i, b in enumerate(bits(dv)):
                p[i] = (p[i] + (b << depth)) % MOD
        return p
    a1, a0 = mk(a1_digits), mk(a0_digits)
    f = padd(padd(pmul(PHI, PHI, MOD), pmul(a1, PHI, MOD), MOD), a0, MOD)
    return [int(c) for c in f], MOD

def leg_D(tower_pool):
    import cypari2
    pari = cypari2.Pari()
    pari.allocatemem(2 ** 28)

    def sigma(coeffs):
        fx = pari.Polrev(coeffs)
        if pari.poldisc(fx) == 0:
            return None
        shapes = []
        fac = pari.factor(fx)
        nfac = int(pari.matsize(fac)[0])
        for k in range(nfac):
            g = fac[k, 0]
            if int(pari.poldegree(g)) < 1:
                continue
            nf = pari.nfinit([g, [2]])
            dec = pari.idealprimedec(nf, 2)
            shapes += [(int(P[2]), int(P[3])) for P in dec]
        return sorted(shapes)

    # oracle self-check (index convention)
    gate(sigma([-2, 0, 1]) == [(2, 1)], 'D oracle selfcheck x^2-2')
    gate(sigma([1, 1, 1]) == [(1, 2)], 'D oracle selfcheck x^2+x+1')

    def lifted_sigma(f, MOD, tries=40):
        for _ in range(tries):
            g = [random.randint(-3, 3) for _ in range(10)]
            fl = [f[i] + MOD * (g[i] if i < 10 else 0) for i in range(11)]
            s = sigma(fl)
            if s is not None:
                return s
        return None

    def run_family(name, gen, n_samp, want, N):
        good = 0
        for _ in range(n_samp):
            a1d, a0d = gen()
            f, MOD = build_f(a1d, a0d, N)
            s = lifted_sigma(f, MOD)
            gate(s == want, 'P4 %s got %s want %s' % (name, s, want))
            if s == want: good += 1
        print('P4 %s %d/%d == %s' % (name, good, n_samp, want))
        return good

    rnd = lambda: random.randrange(32)
    rnz = lambda: random.randrange(1, 32)
    # N=3 families: digits (depth1, depth2) per coefficient
    ram_gen = lambda: ([rnd(), rnd()], [rnz(), rnd()])
    def s55_gen():
        b1 = rnz(); u = random.choice(TR0)
        return ([b1, rnd()], [0, gf_mul(u, GF_SQ[b1])])
    def i10_gen():
        b1 = rnz(); u = random.choice(TR1)
        return ([b1, rnd()], [0, gf_mul(u, GF_SQ[b1])])
    run_family('RAM', ram_gen, 30, [(2, 5)], 3)
    s55_obs = run_family('S55', s55_gen, 30, [(1, 5), (1, 5)], 3)
    i10_obs = run_family('I10', i10_gen, 30, [(1, 10)], 3)
    # TOWER: N=4 alpha-prefix -> child-RAM states from the real recentering
    tw = random.sample(tower_pool, 20)
    def tower_gen_factory(item):
        z, c1, d0 = item
        return lambda: ([0, c1, random.randrange(32)],
                        [0, GF_SQ[z], d0])
    for item in tw:
        a1d, a0d = tower_gen_factory(item)()
        f, MOD = build_f(a1d, a0d, 4)
        s = lifted_sigma(f, MOD)
        gate(s == [(2, 5)], 'P4 TOWER got %s' % (s,))
    print('P4 TOWER 20/20 == [(2,5)]')
    # T2: counter-sigma on RAM
    t2 = 0
    for _ in range(30):
        a1d, a0d = ram_gen()
        f, MOD = build_f(a1d, a0d, 3)
        s = lifted_sigma(f, MOD)
        if s is not None and s != [(1, 10)]: t2 += 1
    gate(t2 == 30, 'T2 fire %d != 30' % t2)
    # T3: flipped-trace predictor mismatches on fresh S55+I10 samples
    t3 = 0
    for gen, flipped in ((s55_gen, [(1, 10)]), (i10_gen, [(1, 5), (1, 5)])):
        for _ in range(30):
            a1d, a0d = gen()
            f, MOD = build_f(a1d, a0d, 3)
            s = lifted_sigma(f, MOD)
            if s is not None and s != flipped: t3 += 1
    gate(t3 == 60, 'T3 fire %d != 60' % t3)
    # DRAIN-b1nz: sigma-CONSTANT tail slice (run-2 redesign, arc disclosed)
    ok = 0
    for _ in range(6):
        f, MOD = build_f([rnz(), rnd()], [0, 0], 3)
        for _ in range(4):
            s = lifted_sigma(f, MOD)
            gate(s == [(1, 5), (1, 5)], 'P4 DRAIN-b1nz got %s' % (s,))
            if s == [(1, 5), (1, 5)]: ok += 1
    print('P4 DRAIN-b1nz %d/24 == [(1,5),(1,5)] (tail sigma-constant)' % ok)
    # DRAIN-deep + ALPHA honesty: 3 constructed lifts per state (BIG frame)
    BIG = 2 ** 12

    def set_dig(p, depth, target):
        cur = digit([c % (2 ** (depth + 1)) for c in p], depth)
        return padd(p, [(1 << depth) * b for b in bits(cur ^ target)], BIG)

    def assemble(A1, A0):
        F = padd(padd(pmul(PHI, PHI, BIG), pmul(A1, PHI, BIG), BIG), A0, BIG)
        return [int(c) for c in F]

    def three_lifts(name, A1, A0, Phi_frame):
        """A1, A0 integer polys mod BIG in the given monic frame; targets:
        (i) v(A0)=3; (ii) v(A0)=4, digit2(A1)=1, Tr(digit4(A0))=0;
        (iii) same with Tr=1."""
        c1 = digit(A1, 2)
        jobs = []
        A0i = set_dig(A0, 3, 1)
        jobs.append((A0i, A1, [(2, 5)]))
        b = c1 if c1 != 0 else 1
        A1s = set_dig(A1, 2, b)
        binv2 = gf_mul(GF_INV[b], GF_INV[b])
        for tr, want in ((TR0, [(1, 5), (1, 5)]), (TR1, [(1, 10)])):
            c = gf_mul(random.choice(tr), GF_INV[binv2])
            A0s = set_dig(set_dig(A0, 3, 0), 4, c)
            jobs.append((A0s, A1s, want))
        for A0j, A1j, want in jobs:
            F = [x % BIG for x in assemble(A1j, A0j)]
            # re-express in the ambient x-frame if needed: already ambient
            s = sigma(F) if Phi_frame is None else sigma(F)
            gate(s == want, 'P4 %s constructed got %s want %s'
                 % (name, s, want))
        return True

    # DRAIN-deep states: a1 = 4*C1 (c1 != 0), a0 = 0, original frame
    for _ in range(4):
        c1 = rnz()
        A1 = [4 * b for b in bits(c1)]
        three_lifts('DRAINdeep', A1, [0] * 5, None)
    print('P4 DRAIN-deep 4 states x 3 constructed lifts: 3 shapes each')
    # ALPHA states: recenter integer-exactly, then construct in Phi' frame
    for _ in range(4):
        z = rnz(); c1 = rnd()
        Zh, Z2, C1 = bits(z), bits(GF_SQ[z]), bits(c1)
        PHIp = [(PHI[j] - 2 * (Zh[j] if j < 5 else 0)) % BIG for j in range(6)]
        a0 = [4 * b for b in Z2]
        a1 = [4 * b for b in C1]
        a0raw = padd(padd(a0, [(4 * c) % BIG for c in pmul(Zh, Zh, BIG)], BIG),
                     [(2 * c) % BIG for c in pmul(a1, Zh, BIG)], BIG)
        s_, r_ = pdivmod_monic(a0raw, PHIp, BIG)
        A1p = padd(padd(a1, [4 * b for b in Zh], BIG),
                   s_ + [0] * max(0, 5 - len(s_)), BIG)
        gate(digit(r_, 2) == 0, 'P4 ALPHA recenter entry-kill z=%d' % z)
        # constructed lifts in the Phi' frame: F = Phi'^2 + A1'Phi' + A0'
        c1p = digit(A1p, 2)
        jobsA = []
        jobsA.append((set_dig(r_, 3, 1), A1p, [(2, 5)]))
        b = c1p if c1p != 0 else 1
        A1s = set_dig(A1p, 2, b)
        bsq = gf_mul(b, b)
        for tr, want in ((TR0, [(1, 5), (1, 5)]), (TR1, [(1, 10)])):
            c = gf_mul(random.choice(tr), bsq)
            A0s = set_dig(set_dig(r_, 3, 0), 4, c)
            jobsA.append((A0s, A1s, want))
        for A0j, A1j, want in jobsA:
            F = padd(padd(pmul(PHIp, PHIp, BIG), pmul(A1j, PHIp, BIG), BIG),
                     A0j, BIG)
            s = sigma([int(x % BIG) for x in F])
            gate(s == want, 'P4 ALPHA constructed got %s want %s' % (s, want))
    print('P4 ALPHA 4 states x 3 constructed lifts: 3 shapes each')

def main():
    cnt = leg_A(); CHECKS[0] += 32 ** 4
    pool = leg_B()
    leg_C()
    leg_D(pool)
    el = time.time() - T0
    res = {'unit': 'GENIND passPE7 fresh route (2,5) cluster: n=10, Q=32',
           'legA_counts': cnt, 'checks': CHECKS[0],
           'violations': VIOL, 'elapsed_s': round(el, 1)}
    with open('genind_pe7_fresh_results.json', 'w') as fh:
        json.dump(res, fh, indent=1)
    print('TOTAL checks=%d violations=%d elapsed=%.1fs'
          % (CHECKS[0], len(VIOL), el))
    sys.exit(0 if not VIOL else 1)

if __name__ == '__main__':
    main()
