#!/usr/bin/env python3
"""H.116b (betaExtract_fiber_card) — certification battery for the RE-PLANTING construction.

Companion to the H.116b unit (blueprint CHAP-H ~line 8089, clause (ii) of the A-H.5 re-signed
pair).  Reuses the OM-2 battery's rings + conservative reader (OM2_genindb_battery.py).
Exact arithmetic, both rings (Zq and Fqt), exhaustive where the cell allows it.

THE CONSTRUCTION (outline, steps C1-C6):

  C1 (planted factor).  For a child lift b (deg mu, coords in the maximal ideal m), slope k,
     centre zhat:  P(b) := alphaParent(b, k, zhat)  [H.115b's inverse shear:
     coeff j = alphaFrame(b,zhat)_j * pi^{k(mu-j)}].  P(b) is monic deg mu, reduction X^mu,
     w-profile w_{k'}(P) = mu*min(k,k'), and its (k',z')-divided frame reductions for
     (k',z') != (k,z) are b-INDEPENDENT with UNIT constant term (three cases k'<k, =, >).
  C2 (peel).  Every lift of a beta-genre state factors EXACTLY as
     f = (prod_{p in L} P(b_p)) * K, where b_p is the (mu,k,z)_p Hensel block of f's p-frame
     (betaChild_spec's factorization + the mod-monic degree argument), K monic, reduction
     X^{m - sum mu}.
  C3 (replant).  Given targets t' (child states at windows N - D_p), set
        b'_p := b_p + Delta_p,   Delta_p := a FIXED section lift of (t'_p - t_p),
        f' := (prod P(b'_p)) * K,   c' := class of f' at window N.
  C4 (genre transport).  c' is a beta state with children EXACTLY L, contents D, and
     betaChild reads t'; CS/drain/full-child status transported from c.  Mechanisms:
     (a) (P(b')-P(b))-frames one digit under the content at EVERY slope (child/content
     transport, no polygons); (b) f'-f strictly above f's FULL Newton polygon at every
     (u,l) (side data + resPoly of f' = of f, the CS transport).
  C5 (stability/injectivity).  See FINDINGS below: the naive stability is REFUTED; the
     map is well defined from the CANONICAL lift, and is measured bijective.
  C6 (equicardinality).  All fibres of the joint child map over a genre (L, D) are
     equicardinal (measured EXACTLY here, including the same-slope multi-child genre the
     main battery's P1(f) never resolves per-z).

FINDINGS (2026-08-16, this battery):

  (+) A: per-(L,D)-WITH-z fibre constancy + onto holds on every enumerable cell — this is
      FINER than P1(f), whose genre key is ((mu,k,window)..., pieces) and aggregates over z.
  (+) E2: in the same-slope two-child genre (q=3, m=4, N=6, L={(2,1,1),(2,1,2)}, K=1) the
      genre splits as EXACTLY 81 fibres x 729, and the canonical replant map is an exact
      bijection between fibres.  The signed Lean statement is TRUE there; no re-sign needed.
  (-) D2 (REFUTED, expected-negative): the replant class DEPENDS on the choice of lift of
      the target difference (t'_p - t_p) beyond its class: Delta and Delta + pi^{N-D}*u give
      DIFFERENT output classes.  So the Lean construction must pin Delta by a FIXED section;
      there is no canonical-free re-planting.
  (-) D3 (REFUTED, expected-negative): "presentation stability" FAILS in multi-child
      same-slope genres: two exact planted presentations of the SAME class, shifted by the
      SAME Delta, can give DIFFERENT classes (witness: rigid-K same-slope cell; the two
      same-slope planted sub-lattices carry a genuine syzygy, gauge group of size q^4 in the
      census cell).  Consequence: injectivity of the replant map does NOT follow from the
      naive stability argument; the counting must go through the raw parameter space
      (presentations) with constant presentation-multiplicity, or another mechanism.
  (-) E3 (expected-negative, recorded): the round trip replant(t->t');replant(t'->t) is NOT
      the identity in Zq (section carries) — mutual injections/bijections must not be built
      from a round-trip identity.
  (+) D1: single-child presentation stability HOLDS on all SINGLE-child genres tested,
      including k = 2, 3 children at nontrivial windows (constructed cells).

Exit 0 iff all checks (incl. the expected-negatives, asserted as refuted) pass.
Run:  python3 OM2_h116b_replant_cert.py [--fast]     (--fast skips the census + big cells)
"""

import sys, os, itertools, random, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from OM2_genindb_battery import (Ring, depth0_data, extract_child, hensel_split,
                                 rpoly_mul, rpoly_sub, rpoly_divmod_monic,
                                 cluster_states, binom)

FAST = "--fast" in sys.argv
random.seed(20260816)

CHECKS = []
def check(name, ok, detail=""):
    CHECKS.append((name, bool(ok), detail))
    print(("  ok  " if ok else "  FAIL") + f"  {name}" + (f"  [{detail}]" if detail and not ok else ""))

# ----------------------------------------------------------------------------------
# helpers on ring polynomials (lists, index = degree)
# ----------------------------------------------------------------------------------
def alpha_parent(RB, b, k, zhat, mu):
    """P(b) = alphaParent: coeff j = alphaFrame(b, zhat)_j * pi^{k(mu-j)};
    alphaFrame = (X^mu + sum b_i X^i).comp(X - zhat)."""
    mp = list(b) + [RB.from_int(1)]
    negz = RB.sub(0, zhat)
    negzpow = [RB.from_int(1)]
    for _ in range(mu):
        negzpow.append(RB.mul(negzpow[-1], negz))
    P = []
    for j in range(mu + 1):
        acc = 0
        for i in range(j, mu + 1):
            term = RB.mul(mp[i], RB.from_int(binom(i, j)))
            term = RB.mul(term, negzpow[i - j])
            acc = RB.add(acc, term)
        P.append(RB.shift_up(acc, k * (mu - j)))
    return P

def frame_of(RB, f, k, zhat):
    """f.comp(pi^k (Y + zhat)): g_j = pi^{kj} * sum_{i>=j} f_i C(i,j) (pi^k zhat)^{i-j}."""
    s = RB.shift_up(zhat, k)
    spow = [RB.from_int(1)]
    for _ in range(len(f)):
        spow.append(RB.mul(spow[-1], s))
    g = []
    for j in range(len(f)):
        acc = 0
        for i in range(j, len(f)):
            term = RB.mul(f[i], RB.from_int(binom(i, j)))
            term = RB.mul(term, spow[i - j])
            acc = RB.add(acc, term)
        g.append(RB.shift_up(acc, k * j))
    return g

def poly_min_val(RB, f):
    return min(RB.val(x) for x in f)

def beta_read(RB, state, m, W, q):
    """None unless BETA; else (L frozenset, D dict, treads dict p -> child tuple @ W-D)."""
    d0 = depth0_data(RB, state, m, W, q)
    if d0['bucket'] != 'BETA':
        return None
    L, Dd, tr = set(), {}, {}
    for (mu, k, z) in d0['children']:
        c, D, Dp = extract_child(RB, state, m, W, k, z, q)
        assert D == Dp
        M = W - D
        assert M >= 1
        g = [RB.shift_down(x, D) for x in c]
        h, _ = hensel_split(RB, g, mu, M, q)
        p = (mu, k, z)
        L.add(p); Dd[p] = D
        tr[p] = tuple(RB.trunc(x, M) for x in h[:mu])
    return frozenset(L), Dd, tr

def factorize_beta(RB, f, m, W, q, L, Dd, prec_margin=2):
    """C2 on the LIFT f: (bs dict p -> full-precision block, K, remainder min-val)."""
    bs = {}
    Ptot = [RB.from_int(1)]
    for p in sorted(L):
        mu, k, z = p
        D = Dd[p]
        g = frame_of(RB, f, k, RB.lift_res(z))
        assert poly_min_val(RB, g) >= D
        gg = [RB.shift_down(x, D) for x in g]
        h, _ = hensel_split(RB, gg, mu, RB.prec - D - prec_margin, q)
        bs[p] = [x for x in h[:mu]]
        Ptot = rpoly_mul(RB, Ptot, alpha_parent(RB, bs[p], k, RB.lift_res(z), mu))
    K, rem = rpoly_divmod_monic(RB, f, Ptot)
    rv = min([RB.val(x) for x in rem] + [RB.prec]) if rem else RB.prec
    return bs, K, rv

def replant(RB, m, W, q, bs, K, L, Dd, tvals, told, delta_mode="trunc"):
    """C3: f' = prod P(b_p + Delta_p) * K; returns (class tuple @ W, f')."""
    Ptot = [RB.from_int(1)]
    for p in sorted(L):
        mu, k, z = p
        M = W - Dd[p]
        b2 = []
        for i in range(mu):
            d = RB.sub(tvals[p][i], told[p][i])
            if delta_mode == "trunc":
                d = RB.trunc(d, M)
            b2.append(RB.add(bs[p][i], d))
        Ptot = rpoly_mul(RB, Ptot, alpha_parent(RB, b2, k, RB.lift_res(z), mu))
    f2 = rpoly_mul(RB, Ptot, K)
    assert len(f2) == m + 1 and f2[m] == RB.from_int(1)
    return tuple(RB.trunc(x, W) for x in f2[:m]), f2

def factorize_one(RB, f, m, W, q, p, D, prec_margin=2):
    """single-child peel: (b_p, Q = f /m P(b_p), remainder min-val)."""
    mu, k, z = p
    g = frame_of(RB, f, k, RB.lift_res(z))
    assert poly_min_val(RB, g) >= D
    gg = [RB.shift_down(x, D) for x in g]
    h, _ = hensel_split(RB, gg, mu, RB.prec - D - prec_margin, q)
    b = [x for x in h[:mu]]
    P = alpha_parent(RB, b, k, RB.lift_res(z), mu)
    Q, rem = rpoly_divmod_monic(RB, f, P)
    rv = min([RB.val(x) for x in rem] + [RB.prec]) if rem else RB.prec
    return b, Q, rv

def replant_one(RB, m, W, q, b, Q, p, D, tnew_p, told_p):
    mu, k, z = p
    M = W - D
    b2 = [RB.add(b[i], RB.trunc(RB.sub(tnew_p[i], told_p[i]), M)) for i in range(mu)]
    P2 = alpha_parent(RB, b2, k, RB.lift_res(z), mu)
    f2 = rpoly_mul(RB, P2, Q)
    return tuple(RB.trunc(x, W) for x in f2[:m]), f2

def state_class(RB, f, m, W):
    return tuple(RB.trunc(x, W) for x in f[:m])

def all_child_states(R, mu, M):
    return [tuple(t) for t in itertools.product(R.elements(M, val_ge=1), repeat=mu)]

def cleared_supp(RB, f, u, l, cap):
    best = None
    for j, x in enumerate(f):
        v = RB.val(x)
        if v >= cap:
            continue
        s = l * v + u * j
        best = s if best is None else min(best, s)
    return best

# ----------------------------------------------------------------------------------
# per-cell full-enumeration certification (A, B, C, D, E1, G + expected-negatives)
# ----------------------------------------------------------------------------------
NEG_WITNESS = {'S2': 0, 'S1multi': 0, 'roundtrip': 0}

def run_cell(ringkind, q, m, W, sample_states=200, sample_targets=6):
    cell = f"{ringkind} q={q} m={m} N={W}"
    BIG = W * (m + 2) + 8
    RB = Ring(ringkind, q, BIG)
    genres = {}
    for st in cluster_states(Ring(ringkind, q, W), m, W):
        r = beta_read(RB, st, m, W, q)
        if r is None:
            continue
        L, Dd, tr = r
        gk = (L, tuple(Dd[p] for p in sorted(L)))
        tk = tuple(tr[p] for p in sorted(L))
        genres.setdefault(gk, {}).setdefault(tk, []).append(st)

    # ---- A: per-(L,D)-with-z constancy + onto -----------------------------------
    okA, detail = True, ""
    for (L, Dt), fibres in genres.items():
        sizes = {len(v) for v in fibres.values()}
        prodT = 1
        for p, D in zip(sorted(L), Dt):
            prodT *= q ** (p[0] * (W - D - 1))
        if len(sizes) != 1 or len(fibres) != prodT:
            okA = False
            detail = f"genre {sorted(L)} D={Dt}: sizes {sizes}, {len(fibres)} fibres vs {prodT}"
            break
    check(f"A per-(L,D)-with-z fibres constant + onto [{cell}] ({len(genres)} genres)", okA, detail)

    okB = okC = okD1 = okE = okG = True
    dB = dC = dD1 = dE = dG = ""
    minmargin = 10 ** 9
    n_tested = 0
    for (L, Dt), fibres in sorted(genres.items(), key=lambda kv: str(kv[0])):
        Dd = {p: D for p, D in zip(sorted(L), Dt)}
        tkeys = sorted(fibres.keys())
        spaces = [all_child_states(Ring(ringkind, q, W - Dd[p]), p[0], W - Dd[p]) for p in sorted(L)]
        all_targets = [tuple(t) for t in itertools.product(*spaces)]
        allstates = [(tk, st) for tk in tkeys for st in fibres[tk]]
        random.shuffle(allstates)
        sample = allstates[:max(3, sample_states // max(len(genres), 1))]
        for tk, st in sample:
            n_tested += 1
            f = [x for x in st] + [RB.from_int(1)]
            told = {p: tk[i] for i, p in enumerate(sorted(L))}
            bs, K, rv = factorize_beta(RB, f, m, W, q, L, Dd)
            if rv < W + 3:
                okB = False; dB = f"{cell} {sorted(L)} margin {rv} < N+3"
            minmargin = min(minmargin, rv)
            targets = [tk] + random.sample(all_targets, min(sample_targets, len(all_targets)))
            for t2 in targets:
                tnew = {p: t2[i] for i, p in enumerate(sorted(L))}
                c2, f2 = replant(RB, m, W, q, bs, K, L, Dd, tnew, told)
                # C: membership in fiber(t2)
                r2 = beta_read(RB, c2, m, W, q)
                if r2 is None or r2[0] != L or tuple(r2[1][p] for p in sorted(L)) != Dt \
                   or tuple(r2[2][p] for p in sorted(L)) != t2:
                    okC = False; dC = f"{cell} {sorted(L)}: replant not in fiber(t')"
                if t2 == tk and c2 != st:
                    okC = False; dC = f"{cell} {sorted(L)}: identity replant moved the class"
                # G: f2 - f strictly above f's polygon at every (u, l)
                df = rpoly_sub(RB, f2, f)
                for l in range(1, m + 1):
                    for u in range(0, l * W + 1):
                        if math.gcd(u, l) != 1:
                            continue
                        s0 = cleared_supp(RB, f, u, l, BIG - 2)
                        s1 = cleared_supp(RB, df, u, l, BIG - 2)
                        if s0 is not None and s1 is not None and s1 <= s0:
                            okG = False; dG = f"{cell} (u,l)=({u},{l}): {s1} <= {s0}"
                # D1: SINGLE-child presentation stability (canonical vs perturbed lift)
                if len(L) == 1:
                    p0 = sorted(L)[0]
                    fp = f[:]
                    for j in range(m):
                        e = random.randrange(0, q ** 2)
                        if ringkind == 'Fqt':
                            e = (e % q) | ((random.randrange(q)) << 16)
                        fp[j] = RB.add(f[j], RB.shift_up(e, W))
                    b1, Q1, rv1 = factorize_one(RB, f, m, W, q, p0, Dd[p0])
                    b1p, Q1p, rv1p = factorize_one(RB, fp, m, W, q, p0, Dd[p0])
                    ca, _ = replant_one(RB, m, W, q, b1, Q1, p0, Dd[p0], tnew[p0], told[p0])
                    cb, _ = replant_one(RB, m, W, q, b1p, Q1p, p0, Dd[p0], tnew[p0], told[p0])
                    if ca != cb:
                        okD1 = False; dD1 = f"{cell} {sorted(L)}: single-child S1 broke"
                    if ca != c2:
                        okD1 = False; dD1 = f"{cell} {sorted(L)}: single-child != joint replant"
                # expected-negative witnesses (recorded, not required per cell)
                c4, _ = replant(RB, m, W, q, bs, K, L, Dd, tnew, told, delta_mode="raw")
                if c4 != c2:
                    NEG_WITNESS['S2'] += 1
                r2b = beta_read(RB, c2, m, W, q)
                if r2b is not None:
                    f2c = [x for x in c2] + [RB.from_int(1)]
                    bs3, K3, rv3 = factorize_beta(RB, f2c, m, W, q, L, Dd)
                    c5, _ = replant(RB, m, W, q, bs3, K3, L, Dd, told, tnew)
                    if c5 != st:
                        NEG_WITNESS['roundtrip'] += 1
        # E1: exhaustive bijection between two fibres via the canonical replant
        if len(tkeys) >= 2:
            t0, t1 = tkeys[0], tkeys[-1]
            image = set()
            for st in fibres[t0]:
                f = [x for x in st] + [RB.from_int(1)]
                bs, K, rv = factorize_beta(RB, f, m, W, q, L, Dd)
                told = {p: t0[i] for i, p in enumerate(sorted(L))}
                tnew = {p: t1[i] for i, p in enumerate(sorted(L))}
                c2, _ = replant(RB, m, W, q, bs, K, L, Dd, tnew, told)
                image.add(c2)
            if image != set(fibres[t1]):
                okE = False; dE = f"{cell} {sorted(L)}: image != fiber(t1)"
    check(f"B exact factorization, margin >= N+3 [{cell}] (min margin {minmargin}, {n_tested} states)", okB, dB)
    check(f"C replant lands in fiber(t'), identity fixed [{cell}]", okC, dC)
    check(f"D1 single-child presentation stability [{cell}]", okD1, dD1)
    check(f"E1 canonical replant bijective fiber(t0) -> fiber(t1) [{cell}]", okE, dE)
    check(f"G replant difference strictly above the polygon [{cell}]", okG, dG)

# ----------------------------------------------------------------------------------
# F: planted-factor profiles (b-independence), standalone
# ----------------------------------------------------------------------------------
def check_profiles():
    ok, det = True, ""
    for ringkind in ('Zq', 'Fqt'):
        for q in (2, 3):
            RB = Ring(ringkind, q, 24)
            for _ in range(40):
                mu = random.choice([2, 3])
                k = random.choice([1, 2, 3])
                z = random.randrange(1, q)
                b = [RB.shift_up(random.randrange(q ** 6), 1) for _ in range(mu)]
                bt = [RB.shift_up(random.randrange(q ** 6), 1) for _ in range(mu)]
                P = alpha_parent(RB, b, k, RB.lift_res(z), mu)
                Pt = alpha_parent(RB, bt, k, RB.lift_res(z), mu)
                for k2 in (1, 2, 3, 4):
                    e = mu * min(k, k2)
                    for z2 in range(1, q):
                        if k2 == k and z2 == z:
                            g = frame_of(RB, P, k, RB.lift_res(z))
                            if poly_min_val(RB, g) != k * mu:
                                ok = False; det = f"own-frame w {poly_min_val(RB,g)} != {k*mu}"
                            continue
                        g = frame_of(RB, P, k2, RB.lift_res(z2))
                        gt = frame_of(RB, Pt, k2, RB.lift_res(z2))
                        w, wt = poly_min_val(RB, g), poly_min_val(RB, gt)
                        if w != e or wt != e:
                            ok = False; det = f"w_(k'={k2}) = {w},{wt} != {e} (k={k},mu={mu})"
                        r = [RB.res(RB.shift_down(x, e)) for x in g]
                        rt = [RB.res(RB.shift_down(x, e)) for x in gt]
                        if r != rt:
                            ok = False; det = f"divided reduction b-DEPENDENT at (k'={k2},z'={z2}), k={k}"
                        if r[0] == 0:
                            ok = False; det = f"divided reduction not unit-constant at (k'={k2},z'={z2}), k={k}"
    check("F planted profiles: w_(k') = mu*min(k,k'), reductions b-independent, unit const", ok, det)

# ----------------------------------------------------------------------------------
# constructed families (windows beyond full enumeration): genre exactness + replant
# + single-child stability; also the D3 witness harvest (simultaneous multi-child S1)
# ----------------------------------------------------------------------------------
def run_constructed(ringkind, q, m, W, Lspec, Ksampler, ntrial, tag, harvest_D3=False):
    BIG = W * (m + 3) + 10
    RB = Ring(ringkind, q, BIG)
    L = frozenset(Lspec)
    ok, det = True, ""
    Dd_glob = None
    for trial in range(ntrial):
        Ptot = [RB.from_int(1)]
        bsent = {}
        for p in sorted(L):
            mu, k, z = p
            b = [RB.shift_up(random.randrange(q ** (W + 2)), 1) for _ in range(mu)]
            bsent[p] = b
            Ptot = rpoly_mul(RB, Ptot, alpha_parent(RB, b, k, RB.lift_res(z), mu))
        f = rpoly_mul(RB, Ptot, Ksampler(RB))
        st = state_class(RB, f, m, W)
        r = beta_read(RB, st, m, W, q)
        if r is None or r[0] != L:
            ok = False; det = f"wrong child set: {None if r is None else sorted(r[0])}"; break
        Dd, told = r[1], r[2]
        if Dd_glob is None:
            Dd_glob = dict(Dd)
        elif Dd != Dd_glob:
            continue
        # child reads = the planted classes
        for p in sorted(L):
            M = W - Dd[p]
            if r[2][p] != tuple(RB.trunc(x, M) for x in bsent[p]):
                ok = False; det = f"child read != planted class at {p}"; break
        if not ok:
            break
        # joint replant membership
        bs, K, rv = factorize_beta(RB, [x for x in st] + [RB.from_int(1)], m, W, q, L, Dd)
        if rv < W + 3:
            ok = False; det = f"factorization margin {rv}"; break
        tnew = {}
        for p in sorted(L):
            mu, k, z = p
            M = W - Dd[p]
            R2 = Ring(ringkind, q, M)
            tnew[p] = tuple(random.choice(list(R2.elements(M, val_ge=1))) for _ in range(mu))
        c2, _ = replant(RB, m, W, q, bs, K, L, Dd, tnew, told)
        r2 = beta_read(RB, c2, m, W, q)
        if r2 is None or r2[0] != L or r2[1] != Dd or r2[2] != tnew:
            ok = False; det = "replant failed on constructed family"; break
        # single-child presentation stability at each child with window >= 2
        for p in sorted(L):
            M = W - Dd[p]
            if M < 2:
                continue
            b1, Q1, rv1 = factorize_one(RB, [x for x in st] + [RB.from_int(1)], m, W, q, p, Dd[p])
            b2, Q2, rv2 = factorize_one(RB, f, m, W, q, p, Dd[p])
            if min(rv1, rv2) < W + 3:
                ok = False; det = f"single-child margin at {p}"; break
            ca, _ = replant_one(RB, m, W, q, b1, Q1, p, Dd[p], tnew[p], told[p])
            cb, _ = replant_one(RB, m, W, q, b2, Q2, p, Dd[p], tnew[p], told[p])
            if len(L) == 1 and ca != cb:
                ok = False; det = f"single-child S1 broke at {p}"; break
            if len(L) > 1 and ca != cb:
                NEG_WITNESS['S1multi'] += 1     # multi-child: EXPECTED to break (D3)
        if not ok:
            break
        if harvest_D3:
            # simultaneous multi-child S1: canonical vs product presentation
            bsP, KP, rvP = factorize_beta(RB, f, m, W, q, L, Dd)
            cc, _ = replant(RB, m, W, q, bsP, KP, L, Dd, tnew, told)
            if cc != c2:
                NEG_WITNESS['S1multi'] += 1
    check(f"H constructed family: genre exact + replant + reads [{tag}]", ok, det)

# ----------------------------------------------------------------------------------
# E2: the same-slope census (exact, via the C1/C2 parametrization + visibility box)
# q=3, m=4, N=6, L={(2,1,1),(2,1,2)}, K=1, D=(4,4), windows (2,2).
# ----------------------------------------------------------------------------------
def run_census_sameslope():
    q, N, m = 3, 6, 4
    MOD = q ** N

    def factor_coeffs(zhat):
        out = []
        for t0 in range(q ** 3):          # b0 mod 3^4, val >= 1 (visibility-measured box)
            b0 = q * t0
            for t1 in range(q ** 4):      # b1 mod 3^5, val >= 1
                b1 = q * t1
                c0 = (zhat * zhat - b1 * zhat + b0) % MOD
                c1 = (-2 * zhat + b1) % MOD
                key = ((b0 % 9) // 3) * q + ((b1 % 9) // 3)
                out.append(((c0 * 9) % MOD, (c1 * 3) % MOD, key))
        return out

    FA, FB = factor_coeffs(1), factor_coeffs(2)
    fibres, classes_seen, bad = {}, {}, 0
    for A0, A1, kA in FA:
        for B0, B1, kB in FB:
            c0 = (A0 * B0) % MOD
            c1 = (A0 * B1 + A1 * B0) % MOD
            c2 = (A0 + B0 + A1 * B1) % MOD
            c3 = (A1 + B1) % MOD
            cls = ((c0 * MOD + c1) * MOD + c2) * MOD + c3
            kv = kA * 9 + kB
            fibres.setdefault(kv, set()).add(cls)
            k0 = classes_seen.get(cls)
            if k0 is None:
                classes_seen[cls] = kv
            elif k0 != kv:
                bad += 1
    sizes = sorted(len(v) for v in fibres.values())
    ok = (len(set(sizes)) == 1 and len(sizes) == 81 and bad == 0
          and len(classes_seen) == 81 * sizes[0])
    check(f"E2 same-slope census: 81 fibres x {sizes[0]} exactly, reads class-determined",
          ok, f"sizes {sorted(set(sizes))[:5]}, key clashes {bad}")

    # canonical replant bijectivity between two fibres of the census, exhaustive
    ringkind = 'Zq'
    BIG = N * (m + 3) + 10
    RB = Ring(ringkind, q, BIG)
    L = frozenset([(2, 1, 1), (2, 1, 2)])
    ps = sorted(L)
    Dd = {ps[0]: 4, ps[1]: 4}
    keys = sorted(fibres.keys())
    t_from, t_to = keys[0], keys[7]

    def key_to_treads(kv):
        kA, kB = kv // 9, kv % 9
        def rd(x):
            return (3 * (x // 3), 3 * (x % 3))
        return {ps[0]: rd(kA), ps[1]: rd(kB)}

    def unpack(cls):
        c3 = cls % MOD; cls //= MOD
        c2 = cls % MOD; cls //= MOD
        c1 = cls % MOD; c0 = cls // MOD
        return (c0, c1, c2, c3)

    told, tnew = key_to_treads(t_from), key_to_treads(t_to)
    image, coll, outside = set(), 0, 0
    for cls in sorted(fibres[t_from]):
        st = unpack(cls)
        f = [x for x in st] + [RB.from_int(1)]
        bs, K, rv = factorize_beta(RB, f, m, N, q, L, Dd)
        c2, _ = replant(RB, m, N, q, bs, K, L, Dd, tnew, told)
        cls2 = ((c2[0] * MOD + c2[1]) * MOD + c2[2]) * MOD + c2[3]
        if cls2 not in fibres[t_to]:
            outside += 1
        if cls2 in image:
            coll += 1
        image.add(cls2)
    ok2 = (coll == 0 and outside == 0 and len(image) == len(fibres[t_to]))
    check("E2 same-slope canonical replant: exact bijection fiber(t) -> fiber(t')", ok2,
          f"collisions {coll}, outside {outside}, image {len(image)}/{len(fibres[t_to])}")

# ----------------------------------------------------------------------------------
# I: NEGATIVE control — a K residual vanishing at a planted z bumps the multiplicity
# ----------------------------------------------------------------------------------
def run_negative():
    q, m, W = 2, 3, 6
    RB = Ring('Zq', q, W * (m + 2) + 8)
    b = [RB.shift_up(1, 2), RB.shift_up(1, 1)]
    P = alpha_parent(RB, b, 1, 1, 2)
    K = [RB.sub(0, 2), RB.from_int(1)]           # X - 2: slope-1 residual root z = 1
    f = rpoly_mul(RB, P, K)
    st = state_class(RB, f, m, W)
    d0 = depth0_data(RB, st, m, W, q)
    bumped = (d0['bucket'] == 'ALPHA') or \
             (d0['bucket'] == 'BETA' and any(mu == 3 for (mu, k, z) in d0['children']))
    check("I negative control: colliding K residual bumps the child multiplicity", bumped,
          f"bucket {d0['bucket']}")

# ----------------------------------------------------------------------------------
def main():
    print("H.116b replant certification — exact, both rings"
          + (" [--fast]" if FAST else ""))
    check_profiles()
    run_negative()
    cells = [('Zq', 2, 3, 4), ('Zq', 2, 3, 5), ('Zq', 3, 3, 4), ('Fqt', 2, 3, 5),
             ('Fqt', 3, 3, 4), ('Zq', 2, 4, 4), ('Fqt', 2, 4, 4)]
    if not FAST:
        cells += [('Zq', 2, 3, 6), ('Fqt', 2, 3, 6)]
    for cellargs in cells:
        run_cell(*cellargs)
    # constructed families
    K1 = lambda RB: [RB.from_int(1)]
    def Kdeg1(RB):
        return [RB.shift_up(1 + RB.q * random.randrange(RB.q ** 5), 1), RB.from_int(1)]
    run_constructed('Zq', 3, 4, 6, [(2, 1, 1), (2, 1, 2)], K1, 60,
                    "Zq q3 m4 N6 same-slope", harvest_D3=True)
    run_constructed('Fqt', 3, 4, 6, [(2, 1, 1), (2, 1, 2)], K1, 60,
                    "Fqt q3 m4 N6 same-slope", harvest_D3=True)
    run_constructed('Zq', 2, 4, 7, [(2, 1, 1), (2, 2, 1)], K1, 60, "Zq q2 m4 N7 mixed-slope")
    run_constructed('Fqt', 2, 4, 7, [(2, 1, 1), (2, 2, 1)], K1, 60, "Fqt q2 m4 N7 mixed-slope")
    run_constructed('Zq', 2, 3, 7, [(2, 2, 1)], Kdeg1, 60, "Zq q2 m3 N7 k=2 W=2")
    run_constructed('Fqt', 2, 3, 7, [(2, 2, 1)], Kdeg1, 60, "Fqt q2 m3 N7 k=2 W=2")
    run_constructed('Zq', 2, 3, 8, [(2, 2, 1)], Kdeg1, 40, "Zq q2 m3 N8 k=2 W=3")
    if not FAST:
        run_census_sameslope()
    # the expected-negatives: witnesses REQUIRED (these are refutations, pinned)
    check("D2 REFUTED (expected): output depends on the Delta lift beyond its class",
          NEG_WITNESS['S2'] > 0, "no witness found")
    check("D3 REFUTED (expected): simultaneous multi-child presentation stability fails",
          NEG_WITNESS['S1multi'] > 0, "no witness found")
    check("E3 recorded (expected): round trip is not the identity (Zq carries)",
          NEG_WITNESS['roundtrip'] > 0, "no witness found")
    bad = [c for c in CHECKS if not c[1]]
    print(f"\n==== {len(CHECKS)} checks, {len(CHECKS) - len(bad)} passed, {len(bad)} failed ====")
    print(f"(negative-witness counts: {NEG_WITNESS})")
    if bad:
        for name, _, det in bad:
            print(f"  FAILED: {name}  {det}")
        sys.exit(1)
    print("ALL CHECKS PASSED")

if __name__ == "__main__":
    main()
