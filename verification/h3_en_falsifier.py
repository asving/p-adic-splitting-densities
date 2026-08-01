#!/usr/bin/env python3
"""h3_en_falsifier.py — EN-U2: the adjudicating falsifier G-EN-1 for caveat (E-N).

BLUEPRINT: lean/blueprints/HDISCHARGE_H3.md §3.3 (unit EN-U2, wave 0, gate G-EN-1).
QUESTION ((E-N), O-1thr rev 4 §6 Theorem 3(c) caveat, verbatim OPEN): can a level-N
box x fiber a decided ns-free classification tree T with thr(T) > N?  fiber(T, x) is
the six-clause predicate (F1)-(F6) of the O-1thr rev-4 brief §1.4 evaluated on the
DECODE f_x (the zero-extended lift: integer coefficients < p^N); thr(T) :=
max(1, max over T's chains H of L(H)) with the §3 read ceiling
    L(H) = 1 + max_i ceil(I_i / E_i),   I_i = ell_i(0) (side line value at slot 0).

SCOPE OF THE MACHINE IMPLEMENTED HERE (exact, n <= 3): for deg <= 3 every descent is
a linear-key refinement — a residual factor psi^mu with mu >= 2 inside a window of
width <= 3 forces e = 1, deg psi = 1 (e*g*mu <= window width) — so every frame has
stretch E_i = 1 and key degree 1, and the OM run is the classical successive-digit
root-clustering machine, computable in exact integer arithmetic:
  * track root state (repeated factor phibar^m of fbar, phibar = x - r): window =
    slots 0..m of the Taylor development of f at the lifted center, shear gammahat=0;
  * state after read nu (e=1,g=1,mu): center c' = c + s*p^lambda (s = residual root
    digit, lambda = plain slope of nu), window 0..mu, shear gammahat' = lambda;
  * window polygon = lower hull of sheared points (j, v_p(B_j) + j*gammahat), B_j the
    Taylor coefficients; principal faces = strictly descending faces (brief §1.4);
  * per face (Dj, Du): g0=gcd, e=Dj/g0, h=Du/g0; pattern digits at stride slots ON the
    face line; residual factored over F_p; mu = 1 -> (tau-irr) leaf, verdict (e, g);
    mu >= 2 -> refinement (descend);
  * per-read ceiling datum I = extended face-line value at slot 0 (sheared units;
    E=1 so ceil(I) is the §3 contribution) — at depth 1 this is EXACTLY the persite
    harvester's `intercept` (verification/openmath/o1thr_persite_check.py, gate V4);
  * decided ns-free  <=>  disc(f_x) != 0 (separable decode: the machine terminates
    with every maximal chain a certified leaf; disc == 0 => a cluster never resolves:
    ns).  Exact integer roots (B_0 = 0) are certified (1,1) leaves (corner counted).

VALIDATION GATES (all must pass before the scan verdict is trusted):
  V1 PARI oracle    — leaf-verdict multiset {(e,f)} + Hensel payload == PARI
                      factorpadic + idealprimedec (quartic_oracle.py algorithm,
                      driven through a gp pipe), exhaustive coarse (degree multiset)
                      on small configs + sampled full (e,f);
  V4 persite tie    — depth-1 read records (j0,j1,e,h,pat,psi,mu,L) == the O1thr
                      persite harvester's sites, on all X^n-reduction boxes;
  V-E Eisenstein    — x^n + p^j (gcd(j,n)=1): unique chain, thr = j+1 exactly
                      (the T-D family of the O1thr falsifier suite);
  V-W worked units  — hand-computed instances (x^2+1, x^2+3, x^2+7, x^2+2x+8,
                      x^2+4x+12 over Q_2; x^3+3 over Q_3).

OUTPUT (G-EN-1): per config (p,n,N): decided/ns counts, thr histogram, margin
N - thr statistics over decided boxes, HIT list (decided ns-free with thr > N) with
full realized-chain records, absorption exemplars (a level-N-equal lift realizing a
DIFFERENT tree — the semantic undecided-at-N witness; the capped-at-N walk halts at
the first read with 1+ceil(I) > N, so definitional absorption is by construction).
HIT => route (a) of §3.3 is dead as stated and the hit feeds route (b)'s absorption
check; NO-HIT => margin statistics support route (a) at the probed range.

Run:  python3 h3_en_falsifier.py [--no-oracle] [--stretch] [--out-dir DIR]
Log:  verification/logs/h3_en_falsifier_<date>.log (+ JSON in verification/results/).
"""
import argparse
import datetime
import json
import math
import os
import random
import subprocess
import sys
from fractions import Fraction
from itertools import product

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "openmath"))

# ---------------------------------------------------------------- basic number theory

def v_int(x, p):
    """Exact p-adic valuation of a nonzero integer."""
    assert x != 0
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v


def disc_monic(a):
    """Discriminant of monic x^n + a[n-1]x^{n-1}+...+a[0], n = len(a) in {2,3}."""
    if len(a) == 2:
        c, b = a[0], a[1]
        return b * b - 4 * c
    if len(a) == 3:
        d, c, b = a[0], a[1], a[2]
        return (18 * b * c * d - 4 * b ** 3 * d + b * b * c * c
                - 4 * c ** 3 - 27 * d * d)
    raise ValueError("n must be 2 or 3")

# ---------------------------------------------------------------- F_p[z] utilities

def _fp_normalize(c, p):
    c = [x % p for x in c]
    while c and c[-1] == 0:
        c.pop()
    return c


def _fp_divmod(a, b, p):
    """a, b lists low->high mod p, b monic-izable; returns (q, r)."""
    a = [x % p for x in a]
    b = _fp_normalize(b, p)
    inv = pow(b[-1], p - 2, p) if b[-1] != 1 else 1
    q = [0] * max(0, len(a) - len(b) + 1)
    while True:
        a = _fp_normalize(a, p)
        if len(a) < len(b):
            break
        f = (a[-1] * inv) % p
        off = len(a) - len(b)
        q[off] = f
        for i, bc in enumerate(b):
            a[off + i] = (a[off + i] - f * bc) % p
    return q, a


_IRR_CACHE = {}


def _fp_irreducibles(p, maxdeg):
    """All monic irreducibles over F_p of degree <= maxdeg (maxdeg <= 3)."""
    key = (p, maxdeg)
    if key in _IRR_CACHE:
        return _IRR_CACHE[key]
    out = [(r, 1) for r in range(p)]  # x + r  (low->high: (r,1))
    for d in (2, 3):
        if d > maxdeg:
            break
        for tup in product(range(p), repeat=d):
            f = list(tup) + [1]
            # deg 2 or 3: irreducible over F_p iff no root in F_p
            if all(sum(cf * pow(r, i, p) for i, cf in enumerate(f)) % p
                   for r in range(p)):
                out.append(tuple(f))
    _IRR_CACHE[key] = out
    return out


def fp_factor(c, p):
    """Factor nonzero c in F_p[z] (low->high ints) into monic irreducibles.
    Returns sorted list of (psi_tuple, multiplicity). Degree <= 3 territory."""
    c = _fp_normalize(c, p)
    assert c, "zero polynomial"
    deg = len(c) - 1
    fac = {}
    rem = c
    for g in _fp_irreducibles(p, deg):
        g = list(g)
        while len(rem) - 1 >= len(g) - 1:
            q, r = _fp_divmod(rem, g, p)
            if r:
                break
            rem = q
            fac[tuple(g)] = fac.get(tuple(g), 0) + 1
        if len(rem) - 1 == 0:
            break
    assert len(_fp_normalize(rem, p)) == 1, (c, rem)
    return sorted(fac.items())

# ---------------------------------------------------------------- the n<=3 OM machine

def taylor_shift(F, c):
    """Coefficients (low->high) of F(x + c), F a list of ints low->high."""
    out = list(F)
    n = len(F) - 1
    for i in range(n):            # synthetic Taylor expansion
        for j in range(n - 1, i - 1, -1):
            out[j] = out[j] + c * out[j + 1]
    return out


def _lower_hull(pts):
    """Lower hull vertices of pts sorted by x (one point per x), exact ints."""
    hull = []
    for pt in pts:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            if (x2 - x1) * (pt[1] - y1) - (y2 - y1) * (pt[0] - x1) <= 0:
                hull.pop()
            else:
                break
        hull.append(pt)
    return hull


class MachineError(Exception):
    pass


def classify(a, p):
    """Run the n<=3 OM machine on the decode f = x^n + a[n-1]x^{n-1}+...+a[0].

    Returns dict: decided (bool), ns (bool), thr (int or None), chains, hensel,
    type (sorted (e,f) multiset), corners (exact-root leaf count).
    Chain record = (reads_tuple, verdict, L); read record =
    (shear, j0, j1, e, h, pat, psi, mu, I_num, I_den)."""
    n = len(a)
    F = list(a) + [1]
    D = disc_monic(a)
    if D == 0:
        return dict(decided=False, ns=True, thr=None, chains=[], hensel=[],
                    type=None, corners=0)
    vD = v_int(D, p)
    hensel = []
    chains = []
    corners = 0
    # track partition (brief §1.4): factor fbar, split by multiplicity
    fbar = fp_factor(F, p)
    stack = []
    for psi, m in fbar:
        if m == 1:
            hensel.append((1, len(psi) - 1))
        else:
            assert len(psi) - 1 == 1, "repeated factor of degree >= 2 at n <= 3"
            r = (-psi[0]) % p
            # (track_id, center, window, shear, reads)
            stack.append((len(stack), r, m, 0, ()))
    track_deg = {t[0]: t[2] for t in stack}
    track_leaf_deg = {tid: 0 for tid in track_deg}
    guard = 0
    while stack:
        guard += 1
        if guard > 10000:
            raise MachineError("guard: runaway refinement (separable input?)")
        tid, c, m, shear, reads = stack.pop()
        B = taylor_shift(F, c)
        pts = [(j, v_int(B[j], p) + j * shear)
               for j in range(m + 1) if B[j] != 0]
        if B[0] == 0:
            # exact integer root: (x - c) | F exactly -> certified (1,1) leaf
            L = 1 + max((-(-r[8] // r[9]) for r in reads), default=0)
            chains.append((reads, (1, 1), L))
            track_leaf_deg[tid] += 1
            corners += 1
        # vertex law sanity (brief (M6b)(i)/Cor VTX): window min at right end
        umin = min(u for _, u in pts)
        if pts[-1][0] != m or pts[-1][1] != umin or \
                any(u == umin for j, u in pts if j != m):
            raise MachineError(f"vertex law fails at a={a} c={c} m={m} pts={pts}")
        hull = _lower_hull(pts)
        faces = list(zip(hull, hull[1:]))
        if not faces and B[0] != 0:
            raise MachineError(f"ns-halt on separable input a={a} c={c}")
        for (j0, u0), (j1, u1) in faces:
            Dj, Du = j1 - j0, u0 - u1
            assert Du > 0, "non-principal face survived"
            g0 = math.gcd(Dj, Du)
            e, h = Dj // g0, Du // g0
            d = Dj // e
            pat = []
            for k in range(d + 1):
                j = j0 + e * k
                Bj = B[j] if j <= n else 0
                on = (Bj != 0 and
                      (v_int(Bj, p) + j * shear) * Dj == u0 * Dj - (j - j0) * Du)
                pat.append((Bj // p ** v_int(Bj, p)) % p if on else 0)
            assert pat[0] != 0 and pat[-1] != 0, (a, c, pat)
            I_num, I_den = u0 * Dj + j0 * Du, Dj
            g_ = math.gcd(I_num, I_den)
            I_num, I_den = I_num // g_, I_den // g_
            for psi, mu in fp_factor(pat, p):
                read = (shear, j0, j1, e, h, tuple(pat), psi, mu, I_num, I_den)
                if mu == 1:
                    rds = reads + (read,)
                    L = 1 + max(-(-r[8] // r[9]) for r in rds)
                    chains.append((rds, (e, len(psi) - 1), L))
                    track_leaf_deg[tid] += e * (len(psi) - 1)
                else:
                    assert e == 1 and len(psi) - 1 == 1, \
                        "descent with e*g > 1 impossible at n <= 3"
                    lam = shear + h          # plain slope; integral since e = 1
                    if lam > 4 * vD + 40:
                        raise MachineError("refinement beyond disc budget")
                    s = (-psi[0]) % p
                    assert s != 0
                    stack.append((tid, c + s * p ** lam, mu, lam,
                                  reads + (read,)))
    # (F6) per-track degree checksum
    for tid, dtot in track_leaf_deg.items():
        assert dtot == track_deg[tid], (a, tid, dtot, track_deg)
    typ = sorted(hensel + [ch[1] for ch in chains])
    assert sum(e * f for e, f in typ) == n, (a, typ)      # (F5)
    thr = max([1] + [ch[2] for ch in chains])
    return dict(decided=True, ns=False, thr=thr, chains=chains, hensel=hensel,
                type=typ, corners=corners)

# ---------------------------------------------------------------- PARI gp oracle

GP_SCRIPT_HEADER = r"""
ef(co, p) = {
  my(fa = factorpadic(Polrev(co), p, 60)[,1], out = List());
  for(i = 1, #fa,
    my(g = fa[i], d = poldegree(g));
    if(d == 1, listput(out, [1,1]),
      my(G = liftall(g), nf = nfinit([G, [p]]),
         dec = idealprimedec(nf, p), done = 0);
      for(k = 1, #dec,
        if(!done && dec[k][3]*dec[k][4] == d,
           listput(out, [dec[k][3], dec[k][4]]); done = 1));
      if(!done, listput(out, [dec[1][3], dec[1][4]]))));
  vecsort(Vec(out)) }
cr(co, p) = vecsort(apply(poldegree, Vec(factorpadic(Polrev(co), p, 60)[,1])))
"""


def gp_batch(calls):
    """calls: list of ('cr'|'ef', coeffs_low_to_high_incl_leading, p).
    Returns list of parsed results (tuples). Uses one gp process."""
    lines = [GP_SCRIPT_HEADER]
    for i, (kind, co, p) in enumerate(calls):
        # co is low->high; gp's Polrev expects exactly that order.
        vec = "[" + ",".join(str(x) for x in co) + "]"
        lines.append(f'print("R{i}:", {kind}({vec}, {p}));')
    src = "\n".join(lines) + "\nquit;\n"
    proc = subprocess.run(["gp", "-q", "-f", "-s", "256000000"],
                          input=src, capture_output=True, text=True,
                          timeout=7200)
    out = {}
    for ln in proc.stdout.splitlines():
        if not ln.startswith("R"):
            continue
        idx, val = ln[1:].split(":", 1)
        out[int(idx)] = val.strip()
    if len(out) != len(calls):
        raise RuntimeError(f"gp returned {len(out)}/{len(calls)} results; "
                           f"stderr tail: {proc.stderr[-500:]}")
    res = []
    for i, (kind, co, p) in enumerate(calls):
        val = eval(out[i])  # noqa: S307 — gp row vectors print as Python lists
        if kind == "cr":
            res.append(tuple(sorted(val)))
        else:
            res.append(tuple(sorted((int(e), int(f)) for e, f in val)))
    return res


def my_coarse(info):
    return tuple(sorted(e * f for e, f in info["type"]))


def my_full(info):
    return tuple(sorted(info["type"]))

# ---------------------------------------------------------------- validation gates

def gate_V4_persite(log):
    """Depth-1 read records == o1thr persite harvester, X^n-reduction boxes."""
    import o1thr_persite_check as base
    bad = tot = 0
    for (p, n, N) in [(2, 2, 4), (3, 2, 3), (2, 3, 3), (3, 3, 2)]:
        for tup in product(range(p ** (N - 1)), repeat=n):
            a = tuple(p * t for t in tup)
            theirs = set()
            for (j0, j1, e, h, pat, psi, mu, L) in base.sites_of_box(
                    list(a), p, n, 64):
                theirs.add((j0, j1, e, h, pat, psi, mu, L))
            if disc_monic(list(a)) == 0:
                # persite still harvests sites; our machine declares ns.
                # compare against direct depth-1 harvest is skipped (ns boxes
                # have no fiber; (E-N) concerns decided boxes only).
                continue
            info = classify(list(a), p)
            mine = set()
            for reads, verdict, L in info["chains"]:
                if not reads:
                    continue
                r = reads[0]
                if r[0] != 0:
                    continue
                mine.add((r[1], r[2], r[3], r[4], r[5], r[6], r[7],
                          1 + -(-r[8] // r[9])))
            tot += 1
            if mine != theirs:
                bad += 1
                if bad <= 3:
                    log(f"  V4 MISMATCH a={a} p={p}: mine={sorted(mine)} "
                        f"theirs={sorted(theirs)}")
    log(f"GATE V4 (persite depth-1 tie): {tot} separable X^n-boxes compared, "
        f"{bad} mismatches -> {'PASS' if bad == 0 else 'FAIL'}")
    return bad == 0


def gate_VE_eisenstein(log):
    ok = True
    for p in (2, 3):
        for n in (2, 3):
            for j in range(1, 6):
                if math.gcd(j, n) != 1:
                    continue
                info = classify([p ** j] + [0] * (n - 1), p)
                want = sorted([(n, 1)])
                good = (info["decided"] and info["thr"] == j + 1
                        and info["type"] == want and len(info["chains"]) == 1)
                ok = ok and good
                if not good:
                    log(f"  V-E FAIL p={p} n={n} j={j}: {info}")
    log(f"GATE V-E (Eisenstein x^n + p^j: thr = j+1, type (n,1)): "
        f"{'PASS' if ok else 'FAIL'}")
    return ok


def gate_VW_worked(log):
    cases = [  # (p, coeffs a (low->high), thr, type)
        (2, [1, 0], 2, [(2, 1)]),          # x^2+1: ram, I=1
        (2, [3, 0], 3, [(1, 2)]),          # x^2+3: inert, I=2
        (2, [7, 0], 4, [(1, 1), (1, 1)]),  # x^2+7: split, faces I=2,3
        (2, [8, 2], 4, [(1, 1), (1, 1)]),  # x^2+2x+8: split, I=2,3
        (2, [12, 4], 4, [(2, 1)]),         # x^2+4x+12: refine then ram
        (3, [3, 0, 0], 2, [(3, 1)]),       # x^3+3: Eisenstein cubic
    ]
    ok = True
    for p, a, thr, typ in cases:
        info = classify(a, p)
        good = info["decided"] and info["thr"] == thr and info["type"] == sorted(typ)
        ok = ok and good
        if not good:
            log(f"  V-W FAIL p={p} a={a}: want thr={thr} type={typ}, "
                f"got thr={info['thr']} type={info['type']}")
    log(f"GATE V-W (hand-computed worked instances): {'PASS' if ok else 'FAIL'}")
    return ok

# ---------------------------------------------------------------- the level-N scan

def chain_summary(info):
    out = []
    for reads, verdict, L in info["chains"]:
        rd = [dict(shear=r[0], j0=r[1], j1=r[2], e=r[3], h=r[4],
                   pat=list(r[5]), psi=list(r[6]), mu=r[7],
                   I=f"{r[8]}/{r[9]}") for r in reads]
        out.append(dict(reads=rd, verdict=list(verdict), L=L))
    return out


def absorption_witness(a, p, n, N, info):
    """Find a level-N-equal lift whose realized tree differs (semantic
    undecided-at-N witness for the hit box). Returns dict or None."""
    base_records = (tuple(sorted(info["chains"])), tuple(sorted(info["hensel"])))
    M = p ** N
    for i in range(n):
        for t in range(1, p):
            a2 = list(a)
            a2[i] += t * M
            try:
                inf2 = classify(a2, p)
            except MachineError:
                continue
            if not inf2["decided"]:
                return dict(lift=list(a2), differs="lift is ns (not decided)")
            rec2 = (tuple(sorted(inf2["chains"])),
                    tuple(sorted(inf2["hensel"])))
            if rec2 != base_records:
                return dict(lift=list(a2),
                            differs="realized tree records differ",
                            lift_type=[list(x) for x in inf2["type"]],
                            lift_thr=inf2["thr"],
                            type_differs=(inf2["type"] != info["type"]))
    return None


def scan_config(p, n, N, log, oracle, rng):
    M = p ** N
    total = ns = machine_err = corners = dec_seen = 0
    thr_hist = {}
    hits = []
    hit_count = 0
    decided_infos_sample = []   # for oracle sampling: (a, coarse, full)
    all_boxes_coarse = []       # (a, coarse) when exhaustive-oracle feasible
    min_margin = None
    for tup in product(range(M), repeat=n):
        a = list(tup)
        total += 1
        try:
            info = classify(a, p)
        except MachineError as exc:
            machine_err += 1
            log(f"  MACHINE ERROR p={p} n={n} N={N} a={a}: {exc}")
            continue
        if not info["decided"]:
            ns += 1
            continue
        corners += info["corners"]
        thr = info["thr"]
        thr_hist[thr] = thr_hist.get(thr, 0) + 1
        margin = N - thr
        if min_margin is None or margin < min_margin:
            min_margin = margin
        if oracle is not None:
            all_boxes_coarse.append((tuple(a), my_coarse(info)))
            # reservoir sample of decided boxes for the full-(e,f) oracle check
            if len(decided_infos_sample) < 2000:
                decided_infos_sample.append((tuple(a), my_full(info)))
            else:
                k = rng.randrange(dec_seen + 1)
                if k < 2000:
                    decided_infos_sample[k] = (tuple(a), my_full(info))
        dec_seen += 1
        if thr > N:
            hit_count += 1
            if len(hits) < 200:
                h = dict(box=list(a), decode=list(a) + [1], thr=thr,
                         margin=margin,
                         type=[list(x) for x in info["type"]],
                         chains=chain_summary(info))
                if len(hits) < 5:
                    h["absorption_witness"] = absorption_witness(
                        a, p, n, N, info)
                hits.append(h)
    dec = total - ns - machine_err
    res = dict(p=p, n=n, N=N, boxes=total, decided=dec, ns=ns,
               machine_errors=machine_err, exact_root_corner_leaves=corners,
               thr_histogram={str(k): v for k, v in sorted(thr_hist.items())},
               min_margin=min_margin, hit_count=hit_count,
               hits_recorded=len(hits), hits=hits,
               verdict=("HIT" if hit_count else "NO-HIT"))
    # ---- oracle cross-checks
    if oracle is not None:
        coarse_pool = (all_boxes_coarse if len(all_boxes_coarse) <= 70000
                       else rng.sample(all_boxes_coarse, 30000))
        calls = [("cr", list(a) + [1], p) for a, _ in coarse_pool]
        got = gp_batch(calls)
        bad = [(a, mine, theirs) for (a, mine), theirs
               in zip(coarse_pool, got) if mine != theirs]
        full_pool = list(decided_infos_sample)
        full_pool += [(tuple(h["box"]),
                       tuple(sorted(tuple(x) for x in h["type"])))
                      for h in hits[:100]]
        callsF = [("ef", list(a) + [1], p) for a, _ in full_pool]
        gotF = gp_batch(callsF)
        badF = [(a, mine, theirs) for (a, mine), theirs
                in zip(full_pool, gotF) if mine != theirs]
        res["oracle"] = dict(
            coarse_checked=len(coarse_pool), coarse_mismatch=len(bad),
            coarse_exhaustive=(len(all_boxes_coarse) <= 70000),
            full_checked=len(full_pool), full_mismatch=len(badF))
        for a, mine, theirs in (bad + badF)[:5]:
            log(f"  ORACLE MISMATCH p={p} a={list(a)}: mine={mine} PARI={theirs}")
        res["oracle_pass"] = not bad and not badF
    log(f"p={p} n={n} N={N}: boxes={total} decided={dec} ns={ns} "
        f"| thr_hist={res['thr_histogram']} | min_margin={min_margin} "
        f"| HITS(thr>N)={hit_count} -> {res['verdict']}"
        + (f" | oracle coarse {res['oracle']['coarse_checked']}"
           f"({'exh' if res['oracle']['coarse_exhaustive'] else 'sample'})"
           f"/full {res['oracle']['full_checked']}: "
           f"{'PASS' if res['oracle_pass'] else 'FAIL'}"
           if oracle is not None else " | oracle SKIPPED"))
    return res


def absorption_audit(res_path, log):
    """Post-scan audit over every RECORDED hit (the W-3 two-predicate probe).

    (i)  TREE reading: probe the n*(p-1) one-coefficient lifts of the hit box for
         one realizing DIFFERENT tree records (semantic tree-undecidedness at N).
    (ii) TYPE reading, n = 2 only: the census disc-class detector qp_type
         (census_n2_uniform.py lineage) — is the hit box sigma-DECIDED at level N
         despite thr > N?  Such boxes are counted by the unrestricted reading of
         "decided-sigma at level N", missed by the thr-scoped sum, and do NOT sit
         in a semantically(type)-defined undecided envelope: absorption holds
         only under the operational/tree reading (blueprint §3.2 W-3 guard).
    """
    from census_n2_uniform import qp_type
    d = json.load(open(res_path))
    tot = no_wit = 0
    n2_tot = n2_type_decided = 0
    for r in d["results"]:
        p, n, N = r["p"], r["n"], r["N"]
        for h in r["hits"]:
            tot += 1
            info = classify(list(h["box"]), p)
            w = absorption_witness(h["box"], p, n, N, info)
            h["absorption_witness"] = w
            if w is None:
                no_wit += 1
                log(f"  AUDIT: no record-differing lift among probes for "
                    f"p={p} n={n} N={N} box={h['box']}")
            if n == 2:
                n2_tot += 1
                t = qp_type(h["box"][1], h["box"][0], p, N)
                h["census_type_at_N"] = t
                if t != "und":
                    n2_type_decided += 1
    d["absorption_audit"] = dict(
        recorded_hits=tot, tree_witness_found=tot - no_wit,
        tree_witness_missing=no_wit, n2_hits=n2_tot,
        n2_type_decided_at_N=n2_type_decided,
        note="type-decided hits refute SEMANTIC-type absorption; tree "
             "witnesses confirm tree-undecidedness at N; operational "
             "(capped-walk) absorption is definitional since thr > N")
    with open(res_path, "w") as fh:
        json.dump(d, fh, indent=1)
    log(f"ABSORPTION AUDIT (all {tot} recorded hits): tree-record witness "
        f"found {tot - no_wit}/{tot} (missing: {no_wit}); n=2 hits "
        f"census-TYPE-decided at N: {n2_type_decided}/{n2_tot} -> the W-3 "
        f"semantic(type)/operational(tree) readings DIVERGE"
        + (" on concrete boxes" if n2_type_decided else " nowhere probed"))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--no-oracle", action="store_true")
    ap.add_argument("--stretch", action="store_true",
                    help="add (p=3, n=3, N=5): 14.3M boxes, slow")
    ap.add_argument("--audit-only", action="store_true",
                    help="re-run the absorption audit on the existing JSON")
    ap.add_argument("--out-dir", default=HERE)
    args = ap.parse_args()

    date = datetime.date.today().isoformat()
    log_path = os.path.join(args.out_dir, "logs", f"h3_en_falsifier_{date}.log")
    res_path = os.path.join(args.out_dir, "results",
                            "h3_en_falsifier_results.json")
    os.makedirs(os.path.dirname(log_path), exist_ok=True)
    os.makedirs(os.path.dirname(res_path), exist_ok=True)
    lf = open(log_path, "a")

    def log(msg):
        print(msg, flush=True)
        lf.write(msg + "\n")
        lf.flush()

    log(f"=== EN-U2 / G-EN-1 falsifier run {datetime.datetime.now().isoformat()}"
        f" (HDISCHARGE_H3 §3.3) ===")
    if args.audit_only:
        absorption_audit(res_path, log)
        lf.close()
        return
    oracle = None if args.no_oracle else True
    if oracle:
        try:
            r = gp_batch([("cr", [1, 0, 1], 2), ("ef", [1, 0, 1], 2),
                          ("ef", [3, 0, 1], 2), ("ef", [2, 0, 0, 1], 2)])
            assert r[0] == (2,) and r[1] == ((2, 1),) and r[2] == ((1, 2),) \
                and r[3] == ((3, 1),), r
            log("PARI gp oracle online (calibration: x^2+1 ram, x^2+3 inert, "
                "x^3+2 tot.ram over Q_2: PASS)")
        except Exception as exc:  # noqa: BLE001
            log(f"PARI gp oracle UNAVAILABLE ({exc}); running --no-oracle")
            oracle = None

    g1 = gate_VW_worked(log)
    g2 = gate_VE_eisenstein(log)
    g3 = gate_V4_persite(log)
    if not (g1 and g2 and g3):
        log("VALIDATION GATES FAILED — scan aborted, no adjudication.")
        sys.exit(1)

    rng = random.Random(20260801)
    configs = [(2, 2, N) for N in range(1, 6)] + \
              [(2, 3, N) for N in range(1, 6)] + \
              [(3, 2, N) for N in range(1, 6)] + \
              [(3, 3, N) for N in range(1, 5)]
    if args.stretch:
        configs.append((3, 3, 5))
    results = []
    for (p, n, N) in configs:
        results.append(scan_config(p, n, N, log, oracle, rng))

    oracle_ok = all(r.get("oracle_pass", True) for r in results)
    any_hit = any(r["hit_count"] > 0 for r in results)
    overall = dict(
        unit="EN-U2", gate="G-EN-1", date=date,
        machine="n<=3 linear-key OM tower (E_i=1), read ceiling "
                "L(H)=1+max ceil(I_i) per O1thr rev4 §3; "
                "fiber = realized runs on the zero-extended decode",
        gates=dict(V_worked=g1, V_eisenstein=g2, V4_persite=g3,
                   oracle_all_pass=oracle_ok, oracle_used=bool(oracle)),
        adjudication=("HIT" if any_hit else "NO-HIT"),
        results=results)
    with open(res_path, "w") as fh:
        json.dump(overall, fh, indent=1)
    log(f"JSON results -> {res_path}")
    absorption_audit(res_path, log)
    per = {(r['p'], r['n'], r['N']): (r['verdict'], r['hit_count'],
                                      r['min_margin']) for r in results}
    log(f"G-EN-1 ADJUDICATION: {overall['adjudication']}  "
        f"(per-config verdict/hits/min-margin: {per})")
    if any_hit:
        log("Consequence per HDISCHARGE_H3 §3.3: route (a) is DEAD as stated "
            "(compiled (E-N) counterexamples recorded above with realized-chain "
            "records + absorption witnesses); route (b) absorption verification "
            "is forced — the hit boxes are the worked instances.")
    else:
        log("Consequence: route (a) supported at the probed range; margins above.")
    lf.close()


if __name__ == "__main__":
    main()
