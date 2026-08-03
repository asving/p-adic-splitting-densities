#!/usr/bin/env python3
"""l3fit_m1_smallcases.py — M1 EXACT INTEGER EXPONENT FIT on the level-3 cocycle.

POST-SEAL DIAGNOSTIC; NOT PREREGISTERED.  This is NOT part of the sealed
ITER-LAW-r probe (seal 911431c); the sealed prereg text and runner are
READ-ONLY to this unit and are consumed by import only.  Charge (M1 of the
recovery lattice, Asvin's 2026-08-03 small-numerics directive): measure the
level-3 cocycle c3(g,g') = zbar^a * z2^b * z1^c on exhaustive tiny towers
(E3 in {4,6,8}, p in {2,3}) using the COMMITTED sealed harness calculus
(grb_order2_check.Tower + strata3_probe.Tower3 + iterlawr_probe.Composite3,
imported read-only), extract the integer exponents (a,b,c) per pair
STRUCTURALLY (slot indices of the committed reads + the definitional
eps-exponents; every extraction re-verified against the field value), build
a feature dictionary per pair from the anchor splits alone (NO candidate law
consumed), and solve the exact Z-linear system per exponent slot: minimal
feature supports with exact rational coefficients reproducing the measured
exponent on ALL training pairs, validated on held-out fresh towers (own
seed 20260810) and spot-checked on 20 tuples against M5's independent
harness (level3_xcheck.py, plain-lift convention).

No floating point anywhere: Fraction linear algebra, exact field arithmetic.
Patterns found here are CONJECTURES (instance evidence), not proofs.

Outputs: l3fit_m1_smallcases_output.txt (run with > redirect),
         l3fit_m1_results.json.
"""
import sys, os, json, math, random, itertools, time
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import iterlawr_probe as IL                      # read-only import (shim active)
from iterlawr_probe import Composite3
import strata3_probe as S3MOD
from strata3_probe import Tower3
import grb_order2_check as G
from grb_order2_check import dev, eq12, bezout, pmul
import level3_xcheck as M5                       # M5's independent harness

# =========================== rosters =========================================
# (name, ring, p, d0, r0, r1, r2); r_i = (e_i, h_i, g_i).  E3 = e0*e1*e2.
TRAIN = [
    ("T01", "Zp",  3, 1, (2,1,2), (1,1,2), (2,1,2)),  # E3=4 top+inner, e1=1
    ("T02", "Fpt", 2, 1, (2,1,2), (1,1,2), (2,1,2)),  # E3=4 char-2 ring
    ("T03", "Zp",  2, 1, (1,1,2), (2,1,2), (2,1,2)),  # E3=4 e0=1 CONTROL
    ("T04", "Fpt", 3, 1, (2,1,2), (2,1,2), (1,1,2)),  # E3=4 e2=1 CONTROL
    ("T05", "Zp",  3, 1, (2,1,2), (2,1,2), (2,1,2)),  # E3=8 all-stacked g=2
    ("T06", "Fpt", 3, 1, (2,1,1), (2,1,2), (2,1,2)),  # E3=8 g0=1 inner cascade
    ("T07", "Zp",  3, 1, (2,1,2), (2,3,1), (2,1,2)),  # E3=8 g1=1 mid cascade, h1=3
    ("T08", "Fpt", 2, 1, (2,1,1), (2,1,1), (2,1,2)),  # E3=8 double cascade
    ("T09", "Zp",  3, 1, (3,2,2), (1,1,2), (2,1,2)),  # E3=6 l0=2 leverage
    ("T10", "Fpt", 2, 1, (3,1,2), (1,1,2), (2,1,2)),  # E3=6 e0=3, l0=1
    ("T11", "Zp",  3, 1, (2,1,2), (1,1,2), (3,2,2)),  # E3=6 e2=3 h2=2 top track
    ("T12", "Fpt", 3, 1, (1,1,2), (3,2,2), (2,1,2)),  # E3=6 mid e1=3 h1=2 (l1=2)
    ("T13", "Zp",  2, 1, (2,3,2), (2,1,2), (2,1,1)),  # E3=8 h0=3; g2=1 (zbar in K2)
    ("T14", "Fpt", 2, 1, (2,1,2), (2,1,2), (2,1,2)),  # E3=8 all-stacked p=2
    ("T15", "Zp",  3, 1, (2,3,2), (2,3,2), (2,3,1)),  # E3=8 all-h=3 (K-analogue)
]
HOLDOUT_FIXED = [
    ("H01", "Zp",  2, 1, (2,1,2), (2,1,2), (2,1,2)),  # E3=8 all-stacked p=2 Zp
    ("H02", "Fpt", 3, 1, (3,2,2), (2,1,1), (1,1,2)),  # E3=6 l0=2 + g1=1, e2=1
    ("H03", "Zp",  3, 1, (1,1,2), (2,3,2), (3,1,2)),  # E3=6 e0=1, h1=3, e2=3
    ("H04", "Fpt", 2, 1, (2,3,2), (1,1,2), (4,1,2)),  # E3=8 e2=4 deep top carry
    ("H05", "Fpt", 3, 2, (2,1,1), (2,1,2), (2,1,2)),  # E3=8 d0=2 base inertia
    ("H06", "Zp",  2, 1, (2,3,2), (2,3,2), (2,3,2)),  # E3=8 all-h=3 all-g=2
    # STRETCH row, E3=12 (outside the {4,6,8} box, labeled): probe-row-B shape
    ("H07s","Zp",  3, 1, (3,2,1), (2,1,2), (2,1,2)),  # E3=12 l0=2 inner CaseII
]
HOLDOUT_SEED = 20260810      # M1's own seed (fresh; never used in this genre)
N_RANDOM_HOLDOUT = 3

def random_holdout_rows(rng):
    """Fresh random tiny specs, E3 in {4,6,8}, avoiding all fixed specs."""
    used = {(p, d0, r0, r1, r2) for _, _, p, d0, r0, r1, r2 in
            [(n, k, p, d, a, b, c) for (n, k, p, d, a, b, c) in TRAIN + HOLDOUT_FIXED]}
    combos = []
    for es in [(2,1,2),(1,2,2),(2,2,1),(2,2,2),(2,1,3),(3,1,2),(1,3,2),
               (1,2,3),(2,1,4),(4,1,2),(1,1,4),(2,4,1)]:
        for hs in itertools.product((1,3), (1,3), (1,2,3)):
            if any(math.gcd(e, h) != 1 for e, h in zip(es, hs)): continue
            for gs in itertools.product((1,2), repeat=3):
                combos.append(tuple(zip(es, hs, gs)))
    rows, tries = [], 0
    while len(rows) < N_RANDOM_HOLDOUT and tries < 4000:
        tries += 1
        r0, r1, r2 = rng.choice(combos)
        ring = rng.choice(("Zp", "Fpt")); p = rng.choice((2, 3))
        if (p, 1, r0, r1, r2) in used: continue
        used.add((p, 1, r0, r1, r2))
        rows.append((f"H{90+len(rows)}r", ring, p, 1, r0, r1, r2))
    return rows

# =========================== measurement =====================================
def onehot_nz(F, coeffs):
    return [j for j, c in enumerate(coeffs) if not F["isz"](c)]

def eps_exp(l, lp, e, h, beta):
    """definitional exponent of eps at (e,h): lp*s - l*u, (s,u)=eq12(beta,e,h)."""
    s, u = eq12(beta, e, h)
    return lp * s - l * u

def read2_struct(T3, A, expect_gamma=None):
    """Structural (z2exp, z1exp, flags) of the level-2 read VALUE R2v(A),
    A an O[x] digit: R2v(A) = sum_j2 R2w(A)[j2] z2^j2, and each K1 coefficient
    = eps1(gm)*R1w-read.  Returns dict or None (extraction failed)."""
    T = T3.T
    coeffs2, meta2 = T.R2w(A, with_meta=True)
    nz2 = [j for j, c in enumerate(coeffs2) if not T.K1["isz"](c)]
    if len(nz2) != 1:
        return None
    j2 = nz2[0]
    g2v = meta2["gamma"]
    if expect_gamma is not None and g2v != expect_gamma:
        return None
    sj = meta2["s2"] + j2 * T.e1
    num = g2v - sj * T.gamma2
    assert num % T.e1 == 0
    gm = num // T.e1
    e1exp = eps_exp(T.l0, T.l0p, T.e0, T.h0, gm)
    a_slot = meta2["dev"][sj]
    r1list = T.R1w(a_slot, gm)
    nz1 = [m for m, cf in enumerate(r1list) if any(cf)]
    if len(nz1) != 1:
        return None
    m = nz1[0]
    cf = r1list[m]
    one0 = tuple([1] + [0] * (T.d0 - 1))
    unit_dlog, unit_exact = 0, True
    if cf != one0:
        # non-1 residue unit (Case-II strata): express as z1-power in K1 if
        # possible; ambiguous mod ord(z1) -> flag inexact (excluded from solve)
        K1 = T.K1
        v = K1["embed"](cf); zp = K1["one"]; found = None
        for k in range(4000):
            if v == zp: found = k; break
            zp = K1["mul"](zp, T.z1)
        if found is None:
            return None
        unit_dlog, unit_exact = found, False
    # exponent of eps2 factor at the level-3 slot weight is added by caller
    return dict(j2=j2, m=m, gamma2read=g2v, gm=gm, e1exp=e1exp,
                unit_dlog=unit_dlog, unit_exact=unit_exact)

def val3_struct(C, f, expect_gamma=None):
    """Structural monomial data of val3(f) for an anchor/anchor-product:
    (top slot j0, z2-exponent, z1-exponent, exactness flags)."""
    T3 = C.T3; T = T3.T
    coeffs, meta = T3.R3w(f, with_meta=True)
    nz = [j for j, c in enumerate(coeffs) if not T3.K2["isz"](c)]
    if len(nz) != 1:
        return None
    j0 = nz[0]
    gv = meta["gamma"]
    if expect_gamma is not None and gv != expect_gamma:
        return None
    sj = meta["s3"] + j0 * T3.e2
    num = gv - sj * T3.gamma3
    assert num % T3.e2 == 0
    gj = num // T3.e2
    e2exp = eps_exp(T3.l1, T3.l1p, T.e1, T.h1, gj)
    A = meta["dev"][sj]
    r2 = read2_struct(T3, A, expect_gamma=gj)
    if r2 is None:
        return None
    return dict(j0=j0, gamma=gv,
                bexp=e2exp + r2["j2"],
                cexp=r2["e1exp"] + r2["m"] + r2["unit_dlog"],
                exact=r2["unit_exact"])

def letter_orders(C):
    K3 = C.K3
    def omul(x):
        if K3["isz"](x): return None
        o, y = 1, x
        while y != K3["one"]:
            y = K3["mul"](y, x); o += 1
            if o > K3["q"]: return None
        return o
    return dict(zbar=omul(C.zbar), z2=omul(C.z2_3), z1=omul(C.z1_3))

def k3_monomial(C, a, b, c):
    K3 = C.K3
    return K3["mul"](K3["pow"](C.zbar, a),
           K3["mul"](K3["pow"](C.z2_3, b), K3["pow"](C.z1_3, c)))

def measure_tower(name, ring, p, d0, r0, r1, r2):
    """Build the sealed-calculus tower, measure all W1xW1 pairs.  Returns
    (tower record, list of pair records).  Pure measurement, no law."""
    tag = f"{ring},p={p},{name}"
    T3 = Tower3(ring, p, d0, r0, r1, r2, tag)
    C = Composite3(T3)
    T = T3.T
    E3 = T3.E3
    W1 = list(range(C.Gamma0, C.Gamma0 + E3))
    ords = letter_orders(C)
    trec = dict(name=name, tag=tag, ring=ring, p=p, d0=d0, r0=r0, r1=r1, r2=r2,
                E3=E3, Gamma0=C.Gamma0, gamma2=T.gamma2, gamma3=T3.gamma3,
                w1Phi1=T.w1Phi1, w2Phi2=T.w2Phi2,
                l0=T.l0, l0p=T.l0p, l1=T.l1, l1p=T.l1p,
                l2=T3.l2, l2p=T3.l2p, orders=ords)
    pairs = []
    for ga in W1:
        for gb in W1:
            s3a, s2a, s1a, b2a, b1a, u1a = C.split(ga)
            s3b, s2b, s1b, b2b, b1b, u1b = C.split(gb)
            s3c, s2c, s1c, b2c, b1c, u1c = C.split(ga + gb)
            cval, vp, nz, gmeas = C.cocycle(ga, gb)
            prod = pmul(T3.R, C.anchor(ga), C.anchor(gb))
            sP = val3_struct(C, prod, expect_gamma=ga + gb)
            sA = val3_struct(C, C.anchor(ga + gb), expect_gamma=ga + gb)
            # cascade-stratum flags: on these rows the STRUCTURAL exponent
            # tuple is a lattice-coset representative that can differ from a
            # universal integer formula's representative (the reduction step
            # hides letter content in residue units / twisted digit
            # representations).  Verified pairwise by field value; EXCLUDED
            # from the exact solves.
            mid2 = (r1[2] == 1 and (s2a + s2b) // r1[0] == 1)  # g1=1 & d2=1
            inn1 = (r0[2] == 1)                                # g0=1 tower
            rec = dict(tower=name, ga=ga, gb=gb,
                       s3a=s3a, s3b=s3b, s3c=s3c, s2a=s2a, s2b=s2b, s2c=s2c,
                       s1a=s1a, s1b=s1b, s1c=s1c,
                       b2a=b2a, b2b=b2b, b2c=b2c, b1a=b1a, b1b=b1b, b1c=b1c,
                       mid2=mid2, inn1=inn1,
                       struct_ok=False, exact_b=False, exact_c=False)
            if sP is not None and sA is not None:
                a_m = sP["j0"] - sA["j0"]
                b_m = sP["bexp"] - sA["bexp"]
                c_m = sP["cexp"] - sA["cexp"]
                # re-verify the structural monomial against the field value
                if k3_monomial(C, a_m, b_m, c_m) == cval:
                    rec.update(a=a_m, b=b_m, c=c_m, struct_ok=True,
                               exact_b=not mid2,
                               exact_c=(sP["exact"] and sA["exact"]
                                        and not inn1 and not mid2))
            pairs.append(rec)
    return trec, C, pairs

# =========================== features ========================================
def features(trec, rec):
    """Feature dictionary per pair, per slot.  Everything computed from the
    tower constants and the anchor SPLITS alone (no candidate law).  Values
    are exact Fractions.  Sig_i = realized level-i shift beta_i''-beta_i-beta_i'
    (pure split bookkeeping)."""
    e0, h0, _ = trec["r0"]; e1, h1, _ = trec["r1"]; e2, h2, _ = trec["r2"]
    l0, l0p, l1, l1p = trec["l0"], trec["l0p"], trec["l1"], trec["l1p"]
    l2, l2p = trec["l2"], trec["l2p"]
    g2c, g3c = trec["gamma2"], trec["gamma3"]
    w1P, w2P = trec["w1Phi1"], trec["w2Phi2"]
    F = Fraction
    d3 = (rec["s3a"] + rec["s3b"]) // e2
    d2 = (rec["s2a"] + rec["s2b"]) // e1
    d1 = (rec["s1a"] + rec["s1b"]) // e0
    sdef3 = rec["s3a"] + rec["s3b"] - rec["s3c"]
    sdef2 = rec["s2a"] + rec["s2b"] - rec["s2c"]
    sdef1 = rec["s1a"] + rec["s1b"] - rec["s1c"]
    Sig2 = rec["b2c"] - rec["b2a"] - rec["b2b"]
    Sig1 = rec["b1c"] - rec["b1a"] - rec["b1b"]
    D2f = F(sdef2 + l1 * g3c * d3, e1)          # composed middle (as feature)
    fA = {
        "1":            F(1),
        "d3":           F(d3),
        "d2":           F(d2),
        "d1":           F(d1),
        "sdef3/e2":     F(sdef3, e2),
        "sdef2/e1":     F(sdef2, e1),
        "Sig2/g3c":     F(Sig2, g3c),
        "fl(s3+s3p,e1)": F((rec["s3a"] + rec["s3b"]) // e1),
        "l2*d3":        F(l2 * d3),
        "h2*d3":        F(h2 * d3),
    }
    fB = {
        "1":            F(1),
        "d2":           F(d2),
        "d3":           F(d3),
        "d1":           F(d1),
        "sdef2/e1":     F(sdef2, e1),
        "l1*g3c*d3/e1": F(l1 * g3c * d3, e1),
        "l1*g2c*d2/e1": F(l1 * g2c * d2, e1),
        "l1p*g3c*d3/e1": F(l1p * g3c * d3, e1),
        "l1*Sig2/e1":   F(l1 * Sig2, e1),
        "l1*g3c*d2/e1": F(l1 * g3c * d2, e1),
        "l1*g2c*d3/e1": F(l1 * g2c * d3, e1),
        "l1*h2*d3/e1":  F(l1 * h2 * d3, e1),
        "l2*d3":        F(l2 * d3),
        "sdef2":        F(sdef2),
    }
    fC = {
        "1":            F(1),
        "d1":           F(d1),
        "d2":           F(d2),
        "d3":           F(d3),
        "sdef1/e0":     F(sdef1, e0),
        "l0*g2c*d2/e0": F(l0 * g2c * d2, e0),       # the NAIVE fibration term
        "l0*Sig1/e0":   F(l0 * Sig1, e0),           # realized inner shift
        "l0*g3c*d3/e0": F(l0 * g3c * d3, e0),
        "l0*g2c*D2f/e0": F(l0 * g2c, e0) * D2f,     # composed piece 1
        "l0*g3c*(l1p-l1*w1P)*d3/e0":
                        F(l0 * g3c * (l1p - l1 * w1P) * d3, e0),  # piece 2
        "l0*g3c*l1p*d3/e0": F(l0 * g3c * l1p * d3, e0),
        "l0*g3c*l1*w1P*d3/e0": F(l0 * g3c * l1 * w1P * d3, e0),
        "l0p*g2c*d2/e0": F(l0p * g2c * d2, e0),
        "l0*h1*d3/e0":  F(l0 * h1 * d3, e0),
        "sdef1":        F(sdef1),
        "l0*g2c*Sig2/(e0*g3c)": F(l0 * g2c * Sig2, e0 * g3c),
    }
    consts = dict(d3=d3, d2=d2, d1=d1, sdef3=sdef3, sdef2=sdef2, sdef1=sdef1,
                  Sig2=Sig2, Sig1=Sig1)
    return fA, fB, fC, consts

# =========================== exact linear fit ================================
def solve_exact(rows, targets):
    """Exact rational solve of rows*theta = targets (overdetermined).
    Returns theta list or None if inconsistent.  Gaussian elimination over
    Fraction; free variables set to 0 (particular solution)."""
    m = [list(r) + [t] for r, t in zip(rows, targets)]
    nr, nc = len(m), len(m[0]) - 1
    piv_cols, r = [], 0
    for c in range(nc):
        pr = next((i for i in range(r, nr) if m[i][c] != 0), None)
        if pr is None: continue
        m[r], m[pr] = m[pr], m[r]
        pv = m[r][c]
        m[r] = [x / pv for x in m[r]]
        for i in range(nr):
            if i != r and m[i][c] != 0:
                f = m[i][c]
                m[i] = [x - f * y for x, y in zip(m[i], m[r])]
        piv_cols.append(c); r += 1
        if r == nr: break
    for i in range(r, nr):
        if m[i][nc] != 0:
            return None                       # inconsistent
    theta = [Fraction(0)] * nc
    for i, c in enumerate(piv_cols):
        theta[c] = m[i][nc]
    return theta

def merge_columns(names, matrix):
    """Projective merge: columns equal up to a nonzero rational scale form one
    class.  Returns (class list [(rep_name, members, column)], col matrix)."""
    classes = []
    for j, nm in enumerate(names):
        col = tuple(row[j] for row in matrix)
        if all(x == 0 for x in col):
            continue                          # drop identically-zero features
        placed = False
        for cl in classes:
            rcol = cl["col"]
            # find scale k with col = k*rcol
            k = None
            for x, y in zip(col, rcol):
                if y != 0:
                    k = x / y; break
            if k is not None and k != 0 and all(x == k * y for x, y in zip(col, rcol)):
                cl["members"].append((nm, k)); placed = True; break
        if not placed:
            classes.append(dict(rep=nm, members=[(nm, Fraction(1))], col=col))
    return classes

def fit_slot(slotname, names, matrix, targets, max_support=4, log=print):
    """Search minimal feature supports (over merged classes) exactly
    reproducing targets on all rows.  Returns dict with all minimal fits."""
    classes = merge_columns(names, matrix)
    cols = [cl["col"] for cl in classes]
    n = len(classes)
    log(f"\n  [{slotname}] {len(matrix)} rows, {len(names)} features -> "
        f"{n} merged classes:")
    for cl in classes:
        mem = ", ".join(f"{nm}" + (f" (x{k})" if k != 1 else "")
                        for nm, k in cl["members"])
        log(f"      class[{cl['rep']}]: {mem}")
    if all(t == 0 for t in targets):
        log(f"  [{slotname}] all targets ZERO -> empty support fits")
        return dict(classes=classes, minimal_size=0, fits=[([], [])])
    wins, size = [], None
    for k in range(1, max_support + 1):
        for sub in itertools.combinations(range(n), k):
            rows = [[cols[j][i] for j in sub] for i in range(len(targets))]
            th = solve_exact(rows, targets)
            if th is None: continue
            if any(x == 0 for x in th): continue   # not a minimal support
            wins.append((list(sub), th))
        if wins:
            size = k; break
    return dict(classes=classes, minimal_size=size, fits=wins)

def fit_display(fitres):
    """Human formula strings for every minimal fit."""
    out = []
    for sub, th in fitres["fits"]:
        terms = []
        for j, coef in zip(sub, th):
            rep = fitres["classes"][j]["rep"]
            cs = "" if coef == 1 else f"{coef}*"
            terms.append(f"{cs}{rep}")
        out.append(" + ".join(terms) if terms else "0")
    return out

def forced_analysis(slotname, fitres, targets, max_extra=1, log=print):
    """Which merged classes are FORCED: no exact fit of size <= minimal+extra
    avoids them.  Only classes appearing in some minimal fit are tested."""
    if fitres["minimal_size"] in (None, 0): return {}
    classes = fitres["classes"]; cols = [cl["col"] for cl in classes]
    n = len(classes)
    used = sorted({j for sub, _ in fitres["fits"] for j in sub})
    forced = {}
    for j in used:
        ok = False
        for k in range(1, fitres["minimal_size"] + max_extra + 1):
            for sub in itertools.combinations([i for i in range(n) if i != j], k):
                rows = [[cols[jj][i] for jj in sub] for i in range(len(targets))]
                if solve_exact(rows, targets) is not None:
                    ok = True; break
            if ok: break
        forced[classes[j]["rep"]] = not ok
        log(f"      class[{classes[j]['rep']}]: "
            f"{'FORCED (no substitute up to size ' + str(fitres['minimal_size']+max_extra) + ')' if not ok else 'substitutable'}")
    return forced

# =========================== law evaluation ==================================
def law_from_fit(fitres, which=0):
    """Returns evaluator: fdict -> Fraction, using merged-class representative
    feature names (members[0] is the representative with scale 1)."""
    if fitres["minimal_size"] == 0:
        return lambda fdict: Fraction(0), "0"
    if not fitres["fits"]:
        return None, "NO EXACT FIT FOUND (support <= max searched)"
    sub, th = fitres["fits"][which]
    reps = [fitres["classes"][j]["rep"] for j in sub]
    def ev(fdict, reps=reps, th=th):
        return sum((c * fdict[r] for r, c in zip(reps, th)), Fraction(0))
    disp = " + ".join((f"{c}*" if c != 1 else "") + r for r, c in zip(reps, th))
    return ev, disp

def verify_law(towers, evA, evB, evC, log=print, label="LAW"):
    """Field-verify the fitted integer law on every measured pair of every
    tower: exponents must be integers and zbar^A z2^B z1^C == measured c3.
    Returns (ok pairs, nonint pairs, mismatch pairs, per-tower detail)."""
    ok = nonint = mism = 0
    detail = {}
    for name, (trec, C, pairs) in towers.items():
        t_ok = t_ni = t_mm = 0
        for rec in pairs:
            fA, fB, fC, _ = features(trec, rec)
            A, B, Cv = evA(fA), evB(fB), evC(fC)
            if any(x.denominator != 1 for x in (A, B, Cv)):
                t_ni += 1; continue
            cval = C.cocycle(rec["ga"], rec["gb"])[0]
            if k3_monomial(C, int(A), int(B), int(Cv)) == cval:
                t_ok += 1
            else:
                t_mm += 1
        ok += t_ok; nonint += t_ni; mism += t_mm
        detail[name] = (t_ok, t_ni, t_mm)
        if t_ni or t_mm:
            log(f"    {label} {name}: ok={t_ok} NONINTEGRAL={t_ni} MISMATCH={t_mm}")
    return ok, nonint, mism, detail

def census_alternative(towers, evA, evB, evC_alt, log, label):
    """Same as verify_law but reports the split for an ALTERNATIVE c-slot law
    (e.g. the naive per-level template)."""
    ok, nonint, mism, detail = verify_law(towers, evA, evB, evC_alt,
                                          log=lambda *a: None, label=label)
    tot = ok + nonint + mism
    log(f"  {label}: {ok}/{tot} exact; {nonint} NONINTEGRAL exponent; "
        f"{mism} integral-but-wrong-value")
    per = {n: d for n, d in detail.items() if d[1] or d[2]}
    if per:
        log(f"    failing towers: " +
            ", ".join(f"{n}(ok={o},ni={ni},mm={mm})" for n, (o, ni, mm) in sorted(per.items())))
    return ok, nonint, mism

# =========================== eyeballable tables ==============================
def print_table(trec, C, pairs, evA, evB, evC, log):
    ords = trec["orders"]
    log(f"\n== {trec['name']} ({trec['tag']}): d0={trec['d0']} "
        f"reads={trec['r0']},{trec['r1']},{trec['r2']}  E3={trec['E3']}")
    log(f"   gamma2={trec['gamma2']} gamma3={trec['gamma3']} "
        f"w1Phi1={trec['w1Phi1']} w2Phi2={trec['w2Phi2']}  "
        f"bez (l0,l0p)=({trec['l0']},{trec['l0p']}) (l1,l1p)=({trec['l1']},{trec['l1p']}) "
        f"(l2,l2p)=({trec['l2']},{trec['l2p']})")
    log(f"   letter orders: zbar={ords['zbar']} z2={ords['z2']} z1={ords['z1']}"
        f"   Gamma0={trec['Gamma0']}")
    log(f"   {'g':>5} {'gp':>5} | s3 s3p s3s | s2 s2p s2s | s1 s1p s1s |"
        f" d3 d2 d1 | Sig2 Sig1 | measured (a,b,c) | fitted (A,B,C) | ok")
    for rec in pairs:
        fA, fB, fC, cst = features(trec, rec)
        A, B, Cv = evA(fA), evB(fB), evC(fC)
        flag = ""
        if rec.get("mid2"): flag += "*m2"
        if rec.get("inn1") and cst["d1"] == 1: flag += "*i1"
        meas = (f"({rec['a']},{rec['b']},{rec['c']}){flag}"
                if rec["struct_ok"] else "nonstruct")
        intg = all(x.denominator == 1 for x in (A, B, Cv))
        okc = "?"
        if intg:
            cval = C.cocycle(rec["ga"], rec["gb"])[0]
            okc = "Y" if k3_monomial(C, int(A), int(B), int(Cv)) == cval else "MISMATCH"
        fit = f"({A},{B},{Cv})" if intg else f"NONINT({A},{B},{Cv})"
        log(f"   {rec['ga']:>5} {rec['gb']:>5} | {rec['s3a']:>2} {rec['s3b']:>3} {rec['s3c']:>3} |"
            f" {rec['s2a']:>2} {rec['s2b']:>3} {rec['s2c']:>3} |"
            f" {rec['s1a']:>2} {rec['s1b']:>3} {rec['s1c']:>3} |"
            f" {cst['d3']:>2} {cst['d2']:>2} {cst['d1']:>2} |"
            f" {cst['Sig2']:>4} {cst['Sig1']:>4} | {meas:>16} | {fit:>12} | {okc}")

# =========================== M5 spot-check ===================================
def conv_elem(x, level):
    """sealed K_level element (d0=1 nesting) -> M5 representation."""
    if level == 0:
        return x[0]                       # K0 = 1-tuple of int -> int
    return tuple(conv_elem(c, level - 1) for c in x)

def m5_spotcheck(towers, fitted, rng, log):
    """20 tuples: rebuild d0=1 towers in M5's independent harness (level3_xcheck,
    plain-lift convention) with the SEALED psi data transplanted, and check the
    fitted integer law reproduces M5's measured cocycle in M5's field.
    g1=1 rows use M5's measured lift-deviation display c3^plain =
    c3^canon * eps1(gamma2)^{d2} (L3XCHECK S0.6, conjecture-grade) — checked
    as stated there; a failure of that factor is reported as DEV-FAIL."""
    evA, evB, evC = fitted
    chosen = ["T01", "T05", "T09", "T02", "T07"]     # T07 is the g1=1 row
    n_ok = n_bad = 0
    for name in chosen:
        trec, C, pairs = towers[name]
        T3 = C.T3; T = T3.T
        R = M5.ZRing(trec["p"]) if trec["ring"] == "Zp" else M5.TRing(trec["p"])
        reads = [(T.e0, T.h0, [conv_elem(c, 0) for c in T.psi0[:-1]]),
                 (T.e1, T.h1, [conv_elem(c, 1) for c in T.psi1[:-1]]),
                 (T3.e2, T3.h2, [conv_elem(c, 2) for c in T3.psi2[:-1]])]
        TM = M5.Tower(R, reads)
        KN = TM.K[3]
        zb_m, z2_m, z1_m = (TM.embed_letter(3), TM.embed_letter(2),
                            TM.embed_letter(1))
        g1_is_1 = trec["r1"][2] == 1
        devexp = 0
        if g1_is_1:
            devexp = eps_exp(trec["l0"], trec["l0p"],
                             trec["r0"][0], trec["r0"][1], trec["gamma2"])
        cand = [r for r in pairs if r["struct_ok"]]
        if g1_is_1:
            # exercise the lift-deviation leg: half the picks at d2 = 1
            e1 = trec["r1"][0]
            c_dev = [r for r in cand if (r["s2a"] + r["s2b"]) // e1 >= 1]
            c_pln = [r for r in cand if (r["s2a"] + r["s2b"]) // e1 == 0]
            picks = rng.sample(c_dev, min(2, len(c_dev))) + \
                    rng.sample(c_pln, 4 - min(2, len(c_dev)))
        else:
            picks = rng.sample(cand, 4)
        for rec in picks:
            fA, fB, fC, cst = features(trec, rec)
            A, B, Cv = int(evA(fA)), int(evB(fB)), int(evC(fC))
            cm5, diag = TM.cocycle(rec["ga"], rec["gb"])
            shift = devexp * cst["d2"] if g1_is_1 else 0
            pred = KN.mul(KN.ppow(zb_m, A),
                   KN.mul(KN.ppow(z2_m, B), KN.ppow(z1_m, Cv + shift)))
            ok = (cm5 is not None and cm5 == pred)
            n_ok += ok; n_bad += (not ok)
            log(f"    M5-XCHK {name} ({rec['ga']},{rec['gb']}): fitted "
                f"(a,b,c)=({A},{B},{Cv})"
                + (f" +liftdev z1^{shift}" if shift else "")
                + f" -> {'MATCH' if ok else 'FAIL'}")
    return n_ok, n_bad

# =========================== main ============================================
def dedup(rows, targets):
    """Drop duplicate (features, target) rows; KEEP conflicting rows (same
    features, different target — the honest no-exact-fit signal), report."""
    seen, R, T, conflicts = {}, [], [], 0
    for r, t in zip(rows, targets):
        k = tuple(r)
        if k in seen:
            if t in seen[k]: continue
            conflicts += 1
        seen.setdefault(k, set()).add(t)
        R.append(r); T.append(t)
    if conflicts:
        print(f"  WARNING: {conflicts} feature-collision rows with DIFFERENT "
              f"targets (dictionary cannot separate them; no exact fit can "
              f"exist on this dictionary)")
    return R, T

def main():
    t0 = time.time()
    rng = random.Random(HOLDOUT_SEED)
    log = print
    log("=" * 78)
    log("M1 EXACT INTEGER EXPONENT FIT — level-3 cocycle, tiny towers")
    log("POST-SEAL DIAGNOSTIC; NOT PREREGISTERED (seal 911431c read-only)")
    log("=" * 78)
    holdout_rows = HOLDOUT_FIXED + random_holdout_rows(rng)
    log(f"train rosters: {[r[0] for r in TRAIN]}")
    log(f"holdout rosters (seed {HOLDOUT_SEED}): {[r[0] for r in holdout_rows]}")

    towers, ho_towers = {}, {}
    n_pairs = n_struct = n_exc = 0
    for row in TRAIN:
        trec, C, pairs = measure_tower(*row)
        towers[row[0]] = (trec, C, pairs)
        ns = sum(r["struct_ok"] for r in pairs)
        nb = sum(r["exact_b"] for r in pairs)
        ne = sum(r["exact_c"] for r in pairs)
        n_pairs += len(pairs); n_struct += ns; n_exc += ne
        log(f"  measured {trec['tag']:22} E3={trec['E3']:>2} pairs={len(pairs):>3} "
            f"struct={ns:>3} exact_b={nb:>3} exact_c={ne:>3} orders(zb,z2,z1)="
            f"({trec['orders']['zbar']},{trec['orders']['z2']},{trec['orders']['z1']})")
    log(f"TRAIN: {n_pairs} pairs, {n_struct} structural, {n_exc} exact-c "
        f"[{time.time()-t0:.1f}s]")
    for row in holdout_rows:
        trec, C, pairs = measure_tower(*row)
        ho_towers[row[0]] = (trec, C, pairs)
        log(f"  measured {trec['tag']:22} E3={trec['E3']:>2} pairs={len(pairs):>3} "
            f"struct={sum(r['struct_ok'] for r in pairs):>3}")
    log(f"HOLDOUT measured [{time.time()-t0:.1f}s]")

    # ---------------- training matrices (structural rows only) --------------
    namesA = namesB = namesC = None
    XA, yA, XB, yB, XC, yC = [], [], [], [], [], []
    for name, (trec, C, pairs) in towers.items():
        for rec in pairs:
            if not rec["struct_ok"]: continue
            fA, fB, fC, _ = features(trec, rec)
            if namesA is None:
                namesA, namesB, namesC = (list(fA), list(fB), list(fC))
            XA.append([fA[k] for k in namesA]); yA.append(Fraction(rec["a"]))
            if rec["exact_b"]:
                XB.append([fB[k] for k in namesB]); yB.append(Fraction(rec["b"]))
            if rec["exact_c"]:
                XC.append([fC[k] for k in namesC]); yC.append(Fraction(rec["c"]))
    XAd, yAd = dedup(XA, yA); XBd, yBd = dedup(XB, yB); XCd, yCd = dedup(XC, yC)
    log(f"\nFIT MATRICES: a-slot {len(XA)}->{len(XAd)} distinct rows; "
        f"b-slot {len(XB)}->{len(XBd)}; c-slot {len(XC)}->{len(XCd)}")

    fitA = fit_slot("a-slot (zbar)", namesA, XAd, yAd, log=log)
    fitB = fit_slot("b-slot (z2)", namesB, XBd, yBd, log=log)
    fitC = fit_slot("c-slot (z1)", namesC, XCd, yCd, log=log)
    for nm, fr in (("a", fitA), ("b", fitB), ("c", fitC)):
        log(f"  [{nm}-slot] minimal support size = {fr['minimal_size']}; "
            f"{len(fr['fits'])} minimal fit(s):")
        for d in fit_display(fr):
            log(f"      {nm} = {d}")
    log(f"\nFORCED-FEATURE ANALYSIS (substitute search up to minimal+1):")
    log(f"  [a-slot]"); forcedA = forced_analysis("a", fitA, yAd, log=log)
    log(f"  [b-slot]"); forcedB = forced_analysis("b", fitB, yBd, log=log)
    log(f"  [c-slot]"); forcedC = forced_analysis("c", fitC, yCd, log=log)

    # ---------------- c-slot closed form (realized-shift-free refit) --------
    log(f"\nC-SLOT REFIT WITHOUT the realized-shift class [l0*Sig1/e0] "
        f"(the closed composed form, discovered by search):")
    keepC = [j for j, nm in enumerate(namesC) if nm != "l0*Sig1/e0"]
    namesC2 = [namesC[j] for j in keepC]
    XC2 = [[row[j] for j in keepC] for row in XCd]
    fitC2 = fit_slot("c-slot closed", namesC2, XC2, yCd, log=lambda *a: None)
    log(f"  minimal support size = {fitC2['minimal_size']}; "
        f"{len(fitC2['fits'])} minimal fit(s):")
    for d in fit_display(fitC2):
        log(f"      c = {d}")

    # ---------------- combined verification ---------------------------------
    evA, dispA = law_from_fit(fitA)
    evB, dispB = law_from_fit(fitB)
    evC, dispC = law_from_fit(fitC)
    evC2, dispC2 = law_from_fit(fitC2)
    log(f"\nTHE FITTED LAW (primary minimal fit per slot):")
    log(f"    c3(g,g') = zbar^a * z2^b * z1^c   with")
    log(f"    a = {dispA}")
    log(f"    b = {dispB}")
    log(f"    c = {dispC}")
    log(f"\nFIELD VERIFICATION (every pair, incl. non-structural rows):")
    ok, ni, mm, _ = verify_law(towers, evA, evB, evC, log=log, label="TRAIN")
    log(f"  TRAIN:   {ok}/{ok+ni+mm} exact ({ni} nonintegral, {mm} mismatch)")
    ok2, ni2, mm2, _ = verify_law(ho_towers, evA, evB, evC, log=log, label="HOLDOUT")
    log(f"  HOLDOUT: {ok2}/{ok2+ni2+mm2} exact ({ni2} nonintegral, {mm2} mismatch)")

    # ---------------- alternative-template censuses -------------------------
    log(f"\nALTERNATIVE-TEMPLATE CENSUSES (same fitted a,b; c-slot swapped):")
    def evC_naive(fC): return fC["sdef1/e0"] + fC["l0*g2c*d2/e0"]
    def evC_nocorr(fC): return fC["sdef1/e0"]
    def evC_d3g3(fC): return fC["sdef1/e0"] + fC["l0*g3c*d3/e0"]
    nv = census_alternative({**towers, **ho_towers}, evA, evB, evC_naive, log,
                            "NAIVE per-level template (l0*gamma2*d2 correction)")
    nc = census_alternative({**towers, **ho_towers}, evA, evB, evC_nocorr, log,
                            "NO-CORRECTION template (bare s1-defect)")
    dg = census_alternative({**towers, **ho_towers}, evA, evB, evC_d3g3, log,
                            "BARE-d3 template (l0*gamma3*d3 correction)")
    def evB_nocorr(fB): return fB["sdef2/e1"]
    bv = census_alternative({**towers, **ho_towers}, evA, evB_nocorr, evC, log,
                            "B-SLOT no-correction (bare s2-defect, fitted c)")

    # ---------------- M5 spot-check ------------------------------------------
    log(f"\nM5 CROSS-HARNESS SPOT-CHECK (20 tuples, transplanted psi data):")
    m5ok, m5bad = m5_spotcheck(towers, (evA, evB, evC), rng, log)
    log(f"  M5 spot-check: {m5ok}/20 match, {m5bad} fail")

    # ---------------- eyeballable tables -------------------------------------
    log(f"\n" + "=" * 78)
    log("FULL SMALL-CASE TABLES (per-pair rows; measured vs fitted)")
    log("=" * 78)
    for name in [r[0] for r in TRAIN] + [r[0] for r in holdout_rows]:
        src = towers if name in towers else ho_towers
        trec, C, pairs = src[name]
        print_table(trec, C, pairs, evA, evB, evC, log)

    # ---------------- summary + json -----------------------------------------
    verdict = ("ALL-EXACT" if ni + mm + ni2 + mm2 == 0 and m5bad == 0
               else "DISCREPANCIES — see above")
    log(f"\nSUMMARY: train {ok}/{ok+ni+mm}, holdout {ok2}/{ok2+ni2+mm2}, "
        f"M5 {m5ok}/20 -> {verdict}   [{time.time()-t0:.1f}s]")
    res = dict(
        unit="M1 exact integer exponent fit (post-seal diagnostic)",
        seed=HOLDOUT_SEED,
        train_rows=[r[0] for r in TRAIN],
        holdout_rows=[r[0] for r in holdout_rows],
        towers={n: dict(tag=t[0]["tag"], E3=t[0]["E3"],
                        r0=t[0]["r0"], r1=t[0]["r1"], r2=t[0]["r2"],
                        d0=t[0]["d0"], orders=t[0]["orders"],
                        Gamma0=t[0]["Gamma0"],
                        n_pairs=len(t[2]),
                        n_struct=sum(r["struct_ok"] for r in t[2]),
                        n_exact_c=sum(r["exact_c"] for r in t[2]))
                for n, t in {**towers, **ho_towers}.items()},
        fit=dict(a=dict(size=fitA["minimal_size"], fits=fit_display(fitA),
                        forced=forcedA),
                 b=dict(size=fitB["minimal_size"], fits=fit_display(fitB),
                        forced=forcedB),
                 c=dict(size=fitC["minimal_size"], fits=fit_display(fitC),
                        forced=forcedC),
                 c_closed=dict(size=fitC2["minimal_size"],
                               fits=fit_display(fitC2))),
        law=dict(a=dispA, b=dispB, c=dispC, c_closed=dispC2),
        verify=dict(train=[ok, ni, mm], holdout=[ok2, ni2, mm2]),
        alternatives=dict(naive=list(nv), nocorr=list(nc), bare_d3=list(dg),
                          b_nocorr=list(bv)),
        m5_spotcheck=[m5ok, m5bad],
        verdict=verdict,
        elapsed=round(time.time() - t0, 1))
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "l3fit_m1_results.json"), "w") as fh:
        json.dump(res, fh, indent=1, default=str)
    return 0 if verdict == "ALL-EXACT" else 1

if __name__ == "__main__":
    sys.exit(main())
