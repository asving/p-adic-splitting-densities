#!/usr/bin/env python3
"""l3finger_m4.py — M4: VALUE-SET / ASSOCIATIVITY / CROSSED-PRODUCT FINGERPRINTS.

*** POST-SEAL DIAGNOSTIC — NON-PREREG. ***
The sealed prereg (ITERLAWR_PROBE_2026-08-08.md + iterlawr_probe.py, seal
911431c) is READ-ONLY and byte-untouched; this runner IMPORTS the sealed
harness classes verbatim and adds representation-level structure checks that
constrain the level-3 cocycle law's SHAPE independently of any template fit:

  FP0  harness sanity on the fresh roster (anchor = eps-chain; top-slot shape;
       ITER-LAW-3 closed form recorded as a decorrelated confirmation count).
  FP1  VALUE-SET: full W1xW1 measured tables; which monomials zbar^a z2^b z1^c
       occur, with multiplicities; box-decomposition ambiguity flagged.
  FP2  SWAP symmetry: c3(g,g') == c3(g',g) exactly (symmetric/antisym split).
  FP3  Z/E3 DESCENT (COR-4 at level 3): single-argument, simultaneous, and
       k in {2,5} representative shifts, measured-side, exact.
  FP4  B0a GENRE at level 3: c3 == zbar^{j_meas} * dF, F = eps-chain (the
       accepted order-2 decomposition genre, one level up); j_meas symmetric,
       j_meas == floor((s3+s3')/e2), and the j 2-cocycle identity on triples;
       measured associativity on the same triples.
  FP5  CROSSED-PRODUCT RESTRICTION: on the E2-subwindow (e2 | gamma both
       args) measured c3 == K3-embed of the MEASURED level-2 cocycle at
       (gamma/e2, gamma'/e2) EXACTLY; off the subwindow the deviation of the
       zbar-stripped body from the level-2 shadow c2(beta2,beta2') is
       censused and localized (expected: exactly the d3 = 1 stratum, factor
       zbar-free).
  FP6  e2-QUOTIENT fingerprint: the measured top-slot j factors through
       (gamma mod e2, gamma' mod e2) and is the carry table of the extension
       0 -> Z/E2 -> Z/E3 -> Z/e2 -> 0 (h2-twisted).
  FP7  DENOMINATOR / integrality census: which denominators the exponent
       tracks actually need (e1 NEW in the middle, e0 inner as accepted,
       e0*e1 NEVER), field battery + 20k symbolic draws.

Fresh tiny-tower roster (E3 in {4,6,8}, p in {2,3}, all four rings; none is a
sealed-roster row).  Seed 20260813 (fresh).  Exact arithmetic only.
Outputs: l3finger_m4_output.txt + l3finger_m4_results.json.
Author: Fable, M4 fingerprint unit, campaign 2026-08-08 (wallclock 2026-08-03).
"""
import sys, os, json, math, random, time, collections

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import iterlawr_probe as IP                 # sealed runner, READ-ONLY import
from iterlawr_probe import Composite3       # (import applies its disclosed
from strata3_probe import Tower3            #  pick_irr3 wraparound shim)
import strata_probe as SP
import grb_order2_check as G
from grb_order2_check import eq12, bezout, pmul

SEED = 20260813

# tag, d0, (e0,h0,g0), (e1,h1,g1), (e2,h2,g2)   — all fresh shapes
ROWS = [
    ("Q4A", 1, (2,1,2), (1,1,2), (2,1,2)),  # E3=4; ALL letters genuine; e1=1
    ("Q4B", 1, (1,1,2), (2,1,2), (2,1,1)),  # E3=4; e0=1; top cascade g2=1
    ("Q4C", 1, (2,3,1), (1,1,1), (2,3,2)),  # E3=4; h-track 3; inner cascade
    ("Q4D", 1, (2,1,2), (2,1,2), (1,1,2)),  # E3=4; e2=1 CONTROL (restr. triv)
    ("Q6A", 1, (2,1,2), (1,1,1), (3,1,2)),  # E3=6; e2=3; z1,zbar genuine
    ("Q6B", 1, (3,2,1), (1,1,2), (2,1,2)),  # E3=6; e0=3, l0=2
    ("Q6C", 1, (1,1,2), (2,1,1), (3,2,2)),  # E3=6; e1=2 != e2=3; mid cascade
    ("Q6D", 1, (2,1,2), (3,1,1), (1,1,2)),  # E3=6; e2=1 CONTROL at E2=6
    ("Q8A", 1, (2,1,2), (2,1,2), (2,1,2)),  # E3=8; full stack, all genuine
    ("Q8B", 1, (2,1,1), (2,3,1), (2,1,2)),  # E3=8; double cascade, zbar vis
    ("Q8C", 2, (2,3,1), (2,3,2), (2,3,1)),  # E3=8; d0=2 inertia, h-track 3
]
CONFIGS = [("Zp",2), ("Zp",3), ("Fpt",2), ("Fpt",3)]
DISPLAY = {("Zp",3,"Q4A"), ("Zp",2,"Q4C"), ("Fpt",3,"Q6A"),
           ("Zp",3,"Q6C"), ("Zp",3,"Q8A")}

OUT = []
def emit(s=""):
    OUT.append(s); print(s)

# ---------------------------------------------------------------------------
def ord_of(K, x, cap=20000):
    """multiplicative order of x in K^x (None if 0 or > cap)."""
    if K["isz"](x): return None
    o, y = 1, x
    while y != K["one"] and o <= cap:
        y = K["mul"](y, x); o += 1
    return o if y == K["one"] else None

class Mono:
    """Monomial decomposition service zbar^a z2^b z1^c for one Composite3.
    Box search: a within +-SPAN_A of 0 (mod ord zbar), b,c within +-SPAN_B.
    Returns ALL box matches (ambiguity = letter relations inside the box)."""
    SPAN_A, SPAN_B = 4, 40
    def __init__(self, C):
        self.C = C; K3 = C.K3; self.K3 = K3
        self.ob = ord_of(K3, C.zbar)
        self.o2 = ord_of(K3, C.z2_3)
        self.o1 = ord_of(K3, C.z1_3)
        def rng(o, span):
            if o is None: return [0]
            return sorted(set(x % o for x in range(-span, span + 1)))
        self.ra = rng(self.ob, self.SPAN_A)
        self.rb = rng(self.o2, self.SPAN_B)
        self.rc = rng(self.o1, self.SPAN_B)
        self.tab = {}                       # zbar^a*z2^b -> [(a,b)]
        for a in self.ra:
            za = K3["pow"](C.zbar, a)
            for b in self.rb:
                w = K3["mul"](za, K3["pow"](C.z2_3, b))
                self.tab.setdefault(self._key(w), []).append((a, b))
        iz1 = K3["inv"](C.z1_3)
        self.invc = {c: K3["pow"](iz1, c) for c in self.rc}
        self._cache = {}
    @staticmethod
    def _key(v): return json.dumps(v, default=str)
    def matches(self, v):
        k = self._key(v)
        if k in self._cache: return self._cache[k]
        K3 = self.K3; out = []
        for c, ic in self.invc.items():
            w = K3["mul"](v, ic)
            for (a, b) in self.tab.get(self._key(w), []):
                out.append((a, b, c))
        out.sort()
        self._cache[k] = out
        return out
    def cent(self, e, o):
        if o is None: return e
        e %= o
        return e - o if e > o // 2 else e
    def name(self, v, centered=True):
        m = self.matches(v)
        if not m: return "RAW(no box match)"
        a, b, c = m[0]
        if centered:
            a, b, c = (self.cent(a, self.ob), self.cent(b, self.o2),
                       self.cent(c, self.o1))
        if not (a or b or c): return "1"
        return f"zbar^{a}*z2^{b}*z1^{c}"
    def name_nonneg(self, v):
        m = self.matches(v)
        if not m: return "RAW(no box match)"
        a, b, c = m[0]
        return f"zbar^{a}*z2^{b}*z1^{c}" if (a or b or c) else "1"
    def zbar_free(self, v):
        """True iff some box representation has a == 0 (v in <z2,z1> box)."""
        return any(a == 0 for (a, _, _) in self.matches(v))

# ---------------------------------------------------------------------------
def spotcheck_rowG(res):
    """Re-derive the sealed run's committed row-G value sets with THIS unit's
    own value-set collection + decomposition machinery; diff vs the committed
    iterlawr_probe_results.json (artifact-integrity spot check)."""
    emit("SPOT-CHECK A: sealed row-G value sets (committed JSON vs recompute)")
    committed = json.load(open(os.path.join(HERE,
        "iterlawr_probe_results.json")))["rowG_valuesets"]
    ok = True
    for kind, p in CONFIGS:
        tag = f"{kind},p={p},G"
        T3 = Tower3(kind, p, 1, (2,1,1), (2,1,1), (2,1,2), tag)
        C = Composite3(T3); M = Mono(C)
        W1 = list(range(C.Gamma0, C.Gamma0 + T3.E3))
        vals = set()
        for ga in W1:
            for gb in W1:
                v = C.cocycle(ga, gb)[0]
                if v != C.K3["one"]:
                    vals.add(M.name_nonneg(v))
        mine, theirs = sorted(vals), sorted(committed[tag])
        same = mine == theirs
        ok = ok and same
        emit(f"  {tag:12} recomputed {mine} committed {theirs} "
             f"{'MATCH' if same else 'DIFF'}")
    res["spotcheck_rowG"] = "MATCH" if ok else "DIFF"
    return ok

def spotcheck_m5(res):
    """Integer-level spot check against M5's independent harness records
    (level3_xcheck_results.json): recompute every pair's iterated splits
    (s3,s2,s1 at g, g', g+g') and d3 from espec alone; compare."""
    emit("SPOT-CHECK B: M5 cross-harness integer data (splits + d3)")
    path = os.path.join(HERE, "level3_xcheck_results.json")
    if not os.path.exists(path):
        emit("  M5 results file missing — SKIPPED"); return True
    rows = json.load(open(path))
    tot = bad = 0
    for row in rows:
        (e0,h0,g0), (e1,h1,g1), (e2,h2,g2) = [tuple(r) for r in row["espec"]]
        w1P = e0*g0*h0; gam2 = e1*w1P + h1
        w2P = e1*g1*gam2; gam3 = e2*w2P + h2
        def split3(g):
            s3, u3 = eq12(g, e2, h2); b2 = u3 - s3*w2P
            s2, u2 = eq12(b2, e1, h1); b1 = u2 - s2*w1P
            s1, u1 = eq12(b1, e0, h0)
            return s3, s2, s1
        if [gam2, gam3] != row["gammaW"][1:]:
            bad += 1; tot += 1
            emit(f"  {row['name']}: gamma constants MISMATCH"); continue
        for pr in row["pairs"]:
            tot += 1
            gs = (pr["g"], pr["gp"], pr["g"] + pr["gp"])
            sp = [split3(g) for g in gs]
            want = (list(pr["s3"]), list(pr["s2"]), list(pr["s1"]))
            got = ([s[0] for s in sp], [s[1] for s in sp],
                   [s[2] for s in sp])
            d3 = (sp[0][0] + sp[1][0]) // e2
            if [list(x) for x in got] != [list(x) for x in want] \
               or d3 != pr["d3"]:
                bad += 1
                if bad <= 5:
                    emit(f"  {row['name']} pair {gs[:2]}: MISMATCH "
                         f"got {got}/d3={d3} want {want}/d3={pr['d3']}")
    emit(f"  M5 integer spot check: {tot - bad}/{tot} pair-records agree")
    res["spotcheck_m5"] = dict(total=tot, mismatches=bad)
    return bad == 0

# ---------------------------------------------------------------------------
def run_tower(kind, p, tag, d0, r0, r1, r2, res, rnd):
    full = f"{kind},p={p},{tag}"
    T3 = Tower3(kind, p, d0, r0, r1, r2, full)
    T = T3.T
    C = Composite3(T3)
    K3, E3, e2 = C.K3, T3.E3, T3.e2
    M = Mono(C)
    C2 = SP.Composite(T)
    G0 = C.Gamma0
    W1 = list(range(G0, G0 + E3))
    st = collections.Counter()
    finds = []
    def find(leg, msg):
        finds.append((leg, msg))
        if len(finds) <= 12: emit(f"    !! {full} {leg}: {msg}")

    # ---- level-2/level-3 tower data certification (fresh rows) ----
    gv0, iv0 = len(G.VIOL), len(IP.VIOL)
    G.T1_T2(T, nf=4); G.T5(T)
    IP.cert3_internal(T3)
    st["cert_viol"] = (len(G.VIOL) - gv0) + (len(IP.VIOL) - iv0)
    if st["cert_viol"]:
        find("CERT", f"{st['cert_viol']} tower-data cert violations")

    # ---- FP0 + measured W1xW1 table ----
    tab, jt = {}, {}
    for g in W1 + [g + E3 for g in W1]:
        st["fp0_anchor"] += 1
        if C.anchor_val(g) != C.eps_chain(g):
            st["fp0_anchor_viol"] += 1; find("FP0", f"anchor!=eps-chain {g}")
    for ga in W1:
        for gb in W1:
            cval, vp, nz, gmeas = C.cocycle(ga, gb)
            j = nz[0] if len(nz) == 1 else None
            if j is None or gmeas != ga + gb:
                st["fp0_shape_viol"] += 1
                find("FP0", f"shape at ({ga},{gb}): nz={nz}")
            tab[(ga, gb)] = cval; jt[(ga, gb)] = j
            st["fp0_pairs"] += 1
            cst = C.constants(ga, gb)
            lawv = C.law_value(cst, "primary")
            if lawv is None or cval != lawv:
                st["fp0_law_viol"] += 1
                find("FP0", f"ITER-LAW-3 mismatch at ({ga},{gb})")

    # ---- FP1 value set ----
    vs = collections.Counter()
    for v in tab.values():
        vs[M.name(v)] += 1
    if any(k.startswith("RAW") for k in vs):
        st["fp1_rawvals"] = sum(n for k, n in vs.items()
                                if k.startswith("RAW"))
        find("FP1", f"{st['fp1_rawvals']} values with NO box monomial")
    amb = sum(1 for v in set(map(M._key, tab.values()))
              if len(M._cache.get(v, [])) > 1)
    res["valuesets"][full] = dict(
        set=sorted(vs), mult={k: vs[k] for k in sorted(vs)},
        distinct=len(set(map(M._key, tab.values()))),
        letter_orders=dict(zbar=M.ob, z2=M.o2, z1=M.o1),
        ambiguous_reps=amb)

    # ---- FP2 swap ----
    for ga in W1:
        for gb in W1:
            st["fp2_pairs"] += 1
            if tab[(ga, gb)] != tab[(gb, ga)] or jt[(ga, gb)] != jt[(gb, ga)]:
                st["fp2_asym"] += 1; find("FP2", f"asym at ({ga},{gb})")

    # ---- FP3 descent (representative independence, measured) ----
    def cc(a, b): return C.cocycle(a, b)[0]
    for k in (1,):
        for ga in W1:
            for gb in W1:
                st["fp3_checks"] += 3
                base = tab[(ga, gb)]
                if cc(ga + k*E3, gb) != base: st["fp3_viol"] += 1
                if cc(ga, gb + k*E3) != base: st["fp3_viol"] += 1
                if cc(ga + k*E3, gb + k*E3) != base: st["fp3_viol"] += 1
    for k in (2, 5):
        for _ in range(8):
            ga, gb = rnd.choice(W1), rnd.choice(W1)
            st["fp3_checks"] += 2
            if cc(ga + k*E3, gb) != tab[(ga, gb)]: st["fp3_viol"] += 1
            if cc(ga, gb + k*E3) != tab[(ga, gb)]: st["fp3_viol"] += 1
    if st["fp3_viol"]: find("FP3", f"{st['fp3_viol']} descent violations")

    # ---- FP4 B0a genre + carry checks + associativity ----
    FEC = {g: C.eps_chain(g) for g in
           range(min(W1), 3*max(W1) + 3)}      # eps-chain gauge F
    def dF(a, b):
        return K3["mul"](K3["mul"](FEC[a], FEC[b]), K3["inv"](FEC[a + b]))
    for ga in W1:
        for gb in W1:
            st["fp4_pairs"] += 1
            j = jt[(ga, gb)]
            s3a, s3b = C.split(ga)[0], C.split(gb)[0]
            if j != (s3a + s3b) // e2:
                st["fp4_jcarry_viol"] += 1
                find("FP4", f"j != floor carry at ({ga},{gb})")
            pred = K3["mul"](K3["pow"](C.zbar, j), dF(ga, gb))
            if tab[(ga, gb)] != pred:
                st["fp4_b0a_viol"] += 1
                find("FP4", f"c3 != zbar^j*dF at ({ga},{gb})")
    trips = [(a, b, t) for a in W1 for b in W1 for t in W1]
    if len(trips) > 120: trips = rnd.sample(trips, 120)
    for (a, b, t) in trips:
        st["fp4_triples"] += 1
        lhs = K3["mul"](cc(a, b), cc(a + b, t))
        rhs = K3["mul"](cc(b, t), cc(a, b + t))
        if lhs != rhs:
            st["fp4_assoc_viol"] += 1; find("FP4", f"assoc at {(a,b,t)}")
        j2 = lambda x, y: C.cocycle(x, y)[2][0]
        if j2(a, b) + j2(a + b, t) != j2(b, t) + j2(a, b + t):
            st["fp4_jcocycle_viol"] += 1
            find("FP4", f"j-cocycle at {(a,b,t)}")

    # ---- FP5 crossed-product restriction ----
    devcen = collections.Counter()
    disp = []
    for ga in W1:
        for gb in W1:
            s3a, s2a, s1a, b2a, b1a, _ = C.split(ga)
            s3b, s2b, s1b, b2b, b1b, _ = C.split(gb)
            d3i = (s3a + s3b) // e2
            sub = (ga % e2 == 0 and gb % e2 == 0)
            if sub != (s3a == 0 and s3b == 0):
                find("FP5", f"s3=0 <=> e2|gamma FAILS at ({ga},{gb})")
            try:
                c2v = C2.cocycle(b2a, b2b)[0]
            except AssertionError:
                c2v = None
            j = jt[(ga, gb)]
            body = K3["mul"](tab[(ga, gb)],
                             K3["inv"](K3["pow"](C.zbar, j)))
            if c2v is None:
                st["fp5_l2win"] += 1
                dev, devname = None, "L2WIN"
            else:
                shadow = K3["embed"](c2v)
                dev = K3["mul"](body, K3["inv"](shadow))
                devname = M.name(dev)
            if sub:
                st["fp5_sub_pairs"] += 1
                if c2v is None or dev != K3["one"] or j != 0:
                    st["fp5_sub_viol"] += 1
                    find("FP5", f"SUBWINDOW restriction fails at ({ga},{gb})")
            else:
                st["fp5_off_pairs"] += 1
            if dev is not None and dev != K3["one"]:
                st["fp5_dev_pairs"] += 1
                if d3i == 0:
                    st["fp5_dev_d3zero"] += 1
                    find("FP5", f"shadow deviation at d3=0 pair ({ga},{gb})")
                if not M.zbar_free(dev):
                    st["fp5_dev_zbar"] += 1
                    find("FP5", f"deviation NOT zbar-free at ({ga},{gb})")
                devcen[devname] += 1
            elif dev is not None and d3i == 1:
                st["fp5_d31_nodev"] += 1
            disp.append((ga, gb, s3a, s3b, d3i, j, M.name(tab[(ga, gb)]),
                         devname))
    res["dev_census"][full] = {k: devcen[k] for k in sorted(devcen)}

    # ---- FP6 e2-quotient fingerprint ----
    qmap = {}
    for (ga, gb), j in jt.items():
        qmap.setdefault((ga % e2, gb % e2), set()).add(j)
    st["fp6_classes"] = len(qmap)
    st["fp6_multival"] = sum(1 for v in qmap.values() if len(v) > 1)
    if st["fp6_multival"]:
        find("FP6", "top-slot j does NOT factor through residues mod e2")
    qtab = {f"{k[0]},{k[1]}": sorted(v)[0] if len(v) == 1 else list(v)
            for k, v in sorted(qmap.items())}
    res["quotient_tables"][full] = qtab

    # ---- FP7 denominators (field battery side) ----
    for ga in W1:
        for gb in W1:
            s3a, s2a, s1a = C.split(ga)[:3]
            s3b, s2b, s1b = C.split(gb)[:3]
            s3c, s2c, s1c = C.split(ga + gb)[:3]
            d3i = (s3a + s3b) // e2
            d2f = (s2a + s2b) // T.e1
            n2 = s2a + s2b - s2c
            n1 = s1a + s1b - s1c
            st["fp7_pairs"] += 1
            if n2 % T.e1: st["fp7_mid_corr_needed"] += 1
            if (n2 + T.l1*T3.gamma3*d3i) % T.e1:
                st["fp7_mid_warrant_viol"] += 1
            D2 = (n2 + T.l1*T3.gamma3*d3i) // T.e1
            Sig = D2*T.gamma2 + d3i*T3.gamma3*(T.l1p - T.l1*T.w1Phi1)
            if (n1 + T.l0*Sig) % T.e0:
                st["fp7_inner_warrant_viol"] += 1
            if (n1 + T.l0*T.gamma2*d2f) % T.e0:
                st["fp7_naive_nonint"] += 1
                if d3i == 0: st["fp7_naive_nonint_d30"] += 1
    if st["fp7_mid_warrant_viol"] or st["fp7_inner_warrant_viol"]:
        find("FP7", "single-level denominator warrant VIOLATED")

    # ---- per-tower summary ----
    emit(f"  {full:14} E3={E3} G0={G0} ords(zb,z2,z1)="
         f"({M.ob},{M.o2},{M.o1}) vset={len(res['valuesets'][full]['set'])}"
         f" law {st['fp0_pairs']-st['fp0_law_viol']}/{st['fp0_pairs']}"
         f" swap0={st['fp2_asym']==0} desc0={st['fp3_viol']==0}"
         f" b0a0={st['fp4_b0a_viol']==0}"
         f" sub {st['fp5_sub_pairs']-st['fp5_sub_viol']}/{st['fp5_sub_pairs']}"
         f" dev@d3=0:{st['fp5_dev_d3zero']} l2win={st['fp5_l2win']}")
    res["towers"][full] = dict(st)
    res["findings"] += [(full,) + f for f in finds]
    return T3, C, M, disp

# ---------------------------------------------------------------------------
def eyeball_table(full, T3, C, M, disp):
    T = T3.T
    emit()
    emit(f"EYEBALL TABLE {full}  (d0={T.d0}; e,h,g: L0=({T.e0},{T.h0},{T.g0})"
         f" L1=({T.e1},{T.h1},{T.g1}) L2=({T3.e2},{T3.h2},{T3.g2}))"
         f"  gamma2={T.gamma2} gamma3={T3.gamma3} l0={T.l0} l1={T.l1}"
         f" ords(zb,z2,z1)=({M.ob},{M.o2},{M.o1})")
    emit(f"  {'ga':>5} {'gb':>5} {'s3,s3~':>7} {'d3':>2} {'j':>2}  "
         f"{'measured c3':24} {'shadow-dev':16}")
    for (ga, gb, s3a, s3b, d3i, j, cname, devname) in disp:
        emit(f"  {ga:>5} {gb:>5} {s3a:>3},{s3b:<3} {d3i:>2} {j:>2}  "
             f"{cname:24} {devname:16}")

# ---------------------------------------------------------------------------
def symbolic_denominators(n, res):
    """20k random-parameter integer draws: which denominators do the exponent
    tracks need?  (No field; splits only.)"""
    rnd = random.Random(SEED + 1)
    st = collections.Counter()
    naive_mod = collections.Counter()
    for _ in range(n):
        e0 = rnd.randrange(1, 13)
        h0 = rnd.choice([h for h in range(1, 40) if math.gcd(h, e0) == 1])
        e1 = rnd.randrange(1, 13)
        h1 = rnd.choice([h for h in range(1, 40) if math.gcd(h, e1) == 1])
        e2 = rnd.randrange(1, 13)
        h2 = rnd.choice([h for h in range(1, 40) if math.gcd(h, e2) == 1])
        g0 = rnd.randrange(1, 5); g1 = rnd.randrange(1, 5)
        l0, l0p = bezout(e0, h0); l1, l1p = bezout(e1, h1)
        w1P = e0*g0*h0; gam2 = e1*w1P + h1
        w2P = e1*g1*gam2; gam3 = e2*w2P + h2
        ga, gb = rnd.randrange(-3000, 3001), rnd.randrange(-3000, 3001)
        def split3(g):
            s3, u3 = eq12(g, e2, h2); b2 = u3 - s3*w2P
            s2, u2 = eq12(b2, e1, h1); b1 = u2 - s2*w1P
            s1, u1 = eq12(b1, e0, h0)
            return s3, s2, s1
        s3a, s2a, s1a = split3(ga); s3b, s2b, s1b = split3(gb)
        s3c, s2c, s1c = split3(ga + gb)
        d3 = (s3a + s3b)//e2; d2 = (s2a + s2b)//e1
        n2 = s2a + s2b - s2c; n1 = s1a + s1b - s1c
        st["draws"] += 1; st[f"d3={d3}"] += 1
        if n2 % e1: st["mid_corr_needed"] += 1
        mid_num = n2 + l1*gam3*d3
        if mid_num % e1: st["mid_warrant_viol"] += 1; continue
        D2 = mid_num//e1
        Sig = D2*gam2 + d3*gam3*(l1p - l1*w1P)
        if (n1 + l0*Sig) % e0: st["inner_warrant_viol"] += 1
        nnum = n1 + l0*gam2*d2
        if nnum % e0:
            st["naive_nonint"] += 1
            if d3 == 0: st["naive_nonint_d30"] += 1
            if e0 > 1: naive_mod[nnum % e0] += 1
        # would a coarser denominator e0*e1 ever be NEEDED in the middle?
        if n2 % e1 and (n2*e0) % (e0*e1) == 0:
            st["mid_e0e1_phantom"] += 1
    res["symbolic"] = dict(st)
    res["symbolic_naive_mod_e0"] = {str(k): naive_mod[k]
                                    for k in sorted(naive_mod)}
    emit(f"SYMBOLIC {n} draws: mid warrant e1 viol={st['mid_warrant_viol']}"
         f" inner warrant e0 viol={st['inner_warrant_viol']}"
         f" | mid corr needed (e1 nmid n2)={st['mid_corr_needed']}"
         f" | naive nonintegral={st['naive_nonint']}"
         f" (of which at d3=0: {st['naive_nonint_d30']})")

# ---------------------------------------------------------------------------
def main():
    t0 = time.time()
    rnd = random.Random(SEED)
    res = dict(valuesets={}, dev_census={}, quotient_tables={}, towers={},
               findings=[], roster=[list(r) for r in ROWS], seed=SEED)
    emit("l3finger_m4.py — POST-SEAL DIAGNOSTIC (non-prereg); "
         "seal 911431c READ-ONLY; seed %d" % SEED)
    emit("=" * 78)
    okA = spotcheck_rowG(res)
    okB = spotcheck_m5(res)
    emit("=" * 78)
    emit("FRESH ROSTER BATTERY (44 towers)")
    displays = []
    for kind, p in CONFIGS:
        for tag, d0, r0, r1, r2 in ROWS:
            try:
                T3, C, M, disp = run_tower(kind, p, tag, d0, r0, r1, r2,
                                           res, rnd)
                if (kind, p, tag) in DISPLAY:
                    displays.append((f"{kind},p={p},{tag}", T3, C, M, disp))
            except Exception as exc:
                res["findings"].append((f"{kind},p={p},{tag}", "HARNESS",
                                        repr(exc)))
                emit(f"  !! HARNESS EVENT {kind},p={p},{tag}: {exc!r}")
    emit("=" * 78)
    symbolic_denominators(20000, res)
    for args in displays:
        eyeball_table(*args)
    # ---- aggregate verdict lines ----
    emit(); emit("=" * 78)
    agg = collections.Counter()
    for stats in res["towers"].values():
        for k, v in stats.items(): agg[k] += v
    res["aggregate"] = dict(agg)
    def line(label, viol, n):
        emit(f"  {label:58} {viol:5d} viol / {n:6d}")
    emit("AGGREGATE (44 fresh towers):")
    line("FP0 anchor=eps-chain", agg["fp0_anchor_viol"], agg["fp0_anchor"])
    line("FP0 top-slot shape", agg["fp0_shape_viol"], agg["fp0_pairs"])
    line("FP0 ITER-LAW-3 closed form (decorrelated confirm)",
         agg["fp0_law_viol"], agg["fp0_pairs"])
    line("FP2 swap symmetry", agg["fp2_asym"], agg["fp2_pairs"])
    line("FP3 Z/E3 descent (single-arg + simult + k=2,5)",
         agg["fp3_viol"], agg["fp3_checks"])
    line("FP4 B0a genre c3 == zbar^j * d(eps-chain)",
         agg["fp4_b0a_viol"], agg["fp4_pairs"])
    line("FP4 j == floor((s3+s3')/e2)", agg["fp4_jcarry_viol"],
         agg["fp4_pairs"])
    line("FP4 measured associativity (triples)", agg["fp4_assoc_viol"],
         agg["fp4_triples"])
    line("FP4 j 2-cocycle identity (triples)", agg["fp4_jcocycle_viol"],
         agg["fp4_triples"])
    line("FP5 SUBWINDOW restriction == measured level-2",
         agg["fp5_sub_viol"], agg["fp5_sub_pairs"])
    line("FP5 shadow deviation at d3=0 (want 0)", agg["fp5_dev_d3zero"],
         agg["fp5_sub_pairs"] + agg["fp5_off_pairs"] - agg["fp5_l2win"])
    line("FP5 deviation with zbar component (want 0)", agg["fp5_dev_zbar"],
         agg["fp5_dev_pairs"])
    line("FP6 j fails to factor through mod-e2 residues",
         agg["fp6_multival"], agg["fp6_classes"])
    line("FP7 middle e1-warrant", agg["fp7_mid_warrant_viol"],
         agg["fp7_pairs"])
    line("FP7 inner e0-warrant (composed)", agg["fp7_inner_warrant_viol"],
         agg["fp7_pairs"])
    emit(f"  FP5 deviating pairs (all should be d3=1): "
         f"{agg['fp5_dev_pairs']}; d3=1 pairs with NO deviation: "
         f"{agg['fp5_d31_nodev']}; L2-window misses: {agg['fp5_l2win']}")
    emit(f"  FP7 naive-template nonintegral: {agg['fp7_naive_nonint']} "
         f"(at d3=0: {agg['fp7_naive_nonint_d30']}); middle correction "
         f"load-bearing (e1 nmid n2): {agg['fp7_mid_corr_needed']}")
    nfind = len(res["findings"])
    ok = (okA and okB and nfind == 0)
    emit(f"FINDINGS: {nfind}")
    for f in res["findings"][:30]: emit(f"  {f}")
    emit(f"ELAPSED {time.time()-t0:.1f}s")
    emit(f"M4 FINGERPRINT VERDICT: "
         f"{'ALL CLEAN' if ok else 'SEE FINDINGS ABOVE'}")
    with open(os.path.join(HERE, "l3finger_m4_results.json"), "w") as fh:
        json.dump(res, fh, indent=1, default=str)
    with open(os.path.join(HERE, "l3finger_m4_output.txt"), "w") as fh:
        fh.write("\n".join(OUT) + "\n")
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
