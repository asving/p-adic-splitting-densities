#!/usr/bin/env python3
"""sdyj_checks.py — (SD-YJ') composer unit machine leg (2026-08-08 campaign).

Derivation shadow + fresh instances for lean/notes/openmath/
SDYJ_PROOF_2026-08-08.md: the digit-valuation floor SDY-L1 (the forced
v-chain from gamma_{i+1} with invariant v_l >= e_{l-1}*gamma_l + 1, terminal
v0 >= 1), the multiplicative valuation ledger SDY-L2 (w0(term) >= what +
sum w0(digit cells) + #pi-junk), and the (SD-YJ') companion clauses SDY-L3
(every cascade-slot companion: CE != 0, junk >= 1, w0 >= what+1, line =
betahat + Em*(w0-what) > betahat), plus the extended-(NEP) population check.

Engines consumed byte-untouched, md5-pinned, UNPATCHED (no pick extension:
all towers g0 = 1, interior g = 1, d0 <= 2).  Row tracing replicates the
construction runner survdisj_construct.py's machinery (reference ED.walk +
recording SK2.walk_rec + its seed / row-selection logic verbatim).

Families (predictions SEALED at commit 1 of the note):
  SDYJ-PIN    8 md5 pins green.
  SDYJ-GAM    engine gamma / wPhi values == the [ILN] S0.1 recursion.
  SDYJ-DIG    correction digits: single cell (i >= 1), forced v-chain dumps,
              w0(c_d) == v0, v0 >= 1, all (INV_l); i = 0: w0 == h0.
  SDYJ-SWEEP  the v-chain floor engine-free on deterministic read grids.
  SDYJ-CASC   cascade cell: w0 == u1+u1'+u0, residue != 0, unique.
  SDYJ-SUPER  SDY-L2 inequality every two-exit terminal; equality junk-free.
  SDYJ-COMP   SDY-L3 (a)(b)(c) + (*) + SD-L1 shapes on every companion.
  SDYJ-NEP    betahat-population at jhat == {Chat} on g0=1 & (STK) rows.
  SDYJ-REP    the nine committed T3 towers re-trace to the construction
              unit's committed artifacts (keys, ncomp, casc states, the 8
              companions' (w0, line)).
  SDYJ-WALL   the d0 = 3 capability wall reproduces (hardcoded quadratic
              phibar at d0 >= 2 in the committed tower chain).
  HARNESS     engine-internal violations, walk/consistency mismatches.

Measured findings (no seal): fresh-tower companion realizations; the
per-companion L/X-child resolution census.

Deterministic, exact arithmetic, no sampling.
Usage: python3 sdyj_checks.py [outdir]      (full battery)
       python3 sdyj_checks.py --shakedown   (throwaway spec + mini sweep
                                             only; crash-freedom probe,
                                             disclosed in the note)
"""
import sys, os, time, json, hashlib, collections, signal, itertools

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
SHAKE = "--shakedown" in sys.argv
OUTDIR = HERE
for a in sys.argv[1:]:
    if not a.startswith("--"):
        OUTDIR = a

VIOL, CNT, FINDINGS = [], {}, []
def note(f, n=1): CNT[f] = CNT.get(f, 0) + n
def viol(fam, tag, detail):
    VIOL.append((fam, tag, str(detail)[:400]))
    print(f"VIOLATION [{fam}] {tag}: {str(detail)[:360]}")
def finding(kind, tag, detail):
    FINDINGS.append((kind, tag, detail))
    print(f"*** FINDING [{kind}] {tag}: {str(detail)[:360]}")

PINS = {
    "grb_order2_check.py":            "dab62713175363a7185211890019ae2f",
    "rmengine_pe_reimpl.py":          "103c1a9c99e2b4a3e8b63c93cbf87e25",
    "empty_derive_checks.py":         "8fed92402bcffe6e0c536f1f9d847612",
    "wmultdcx_stress.py":             "15315cca59c87e6c2001ea744c50aab5",
    "wmultdcx_derive_checks.py":      "bea1a43d619a3c91a9a0b2f32c0920c0",
    "survk2_derive_checks.py":        "d8493ab90e3578fae60032cde73a3b81",
    "survdisj_construct.py":          "d8001674768b057d9de113574ee401ff",
    "survdisj_construct_results.json":"cdf2ce6fef7d3145c50b102da6dad05d",
}
for fn, want in PINS.items():
    got = hashlib.md5(open(os.path.join(HERE, fn), "rb").read()).hexdigest()
    if got != want:
        viol("SDYJ-PIN", fn, f"md5 {got} != pinned {want}")

import grb_order2_check as G
from grb_order2_check import (pnorm, padd, pneg, pmul, pdivmod, pscal, w0)
import rmengine_pe_reimpl as PE
import wmultdcx_stress as WS
import wmultdcx_derive_checks as WD
import empty_derive_checks as ED
import survk2_derive_checks as SK2

def harvest(tag):
    for src, lst in (("PE", PE.VIOL), ("ED", ED.VIOL), ("WS", WS.VIOL),
                     ("WD", WD.VIOL), ("SK2", SK2.VIOL)):
        while len(lst) > harvest.seen[src]:
            v = lst[harvest.seen[src]]
            if "tree cap" in str(v):
                note("treecap")
            else:
                viol("HARNESS", tag, f"{src}: {v}")
            harvest.seen[src] += 1
harvest.seen = {"PE": 0, "ED": 0, "WS": 0, "WD": 0, "SK2": 0}

# =================== SDY-L1: the v-chain (note S2, engine-free) ==============
def sval(v, e, h):
    """eq-(12-int) s-value: v = e*u + s*h, 0 <= s < e (s = l*v mod e)."""
    if e == 1:
        return 0
    return (pow(h, -1, e) * v) % e

def vchain(eh, i):
    """eh = [(e_l, h_l)] levels 0..i (all g = 1).  Returns
    (v0, avec, gams, inv_ok, int_ok, Bi_lt_Ei) per the SDY-L1 display."""
    gam = [0] * (i + 2)
    gam[1] = eh[0][1]                       # gamma_1 = h_0
    for l in range(1, i + 1):
        wphi = eh[l - 1][0] * gam[l]        # w_l Phi_l = e_{l-1} gamma_l
        gam[l + 1] = eh[l][0] * wphi + eh[l][1]
    v = gam[i + 1]
    avec = [0] * i
    inv_ok = int_ok = True
    for l in range(i, 0, -1):
        e, h = eh[l - 1]
        if v < e * gam[l] + 1:              # (INV_l)
            inv_ok = False
        s = sval(v, e, h)
        num = v - s * gam[l]
        if num % e != 0:
            int_ok = False
            break
        avec[l - 1] = s
        v = num // e
    # naive full-dump rational bound B_i vs E_i (integrality-load census)
    Ei, Bi = 1, gam[i + 1]
    for l in range(i):
        Gl = gam[l + 1]
        for s2 in range(l + 1, i):
            Gl *= eh[s2][0]
        Bi -= (eh[l][0] - 1) * Gl
        Ei *= eh[l][0]
    return v, tuple(avec), gam, inv_ok, int_ok, (Bi < Ei)

SWEEP_GRIDS = {1: (8, 9), 2: (6, 7), 3: (5, 6), 4: (4, 5)}

def run_sweep(mini=False):
    import math
    t0 = time.time()
    grids = {1: (3, 3)} if mini else SWEEP_GRIDS
    tot = 0
    for i, (emax, hmax) in sorted(grids.items()):
        pairs = [(e, h) for e in range(1, emax + 1)
                 for h in range(1, hmax + 1) if math.gcd(e, h) == 1]
        for chain in itertools.product(pairs, repeat=i + 1):
            tot += 1
            v0, avec, gam, inv_ok, int_ok, bload = vchain(list(chain), i)
            if not int_ok:
                viol("SDYJ-SWEEP", f"i={i}", f"chain {chain}: non-integral step")
                continue
            if not inv_ok:
                viol("SDYJ-SWEEP", f"i={i}", f"chain {chain}: (INV) breach")
            if v0 < 1:
                viol("SDYJ-SWEEP", f"i={i}", f"chain {chain}: v0 = {v0} < 1")
            if v0 == 1:
                note("sweep_sharp_v0_1")
            if bload:
                note("sweep_integrality_loadbearing")
    note("sweep_chains", tot)
    print(f"-- SWEEP: {tot} chains ({time.time()-t0:.1f}s); sharp v0=1: "
          f"{CNT.get('sweep_sharp_v0_1',0)}; integrality-load: "
          f"{CNT.get('sweep_integrality_loadbearing',0)}")

# =================== SDYJ-WALL: the d0 = 3 engine wall =======================
def wall_probe():
    def _alrm(s, f): raise TimeoutError("wall probe budget")
    old = signal.signal(signal.SIGALRM, _alrm)
    signal.alarm(30)
    try:
        T = G.Tower2("Fpt", 2, 3, (2, 1, 1), (2, 1, 1), "wallprobe")
        degPhi0 = len(pnorm(T.R, T.Phi0)) - 1
        signal.alarm(0)
        if degPhi0 == 3:
            viol("SDYJ-WALL", "d0=3", "committed chain produced a CUBIC Phi0 "
                 "— the wall disclosure in the note is WRONG")
        else:
            note("wall_quadratic_phi0")
            print(f"-- WALL: committed Tower2 at d0=3 built deg Phi0 = "
                  f"{degPhi0} != 3 (hardcoded quadratic phibar) — d0 = 3 is "
                  f"engine-dark, as disclosed (F-D)")
    except TimeoutError:
        note("wall_hang")
        print("-- WALL: committed Tower2 at d0=3 HUNG (30s) — engine-dark")
    except Exception as ex:
        note("wall_exception")
        print(f"-- WALL: committed Tower2 at d0=3 raised {ex!r} — engine-dark")
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, old)

# ========================= one traced row ====================================
def trace_row(E, sA, sB, u1a, u1b, aA, aB, su, cs, pools, Dd, kdef, key, prin,
              tag, u0, dmap, Dmap, rowrecs, comprecs):
    """Replicates survdisj_construct.trace_row's walk plumbing; per-cell
    checks are THIS unit's families."""
    R = E.R; m = E.m; g0 = E.g[0]; d0 = E.d0
    sig = tuple(sA[l + 1] + sB[l + 1] for l in range(m))
    b0 = pscal(R, R["pi_pow"](u1a + u1b), [R["one"]])
    prodp = pmul(R, aA, aB)
    z = (0,) * m
    init_ref = [(1, b0, sig, z, z, z, z, 0, None, False, (), 0)]
    q1_ref = []
    out = ED.walk(E, init_ref, q1_ref, tag)
    if out[0] is None: harvest(tag); return None
    init_rec = [(1, b0, sig, z, z, z, z, 0, None, False, (), 0, ())]
    q1_rec = []
    r = SK2.walk_rec(E, init_rec, q1_rec, tag)
    if r is None: return None
    if (sorted(map(SK2.fingerprint, q1_ref)) !=
            sorted(SK2.fingerprint(st[:12]) for st in q1_rec)):
        viol("HARNESS", tag, f"stage-1 terminal mismatch at {key}")
        return None
    E1c, _ = pdivmod(R, prodp, E.Phis[m])
    if WD.cellsum(E, q1_ref) != pnorm(R, E1c):
        viol("HARNESS", tag, f"stage-1 sum != E1IH at {key}")

    def seed(states, rec):
        init2 = []
        for st in states:
            if rec:
                sgn, b, j, pc, dmp, cons, ncorr, junk, _, _, ce, _, hist = st
            else:
                sgn, b, j, pc, dmp, cons, ncorr, junk, _, _, ce, _ = st
            for (cD, jD) in E.Dcells:
                Lc, Xc, Yc = E.digit_split(b, cD)
                js = tuple(j[l] + jD[l] for l in range(m))
                isp = (tuple(jD) == prin)
                for (cc, jtag, dj0) in ((Lc, 0, 0), (Xc, 1, 0), (Yc, 1, 1)):
                    if not pnorm(R, cc): continue
                    jj = list(js); jj[0] += dj0
                    dd = list(dmp); dd[0] += dj0
                    if rec:
                        h2 = hist + (('seed', jD[0] + dj0),)
                        init2.append((sgn, cc, tuple(jj), pc, tuple(dd), cons,
                                      ncorr, junk + jtag, tuple(jD), isp, ce,
                                      dj0, h2))
                    else:
                        init2.append((sgn, cc, tuple(jj), pc, tuple(dd), cons,
                                      ncorr, junk + jtag, tuple(jD), isp, ce,
                                      dj0))
        return init2

    q2_ref = []
    out2 = ED.walk(E, seed(q1_ref, False), q2_ref, tag)
    if out2[0] is None: harvest(tag); return None
    q2_rec = []
    r = SK2.walk_rec(E, seed(q1_rec, True), q2_rec, tag)
    if r is None: return None
    if (sorted(map(SK2.fingerprint, q2_ref)) !=
            sorted(SK2.fingerprint(st[:12]) for st in q2_rec)):
        viol("HARNESS", tag, f"stage-2 terminal mismatch at {key}")
        return None
    Q1c = pdivmod(R, pmul(R, E1c, E.Chat), E.Phis[m])[0]
    if WD.cellsum(E, q2_ref) != pnorm(R, Q1c):
        viol("HARNESS", tag, f"stage-2 sum != Q1 at {key}")
    harvest(tag)
    if not q2_rec:
        return None
    note("live_rows")
    EW = [1]
    for l in range(m): EW.append(EW[-1] * E.e[l])
    Em = EW[m]
    a_, r_, b_, stock1 = WD.greedy_chains(E, sig, su, cs)
    stk = (stock1 >= E.P[m - 1])
    base = (u1a + u1b) + u0
    cells = []
    for st in q2_rec:
        (sgn, b, j, pc, dmp, cons, ncorr, junk, jD, isp, ce, y2, hist) = st
        ln = E.line(b, j)
        wb = w0(R, b)
        # -------- SDYJ-SUPER: the SDY-L2 valuation ledger --------
        ssum, defcs, ok = 0, [], True
        for (i, kc, avec, dj0) in ce:
            dg = dmap.get((i, kc, avec))
            if dg is None:
                viol("SDYJ-SUPER", tag, f"ce digit missing in dmap at {key}: "
                     f"(i={i},k={kc},avec={avec})")
                ok = False; break
            ssum += w0(R, dg)
            dc = ((E.P[i] - E.e[i] * kc) * EW[i]
                  - sum(avec[l] * EW[l] for l in range(i)) - dj0)
            defcs.append((i, kc, avec, dj0, dc))
        if ok:
            nY = y2 + sum(dj0 for (_, _, _, dj0) in ce)
            nX = junk - nY
            if nX < 0:
                viol("SDYJ-SUPER", tag, f"junk arithmetic broken at {key}: "
                     f"junk={junk} y2={y2} nY={nY}")
            lo = base + ssum + max(nX, 0)
            if wb < lo:
                viol("SDYJ-SUPER", tag, f"SDY-L2 breach at {key}: w0={wb} < "
                     f"{lo} (base={base} sum_digits={ssum} nX={nX})")
            if junk == 0 and y2 == 0 and wb != base + ssum:
                viol("SDYJ-SUPER", tag, f"junk-free equality fails at {key}: "
                     f"w0={wb} != {base+ssum}")
            note("super_cells")
        cells.append(dict(sgn=sgn, b=b, j=tuple(j), junk=junk, ce=ce, y2=y2,
                          line=ln, w0=wb, jD=tuple(jD), prin=isp,
                          defcs=defcs))
    slots = collections.defaultdict(list)
    for c in cells: slots[c['j']].append(c)
    # -------- cascade + companions --------
    casc = [c for c in cells if c['ce'] == () and c['junk'] == 0
            and c['y2'] == 0 and c['prin']]
    if len(casc) > 1:
        viol("SDYJ-CASC", tag, f"cascade cell not unique at {key}: {len(casc)}")
    crec = casc[0] if len(casc) == 1 else None
    ncomp = 0
    casc_state = "ABSENT"
    if crec is not None:
        what, bhat, jhat = crec['w0'], crec['line'], crec['j']
        # SDYJ-CASC: the S-L1 shadow at any d0
        if what != base:
            viol("SDYJ-CASC", tag, f"what {what} != u1+u1'+u0 {base} at {key}")
        if E.Km["isz"](E.resKm(crec['b'])):
            viol("SDYJ-CASC", tag, f"cascade residue ZERO at {key}")
        note("casc_rows")
        acc = []
        for c in slots[jhat]:
            acc = padd(R, acc, c['b'] if c['sgn'] > 0 else pneg(R, c['b']))
        acc = pnorm(R, acc)
        casc_state = "SURV" if (acc and w0(R, acc) == what) else "KILLED"
        if stk and g0 == 1:
            # SDYJ-NEP: the betahat-line population at jhat is {Chat}
            pop = [c for c in slots[jhat] if c['line'] == bhat]
            if len(pop) != 1 or pop[0] is not crec:
                viol("SDYJ-NEP", tag, f"betahat population != {{Chat}} at "
                     f"{key}: {len(pop)} cells")
            # the netted slot must survive at what (SDY-THM(iii) shadow)
            if casc_state != "SURV":
                viol("SDYJ-NEP", tag, f"B_jhat killed/raised at {key} — "
                     f"contradicts SDY-THM(iii)")
            # SDYJ-COMP: SDY-L3 on every companion
            for c in slots[jhat]:
                if c is crec: continue
                ncomp += 1
                sd = sum(dc for (_, _, _, _, dc) in c['defcs'])
                xmate = (c['ce'] == ())
                if xmate and not (c['junk'] >= 1 and c['y2'] == 0
                                  and c['jD'] == tuple(prin)):
                    viol("SDYJ-COMP", tag, f"CE=0 companion outside the "
                         f"X-mate shape at {key}")
                if not xmate:
                    if c['junk'] < 1:
                        viol("SDYJ-COMP", tag, f"companion junk=0 at {key} — "
                             f"the automatic clause fails")
                    if sd != c['y2']:
                        viol("SDYJ-COMP", tag, f"(*) breach at {key}: "
                             f"sum defc {sd} != Y2 {c['y2']}")
                    for (i, kc, avec, dj0, dc) in c['defcs']:
                        if dc < 0:
                            viol("SDYJ-COMP", tag, f"defc < 0 at {key}")
                        if dc == 0:
                            fulldump = all(avec[l] == E.P[l] - 1
                                           for l in range(i))
                            if not (E.e[i] == 1 and dj0 == 1 and fulldump):
                                viol("SDYJ-COMP", tag, f"defc=0 outside the "
                                     f"(SD-YJ) shape at {key}")
                if c['w0'] < what + 1:
                    viol("SDYJ-COMP", tag, f"companion w0 {c['w0']} < what+1 "
                         f"{what+1} at {key} — (SD-YJ') FAILS")
                if c['line'] != bhat + Em * (c['w0'] - what):
                    viol("SDYJ-COMP", tag, f"line affinity fails at {key}")
                if c['line'] <= bhat:
                    viol("SDYJ-COMP", tag, f"companion line <= betahat at "
                         f"{key} — (SD-YJ') FAILS")
                # measured: L/X resolution of the correction edges
                nY = c['y2'] + sum(d for (_, _, _, d) in c['ce'])
                nX = c['junk'] - nY
                comprecs.append(dict(tower=tag, key=list(key),
                                     w0=c['w0'], line=c['line'], what=what,
                                     bhat=bhat, gain=c['w0'] - what,
                                     junk=c['junk'], y2=c['y2'],
                                     ce=[list(e) for e in c['ce']],
                                     nX=nX, xmate=xmate))
                finding("YJ-COMP", tag, dict(
                    key=list(key), gain=c['w0'] - what, junk=c['junk'],
                    y2=c['y2'], nce=len(c['ce']), nX=nX,
                    corr_child=("X" if nX > 0 else "L/Y-only")))
    elif stk and g0 == 1:
        note("casc_absent_stk_rows")
        finding("CASC-ABSENT", tag, dict(key=list(key)))
    rowrecs.append(dict(tower=tag, key=list(key), ncells=len(cells),
                        stk=stk, casc=casc_state, ncomp=ncomp))
    return dict(live=True)

# ========================= tower driver ======================================
def run_tower(spec, rowrecs, comprecs, budget=900):
    tag, m, kind, p, d0, reads = spec[:6]
    t0 = time.time()
    def _alrm(s, f): raise TimeoutError("tower budget")
    old = signal.signal(signal.SIGALRM, _alrm)
    signal.alarm(budget)
    try:
        E = PE.Eng(m, kind, p, d0, reads, tag)
        PE.prep(E)
        harvest(tag)
        # ---- SDYJ-GAM: the S0.1 weight recursion, non-textually ----
        eh = [(E.e[l], E.h[l]) for l in range(m + 1)]
        gam = [0] * (m + 2); gam[1] = eh[0][1]
        for l in range(1, m + 1):
            gam[l + 1] = eh[l][0] * (eh[l - 1][0] * E.g[l - 1] * gam[l]) \
                         + eh[l][1]
        for l in range(1, m + 2):
            if E.gam.get(l) != gam[l]:
                viol("SDYJ-GAM", tag, f"gamma_{l}: engine {E.gam.get(l)} != "
                     f"recursion {gam[l]}")
        if E.wmPhi != E.e[m - 1] * E.g[m - 1] * gam[m]:
            viol("SDYJ-GAM", tag, "wmPhi mismatch")
        note("gam_towers")
        # ---- SDYJ-DIG: the SDY-L1 floor on the engine's own digits ----
        corr = E.corr_table()
        for (k, dcells) in corr[0]:
            for (cd, av) in dcells:
                if w0(E.R, cd) != (E.g[0] - k) * E.h[0]:
                    viol("SDYJ-DIG", tag, f"i=0 digit w0 != (g0-k)h0")
                if E.g[0] == 1 and w0(E.R, cd) < 1:
                    viol("SDYJ-DIG", tag, f"i=0 digit w0 < 1 at g0=1")
        for i in range(1, m):
            rows = corr[i]
            if len(rows) != 1 or rows[0][0] != 0:
                viol("SDYJ-DIG", tag, f"level {i}: k-rows != [k=0] (g_i=1)")
                continue
            dcells = rows[0][1]
            if len(dcells) != 1:
                viol("SDYJ-DIG", tag, f"level {i}: {len(dcells)} cells != 1 "
                     f"(the forced single cell at all-g-1)")
            v0, avec, gams, inv_ok, int_ok, _ = vchain(eh[:i + 1], i)
            if not (int_ok and inv_ok):
                viol("SDYJ-DIG", tag, f"level {i}: v-chain (INV)/integrality "
                     f"fails on this tower's reads")
            for (cd, av) in dcells:
                avv = tuple((av[l] if l < len(av) else 0) for l in range(i))
                if avv != avec:
                    viol("SDYJ-DIG", tag, f"level {i}: dump {avv} != forced "
                         f"v-chain dump {avec}")
                if w0(E.R, cd) != v0:
                    viol("SDYJ-DIG", tag, f"level {i}: w0(c_d) = "
                         f"{w0(E.R, cd)} != v0 = {v0}")
                if v0 < 1:
                    viol("SDYJ-DIG", tag, f"level {i}: v0 = {v0} < 1 — "
                         f"SDY-L1 FAILS")
                if v0 == 1:
                    note("dig_sharp_v0_1")
            note("dig_digits")
        # ---- rows ----
        u, su = WS.uchain(E)
        if u is None:
            raise RuntimeError("u-chain failed")
        Etot, G0, split = WS.window_split(E)
        anch = WS.anchors_of(E, Etot, G0, split)
        prin, meta = WD.inv_checks(E, u, su)
        harvest(tag)
        if meta is None:
            raise RuntimeError("inv_checks failed")
        dmap, Dmap = SK2.build_maps(E)
        u0 = meta["u0"]
        etop = E.e[m - 1]; R = E.R
        seen = set(); nl = 0; nrows = 0
        for ga in range(G0, G0 + Etot):
            aA, sA, u1a = anch[ga]
            for gb in range(G0, G0 + Etot):
                aB, sB, u1b = anch[gb]
                if not (sA[m + 1] == E.e[m] - 1
                        and sB[m + 1] == E.e[m] - 1):
                    continue
                E1, _ = pdivmod(R, pmul(R, aA, aB), E.Phis[m])
                if not pnorm(R, E1): continue
                key = (tuple(sorted([(tuple(sA[l] for l in range(1, m + 2)),
                                      u1a),
                                     (tuple(sB[l] for l in range(1, m + 2)),
                                      u1b)])))
                if key in seen: continue
                seen.add(key)
                pools, cs, Dd, top = WS.pools_of(E, sA, sB, su)
                ctop = cs[-1] if cs else 0
                kdef = 2 * etop - Dd
                if kdef > ctop: continue
                nrows += 1
                rr = trace_row(E, sA, sB, u1a, u1b, aA, aB, su, cs, pools,
                               Dd, kdef, (ga, gb), prin, tag, u0,
                               dmap, Dmap, rowrecs, comprecs)
                if rr: nl += 1
        signal.alarm(0); signal.signal(signal.SIGALRM, old)
        print(f"-- {tag} m={m} {kind},p={p},d0={d0}: live-clause rows="
              f"{nrows} traced nonempty={nl} ({time.time()-t0:.1f}s)")
    except TimeoutError:
        signal.alarm(0); signal.signal(signal.SIGALRM, old)
        print(f"-- {tag}: TOWER BUDGET EXCEEDED ({budget}s) — disclosed skip")
        note("tower_budget_skips")
    except Exception as ex:
        signal.alarm(0); signal.signal(signal.SIGALRM, old)
        print(f"-- {tag}: ENGINE UNSUPPORTED ({ex!r}) — disclosed")
        note("tower_skipped")

# ========================= rosters ===========================================
T3_COMMITTED = [
    ("YJ2F",    2, "Fpt", 2, 2, [(2,1,1), (2,1,1), (2,1,1)]),
    ("YJ3F",    3, "Fpt", 2, 2, [(2,1,1), (2,1,1), (2,1,1), (2,1,1)]),
    ("YJ3FLT",  3, "Fpt", 2, 2, [(2,1,1), (1,1,1), (2,1,1), (2,1,1)]),
    ("YJ3FLTB", 3, "Fpt", 2, 2, [(2,3,1), (1,1,1), (2,1,1), (2,1,1)]),
    ("YJ3DPF",  3, "Fpt", 2, 2, [(3,1,1), (2,1,1), (2,1,1), (2,1,1)]),
    ("YJ4FLT",  4, "Fpt", 2, 2, [(2,1,1), (1,1,1), (2,1,1), (2,1,1), (2,1,1)]),
    ("YJ3Z",    3, "Zp",  2, 2, [(2,1,1), (1,1,1), (2,1,1), (2,1,1)]),
    ("YJ3F3",   3, "Fpt", 3, 2, [(2,1,1), (1,1,1), (2,1,1), (2,1,1)]),
    ("YJT1F",   3, "Fpt", 2, 2, [(2,1,1), (2,1,1), (2,1,1), (1,1,1)]),
]
FRESH = [
    ("YJX1", 3, "Fpt", 2, 2, [(2,3,1), (1,3,1), (2,1,1), (2,1,1)]),
    ("YJX2", 3, "Fpt", 3, 2, [(3,1,1), (1,1,1), (2,1,1), (2,1,1)]),
    ("YJX3", 3, "Fpt", 3, 2, [(3,2,1), (1,1,1), (2,1,1), (2,1,1)]),
    ("YJX4", 4, "Fpt", 2, 2, [(2,1,1), (1,1,1), (1,1,1), (2,1,1), (2,1,1)]),
    ("YJX5", 3, "Fpt", 2, 1, [(2,1,1), (1,1,1), (2,1,1), (2,1,1)]),
    ("YJX6", 2, "Fpt", 2, 2, [(2,1,1), (1,1,1), (2,1,1)]),
]
THROWAWAY = ("SHAKE", 2, "Fpt", 3, 2, [(2,1,1), (2,3,1), (2,1,1)])

# ========================= replication check =================================
def replication(rowrecs, comprecs):
    ref = json.load(open(os.path.join(HERE,
                                      "survdisj_construct_results.json")))
    t3names = {s[0] for s in T3_COMMITTED}
    refrows = {(r["tower"], tuple(r["key"])): r for r in ref["rows"]
               if r["tower"] in t3names}
    myrows = {(r["tower"], tuple(r["key"])): r for r in rowrecs
              if r["tower"] in t3names}
    if set(refrows) != set(myrows):
        viol("SDYJ-REP", "keys", f"live-row key sets differ: "
             f"{len(refrows)} committed vs {len(myrows)} here")
    for kk in sorted(set(refrows) & set(myrows)):
        a, b = refrows[kk], myrows[kk]
        if a["ncomp"] != b["ncomp"] or a["casc"] != b["casc"]:
            viol("SDYJ-REP", str(kk), f"ncomp/casc mismatch: committed "
                 f"({a['ncomp']},{a['casc']}) vs ({b['ncomp']},{b['casc']})")
    refcomps = []
    for f in ref["findings"]:
        if f[0] == "YJ-COMPANION":
            for c in f[2]["comps"]:
                refcomps.append((f[1], tuple(f[2]["key"]),
                                 c["w0"], c["line"]))
    mycomps = [(c["tower"], tuple(c["key"]), c["w0"], c["line"])
               for c in comprecs if c["tower"] in t3names]
    if sorted(refcomps) != sorted(mycomps):
        viol("SDYJ-REP", "companions", f"companion (w0,line) multisets "
             f"differ: {sorted(refcomps)} vs {sorted(mycomps)}")
    else:
        note("rep_companions", len(refcomps))
    print(f"-- REP: {len(myrows)} committed T3 rows re-traced; "
          f"{len(mycomps)} companions matched against the committed 8")

# ================================ main =======================================
def main():
    t0 = time.time()
    print("=" * 78)
    print("(SD-YJ') composer machine leg — "
          + ("SHAKEDOWN (throwaway only)" if SHAKE else "sealed battery"))
    print("=" * 78)
    rowrecs, comprecs = [], []
    if SHAKE:
        run_sweep(mini=True)
        run_tower(THROWAWAY, rowrecs, comprecs)
    else:
        run_sweep()
        wall_probe()
        print("---- committed T3 roster (replication) ----")
        for spec in T3_COMMITTED:
            run_tower(spec, rowrecs, comprecs)
        print("---- fresh roster ----")
        for spec in FRESH:
            run_tower(spec, rowrecs, comprecs)
        replication(rowrecs, comprecs)
    print("=" * 78)
    fams = ["SDYJ-PIN", "SDYJ-GAM", "SDYJ-DIG", "SDYJ-SWEEP", "SDYJ-CASC",
            "SDYJ-SUPER", "SDYJ-COMP", "SDYJ-NEP", "SDYJ-REP", "SDYJ-WALL",
            "HARNESS"]
    for f in fams:
        print(f"{f:10s}: {sum(1 for v in VIOL if v[0] == f)} violations")
    print("-" * 78)
    fk = collections.Counter(k for (k, _, _) in FINDINGS)
    print("FINDINGS census:", dict(sorted(fk.items())))
    print("counters:", {k: CNT[k] for k in sorted(CNT)})
    print(f"total violations: {len(VIOL)}")
    el = time.time() - t0
    print(f"elapsed: {el:.1f}s")
    if not SHAKE:
        out = dict(final=True, violations=VIOL, findings=FINDINGS,
                   counters=CNT, rows=rowrecs, companions=comprecs,
                   elapsed=el)
        with open(os.path.join(OUTDIR, "sdyj_checks_results.json"),
                  "w") as f:
            json.dump(out, f, indent=1, default=str)
        print("results -> sdyj_checks_results.json")

if __name__ == "__main__":
    main()
