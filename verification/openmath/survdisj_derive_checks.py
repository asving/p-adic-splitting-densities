#!/usr/bin/env python3
"""survdisj_derive_checks.py — machine leg of SURVDISJ_PROOF_2026-08-08.md
(the (SURV-DISJ) COMPOSER unit, 2026-08-08 campaign).

This is a DERIVATION SHADOW, not a re-run of the committed instrument: every
family below checks a displayed step of the proof note cellwise / groupwise
on the instrument's exact union roster (selection logic replicated from the
committed survdisj_instrument.py, md5-pinned; engines consumed byte-untouched).

Verdict families (predicted 0 violations):
  DRV-PIN    md5 pins: the five engines + the two SURV runners + the
             committed instrument (whose roster/selection this runner
             replicates).
  DRV-MASS   the E-weighted mass ledger (SD-L2's parent display), cellwise,
             all g0:  with E_l := e_0...e_{l-1},
             sum_l j_l E_l  ==  sum_l sigma_{l+1} E_l + sum_l jD_l E_l + y2
                 - 2 P_{m-1} E_{m-1}
                 - sum_{l=1..m-1} pi_l (P_{l-1} E_{l-1} - E_l)
                 - sum_{corr (i,k,a,dj0)} [ (P_i - e_i k) E_i
                                            - sum_{l<i} a_l E_l - dj0 ].
  DRV-DEF    per correction edge: dump exponents reduced (a_l <= P_l - 1,
             the S2.2 inventory display); k = 0 whenever g_i = 1; and on
             g0 = 1 towers the SD-L1 deficit bound
             defc := (P_i - e_i k) E_i - sum a_l E_l - dj0 >= E_{i+1} - E_i,
             with defc >= E_{i+1} - E_i + 1 when dj0 = 0.
  DRV-Y0     SD-L3 (= L-NORM(c)): on d0 = 1 towers NO path carries any
             Phi0Y-junk edge (y2 = 0 and every correction dj0 = 0), any g0.
  DRV-SEEDY  SD-L4(i) (= E-L6): the stage-2 seeding of the MONOMIAL b0 with
             any d-cell has ZERO Y-child (any d0).  The X-child is MEASURED
             (allowed by the proof; absorbed by S-L4(ii)): counter seedx.
  DRV-NEPS   SD-THM-A shadow at g0 = 1, d0 = 1, (STK): the cascade slot's
             cell population is the cascade alone, or the cascade plus
             X-mates of strictly higher w0 with junk > 0 and no corrections
             (the only companion shape the proof permits; the committed
             instrument observed the stronger "none at all", P-A 693/693).
  DRV-RIG    SD-L5: correction-free junk-free two-exit terminals: at most
             ONE per d-cell seed, pairwise DISTINCT slots (any g0).
  DRV-CRIT   SD-L6: every same-slot equal-line group (n >= 2): single w0;
             killed-by-netting  <=>  w0(subsum) > w0 or subsum = 0; and the
             line/w0 affinity line(acc) - ln == E_m (w0(acc) - w0_group).
  DRV-M1     SD-L7: every group whose residue-class signed-count vector is
             PROTECTED (a single +-1 class, or exactly two nonzero classes
             with counts +1 and -1) nets NONZERO at its line, char-free.
  HARNESS    engine violation harvest.

Controls (teeth; disclosed if silent): CTRL-Y (some Phi0Y-edge exists on a
d0 >= 2 tower), CTRL-XSEED (some junk-carrying cell exists — X-junk real),
CTRL-DEFNEG (at g0 >= 2 some correction with defc <= 0 — the recycle
economy), CTRL-M1 (some UNPROTECTED group exists), CTRL-RIGSEEDS (some row
with >= 2 correction-free junk-free terminals — distinct-slot claim has
teeth), CTRL-KILL (killed groups exist).

Deterministic, exact arithmetic.  Usage: python3 survdisj_derive_checks.py
[outdir]
"""
import sys, os, time, json, hashlib, collections

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
OUTDIR = sys.argv[1] if len(sys.argv) > 1 else HERE

import wmultdcx_stress as WS
import wmultdcx_derive_checks as WD
import rmengine_pe_reimpl as PE
import empty_derive_checks as ED
from grb_order2_check import pnorm, padd, pneg, pmul, pscal, pdivmod, w0

VIOL, CNT = [], {}
MUT = collections.Counter()
def note(f, n=1): CNT[f] = CNT.get(f, 0) + n
def viol(fam, tag, detail):
    VIOL.append((fam, tag, detail)); print(f"VIOLATION [{fam}] {tag}: {detail}")

def harvest(tag):
    for src, lst in (("PE", PE.VIOL), ("ED", ED.VIOL), ("WS", WS.VIOL),
                     ("WD", WD.VIOL)):
        while len(lst) > harvest.seen[src]:
            viol("HARNESS", tag, f"{src}: {lst[harvest.seen[src]]}")
            harvest.seen[src] += 1
harvest.seen = {"PE": 0, "ED": 0, "WS": 0, "WD": 0}

PINS = {
    "wmultdcx_stress.py":        "15315cca59c87e6c2001ea744c50aab5",
    "wmultdcx_derive_checks.py": "bea1a43d619a3c91a9a0b2f32c0920c0",
    "rmengine_pe_reimpl.py":     "103c1a9c99e2b4a3e8b63c93cbf87e25",
    "grb_order2_check.py":       "dab62713175363a7185211890019ae2f",
    "empty_derive_checks.py":    "8fed92402bcffe6e0c536f1f9d847612",
    "surv_derive_checks.py":     "2365289e1f925404e66c8ce2b3e827ed",
    "surv_pe1_ext.py":           "937317c75fb381eec96b59b8a1f743ad",
    "survdisj_instrument.py":    "3df33c7406913510ed7ebaa60d480b57",
}

DEFC_MIN = {}                 # (g0class, e_i, dj0) -> min deficit observed
GROUPS = collections.Counter()  # census rows for the note

def classify_group(E, grp, p):
    classes = []
    for c in grp:
        for cl in classes:
            if E.keq(cl[0], c["res"]):
                if c["sgn"] > 0: cl[1] += 1
                else: cl[2] += 1
                break
        else:
            classes.append([c["res"], int(c["sgn"] > 0), int(c["sgn"] < 0)])
    signed = [cl[1] - cl[2] for cl in classes]
    return classes, signed

def protected(signed):
    nz = [s for s in signed if s != 0]
    if len(nz) == 1 and abs(nz[0]) == 1: return True
    if len(nz) == 2 and sorted(nz) == [-1, 1]: return True
    return False

def trace_row(E, sA, sB, u1a, u1b, aA, aB, su, cs, Dd, kdef, key, prin,
              tag, p, kind, g0, d0, phase):
    R = E.R; m = E.m
    sig = tuple(sA[l + 1] + sB[l + 1] for l in range(m))
    b0 = pscal(R, R["pi_pow"](u1a + u1b), [R["one"]])
    prodp = pmul(R, aA, aB)
    if pnorm(R, padd(R, prodp, pneg(R, E.cellpoly(b0, sig)))):
        viol("HARNESS", tag, f"a*a' != formal cell at {key}"); return None
    z = (0,) * m
    init = [(1, b0, sig, z, z, z, z, 0, None, False, (), 0)]
    q1sink = []
    out = ED.walk(E, init, q1sink, tag)
    if out[0] is None: harvest(tag); return None
    E1c, _ = pdivmod(R, prodp, E.Phis[m])
    if WD.cellsum(E, q1sink) != pnorm(R, E1c):
        viol("HARNESS", tag, f"stage-1 sum != E1IH at {key}")
    # DRV-SEEDY: the b0-seeding split for every d-cell (SD-L4(i) = E-L6),
    # plus the measured X census
    for (cD, jD) in E.Dcells:
        Lc, Xc, Yc = ED.split_checked(E, b0, cD, tag, f"seedchk@{key}")
        if pnorm(R, Yc):
            viol("DRV-SEEDY", tag, f"b0-seeding Y-child NONZERO at {key} "
                 f"jD={list(jD)} (SD-L4(i)/E-L6 breach)")
        if pnorm(R, Xc): note("seedx_nonzero")
        else: note("seedx_zero")
    init2 = []
    for st in q1sink:
        sgn, b, j, pc, dmp, cons, ncorr, junk, _, _, ce, _ = st
        for (cD, jD) in E.Dcells:
            Lc, Xc, Yc = ED.split_checked(E, b, cD, tag, f"seed@{key}")
            js = tuple(j[l] + jD[l] for l in range(m))
            isp = (tuple(jD) == prin)
            for (cc, jtag, dj0) in ((Lc, 0, 0), (Xc, 1, 0), (Yc, 1, 1)):
                if not pnorm(R, cc): continue
                jj = list(js); jj[0] += dj0
                dd = list(dmp); dd[0] += dj0
                init2.append((sgn, cc, tuple(jj), pc, tuple(dd), cons,
                              ncorr, junk + jtag, tuple(jD), isp, ce, dj0))
    q2sink = []
    out2 = ED.walk(E, init2, q2sink, tag)
    if out2[0] is None: harvest(tag); return None
    Q1c = pdivmod(R, pmul(R, E1c, E.Chat), E.Phis[m])[0]
    if WD.cellsum(E, q2sink) != pnorm(R, Q1c):
        viol("HARNESS", tag, f"stage-2 sum != Q1 at {key}")
    harvest(tag)
    ctop = cs[-1] if cs else 0
    if kdef > ctop or not q2sink:
        return None
    EW = [1]
    for l in range(m): EW.append(EW[-1] * E.e[l])
    Em = EW[m]
    a_, r_, b_, stock1 = WD.greedy_chains(E, sig, su, cs)
    stk = (stock1 >= E.P[m - 1])
    g0cls = "g1" if g0 == 1 else "g2+"
    cells = []
    for st in q2sink:
        sgn, b, j, pc, dmp, cons, ncorr, junk, jD, isp, ce, y2 = st
        # ---- DRV-MASS: the E-weighted ledger, all g0 ----
        lhs = sum(j[l] * EW[l] for l in range(m))
        rhs = (sum(sig[l] * EW[l] for l in range(m))
               + sum(jD[l] * EW[l] for l in range(m)) + y2
               - 2 * E.P[m - 1] * EW[m - 1]
               - sum(pc[l - 1] * (E.P[l - 1] * EW[l - 1] - EW[l])
                     for l in range(1, m)))
        for (i, kc, avec, dj0) in ce:
            rhs -= ((E.P[i] - E.e[i] * kc) * EW[i]
                    - sum(avec[l] * EW[l] for l in range(i)) - dj0)
        if lhs != rhs:
            viol("DRV-MASS", tag, f"mass ledger fails at {key}: j={j} "
                 f"lhs={lhs} rhs={rhs}")
        else:
            note("mass_ok")
        # ---- DRV-DEF: per-correction inventory + SD-L1 deficit ----
        for (i, kc, avec, dj0) in ce:
            if any(avec[l] > E.P[l] - 1 for l in range(i)):
                viol("DRV-DEF", tag, f"dump not reduced at {key}: i={i} "
                     f"avec={list(avec)}")
            if E.g[i] == 1 and kc != 0:
                viol("DRV-DEF", tag, f"k != 0 at g_i = 1 level at {key}")
            defc = ((E.P[i] - E.e[i] * kc) * EW[i]
                    - sum(avec[l] * EW[l] for l in range(i)) - dj0)
            kk = (g0cls, E.e[i], dj0)
            if kk not in DEFC_MIN or defc < DEFC_MIN[kk]: DEFC_MIN[kk] = defc
            if g0 == 1:
                lo = EW[i + 1] - EW[i] + (1 if dj0 == 0 else 0)
                if defc < lo:
                    viol("DRV-DEF", tag, f"SD-L1 deficit breach at {key}: "
                         f"i={i} defc={defc} < {lo}")
                else:
                    note("defc_ok_g1")
            elif defc <= 0:
                MUT["CTRL-DEFNEG"] += 1
        # ---- DRV-Y0: SD-L3 = L-NORM(c) at d0 = 1 ----
        if d0 == 1:
            if y2 != 0 or any(dj0 != 0 for (_, _, _, dj0) in ce):
                viol("DRV-Y0", tag, f"Phi0Y-edge on a d0=1 tower at {key}")
            else:
                note("y0_ok")
        elif y2 != 0 or any(dj0 != 0 for (_, _, _, dj0) in ce):
            MUT["CTRL-Y"] += 1
        if junk > 0: MUT["CTRL-XSEED"] += 1
        cells.append(dict(sgn=sgn, b=b, j=j, jD=jD, ce=ce, junk=junk,
                          prin=isp, y2=y2, line=E.line(b, j), w0=w0(R, b),
                          res=E.resKm(b)))
    # ---- cascade record ----
    casc = [c for c in cells if c["ce"] == () and c["junk"] == 0
            and c["prin"] and c["y2"] == 0]
    casc_rec = casc[0] if len(casc) == 1 else None
    # ---- DRV-NEPS: SD-THM-A shadow ----
    if g0 == 1 and d0 == 1 and stk and casc_rec is not None:
        mates = [c for c in cells if c["j"] == casc_rec["j"]
                 and c is not casc_rec]
        bad = [c for c in mates if not (c["junk"] > 0 and c["ce"] == ()
                                        and c["w0"] > casc_rec["w0"])]
        if bad:
            viol("DRV-NEPS", tag, f"cascade-slot companion outside the "
                 f"proof's X-mate shape at {key}: "
                 f"{[(c['junk'], len(c['ce']), c['w0']) for c in bad]}")
        else:
            note("neps_ok")
            if mates: note("neps_xmates", len(mates))
    # ---- DRV-RIG: SD-L5 ----
    cfjf = [c for c in cells if c["ce"] == () and c["junk"] == 0
            and c["y2"] == 0]
    byseed = collections.defaultdict(list)
    for c in cfjf: byseed[c["jD"]].append(c)
    for jd, lst in byseed.items():
        if len(lst) > 1:
            viol("DRV-RIG", tag, f">1 correction-free junk-free terminal "
                 f"per seed at {key}: jD={list(jd)} n={len(lst)}")
    seen_slots = {}
    for jd, lst in byseed.items():
        jv = lst[0]["j"]
        if jv in seen_slots:
            viol("DRV-RIG", tag, f"two seeds share a slot at {key}: "
                 f"{list(jd)} vs {list(seen_slots[jv])}")
        seen_slots[jv] = jd
    if len(byseed) >= 2: MUT["CTRL-RIGSEEDS"] += 1
    note("rig_rows")
    # ---- groups: DRV-CRIT + DRV-M1 ----
    slots = collections.defaultdict(list)
    for c in cells: slots[c["j"]].append(c)
    beta_min = min(c["line"] for c in cells)
    for jv, grp in slots.items():
        lines = collections.defaultdict(list)
        for c in grp: lines[c["line"]].append(c)
        for ln, sub in lines.items():
            if len(sub) < 2: continue
            w0s = set(c["w0"] for c in sub)
            if len(w0s) != 1:
                viol("DRV-CRIT", tag, f"same slot+line, >1 w0 at {key}")
                continue
            w0g = w0s.pop()
            acc = []
            for c in sub:
                acc = padd(R, acc, c["b"] if c["sgn"] > 0 else pneg(R, c["b"]))
            acc = pnorm(R, acc)
            killed_poly = (not acc) or E.line(acc, jv) != ln
            killed_w0 = (not acc) or w0(R, acc) > w0g
            if killed_poly != killed_w0:
                viol("DRV-CRIT", tag, f"line-kill != w0-kill at {key}")
            if acc and (E.line(acc, jv) - ln) != Em * (w0(R, acc) - w0g):
                viol("DRV-CRIT", tag, f"line/w0 affinity fails at {key}")
            if not killed_poly: note("crit_ok")
            classes, signed = classify_group(E, sub, p)
            GROUPS[(g0cls, "bot" if ln == beta_min else "off",
                    "kill" if killed_poly else "surv")] += 1
            if killed_poly: MUT["CTRL-KILL"] += 1
            if protected(signed):
                note("m1_protected")
                if killed_poly:
                    viol("DRV-M1", tag, f"PROTECTED group killed at {key}: "
                         f"slot={list(jv)} line={ln} signed={signed} "
                         f"(SD-L7 breach)")
            else:
                MUT["CTRL-M1"] += 1
    note("live_rows")
    return dict(live=True)

def setup(spec):
    tag, m, kind, p, d0, reads = spec
    try:
        E = PE.Eng(m, kind, p, d0, reads, tag)
        PE.prep(E)
    except Exception as ex:
        print(f"-- {tag}: ENGINE UNSUPPORTED ({ex!r}) — disclosed, skipped")
        note("tower_skipped"); return None
    harvest(tag)
    u, su = WS.uchain(E)
    if u is None:
        print(f"-- {tag}: u-chain failed — disclosed, skipped")
        note("tower_skipped"); return None
    Etot, G0, split = WS.window_split(E)
    anch = WS.anchors_of(E, Etot, G0, split)
    prin, _ = WD.inv_checks(E, u, su)
    harvest(tag)
    return E, su, Etot, G0, anch, prin

def run_sealed_tower(spec):
    tag, m, kind, p, d0, reads = spec
    t0 = time.time()
    st = setup(spec)
    if st is None: return
    E, su, Etot, G0, anch, prin = st
    etop = E.e[m - 1]; R = E.R
    pid_keys = {}
    for ga in range(G0, G0 + Etot):
        aA, sA, u1a = anch[ga]
        for gb in range(G0, G0 + Etot):
            aB, sB, u1b = anch[gb]
            strack = (sA[m + 1] == E.e[m] - 1 and sB[m + 1] == E.e[m] - 1)
            if not strack: continue
            E1, _ = pdivmod(R, pmul(R, aA, aB), E.Phis[m])
            e1nz = bool(pnorm(R, E1))
            track = strack and e1nz
            if not (track and m >= 2): continue
            pools, cs, Dd, top = WS.pools_of(E, sA, sB, su)
            meas = False
            Q1 = pdivmod(R, pmul(R, E1, E.Chat), E.Phis[m])[0]
            if pnorm(R, Q1):
                Tsum = sA[m + 1] + sB[m + 1]
                dpl = Tsum // E.e[m]
                locus = ((dpl == 1 and strack and E.e[m] >= 2)
                         or (Tsum == E.e[m] - 1 and E.e[m] == 1))
                if locus: meas = True
            key = (tuple(sorted([(tuple(sA[l] for l in range(1, m + 2)), u1a),
                                 (tuple(sB[l] for l in range(1, m + 2)), u1b)])))
            if key not in pid_keys:
                kdef = 2 * etop - Dd
                want = (meas or top in (2 * etop - 1, 2 * etop, 2 * etop - 2)
                        or (len(cs) >= 2 and cs[0] > 0 and cs[1] > 0)
                        or (cs and max(cs) >= 2))
                if want:
                    pid_keys[key] = (ga, gb, cs, Dd, kdef, meas,
                                     sA, sB, u1a, u1b)
    cap = 14 if m >= 4 else 40
    chosen = sorted(pid_keys.items(), key=lambda kv: (
        not kv[1][5], -(kv[1][2][0] if kv[1][2] else 0), kv[0]))[:cap]
    nl = 0
    for key, (ga, gb, cs, Dd, kdef, meas, sA, sB, u1a, u1b) in chosen:
        r = trace_row(E, sA, sB, u1a, u1b, anch[ga][0], anch[gb][0], su,
                      cs, Dd, kdef, (ga, gb), prin, tag, p, kind, E.g[0],
                      d0, "sealed")
        if r: nl += 1
    print(f"-- SEALED {tag} m={m} {kind},p={p},d0={d0} g0={E.g[0]}: "
          f"live traced={nl} ({time.time()-t0:.1f}s)")

def run_fresh_tower(spec, cap3, cap4, phase):
    tag, m, kind, p, d0, reads = spec
    t0 = time.time()
    st = setup(spec)
    if st is None: return
    E, su, Etot, G0, anch, prin = st
    etop = E.e[m - 1]; R = E.R
    seen, live_pool = set(), {}
    for ga in range(G0, G0 + Etot):
        aA, sA, u1a = anch[ga]
        for gb in range(G0, G0 + Etot):
            aB, sB, u1b = anch[gb]
            if not (sA[m + 1] == E.e[m] - 1 and sB[m + 1] == E.e[m] - 1):
                continue
            E1, _ = pdivmod(R, pmul(R, aA, aB), E.Phis[m])
            if not pnorm(R, E1): continue
            key = (tuple(sorted([(tuple(sA[l] for l in range(1, m + 2)), u1a),
                                 (tuple(sB[l] for l in range(1, m + 2)), u1b)])))
            if key in seen: continue
            seen.add(key)
            pools, cs, Dd, top = WS.pools_of(E, sA, sB, su)
            ctop = cs[-1] if cs else 0
            kdef = 2 * etop - Dd
            if kdef > ctop: continue
            live_pool.setdefault((kdef, ctop), []).append(
                (ga, gb, cs, Dd, kdef, sA, sB, u1a, u1b))
    cap = cap4 if m >= 4 else cap3
    nl = 0
    for stratum in sorted(live_pool):
        for row in live_pool[stratum][:cap]:
            ga, gb, cs, Dd, kdef, sA, sB, u1a, u1b = row
            r = trace_row(E, sA, sB, u1a, u1b, anch[ga][0], anch[gb][0], su,
                          cs, Dd, kdef, (ga, gb), prin, tag, p, kind,
                          E.g[0], d0, phase)
            if r: nl += 1
    print(f"-- {phase.upper()} {tag} m={m} {kind},p={p},d0={d0} g0={E.g[0]}: "
          f"live traced={nl} ({time.time()-t0:.1f}s)")

PX_ROSTER = [
    ("PXDEEPF3", 3, "Fpt", 3, 1, [(3,2,1), (2,1,1), (2,1,1), (2,1,1)]),
    ("PXT3F3",   3, "Fpt", 3, 1, [(3,1,1), (2,1,1), (3,2,1), (2,1,1)]),
    ("PXDEEPZ2", 3, "Zp", 2, 1, [(3,2,1), (2,1,1), (2,1,1), (2,1,1)]),
    ("PXT3Z2",   3, "Zp", 2, 1, [(3,1,1), (2,1,1), (3,2,1), (2,1,1)]),
    ("PXDEEP4F", 3, "Fpt", 2, 1, [(4,3,1), (2,1,1), (2,3,1), (2,1,1)]),
    ("PXTRK1F",  3, "Fpt", 2, 1, [(3,2,1), (2,1,1), (2,1,1), (1,1,1)]),
    ("PXFLTF",   3, "Fpt", 2, 1, [(3,1,1), (1,1,1), (2,1,1), (2,1,1)]),
    ("PXW4DPF",  4, "Fpt", 2, 1, [(3,1,1), (2,1,1), (2,1,1), (2,1,1), (2,1,1)]),
]
SD_ROSTER = [
    ("SDG2BF",  3, "Fpt", 2, 1, [(3,1,2), (2,1,1), (3,2,1), (2,1,1)]),
    ("SDG2BZ",  3, "Zp",  2, 1, [(3,1,2), (2,1,1), (3,2,1), (2,1,1)]),
    ("SDG2AF",  3, "Fpt", 2, 2, [(2,1,2), (3,2,1), (3,1,1), (2,1,1)]),
    ("SDG2AZ",  3, "Zp",  2, 2, [(2,1,2), (3,2,1), (3,1,1), (2,1,1)]),
    ("SDW3G2F", 3, "Fpt", 2, 1, [(3,1,2), (2,1,1), (2,3,1), (2,1,1)]),
    ("SDDPG2F", 3, "Fpt", 2, 1, [(3,2,2), (2,1,1), (2,1,1), (2,1,1)]),
    ("SDDPG2Z", 3, "Zp",  2, 1, [(3,2,2), (2,1,1), (2,1,1), (2,1,1)]),
    ("SDW4G2F", 4, "Fpt", 2, 1, [(3,1,2), (2,1,1), (2,1,1), (2,1,1), (2,1,1)]),
]

def save(elapsed, final=False):
    out = dict(final=final, violations=VIOL, counters=CNT,
               mutations=dict(MUT),
               defc_min={f"{k[0]}|e={k[1]}|Y={k[2]}": v
                         for k, v in sorted(DEFC_MIN.items())},
               groups={f"{k[0]}|{k[1]}|{k[2]}": n
                       for k, n in sorted(GROUPS.items())},
               elapsed=elapsed)
    with open(os.path.join(OUTDIR, "survdisj_derive_checks_results.json"),
              "w") as f:
        json.dump(out, f, indent=1, default=str)

def main():
    t0 = time.time()
    for fn, want in PINS.items():
        got = hashlib.md5(open(os.path.join(HERE, fn), "rb").read()).hexdigest()
        if got != want:
            viol("DRV-PIN", fn, f"md5 {got} != pinned {want}")
    print("=" * 78)
    print("PHASE SEALED — WS.ROSTER via the committed sealed selection")
    print("=" * 78)
    for spec in WS.ROSTER:
        run_sealed_tower(spec); save(time.time() - t0)
    print("=" * 78)
    print("PHASE EQ — ED.FRESH_ROSTER, caps 12/6")
    print("=" * 78)
    for spec in ED.FRESH_ROSTER:
        run_fresh_tower(spec, 12, 6, "eq"); save(time.time() - t0)
    print("=" * 78)
    print("PHASE PX — the PE1 PX roster, caps 12/6")
    print("=" * 78)
    for spec in PX_ROSTER:
        run_fresh_tower(spec, 12, 6, "px"); save(time.time() - t0)
    print("=" * 78)
    print("PHASE SD — the instrument's g0>=2 x residue-char-2 roster, 12/6")
    print("=" * 78)
    for spec in SD_ROSTER:
        run_fresh_tower(spec, 12, 6, "sd"); save(time.time() - t0)
    print("=" * 78)
    fams = ["DRV-PIN", "DRV-MASS", "DRV-DEF", "DRV-Y0", "DRV-SEEDY",
            "DRV-NEPS", "DRV-RIG", "DRV-CRIT", "DRV-M1", "HARNESS"]
    for f in fams:
        print(f"{f:10s}: {sum(1 for v in VIOL if v[0] == f)} violations")
    print("-" * 78)
    print("counters:", {k: CNT[k] for k in sorted(CNT)})
    print("min correction deficits (g0class | e_i | Y-flag):")
    for k, v in sorted(DEFC_MIN.items()):
        print(f"    {k[0]}|e={k[1]}|Y={k[2]}: {v}")
    print("group census (g0class, bottom?, verdict):",
          {f"{k[0]}|{k[1]}|{k[2]}": n for k, n in sorted(GROUPS.items())})
    print("MUTATION CONTROLS (teeth):", dict(MUT))
    for mc in ("CTRL-Y", "CTRL-XSEED", "CTRL-DEFNEG", "CTRL-M1",
               "CTRL-RIGSEEDS", "CTRL-KILL"):
        if MUT.get(mc, 0) == 0:
            print(f"  CONTROL SILENT: {mc} never fired — the matching "
                  f"family's evidence is TOOTHLESS on this roster")
    print(f"total violations: {len(VIOL)}")
    el = time.time() - t0
    print(f"elapsed: {el:.1f}s")
    save(el, final=True)
    print("results ->",
          os.path.join(OUTDIR, "survdisj_derive_checks_results.json"))

if __name__ == "__main__":
    main()
