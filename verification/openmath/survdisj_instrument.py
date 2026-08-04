#!/usr/bin/env python3
"""survdisj_instrument.py — (SURV-DISJ) INSTRUMENT unit (2026-08-08 campaign).

Target: the boxed conjecture (SURV-DISJ) of SURV_PROOF_2026-08-08.md S7 —
on live rows (TRACK, (H1)-(H3), c_{m-1} >= k) the netted BOTTOM stratum
survives OR the CASCADE slot survives at the cascade line.  The record so
far: 486 committed + 545 fresh rows, six unique kill rows, 0 counterexamples.
The composer's question this unit instruments: WHAT IDENTITY protects the
surviving slot in each kill regime?
  (K1) residue-char-2 mod-p multiplicity pair-kills at g0 = 1 (bottom dies,
       cascade survives);
  (K2) characteristic-blind opposite-sign equal-residue pair-kills at
       g0 = 2 (a bottom-line slot dies, the bottom survives elsewhere;
       plus the 52 committed cascade-slot kills).

Consumes the committed engines byte-untouched (md5-pinned): rmengine_pe_reimpl
(Eng), wmultdcx_stress (roster/anchors/pools), wmultdcx_derive_checks
(q_quanta/greedy_chains/inv_checks/cellsum), empty_derive_checks (walk +
FRESH_ROSTER + split_checked), grb_order2_check (poly kit).  Also pins the
two SURV runners whose selection logic is replicated here (surv_derive_checks:
the sealed selection loop; surv_pe1_ext: the PX roster + raised caps).

UNION ROSTER (all live rows):
  phase SEALED  WS.ROSTER via the committed sealed selection loop (copied
                verbatim from surv_derive_checks.run_sealed_tower), live rows
                traced — the committed battery's live component;
  phase EQ      ED.FRESH_ROSTER at PE1's RAISED caps (12 at m=3, 6 at m=4)
                — superset of the committed fresh 6/3 selection;
  phase PX      the PE1 PX roster verbatim (char-3 twins, Zp p=2 twins,
                p=2 Fpt twins), caps 12/6;
  phase SD      NEW ADVERSARIAL roster: g0 >= 2 towers at RESIDUE
                CHARACTERISTIC 2 (both kill regimes reachable on the SAME
                rows — no committed battery ever probed this cross), caps
                12/6.  Engine-unsupported shapes disclosed-skipped.

PER-ROW INSTRUMENTATION (the residue decomposition layer):
  For every same-slot equal-line group: the group subsum at its line; killed
  iff subsum == 0 or its line rises.  For every KILLED group AND for the
  row's SURVIVOR slot(s) (the netted slots attaining w_m(Q^1)): per-cell
  (sign, w0, normalized K-residue, corrections, junk, path type) plus the
  K0-RESIDUE-PRODUCT FACTORIZATION of every junk-free coefficient
  (res(b) == res(b0) * prod over correction edges of res(c_d) * res(c_D
  seed), w0 additive, sign = (-1)^{#corrections} — the L-NORM(a) chain,
  checked cellwise as SDI-RESFACT) and the residue-class multiplicity
  structure mod p (classes by keq, signed counts).
  Kill-genre classification per killed group:
    SIGN-PAIR   every residue class has signed count 0 (char-blind);
    MODP        some class has signed count != 0 but == 0 mod p (needs
                residue char p);
    CROSS       neither (cancellation ACROSS distinct residue classes —
                a genre the S7 box does not carry; loud flag).

CANDIDATE PROTECTION IDENTITIES (law-keyed counts, keyed by
(g0=1 / g0>=2 | residue char 2 / odd | thresh / above / direct)):
  P-A  [combinatorial, g0=1]: the cascade slot is a SINGLE cell (no
       same-slot companion of ANY valuation) on every g0=1 live row.
       Mutations: M-A1 the same predicate must FAIL on some g0>=2 row
       (partnered cascades exist); M-A2 "every bottom-line slot at g0=1
       is a singleton" must FAIL somewhere (collisions exist).
  P-B  [g0>=2 bottom structure]: measured per g0>=2 row over bottom-line
       slot groups: some group singleton (pb_single_some); some group odd
       (pb_odd_some); every SURVIVING netted bottom slot has odd group
       count (pb_odd_all_surv); some group with a residue class of
       |signed count| == 1 (pb_mult1_some).  Sub-keyed to rows where a
       bottom-line group was KILLED.  Mutations: M-B1 killed groups with
       ODD cell count (0 => parity separates kills from survivals; > 0 =>
       parity is NOT the protection — refutation pattern); M-B2 some
       g0>=2 row must carry an EVEN bottom-line group (else no partnered
       bottom was ever censused — coverage failure).
  P-C  [valuation separation]: on rows with >= 1 killed group: every
       killed group's line > beta_min (kills never reach the bottom).
       Expected REFUTED (the record has bottom-line kills in BOTH
       regimes); the law-keyed failure pattern IS the datum.
  P-D  [survivor sum-free]: every minimal surviving netted slot is a
       SINGLE cell at its minimal line with netline == that line (residue
       = a single L-NORM(a) product, never a sum).  pd_all / pd_some over
       all rows; pd_kill over rows with >= 1 killed group (the
       load-bearing case).  Mutation M-D1: some row must have a minimal
       survivor with >= 2 cells at its line netting NONZERO (else the
       predicate is structurally vacuous); every such row is recorded
       with its net-residue identity (what saved it).

VERDICT families (predicted 0): SDI-PIN, SDI-CONS, SDI-DIGIT, SDI-LINE,
SDI-EQV (same slot+line => same w0 — S-L4(i) shadow), SDI-RESFACT,
SDI-SEP, SDI-SURV ((SURV-DISJ) itself — a violation is a counterexample),
HARNESS.  Measured censuses: KILLDEC / SURVDEC / EQLGRP / PB rows /
PDFAIL witnesses / mutation controls.

Deterministic, exact arithmetic, no sampling.  Results written
incrementally (after every tower) for salvage safety.
Usage: python3 survdisj_instrument.py [outdir]
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
}

# ---- law-keyed counters: LAW[cand][(lawkey, verdict)] = n ------------------
LAW = collections.defaultdict(collections.Counter)
MUT = collections.Counter()          # mutation-control firing counts
KILLDEC, SURVDEC, PDFAIL, PBROWS, EQLGRP, CANC = [], [], [], [], [], []

def lawkey(g0, p, kdef, ctop):
    strat = "thresh" if kdef == ctop else ("above" if kdef > 0 else "direct")
    return (("g1" if g0 == 1 else "g2+"),
            ("rc2" if p == 2 else "rcODD"), strat)

def resstr(E, r):
    return str(r)

def classify_group(E, grp, p):
    """Residue classes by keq with signed counts; kill genre."""
    classes = []                      # [res, npos, nneg]
    for c in grp:
        for cl in classes:
            if E.keq(cl[0], c["res"]):
                if c["sgn"] > 0: cl[1] += 1
                else: cl[2] += 1
                break
        else:
            classes.append([c["res"], int(c["sgn"] > 0), int(c["sgn"] < 0)])
    signed = [cl[1] - cl[2] for cl in classes]
    if all(s == 0 for s in signed):
        genre = "SIGN-PAIR" if len(classes) == 1 else "SIGN-PAIR-MULTI"
    elif all(s % p == 0 for s in signed):
        genre = "MODP" if len(classes) == 1 else "MODP-MULTI"
    else:
        genre = "CROSS"
    return classes, signed, genre

def cell_public(E, c, R):
    d = dict(sgn=c["sgn"], w0=c["w0"], res=resstr(E, c["res"]),
             ncorr=sum(c["ncorr"]), r=c["ncorr"][E.m - 1], junk=c["junk"],
             prin=bool(c["prin"]), y2=c["y2"], nedges=len(c["ce"]))
    if c.get("fact") is not None:
        d["fact"] = c["fact"]
    return d

def trace_full(E, sA, sB, u1a, u1b, aA, aB, su, cs, Dd, kdef, key, prin,
               tag, p, kind, g0, phase, dmap, Dmap):
    """One live row: full multiset + residue decomposition + candidates."""
    R = E.R; m = E.m
    sig = tuple(sA[l + 1] + sB[l + 1] for l in range(m))
    b0 = pscal(R, R["pi_pow"](u1a + u1b), [R["one"]])
    prodp = pmul(R, aA, aB)
    if pnorm(R, padd(R, prodp, pneg(R, E.cellpoly(b0, sig)))):
        viol("HARNESS", tag, f"a*a' != formal cell at {key}"); return None
    pools = WS.pools_of(E, sA, sB, su)[0]
    rho = [pools[l] % E.e[l] for l in range(m - 1)]
    z = (0,) * m
    init = [(1, b0, sig, z, z, z, z, 0, None, False, (), 0)]
    q1sink = []
    out = ED.walk(E, init, q1sink, tag)
    if out[0] is None: harvest(tag); return None
    E1c, _ = pdivmod(R, prodp, E.Phis[m])
    if WD.cellsum(E, q1sink) != pnorm(R, E1c):
        viol("SDI-CONS", tag, f"stage-1 sum != E1IH at {key}")
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
        viol("SDI-CONS", tag, f"stage-2 sum != Q1 at {key}")
    harvest(tag)
    ctop = cs[-1] if cs else 0
    if kdef > ctop or not q2sink:
        return None                       # dead / empty: out of scope
    lk = lawkey(g0, p, kdef, ctop)
    q = WD.q_quanta(E)
    lamhat = E.line(b0, sig) + E.gam[m + 1] - 2 * E.wmPhi
    allg1 = (E.g[0] == 1)
    a_, r_, b_, stock1 = WD.greedy_chains(E, sig, su, cs)
    stk = (stock1 >= E.P[m - 1])
    cells = []
    for st in q2sink:
        sgn, b, j, pc, dmp, cons, ncorr, junk, jD, isp, ce, y2 = st
        ln = E.line(b, j)
        if E.wm(E.cellpoly(b, j)) != ln:
            viol("SDI-DIGIT", tag, f"w_m(cell) != line at {key}: j={j}")
        floor = lamhat + sum(pc[l - 1] * q[l] for l in range(1, m))
        if junk == 0 and ln != floor:
            viol("SDI-LINE", tag, f"junk-free off line at {key}")
        if junk > 0 and ln <= floor:
            viol("SDI-LINE", tag, f"junk not above floor at {key}")
        c = dict(sgn=sgn, b=b, j=j, pc=pc, ncorr=ncorr, junk=junk, jD=jD,
                 prin=isp, ce=ce, y2=y2, line=ln, w0=w0(R, b),
                 res=E.resKm(b), fact=None)
        # SDI-RESFACT: the K0-residue-product factorization (junk-free only)
        if junk == 0:
            pr = E.resKm(b0); pw = u1a + u1b
            fact = [f"b0[w0={u1a+u1b}]"]
            ok = True
            for (i, kc, avec, dj0) in ce:
                cd = dmap.get((i, kc, avec))
                if cd is None:
                    viol("SDI-RESFACT", tag,
                         f"correction d-cell lookup fails at {key} "
                         f"(i={i},k={kc})"); ok = False; break
                pr = E.kmul(pr, E.resKm(cd)); pw += w0(R, cd)
                fact.append(f"cd(i={i},k={kc})[w0={w0(R, cd)},"
                            f"res={resstr(E, E.resKm(cd))}]")
            if ok:
                cD = Dmap.get(tuple(jD))
                if cD is None:
                    viol("SDI-RESFACT", tag, f"seed d-cell lookup at {key}")
                else:
                    pr = E.kmul(pr, E.resKm(cD)); pw += w0(R, cD)
                    fact.append(f"cD(jD={list(jD)})[w0={w0(R, cD)},"
                                f"res={resstr(E, E.resKm(cD))}]")
                    if (c["w0"] != pw or not E.keq(c["res"], pr)
                            or sgn != (-1) ** len(ce)):
                        viol("SDI-RESFACT", tag,
                             f"L-NORM chain fails at {key}: w0 {c['w0']} vs "
                             f"{pw}, sgn {sgn} vs {(-1)**len(ce)}")
                    else:
                        c["fact"] = fact; note("resfact_ok")
        cells.append(c)
    # cascade cell (unique correction-free junk-free principal Y2-free)
    casc = [c for c in cells if c["ce"] == () and c["junk"] == 0
            and c["prin"] and c["y2"] == 0]
    casc_rec = casc[0] if len(casc) == 1 else None
    if allg1 and stk and len(casc) != 1:
        viol("SDI-SURV", tag, f"cascade count {len(casc)} != 1 at {key}")
    beta_min = min(c["line"] for c in cells)
    # ---- slots, netting, groups ----
    slots = collections.defaultdict(list)
    for c in cells: slots[c["j"]].append(c)
    spec = []                              # netted spectrum
    for jv, grp in slots.items():
        acc = []
        for c in grp:
            acc = padd(R, acc, c["b"] if c["sgn"] > 0 else pneg(R, c["b"]))
        acc = pnorm(R, acc)
        if acc: spec.append((E.line(acc, jv), jv, len(grp), acc))
    spec.sort(key=lambda t: t[0])
    wq = E.wm(Q1c) if pnorm(R, Q1c) else None
    if wq is None:
        viol("SDI-SEP", tag, f"live row with Q1 == 0 at {key}"); return None
    if wq < beta_min or (spec and wq != spec[0][0]):
        viol("SDI-SEP", tag, f"w_m(Q1)={wq} vs beta_min={beta_min}, "
             f"min netted={spec[0][0] if spec else None} at {key}")
    # equal-line same-slot groups + kills
    killed_groups = []
    for jv, grp in slots.items():
        lines = collections.defaultdict(list)
        for c in grp: lines[c["line"]].append(c)
        w0s = collections.defaultdict(set)
        for c in grp: w0s[c["line"]].add(c["w0"])
        for ln, sub in lines.items():
            if len(w0s[ln]) > 1:
                viol("SDI-EQV", tag, f"same slot+line, different w0 at {key}")
            if len(sub) < 2: continue
            acc = []
            for c in sub:
                acc = padd(R, acc, c["b"] if c["sgn"] > 0 else pneg(R, c["b"]))
            acc = pnorm(R, acc)
            killed = (not acc) or E.line(acc, jv) != ln
            classes, signed, genre = classify_group(E, sub, p)
            grec = dict(tower=tag, key=list(key), p=p, kind=kind, g0=g0,
                        phase=phase, slot=list(jv), line=ln, n=len(sub),
                        at_bottom=(ln == beta_min), killed=bool(killed),
                        raised=bool(acc), genre=genre,
                        signed=[int(s) for s in signed],
                        junks=sorted(set(c["junk"] for c in sub)))
            EQLGRP.append(grec)
            if killed:
                kg = dict(grec)
                kg["cells"] = [cell_public(E, c, R) for c in sub]
                kg["classes"] = [[resstr(E, cl[0]), cl[1], cl[2],
                                  (cl[1] - cl[2]) % p] for cl in classes]
                KILLDEC.append(kg)
                killed_groups.append((jv, ln, sub, genre))
                if genre == "CROSS":
                    print(f"  !! CROSS-genre kill at {tag}{list(key)} "
                          f"slot={list(jv)} line={ln}")
                    note("cross_kills")
    # ---- (SURV-DISJ) verdict family ----
    bottom_surv = bool(spec) and spec[0][0] == beta_min
    casc_surv = False
    if casc_rec is not None:
        casc_surv = any(s[1] == casc_rec["j"] and s[0] == casc_rec["line"]
                        for s in spec)
    if not (bottom_surv or casc_surv):
        viol("SDI-SURV", tag,
             f"(SURV-DISJ) COUNTEREXAMPLE at {tag}{list(key)} p={p} {kind} "
             f"g0={g0}: bottom dead AND cascade slot dead; spec head="
             f"{[(s[0], list(s[1])) for s in spec[:3]]}")
    if not bottom_surv:
        CANC.append(dict(tower=tag, key=list(key), p=p, kind=kind, g0=g0,
                         phase=phase, beta_min=beta_min, wq=wq,
                         surv_is_casc=bool(casc_surv)))
    # ---- survivors: the minimal netted slots ----
    surv_slots = [s for s in spec if s[0] == wq]
    surv_meas = []
    for (netline, jv, nslot, acc) in surv_slots:
        grp = slots[jv]
        minline = min(c["line"] for c in grp)
        at_min = [c for c in grp if c["line"] == minline]
        sumfree = (len(at_min) == 1 and netline == minline)
        is_casc = bool(casc_rec is not None and jv == casc_rec["j"]
                       and netline == casc_rec["line"])
        surv_meas.append(dict(slot=list(jv), netline=netline,
                              minline=minline, n_at_min=len(at_min),
                              n_slot=len(grp), sumfree=bool(sumfree),
                              is_casc=is_casc,
                              cells=[cell_public(E, c, R) for c in at_min]))
    # ---- candidates ----
    # P-A
    if allg1 and stk and casc_rec is not None and g0 == 1:
        nc = len(slots[casc_rec["j"]])
        LAW["P-A"][(lk, "ok" if nc == 1 else "fail")] += 1
        if nc != 1:
            PDFAIL.append(dict(cand="P-A", tower=tag, key=list(key), p=p,
                               g0=g0, n=nc))
    if g0 >= 2 and casc_rec is not None and len(slots[casc_rec["j"]]) >= 2:
        MUT["M-A1"] += 1                   # singleton predicate fails at g0>=2
    if g0 == 1 and any(len([c for c in slots[jv] if c["line"] == beta_min])
                       >= 2 for jv in slots):
        MUT["M-A2"] += 1                   # g0=1 bottom collision exists
    # P-B (g0 >= 2 rows)
    if g0 >= 2:
        bgroups = {jv: [c for c in slots[jv] if c["line"] == beta_min]
                   for jv in slots}
        bgroups = {jv: g for jv, g in bgroups.items() if g}
        sizes = sorted(len(g) for g in bgroups.values())
        kill_here = any(ln == beta_min for (_, ln, _, _) in killed_groups)
        surv_bottom = [s for s in spec if s[0] == beta_min]
        odd_all_surv = bool(surv_bottom) and all(
            len([c for c in slots[s[1]] if c["line"] == beta_min]) % 2 == 1
            for s in surv_bottom)
        mult1 = False
        for jv, g in bgroups.items():
            classes, signed, _ = classify_group(E, g, p)
            if any(abs(s) == 1 for s in signed): mult1 = True; break
        for nm, val in (("PB-single-some", any(n == 1 for n in sizes)),
                        ("PB-odd-some", any(n % 2 == 1 for n in sizes)),
                        ("PB-odd-all-surv", odd_all_surv),
                        ("PB-mult1-some", mult1)):
            LAW[nm][(lk, "ok" if val else "fail")] += 1
            if kill_here:
                LAW[nm + "@kill"][(lk, "ok" if val else "fail")] += 1
        if any(n % 2 == 0 for n in sizes): MUT["M-B2"] += 1
        PBROWS.append(dict(tower=tag, key=list(key), p=p, kind=kind,
                           phase=phase, sizes=sizes, kill_here=bool(kill_here),
                           n_surv_bottom=len(surv_bottom),
                           surv_sizes=[len([c for c in slots[s[1]]
                                            if c["line"] == beta_min])
                                       for s in surv_bottom]))
    for (jv, ln, sub, genre) in killed_groups:
        if len(sub) % 2 == 1: MUT["M-B1-oddkill"] += 1
        else: MUT["M-B1-evenkill"] += 1
    # P-C
    if killed_groups:
        ok = all(ln > beta_min for (_, ln, _, _) in killed_groups)
        LAW["P-C"][(lk, "ok" if ok else "fail")] += 1
    # P-D
    pd_all = all(s["sumfree"] for s in surv_meas)
    pd_some = any(s["sumfree"] for s in surv_meas)
    LAW["P-D-all"][(lk, "ok" if pd_all else "fail")] += 1
    LAW["P-D-some"][(lk, "ok" if pd_some else "fail")] += 1
    if killed_groups:
        LAW["P-D-all@kill"][(lk, "ok" if pd_all else "fail")] += 1
        SURVDEC.append(dict(tower=tag, key=list(key), p=p, kind=kind, g0=g0,
                            phase=phase, beta_min=beta_min, wq=wq,
                            bottom_surv=bool(bottom_surv),
                            casc_surv=bool(casc_surv),
                            kills=[dict(slot=list(jv), line=ln, n=len(sub),
                                        genre=genre)
                                   for (jv, ln, sub, genre) in killed_groups],
                            survivors=surv_meas))
    if not pd_all:
        MUT["M-D1"] += 1
        for s in surv_meas:
            if not s["sumfree"]:
                PDFAIL.append(dict(cand="P-D", tower=tag, key=list(key), p=p,
                                   kind=kind, g0=g0, phase=phase,
                                   had_kill=bool(killed_groups), **s))
    note("live_rows")
    return dict(live=True)

# ---------------- d-cell lookup tables --------------------------------------
def build_maps(E):
    dmap = {}
    for i, row in enumerate(E.corr_table()):
        for (k, dcells) in row:
            for (cd, av) in dcells:
                avec = tuple((av[l] if l < len(av) else 0) for l in range(i))
                dmap[(i, k, avec)] = cd
    Dmap = {tuple(jD): cD for (cD, jD) in E.Dcells}
    return dmap, Dmap

# ---------------- tower drivers ---------------------------------------------
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
    dmap, Dmap = build_maps(E)
    return E, su, Etot, G0, anch, prin, dmap, Dmap

def run_sealed_tower(spec):
    """The committed sealed selection loop, copied verbatim from
    surv_derive_checks.run_sealed_tower; live rows traced by this unit's
    instrumented tracer, dead rows skipped (out of (SURV) scope)."""
    tag, m, kind, p, d0, reads = spec
    t0 = time.time()
    st = setup(spec)
    if st is None: return
    E, su, Etot, G0, anch, prin, dmap, Dmap = st
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
        r = trace_full(E, sA, sB, u1a, u1b, anch[ga][0], anch[gb][0], su,
                       cs, Dd, kdef, (ga, gb), prin, tag, p, kind, E.g[0],
                       "sealed", dmap, Dmap)
        if r: nl += 1
    print(f"-- SEALED {tag} m={m} {kind},p={p},d0={d0} g0={E.g[0]}: "
          f"live traced={nl} ({time.time()-t0:.1f}s)")

def run_fresh_tower(spec, cap3, cap4, phase):
    tag, m, kind, p, d0, reads = spec
    t0 = time.time()
    st = setup(spec)
    if st is None: return
    E, su, Etot, G0, anch, prin, dmap, Dmap = st
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
            r = trace_full(E, sA, sB, u1a, u1b, anch[ga][0], anch[gb][0], su,
                           cs, Dd, kdef, (ga, gb), prin, tag, p, kind,
                           E.g[0], phase, dmap, Dmap)
            if r: nl += 1
    print(f"-- {phase.upper()} {tag} m={m} {kind},p={p},d0={d0} g0={E.g[0]}: "
          f"live traced={nl} ({time.time()-t0:.1f}s)")

# PE1's PX roster, verbatim (surv_pe1_ext.py, pinned above)
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

# NEW adversarial roster: g0 >= 2 x residue characteristic 2 — BOTH kill
# regimes reachable on the same rows (no committed battery probed this cross)
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
               law={cand: {f"{'|'.join(k[0])}|{k[1]}": n
                           for k, n in c.items()}
                    for cand, c in LAW.items()},
               mutations=dict(MUT), killdec=KILLDEC, survdec=SURVDEC,
               pdfail=PDFAIL, pbrows=PBROWS, eqlgrp=EQLGRP, canc=CANC,
               elapsed=elapsed)
    with open(os.path.join(OUTDIR, "survdisj_instrument_results.json"),
              "w") as f:
        json.dump(out, f, indent=1, default=str)

def main():
    t0 = time.time()
    for fn, want in PINS.items():
        got = hashlib.md5(open(os.path.join(HERE, fn), "rb").read()).hexdigest()
        if got != want:
            viol("SDI-PIN", fn, f"md5 {got} != pinned {want}")
    print("=" * 78)
    print("PHASE SEALED — WS.ROSTER via the committed sealed selection")
    print("=" * 78)
    for spec in WS.ROSTER:
        run_sealed_tower(spec); save(time.time() - t0)
    print("=" * 78)
    print("PHASE EQ — ED.FRESH_ROSTER at raised caps 12/6 (PE1 selection)")
    print("=" * 78)
    for spec in ED.FRESH_ROSTER:
        run_fresh_tower(spec, 12, 6, "eq"); save(time.time() - t0)
    print("=" * 78)
    print("PHASE PX — the PE1 PX roster, caps 12/6")
    print("=" * 78)
    for spec in PX_ROSTER:
        run_fresh_tower(spec, 12, 6, "px"); save(time.time() - t0)
    print("=" * 78)
    print("PHASE SD — NEW adversarial g0>=2 x residue-char-2 roster, 12/6")
    print("=" * 78)
    for spec in SD_ROSTER:
        run_fresh_tower(spec, 12, 6, "sd"); save(time.time() - t0)
    print("=" * 78)
    fams = ["SDI-PIN", "SDI-CONS", "SDI-DIGIT", "SDI-LINE", "SDI-EQV",
            "SDI-RESFACT", "SDI-SEP", "SDI-SURV", "HARNESS"]
    for f in fams:
        print(f"{f:12s}: {sum(1 for v in VIOL if v[0] == f)} violations")
    print("-" * 78)
    print(f"live rows traced: {CNT.get('live_rows', 0)}; junk-free cells "
          f"with verified K0-product factorization: {CNT.get('resfact_ok', 0)}")
    print(f"CROSS-genre kills (new-genre flag): {CNT.get('cross_kills', 0)}")
    print(f"total-bottom-dead rows (CANC): {len(CANC)}; on ALL of them "
          f"survivor = cascade slot at cascade line: "
          f"{all(c['surv_is_casc'] for c in CANC) if CANC else 'n/a'}")
    print("-" * 78)
    print("LAW-KEYED CANDIDATE COUNTS  (key = g0-class | residue-char | "
          "stratum):")
    for cand in sorted(LAW):
        print(f"  {cand}:")
        agg = collections.Counter()
        for (lk, verdict), n in sorted(LAW[cand].items()):
            print(f"    {'|'.join(lk):24s} {verdict:5s} {n}")
            agg[verdict] += n
        print(f"    {'TOTAL':24s} ok={agg['ok']} fail={agg['fail']}")
    print("MUTATION CONTROLS (teeth):", dict(MUT))
    for mc, need in (("M-A1", "P-A"), ("M-A2", "P-A"), ("M-B2", "P-B"),
                     ("M-D1", "P-D")):
        if MUT.get(mc, 0) == 0:
            print(f"  CONTROL FAILURE: {mc} never fired — {need} counts "
                  f"are TOOTHLESS as evidence")
    print("-" * 78)
    genres = collections.Counter((g["genre"], g["p"], g["g0"],
                                  g["at_bottom"]) for g in KILLDEC)
    print("KILLED-GROUP GENRES (genre, p, g0, at_bottom):")
    for k, n in sorted(genres.items()): print(f"    {k}: {n}")
    sv = collections.Counter((bool(s["bottom_surv"]), bool(s["casc_surv"]))
                             for s in SURVDEC)
    print("KILL-ROW SURVIVOR PATTERN (bottom_surv, casc_surv):", dict(sv))
    sf = collections.Counter(
        (all(x["sumfree"] for x in s["survivors"])) for s in SURVDEC)
    print("KILL-ROW minimal survivor sum-free:", dict(sf))
    print(f"total violations: {len(VIOL)}")
    el = time.time() - t0
    print(f"elapsed: {el:.1f}s")
    save(el, final=True)
    print("results ->", os.path.join(OUTDIR, "survdisj_instrument_results.json"))

if __name__ == "__main__":
    main()
