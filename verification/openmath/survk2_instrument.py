#!/usr/bin/env python3
"""survk2_instrument.py — (SURV-K2) INSTRUMENT unit (2026-08-08 campaign).

Target: the (SURV-K2) box of SURVDISJ_PROOF_2026-08-08.md S6 (at 553895d) —
at g0 >= 2 on live rows, SOME bottom-line group carries a residue class of
signed path-count +-1 (the signed-multiplicity-one law; existence half).
The proved reduction (SD-L6/SD-L7): protected => survives, char-free.
This unit MEASURES the sign-reversing pairing structure the box names as
the proof target: pair correction-riders by a local toggle
(level-0 correction (0,k) <-> seed shift t -> t + (g0-k), the two routes
to the same slot mass at the same w0), residue-preserving, sign-flipping.

Design derivations (input, not proof): W-D2(iv) t-inventory
j0(D_t) = s1(u1) + t*e0, w0 = u0 - t*h0; corr_table level-0 children
C_k = lift(psi0_k)*pi^{(g0-k)h0}, consumption e0(g0-k), no dump; LED_0
forces t_rider - t_other = g0 - k for a single-level-0-edge toggle at a
fixed slot, and w0 then matches automatically.  Residue preservation is
the SEED-LEVEL identity res(C_k)*res(cD_{t+g0-k}) == res(cD_t) — measured
directly as Q-A0.

Measurements (law-keyed g2/g3/g4+ | rc2/rcODD | thresh/above/direct):
  Q-A0 seed-level residue truth table per tower.
  Q-A  per-class max bipartite matching (+ vs -) using T0 u TI pairs:
       T0 = single level-0 edge toggle with the exact quantum;
       TG = single level-0 edge, quantum FAILS;
       TI = single interior edge (descriptor censused);
       TM = anything else.  Perfect matching = QA-match ok.
       Teeth: M-QA-TX (TM pairs exist), M-QA-WRONGQ (quantum+1 shrinks).
  Q-B  canonical remainder of +-1 classes (removable-cell analysis);
       extremal-t classification.  Mutation M-QB-T1.
  Q-C  per-seed signed counts S_t; QC-seedbound (|S_t| <= 1);
       QC-cf (total == correction-free signed count).  Teeth M-QC-2.
  Q-D  minimal/survivor-group class-vector patterns vs pool strata.
Verdict families (predicted 0): SK2-PIN, SK2-CONS, SK2-SEED, SK2-W0K,
SK2-SGN, SK2-EQV, SK2-MULT1 (violation = (SURV-K2)-form counterexample),
SK2-BOT, HARNESS.

Rows: the committed survdisj_instrument union-roster selection replicated
verbatim, filtered to g0 >= 2 towers (the committed 286), plus the NEW
adversarial K2 roster (g0 in {2,3,4}, m = 4 deep, chars 2/3/5, d0 = 2,
deep pools).  Tree-cap overflow = disclosed skip, NOT a violation.
Deterministic, exact arithmetic; incremental result writes.
Usage: python3 survk2_instrument.py [outdir]
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
    """Engine-violation harvest; ED tree-cap events are DISCLOSED SKIPS."""
    for src, lst in (("PE", PE.VIOL), ("ED", ED.VIOL), ("WS", WS.VIOL),
                     ("WD", WD.VIOL)):
        while len(lst) > harvest.seen[src]:
            v = lst[harvest.seen[src]]
            if "tree cap exceeded" in str(v):
                note("row_treecap")
                print(f"  DISCLOSED SKIP [{tag}]: tree cap exceeded")
            else:
                viol("HARNESS", tag, f"{src}: {v}")
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

LAW = collections.defaultdict(collections.Counter)
MUT = collections.Counter()
PAIRC = collections.Counter()          # pair-relation label census
QBREC, QCREC, QDROWS, GRPREC = [], [], [], []
A0TAB = {}

def lawkey(g0, p, kdef, ctop):
    strat = "thresh" if kdef == ctop else ("above" if kdef > 0 else "direct")
    gk = "g2" if g0 == 2 else ("g3" if g0 == 3 else "g4+")
    return (gk, ("rc2" if p == 2 else "rcODD"), strat)

def classify_group(E, grp, p):
    classes = []                      # [res, npos, nneg, cells]
    for c in grp:
        for cl in classes:
            if E.keq(cl[0], c["res"]):
                if c["sgn"] > 0: cl[1] += 1
                else: cl[2] += 1
                cl[3].append(c)
                break
        else:
            classes.append([c["res"], int(c["sgn"] > 0), int(c["sgn"] < 0), [c]])
    signed = [cl[1] - cl[2] for cl in classes]
    return classes, signed

# ---------------- pair relations ---------------------------------------------
def relpair(E, ca, cb):
    """Label an opposite-sign same-class pair.  Returns (label, descriptor)."""
    g0 = E.g[0]
    Ca, Cb = collections.Counter(ca["ce"]), collections.Counter(cb["ce"])
    da, db = Ca - Cb, Cb - Ca
    na, nb = sum(da.values()), sum(db.values())
    if na + nb != 1:
        return "TM", dict(nextra=(na, nb))
    rider, other = (ca, cb) if na == 1 else (cb, ca)
    (i, k, avec, dj0), = list((da if na == 1 else db).elements())
    dt = rider["t"] - other["t"]
    dpc = tuple(rider["pc"][l] - other["pc"][l] for l in range(len(rider["pc"])))
    if i == 0:
        q = g0 - k
        if avec == () and dj0 == 0 and dt == q:
            return "T0", dict(k=k, dt=dt, dpc=list(dpc),
                              junk_eq=(rider["junk"] == other["junk"]),
                              y2_eq=(rider["y2"] == other["y2"]))
        return "TG", dict(k=k, dt=dt, q=q, dj0=dj0, dpc=list(dpc))
    return "TI", dict(i=i, avec=list(avec), dj0=dj0, dt=dt, dpc=list(dpc))

def relpair_mut(E, ca, cb):
    """M-QA-WRONGQ mutation: the T0 quantum shifted by +1."""
    lab, d = relpair(E, ca, cb)
    if lab == "T0": return "TG", d
    if lab == "TG" and d.get("dj0") == 0 and d["dt"] == d["q"] + 1:
        return "T0", d
    return lab, d

def kuhn(np_, nn_, ok):
    matchR = [-1] * nn_
    def aug(u, seen):
        for v in range(nn_):
            if ok(u, v) and v not in seen:
                seen.add(v)
                if matchR[v] < 0 or aug(matchR[v], seen):
                    matchR[v] = u; return True
        return False
    sz = 0
    for u in range(np_):
        if aug(u, set()): sz += 1
    return sz

def class_match(E, cl, rel):
    """Max matching of a class's + cells vs - cells under relation labels
    in `rel`.  Returns (size, npos, nneg, labels_matrix)."""
    pos = [c for c in cl[3] if c["sgn"] > 0]
    neg = [c for c in cl[3] if c["sgn"] < 0]
    labs = [[relpair(E, a, b)[0] for b in neg] for a in pos]
    sz = kuhn(len(pos), len(neg), lambda u, v: labs[u][v] in rel)
    return sz, pos, neg, labs

# ---------------- one traced row ---------------------------------------------
def trace_k2(E, sA, sB, u1a, u1b, aA, aB, su, cs, Dd, kdef, key, prin,
             tag, p, kind, g0, phase, dmap, Dmap, u0):
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
        viol("SK2-CONS", tag, f"stage-1 sum != E1IH at {key}")
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
        viol("SK2-CONS", tag, f"stage-2 sum != Q1 at {key}")
    harvest(tag)
    ctop = cs[-1] if cs else 0
    if kdef > ctop or not q2sink:
        return None
    lk = lawkey(g0, p, kdef, ctop)
    # [rev 2] per-row ATOMIC buffers: globals are committed only at the end
    # of a fully traced row, so a K2-phase budget timeout never leaves a
    # partially recorded row in the artifacts.
    L_LAW = []
    L_MUT = collections.Counter()
    L_PAIRC = collections.Counter()
    L_CNT = collections.Counter()
    L_QB, L_QC, L_QD, L_GRP = [], [], [], []
    cells = []
    for st in q2sink:
        sgn, b, j, pc, dmp, cons, ncorr, junk, jD, isp, ce, y2 = st
        ln = E.line(b, j)
        # SK2-SEED: the W-D2(iv) t-decomposition
        t, rem = divmod(jD[0] - su[1], E.e[0])
        if rem != 0 or not (0 <= t < g0):
            viol("SK2-SEED", tag, f"jD[0]={jD[0]} not s1(u1)+t*e0 at {key}")
            t = None
        else:
            cD = Dmap.get(tuple(jD))
            if cD is None or w0(R, cD) != u0 - t * E.h[0]:
                viol("SK2-SEED", tag,
                     f"seed w0 != u0 - t*h0 at {key}: jD={jD} t={t}")
        if sgn != (-1) ** len(ce):
            viol("SK2-SGN", tag, f"sgn {sgn} != (-1)^{len(ce)} at {key}")
        cells.append(dict(sgn=sgn, b=b, j=j, pc=tuple(pc), ncorr=sum(ncorr),
                          junk=junk, jD=jD, prin=isp, ce=ce, y2=y2, line=ln,
                          w0=w0(R, b), res=E.resKm(b), t=t))
    if any(c["t"] is None for c in cells):
        return None                       # SEED breach already recorded
    beta_min = min(c["line"] for c in cells)
    slots = collections.defaultdict(list)
    for c in cells: slots[c["j"]].append(c)
    # SK2-EQV
    for jv, grp in slots.items():
        w0s = collections.defaultdict(set)
        for c in grp: w0s[c["line"]].add(c["w0"])
        if any(len(s) > 1 for s in w0s.values()):
            viol("SK2-EQV", tag, f"same slot+line, different w0 at {key}")
    # netted spectrum
    spec = []
    for jv, grp in slots.items():
        acc = []
        for c in grp:
            acc = padd(R, acc, c["b"] if c["sgn"] > 0 else pneg(R, c["b"]))
        acc = pnorm(R, acc)
        if acc: spec.append((E.line(acc, jv), jv, acc))
    spec.sort(key=lambda s: (s[0], s[1]))
    if not spec:
        viol("HARNESS", tag, f"live row nets to zero at {key}"); return None
    bottom_surv = (spec[0][0] == beta_min)
    if not bottom_surv:
        viol("SK2-BOT", tag, f"netted bottom DEAD on g0>=2 row at {tag}{key}")
    # bottom-line groups
    bgroups = {}
    for jv, grp in slots.items():
        g = [c for c in grp if c["line"] == beta_min]
        if g: bgroups[jv] = g
    killed_bottom = {}
    for jv, g in bgroups.items():
        acc = []
        for c in g:
            acc = padd(R, acc, c["b"] if c["sgn"] > 0 else pneg(R, c["b"]))
        acc = pnorm(R, acc)
        killed_bottom[jv] = (not acc) or E.line(acc, jv) != beta_min
    kill_here = any(killed_bottom.values())
    # SK2-MULT1: some bottom group carries a +-1 class
    mult1 = False
    ginfo = {}
    for jv, g in bgroups.items():
        classes, signed = classify_group(E, g, p)
        ginfo[jv] = (classes, signed)
        if any(abs(s) == 1 for s in signed): mult1 = True
        if any(abs(s) >= 2 for s in signed): L_MUT["M-QC-2"] += 1
    if not mult1:
        viol("SK2-MULT1", tag,
             f"(SURV-K2) FORM COUNTEREXAMPLE at {tag}{list(key)} p={p} "
             f"g0={g0}: no bottom-line group carries a +-1 class")
    L_LAW.append(("SK2-MULT1", lk, "ok" if mult1 else "fail"))
    # survivor bottom slots + the minimal group
    surv_bottom = sorted(s[1] for s in spec if s[0] == beta_min)
    min_jv = surv_bottom[0] if surv_bottom else None
    # ---- Q-A / Q-B / Q-C / Q-D over bottom groups ----
    row_qa_min = None
    for jv, g in sorted(bgroups.items()):
        classes, signed = ginfo[jv]
        if len(g) > 40:
            L_CNT["qa_skipped_big"] += 1; continue
        is_min = (jv == min_jv)
        is_surv = jv in surv_bottom
        # pair census + matching
        grp_perfect = True
        cl_recs = []
        for ci, cl in enumerate(classes):
            pos = [c for c in cl[3] if c["sgn"] > 0]
            neg = [c for c in cl[3] if c["sgn"] < 0]
            for a in pos:
                for b_ in neg:
                    L_PAIRC[relpair(E, a, b_)[0]] += 1
            sz, pos, neg, labs = class_match(E, cl, ("T0", "TI"))
            perfect = (sz == min(len(pos), len(neg)))
            if not perfect: grp_perfect = False
            # M-QA-WRONGQ: mutated quantum must shrink somewhere
            if pos and neg:
                labs_m = [[relpair_mut(E, a, b_)[0] for b_ in neg]
                          for a in pos]
                szm = kuhn(len(pos), len(neg),
                           lambda u, v: labs_m[u][v] in ("T0", "TI"))
                if szm < sz: L_MUT["M-QA-WRONGQ"] += 1
            # Q-B: canonical remainder for +-1 classes
            s = cl[1] - cl[2]
            qb = None
            if abs(s) == 1 and perfect and (pos or neg):
                maj, mino = (pos, neg) if s > 0 else (neg, pos)
                laM = [[relpair(E, a, b_)[0] in ("T0", "TI") for b_ in mino]
                       for a in maj]
                removable = []
                for xi in range(len(maj)):
                    idx = [u for u in range(len(maj)) if u != xi]
                    szx = kuhn(len(idx), len(mino),
                               lambda u, v: laM[idx[u]][v])
                    if szx == len(mino): removable.append(xi)
                canon = (len(removable) == 1)
                L_LAW.append(("QB-canon", lk, "ok" if canon else "fail"))
                ts = [c["t"] for c in cl[3]]
                if canon:
                    r = maj[removable[0]]
                    if len(set(ts)) == 1: cat = "single-t"
                    elif r["t"] == 0: cat = "t0"
                    elif r["t"] == max(ts): cat = "tmax"
                    else: cat = "interior"
                    L_LAW.append(("QB-rem", lk, cat))
                    if r["t"] != 1: L_MUT["M-QB-T1-fail"] += 1
                    qb = dict(cat=cat, t=r["t"], tmax=max(ts),
                              tset=sorted(set(ts)), ncorr=r["ncorr"],
                              junk=r["junk"],
                              cf=(r["ncorr"] == 0 and r["junk"] == 0),
                              sgn=int(s))
                    L_QB.append(dict(tower=tag, key=list(key), p=p, g0=g0,
                                     slot=list(jv), is_min=is_min,
                                     is_surv=is_surv, killed=killed_bottom[jv],
                                     **qb))
                else:
                    L_QB.append(dict(tower=tag, key=list(key), p=p, g0=g0,
                                     slot=list(jv), is_min=is_min,
                                     is_surv=is_surv, killed=killed_bottom[jv],
                                     cat="noncanon", nremov=len(removable),
                                     tset=sorted(set(ts)), sgn=int(s)))
            cl_recs.append(dict(signed=int(s), n=len(cl[3]),
                                npos=len(pos), nneg=len(neg),
                                perfect=bool(perfect)))
        L_LAW.append(("QA-match-all", lk, "ok" if grp_perfect else "fail"))
        if is_min:
            row_qa_min = grp_perfect
            L_LAW.append(("QA-match", lk, "ok" if grp_perfect else "fail"))
        # Q-C on this group
        St = collections.Counter()
        for c in g: St[c["t"]] += c["sgn"]
        stvec = [St.get(t, 0) for t in range(g0)]
        seedb = all(abs(x) <= 1 for x in stvec)
        cfs = sum(c["sgn"] for c in g if c["ncorr"] == 0 and c["junk"] == 0)
        tot = sum(c["sgn"] for c in g)
        if is_min:
            L_LAW.append(("QC-seedbound", lk, "ok" if seedb else "fail"))
            L_LAW.append(("QC-cf", lk, "ok" if tot == cfs else "fail"))
            L_QC.append(dict(tower=tag, key=list(key), p=p, g0=g0,
                             slot=list(jv), stvec=stvec, total=tot,
                             cfsigned=cfs, n=len(g),
                             signed=[int(s) for s in signed],
                             killed=killed_bottom[jv]))
        # Q-D pattern (survivor groups; committed first-occurrence order)
        if is_surv:
            pat = ",".join(str(int(s)) for s in signed)
            L_LAW.append(("QD-pattern", lk, f"({pat})"))
        L_GRP.append(dict(
            tower=tag, key=list(key), p=p, kind=kind, g0=g0, phase=phase,
            slot=list(jv), n=len(g), is_min=is_min, is_surv=is_surv,
            killed=bool(killed_bottom[jv]), signed=[int(s) for s in signed],
            classes=cl_recs,
            cells=[dict(sgn=c["sgn"], t=c["t"], ncorr=c["ncorr"],
                        junk=c["junk"], y2=c["y2"], w0=c["w0"],
                        res=str(c["res"]),
                        ce=[list(map(str, e)) for e in c["ce"]])
                   for c in g]))
    # Q-D row record (minimal group + strata keys)
    if min_jv is not None:
        classes, signed = ginfo[min_jv]
        gmin = bgroups[min_jv]
        cf = [c for c in gmin if c["ncorr"] == 0 and c["junk"] == 0]
        L_QD.append(dict(
            tower=tag, key=list(key), p=p, kind=kind, g0=g0, phase=phase,
            e0=E.e[0], h0=E.h[0], d0=E.d0, m=m, kdef=kdef, ctop=ctop,
            strat=lk[2], ndcells=len(E.Dcells),
            has_prin=any(tuple(c["jD"]) == prin for c in gmin),
            t_cf=(cf[0]["t"] if cf else None), n_cf=len(cf),
            nslots_bottom=len(bgroups), kill_here=bool(kill_here),
            n=len(gmin), pattern=",".join(str(int(s)) for s in signed),
            qa_perfect=bool(row_qa_min) if row_qa_min is not None else None))
    # [rev 2] atomic commit of the fully traced row
    for (cand, lkk, v) in L_LAW: LAW[cand][(lkk, v)] += 1
    MUT.update(L_MUT); PAIRC.update(L_PAIRC)
    for k_, n_ in L_CNT.items(): note(k_, n_)
    QBREC.extend(L_QB); QCREC.extend(L_QC); QDROWS.extend(L_QD)
    GRPREC.extend(L_GRP)
    note("live_rows"); note(f"live_rows_{lk[0]}")
    if kill_here: note("kill_rows")
    return dict(live=True)

# ---------------- Q-A0: the seed-level residue law (per tower) ---------------
def qa0_table(E, su, u0, dmap, Dmap, tag):
    g0 = E.g[0]
    tmap = {}
    for jD, cD in Dmap.items():
        t, rem = divmod(jD[0] - su[1], E.e[0])
        if rem == 0 and 0 <= t < g0:
            tmap[t] = cD
    corr0 = E.corr_table()[0]
    tab, nok, nfail = [], 0, 0
    for (k, dcells) in corr0:
        Ck = dcells[0][0]
        if w0(E.R, Ck) != (g0 - k) * E.h[0]:
            viol("SK2-W0K", tag, f"w0(C_{k}) != (g0-k)*h0")
        for t_hi in sorted(tmap):
            t_lo = t_hi - (g0 - k)
            if t_lo not in tmap: continue
            ok = E.keq(E.kmul(E.resKm(Ck), E.resKm(tmap[t_hi])),
                       E.resKm(tmap[t_lo]))
            tab.append(dict(k=k, t_hi=t_hi, t_lo=t_lo, ok=bool(ok)))
            if ok: nok += 1
            else: nfail += 1
    A0TAB[tag] = dict(g0=g0, ts=sorted(tmap), ks=[k for (k, _) in corr0],
                      table=tab, nok=nok, nfail=nfail)
    note("a0_ok", nok); note("a0_fail", nfail)

# ---------------- d-cell lookup + setup (replicated) --------------------------
def build_maps(E):
    dmap = {}
    for i, row in enumerate(E.corr_table()):
        for (k, dcells) in row:
            for (cd, av) in dcells:
                avec = tuple((av[l] if l < len(av) else 0) for l in range(i))
                dmap[(i, k, avec)] = cd
    Dmap = {tuple(jD): cD for (cD, jD) in E.Dcells}
    return dmap, Dmap

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
    prin, meta = WD.inv_checks(E, u, su)
    harvest(tag)
    if meta is None:
        print(f"-- {tag}: u0 unavailable — disclosed, skipped")
        note("tower_skipped"); return None
    dmap, Dmap = build_maps(E)
    qa0_table(E, su, meta["u0"], dmap, Dmap, tag)
    return E, su, Etot, G0, anch, prin, dmap, Dmap, meta["u0"]

# ---------------- tower drivers (selection replicated verbatim) --------------
def run_sealed_tower(spec, nrows):
    tag, m, kind, p, d0, reads = spec
    t0 = time.time()
    st = setup(spec)
    if st is None: return
    E, su, Etot, G0, anch, prin, dmap, Dmap, u0 = st
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
        r = trace_k2(E, sA, sB, u1a, u1b, anch[ga][0], anch[gb][0], su,
                     cs, Dd, kdef, (ga, gb), prin, tag, p, kind, E.g[0],
                     "sealed", dmap, Dmap, u0)
        if r: nl += 1
    nrows.append(nl)
    print(f"-- SEALED {tag} m={m} {kind},p={p},d0={d0} g0={E.g[0]}: "
          f"live traced={nl} ({time.time()-t0:.1f}s)")

def run_fresh_tower(spec, cap3, cap4, phase, nrows):
    tag, m, kind, p, d0, reads = spec
    t0 = time.time()
    st = setup(spec)
    if st is None: return
    E, su, Etot, G0, anch, prin, dmap, Dmap, u0 = st
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
            r = trace_k2(E, sA, sB, u1a, u1b, anch[ga][0], anch[gb][0], su,
                         cs, Dd, kdef, (ga, gb), prin, tag, p, kind,
                         E.g[0], phase, dmap, Dmap, u0)
            if r: nl += 1
    nrows.append(nl)
    print(f"-- {phase.upper()} {tag} m={m} {kind},p={p},d0={d0} g0={E.g[0]}: "
          f"live traced={nl} ({time.time()-t0:.1f}s)")

# PE1 PX roster (verbatim from the pinned survdisj_instrument; all g0 = 1 —
# kept for the union-roster replication census, filtered like the rest)
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

# NEW adversarial K2 roster: g0 in {2,3,4} (first g0 >= 3 probes anywhere),
# deep m = 4, chars 2/3/5, d0 = 2, deep pools
K2_BUDGET = 300          # [rev 2] wall-clock seconds per K2 tower
K2_ROSTER = [
    ("K2G3AF",  3, "Fpt", 2, 1, [(2,1,3), (2,1,1), (3,2,1), (2,1,1)]),
    ("K2G3AZ",  3, "Zp",  3, 1, [(2,1,3), (2,1,1), (3,2,1), (2,1,1)]),
    ("K2G3BF",  3, "Fpt", 2, 1, [(3,1,3), (2,1,1), (2,1,1), (2,1,1)]),
    ("K2G3P5",  3, "Zp",  5, 1, [(2,1,3), (2,1,1), (2,1,1), (2,1,1)]),
    ("K2G4AF",  3, "Fpt", 2, 1, [(2,1,4), (2,1,1), (2,1,1), (2,1,1)]),
    ("K2G4AZ",  3, "Zp",  3, 1, [(2,1,4), (2,1,1), (2,1,1), (2,1,1)]),
    ("K2G3D2Z", 3, "Zp",  3, 2, [(2,1,3), (3,2,1), (3,1,1), (2,1,1)]),
    ("K2DPG3F", 3, "Fpt", 2, 1, [(3,2,3), (2,1,1), (2,1,1), (2,1,1)]),
    ("K2W4G3F", 4, "Fpt", 2, 1, [(2,1,3), (2,1,1), (2,1,1), (2,1,1), (2,1,1)]),
    ("K2W4G3Z", 4, "Zp",  3, 1, [(2,1,3), (2,1,1), (2,1,1), (2,1,1), (2,1,1)]),
    ("K2G2P5B", 3, "Zp",  5, 1, [(3,1,2), (2,1,1), (3,2,1), (2,1,1)]),
    ("K2W4G2Z", 4, "Zp",  3, 1, [(3,1,2), (2,1,1), (2,1,1), (2,1,1), (2,1,1)]),
]

def save(elapsed, union_rows, final=False):
    out = dict(final=final, violations=VIOL, counters=CNT,
               union_g2_rows=union_rows,
               law={cand: {f"{'|'.join(k[0])}|{k[1]}": n
                           for k, n in c.items()}
                    for cand, c in LAW.items()},
               mutations=dict(MUT), pair_census=dict(PAIRC),
               a0tab=A0TAB, qbrec=QBREC, qcrec=QCREC, qdrows=QDROWS,
               grprec=GRPREC, elapsed=elapsed)
    with open(os.path.join(OUTDIR, "survk2_instrument_results.json"),
              "w") as f:
        json.dump(out, f, indent=1, default=str)

def main():
    t0 = time.time()
    for fn, want in PINS.items():
        got = hashlib.md5(open(os.path.join(HERE, fn), "rb").read()).hexdigest()
        if got != want:
            viol("SK2-PIN", fn, f"md5 {got} != pinned {want}")
    union_rows = []
    print("=" * 78)
    print("UNION ROSTER (survdisj_instrument selection, g0 >= 2 towers only)")
    print("=" * 78)
    for spec in WS.ROSTER:
        if spec[5][0][2] < 2: continue
        run_sealed_tower(spec, union_rows); save(time.time() - t0, sum(union_rows))
    for spec in ED.FRESH_ROSTER:
        if spec[5][0][2] < 2: continue
        run_fresh_tower(spec, 12, 6, "eq", union_rows)
        save(time.time() - t0, sum(union_rows))
    for spec in PX_ROSTER:
        if spec[5][0][2] < 2: continue
        run_fresh_tower(spec, 12, 6, "px", union_rows)
        save(time.time() - t0, sum(union_rows))
    for spec in SD_ROSTER:
        if spec[5][0][2] < 2: continue
        run_fresh_tower(spec, 12, 6, "sd", union_rows)
        save(time.time() - t0, sum(union_rows))
    nu = sum(union_rows)
    print(f"union-roster g0>=2 live rows: {nu} (committed count: 286)")
    if nu != 286:
        print("  !! ROSTER REPLICATION DIVERGENCE (disclosed; see D3)")
        note("roster_divergence")
    print("=" * 78)
    print("PHASE K2 — NEW adversarial roster (g0 in {2,3,4}, deep m, "
          "chars 2/3/5)")
    print("[rev 2] per-tower wall-clock budget %ds (g0 >= 3 engine cost — "
          "see the note's amendment bracket); timeout = disclosed skip" %
          K2_BUDGET)
    print("=" * 78)
    import signal
    def _alrm(sig, frm): raise TimeoutError("K2 tower budget")
    k2rows = []
    for spec in K2_ROSTER:
        old = signal.signal(signal.SIGALRM, _alrm)
        signal.alarm(K2_BUDGET)
        try:
            run_fresh_tower(spec, 12, 6, "k2", k2rows)
        except TimeoutError:
            note("tower_budget_timeout")
            print(f"-- K2 {spec[0]} m={spec[1]} {spec[2]},p={spec[3]},"
                  f"d0={spec[4]} g0={spec[5][0][2]}: BUDGET TIMEOUT "
                  f"({K2_BUDGET}s) — disclosed, skipped")
            harvest(spec[0])
        finally:
            signal.alarm(0); signal.signal(signal.SIGALRM, old)
        save(time.time() - t0, nu)
    print("=" * 78)
    fams = ["SK2-PIN", "SK2-CONS", "SK2-SEED", "SK2-W0K", "SK2-SGN",
            "SK2-EQV", "SK2-MULT1", "SK2-BOT", "HARNESS"]
    for f in fams:
        print(f"{f:12s}: {sum(1 for v in VIOL if v[0] == f)} violations")
    print("-" * 78)
    print(f"live g0>=2 rows traced: {CNT.get('live_rows', 0)} "
          f"(union {nu} + K2 {sum(k2rows)}); kill rows: "
          f"{CNT.get('kill_rows', 0)}; treecap skips: "
          f"{CNT.get('row_treecap', 0)}; towers skipped: "
          f"{CNT.get('tower_skipped', 0)}")
    print(f"Q-A0 seed-level residue law: ok={CNT.get('a0_ok', 0)} "
          f"fail={CNT.get('a0_fail', 0)} over "
          f"{sum(len(v['table']) for v in A0TAB.values())} triples, "
          f"{len(A0TAB)} towers")
    print("PAIR-RELATION CENSUS (all same-class opposite-sign bottom pairs):",
          dict(PAIRC))
    print("-" * 78)
    print("LAW-KEYED COUNTS (key = g0 | residue-char | stratum):")
    for cand in sorted(LAW):
        print(f"  {cand}:")
        agg = collections.Counter()
        for (lk, verdict), n in sorted(LAW[cand].items()):
            print(f"    {'|'.join(lk):24s} {verdict:12s} {n}")
            agg[verdict] += n
        tot = ", ".join(f"{k}={v}" for k, v in sorted(agg.items()))
        print(f"    TOTAL: {tot}")
    print("MUTATION CONTROLS (teeth):", dict(MUT))
    if PAIRC.get("TM", 0) == 0:
        print("  CONTROL NOTE: no TM pairs — single-toggle predicate "
              "unrestrictive on this roster (disclose)")
    if MUT.get("M-QA-WRONGQ", 0) == 0:
        print("  CONTROL FAILURE: M-QA-WRONGQ never fired — the T0 quantum "
              "was never load-bearing (QA counts TOOTHLESS)")
    if MUT.get("M-QC-2", 0) == 0:
        print("  CONTROL NOTE: no bottom class with |signed| >= 2 — "
              "seedbound/mult1 unstressed (disclose)")
    pats = set()
    for (lk, verdict), n in LAW.get("QD-pattern", {}).items():
        pats.add(verdict)
    print(f"distinct survivor-group patterns: {len(pats)} -> {sorted(pats)}")
    if len(pats) < 2:
        print("  CONTROL FAILURE: M-QD-DIV — pattern diversity absent")
    print(f"total violations: {len(VIOL)}")
    el = time.time() - t0
    print(f"elapsed: {el:.1f}s")
    save(el, nu, final=True)
    print("results ->",
          os.path.join(OUTDIR, "survk2_instrument_results.json"))

if __name__ == "__main__":
    main()
