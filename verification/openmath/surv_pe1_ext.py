#!/usr/bin/env python3
"""surv_pe1_ext.py — PE1's INDEPENDENT instrument for the first hostile pass
on lean/notes/openmath/SURV_PROOF_2026-08-08.md (charge: re-derive the two
committed cancellation instances from the committed engines, census the
same-slot equal-line collision stratum on FRESH rows, hunt MORE cancellation
instances — p > 2? g0 = 1? — and probe the S-L4(iii) partner anatomy).

Consumes the committed engines byte-untouched (md5-pinned, same pins as the
note): rmengine_pe_reimpl (Eng), wmultdcx_stress (roster/anchors/pools),
wmultdcx_derive_checks (q_quanta/greedy_chains/inv_checks/cellsum),
empty_derive_checks (walk + FRESH_ROSTER + split_checked).

Phases:
  A  HAND-AUDIT DUMP: re-trace W3DEEPF[663,667], W3DEEP[663,667],
     EQ3T3F[831,835]; print every raw bottom-stratum cell in full (sign,
     coefficient, w0, normalized residue, correction edges, profile) plus
     the netted sum — the by-hand re-derivation display for the report.
  B  FRESH COLLISION CENSUS: the frozen EQ roster at RAISED caps (12 at
     m = 3, 6 at m = 4; the committed run used 6/3 — every extra row is
     fresh) + a NEW 8-tower PX roster: char-3 Fpt twins of both committed
     cancellation shapes, p = 2 Zp twins (residue char 2 in MIXED
     characteristic), Fpt p = 2 twins of the other collision-carrying
     sealed shapes (W3DEEP4/W3TRK1/W4DEEP/EQ3FLT reads).  Census EVERY
     same-slot equal-line group in the full two-exit multiset.
  C  PARTNER ANATOMY: every cell group sharing the cascade cell's slot;
     for equal-line partners record junk/ncorr and test the S-L4(iii)
     resonance sum sum(pi_l q_l) == sum(c_l q_l); ALSO census same-slot
     equal-line groups with MIXED junk values anywhere (a mixed group
     would concretely refute the "junk gains strictly positive => equal-
     line partner junk-free" forcing argument).

Violation families (each backs a PROVED lemma of the note, on fresh rows):
  PX-PIN    consumed engine md5s match the note pins.
  PX-CONS   stage sums reassemble E1IH / Q1 per traced row.
  PX-DIGIT  w_m(cell) == line(cell) on every two-exit cell (S-L0(c)).
  PX-SEP    w_m(Q1) >= beta_min always; == on unique-netted-bottom rows
            (S-L2), and == whenever the netted bottom is nonempty and all
            bottom cells are top-reduced (S-L3 instance form).
  PX-CASC   S-L1's clauses on all-g=1 (STK) live rows (fresh rows too).
  PX-LINE   W-D5 line law (junk-free exact, junk strictly above).
  HARNESS   violations raised inside consumed engines.
Measured censuses (no prediction): CANCHUNT / EQLGRP / PRT / MIXJUNK.

Deterministic, exact arithmetic, no sampling.
Usage: python3 surv_pe1_ext.py [outdir]
"""
import sys, os, time, json, hashlib

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
}

CANCHUNT = []      # cancellation instances found (bottom slot netted dead)
EQLGRP   = []      # same-slot equal-line groups, n >= 2
PRT      = []      # cascade-slot partner records
MIXJUNK  = []      # same-slot equal-line groups with mixed junk values

def trace_full(E, sA, sB, u1a, u1b, aA, aB, su, cs, Dd, kdef, key, prin,
               tag, p, kind, g0, dump=False):
    """One row, full-cell retention + censuses.  Returns row record or None."""
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
        viol("PX-CONS", tag, f"stage-1 sum != E1IH at {key}")
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
        viol("PX-CONS", tag, f"stage-2 sum != Q1 at {key}")
    harvest(tag)
    ctop = cs[-1] if cs else 0
    if kdef > ctop or not q2sink:
        return None                       # dead / empty: out of scope here
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
            viol("PX-DIGIT", tag, f"w_m(cell) != line at {key}: j={j}")
        floor = lamhat + sum(pc[l - 1] * q[l] for l in range(1, m))
        if junk == 0 and ln != floor:
            viol("PX-LINE", tag, f"junk-free off line at {key}")
        if junk > 0 and ln <= floor:
            viol("PX-LINE", tag, f"junk not above floor at {key}")
        cells.append(dict(sgn=sgn, b=b, j=j, pc=pc, ncorr=ncorr, junk=junk,
                          jD=jD, prin=isp, ce=ce, y2=y2, line=ln,
                          qsum=sum(pc[l - 1] * q[l] for l in range(1, m))))
    # cascade cell
    casc = [c for c in cells if c["ce"] == () and c["junk"] == 0
            and c["prin"] and c["y2"] == 0]
    casc_rec = casc[0] if len(casc) == 1 else None
    if allg1 and stk:
        if len(casc) != 1:
            viol("PX-CASC", tag, f"cascade count {len(casc)} != 1 at {key}")
        else:
            c = casc[0]
            cprin = next(cD for (cD, jD) in E.Dcells if tuple(jD) == prin)
            if (list(c["pc"][:m - 1]) != list(cs) or c["ncorr"][m - 1] != 0
                    or c["pc"][m - 1] != 2 or c["j"][m - 1] != ctop - kdef
                    or list(c["j"][:m - 1]) != rho
                    or c["line"] != lamhat + sum(cs[l-1]*q[l] for l in range(1, m))
                    or w0(R, c["b"]) != (u1a + u1b) + w0(R, cprin)):
                viol("PX-CASC", tag, f"S-L1 clause fails at {key}")
            want = E.kmul(E.resKm(b0), E.resKm(cprin))
            if E.kisz(want) or not E.keq(E.resKm(c["b"]), want):
                viol("PX-CASC", tag, f"S-L1 residue fails at {key}")
            note("px_casc_ok")
    # ---- censuses ----
    beta_min = min(c["line"] for c in cells)
    csum = sum(cs[l - 1] * q[l] for l in range(1, m))
    # same-slot equal-line groups over the FULL multiset
    gl = {}
    for c in cells:
        gl.setdefault((c["j"], c["line"]), []).append(c)
    for (jv, ln), grp in sorted(gl.items(), key=lambda kv: kv[0][1]):
        if len(grp) < 2: continue
        acc = []
        for c in grp:
            acc = padd(R, acc, c["b"] if c["sgn"] > 0 else pneg(R, c["b"]))
        acc = pnorm(R, acc)
        killed = (not acc) or E.line(acc, jv) != ln
        junks = sorted(set(c["junk"] for c in grp))
        res_equal = all(E.keq(E.resKm(grp[0]["b"]), E.resKm(c["b"]))
                        for c in grp[1:])
        sgns = sorted(c["sgn"] for c in grp)
        rec = dict(tower=tag, key=list(key), p=p, kind=kind, g0=g0,
                   slot=list(jv), line=ln, n=len(grp), junks=junks,
                   ncorr=sorted(set(sum(c["ncorr"]) for c in grp)),
                   sgns=sgns, res_equal=bool(res_equal), killed=bool(killed),
                   at_bottom=(ln == beta_min),
                   at_casc_slot=bool(casc_rec and jv == casc_rec["j"]))
        EQLGRP.append(rec)
        if len(junks) > 1:
            MIXJUNK.append(rec)
        if killed and ln == beta_min:
            note("canc_bottom_group")
    # netted bottom + full netted spectrum
    slots = {}
    for c in cells:
        slots.setdefault(c["j"], []).append(c)
    spec = []
    for jv, grp in slots.items():
        acc = []
        for c in grp:
            acc = padd(R, acc, c["b"] if c["sgn"] > 0 else pneg(R, c["b"]))
        acc = pnorm(R, acc)
        if acc:
            spec.append((E.line(acc, jv), jv, len(grp), acc))
    spec.sort(key=lambda t: t[0])
    net_bottom = [s for s in spec if s[0] == beta_min]
    wq = E.wm(Q1c) if pnorm(R, Q1c) else None
    if wq is None:
        viol("PX-SEP", tag, f"live row with Q1 == 0 at {key}"); return None
    if wq < beta_min:
        viol("PX-SEP", tag, f"w_m(Q1) < beta_min at {key}")
    if len(net_bottom) == 1 and wq != beta_min:
        viol("PX-SEP", tag, f"unique netted bottom but w_m != beta at {key}")
    topred = all(c["j"][m - 1] <= E.P[m - 1] - 1
                 for c in cells if c["line"] == beta_min)
    if net_bottom and topred and wq != beta_min:
        viol("PX-SEP", tag, f"S-L3 shadow fails at {key}")
    if wq > beta_min:
        CANCHUNT.append(dict(
            tower=tag, key=list(key), p=p, kind=kind, g0=g0, cs=list(cs),
            D=Dd, kdef=kdef, beta_min=beta_min, wmQ1=wq,
            raw_bottom=[(list(c["j"]), c["sgn"], sum(c["ncorr"]), c["junk"])
                        for c in cells if c["line"] == beta_min],
            surv_head=[(s[0], list(s[1]), s[2]) for s in spec[:3]],
            surv_is_casc_slot=bool(spec and casc_rec is not None
                                   and spec[0][1] == casc_rec["j"]
                                   and spec[0][0] == casc_rec["line"])))
        print(f"  CANCHUNT [{tag}{list(key)} p={p} {kind} g0={g0}]: bottom "
              f"beta_min={beta_min} DEAD; w_m(Q1)={wq}; head="
              f"{[(s[0], list(s[1]), s[2]) for s in spec[:2]]}")
    # cascade-slot partner census
    if casc_rec is not None:
        grp = slots.get(casc_rec["j"], [])
        if len(grp) > 1:
            for c in grp:
                if c is casc_rec: continue
                PRT.append(dict(
                    tower=tag, key=list(key), p=p, g0=g0,
                    eql=(c["line"] == casc_rec["line"]),
                    dline=c["line"] - casc_rec["line"], junk=c["junk"],
                    ncorr=sum(c["ncorr"]), r=c["ncorr"][m - 1],
                    prin=c["prin"], y2=c["y2"],
                    resonance=(c["qsum"] == csum)))
            note("prt_rows")
    # hand-audit dump
    if dump:
        print(f"\n== HAND-AUDIT {tag}{list(key)}  p={p} {kind} g0={g0} "
              f"cs={list(cs)} D={Dd} k={kdef}  beta_min={beta_min} "
              f"w_m(Q1)={wq}  lamhat={lamhat} csum={csum}")
        for c in cells:
            if c["line"] != beta_min: continue
            print(f"   RAW BOTTOM cell: slot={list(c['j'])} sgn={c['sgn']:+d} "
                  f"profile={list(c['pc'])} ncorr={list(c['ncorr'])} "
                  f"junk={c['junk']} y2={c['y2']} ce={c['ce']} "
                  f"jD={list(c['jD'])} prin={c['prin']}")
            print(f"     coeff b = {c['b']}  w0={w0(R, c['b'])} "
                  f"res = {E.resKm(c['b'])}")
        for jv, grpc in slots.items():
            if all(c["line"] != beta_min for c in grpc): continue
            acc = []
            for c in grpc:
                acc = padd(R, acc, c["b"] if c["sgn"] > 0 else pneg(R, c["b"]))
            acc = pnorm(R, acc)
            print(f"   NET at slot {list(jv)}: {'ZERO' if not acc else acc}"
                  f"{'' if not acc else '  line=' + str(E.line(acc, jv))}")
        print(f"   netted spectrum head: "
              f"{[(s[0], list(s[1]), s[2]) for s in spec[:4]]}")
        if casc_rec is not None:
            print(f"   cascade cell: slot={list(casc_rec['j'])} "
                  f"line={casc_rec['line']} res={E.resKm(casc_rec['b'])}")
    return dict(live=True, wq=wq, beta=beta_min)

# ---------------- row enumeration (fresh-style, capped per stratum) ---------
def run_tower(spec, cap3, cap4, only_keys=None, dump=False):
    tag, m, kind, p, d0, reads = spec
    t0 = time.time()
    try:
        E = PE.Eng(m, kind, p, d0, reads, tag)
        PE.prep(E)
    except Exception as ex:
        print(f"-- {tag}: ENGINE UNSUPPORTED ({ex!r}) — disclosed, skipped")
        note("tower_skipped"); return
    harvest(tag)
    u, su = WS.uchain(E)
    if u is None:
        print(f"-- {tag}: u-chain failed — disclosed, skipped")
        note("tower_skipped"); return
    Etot, G0, split = WS.window_split(E)
    anch = WS.anchors_of(E, Etot, G0, split)
    etop = E.e[m - 1]
    prin, _ = WD.inv_checks(E, u, su)
    harvest(tag)
    R = E.R
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
            if only_keys is not None and (ga, gb) not in only_keys: continue
            live_pool.setdefault((kdef, ctop), []).append(
                (ga, gb, cs, Dd, kdef, sA, sB, u1a, u1b))
    cap = (cap4 if m >= 4 else cap3) if only_keys is None else 10**9
    nl = 0
    for stratum in sorted(live_pool):
        for row in live_pool[stratum][:cap]:
            ga, gb, cs, Dd, kdef, sA, sB, u1a, u1b = row
            r = trace_full(E, sA, sB, u1a, u1b, anch[ga][0], anch[gb][0], su,
                           cs, Dd, kdef, (ga, gb), prin, tag, p, kind,
                           E.g[0], dump=dump)
            if r: nl += 1
    print(f"-- {tag} m={m} {kind},p={p},d0={d0} g0={E.g[0]}: live traced={nl} "
          f"({time.time()-t0:.1f}s)")
    note("live_rows", nl)

PX_ROSTER = [
    # char-3 equal-characteristic twins of BOTH committed cancellation shapes
    ("PXDEEPF3", 3, "Fpt", 3, 1, [(3,2,1), (2,1,1), (2,1,1), (2,1,1)]),
    ("PXT3F3",   3, "Fpt", 3, 1, [(3,1,1), (2,1,1), (3,2,1), (2,1,1)]),
    # residue-characteristic-2 MIXED-characteristic twins (Zp, p = 2)
    ("PXDEEPZ2", 3, "Zp", 2, 1, [(3,2,1), (2,1,1), (2,1,1), (2,1,1)]),
    ("PXT3Z2",   3, "Zp", 2, 1, [(3,1,1), (2,1,1), (3,2,1), (2,1,1)]),
    # p = 2 Fpt twins of the OTHER collision-carrying sealed shapes
    ("PXDEEP4F", 3, "Fpt", 2, 1, [(4,3,1), (2,1,1), (2,3,1), (2,1,1)]),
    ("PXTRK1F",  3, "Fpt", 2, 1, [(3,2,1), (2,1,1), (2,1,1), (1,1,1)]),
    ("PXFLTF",   3, "Fpt", 2, 1, [(3,1,1), (1,1,1), (2,1,1), (2,1,1)]),
    ("PXW4DPF",  4, "Fpt", 2, 1, [(3,1,1), (2,1,1), (2,1,1), (2,1,1), (2,1,1)]),
]

def main():
    t0 = time.time()
    for fn, want in PINS.items():
        got = hashlib.md5(open(os.path.join(HERE, fn), "rb").read()).hexdigest()
        if got != want:
            viol("PX-PIN", fn, f"md5 {got} != pinned {want}")
    print("=" * 78)
    print("PHASE A — hand-audit dumps (the two committed kills + p=3 witness)")
    print("=" * 78)
    spec_by_tag = {s[0]: s for s in list(WS.ROSTER) + list(ED.FRESH_ROSTER)}
    for tag, key in (("W3DEEPF", (663, 667)), ("W3DEEP", (663, 667)),
                     ("EQ3T3F", (831, 835))):
        run_tower(spec_by_tag[tag], 0, 0, only_keys={key}, dump=True)
    print("=" * 78)
    print("PHASE B — EQ roster, RAISED caps (12/6; committed run used 6/3)")
    print("=" * 78)
    for spec in ED.FRESH_ROSTER:
        run_tower(spec, 12, 6)
    print("=" * 78)
    print("PHASE B' — the NEW PX roster (char-3 / mixed-char-2 / p=2 twins)")
    print("=" * 78)
    for spec in PX_ROSTER:
        run_tower(spec, 12, 6)
    print("=" * 78)
    fams = ["PX-PIN", "PX-CONS", "PX-DIGIT", "PX-LINE", "PX-CASC", "PX-SEP",
            "HARNESS"]
    for f in fams:
        print(f"{f:10s}: {sum(1 for v in VIOL if v[0] == f)} violations")
    print("-" * 78)
    live = CNT.get("live_rows", 0)
    print(f"live rows traced: {live}; S-L1 machine-verified on "
          f"{CNT.get('px_casc_ok', 0)} all-g=1 (STK) rows")
    print(f"CANCHUNT — cancellation instances (netted bottom DEAD): "
          f"{len(CANCHUNT)}")
    for c in CANCHUNT:
        print(f"  {c['tower']}{c['key']} p={c['p']} {c['kind']} g0={c['g0']} "
              f"cs={c['cs']} D={c['D']} k={c['kdef']} raw_bottom="
              f"{c['raw_bottom']} surv_is_casc_slot={c['surv_is_casc_slot']}")
    bott = [g for g in EQLGRP if g["at_bottom"]]
    print(f"EQLGRP — same-slot equal-line groups (n >= 2) in full multisets: "
          f"{len(EQLGRP)} ({len(bott)} at the bottom line)")
    import collections
    byp = collections.Counter((g["p"], g["kind"], g["killed"]) for g in bott)
    print("  bottom groups by (p, kind, killed):", dict(byp))
    req = collections.Counter((g["res_equal"], g["killed"]) for g in bott)
    print("  bottom groups by (res_equal, killed):", dict(req))
    print(f"MIXJUNK — equal-line same-slot groups with MIXED junk: "
          f"{len(MIXJUNK)}")
    for g in MIXJUNK[:10]:
        print(f"  {g['tower']}{g['key']} slot={g['slot']} line={g['line']} "
              f"junks={g['junks']} ncorr={g['ncorr']} at_casc={g['at_casc_slot']}")
    eqp = [r for r in PRT if r["eql"]]
    print(f"PRT — cascade-slot partners: {len(PRT)} total, {len(eqp)} "
          f"equal-line; equal-line junk/resonance profile:")
    prof = collections.Counter((r["junk"], r["resonance"], r["ncorr"] > 0,
                                r["prin"]) for r in eqp)
    print("  (junk, resonance, has_corr, principal):", dict(prof))
    g1p = [r for r in PRT if r["g0"] == 1]
    print(f"  partners on g0=1 rows: {len(g1p)}")
    print(f"total violations: {len(VIOL)}")
    print(f"elapsed: {time.time()-t0:.1f}s")
    out = dict(violations=VIOL, counters=CNT, canchunt=CANCHUNT,
               eqlgrp=EQLGRP, mixjunk=MIXJUNK, prt=PRT,
               elapsed=time.time() - t0)
    with open(os.path.join(OUTDIR, "surv_pe1_ext_results.json"), "w") as f:
        json.dump(out, f, indent=1, default=str)
    print("results ->", os.path.join(OUTDIR, "surv_pe1_ext_results.json"))

if __name__ == "__main__":
    main()
