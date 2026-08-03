#!/usr/bin/env python3
"""l3ramps_m3.py — M3: DEGENERATION LADDER + ONE-PARAMETER RAMPS.

POST-SEAL DIAGNOSTIC, NOT PREREGISTERED.  The sealed prereg
(ITERLAWR_PROBE_2026-08-08.md S0-S4 + iterlawr_probe.py, seal 911431c) is
consumed READ-ONLY; nothing here amends it.  Note of record:
lean/notes/openmath/L3RAMPS_M3_2026-08-08.md.

CONTEXT (M3's own artifact read, decorrelated): the sealed battery's exit-1
("RED") shows violations == [] and every law family GREEN (G3 = 0/13440);
the only failed row is MUTATION m4 "detected 0" — a battery-teeth failure
(the m4-mutated form never separated on the mutation sub-battery), not a law
failure.  This script therefore treats the sealed composed form as the
MEASURED LAW (conjecture status unchanged) and asks a different question:

  factorize the CORRECTION TERM — the difference between the measured level-3
  cocycle and the naive per-level lift of the ACCEPTED order-2 law — by which
  tower parameters it needs, via (1) a degeneration ladder (e2=1 / e1=1 /
  e0=1 / doubles / g-ladder) on exhaustive tiny towers and (2) one-parameter
  ramps with exact first differences (slopes + floor/carry breakpoints).

TWO MEASUREMENT LEGS per pair (gamma, gamma'):
  * FIELD leg: c3 = val3(phi_g phi_g')/val3(phi_{g+g'}) via the sealed
    harness (Composite3); compared against composed / naive monomials.
  * INTEGER leg (law-free): the realized inner shifts read off the split
    chain itself, Sig2m := b2(g+g') - b2(g) - b2(g'), Sig1m := b1(g+g') -
    b1(g) - b1(g').  No closed form is assumed in these; the sealed law's
    claims about them (Sig2m = d3*gamma3; Sig1m = Sig) are CHECKED.

CORRECTION-TERM DECOMPOSITION under test (Delta := Sig1m - gamma2*d2):
    Delta = gamma2*J + d3*gamma3*kappa,   J := D2 - d2,
    kappa := l1p - l1*w1Phi1   (tower constant),
and the observable z1-exponent correction D1 - D1naive = l0*Delta/e0
(both-integral case) resp. naive nonintegrality iff e0 does not divide
l0*Delta + (composed numerator).

Deterministic: seed 20260803 (fresh, decorrelated from the sealed 20260903).
Exit 0 iff all STRUCTURAL identities hold (composed form field-exact,
Sig2m/residual identities, F0a level-2 fidelity, certs, e2=1 two-way
level-2 recovery, M5 cross-harness ties); separation counts are REPORTS.
"""
import sys, os, json, math, time, random

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import iterlawr_probe as IP                       # sealed runner (read-only reuse)
from iterlawr_probe import Composite3, closed_form2
import grb_order2_check as G
from grb_order2_check import eq12, bezout
from strata3_probe import Tower3
import strata_probe as SP

OUTLINES = []
def log(s=""):
    print(s); OUTLINES.append(str(s))

STRUCT_BAD = []          # structural-identity failures (exit-code relevant)
def sbad(tag, what):
    STRUCT_BAD.append((tag, what)); log(f"  !! STRUCT {tag}: {what}")

def zpow(K, z, n):
    return K["pow"](z, n)                         # pow reduces mod q-1 (negatives OK)

def letter_order(K, z, cap=100000):
    o, y = 1, z
    while y != K["one"] and o < cap:
        y = K["mul"](y, z); o += 1
    return o if y == K["one"] else None

def tower_consts(T3):
    T = T3.T
    kap = T.l1p - T.l1*T.w1Phi1
    return dict(e0=T.e0, h0=T.h0, g0=T.g0, e1=T.e1, h1=T.h1, g1=T.g1,
                e2=T3.e2, h2=T3.h2, g2=T3.g2, E3=T3.E3, gamma2=T.gamma2,
                gamma3=T3.gamma3, w1P=T.w1Phi1, w2P=T.w2Phi2,
                l0=T.l0, l0p=T.l0p, l1=T.l1, l1p=T.l1p,
                kappa=kap, TB=T3.gamma3*kap)

# ---------------------------------------------------------------------------
def probe_tower(kind, p, r0, r1, r2, name, d0=1, pari=None, want_rows=False):
    """Build tower, run certs, measure all W1xW1 pairs on both legs."""
    tag = f"{kind},p={p},{name}"
    T3 = Tower3(kind, p, d0, r0, r1, r2, tag)
    T = T3.T
    C = Composite3(T3)
    K3 = C.K3
    cst0 = tower_consts(T3)
    E3, G0 = T3.E3, C.Gamma0
    W1 = list(range(G0, G0 + E3))
    ords = dict(zb=letter_order(K3, C.zbar), z2=letter_order(K3, C.z2_3),
                z1=letter_order(K3, C.z1_3))
    # certs (sealed families re-run on this tower)
    gv0, iv0 = len(G.VIOL), len(IP.VIOL)
    G.T1_T2(T, nf=4); G.T5(T)
    IP.cert3_internal(T3)
    if pari is not None and kind == "Zp":
        IP.cert3_pari(T3, pari)
    certbad = (len(G.VIOL) - gv0) + (len(IP.VIOL) - iv0)
    if certbad: sbad(tag, f"{certbad} cert violations")
    # F0a: accepted order-2 law on the level-2 subtower (harness fidelity)
    C2 = SP.Composite(T)
    f0bad = 0
    W2l = list(range(C2.Gamma0, C2.Gamma0 + T.E2))
    for ga in W2l:
        for gb in W2l:
            c2m, _ = C2.cocycle(ga, gb)
            cf2, _ = closed_form2(C2, ga, gb)
            if cf2 is None or c2m != cf2: f0bad += 1
    if f0bad: sbad(tag, f"F0a level-2 fidelity fails on {f0bad} pairs")
    agg = dict(tag=tag, name=name, kind=kind, p=p, consts=cst0, ords=ords,
               Gamma0=G0, certbad=certbad, f0bad=f0bad, npairs=0, nd3=0,
               comp_bad=0, nonint=0, intdiff=0, fdiff=0, sig2_bad=0,
               resid_bad=0, J0_bad=0, fac_bad=0, kset=set(), Jset=set(),
               Dset=set(), rows=[])
    for ga in W1:
        for gb in W1:
            cst = C.constants(ga, gb)
            d3, d2 = cst["d3"], cst["d2"]
            D2, D1, D1n = cst["D2"], cst["D1"], cst["D1n"]
            _, _, _, b2a, b1a, _ = C.split(ga)
            _, _, _, b2b, b1b, _ = C.split(gb)
            s3a, s2a, s1a = C.split(ga)[:3]
            s3b, s2b, s1b = C.split(gb)[:3]
            s3c, s2c, s1c, b2c, b1c, _ = C.split(ga + gb)
            Sig2m = b2c - b2a - b2b                # measured, law-free
            Sig1m = b1c - b1a - b1b                # measured, law-free
            Delta = Sig1m - T.gamma2*d2            # the correction term
            J = None if D2 is None else D2 - d2
            agg["npairs"] += 1
            if d3 == 1: agg["nd3"] += 1
            if Sig2m != d3*T3.gamma3:
                agg["sig2_bad"] += 1; sbad(tag, f"Sig2m at ({ga},{gb})")
            if J is not None:
                resid = Delta - T.gamma2*J - d3*cst0["TB"]
                if resid != 0:
                    agg["resid_bad"] += 1; sbad(tag, f"resid at ({ga},{gb})")
                if d3 == 0 and J != 0:
                    agg["J0_bad"] += 1; sbad(tag, f"J!=0 at d3=0 ({ga},{gb})")
                if d3 == 1:
                    agg["kset"].add(Delta - T.gamma2*J)
                    agg["Jset"].add(J)
                agg["Dset"].add(Delta)
            # field leg
            cval = C.cocycle(ga, gb)[0]
            lawv = C.law_value(cst, "primary")
            nv = C.law_value(cst, "naive")
            if lawv is None or cval != lawv:
                agg["comp_bad"] += 1; sbad(tag, f"composed law at ({ga},{gb})")
            sep = "-"
            if nv is None:
                agg["nonint"] += 1; sep = "NI"
            else:
                if D1n != D1:
                    agg["intdiff"] += 1; sep = "ID"
                if cval != nv:
                    agg["fdiff"] += 1
                    sep = sep + "+FD" if sep != "-" else "FD"
                    fac = K3["mul"](cval, K3["inv"](nv))
                    if fac != zpow(K3, C.z1_3, D1 - D1n):
                        agg["fac_bad"] += 1
                        sbad(tag, f"discrepancy factor not z1^(D1-D1n) at ({ga},{gb})")
            if want_rows:
                agg["rows"].append((ga-G0, gb-G0, s3a, s3b, d3, s2a, s2b, s2c,
                                    s1a, s1b, s1c, Sig2m, Sig1m, Delta,
                                    (J if J is not None else "*"), D2, D1,
                                    ("NI" if D1n is None else D1n), sep))
    # e2 = 1 towers: TWO-WAY level-2 recovery
    if T3.e2 == 1:
        w1bad = w2bad = idbad = 0
        for g in W1 + [W1[0] + W1[-1]]:
            sp3 = C.split(g)
            sp2 = C2.split(g)
            if not (sp3[0] == 0 and sp3[3] == g and (sp3[1], sp3[2]) == (sp2[0], sp2[1])):
                idbad += 1
        for ga in W1:
            for gb in W1:
                cval = C.cocycle(ga, gb)[0]
                c2m, _ = C2.cocycle(ga, gb)
                if cval != K3["embed"](c2m): w1bad += 1
                cf2, _ = closed_form2(C2, ga, gb)
                if cf2 is None or cval != K3["embed"](cf2): w2bad += 1
        agg["recovery"] = dict(split_id_bad=idbad, meas_tie_bad=w1bad,
                               law_tie_bad=w2bad)
        if idbad or w1bad or w2bad:
            sbad(tag, f"e2=1 recovery: id={idbad} meas={w1bad} law={w2bad}")
    agg["kset"] = sorted(agg["kset"]); agg["Jset"] = sorted(agg["Jset"])
    agg["Dset"] = sorted(agg["Dset"])
    return T3, C, agg

def fmt_agg_row(a):
    c = a["consts"]
    km = (a["kset"][0] if len(a["kset"]) == 1 else
          ("none" if not a["kset"] else f"NONCONST{a['kset']}"))
    return (f"{a['name']:8} {c['e0']}{c['e1']}{c['e2']} E3={c['E3']:>2} "
            f"g={c['g0']}{c['g1']}{c['g2']} | g2c={c['gamma2']:>3} g3c={c['gamma3']:>4} "
            f"l0={c['l0']} l1={c['l1']} kap={c['kappa']:>4} TB={c['TB']:>5} | "
            f"prs={a['npairs']:>3} d3+={a['nd3']:>3} NI={a['nonint']:>3} "
            f"ID={a['intdiff']:>3} FD={a['fdiff']:>3} | gJK={km:>5} "
            f"J{a['Jset']} | cmp0={a['comp_bad']} s2id0={a['sig2_bad']} "
            f"r0={a['resid_bad']}")

def print_pair_table(a):
    c = a["consts"]
    log(f"\n  PAIR TABLE {a['tag']}  (e,h,g)x3 = "
        f"({c['e0']},{c['h0']},{c['g0']})({c['e1']},{c['h1']},{c['g1']})"
        f"({c['e2']},{c['h2']},{c['g2']})  E3={c['E3']} Gamma0={a['Gamma0']} "
        f"gamma2={c['gamma2']} gamma3={c['gamma3']} w1P={c['w1P']} "
        f"l0={c['l0']} l1={c['l1']} l1p={c['l1p']} kappa={c['kappa']} "
        f"ord(zb,z2,z1)=({a['ords']['zb']},{a['ords']['z2']},{a['ords']['z1']})")
    log(f"  {'r':>2} {'rp':>2} | s3 s3p d3 | s2 s2p s2s | s1 s1p s1s |"
        f" {'S2m':>4} {'S1m':>4} {'Dlt':>4} {'J':>3} | {'D2':>3} {'D1':>3} "
        f"{'D1n':>3} | sep")
    for r in a["rows"]:
        (ra, rb, s3a, s3b, d3, s2a, s2b, s2c, s1a, s1b, s1c,
         S2m, S1m, Dl, J, D2, D1, D1n, sep) = r
        log(f"  {ra:>2} {rb:>2} |  {s3a}   {s3b}  {d3} |  {s2a}   {s2b}   {s2c} |"
            f"  {s1a}   {s1b}   {s1c} | {S2m:>4} {S1m:>4} {Dl:>4} {J!s:>3} |"
            f" {D2!s:>3} {D1!s:>3} {D1n!s:>3} | {sep}")

# ---------------------------------------------------------------------------
def gamma_scan(C, T3, label):
    """Within-tower breakpoint loci: fix gamma = Gamma0, ramp gamma'."""
    T = T3.T
    G0, E3 = C.Gamma0, T3.E3
    # anchor at the first window gamma with TOP split s3 = e2-1 (G0 itself is
    # a multiple of E3, hence s3 = 0 there and the top carry would never fire)
    ga = next(g for g in range(G0, G0 + E3) if C.split(g)[0] == T3.e2 - 1)
    log(f"\n  GAMMA'-SCAN {label}: gamma={ga} fixed (s3={T3.e2-1}), "
        f"gamma'={G0}..{G0+2*E3-1}  (first differences in brackets; * marks "
        f"d3-flip rows)")
    log(f"  {'rp':>3} | s3p d3 | {'S1m':>4} {'Dlt':>4} {'D2':>3} {'D1':>4} {'D1n':>4} | diffs d(S1m) d(D1)")
    prev = None
    loci = []
    for gb in range(G0, G0 + 2*E3):
        cst = C.constants(ga, gb)
        s3b = C.split(gb)[0]
        b1a = C.split(ga)[4]; b1b = C.split(gb)[4]; b1c = C.split(ga+gb)[4]
        S1m = b1c - b1a - b1b
        Dl = S1m - T.gamma2*cst["d2"]
        row = (s3b, cst["d3"], S1m, Dl, cst["D2"], cst["D1"], cst["D1n"])
        if prev is None:
            log(f"  {gb-G0:>3} |  {s3b}   {cst['d3']} | {S1m:>4} {Dl:>4} "
                f"{cst['D2']!s:>3} {cst['D1']!s:>4} {cst['D1n']!s:>4} |")
        else:
            dS = S1m - prev[2]
            dD1 = (cst["D1"] - prev[5]) if (cst["D1"] is not None and prev[5] is not None) else "*"
            mark = "*" if (prev[1] != cst["d3"]) else " "
            if mark == "*": loci.append(gb - G0)
            log(f"  {gb-G0:>3} |  {s3b}   {cst['d3']} | {S1m:>4} {Dl:>4} "
                f"{cst['D2']!s:>3} {cst['D1']!s:>4} {cst['D1n']!s:>4} | "
                f"[{dS:>3} {dD1!s:>3}] {mark}")
        prev = row
    log(f"  d3-flip loci (offsets where d3 changes vs previous row): {loci}")
    return loci

# ---------------------------------------------------------------------------
def m5_crosscheck(specs, my_data):
    """M5 cross-harness tie: my integer exponents drive M5's independent
    field measurement (level3_xcheck harness, own psi choices)."""
    import level3_xcheck as M5X
    log("\n" + "="*78)
    log("M5 CROSS-HARNESS SPOT-CHECK (level3_xcheck: independent fields/psi)")
    log("  tie: M5-measured c3 == z3^d3 z2^D2 z1^D1 with (d3,D2,D1) from the")
    log("  SEALED-harness integer leg at the SAME (gamma,gamma'); plus s-chain id")
    allbad = 0
    for name, ringname, p, espec, prs in specs:
        T5 = M5X.build_tower(ringname, p, espec)
        KN = T5.K[T5.N]
        z3, z2, z1 = T5.embed_letter(3), T5.embed_letter(2), T5.embed_letter(1)
        C = my_data[name][1]
        schain_bad = tie_bad = sep_seen = 0
        for (ga, gb) in prs:
            cst = C.constants(ga, gb)
            c5, diag = T5.cocycle(ga, gb)
            dA = diag["d1"]
            mine = C.split(ga)[:3]
            if (dA["s"][3], dA["s"][2], dA["s"][1]) != mine:
                schain_bad += 1
            pred = KN.mul(KN.ppow(z3, cst["d3"]),
                          KN.mul(KN.ppow(z2, cst["D2"]), KN.ppow(z1, cst["D1"])))
            if c5 != pred:
                tie_bad += 1
            # naive-side cross-report: where naive is integral but different,
            # does M5's independent field also separate the two monomials?
            if cst["D1n"] is not None and cst["D1n"] != cst["D1"]:
                nvd = KN.mul(KN.ppow(z3, cst["d3"]),
                             KN.mul(KN.ppow(z2, cst["D2"]), KN.ppow(z1, cst["D1n"])))
                if nvd != c5:
                    sep_seen += 1
        log(f"  {name}: pairs={len(prs)} schain_bad={schain_bad} "
            f"tie_bad={tie_bad} naive-field-sep-seen={sep_seen}")
        if schain_bad or tie_bad:
            sbad(f"M5,{name}", f"schain={schain_bad} tie={tie_bad}")
            allbad += schain_bad + tie_bad
    return allbad

# ---------------------------------------------------------------------------
def main():
    t0 = time.time()
    random.seed(20260803)
    sys.path.insert(0, os.path.expanduser('~/.local/lib/python3.10/site-packages'))
    try:
        import cypari2
        pari = cypari2.Pari(); pari.allocatemem(1 << 28, silent=True)
    except Exception as exc:
        pari = None
        log(f"WARNING: cypari2 unavailable ({exc}); PARI certs skipped")
    log("M3 DEGENERATION LADDER + RAMPS — post-seal diagnostic, seed 20260803")
    log(f"sealed artifacts read-only; own artifact read of the RED verdict:")
    with open(os.path.join(HERE, "iterlawr_probe_results.json")) as fh:
        sealed = json.load(fh)
    log(f"  sealed violations={len(sealed['violations'])} "
        f"m4_detected={sealed['mutations']['detected']['m4']} "
        f"harness_events={len(sealed['harness_events'])} "
        f"=> RED = m4-teeth-only (concur, from raw artifacts)")
    results = dict(ladder=[], ramps={}, scans={}, m5=None)

    # ================= PART A: THE DEGENERATION LADDER =================
    LADDER = [
        # name,      r0,      r1,      r2       (d0=1 throughout)
        ("FULL8",  (2,1,1), (2,1,1), (2,1,1)),
        ("FULLg0", (2,1,2), (2,1,1), (2,1,1)),
        ("FULLg1", (2,1,1), (2,1,2), (2,1,1)),
        ("FULLg2", (2,1,1), (2,1,1), (2,1,2)),
        ("De2a",   (2,1,1), (2,1,1), (1,1,2)),
        ("De2b",   (2,1,1), (3,1,1), (1,1,2)),
        ("De2c",   (3,2,1), (2,1,1), (1,1,2)),
        ("De2g0",  (2,1,2), (2,1,1), (1,1,2)),
        ("De1a",   (2,1,1), (1,1,2), (2,1,1)),
        ("De1b",   (3,1,1), (1,1,2), (2,1,1)),
        ("De1c",   (2,1,1), (1,1,2), (3,1,1)),
        ("De0a",   (1,1,2), (2,1,1), (2,1,1)),
        ("De0b",   (1,1,2), (2,1,1), (3,1,1)),
        ("De0c",   (1,1,2), (3,1,1), (2,1,1)),
        ("De0e1",  (1,1,2), (1,1,2), (4,3,1)),
        ("De0e2",  (1,1,2), (4,3,1), (1,1,2)),
        ("De1e2",  (4,3,1), (1,1,2), (1,1,2)),
    ]
    CONFIGS = [("Zp", 2), ("Zp", 3), ("Fpt", 2), ("Fpt", 3)]
    ladder_data = {}
    log("\n" + "="*78)
    log("PART A: DEGENERATION LADDER — exhaustive W1xW1 per tower, 4 ring configs")
    log("  cols: NI naive-nonintegral | ID both-integral D1!=D1n | FD field diff")
    log("  gJK = Delta - gamma2*J on d3=1 pairs (must be the CONSTANT gamma3*kappa)")
    for kind, p in CONFIGS:
        log(f"\n-- config ({kind}, p={p}) --")
        for name, r0, r1, r2 in LADDER:
            try:
                T3, C, a = probe_tower(kind, p, r0, r1, r2, name, pari=pari,
                                       want_rows=(p == 3 and kind == "Zp"))
            except Exception as exc:
                sbad(f"{kind},p={p},{name}", f"HARNESS EVENT {exc!r}")
                continue
            ladder_data[(kind, p, name)] = (T3, C, a)
            log("  " + fmt_agg_row(a))
            if "recovery" in a:
                r = a["recovery"]
                log(f"           e2=1 RECOVERY: split-id bad={r['split_id_bad']} "
                    f"measured-tie bad={r['meas_tie_bad']} law-tie bad={r['law_tie_bad']}")
            aa = dict(a); aa.pop("rows")
            results["ladder"].append(aa)
        log(f"  [{time.time()-t0:6.1f}s]")

    # eyeball full per-pair tables (Zp, p=3): every degenerate row + the base
    log("\n" + "="*78)
    log("PART A TABLES (Zp, p=3): full per-pair rows (eyeball; S2m/S1m are the")
    log("law-free measured shifts; Dlt = S1m - gamma2*d2 = the correction term)")
    for name in ("FULL8", "De2a", "De1a", "De0a", "De2b", "De1b", "De0b",
                 "De0e1", "De0e2", "De1e2", "FULLg2"):
        key = ("Zp", 3, name)
        if key in ladder_data:
            print_pair_table(ladder_data[key][2])

    # ================= PART B: ONE-PARAMETER RAMPS =================
    log("\n" + "="*78)
    log("PART B: ONE-PARAMETER RAMPS (Zp, p=3, d0=1) — exact first differences")
    RAMPS = {
        "e2":  [((2,1,1), (2,1,1), (e2,1,1)) for e2 in (1, 2, 3, 4)],
        "h2":  [((2,1,1), (2,1,1), (2,h2,1)) for h2 in (1, 3, 5, 7, 9)],
        "l1":  [((2,1,1), (5,h1,1), (2,1,1)) for h1 in (1, 2, 3, 4, 7)],
        "h0":  [((2,h0,1), (2,1,1), (2,1,1)) for h0 in (1, 3, 5, 7)],
        "e1":  [((2,1,1), (e1,1,1), (2,1,1)) for e1 in (1, 2, 3, 4)],
        # levels 0/1: the harness irreducible-picker (grb pick_irreducible)
        # only enumerates degrees 1-2, so g0/g1 in {1,2} IS the harness class
        "g0":  [((2,1,g0), (2,1,1), (2,1,1)) for g0 in (1, 2)],
        "g1":  [((2,1,1), (2,1,g1), (2,1,1)) for g1 in (1, 2)],
        "g2":  [((2,1,1), (2,1,1), (2,1,g2)) for g2 in (1, 2, 3)],
    }
    ramp_data = {}
    for rname, specs in RAMPS.items():
        log(f"\n-- RAMP {rname}: {len(specs)} towers --")
        rows = []
        for r0, r1, r2 in specs:
            nm = f"R{rname}_{r0}{r1}{r2}".replace(" ", "")
            try:
                T3, C, a = probe_tower("Zp", 3, r0, r1, r2, nm, pari=pari)
            except Exception as exc:
                sbad(f"Zp,p=3,{nm}", f"HARNESS EVENT {exc!r}")
                continue
            ramp_data[(rname, (r0, r1, r2))] = (T3, C, a)
            log("  " + fmt_agg_row(a))
            if "recovery" in a:
                r = a["recovery"]
                log(f"           e2=1 RECOVERY: split-id bad={r['split_id_bad']} "
                    f"measured-tie bad={r['meas_tie_bad']} law-tie bad={r['law_tie_bad']}")
            c = a["consts"]
            rows.append(dict(spec=(r0, r1, r2), gamma2=c["gamma2"],
                             gamma3=c["gamma3"], w1P=c["w1P"], w2P=c["w2P"],
                             l0=c["l0"], l1=c["l1"], l1p=c["l1p"],
                             kappa=c["kappa"], TB=c["TB"], E3=c["E3"],
                             kmeas=(a["kset"][0] if len(a["kset"]) == 1 else a["kset"]),
                             Jset=a["Jset"], nd3=a["nd3"], npairs=a["npairs"],
                             NI=a["nonint"], ID=a["intdiff"], FD=a["fdiff"],
                             comp_bad=a["comp_bad"]))
        # slope table: exact first differences of the tower-level quantities
        if len(rows) >= 2:
            log(f"  SLOPES (first differences along the {rname}-ramp):")
            keys = ("gamma2", "gamma3", "w2P", "kappa", "TB")
            for k in keys:
                vals = [r[k] for r in rows]
                difs = [vals[i+1]-vals[i] for i in range(len(vals)-1)]
                d2s = [difs[i+1]-difs[i] for i in range(len(difs)-1)]
                nc = " NONCONST" if len(set(difs)) > 1 else ""
                log(f"    {k:>6}: {vals}  d1={difs}  d2={d2s}{nc}")
            kms = [r["kmeas"] for r in rows]
            log(f"    kappa*gamma3 MEASURED (Delta-gamma2*J const on d3=1): {kms}")
        results["ramps"][rname] = rows

    # within-tower breakpoint loci
    log("\n" + "="*78)
    log("PART B2: WITHIN-TOWER BREAKPOINT LOCI (gamma'-scans)")
    for key, label in [(("e2", ((2,1,1),(2,1,1),(3,1,1))), "e2=3 ramp tower"),
                       (("l1", ((2,1,1),(5,2,1),(2,1,1))), "l1 ramp h1=2"),
                       (("e1", ((2,1,1),(3,1,1),(2,1,1))), "e1=3 ramp tower")]:
        if key in ramp_data:
            T3, C, a = ramp_data[key]
            loci = gamma_scan(C, T3, label)
            results["scans"][label] = loci

    # ================= M5 cross-harness =================
    fullC = ladder_data.get(("Zp", 3, "FULL8"))
    de1C = ladder_data.get(("Zp", 3, "De1a"))
    l1C = ramp_data.get(("l1", ((2,1,1),(5,2,1),(2,1,1))))
    specs, mydata = [], {}
    if fullC:
        W = list(range(fullC[1].Gamma0, fullC[1].Gamma0 + 8))
        specs.append(("FULL8", "Zp", 3, [(2,1,1),(2,1,1),(2,1,1)],
                      [(a, b) for a in W for b in W]))
        mydata["FULL8"] = fullC
    if de1C:
        W = list(range(de1C[1].Gamma0, de1C[1].Gamma0 + 4))
        specs.append(("De1a", "Zp", 3, [(2,1,1),(1,1,2),(2,1,1)],
                      [(a, b) for a in W for b in W]))
        mydata["De1a"] = de1C
    if l1C:
        W = list(range(l1C[1].Gamma0, l1C[1].Gamma0 + 6))
        specs.append(("Rl1h2", "Zp", 3, [(2,1,1),(5,2,1),(2,1,1)],
                      [(a, b) for a in W for b in W]))
        mydata["Rl1h2"] = l1C
    try:
        m5bad = m5_crosscheck(specs, mydata)
        results["m5"] = dict(bad=m5bad, ntow=len(specs))
    except Exception as exc:
        sbad("M5", f"HARNESS EVENT {exc!r}")

    # ================= verdict =================
    log("\n" + "="*78)
    log(f"STRUCTURAL identity failures: {len(STRUCT_BAD)}")
    for s in STRUCT_BAD[:30]:
        log(f"  {s}")
    log(f"TOTAL elapsed {time.time()-t0:.1f}s")
    verdict = "STRUCT-GREEN" if not STRUCT_BAD else "STRUCT-RED"
    log(f"M3 VERDICT (structural identities only; separation counts are data): {verdict}")
    results["struct_bad"] = STRUCT_BAD
    with open(os.path.join(HERE, "l3ramps_m3_results.json"), "w") as fh:
        json.dump(results, fh, indent=1, default=str)
    with open(os.path.join(HERE, "l3ramps_m3_output.txt"), "w") as fh:
        fh.write("\n".join(OUTLINES) + "\n")
    return 0 if not STRUCT_BAD else 1

if __name__ == "__main__":
    sys.exit(main())
