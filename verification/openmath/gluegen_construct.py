#!/usr/bin/env python3
"""gluegen_construct.py — GLUEGEN-CONSTRUCT unit (2026-08-08 campaign): the
PV-4 falsifier target — residue-GENERIC glued groups, derived, solved,
realized, and run through the K2-CLOSE verdict machinery.

Note of record: lean/notes/openmath/GLUEGEN_CONSTRUCT_2026-08-08.md (the
derivation D1-D4, the laws, the sealed predictions PG-A1..PG-C2 — sealed at
commit 1 BEFORE the run; this docstring only summarizes).

PART A (solve): per shape (43 main + 10 annex, re-enumerated in process and
guard-counted) x field F3/F4/F5/F7/F8/F9 (+F2 nullity check): exhaustive
search for PIN-COMPLIANT fully generic assignments of the K2-L4 monomial
coordinates.  Pin (checked FIRST, the search space excludes violators): the
digit pair (ps0, ps1) must be the coefficient pair of a monic irreducible
quadratic y^2 + ps1*y + ps0 over K0 with ps0 != 0 (K2-L8: A = {1} is
class-empty — assignments needing ps0 = 0 are dead on arrival); main table
also ps1 != 0 ((R2)); annex ps1 = 0, odd characteristic only.  x0 = 1 and
rho_1 = 1 WLOG (global scalings preserve coincidences).  GENERIC = all cell
monomials pairwise distinct in K0*.  Output per shape: minimal generic q,
witness, witness corner, and the free-digit comparison (irreducibility
dropped, ps0 != 0 kept) — does the pin ever RAISE the threshold?

PART B (realize): sealed roster GGB2AF/GGB2AZ (m=3, p=2, d0=2, the SDG2B
glue reads, K0=F4), GGW4AF (m=4, p=2, d0=2, SDW4 reads, F4), GGB3AF (m=3,
p=2, d0=3, F8 — through the (W2) wall via engine_ext TowerExt), GGW3AF
(m=3, p=2, d0=2, SDW3 reads — control), GGP3BF (m=3, p=3, d0=2, F9 — the
char-2-hypothesis control, MEASURED).  engine_ext per the standing rule:
import + install() + agreement_gate() re-run, counts reported.  Row
selection = survk2_instrument.run_fresh_tower caps 12/6 REPLICATED VERBATIM
(the selection loop is copied; trace_k2 is called unmodified), per-tower
wall budget, timeout = disclosed skip.

PART C (verdict laws, LAW-KEYED; predicted 0 unless MEASURED):
  GG-PIN     psi0_0 != 0 on every constructed tower (K2-L8 shadow).
  GG-STR     string-residue-classes == the tracer's keq classes (harness;
             validated first on ALL 531 pinned grprec records).
  GG-FACT    K2-L4 readout: every glued bottom cell's residue equals
             x_t * prod_K psibar_k * prod_I res(c_d) (string-compare under
             GG-STR; junk = y2 = 0 asserted).
  GG-SHAPE   realized glued groups normalize into the committed 43+10
             table.  UNMATCHED/BREACH = censused FINDING (first
             beyond-perimeter realization), NOT a violation.
  GG-CLOSED  the in-vivo coincidence partition is CLOSED (K2-L12 shadow).
  GG-IDC     the state's H has digit part inside <I1, I3> (K2-L11 shadow).
  GG-CORNER  H contains no in-vivo-falsified tower identity.
  GG-PROT    SD-L7 protection of the in-vivo vector == protection() of the
             realized state blocks (two routes, one verdict).
  GG-THMB    THE FALSIFIER: on every realized row that contains a glued
             group and covers its in-vivo corner c(phi) (FORM_CORNERS +
             the committed corner-safety column), some bottom group's
             in-vivo class vector is SD-L7 protected.  A violation is a
             COUNTEREXAMPLE to K2-THM-B's covers.
Genericity census (MEASURED, drives PG-B2): in-vivo class counts of every
realized glued group.

Deterministic, exact arithmetic.  Usage:
  python3 gluegen_construct.py            (sealed battery)
  python3 gluegen_construct.py --shakedown  (crash-freedom probe: Part A at
                                           F3/F4 only + 1 tower, no json)

[SHAKEDOWN DESIGN REPAIRS, pre-seal, DISCLOSED (one --shakedown crash probe
ran before commit 1; its readouts driving these repairs: the Part-A None
tail, corner=None on GGB2AF, glue counts 14/18):
 (i) COUNTING BOUND surfaced: genericity needs q - 1 >= n_monos (all
     monomial values distinct in the cyclic K0*), so the field list is
     extended to F11/F13/F16 (max n_monos over the table = 12 -> q = 13
     suffices); fields with q - 1 < n_monos are skipped with the bound
     recorded.  The note's S2 field list (F3..F9) predates this; PG-A1
     stays sealed at "q <= 9" and is judged as written (a MISS there is
     the bound's finding).
 (ii) SINGLE-SEED CORNERS: every realized glue tower (pinned a0tab ts =
     [0] or [1]) has ONE available seed, so x1 does not exist and I1 is
     tower-UNDETERMINED (this was ALSO true of the SDG2*/SDW4G2F roster —
     the K2-CLOSE corner talk silently sat on I1-vacuous towers).  corner
     is recorded as the SET of completions ("cx1" = {c01, c11}); GG-THMB
     applies only when EVERY completion is covered (conservative).
 (iii) tdata q display fix (p ** d0 both kinds).]
"""
import sys, os, time, json, ast, collections, itertools, signal, hashlib

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

RESULTS = os.path.join(HERE, "gluegen_construct_results.json")
TABLE_MD = os.path.join(HERE, "gluegen_table.md")
TOWER_BUDGET = 900

VIOL = []
def viol(fam, msg):
    VIOL.append((fam, msg)); print(f"VIOLATION [{fam}] {msg}")
FINDINGS = []
def finding(fam, msg):
    FINDINGS.append((fam, msg)); print(f"FINDING [{fam}] {msg}")

# ---------------- Part A: finite fields --------------------------------------
def gf(q):
    """Small finite field as (elements, add, mul, zero, one).  Elements are
    tuples of F_p coeffs, ascending powers, fixed length."""
    fac = {2:(2,1), 3:(3,1), 4:(2,2), 5:(5,1), 7:(7,1), 8:(2,3),
           9:(3,2), 11:(11,1), 13:(13,1), 16:(2,4)}
    p, d = fac[q]
    MODP = {4: (1, 1), 8: (1, 1, 0), 9: (1, 0),
            16: (1, 1, 0, 0)}   # x^d = -(these), asc
    els = [tuple(v) for v in itertools.product(range(p), repeat=d)]
    def add(a, b): return tuple((x + y) % p for x, y in zip(a, b))
    def neg(a): return tuple((-x) % p for x in a)
    def mul(a, b):
        raw = [0] * (2 * d - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                raw[i + j] += x * y
        for k in range(2 * d - 2, d - 1, -1):
            c = raw[k] % p
            if c:
                for t, mc in enumerate(MODP[q]):
                    raw[k - d + t] -= c * mc
            raw[k] = 0
        return tuple(x % p for x in raw[:d])
    zero, one = els[0], tuple([1] + [0] * (d - 1))
    return dict(q=q, p=p, els=els, add=add, mul=mul, neg=neg,
                zero=zero, one=one, units=[e for e in els if e != els[0]])

def quad_irreducible(F, ps0, ps1):
    """y^2 + ps1*y + ps0 irreducible over F <=> no root in F."""
    for y in F["els"]:
        v = F["add"](F["add"](F["mul"](y, y), F["mul"](ps1, y)), ps0)
        if v == F["zero"]:
            return False
    return True

def digit_pairs(F, annex, pinned):
    """Legal (ps0, ps1) pairs.  pinned=True: irreducible quadratic pin.
    Always ps0 != 0 (K2-L8 — the A = {1} kill, applied FIRST)."""
    out = []
    if annex:
        if F["p"] == 2:
            return []                       # K2-L8 Reading: annex needs odd p
        for ps0 in F["units"]:
            if not pinned or quad_irreducible(F, ps0, F["zero"]):
                out.append((ps0, F["zero"]))
    else:
        for ps0 in F["units"]:
            for ps1 in F["units"]:
                if not pinned or quad_irreducible(F, ps0, ps1):
                    out.append((ps0, ps1))
    return out

def mono_val(F, v, coords):
    acc = F["one"]
    for c, e in zip(coords, v):
        for _ in range(e):
            acc = F["mul"](acc, c)
    return acc

def generic_witness(F, monos, r, annex, pinned):
    """Search pin-compliant assignments; return witness dict or None.
    Coordinates (x0, x1, ps0, ps1, rho_1..rho_r); x0 = rho_1 = 1 WLOG."""
    U, one = F["units"], F["one"]
    for (ps0, ps1) in digit_pairs(F, annex, pinned):
        for x1 in U:
            for rhos in itertools.product(U, repeat=r - 1):
                coords = [one, x1, ps0, ps1, one] + list(rhos)
                vals = [mono_val(F, v, coords) for v in monos]
                if len(set(vals)) == len(vals):
                    i1 = (F["mul"](x1, ps1) == one)          # x0 = x1*ps1
                    i3 = (F["mul"](ps1, ps1) == ps0)         # ps0 = ps1^2
                    return dict(q=F["q"], ps0=ps0, ps1=ps1, x1=x1,
                                rhos=list(rhos), I1=bool(i1), I3=bool(i3))
    return None

def solve_all(KV, KE, qs):
    """Part A: per-shape minimal generic q, pinned vs free-digit."""
    main_sh = KE.enumerate_shapes({0, 1}, "A={0,1}")
    annex_sh = KE.enumerate_shapes({0}, "A={0}")
    ids_m, order_m = KE.sorted_ids(main_sh, "GS")
    ids_a, order_a = KE.sorted_ids(annex_sh, "AS")
    if len(main_sh) != 43 or len(annex_sh) != 10:
        viol("GG-GUARD", f"shape counts {len(main_sh)}/{len(annex_sh)}")
    rows = []
    for annex, ids, order in ((False, ids_m, order_m), (True, ids_a, order_a)):
        for key in order:
            monos, nets, labels, D = KV.shape_model(key)
            r = len(key)
            rec = dict(id=ids[key], annex=annex, n_monos=len(monos), r=r,
                       per_q={}, min_q=None, min_q_free=None, wit=None)
            for q in qs:
                if q - 1 < len(monos):
                    rec["per_q"][q] = dict(pin=False, free=False,
                                           bound=True)
                    continue
                F = gf(q)
                w = generic_witness(F, monos, r, annex, pinned=True)
                wf = (w if w else
                      generic_witness(F, monos, r, annex, pinned=False))
                rec["per_q"][q] = dict(pin=bool(w), free=bool(wf))
                if w and rec["min_q"] is None:
                    rec["min_q"], rec["wit"] = q, w
                if wf and rec["min_q_free"] is None:
                    rec["min_q_free"] = q
            rows.append(rec)
            print(f"  {rec['id']}: min generic q = {rec['min_q']} "
                  f"(free-digit {rec['min_q_free']})"
                  + (f" wit corner I1={rec['wit']['I1']} "
                     f"I3={rec['wit']['I3']}" if rec["wit"] else ""))
    return rows

# ---------------- Part B: realization ----------------------------------------
GG_ROSTER = [
    ("GGB2AF", 3, "Fpt", 2, 2, [(3,1,2), (2,1,1), (3,2,1), (2,1,1)]),
    ("GGB2AZ", 3, "Zp",  2, 2, [(3,1,2), (2,1,1), (3,2,1), (2,1,1)]),
    ("GGW4AF", 4, "Fpt", 2, 2, [(3,1,2), (2,1,1), (2,1,1), (2,1,1), (2,1,1)]),
    ("GGB3AF", 3, "Fpt", 2, 3, [(3,1,2), (2,1,1), (3,2,1), (2,1,1)]),
    ("GGW3AF", 3, "Fpt", 2, 2, [(3,1,2), (2,1,1), (2,3,1), (2,1,1)]),
    ("GGP3BF", 3, "Fpt", 3, 2, [(3,1,2), (2,1,1), (3,2,1), (2,1,1)]),
]

def str_classes(cells):
    """Partition cell indices by residue STRING (validated by GG-STR)."""
    blocks = collections.defaultdict(list)
    for i, c in enumerate(cells):
        blocks[c["res"]].append(i)
    return list(blocks.values())

def validate_str_on_pinned():
    """GG-STR harness leg: string classes == tracer keq classes on ALL
    pinned grprec records (531)."""
    inst = json.load(open(os.path.join(HERE,
                                       "survk2_instrument_results.json")))
    n = 0
    for rec in inst["grprec"]:
        blocks = str_classes(rec["cells"])
        got = sorted((sum(rec["cells"][i]["sgn"] for i in b), len(b))
                     for b in blocks)
        want = sorted((c["signed"], c["n"]) for c in rec["classes"])
        if got != want:
            viol("GG-STR", f"pinned {rec['tower']}{rec['key']} "
                 f"slot {rec['slot']}: {got} != {want}")
        n += 1
    return n

def tower_residue_data(SI, E, su, dmap, Dmap, tag):
    """psibar digits, seed digits x_t, I1/I3 truth, availability."""
    from grb_order2_check import w0 as W0
    g0 = E.g[0]
    corr0 = E.corr_table()[0]
    psibar = {k: E.resKm(dcells[0][0]) for (k, dcells) in corr0}
    if 0 not in psibar:
        viol("GG-PIN", f"{tag}: psi0_0 = 0 (A = {{1}} REALIZED?!)")
    xres = {}
    for jD, cD in Dmap.items():
        t, rem = divmod(jD[0] - su[1], E.e[0])
        if rem == 0 and 0 <= t < g0:
            xres[t] = E.resKm(cD)
    I1 = I3 = None
    if 0 in psibar and 1 in psibar:
        I3 = bool(E.keq(E.kmul(psibar[1], psibar[1]), psibar[0]))
    if 1 in psibar and 0 in xres and 1 in xres:
        I1 = bool(E.keq(E.kmul(psibar[1], xres[1]), xres[0]))
    b = lambda v: "x" if v is None else ("1" if v else "0")
    corner = "c" + b(I1) + b(I3)          # "x" = tower-undetermined
    comps = ["c" + i1 + i3
             for i1 in (("1", "0") if I1 is None else (b(I1),))
             for i3 in (("1", "0") if I3 is None else (b(I3),))]
    return dict(psibar=psibar, xres=xres, I1=I1, I3=I3, corner=corner,
                completions=comps, A=sorted(psibar), q=None)

def analyze_glued_rec(KV, KE, E, tdata, dmap, rec, ids_m, ids_a, corner_map):
    """One realized glued bottom group: shape, state, laws.  Returns dict."""
    tag = f"{rec['tower']}{rec['key']} slot {rec['slot']}"
    cells = rec["cells"]
    fibers = collections.defaultdict(collections.Counter)
    fkey_of = {}
    for i, c in enumerate(cells):
        if c["junk"] or c["y2"]:
            viol("GG-FACT", f"{tag}: junk/Y cell at beta_min")
        cell, book = KE.parse_cell(c)
        fibers[book][cell] += 1
        fkey_of[i] = (book, cell)
    books = sorted(fibers)
    # shape match (GLUE-COVER extension; UNMATCHED/BREACH = finding)
    try:
        key = KE.normalize_group([dict(fibers[b]) for b in books])
        kind = ids_m.get(key) or ids_a.get(key) or "UNMATCHED"
    except AssertionError as e:
        key, kind = None, "BREACH"
    if kind in ("UNMATCHED", "BREACH"):
        finding("GG-SHAPE", f"{tag}: {kind} — beyond-perimeter glued group "
                f"realized (K2-RES-B(iii) instance)")
    # raw monomial model: coords (x0, x1, ps0, ps1, rho_book...)
    D = 4 + len(books)
    mono_of, monos, nets, mlab = {}, [], [], []
    for i, c in enumerate(cells):
        book, (t, K, s) = fkey_of[i]
        assert t in (0, 1), f"raw t out of range at {tag}"
        mk = (books.index(book), t, K)
        if mk not in mono_of:
            v = [0] * D
            v[t] += 1
            for k in K:
                v[2 + k] += 1
            v[4 + mk[0]] = 1
            mono_of[mk] = len(monos)
            monos.append(tuple(v)); nets.append(0)
            mlab.append(f"f{mk[0]+1}(t={t},K={{{','.join(map(str,K))}}})")
        nets[mono_of[mk]] += s
    # GG-FACT: K2-L4 readout per cell (string compare under GG-STR)
    for i, c in enumerate(cells):
        book, (t, K, s) = fkey_of[i]
        pred = tdata["xres"][t]
        for k in K:
            pred = E.kmul(pred, tdata["psibar"][k])
        for (lvl, k, avec, dj0) in book:
            cd = dmap.get((lvl, k, tuple(avec)))
            if cd is None:
                viol("GG-FACT", f"{tag}: interior edge ({lvl},{k},{avec}) "
                     f"not in dmap"); continue
            pred = E.kmul(pred, E.resKm(cd))
        if str(pred) != c["res"]:
            viol("GG-FACT", f"{tag}: cell {i} K2-L4 readout mismatch "
                 f"{pred} != {c['res']}")
    # realized state on the monomials
    mono_res = {}
    for i, c in enumerate(cells):
        book, (t, K, s) = fkey_of[i]
        mi = mono_of[(books.index(book), t, K)]
        if mi in mono_res and mono_res[mi] != c["res"]:
            viol("GG-FACT", f"{tag}: equal (f,t,K) cells, distinct res")
        mono_res[mi] = c["res"]
    rblocks = collections.defaultdict(set)
    for mi, rs in mono_res.items():
        rblocks[rs].add(mi)
    blocks = [set(b) for b in rblocks.values()]
    nclasses = len(blocks)
    # GG-CLOSED (K2-L12) + GG-IDC (K2-L11) + GG-CORNER
    ckey, L = KV.closure([set(b) for b in blocks], [], monos, D)
    if ckey != tuple(sorted(tuple(sorted(b)) for b in blocks)):
        viol("GG-CLOSED", f"{tag}: in-vivo partition NOT closed: "
             f"{ckey} vs {sorted(map(sorted, blocks))}")
    cat = KV.Lat(D); cat.add(KV.ivec(D, "I1")); cat.add(KV.ivec(D, "I3"))
    if not KV.idclosure_ok(L, D, cat):
        viol("GG-IDC", f"{tag}: state H digit part outside <I1,I3>")
    for nm, truth in (("I1", tdata["I1"]), ("I3", tdata["I3"])):
        if truth is False and L.contains(KV.ivec(D, nm)):
            viol("GG-CORNER", f"{tag}: H contains falsified {nm}")
    # GG-PROT: two routes to protection
    annex = (tdata["A"] == [0])
    pmodel = KV.protection(blocks, nets, annex)
    nz = sorted(s for s in rec["signed"] if s)
    pvivo = "PROT" if nz in ([1], [-1], [-1, 1]) else (
        "DEAD" if not nz else "UNPROT")
    ok = (pmodel == pvivo or (pmodel == "PROT2K" and pvivo == "UNPROT"))
    if not ok:
        viol("GG-PROT", f"{tag}: model {pmodel} != vivo {pvivo}")
    return dict(tower=rec["tower"], key=rec["key"], slot=rec["slot"],
                shape=kind, n=rec["n"], r=len(books), nclasses=nclasses,
                n_monos=len(monos), signed=rec["signed"],
                state=[sorted(b) for b in blocks], mlab=mlab,
                prot=pmodel, full_merge=(nclasses == 1),
                generic=(nclasses == len(monos)))

# ---------------- Part B driver: replicated selection + per-row analysis -----
def run_gg_tower(SI, KV, KE, spec, ids_m, ids_a, corner_map, out):
    """run_fresh_tower's selection loop replicated verbatim (caps 12/6);
    trace_k2 called unmodified; per-row post-processing of SI.GRPREC."""
    from grb_order2_check import pnorm, pmul, pdivmod
    tag, m, kind, p, d0, reads = spec
    t0 = time.time()
    st = SI.setup(spec)
    if st is None:
        out["towers"][tag] = dict(skipped=True); return
    E, su, Etot, G0, anch, prin, dmap, Dmap, u0 = st
    tdata = tower_residue_data(SI, E, su, dmap, Dmap, tag)
    tdata["q"] = E.p ** E.d0
    R = E.R; etop = E.e[m - 1]
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
            pools, cs, Dd, top = SI.WS.pools_of(E, sA, sB, su)
            ctop = cs[-1] if cs else 0
            kdef = 2 * etop - Dd
            if kdef > ctop: continue
            live_pool.setdefault((kdef, ctop), []).append(
                (ga, gb, cs, Dd, kdef, sA, sB, u1a, u1b))
    cap = 6 if m >= 4 else 12
    trec = dict(skipped=False, q=tdata["q"], A=tdata["A"],
                psibar={k: str(v) for k, v in tdata["psibar"].items()},
                xres={t: str(v) for t, v in tdata["xres"].items()},
                I1=tdata["I1"], I3=tdata["I3"], corner=tdata["corner"],
                live=0, glued_rows=0, glued_groups=0, rows=[])
    out["towers"][tag] = trec
    for stratum in sorted(live_pool):
        for row in live_pool[stratum][:cap]:
            ga, gb, cs, Dd, kdef, sA, sB, u1a, u1b = row
            n0 = len(SI.GRPREC)
            r = SI.trace_k2(E, sA, sB, u1a, u1b, anch[ga][0], anch[gb][0],
                            su, cs, Dd, kdef, (ga, gb), prin, tag, p, kind,
                            E.g[0], "gg", dmap, Dmap, u0)
            if not r: continue
            trec["live"] += 1
            recs = SI.GRPREC[n0:]
            process_row(KV, KE, E, tdata, dmap, recs, ids_m, ids_a,
                        corner_map, trec, out)
    print(f"-- GG {tag} m={m} {kind},p={p},d0={d0} q={trec['q']} "
          f"corner={trec['corner']}: live={trec['live']} glued rows="
          f"{trec['glued_rows']} groups={trec['glued_groups']} "
          f"({time.time()-t0:.1f}s)")

def process_row(KV, KE, E, tdata, dmap, recs, ids_m, ids_a, corner_map,
                trec, out):
    """One traced row: GG-STR, glued analysis, GG-THMB."""
    glued, covered, sdl7_any = [], set(), False
    rowtag = f"{recs[0]['tower']}{recs[0]['key']}" if recs else "?"
    for rec in recs:
        blocks = str_classes(rec["cells"])
        got = sorted((sum(rec["cells"][i]["sgn"] for i in b), len(b))
                     for b in blocks)
        want = sorted((c["signed"], c["n"]) for c in rec["classes"])
        if got != want:
            viol("GG-STR", f"{rowtag} slot {rec['slot']}: {got} != {want}")
        nz = sorted(s for s in rec["signed"] if s)
        if nz in ([1], [-1], [-1, 1]):
            sdl7_any = True
        fibers = collections.defaultdict(collections.Counter)
        for c in rec["cells"]:
            cell, book = KE.parse_cell(c)
            fibers[book][cell] += 1
        if len(fibers) >= 2:
            g = analyze_glued_rec(KV, KE, E, tdata, dmap, rec,
                                  ids_m, ids_a, corner_map)
            glued.append(g)
            out["glued"].append(g)
            covered |= corner_map.get(g["shape"], set())
        else:
            cnt = dict(list(fibers.values())[0])
            form = KV.classify_form(cnt)
            covered |= KV.FORM_CORNERS.get(form, set())
    if not glued:
        return
    trec["glued_rows"] += 1
    trec["glued_groups"] += len(glued)
    cphi = tdata["corner"]
    is_covered = all(c in covered for c in tdata["completions"])
    if is_covered and not sdl7_any:
        viol("GG-THMB", f"{rowtag}: K2-THM-B COUNTEREXAMPLE — corner "
             f"{cphi} covered ({sorted(covered)}) but NO bottom group "
             f"protected in vivo")
    trec["rows"].append(dict(key=recs[0]["key"], cphi=cphi,
                             covered=sorted(covered),
                             thmb_applicable=bool(is_covered),
                             prot_in_vivo=bool(sdl7_any),
                             glued=[g["slot"] for g in glued]))

# ---------------- assembly ----------------------------------------------------
def load_corner_map():
    """Committed corner-safety column (k2close_verdicts_results.json)."""
    fn = os.path.join(HERE, "k2close_verdicts_results.json")
    md5 = hashlib.md5(open(fn, "rb").read()).hexdigest()
    d = json.load(open(fn))
    cm = {}
    for r in d["shapes"]:
        cm[r["id"]] = ({c for c, v in (r["corners"] or {}).items()
                        if v["safe"]})
    return cm, md5

def write_table(out):
    L = []
    A = L.append
    A("# gluegen_table.md — residue-generic glued construction "
      "(MACHINE-GENERATED)")
    A("")
    A("Generated by `gluegen_construct.py`.  DO NOT EDIT BY HAND.  Laws, "
      "model, pin, predictions: the runner docstring + the note of record.")
    A("")
    A("## Part A: minimal generic q per shape (pin-compliant | free-digit)")
    A("")
    A("| ID | monos | r | min q (pin) | min q (free) | wit (ps0,ps1,x1,"
      "rhos) | wit corner |")
    A("|---|---|---|---|---|---|---|")
    for r in out["solve"]:
        w = r["wit"]
        ws = (f"{w['ps0']},{w['ps1']},{w['x1']},{w['rhos']}" if w else "—")
        wc = (f"I1={int(w['I1'])} I3={int(w['I3'])}" if w else "—")
        A(f"| {r['id']} | {r['n_monos']} | {r['r']} | {r['min_q']} | "
          f"{r['min_q_free']} | {ws} | {wc} |")
    A("")
    A("## Part B: towers")
    A("")
    A("| tower | q | A | corner (I1,I3) | live rows | glued rows | glued "
      "groups |")
    A("|---|---|---|---|---|---|---|")
    for tag, t in out["towers"].items():
        if t.get("skipped"):
            A(f"| {tag} | — | — | — | SKIPPED | — | — |"); continue
        A(f"| {tag} | {t['q']} | {t['A']} | {t['corner']} "
          f"(I1={t['I1']},I3={t['I3']}) | {t['live']} | {t['glued_rows']} "
          f"| {t['glued_groups']} |")
    A("")
    A("## Part B/C: realized glued groups (the PV-4 probe)")
    A("")
    A("| tower | key | slot | shape | n | classes/monos | signed | prot | "
      "state |")
    A("|---|---|---|---|---|---|---|---|---|")
    for g in out["glued"]:
        st = "FULL-MERGE" if g["full_merge"] else (
            "GENERIC" if g["generic"] else "PARTIAL")
        A(f"| {g['tower']} | {g['key']} | {g['slot']} | {g['shape']} | "
          f"{g['n']} | {g['nclasses']}/{g['n_monos']} ({st}) | "
          f"{g['signed']} | {g['prot']} | {g['state']} |")
    A("")
    A("## Sealed-prediction verdicts (misses are findings, not violations)")
    A("")
    for k, v in out["predictions"].items():
        A(f"- {k}: {'GREEN' if v[0] else 'MISS'} — {v[1]}")
    A("")
    A(f"FINAL: laws {'GREEN' if not VIOL else 'RED'} ({len(VIOL)} "
      f"violations); findings {len(FINDINGS)}; "
      f"{out['elapsed']:.1f}s.")
    open(TABLE_MD, "w").write("\n".join(L) + "\n")
    print(f"WROTE {TABLE_MD}")

def main():
    shakedown = "--shakedown" in sys.argv
    t0 = time.time()
    import k2close_verdicts as KV
    import k2close_enum as KE
    out = dict(final=False, towers={}, glued=[], solve=[], predictions={},
               violations=None, findings=None)
    # GG-STR harness leg on the pinned artifact
    n = validate_str_on_pinned()
    print(f"GG-STR pinned validation: {n} grprec records checked")
    # Part A
    print("=" * 78); print("PART A: the solve (minimal generic q per shape)")
    qs = [2, 3, 4] if shakedown else [2, 3, 4, 5, 7, 8, 9, 11, 13, 16]
    out["solve"] = solve_all(KV, KE, qs)
    out["qs"] = qs
    # engine_ext per the standing rule
    print("=" * 78); print("ENGINE_EXT: install() + agreement_gate()")
    import engine_ext as EX
    EX.install()
    nv = EX.agreement_gate(full=not shakedown)
    print(f"agreement_gate: {nv} new violations; counters "
          f"{ {k: v for k, v in EX.CNT.items() if k.startswith('agr')} }")
    if nv:
        viol("GG-HARNESS", f"engine_ext agreement_gate: {nv} violations")
    out["agreement_gate"] = dict(new_violations=nv,
                                 counters=dict(EX.CNT))
    # Part B
    import survk2_instrument as SI
    corner_map, cmd5 = load_corner_map()
    out["corner_map_md5"] = cmd5
    ids_m, _ = KE.sorted_ids(KE.enumerate_shapes({0, 1}, "A={0,1}"), "GS")
    ids_a, _ = KE.sorted_ids(KE.enumerate_shapes({0}, "A={0}"), "AS")
    print("=" * 78); print("PART B: the realization roster")
    roster = GG_ROSTER[:1] if shakedown else GG_ROSTER
    nsi0 = len(SI.VIOL)
    def _alrm(sig, frm): raise TimeoutError("GG tower budget")
    for spec in roster:
        old = signal.signal(signal.SIGALRM, _alrm)
        signal.alarm(0 if shakedown else TOWER_BUDGET)
        try:
            run_gg_tower(SI, KV, KE, spec, ids_m, ids_a, corner_map, out)
        except TimeoutError:
            print(f"-- GG {spec[0]}: BUDGET TIMEOUT ({TOWER_BUDGET}s) — "
                  f"disclosed, skipped")
            out["towers"].setdefault(spec[0], dict(skipped=True))
            out["towers"][spec[0]]["timeout"] = True
        finally:
            signal.alarm(0); signal.signal(signal.SIGALRM, old)
        if not shakedown:
            out["elapsed"] = time.time() - t0
            json.dump(out, open(RESULTS, "w"), indent=1, default=str)
    # surface tracer violations (SK2-*) from the new towers
    for v in SI.VIOL[nsi0:]:
        viol("GG-SI", f"{v[0]} {v[1]}: {v[2]}")
    # ---- sealed-prediction verdicts ----
    pv = {}
    sv = out["solve"]
    if not shakedown:
        pv["PG-A1"] = (all(r["min_q"] is not None and r["min_q"] <= 9
                           for r in sv)
                       and not any(r["per_q"].get(2, {}).get("pin")
                                   for r in sv),
                       "all 53 generic at some q <= 9; none at q = 2")
        bid = {r["id"]: r for r in sv}
        pv["PG-A2"] = (bid["GS-02"]["min_q"] == 3 and
                       bid["GS-01"]["min_q"] == 3 and
                       bid["GS-08"]["min_q"] == 4,
                       f"GS-01={bid['GS-01']['min_q']} "
                       f"GS-02={bid['GS-02']['min_q']} "
                       f"GS-08={bid['GS-08']['min_q']} (want 3/3/4)")
        pv["PG-A3"] = (all(r["min_q"] == r["min_q_free"] for r in sv),
                       "pin never raises the threshold: " + ", ".join(
                           f"{r['id']} {r['min_q_free']}->{r['min_q']}"
                           for r in sv if r["min_q"] != r["min_q_free"])
                       if any(r["min_q"] != r["min_q_free"] for r in sv)
                       else "pin never raises the threshold")
        gg = lambda tag: out["towers"].get(tag, {})
        pv["PG-B1"] = (gg("GGB2AF").get("glued_rows", 0) >= 1 and
                       gg("GGB2AZ").get("glued_rows", 0) >= 1 and
                       not any(g["shape"] in ("UNMATCHED", "BREACH")
                               for g in out["glued"]),
                       f"GGB2AF {gg('GGB2AF').get('glued_rows')} / GGB2AZ "
                       f"{gg('GGB2AZ').get('glued_rows')} glued rows; "
                       f"shapes all matched")
        pv["PG-B2"] = (any(g["nclasses"] >= 2 for g in out["glued"]
                           if out["towers"][g["tower"]]["q"] >= 4),
                       "non-full-merge in-vivo state realized at q >= 4: " +
                       str(collections.Counter(
                           (g["shape"], g["nclasses"]) for g in out["glued"])))
        lawv = collections.Counter(f for (f, _) in VIOL)
        pv["PG-B3"] = (all(lawv.get(k, 0) == 0 for k in
                           ("GG-PIN", "GG-FACT", "GG-CLOSED", "GG-IDC",
                            "GG-CORNER", "GG-STR")),
                       f"law counts {dict(lawv)}")
        pv["PG-C1"] = (lawv.get("GG-THMB", 0) == 0,
                       "K2-THM-B protection on every covered realized row")
        pv["PG-C2"] = (gg("GGP3BF").get("glued_rows", None) == 0,
                       f"p=3 control glued rows = "
                       f"{gg('GGP3BF').get('glued_rows')} (char-2 "
                       f"hypothesis; MEASURED)")
        for k, v in pv.items():
            if not v[0]:
                finding(f"PRED-MISS {k}", v[1])
    out["predictions"] = {k: list(v) for k, v in pv.items()}
    out["violations"] = [list(v) for v in VIOL]
    out["findings"] = [list(f) for f in FINDINGS]
    out["elapsed"] = time.time() - t0
    out["final"] = True
    if not shakedown:
        json.dump(out, open(RESULTS, "w"), indent=1, default=str)
        print(f"WROTE {RESULTS}")
        write_table(out)
    print(f"FINAL: laws {'GREEN' if not VIOL else 'RED'} ({len(VIOL)} "
          f"violations); findings {len(FINDINGS)}; predictions "
          f"{sum(1 for v in pv.values() if v[0])}/{len(pv)} green; "
          f"{out['elapsed']:.1f}s")

if __name__ == "__main__":
    main()
