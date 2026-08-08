#!/usr/bin/env python3
"""k2res_regx_ext.py — K2-RESIDUE POST-SEAL ANALYSIS EXTENSION (verdict
stage, 2026-08-08 campaign; wallclock 2026-08-07).

NOT part of the sealed battery (k2res_checks.py, sealed at caa7c50 and
run UNMODIFIED).  This leg is the disclosed verdict-stage reading of the
KR-PFREE census artifact: prediction P-6 left "whether any REGULAR row
carries a promotion-carrying beta_min cell" OPEN with "the census
decides it" — but the sealed runner records promo rows without their
K2-REG flag (REG := every beta_min group single-book i.e. single-fiber,
AND full availability — survk2_derive_checks.py trace_row, lines
424/539-541).  This script re-traces EXACTLY the promo rows named in
the committed k2res_checks_results.json findings and computes, per row:
  avail (corr_table digits), row_reg, per-group fiber counts, protection
  (pinned SD.classify_group/SD.protected), and for each promotion-
  carrying junk-free beta_min cell: its group's fiber count, size,
  and protection.
Walk + cell construction copied verbatim from the sealed pfree_row
(k2res_checks.py) with `ce` additionally retained per cell.  Read-only:
imports the pinned survk2_derive_checks / engine stack; writes only
k2res_regx_ext_results.json + stdout.
"""
import sys, os, re, json, time, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import survk2_derive_checks as SD
import rmengine_pe_reimpl as PE
import wmultdcx_stress as WS
import wmultdcx_derive_checks as WD
import empty_derive_checks as ED
from grb_order2_check import pnorm, pmul, pscal, pdivmod, w0

RESULTS = json.load(open(os.path.join(HERE, "k2res_checks_results.json")))
promo = []
for tag_, detail in RESULTS["findings"]:
    if tag_ != "PFREE":
        continue
    m = re.match(r"(\w+)\[(\d+), (\d+)\]: (\d+) beta_min", detail)
    assert m, detail
    promo.append((m.group(1), int(m.group(2)), int(m.group(3)),
                  int(m.group(4))))
print(f"promo rows in committed findings: {len(promo)} "
      f"({sum(x[3] for x in promo)} cells) on "
      f"{len(set(x[0] for x in promo))} towers")

ROSters = list(WS.ROSTER) + list(ED.FRESH_ROSTER) + list(SD.PX_ROSTER) \
    + list(SD.SD_ROSTER) + list(SD.K2_TRACED)
SPEC = {s[0]: s for s in ROSters}

def row_cells(E, sA, sB, u1a, u1b, su, tag):
    """pfree_row's walk verbatim (k2res_checks.py), cells keep ce."""
    R = E.R; m = E.m
    sig = tuple(sA[l + 1] + sB[l + 1] for l in range(m))
    b0 = pscal(R, R["pi_pow"](u1a + u1b), [R["one"]])
    z = (0,) * m
    init = [(1, b0, sig, z, z, z, z, 0, None, False, (), 0, ())]
    q1 = []
    r = SD.walk_rec(E, init, q1, tag)
    if r is None: return None
    init2 = []
    for st in q1:
        sgn, b, j, pc, dmp, cons, ncorr, junk, _, _, ce, _, hist = st
        for (cD, jD) in E.Dcells:
            Lc, Xc, Yc = E.digit_split(b, cD)
            js = tuple(j[l] + jD[l] for l in range(m))
            for (cc, jtag, dj0) in ((Lc, 0, 0), (Xc, 1, 0), (Yc, 1, 1)):
                if not pnorm(R, cc): continue
                jj = list(js); jj[0] += dj0
                dd = list(dmp); dd[0] += dj0
                init2.append((sgn, cc, tuple(jj), pc, tuple(dd), cons,
                              ncorr, junk + jtag, tuple(jD), False, ce, dj0,
                              hist + (('seed', jD[0] + dj0),)))
    q2 = []
    r = SD.walk_rec(E, init2, q2, tag)
    if r is None or not q2: return None
    cells = []
    for st in q2:
        (sgn, b, j, pc, dmp, cons, ncorr, junk, jD, isp, ce, y2, hist) = st
        cells.append(dict(sgn=sgn, j=j, pc=tuple(pc), junk=junk, y2=y2,
                          line=E.line(b, j), hist=hist, res=E.resKm(b),
                          jD=jD, ce=ce))
    return cells

out = dict(rows=[], summary={})
t00 = time.time()
nreg = nglued_row = 0
promo_group_glued = promo_group_single = 0
unprotected_rows = 0
for tag in sorted(set(x[0] for x in promo)):
    spec = SPEC[tag]
    _, m, kind, p, d0, reads = spec
    t0 = time.time()
    E = PE.Eng(m, kind, p, d0, reads, tag)
    PE.prep(E)
    u, su = WS.uchain(E)
    Etot, G0, split = WS.window_split(E)
    anch = WS.anchors_of(E, Etot, G0, split)
    avail = set(k for (k, dc) in E.corr_table()[0])
    g0 = E.g[0]
    for (tg, ga, gb, ncell) in [x for x in promo if x[0] == tag]:
        aA, sA, u1a = anch[ga]
        aB, sB, u1b = anch[gb]
        cells = row_cells(E, sA, sB, u1a, u1b, su, tag)
        assert cells, (tag, ga, gb)
        bmin = min(c['line'] for c in cells)
        slots = collections.defaultdict(list)
        for c in cells: slots[c['j']].append(c)
        bgroups = {jv: [c for c in grp if c['line'] == bmin]
                   for jv, grp in slots.items()}
        bgroups = {jv: g for jv, g in bgroups.items() if g}
        row_reg = (avail == set(range(g0)))
        prot_some = False
        ginfo = {}
        for jv, g in sorted(bgroups.items()):
            fibs = collections.defaultdict(list)
            for c in g:
                ibook = tuple(sorted(e for e in c['ce'] if e[0] != 0))
                fibs[(ibook, c['pc'])].append(c)
            if len(fibs) > 1:
                row_reg = False
            classes, signed = SD.classify_group(E, g)
            prot = SD.protected(signed)
            if prot: prot_some = True
            ginfo[jv] = (len(fibs), len(g), prot, signed)
        # locate the promotion-carrying junk-free beta_min cells
        pcell_rec = []
        npr = 0
        for jv, g in sorted(bgroups.items()):
            for c in g:
                if c['junk'] or c['y2']: continue
                p0 = sum(1 for ev in c['hist'] if ev[0] == 'p0')
                if p0 > 0:
                    npr += 1
                    nf, sz, prot, signed = ginfo[jv]
                    pcell_rec.append(dict(slot=list(jv), group_fibers=nf,
                                          group_size=sz, group_prot=prot,
                                          signed=sorted(signed)))
                    if nf > 1: promo_group_glued += 1
                    else: promo_group_single += 1
        if npr != ncell:
            print(f"MISMATCH {tag}[{ga},{gb}]: recount {npr} != "
                  f"committed {ncell}")
        nreg += row_reg
        nglued_row += (not row_reg)
        if not prot_some: unprotected_rows += 1
        out["rows"].append(dict(tower=tag, key=[ga, gb], g0=g0,
                                avail=sorted(avail), row_reg=row_reg,
                                prot_some=prot_some, npromo=npr,
                                ngroups=len(bgroups),
                                promo_cells=pcell_rec))
    print(f"-- {tag}: {sum(1 for x in promo if x[0]==tag)} rows "
          f"({time.time()-t0:.1f}s)")
out["summary"] = dict(
    promo_rows=len(promo), reg_rows=nreg, nonreg_rows=nglued_row,
    promo_cells_in_single_fiber_groups=promo_group_single,
    promo_cells_in_glued_groups=promo_group_glued,
    rows_without_protected_group=unprotected_rows,
    elapsed=round(time.time() - t00, 1))
print("SUMMARY:", out["summary"])
with open(os.path.join(HERE, "k2res_regx_ext_results.json"), "w") as f:
    json.dump(out, f, indent=1, default=str)
print("results -> k2res_regx_ext_results.json")
