#!/usr/bin/env python3
"""survdisj_construct_posthoc.py — POST-HOC DIAGNOSTIC leg of the
(SURV-DISJ) DOUBLE-KILL CONSTRUCTION unit (NOT sealed; composed and run
AFTER the sealed battery's verdict artifacts landed; consumed by the note's
S6 verdict as labeled diagnosis only).

Three questions the sealed artifacts raise:
  (Q1) T1: why did no n = 5 window door realize?  -> per-tower realized
       window-budget census (all cells, all live rows) + the opening
       anatomy (parked + arrival) of the largest realized budgets.
  (Q2) T3: why did every (SD-YJ) companion leave the cascade alive?
       -> companion vs cascade (w0, line) anatomy on the 8 finding rows.
  (Q3) T2: glued/duplicate parity census — group sizes on all glued
       bottom groups (is any even?).
Same engines, same disclosed pick extension as the sealed runner.
"""
import sys, os, time, collections

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import survdisj_construct as SC          # installs the patch; reuses rosters
import rmengine_pe_reimpl as PE
import wmultdcx_stress as WS
import wmultdcx_derive_checks as WD
import empty_derive_checks as ED
import survk2_derive_checks as SK2
from grb_order2_check import pnorm, padd, pneg, pmul, pscal, pdivmod, w0

def rows_of(E, su, Etot, G0, anch):
    R = E.R; m = E.m; etop = E.e[m - 1]
    seen = set(); out = []
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
            if 2 * etop - Dd > (cs[-1] if cs else 0): continue
            out.append((ga, gb, sA, sB, u1a, u1b, cs))
    return out

def trace_cells(E, sA, sB, u1a, u1b, su, prin, tag):
    R = E.R; m = E.m
    sig = tuple(sA[l + 1] + sB[l + 1] for l in range(m))
    b0 = pscal(R, R["pi_pow"](u1a + u1b), [R["one"]])
    z = (0,) * m
    q1 = []
    SK2.walk_rec(E, [(1, b0, sig, z, z, z, z, 0, None, False, (), 0, ())],
                 q1, tag)
    init2 = []
    for st in q1:
        sgn, b, j, pc, dmp, cons, ncorr, junk, _, _, ce, _, hist = st
        for (cD, jD) in E.Dcells:
            Lc, Xc, Yc = E.digit_split(b, cD)
            js = tuple(j[l] + jD[l] for l in range(m))
            isp = (tuple(jD) == prin)
            for (cc, jtag, dj0) in ((Lc, 0, 0), (Xc, 1, 0), (Yc, 1, 1)):
                if not pnorm(R, cc): continue
                jj = list(js); jj[0] += dj0
                dd = list(dmp); dd[0] += dj0
                init2.append((sgn, cc, tuple(jj), pc, tuple(dd), cons, ncorr,
                              junk + jtag, tuple(jD), isp, ce, dj0,
                              hist + (('seed', jD[0] + dj0),)))
    q2 = []
    SK2.walk_rec(E, init2, q2, tag)
    return sig, q2

def main():
    print("=" * 78)
    print("POST-HOC DIAGNOSTICS (labeled; not sealed)")
    print("=" * 78)
    # ---------------- Q1: T1 window-budget census ----------------
    print("---- Q1: realized window budgets at g0 = 3 ----")
    for spec in SC.T1_ROSTER + [SC.T1_OMX]:
        tag, m, kind, p, d0, reads = spec
        if spec == SC.T1_OMX:
            SC.PICK_OVERRIDE[(4, 3)] = SC._omx
        try:
            E = PE.Eng(m, kind, p, d0, reads, tag)
            PE.prep(E)
            u, su = WS.uchain(E)
            Etot, G0, split = WS.window_split(E)
            anch = WS.anchors_of(E, Etot, G0, split)
            prin, meta = WD.inv_checks(E, u, su)
        finally:
            SC.PICK_OVERRIDE.pop((4, 3), None)
        ncens = collections.Counter()
        open_anat = collections.Counter()   # (kind, n) at n >= 4
        seedmax = 0
        for (ga, gb, sA, sB, u1a, u1b, cs) in rows_of(E, su, Etot, G0, anch):
            sig, q2 = trace_cells(E, sA, sB, u1a, u1b, su, prin, tag)
            for st in q2:
                hist = st[12]
                wins, endj0 = SK2.windows_of(E, hist, sig[0], None)
                if wins is None: continue
                for wnd in wins:
                    ncens[wnd['n']] += 1
                    if wnd['kind'] == 'seed':
                        seedmax = max(seedmax, wnd['n'])
                    if wnd['n'] >= 4:
                        open_anat[(wnd['kind'], wnd['n'])] += 1
        print(f"{tag}: budget census {dict(sorted(ncens.items()))} "
              f"seed-window max n = {seedmax} n>=4 anatomy "
              f"{dict(sorted(open_anat.items()))}")
    # ---------------- Q2: T3 companion anatomy ----------------
    print("---- Q2: (SD-YJ) companion anatomy ----")
    for spec in SC.T3_ROSTER:
        tag, m, kind, p, d0, reads = spec
        E = PE.Eng(m, kind, p, d0, reads, tag)
        PE.prep(E)
        u, su = WS.uchain(E)
        Etot, G0, split = WS.window_split(E)
        anch = WS.anchors_of(E, Etot, G0, split)
        prin, meta = WD.inv_checks(E, u, su)
        for (ga, gb, sA, sB, u1a, u1b, cs) in rows_of(E, su, Etot, G0, anch):
            sig, q2 = trace_cells(E, sA, sB, u1a, u1b, su, prin, tag)
            cells = []
            for st in q2:
                (sgn, b, j, pc, dmp, cons, ncorr, junk, jD, isp, ce, y2,
                 hist) = st
                cells.append(dict(sgn=sgn, b=b, j=j, junk=junk, ce=ce, y2=y2,
                                  prin=isp, w0=w0(E.R, b),
                                  line=E.line(b, j)))
            casc = [c for c in cells if c['ce'] == () and c['junk'] == 0
                    and c['y2'] == 0 and c['prin']]
            if len(casc) != 1: continue
            C = casc[0]
            comps = [c for c in cells if c['j'] == C['j'] and c is not C]
            for c in comps:
                (i, kc, avec, dj0) = c['ce'][0] if c['ce'] else (None,)*4
                print(f"{tag}[{ga},{gb}]: casc (w0={C['w0']}, line="
                      f"{C['line']}); companion (w0={c['w0']}, line="
                      f"{c['line']}, junk={c['junk']}, y2={c['y2']}, "
                      f"ce=[i={i},k={kc},dump={avec},Y={dj0}]) "
                      f"delta_line={c['line'] - C['line']}")
    # ---------------- Q3: T2 glued parity census ----------------
    print("---- Q3: glued bottom-group sizes (T2) ----")
    for spec in SC.T2_ROSTER:
        tag, m, kind, p, d0, reads = spec
        E = PE.Eng(m, kind, p, d0, reads, tag)
        PE.prep(E)
        u, su = WS.uchain(E)
        Etot, G0, split = WS.window_split(E)
        anch = WS.anchors_of(E, Etot, G0, split)
        prin, meta = WD.inv_checks(E, u, su)
        sizes = collections.Counter(); glued_sizes = collections.Counter()
        for (ga, gb, sA, sB, u1a, u1b, cs) in rows_of(E, su, Etot, G0, anch):
            sig, q2 = trace_cells(E, sA, sB, u1a, u1b, su, prin, tag)
            if not q2: continue
            cells = []
            for st in q2:
                (sgn, b, j, pc, dmp, cons, ncorr, junk, jD, isp, ce, y2,
                 hist) = st
                cells.append(dict(sgn=sgn, j=j, ce=ce, pc=tuple(pc),
                                  line=E.line(b, j)))
            bmin = min(c['line'] for c in cells)
            slots = collections.defaultdict(list)
            for c in cells:
                if c['line'] == bmin: slots[c['j']].append(c)
            for jv, grp in slots.items():
                sizes[len(grp)] += 1
                fk = set()
                for c in grp:
                    ib = tuple(sorted(e for e in c['ce'] if e[0] != 0))
                    fk.add((ib, c['pc']))
                if len(fk) > 1:
                    glued_sizes[len(grp)] += 1
        print(f"{tag}: bottom-group sizes {dict(sorted(sizes.items()))}; "
              f"glued-group sizes {dict(sorted(glued_sizes.items()))}")

if __name__ == "__main__":
    main()
