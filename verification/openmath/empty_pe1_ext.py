#!/usr/bin/env python3
"""empty_pe1_ext.py — EMPTY-PE1 independent verification instrument (hostile pass 1
on lean/notes/openmath/EMPTY_PROOF_2026-08-08.md @ 4eb1719).  READ-ONLY consumption
of the committed engines (imports only; touches no committed file); writes
empty_pe1_ext_results.json + stdout.

Sections:
  EXT-GRID-EL4   E-L4 unroll identity + remainder bound, exhaustive grid (pure arith).
  EXT-GRID-EL5   E-L5 (i)/(ii) + the EXACT +1-iff-Y-tight classification, same grid;
                 also: the +1 is never +2.
  EXT-TIGHT-RHO  the repair's key lemma (nowhere stated in the note): on the Y-tight
                 stratum, c+_l(1) = c_l + 1 at EVERY level 1..m-1 and the c+(1)-chain
                 remainders VANISH at every level >= 2 (so the unroll slack is 0).
  EXT-MIDSTEP    the S7 pi_1 middle step (the unconditional -1[CE0] deduction) is
                 FALSE as arithmetic: explicit countermodel + grid failure count;
                 and it HOLDS restricted to the tight boundary with Y2 = 1 (grid).
  EXT-DISPLAY    the S7 master display evaluated on the batteries' own two-exit
                 cells (all three readings of rho+_l): violation counts + witnesses,
                 while the theorem's conclusion k <= c_{m-1} holds on every cell.
  EXT-PAY        CTRL-PAY1: in-scope corner classification (slack floor = W_0; the
                 ONLY slack-0 corner = top-level full-house dumps + Y-child, d0 >= 2);
                 roster inventory scan for that corner; detector self-test on the
                 synthetic corner edge; battery edges attaining slack EXACTLY W_0.
  EXT-CPGUARD    the EDC-CPLUS "Y-unit crossed off tight0" guard is a PHANTOM: clean
                 in-scope arithmetic satisfies its firing condition with no E-L5
                 clause violated.
  EXT-TRACE      3 fresh dead rows re-traced end to end (telescope numbers, c/c+
                 chains, zero two-exit terminals), printed for the report.

Deterministic, exact arithmetic, no sampling.
Usage: python3 empty_pe1_ext.py > empty_pe1_ext_output.txt
"""
import sys, os, json
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import wmultdcx_stress as WS
import wmultdcx_derive_checks as WD
import rmengine_pe_reimpl as PE
import empty_derive_checks as EDC
from grb_order2_check import pnorm, padd, pneg, pmul, pscal, pdivmod

OUT = {}
FAIL = []


def fail(sec, msg):
    FAIL.append((sec, msg))
    print(f"EXT-FAIL [{sec}] {msg}")


# ---------- shared arithmetic ----------
def cchain(ts, es):
    """c-chain and remainders: ts[l] = t_l (1-indexed list with ts[0]=None)."""
    c, cl, rem = 0, [0], [None]
    for l in range(1, len(ts)):
        rem.append((ts[l] + c) % es[l - 1])
        c = (ts[l] + c) // es[l - 1]
        cl.append(c)
    return cl, rem


def cplus_chain(ts, es, g0, Y):
    P0 = es[0] * g0
    cp = (ts[1] + (g0 - 1) * es[0] + Y) // P0
    cps, rem = [None, cp], [None, None]
    for l in range(2, len(ts)):
        rem.append((ts[l] + cp) % es[l - 1])
        cp = (ts[l] + cp) // es[l - 1]
        cps.append(cp)
    return cps, rem


def tight_pred(ts, es, g0):
    if g0 == 1:
        t0 = (ts[1] % es[0] == es[0] - 1)
    else:
        t0 = (ts[1] == es[0] - 1)
    if not t0:
        return False
    c = ts[1] // es[0]
    for l in range(2, len(ts)):
        if (ts[l] + c) % es[l - 1] != es[l - 1] - 1:
            return False
        c = (ts[l] + c) // es[l - 1]
    return True


def eweights_of(es):
    m1 = len(es)  # es = e_0..e_{m-2}; weights w_0..w_{m-1}, w_{m-1}=1
    w = [Fraction(1)] * (m1 + 1)
    for l in range(m1 - 1, -1, -1):
        w[l] = w[l + 1] / es[l]
    return w


# ---------- EXT-GRID-EL4 / EXT-GRID-EL5 / EXT-TIGHT-RHO ----------
def grids():
    import itertools
    n4 = n5 = nrho = 0
    for m in (2, 3, 4):
        for es in itertools.product((1, 2, 3), repeat=m - 1):
            w = eweights_of(list(es))
            for g0 in (1, 2, 3):
                rngs = [range(0, 3 * es[l - 1] + 3) for l in range(1, m)]
                for tt in itertools.product(*rngs):
                    ts = [None] + list(tt)
                    cl, rem = cchain(ts, es)
                    ctop = cl[m - 1]
                    # E-L4 (g-free arithmetic)
                    if g0 == 1:
                        R = sum(ts[l] * w[l - 1] for l in range(1, m))
                        un = R - sum(rem[l] * w[l - 1] for l in range(1, m))
                        if un != ctop:
                            fail("EXT-GRID-EL4", f"unroll {es} {tt}: {un}!={ctop}")
                        if R > ctop + 1 - w[0]:
                            fail("EXT-GRID-EL4", f"R bound {es} {tt}")
                        n4 += 1
                    # E-L5
                    cp0, _ = cplus_chain(ts, es, g0, 0)
                    cp1, rem1 = cplus_chain(ts, es, g0, 1)
                    tight = tight_pred(ts, es, g0)
                    if cp0[m - 1] > ctop:
                        fail("EXT-GRID-EL5", f"(i) {es} g0={g0} {tt}")
                    if cp1[m - 1] > ctop + 1:
                        fail("EXT-GRID-EL5", f"(ii)cap {es} g0={g0} {tt}")
                    if (cp1[m - 1] == ctop + 1) != tight:
                        fail("EXT-GRID-EL5",
                             f"classification {es} g0={g0} {tt}: "
                             f"cp1={cp1[m-1]} c={ctop} tight={tight}")
                    n5 += 1
                    # repair lemma: on tight, c+_l(1)=c_l+1 all l, remainders 0 (l>=2)
                    if tight:
                        ok = all(cp1[l] == cl[l] + 1 for l in range(1, m)) and \
                             all(rem1[l] == 0 for l in range(2, m))
                        if not ok:
                            fail("EXT-TIGHT-RHO", f"{es} g0={g0} {tt}")
                        nrho += 1
    OUT["EXT-GRID-EL4"] = n4
    OUT["EXT-GRID-EL5"] = n5
    OUT["EXT-TIGHT-RHO"] = nrho
    print(f"EXT-GRID-EL4: {n4} cases, EXT-GRID-EL5: {n5} cases, "
          f"EXT-TIGHT-RHO: {nrho} tight cases — failures so far: {len(FAIL)}")


# ---------- EXT-MIDSTEP ----------
def midstep():
    """S7 middle step: line1 := floor((t1 + t*e0 + Y2 + sum_CE(a0+y)
    - sum_{CE,i=0}(P0-e0k-y))/P0)  <=?  line2 := cplus1(Y2)
    + sum_{i>=1} ceil((a0+y)/P0) - 1[CE0 nonempty].  Single i=0 edge, no i>=1
    edges (their ceil-units peel off both sides identically)."""
    import itertools
    # explicit countermodel
    e0, g0, t1, t, Y2, k, y = 2, 2, 4, 1, 0, 1, 1
    P0 = e0 * g0
    remv = P0 - e0 * k - y
    line1 = (t1 + t * e0 + Y2 + y - remv) // P0
    cp1Y = (t1 + (g0 - 1) * e0 + Y2) // P0
    line2 = cp1Y - 1
    print(f"EXT-MIDSTEP witness: e0={e0} g0={g0} P0={P0} t1={t1} t={t} Y2={Y2} "
          f"CE0 edge (k={k},y={y}, removal={remv}): line1={line1} line2={line2} "
          f"-> middle step {'FALSE' if line1 > line2 else 'holds'}")
    if line1 <= line2:
        fail("EXT-MIDSTEP", "expected countermodel did not fire")
    nfail = ntight = ntfail = 0
    nfail_t = ntfail_t = 0
    wit = wit_t = None
    for e0, g0 in itertools.product((2, 3), (1, 2, 3)):
        P0 = e0 * g0
        for t1 in range(0, 3 * P0 + 3):
            for t in range(g0):
                for Y2 in (0, 1):
                    for k in range(g0):
                        for y in (0, 1):
                            remv = P0 - e0 * k - y
                            if remv <= 0:
                                continue
                            # NOTE-AS-PRINTED numerator: the S7 display's
                            # Sum_CE(a0+y) term includes the i=0 edge's y AND
                            # the removal term re-adds it (P0-e0k-y): net +2y.
                            line1 = (t1 + t * e0 + Y2 + y - remv) // P0
                            # TRUE ledger numerator: dmp0 - ccons0 nets to -remv.
                            line1t = (t1 + t * e0 + Y2 - remv) // P0
                            line2 = (t1 + (g0 - 1) * e0 + Y2) // P0 - 1
                            if line1 > line2:
                                nfail += 1
                                if wit is None:
                                    wit = (e0, g0, t1, t, Y2, k, y)
                            if line1t > line2:
                                nfail_t += 1
                                if wit_t is None:
                                    wit_t = (e0, g0, t1, t, Y2, k, y)
                            tight0 = (t1 % e0 == e0 - 1) if g0 == 1 \
                                else (t1 == e0 - 1)
                            if tight0 and Y2 == 1:
                                ntight += 1
                                if line1 > line2:
                                    ntfail += 1
                                if line1t > line2:
                                    ntfail_t += 1
                                    fail("EXT-MIDSTEP",
                                         f"TRUE-form tight-boundary failure "
                                         f"{e0},{g0},{t1},{t},{k},{y}")
    OUT["EXT-MIDSTEP"] = dict(
        note_form=dict(grid_failures=nfail, first=wit, tight_failures=ntfail),
        true_form=dict(grid_failures=nfail_t, first=wit_t,
                       tight_failures=ntfail_t),
        tight_cases=ntight)
    print(f"EXT-MIDSTEP grid: NOTE-form failures {nfail} (first {wit}), "
          f"of which ON the tight boundary (tight0 & Y2=1): {ntfail} of "
          f"{ntight} cases — the printed step fails even where the repair "
          f"needs it, because the printed numerator double-counts y;")
    print(f"             TRUE-ledger form: {nfail_t} unconditional failures "
          f"(first {wit_t}) but {ntfail_t} failures on the tight boundary "
          f"— the repair's conditional step holds exactly there")


# ---------- battery walks (shared by EXT-DISPLAY / EXT-PAY / EXT-TRACE) ----------
def walk_row(E, sA, sB, u1a, u1b, aA, aB, su):
    R = E.R
    m = E.m
    sig = tuple(sA[l + 1] + sB[l + 1] for l in range(m))
    b0 = pscal(R, R["pi_pow"](u1a + u1b), [R["one"]])
    z = (0,) * m
    init = [(1, b0, sig, z, z, z, z, 0, None, False, (), 0)]
    q1sink = []
    out = EDC.walk(E, init, q1sink, "ext")
    if out[0] is None:
        return sig, None, None
    init2 = []
    for st in q1sink:
        sgn, b, j, pc, dmp, cons, ncorr, junk, _, _, ce, _ = st
        for (cD, jD) in E.Dcells:
            Lc, Xc, Yc = E.digit_split(b, cD)
            js = tuple(j[l] + jD[l] for l in range(m))
            for (cc, jtag, dj0) in ((Lc, 0, 0), (Xc, 1, 0), (Yc, 1, 1)):
                if not pnorm(R, cc):
                    continue
                jj = list(js)
                jj[0] += dj0
                dd = list(dmp)
                dd[0] += dj0
                init2.append((sgn, cc, tuple(jj), pc, tuple(dd), cons,
                              ncorr, junk + jtag, tuple(jD), False, ce, dj0))
    q2sink = []
    out2 = EDC.walk(E, init2, q2sink, "ext")
    if out2[0] is None:
        return sig, None, None
    return sig, q1sink, q2sink


def track_rows(E, su):
    R = E.R
    m = E.m
    Etot, G0, split = WS.window_split(E)
    anch = WS.anchors_of(E, Etot, G0, split)
    etop = E.e[m - 1]
    seen = set()
    rows = []
    for ga in range(G0, G0 + Etot):
        aA, sA, u1a = anch[ga]
        for gb in range(G0, G0 + Etot):
            aB, sB, u1b = anch[gb]
            if not (sA[m + 1] == E.e[m] - 1 and sB[m + 1] == E.e[m] - 1):
                continue
            E1, _ = pdivmod(R, pmul(R, aA, aB), E.Phis[m])
            if not pnorm(R, E1):
                continue
            key = tuple(sorted([(tuple(sA[l] for l in range(1, m + 2)), u1a),
                                (tuple(sB[l] for l in range(1, m + 2)), u1b)]))
            if key in seen:
                continue
            seen.add(key)
            pools, cs, Dd, top = WS.pools_of(E, sA, sB, su)
            ctop = cs[-1] if cs else 0
            kdef = 2 * etop - Dd
            rows.append((ga, gb, kdef, ctop, cs, sA, sB, u1a, u1b, anch))
    return rows


def eval_display(E, W, st, sig, su, cs, kdef):
    m = E.m
    sign, b, j, pc, dmp, cons, ncorr, junk, jD, prin, ce, y2 = st
    ts = [None] + [sig[l - 1] + su[l] for l in range(1, m)]
    es = [E.e[l] for l in range(m - 1)]
    ctop = cs[-1] if cs else 0
    cl, rem = cchain(ts, es)
    assert cl[1:] == list(cs), (cl, cs)
    _, rem1 = cplus_chain(ts, es, E.g[0], y2)
    tight = tight_pred(ts, es, E.g[0])
    r_top = ncorr[m - 1]
    ce0 = any(i == 0 for (i, k, a, y) in ce)
    ce_int = [(i, k) for (i, k, a, y) in ce if 1 <= i <= m - 2]
    W1 = W[1] if m >= 3 else Fraction(1)
    base = ctop + (1 if (tight and y2 == 1) else 0) \
        - sum((E.e[i] - 1) * W[i] for (i, k, a, y) in ce if 1 <= i <= m - 2) \
        - (E.e[m - 1] - 1) * r_top - (W1 if ce0 else 0) \
        - j[m - 1] - sum(W[l] * j[l] for l in range(1, m - 1))
    rhs = {"A1": base - sum(rem[l] * W[l - 1] for l in range(2, m)),
           "A2": base - sum(rem1[l] * W[l - 1] for l in range(2, m)),
           "B": base - sum((E.e[l - 1] - 1 - rem[l]) * W[l - 1]
                           for l in range(2, m))}
    return {rd: (kdef > v) for rd, v in rhs.items()}, \
        dict(r=r_top, nint=len(ce_int), ce0=ce0, y2=y2, tight=tight,
             jtop=j[m - 1])


DISPLAY_TOWERS = ["W3DEEP4", "W3TRK1", "W3DIR", "W3G2A", "W3G2B",
                  "W4DEEP", "EQ3G2B", "EQ3T3B"]


def display_and_pay():
    v = {"A1": 0, "A2": 0, "B": 0}
    wit = {}
    ncells = nrows = 0
    thm_breach = 0
    minslack = None
    slack_w0_edge = None
    nedges = 0
    for spec in list(WS.ROSTER) + list(EDC.FRESH_ROSTER):
        tag = spec[0]
        if tag not in DISPLAY_TOWERS:
            continue
        E = PE.Eng(spec[1], spec[2], spec[3], spec[4], spec[5], tag)
        PE.prep(E)
        u, su = WS.uchain(E)
        W = EDC.pweights(E)
        rows = track_rows(E, su)
        live = [r for r in rows if r[2] <= r[3]]
        live.sort(key=lambda r: (r[2] != r[3],))  # at-equality rows first
        for (ga, gb, kdef, ctop, cs, sA, sB, u1a, u1b, anch) in live[:25]:
            sig, q1, q2 = walk_row(E, sA, sB, u1a, u1b,
                                   anch[ga][0], anch[gb][0], su)
            if q2 is None:
                continue
            nrows += 1
            for st in q2:
                ncells += 1
                if kdef > ctop:
                    thm_breach += 1
                vio, meta = eval_display(E, W, st, sig, su, cs, kdef)
                for rd in v:
                    if vio[rd]:
                        v[rd] += 1
                        if rd not in wit:
                            wit[rd] = dict(tower=tag, key=(ga, gb), kdef=kdef,
                                           c=ctop, **meta)
                # per-edge payment slacks (E-L2 pure form)
                m = E.m
                _, _, _, _, _, _, _, _, _, _, ce, _ = st
                for (i, k, avec, ty) in ce:
                    nedges += 1
                    pay = (E.P[i] - E.e[i] * k) * W[i] if i <= m - 2 \
                        else Fraction(1)
                    lhs = sum(avec[l] * W[l] for l in
                              range(min(i, len(avec)))) + ty * W[0]
                    sl = pay - lhs
                    if minslack is None or sl < minslack:
                        minslack = sl
                    if sl == W[0] and slack_w0_edge is None:
                        slack_w0_edge = dict(tower=tag, i=i, k=k,
                                             avec=list(avec), y=ty,
                                             W0=str(W[0]))
    OUT["EXT-DISPLAY"] = dict(rows=nrows, cells=ncells, violations=v,
                              witnesses=wit, theorem_breaches=thm_breach)
    OUT["EXT-PAY-battery"] = dict(edges=nedges, min_slack=str(minslack),
                                  slack_eq_W0_edge=slack_w0_edge)
    print(f"EXT-DISPLAY: {nrows} live rows re-walked, {ncells} two-exit cells; "
          f"S7-display violations A1={v['A1']} A2={v['A2']} B={v['B']}; "
          f"theorem breaches (k>c): {thm_breach}")
    for rd, w in wit.items():
        print(f"  first {rd}-witness: {w}")
    print(f"EXT-PAY battery: {nedges} edges, min pure-form slack {minslack}, "
          f"slack==W0 edge: {slack_w0_edge}")
    if thm_breach:
        fail("EXT-DISPLAY", "theorem conclusion breached")


def pay_corners_and_inventory():
    import itertools
    # (a) in-scope corner classification, pure arithmetic
    bad = 0
    corner_only = True
    n = 0
    for m in (2, 3):
        for eg in itertools.product(((1, 1), (1, 2), (2, 1), (2, 2), (3, 1),
                                     (2, 3), (3, 2)), repeat=m):
            es = [x[0] for x in eg]
            gs = [x[1] for x in eg]
            Ps = [e * g for e, g in eg]
            d0_1 = True   # d0 = 1 branch: y = 0 forced
            d0_2 = all(e >= 2 for e in es)  # d0 >= 2 branch needs all e >= 2
            Wl = [Fraction(1)] * (m + 1)
            for l in range(m - 1, -1, -1):
                Wl[l] = Wl[l + 1] / Ps[l]
            W = Wl[:m] + [Fraction(1)]
            # levels are 0..m here standing for 0..m-1 with top = m; treat top
            # as index m with W=1, pay=1
            for i in list(range(m)) + ["top"]:
                if i == "top":
                    ii, pay = m, Fraction(1)
                    ks = [0]
                else:
                    ii = i
                    ks = range(gs[i])
                for k in ks:
                    if i != "top":
                        pay = (Ps[i] - es[i] * k) * Wl[i]
                    for full in (True, False):
                        for y in (0, 1):
                            for branch in ("d01", "d02"):
                                if branch == "d01" and y == 1:
                                    continue
                                if branch == "d02" and not d0_2:
                                    continue
                                lhs = sum((Ps[l] - 1 if full else Ps[l] - 2)
                                          * Wl[l] for l in range(ii)
                                          if Ps[l] >= (1 if full else 2)) \
                                    + y * Wl[0]
                                sl = pay - lhs
                                n += 1
                                if sl < Wl[0]:
                                    bad += 1
                                    if not (i == "top" and full and y == 1):
                                        corner_only = False
    OUT["EXT-PAY-corners"] = dict(cases=n, below_W0=bad,
                                  only_top_fullhouse_Y=corner_only)
    print(f"EXT-PAY corners: {n} in-scope corner cases, {bad} with slack < W0, "
          f"ALL at the top-full-house+Y corner: {corner_only}")
    # (b) roster inventory scan: does any tower's TOP correction table contain a
    # full-house dump vector (a_l = P_l - 1 for every l < m-1)?
    found = []
    topmax = {}
    for spec in list(WS.ROSTER) + list(EDC.FRESH_ROSTER):
        tag, m, kind, p, d0, reads = spec
        E = PE.Eng(m, kind, p, d0, reads, tag)
        PE.prep(E)
        W = EDC.pweights(E)
        corr = E.corr_table()
        best = Fraction(0)
        for (k, dcells) in corr[m - 1]:
            for (cd, av) in dcells:
                a = [av[l] if l < len(av) else 0 for l in range(m - 1)]
                val = sum(a[l] * W[l] for l in range(m - 1))
                if val > best:
                    best = val
                if all(a[l] == E.P[l] - 1 for l in range(m - 1)):
                    found.append(dict(tower=tag, k=k, a=a, d0=d0))
        topmax[tag] = str(best) + f" (1-W0 = {1 - W[0]}, d0={d0})"
    OUT["EXT-PAY-inventory"] = dict(fullhouse_top_dcells=found)
    detail = found if found else ("(NONE - the CTRL-PAY1 corner is unrealizable "
                                  "on these rosters at inventory level, before "
                                  "any path)")
    print(f"EXT-PAY inventory: full-house top-level d-cells across all "
          f"{len(list(WS.ROSTER)) + len(EDC.FRESH_ROSTER)} roster towers: "
          f"{len(found)} {detail}")
    # (c) detector self-test: synthetic corner edge on a d0>=2 shape
    m = 3
    Ps = [4, 3, 2]
    Wl = [Fraction(1)] * m
    for l in range(m - 2, -1, -1):
        Wl[l] = Wl[l + 1] / Ps[l]
    lhs = sum((Ps[l] - 1) * Wl[l] for l in range(m - 1)) + Wl[0]
    pay = Fraction(1)
    fires = lhs > pay - Wl[0]
    OUT["EXT-PAY-selftest"] = dict(lhs=str(lhs), pay=str(pay), fires=fires)
    print(f"EXT-PAY detector self-test (synthetic top edge, full house + Y, "
          f"P=(4,3)): lhs={lhs}, pay={pay}, CTRL-PAY1 condition fires: {fires}")
    if not fires:
        fail("EXT-PAY", "detector failed to fire on the synthetic corner")


def cpguard():
    e0, g0, t1 = 2, 2, 5
    P0 = e0 * g0
    res0 = (t1 + (g0 - 1) * e0 + 0) // P0
    res1 = (t1 + (g0 - 1) * e0 + 1) // P0
    tight0 = (t1 == e0 - 1)
    c1 = t1 // e0
    guard_fires = (res1 > res0 and not tight0)
    el5_ok = (res0 <= c1) and (res1 <= c1 + 1) and \
        ((res1 == c1 + 1) == tight_pred([None, t1], [e0], g0))
    OUT["EXT-CPGUARD"] = dict(e0=e0, g0=g0, t1=t1, res0=res0, res1=res1,
                              c1=c1, guard_fires=guard_fires, el5_ok=el5_ok)
    print(f"EXT-CPGUARD: e0={e0} g0={g0} t1={t1}: cplus1(0)={res0} "
          f"cplus1(1)={res1} c1={c1}; runner guard condition fires: "
          f"{guard_fires}; every E-L5 clause holds: {el5_ok} "
          f"-> the guard is a phantom (firing would not witness a lemma breach)")
    if not (guard_fires and el5_ok):
        fail("EXT-CPGUARD", "phantom demonstration failed")


TRACE_TOWERS = ["EQ3T4A", "EQ3G2A", "EQ4T3A"]


def traces():
    recs = []
    for spec in EDC.FRESH_ROSTER:
        tag = spec[0]
        if tag not in TRACE_TOWERS:
            continue
        E = PE.Eng(spec[1], spec[2], spec[3], spec[4], spec[5], tag)
        PE.prep(E)
        u, su = WS.uchain(E)
        W = EDC.pweights(E)
        m = E.m
        rows = track_rows(E, su)
        dead = [r for r in rows if r[2] > r[3]]
        (ga, gb, kdef, ctop, cs, sA, sB, u1a, u1b, anch) = dead[0]
        sig, q1, q2 = walk_row(E, sA, sB, u1a, u1b, anch[ga][0], anch[gb][0], su)
        ts = [None] + [sig[l - 1] + su[l] for l in range(1, m)]
        es = [E.e[l] for l in range(m - 1)]
        cl, rem = cchain(ts, es)
        cp0, _ = cplus_chain(ts, es, E.g[0], 0)
        cp1, _ = cplus_chain(ts, es, E.g[0], 1)
        # telescope at every terminal of this row (stage-1 exits + stage-2 cells
        # + a sample of leaves): recompute E-L1 independently
        tel_ok = 0
        for st in list(q1) + list(q2):
            sign, b, j, pc, dmp, cons, ncorr, junk, jD, prin, ce, y2 = st
            jDv = jD if jD is not None else (0,) * m
            tel = sum(W[l] * (sig[l] + jDv[l] + dmp[l]
                              - (cons[l] - E.P[l] * pc[l]) - j[l])
                      for l in range(m - 1))
            if tel != pc[m - 2]:
                fail("EXT-TRACE", f"{tag} telescope mismatch")
            else:
                tel_ok += 1
        rec = dict(tower=tag, key=(ga, gb), m=m, e=[E.e[l] for l in range(m)],
                   g=[E.g[l] for l in range(m)], d0=E.d0, sig=list(sig),
                   su=[su[l] for l in range(1, m + 1)], t=[None] + [ts[l] for
                   l in range(1, m)], c=cl[1:], kdef=kdef, D=2 * E.e[m - 1] -
                   kdef if False else None, cplus0=cp0[m - 1],
                   cplus1=cp1[m - 1], tight=tight_pred(ts, es, E.g[0]),
                   n_exit1=len(q1), n_twoexit=len(q2), telescope_checked=tel_ok)
        recs.append(rec)
        print(f"EXT-TRACE {tag} row {(ga, gb)}: e={rec['e']} g={rec['g']} "
              f"d0={E.d0} sigma={list(sig)} s_l(u_l)={rec['su']} "
              f"t={rec['t'][1:]} c-chain={cl[1:]} kdef={kdef} "
              f"c+(0)={cp0[m-1]} c+(1)={cp1[m-1]} tight={rec['tight']} "
              f"stage1-exits={len(q1)} TWO-EXIT TERMINALS={len(q2)} "
              f"(telescope re-verified at {tel_ok} terminals)")
        if len(q2) != 0:
            fail("EXT-TRACE", f"{tag} dead row has two-exit terminals")
        if kdef <= ctop:
            fail("EXT-TRACE", f"{tag} selected row not dead")
    OUT["EXT-TRACE"] = recs


def main():
    grids()
    midstep()
    display_and_pay()
    pay_corners_and_inventory()
    cpguard()
    traces()
    OUT["engine_violations_during_ext"] = list(EDC.VIOL)
    OUT["failures"] = FAIL
    print("-" * 70)
    print(f"engine-harness violations raised during ext walks: {len(EDC.VIOL)}")
    print(f"EXT failures: {len(FAIL)}")
    with open(os.path.join(HERE, "empty_pe1_ext_results.json"), "w") as f:
        json.dump(OUT, f, indent=1, default=str)
    print("results -> empty_pe1_ext_results.json")


if __name__ == "__main__":
    main()
