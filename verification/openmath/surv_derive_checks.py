#!/usr/bin/env python3
"""surv_derive_checks.py — (SURV-(m+1))(i) COMPOSER unit: the machine leg of
lean/notes/openmath/SURV_PROOF_2026-08-08.md.

Object (the WMULTDCX_2026-08-08.md S9 box, clause (i)):

    (SURV-(m+1))(i):  on TRACK, (H1)-(H2), c_{m-1} >= k := 2e_{m-1} - D
    =>  Q^1 != 0.

The dedicated (SURV) instrument unit returned a NULL verdict (never ran),
so this runner doubles as the instrument: it measures the BOTTOM-STRATUM
STRUCTURE of Q^1 on live rows (the min-line cell census) that decides
between the composer routes
  (A) unique bottom cell  -> ultrametric separation closes (i) on the row;
  (B) multi-cell strata   -> the residue algebra (DEV-at-depth) is needed.

Consumed committed engines, byte-untouched (md5-pinned): the PE engine
(rmengine_pe_reimpl.Eng: towers, weights w_m, exact reads R_{m,.}, cells,
lines, digit_split, corr_table), the sealed stress roster + selection
(wmultdcx_stress, wmultdcx_derive_checks), and the (EMPTY) instrumented
walker (empty_derive_checks.walk — per-edge correction logging).

VERDICT families (predicted 0 violations — each backs a displayed claim
of the note):
  SDK-PIN     consumed committed runners match the note-pinned md5s.
  SDK-CONS    both stage trees reassemble the canonical divisions
              (stage-1 exits = E1IH, stage-2 exits = Q^1) per traced row.
  SDK-EMPTY   law-dead traced row => zero two-exit terminals (EMPTY shadow).
  SDK-DIGIT   every two-exit terminal cell C has w_m(cellpoly) == line(C)
              EXACTLY (single-digit weight exactness, incl. top exponents
              >= P_{m-1} if any occur — counter jtop_ge_P).
  SDK-LINE    W-D5 at my extraction: junk-free cells sit EXACTLY on
              line = lamhat + sum_l pi_l q_l; junk cells strictly above.
  SDK-CASC    on every all-g=1 live row with (STK): the cascade cell
              (ce = (), junk = 0, principal d-cell, Y2 = 0) EXISTS, is
              UNIQUE as such, has profile pi_l = c_l (all l), r = 0,
              exits = 2, top exponent c_{m-1} - k, interior exponents
              EXACTLY the pool remainders rho_l := pool_l mod e_{l-1}
              (the E-L4 remainders), line exactly
              lamhat + sum c_l q_l, coefficient valuation
              w0(b) = u1 + u1' + u0, and normalized residue EXACTLY
              res(b0bar)*res(cprinbar) != 0  (S-L1's machine leg).
  SDK-GRID    every NETTED min-line cell is on-grid at its own line
              (L-GRID shadow at the bottom stratum).
  SDK-SEP     on live rows whose NETTED bottom stratum is a single cell:
              w_m(Q^1) == beta_min  (S-L2's instance form); and never
              w_m(Q^1) < beta_min anywhere (subadditivity).
  HARNESS     violations raised inside the consumed engines.

CENSUSES (measured, no prediction — the instrument layer):
  MINSTRAT    histogram of netted bottom-stratum sizes over live rows,
              split by threshold (k = c_{m-1}) vs above-threshold (k <
              c_{m-1}) vs direct (k <= 0); per-row records in the json.
  CASCMIN     rows where the cascade cell IS the unique netted bottom
              cell; rows where the bottom is attained by non-cascade
              cells (with their profiles).
  READADD     per live row with w_m(Q^1) == beta_min: does
              R_{m,beta_min}(Q^1) == sum over netted min-line cells of
              res(bbar)*zh(j; beta_min)?  (read-additivity shadow; the
              cellwise term for top exponents >= P_{m-1} is NOT a
              displayed lemma — mismatches are recorded, not violations.)
  WMQ1        w_m(Q^1) - beta_min distribution (0 = bottom survives).
  CGRP        the CASCADE GROUP census ((SURV-CASC) lead): per all-g=1
              live row with a cascade cell — the number of two-exit
              cells sharing the cascade's exponent vector j, and whether
              the netted group SURVIVES at the cascade line (net b != 0
              with w0 unchanged).  cgrp_survives == False anywhere would
              REFUTE the single-slot route; counters cgrp_partnered /
              cgrp_survived / cgrp_KILLED.
  CANCGRADE   on bottom-cancelled rows (CTRL-CANCEL): the full netted
              grade spectrum — which line and which exponent vector
              survive minimally (is it the cascade slot?).
  REDWIN      every two-exit terminal reduced at every level (j_l <=
              P_l - 1 incl. the top)?  counters red_all / red_topbreach
              — the (RW) pin of the note's S5 consumption is
              instance-censused here, never assumed.

CONTROLS (teeth: each must fire >= once, else CONTROL FAILURE disclosed):
  CTRL-MULTI  some live row has netted bottom-stratum size >= 2 (the
              residue-cancellation question is instance-realized).
  CTRL-ABOVE  some live row strictly above threshold (k < c_{m-1}) is
              traced (else the deep side is uncovered).
  CTRL-NONCASC some netted bottom cell is NOT the cascade cell (else
              uniqueness is only ever pattern-matched on cascades).
  CTRL-CANCEL fires iff some live row has w_m(Q^1) > beta_min (bottom-
              stratum TOTAL cancellation observed).  May stay 0: its
              non-firing IS the headline datum (disclosed either way,
              never a violation).

Deterministic, exact integer/polynomial arithmetic, no sampling, no seed.
Usage: python3 surv_derive_checks.py > surv_derive_checks_output.txt
"""
import sys, os, time, json, hashlib

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import wmultdcx_stress as WS                    # read-only consumption
import wmultdcx_derive_checks as WD             # read-only consumption
import rmengine_pe_reimpl as PE                 # read-only consumption
import empty_derive_checks as ED                # read-only consumption (walk)
from grb_order2_check import pnorm, padd, pneg, pmul, pscal, pdivmod
from grb_order2_check import w0

VIOL = []
CNT = {}
CTRL = {k: 0 for k in ("CTRL-MULTI", "CTRL-ABOVE", "CTRL-NONCASC",
                       "CTRL-CANCEL")}

PINS = {
    "wmultdcx_stress.py":        "15315cca59c87e6c2001ea744c50aab5",
    "wmultdcx_derive_checks.py": "bea1a43d619a3c91a9a0b2f32c0920c0",
    "rmengine_pe_reimpl.py":     "103c1a9c99e2b4a3e8b63c93cbf87e25",
    "grb_order2_check.py":       "dab62713175363a7185211890019ae2f",
    "empty_derive_checks.py":    "8fed92402bcffe6e0c536f1f9d847612",
}

def note(fam, n=1): CNT[fam] = CNT.get(fam, 0) + n
def viol(fam, tag, detail):
    VIOL.append((fam, tag, detail))
    print(f"VIOLATION [{fam}] {tag}: {detail}")

def harvest(tag):
    """Consumed engines keep their own violation lists; anything new there
    is a HARNESS violation of this unit."""
    for src, lst in (("PE", PE.VIOL), ("ED", ED.VIOL), ("WS", WS.VIOL),
                     ("WD", WD.VIOL)):
        while len(lst) > harvest.seen[src]:
            viol("HARNESS", tag, f"{src} engine violation: "
                 f"{lst[harvest.seen[src]]}")
            harvest.seen[src] += 1
harvest.seen = {"PE": 0, "ED": 0, "WS": 0, "WD": 0}

# ---------------- one traced row: bottom-stratum extraction ----------------
def trace_row(E, sA, sB, u1a, u1b, aA, aB, su, cs, Dd, kdef, live, key,
              prin, recs, tag):
    R = E.R; m = E.m
    sig = tuple(sA[l + 1] + sB[l + 1] for l in range(m))
    b0 = pscal(R, R["pi_pow"](u1a + u1b), [R["one"]])
    prodp = pmul(R, aA, aB)
    if pnorm(R, padd(R, prodp, pneg(R, E.cellpoly(b0, sig)))):
        viol("HARNESS", tag, f"a*a' != formal cell at {key}"); return
    pools = WS.pools_of(E, sA, sB, su)[0]
    rho = [pools[l] % E.e[l] for l in range(m - 1)]   # rho_{l+1} 0-indexed
    z = (0,) * m
    init = [(1, b0, sig, z, z, z, z, 0, None, False, (), 0)]
    q1sink = []
    out = ED.walk(E, init, q1sink, tag)
    if out[0] is None:
        harvest(tag); return
    leaves1, _ = out
    E1c, E0c = pdivmod(R, prodp, E.Phis[m])
    if WD.cellsum(E, q1sink) != pnorm(R, E1c):
        viol("SDK-CONS", tag, f"stage-1 exit sum != E1IH at {key}")
    # stage-2 seeding (the L-NORM split of b_Y * c_D), mirroring the
    # committed empty_derive_checks.trace_row seeding verbatim
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
    if out2[0] is None:
        harvest(tag); return
    Q1c = pdivmod(R, pmul(R, E1c, E.Chat), E.Phis[m])[0]
    if WD.cellsum(E, q2sink) != pnorm(R, Q1c):
        viol("SDK-CONS", tag, f"stage-2 exit sum != Q1 at {key}")
    harvest(tag)
    ctop = cs[-1] if cs else 0
    lawlive = (kdef <= ctop)
    if not lawlive:
        if len(q2sink) > 0:
            viol("SDK-EMPTY", tag,
                 f"law-dead row with {len(q2sink)} two-exit cells at {key}")
        note("dead_traced")
        recs.append(dict(tower=tag, key=list(key), cs=list(cs), D=Dd,
                         kdef=kdef, live=False, ncells=0))
        return
    note("live_traced")
    if kdef < ctop: CTRL["CTRL-ABOVE"] += 1
    # ---- per-cell data ----
    q = WD.q_quanta(E)                     # q[l], 1 <= l <= m-1
    lamhat = E.line(b0, sig) + E.gam[m + 1] - 2 * E.wmPhi
    allg1 = (E.g[0] == 1)                  # interior g == 1 pinned by roster
    a_, r_, b_, stock1 = WD.greedy_chains(E, sig, su, cs)
    stk = (stock1 >= E.P[m - 1])
    cells = []
    for st in q2sink:
        sgn, b, j, pc, dmp, cons, ncorr, junk, jD, isp, ce, y2 = st
        ln = E.line(b, j)
        # SDK-DIGIT: single-digit weight exactness on the terminal cell
        if E.wm(E.cellpoly(b, j)) != ln:
            viol("SDK-DIGIT", tag,
                 f"w_m(cell) != line at {key}: j={j}")
        if j[m - 1] >= E.P[m - 1]:
            note("jtop_ge_P")
        # SDK-LINE: the W-D5 line law at my extraction
        floor = lamhat + sum(pc[l - 1] * q[l] for l in range(1, m))
        if junk == 0 and ln != floor:
            viol("SDK-LINE", tag,
                 f"junk-free cell off its line at {key}: {ln} != {floor}")
        if junk > 0 and ln <= floor:
            viol("SDK-LINE", tag,
                 f"junk cell not strictly above the line at {key}")
        cells.append(dict(sgn=sgn, b=b, j=j, pc=pc, ncorr=ncorr, junk=junk,
                          jD=jD, prin=isp, ce=ce, y2=y2, line=ln))
        # REDWIN census: reduced at every level?
        if all(j[l] <= E.P[l] - 1 for l in range(m)):
            note("red_all")
        else:
            note("red_topbreach")
    # ---- the cascade cell (S-L1's object) ----
    casc = [c for c in cells if c["ce"] == () and c["junk"] == 0
            and c["prin"] and c["y2"] == 0]
    casc_rec = None
    if allg1 and stk:
        if len(casc) != 1:
            viol("SDK-CASC", tag,
                 f"cascade count {len(casc)} != 1 on all-g=1 live row {key}")
        else:
            c = casc[0]
            cprin = next(cD for (cD, jD) in E.Dcells if tuple(jD) == prin)
            ok = True
            if list(c["pc"][:m - 1]) != list(cs):
                viol("SDK-CASC", tag, f"cascade profile {c['pc']} != c-chain "
                     f"{cs} at {key}"); ok = False
            if c["ncorr"][m - 1] != 0 or c["pc"][m - 1] != 2:
                viol("SDK-CASC", tag, f"cascade r/exits wrong at {key}")
                ok = False
            if c["j"][m - 1] != ctop - kdef:
                viol("SDK-CASC", tag,
                     f"cascade top exponent {c['j'][m-1]} != c-k="
                     f"{ctop - kdef} at {key}"); ok = False
            if list(c["j"][:m - 1]) != rho:
                viol("SDK-CASC", tag,
                     f"cascade interior exponents {c['j'][:m-1]} != pool "
                     f"remainders rho={rho} at {key}"); ok = False
            lpred = lamhat + sum(cs[l - 1] * q[l] for l in range(1, m))
            if c["line"] != lpred:
                viol("SDK-CASC", tag,
                     f"cascade line {c['line']} != lamhat+sum c*q={lpred} "
                     f"at {key}"); ok = False
            if w0(R, c["b"]) != (u1a + u1b) + w0(R, cprin):
                viol("SDK-CASC", tag, f"cascade coeff w0 != u1+u1'+u0 at {key}")
                ok = False
            want = E.kmul(E.resKm(b0), E.resKm(cprin))
            if E.kisz(want):
                viol("SDK-CASC", tag, f"residue product ZERO at {key} "
                     f"(field breach)"); ok = False
            if not E.keq(E.resKm(c["b"]), want):
                viol("SDK-CASC", tag,
                     f"cascade residue != res(b0)*res(cprin) at {key}")
                ok = False
            if ok: note("casc_verified")
            casc_rec = c
    elif casc:
        casc_rec = casc[0] if len(casc) == 1 else None
        note("casc_offscope_present")
    # ---- the CASCADE GROUP ((SURV-CASC) lead): net ALL cells at casc j ----
    cgrp_n = cgrp_survives = None
    if casc_rec is not None:
        grp = [c for c in cells if c["j"] == casc_rec["j"]]
        cgrp_n = len(grp)
        acc = []
        for c in grp:
            acc = padd(R, acc, c["b"] if c["sgn"] > 0 else pneg(R, c["b"]))
        acc = pnorm(R, acc)
        cgrp_survives = bool(acc and
                             E.line(acc, casc_rec["j"]) == casc_rec["line"])
        if cgrp_n > 1: note("cgrp_partnered")
        note("cgrp_survived" if cgrp_survives else "cgrp_KILLED")
    # ---- the bottom stratum, netted ----
    beta_min = min(c["line"] for c in cells)
    raw_min = [c for c in cells if c["line"] == beta_min]
    groups = {}
    for c in raw_min:
        groups.setdefault(c["j"], []).append(c)
    netted = []
    for jv, grp in groups.items():
        acc = []
        for c in grp:
            acc = padd(R, acc, pscal(R, R["pi_pow"](0), c["b"])
                       if c["sgn"] > 0 else pneg(R, c["b"]))
        acc = pnorm(R, acc)
        if acc and E.line(acc, jv) == beta_min:
            netted.append((acc, jv, grp))
    nmin_raw, nmin_net = len(raw_min), len(netted)
    if nmin_net >= 2: CTRL["CTRL-MULTI"] += 1
    casc_is_min = bool(casc_rec and casc_rec["line"] == beta_min)
    casc_is_unique_min = bool(casc_is_min and nmin_net == 1 and
                              netted[0][1] == casc_rec["j"])
    if any(not (len(grp) == 1 and grp[0] is casc_rec) for (_, _, grp) in netted):
        CTRL["CTRL-NONCASC"] += 1
    # ---- w_m(Q^1) vs beta_min (S-L2 shadow) ----
    wq = E.wm(Q1c)
    if not pnorm(R, Q1c):
        viol("SDK-SEP", tag, f"LIVE row with Q1 == 0 at {key} (law breach)")
        return
    if wq < beta_min:
        viol("SDK-SEP", tag,
             f"w_m(Q1)={wq} < beta_min={beta_min} at {key} (subadditivity)")
    canc_anat = None
    if wq > beta_min:
        CTRL["CTRL-CANCEL"] += 1
        note("bottom_cancelled")
        # CANCGRADE anatomy: the full netted grade spectrum of the multiset
        allg = {}
        for c in cells:
            allg.setdefault(c["j"], []).append(c)
        spec = []
        for jv, grp in allg.items():
            acc = []
            for c in grp:
                acc = padd(R, acc, c["b"] if c["sgn"] > 0 else pneg(R, c["b"]))
            acc = pnorm(R, acc)
            if acc:
                spec.append((E.line(acc, jv), list(jv), len(grp)))
        spec.sort()
        canc_anat = dict(
            surviving_spectrum=spec[:6],
            min_surviving_line=spec[0][0] if spec else None,
            min_is_cascade_slot=bool(
                spec and casc_rec is not None and
                tuple(spec[0][1]) == casc_rec["j"] and
                spec[0][0] == casc_rec["line"]),
            wmQ1_eq_min_surviving=bool(spec and spec[0][0] == wq))
        print(f"  CANCGRADE [{tag}{list(key)}]: bottom beta_min={beta_min} "
              f"netted to ZERO; surviving spectrum head={spec[:3]} "
              f"w_m(Q1)={wq} cascade_slot_min="
              f"{canc_anat['min_is_cascade_slot']}")
    if nmin_net == 1 and wq != beta_min:
        viol("SDK-SEP", tag,
             f"UNIQUE netted bottom cell but w_m(Q1)={wq} != "
             f"beta_min={beta_min} at {key}")
    # ---- read additivity at the bottom (census) ----
    read_ok = None
    if wq == beta_min:
        acc = E.Km["zero"]
        gridok = True
        for (bb, jv, _) in netted:
            zv = E.zh(jv, beta_min)
            if zv is None:
                viol("SDK-GRID", tag,
                     f"netted min cell OFF-GRID at its own line at {key}: {jv}")
                gridok = False; continue
            acc = E.Km["add"](acc, E.kmul(E.resKm(bb), zv))
        if gridok:
            read_ok = bool(E.keq(acc, E.Rvm(Q1c)))
            note("read_match" if read_ok else "read_MISMATCH")
    thresh = (kdef == ctop)
    strat = "thresh" if thresh else ("above" if kdef > 0 else "direct")
    note(f"minstrat_{strat}_n{min(nmin_net, 4)}")
    if casc_is_unique_min: note(f"cascuniq_{strat}")
    recs.append(dict(
        tower=tag, key=list(key), cs=list(cs), D=Dd, kdef=kdef, live=True,
        allg1=allg1, stk=bool(stk), ncells=len(cells),
        beta_min=beta_min, nmin_raw=nmin_raw, nmin_net=nmin_net,
        wmQ1=wq, wq_minus_beta=wq - beta_min,
        casc_found=bool(casc_rec is not None), casc_is_min=casc_is_min,
        casc_unique_min=casc_is_unique_min,
        casc_line=(casc_rec["line"] if casc_rec else None),
        read_ok=read_ok, thresh=thresh, strat=strat,
        cgrp_n=cgrp_n, cgrp_survives=cgrp_survives, canc_anat=canc_anat,
        min_profiles=sorted(set(tuple(c["pc"]) for c in raw_min)),
        min_junk=sorted(set(c["junk"] for c in raw_min)),
        min_rvals=sorted(set(c["ncorr"][m - 1] for c in raw_min)),
        min_ncorr_tot=sorted(set(sum(c["ncorr"]) for c in raw_min)),
        min_jtops=sorted(set(c["j"][m - 1] for c in raw_min))))

# ---------------- sealed phase: the 412-row selection, VERBATIM ----------------
def run_sealed_tower(spec, results):
    tag, m, kind, p, d0, reads = spec
    t0 = time.time()
    E = PE.Eng(m, kind, p, d0, reads, tag)
    PE.prep(E)
    harvest(tag)
    u, su = WS.uchain(E)
    if u is None:
        viol("HARNESS", tag, "u-chain failed"); return
    Etot, G0, split = WS.window_split(E)
    anch = WS.anchors_of(E, Etot, G0, split)
    etop = E.e[m - 1]
    prin, _ = WD.inv_checks(E, u, su)
    harvest(tag)
    R = E.R
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
    recs = []
    for key, (ga, gb, cs, Dd, kdef, meas, sA, sB, u1a, u1b) in chosen:
        trace_row(E, sA, sB, u1a, u1b, anch[ga][0], anch[gb][0], su,
                  cs, Dd, kdef, meas, (ga, gb), prin, recs, tag)
    live = [r for r in recs if r["live"]]
    print(f"-- SEALED {tag} m={m} {kind},p={p},d0={d0} g0={E.g[0]}: "
          f"traced={len(recs)} live={len(live)} "
          f"cells={sum(r['ncells'] for r in live)} ({time.time()-t0:.1f}s)")
    results.append(dict(phase="sealed", tag=tag, m=m, kind=kind, p=p, d0=d0,
                        reads=reads, rows=recs))

# ---------------- fresh phase: LIVE rows, per-stratum caps ----------------
def run_fresh_tower(spec, results):
    tag, m, kind, p, d0, reads = spec
    t0 = time.time()
    E = PE.Eng(m, kind, p, d0, reads, tag)
    PE.prep(E)
    harvest(tag)
    u, su = WS.uchain(E)
    if u is None:
        viol("HARNESS", tag, "u-chain failed"); return
    Etot, G0, split = WS.window_split(E)
    anch = WS.anchors_of(E, Etot, G0, split)
    etop = E.e[m - 1]
    prin, _ = WD.inv_checks(E, u, su)
    harvest(tag)
    R = E.R
    seen = set()
    live_pool = {}
    for ga in range(G0, G0 + Etot):
        aA, sA, u1a = anch[ga]
        for gb in range(G0, G0 + Etot):
            aB, sB, u1b = anch[gb]
            strack = (sA[m + 1] == E.e[m] - 1 and sB[m + 1] == E.e[m] - 1)
            if not strack: continue
            E1, _ = pdivmod(R, pmul(R, aA, aB), E.Phis[m])
            if not pnorm(R, E1): continue
            key = (tuple(sorted([(tuple(sA[l] for l in range(1, m + 2)), u1a),
                                 (tuple(sB[l] for l in range(1, m + 2)), u1b)])))
            if key in seen: continue
            seen.add(key)
            pools, cs, Dd, top = WS.pools_of(E, sA, sB, su)
            ctop = cs[-1] if cs else 0
            kdef = 2 * etop - Dd
            if kdef > ctop: continue                 # dead: (EMPTY)'s territory
            live_pool.setdefault((kdef, ctop), []).append(
                (ga, gb, cs, Dd, kdef, sA, sB, u1a, u1b))
    cap = 3 if m >= 4 else 6
    recs = []
    for stratum in sorted(live_pool):
        for row in live_pool[stratum][:cap]:
            ga, gb, cs, Dd, kdef, sA, sB, u1a, u1b = row
            trace_row(E, sA, sB, u1a, u1b, anch[ga][0], anch[gb][0], su,
                      cs, Dd, kdef, True, (ga, gb), prin, recs, tag)
    print(f"-- FRESH {tag} m={m} {kind},p={p},d0={d0} g0={E.g[0]}: "
          f"live-strata={len(live_pool)} traced={len(recs)} "
          f"cells={sum(r['ncells'] for r in recs)} ({time.time()-t0:.1f}s)")
    results.append(dict(phase="fresh", tag=tag, m=m, kind=kind, p=p, d0=d0,
                        reads=reads,
                        live_strata={str(k): len(v)
                                     for k, v in sorted(live_pool.items())},
                        rows=recs))

# ---------------- main ----------------
def main():
    t0 = time.time()
    prov = {}
    for fn, want in PINS.items():
        got = hashlib.md5(open(os.path.join(HERE, fn), "rb").read()).hexdigest()
        prov[fn] = got
        if got != want:
            viol("SDK-PIN", fn, f"md5 {got} != pinned {want}")
    prov["surv_derive_checks.py"] = hashlib.md5(
        open(os.path.abspath(__file__), "rb").read()).hexdigest()
    results = []
    print("=" * 78)
    print("(SURV-(m+1))(i) derive checks — SEALED phase (the 412-row selection)")
    print("=" * 78)
    for spec in WS.ROSTER:
        run_sealed_tower(spec, results)
    print("=" * 78)
    print("(SURV-(m+1))(i) derive checks — FRESH phase (EQ roster, LIVE rows)")
    print("=" * 78)
    for spec in ED.FRESH_ROSTER:
        run_fresh_tower(spec, results)
    print("=" * 78)
    allrows = [x for r in results for x in r["rows"]]
    live = [x for x in allrows if x["live"]]
    fams = ["SDK-PIN", "SDK-CONS", "SDK-EMPTY", "SDK-DIGIT", "SDK-LINE",
            "SDK-CASC", "SDK-GRID", "SDK-SEP", "HARNESS"]
    nv = {f: sum(1 for v in VIOL if v[0] == f) for f in fams}
    for f in fams:
        print(f"{f:12s}: {nv[f]} violations")
    print("-" * 78)
    # the instrument layer: bottom-stratum census
    hist = {}
    for x in live:
        k = (x["strat"], x["nmin_net"])
        hist[k] = hist.get(k, 0) + 1
    print("MINSTRAT netted-bottom-size histogram (strat, n): ",
          json.dumps({f"{a}_n{b}": c for (a, b), c in sorted(hist.items())}))
    uq = sum(1 for x in live if x["nmin_net"] == 1)
    cuq = sum(1 for x in live if x["casc_unique_min"])
    print(f"live rows traced: {len(live)}; netted bottom UNIQUE: {uq}; "
          f"unique AND = cascade cell: {cuq}")
    print(f"rows with w_m(Q1) == beta_min (bottom survives): "
          f"{sum(1 for x in live if x['wq_minus_beta'] == 0)}/{len(live)}")
    rm = [x for x in live if x["read_ok"] is False]
    print(f"READADD: match {CNT.get('read_match', 0)} / "
          f"MISMATCH {CNT.get('read_MISMATCH', 0)}")
    print(f"REDWIN: red_all={CNT.get('red_all', 0)} "
          f"red_topbreach={CNT.get('red_topbreach', 0)}")
    print(f"CGRP ((SURV-CASC) lead): survived={CNT.get('cgrp_survived', 0)} "
          f"KILLED={CNT.get('cgrp_KILLED', 0)} "
          f"partnered={CNT.get('cgrp_partnered', 0)}")
    ck = [x for x in live if x.get("cgrp_survives") is False]
    if ck:
        print("  cgrp KILLED rows (the single-slot route refuted there):",
              [(x["tower"], x["key"]) for x in ck][:10])
    cp = [x for x in live if (x.get("cgrp_n") or 0) > 1]
    for x in cp[:8]:
        print(f"  cgrp partnered: {x['tower']}{x['key']} n={x['cgrp_n']} "
              f"survives={x['cgrp_survives']} strat={x['strat']}")
    if rm:
        print("  mismatch rows:", [(x["tower"], x["key"]) for x in rm][:10])
    multi = [x for x in live if x["nmin_net"] >= 2]
    print(f"multi-cell netted bottoms: {len(multi)} rows; profiles/junk/r "
          f"of the first 6:")
    for x in multi[:6]:
        print(f"  {x['tower']}{x['key']} strat={x['strat']} k={x['kdef']} "
              f"c={x['cs']} nmin={x['nmin_net']} profiles={x['min_profiles']} "
              f"junk={x['min_junk']} r={x['min_rvals']} "
              f"ncorr={x['min_ncorr_tot']}")
    noncasc_min = [x for x in live if not x["casc_is_min"]]
    print(f"rows where the bottom is NOT at the cascade line: "
          f"{len(noncasc_min)}")
    for x in noncasc_min[:6]:
        print(f"  {x['tower']}{x['key']} strat={x['strat']} k={x['kdef']} "
              f"c={x['cs']} beta_min={x['beta_min']} casc_line={x['casc_line']}")
    print("counters:", json.dumps(CNT, sort_keys=True))
    print("controls:", json.dumps(CTRL, sort_keys=True))
    ctrl_fail = [k for k, v in CTRL.items() if v == 0]
    if ctrl_fail:
        print(f"CONTROL non-firing (disclosed, does not color the verdict "
              f"lines): {ctrl_fail}")
    print(f"total violations: {len(VIOL)}")
    print(f"elapsed: {time.time()-t0:.1f}s")
    out = dict(violations=VIOL, counters=CNT, controls=CTRL,
               live_traced=len(live), dead_traced=CNT.get("dead_traced", 0),
               unique_bottom=uq, cascade_unique_bottom=cuq,
               provenance=prov,
               rows=allrows, elapsed=time.time() - t0)
    with open(os.path.join(HERE, "surv_derive_checks_results.json"), "w") as f:
        json.dump(out, f, indent=1, default=str)
    print("results -> surv_derive_checks_results.json")

if __name__ == "__main__":
    main()
