#!/usr/bin/env python3
"""empty_instrument.py — (EMPTY-(m+1)) INSTRUMENT unit: measure the MECHANISM
of deadness on dead rows (c_{m-1} < k), for the conjecture-grade route
displayed at WMULTDCX_2026-08-08.md S9:

    (EMPTY-(m+1)):  on TRACK, (H1)-(H2), c_{m-1} < k  =>  the two-stage tree
    T^2 has NO two-exit path at all (Q^1 has no cells; a fortiori Q^1 = 0).
    By W-D4 + W-D6c it suffices to show: when c_{m-1} < k, the two excess
    channels (correction dumps; non-principal d-cells) cannot fund
    pi_{m-1} >= k on any legal path — a counting statement about the tree.

This unit does NOT prove anything.  It enumerates, on every traced dead row,
ALL terminal states of the two-stage tree (stage-1 leaves, stage-1 exit
cofactors, stage-2 leaves, two-exit cells — pc/dmp/cons monotone along paths,
so terminal maxima = path maxima) and measures WHICH quantity is conserved /
bounded: the maximum pi_{m-1} any path attains, its channel decomposition
(principal supply vs correction dumps vs non-principal d-cells), and the
per-level LED_l ledger at the maximizing path.

Batteries:
  SEALED phase — the derive battery's exact traced-row selection
    (wmultdcx_derive_checks.py selection replicated VERBATIM on the sealed
    roster wmultdcx_stress.ROSTER), dead rows = the 126 zero-cell census rows
    (count re-verified, EMP-SEAL), plus <= 3 live CONTRAST rows per tower
    (controls only; the live mechanism is not this unit's object).
  FRESH phase — new adversarial towers (roster FROZEN at seal from the
    --design census, empty_instrument_design.json): deficits k = 1..4+,
    non-near-miss dead rows (c_{m-1} <= k-2, absent from the sealed 126,
    which are ALL near-miss), both characteristics, m = 4 deep-deficit
    towers, g0 >= 2, flat interior.  All law-dead TRACK rows traced up to a
    stratified cap per (kdef, c_top); every fresh pair also re-runs the LAW
    census (law-keyed countermodel guard).

VERDICT families (predicted-0; violations LAW-KEYED with the row's
(tag, m, kind, g0, kdef, c_top, near-miss) key):
  EMP-SEAL    sealed-phase dead-row count == 126 (selection replication).
  EMP-CELL    a dead row carries a two-exit path ((EMPTY) refuted at the
              instance — the unit's loudest possible product).
  EMP-Q1LAW   Q^1 != 0 on a law-dead row / == 0 on a law-live row
              (LAW-DCX-(m+1) countermodel; fresh pairs all censused).
  EMP-LEDGER  LED_l identity fails at ANY terminal (extends the committed
              DCK-LEDGER coverage from Q^1 cells to leaves + stage-1 states).
  EMP-INVA    [INV-A] some terminal has pi_l > A_l, the PER-PATH augmented
              cap chain  A_l = floor((sigma_l + jD_{l-1} + dmp_{l-1}
              + A_{l-1})/P_{l-1})  (the W-D6 induction with the path's OWN
              dump/d-cell channels added — the exact "channel-bounded
              excess" candidate).
  EMP-CONS    stage trees reassemble the canonical divisions (per row).
  EMP-PIN     consumed-runner md5s match the note-pinned seals.
  HARNESS     violations raised inside the consumed engines.

MEASURED censuses (no prediction; the unit's product; all law-keyed):
  MAXPI   per dead row, TWO maxima of pi_{m-1}:
            maxpi_all over ALL terminals, and
            maxpi_s2 over STAGE-2 terminals only (the Q^1-CAPABLE paths:
            only a stage-2 path can take the second exit, and every
            stage-1 exit's pc rides into its stage-2 seeds — stage-1
            leaves are dead ends in rem(a*a')).
          The KEY question is maxpi_s2 >= k (S2-BREACH, loud: a Q^1-capable
          path reaching the W-D4 depth on a dead row; EMP-CELL implies it).
          If 0 everywhere, "no Q^1-capable path attains depth k on dead
          rows" is the (EMPTY) proof target, sufficient via W-D4.
          maxpi_all >= k (ALL-BREACH) is a quiet census: the design-time
          smoke already showed stage-1 DEAD-END paths reaching depth k
          (dump-fed leaf-1 paths; disclosed here, not a refutation of
          anything).  Also the excess distributions maxpi_* - c_{m-1} and
          the exact-formula fits maxpi_* == c_{m-1} / == greedy_attained.
  INV-B   [charged form B1] dumps_total <= cons_subtop := sum_{l<=m-2} cons_l
          per terminal (the self-funding constraint), and [B2] <= cons_total.
  INV-C   maxpi_all <= greedy_attained := a_{m-1}+b_{m-1} if stock1 >=
          P_{m-1} else a_{m-1}  (the W-D7 cascade value, P-divisor form;
          == c_{m-1} at all-g=1 under STK) — the charged all-paths form —
          AND the stage-2 form INV-C-S2: maxpi_s2 <= greedy_attained.
  BFT     dead-row terminals beyond the dump-free floors (pc_l > cP_l):
          how active the excess channels are on dead rows at all.

DESIGN-TIME MUTATION CONTROLS (teeth: each must fire >= once somewhere in
the batteries, else CONTROL FAILURE — reported separately, never colors the
law lines):
  CTRL-A1     INV-A tightened by 1 (pi_l <= A_l - 1): must be violated
              (the augmented cap is ATTAINED somewhere).
  CTRL-NODUMP INV-A with both channels deleted (pi_l <= cP_l at ALL
              terminals, the refuted row-11c genre): must fire.
  CTRL-B1     INV-B1 tightened by 1 (dumps <= cons_subtop - 1): must fire.
  CTRL-C1     INV-C tightened by 1 (maxpi <= greedy - 1): must fire.
  CTRL-CAP1   maxpi <= cap1_top (carries capped at 1 — the REFUTED v1
              law pattern): must fire.
  CTRL-CELL   some live-contrast row yields >= 1 two-exit cell (the cell
              detector sees cells when they exist).
  CTRL-DEPTH  some live-contrast row with kdef >= 1 yields a cell with
              pi_{m-1} >= kdef (the depth counter sees depth when W-D4
              forces it).

Consumption, all READ-ONLY (this runner mutates none of these files):
wmultdcx_stress.py (roster, u-chain, window/anchors, pools, the sealed
selection key) · wmultdcx_derive_checks.py (reduce_ext — the full-ledger
two-stage tree, cellsum, cP_chain, greedy_chains) · rmengine_pe_reimpl.py
(Eng/prep) · grb_order2_check.py primitives.  Deterministic, exact integer/
polynomial arithmetic, no sampling, no seed.

Modes: --design  candidate-tower INTEGER law-side dead-strata census ONLY
                 (no tracing; the roster-freeze input; the DCX3/stress
                 design-disclosure convention) -> empty_instrument_design.json
       --smoke   mechanics validation on 2 towers, tiny caps
                 -> empty_instrument_smoke.json
       (default) the full two-phase battery -> empty_instrument_results.json
"""
import sys, os, time, json, hashlib

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import wmultdcx_stress as WS                    # read-only consumption
import wmultdcx_derive_checks as WD             # read-only consumption
import rmengine_pe_reimpl as PE                 # read-only consumption
from grb_order2_check import pnorm, pmul, pdivmod, pscal

VIOL = []       # verdict-family violations (predicted-0 legs)
CTRL = {k: 0 for k in ("CTRL-A1", "CTRL-NODUMP", "CTRL-B1", "CTRL-C1",
                       "CTRL-CAP1", "CTRL-CELL", "CTRL-DEPTH")}
CTRL_EX = {}    # first firing example per control
CNT = {}

NOTE_PINS = {   # WMULTDCX_2026-08-08.md S0/S10 machine-leg seals
    "wmultdcx_derive_checks.py": "bea1a43d619a3c91a9a0b2f32c0920c0",
}

def note(fam, n=1): CNT[fam] = CNT.get(fam, 0) + n
def viol(fam, key, detail):
    VIOL.append((fam, str(key), str(detail)[:400]))
    if sum(1 for v in VIOL if v[0] == fam) <= 10:
        print(f"  VIOLATION [{fam}] {key}: {str(detail)[:300]}")
def ctrl_fire(name, key, detail=""):
    CTRL[name] += 1
    if name not in CTRL_EX:
        CTRL_EX[name] = f"{key}: {str(detail)[:160]}"

def prod(xs):
    r = 1
    for x in xs: r *= x
    return r

def md5f(fn):
    with open(os.path.join(HERE, fn), "rb") as fh:
        return hashlib.md5(fh.read()).hexdigest()

# --------------- harness-event harvest around consumed engines ---------------
def harv_base(): return (len(PE.VIOL), len(WS.VIOL), len(WD.VIOL))
def harv(key, n0):
    for (src, lst, k0) in (("PE", PE.VIOL, n0[0]), ("WS", WS.VIOL, n0[1]),
                           ("WD", WD.VIOL, n0[2])):
        for f in lst[k0:]:
            viol("HARNESS", key, f"{src}:{f}")

# ===================== per-path channel/cap arithmetic ========================
def aug_chain(E, sig, jDv, dmp):
    """A_l per level (index i = promotions into level i+1), the W-D6
    induction with the path's own dump mass and d-cell exponents added:
    A_{i+1} = floor((sig_i + jD_i + dmp_i + A_i)/P_i)."""
    A = 0; out = []
    for i in range(E.m - 1):
        A = (sig[i] + jDv[i] + dmp[i] + A)//E.P[i]
        out.append(A)
    return out

def cap1_top(E, sig, su):
    """the REFUTED v1 pattern: carries capped at 1, literal e divisor."""
    c = 0
    for l in range(1, E.m):
        c = min(1, (sig[l-1] + su[l] + c)//E.e[l-1])
    return c

# ============================ one traced row ==================================
CLS_RANK = {"cell": 0, "leaf2": 1, "exit1": 2, "leaf1": 3}

def trace_row(E, su, prin, anch, ga, gb, cs, D, kdef, live, rowkey, recs):
    """full two-stage tree with ledgers (WD.reduce_ext); ALL terminals kept."""
    R = E.R; m = E.m; etop = E.e[m-1]
    aA, sA, u1a = anch[ga]; aB, sB, u1b = anch[gb]
    sig = tuple(sA[l+1] + sB[l+1] for l in range(m))
    b0 = pscal(R, R["pi_pow"](u1a + u1b), [R["one"]])
    z = (0,)*m
    lawkey = dict(tag=E.tag, m=m, kind=E.kind, g0=E.g[0], d0=E.d0,
                  key=rowkey, kdef=kdef, c_top=(cs[-1] if cs else 0),
                  near=(cs and cs[-1] == kdef - 1) or (not cs and kdef == 1),
                  live=live)
    kstr = f"{E.tag}{rowkey}/k={kdef},c={cs}"
    n0 = harv_base()
    # ---- stage 1 ----
    init = [(1, b0, sig, z, z, z, z, 0, None, False)]
    q1sink = []
    out = WD.reduce_ext(E, init, q1sink, {})
    if out[0] is None:
        viol("HARNESS", kstr, "stage-1 tree cap"); return
    leaves1, _ = out
    prodp = pmul(R, aA, aB)
    E1c, E0c = pdivmod(R, prodp, E.Phis[m])
    if WD.cellsum(E, q1sink) != pnorm(R, E1c):
        viol("EMP-CONS", kstr, "stage-1 exit sum != E1IH")
    if WD.cellsum(E, leaves1) != pnorm(R, E0c):
        viol("EMP-CONS", kstr, "stage-1 leaf sum != rem")
    # ---- stage 2 seeding (verbatim the derive-battery convention) ----
    init2 = []
    for st in q1sink:
        sign, b, j, pc, dmp, cons, ncorr, junk = st[:8]
        for (cD, jD) in E.Dcells:
            Lc, Xc, Yc = E.digit_split(b, cD)
            js = tuple(j[l] + jD[l] for l in range(m))
            isp = (tuple(jD) == prin)
            for (cc, jtag, dj0) in ((Lc, 0, 0), (Xc, 1, 0), (Yc, 1, 1)):
                if not pnorm(R, cc): continue
                jj = list(js); jj[0] += dj0
                dd = list(dmp); dd[0] += dj0
                init2.append((sign, cc, tuple(jj), pc, tuple(dd), cons,
                              ncorr, junk + jtag, tuple(jD), isp))
    q2sink = []
    out2 = WD.reduce_ext(E, init2, q2sink, {})
    if out2[0] is None:
        viol("HARNESS", kstr, "stage-2 tree cap"); return
    leaves2, _ = out2
    Q1c, R1c = pdivmod(R, pmul(R, E1c, E.Chat), E.Phis[m])
    if WD.cellsum(E, q2sink) != pnorm(R, Q1c):
        viol("EMP-CONS", kstr, "stage-2 exit sum != Q1")
    if WD.cellsum(E, leaves2) != pnorm(R, R1c):
        viol("EMP-CONS", kstr, "stage-2 leaf sum != rem")
    q1nz = bool(pnorm(R, Q1c))
    if (not live) and q1nz:
        viol("EMP-Q1LAW", kstr, "Q1 != 0 on a law-dead row (LAW COUNTERMODEL)")
    if live and not q1nz:
        viol("EMP-Q1LAW", kstr, "Q1 == 0 on a live-selected row")
    if (not live) and q2sink:
        viol("EMP-CELL", kstr,
             f"{len(q2sink)} two-exit path(s) on a dead row — (EMPTY) refuted "
             f"at the instance; pc profiles {[st[3] for st in q2sink[:4]]}")
    # ---- terminal sweep ----
    terms = ([("leaf1", st) for st in leaves1] +
             [("exit1", st) for st in q1sink] +
             [("leaf2", st) for st in leaves2] +
             [("cell",  st) for st in q2sink])
    cP = WD.cP_chain(E, sig, su)
    a, rr, bb, stock1 = WD.greedy_chains(E, sig, su, cs)
    greedy_att = (a[m-1] + bb[m-1]) if stock1 >= E.P[m-1] else a[m-1]
    cap1 = cap1_top(E, sig, su)
    zvec = (0,)*m
    maxpi_all = -1; maxpi_s2 = -1; arg = None; arg2 = None
    hist = {}
    nb1 = nb2 = ninva = nbft = 0
    ndump_terms = nnonprin_terms = 0
    max_dump_gap = None
    for (cls, st) in terms:
        sign, b, j, pc, dmp, cons, ncorr, junk, jD, isp = st
        jDv = jD if jD is not None else zvec
        # LED_l identity at EVERY terminal (leaf/exit/cell alike)
        for l in range(m):
            pin = pc[l-1] if l >= 1 else 0
            if j[l] != sig[l] + jDv[l] + pin + dmp[l] - cons[l]:
                viol("EMP-LEDGER", kstr,
                     f"{cls} LED_{l}: j={j} sig={sig} jD={jDv} pc={pc} "
                     f"dmp={dmp} cons={cons}")
                break
        # INV-A: per-path augmented cap  (+ CTRL-A1 / CTRL-NODUMP mutants)
        Afull = aug_chain(E, sig, jDv, dmp)
        for i in range(m - 1):
            if pc[i] > Afull[i]:
                ninva += 1
                viol("EMP-INVA", kstr,
                     f"{cls} pi_{i+1}={pc[i]} > A={Afull[i]} (jD={jDv}, "
                     f"dmp={dmp})")
            if pc[i] > Afull[i] - 1:
                ctrl_fire("CTRL-A1", kstr, f"{cls} pi_{i+1}={pc[i]}=A")
            if pc[i] > cP[i]:
                ctrl_fire("CTRL-NODUMP", kstr,
                          f"{cls} pi_{i+1}={pc[i]} > cP={cP[i]}")
                if not live: nbft += 1
        # INV-B: self-funding (census)  (+ CTRL-B1 mutant)
        dtot = sum(dmp); csub = sum(cons[:m-1]); ctot = sum(cons)
        if dtot > csub:
            nb1 += 1
            gap = dtot - csub
            if max_dump_gap is None or gap > max_dump_gap: max_dump_gap = gap
        if dtot > ctot: nb2 += 1
        if dtot > csub - 1:
            ctrl_fire("CTRL-B1", kstr, f"{cls} dumps={dtot} cons_sub={csub}")
        if dtot > 0: ndump_terms += 1
        if jD is not None and not isp: nnonprin_terms += 1
        # maxima
        pt = pc[m-2]
        hist[pt] = hist.get(pt, 0) + 1
        if cls in ("leaf2", "cell"):
            better2 = (pt > maxpi_s2 or
                       (pt == maxpi_s2 and arg2 is not None and
                        (CLS_RANK[cls], -sum(dmp)) <
                        (CLS_RANK[arg2[0]], -sum(arg2[1][4]))))
            if better2:
                maxpi_s2 = pt; arg2 = (cls, st)
        better = (pt > maxpi_all or
                  (pt == maxpi_all and arg is not None and
                   (CLS_RANK[cls], -sum(dmp)) <
                   (CLS_RANK[arg[0]], -sum(arg[1][4]))))
        if better:
            maxpi_all = pt; arg = (cls, st)
        if cls == "cell" and live and kdef >= 1 and pt >= kdef:
            ctrl_fire("CTRL-DEPTH", kstr, f"cell pi_top={pt} >= k={kdef}")
    if live and q2sink:
        ctrl_fire("CTRL-CELL", kstr, f"{len(q2sink)} cells")
    # ---- row-level measured censuses (dead rows are the object) ----
    c_top = cs[-1] if cs else 0
    exc = maxpi_all - c_top
    exc2 = maxpi_s2 - c_top
    invc_viol = maxpi_all > greedy_att
    invc2_viol = maxpi_s2 > greedy_att
    if not live:
        note("dead_rows")
        note(f"exc_all_{exc}")
        note(f"exc_s2_{exc2}")
        if maxpi_s2 >= kdef:
            note("S2_BREACH")
            viol("S2-BREACH", kstr,
                 f"dead row: Q1-CAPABLE (stage-2) path attains "
                 f"pi_top={maxpi_s2} >= k={kdef} (maxpi_all={maxpi_all}) — "
                 f"the counting route must handle it")
        if maxpi_all >= kdef:
            note("ALL_BREACH")        # quiet census: stage-1 dead ends
        if maxpi_all == c_top: note("maxpi_all_eq_ctop")
        if maxpi_s2 == c_top: note("maxpi_s2_eq_ctop")
        if maxpi_all == greedy_att: note("maxpi_all_eq_greedy")
        if maxpi_s2 == greedy_att: note("maxpi_s2_eq_greedy")
        if maxpi_s2 < c_top: note("maxpi_s2_lt_ctop")
        if invc_viol: note("INVC_viol")
        if invc2_viol: note("INVC_s2_viol")
        if nb1: note("INVB1_viol_rows")
        if nb2: note("INVB2_viol_rows")
        if nbft: note("BFT_rows")
    if maxpi_all > greedy_att - 1:
        ctrl_fire("CTRL-C1", kstr, f"maxpi={maxpi_all} = greedy={greedy_att}")
    if maxpi_all > cap1:
        ctrl_fire("CTRL-CAP1", kstr, f"maxpi={maxpi_all} > cap1={cap1}")
    # ---- argmax record: channels + per-level LED ----
    cls, st = arg
    sign, b, j, pc, dmp, cons, ncorr, junk, jD, isp = st
    jDv = jD if jD is not None else zvec
    Afull = aug_chain(E, sig, jDv, dmp)
    Anod = aug_chain(E, sig, jDv, zvec)
    base_jD = prin if (jD is not None) else zvec
    Abase = aug_chain(E, sig, base_jD, zvec)
    argrec = dict(cls=cls, pc=list(pc), j=list(j), dmp=list(dmp),
                  cons=list(cons), ncorr=list(ncorr), junk=junk,
                  jD=(list(jD) if jD is not None else None), principal=isp,
                  A_full=Afull, A_nodump=Anod, A_base=Abase,
                  chan=dict(principal=Abase[m-2],
                            nonprin=Anod[m-2] - Abase[m-2],
                            dump=Afull[m-2] - Anod[m-2],
                            slack=Afull[m-2] - pc[m-2]),
                  led=[[l, j[l], sig[l], jDv[l],
                        (pc[l-1] if l >= 1 else 0), dmp[l], cons[l]]
                       for l in range(m)])
    recs.append(dict(**lawkey, sig=list(sig), su={str(l): su[l] for l in su},
                     cs=cs, cP=cP, D=D, stock1=stock1,
                     a_top=a[m-1], b_top=bb[m-1], greedy_att=greedy_att,
                     cap1=cap1, allg1=all(E.g[l] == 1 for l in range(m)),
                     n_leaf1=len(leaves1), n_exit1=len(q1sink),
                     n_leaf2=len(leaves2), n_cell=len(q2sink),
                     maxpi_all=maxpi_all, maxpi_s2=maxpi_s2, exc=exc,
                     hist={str(k): v for k, v in sorted(hist.items())},
                     invb1_terms=nb1, invb2_terms=nb2, inva_terms=ninva,
                     bft_terms=nbft, invc_viol=invc_viol,
                     dump_terms=ndump_terms, nonprin_terms=nnonprin_terms,
                     max_dump_gap=max_dump_gap, argmax=argrec))
    harv(kstr, n0)

# ====================== row selection (both phases) ===========================
def scan_pairs(E, su, anch, Etot, G0, law_guard):
    """one full pair scan: yields (key, ga, gb, cs, D, kdef, meas, law) with
    dedup by the sealed pid key; optionally law-checks every TRACK pair."""
    R = E.R; m = E.m; etop = E.e[m-1]
    seen = {}
    for ga in range(G0, G0 + Etot):
        aA, sA, u1a = anch[ga]
        for gb in range(G0, G0 + Etot):
            aB, sB, u1b = anch[gb]
            strack = (sA[m+1] == E.e[m]-1 and sB[m+1] == E.e[m]-1)
            if not strack: continue
            E1, _ = pdivmod(R, pmul(R, aA, aB), E.Phis[m])
            if not pnorm(R, E1): continue                    # not TRACK
            pools, cs, D, top = WS.pools_of(E, sA, sB, su)
            kdef = 2*etop - D
            law = top >= 2*etop
            Q1 = pdivmod(R, pmul(R, E1, E.Chat), E.Phis[m])[0]
            meas = False
            if pnorm(R, Q1):
                Tsum = sA[m+1] + sB[m+1]
                dpl = Tsum//E.e[m]
                locus = ((dpl == 1 and strack and E.e[m] >= 2)
                         or (Tsum == E.e[m]-1 and E.e[m] == 1))
                if locus: meas = True
            if law_guard and law != meas:
                viol("EMP-Q1LAW", f"{E.tag}({ga},{gb})",
                     f"LAW COUNTERMODEL: law={law} meas={meas} top={top} "
                     f"cs={cs} D={D}")
            key = (tuple(sorted([(tuple(sA[l] for l in range(1, m+2)), u1a),
                                 (tuple(sB[l] for l in range(1, m+2)), u1b)])))
            if key in seen: continue
            seen[key] = True
            yield key, ga, gb, cs, D, kdef, meas

def select_sealed(E, su, anch, Etot, G0):
    """the derive battery's pid-key selection, replicated VERBATIM (same
    want-heuristic, same cap, same sort) -> (dead rows, live contrast)."""
    m = E.m; etop = E.e[m-1]
    pid_keys = {}
    for key, ga, gb, cs, D, kdef, meas in scan_pairs(E, su, anch, Etot, G0,
                                                     law_guard=False):
        top = D + (cs[-1] if cs else 0)
        want = (meas or top in (2*etop - 1, 2*etop, 2*etop - 2)
                or (len(cs) >= 2 and cs[0] > 0 and cs[1] > 0)
                or (cs and max(cs) >= 2))
        if want:
            pid_keys[key] = (ga, gb, cs, D, kdef, meas)
    cap = 14 if m >= 4 else 40
    chosen = sorted(pid_keys.items(), key=lambda kv: (
        not kv[1][5], -(kv[1][2][0] if kv[1][2] else 0), kv[0]))[:cap]
    dead = [v for _, v in chosen if not v[5]]
    live = sorted([v for _, v in chosen if v[5]],
                  key=lambda v: (-v[4], -(v[2][0] if v[2] else 0)))[:3]
    return dead, live

CAP_STRAT = {3: 8, 4: 6}      # fresh dead rows per (kdef, c_top) stratum
N_LIVE = 3

def select_fresh(E, su, anch, Etot, G0):
    """all law-dead TRACK rows, stratified cap per (kdef, c_top); live
    contrast; EVERY TRACK pair law-guarded (countermodel census)."""
    strat = {}; live = []
    for key, ga, gb, cs, D, kdef, meas in scan_pairs(E, su, anch, Etot, G0,
                                                     law_guard=True):
        c_top = cs[-1] if cs else 0
        if c_top < kdef:                                    # law-dead
            strat.setdefault((kdef, c_top), []).append((ga, gb, cs, D, kdef,
                                                        meas))
        elif meas:
            live.append((ga, gb, cs, D, kdef, meas))
    cap = CAP_STRAT.get(E.m, 6)
    dead = []
    for sk in sorted(strat):
        dead.extend(strat[sk][:cap])
    live = sorted(live, key=lambda v: (-v[4], -(v[2][0] if v[2] else 0)))
    return dead, live[:N_LIVE], {str(k): len(v) for k, v in sorted(strat.items())}

# ============================ tower drivers ===================================
def build(spec):
    tag, m, kind, p, d0, reads = spec
    n0 = harv_base()
    E = PE.Eng(m, kind, p, d0, reads, tag)
    PE.prep(E)
    u, su = WS.uchain(E)
    if u is None:
        viol("HARNESS", tag, "u-chain failed"); return None
    Etot, G0, split = WS.window_split(E)
    anch = WS.anchors_of(E, Etot, G0, split)
    prin = tuple(su[l+1] for l in range(m))
    harv(tag, n0)
    return E, su, prin, anch, Etot, G0

def run_tower(spec, phase, recs, meta):
    t0 = time.time()
    built = build(spec)
    if built is None: return
    E, su, prin, anch, Etot, G0 = built
    if phase == "sealed":
        dead, live = select_sealed(E, su, anch, Etot, G0)
        strat = None
    else:
        dead, live, strat = select_fresh(E, su, anch, Etot, G0)
    for (ga, gb, cs, D, kdef, meas) in dead + live:
        trace_row(E, su, prin, anch, ga, gb, cs, D, kdef, meas, (ga, gb), recs)
    meta.append(dict(tag=E.tag, phase=phase, m=E.m, kind=E.kind, p=E.p,
                     d0=E.d0, reads=E.reads, n_dead=len(dead),
                     n_live=len(live), strat=strat,
                     elapsed=round(time.time() - t0, 2)))
    print(f"-- [{phase}] {E.tag} m={E.m} {E.kind},p={E.p},d0={E.d0} "
          f"g={E.g[:E.m]}: dead={len(dead)} live_ctrl={len(live)}"
          f"{' strat=' + str(strat) if strat else ''} "
          f"({time.time()-t0:.1f}s)")

# ===================== fresh-tower design candidates ==========================
# Design pool (census only in --design; the run-mode roster FRESH_ROSTER is
# frozen from empty_instrument_design.json BEFORE the seal commit).
CANDS = [
    # m=3, Zp, top e2=3/4: deficits k=3..4+, c-gap >= 2 (absent from sealed)
    ("EQ3T3A",  3, "Zp", 3, 1, [(2,1,1), (2,1,1), (3,1,1), (2,1,1)]),
    ("EQ3T3B",  3, "Zp", 3, 1, [(3,2,1), (2,1,1), (3,2,1), (2,1,1)]),
    ("EQ3T3C",  3, "Zp", 5, 1, [(3,1,1), (2,3,1), (3,1,1), (2,1,1)]),
    ("EQ3T4A",  3, "Zp", 3, 1, [(2,1,1), (2,1,1), (4,1,1), (2,1,1)]),
    ("EQ3T4B",  3, "Zp", 3, 1, [(4,3,1), (2,1,1), (4,3,1), (2,1,1)]),
    ("EQ3T4C",  3, "Zp", 3, 1, [(2,1,1), (2,1,1), (4,3,1), (2,1,1)]),
    # equal characteristic (Fpt, p=2)
    ("EQ3T3F",  3, "Fpt", 2, 1, [(3,1,1), (2,1,1), (3,2,1), (2,1,1)]),
    ("EQ3T4F",  3, "Fpt", 2, 1, [(2,1,1), (2,1,1), (4,1,1), (2,1,1)]),
    # g0 >= 2 with deep top deficits (fresh corner)
    ("EQ3G2A",  3, "Zp", 3, 2, [(2,1,2), (3,2,1), (3,1,1), (2,1,1)]),
    ("EQ3G2B",  3, "Zp", 3, 1, [(3,1,2), (2,1,1), (3,2,1), (2,1,1)]),
    # flat interior (carry pass-through deadness)
    ("EQ3FLT",  3, "Zp", 5, 1, [(3,1,1), (1,1,1), (2,1,1), (2,1,1)]),
    # m=4 deep deficits (never probed at m=4)
    ("EQ4T3A",  4, "Zp", 3, 1, [(2,1,1), (2,1,1), (2,1,1), (3,1,1), (2,1,1)]),
    ("EQ4T3F",  4, "Fpt", 2, 1, [(2,1,1), (2,1,1), (2,1,1), (3,1,1), (2,1,1)]),
    ("EQ4DEEP", 4, "Zp", 3, 1, [(3,2,1), (2,1,1), (2,1,1), (2,1,1), (2,1,1)]),
    ("EQ4NEST", 4, "Zp", 3, 1, [(2,1,1), (2,1,1), (2,1,1), (2,3,1), (2,1,1)]),
]

# FROZEN at seal from the --design census (empty_instrument_design.json,
# this file's seal commit): every candidate carrying >= 1 dead TRACK row,
# prioritized for k >= 3 strata, c-gap >= 2, both kinds, m = 4, g0 = 2.
FRESH_ROSTER = [
    ("EQ3T3A",  3, "Zp", 3, 1, [(2,1,1), (2,1,1), (3,1,1), (2,1,1)]),
    ("EQ3T3B",  3, "Zp", 3, 1, [(3,2,1), (2,1,1), (3,2,1), (2,1,1)]),
    ("EQ3T3C",  3, "Zp", 5, 1, [(3,1,1), (2,3,1), (3,1,1), (2,1,1)]),
    ("EQ3T4A",  3, "Zp", 3, 1, [(2,1,1), (2,1,1), (4,1,1), (2,1,1)]),
    ("EQ3T4B",  3, "Zp", 3, 1, [(4,3,1), (2,1,1), (4,3,1), (2,1,1)]),
    ("EQ3T4C",  3, "Zp", 3, 1, [(2,1,1), (2,1,1), (4,3,1), (2,1,1)]),
    ("EQ3T3F",  3, "Fpt", 2, 1, [(3,1,1), (2,1,1), (3,2,1), (2,1,1)]),
    ("EQ3T4F",  3, "Fpt", 2, 1, [(2,1,1), (2,1,1), (4,1,1), (2,1,1)]),
    ("EQ3G2A",  3, "Zp", 3, 2, [(2,1,2), (3,2,1), (3,1,1), (2,1,1)]),
    ("EQ3G2B",  3, "Zp", 3, 1, [(3,1,2), (2,1,1), (3,2,1), (2,1,1)]),
    ("EQ3FLT",  3, "Zp", 5, 1, [(3,1,1), (1,1,1), (2,1,1), (2,1,1)]),
    ("EQ4T3A",  4, "Zp", 3, 1, [(2,1,1), (2,1,1), (2,1,1), (3,1,1), (2,1,1)]),
    ("EQ4T3F",  4, "Fpt", 2, 1, [(2,1,1), (2,1,1), (2,1,1), (3,1,1), (2,1,1)]),
    ("EQ4DEEP", 4, "Zp", 3, 1, [(3,2,1), (2,1,1), (2,1,1), (2,1,1), (2,1,1)]),
    ("EQ4NEST", 4, "Zp", 3, 1, [(2,1,1), (2,1,1), (2,1,1), (2,3,1), (2,1,1)]),
]

def design_census(spec, out):
    """INTEGER law-side dead-strata census only (no tracing, no verdicts)."""
    t0 = time.time()
    built = build(spec)
    if built is None: return
    E, su, prin, anch, Etot, G0 = built
    strat = {}; nlive = nlivek = ntrack = 0; cm = 0
    for key, ga, gb, cs, D, kdef, meas in scan_pairs(E, su, anch, Etot, G0,
                                                     law_guard=False):
        ntrack += 1
        c_top = cs[-1] if cs else 0
        if c_top < kdef:
            strat[(kdef, c_top)] = strat.get((kdef, c_top), 0) + 1
            if meas: cm += 1                     # law-dead but measured live
        elif meas:
            nlive += 1
            if kdef >= 1: nlivek += 1
    out[spec[0]] = dict(m=E.m, kind=E.kind, p=E.p, d0=E.d0, reads=E.reads,
                        track_keys=ntrack,
                        dead_strata={str(k): v for k, v in sorted(strat.items())},
                        dead_total=sum(strat.values()),
                        dead_meas_mismatch=cm, live_keys=nlive,
                        live_kdef1=nlivek, elapsed=round(time.time()-t0, 2))
    print(f"-- design {spec[0]}: track_keys={ntrack} "
          f"dead={sum(strat.values())} strata={out[spec[0]]['dead_strata']} "
          f"live={nlive} (kdef>=1: {nlivek}) mism={cm} "
          f"({time.time()-t0:.1f}s)")

# ================================== main ======================================
def main():
    t0 = time.time()
    mode = ("design" if "--design" in sys.argv
            else "smoke" if "--smoke" in sys.argv else "run")
    print(f"== empty_instrument: (EMPTY-(m+1)) dead-row mechanism "
          f"instrument [mode={mode}] ==")
    prov = {fn: md5f(fn) for fn in
            ("empty_instrument.py", "wmultdcx_stress.py",
             "wmultdcx_derive_checks.py", "rmengine_pe_reimpl.py",
             "grb_order2_check.py")}
    for fn, want in NOTE_PINS.items():
        if prov[fn] != want:
            viol("EMP-PIN", fn, f"md5 {prov[fn]} != note-pinned {want}")
    if mode == "design":
        out = {}
        for spec in CANDS:
            design_census(spec, out)
        blob = dict(mode="design", cands=out, provenance=prov,
                    note="law-side dead-strata census only; no tracing; "
                         "roster-freeze input (design disclosure)",
                    elapsed=time.time() - t0)
        with open(os.path.join(HERE, "empty_instrument_design.json"),
                  "w") as fh:
            json.dump(blob, fh, indent=1, default=str)
        print(f"design census done; {len(out)} candidates; "
              f"elapsed {time.time()-t0:.1f}s")
        return 0
    recs = []; meta = []
    sealed_specs = ([s for s in WS.ROSTER if s[0] == "XM3A"] if mode == "smoke"
                    else WS.ROSTER)
    fresh_specs = (FRESH_ROSTER[:1] if mode == "smoke" else FRESH_ROSTER)
    for spec in sealed_specs:
        run_tower(spec, "sealed", recs, meta)
    for spec in fresh_specs:
        run_tower(spec, "fresh", recs, meta)
    # ---- EMP-SEAL: the sealed battery's dead-row census must be the 126 ----
    nsd = sum(1 for r in recs if not r["live"]
              and any(mm["tag"] == r["tag"] and mm["phase"] == "sealed"
                      for mm in meta))
    if mode != "smoke" and nsd != 126:
        viol("EMP-SEAL", "global",
             f"sealed-phase dead rows = {nsd} != 126 (selection replication)")
    # ---- verdicts ----
    dead = [r for r in recs if not r["live"]]
    live = [r for r in recs if r["live"]]
    print()
    fams = ["EMP-PIN", "EMP-SEAL", "EMP-CONS", "EMP-LEDGER", "EMP-INVA",
            "EMP-CELL", "EMP-Q1LAW", "HARNESS"]
    for f in fams:
        n = sum(1 for v in VIOL if v[0] == f)
        print(f"{f} VERDICT (predicted-0): "
              f"{'GREEN' if n == 0 else 'RED'} [{n} violations]")
    nbre = sum(1 for v in VIOL if v[0] == "MAXPI-BREACH")
    print(f"MAXPI CENSUS (KEY: dead rows where some path attains "
          f"pi_top >= k): {nbre} breach rows / {len(dead)} dead rows")
    # law-keyed stratum table
    strata = {}
    for r in dead:
        sk = (r["m"], r["kind"], r["g0"], r["kdef"], r["c_top"])
        s = strata.setdefault(sk, dict(n=0, exc=set(), eqc=0, eqg=0, brc=0,
                                       bft=0, invc=0))
        s["n"] += 1; s["exc"].add(r["exc"])
        if r["maxpi_all"] == r["c_top"]: s["eqc"] += 1
        if r["maxpi_all"] == r["greedy_att"]: s["eqg"] += 1
        if r["maxpi_all"] >= r["kdef"]: s["brc"] += 1
        if r["bft_terms"]: s["bft"] += 1
        if r["invc_viol"]: s["invc"] += 1
    print("DEAD-ROW STRATA (m,kind,g0,kdef,c_top): n / maxpi==c / "
          "maxpi==greedy / breaches / beyond-floor rows / INV-C viol / "
          "excess values")
    for sk in sorted(strata, key=str):
        s = strata[sk]
        print(f"  {sk}: {s['n']} / {s['eqc']} / {s['eqg']} / {s['brc']} / "
              f"{s['bft']} / {s['invc']} / {sorted(s['exc'])}")
    nb1r = CNT.get("INVB1_viol_rows", 0); nb2r = CNT.get("INVB2_viol_rows", 0)
    print(f"INV-A VERDICT (augmented per-path cap, predicted-0): "
          f"{'GREEN' if not any(v[0] == 'EMP-INVA' for v in VIOL) else 'RED'}")
    print(f"INV-B CENSUS (self-funding): B1 (dumps <= sub-top cons) violated "
          f"on {nb1r} dead rows; B2 (<= total cons) on {nb2r}")
    print(f"INV-C CENSUS (greedy maximizes over ALL paths on dead rows): "
          f"violated on {CNT.get('INVC_viol', 0)}/{len(dead)} dead rows")
    print(f"FORMULA CENSUS: maxpi == c_top on "
          f"{CNT.get('maxpi_eq_ctop', 0)}/{len(dead)}; == greedy_att on "
          f"{CNT.get('maxpi_eq_greedy', 0)}/{len(dead)}; < c_top on "
          f"{CNT.get('maxpi_lt_ctop', 0)}")
    print(f"BFT CENSUS (dead-row terminals beyond dump-free floors): "
          f"{CNT.get('BFT_rows', 0)} rows")
    teeth = all(CTRL[k] > 0 for k in CTRL)
    print(f"CONTROL VERDICT (mutants must fire, SEPARATE): "
          f"{'MET' if teeth else 'CONTROL FAILURE'} "
          f"{ {k: CTRL[k] for k in sorted(CTRL)} }")
    print(f"counters: {dict(sorted(CNT.items()))}")
    print(f"total verdict violations: {len(VIOL)}; rows traced: {len(recs)} "
          f"(dead {len(dead)}, live-ctrl {len(live)}); "
          f"elapsed {time.time()-t0:.1f}s")
    out = dict(mode=mode, violations=VIOL, counters=CNT,
               controls=CTRL, control_examples=CTRL_EX,
               sealed_dead_count=nsd,
               strata={str(k): dict(n=v["n"], exc=sorted(v["exc"]),
                                    eqc=v["eqc"], eqg=v["eqg"], brc=v["brc"],
                                    bft=v["bft"], invc=v["invc"])
                       for k, v in strata.items()},
               towers=meta, rows=recs, provenance=prov,
               elapsed=time.time() - t0)
    fn = ("empty_instrument_results.json" if mode == "run"
          else "empty_instrument_smoke.json")
    with open(os.path.join(HERE, fn), "w") as fh:
        json.dump(out, fh, indent=1, default=str)
    return 0

if __name__ == "__main__":
    sys.exit(main())
