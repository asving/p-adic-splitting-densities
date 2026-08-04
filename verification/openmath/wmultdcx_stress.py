#!/usr/bin/env python3
"""wmultdcx_stress.py — W-MULT-DCX STRESS unit: adversarial countermodel hunt
for the pool-floor form of LAW-DCX-(m+1) (RMENGINE_2026-08-08.md S6.1) BEFORE
any proof attempt.  A found countermodel is a SUCCESS for this unit.

THE LAW UNDER STRESS (S6.1, verbatim semantics):
    u_m := gamma_{m+1};  u_{l-1} := (u_l - s_l(u_l)*gamma_l)/e_{l-1}
    pool_1 := (s_1+s_1') + s_1(u_1);           c_1 := pool_1 // e_0
    pool_l := (s_l+s_l') + s_l(u_l) + c_{l-1}; c_l := pool_l // e_{l-1}
    TRACK  := (s_{m+1} = s_{m+1}' = e_m - 1) and E1IH != 0
    LAW-DCX-(m+1):  DCX_{m+1} = TRACK and
                    (s_m+s_m') + s_m(u_m) + c_{m-1} >= 2*e_{m-1}
Measured side (the [ILN] S4.7 definition, diag D5 operationalization):
    meas := E1IH != 0 and Q1 := quo(E1IH*Chat_m, Phi_m) != 0 and the locus
    clause ((delta=1 and s=s'=e_m-1) or (T=e_m-1 and e_m=1)).
Status of the law: m=1 PROVED, m=2 SEALED-CONFIRMED conjecture (DCX3 v2,
11,808/0), m>=3 census-grade only (D5 896/896; PE 2,208/0).  This unit
attacks the corners none of that evidence touched:
  A. DOUBLE-nested carries: c_1 > 0 AND c_2 > 0 simultaneously, incl. c_1=2
     deep pools (every prior m=3 live row had single nesting only).
  B. Top-deficit strata at m>=3: direct top mass 2e-2 (deficit-2, needs
     c_{m-1}=2) — the stratum whose m=2 analogue KILLED candidate v1.
  C. Flat interior levels (e_i = 1, d_0 = 1): pools degenerate to carry
     pass-through (s == 0 at flat reads); law census barely ran there
     (M2C live=0, M3C live=3).  Shapes where the LAW IS DECIDED BY c alone.
  D. Threshold edges: pool_l at exact multiples of e_{l-1}; just-miss rows
     (top = 2e-1) must all be dead.
  E. g_0 >= 2: the pool divisor is the LITERAL e_{l-1}, not e*g (sealed at
     m=2 only: DS7/EX3); first m=3 data on the g-pattern.
  F. m=4 (LAW-DCX-5) nesting: prior data (M4A) had maxc=1, zero deficits.
  G. Both residue characteristics (Zp and Fpt).

POOL-IDENTIFICATION instrument (the RM-GEN S8 row 11c HEURISTIC, stressed
directly): a two-stage promotion-tracking reduction tree (the DCX3 TraceTree
generalized to level m) records, per Q1 cell, the per-level promotion count
along its ancestry (pc_l = # promotion edges (l-1)->l; stage-1 = reduction of
a*a', stage-2 = reduction of E1IH*Chat).  Q1 is split into promotion-profile
parts (exact linear bookkeeping; reassembly asserted).  Compared instance by
instance with the pools:
  PID-MAX: no NONZERO Q1 part carries pc_l > c_l  (l = 1..m-1)  [the literal
           "maximal promotion count into level l is floor(pool_l/e_{l-1})"]
  PID-DEF: on a live row with top deficit k := 2e_{m-1} - direct >= 1, every
           nonzero Q1 part has pc_{m-1} >= k  (DCX3 C2 one level up)
  PID-DIR: on direct live rows the pc_{m-1} = 0 part is nonzero (DCX3 C3)
Working predictions (NOT seals): PID legs 0-divergence at g_0 = 1 (DCX3
C2/C3 precedent); NO prediction at g_0 >= 2 (first mechanism data ever —
the literal-e_0 divisor must there ride C_k rebuild paths, not the naked
promotion edge).  Any divergence is dumped instance-by-instance.

Consumption: rmengine_pe_reimpl.Eng/prep (the PE hostile-pass reimplementation,
consumed READ-ONLY by import; it in turn consumes the sealed harness chain
grb_order2_check / strata3_probe / iterlawr_probe / iterlaw4_probe /
iterlawn_diag byte-untouched).  This runner mutates NONE of those files.
My law census is an independent re-implementation from the note text; a
consistency leg ties it to PE.law_leg AND to the committed
rmengine_pe_reimpl_results.json on the shared shapes (XM3A/XM3B).

Verdict lines are LAW-KEYED; controls are SEPARATE and must FIRE (teeth):
  CTRL-CAP1   carries capped at 1 (the REFUTED v1 pattern, generalized)
  CTRL-NOCARRY  c_{m-1} deleted from the top clause
  CTRL-EG     pool divisor e_{l-1}*g_{l-1} instead of literal e_{l-1}
  CTRL-THRP1 / CTRL-THRM1  threshold 2e+1 / 2e-1
  CTRL-NOU    the u-chain terms s_l(u_l) deleted from every pool
A control that does not trip on >= 1 pair somewhere in the battery is a
CONTROL FAILURE (reported separately; never colors the law lines).

Modes: --design  = pre-seal design pass: tower certs + INTEGER law-side
                   strata + E1IH track censuses ONLY (no Q1, no meas, no PID;
                   the DCX3 design-disclosure convention), writes
                   wmultdcx_stress_design.json;
       (default) = the sealed battery: full law census + PID traces,
                   writes wmultdcx_stress_results.json.
Deterministic, exact arithmetic, no sampling, no seed.
"""
import sys, os, time, json, hashlib

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import rmengine_pe_reimpl as PE                     # read-only consumption
from grb_order2_check import (pnorm, padd, pneg, pmul, ppow, pscal,
                              pdivmod, eq12, INF)

VIOL = []      # verdict-family violations (predicted-0 legs)
CM   = []      # LAW countermodels (law != meas) — the unit's hunted product
PIDD = []      # pool-identification divergences — the other hunted product
CNT  = {}

def note(fam, n=1): CNT[fam] = CNT.get(fam, 0) + n
def viol(fam, tag, detail):
    VIOL.append((fam, tag, str(detail)[:300]))
    if sum(1 for v in VIOL if v[0] == fam) <= 8:
        print(f"  VIOLATION [{fam}] {tag}: {str(detail)[:260]}")
def countermodel(tag, detail):
    CM.append((tag, detail))
    print(f"  *** LAW COUNTERMODEL *** {tag}: {str(detail)[:400]}")
def pid_div(fam, tag, detail):
    PIDD.append((fam, tag, detail))
    print(f"  *** PID DIVERGENCE [{fam}] *** {tag}: {str(detail)[:400]}")

def prod(xs):
    r = 1
    for x in xs: r *= x
    return r

# ------------- harness-event capture around PE-level violations --------------
def pe_baseline(): return len(PE.VIOL)
def pe_harvest(tag, n0):
    fresh = PE.VIOL[n0:]
    for f in fresh:
        viol("HARNESS", tag, f)
    return len(fresh)

# ===================== the law side (S6.1, reimplemented) =====================
def uchain(E):
    """u_l chain + s_l(u_l) values; None on integrality failure (verdict)."""
    m = E.m
    u = {m: E.gam[m+1]}; su = {}
    for l in range(m, 1, -1):
        s = eq12(u[l], E.e[l-1], E.h[l-1])[0]; su[l] = s
        num = u[l] - s*E.gam[l]
        if num % E.e[l-1] != 0 or num < 0:
            viol("V-UCHAIN", E.tag, f"u-chain not in Z>=0 at l={l}: u_l={u[l]}")
            return None, None
        u[l-1] = num//E.e[l-1]
    su[1] = eq12(u[1], E.e[0], E.h[0])[0]
    return u, su

def window_split(E):
    """the composite anchor split + window base (PE.law_leg verbatim-adapted)."""
    m = E.m
    Etot = prod(E.e[:m+1])
    wPhi = {0: 0}
    for l in range(1, m+1):
        wPhi[l] = E.e[l-1]*E.g[l-1]*E.gam[l]
    def split(gamma):
        s = {}; b = gamma
        for l in range(m+1, 0, -1):
            slv, ulv = eq12(b, E.e[l-1], E.h[l-1])
            s[l] = slv; b = ulv - slv*wPhi[l-1]
        return s, b
    G0 = ((3*E.gam[m+1])//Etot + 1)*Etot
    while not all(split(g)[1] >= 0 for g in range(G0, G0 + Etot)):
        G0 += Etot
    return Etot, G0, split

def anchors_of(E, Etot, G0, split):
    R = E.R
    anch = {}
    for gv in range(G0, G0 + Etot):
        s, u1 = split(gv)
        a = pscal(R, R["pi_pow"](u1), [R["one"]])
        for l in range(E.m):
            a = pmul(R, a, ppow(R, E.Phis[l], s[l+1]))
        anch[gv] = (pnorm(R, a), s, u1)
    return anch

def pools_of(E, sA, sB, su):
    m = E.m
    cs = []; pools = []; c = 0
    for l in range(1, m):
        pool = sA[l] + sB[l] + su[l] + c
        pools.append(pool)
        c = pool//E.e[l-1]
        cs.append(c)
    D = sA[m] + sB[m] + su[m]
    return pools, cs, D, D + (cs[-1] if cs else 0)

def variant_preds(E, sA, sB, su, track):
    """primary law + the six broken-law controls, one pair."""
    m = E.m; etop = E.e[m-1]
    pools, cs, D, top = pools_of(E, sA, sB, su)
    out = {"primary": track and top >= 2*etop}
    c = 0
    for l in range(1, m):
        c = min(1, (sA[l] + sB[l] + su[l] + c)//E.e[l-1])
    out["CAP1"] = track and (D + c >= 2*etop)
    out["NOCARRY"] = track and (D >= 2*etop)
    c = 0
    for l in range(1, m):
        c = (sA[l] + sB[l] + su[l] + c)//(E.e[l-1]*E.g[l-1])
    out["EG"] = track and (D + c >= 2*etop)
    out["THRP1"] = track and (top >= 2*etop + 1)
    out["THRM1"] = track and (top >= 2*etop - 1)
    c = 0
    for l in range(1, m):
        c = (sA[l] + sB[l] + c)//E.e[l-1]
    out["NOU"] = track and (sA[m] + sB[m] + c >= 2*etop)
    return pools, cs, D, top, out

CTRLS = ("CAP1", "NOCARRY", "EG", "THRP1", "THRM1", "NOU")

# ================ the two-stage promotion-tracking trace (PID) ================
TREE_CAP = 500000

def reduce_pc(E, cells, qsink, stats):
    """E1-priority reduction with per-cell promotion-count vectors.
    cells: (sign, b, j[0..m-1], pc[0..m-1]); pc[l] = # promotions into
    level l+1 along ancestry (pc[m-1] counts Phi_m exits).  Exits land in
    qsink (cofactor cells of the Phi_m quotient); leaves returned."""
    R = E.R; m = E.m
    corr = E.corr_table()
    stack = list(cells)
    leaves = []
    nodes = 0
    while stack:
        sign, b, j, pc = stack.pop()
        nodes += 1
        if nodes > TREE_CAP:
            viol("V-CONS", E.tag, "PID tree cap exceeded")
            return None, nodes
        for l in range(m):
            stats["maxpc_all"][l] = max(stats["maxpc_all"][l], pc[l])
        i = next((l for l in range(m) if j[l] >= E.P[l]), None)
        if i is None:
            leaves.append((sign, b, j, pc))
            continue
        if i <= m-2:
            j2 = list(j); j2[i] -= E.P[i]; j2[i+1] += 1
            pc2 = list(pc); pc2[i] += 1
            stack.append((sign, b, tuple(j2), tuple(pc2)))
        else:
            j2 = list(j); j2[m-1] -= E.P[m-1]
            pc2 = list(pc); pc2[m-1] += 1
            qsink.append((sign, b, tuple(j2), tuple(pc2)))
        for (k, dcells) in corr[i]:
            base = list(j); base[i] -= E.P[i] - E.e[i]*k
            for (cd, av) in dcells:
                Lc, Xc, Yc = E.digit_split(b, cd)
                nj = list(base)
                for l in range(min(i, len(av))):
                    nj[l] += av[l]
                for (cc, dj0) in ((Lc, 0), (Xc, 0), (Yc, 1)):
                    if not pnorm(R, cc): continue
                    jj = list(nj); jj[0] += dj0
                    stack.append((-sign, cc, tuple(jj), pc))
    return leaves, nodes

def cellsum(E, cells):
    R = E.R
    acc = []
    for (sign, b, j, pc) in cells:
        lp = E.cellpoly(b, j)
        acc = padd(R, acc, lp if sign > 0 else pneg(R, lp))
    return pnorm(R, acc)

def pid_trace(E, sA, sB, u1a, u1b, aA, aB, cs, D, kdef, live, key, recs):
    """two-stage promotion-profiled Q1; the PID-MAX/DEF/DIR comparisons.
    Stage-1 seed = the FORMAL anchor-exponent cell (b = pi^(u1+u1'),
    j = sA+sB), NOT the dev of the product polynomial: the Phi-adic
    re-expansion of a*a' redistributes exponent mass upward arithmetically
    (a deg-(>= deg Phi_l) coefficient acquires higher digits), which would
    fake untracked promotions; the formal cell keeps every level crossing
    on an explicit tree edge (the DCX3 TraceTree convention)."""
    R = E.R; m = E.m
    stats = dict(maxpc_all=[0]*m)
    # stage 1: a*a' -> E1IH (exit cofactors) + remainder leaves
    prodp = pmul(R, aA, aB)
    b0 = pscal(R, R["pi_pow"](u1a + u1b), [R["one"]])
    j0 = tuple(sA[l+1] + sB[l+1] for l in range(m))
    init = [(1, b0, j0, (0,)*m)]
    q1cellsink = []
    out = reduce_pc(E, init, q1cellsink, stats)
    if out[0] is None: return None
    leaves1, nodes1 = out
    E1c, E0c = pdivmod(R, prodp, E.Phis[m])
    if cellsum(E, q1cellsink) != pnorm(R, E1c):
        viol("V-CONS", E.tag, f"stage-1 exit sum != E1IH at {key}")
    if cellsum(E, leaves1) != pnorm(R, E0c):
        viol("V-CONS", E.tag, f"stage-1 leaf sum != E0IH at {key}")
    # stage 2: E1IH * Chat, seeded per exit cofactor x Chat d-cell
    init2 = []
    for (sign, b, j, pc) in q1cellsink:
        for (cD, jD) in E.Dcells:
            Lc, Xc, Yc = E.digit_split(b, cD)
            js = tuple(j[l] + jD[l] for l in range(m))
            for (cc, dj0) in ((Lc, 0), (Xc, 0), (Yc, 1)):
                if not pnorm(R, cc): continue
                jj = list(js); jj[0] += dj0
                init2.append((sign, cc, tuple(jj), pc))
    q2sink = []
    out2 = reduce_pc(E, init2, q2sink, stats)
    if out2[0] is None: return None
    leaves2, nodes2 = out2
    Q1c, R1c = pdivmod(R, pmul(R, E1c, E.Chat), E.Phis[m])
    if cellsum(E, q2sink) != pnorm(R, Q1c):
        viol("V-CONS", E.tag, f"stage-2 exit sum != Q1 at {key}")
    if cellsum(E, leaves2) != pnorm(R, R1c):
        viol("V-CONS", E.tag, f"stage-2 leaf sum != rem(E1IH*Chat) at {key}")
    for (sign, b, j, pc) in q2sink:
        if pc[m-1] != 2:
            viol("V-CONS", E.tag, f"Q1 cell with {pc[m-1]} exits at {key}")
    # promotion-profile parts of Q1, per level
    maxnz = [None]*(m-1); minnz_top = None
    for l in range(1, m):        # promotions into level l = pc index l-1
        byk = {}
        for (sign, b, j, pc) in q2sink:
            byk.setdefault(pc[l-1], []).append((sign, b, j, pc))
        for k in sorted(byk):
            nz = bool(cellsum(E, byk[k]))
            if nz:
                if maxnz[l-1] is None or k > maxnz[l-1]:
                    maxnz[l-1] = k
                if l == m-1 and (minnz_top is None or k < minnz_top):
                    minnz_top = k
    rec = dict(key=key, cs=cs, D=D, kdef=kdef, live=live,
               maxnz=maxnz, minnz_top=minnz_top,
               maxpc_all=stats["maxpc_all"],
               nodes=nodes1 + nodes2, q1nz=bool(pnorm(R, Q1c)))
    recs.append(rec)
    # PID-MAX: nonzero part beyond the pool floor
    for l in range(1, m):
        if maxnz[l-1] is not None and maxnz[l-1] > cs[l-1]:
            pid_div("PID-MAX", E.tag,
                    dict(key=key, level=l, maxnz=maxnz[l-1], c=cs[l-1],
                         cs=cs, D=D, kdef=kdef))
    # PID-DEF: deficit-k live row must carry the top feed at depth >= k
    if live and kdef >= 1:
        if minnz_top is None or minnz_top < kdef:
            pid_div("PID-DEF", E.tag,
                    dict(key=key, kdef=kdef, minnz_top=minnz_top, cs=cs, D=D))
    # PID-DIR: direct live row clean-visible
    if live and kdef <= 0:
        note("pid_direct")
        if minnz_top == 0:
            note("pid_direct_clean")
    return rec

# ============================ one battery tower ===============================
def run_tower(spec, results, mode):
    tag, m, kind, p, d0, reads = spec
    t0 = time.time()
    n0 = pe_baseline()
    try:
        E = PE.Eng(m, kind, p, d0, reads, tag)
        PE.prep(E)
    except Exception as ex:
        viol("HARNESS", tag, f"tower construction failed: {ex}")
        return None
    nharn = pe_harvest(tag, n0)
    u, su = uchain(E)
    if u is None: return None
    Etot, G0, split = window_split(E)
    anch = anchors_of(E, Etot, G0, split)
    etop = E.e[m-1]
    res = dict(tag=tag, m=m, kind=kind, p=p, d0=d0, reads=reads,
               Etot=Etot, G0=G0, harness_events=nharn,
               uchain={str(l): u[l] for l in u},
               su={str(l): su[l] for l in su})
    cen = dict(pairs=0, strack=0, track=0, live=0, pred=0, mism=0,
               q1nz_offlocus=0, chainfed=0, nested12=0, nested123=0,
               c1eq2=0, maxc=[0]*(m-1), edge_top=0, justmiss_top=0,
               justmiss_live=0, def_hist={}, kdef_hist={},
               pool_mult_edge=0, flat_pass=0)
    ctrl = {k: 0 for k in CTRLS}
    pid_keys = {}
    R = E.R
    for ga in range(G0, G0 + Etot):
        aA, sA, u1a = anch[ga]
        for gb in range(G0, G0 + Etot):
            aB, sB, u1b = anch[gb]
            cen["pairs"] += 1
            strack = (sA[m+1] == E.e[m]-1 and sB[m+1] == E.e[m]-1)
            if strack: cen["strack"] += 1
            pools, cs, D, top, preds = variant_preds(E, sA, sB, su, True)
            for i, c in enumerate(cs):
                cen["maxc"][i] = max(cen["maxc"][i], c)
                if c > 2:
                    viol("V-LCAP", tag, f"c_{i+1}={c} > 2 at ({ga},{gb})")
            if mode == "design":
                # design side: E1IH allowed (IH-side), NO Q1/meas
                track = False
                if strack:
                    E1 = pdivmod(R, pmul(R, aA, aB), E.Phis[m])[0]
                    track = bool(pnorm(R, E1))
                if track:
                    cen["track"] += 1
                    if preds["primary"]:
                        cen["pred"] += 1
                        kd = 2*etop - D
                        cen["kdef_hist"][kd] = cen["kdef_hist"].get(kd, 0) + 1
                    _strata(cen, E, m, etop, pools, cs, D, top, su, sA, sB,
                            live=preds["primary"])
                    for k in CTRLS:
                        if (preds[k] and track) != (preds["primary"] and track):
                            ctrl[k] += 1
                continue
            # sealed mode: full measured side, diag-style (every pair)
            E1, _ = pdivmod(R, pmul(R, aA, aB), E.Phis[m])
            e1nz = bool(pnorm(R, E1))
            track = strack and e1nz
            if track: cen["track"] += 1
            meas = False
            if e1nz:
                Q1 = pdivmod(R, pmul(R, E1, E.Chat), E.Phis[m])[0]
                if pnorm(R, Q1):
                    Tsum = sA[m+1] + sB[m+1]
                    dpl = Tsum//E.e[m]
                    locus = ((dpl == 1 and strack and E.e[m] >= 2)
                             or (Tsum == E.e[m]-1 and E.e[m] == 1))
                    if locus:
                        meas = True
                    else:
                        cen["q1nz_offlocus"] += 1
            pred = preds["primary"] and track
            if pred: cen["pred"] += 1
            if meas:
                cen["live"] += 1
                if cs and cs[-1] > 0: cen["chainfed"] += 1
                d = top - 2*etop
                cen["def_hist"][d] = cen["def_hist"].get(d, 0) + 1
                kd = 2*etop - D
                cen["kdef_hist"][kd] = cen["kdef_hist"].get(kd, 0) + 1
            if track:
                _strata(cen, E, m, etop, pools, cs, D, top, su, sA, sB,
                        live=meas)
            if meas != pred:
                cen["mism"] += 1
                countermodel(tag, dict(
                    pair=(ga, gb), meas=meas, pred=pred,
                    sA={l: sA[l] for l in sA}, sB={l: sB[l] for l in sB},
                    u1=(u1a, u1b), su={str(l): su[l] for l in su},
                    pools=pools, carries=cs, D=D, top=top,
                    threshold=2*etop, track=track))
            for k in CTRLS:
                if (preds[k] and track) != meas:
                    ctrl[k] += 1
            # PID rep selection (track rows only, dedup by split key)
            if track and m >= 2:
                key = (tuple(sorted([(tuple(sA[l] for l in range(1, m+2)), u1a),
                                     (tuple(sB[l] for l in range(1, m+2)), u1b)])))
                if key not in pid_keys:
                    kdef = 2*etop - D
                    want = (meas or top in (2*etop - 1, 2*etop, 2*etop - 2)
                            or (len(cs) >= 2 and cs[0] > 0 and cs[1] > 0)
                            or (cs and max(cs) >= 2))
                    if want:
                        pid_keys[key] = (ga, gb, cs, D, kdef, meas,
                                         sA, sB, u1a, u1b)
    res["census"] = cen
    res["controls"] = ctrl
    # ---- PID traces (sealed mode only) ----
    pid_recs = []
    if mode != "design":
        n0pid = pe_baseline()
        cap = 14 if m >= 4 else 40
        chosen = sorted(pid_keys.items(), key=lambda kv: (
            not kv[1][5],                     # live rows first
            -(kv[1][2][0] if kv[1][2] else 0),
            kv[0]))[:cap]
        for key, (ga, gb, cs, D, kdef, meas, sA, sB, u1a, u1b) in chosen:
            aA = anch[ga][0]; aB = anch[gb][0]
            pid_trace(E, sA, sB, u1a, u1b, aA, aB, cs, D, kdef, meas,
                      (ga, gb), pid_recs)
        pe_harvest(tag + "/pid", n0pid)
        res["pid"] = pid_recs
        res["pid_traced"] = len(pid_recs)
    print(f"-- {tag} m={m} {kind},p={p},d0={d0} e={E.e[:m+1]}: "
          f"pairs={cen['pairs']} strack={cen['strack']} track={cen['track']} "
          f"live={cen['live']} pred={cen['pred']} MISM={cen['mism']} "
          f"nested12={cen['nested12']}/{cen['nested123']} "
          f"c1eq2={cen['c1eq2']} maxc={cen['maxc']} defs={cen['def_hist']} "
          f"kdefs={cen['kdef_hist']} "
          f"edge/miss={cen['edge_top']}/{cen['justmiss_top']} "
          f"pid={len(pid_recs)} ({time.time()-t0:.1f}s)")
    results.append(res)
    return res

def _strata(cen, E, m, etop, pools, cs, D, top, su, sA, sB, live):
    if len(cs) >= 2 and cs[0] > 0 and cs[1] > 0: cen["nested12"] += 1
    if len(cs) >= 3 and cs[0] > 0 and cs[1] > 0 and cs[2] > 0:
        cen["nested123"] += 1
    if cs and cs[0] >= 2: cen["c1eq2"] += 1
    if top == 2*etop: cen["edge_top"] += 1
    if top == 2*etop - 1:
        cen["justmiss_top"] += 1
        if live: cen["justmiss_live"] += 1
    for i, pl in enumerate(pools):
        if pl > 0 and pl % E.e[i] == 0:
            cen["pool_mult_edge"] += 1
            break
    if any(E.e[l] == 1 for l in range(1, m)) and cs and cs[-1] > 0:
        cen["flat_pass"] += 1

# ===================== consistency legs (PE tie + artifacts) ==================
def consistency_leg(results):
    """my census vs PE.law_leg (fresh) AND vs the committed PE results JSON,
    on the two shared shapes M3A (d0=1) and M3B (d0=2, g0=2, maxc=2)."""
    stored = json.load(open(os.path.join(HERE,
                            "rmengine_pe_reimpl_results.json")))
    for (tag, m, kind, p, d0, reads) in [
            ("M3A", 3, "Zp", 5, 1, [(2,1,1), (2,1,1), (2,1,1), (2,1,1)]),
            ("M3B", 3, "Zp", 3, 2, [(2,1,2), (3,2,1), (2,1,1), (2,1,1)])]:
        n0 = pe_baseline()
        E = PE.Eng(m, kind, p, d0, reads, "X" + tag)
        PE.prep(E)
        pe_harvest("X" + tag, n0)
        scratch = dict(MU5=0, MU6=0)
        n1 = pe_baseline()
        law = PE.law_leg(E, scratch)
        pe_harvest("X" + tag + "/law_leg", n1)
        mine = [r for r in results if r["tag"] == "X" + tag]
        if not mine:
            viol("V-PETIE", tag, "own census missing"); continue
        c = mine[0]["census"]
        ok = (law["pairs"] == c["pairs"] and law["track"] == c["track"]
              and law["live"] == c["live"] and law["mism"] == c["mism"]
              and law["chainfed"] == c["chainfed"])
        st = stored["towers"][tag]["law"]
        ok2 = (st["pairs"] == c["pairs"] and st["track"] == c["track"]
               and st["live"] == c["live"] and st["mism"] == c["mism"])
        if not ok:
            viol("V-PETIE", tag, f"fresh law_leg {law} != mine {c}")
        if not ok2:
            viol("V-PETIE", tag, f"stored {st} != mine "
                 f"{ {k: c[k] for k in ('pairs','track','live','mism')} }")
        print(f"-- PE-tie {tag}: fresh_leg_match={ok} stored_match={ok2}")

# ============================== the battery ROSTER ============================
# Frozen at design close (see wmultdcx_stress_design.json for the scan that
# picked the h-tracks; strata targets per corner class in the header).
# Frozen from the design scan (wmultdcx_stress_design.json, 45 candidates):
# per-corner design strata quoted as  track/pred[kdef2]/nested12/c1eq2.
ROSTER = [
    # A/B: deep pools, c1=2, top-deficit-2 (e0=3/4)     66/28[2]/53/10 + 120/105[42]/114/30
    ("W3DEEP",  3, "Zp", 3, 1, [(3,2,1), (2,1,1), (2,1,1), (2,1,1)]),
    ("W3DEEP4", 3, "Zp", 3, 1, [(4,3,1), (2,1,1), (2,3,1), (2,1,1)]),
    # A: all-2 nested carries, fresh h-track, cross-ring 28/21[6]/22 each
    ("W3NEST",  3, "Zp", 3, 1, [(2,1,1), (2,1,1), (2,3,1), (2,1,1)]),
    ("W3NESTF", 3, "Fpt", 2, 1, [(2,1,1), (2,1,1), (2,3,1), (2,1,1)]),
    # C: flat interior levels (d0=1): pass-through / carry-decided laws
    ("W3FMID",  3, "Zp", 3, 1, [(2,1,1), (1,1,1), (2,1,1), (2,1,1)]),   # 6/3
    ("W3FTOP",  3, "Zp", 3, 1, [(2,1,1), (2,1,1), (1,1,1), (2,1,1)]),   # 6/3[3] law=track&c2>=2
    ("W3FDBL",  3, "Zp", 3, 1, [(3,1,1), (1,1,1), (1,1,1), (2,1,1)]),   # 3/1[1] law=track&c1>=2
    ("W3FMIDF", 3, "Fpt", 2, 1, [(2,1,1), (1,1,1), (2,1,1), (2,1,1)]),
    # track-everywhere top (e3=1)                        66/55[20]/60/10
    ("W3TRK1",  3, "Zp", 3, 1, [(3,2,1), (2,1,1), (2,1,1), (1,1,1)]),
    # D: direct rows at m=3 (e2=3, kdef<=0 reachable)    66/55[kdef0:16,2:9]
    ("W3DIR",   3, "Zp", 3, 1, [(2,1,1), (2,1,1), (3,2,1), (2,1,1)]),
    # E: g0 >= 2 (literal-e0 divisor stress)
    ("W3G2A",   3, "Zp", 3, 1, [(3,1,2), (2,1,1), (2,3,1), (2,1,1)]),   # 54/51[16]/48/6
    ("W3G2B",   3, "Zp", 3, 2, [(2,1,2), (3,2,1), (2,3,1), (2,1,1)]),   # 60/36[6]/42 d0=2
    ("W3G2P5",  3, "Zp", 5, 2, [(2,1,2), (2,1,1), (2,1,1), (2,1,1)]),   # fresh p=5 EXT
    # cross-ring deep pool (deficit-2 + c1=2 in eq char) 66/28[2]/53/10
    ("W3DEEPF", 3, "Fpt", 2, 1, [(3,2,1), (2,1,1), (2,1,1), (2,1,1)]),
    # F: m=4 (LAW-DCX-5): triple nesting + deep + flat + cross-ring
    ("W4NEST",  4, "Zp", 3, 1, [(2,1,1), (2,1,1), (2,3,1), (2,1,1), (2,1,1)]),  # n123=65
    ("W4DEEP",  4, "Zp", 3, 1, [(3,1,1), (2,1,1), (2,1,1), (2,1,1), (2,1,1)]),  # n123=182 c1eq2=36 kdef2=2
    ("W4FLAT",  4, "Zp", 3, 1, [(2,1,1), (2,3,1), (1,1,1), (2,1,1), (2,1,1)]),  # maxc=[1,2,2]
    ("W4NESTF", 4, "Fpt", 2, 1, [(2,1,1), (2,1,1), (2,3,1), (2,1,1), (2,1,1)]),
    # consistency replicas (PE tie; shared shapes, run identically)
    ("XM3A",    3, "Zp", 5, 1, [(2,1,1), (2,1,1), (2,1,1), (2,1,1)]),
    ("XM3B",    3, "Zp", 3, 2, [(2,1,2), (3,2,1), (2,1,1), (2,1,1)]),
]

# design-scan candidate pool (h-track tuning; design mode only)
def design_cands():
    out = []
    for h0 in (1, 2):
        for h1 in (1, 3):
            out.append((f"DEEP-h{h0}{h1}", 3, "Zp", 3, 1,
                        [(3,h0,1), (2,h1,1), (2,1,1), (2,1,1)]))
    for h0 in (1, 3):
        for h2 in (1, 3):
            out.append((f"DEEP4-h{h0}{h2}", 3, "Zp", 3, 1,
                        [(4,h0,1), (2,1,1), (2,h2,1), (2,1,1)]))
    for h1 in (1, 3):
        for h2 in (1, 3):
            out.append((f"NEST-h{h1}{h2}", 3, "Zp", 3, 1,
                        [(2,1,1), (2,h1,1), (2,h2,1), (2,1,1)]))
    for h0 in (1, 3):
        for h3 in (1, 3):
            out.append((f"FMID-h{h0}{h3}", 3, "Zp", 3, 1,
                        [(2,h0,1), (1,1,1), (2,1,1), (2,h3,1)]))
    for h0 in (1, 3):
        for h1 in (1, 3):
            out.append((f"FTOP-h{h0}{h1}", 3, "Zp", 3, 1,
                        [(2,h0,1), (2,h1,1), (1,1,1), (2,1,1)]))
    for h0 in (1, 2):
        out.append((f"FDBL-h{h0}", 3, "Zp", 3, 1,
                    [(3,h0,1), (1,1,1), (1,1,1), (2,1,1)]))
    for h0 in (1, 2):
        out.append((f"TRK1-h{h0}", 3, "Zp", 3, 1,
                    [(3,h0,1), (2,1,1), (2,1,1), (1,1,1)]))
    for h2 in (1, 2):
        for h3 in (1, 3):
            out.append((f"DIR-h{h2}{h3}", 3, "Zp", 3, 1,
                        [(2,1,1), (2,1,1), (3,h2,1), (2,h3,1)]))
    for h1 in (1, 3):
        out.append((f"G2A-h{h1}", 3, "Zp", 3, 1,
                    [(2,1,2), (2,h1,1), (2,1,1), (2,1,1)]))
    out.append(("G2B", 3, "Zp", 5, 2, [(2,1,2), (2,1,1), (2,1,1), (2,1,1)]))
    for h2 in (1, 3):
        out.append((f"G2C-h{h2}", 3, "Zp", 3, 1,
                    [(3,1,2), (2,1,1), (2,h2,1), (2,1,1)]))
        out.append((f"G2D-h{h2}", 3, "Zp", 3, 2,
                    [(2,1,2), (3,2,1), (2,h2,1), (2,1,1)]))
    for h1 in (1, 3):
        for h2 in (1, 3):
            out.append((f"M4-h{h1}{h2}", 4, "Zp", 3, 1,
                        [(2,1,1), (2,h1,1), (2,h2,1), (2,1,1), (2,1,1)]))
    for h0 in (1, 2):
        for h1 in (1, 3):
            out.append((f"M4DEEP-h{h0}{h1}", 4, "Zp", 3, 1,
                        [(3,h0,1), (2,h1,1), (2,1,1), (2,1,1), (2,1,1)]))
    for h3 in (1, 3):
        out.append((f"M4FLAT-h{h3}", 4, "Zp", 3, 1,
                    [(2,1,1), (2,3,1), (1,1,1), (2,h3,1), (2,1,1)]))
    # Fpt mirrors (construction + strata check in eq characteristic)
    out.append(("F-NEST13", 3, "Fpt", 2, 1,
                [(2,1,1), (2,1,1), (2,3,1), (2,1,1)]))
    out.append(("F-FMID11", 3, "Fpt", 2, 1,
                [(2,1,1), (1,1,1), (2,1,1), (2,1,1)]))
    out.append(("F-DEEP21", 3, "Fpt", 2, 1,
                [(3,2,1), (2,1,1), (2,1,1), (2,1,1)]))
    out.append(("F-M4h13", 4, "Fpt", 2, 1,
                [(2,1,1), (2,1,1), (2,3,1), (2,1,1), (2,1,1)]))
    return out

# ================================== main ======================================
def main():
    t0 = time.time()
    mode = ("design" if "--design" in sys.argv
            else "smoke" if "--smoke" in sys.argv else "run")
    print(f"== wmultdcx_stress: LAW-DCX-(m+1) countermodel hunt "
          f"[mode={mode}] ==")
    results = []
    specs = (design_cands() if mode == "design"
             else [s for s in ROSTER if s[0].startswith("X")]
             if mode == "smoke" else ROSTER)
    for spec in specs:
        run_tower(spec, results, mode)
    if mode == "design":
        out = dict(mode="design", towers=results,
                   note="INTEGER law-side strata + E1IH track census only; "
                        "no Q1, no meas, no PID (design disclosure)",
                   elapsed=time.time() - t0)
        with open(os.path.join(HERE, "wmultdcx_stress_design.json"), "w") as fh:
            json.dump(out, fh, indent=1, default=str)
        print(f"design pass done; {len(results)} candidates; "
              f"elapsed {time.time()-t0:.1f}s")
        return 0
    consistency_leg(results)
    # ------------- verdicts (law-keyed; controls separate) -------------
    per_m = {}
    for r in results:
        if r["tag"].startswith("X"): continue      # replicas: tie leg only
        d = per_m.setdefault(r["m"], dict(pairs=0, track=0, live=0, mism=0))
        c = r["census"]
        d["pairs"] += c["pairs"]; d["track"] += c["track"]
        d["live"] += c["live"];   d["mism"] += c["mism"]
    print()
    for m in sorted(per_m):
        d = per_m[m]
        print(f"LAW-DCX-{m+1} VERDICT (pool-floor law == measured, "
              f"countermodel hunt): violations={d['mism']} over {d['pairs']} "
              f"pairs (track={d['track']}, live={d['live']}) "
              f"[{'NO COUNTERMODEL' if d['mism'] == 0 else 'COUNTERMODEL FOUND'}]")
    nstr = sum(1 for v in VIOL if v[0] in ("V-UCHAIN", "V-LCAP"))
    print(f"STRUCT VERDICT (u-chain in Z>=0 + L-CAP c_l <= 2, predicted-0): "
          f"{'GREEN' if nstr == 0 else 'RED'} [{nstr} violations]")
    ncons = sum(1 for v in VIOL if v[0] in ("V-CONS", "V-PETIE", "HARNESS"))
    print(f"CONS VERDICT (stage trees == canonical divisions + PE/artifact "
          f"tie + harness events, predicted-0): "
          f"{'GREEN' if ncons == 0 else 'RED'} [{ncons} violations]")
    npm = sum(1 for v in PIDD if v[0] == "PID-MAX")
    npd = sum(1 for v in PIDD if v[0] == "PID-DEF")
    ntr = sum(r.get("pid_traced", 0) for r in results)
    print(f"PID-MAX CENSUS (max promo count into level l vs "
          f"floor(pool_l/e_(l-1)), nonzero Q1 parts, instance-keyed): "
          f"divergences={npm} over {ntr} traced rows")
    print(f"PID-DEF VERDICT (deficit-k live rows feed the top at depth >= k, "
          f"DCX3-C2 one level up, working-predicted-0 at g0=1): "
          f"{'GREEN' if npd == 0 else 'RED'} [{npd} violations]")
    print(f"PID-DIR CENSUS (direct live rows clean-visible at depth 0): "
          f"{CNT.get('pid_direct_clean', 0)}/{CNT.get('pid_direct', 0)}")
    ctrl_tot = {k: 0 for k in CTRLS}
    for r in results:
        if r["tag"].startswith("X"): continue
        for k in CTRLS: ctrl_tot[k] += r["controls"][k]
    teeth = all(ctrl_tot[k] > 0 for k in CTRLS)
    print(f"CONTROL VERDICT (broken-law variants must trip vs meas, teeth, "
          f"SEPARATE): {'MET' if teeth else 'CONTROL FAILURE'} {ctrl_tot}")
    # coverage meters
    tot = lambda k: sum(r["census"][k] for r in results
                        if not r["tag"].startswith("X"))
    meters = dict(nested12=tot("nested12"), c1eq2=tot("c1eq2"),
                  edge_top=tot("edge_top"), justmiss_top=tot("justmiss_top"),
                  flat_pass=tot("flat_pass"),
                  deficit2live=sum(r["census"]["kdef_hist"].get(2, 0)
                                   for r in results
                                   if not r["tag"].startswith("X")),
                  nested123=tot("nested123"))
    m_ok = (meters["nested12"] >= 20 and meters["c1eq2"] >= 10 and
            meters["justmiss_top"] >= 10 and meters["flat_pass"] >= 5)
    print(f"COVERAGE (battery meters: nested12>=20, c1eq2>=10, "
          f"justmiss>=10, flat_pass>=5): {'MET' if m_ok else 'NOT-MET'} "
          f"{meters}")
    print(f"countermodels: {len(CM)}; PID divergences: {len(PIDD)}; "
          f"verdict-family violations: {len(VIOL)}")
    print(f"counters: {dict(sorted(CNT.items()))}")
    print(f"elapsed {time.time()-t0:.1f}s")
    def md5(fn):
        with open(os.path.join(HERE, fn), "rb") as fh:
            return hashlib.md5(fh.read()).hexdigest()
    out = dict(mode="run", countermodels=CM, pid_divergences=PIDD,
               violations=VIOL, counters=CNT, controls=ctrl_tot,
               meters=meters, per_m=per_m, towers=results,
               provenance={fn: md5(fn) for fn in
                           ("wmultdcx_stress.py", "rmengine_pe_reimpl.py",
                            "grb_order2_check.py", "iterlaw4_probe.py",
                            "iterlawn_diag.py")},
               elapsed=time.time() - t0)
    fn = ("wmultdcx_stress_results.json" if mode == "run"
          else "wmultdcx_stress_smoke.json")
    with open(os.path.join(HERE, fn), "w") as fh:
        json.dump(out, fh, indent=1, default=str)
    return 0

if __name__ == "__main__":
    sys.exit(main())
