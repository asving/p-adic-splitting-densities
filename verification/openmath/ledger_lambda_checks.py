#!/usr/bin/env python3
"""ledger_lambda_checks.py — LEDGER-Λ machine leg (synthesis pass 9 unit S7.U1;
2026-08-08 campaign, wallclock 2026-08-04).

Non-textual leg of lean/notes/openmath/LEDGERLAMBDA_2026-08-08.md: ONE
walk-replay runner computing ALL FIVE weight-functional faces of the graded
path ledger LED-Lambda simultaneously, per two-exit terminal (plus face A on
stage-1 exit cofactors), on BOTH committed rosters:

  Phase W  : wmultdcx_stress.ROSTER under the WMULTDCX battery pid-key
             selection, replicated verbatim from the committed
             wmultdcx_derive_checks.py (caps 40/14 — the 412-row selection).
  Phase SD : the SURVDISJ rosters PX_ROSTER + SD_ROSTER (copied verbatim from
             survdisj_derive_checks.py) under the committed fresh-tower
             live-row selection (kdef <= c_top, per-stratum caps 12/6).
  Phase YJ : the SDYJ rosters T3_COMMITTED + FRESH (copied verbatim from
             sdyj_checks_v2.py) under the SDYJ live-clause selection.

DESIGN (the extraction-decorrelation discipline).  Rows are traced with the
committed recording walk (survk2_derive_checks.walk_rec, byte-pinned).  For
every terminal, THIS runner replays the recorded edge list through its OWN
fresh implementation of the note's S1 quantum table (fresh gamma/Gamma/E/W/q
arithmetic from the [ILN] S0.1 recursion — never E.gam/E.Gam/E.line, which
are instead cross-tied in LAM-GAM) and computes the five faces from the
replayed data.  The walk's own accumulated counters are cross-checked against
the replay (LAM-LAT), and the stage sums are tied to the canonical divisions
(LAM-CONS).  The recorded flags resolve X vs Y junk; the walk does not label
L vs X per correction edge, so the pi-coordinate face is checked in its
per-path form — the form the committed displays take.  Reference ED.walk
re-tracing is NOT duplicated here (LAM-CONS is the integrity anchor);
disclosed.

Per the standing engine rule (ENGINE REFIT, ledger d326677): imports
engine_ext, calls install(), RE-RUNS agreement_gate() in-unit, and reports
its counts (family LAM-GATE).

============================ SEALED PREDICTIONS ==============================
(violation counts; a family whose observed count differs from its prediction
is RED.  Sealed at commit 1 of the two-commit seal, BEFORE the battery runs.
One pre-commit shakedown of the runner on the throwaway spec outside every
roster (the SDYJ THROWAWAY shape) plus a crash-freedom pass is disclosed.)

  LAM-PIN    md5 pins on the 9 consumed artifacts.               PREDICTED 0.
  LAM-GATE   engine_ext.agreement_gate() re-run in-unit.         PREDICTED 0.
  LAM-GAM    fresh gamma/Gamma_l/E_l/w_mPhi_m/q_l recursion == engine
             constants; fresh line() == E.line on every terminal. PREDICTED 0.
  LAM-CONS   stage-1 cell sum == E1IH; stage-2 == Q1.            PREDICTED 0.
  LAM-LAT    per-edge replay of the S1 table's Delta_lev == terminal j
             AND replayed pi/dmp/ccons/ncorr/exits == the walk's counters
             AND sgn == (-1)^{|CE|}.                             PREDICTED 0.
  LAM-A      face lambda_A == the E-L1 display (two-exit terminals AND
             stage-1 exit cofactors).                            PREDICTED 0.
  LAM-B      face lambda_B == the SD-L2 display, per terminal.   PREDICTED 0.
  LAM-B1     SD-L1 deficit bound + equality analysis, all-g-1 rows.
                                                                 PREDICTED 0.
  LAM-BSTAR  (*) sum defc == Y2 on cascade-slot terminals of all-g-1
             (STK & c >= k) live rows.                           PREDICTED 0.
  LAM-C      face lambda_C == the W-D4 display + threshold >= kdef + the
             (H2) seed pin jD_{m-1} == s_m(u_m).                 PREDICTED 0.
  LAM-D      face lambda_D: w0(b_C) >= w0(b0) + w0(c_D) + sum w0(c_d)
             + X(C) at EVERY g0 (seed term off the actual d-cell),
             equality iff junk-free.                             PREDICTED 0.
  LAM-E      face lambda_E: junk-free line EQUALITY at lamhat + sum pi_l
             q_l; always >= that + X*E_m + nY*Gamma_0.           PREDICTED 0.
  LAM-R      residue face on junk-free terminals: res0(b_C) ==
             res0(b0)*res0(c_D)*prod res0(c_d) in K0, factors nonzero.
                                                                 PREDICTED 0.
  LAM-POOL   fresh c/rho chain == WS.pools_of; the E-L4 unroll identity
             (exact Fractions) on every traced row; on all-g-1 (STK &
             c >= k) live rows: cascade unique, line == betahat_pool =
             lamhat + sum c_l q_l, w0 == u1+u1'+u0, residue != 0.
                                                                 PREDICTED 0.
  LAM-MICRO  M-1 mixed-radix telescope, three weight families, per tower,
             exact Fractions.                                    PREDICTED 0.
  HARNESS    engine-internal violations harvested from the consumed
             modules (tree-cap skips disclosed, not violations). PREDICTED 0.

MUTATION CONTROLS (the CTRL-TEL0 genre: a broken quantum table must fire on
every face; sub-roster W3DEEP + W3G2B + YJ2F; each control must fire >= 1
or the battery is RED — family LAM-MUT):
  MUT-LAT  level-0 promotion consumes P0 - 1 (one corrupted Delta entry).
  MUT-A    the l = 0 term dropped from the face-A telescope (CTRL-TEL0).
  MUT-B    exit mass corrupted: 2*P_{m-1}E_{m-1} - 1.
  MUT-C    face-C identity offset by +1.
  MUT-D    junk-free pi-coordinate equality offset by +1.
  MUT-E    lamhat + 1 in the face-E equality.
  MUT-R    expected residue product shifted by +1 in K0.

Deterministic, exact arithmetic, no sampling.
Usage: python3 ledger_lambda_checks.py [outdir]     (full sealed battery)
       python3 ledger_lambda_checks.py --shakedown  (throwaway spec only)
"""
import sys, os, time, json, hashlib, collections, signal
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
SHAKE = "--shakedown" in sys.argv
OUTDIR = HERE
for a in sys.argv[1:]:
    if not a.startswith("--"):
        OUTDIR = a

VIOL, CNT, FINDINGS = [], {}, []
def note(f, n=1): CNT[f] = CNT.get(f, 0) + n
def viol(fam, tag, detail):
    VIOL.append((fam, tag, str(detail)[:400]))
    if sum(1 for v in VIOL if v[0] == fam) <= 10:
        print(f"VIOLATION [{fam}] {tag}: {str(detail)[:340]}")
def finding(kind, tag, detail):
    FINDINGS.append((kind, tag, detail))
    print(f"*** FINDING [{kind}] {tag}: {str(detail)[:340]}")

PINS = {
    "grb_order2_check.py":       "dab62713175363a7185211890019ae2f",
    "rmengine_pe_reimpl.py":     "103c1a9c99e2b4a3e8b63c93cbf87e25",
    "wmultdcx_stress.py":        "15315cca59c87e6c2001ea744c50aab5",
    "wmultdcx_derive_checks.py": "bea1a43d619a3c91a9a0b2f32c0920c0",
    "empty_derive_checks.py":    "8fed92402bcffe6e0c536f1f9d847612",
    "survk2_derive_checks.py":   "d8493ab90e3578fae60032cde73a3b81",
    "sdyj_checks_v2.py":         "d58be8b80dd01e27eaa7094fe27c4709",
    "survdisj_derive_checks.py": "3eaf69c08f9a5b278826102610d4aa22",
    "engine_ext.py":             "d7eba6ac75d8d894f41ac8d0cf16de9c",
}
for fn, want in PINS.items():
    got = hashlib.md5(open(os.path.join(HERE, fn), "rb").read()).hexdigest()
    if got != want:
        viol("LAM-PIN", fn, f"md5 {got} != pinned {want}")

# ---- the standing engine rule: engine_ext first, install, re-run the gate ---
import engine_ext as EXT
import grb_order2_check as G
from grb_order2_check import (pnorm, padd, pneg, pmul, ppow, pscal, pdivmod,
                              eq12, w0)
import rmengine_pe_reimpl as PE
import wmultdcx_stress as WS
import wmultdcx_derive_checks as WD
import empty_derive_checks as ED
import survk2_derive_checks as SK2

def harvest(tag):
    for src, lst in (("PE", PE.VIOL), ("ED", ED.VIOL), ("WS", WS.VIOL),
                     ("WD", WD.VIOL), ("SK2", SK2.VIOL), ("EXT", EXT.VIOL)):
        while len(lst) > harvest.seen[src]:
            v = lst[harvest.seen[src]]
            if "tree cap" in str(v):
                note("treecap")
            else:
                viol("HARNESS", tag, f"{src}: {v}")
            harvest.seen[src] += 1
harvest.seen = {"PE": 0, "ED": 0, "WS": 0, "WD": 0, "SK2": 0, "EXT": 0}

def prod(xs):
    r = 1
    for x in xs: r *= x
    return r

# ==================== fresh constants (the S0.1 recursion) ===================
def fresh_consts(E):
    """gamma/Gamma/E_l/w_mPhi_m/q_l/W_l/w_l assembled FRESH from the reads;
    cross-tied to the engine in LAM-GAM by the caller."""
    m = E.m
    e = [E.e[l] for l in range(m + 1)]
    h = [E.h[l] for l in range(m + 1)]
    g = [E.g[l] for l in range(m + 1)]
    gam = [0] * (m + 2)
    gam[1] = h[0]
    for l in range(1, m + 1):
        wphi = e[l - 1] * g[l - 1] * gam[l]      # w_l Phi_l
        gam[l + 1] = e[l] * wphi + h[l]
    wmPhi = e[m - 1] * g[m - 1] * gam[m]
    Em = prod(e[:m])
    Gam = [gam[l + 1] * prod(e[l + 1:m]) for l in range(m)]
    EL = [prod(e[:l]) for l in range(m + 1)]     # E_0..E_m
    qv = [None] + [h[l] * prod(e[l + 1:m]) for l in range(1, m)]
    P = [e[l] * g[l] for l in range(m)]
    WL = [Fraction(1, prod(P[l:m - 1])) for l in range(m)]     # W_l, W_{m-1}=1
    wl = [Fraction(1, prod(e[l:m - 1])) for l in range(m)]     # literal-e form
    return dict(m=m, e=e, h=h, g=g, gam=gam, wmPhi=wmPhi, Em=Em, Gam=Gam,
                EL=EL, qv=qv, P=P, WL=WL, wl=wl)

def gam_checks(E, FC, tag):
    m = E.m
    for l in range(1, m + 2):
        if E.gam.get(l) != FC["gam"][l]:
            viol("LAM-GAM", tag, f"gamma_{l}: engine {E.gam.get(l)} != "
                 f"fresh {FC['gam'][l]}")
    if E.wmPhi != FC["wmPhi"]:
        viol("LAM-GAM", tag, f"wmPhi {E.wmPhi} != fresh {FC['wmPhi']}")
    if E.Em != FC["Em"]:
        viol("LAM-GAM", tag, f"Em {E.Em} != fresh {FC['Em']}")
    if list(E.Gam) != FC["Gam"]:
        viol("LAM-GAM", tag, f"Gam {E.Gam} != fresh {FC['Gam']}")
    if [E.P[l] for l in range(m)] != FC["P"]:
        viol("LAM-GAM", tag, "P mismatch")
    wd_q = WD.q_quanta(E)
    if wd_q[1:] != FC["qv"][1:]:
        viol("LAM-GAM", tag, f"q quanta {wd_q} != fresh {FC['qv']}")
    note("gam_towers")

def fresh_line(E, FC, b, j):
    return FC["Em"] * w0(E.R, b) + sum(j[l] * FC["Gam"][l]
                                       for l in range(FC["m"]))

def micro_checks(FC, tag):
    """M-1 mixed-radix telescope, three weight families, exact Fractions."""
    m = FC["m"]
    for i in range(m):
        lhs = sum((FC["P"][l] - 1) * FC["WL"][l] for l in range(i))
        if lhs != FC["WL"][i] - FC["WL"][0]:
            viol("LAM-MICRO", tag, f"W-form telescope fails at i={i}")
        lhsE = sum((FC["e"][l] - 1) * FC["EL"][l] for l in range(i))
        if lhsE != FC["EL"][i] - 1:
            viol("LAM-MICRO", tag, f"E-form telescope fails at i={i}")
    lhsw = sum((FC["e"][l - 1] - 1) * FC["wl"][l - 1] for l in range(1, m))
    if lhsw != 1 - FC["wl"][0]:
        viol("LAM-MICRO", tag, "w-form telescope fails")
    note("micro_towers")

# ============================ the per-path replay =============================
def replay(FC, sig, jD, y2, hist, mut=None):
    """Fresh per-edge replay of the S1 quantum table's LEVEL BLOCK along the
    recorded edge list.  Returns dict(j, pi, exits, dmp, ccons, ncorr, ce, r).
    jD/y2 resolve the seed row (the hist 'seed' event carries only the
    level-0 add; the full d-cell vector rides the state).  mut='LAT'
    corrupts one Delta entry (level-0 promotion consumes P0 - 1)."""
    m = FC["m"]; P = FC["P"]; e = FC["e"]
    j = list(sig)
    pi = [0] * m          # pi[l] = promotion edges INTO level l (pi[0] = 0)
    exits = 0
    dmp = [0] * m
    ccons = [0] * m
    ncorr = [0] * m
    ce = []
    for ev in hist:
        if ev[0] == 'p0' or ev[0] == 'pi':
            i = 0 if ev[0] == 'p0' else ev[1]
            cons = P[i] - (1 if (mut == 'LAT' and i == 0) else 0)
            j[i] -= cons
            j[i + 1] += 1
            pi[i + 1] += 1
        elif ev[0] == 'exit':
            j[m - 1] -= P[m - 1]
            exits += 1
        elif ev[0] == 'c0':
            k, dj0 = ev[1], ev[2]
            j[0] -= P[0] - e[0] * k
            j[0] += dj0
            dmp[0] += dj0
            ccons[0] += P[0] - e[0] * k
            ncorr[0] += 1
            ce.append((0, k, (), dj0))
        elif ev[0] == 'ci':
            _, i, k, avec, dj0 = ev
            j[i] -= P[i] - e[i] * k
            for l in range(i):
                j[l] += avec[l]
                dmp[l] += avec[l]
            j[0] += dj0
            dmp[0] += dj0
            ccons[i] += P[i] - e[i] * k
            ncorr[i] += 1
            ce.append((i, k, tuple(avec), dj0))
        elif ev[0] == 'seed':
            for l in range(m):
                j[l] += jD[l]
            j[0] += y2
            dmp[0] += y2
    return dict(j=j, pi=pi, exits=exits, dmp=dmp, ccons=ccons,
                ncorr=ncorr, ce=ce, r=ncorr[m - 1])

# ============================== the five faces ================================
def check_faces(E, FC, ctx, st, stage, mut=None, fire=None):
    """All five faces on one terminal state.  stage in ('q1','q2').
    ctx = dict(tag,key,sig,base,su,u0,kdef,dmap,Dmap,lamhat).  When mut is
    set, a failed check increments fire[face] instead of recording a
    violation."""
    R = E.R; m = FC["m"]
    (sgn, b, j, pc, dmp, cons, ncorr, junk, jD, prin, ce, y2, hist) = st
    tag, key = ctx["tag"], ctx["key"]
    jDv = tuple(jD) if jD is not None else (0,) * m
    y2v = y2 if stage == 'q2' else 0
    rp = replay(FC, ctx["sig"], jDv, y2v, hist, mut=mut)

    def bad(face, detail):
        if mut is not None:
            fire[face] = fire.get(face, 0) + 1
        else:
            viol(face, tag, f"{detail} at {key}")

    # ---- LAM-LAT: the exact level-lattice telescope + counter cross-tie ----
    if list(j) != rp["j"]:
        bad("LAM-LAT", f"replayed j {rp['j']} != terminal {list(j)}")
    if mut is None:
        mypi = [pc[l - 1] if l >= 1 else 0 for l in range(m)]
        if rp["pi"][1:] != mypi[1:] or rp["exits"] != pc[m - 1]:
            bad("LAM-LAT", f"replayed pi/exits {rp['pi']},{rp['exits']} != "
                f"walk pc {list(pc)}")
        if rp["dmp"] != list(dmp):
            bad("LAM-LAT", f"replayed dmp {rp['dmp']} != walk {list(dmp)}")
        for l in range(m):
            want = rp["ccons"][l] + (rp["pi"][l + 1] * FC["P"][l]
                                     if l <= m - 2 else
                                     rp["exits"] * FC["P"][m - 1])
            if cons[l] != want:
                bad("LAM-LAT", f"cons[{l}]={cons[l]} != replay {want}")
        if list(ncorr) != rp["ncorr"]:
            bad("LAM-LAT", f"ncorr mismatch")
        if tuple(ce) != tuple(rp["ce"]):
            bad("LAM-LAT", f"ce mismatch")
        if sgn != (1 if len(ce) % 2 == 0 else -1):
            bad("LAM-LAT", f"sign {sgn} != (-1)^|CE|")
    pi = rp["pi"]

    # ---- face A (E-L1): pi_{m-1} == sum W_l (sig + jD + dmp - ccons - j) ----
    drop0 = 1 if mut == 'A' else 0
    rhs = sum(FC["WL"][l] * (ctx["sig"][l] + jDv[l] + rp["dmp"][l]
                             - rp["ccons"][l] - rp["j"][l])
              for l in range(drop0, m - 1))
    if Fraction(pi[m - 1]) != rhs:
        bad("LAM-A", f"E-L1 telescope: pi_top {pi[m-1]} != {rhs}")

    if stage == 'q1':
        return

    # ---- face B (SD-L2): the E-weighted mass ledger, any g0 ----
    EL = FC["EL"]
    M = lambda x: sum(x[l] * EL[l] for l in range(m))
    defcs = [( (FC["P"][i] - FC["e"][i] * k) * EL[i]
               - sum(av[l] * EL[l] for l in range(i)) - dj0,
               i, k, av, dj0) for (i, k, av, dj0) in rp["ce"]]
    exitmass = 2 * FC["P"][m - 1] * EL[m - 1] - (1 if mut == 'B' else 0)
    rhsB = (M(ctx["sig"]) + M(jDv) + y2v - exitmass
            - sum(pi[l] * (FC["P"][l - 1] * EL[l - 1] - EL[l])
                  for l in range(1, m))
            - sum(d for (d, *_ ) in defcs))
    if M(rp["j"]) != rhsB:
        bad("LAM-B", f"SD-L2 ledger: M(j)={M(rp['j'])} != {rhsB}")

    # ---- LAM-B1 (SD-L1) on all-g-1 rows ----
    if mut is None and ctx["allg1"]:
        for (d, i, k, av, dj0) in defcs:
            if d < EL[i + 1] - EL[i] + 1 - dj0 or d < 0:
                viol("LAM-B1", tag, f"SD-L1 bound breach: defc={d} at "
                     f"(i={i},Y={dj0}) at {key}")
            if d == 0:
                fulldump = all(av[l] == FC["P"][l] - 1 for l in range(i))
                if not (FC["e"][i] == 1 and dj0 == 1 and fulldump):
                    viol("LAM-B1", tag, f"defc=0 outside the SD-L1 equality "
                         f"shape at {key}")

    # ---- face C (W-D4): the top-indicator face ----
    su = ctx["su"]
    off = 1 if mut == 'C' else 0
    if pi[m - 1] != ctx["kdef"] + FC["e"][m - 1] * rp["r"] + rp["j"][m - 1] \
                    + (jDv[m - 1] - su[m]) + off:
        bad("LAM-C", f"W-D4 identity: pi_top={pi[m-1]} kdef={ctx['kdef']} "
            f"r={rp['r']} jtop={rp['j'][m-1]}")
    if mut is None:
        if E.g[m - 1] == 1 and jDv[m - 1] != su[m]:
            viol("LAM-C", tag, f"(H2) seed pin jD_top {jDv[m-1]} != "
                 f"s_m(u_m) {su[m]} at {key}")
        if jDv[m - 1] == su[m] and pi[m - 1] < ctx["kdef"]:
            viol("LAM-C", tag, f"threshold: pi_top {pi[m-1]} < kdef "
                 f"{ctx['kdef']} at {key}")

    # ---- face D (the (1;0) valuation face), every g0 ----
    wcD = w0(R, ctx["Dmap"][jDv])
    digs = []
    ok = True
    for (i, k, av, dj0) in rp["ce"]:
        dg = ctx["dmap"].get((i, k, av))
        if dg is None:
            bad("LAM-D", f"digit missing in dmap: ({i},{k},{av})")
            ok = False
            break
        digs.append(w0(R, dg))
    if ok:
        nY = y2v + sum(dj0 for (_, _, _, dj0) in rp["ce"])
        nX = junk - nY
        if nX < 0:
            bad("LAM-D", f"junk arithmetic: junk={junk} nY={nY}")
        floor = ctx["b0w"] + wcD + sum(digs) + max(nX, 0)
        wb = w0(R, b)
        if wb < floor:
            bad("LAM-D", f"pi-face breach: w0={wb} < floor {floor}")
        if junk == 0 and wb != floor + (1 if mut == 'D' else 0):
            bad("LAM-D", f"junk-free equality: w0={wb} != {floor}")

        # ---- face E (the line face) ----
        lam0 = ctx["lamhat"] + (1 if mut == 'E' else 0)
        lf = lam0 + sum(pi[l] * FC["qv"][l] for l in range(1, m))
        ln = fresh_line(E, FC, b, rp["j"])
        if mut is None and ln != E.line(b, j):
            viol("LAM-GAM", tag, f"fresh line {ln} != E.line at {key}")
        if junk == 0 and ln != lf:
            bad("LAM-E", f"junk-free line {ln} != {lf}")
        if ln < lf + max(nX, 0) * FC["Em"] + nY * FC["Gam"][0]:
            bad("LAM-E", f"line {ln} < floor+slack "
                f"{lf + max(nX,0)*FC['Em'] + nY*FC['Gam'][0]}")

        # ---- face R (residue face, junk-free) ----
        if junk == 0:
            T = E.grbT; K0 = T.K0
            exp = T.res_digit(pscal(R, R["pi_pow"](ctx["b0w"]),
                                    [R["one"]]), ctx["b0w"])
            exp = K0["mul"](exp, T.res_digit(ctx["Dmap"][jDv], wcD))
            for (i, k, av, dj0) in rp["ce"]:
                dg = ctx["dmap"][(i, k, av)]
                fr = T.res_digit(dg, w0(R, dg))
                if mut is None and K0["isz"](fr):
                    viol("LAM-R", tag, f"digit residue ZERO at {key}")
                exp = K0["mul"](exp, fr)
            if mut == 'R':
                exp = K0["add"](exp, K0["one"])
            got = T.res_digit(b, w0(R, b))
            if not K0["isz"](K0["add"](got, K0["neg"](exp))):
                bad("LAM-R", f"residue product law fails")
            elif mut is None:
                note("res_cells")
    if mut is None:
        note("cells")
        if junk == 0: note("cells_junkfree")

# ============================== one traced row ================================
def trace_row(E, FC, sA, sB, u1a, u1b, aA, aB, su, cs, Dd, kdef, key, prin,
              tag, u0, dmap, Dmap, rowrecs, mut=None, fire=None):
    R = E.R; m = E.m
    sig = tuple(sA[l + 1] + sB[l + 1] for l in range(m))
    b0 = pscal(R, R["pi_pow"](u1a + u1b), [R["one"]])
    prodp = pmul(R, aA, aB)
    z = (0,) * m
    init_rec = [(1, b0, sig, z, z, z, z, 0, None, False, (), 0, ())]
    q1_rec = []
    r = SK2.walk_rec(E, init_rec, q1_rec, tag)
    if r is None:
        harvest(tag); return None
    E1c, _ = pdivmod(R, prodp, E.Phis[m])
    if mut is None and WD.cellsum(E, q1_rec) != pnorm(R, E1c):
        viol("LAM-CONS", tag, f"stage-1 sum != E1IH at {key}")

    b0w = u1a + u1b          # w0 of the stage-1 seed coefficient (W-D1)
    what = b0w + u0          # S-L1's w-hat = u1 + u1' + u0
    lamhat = FC["Em"] * (u1a + u1b) + sum(sig[l] * FC["Gam"][l]
                                          for l in range(m)) \
             + FC["gam"][m + 1] - 2 * FC["wmPhi"]
    if mut is None:
        lam_eng = E.line(b0, sig) + E.gam[m + 1] - 2 * E.wmPhi
        if lamhat != lam_eng:
            viol("LAM-GAM", tag, f"fresh lamhat {lamhat} != engine "
                 f"{lam_eng} at {key}")
    allg1 = all(E.g[l] == 1 for l in range(m))
    a_, r_, b_, stock1 = WD.greedy_chains(E, sig, su, cs)
    stk = (stock1 >= E.P[m - 1])
    ctx = dict(tag=tag, key=key, sig=sig, b0w=b0w, su=su, u0=u0, kdef=kdef,
               dmap=dmap, Dmap=Dmap, lamhat=lamhat, allg1=allg1)

    # face A on the stage-1 exit cofactors
    for st in q1_rec:
        check_faces(E, FC, ctx, st, 'q1', mut=mut, fire=fire)

    # stage-2 seeding (the committed pattern)
    init2 = []
    for st in q1_rec:
        sgn, b, j, pc, dmp, cons, ncorr, junk, _, _, ce, _, hist = st
        for (cD, jD) in E.Dcells:
            Lc, Xc, Yc = E.digit_split(b, cD)
            js = tuple(j[l] + jD[l] for l in range(m))
            isp = (tuple(jD) == prin)
            for (cc, jtag, dj0) in ((Lc, 0, 0), (Xc, 1, 0), (Yc, 1, 1)):
                if not pnorm(R, cc): continue
                jj = list(js); jj[0] += dj0
                dd = list(dmp); dd[0] += dj0
                h2 = hist + (('seed', jD[0] + dj0),)
                init2.append((sgn, cc, tuple(jj), pc, tuple(dd), cons,
                              ncorr, junk + jtag, tuple(jD), isp, ce,
                              dj0, h2))
    q2_rec = []
    r = SK2.walk_rec(E, init2, q2_rec, tag)
    if r is None:
        harvest(tag); return None
    Q1c = pdivmod(R, pmul(R, E1c, E.Chat), E.Phis[m])[0]
    if mut is None and WD.cellsum(E, q2_rec) != pnorm(R, Q1c):
        viol("LAM-CONS", tag, f"stage-2 sum != Q1 at {key}")
    harvest(tag)

    for st in q2_rec:
        check_faces(E, FC, ctx, st, 'q2', mut=mut, fire=fire)

    if mut is not None:
        return dict(live=bool(q2_rec))

    # ---- LAM-POOL: the fresh carry chain, the E-L4 unroll, betahat ----
    tl = {l: sig[l - 1] + su[l] for l in range(1, m)}
    cf, cl_f, rho_f = 0, [], []
    for l in range(1, m):
        pool = tl[l] + cf
        cf = pool // E.e[l - 1]
        cl_f.append(cf)
        rho_f.append(pool - E.e[l - 1] * cf)
    if cl_f != list(cs):
        viol("LAM-POOL", tag, f"fresh carry chain {cl_f} != WS.pools_of "
             f"{list(cs)} at {key}")
    ctop = cl_f[-1] if cl_f else 0
    if Fraction(ctop) != sum((tl[l] - rho_f[l - 1]) * FC["wl"][l - 1]
                             for l in range(1, m)):
        viol("LAM-POOL", tag, f"E-L4 unroll identity fails at {key}")
    if sum(rho_f[l - 1] * FC["wl"][l - 1] for l in range(1, m)) > \
            1 - FC["wl"][0]:
        viol("LAM-POOL", tag, f"E-L4 remainder bound fails at {key}")

    live = (kdef <= ctop)
    ncomp = 0
    casc_state = "N/A"
    if q2_rec and allg1 and stk and live:
        casc = [st for st in q2_rec
                if st[10] == () and st[7] == 0 and st[11] == 0 and st[9]]
        if len(casc) > 1:
            viol("LAM-POOL", tag, f"cascade not unique at {key}: {len(casc)}")
        if casc:
            st = casc[0]
            bhat_pool = lamhat + sum(cl_f[l - 1] * FC["qv"][l]
                                     for l in range(1, m))
            ln = fresh_line(E, FC, st[1], st[2])
            if ln != bhat_pool:
                viol("LAM-POOL", tag, f"cascade line {ln} != betahat_pool "
                     f"{bhat_pool} at {key}")
            if w0(R, st[1]) != what:
                viol("LAM-POOL", tag, f"cascade w0 {w0(R, st[1])} != "
                     f"u1+u1'+u0 {what} at {key}")
            if E.Km["isz"](E.resKm(st[1])):
                viol("LAM-POOL", tag, f"cascade residue ZERO at {key}")
            note("casc_rows")
            casc_state = "PRESENT"
            # ---- LAM-BSTAR: (*) at the cascade slot ----
            jhat = tuple(rho_f) + (ctop - kdef,)
            EL = FC["EL"]
            for st2 in q2_rec:
                if tuple(st2[2]) != jhat: continue
                sd = sum((FC["P"][i] - FC["e"][i] * k) * EL[i]
                         - sum(av[l] * EL[l] for l in range(i)) - dj0
                         for (i, k, av, dj0) in st2[10])
                if sd != st2[11]:
                    viol("LAM-BSTAR", tag, f"(*) breach: sum defc {sd} != "
                         f"Y2 {st2[11]} at {key}")
                else:
                    note("star_cells")
                if st2 is not st and tuple(st2[2]) == jhat:
                    ncomp += 1
    rowrecs.append(dict(tower=tag, key=list(key), ncells=len(q2_rec),
                        live=live, allg1=allg1, stk=stk, casc=casc_state,
                        ncomp=ncomp))
    return dict(live=bool(q2_rec))

# ============================= tower drivers ==================================
def setup(spec, budget=900):
    tag, m, kind, p, d0, reads = spec
    E = PE.Eng(m, kind, p, d0, reads, tag)
    PE.prep(E)
    harvest(tag)
    u, su = WS.uchain(E)
    if u is None:
        raise RuntimeError("u-chain failed")
    Etot, G0, split = WS.window_split(E)
    anch = WS.anchors_of(E, Etot, G0, split)
    prin, meta = WD.inv_checks(E, u, su)
    harvest(tag)
    if meta is None:
        raise RuntimeError("inv_checks failed")
    dmap, Dmap = SK2.build_maps(E)
    FC = fresh_consts(E)
    gam_checks(E, FC, tag)
    micro_checks(FC, tag)
    return E, FC, su, Etot, G0, anch, prin, meta["u0"], dmap, Dmap

def run_tower(spec, mode, rowrecs, budget=900, mut=None, fire=None):
    """mode 'W' = the WMULTDCX battery pid-key selection (verbatim);
    mode 'SD' = the SURVDISJ fresh-tower live-row selection (caps 12/6);
    mode 'YJ' = the SDYJ live-clause selection (uncapped)."""
    tag, m, kind, p, d0, reads = spec
    t0 = time.time()
    def _alrm(s, f): raise TimeoutError("tower budget")
    old = signal.signal(signal.SIGALRM, _alrm)
    signal.alarm(budget)
    try:
        E, FC, su, Etot, G0, anch, prin, u0, dmap, Dmap = setup(spec)
        etop = E.e[m - 1]; R = E.R
        rows = []
        if mode == 'W':
            pid_keys = {}
            for ga in range(G0, G0 + Etot):
                aA, sA, u1a = anch[ga]
                for gb in range(G0, G0 + Etot):
                    aB, sB, u1b = anch[gb]
                    strack = (sA[m + 1] == E.e[m] - 1
                              and sB[m + 1] == E.e[m] - 1)
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
                    key = (tuple(sorted([(tuple(sA[l] for l in
                                                range(1, m + 2)), u1a),
                                         (tuple(sB[l] for l in
                                                range(1, m + 2)), u1b)])))
                    if key not in pid_keys:
                        kdef = 2 * etop - Dd
                        want = (meas or top in (2 * etop - 1, 2 * etop,
                                                2 * etop - 2)
                                or (len(cs) >= 2 and cs[0] > 0 and cs[1] > 0)
                                or (cs and max(cs) >= 2))
                        if want:
                            pid_keys[key] = (ga, gb, cs, Dd, kdef, meas,
                                             sA, sB, u1a, u1b)
            cap = 14 if m >= 4 else 40
            chosen = sorted(pid_keys.items(), key=lambda kv: (
                not kv[1][5], -(kv[1][2][0] if kv[1][2] else 0), kv[0]))[:cap]
            rows = [(key, v[0], v[1], v[2], v[3], v[4], v[6], v[7],
                     v[8], v[9]) for key, v in chosen]
        else:
            seen, live_pool = set(), {}
            for ga in range(G0, G0 + Etot):
                aA, sA, u1a = anch[ga]
                for gb in range(G0, G0 + Etot):
                    aB, sB, u1b = anch[gb]
                    if not (sA[m + 1] == E.e[m] - 1
                            and sB[m + 1] == E.e[m] - 1):
                        continue
                    E1, _ = pdivmod(R, pmul(R, aA, aB), E.Phis[m])
                    if not pnorm(R, E1): continue
                    key = (tuple(sorted([(tuple(sA[l] for l in
                                                range(1, m + 2)), u1a),
                                         (tuple(sB[l] for l in
                                                range(1, m + 2)), u1b)])))
                    if key in seen: continue
                    seen.add(key)
                    pools, cs, Dd, top = WS.pools_of(E, sA, sB, su)
                    ctop = cs[-1] if cs else 0
                    kdef = 2 * etop - Dd
                    if kdef > ctop: continue
                    live_pool.setdefault((kdef, ctop), []).append(
                        (key, ga, gb, cs, Dd, kdef, sA, sB, u1a, u1b))
            cap = (6 if m >= 4 else 12) if mode == 'SD' else 10**9
            for stratum in sorted(live_pool):
                rows.extend(live_pool[stratum][:cap])
        nl = 0
        for (key, ga, gb, cs, Dd, kdef, sA, sB, u1a, u1b) in rows:
            rr = trace_row(E, FC, sA, sB, u1a, u1b, anch[ga][0], anch[gb][0],
                           su, cs, Dd, kdef, key, prin, tag, u0, dmap, Dmap,
                           rowrecs, mut=mut, fire=fire)
            if rr and rr["live"]: nl += 1
        signal.alarm(0); signal.signal(signal.SIGALRM, old)
        if mut is None:
            print(f"-- [{mode}] {tag} m={m} {kind},p={p},d0={d0} "
                  f"g={E.g[:m]}: traced={len(rows)} nonempty={nl} "
                  f"({time.time()-t0:.1f}s)")
    except TimeoutError:
        signal.alarm(0); signal.signal(signal.SIGALRM, old)
        print(f"-- {tag}: TOWER BUDGET EXCEEDED ({budget}s) — disclosed skip")
        note("tower_budget_skips")
    except Exception as ex:
        signal.alarm(0); signal.signal(signal.SIGALRM, old)
        print(f"-- {tag}: ENGINE UNSUPPORTED ({ex!r}) — disclosed")
        note("tower_skipped")

# ========================= rosters (copied verbatim) ==========================
# survdisj_derive_checks.py PX_ROSTER + SD_ROSTER (committed, pinned):
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
# sdyj_checks_v2.py T3_COMMITTED + FRESH (committed, pinned):
T3_COMMITTED = [
    ("YJ2F",    2, "Fpt", 2, 2, [(2,1,1), (2,1,1), (2,1,1)]),
    ("YJ3F",    3, "Fpt", 2, 2, [(2,1,1), (2,1,1), (2,1,1), (2,1,1)]),
    ("YJ3FLT",  3, "Fpt", 2, 2, [(2,1,1), (1,1,1), (2,1,1), (2,1,1)]),
    ("YJ3FLTB", 3, "Fpt", 2, 2, [(2,3,1), (1,1,1), (2,1,1), (2,1,1)]),
    ("YJ3DPF",  3, "Fpt", 2, 2, [(3,1,1), (2,1,1), (2,1,1), (2,1,1)]),
    ("YJ4FLT",  4, "Fpt", 2, 2, [(2,1,1), (1,1,1), (2,1,1), (2,1,1), (2,1,1)]),
    ("YJ3Z",    3, "Zp",  2, 2, [(2,1,1), (1,1,1), (2,1,1), (2,1,1)]),
    ("YJ3F3",   3, "Fpt", 3, 2, [(2,1,1), (1,1,1), (2,1,1), (2,1,1)]),
    ("YJT1F",   3, "Fpt", 2, 2, [(2,1,1), (2,1,1), (2,1,1), (1,1,1)]),
]
FRESH = [
    ("YJX1", 3, "Fpt", 2, 2, [(2,3,1), (1,3,1), (2,1,1), (2,1,1)]),
    ("YJX2", 3, "Fpt", 3, 2, [(3,1,1), (1,1,1), (2,1,1), (2,1,1)]),
    ("YJX3", 3, "Fpt", 3, 2, [(3,2,1), (1,1,1), (2,1,1), (2,1,1)]),
    ("YJX4", 4, "Fpt", 2, 2, [(2,1,1), (1,1,1), (1,1,1), (2,1,1), (2,1,1)]),
    ("YJX5", 3, "Fpt", 2, 1, [(2,1,1), (1,1,1), (2,1,1), (2,1,1)]),
    ("YJX6", 2, "Fpt", 2, 2, [(2,1,1), (1,1,1), (2,1,1)]),
]
THROWAWAY = ("SHAKE", 2, "Fpt", 3, 2, [(2,1,1), (2,3,1), (2,1,1)])

MUT_ROSTER = [
    ("W3DEEP",  3, "Zp", 3, 1, [(3,2,1), (2,1,1), (2,1,1), (2,1,1)], 'W'),
    ("W3G2B",   3, "Zp", 3, 2, [(2,1,2), (3,2,1), (2,3,1), (2,1,1)], 'W'),
    ("YJ2F",    2, "Fpt", 2, 2, [(2,1,1), (2,1,1), (2,1,1)], 'YJ'),
]
MUTS = ['LAT', 'A', 'B', 'C', 'D', 'E', 'R']
MUT_FACE = {'LAT': 'LAM-LAT', 'A': 'LAM-A', 'B': 'LAM-B', 'C': 'LAM-C',
            'D': 'LAM-D', 'E': 'LAM-E', 'R': 'LAM-R'}

def mutation_battery():
    print("---- mutation controls (the CTRL-TEL0 genre) ----")
    fires = {}
    for mut in MUTS:
        fire = {}
        for spec7 in MUT_ROSTER:
            spec, mode = spec7[:6], spec7[6]
            run_tower(spec, mode, [], mut=mut, fire=fire)
        n = fire.get(MUT_FACE[mut], 0)
        fires[mut] = dict(fire)
        print(f"  MUT-{mut}: {MUT_FACE[mut]} fired {n} times "
              f"(all faces touched: {dict(fire)})")
        if n < 1:
            viol("LAM-MUT", f"MUT-{mut}", f"control NEVER fired on "
                 f"{MUT_FACE[mut]} — the face's evidence is toothless")
        else:
            note(f"mut_{mut}_fires", n)
    return fires

# ================================= main =======================================
def main():
    t0 = time.time()
    print("=" * 78)
    print("LEDGER-Lambda machine leg — " +
          ("SHAKEDOWN (throwaway only)" if SHAKE else "full sealed battery"))
    print("=" * 78)
    # the standing engine rule: install + re-run the agreement gate
    EXT.install()
    n = EXT.agreement_gate(full=not SHAKE)
    if n:
        viol("LAM-GATE", "gate", f"{n} agreement-gate violations")
    print(f"[{time.time()-t0:6.1f}s] LAM-GATE: {n} violations "
          f"(pairs={EXT.CNT.get('agr_tower_pairs',0)}, "
          f"irr={EXT.CNT.get('agr_irr_cases',0)}, "
          f"cert={EXT.CNT.get('agr_cert_cases',0)}, "
          f"pick={EXT.CNT.get('agr_pick_cases',0)})")
    harvest("gate")
    rowrecs = []
    if SHAKE:
        run_tower(THROWAWAY, 'YJ', rowrecs)
        for mut in MUTS:   # crash-freedom of the mutation path only
            fire = {}
            run_tower(THROWAWAY, 'YJ', [], mut=mut, fire=fire)
            print(f"  shakedown MUT-{mut}: fires {dict(fire)}")
    else:
        print("---- Phase W: the WMULTDCX battery selection ----")
        for spec in WS.ROSTER:
            run_tower(spec, 'W', rowrecs)
        print("---- Phase SD: the SURVDISJ rosters ----")
        for spec in PX_ROSTER + SD_ROSTER:
            run_tower(spec, 'SD', rowrecs)
        print("---- Phase YJ: the SDYJ rosters ----")
        for spec in T3_COMMITTED + FRESH:
            run_tower(spec, 'YJ', rowrecs)
        fires = mutation_battery()
    print("=" * 78)
    fams = ["LAM-PIN", "LAM-GATE", "LAM-GAM", "LAM-CONS", "LAM-LAT",
            "LAM-A", "LAM-B", "LAM-B1", "LAM-BSTAR", "LAM-C", "LAM-D",
            "LAM-E", "LAM-R", "LAM-POOL", "LAM-MICRO", "LAM-MUT", "HARNESS"]
    for f in fams:
        nf = sum(1 for v in VIOL if v[0] == f)
        print(f"{f:10s}: {nf} violations "
              f"[{'GREEN' if nf == 0 else 'RED'}]")
    print("-" * 78)
    nW = sum(1 for r in rowrecs if r['tower'].startswith(('W3', 'W4', 'XM')))
    print(f"rows traced: {len(rowrecs)} (phase W: {nW}; committed battery "
          f"selection: 412); Q1 cells: {CNT.get('cells',0)} "
          f"(junk-free {CNT.get('cells_junkfree',0)}); residue-face cells: "
          f"{CNT.get('res_cells',0)}; (*) cells: {CNT.get('star_cells',0)}; "
          f"cascade rows: {CNT.get('casc_rows',0)}")
    print("counters:", {k: CNT[k] for k in sorted(CNT)})
    print(f"total violations: {len(VIOL)}")
    el = time.time() - t0
    print(f"elapsed: {el:.1f}s")
    print(f"VERDICT: {'ALL GREEN' if not VIOL else 'RED — see above'}")
    if not SHAKE:
        out = dict(final=True, violations=VIOL, findings=FINDINGS,
                   counters=CNT, rows=rowrecs, mutation_fires=fires,
                   provenance=PINS, elapsed=el)
        with open(os.path.join(OUTDIR, "ledger_lambda_checks_results.json"),
                  "w") as f:
            json.dump(out, f, indent=1, default=str)
        print("results -> ledger_lambda_checks_results.json")
    return 0 if not VIOL else 1

if __name__ == "__main__":
    sys.exit(main())
