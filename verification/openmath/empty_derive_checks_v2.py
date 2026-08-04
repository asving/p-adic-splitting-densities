#!/usr/bin/env python3
"""empty_derive_checks_v2.py — (EMPTY-(m+1)) machine leg, VERSION 2 [E-r1 repair
unit, 2026-08-08 campaign].  v1 (empty_derive_checks.py, md5
8fed92402bcffe6e0c536f1f9d847612) is committed and NEVER MUTATED; this file is
v1 verbatim plus the EMPTY-PE1 Finding-3 repair (the CTRL-PAY1 teeth):

  NEW EDC-PAYINV  inventory-level E-L2 (pure form): for EVERY correction-table
                  entry (i, k, d-cell dump vector) of EVERY roster tower, and
                  every class-admissible Y-flag (y = 1 admissible iff d0 >= 2 —
                  at d0 = 1 the Phi0Y-child is absent, L-NORM(c)):
                      sum_{l<i} a_l W_l + y W_0  <=  (P_i - e_i k) W_i
                  (resp. <= 1 at i = m-1).  Predicted 0 violations (E-L2 is a
                  theorem of the inventory bounds).
  NEW CTRL-PAY2   the BROKEN-E-L2 variant (E-L2 tightened by W_0: "slack >= W_0
                  always") applied at the same inventory level.  This variant is
                  FALSE at the real slack-0 corner — i = m-1, FULL-HOUSE dump
                  vector (a_l = P_l - 1 for all l <= m-2), Y-child, d0 >= 2 —
                  which EMPTY-PE1 (EXT-PAY) showed is the ONLY in-scope sub-W_0
                  corner and is inventory-present on XM3B and EQ3G2A (both
                  d0 = 2, top d-cell a = (3,2)).  CTRL-PAY2 MUST FIRE there
                  (teeth: the detector logic demonstrably fires on real
                  committed tower data, not a synthetic parameter point); the
                  witness list must be EXACTLY that corner (checked).
  NEW SLACK-W0    the battery min-slack sharpness record: the measured minimum
                  E-L2 slack over all walked correction edges is compared to
                  W_0 of the attaining tower — EMPTY-PE1 found min slack
                  1/12 = W_0 (W3G2B, i=0, k=1, y=1) EXACTLY: the payment
                  inequality runs at ZERO margin above the CTRL-PAY1 threshold,
                  not "comfortably".  The first slack == W_0 edge is recorded.

Everything below the v2 marker comments is v1 verbatim (same walk, same 17
families, same rosters, same selection); v2 writes its own output/results
files and its own self-pin.  Original v1 docstring follows.

----------------------------------------------------------------------------
empty_derive_checks.py — (EMPTY-(m+1)) COMPOSER unit: the machine leg of
lean/notes/openmath/EMPTY_PROOF_2026-08-08.md.

Object (the S9 route display of WMULTDCX_2026-08-08.md):

    (EMPTY-(m+1)):  on TRACK, (H1)-(H2)(+H3 as proved), c_{m-1} < k  =>
    the two-stage tree T^2 has NO two-exit path at all.

The note proves this by a weighted path-ledger assembly:
  (E-L1) the exact P-weighted telescope of LED_l  (pi_{m-1} as an exact
         rational functional of seeds/dumps/corrections/terminal exponents);
  (E-L2) per-correction-edge dump payment (pure and hybrid charged forms);
  (E-L3) = W-D4 (consumed verbatim);
  (E-L4/5) the pool unroll c_{m-1} = R - sum rho_l w_{l-1} and the level-0
         integer-floor chain cplus with  cplus <= c (+1 only on the Y-tight
         stratum);
  (E-L6) Phi0Y-junk-child vanishing on monomial coefficients (canonical
         DIGIT-SPLIT Y = quo(bh*ch, Phi_0); deg < d0 => Y = 0);
  (E-THM) assembly: any two-exit path forces k <= c_{m-1}.

This runner machine-checks EVERY displayed intermediate on the sealed
battery's exact 412-row selection (roster wmultdcx_stress.ROSTER, selection
replicated VERBATIM from wmultdcx_derive_checks.run_tower) PLUS the frozen
fresh roster of the (EMPTY) instrument phase (empty_instrument_design.json,
md5 f4ff4a90603d3be90bf8c07df985a1b3; the instrument phase died before its
full run — files salvaged uncommitted->committed, disclosed in the note).
It re-implements the two-stage walk WITH PER-EDGE LOGGING (each correction
edge records (level, k, dump vector, Y-taken)) so the payment lemma is
checked edge by edge, not in aggregate; the walk consumes the committed
engine primitives (PE.Eng: corr_table, digit_split, cellpoly) byte-untouched.

VERDICT families (ALL predicted 0 violations):
  EDC-PIN     consumed committed runners match the note-pinned md5s.
  EDC-LED     LED_l identity at EVERY terminal state (stage-1 leaves,
              stage-1 exits, stage-2 leaves, two-exit cells), every level.
  EDC-TEL     (E-L1) exact Fraction telescope at every terminal:
              pi_{m-1} = sum_{l<=m-2} W_l*(sig_{l+1} + jD_l + dmp_l
                                           - ccons_l - j_l),
              W_l = 1/(P_l...P_{m-2}); ccons_l := cons_l - P_l*pc[l] >= 0.
  EDC-PAY     (E-L2 pure) per correction edge at level i <= m-2:
              sum_{l<i} a_l W_l + [Y] W_0  <=  (P_i - e_i k) W_i ;
              at i = m-1: dump value <= 1.
  EDC-PAYH    (E-L2 hybrid) per correction edge at level i >= 1:
              sum_{1<=l<i} a_l W_l + ceil((a_0+[Y])/P_0) * W_1
                 <= (P_i - e_i k) W_i   (i <= m-2)   resp.  <= 1 (i = m-1).
  EDC-FLOOR   level-0 integer floor at every terminal:
              pc[0] <= floor((sig_1 + jD_0 + dmp_0) / P_0).
  EDC-BND     assembled bound per two-exit cell:
              pi_{m-1} <= R_P + [Y2] W_0 + ncorr_{m-1}   (Fraction).
  EDC-HEAD    per two-exit cell: the W-D4 identity
              pi_{m-1} = k + e_{m-1} r + j_top  (top d-cell pin re-checked)
              AND THE THEOREM'S CONCLUSION  k <= c_{m-1}.
  EDC-EMPTY   law-dead traced row => ZERO two-exit terminals.
  EDC-Q1LAW   fresh-phase full census: Q^1 != 0 <=> D + c_{m-1} >= 2e_{m-1}
              on every TRACK key of every fresh tower (law countermodel guard).
  EDC-UNROLL  per all-g=1 row: c_{m-1} == R - sum rho_l w^e_{l-1} exactly
              (Fractions) and R <= c_{m-1} + 1 - w^e_0.
  EDC-CPLUS   per row: cplus(Y=0, worst t) <= c_{m-1}  and
              cplus(Y=1, worst t) <= c_{m-1} + 1, with the +1 exactly on the
              displayed tight-stratum arithmetic (E-L5).
  EDC-YMON    (E-L6) every digit_split with deg(b*c) < d0 has Y-child == 0;
              every stage-2 seed whose stage-1 prefix took no correction
              edge has deg(b) == 0 (monomial coefficient) AND Y-child == 0.
  EDC-INV     every d-cell top exponent == s_m(u_m) (the (H2) pin);
              interior d-cell exponents principal ((H3) pin, g0-free levels).
  EDC-CONS    both stage trees reassemble the canonical divisions per row.
  EDC-SEAL    sealed-phase replication: 412 rows, 858 cells, 126 dead rows.
  HARNESS     violations raised inside the consumed engines.

CENSUSES (measured, no prediction):
  TIGHT       rows on the Y-tight stratum (k = c_{m-1}+1, remainder-maximal
              chain, tight0 arithmetic): count, d0>=2 subset, cells found.
  Y2TAKEN     stage-2 Y-junk seed edges ever taken (per s1-corr count).
  YCNZ        digit_split calls with nonzero Y-child (where Y-children live).

CONTROLS (teeth: each must fire >= once, else CONTROL FAILURE disclosed):
  CTRL-PAY1   EDC-PAY tightened by W_0 must fail somewhere (payment is tight).
  CTRL-FLOOR1 some terminal attains the level-0 floor cap (> 0) exactly.
  CTRL-HEAD1  k <= c_{m-1} - 1 must fail on some live cell (the bound is sharp).
  CTRL-TEL0   the telescope with the l = 0 term dropped must fail somewhere.
  CTRL-Y      some digit_split yields a nonzero Y-child somewhere (the
              Y-detector detects; else the E-L6 leg is instance-untested).
  CTRL-TIGHT  some tight-stratum row occurs in the batteries (else the
              Y-corner is disclosed instance-unprobed).

Deterministic, exact integer/polynomial arithmetic, no sampling, no seed.
Usage: python3 empty_derive_checks_v2.py > empty_derive_checks_v2_output.txt
"""
import sys, os, time, json, hashlib
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import wmultdcx_stress as WS                    # read-only consumption
import wmultdcx_derive_checks as WD             # read-only consumption
import rmengine_pe_reimpl as PE                 # read-only consumption
from grb_order2_check import pnorm, padd, pneg, pmul, pscal, pdivmod

VIOL = []
CNT = {}
CTRL = {k: 0 for k in ("CTRL-PAY1", "CTRL-FLOOR1", "CTRL-HEAD1",
                       "CTRL-TEL0", "CTRL-Y", "CTRL-TIGHT",
                       "CTRL-PAY2")}                      # v2: inventory teeth
MINSLACK = [None]     # measured min of (pay - dumpvalue) over correction edges
MINSLACK_EDGE = [None]  # v2: the attaining edge + its own tower's W_0
SLACKW0_EDGE = [None]  # v2: first battery edge with slack == W_0 exactly
PAY2_WITNESS = []      # v2: CTRL-PAY2 firing witnesses (inventory corners)
TIGHT_WITNESS = []    # first few tight-stratum rows, displayed in the note
TREE_CAP = 500000

PINS = {   # the WMULTDCX S0 seals + the instrument design provenance
    "wmultdcx_stress.py":        "15315cca59c87e6c2001ea744c50aab5",
    "wmultdcx_derive_checks.py": "bea1a43d619a3c91a9a0b2f32c0920c0",
    "rmengine_pe_reimpl.py":     "103c1a9c99e2b4a3e8b63c93cbf87e25",
    "grb_order2_check.py":       "dab62713175363a7185211890019ae2f",
}

# the FROZEN fresh roster (= empty_instrument_design.json census towers,
# re-declared here; the design json is the roster-freeze disclosure)
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

def note(fam, n=1): CNT[fam] = CNT.get(fam, 0) + n
def viol(fam, tag, detail):
    VIOL.append((fam, tag, detail))
    print(f"VIOLATION [{fam}] {tag}: {detail}")

def prod(xs):
    r = 1
    for x in xs: r *= x
    return r

def pdeg(R, b):
    bb = pnorm(R, b)
    return len(bb) - 1          # -1 for the zero polynomial

def pe_guard(tag, n0):
    if len(PE.VIOL) > n0:
        for v in PE.VIOL[n0:]:
            viol("HARNESS", tag, f"engine violation: {v}")
    return len(PE.VIOL)

# ---------------- weights ----------------
def pweights(E):
    """W_l = 1/(P_l ... P_{m-2}) (P-divisor omegas), W_{m-1} = 1."""
    m = E.m
    W = [Fraction(1)] * m
    for l in range(m - 2, -1, -1):
        W[l] = W[l + 1] / E.P[l]
    return W

def eweights(E):
    """w^e_l = 1/(e_l ... e_{m-2}) (the law's literal-e omegas)."""
    m = E.m
    W = [Fraction(1)] * m
    for l in range(m - 2, -1, -1):
        W[l] = W[l + 1] / E.e[l]
    return W

# ---------------- the instrumented two-stage walk ----------------
# state: (sign, b, j, pc, dmp, cons, ncorr, junk, jD, prin, ce, y2)
#   pc[l]   = promotions taken OUT of level l (= pi_{l+1}); pc[m-1] = exits
#   ce      = tuple of correction-edge records (i, k, avec<i, tookY)
#   y2      = 1 iff the stage-2 seed edge was the Phi0Y-junk child
def split_checked(E, b, cd, tag, where):
    n0 = len(PE.VIOL)
    Lc, Xc, Yc = E.digit_split(b, cd)
    pe_guard(tag, n0)
    if pnorm(E.R, Yc):
        note("YCNZ"); CTRL["CTRL-Y"] += 1
        # (E-L6 canonical form) deg(b*c) < d0 would make this a violation
        if pdeg(E.R, pmul(E.R, b, cd)) < E.d0:
            viol("EDC-YMON", tag, f"deg(b*c) < d0 but Y-child nonzero at {where}")
    return Lc, Xc, Yc

def walk(E, cells, qsink, tag):
    R = E.R; m = E.m
    corr = E.corr_table()
    stack = list(cells)
    leaves = []
    nodes = 0
    while stack:
        st = stack.pop()
        sign, b, j, pc, dmp, cons, ncorr, junk, jD, prin, ce, y2 = st
        nodes += 1
        if nodes > TREE_CAP:
            viol("HARNESS", tag, "tree cap exceeded")
            return None, nodes
        i = next((l for l in range(m) if j[l] >= E.P[l]), None)
        if i is None:
            leaves.append(st)
            continue
        if i <= m - 2:
            j2 = list(j); j2[i] -= E.P[i]; j2[i + 1] += 1
            pc2 = list(pc); pc2[i] += 1
            cn2 = list(cons); cn2[i] += E.P[i]
            stack.append((sign, b, tuple(j2), tuple(pc2), dmp, tuple(cn2),
                          ncorr, junk, jD, prin, ce, y2))
        else:
            j2 = list(j); j2[m - 1] -= E.P[m - 1]
            pc2 = list(pc); pc2[m - 1] += 1
            cn2 = list(cons); cn2[m - 1] += E.P[m - 1]
            qsink.append((sign, b, tuple(j2), tuple(pc2), dmp, tuple(cn2),
                          ncorr, junk, jD, prin, ce, y2))
        for (k, dcells) in corr[i]:
            base = list(j); base[i] -= E.P[i] - E.e[i] * k
            cn2 = list(cons); cn2[i] += E.P[i] - E.e[i] * k
            nc2 = list(ncorr); nc2[i] += 1
            for (cd, av) in dcells:
                Lc, Xc, Yc = split_checked(E, b, cd, tag, f"corr(i={i},k={k})")
                nj = list(base); nd = list(dmp)
                for l in range(min(i, len(av))):
                    nj[l] += av[l]; nd[l] += av[l]
                avec = tuple((av[l] if l < len(av) else 0) for l in range(i))
                for (cc, jtag, dj0) in ((Lc, 0, 0), (Xc, 1, 0), (Yc, 1, 1)):
                    if not pnorm(R, cc): continue
                    jj = list(nj); jj[0] += dj0
                    dd = list(nd); dd[0] += dj0
                    ce2 = ce + ((i, k, avec, dj0),)
                    stack.append((-sign, cc, tuple(jj), pc, tuple(dd),
                                  tuple(cn2), tuple(nc2), junk + jtag,
                                  jD, prin, ce2, y2))
    return leaves, nodes

# ---------------- per-terminal checks ----------------
def check_terminal(E, st, sig, su, cs, kdef, key, cls, W, tag):
    R = E.R; m = E.m
    sign, b, j, pc, dmp, cons, ncorr, junk, jD, prin, ce, y2 = st
    jDv = jD if jD is not None else (0,) * m
    note("terminals")
    # EDC-LED: the LED_l identity, every level
    for l in range(m):
        pin = pc[l - 1] if l >= 1 else 0
        if j[l] != sig[l] + jDv[l] + pin + dmp[l] - cons[l]:
            viol("EDC-LED", tag,
                 f"{cls} ledger fails level {l} key={key}: j={j} sig={sig} "
                 f"jD={jDv} pc={pc} dmp={dmp} cons={cons}")
            return
    # EDC-TEL: the exact telescope (E-L1)
    tel = Fraction(0); tel0 = Fraction(0)
    ok = True
    for l in range(m - 1):
        cc = cons[l] - E.P[l] * pc[l]
        if cc < 0:
            viol("EDC-TEL", tag, f"{cls} ccons_{l} < 0 at {key}"); ok = False
        term = W[l] * (sig[l] + jDv[l] + dmp[l] - cc - j[l])
        tel += term
        if l >= 1: tel0 += term
    if ok and tel != pc[m - 2]:
        viol("EDC-TEL", tag,
             f"{cls} telescope != pi_top at {key}: {tel} vs {pc[m-2]}")
    if ok and tel0 != pc[m - 2]:
        CTRL["CTRL-TEL0"] += 1
    # EDC-PAY / EDC-PAYH per correction edge (E-L2)
    for (i, k, avec, ty) in ce:
        note("edges")
        pay = (E.P[i] - E.e[i] * k) * W[i] if i <= m - 2 else Fraction(1)
        lhs = sum(avec[l] * W[l] for l in range(min(i, len(avec)))) + ty * W[0]
        if MINSLACK[0] is None or pay - lhs < MINSLACK[0]:
            MINSLACK[0] = pay - lhs
            MINSLACK_EDGE[0] = dict(tower=tag, i=i, k=k, avec=list(avec),
                                    y=ty, slack=str(pay - lhs), W0=str(W[0]))
        if pay - lhs == W[0] and SLACKW0_EDGE[0] is None:   # v2: SLACK-W0
            SLACKW0_EDGE[0] = dict(tower=tag, i=i, k=k, avec=list(avec),
                                   y=ty, W0=str(W[0]))
        if lhs > pay:
            viol("EDC-PAY", tag,
                 f"{cls} edge (i={i},k={k},a={avec},Y={ty}) dump {lhs} > pay {pay} at {key}")
        if lhs > pay - W[0]:
            CTRL["CTRL-PAY1"] += 1
        if i >= 1:
            a0 = avec[0] if len(avec) >= 1 else 0
            ch0 = -((-(a0 + ty)) // E.P[0])          # ceil((a0+Y)/P0)
            W1 = W[1] if m >= 3 else Fraction(1)
            lhsh = sum(avec[l] * W[l] for l in range(1, min(i, len(avec)))) \
                   + ch0 * W1
            if lhsh > pay:
                viol("EDC-PAYH", tag,
                     f"{cls} hybrid edge (i={i},k={k}) charge {lhsh} > pay {pay} at {key}")
    # EDC-FLOOR: the level-0 integer floor
    cap0 = (sig[0] + jDv[0] + dmp[0]) // E.P[0]
    if pc[0] > cap0:
        viol("EDC-FLOOR", tag,
             f"{cls} pc0={pc[0]} > floor cap {cap0} at {key}")
    if pc[0] == cap0 and cap0 > 0:
        CTRL["CTRL-FLOOR1"] += 1
    # two-exit cells: EDC-HEAD + EDC-BND
    if cls == "cell":
        if pc[m - 1] != 2:
            viol("EDC-HEAD", tag, f"cell with {pc[m-1]} exits at {key}")
        etop = E.e[m - 1]
        if pc[m - 2] != kdef + etop * ncorr[m - 1] + j[m - 1] + (jDv[m - 1] - su[m]):
            viol("EDC-HEAD", tag,
                 f"W-D4 identity fails at {key}: pi={pc[m-2]} kdef={kdef} "
                 f"r={ncorr[m-1]} jtop={j[m-1]}")
        ctop = cs[-1] if cs else 0
        if kdef > ctop:
            viol("EDC-HEAD", tag,
                 f"THEOREM BREACH: cell on dead row at {key}: kdef={kdef} > c={ctop}")
        if kdef > ctop - 1:
            CTRL["CTRL-HEAD1"] += 1
        RP = sum(W[l] * (sig[l] + jDv[l]) for l in range(m - 1))
        if pc[m - 2] > RP + y2 * W[0] + ncorr[m - 1]:
            viol("EDC-BND", tag,
                 f"assembled bound fails at {key}: pi={pc[m-2]} > "
                 f"{RP} + {y2}*W0 + {ncorr[m-1]}")
        note("cells")

# ---------------- row-level arithmetic checks ----------------
def row_arith(E, sig1, su, cs, kdef, tag, key):
    """EDC-UNROLL (all-g=1), EDC-CPLUS + tight-stratum arithmetic (E-L4/E-L5).
    sig1[l] = sigma_{l+1} (0-indexed);  t_l := sigma_l + s_l(u_l)."""
    m = E.m
    t = [None] + [sig1[l - 1] + su[l] for l in range(1, m)]     # t_1..t_{m-1}
    allg1 = all(E.g[l] == 1 for l in range(m))
    we = eweights(E)
    ctop = cs[-1] if cs else 0
    if allg1:
        Rr = sum(t[l] * we[l - 1] for l in range(1, m))
        rho = []
        c = 0
        for l in range(1, m):
            rho.append((t[l] + c) % E.e[l - 1])
            c = (t[l] + c) // E.e[l - 1]
        un = Rr - sum(rho[l - 1] * we[l - 1] for l in range(1, m))
        if un != ctop:
            viol("EDC-UNROLL", tag, f"unroll fails at {key}: {un} != {ctop}")
        if Rr > ctop + 1 - we[0]:
            viol("EDC-UNROLL", tag, f"R > c+1-w0 at {key}: {Rr} vs {ctop}")
    # cplus chains (worst-case d-cell t = g0-1), Y in {0,1}
    res = {}
    for Y in (0, 1):
        cp = (t[1] + (E.g[0] - 1) * E.e[0] + Y) // E.P[0]
        for l in range(2, m):
            cp = (t[l] + cp) // E.e[l - 1]
        res[Y] = cp
        if Y == 0 and cp > ctop:
            viol("EDC-CPLUS", tag, f"cplus(Y=0)={cp} > c={ctop} at {key}")
        if Y == 1 and cp > ctop + 1:
            viol("EDC-CPLUS", tag, f"cplus(Y=1)={cp} > c+1={ctop+1} at {key}")
    # the tight-stratum arithmetic (E-L5): +1 iff tight0 and max remainders
    if E.g[0] == 1:
        tight0 = (t[1] % E.e[0] == E.e[0] - 1)
    else:
        tight0 = (t[1] == E.e[0] - 1)           # q = 0 and s = e0 - 1
    c = ((t[1] + (E.g[0] - 1) * E.e[0] + 1) // E.P[0]) if tight0 else None
    tight = tight0
    if tight0:
        cc = t[1] // E.e[0]
        for l in range(2, m):
            if (t[l] + cc) % E.e[l - 1] != E.e[l - 1] - 1:
                tight = False; break
            cc = (t[l] + cc) // E.e[l - 1]
    tight = bool(tight and kdef == ctop + 1)
    if (res[1] == ctop + 1) != bool(tight0 and res[1] == ctop + 1):
        pass  # tautology guard; the classifying check is below
    if res[1] > res[0] and not tight0:
        viol("EDC-CPLUS", tag,
             f"Y-unit crossed the level-0 floor off tight0 at {key}")
    if tight:
        CTRL["CTRL-TIGHT"] += 1
        note("TIGHT")
        if len(TIGHT_WITNESS) < 8:
            TIGHT_WITNESS.append(dict(tag=tag, key=str(key), kdef=kdef,
                                      cs=list(cs), d0=E.d0, g0=E.g[0]))
    return tight

# ---------------- one row, full trace ----------------
def trace_row(E, sA, sB, u1a, u1b, aA, aB, su, cs, D, kdef, live, key,
              prin, W, recs, tag):
    R = E.R; m = E.m
    sig = tuple(sA[l + 1] + sB[l + 1] for l in range(m))
    b0 = pscal(R, R["pi_pow"](u1a + u1b), [R["one"]])
    prodp = pmul(R, aA, aB)
    if pnorm(R, padd(R, prodp, pneg(R, E.cellpoly(b0, sig)))):
        viol("HARNESS", tag, f"a*a' != formal cell at {key}"); return
    z = (0,) * m
    init = [(1, b0, sig, z, z, z, z, 0, None, False, (), 0)]
    q1sink = []
    out = walk(E, init, q1sink, tag)
    if out[0] is None: return
    leaves1, _ = out
    E1c, E0c = pdivmod(R, prodp, E.Phis[m])
    if WD.cellsum(E, q1sink) != pnorm(R, E1c):
        viol("EDC-CONS", tag, f"stage-1 exit sum != E1IH at {key}")
    if WD.cellsum(E, leaves1) != pnorm(R, E0c):
        viol("EDC-CONS", tag, f"stage-1 leaf sum != rem at {key}")
    # stage-2 seeding (L-NORM split of b_Y * c_D), with the E-L6 checks
    init2 = []
    for st in q1sink:
        sgn, b, j, pc, dmp, cons, ncorr, junk, _, _, ce, _ = st
        s1c = sum(ncorr)
        for (cD, jD) in E.Dcells:
            # EDC-INV: the (H2)/(H3) d-cell pins
            if jD[m - 1] != su[m]:
                viol("EDC-INV", tag, f"d-cell top exponent {jD[m-1]} != s_m(u_m)={su[m]}")
            for l in range(1, m - 1):
                if jD[l] != su[l + 1]:
                    viol("EDC-INV", tag,
                         f"d-cell interior exponent j_{l}={jD[l]} != {su[l+1]} at {key}")
            tt = jD[0] - su[1]      # W-D2(iii)/(iv): j_0(D) = s_1(u_1) + t*e_0
            if tt < 0 or tt % E.e[0] != 0 or tt // E.e[0] >= E.g[0]:
                viol("EDC-INV", tag,
                     f"d-cell level-0 exponent j_0={jD[0]} not of the "
                     f"(iv)-form s_1(u_1)+t*e_0, 0<=t<g_0 at {key}")
            Lc, Xc, Yc = split_checked(E, b, cD, tag, f"seed@{key}")
            if s1c == 0:
                if pdeg(R, b) != 0:
                    viol("EDC-YMON", tag,
                         f"s1-corr-free exit cofactor with deg(b)={pdeg(R,b)} at {key}")
                if pnorm(R, Yc):
                    viol("EDC-YMON", tag,
                         f"s1-corr-free seed has NONZERO Y-child at {key} "
                         f"(the E-L6 kill fails here)")
            js = tuple(j[l] + jD[l] for l in range(m))
            isp = (tuple(jD) == prin)
            for (cc, jtag, dj0) in ((Lc, 0, 0), (Xc, 1, 0), (Yc, 1, 1)):
                if not pnorm(R, cc): continue
                if dj0 == 1:
                    note("Y2TAKEN"); note(f"Y2TAKEN_s1c{min(s1c,1)}")
                jj = list(js); jj[0] += dj0
                dd = list(dmp); dd[0] += dj0
                init2.append((sgn, cc, tuple(jj), pc, tuple(dd), cons,
                              ncorr, junk + jtag, tuple(jD), isp, ce, dj0))
    q2sink = []
    out2 = walk(E, init2, q2sink, tag)
    if out2[0] is None: return
    leaves2, _ = out2
    Q1c, R1c = pdivmod(R, pmul(R, E1c, E.Chat), E.Phis[m])
    if WD.cellsum(E, q2sink) != pnorm(R, Q1c):
        viol("EDC-CONS", tag, f"stage-2 exit sum != Q1 at {key}")
    if WD.cellsum(E, leaves2) != pnorm(R, R1c):
        viol("EDC-CONS", tag, f"stage-2 leaf sum != rem at {key}")
    # per-terminal checks, all four classes
    for st in leaves1:
        check_terminal(E, st, sig, su, cs, kdef, key, "leaf1", W, tag)
    for st in q1sink:
        check_terminal(E, st, sig, su, cs, kdef, key, "exit1", W, tag)
    for st in leaves2:
        check_terminal(E, st, sig, su, cs, kdef, key, "leaf2", W, tag)
    for st in q2sink:
        check_terminal(E, st, sig, su, cs, kdef, key, "cell", W, tag)
    ctop = cs[-1] if cs else 0
    lawdead = kdef > ctop
    if lawdead and len(q2sink) > 0:
        viol("EDC-EMPTY", tag,
             f"law-dead row with {len(q2sink)} two-exit terminals at {key}")
    if lawdead: note("dead_traced")
    tight = row_arith(E, sig, su, cs, kdef, tag, key)
    recs.append(dict(key=list(key) if isinstance(key, tuple) else key,
                     cs=list(cs), D=D, kdef=kdef, live=bool(live),
                     ncells=len(q2sink), tight=bool(tight),
                     nleaf1=len(leaves1), nexit1=len(q1sink),
                     nleaf2=len(leaves2)))
    if tight:
        note("TIGHT_d0ge2" if E.d0 >= 2 else "TIGHT_d01")

# ---------------- sealed phase: the 412-row selection, VERBATIM ----------------
def run_sealed_tower(spec, results):
    tag, m, kind, p, d0, reads = spec
    t0 = time.time()
    n0 = len(PE.VIOL)
    E = PE.Eng(m, kind, p, d0, reads, tag)
    PE.prep(E)
    pe_guard(tag, n0)
    u, su = WS.uchain(E)
    if u is None:
        viol("HARNESS", tag, "u-chain failed"); return
    Etot, G0, split = WS.window_split(E)
    anch = WS.anchors_of(E, Etot, G0, split)
    etop = E.e[m - 1]
    prin, _ = WD.inv_checks(E, u, su)
    W = pweights(E)
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
                  cs, Dd, kdef, meas, (ga, gb), prin, W, recs, tag)
    print(f"-- SEALED {tag} m={m} {kind},p={p},d0={d0} g={E.g[:m]}: "
          f"traced={len(recs)} cells={sum(r['ncells'] for r in recs)} "
          f"dead={sum(1 for r in recs if r['kdef'] > (r['cs'][-1] if r['cs'] else 0))} "
          f"({time.time()-t0:.1f}s)")
    results.append(dict(phase="sealed", tag=tag, m=m, kind=kind, p=p, d0=d0,
                        reads=reads, rows=recs))

# ---------------- fresh phase: dead-row tracing + full law census ----------------
def run_fresh_tower(spec, results):
    tag, m, kind, p, d0, reads = spec
    t0 = time.time()
    n0 = len(PE.VIOL)
    E = PE.Eng(m, kind, p, d0, reads, tag)
    PE.prep(E)
    pe_guard(tag, n0)
    u, su = WS.uchain(E)
    if u is None:
        viol("HARNESS", tag, "u-chain failed"); return
    Etot, G0, split = WS.window_split(E)
    anch = WS.anchors_of(E, Etot, G0, split)
    etop = E.e[m - 1]
    prin, _ = WD.inv_checks(E, u, su)
    W = pweights(E)
    R = E.R
    seen = set()
    dead_pool = {}
    live_pool = []
    ncensus = 0
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
            lawlive = (Dd + ctop >= 2 * etop)
            Q1 = pdivmod(R, pmul(R, E1, E.Chat), E.Phis[m])[0]
            meas = bool(pnorm(R, Q1))
            ncensus += 1
            if meas != lawlive:
                viol("EDC-Q1LAW", tag,
                     f"LAW breach at {key}: Q1{'!=' if meas else '=='}0 vs "
                     f"D+c={Dd}+{ctop} vs 2e={2*etop}")
            row = (ga, gb, cs, Dd, kdef, meas, sA, sB, u1a, u1b)
            if not meas:
                dead_pool.setdefault((kdef, ctop), []).append(row)
            elif len(live_pool) < 3:
                live_pool.append(row)
    cap = 10 if m >= 4 else 24
    recs = []
    for stratum in sorted(dead_pool):
        for row in dead_pool[stratum][:cap]:
            ga, gb, cs, Dd, kdef, meas, sA, sB, u1a, u1b = row
            trace_row(E, sA, sB, u1a, u1b, anch[ga][0], anch[gb][0], su,
                      cs, Dd, kdef, meas, (ga, gb), prin, W, recs, tag)
    for row in live_pool:
        ga, gb, cs, Dd, kdef, meas, sA, sB, u1a, u1b = row
        trace_row(E, sA, sB, u1a, u1b, anch[ga][0], anch[gb][0], su,
                  cs, Dd, kdef, meas, (ga, gb), prin, W, recs, tag)
    ndead = sum(len(v) for v in dead_pool.values())
    print(f"-- FRESH {tag} m={m} {kind},p={p},d0={d0} g={E.g[:m]}: census={ncensus} "
          f"dead={ndead} traced={len(recs)} "
          f"cells={sum(r['ncells'] for r in recs)} ({time.time()-t0:.1f}s)")
    results.append(dict(phase="fresh", tag=tag, m=m, kind=kind, p=p, d0=d0,
                        reads=reads, census=ncensus, dead_total=ndead,
                        dead_strata={str(k): len(v) for k, v in sorted(dead_pool.items())},
                        rows=recs))

# ---------------- v2: EDC-PAYINV + CTRL-PAY2 (the CTRL-PAY1 teeth) ----------------
def pay_inventory_teeth():
    """Inventory-level E-L2 over EVERY correction-table entry of EVERY roster
    tower (WS.ROSTER + FRESH_ROSTER), both class-admissible Y-flags.

    EDC-PAYINV: the TRUE lemma (dump value <= payment) — predicted 0 violations.
    CTRL-PAY2:  the BROKEN variant (dump value <= payment - W_0, i.e. 'slack is
    always >= W_0') — must FIRE; every firing must be the top-full-house-Y
    corner at d0 >= 2 (the only in-scope sub-W_0 corner, per EMPTY-PE1 EXT-PAY),
    else EDC-PAYINV records a corner-classification violation."""
    n_entries = 0
    fired_towers = set()
    for spec in list(WS.ROSTER) + list(FRESH_ROSTER):
        tag, m, kind, p, d0, reads = spec
        n0 = len(PE.VIOL)
        E = PE.Eng(m, kind, p, d0, reads, tag)
        PE.prep(E)
        pe_guard(tag, n0)
        W = pweights(E)
        corr = E.corr_table()
        yflags = (0, 1) if E.d0 >= 2 else (0,)   # L-NORM(c): no Y-child at d0=1
        for i in range(m):
            for (k, dcells) in corr[i]:
                for (cd, av) in dcells:
                    avec = tuple((av[l] if l < len(av) else 0) for l in range(i))
                    for y in yflags:
                        n_entries += 1
                        pay = (E.P[i] - E.e[i] * k) * W[i] if i <= m - 2 \
                            else Fraction(1)
                        lhs = sum(avec[l] * W[l]
                                  for l in range(min(i, len(avec)))) + y * W[0]
                        if lhs > pay:
                            viol("EDC-PAYINV", tag,
                                 f"inventory E-L2 breach (i={i},k={k},a={avec},"
                                 f"Y={y}): dump {lhs} > pay {pay}")
                        if lhs > pay - W[0]:          # the BROKEN variant fires
                            CTRL["CTRL-PAY2"] += 1
                            fired_towers.add(tag)
                            fullhouse = (i == m - 1 and
                                         all(avec[l] == E.P[l] - 1
                                             for l in range(m - 1)))
                            if not (fullhouse and y == 1 and E.d0 >= 2):
                                viol("EDC-PAYINV", tag,
                                     f"CTRL-PAY2 fired OFF the predicted corner:"
                                     f" (i={i},k={k},a={avec},Y={y},d0={E.d0}) "
                                     f"slack={pay - lhs}")
                            if len(PAY2_WITNESS) < 8:
                                PAY2_WITNESS.append(dict(
                                    tower=tag, d0=E.d0, i=i, k=k,
                                    avec=list(avec), y=y,
                                    slack=str(pay - lhs), W0=str(W[0])))
    print(f"EDC-PAYINV: {n_entries} inventory entries (all towers, all "
          f"correction-table d-cells, class-admissible Y-flags)")
    print(f"CTRL-PAY2 (broken E-L2, slack < W_0 detector): fired "
          f"{CTRL['CTRL-PAY2']} times on towers {sorted(fired_towers)}; "
          f"witnesses: {json.dumps(PAY2_WITNESS)}")
    return n_entries


# ---------------- main ----------------
def main():
    t0 = time.time()
    prov = {}
    for fn, want in PINS.items():
        got = hashlib.md5(open(os.path.join(HERE, fn), "rb").read()).hexdigest()
        prov[fn] = got
        if got != want:
            viol("EDC-PIN", fn, f"md5 {got} != pinned {want}")
    prov["empty_derive_checks_v2.py"] = hashlib.md5(
        open(os.path.abspath(__file__), "rb").read()).hexdigest()
    prov["empty_derive_checks.py (v1, unmutated)"] = hashlib.md5(
        open(os.path.join(HERE, "empty_derive_checks.py"), "rb").read()
    ).hexdigest()
    results = []
    print("=" * 78)
    print("(EMPTY-(m+1)) derive checks — SEALED phase (the 412-row selection)")
    print("=" * 78)
    for spec in WS.ROSTER:
        run_sealed_tower(spec, results)
    sealed_rows = sum(len(r["rows"]) for r in results)
    sealed_cells = sum(x["ncells"] for r in results for x in r["rows"])
    sealed_dead = sum(1 for r in results for x in r["rows"]
                      if x["kdef"] > (x["cs"][-1] if x["cs"] else 0))
    if (sealed_rows, sealed_cells, sealed_dead) != (412, 858, 126):
        viol("EDC-SEAL", "roster",
             f"selection replication failed: rows={sealed_rows} "
             f"cells={sealed_cells} dead={sealed_dead} (want 412/858/126)")
    print(f"SEALED phase: rows={sealed_rows} cells={sealed_cells} dead={sealed_dead}")
    print("=" * 78)
    print("(EMPTY-(m+1)) derive checks — FRESH phase (the frozen EQ roster)")
    print("=" * 78)
    for spec in FRESH_ROSTER:
        run_fresh_tower(spec, results)
    print("=" * 78)
    print("(EMPTY-(m+1)) derive checks v2 — INVENTORY phase (EDC-PAYINV + "
          "CTRL-PAY2 teeth)")
    print("=" * 78)
    n_inv = pay_inventory_teeth()
    print("=" * 78)
    fams = ["EDC-PIN", "EDC-LED", "EDC-TEL", "EDC-PAY", "EDC-PAYH", "EDC-FLOOR",
            "EDC-BND", "EDC-HEAD", "EDC-EMPTY", "EDC-Q1LAW", "EDC-UNROLL",
            "EDC-CPLUS", "EDC-YMON", "EDC-INV", "EDC-CONS", "EDC-SEAL",
            "EDC-PAYINV", "HARNESS"]
    nv = {f: sum(1 for v in VIOL if v[0] == f) for f in fams}
    for f in fams:
        print(f"{f:12s}: {nv[f]} violations")
    print("-" * 78)
    print("counters:", json.dumps(CNT, sort_keys=True))
    print("controls:", json.dumps(CTRL, sort_keys=True))
    ctrl_fail = [k for k, v in CTRL.items() if v == 0]
    if ctrl_fail:
        print(f"CONTROL FAILURE (disclosed, does not color the verdict lines): "
              f"{ctrl_fail}")
    dead_traced = CNT.get("dead_traced", 0)
    print(f"dead rows traced (EMPTY census population): {dead_traced}")
    print(f"min payment slack over {CNT.get('edges',0)} correction edges: "
          f"{MINSLACK[0]} (CTRL-PAY1 fires iff < W_0)")
    me = MINSLACK_EDGE[0]
    sharp = (me is not None and str(MINSLACK[0]) == me["W0"])
    print(f"SLACK-W0 sharpness: global min-slack edge {json.dumps(me)} — "
          f"min slack {MINSLACK[0]} == the attaining tower's own W_0: {sharp} "
          f"(SHARP: zero margin above the CTRL-PAY1 threshold, not headroom)")
    print(f"  (first edge at exactly its tower's W_0: "
          f"{json.dumps(SLACKW0_EDGE[0])})")
    print(f"tight-stratum witnesses (first {len(TIGHT_WITNESS)}): "
          f"{json.dumps(TIGHT_WITNESS)}")
    print(f"total violations: {len(VIOL)}")
    print(f"elapsed: {time.time()-t0:.1f}s")
    out = dict(violations=VIOL, counters=CNT, controls=CTRL,
               sealed=dict(rows=sealed_rows, cells=sealed_cells,
                           dead=sealed_dead),
               dead_traced=dead_traced,
               towers=[dict(r, rows=len(r["rows"])) for r in results],
               rows=[x for r in results for x in
                     [dict(tower=r["tag"], phase=r["phase"], **row)
                      for row in r["rows"]]],
               min_pay_slack=str(MINSLACK[0]), tight_witnesses=TIGHT_WITNESS,
               min_slack_edge=MINSLACK_EDGE[0], min_slack_sharp=sharp,
               slack_w0_edge=SLACKW0_EDGE[0],
               pay_inventory=dict(entries=n_inv, pay2_fired=CTRL["CTRL-PAY2"],
                                  pay2_witnesses=PAY2_WITNESS),
               provenance=prov, elapsed=time.time() - t0)
    with open(os.path.join(HERE, "empty_derive_checks_v2_results.json"), "w") as f:
        json.dump(out, f, indent=1, default=str)
    print("results -> empty_derive_checks_v2_results.json")

if __name__ == "__main__":
    main()
