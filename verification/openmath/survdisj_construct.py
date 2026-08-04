#!/usr/bin/env python3
"""survdisj_construct.py — (SURV-DISJ) DOUBLE-KILL CONSTRUCTION unit
(2026-08-08 campaign; the first do-not-sweep/CONSTRUCT unit, ledger 1d40751).

Machine leg of lean/notes/openmath/SURVDISJ_CONSTRUCT_2026-08-08.md.  Three
deliberate defeat constructions against (SURV-DISJ) = "on live rows the netted
BOTTOM stratum survives netting OR the CASCADE slot survives at the cascade
line", OUTSIDE its proved loci (g0=1 ∧ d0=1 cascade leg; g0=2 ∧ (K2-REG)
bottom leg):

  (T1) g0 = 3 double kill — the derived n=5 window doors (the count(-2)
       exchange {C0} vs {C2,C2,C2}, the {C2,C1} order-multiplicity) at
       residue characteristic 2, where equal-residue pairs annihilate
       sign-blind.
  (T2) the glued stratum — the SDW4G2F duplicate-book mechanism amplified
       (char-2 duplicate pairs net 0 automatically; hunt even glued groups).
  (T3) the (SD-YJ) box — the FIRST-EVER g0 = 1 ∧ d0 >= 2 towers; measure
       whether Phi0Y-fed cascade companions materialize and whether the
       cascade survives (machine-dark corner -> data).

ENGINE-CAPABILITY DISCLOSURE (the T1 gate finding, reproduced as CON-WALL):
the committed level-0 pick grb_order2_check.pick_irreducible enumerates ONLY
degree-2 candidates at g >= 2 ([b, a, 1] loop) and fp_irreducible raises
ValueError above degree 2 — so at g0 = 3 the committed chain SILENTLY returns
a degree-2 psi0 and then HANGS in PE.prep (probe: 20 s alarm, stage = prep).
The "g0 >= 3 engine cost wall" (SURVK2 instrument amendment; ten 300 s
timeouts) is therefore a CAPABILITY wall, not a cost wall.  This runner
carries a disclosed, minimal extension — installed by monkeypatch BEFORE any
tower construction, engines byte-untouched on disk:
  * fp_irr_gen: deg <= 2 delegates to the committed test verbatim; deg 3 uses
    no-root-in-F (exact for cubics);
  * pick_irr_gen: g <= 2 delegates to the committed pick verbatim (agreement
    census CON-AGREE); g = 3 enumerates [b, a1, a2, 1] in the committed
    _field_elems order with nonzero constant term, idx % len wraparound (the
    committed convention one degree up);
  * PICK_OVERRIDE for tower C3OMX ONLY: psi0 = the first irreducible cubic
    over F4 with ALL coefficients nonzero (deterministic enumeration; opens
    the order-multiplicity door, unreachable through idx in {0,1}) —
    irreducibility + psi0(0) != 0 re-verified at pick time (the class pin).
All engine certificates (PE.prep Chat/eps/corr-table exactness, stage sums,
inv_checks) then run UNCHANGED on the extended towers and are harvested as
CON-ENG (predicted 0).

Verdict families (predicted 0 violations unless marked):
  CON-PIN    md5 pins on the consumed engines (byte-untouched).
  CON-WALL   the capability wall reproduces exactly as displayed.
  CON-AGREE  patched pick == committed pick on every g <= 2 case probed.
  CON-ENG    engine-internal violations (PE/ED/WS/WD/SK2 harvest).
  CON-XWALK  recording walk == committed ED.walk (terminal multiset).
  CON-CONS   stage sums = E1IH / Q1.
  CON-MASS   the SD-L2 E-weighted mass ledger, cellwise, all towers.
  CON-WIN    window replay exact; budgets n <= 2g0 - 1 (= 5 at g0 = 3).
  CON-INV    every realized Y-free drain is in the general legal inventory.
  CON-FACT   K2-L4 factorization on junk-free two-exit cells (first g0 = 3
             and first g0=1∧d0=2 exercise).
  CON-CRIT   SD-L6 crosscheck: polynomial group kill == residue-sum kill.
  CON-EXCH   realized (-2)-window partner pairs carry EQUAL residues
             (the char-2 auto-kill identity, derived in the note).
  CON-DUP    duplicate-book pairs carry equal residues (same book).
  CON-STAR   (*) at g0=1 ∧ (STK): every cascade-slot cell has
             sum(defc) == Y2 — first exercise at d0 = 2.
  CON-DEF    SD-L1 deficit bound on g0 = 1 rows — first exercise at d0 = 2.
  CON-YJ0    every defc = 0 correction has e_i = 1 ∧ Y-child ∧ full dump
             (the (SD-YJ) equality analysis).
  HARNESS    everything else.
FINDINGS (measured, never violations): DK rows (bottom dead AND cascade leg
dead — (SURV-DISJ) counterexample candidates), bottom-dead rows, rows with no
protected bottom group ((SURV-K2)-form events), exchange/order-multiplicity
window realizations, duplicate-book fibers, g0=1 cascade companions,
Phi0Y-edge counts on the YJ towers.

Deterministic, exact arithmetic, no sampling.  Two-commit seal: this runner
+ the note's defeat systems and prediction sheet are committed BEFORE the
sealed run; the verdict is appended from the artifacts.
Usage: python3 survdisj_construct.py [outdir]
"""
import sys, os, time, json, hashlib, collections, signal

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
OUTDIR = sys.argv[1] if len(sys.argv) > 1 else HERE

VIOL, CNT = [], {}
FINDINGS = []
def note(f, n=1): CNT[f] = CNT.get(f, 0) + n
def viol(fam, tag, detail):
    VIOL.append((fam, tag, str(detail)[:400]))
    print(f"VIOLATION [{fam}] {tag}: {str(detail)[:360]}")
def finding(kind, tag, detail):
    FINDINGS.append((kind, tag, detail))
    print(f"*** FINDING [{kind}] {tag}: {str(detail)[:360]}")

PINS = {
    "grb_order2_check.py":       "dab62713175363a7185211890019ae2f",
    "rmengine_pe_reimpl.py":     "103c1a9c99e2b4a3e8b63c93cbf87e25",
    "empty_derive_checks.py":    "8fed92402bcffe6e0c536f1f9d847612",
    "wmultdcx_stress.py":        "15315cca59c87e6c2001ea744c50aab5",
    "wmultdcx_derive_checks.py": "bea1a43d619a3c91a9a0b2f32c0920c0",
    "survk2_derive_checks.py":   "d8493ab90e3578fae60032cde73a3b81",
    "survdisj_derive_checks.py": "3eaf69c08f9a5b278826102610d4aa22",
}
for fn, want in PINS.items():
    got = hashlib.md5(open(os.path.join(HERE, fn), "rb").read()).hexdigest()
    if got != want:
        viol("CON-PIN", fn, f"md5 {got} != pinned {want}")

# ===================== the disclosed level-0 pick extension ===================
import grb_order2_check as G
from grb_order2_check import (pnorm, padd, pneg, pmul, pscal, pdivmod, w0,
                              mk_field_base)

_committed_pick = G.pick_irreducible
_committed_irr  = G.fp_irreducible

# CON-WALL: reproduce the capability wall from the committed functions.
_F2 = mk_field_base(2, [0, 1])
_w = _committed_pick(_F2, 3, idx=1)
if len(_w) - 1 != 2:
    viol("CON-WALL", "pick", f"committed pick at (F2, g=3) returned degree "
         f"{len(_w)-1}, expected the silent degree-2 wall")
else:
    note("wall_pick_deg2")
try:
    _committed_irr(_F2, [_F2["one"], _F2["one"], _F2["zero"], _F2["one"]])
    viol("CON-WALL", "irr", "committed fp_irreducible accepted a cubic")
except ValueError:
    note("wall_irr_valueerror")

def _no_root(F, A):
    return all(not F["isz"](G.fp_eval(F, A, e)) for e in G._field_elems(F))

def fp_irr_gen(F, A):
    d = len(A) - 1
    if d <= 2:
        return _committed_irr(F, A)
    if d == 3:
        return _no_root(F, A)          # cubic: no root <=> irreducible
    raise ValueError("this unit extends to deg 3 only")

PICK_OVERRIDE = {}                     # (q, g) -> coeff list; C3OMX only

def pick_irr_gen(F, g, idx=0):
    key = (F.get("q"), g)
    if key in PICK_OVERRIDE:
        cand = PICK_OVERRIDE[key]
        # the class pin, re-verified at pick time
        assert not F["isz"](cand[0]) and cand[-1] == F["one"] \
            and fp_irr_gen(F, cand)
        note("pick_override_used")
        return cand
    if g <= 2:
        return _committed_pick(F, g, idx)
    matches = []
    for b in G._field_elems(F):
        if F["isz"](b): continue
        for a1 in G._field_elems(F):
            for a2 in G._field_elems(F):
                cand = [b, a1, a2, F["one"]]
                if fp_irr_gen(F, cand):
                    matches.append(cand)
    if not matches:
        raise RuntimeError("no irreducible found")
    return matches[idx % len(matches)]

# CON-AGREE: byte-agreement with the committed pick on the g <= 2 grid.
for (p_, phibar_, nm_) in ((2, [0, 1], "F2"), (3, [0, 1], "F3"),
                           (5, [0, 1], "F5"), (2, [1, 1, 1], "F4"),
                           (3, [1, 0, 1], "F9")):
    F_ = mk_field_base(p_, phibar_)
    for g_ in (1, 2):
        for idx_ in (0, 1):
            if _committed_pick(F_, g_, idx_) != pick_irr_gen(F_, g_, idx_):
                viol("CON-AGREE", nm_, f"g={g_} idx={idx_} mismatch")
            else:
                note("agree_cases")

# the C3OMX override: first irreducible cubic over F4 with ALL coeffs nonzero
_F4 = mk_field_base(2, [1, 1, 1])
_omx = None
for b in G._field_elems(_F4):
    if _F4["isz"](b): continue
    for a1 in G._field_elems(_F4):
        if _F4["isz"](a1): continue
        for a2 in G._field_elems(_F4):
            if _F4["isz"](a2): continue
            cand = [b, a1, a2, _F4["one"]]
            if _no_root(_F4, cand):
                _omx = cand; break
        if _omx: break
    if _omx: break

G.pick_irreducible = pick_irr_gen
G.fp_irreducible = fp_irr_gen

# committed engines, imported AFTER the patch install (call-time lookup makes
# the order immaterial; kept explicit for the audit trail)
import rmengine_pe_reimpl as PE
import wmultdcx_stress as WS
import wmultdcx_derive_checks as WD
import empty_derive_checks as ED
import survk2_derive_checks as SK2     # walk_rec / windows_of / build_maps /
                                       # fingerprint / classify_group / protected

def harvest(tag):
    for src, lst in (("PE", PE.VIOL), ("ED", ED.VIOL), ("WS", WS.VIOL),
                     ("WD", WD.VIOL), ("SK2", SK2.VIOL)):
        while len(lst) > harvest.seen[src]:
            v = lst[harvest.seen[src]]
            if "tree cap" in str(v):
                note("treecap")
            else:
                viol("CON-ENG", tag, f"{src}: {v}")
            harvest.seen[src] += 1
harvest.seen = {"PE": 0, "ED": 0, "WS": 0, "WD": 0, "SK2": 0}

# ===================== the general level-0 drain inventory ====================
def legal_drains_gen(n, g0, masses):
    """All legal Y-free drains from n units: events fire at u >= g0; a
    correction of mass mu in `masses` consumes mu units; a promotion consumes
    g0.  Returns [(K_mass_multiset_sorted, p, f_units, seq)]."""
    out = []
    def rec(u, K, p, seq):
        if u < g0:
            out.append((tuple(sorted(K)), p, u, tuple(seq)))
            return
        for mu in sorted(masses):
            rec(u - mu, K + [mu], p, seq + (('c', mu),))
        rec(u - g0, K, p + 1, seq + (('p',),))
    rec(n, [], 0, ())
    return out

# ============================== one traced row ================================
def trace_row(E, sA, sB, u1a, u1b, aA, aB, su, cs, pools, Dd, kdef, key, prin,
              tag, target, u0, dmap, Dmap, rowrecs):
    R = E.R; m = E.m; g0 = E.g[0]; d0 = E.d0; p = E.p
    sig = tuple(sA[l + 1] + sB[l + 1] for l in range(m))
    s1u1 = su[1]
    b0 = pscal(R, R["pi_pow"](u1a + u1b), [R["one"]])
    prodp = pmul(R, aA, aB)
    z = (0,) * m
    # reference walk (committed ED.walk), stage 1
    init_ref = [(1, b0, sig, z, z, z, z, 0, None, False, (), 0)]
    q1_ref = []
    out = ED.walk(E, init_ref, q1_ref, tag)
    if out[0] is None: harvest(tag); return None
    # recording walk, stage 1
    init_rec = [(1, b0, sig, z, z, z, z, 0, None, False, (), 0, ())]
    q1_rec = []
    r = SK2.walk_rec(E, init_rec, q1_rec, tag)
    if r is None: return None
    if (sorted(map(SK2.fingerprint, q1_ref)) !=
            sorted(SK2.fingerprint(st[:12]) for st in q1_rec)):
        viol("CON-XWALK", tag, f"stage-1 terminal mismatch at {key}")
        return None
    E1c, _ = pdivmod(R, prodp, E.Phis[m])
    if WD.cellsum(E, q1_ref) != pnorm(R, E1c):
        viol("CON-CONS", tag, f"stage-1 sum != E1IH at {key}")
    def seed(states, rec):
        init2 = []
        for st in states:
            if rec:
                sgn, b, j, pc, dmp, cons, ncorr, junk, _, _, ce, _, hist = st
            else:
                sgn, b, j, pc, dmp, cons, ncorr, junk, _, _, ce, _ = st
            for (cD, jD) in E.Dcells:
                Lc, Xc, Yc = E.digit_split(b, cD)
                js = tuple(j[l] + jD[l] for l in range(m))
                isp = (tuple(jD) == prin)
                for (cc, jtag, dj0) in ((Lc, 0, 0), (Xc, 1, 0), (Yc, 1, 1)):
                    if not pnorm(R, cc): continue
                    jj = list(js); jj[0] += dj0
                    dd = list(dmp); dd[0] += dj0
                    if rec:
                        h2 = hist + (('seed', jD[0] + dj0),)
                        init2.append((sgn, cc, tuple(jj), pc, tuple(dd), cons,
                                      ncorr, junk + jtag, tuple(jD), isp, ce,
                                      dj0, h2))
                    else:
                        init2.append((sgn, cc, tuple(jj), pc, tuple(dd), cons,
                                      ncorr, junk + jtag, tuple(jD), isp, ce,
                                      dj0))
        return init2
    q2_ref = []
    out2 = ED.walk(E, seed(q1_ref, False), q2_ref, tag)
    if out2[0] is None: harvest(tag); return None
    q2_rec = []
    r = SK2.walk_rec(E, seed(q1_rec, True), q2_rec, tag)
    if r is None: return None
    if (sorted(map(SK2.fingerprint, q2_ref)) !=
            sorted(SK2.fingerprint(st[:12]) for st in q2_rec)):
        viol("CON-XWALK", tag, f"stage-2 terminal mismatch at {key}")
        return None
    Q1c = pdivmod(R, pmul(R, E1c, E.Chat), E.Phis[m])[0]
    if WD.cellsum(E, q2_ref) != pnorm(R, Q1c):
        viol("CON-CONS", tag, f"stage-2 sum != Q1 at {key}")
    harvest(tag)
    if not q2_rec:
        return None
    note("live_rows")
    EW = [1]
    for l in range(m): EW.append(EW[-1] * E.e[l])
    a_, r_, b_, stock1 = WD.greedy_chains(E, sig, su, cs)
    stk = (stock1 >= E.P[m - 1])
    # -------- per-cell processing --------
    cells = []
    inv_cache = {}
    for st in q2_rec:
        (sgn, b, j, pc, dmp, cons, ncorr, junk, jD, isp, ce, y2, hist) = st
        ln = E.line(b, j)
        t, rem = divmod(jD[0] - s1u1, E.e[0])
        if rem != 0 or not (0 <= t < g0):
            viol("CON-FACT", tag, f"seed t-decomposition fails at {key}")
            return None
        # CON-MASS: the SD-L2 ledger
        lhs = sum(j[l] * EW[l] for l in range(m))
        rhs = (sum(sig[l] * EW[l] for l in range(m))
               + sum(jD[l] * EW[l] for l in range(m)) + y2
               - 2 * E.P[m - 1] * EW[m - 1]
               - sum(pc[l - 1] * (E.P[l - 1] * EW[l - 1] - EW[l])
                     for l in range(1, m)))
        defcs = []
        for (i, kc, avec, dj0) in ce:
            dc = ((E.P[i] - E.e[i] * kc) * EW[i]
                  - sum(avec[l] * EW[l] for l in range(i)) - dj0)
            rhs -= dc
            defcs.append((i, kc, avec, dj0, dc))
        if lhs != rhs:
            viol("CON-MASS", tag, f"ledger fails at {key}: {lhs} != {rhs}")
        # CON-DEF / CON-YJ0 at g0 = 1 (any d0 — first d0 = 2 exercise)
        if g0 == 1:
            for (i, kc, avec, dj0, dc) in defcs:
                lo = EW[i + 1] - EW[i] + (1 if dj0 == 0 else 0)
                if dc < lo or dc < 0:
                    viol("CON-DEF", tag,
                         f"SD-L1 breach at {key}: i={i} defc={dc} < {lo}")
                if dc == 0:
                    note("defc0_corrections")
                    fulldump = all(avec[l] == E.P[l] - 1 for l in range(i))
                    if not (E.e[i] == 1 and dj0 == 1 and fulldump):
                        viol("CON-YJ0", tag,
                             f"defc=0 outside the (SD-YJ) shape at {key}: "
                             f"i={i} e_i={E.e[i]} Y={dj0} avec={list(avec)}")
        if y2: note("y2_edges")
        for (_, _, _, dj0) in ce:
            if dj0: note("yc_edges")
        # windows
        wins, endj0 = SK2.windows_of(E, hist, sig[0], None)
        if wins is None:
            viol("CON-WIN", tag, f"window replay failed at {key}: {endj0}")
            continue
        if endj0 != j[0]:
            viol("CON-WIN", tag, f"replay j0 {endj0} != {j[0]} at {key}")
        masses = frozenset(g0 - kk for (kk, dcl) in E.corr_table()[0])
        for w in wins:
            if w['n'] > 2 * g0 - 1:
                viol("CON-WIN", tag, f"budget n={w['n']} > 2g0-1 at {key}")
            if w['j0close'] >= E.P[0]:
                viol("CON-WIN", tag, f"window did not drain at {key}")
            if w['ev'] and not w['hasY']:
                ck = (w['n'], masses)
                if ck not in inv_cache:
                    inv_cache[ck] = legal_drains_gen(w['n'], g0, masses)
                drains = inv_cache[ck]
                mseq = tuple(('c', g0 - e[1]) if e[0] == 'c' else ('p',)
                             for e in w['ev'])
                match = [d for d in drains if d[3] == mseq]
                if not match:
                    viol("CON-INV", tag,
                         f"drain {w['ev']} not in inventory n={w['n']} "
                         f"at {key}")
                else:
                    Kms = match[0][0]
                    same_kp = [d for d in drains
                               if d[0] == Kms and d[1] == w['p']]
                    if len(same_kp) >= 2:
                        note("om_order_windows")
                        finding("OM-WINDOW", tag,
                                dict(key=key, n=w['n'], K=list(Kms),
                                     p=w['p'], orders=len(same_kp)))
        M_K = sum(g0 - e[1] for e in ce if e[0] == 0)
        cells.append(dict(sgn=sgn, b=b, j=j, pc=tuple(pc), ncorr=sum(ncorr),
                          junk=junk, jD=tuple(jD), ce=ce, y2=y2, line=ln,
                          w0=w0(R, b), res=E.resKm(b), t=t, MK=M_K,
                          prin=isp, wins=wins, defcs=defcs))
        # CON-FACT on junk-free cells
        if junk == 0 and y2 == 0:
            cD = Dmap.get(tuple(jD))
            wexp = (u1a + u1b) + (u0 - t * E.h[0])
            racc = E.resKm(cD)
            ok = (w0(R, cD) == u0 - t * E.h[0])
            if not ok:
                viol("CON-FACT", tag, f"seed w0 leg fails at {key}")
            for (i, kk, avec, dj0) in ce:
                dg = dmap.get((i, kk, avec))
                if dg is None or dj0 != 0:
                    ok = False; break
                wexp += w0(R, dg)
                racc = E.kmul(racc, E.resKm(dg))
            if ok:
                if w0(R, b) != wexp:
                    viol("CON-FACT", tag, f"w0 additivity fails at {key}")
                if not E.keq(E.resKm(b), racc):
                    viol("CON-FACT", tag, f"residue product fails at {key}")
                if sgn != (-1) ** len(ce):
                    viol("CON-FACT", tag, f"sign parity fails at {key}")
                note("fact_cells")
    if not cells:
        return None
    # -------- groups + verdicts --------
    beta_min = min(c['line'] for c in cells)
    slots = collections.defaultdict(list)
    for c in cells: slots[c['j']].append(c)

    def group_verdict(grp, jv, ln):
        acc = []
        for c in grp:
            acc = padd(R, acc, c['b'] if c['sgn'] > 0 else pneg(R, c['b']))
        acc = pnorm(R, acc)
        killed = (not acc) or E.line(acc, jv) != ln
        classes, signed = SK2.classify_group(E, grp)
        rsum = E.Km["zero"]
        for c in grp:
            rv = c['res'] if c['sgn'] > 0 else E.Km["neg"](c['res'])
            rsum = E.Km["add"](rsum, rv)
        if killed != E.Km["isz"](rsum):
            viol("CON-CRIT", tag, f"poly-kill != residue-kill at {key} "
                 f"slot {list(jv)} line {ln}")
        return killed, classes, signed, acc

    bot_report = []
    bottom_dead = True
    prot_some = False
    for jv in sorted(slots):
        grp = [c for c in slots[jv] if c['line'] == beta_min]
        if not grp: continue
        killed, classes, signed, acc = group_verdict(grp, jv, beta_min)
        if not killed: bottom_dead = False
        if SK2.protected(signed): prot_some = True
        bot_report.append(dict(slot=list(jv), n=len(grp), signed=signed,
                               killed=killed))
        # T1 exchange-pair detection: within fibers, K differing by
        # {0} <-> {2,2,2} (g0 = 3 only)
        if g0 == 3:
            fibs = collections.defaultdict(list)
            for c in grp:
                ib = tuple(sorted(e for e in c['ce'] if e[0] != 0))
                fibs[(c['t'], ib, c['pc'])].append(c)
            for fk, fc in fibs.items():
                byK = {}
                for c in fc:
                    K = tuple(sorted(e[1] for e in c['ce'] if e[0] == 0))
                    byK.setdefault(K, []).append(c)
                for K in list(byK):
                    base = list(K)
                    if 0 in base:
                        base.remove(0)
                        Kb = tuple(sorted(base + [2, 2, 2]))
                        if Kb in byK:
                            note("exch_pairs")
                            a1 = byK[K][0]; b1 = byK[Kb][0]
                            finding("EXCH-WINDOW", tag,
                                    dict(key=key, slot=list(jv),
                                         KA=list(K), KB=list(Kb),
                                         sgns=(a1['sgn'], b1['sgn'])))
                            if not E.keq(a1['res'], b1['res']):
                                viol("CON-EXCH", tag,
                                     f"exchange partners residues differ "
                                     f"at {key} slot {list(jv)}")
        # duplicate-book detection (any tower)
        dupk = collections.Counter()
        for c in grp:
            ib = tuple(sorted(e for e in c['ce'] if e[0] != 0))
            K = tuple(sorted(e[1] for e in c['ce'] if e[0] == 0))
            dupk[(c['t'], K, ib, c['pc'], c['sgn'])] += 1
        for dk, nn in dupk.items():
            if nn >= 2:
                note("dup_book_fibers")
                cc = [c for c in grp if (c['t'],
                      tuple(sorted(e[1] for e in c['ce'] if e[0] == 0)),
                      tuple(sorted(e for e in c['ce'] if e[0] != 0)),
                      c['pc'], c['sgn']) == dk]
                for i1 in range(1, len(cc)):
                    if not E.keq(cc[0]['res'], cc[i1]['res']):
                        viol("CON-DUP", tag,
                             f"duplicate-book residues differ at {key}")
                finding("DUP-BOOK", tag,
                        dict(key=key, slot=list(jv), mult=nn,
                             book=str(dk)[:120], groupn=len(grp)))
    # glued census
    for jv in sorted(slots):
        grp = [c for c in slots[jv] if c['line'] == beta_min]
        if len(grp) < 2: continue
        fibkeys = set()
        for c in grp:
            ib = tuple(sorted(e for e in c['ce'] if e[0] != 0))
            fibkeys.add((ib, c['pc']))
        if len(fibkeys) > 1:
            note("glued_groups")
    # -------- cascade leg --------
    casc = [c for c in cells if c['ce'] == () and c['junk'] == 0
            and c['y2'] == 0 and c['prin']]
    casc_rec = casc[0] if len(casc) == 1 else None
    jhat = tuple([pools[l] - E.e[l] * cs[l] for l in range(m - 1)]
                 + [cs[-1] - kdef]) if cs else None
    if casc_rec is not None and jhat is not None and casc_rec['j'] != jhat:
        note("jhat_formula_mismatch")   # census only; cell is authoritative
    if casc_rec is not None:
        jv = casc_rec['j']
        allj = slots[jv]
        acc = []
        for c in allj:
            acc = padd(R, acc, c['b'] if c['sgn'] > 0 else pneg(R, c['b']))
        acc = pnorm(R, acc)
        casc_strong = bool(acc) and w0(R, acc) == casc_rec['w0']
        grp = [c for c in allj if c['line'] == casc_rec['line']]
        killed, _, _, _ = group_verdict(grp, jv, casc_rec['line'])
        casc_group_surv = not killed
        casc_partners = len(allj) - 1
        casc_state = "SURV" if casc_strong else "KILLED"
    else:
        casc_strong = False
        casc_group_surv = False
        casc_partners = None
        casc_state = "ABSENT"
    # (*) + companions at g0 = 1
    companions = []
    if g0 == 1 and casc_rec is not None and stk:
        for c in slots[casc_rec['j']]:
            if c is casc_rec: continue
            sd = sum(dc for (_, _, _, _, dc) in c['defcs'])
            if sd != c['y2']:
                viol("CON-STAR", tag,
                     f"(*) breach at {key}: sum defc={sd} != Y2={c['y2']}")
            companions.append(dict(junk=c['junk'], nce=len(c['ce']),
                                   y2=c['y2'], w0=c['w0'],
                                   line=c['line'], sumdefc=sd))
        if companions:
            finding("YJ-COMPANION", tag,
                    dict(key=key, n=len(companions), comps=companions,
                         casc_state=casc_state))
    # -------- row verdict --------
    if not prot_some:
        finding("K2FORM", tag, dict(key=key,
                detail="no protected bottom group",
                bots=bot_report))
    if bottom_dead:
        finding("BOTTOM-DEAD", tag, dict(key=key, bots=bot_report,
                                         casc=casc_state))
    dk = bottom_dead and not casc_strong
    if dk:
        finding("DOUBLE-KILL", tag, dict(
            key=key, casc=casc_state, bots=bot_report,
            detail="(SURV-DISJ) DEFEATED on this row: bottom stratum "
                   "netted to zero at beta_min AND the cascade leg fails"))
        note("dk_rows")
    rowrecs.append(dict(tower=tag, key=list(key), g0=g0, d0=d0, p=p,
                        kind=E.kind, ncells=len(cells), beta_min=beta_min,
                        nbot=len(bot_report), bottom_dead=bottom_dead,
                        prot=prot_some, casc=casc_state,
                        casc_group_surv=casc_group_surv,
                        casc_partners=casc_partners, stk=stk,
                        ncomp=len(companions), dk=dk))
    return dict(live=True)

# ============================== tower driver ==================================
def run_tower(spec, target, rowrecs, budget=900):
    tag, m, kind, p, d0, reads = spec[:6]
    t0 = time.time()
    def _alrm(s, f): raise TimeoutError("tower budget")
    old = signal.signal(signal.SIGALRM, _alrm)
    signal.alarm(budget)
    try:
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
        u0 = meta["u0"]
        etop = E.e[m - 1]; R = E.R
        psi0 = E.grbT.psi0
        A = sorted(k for k in range(E.g[0])
                   if not E.grbT.K0["isz"](psi0[k]))
        seen = set(); nl = 0; nrows = 0
        for ga in range(G0, G0 + Etot):
            aA, sA, u1a = anch[ga]
            for gb in range(G0, G0 + Etot):
                aB, sB, u1b = anch[gb]
                if not (sA[m + 1] == E.e[m] - 1
                        and sB[m + 1] == E.e[m] - 1):
                    continue
                E1, _ = pdivmod(R, pmul(R, aA, aB), E.Phis[m])
                if not pnorm(R, E1): continue
                key = (tuple(sorted([(tuple(sA[l] for l in range(1, m + 2)),
                                      u1a),
                                     (tuple(sB[l] for l in range(1, m + 2)),
                                      u1b)])))
                if key in seen: continue
                seen.add(key)
                pools, cs, Dd, top = WS.pools_of(E, sA, sB, su)
                ctop = cs[-1] if cs else 0
                kdef = 2 * etop - Dd
                if kdef > ctop: continue
                nrows += 1
                rr = trace_row(E, sA, sB, u1a, u1b, aA, aB, su, cs, pools,
                               Dd, kdef, (ga, gb), prin, tag, target, u0,
                               dmap, Dmap, rowrecs)
                if rr: nl += 1
        signal.alarm(0); signal.signal(signal.SIGALRM, old)
        print(f"-- {target} {tag} m={m} {kind},p={p},d0={d0} g0={E.g[0]} "
              f"A={A} psi0={psi0}: live-clause rows={nrows} traced "
              f"nonempty={nl} ({time.time()-t0:.1f}s)")
    except TimeoutError:
        signal.alarm(0); signal.signal(signal.SIGALRM, old)
        print(f"-- {target} {tag}: TOWER BUDGET EXCEEDED ({budget}s) — "
              f"disclosed skip")
        note("tower_budget_skips")
    except Exception as ex:
        signal.alarm(0); signal.signal(signal.SIGALRM, old)
        print(f"-- {target} {tag}: ENGINE UNSUPPORTED ({ex!r}) — disclosed")
        note("tower_skipped")

# ============================== the rosters ===================================
T1_ROSTER = [
    # the (-2)-window door towers: A = {0,2} at char 2 (psi0 = y^3+y^2+1 / F2)
    ("C3W2F",  3, "Fpt", 2, 1, [(2,1,3), (3,2,1), (2,1,1), (2,1,1)]),
    ("C3W2F2", 3, "Fpt", 2, 1, [(2,1,3), (3,2,1), (2,3,1), (2,1,1)]),
    ("C2W2F",  2, "Fpt", 2, 1, [(2,1,3), (3,2,1), (2,1,1)]),
    ("C3W2Z",  3, "Zp",  2, 1, [(2,1,3), (3,2,1), (2,1,1), (2,1,1)]),
    # A = {0,1} controls (y^3+y+1): no multi-member drain class at any n <= 5
    ("C3T0F",  3, "Fpt", 2, 1, [(2,1,3), (2,1,1), (2,1,1), (2,1,1)]),
    ("C3DPF",  3, "Fpt", 2, 1, [(2,1,3), (2,3,1), (2,1,1), (2,1,1)]),
    # the K2 instrument's stalled towers, resurrected verbatim reads
    ("C3K2AF", 3, "Fpt", 2, 1, [(2,1,3), (2,1,1), (3,2,1), (2,1,1)]),
    ("C3E3F",  3, "Fpt", 2, 1, [(3,1,3), (2,1,1), (2,1,1), (2,1,1)]),
    # d0 = 2 (K0 = F4): default picks give A = {0,2}
    ("C3OM3F", 3, "Fpt", 2, 2, [(2,1,3), (2,1,1), (2,1,1), (2,1,1)]),
    ("C2OMF",  2, "Fpt", 2, 2, [(2,1,3), (2,1,1), (2,1,1)]),
    # char-3 full-availability control (order pair survives at p = 3: teeth)
    ("C3F3Z",  3, "Zp",  3, 1, [(2,1,3), (2,1,1), (2,1,1), (2,1,1)]),
]
# C3OMX: the override tower (A = {0,1,2} over F4 — BOTH doors), appended in
# main() so the override is scoped to exactly one construction.
T1_OMX = ("C3OMX", 3, "Fpt", 2, 2, [(2,1,3), (2,1,1), (2,1,1), (2,1,1)])

T2_ROSTER = [
    ("SDW4G2F",  4, "Fpt", 2, 1, [(3,1,2), (2,1,1), (2,1,1), (2,1,1), (2,1,1)]),
    ("CDW3G2F",  3, "Fpt", 2, 1, [(3,1,2), (2,1,1), (2,1,1), (2,1,1)]),
    ("CDW4G2F2", 4, "Fpt", 2, 1, [(3,1,2), (2,3,1), (2,1,1), (2,1,1), (2,1,1)]),
]

T3_ROSTER = [
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

# ================================== main ======================================
def main():
    t0 = time.time()
    print("=" * 78)
    print("(SURV-DISJ) DOUBLE-KILL CONSTRUCTION — sealed battery")
    print(f"override cubic for C3OMX (F4, all coeffs nonzero): {_omx}")
    print("=" * 78)
    rowrecs = []
    print("---- T1: g0 = 3 (the resurrected regime) ----")
    for spec in T1_ROSTER:
        run_tower(spec, "T1", rowrecs)
    PICK_OVERRIDE[(4, 3)] = _omx
    run_tower(T1_OMX, "T1", rowrecs)
    del PICK_OVERRIDE[(4, 3)]
    print("---- T2: the glued stratum (duplicate-book amplification) ----")
    for spec in T2_ROSTER:
        run_tower(spec, "T2", rowrecs)
    print("---- T3: g0 = 1 AND d0 = 2 (the (SD-YJ) machine-dark corner) ----")
    for spec in T3_ROSTER:
        run_tower(spec, "T3", rowrecs)
    print("=" * 78)
    fams = ["CON-PIN", "CON-WALL", "CON-AGREE", "CON-ENG", "CON-XWALK",
            "CON-CONS", "CON-MASS", "CON-WIN", "CON-INV", "CON-FACT",
            "CON-CRIT", "CON-EXCH", "CON-DUP", "CON-STAR", "CON-DEF",
            "CON-YJ0", "HARNESS"]
    for f in fams:
        print(f"{f:10s}: {sum(1 for v in VIOL if v[0] == f)} violations")
    print("-" * 78)
    fk = collections.Counter(k for (k, _, _) in FINDINGS)
    print("FINDINGS census:", dict(sorted(fk.items())))
    print("counters:", {k: CNT[k] for k in sorted(CNT)})
    print(f"live rows traced: {CNT.get('live_rows', 0)}; "
          f"double-kill rows: {CNT.get('dk_rows', 0)}")
    print(f"total violations: {len(VIOL)}")
    el = time.time() - t0
    print(f"elapsed: {el:.1f}s")
    out = dict(final=True, violations=VIOL, findings=FINDINGS, counters=CNT,
               rows=rowrecs, omx_cubic=str(_omx), elapsed=el)
    with open(os.path.join(OUTDIR, "survdisj_construct_results.json"),
              "w") as f:
        json.dump(out, f, indent=1, default=str)
    print("results -> survdisj_construct_results.json")

if __name__ == "__main__":
    main()
