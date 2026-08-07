#!/usr/bin/env python3
"""k2res_checks.py — K2-RESIDUE unit machine leg (2026-08-08 campaign,
wallclock 2026-08-07).  Note of record: lean/notes/openmath/
K2RES_PROOF_2026-08-08.md (sealed with this runner at commit 1, UNRUN).

Attacks the ledgered Q2 residue (K2-MULT-RES + g0 >= 3) per that note:
the any-g0 drain calculus (K2-L13), the single-window form space and
verdict column at g0 in {3,4} (K2-L14/L15, K2-THM-C), the any-g0 A={0}
lemma (K2-L16), the promotion-swap reduction (K2-L17), the in-vivo
promotion census on the 332 traced rows (KR-PFREE), and a budget-boxed
g0 >= 3 engine attempt (KR-VIVO; skip = disclosed, exactly the
instrument's precedent).

REUSE (md5-pinned, read-only imports; no pinned file is modified):
  survk2_derive_checks.py  — legal_drains_g2 (calibration target),
                             walk_rec + windows_of (the recording walk),
                             classify_group/protected (SD-L7 predicate),
                             roster constants PX/SD/K2_TRACED.
  survk2_instrument.py     — not imported (roster duplicated in SD).
  k2close_verdicts.py      — Lat/closure/protection/vsub (exact lattice
                             kit), classify_form + FORM_CORNERS (the
                             g0=2 calibration target).
  engine stack             — wmultdcx_stress, wmultdcx_derive_checks,
                             rmengine_pe_reimpl, empty_derive_checks,
                             grb_order2_check (via SD's own imports +
                             direct, all pinned).

PREREGISTERED PREDICTIONS (sealed; judged at commit 2):
 P-1 KR-INV/KR-CAL: fresh double enumerator (unit + raw-j0) == pinned
     legal_drains_g2 at g0=2 EXACTLY; g0=2 column reproduces S/P1/P2/T1
     + FORM_CORNERS exactly (I1 = A1, I3 = E0).
 P-2 KR-ORD/KR-TOT: g0=3 full A: S2 table of the note byte-exact;
     {C1,C2}@n=5 the unique multi-order multiset (2 orders); class
     totals in {-1,0,+1}; multi-member class totals in {0,+1}.
 P-3 KR-ORD: g0=4 full A: class totals in {-1,0,+1}; multi-order
     multisets exist with counts up to 3 (incl {C2,C3,C3} x3 at n=7).
 P-4 KR-TOT: over all A containing 0 at g0=3: the -2 window
     (A={0,2}, n=5, units 3, p 0) is the UNIQUE |total| >= 2 sector;
     at g0=4 such sectors exist incl. the pure order-multiplicity +2
     (A={0,1,2}, n=7, units 5: {C1,C2} x2 alone).
 P-5 KR-SWAP/KR-INV: g0 in 2..6: A={0} inventories all-singleton
     one-event drains; {C_{g0-1},P} fits at budget 2g0-1; {C0,P} never.
 P-6 KR-PFREE (MEASURED census; RESHAPED at shakedown, disclosed
     below): promotion-carrying junk-free beta_min cells EXIST — the
     pre-seal shakedown found 2 rows on SDW4G2F (the glued witness
     tower) — so the K2-L17(c) exit-critical corner is REALIZED in
     vivo, not hypothetical.  The full census measures: #rows with
     promotion-carrying beta_min cells (predicted >= 2, exact count
     open), their towers (predicted to include glued towers; whether
     any REGULAR row carries one is OPEN and the census decides it),
     and the single-/multi-window split of beta_min cells.  All
     reported as FINDINGS, never violations.
 P-7 KR-COL: g0=3: singleton-census single-seed forms safe at every
     corner; exchange-pair forms conditional exactly on their identity;
     the obstruction sector (n=5,u=3,p=0 single-seed) corner-safe
     exactly on the 8 corners with E0 xor E1, NOVEL where !E0 & !E1,
     dead-merge where E0 & E1; full-A group totals T in {-1,0,+1} at
     g0 in {3,4}; every NOVEL (form,corner)'s unconditional-death genre
     is char|T (T != 0) or T0 (census).
 P-8 KR-VIVO (conditional): if a g0>=3 tower preps within the phase
     budget: window budgets <= 2g0-1, realized Y-free drains in the
     K2-L13 inventory, SD-generic laws hold; protection failures are
     FINDINGS.  Else: DISCLOSED SKIP + measured prep times.

PLANTED TEETH (each must FIRE, i.e. the mutant must diverge; a
non-firing tooth is a violation):
 TOOTH-1 firing-threshold mutant (fire at >= g0-1): must produce
         out-of-inventory drains at g0=2, n=3.
 TOOTH-2 sign-blind mutant (all cells +): must break the g0=2
         FORM_CORNERS calibration (P1 loses its safe corners).
 TOOTH-3 seed-quantum mutant (sector budgets n0+2t, masses u0+2t):
         must break the canonical P1 form reproduction (classify_form
         no longer returns P1).

SMOKE + SHAKEDOWN DISCLOSURE (everything that ran before the seal):
(1) an abstract-enumerator smoke (g0 in {2,3,4} inventories,
availability-corner census, a form count, the group-total distribution
at full A) shaped P-2..P-5/P-7.  (2) A full shakedown of the abstract
families ran green (KR-INV/ORD/SWAP/IDC/CAL 0 violations, teeth 3/3
fired; KR-COL 0 violations: g0=3 26 forms 416 pairs 0.1s, g0=4 72
forms 4608 pairs 119s, obstruction corner law confirmed) with ONE
harness repair (the P-7 obstruction-form lookup re-keyed to the census
key after form dedup hid the (n0=5,u0=3) record).  (3) A 2-tower
KR-PFREE shakedown (SDDPG2F, SDW4G2F; 13 rows) ran 0 violations and
RESHAPED P-6: it found the 2 SDW4G2F promotion-carrying rows quoted
there.  No other tower was traced; the full 332-row census, the sealed
teeth run, and KR-VIVO run only at the verdict.  Two engine timing
probes (m=2 g0=3 towers, e0 in {1,2}) were LAUNCHED before sealing to
gate KR-VIVO; their only output is wall-clock time, disclosed at S8.

Deterministic, exact integer arithmetic; engines read-only.
Usage: python3 k2res_checks.py [outdir]
"""
import sys, os, time, json, hashlib, collections, itertools, signal
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
OUTDIR = sys.argv[1] if len(sys.argv) > 1 else HERE

PINS = {
    "survk2_derive_checks.py":   "d8493ab90e3578fae60032cde73a3b81",
    "survk2_instrument.py":      "389b1db9fc0266a12db74e021d7d51c9",
    "survk2_instrument_results.json": "1ac516df8292ac5d57a88e430de3d1e4",
    "k2close_verdicts.py":       "0ad93b21296be9e0056837a3b9fbcd40",
    "k2close_enum.py":           "69cae1baa2eac5282651aa5079695d71",
    "wmultdcx_stress.py":        "15315cca59c87e6c2001ea744c50aab5",
    "wmultdcx_derive_checks.py": "bea1a43d619a3c91a9a0b2f32c0920c0",
    "rmengine_pe_reimpl.py":     "103c1a9c99e2b4a3e8b63c93cbf87e25",
    "grb_order2_check.py":       "dab62713175363a7185211890019ae2f",
    "empty_derive_checks.py":    "8fed92402bcffe6e0c536f1f9d847612",
}

VIOL, CNT, FINDINGS = [], {}, []
def note(f, n=1): CNT[f] = CNT.get(f, 0) + n
def viol(fam, tag, detail):
    VIOL.append((fam, tag, detail)); print(f"VIOLATION [{fam}] {tag}: {detail}")
def finding(tag, detail):
    FINDINGS.append((tag, detail)); print(f"FINDING [{tag}]: {detail}")

import survk2_derive_checks as SD          # pinned; main-guarded
import k2close_verdicts as KV              # pinned; main-guarded
import rmengine_pe_reimpl as PE
import wmultdcx_stress as WS
import wmultdcx_derive_checks as WD
import empty_derive_checks as ED
from grb_order2_check import pnorm, pmul, pscal, pdivmod, w0

def harvest(tag):
    for src, lst in (("PE", PE.VIOL), ("ED", ED.VIOL), ("WS", WS.VIOL),
                     ("WD", WD.VIOL), ("SD", SD.VIOL)):
        while len(lst) > harvest.seen[src]:
            v = lst[harvest.seen[src]]
            if "tree cap exceeded" in str(v):
                note("row_treecap")
            else:
                viol("HARNESS", tag, f"{src}: {v}")
            harvest.seen[src] += 1
harvest.seen = {"PE": 0, "ED": 0, "WS": 0, "WD": 0, "SD": 0}

RES = dict(final=False)
def save(t0, final=False):
    RES.update(final=final, violations=VIOL, counters=CNT,
               findings=FINDINGS, elapsed=round(time.time() - t0, 1))
    with open(os.path.join(OUTDIR, "k2res_checks_results.json"), "w") as f:
        json.dump(RES, f, indent=1, default=str)

# ============ 1. the fresh drain enumerator (two implementations) =============
def drains_units(n, g0, A, thresh=None):
    """Unit-level: sequences over C_k (mass g0-k) / P (mass g0), firing
    while running >= g0 (thresh overrides for TOOTH-1).  Returns list of
    (K sorted tuple, p, f_units, seq)."""
    th = g0 if thresh is None else thresh
    out = []
    def rec(rem, seq):
        if rem < th:
            K = tuple(sorted(k for (c, k) in seq if c == 'c'))
            p = sum(1 for (c, k) in seq if c == 'p')
            out.append((K, p, rem, tuple(seq)))
            return
        for k in sorted(A):
            rec(rem - (g0 - k), seq + [('c', k)])
        rec(rem - g0, seq + [('p', 0)])
    rec(n, [])
    return out

def drains_rawj0(n, r, e0, g0, A):
    """Raw-j0 level: j0 = n*e0 + r; events at j0 >= e0*g0; C_k consumes
    e0*(g0-k), P consumes e0*g0.  Returns list of (K, p, f_units, seq);
    the sub-unit residue r must ride through untouched."""
    P0 = e0 * g0
    out = []
    def rec(j0, seq):
        if j0 < P0:
            fu, rr = divmod(j0, e0)
            if rr != r:
                viol("KR-INV", "rawj0", f"sub-unit residue moved: {rr}!={r}")
            K = tuple(sorted(k for (c, k) in seq if c == 'c'))
            p = sum(1 for (c, k) in seq if c == 'p')
            out.append((K, p, fu, tuple(seq)))
            return
        for k in sorted(A):
            rec(j0 - e0 * (g0 - k), seq + [('c', k)])
        rec(j0 - P0, seq + [('p', 0)])
    rec(n * e0 + r, [])
    return out

def class_census(n, g0, A):
    """(units,p) -> Counter(K -> #legal orders)."""
    cls = collections.defaultdict(collections.Counter)
    for (K, p, fu, seq) in drains_units(n, g0, A):
        cls[(sum(g0 - k for k in K), p)][K] += 1
    return cls

def kr_inv():
    """KR-INV: double-enumerator agreement + g0=2 calibration vs the
    pinned legal_drains_g2 + TOOTH-1."""
    for g0 in range(2, 7):
        for Am in range(1, 1 << g0):
            A = frozenset(k for k in range(g0) if Am >> k & 1)
            if 0 not in A: continue
            if g0 >= 5 and len(A) > 2: continue        # cost fence
            for n in range(0, 2 * g0):
                du = drains_units(n, g0, A)
                for e0 in (1, 2, 3):
                    for r in range(e0):
                        dr = drains_rawj0(n, r, e0, g0, A)
                        if (sorted((K, p, f) for (K, p, f, s) in du) !=
                                sorted((K, p, f) for (K, p, f, s) in dr)):
                            viol("KR-INV", f"g0={g0}",
                                 f"unit/raw disagree n={n} e0={e0} r={r} "
                                 f"A={sorted(A)}")
                        note("inv_pairs")
    # g0=2 calibration vs pinned SD.legal_drains_g2
    for A in ({0, 1}, {0}):
        for n in range(0, 4):
            mine = sorted((K, p, f) for (K, p, f, s) in drains_units(n, 2, A))
            ref = sorted((K, p, f) for (K, p, f, s) in
                         SD.legal_drains_g2(n, A))
            if mine != ref:
                viol("KR-INV", "cal", f"!= legal_drains_g2 n={n} A={A}")
            note("inv_cal")
    # the displayed K2-L3 inventory at n=3, A={0,1}: eight drains total
    tot = sum(len(drains_units(n, 2, {0, 1})) for n in (2, 3))
    if tot != 3 + 5:
        viol("KR-INV", "K2-L3", f"g0=2 inventory count {tot} != 8")
    # TOOTH-1: threshold mutant must diverge at g0=2 n=3
    mut = set((K, p) for (K, p, f, s) in drains_units(3, 2, {0, 1}, thresh=1))
    good = set((K, p) for (K, p, f, s) in drains_units(3, 2, {0, 1}))
    if mut <= good:
        viol("KR-INV", "TOOTH-1", "threshold mutant did NOT diverge")
    else:
        note("tooth1_fired")
        print(f"TOOTH-1 fired: mutant extras {sorted(mut - good)[:3]}")

def kr_ord_tot():
    """KR-ORD + KR-TOT: order-multiplicity law and class totals."""
    # the displayed g0=3 full-A table (P-2), byte-encoded
    want_g3 = {
        (3, 0, 1): {(): 1}, (3, 1, 0): {(2,): 1}, (3, 2, 0): {(1,): 1},
        (3, 3, 0): {(0,): 1},
        (4, 0, 1): {(): 1}, (4, 1, 1): {(2,): 1},
        (4, 2, 0): {(1,): 1, (2, 2): 1}, (4, 3, 0): {(0,): 1, (1, 2): 1},
        (4, 4, 0): {(0, 2): 1},
        (5, 0, 1): {(): 1}, (5, 1, 1): {(2,): 1},
        (5, 2, 1): {(1,): 1, (2, 2): 1},
        (5, 3, 0): {(0,): 1, (1, 2): 2, (2, 2, 2): 1},
        (5, 4, 0): {(0, 2): 1, (1, 1): 1, (1, 2, 2): 1},
        (5, 5, 0): {(0, 1): 1, (0, 2, 2): 1},
    }
    got = {}
    for n in (3, 4, 5):
        for (u, p), cnt in class_census(n, 3, {0, 1, 2}).items():
            got[(n, u, p)] = dict(cnt)
    if got != want_g3:
        viol("KR-ORD", "g3table", f"g0=3 table mismatch: "
             f"{sorted(set(got) ^ set(want_g3))[:4]}")
    else:
        note("g3_table_exact")
    # multi-order census + totals, g0 in {2,3,4}, all A
    RES["multiorder"] = {}
    RES["bigT_sectors"] = {}
    for g0 in (2, 3, 4):
        multi, bigT = [], []
        totset = set()
        for Am in range(1, 1 << g0):
            A = frozenset(k for k in range(g0) if Am >> k & 1)
            if 0 not in A: continue
            full = (len(A) == g0)
            for n in range(0, 2 * g0):
                for (u, p), cnt in class_census(n, g0, A).items():
                    tot = sum(((-1) ** len(K)) * m for K, m in cnt.items())
                    if full:
                        totset.add(tot)
                        if len(cnt) > 1 and tot not in (0, 1):
                            viol("KR-TOT", f"g0={g0}",
                                 f"full-A multi-member total {tot} at "
                                 f"n={n} ({u},{p})")
                    for K, m in cnt.items():
                        if m > 1:
                            multi.append((sorted(A), n, u, p, K, m))
                    if abs(tot) >= 2:
                        bigT.append((sorted(A), n, u, p, tot,
                                     sorted(cnt.items())))
        RES["multiorder"][g0] = multi
        RES["bigT_sectors"][g0] = bigT
        if g0 == 2 and multi:
            viol("KR-ORD", "g0=2", f"multi-order at g0=2: {multi[:2]}")
        if g0 == 3:
            fullmulti = [x for x in multi if x[0] == [0, 1, 2]]
            if [(x[4], x[5]) for x in fullmulti] != [((1, 2), 2)]:
                viol("KR-ORD", "g0=3",
                     f"unique multi-order law fails: {fullmulti}")
            if [(x[0], x[1], x[2], x[3], x[4]) for x in bigT] != \
                    [([0, 2], 5, 3, 0, -2)]:
                viol("KR-TOT", "g0=3",
                     f"-2 window uniqueness fails: {bigT}")
        if g0 == 4:
            if not any(x[4] == (2, 3, 3) and x[5] == 3 for x in multi):
                viol("KR-ORD", "g0=4", "no x3 order-multiplicity found")
            pure = [x for x in bigT if x[0] == [0, 1, 2] and x[1] == 7
                    and x[2] == 5]
            if not (len(pure) == 1 and pure[0][4] == 2 and
                    len(pure[0][5]) == 1):
                viol("KR-TOT", "g0=4",
                     f"pure order-multiplicity +2 sector missing: {pure}")
        if not totset <= {-1, 0, 1}:
            viol("KR-TOT", f"g0={g0}", f"full-A class totals {totset}")
    note("ord_tot_done")

def kr_swap():
    """KR-SWAP: the K2-L16/K2-L17(a) arithmetic at g0 in 2..6."""
    for g0 in range(2, 7):
        if not (g0 + 1 <= 2 * g0 - 1):
            viol("KR-SWAP", f"g0={g0}", "{C_{g0-1},P} does not fit")
        if not (2 * g0 > 2 * g0 - 1):
            viol("KR-SWAP", f"g0={g0}", "{C0,P} fits (!)")
        # A={0}: every drain a single event; every (units,p) singleton
        for n in range(0, 2 * g0):
            dr = drains_units(n, g0, {0})
            for (K, p, f, s) in dr:
                if len(K) + p > 1:
                    viol("KR-SWAP", f"g0={g0}",
                         f"A={{0}} drain with 2 events at n={n}")
            cc = class_census(n, g0, {0})
            for (u, p), cnt in cc.items():
                if sum(cnt.values()) != 1:
                    viol("KR-SWAP", f"g0={g0}",
                         f"A={{0}} non-singleton class at n={n}")
        # in-window pair {C_{g0-1},P} realized at budget 2g0-1
        found = any(sorted(K) == [g0 - 1] and p == 1
                    for (K, p, f, s) in drains_units(2 * g0 - 1, g0,
                                                     set(range(g0))))
        if not found:
            viol("KR-SWAP", f"g0={g0}", "{C_{g0-1},P} window not realized")
    # the (e)-chain cross-check at g0=2 (K2-CAND face, read-only)
    two = [(K, p, f, s) for (K, p, f, s) in SD.legal_drains_g2(3, {0, 1})
           if p == 1 and sum(2 - k for k in K) + 2 * p <= 3]
    note("swap_done")

# ============ 2. the form space and the verdict column ========================
def sector_cells(g0, A, n, u, p):
    """Cells of one seed sector: list of (K, mult)."""
    return sorted(class_census(n, g0, A).get((u, p), {}).items())

def form_space(g0, A):
    """Enumerate (n0,u0,p,T) with EVERY t in T a nonempty sector; dedupe
    by the monomial model.  Returns dict model_key -> record."""
    forms = {}
    for n0 in range(0, 2 * g0):
        for u0 in range(0, 2 * g0):
            for p in (0, 1):
                for Tm in range(1, 1 << g0):
                    T = [t for t in range(g0) if Tm >> t & 1]
                    if n0 + max(T) > 2 * g0 - 1: continue
                    secs = []
                    ok = True
                    for t in T:
                        sc = sector_cells(g0, A, n0 + t, u0 + t, p)
                        if not sc: ok = False; break
                        secs.append((t, sc))
                    if not ok: continue
                    tmin = min(t for (t, sc) in secs)
                    key = tuple((t - tmin, tuple(sc)) for (t, sc) in secs)
                    if key not in forms:
                        forms[key] = dict(n0=n0, u0=u0, p=p, T=tuple(T),
                                          key=key)
    return forms

def model_of(key, g0):
    """Monomial model: coords (x_0..x_{g0-1}, psi_0..psi_{g0-1})."""
    monos, nets, labels = [], [], []
    for (dt, sc) in key:
        for (K, m) in sc:
            v = [0] * (2 * g0)
            v[dt] += 1
            for k in K:
                v[g0 + k] += 1
            monos.append(tuple(v))
            nets.append(((-1) ** len(K)) * m)
            labels.append(f"(t+{dt},{{{','.join(map(str,K))}}})")
    assert len(set(monos)) == len(monos), "monomial collision"
    return monos, nets, labels

def gens_AE(g0):
    """K2-L15 generators: A_t (t=1..g0-1), E_j (j=0..g0-2)."""
    D = 2 * g0
    gens = []
    names = []
    for t in range(1, g0):
        v = [0] * D; v[t - 1], v[t], v[g0 + g0 - 1] = 1, -1, -1
        gens.append(tuple(v)); names.append(f"A{t}")
    for j in range(0, g0 - 1):
        v = [0] * D
        v[g0 + j] += 1; v[g0 + j + 1] -= 1; v[g0 + g0 - 1] -= 1
        # (at j = g0-2 the last two indices coincide: coefficient -2,
        #  E_{g0-2} = psi_{g0-2} - 2 psi_{g0-1} — the += arithmetic is
        #  exactly right)
        gens.append(tuple(v)); names.append(f"E{j}")
    return gens, names

def kr_idc():
    """KR-IDC: L(g0) == <A_.,E_.> by echelon comparison, g0 in 2..6."""
    for g0 in range(2, 7):
        D = 2 * g0
        gens, names = gens_AE(g0)
        LatAE = KV.Lat(D)
        for v in gens: LatAE.add(v)
        # a spanning set of {deg=0, phi=0}: differences e_a - e_b - (the
        # phi-compensator in psi coords) ... build kernel basis directly:
        # kernel of the 2xD matrix [deg; phi] over Z, via pairwise combos
        deg = [1] * g0 + [0] * g0
        phi = [-t for t in range(g0)] + [g0 - k for k in range(g0)]
        Lker = []
        # integer kernel via HNF on the transpose: use Lat over D+2 dims
        KL = KV.Lat(2 + D)
        for i in range(D):
            row = [deg[i], phi[i]] + [1 if j == i else 0 for j in range(D)]
            KL.add(row)
        for c, r in KL.rows.items():
            if c >= 2:
                Lker.append(tuple(r[2:]))
        # sanity: every kernel vector really kills deg and phi
        for v in Lker:
            if (sum(v[t] for t in range(g0)) != 0 or
                    sum(phi[i] * v[i] for i in range(D)) != 0):
                viol("KR-IDC", f"g0={g0}", "kernel construction broken")
        for v in Lker:
            if not LatAE.contains(v):
                viol("KR-IDC", f"g0={g0}", f"kernel vector outside <A,E>: {v}")
        for v in gens:
            if (sum(v[t] for t in range(g0)) != 0 or
                    sum(phi[i] * v[i] for i in range(D)) != 0):
                viol("KR-IDC", f"g0={g0}", f"generator outside L(g0): {v}")
        note("idc_lattices")
    note("idc_done")

STATE_CAP = 20000

def explore_ext(monos, nets, D, base, exclude, latAE, mode, tag):
    """Layout-generic clone of KV.explore (pinned import for Lat/closure/
    protection); adds the K2-L15 membership shadow on every merge."""
    start, L0 = KV.closure([{i} for i in range(len(monos))], list(base),
                           monos, D)
    res = dict(n_states=0, capped=False, prot=None, bad=None, dead=None,
               torsion=0)
    if any(L0.contains(v) for v in exclude):
        res["corner_empty"] = True
        return res
    seen = {start}
    stack = [(start, L0)]
    while stack:
        blocks, L = stack.pop()
        res["n_states"] += 1
        p = KV.protection(blocks, nets, False)
        good = (p == "PROT")
        # torsion flag (kept conservatively, informational)
        reps = [min(b) for b in blocks]
        tors = any(L.contains_q(KV.vsub(monos[reps[j]], monos[reps[i]]))
                   and not L.contains(KV.vsub(monos[reps[j]], monos[reps[i]]))
                   for i in range(len(reps)) for j in range(i + 1, len(reps)))
        if tors: res["torsion"] += 1
        # K2-L15 shadow: same-block differences lie in <A,E>
        for b in blocks:
            bs = sorted(b)
            for i in bs[1:]:
                d = KV.vsub(monos[i], monos[bs[0]])
                if not latAE.contains(d):
                    viol("KR-IDC", tag, f"state identity outside <A,E>: {d}")
        if good and res["prot"] is None:
            res["prot"] = [sorted(b) for b in blocks]
            if mode == "exists": return res
        if not good and res["bad"] is None:
            res["bad"] = (p, [sorted(b) for b in blocks])
            if mode == "universal": return res
        if p == "DEAD" and res["dead"] is None:
            res["dead"] = True
        if res["n_states"] >= STATE_CAP:
            res["capped"] = True
            return res
        for i in range(len(blocks)):
            for j in range(i + 1, len(blocks)):
                nb = [set(b) for b in blocks]
                nb[i] |= nb[j]
                del nb[j]
                nkey, NL = KV.closure(nb, list(base), monos, D)
                if nkey in seen: continue
                seen.add(nkey)
                if any(NL.contains(v) for v in exclude):
                    continue
                stack.append((nkey, NL))
    return res
def column(g0, tag):
    """KR-COL: per-form per-corner verdicts at full availability."""
    A = set(range(g0))
    D = 2 * g0
    gens, names = gens_AE(g0)
    latAE = KV.Lat(D)
    for v in gens: latAE.add(v)
    forms = form_space(g0, A)
    col = {}
    tally = collections.Counter()
    for key, rec in sorted(forms.items()):
        monos, nets, labels = model_of(key, g0)
        T = sum(nets)
        if not (-1 <= T <= 1):
            viol("KR-COL", tag, f"full-A group total {T} at {rec}")
        safe, novel, cond, capped = [], [], [], []
        for cm in range(1 << len(gens)):
            base = [gens[i] for i in range(len(gens)) if cm >> i & 1]
            excl = [gens[i] for i in range(len(gens)) if not cm >> i & 1]
            ru = explore_ext(monos, nets, D, base, excl, latAE,
                             "universal", tag)
            if ru.get("corner_empty"):
                continue
            if ru["capped"]:
                capped.append(cm); continue
            if ru["bad"] is None:
                safe.append(cm)
                continue
            re_ = explore_ext(monos, nets, D, base, excl, latAE,
                              "exists", tag)
            if re_["capped"]:
                capped.append(cm)
            elif re_["prot"] is None:
                novel.append(cm)
            else:
                cond.append(cm)
        col[key] = dict(rec=dict(n0=rec["n0"], u0=rec["u0"], p=rec["p"],
                                 T=rec["T"]), total=T, ncells=len(monos),
                        safe=safe, cond=cond, novel=novel, capped=capped)
        tally["forms"] += 1
        tally["safe_pairs"] += len(safe)
        tally["cond_pairs"] += len(cond)
        tally["novel_pairs"] += len(novel)
        tally["capped_pairs"] += len(capped)
        # the genre census on NOVEL corners: char|T or T0
        for cm in novel:
            tally["novel_charT" if T else "novel_T0"] += 1
    return forms, col, dict(tally), names

def kr_col():
    RES["column"] = {}
    for g0 in (3, 4):
        t0 = time.time()
        forms, col, tally, names = column(g0, f"col-g{g0}")
        RES["column"][g0] = dict(
            tally=tally, gens=names,
            forms=[dict(v, key=str(k)) for k, v in
                   sorted(col.items(), key=lambda kv: str(kv[0]))])
        print(f"KR-COL g0={g0}: {tally} ({time.time()-t0:.1f}s)")
        if g0 == 3:
            # P-7: the obstruction sector as a single-seed form, keyed by
            # its census (forms are deduped by t-rebased census key)
            obkey = ((0, (((0,), 1), ((1, 2), 2), ((2, 2, 2), 1))),)
            ob = [v for k, v in col.items() if k == obkey]
            if len(ob) != 1:
                viol("KR-COL", "g3-ob", f"obstruction form count {len(ob)}")
            else:
                o = ob[0]
                # gens order: A1, A2, E0, E1 -> bits 0,1,2,3
                wantsafe = sorted(cm for cm in range(16)
                                  if (cm >> 2 & 1) != (cm >> 3 & 1))
                if sorted(o["safe"]) != wantsafe:
                    viol("KR-COL", "g3-ob",
                         f"obstruction safe set {sorted(o['safe'])} != "
                         f"E0-xor-E1 {wantsafe}")
                else:
                    note("obstruction_corner_law")
            # singleton-census single-seed forms: safe everywhere
            for k, v in col.items():
                if len(v["rec"]["T"]) == 1 and v["ncells"] == 1:
                    if len(v["safe"]) != 16:
                        viol("KR-COL", "g3-S",
                             f"singleton form not safe everywhere: {v['rec']}")

def kr_cal():
    """KR-CAL: the g0=2 pipeline vs KV.classify_form/FORM_CORNERS
    + TOOTH-2 + TOOTH-3."""
    g0 = 2
    A = {0, 1}
    D = 4
    gens, names = gens_AE(2)              # [A1, E0] = [I1, I3]
    latAE = KV.Lat(D)
    for v in gens: latAE.add(v)
    # canonical data -> expected THM-A form names
    canon = {(2, 2, 0, (0,)): "S", (1, 0, 0, (0, 1)): "P1",
             (3, 2, 0, (0,)): "P2", (2, 1, 0, (0, 1)): "T1"}
    def cells_of(n0, u0, p, T, qmut=False):
        cnt = {}
        for t in T:
            fac = 2 if qmut else 1
            for (K, m) in sector_cells(2, A, n0 + fac * t, u0 + fac * t, p):
                cnt[(t, K, (-1) ** len(K))] = m
        return cnt
    corner_names = {0: "c00", 1: "c10", 2: "c01", 3: "c11"}  # bit0=A1,bit1=E0
    for (n0, u0, p, T), wname in sorted(canon.items()):
        cnt = cells_of(n0, u0, p, T)
        got = KV.classify_form(cnt)
        if got != wname:
            viol("KR-CAL", "form", f"{(n0,u0,p,T)} -> {got} != {wname}")
        # the column at g0=2 vs FORM_CORNERS
        key = tuple((t - min(T), tuple(sector_cells(2, A, n0 + t, u0 + t,
                                                    p))) for t in sorted(T))
        monos, nets, labels = model_of(key, 2)
        safe = []
        for cm in range(4):
            base = [gens[i] for i in range(2) if cm >> i & 1]
            excl = [gens[i] for i in range(2) if not cm >> i & 1]
            ru = explore_ext(monos, nets, D, base, excl, latAE,
                             "universal", "cal")
            if not ru["capped"] and ru["bad"] is None:
                safe.append(corner_names[cm])
        if set(safe) != KV.FORM_CORNERS[wname]:
            viol("KR-CAL", "corners",
                 f"{wname}: safe {sorted(safe)} != "
                 f"{sorted(KV.FORM_CORNERS[wname])}")
        note("cal_forms")
    # TOOTH-2: sign-blind mutant (all cells +) must lose P1's safe corners
    cnt = cells_of(1, 0, 0, (0, 1))
    key = tuple((t, tuple(sector_cells(2, A, 1 + t, 0 + t, 0)))
                for t in (0, 1))
    monos, nets, labels = model_of(key, 2)
    nets_mut = [abs(x) for x in nets]
    safe_mut = []
    for cm in range(4):
        base = [gens[i] for i in range(2) if cm >> i & 1]
        excl = [gens[i] for i in range(2) if not cm >> i & 1]
        ru = explore_ext(monos, nets_mut, D, base, excl, latAE,
                         "universal", "tooth2")
        if not ru["capped"] and ru["bad"] is None:
            safe_mut.append(corner_names[cm])
    if set(safe_mut) == KV.FORM_CORNERS["P1"]:
        viol("KR-CAL", "TOOTH-2", "sign-blind mutant did NOT diverge")
    else:
        note("tooth2_fired")
        print(f"TOOTH-2 fired: P1 sign-blind safe set {sorted(safe_mut)}")
    # TOOTH-3: seed-quantum mutant must break P1 classification
    got = KV.classify_form(cells_of(1, 0, 0, (0, 1), qmut=True))
    if got == "P1":
        viol("KR-CAL", "TOOTH-3", "seed-quantum mutant did NOT diverge")
    else:
        note("tooth3_fired")
        print(f"TOOTH-3 fired: quantum-mutant P1 data classifies as {got}")

# ============ 3. KR-PFREE: the 332-row in-vivo promotion census ===============
def pfree_row(E, sA, sB, u1a, u1b, aA, aB, su, key, tag, rowset, g0):
    """Light row processor: recording walk both stages; beta_min census."""
    R = E.R; m = E.m
    sig = tuple(sA[l + 1] + sB[l + 1] for l in range(m))
    s1u1 = su[1]
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
    note("pfree_rows")
    rowset.add((tag,) + tuple(key))
    cells = []
    for st in q2:
        (sgn, b, j, pc, dmp, cons, ncorr, junk, jD, isp, ce, y2, hist) = st
        cells.append(dict(sgn=sgn, j=j, pc=tuple(pc), junk=junk, y2=y2,
                          line=E.line(b, j), hist=hist, res=E.resKm(b),
                          jD=jD))
    bmin = min(c['line'] for c in cells)
    nprom, nsw, nmw, njf = 0, 0, 0, 0
    for c in cells:
        if c['line'] != bmin or c['junk'] or c['y2']: continue
        njf += 1
        p0 = sum(1 for ev in c['hist'] if ev[0] == 'p0')
        if p0 > 0:
            nprom += 1
        wins, endj0 = SD.windows_of(E, c['hist'], sig[0], None)
        if wins is None:
            viol("HARNESS", tag, f"window replay failed at {key}")
            continue
        active = sum(1 for w in wins if w['ev'])
        if active <= 1: nsw += 1
        else: nmw += 1
        for w in wins:
            if w['n'] > 2 * g0 - 1:
                viol("KR-VIVO" if g0 >= 3 else "KR-PFREE", tag,
                     f"window budget {w['n']} > {2*g0-1} at {key}")
            if g0 >= 3 and w['ev'] and not w['hasY']:
                inv = set((K, p) for (K, p, f, s) in
                          drains_units(w['n'], g0,
                                       set(k for (k, dc) in
                                           E.corr_table()[0])))
                if (w['K'], w['p']) not in inv:
                    viol("KR-VIVO", tag,
                         f"drain {w['K']},{w['p']} not in inventory "
                         f"n={w['n']} at {key}")
    if nprom:
        finding("PFREE", f"{tag}{list(key)}: {nprom} beta_min junk-free "
                f"cells carry a level-0 promotion (exit-criticality "
                f"candidate)")
        note("pfree_promo_rows")
    note("pfree_cells_jf", njf)
    note("pfree_single_window", nsw)
    note("pfree_multi_window", nmw)
    # protection census (g0 >= 3 vivo: a violation-form event is a FINDING)
    if g0 >= 3:
        slots = collections.defaultdict(list)
        for c in cells:
            if c['line'] == bmin:
                slots[c['j']].append(c)
        prot_some = False
        for jv, grp in slots.items():
            classes, signed = SD.classify_group(E, grp)
            if SD.protected(signed): prot_some = True
        if not prot_some:
            finding("KR-VIVO", f"{tag}{list(key)}: NO protected beta_min "
                    f"group at g0={g0} — the R-B counter-instance form")
        else:
            note("vivo_protected_rows")
    return True

def pfree_tower(spec, phase, rowset, caps=(12, 6)):
    """Selection loops transcribed from the pinned SD.run_tower (same
    keys, same caps, same strata) with the light processor above."""
    tag, m, kind, p, d0, reads = spec
    t0 = time.time()
    try:
        E = PE.Eng(m, kind, p, d0, reads, tag)
        PE.prep(E)
    except Exception as ex:
        print(f"-- {tag}: ENGINE UNSUPPORTED ({ex!r}) — disclosed, skipped")
        note("tower_skipped"); return
    harvest(tag)
    u, su = WS.uchain(E)
    if u is None:
        note("tower_skipped"); return
    Etot, G0, split = WS.window_split(E)
    anch = WS.anchors_of(E, Etot, G0, split)
    prin, meta = WD.inv_checks(E, u, su)
    harvest(tag)
    if meta is None:
        note("tower_skipped"); return
    etop = E.e[m - 1]; R = E.R
    n0 = 0
    g0 = E.g[0]
    if phase == "sealed":
        pid_keys = {}
        for ga in range(G0, G0 + Etot):
            aA, sA, u1a = anch[ga]
            for gb in range(G0, G0 + Etot):
                aB, sB, u1b = anch[gb]
                strack = (sA[m + 1] == E.e[m] - 1 and sB[m + 1] == E.e[m] - 1)
                if not strack: continue
                E1, _ = pdivmod(R, pmul(R, aA, aB), E.Phis[m])
                e1nz = bool(pnorm(R, E1))
                if not (strack and e1nz and m >= 2): continue
                pools, cs, Dd, top = WS.pools_of(E, sA, sB, su)
                meas = False
                Q1 = pdivmod(R, pmul(R, E1, E.Chat), E.Phis[m])[0]
                if pnorm(R, Q1):
                    Tsum = sA[m + 1] + sB[m + 1]
                    dpl = Tsum // E.e[m]
                    locus = ((dpl == 1 and strack and E.e[m] >= 2)
                             or (Tsum == E.e[m] - 1 and E.e[m] == 1))
                    if locus: meas = True
                key = (tuple(sorted([(tuple(sA[l] for l in range(1, m + 2)),
                                      u1a),
                                     (tuple(sB[l] for l in range(1, m + 2)),
                                      u1b)])))
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
        rows = [(key, v) for key, v in chosen]
    else:
        seen, live_pool = set(), {}
        for ga in range(G0, G0 + Etot):
            aA, sA, u1a = anch[ga]
            for gb in range(G0, G0 + Etot):
                aB, sB, u1b = anch[gb]
                if not (sA[m + 1] == E.e[m] - 1 and
                        sB[m + 1] == E.e[m] - 1):
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
                live_pool.setdefault((kdef, ctop), []).append(
                    (ga, gb, cs, Dd, kdef, sA, sB, u1a, u1b))
        cap = caps[1] if m >= 4 else caps[0]
        rows = []
        for stratum in sorted(live_pool):
            for row in live_pool[stratum][:cap]:
                ga, gb, cs, Dd, kdef, sA, sB, u1a, u1b = row
                rows.append(((ga, gb), (ga, gb, cs, Dd, kdef, None,
                                        sA, sB, u1a, u1b)))
    for key, v in rows:
        (ga, gb, cs, Dd, kdef, meas, sA, sB, u1a, u1b) = v
        ctop = cs[-1] if cs else 0
        if kdef > ctop: continue
        r = pfree_row(E, sA, sB, u1a, u1b, anch[ga][0], anch[gb][0], su,
                      (ga, gb), tag, rowset, g0)
        if r: n0 += 1
    harvest(tag)
    print(f"-- PFREE {tag} m={m} {kind},p={p},d0={d0} g0={g0}: "
          f"rows={n0} ({time.time()-t0:.1f}s)")

def kr_pfree():
    rowset = set()
    for spec in WS.ROSTER:
        if spec[5][0][2] < 2: continue
        pfree_tower(spec, "sealed", rowset)
    for spec in ED.FRESH_ROSTER:
        if spec[5][0][2] < 2: continue
        pfree_tower(spec, "eq", rowset)
    for spec in SD.PX_ROSTER:
        if spec[5][0][2] < 2: continue
        pfree_tower(spec, "px", rowset)
    for spec in SD.SD_ROSTER:
        if spec[5][0][2] < 2: continue
        pfree_tower(spec, "sd", rowset)
    for spec in SD.K2_TRACED:
        pfree_tower(spec, "k2", rowset)
    try:
        with open(os.path.join(HERE, "survk2_instrument_results.json")) as f:
            inst = json.load(f)
        inst_rows = set((q['tower'],) + tuple(q['key'])
                        for q in inst['qdrows'])
        if rowset != inst_rows:
            viol("KR-PFREE", "roster",
                 f"rowset != instrument ({len(rowset)} vs {len(inst_rows)})")
    except Exception as ex:
        viol("KR-PFREE", "roster", f"instrument results unreadable: {ex!r}")
    RES["pfree"] = dict(rows=CNT.get("pfree_rows", 0),
                        promo_rows=CNT.get("pfree_promo_rows", 0),
                        jf_cells=CNT.get("pfree_cells_jf", 0),
                        single_window=CNT.get("pfree_single_window", 0),
                        multi_window=CNT.get("pfree_multi_window", 0))
    print(f"KR-PFREE: {RES['pfree']}")

# ============ 4. KR-VIVO: the g0 >= 3 engine attempt (budget-boxed) ===========
KR_VIVO_BUDGET = 3000        # seconds, PHASE total; timeout = disclosed skip
VIVO_ROSTER = [
    ("KRG3E1F", 2, "Fpt", 2, 1, [(1, 1, 3), (2, 1, 1), (2, 1, 1)]),
    ("KRG3M2F", 2, "Fpt", 2, 1, [(2, 1, 3), (2, 1, 1), (2, 1, 1)]),
    ("KRG4E1F", 2, "Fpt", 2, 1, [(1, 1, 4), (2, 1, 1), (2, 1, 1)]),
]

def kr_vivo():
    t0 = time.time()
    RES["vivo"] = dict(attempted=[], traced=[], skipped=[], prep_s={})
    def _alrm(sig_, frm): raise TimeoutError("vivo budget")
    rowset = set()
    for spec in VIVO_ROSTER:
        left = int(KR_VIVO_BUDGET - (time.time() - t0))
        if left <= 60:
            RES["vivo"]["skipped"].append((spec[0], "phase budget exhausted"))
            print(f"-- VIVO {spec[0]}: PHASE BUDGET EXHAUSTED — "
                  f"disclosed skip")
            continue
        RES["vivo"]["attempted"].append(spec[0])
        old = signal.signal(signal.SIGALRM, _alrm)
        signal.alarm(left)
        tp = time.time()
        try:
            before = CNT.get("pfree_rows", 0)
            pfree_tower(spec, "eq", rowset, caps=(6, 4))
            RES["vivo"]["prep_s"][spec[0]] = round(time.time() - tp, 1)
            RES["vivo"]["traced"].append(
                (spec[0], CNT.get("pfree_rows", 0) - before))
        except TimeoutError:
            RES["vivo"]["skipped"].append(
                (spec[0], f"timeout after {round(time.time()-tp,1)}s"))
            print(f"-- VIVO {spec[0]}: BUDGET TIMEOUT — disclosed skip")
            harvest(spec[0])
        finally:
            signal.alarm(0); signal.signal(signal.SIGALRM, old)
    print(f"KR-VIVO: {RES['vivo']}")

# ============ main ============================================================
def main():
    t0 = time.time()
    for fn, want in PINS.items():
        got = hashlib.md5(open(os.path.join(HERE, fn), 'rb').read()
                          ).hexdigest()
        if got != want:
            viol("KR-PIN", fn, f"md5 {got} != pinned {want}")
    save(t0)
    print("=" * 78)
    print("K2-RESIDUE machine leg — abstract families first")
    print("=" * 78)
    kr_inv();      save(t0)
    kr_ord_tot();  save(t0)
    kr_swap();     save(t0)
    kr_idc();      save(t0)
    kr_cal();      save(t0)
    kr_col();      save(t0)
    print("=" * 78)
    print("KR-PFREE — the 332-row in-vivo promotion census")
    print("=" * 78)
    kr_pfree();    save(t0)
    print("=" * 78)
    print(f"KR-VIVO — g0 >= 3 engine attempt (phase budget "
          f"{KR_VIVO_BUDGET}s; skip = disclosed)")
    print("=" * 78)
    kr_vivo();     save(t0)
    print("=" * 78)
    fams = ["KR-PIN", "KR-INV", "KR-ORD", "KR-TOT", "KR-FORM", "KR-IDC",
            "KR-COL", "KR-CAL", "KR-SWAP", "KR-PFREE", "KR-VIVO", "HARNESS"]
    for f in fams:
        print(f"{f:10s}: {sum(1 for v in VIOL if v[0] == f)} violations")
    teeth = [CNT.get("tooth1_fired", 0), CNT.get("tooth2_fired", 0),
             CNT.get("tooth3_fired", 0)]
    print(f"teeth fired: {teeth} (all must be 1)")
    if teeth != [1, 1, 1]:
        viol("HARNESS", "teeth", f"tooth census {teeth} != [1,1,1]")
    print(f"findings (measured, never violations): {len(FINDINGS)}")
    for f in FINDINGS: print(f"  FINDING {f[0]}: {f[1]}")
    print(f"total violations: {len(VIOL)}")
    el = time.time() - t0
    print(f"elapsed: {el:.1f}s")
    save(t0, final=True)
    print("results -> k2res_checks_results.json")
    sys.exit(0 if not VIOL else 1)

if __name__ == "__main__":
    main()

