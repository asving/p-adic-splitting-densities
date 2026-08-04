#!/usr/bin/env python3
"""survk2_derive_checks.py — (SURV-K2) COMPOSER unit machine leg (2026-08-08).

Derivation shadow for SURVK2_PROOF_2026-08-08.md: re-traces the instrument's
332 traced g0 >= 2 live rows (union g0>=2 selection replicated verbatim +
the two traced K2 towers; the ten g0 >= 3 towers are excluded up front —
the instrument's measured engine cost wall, disclosed skip) with a RECORDING
walk (event history -> level-0 window decomposition), cross-checked EXACTLY
against the committed ED.walk, and verifies the note's displayed lemmas
cellwise:

  K2-PIN     md5 pins (engines + instrument runner + instrument results).
  K2-XWALK   recording walk == ED.walk (terminal multiset, both stages).
  K2-CONS    stage sums = E1IH / Q1.
  K2-WIN     window decomposition: every level-0 event at j0 >= P0; window
             budgets n <= 2g0-1 (=3 at g0=2); drains end < P0; at g0=2 the
             realized drain is IN the displayed legal inventory and is the
             UNIQUE legal order of its (K, p) multiset in its budget;
             arrival bounds (root sigma1 <= 2(e0-1) < P0; s1(u1) <= e0-1;
             dumps <= P0-1).
  K2-FACT    junk-free two-exit cells: res = res(cD_t) * prod res(digits),
             w0 = (u0 - t*h0) + sum w0(digits), sgn = (-1)^{#ce}.
  K2-NU      nu := t - M_K constant per (slot, line, book) fiber.
  K2-JBOT    every beta_min cell junk-free and Y-free (W-D5 shadow, any d0).
  K2-COLOC   junk-free cells: line is a function of the promotion totals pc
             (W-D5: line = lambda-hat + sum pi_l q_l), per row.
  K2-FIB     beta_min fiber completeness: each bottom (slot, book, p-vec)
             fiber equals its chain enumeration (all legal level-0
             placements with the same arrivals, per-window promos, total
             mass, final parked state, over available seeds) — the
             involution's domain is complete in vivo.
  K2-CHAIN   per-(fiber, seed) signed count in {-1,0,+1} (fixed-book
             seedbound); fiber branch census (exchange vs placement).
  K2-REG     row classification: REG := every bottom group single-book,
             single-family, table shape (S1)/(S2) with A = {0,1} both
             available; THM-A shadow: every REG row protected.
  K2-PROT    every traced row: some bottom-line group protected (SD-L7
             predicate) — a violation is a (SURV-K2) counterexample.
  K2-CAND    displayed failure-candidate arithmetic confirmed abstractly:
             (a) the g0=2 placement-pair chain nets -2 (integer level);
             (b) the g0=3 n=5 window: {C0} & {C2^3} both sign '-' (count
             -2) and the {C2,C1} order-multiplicity; (c) census: 0
             realized instances of either shape at beta_min on the roster.
  HARNESS    engine violations; roster equality vs the instrument.

Deterministic, exact arithmetic, engines read-only.  Usage:
    python3 survk2_derive_checks.py [outdir]
"""
import sys, os, time, json, hashlib, collections, itertools

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
OUTDIR = sys.argv[1] if len(sys.argv) > 1 else HERE

import wmultdcx_stress as WS
import wmultdcx_derive_checks as WD
import rmengine_pe_reimpl as PE
import empty_derive_checks as ED
from grb_order2_check import pnorm, padd, pneg, pmul, pscal, pdivmod, w0

VIOL, CNT = [], {}
def note(f, n=1): CNT[f] = CNT.get(f, 0) + n
def viol(fam, tag, detail):
    VIOL.append((fam, tag, detail)); print(f"VIOLATION [{fam}] {tag}: {detail}")

def harvest(tag):
    for src, lst in (("PE", PE.VIOL), ("ED", ED.VIOL), ("WS", WS.VIOL),
                     ("WD", WD.VIOL)):
        while len(lst) > harvest.seen[src]:
            v = lst[harvest.seen[src]]
            if "tree cap exceeded" in str(v):
                note("row_treecap")
            else:
                viol("HARNESS", tag, f"{src}: {v}")
            harvest.seen[src] += 1
harvest.seen = {"PE": 0, "ED": 0, "WS": 0, "WD": 0}

PINS = {
    "wmultdcx_stress.py":        "15315cca59c87e6c2001ea744c50aab5",
    "wmultdcx_derive_checks.py": "bea1a43d619a3c91a9a0b2f32c0920c0",
    "rmengine_pe_reimpl.py":     "103c1a9c99e2b4a3e8b63c93cbf87e25",
    "grb_order2_check.py":       "dab62713175363a7185211890019ae2f",
    "empty_derive_checks.py":    "8fed92402bcffe6e0c536f1f9d847612",
    "surv_derive_checks.py":     "2365289e1f925404e66c8ce2b3e827ed",
    "surv_pe1_ext.py":           "937317c75fb381eec96b59b8a1f743ad",
    "survdisj_instrument.py":    "3df33c7406913510ed7ebaa60d480b57",
    "survk2_instrument.py":      "389b1db9fc0266a12db74e021d7d51c9",
    "survk2_instrument_results.json": "1ac516df8292ac5d57a88e430de3d1e4",
}

# ---------------- the RECORDING walk (shadow of ED.walk + event history) ------
# state: (sign, b, j, pc, dmp, cons, ncorr, junk, jD, prin, ce, y2, hist)
# hist events: ('c0', k) level-0 correction | ('p0',) level-0 promotion |
#   ('ci', i, k, avec, dj0) interior correction (its dump = arrival) |
#   ('pi', l) promotion out of level l >= 1 | ('exit',) | ('seed', add0)
def walk_rec(E, cells, qsink, tag):
    R = E.R; m = E.m
    corr = E.corr_table()
    stack = list(cells)
    nodes = 0
    while stack:
        st = stack.pop()
        (sign, b, j, pc, dmp, cons, ncorr, junk, jD, prin, ce, y2, hist) = st
        nodes += 1
        if nodes > ED.TREE_CAP:
            viol("HARNESS", tag, "rec-walk tree cap exceeded")
            return None
        i = next((l for l in range(m) if j[l] >= E.P[l]), None)
        if i is None:
            continue_leaf = st
            # leaf: nothing (stage-1 leaves / stage-2 leaves are remainders)
            continue
        if i <= m - 2:
            j2 = list(j); j2[i] -= E.P[i]; j2[i + 1] += 1
            pc2 = list(pc); pc2[i] += 1
            cn2 = list(cons); cn2[i] += E.P[i]
            ev = ('p0',) if i == 0 else ('pi', i)
            stack.append((sign, b, tuple(j2), tuple(pc2), dmp, tuple(cn2),
                          ncorr, junk, jD, prin, ce, y2, hist + (ev,)))
        else:
            j2 = list(j); j2[m - 1] -= E.P[m - 1]
            pc2 = list(pc); pc2[m - 1] += 1
            cn2 = list(cons); cn2[m - 1] += E.P[m - 1]
            qsink.append((sign, b, tuple(j2), tuple(pc2), dmp, tuple(cn2),
                          ncorr, junk, jD, prin, ce, y2, hist + (('exit',),)))
        for (k, dcells) in corr[i]:
            base = list(j); base[i] -= E.P[i] - E.e[i] * k
            cn2 = list(cons); cn2[i] += E.P[i] - E.e[i] * k
            nc2 = list(ncorr); nc2[i] += 1
            for (cd, av) in dcells:
                Lc, Xc, Yc = E.digit_split(b, cd)
                nj = list(base); nd = list(dmp)
                for l in range(min(i, len(av))):
                    nj[l] += av[l]; nd[l] += av[l]
                avec = tuple((av[l] if l < len(av) else 0) for l in range(i))
                for (cc, jtag, dj0) in ((Lc, 0, 0), (Xc, 1, 0), (Yc, 1, 1)):
                    if not pnorm(R, cc): continue
                    jj = list(nj); jj[0] += dj0
                    dd = list(nd); dd[0] += dj0
                    ce2 = ce + ((i, k, avec, dj0),)
                    ev = (('c0', k, dj0) if i == 0
                          else ('ci', i, k, avec, dj0))
                    stack.append((-sign, cc, tuple(jj), pc, tuple(dd),
                                  tuple(cn2), tuple(nc2), junk + jtag,
                                  jD, prin, ce2, y2, hist + (ev,)))
    return qsink

def fingerprint(st):
    """Order-insensitive terminal fingerprint for XWALK comparison."""
    sgn, b, j, pc, dmp, cons, ncorr, junk, jD, prin, ce, y2 = st[:12]
    return (sgn, tuple(map(tuple, [[c for c in b]])) if False else str(b),
            j, pc, dmp, cons, tuple(ncorr), junk,
            jD if jD is None else tuple(jD), tuple(ce), y2)

# ---------------- window decomposition ----------------------------------------
def windows_of(E, hist, j0_start, seed_add):
    """Replay the level-0 exponent through hist; segment into windows.
    Returns (windows, ok).  Window = dict(nstart_units, events [(kind,k)],
    p (promos), K (level-0 corr multiset), f_units_end, arrival)."""
    P0, e0, g0 = E.P[0], E.e[0], E.g[0]
    j0 = j0_start
    wins = []
    cur = dict(arrival=j0_start, kind='root', j0open=j0, ev=[], K=[], p=0, hasY=False)
    def close():
        wins.append(dict(n=cur['j0open'] // e0, kind=cur['kind'],
                         ev=tuple(cur['ev']), K=tuple(sorted(cur['K'])),
                         p=cur['p'], fu=j0 // e0, arrival=cur['arrival'],
                         j0open=cur['j0open'], j0close=j0,
                         hasY=cur['hasY']))
    for ev in hist:
        if ev[0] == 'c0':
            k, ydj = ev[1], ev[2]
            if j0 < P0: return None, f"c0 fired at j0={j0} < P0"
            cur['ev'].append(('c', k)); cur['K'].append(k)
            if ydj: cur['hasY'] = True
            j0 -= P0 - e0 * k - ydj
        elif ev[0] == 'p0':
            if j0 < P0: return None, f"p0 fired at j0={j0} < P0"
            cur['ev'].append(('p',)); cur['p'] += 1
            j0 -= P0
        elif ev[0] == 'ci':
            _, i, k, avec, dj0 = ev
            add = (avec[0] if len(avec) >= 1 else 0) + dj0
            if add > 0:
                close()
                j0 += add
                cur = dict(arrival=add, kind='dump', j0open=j0, ev=[], K=[],
                           p=0, hasY=False)
        elif ev[0] == 'seed':
            add = ev[1]
            close()
            j0 += add
            cur = dict(arrival=add, kind='seed', j0open=j0, ev=[], K=[], p=0,
                       hasY=False)
        # ('pi', l) and ('exit',) do not touch level 0
    close()
    return wins, j0

# legal drains at g0 = 2 in units: events at u >= 2; C1 = 1 unit, C0 = promo = 2
def legal_drains_g2(n, avail):
    """Enumerate legal drain SEQUENCES from n units.  Returns list of
    (K_multiset_sorted, p, f_units, seq)."""
    out = []
    def rec(u, K, p, seq):
        if u <= 1:
            out.append((tuple(sorted(K)), p, u, tuple(seq)))
            return
        if 1 in avail: rec(u - 1, K + [1], p, seq + [('c', 1)])
        if 0 in avail: rec(u - 2, K + [0], p, seq + [('c', 0)])
        rec(u - 2, K, p + 1, seq + [('p',)])
    rec(n, [], 0, [])
    return out

# ---------------- d-cell / digit lookup ---------------------------------------
def build_maps(E):
    dmap = {}
    for i, row in enumerate(E.corr_table()):
        for (k, dcells) in row:
            for (cd, av) in dcells:
                avec = tuple((av[l] if l < len(av) else 0) for l in range(i))
                dmap[(i, k, avec)] = cd
    Dmap = {tuple(jD): cD for (cD, jD) in E.Dcells}
    return dmap, Dmap

# ---------------- SD-L7 protection predicate ----------------------------------
def classify_group(E, grp):
    classes = []
    for c in grp:
        for cl in classes:
            if E.keq(cl[0], c["res"]):
                cl[1] += (1 if c["sgn"] > 0 else 0)
                cl[2] += (1 if c["sgn"] < 0 else 0)
                cl[3].append(c); break
        else:
            classes.append([c["res"], int(c["sgn"] > 0), int(c["sgn"] < 0), [c]])
    signed = [cl[1] - cl[2] for cl in classes]
    return classes, signed

def protected(signed):
    nz = [s for s in signed if s != 0]
    return (len(nz) == 1 and abs(nz[0]) == 1) or (sorted(nz) == [-1, 1])

# ---------------- one traced row ----------------------------------------------
def trace_row(E, sA, sB, u1a, u1b, aA, aB, su, cs, Dd, kdef, key, prin,
              tag, p, kind, g0, dmap, Dmap, u0, rowset):
    R = E.R; m = E.m
    sig = tuple(sA[l + 1] + sB[l + 1] for l in range(m))
    # K2-WIN arrival bound (root): sigma1 <= 2(e0-1) < P0 at g0 >= 2
    if not (sig[0] <= 2 * (E.e[0] - 1) and sig[0] < E.P[0]):
        viol("K2-WIN", tag, f"root arrival sigma1={sig[0]} >= P0 at {key}")
    s1u1 = su[1]
    if not (0 <= s1u1 <= E.e[0] - 1):
        viol("K2-WIN", tag, f"s1(u1)={s1u1} not in [0, e0-1] at {key}")
    b0 = pscal(R, R["pi_pow"](u1a + u1b), [R["one"]])
    prodp = pmul(R, aA, aB)
    z = (0,) * m
    # ---- reference walk (committed ED.walk), stage 1
    init_ref = [(1, b0, sig, z, z, z, z, 0, None, False, (), 0)]
    q1_ref = []
    out = ED.walk(E, init_ref, q1_ref, tag)
    if out[0] is None: harvest(tag); return None
    # ---- recording walk, stage 1
    init_rec = [(1, b0, sig, z, z, z, z, 0, None, False, (), 0, ())]
    q1_rec = []
    r = walk_rec(E, init_rec, q1_rec, tag)
    if r is None: return None
    if (sorted(map(fingerprint, q1_ref)) !=
            sorted(fingerprint(st[:12]) for st in q1_rec)):
        viol("K2-XWALK", tag, f"stage-1 terminal mismatch at {key}")
        return None
    E1c, _ = pdivmod(R, prodp, E.Phis[m])
    if WD.cellsum(E, q1_ref) != pnorm(R, E1c):
        viol("K2-CONS", tag, f"stage-1 sum != E1IH at {key}")
    # ---- seeding (both walks)
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
    r = walk_rec(E, seed(q1_rec, True), q2_rec, tag)
    if r is None: return None
    if (sorted(map(fingerprint, q2_ref)) !=
            sorted(fingerprint(st[:12]) for st in q2_rec)):
        viol("K2-XWALK", tag, f"stage-2 terminal mismatch at {key}")
        return None
    Q1c = pdivmod(R, pmul(R, E1c, E.Chat), E.Phis[m])[0]
    if WD.cellsum(E, q2_ref) != pnorm(R, Q1c):
        viol("K2-CONS", tag, f"stage-2 sum != Q1 at {key}")
    harvest(tag)
    ctop = cs[-1] if cs else 0
    if kdef > ctop or not q2_rec:
        return None
    note("live_rows")
    rowset.add((tag,) + tuple(key))
    # ---------------- per-cell processing -------------------------------------
    cells = []
    for st in q2_rec:
        (sgn, b, j, pc, dmp, cons, ncorr, junk, jD, isp, ce, y2, hist) = st
        ln = E.line(b, j)
        t, rem = divmod(jD[0] - s1u1, E.e[0])
        if rem != 0 or not (0 <= t < g0):
            viol("K2-FACT", tag, f"seed t-decomposition fails at {key}")
            return None
        # window decomposition
        wins, endj0 = windows_of(E, hist, sig[0], None)
        if wins is None:
            viol("K2-WIN", tag, f"window replay failed at {key}: {endj0}")
            continue
        if endj0 != j[0]:
            viol("K2-WIN", tag, f"window replay j0 {endj0} != {j[0]} at {key}")
        for w in wins:
            if w['n'] > 2 * g0 - 1:
                viol("K2-WIN", tag,
                     f"window budget n={w['n']} > 2g0-1 at {key}")
            if w['j0close'] >= E.P[0]:
                viol("K2-WIN", tag, f"window did not drain at {key}")
            if g0 == 2 and w['ev'] and not w['hasY']:
                # realized drain must be in the legal inventory, and be the
                # unique legal order of its (K, p) in this budget
                drains = legal_drains_g2(w['n'], set(
                    k for (k, dc) in E.corr_table()[0]))
                match = [d for d in drains if d[3] == w['ev']]
                if not match:
                    viol("K2-WIN", tag,
                         f"drain {w['ev']} not in inventory n={w['n']} at {key}")
                same_kp = [d for d in drains
                           if d[0] == w['K'] and d[1] == w['p']]
                if len(same_kp) != 1:
                    viol("K2-WIN", tag,
                         f"drain order not unique for K={w['K']} p={w['p']} "
                         f"n={w['n']} at {key}")
        M_K = sum(g0 - e[1] for e in ce if e[0] == 0)
        cells.append(dict(sgn=sgn, b=b, j=j, pc=tuple(pc), dmp=tuple(dmp),
                          ncorr=sum(ncorr), junk=junk, jD=tuple(jD), ce=ce,
                          y2=y2, line=ln, w0=w0(R, b), res=E.resKm(b), t=t,
                          MK=M_K, wins=wins, hist=hist))
        # K2-FACT on junk-free cells
        if junk == 0 and y2 == 0:
            cD = Dmap.get(tuple(jD))
            if w0(R, cD) != u0 - t * E.h[0]:
                viol("K2-FACT", tag,
                     f"seed w0 != u0 - t*h0 at {key} (W-D2(iv) leg)")
            wexp = (u1a + u1b) + (u0 - t * E.h[0])
            racc = E.resKm(cD)
            ok = True
            for (i, k, avec, dj0) in ce:
                dg = dmap.get((i, k, avec))
                if dg is None or dj0 != 0:
                    ok = False; break
                wexp += w0(R, dg)
                racc = E.kmul(racc, E.resKm(dg))
            if ok:
                if w0(R, b) != wexp:
                    viol("K2-FACT", tag,
                         f"w0 {w0(R, b)} != additive {wexp} at {key}")
                if not E.keq(E.resKm(b), racc):
                    viol("K2-FACT", tag, f"residue product fails at {key}")
                if sgn != (-1) ** len(ce):
                    viol("K2-FACT", tag, f"sign parity fails at {key}")
            note("fact_cells")
    if not cells:
        return None
    # K2-COLOC: junk-free line = function of pc totals
    by_pc = {}
    for c in cells:
        if c['junk'] == 0 and c['y2'] == 0:
            v = by_pc.setdefault(c['pc'], c['line'])
            if v != c['line']:
                viol("K2-COLOC", tag,
                     f"same pc, different line at {key}: {c['pc']}")
    beta_min = min(c['line'] for c in cells)
    slots = collections.defaultdict(list)
    for c in cells: slots[c['j']].append(c)
    bgroups = {jv: [c for c in grp if c['line'] == beta_min]
               for jv, grp in slots.items()}
    bgroups = {jv: g for jv, g in bgroups.items() if g}
    # K2-JBOT
    for jv, g in bgroups.items():
        for c in g:
            if c['junk'] or c['y2']:
                viol("K2-JBOT", tag, f"junk cell at beta_min at {key}")
    # K2-NU per (slot, book) at every line (book = interior ce multiset + pc)
    for jv, grp in slots.items():
        fib = collections.defaultdict(set)
        for c in grp:
            if c['junk'] or c['y2']: continue
            book = (tuple(sorted(e for e in c['ce'] if e[0] != 0)), c['pc'],
                    c['line'])
            fib[book].add(c['t'] - c['MK'])
        for book, nus in fib.items():
            if len(nus) > 1:
                viol("K2-NU", tag, f"nu not constant at {key} slot {jv}")
    # ---------------- bottom fiber completeness + chain counts ----------------
    avail = set(k for (k, dc) in E.corr_table()[0])
    seedsT = {}
    for jDv, cD in Dmap.items():
        tt, rr = divmod(jDv[0] - s1u1, E.e[0])
        if rr == 0 and 0 <= tt < g0:
            seedsT[tt] = jDv
    row_reg = True
    prot_some = False
    row_forms = []
    ginfo = {}
    for jv, g in sorted(bgroups.items()):
        classes, signed = classify_group(E, g)
        ginfo[jv] = (classes, signed)
        if protected(signed): prot_some = True
        # fibers: key = (interior ce multiset, pc totals); level-0
        # placement AND per-window promo placement free inside the fiber
        fibs = collections.defaultdict(list)
        for c in g:
            ibook = tuple(sorted(e for e in c['ce'] if e[0] != 0))
            fibs[(ibook, c['pc'])].append(c)
        if len(fibs) > 1:
            row_reg = False
            note("glued_groups")
        for bk, fc in sorted(fibs.items()):
            # chain enumeration (g0 = 2 only)
            if g0 != 2: continue
            c0 = fc[0]
            arrs = [w['arrival'] for w in c0['wins']]
            kinds = [w['kind'] for w in c0['wins']]
            ptot = c0['pc'][0]
            swin = [ix for ix, kd in enumerate(kinds) if kd == 'seed']
            pred = set()
            for tt in sorted(seedsT):
                if not swin: continue
                si = swin[0]
                arr2 = list(arrs)
                arr2[si] = arrs[si] + (tt - c0['t']) * E.e[0]
                if arr2[si] < 0: continue
                # enumerate legal drains per window (promo placement free,
                # total promos = ptot); parked exponent carries through
                def rec_chain(ix, j0carry, Kacc, pacc):
                    if pacc > ptot or ix == len(arr2): return
                    j0v = j0carry + arr2[ix]
                    n = j0v // E.e[0]
                    if n > 3: return
                    for (K, pp, fu, seq) in legal_drains_g2(n, avail):
                        rem = j0v - sum((E.P[0] - E.e[0] * kk) for kk in K) \
                            - pp * E.P[0]
                        if rem < 0: continue
                        if ix + 1 == len(arr2):
                            if pacc + pp == ptot:
                                pred.add((tt, tuple(sorted(
                                    list(Kacc) + list(K))), rem))
                        else:
                            rec_chain(ix + 1, rem, Kacc + list(K), pacc + pp)
                rec_chain(0, 0, [], 0)
            got = set((c['t'], tuple(sorted(e[1] for e in c['ce']
                                            if e[0] == 0)), c['j'][0])
                      for c in fc)
            want = set((tt, K, rem) for (tt, K, rem) in pred
                       if rem == fc[0]['j'][0])
            if not (got <= want):
                viol("K2-FIB", tag,
                     f"fiber cell outside chain enumeration at {key} slot "
                     f"{jv}: got {sorted(got)} want {sorted(want)}")
            elif got != want:
                viol("K2-FIB", tag,
                     f"fiber INCOMPLETE at {key} slot {jv}: got "
                     f"{sorted(got)} want {sorted(want)}")
            # K2-CHAIN: per-seed signed count within fiber
            St = collections.Counter()
            for c in fc: St[c['t']] += c['sgn']
            if any(abs(v) > 1 for v in St.values()):
                viol("K2-CHAIN", tag,
                     f"fixed-book per-seed count > 1 at {key} slot {jv}")
            # branch census
            nx = sum(1 for w in fc[0]['wins']
                     if w['n'] == 3 and w['p'] == 0 and avail == {0, 1})
            if nx >= 2: note("fibers_two_exchange_windows")
            pvs = set(tuple(w['p'] for w in c['wins']) for c in fc)
            if len(pvs) > 1: note("placement_pair_fibers")
        # K2-SHAPE: single-book groups must realize a THM-A table form
        # (normalized: strip common K, base the seed at its min)
        if len(fibs) == 1 and g0 == 2:
            cellsK = [(c['t'], collections.Counter(
                e[1] for e in c['ce'] if e[0] == 0), c['sgn']) for c in g]
            tmin = min(t for t, K, s in cellsK)
            common = None
            for t, K, s in cellsK:
                common = K.copy() if common is None else (common & K)
            norm = tuple(sorted((t - tmin,
                                 tuple(sorted((K - common).elements())), s)
                                for t, K, s in cellsK))
            eps = norm[0][2]
            flip = tuple(sorted((a, b, -s) for a, b, s in norm))
            FORMS = {
                (((0, (), 1),)),                                   # S
                ((0, (), 1), (1, (1,), -1)),                       # P1
                ((0, (0,), 1), (0, (1, 1), -1)),                   # P2
                ((0, (1,), -1), (1, (0,), -1), (1, (1, 1), 1)),    # T1
            }
            if norm not in FORMS and flip not in FORMS and \
               norm != ((0, (), 1),) and norm != ((0, (), -1),):
                viol("K2-SHAPE", tag,
                     f"single-book bottom group outside THM-A form list "
                     f"at {key} slot {jv}: {norm}")
            else:
                base = norm if (norm in FORMS or norm in
                                (((0, (), 1),), ((0, (), -1),))) else flip
                if len(base) == 1 and base[0][1] == ():
                    row_forms.append('S')
                elif len(base) == 2 and base[1][1] == (1,):
                    row_forms.append('P1')
                elif len(base) == 2:
                    row_forms.append('P2')
                else:
                    row_forms.append('T1')
    if not prot_some:
        viol("K2-PROT", tag,
             f"(SURV-K2) COUNTEREXAMPLE: no protected bottom group at "
             f"{tag}{list(key)}")
    # K2-REG census + THM-A shadow
    if avail != {0, 1}: row_reg = False
    if row_reg:
        note("reg_rows")
        # K2-SYS: the THM-A system law (R5) — the beta_min system contains a
        # singleton group, or contains both a P1 and a T1
        if g0 == 2 and not ('S' in row_forms or
                            ('P1' in row_forms and 'T1' in row_forms)):
            viol("K2-SYS", tag,
                 f"REG system outside THM-A system law at {key}: {row_forms}")
        if not prot_some:
            viol("K2-REG", tag, f"REG row unprotected at {key} — THM-A breach")
    else:
        note("nonreg_rows")
    return dict(live=True)

# ---------------- tower drivers (selection replicated from the instrument) ----
def run_tower(spec, phase, rowset, caps=(12, 6)):
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
    dmap, Dmap = build_maps(E)
    u0 = meta["u0"]
    etop = E.e[m - 1]; R = E.R
    n0 = 0
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
        for key, (ga, gb, cs, Dd, kdef, meas, sA, sB, u1a, u1b) in chosen:
            r = trace_row(E, sA, sB, u1a, u1b, anch[ga][0], anch[gb][0], su,
                          cs, Dd, kdef, (ga, gb), prin, tag, p, kind, E.g[0],
                          dmap, Dmap, u0, rowset)
            if r: n0 += 1
    else:
        seen, live_pool = set(), {}
        for ga in range(G0, G0 + Etot):
            aA, sA, u1a = anch[ga]
            for gb in range(G0, G0 + Etot):
                aB, sB, u1b = anch[gb]
                if not (sA[m + 1] == E.e[m] - 1 and sB[m + 1] == E.e[m] - 1):
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
        for stratum in sorted(live_pool):
            for row in live_pool[stratum][:cap]:
                ga, gb, cs, Dd, kdef, sA, sB, u1a, u1b = row
                r = trace_row(E, sA, sB, u1a, u1b, anch[ga][0], anch[gb][0],
                              su, cs, Dd, kdef, (ga, gb), prin, tag, p, kind,
                              E.g[0], dmap, Dmap, u0, rowset)
                if r: n0 += 1
    print(f"-- {phase.upper()} {tag} m={m} {kind},p={p},d0={d0} g0={E.g[0]}: "
          f"live traced={n0} ({time.time()-t0:.1f}s)")

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
K2_TRACED = [
    ("K2G2P5B", 3, "Zp",  5, 1, [(3,1,2), (2,1,1), (3,2,1), (2,1,1)]),
    ("K2W4G2Z", 4, "Zp",  3, 1, [(3,1,2), (2,1,1), (2,1,1), (2,1,1), (2,1,1)]),
]

def cand_arithmetic():
    """K2-CAND: the displayed failure-candidate arithmetic, abstractly."""
    ok = True
    # (a) g0=2 placement pair: chain [n=3 window, p=1] -> [arrival 1 unit]
    # two paths, both mass 1 (one C1), both sign -, same residue class
    paths = []
    for (K1, p1, f1, seq1) in legal_drains_g2(3, {0, 1}):
        if p1 != 1: continue
        n2 = f1 + 1
        if n2 <= 1:
            if sum(2 - k for k in K1) == 1:
                paths.append((K1, ()))
            continue
        for (K2, p2, f2, seq2) in legal_drains_g2(n2, {0, 1}):
            if p2 != 0: continue
            if sum(2 - k for k in K1) + sum(2 - k for k in K2) == 1 \
               and f2 == 1:
                paths.append((K1, K2))
    cnt = sum((-1) ** (len(a) + b.__len__()) for (a, b) in paths)
    if not (len(paths) == 2 and cnt == -2):
        viol("K2-CAND", "g2-placement", f"expected 2 paths / -2, got "
             f"{paths} / {cnt}")
        ok = False
    # (b) g0=3, n=5 window, f=2, p=0: {C0} and {C2,C2,C2} both '-';
    # {C2,C1} realized by two orders
    def drains_g3(n, avail_masses):
        out = []
        def rec(u, K, seq):
            if u <= 2:
                out.append((tuple(sorted(K)), u, tuple(seq))); return
            for mu in avail_masses:
                if True: rec(u - mu, K + [mu], seq + [mu])
            rec(u - 3, K, seq + ['p'])
        rec(n, [], [])
        return out
    d = [x for x in drains_g3(5, (1, 2, 3)) if x[1] == 2 and
         'p' not in x[2]]
    masses = collections.Counter(x[0] for x in d)
    if not (masses[(3,)] == 1 and masses[(1, 1, 1)] == 1
            and masses[(1, 2)] == 2):
        viol("K2-CAND", "g3-n5", f"unexpected census {dict(masses)}")
        ok = False
    if ok: note("cand_ok")

def main():
    t0 = time.time()
    for fn, want in PINS.items():
        got = hashlib.md5(open(os.path.join(HERE, fn), "rb").read()).hexdigest()
        if got != want:
            viol("K2-PIN", fn, f"md5 {got} != pinned {want}")
    cand_arithmetic()
    rowset = set()
    print("=" * 78)
    print("(SURV-K2) DERIVE CHECKS — the instrument's traced g0 >= 2 rows")
    print("(the ten g0 >= 3 towers excluded up front: measured engine cost")
    print(" wall, SURVK2_INSTRUMENT amendment bracket — disclosed skip)")
    print("=" * 78)
    for spec in WS.ROSTER:
        if spec[5][0][2] < 2: continue
        run_tower(spec, "sealed", rowset)
    for spec in ED.FRESH_ROSTER:
        if spec[5][0][2] < 2: continue
        run_tower(spec, "eq", rowset)
    for spec in PX_ROSTER:
        if spec[5][0][2] < 2: continue
        run_tower(spec, "px", rowset)
    for spec in SD_ROSTER:
        if spec[5][0][2] < 2: continue
        run_tower(spec, "sd", rowset)
    for spec in K2_TRACED:
        run_tower(spec, "k2", rowset)
    # roster equality vs the instrument's artifacts
    try:
        with open(os.path.join(HERE, "survk2_instrument_results.json")) as f:
            inst = json.load(f)
        inst_rows = set((q['tower'],) + tuple(q['key']) for q in inst['qdrows'])
        if rowset != inst_rows:
            viol("HARNESS", "roster",
                 f"traced rowset != instrument ({len(rowset)} vs "
                 f"{len(inst_rows)}; diff {sorted(rowset ^ inst_rows)[:6]})")
    except Exception as ex:
        viol("HARNESS", "roster", f"instrument results unreadable: {ex!r}")
    print("=" * 78)
    fams = ["K2-PIN", "K2-XWALK", "K2-CONS", "K2-WIN", "K2-FACT", "K2-NU",
            "K2-JBOT", "K2-COLOC", "K2-FIB", "K2-CHAIN", "K2-SHAPE",
            "K2-REG", "K2-SYS",
            "K2-PROT", "K2-CAND", "HARNESS"]
    for f in fams:
        print(f"{f:10s}: {sum(1 for v in VIOL if v[0] == f)} violations")
    print("-" * 78)
    print(f"live rows traced: {CNT.get('live_rows', 0)} (expected 332); "
          f"REG rows: {CNT.get('reg_rows', 0)}; non-REG: "
          f"{CNT.get('nonreg_rows', 0)}; glued groups: "
          f"{CNT.get('glued_groups', 0)}")
    print(f"fibers with two n=3 windows: "
          f"{CNT.get('fibers_two_exchange_windows', 0)}; placement-pair "
          f"fibers: {CNT.get('placement_pair_fibers', 0)}; fact cells: "
          f"{CNT.get('fact_cells', 0)}")
    print(f"total violations: {len(VIOL)}")
    el = time.time() - t0
    print(f"elapsed: {el:.1f}s")
    out = dict(final=True, violations=VIOL, counters=CNT, elapsed=el,
               nrows=len(rowset))
    with open(os.path.join(OUTDIR, "survk2_derive_checks_results.json"),
              "w") as f:
        json.dump(out, f, indent=1, default=str)
    print("results -> survk2_derive_checks_results.json")

if __name__ == "__main__":
    main()
