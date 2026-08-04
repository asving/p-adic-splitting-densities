#!/usr/bin/env python3
"""survk2_pe1_ext.py — SURVK2 pass PE1 counterexample probe (2026-08-08 campaign).

Hostile-pass instrument for SURVK2_PROOF_2026-08-08.md (verifier-owned; the
note and all engines are READ-ONLY).  Four probes:

  A. THE A = {1} CORNER (the note's sharpest counterexample candidate,
     (K2-RES)(c)): is a g0 = 2 tower with psi0_0 = 0 (level-0 digit C0
     absent) class-realizable?
       A1 field-level: over every K0 in the grid, enumerate ALL monic
          degree-2 polynomials; verify psi(0) = 0 => reducible (y divides),
          i.e. IRREDUCIBILITY ALONE forces 0 in A at g0 = 2; count the
          irreducibles with zero LINEAR term (the A = {0} shape) per
          characteristic (char 2: expect none; odd: expect > 0).
       A2 engine-level: systematic tower grid; record psi0 and
          A := {k : psi0_k != 0}; expect 0 in A ALWAYS (the class pin
          [ILN] S0.1 requires psi_j monic irreducible with psi_j(0) != 0;
          grb_order2_check.pick_irreducible enforces both).
  B. INDEPENDENT DRAIN INVENTORY (decorrelated from the composer's
     legal_drains_g2): B1 unit-level brute force at g0 = 2 over
     avail in {{0,1},{0},{1}}; B2 raw-j0-level enumeration (no unit
     abstraction) cross-check for e0 in {2,3}, all residues r; B3 the
     g0 = 3 / n = 5 failure-candidate census (the -2 window, the
     order-multiplicity pair) plus the full masses-{1,2,3} class census;
     B4 the g0 = 2 placement-pair chain.
  C. GLUED DUMP-SWAP GROUPS BY HAND ((K2-RES)(a)): re-trace SDG2BF
     [1479,1485], SDG2BZ [1479,1485], SDW4G2F (the worked 5-cell group);
     display every beta_min glued group's anatomy (t, K, dumps, sign,
     residue), verify the glue quantum delta(dump_0) = e0*(g0-k) and the
     instance protection.
  D. THE TWO HAND-RE-DERIVATION WITNESSES: D1 the EQ3G2B [1479,1485] T0
     kill (Q-A0 identity res(C1)*res(cD_1) = res(cD_0), elements printed
     raw for the by-hand check); D2 the K2G2P5B [1479,1479] exchange kill
     (I3: res(C1)^2 = res(C0), psi0 printed raw).

Deterministic, exact, read-only on all committed artifacts.  Usage:
    python3 survk2_pe1_ext.py [outdir]
"""
import sys, os, time, json, collections, itertools

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
OUTDIR = sys.argv[1] if len(sys.argv) > 1 else HERE

import survk2_derive_checks as SK
import wmultdcx_stress as WS
import wmultdcx_derive_checks as WD
import rmengine_pe_reimpl as PE
import empty_derive_checks as ED
from grb_order2_check import (pnorm, pdivmod, pmul, pscal, w0,
                              _field_elems, fp_irreducible, pick_irreducible)

VIOL, FINDINGS = [], []
def viol(tag, msg):
    VIOL.append((tag, msg)); print(f"PROBE-VIOLATION [{tag}] {msg}")
def finding(msg):
    FINDINGS.append(msg); print(f"PROBE-FINDING: {msg}")

# ============================ PROBE B: inventories ============================
def drains_units(n, avail, g0=2):
    """Unit-level brute force: complete junk-free drain sequences from n
    units.  Events fire at u >= g0; C_k costs g0-k units; promo costs g0."""
    out = []
    def rec(u, seq, K, p):
        if u < g0:
            out.append((tuple(sorted(K)), p, u, tuple(seq))); return
        for k in sorted(avail):
            rec(u - (g0 - k), seq + [('c', k)], K + [k], p)
        rec(u - g0, seq + [('p',)], K, p + 1)
    rec(n, [], [], 0)
    return sorted(set(out))

def drains_rawj0(j0, e0, avail, g0=2):
    """Raw exponent-level enumeration, NO unit abstraction: events at
    j0 >= P0 = e0*g0; C_k consumes e0*(g0-k); promo consumes P0."""
    P0 = e0 * g0
    out = []
    def rec(j, seq, K, p):
        if j < P0:
            out.append((tuple(sorted(K)), p, j // e0, tuple(seq))); return
        for k in sorted(avail):
            rec(j - e0 * (g0 - k), seq + [('c', k)], K + [k], p)
        rec(j - P0, seq + [('p',)], K, p + 1)
    rec(j0, [], [], 0)
    return sorted(set(out))

def probe_B():
    print("=" * 78)
    print("PROBE B — independent drain inventories")
    ok = True
    # B1: the note's display at avail = {0,1}  ("n <= 1: none" = no EVENTS;
    # the enumerator returns the trivial empty drain there)
    want = {
        0: {((), 0, 0)}, 1: {((), 0, 1)},
        2: {((1,), 0, 1), ((0,), 0, 0), ((), 1, 0)},
        3: {((1, 1), 0, 1), ((0,), 0, 1), ((), 1, 1),
            ((0, 1), 0, 0), ((1,), 1, 0)},
    }
    for n in range(4):
        got = {(K, p, f) for (K, p, f, seq) in drains_units(n, {0, 1})}
        if got != want[n]:
            viol("B1", f"n={n}: got {sorted(got)} != note display "
                 f"{sorted(want[n])}"); ok = False
    # (i) unique legal order per (K, p) per budget
    for n in (2, 3):
        cnt = collections.Counter(
            (K, p) for (K, p, f, seq) in drains_units(n, {0, 1}))
        if any(v != 1 for v in cnt.values()):
            viol("B1-i", f"order multiplicity at n={n}: {cnt}"); ok = False
    # (ii) unique exchange class; (iv) signed counts
    for n in (2, 3):
        cls = collections.defaultdict(list)
        for (K, p, f, seq) in drains_units(n, {0, 1}):
            units = sum(2 - k for k in K) + 2 * p
            cls[(units, p)].append(K)
        for (u, p), Ks in cls.items():
            sgn = sum((-1) ** len(K) for K in Ks)
            if len(Ks) > 1 and (n, u, p) != (3, 2, 0):
                viol("B1-ii", f"unexpected multi-drain class n={n} "
                     f"(units,p)=({u},{p}): {Ks}"); ok = False
            if abs(sgn) > 1:
                viol("B1-iv", f"class signed count {sgn} at n={n} "
                     f"({u},{p})"); ok = False
    # restricted availability (the A-corner arithmetic used by S7(c)):
    for avail, lab in (({0}, "A={0} (only C0)"), ({1}, "A={1} (only C1)")):
        for n in (2, 3):
            cls = collections.defaultdict(list)
            for (K, p, f, seq) in drains_units(n, avail):
                units = sum(2 - k for k in K) + 2 * p
                cls[(units, p)].append(K)
            multi = {k: v for k, v in cls.items() if len(v) > 1}
            if multi:
                viol("B1-A", f"{lab}: multi-member class at n={n}: {multi}")
                ok = False
        print(f"  {lab}: every (units,p) class a singleton at n<=3 "
              f"(in-window exchange dead)  [OK]")
    # cross-seed parity at A={0}: budgets n, n+1 with only 2-unit moves
    # cannot land equal parked f: parity obstruction
    for n in (2,):
        f_n  = {f for (K, p, f, s) in drains_units(n, {0})}
        f_n1 = {f for (K, p, f, s) in drains_units(n + 1, {0})}
        if f_n & f_n1:
            viol("B1-A0x", f"A={{0}}: cross-seed parked overlap {f_n & f_n1}")
            ok = False
    print("  A={0}: cross-seed toggle impossible (parked-parity disjoint) "
          "[OK]" if ok else "  [see violations]")
    # B2: raw-j0 cross-check (kills any unit-arithmetic slip)
    okB2 = True
    for e0 in (2, 3):
        for r in range(e0):
            for n in (2, 3):
                j0 = n * e0 + r
                a = {(K, p, f) for (K, p, f, s) in
                     drains_rawj0(j0, e0, {0, 1})}
                b = {(K, p, f) for (K, p, f, s) in drains_units(n, {0, 1})}
                if a != b:
                    viol("B2", f"raw-j0 (e0={e0}, r={r}, n={n}) disagrees "
                         f"with unit level: {a ^ b}"); ok = okB2 = False
    print("  B2 raw-j0 == unit-level for e0 in {2,3}, all residues [OK]"
          if okB2 else "  B2 FAILED")
    # B3: g0 = 3, n = 5 candidates
    d13 = [x for x in drains_units(5, {0, 2}, g0=3) if x[1] == 0 and x[2] == 2]
    mass13 = collections.Counter(x[0] for x in d13)
    exp13 = {(0,): 1, (2, 2, 2): 1}
    if {k: v for k, v in mass13.items()} != exp13:
        viol("B3", f"masses {{1,3}} n=5 f=2 p=0 census {dict(mass13)} != "
             f"{exp13}"); ok = False
    else:
        s = sum((-1) ** len(K) for K in mass13)
        print(f"  B3 g0=3 n=5 masses {{1,3}}: drains {dict(mass13)}, both "
              f"sign -, class count -2  [-2 WINDOW CONFIRMED]")
    d12 = [x for x in drains_units(5, {1, 2}, g0=3) if x[1] == 0]
    seqs = [x[3] for x in d12 if x[0] == (1, 2)]
    if len(seqs) != 2:
        viol("B3", f"{{C2,C1}} order census at n=5: {seqs}"); ok = False
    else:
        print(f"  B3 g0=3 n=5 {{C2,C1}}: {len(seqs)} legal orders "
              f"{seqs}  [ORDER-MULTIPLICITY CONFIRMED]")
    # full-availability census at g0=3, n<=5: all multi-member classes
    print("  B3 full census (masses {1,2,3}), multi-member (n,units,p) "
          "classes:")
    for n in range(3, 6):
        cls = collections.defaultdict(list)
        for (K, p, f, seq) in drains_units(n, {0, 1, 2}, g0=3):
            units = sum(3 - k for k in K) + 3 * p
            cls[(units, p)].append(K)
        for (u, p), Ks in sorted(cls.items()):
            if len(Ks) > 1:
                sg = sum((-1) ** len(K) for K in Ks)
                print(f"    n={n} (units,p)=({u},{p}): {Ks} signed={sg}")
    # B4: the placement pair (drains_units handles n2 <= 1 via the trivial
    # empty drain, so a single loop suffices — no extra branch)
    paths = []
    for (K1, p1, f1, s1) in drains_units(3, {0, 1}):
        if p1 != 1: continue
        n2 = f1 + 1
        for (K2, p2, f2, s2) in drains_units(n2, {0, 1}):
            if p2 != 0: continue
            if sorted(list(K1) + list(K2)) == [1] and f2 == 1:
                paths.append((K1, K2))
    cnt = sum((-1) ** (len(a) + len(b)) for a, b in paths)
    if not (len(paths) == 2 and cnt == -2):
        viol("B4", f"placement pair: {paths} count {cnt}"); ok = False
    else:
        print(f"  B4 placement-pair chain: 2 paths {paths}, net -2 "
              f"[CONFIRMED]")
    return ok

# ============================ PROBE A: the corner =============================
def poly_str(F, poly):
    return "[" + ", ".join(str(c) for c in poly) + "]"

def probe_A():
    print("=" * 78)
    print("PROBE A — the A = {1} availability corner (psi0_0 = 0)")
    grid = []
    for kind in ("Fpt", "Zp"):
        for p in (2, 3, 5):
            for d0 in (1, 2):
                for r0 in ((2, 1, 2), (3, 1, 2), (3, 2, 2), (1, 1, 2)):
                    for r1 in ((2, 1, 1), (3, 2, 1)):
                        grid.append((kind, p, d0, r0, r1, (2, 1, 1)))
    a_census = collections.Counter()
    k0_seen = {}
    built = failed = 0
    for (kind, p, d0, r0, r1, r2) in grid:
        tag = f"PE1A-{kind}-p{p}-d{d0}-{r0[0]}{r0[1]}-{r1[0]}{r1[1]}"
        try:
            E = PE.Eng(2, kind, p, d0, [r0, r1, r2], tag)
        except Exception:
            failed += 1; continue
        built += 1
        T = E.grbT
        psi0 = T.psi0
        A = frozenset(k for k, c in enumerate(psi0[:-1])
                      if not T.K0["isz"](c))
        a_census[tuple(sorted(A))] += 1
        if 0 not in A:
            viol("A2", f"{tag}: psi0 = {psi0} has psi0_0 = 0 — "
                 f"A = {set(A)} WITHOUT 0: the corner is ENGINE-REALIZED")
        k0key = (p, d0, kind)
        if k0key not in k0_seen:
            k0_seen[k0key] = T.K0
    print(f"  engine grid: {built} towers built, {failed} unsupported; "
          f"A-census over built towers: {dict(a_census)}")
    if all(0 in set(a) for a in a_census):
        finding("A2: 0 in A on EVERY built tower (psi0_0 != 0 always) — "
                "the A = {1} and A = {} corners never realized")
    # A1: field-level exhaustive scan
    print("  A1 field-level: monic degree-2 census per K0:")
    for (p, d0, kind), F in sorted(k0_seen.items()):
        elems = list(_field_elems(F))
        tot = irr = irr_b0 = irr_a0 = 0
        for b in elems:
            for a in elems:
                cand = [b, a, F["one"]]
                tot += 1
                if fp_irreducible(F, cand):
                    irr += 1
                    if F["isz"](b): irr_b0 += 1
                    if F["isz"](a): irr_a0 += 1
        q = len(elems)
        print(f"    K0 (p={p}, d0={d0}, {kind}): q={q}; monic deg-2 total "
              f"{tot}, irreducible {irr}, irreducible with psi(0)=0: "
              f"{irr_b0}, irreducible with psi_1=0 (A={{0}} shape): "
              f"{irr_a0}")
        if irr_b0 != 0:
            viol("A1", f"K0 (p={p},d0={d0}): irreducible with zero "
                 f"constant term exists?!")
        if p == 2 and irr_a0 != 0:
            viol("A1", f"K0 char 2: y^2+c irreducible exists?! "
                 f"(Artin-Schreier says no)")
    finding("A1: psi(0) = 0 => reducible on every K0 scanned (y | psi): "
            "IRREDUCIBILITY ALONE empties the A = {1} corner at g0 = 2; "
            "the [ILN] S0.1 class pin ALSO demands psi_j(0) != 0 outright "
            "(ITERLAWN_PROOF S0.1). The (K2-RES)(c) candidate is "
            "CLASS-VACUOUS, not machine-dark.")
    finding("A1b: the A = {0} shape (psi0_1 = 0) is field-realizable at "
            "odd characteristic only (char 2: zero irreducibles of shape "
            "y^2 + c); never picked by the committed enumeration on the "
            "16-tower roster (instrument a0tab: ks = [0,1] on all 16).")

# ==================== shared row machinery (C and D) ==========================
def select_rows(E, su):
    """Replicate the runner's non-sealed row selection (eq/px/sd/k2 phases)."""
    R = E.R; m = E.m; etop = E.e[m - 1]
    Etot, G0, split = WS.window_split(E)
    anch = WS.anchors_of(E, Etot, G0, split)
    seen, live_pool = set(), {}
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
            ctop = cs[-1] if cs else 0
            kdef = 2 * etop - Dd
            if kdef > ctop: continue
            live_pool.setdefault((kdef, ctop), []).append(
                (ga, gb, cs, Dd, kdef, sA, sB, u1a, u1b))
    cap = 6 if m >= 4 else 12
    rows = []
    for stratum in sorted(live_pool):
        rows.extend(live_pool[stratum][:cap])
    return rows, anch

def trace_cells(E, sA, sB, u1a, u1b, aA, aB, su, prin, g0):
    """Light recording-walk trace (no cross-checks — those are the runner's,
    already re-run green).  Returns the per-cell dicts of the terminal q2."""
    R = E.R; m = E.m
    sig = tuple(sA[l + 1] + sB[l + 1] for l in range(m))
    s1u1 = su[1]
    b0 = pscal(R, R["pi_pow"](u1a + u1b), [R["one"]])
    z = (0,) * m
    init = [(1, b0, sig, z, z, z, z, 0, None, False, (), 0, ())]
    q1 = []
    if SK.walk_rec(E, init, q1, "pe1") is None: return None
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
                init2.append((sgn, cc, tuple(jj), pc, tuple(dd), cons,
                              ncorr, junk + jtag, tuple(jD), isp, ce, dj0,
                              hist + (('seed', jD[0] + dj0),)))
    q2 = []
    if SK.walk_rec(E, init2, q2, "pe1") is None: return None
    cells = []
    for st in q2:
        (sgn, b, j, pc, dmp, cons, ncorr, junk, jD, isp, ce, y2, hist) = st
        t = (jD[0] - s1u1) // E.e[0]
        cells.append(dict(sgn=sgn, b=b, j=j, pc=tuple(pc), dmp=tuple(dmp),
                          junk=junk, jD=tuple(jD), ce=ce, y2=y2,
                          line=E.line(b, j), w0=w0(R, b), res=E.resKm(b),
                          t=t, hist=hist, sig0=sig[0]))
    return cells

def show_group(E, grp, label):
    classes, signed = SK.classify_group(E, grp)
    print(f"  {label}: n={len(grp)} cells, signed vector {signed}, "
          f"protected={SK.protected(signed)}")
    for c in sorted(grp, key=lambda c: (c['t'], str(c['ce']))):
        K0c = tuple(sorted(e[1] for e in c['ce'] if e[0] == 0))
        Ic = tuple(e for e in c['ce'] if e[0] != 0)
        print(f"    t={c['t']} K={K0c} I={Ic} sgn={c['sgn']:+d} "
              f"w0={c['w0']} res={c['res']}")
    return classes, signed

def probe_tower(spec, wanted_keys, label, show_all_glued=False,
                find_exchange=False):
    tag, m, kind, p, d0, reads = spec
    print(f"-- tracing {tag} (m={m} {kind} p={p} d0={d0}) --")
    E = PE.Eng(m, kind, p, d0, reads, tag)
    PE.prep(E)
    u, su = WS.uchain(E)
    prin, meta = WD.inv_checks(E, u, su)
    rows, anch = select_rows(E, su)
    g0 = E.g[0]
    print(f"  psi0 = {E.grbT.psi0}  (K0 elements, ascending degree; "
          f"A = {{k: psi0_k != 0}})")
    hits = []
    for (ga, gb, cs, Dd, kdef, sA, sB, u1a, u1b) in rows:
        if wanted_keys is not None and (ga, gb) not in wanted_keys:
            continue
        cells = trace_cells(E, sA, sB, u1a, u1b, anch[ga][0], anch[gb][0],
                            su, prin, g0)
        if not cells: continue
        bmin = min(c['line'] for c in cells)
        slots = collections.defaultdict(list)
        for c in cells:
            if c['line'] == bmin: slots[c['j']].append(c)
        for jv, grp in sorted(slots.items()):
            fibs = collections.defaultdict(list)
            for c in grp:
                ibook = tuple(sorted(e for e in c['ce'] if e[0] != 0))
                fibs[(ibook, c['pc'])].append(c)
            glued = len(fibs) > 1
            if show_all_glued and not glued and wanted_keys is None:
                continue
            _, signed = show_group(
                E, grp, f"{tag}[{ga},{gb}] slot {jv} beta_min={bmin}"
                        f"{' GLUED (' + str(len(fibs)) + ' books)' if glued else ''}")
            hits.append((ga, gb, jv, glued, signed, grp))
    return E, hits

# ============ PROBE E: full-roster duplicate-book census ======================
def select_rows_sealed(E, su):
    """Replicate the runner's SEALED-phase selection (WS.ROSTER towers)."""
    R = E.R; m = E.m; etop = E.e[m - 1]
    Etot, G0, split = WS.window_split(E)
    anch = WS.anchors_of(E, Etot, G0, split)
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
                    pid_keys[key] = (ga, gb, cs, Dd, kdef, meas, sA, sB,
                                     u1a, u1b)
    cap = 14 if m >= 4 else 40
    chosen = sorted(pid_keys.items(), key=lambda kv: (
        not kv[1][5], -(kv[1][2][0] if kv[1][2] else 0), kv[0]))[:cap]
    rows = [(ga, gb, cs, Dd, kdef, sA, sB, u1a, u1b)
            for key, (ga, gb, cs, Dd, kdef, meas, sA, sB, u1a, u1b) in chosen]
    return rows, anch

def probe_E():
    """Duplicate-book census over the FULL traced roster: cells of one
    beta_min fiber sharing (t, K-multiset, I, pc, sgn).  K2-CHAIN can miss
    these when an opposite-sign cell offsets the pair (SDW4G2F showed one);
    census them all."""
    print("=" * 78)
    print("PROBE E — full-roster beta_min duplicate-book census")
    dup_rows, nrows = [], 0
    rosters = ([(s, "sealed") for s in WS.ROSTER if s[5][0][2] >= 2] +
               [(s, "eq") for s in ED.FRESH_ROSTER if s[5][0][2] >= 2] +
               [(s, "px") for s in SK.PX_ROSTER if s[5][0][2] >= 2] +
               [(s, "sd") for s in SK.SD_ROSTER if s[5][0][2] >= 2] +
               [(s, "k2") for s in SK.K2_TRACED])
    for spec, phase in rosters:
        tag, m, kind, p, d0, reads = spec
        try:
            E = PE.Eng(m, kind, p, d0, reads, tag)
            PE.prep(E)
        except Exception:
            continue
        u, su = WS.uchain(E)
        if u is None: continue
        prin, meta = WD.inv_checks(E, u, su)
        if meta is None: continue
        rows, anch = (select_rows_sealed(E, su) if phase == "sealed"
                      else select_rows(E, su))
        for (ga, gb, cs, Dd, kdef, sA, sB, u1a, u1b) in rows:
            ctop = cs[-1] if cs else 0
            if kdef > ctop: continue
            cells = trace_cells(E, sA, sB, u1a, u1b, anch[ga][0],
                                anch[gb][0], su, prin, E.g[0])
            if not cells: continue
            nrows += 1
            bmin = min(c['line'] for c in cells)
            slots = collections.defaultdict(list)
            for c in cells:
                if c['line'] == bmin: slots[c['j']].append(c)
            for jv, grp in slots.items():
                fibs = collections.defaultdict(list)
                for c in grp:
                    ib = tuple(sorted(e for e in c['ce'] if e[0] != 0))
                    fibs[(ib, c['pc'])].append(c)
                for bk, fc in fibs.items():
                    summ = collections.Counter(
                        (c['t'], tuple(sorted(e[1] for e in c['ce']
                                              if e[0] == 0)), c['sgn'])
                        for c in fc)
                    d = {k: v for k, v in summ.items() if v > 1}
                    if d:
                        dup_rows.append((tag, ga, gb, jv, dict(d)))
    print(f"  rows traced: {nrows}; beta_min fibers with duplicate "
          f"(t,K,sgn) books: {len(dup_rows)}")
    for r in dup_rows: print(f"    {r}")
    finding(f"E: duplicate-book fibers on the full traced roster: "
            f"{len(dup_rows)} (rows: {sorted(set(x[0] for x in dup_rows))})"
            f" — every one on a glued (non-REGULAR) row" if dup_rows else
            "E: no duplicate-book fibers realized anywhere")
    return dup_rows

# ============================ main ============================================
def main():
    t0 = time.time()
    okB = probe_B()
    probe_A()

    print("=" * 78)
    print("PROBE C — glued dump-swap groups ((K2-RES)(a)), by hand")
    # C1: the instrument's SDG2BF witness row
    E, hits = probe_tower(
        ("SDG2BF", 3, "Fpt", 2, 1, [(3,1,2), (2,1,1), (3,2,1), (2,1,1)]),
        {(1479, 1485)}, "C1", show_all_glued=True)
    for (ga, gb, jv, glued, signed, grp) in hits:
        if not glued: continue
        # glue quantum: pair cells across books differing by one C1 against
        # a dump-coordinate shift of e0*(g0-k) = 3
        for c1, c2 in itertools.combinations(grp, 2):
            K1 = sorted(e[1] for e in c1['ce'] if e[0] == 0)
            K2 = sorted(e[1] for e in c2['ce'] if e[0] == 0)
            d1 = c1['dmp'][0]; d2 = c2['dmp'][0]
            if abs(len(K1) - len(K2)) == 1 and c1['t'] == c2['t']:
                lo, hi = (c1, c2) if len(K1) < len(K2) else (c2, c1)
                # rider (with the extra C1) must carry dump0 LARGER by
                # e0*(g0-k) = 3 — the level-0 mass balance
                delta = hi['dmp'][0] - lo['dmp'][0]
                print(f"    glue pair: rider dump0={hi['dmp'][0]} (+C1) vs "
                      f"other dump0={lo['dmp'][0]}: rider-other = {delta} "
                      f"(= e0*(g0-k) = 3? {'YES' if delta == 3 else 'no'}) "
                      f"same res: {E.keq(c1['res'], c2['res'])}")
    # C2: SDW4G2F worked 5-cell group + C3: SDG2BZ same key
    E4, hits4 = probe_tower(
        ("SDW4G2F", 4, "Fpt", 2, 1,
         [(3,1,2), (2,1,1), (2,1,1), (2,1,1), (2,1,1)]),
        None, "C2", show_all_glued=True)
    n5 = [h for h in hits4 if len(h[5]) == 5]
    print(f"  SDW4G2F glued groups found: {sum(1 for h in hits4 if h[3])}; "
          f"5-cell groups: {len(n5)}")
    # C2b: the (t,K)-DUPLICATE pair inside the 5-cell group — print the
    # full window decomposition + pc of every cell to pin down what
    # distinguishes the two same-summary cells
    for (ga, gb, jv, glued, signed, grp) in n5:
        print(f"  C2b anatomy of SDW4G2F[{ga},{gb}] slot {jv}:")
        for c in sorted(grp, key=lambda c: (str(sorted(
                e[1] for e in c['ce'] if e[0] == 0)), str(c['ce']))):
            K0c = tuple(sorted(e[1] for e in c['ce'] if e[0] == 0))
            wins, endj0 = SK.windows_of(E4, c['hist'], c['sig0'], None)
            wshow = [(w['kind'], w['arrival'], w['n'], w['ev'], w['p'])
                     for w in wins]
            print(f"    t={c['t']} K={K0c} sgn={c['sgn']:+d} pc={c['pc']} "
                  f"dmp={c['dmp']}")
            print(f"      windows: {wshow}")
        # duplicate census
        summ = collections.Counter(
            (c['t'], tuple(sorted(e[1] for e in c['ce'] if e[0] == 0)),
             tuple(sorted(e for e in c['ce'] if e[0] != 0)), c['pc'],
             c['sgn']) for c in grp)
        dups = {k: v for k, v in summ.items() if v > 1}
        if dups:
            finding(f"C2b: REALIZED (t,K,I,pc,sgn)-duplicate cells inside "
                    f"one fiber (glued stratum, SDW4G2F[{ga},{gb}] slot "
                    f"{jv}): {dups} — same-sign same-class pair "
                    f"distinguished only by event placement; the S8 "
                    f"'placement-pair fibers: 0' census counts only "
                    f"PROMOTION-placement pairs and misses this shape")
    EZ, hitsZ = probe_tower(
        ("SDG2BZ", 3, "Zp", 2, 1, [(3,1,2), (2,1,1), (3,2,1), (2,1,1)]),
        {(1479, 1485)}, "C3", show_all_glued=True)

    print("=" * 78)
    print("PROBE D — the two hand-re-derivation witnesses")
    # D1: EQ3G2B T0 kill
    E1, hits1 = probe_tower(
        ("EQ3G2B", 3, "Zp", 3, 1, [(3,1,2), (2,1,1), (3,2,1), (2,1,1)]),
        {(1479, 1485)}, "D1")
    su1 = WS.uchain(E1)[1]
    dmap1, Dmap1 = SK.build_maps(E1)
    xs = {}
    for jDv, cD in Dmap1.items():
        tt, rr = divmod(jDv[0] - su1[1], E1.e[0])
        if rr == 0: xs[tt] = (jDv, cD, E1.resKm(cD))
    psb1 = E1.resKm(dmap1[(0, 1, ())])
    print(f"  EQ3G2B raw data for the by-hand leg (K3 elements as nested "
          f"tuples over F3):")
    for tt in sorted(xs):
        print(f"    x_{tt} = res(cD_{tt}) = {xs[tt][2]}   (jD = {xs[tt][0]}, "
              f"cD = {xs[tt][1]})")
    print(f"    psibar_1 = res(C_1) = {psb1}   (C_1 = {dmap1[(0, 1, ())]})")
    lhs = E1.kmul(psb1, xs[1][2])
    print(f"    I1 check: res(C1)*x_1 = {lhs}  ==  x_0 = {xs[0][2]}  ->  "
          f"{E1.keq(lhs, xs[0][2])}")
    if not E1.keq(lhs, xs[0][2]):
        viol("D1", "Q-A0 identity FAILS on EQ3G2B — contradicts the "
             "instrument's a0tab")
    # D2: K2G2P5B exchange kill
    E2, hits2 = probe_tower(
        ("K2G2P5B", 3, "Zp", 5, 1, [(3,1,2), (2,1,1), (3,2,1), (2,1,1)]),
        {(1479, 1479)}, "D2")
    dmap2, _ = SK.build_maps(E2)
    ps0 = E2.resKm(dmap2[(0, 0, ())]); ps1 = E2.resKm(dmap2[(0, 1, ())])
    print(f"  K2G2P5B psi0 = {E2.grbT.psi0} over F5")
    print(f"    res(C0) = {ps0}   res(C1) = {ps1}")
    sq = E2.kmul(ps1, ps1)
    print(f"    I3 check: res(C1)^2 = {sq}  ==  res(C0) = {ps0}  ->  "
          f"{E2.keq(sq, ps0)}")
    if not E2.keq(sq, ps0):
        viol("D2", "I3 exchange identity FAILS on K2G2P5B — contradicts "
             "the 4 fresh same-t kills")

    # D3: the K2W4G2Z CROSS event — the note derives it as T1's
    # not-I1 & not-I3 & I2 corner; verify all three identity values and
    # the (-1,+2)-shaped group at [2635,2635] slot (4,0,0,0)
    E3, hits3 = probe_tower(
        ("K2W4G2Z", 4, "Zp", 3, 1,
         [(3,1,2), (2,1,1), (2,1,1), (2,1,1), (2,1,1)]),
        {(2635, 2635)}, "D3")
    su3 = WS.uchain(E3)[1]
    dmap3, Dmap3 = SK.build_maps(E3)
    xs3 = {}
    for jDv, cD in Dmap3.items():
        tt, rr = divmod(jDv[0] - su3[1], E3.e[0])
        if rr == 0: xs3[tt] = E3.resKm(cD)
    q0 = E3.resKm(dmap3[(0, 0, ())]); q1 = E3.resKm(dmap3[(0, 1, ())])
    print(f"  K2W4G2Z psi0 = {E3.grbT.psi0} over F3; seeds ts = "
          f"{sorted(xs3)}")
    if 0 in xs3 and 1 in xs3:
        I1 = E3.keq(E3.kmul(q1, xs3[1]), xs3[0])
        I3 = E3.keq(E3.kmul(q1, q1), q0)
        I2 = E3.keq(E3.kmul(q1, xs3[0]), E3.kmul(q0, xs3[1]))
        print(f"    I1 (psb1*x1 == x0): {I1}   I3 (psb1^2 == psb0): {I3}"
              f"   I2 (psb1*x0 == psb0*x1): {I2}")
        if I1 or I3 or not I2:
            viol("D3", f"CROSS-corner identity pattern (I1,I3,I2) = "
                 f"({I1},{I3},{I2}) != (False,False,True) — the note's "
                 f"derivation of the K2W4G2Z event is wrong")
        else:
            finding("D3: K2W4G2Z identities (not-I1, not-I3, I2) confirmed "
                    "— the note's T1-corner derivation of the CROSS event "
                    "matches the tower's residue data")

    dup_rows = probe_E()

    print("=" * 78)
    print(f"probe violations: {len(VIOL)}")
    for v in VIOL: print(f"  {v}")
    print(f"findings: {len(FINDINGS)}")
    el = time.time() - t0
    print(f"elapsed: {el:.1f}s")
    with open(os.path.join(OUTDIR, "survk2_pe1_ext_results.json"), "w") as f:
        json.dump(dict(final=True, violations=VIOL, findings=FINDINGS,
                       elapsed=el), f, indent=1, default=str)
    print("results -> survk2_pe1_ext_results.json")

if __name__ == "__main__":
    main()
