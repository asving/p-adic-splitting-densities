#!/usr/bin/env python3
"""wmultdcx_pe1_ext.py — PE1 hostile-verification instrument (NEW file; the
committed referees wmultdcx_stress.py / wmultdcx_derive_checks.py are consumed
READ-ONLY and never mutated).

Purpose: INDEPENDENT re-derivation of the sealed PID-MAX divergences (the 72)
and of the W-D4/W-D6 layer, with freshly written code paths for everything
that the committed runners implement themselves:
  * gamma split (eq-12 digit split) — reimplemented from the S1 display;
  * anchors a-hat = pi^u1 * prod Phi_l^{s_{l+1}} — rebuilt from the split;
  * u-chain / pools / carries — reimplemented from the S6.1 display;
  * the two-stage E1-priority promotion-profiled tree — reimplemented from
    the S2.2 child inventory (recursive structure, separate bookkeeping);
  * promotion-profile part sums and the nonzero-part maxima.
Engine primitives consumed (shared object language only): PE.Eng/prep
(Phis, Chat, Dcells, digit_split, corr_table, cellpoly, ring ops) and the
grb polynomial arithmetic.  Every canonical division used is INDEPENDENTLY
verified by re-multiplication (Q*Phi + R == input, deg R < deg Phi), so the
quotient side does not rest on pdivmod's internals.

Legs:
  L1  full independent replication of the PID-MAX census on the EXACT sealed
      412-row selection (keys read from the committed stress results JSON,
      never recomputed): my divergence set must equal the sealed 72 records
      (tower, key, level, maxnz, c) exactly.
  L2  detailed re-derivation dumps for 7 chosen instances (incl. both sealed
      "+2" witnesses and both "sharpest" pc_2=3 witnesses, one g0>=2, one
      m=4 flat, one replica XM3B) with full path-edge traces for the small
      ones (hand-checkable).
  L3  W-D4 cellwise threshold + W-D6 dump-free-principal cap + W-D6c channel
      re-checked by MY bookkeeping on all rows; count beyond-floor cells on
      DEAD rows separately (input to the S9 obstruction reading).
  L4  liveness of every divergent row recomputed (Q1 != 0 + locus clause).
"""
import sys, os, json, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import rmengine_pe_reimpl as PE
from grb_order2_check import (pnorm, padd, pneg, pmul, ppow, pscal,
                              pdivmod, w0)

def prod(xs):
    r = 1
    for x in xs: r *= x
    return r

# ---------- my own eq-12 split (fresh: brute force over s in [0,e)) ----------
def my_eq12(beta, e, h):
    if e == 1:
        return 0, beta
    for s in range(e):
        if (beta - s*h) % e == 0:
            return s, (beta - s*h)//e
    raise AssertionError("no eq12 digit (gcd(e,h) != 1?)")

# ---------- my own gamma split + anchor (from the S1 display) ----------
def my_split(E, gamma):
    m = E.m
    wPhi = {0: 0}
    for l in range(1, m+1):
        wPhi[l] = E.e[l-1]*E.g[l-1]*E.gam[l]
    s = {}; b = gamma
    for l in range(m+1, 0, -1):
        sl, ul = my_eq12(b, E.e[l-1], E.h[l-1])
        s[l] = sl
        b = ul - sl*wPhi[l-1]
    return s, b

def my_anchor(E, s, u1):
    R = E.R
    a = pscal(R, R["pi_pow"](u1), [R["one"]])
    for l in range(E.m):
        for _ in range(s[l+1]):
            a = pmul(R, a, E.Phis[l])
    return pnorm(R, a)

# ---------- my own u-chain / pools / carries (from the S6.1 display) ----------
def my_uchain(E):
    m = E.m
    u = {m: E.gam[m+1]}; su = {}
    for l in range(m, 1, -1):
        s, _ = my_eq12(u[l], E.e[l-1], E.h[l-1])
        su[l] = s
        num = u[l] - s*E.gam[l]
        assert num % E.e[l-1] == 0 and num >= 0, "u-chain integrality"
        u[l-1] = num//E.e[l-1]
    su[1], _ = my_eq12(u[1], E.e[0], E.h[0])
    return u, su

def my_pools(E, sA, sB, su):
    m = E.m
    cs = []; c = 0
    for l in range(1, m):
        pool = sA[l] + sB[l] + su[l] + c
        c = pool//E.e[l-1]
        cs.append(c)
    D = sA[m] + sB[m] + su[m]
    return cs, D

# ---------- verified canonical division (re-multiplication check) ----------
def my_quo(E, A, B):
    R = E.R
    Q, Rm = pdivmod(R, A, B)
    # independent verification: Q*B + Rm == A and deg Rm < deg B
    chk = padd(R, pmul(R, Q, B), Rm)
    assert not pnorm(R, padd(R, chk, pneg(R, A))), "division re-mult FAILED"
    assert len(pnorm(R, Rm)) - 1 < len(pnorm(R, B)) - 1 or not pnorm(R, Rm), \
        "division remainder degree FAILED"
    return Q, Rm

# ---------- MY two-stage tree (fresh implementation of S2.2) ----------
# node: dict(sign, b, j, pc, dmp, ncorr, jD, prin, junk)
#   pc[i] = promotions into level i+1 (pc[m-1] = Phi_m exits)

def my_reduce(E, seeds, trace=None):
    """returns (exits, leaves); breadth-first, freshly written."""
    R = E.R; m = E.m
    corr = E.corr_table()
    exits, leaves = [], []
    frontier = list(seeds)
    guard = 0
    while frontier:
        nxt = []
        for nd in frontier:
            guard += 1
            assert guard < 2000000, "tree too large"
            j = nd["j"]
            lvl = None
            for l in range(m):
                if j[l] >= E.P[l]:
                    lvl = l; break
            if lvl is None:
                leaves.append(nd); continue
            kids = []
            if lvl <= m-2:
                k2 = dict(nd); k2["j"] = tuple(
                    v - E.P[lvl] if t == lvl else (v+1 if t == lvl+1 else v)
                    for t, v in enumerate(j))
                k2["pc"] = tuple(v+1 if t == lvl else v
                                 for t, v in enumerate(nd["pc"]))
                kids.append(("promo", k2))
            else:
                k2 = dict(nd); k2["j"] = tuple(
                    v - E.P[m-1] if t == m-1 else v for t, v in enumerate(j))
                k2["pc"] = tuple(v+1 if t == m-1 else v
                                 for t, v in enumerate(nd["pc"]))
                kids.append(("exit", k2))
            for (kk, dcells) in corr[lvl]:
                for (cd, av) in dcells:
                    Lc, Xc, Yc = E.digit_split(nd["b"], cd)
                    base = list(j)
                    base[lvl] -= E.P[lvl] - E.e[lvl]*kk
                    dmp = list(nd["dmp"])
                    for t in range(min(lvl, len(av))):
                        base[t] += av[t]; dmp[t] += av[t]
                    nc = tuple(v+1 if t == lvl else v
                               for t, v in enumerate(nd["ncorr"]))
                    for cc, isjunk, dj0 in ((Lc, 0, 0), (Xc, 1, 0), (Yc, 1, 1)):
                        if not pnorm(R, cc): continue
                        k3 = dict(nd)
                        k3["sign"] = -nd["sign"]; k3["b"] = cc
                        jj = list(base); jj[0] += dj0
                        dd = list(dmp); dd[0] += dj0
                        k3["j"] = tuple(jj); k3["dmp"] = tuple(dd)
                        k3["ncorr"] = nc
                        k3["junk"] = nd["junk"] + isjunk
                        kids.append(("corr" + ("Y" if dj0 else
                                               ("X" if isjunk else "L")), k3))
            for typ, kd in kids:
                if trace is not None:
                    trace.append((typ, nd, kd))
                if typ == "exit":
                    exits.append(kd)
                else:
                    nxt.append(kd)
        frontier = nxt
    return exits, leaves

def my_cellsum(E, nodes):
    R = E.R
    acc = []
    for nd in nodes:
        lp = E.cellpoly(nd["b"], nd["j"])
        acc = padd(R, acc, lp if nd["sign"] > 0 else pneg(R, lp))
    return pnorm(R, acc)

def run_instance(E, prin, ga, gb, verbose=False):
    """full two-stage profiled trace for one pair; returns record."""
    R = E.R; m = E.m
    sA, u1a = my_split(E, ga)
    sB, u1b = my_split(E, gb)
    aA = my_anchor(E, sA, u1a)
    aB = my_anchor(E, sB, u1b)
    u, su = my_uchain(E)
    cs, D = my_pools(E, sA, sB, su)
    etop = E.e[m-1]
    kdef = 2*etop - D
    # TRACK
    strack = (sA[m+1] == E.e[m]-1 and sB[m+1] == E.e[m]-1)
    prodp = pmul(R, aA, aB)
    E1, rem0 = my_quo(E, prodp, E.Phis[m])
    track = strack and bool(pnorm(R, E1))
    # measured liveness (locus clause per the stress display)
    Q1, rem1 = my_quo(E, pmul(R, E1, E.Chat), E.Phis[m])
    Tsum = sA[m+1] + sB[m+1]
    locus = ((Tsum//E.e[m] == 1 and strack and E.e[m] >= 2)
             or (Tsum == E.e[m]-1 and E.e[m] == 1))
    live = bool(pnorm(R, Q1)) and locus
    # stage 1 (my tree)
    z = (0,)*m
    seed = dict(sign=1,
                b=pscal(R, R["pi_pow"](u1a+u1b), [R["one"]]),
                j=tuple(sA[l+1] + sB[l+1] for l in range(m)),
                pc=z, dmp=z, ncorr=z, jD=None, prin=False, junk=0)
    # W-D1 check: product == formal cell
    assert not pnorm(R, padd(R, prodp,
                             pneg(R, E.cellpoly(seed["b"], seed["j"])))), \
        "W-D1 seed identity FAILED"
    tr = [] if verbose else None
    ex1, lv1 = my_reduce(E, [seed], tr)
    assert my_cellsum(E, ex1) == pnorm(R, E1), "stage-1 exits != E1IH"
    assert my_cellsum(E, lv1) == pnorm(R, rem0), "stage-1 leaves != rem"
    # stage 2 seeding
    seeds2 = []
    for nd in ex1:
        for (cD, jD) in E.Dcells:
            Lc, Xc, Yc = E.digit_split(nd["b"], cD)
            js = tuple(nd["j"][l] + jD[l] for l in range(m))
            isp = (tuple(jD) == prin)
            for cc, isjunk, dj0 in ((Lc, 0, 0), (Xc, 1, 0), (Yc, 1, 1)):
                if not pnorm(R, cc): continue
                jj = list(js); jj[0] += dj0
                dd = list(nd["dmp"]); dd[0] += dj0
                seeds2.append(dict(sign=nd["sign"], b=cc, j=tuple(jj),
                                   pc=nd["pc"], dmp=tuple(dd),
                                   ncorr=nd["ncorr"], jD=tuple(jD), prin=isp,
                                   junk=nd["junk"] + isjunk))
    ex2, lv2 = my_reduce(E, seeds2, tr)
    assert my_cellsum(E, ex2) == pnorm(R, Q1), "stage-2 exits != Q1"
    assert my_cellsum(E, lv2) == pnorm(R, rem1), "stage-2 leaves != rem"
    # profile parts
    maxnz = [None]*(m-1)
    for l in range(1, m):
        parts = {}
        for nd in ex2:
            parts.setdefault(nd["pc"][l-1], []).append(nd)
        for kk, nds in parts.items():
            if pnorm(R, my_cellsum(E, nds)):
                if maxnz[l-1] is None or kk > maxnz[l-1]:
                    maxnz[l-1] = kk
    # W-D4 cellwise + W-D6 dump-free cap + W-D6c channels (my bookkeeping)
    wd4_fail = wd6_fail = wd6c_fail = 0
    beyond = 0; beyond_dead = 0
    for nd in ex2:
        assert nd["pc"][m-1] == 2, "Q1 cell without exactly 2 exits"
        pi_top = nd["pc"][m-2]
        r = nd["ncorr"][m-1]
        if pi_top != kdef + etop*r + nd["j"][m-1] or pi_top < kdef:
            wd4_fail += 1
        dfree = (sum(nd["dmp"]) == 0)
        cP = []
        cp = 0
        for l in range(1, m):
            cp = (sA[l] + sB[l] + su[l] + cp)//E.P[l-1]
            cP.append(cp)
        if dfree and nd["prin"]:
            if any(nd["pc"][l-1] > cP[l-1] for l in range(1, m)):
                wd6_fail += 1
        isbeyond = any(nd["pc"][l-1] > cs[l-1] for l in range(1, m))
        if isbeyond:
            beyond += 1
            if not live: beyond_dead += 1
            if dfree and nd["prin"]:
                wd6c_fail += 1
    if verbose and tr is not None:
        print(f"    -- full edge trace ({len(tr)} edges):")
        for typ, par, kid in tr:
            print(f"       {typ:6s} j{list(par['j'])}->j{list(kid['j'])} "
                  f"pc{list(kid['pc'])} dmp{list(kid['dmp'])} "
                  f"sign{kid['sign']} junk{kid['junk']}")
        print(f"    -- Q1 cells ({len(ex2)}):")
        for nd in ex2:
            print(f"       sign={nd['sign']} j={list(nd['j'])} "
                  f"pc={list(nd['pc'])} dmp={list(nd['dmp'])} "
                  f"ncorr={list(nd['ncorr'])} jD={nd['jD']} prin={nd['prin']} "
                  f"w0(b)={w0(R, nd['b'])}")
    return dict(key=(ga, gb), cs=cs, D=D, kdef=kdef, live=live, track=track,
                maxnz=maxnz, ncells=len(ex2), beyond=beyond,
                beyond_dead=beyond_dead, wd4_fail=wd4_fail,
                wd6_fail=wd6_fail, wd6c_fail=wd6c_fail,
                su={k: v for k, v in su.items()}, u={k: v for k, v in u.items()})

# ------------------------------ main ------------------------------
def main():
    t0 = time.time()
    sealed = json.load(open(os.path.join(HERE, "wmultdcx_stress_results.json")))
    sealed_div = [(d[1], tuple(d[2]["key"]), d[2]["level"], d[2]["maxnz"],
                   d[2]["c"]) for d in sealed["pid_divergences"]]
    rows_by_tower = {t["tag"]: [tuple(r["key"]) for r in t.get("pid", [])]
                     for t in sealed["towers"]}
    ROSTER = {s[0]: s for s in
              __import__("wmultdcx_stress").ROSTER}

    detailed = [
        ("W3FMID",  (95, 95),     True),   # small; full edge dump
        ("W3DEEP",  (659, 667),   False),
        ("W3DEEP4", (1263, 1271), False),  # sealed +2 witness
        ("W3TRK1",  (327, 335),   False),  # sealed +2 witness
        ("W3TRK1",  (335, 335),   False),  # sharpest: pc_2 = 3 > 2 = L-CAP
        ("W3G2A",   (687, 687),   False),  # sharpest at g0 = 2
        ("XM3B",    (1055, 1055), False),  # replica, d0 = 2, g0 = 2
        ("W4FLAT",  (399, 399),   False),  # m = 4, flat interior
    ]
    print("== PE1 independent instrument ==")
    print("\n-- L2: chosen-instance re-derivations --")
    mydivs = []
    towers_done = {}
    all_stats = dict(rows=0, cells=0, beyond=0, beyond_dead=0,
                     wd4=0, wd6=0, wd6c=0, live=0)

    def get_tower(tag):
        if tag not in towers_done:
            spec = ROSTER[tag]
            E = PE.Eng(spec[1], spec[2], spec[3], spec[4], spec[5], tag)
            PE.prep(E)
            _, su = my_uchain(E)
            prin = tuple(su[l+1] for l in range(E.m))
            towers_done[tag] = (E, prin)
        return towers_done[tag]

    for tag, key, verb in detailed:
        E, prin = get_tower(tag)
        rec = run_instance(E, prin, key[0], key[1], verbose=verb)
        sd = [d for d in sealed_div if d[0] == tag and d[1] == key]
        print(f"  {tag} {key}: u={rec['u']} su={rec['su']}")
        print(f"    cs={rec['cs']} D={rec['D']} kdef={rec['kdef']} "
              f"live={rec['live']} track={rec['track']} ncells={rec['ncells']}")
        print(f"    MY maxnz per level: {rec['maxnz']}  "
              f"(sealed claims: {[(d[2], d[3], d[4]) for d in sd]})")
        for d in sd:
            lvl, mx, c = d[2], d[3], d[4]
            ok = (rec["maxnz"][lvl-1] == mx and rec["cs"][lvl-1] == c
                  and mx > c)
            print(f"    sealed divergence level {lvl}: maxnz {mx} > c {c}  "
                  f"-> MY verdict: {'CONFIRMED' if ok else 'MISMATCH'}")
        print(f"    W-D4 fails: {rec['wd4_fail']}  W-D6 fails: "
              f"{rec['wd6_fail']}  W-D6c fails: {rec['wd6c_fail']}  "
              f"beyond-floor cells: {rec['beyond']}")

    print("\n-- L1+L3: full replication on the sealed 412-row selection --")
    for tag, keys in sorted(rows_by_tower.items()):
        E, prin = get_tower(tag)
        for key in keys:
            rec = run_instance(E, prin, key[0], key[1])
            all_stats["rows"] += 1
            all_stats["cells"] += rec["ncells"]
            all_stats["beyond"] += rec["beyond"]
            all_stats["beyond_dead"] += rec["beyond_dead"]
            all_stats["wd4"] += rec["wd4_fail"]
            all_stats["wd6"] += rec["wd6_fail"]
            all_stats["wd6c"] += rec["wd6c_fail"]
            if rec["live"]: all_stats["live"] += 1
            for l in range(1, E.m):
                mx = rec["maxnz"][l-1]
                if mx is not None and mx > rec["cs"][l-1]:
                    mydivs.append((tag, key, l, mx, rec["cs"][l-1]))
    myset = set(mydivs)
    sealedset = set(sealed_div)
    print(f"rows={all_stats['rows']} cells={all_stats['cells']} "
          f"live rows={all_stats['live']}")
    print(f"MY divergences: {len(myset)}; sealed: {len(sealedset)}; "
          f"SET-EQUAL: {myset == sealedset}")
    if myset != sealedset:
        print("  only mine:", sorted(myset - sealedset))
        print("  only sealed:", sorted(sealedset - myset))
    print(f"W-D4 cellwise failures: {all_stats['wd4']} (predicted 0)")
    print(f"W-D6 dump-free-principal cap failures: {all_stats['wd6']} "
          f"(predicted 0)")
    print(f"W-D6c channel failures: {all_stats['wd6c']} (predicted 0)")
    print(f"beyond-floor cells: {all_stats['beyond']} (committed: 112); "
          f"of which on DEAD rows: {all_stats['beyond_dead']}")
    print(f"elapsed {time.time()-t0:.1f}s")
    return 0

if __name__ == "__main__":
    sys.exit(main())
