#!/usr/bin/env python3
"""CASE-HN3 gate census (written AFTER CASE_HN3_SEALED_PREDICTIONS.md).

Enumerates family F_H (f-bar = z^2(z+1)) block/cubic boxes at p=2 (O(2^8)) and
p=3 (O(3^6); marked O(3^7) extension for the entrance h0=3 leg), classifies reads
by a direct Montes walk, tallies per-(h0,h1) masses, and compares EXACTLY against
the sealed values. Long log -> /tmp/hn3_census.out; JSON -> results/case_hn3_results.json.
Usage: python3 case_hn3_gate.py [p2|p3|oracle|all]
"""
import json, os, subprocess, sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
LOG = open("/tmp/hn3_census.out", "a")
def log(*a):
    s = " ".join(str(x) for x in a)
    print(s); LOG.write(s + "\n"); LOG.flush()

FAILURES = []
def check(name, ok, detail=""):
    log(("PASS " if ok else "FAIL ") + name + (" | " + detail if detail else ""))
    if not ok:
        FAILURES.append((name, detail))
    return ok

def val(x, p, N):
    if x % p**N == 0:
        return N
    v = 0
    while x % p == 0:
        x //= p; v += 1
    return v

def digit(x, p, lvl):
    return (x // p**lvl) % p

def classify(b, c, p, N):
    """Montes walk on block z^2 + b z + c (v(b),v(c) >= 1). Returns
    (loops, terminal, shift): loops = [(t, ustar)...]; terminal in
    {('RAM', h1, lead), ('SPLIT', t), ('INERT', t), ('VERTEX',), ('DEEP',)};
    shift = accumulated recentering (sum ustar*p^t)."""
    pN = p**N
    loops, shift = [], 0
    inv2 = pow(2, -1, p) if p != 2 else None
    while True:
        vc, vb = val(c, p, N), val(b, p, N)
        if vc >= N:
            return loops, ('DEEP',), shift
        if 2 * vb < vc:
            return loops, ('VERTEX',), shift
        if vc % 2 == 1:
            return loops, ('RAM', vc, digit(c, p, vc)), shift
        t = vc // 2
        b_t, c_2t = (digit(b, p, t) if vb <= t else 0), digit(c, p, 2 * t)
        assert c_2t != 0
        if p == 2:
            if b_t != 0:
                return loops, ('INERT', t), shift   # y^2+y+1 irreducible over F_2
            ystar = 1
        else:
            disc = (b_t * b_t - 4 * c_2t) % p
            if disc != 0:
                kind = 'SPLIT' if pow(disc, (p - 1) // 2, p) == 1 else 'INERT'
                return loops, (kind, t), shift
            ystar = (-b_t * inv2) % p
        assert ystar != 0
        loops.append((t, ystar))
        s = ystar * p**t
        shift += s
        c = (s * s + b * s + c) % pN
        b = (b + 2 * s) % pN
        # (HV) hinge + landing-cell checks: recentered block back in the block cell
        assert val(c, p, N) >= 2 * t + 1, "hinge cancellation failed"
        assert val(b, p, N) >= t + 1, "b-line cancellation failed"

def listed_points(cap_h1):
    """Lattice points of L((1,3);{(2,4),(0,2)}) u L((2,5);{(2,4),(0,2)}), h1 <= cap."""
    pts = set()
    for (b0, b1) in [(1, 3), (2, 5)]:
        a = 0
        while b1 + 4 * a <= cap_h1:
            k = 0
            while b1 + 4 * a + 2 * k <= cap_h1:
                pts.add((b0 + 2 * a, b1 + 4 * a + 2 * k))
                k += 1
            a += 1
    return pts

def coarse_points(cap_h1):
    """L((1,3);{(1,2),(0,2)}) up to cap: the sealed coarse form."""
    pts = set()
    n1 = 0
    while 3 + 2 * n1 <= cap_h1:
        n2 = 0
        while 3 + 2 * n1 + 2 * n2 <= cap_h1:
            pts.add((1 + n1, 3 + 2 * n1 + 2 * n2))
            n2 += 1
        n1 += 1
    return pts

SEALED = {  # per-point (E, sealed census set) — S4/S6 of the seal
    2: {'N': 8, 'points': {(1, 3): 4, (2, 5): 7, (1, 5): 7, (3, 7): 10, (2, 7): 10, (1, 7): 10}},
    3: {'N': 6, 'points': {(1, 3): 4, (2, 5): 7, (1, 5): 7}},
}

def E_of(h0, h1):
    assert (3 * h1 - 1) % 2 == 0
    return (3 * h1 - 1) // 2

def block_census(p, N):
    """Walk the block box; return per-(h0,h1) gamma_H tallies, ladder tallies,
    entrance tallies, member lists."""
    pN = p**N
    gam = {}      # (h0,h1) -> {chain (u,lead): count}
    gam_members = {}  # (h0,h1) -> [(b, c, u, shift)]
    ladder = {}   # (h0,h1) -> count of loop-paths ending RAM(h1), first loop h0
    ladder_members = {}
    ent = {}      # h0 -> {u: count}
    other = {'VERTEX': 0, 'DEEP': 0, 'RAM0': 0, 'SPLIT': 0, 'INERT': 0}
    for b in range(0, pN, p):
        for c in range(0, pN, p):
            loops, term, shift = classify(b, c, p, N)
            if loops:
                h0, u = loops[0]
                ent.setdefault(h0, {}).setdefault(u, 0)
                ent[h0][u] += 1
            if term[0] == 'RAM':
                h1, lead = term[1], term[2]
                if loops:
                    key = (loops[0][0], h1)
                    ladder[key] = ladder.get(key, 0) + 1
                    ladder_members.setdefault(key, set()).add((b, c))
                    if len(loops) == 1:
                        gam.setdefault(key, {}).setdefault((loops[0][1], lead), 0)
                        gam[key][(loops[0][1], lead)] += 1
                        gam_members.setdefault(key, []).append((b, c, loops[0][1], shift))
                else:
                    other['RAM0'] += 1
            elif term[0] in other:
                other[term[0]] += 1
            else:
                other[term[0] if term[0] in other else 'SPLIT' if term[0] == 'SPLIT' else 'INERT'] += 1
    return gam, gam_members, ladder, ladder_members, ent, other

def run_block_layers(p, results):
    N = SEALED[p]['N']
    pts = SEALED[p]['points']
    cyl = p**(2 * (N - 1))
    cap_h1 = N - 1
    log(f"\n=== BLOCK CENSUS p={p}, N={N}, cylinder={cyl} ===")
    # sealed component-list arithmetic check (S2 coarse bijection, up to cap)
    check(f"p{p} S2 components == coarse set (cap h1<={cap_h1})",
          listed_points(cap_h1) == coarse_points(cap_h1),
          f"listed={sorted(listed_points(cap_h1))}")
    check(f"p{p} S2 listed-points-in-cap == sealed census set",
          listed_points(cap_h1) == set(pts), f"{sorted(listed_points(cap_h1))}")
    gam, gam_members, ladder, ladder_members, ent, other = block_census(p, N)
    results[f'p{p}_other'] = other
    # (L1) two-sided exactness
    realized = set(gam)
    check(f"p{p} L1 realized == listed (two-sided, zero orphans/strays)",
          realized == set(pts), f"realized={sorted(realized)} listed={sorted(pts)}")
    for (h0, h1), E in sorted(pts.items()):
        T_pred = (p - 1) ** 2
        cnt_pred = T_pred * cyl // p**E
        chains = gam.get((h0, h1), {})
        tot = sum(chains.values())
        check(f"p{p} L1 count at {(h0,h1)} == T*q^-E*cyl = {cnt_pred}", tot == cnt_pred, f"got {tot}")
        check(f"p{p} L1 witness T>=1 at {(h0,h1)}", tot >= 1)
        # (c) chain structure: T = (p-1)^2, u and lead each over F_p^x, uniform q^-E
        check(f"p{p} S4 chain count T at {(h0,h1)} == {T_pred}", len(chains) == T_pred,
              f"chains={sorted(chains)}")
        check(f"p{p} S4 chain set at {(h0,h1)} == FpX x FpX",
              set(chains) == {(u, l) for u in range(1, p) for l in range(1, p)})
        check(f"p{p} L2-block per-chain mass at {(h0,h1)} == q^-{E} (all chains)",
              all(v * p**E == cyl for v in chains.values()),
              f"per-chain counts {sorted(set(chains.values()))} vs {cyl // p**E}")
    results[f'p{p}_gamma_counts'] = {str(k): sum(v.values()) for k, v in sorted(gam.items())}
    return gam, gam_members, ladder, ladder_members, ent, cyl

def run_ladder_det_ent(p, gam, gam_members, ladder, ladder_members, ent, results):
    N = SEALED[p]['N']; pts = SEALED[p]['points']; cyl = p**(2 * (N - 1)); pN = p**N
    # (L5/d) ladder crosscheck at every censused point
    for (h0, h1) in sorted(pts):
        pred = (p - 1) ** 2 * cyl // p**(h0 + h1)
        got = ladder.get((h0, h1), 0)
        check(f"p{p} L5 ladder total at {(h0,h1)} == (p-1)^2*q^-(h0+h1)*cyl = {pred}",
              got == pred, f"got {got}")
        k = (h1 - 1) // 2 - h0
        check(f"p{p} L5 ladder == p^k * gamma_H count at {(h0,h1)} (k={k})",
              got == p**k * sum(gam.get((h0, h1), {}).values()))
    if p % 2 == 1:  # complete-the-square comparison, p odd
        inv2 = pow(2, -1, pN)
        for (h0, h1) in sorted(pts):
            cts = set()
            for b in range(0, pN, p):
                beta = (b * inv2) % pN
                if val(beta, p, N) != h0:
                    continue
                bsq4 = (beta * beta) % pN
                for c in range(0, pN, p):
                    if val((c - bsq4) % pN, p, N) == h1:
                        cts.add((b, c))
            check(f"p{p} L5 CTS set == ladder set at {(h0,h1)}",
                  cts == ladder_members.get((h0, h1), set()),
                  f"|CTS|={len(cts)} |ladder|={len(ladder_members.get((h0,h1),set()))}")
    # (S6/F6) determination level: strata are unions of full mod-p^(h1+1) cylinders
    for (h0, h1) in sorted(pts):
        M = p**(h1 + 1); expect = p**(2 * (N - h1 - 1))
        groups = {}
        for (b, c, u, shift) in gam_members[(h0, h1)]:
            groups.setdefault((b % M, c % M), []).append((u, shift % M))
        ok = all(len(v) == expect and len(set(v)) == 1 for v in groups.values())
        check(f"p{p} S6 determination level N={h1+1} at {(h0,h1)}: "
              f"{len(groups)} classes x {expect}", ok)
    # (L4-ENT) entrance family at h0 = 1,2,3 (p=3: 1,2 here; 3 via extension box)
    h0_list = [1, 2, 3] if p == 2 else [1, 2]
    for h0 in h0_list:
        chains = ent.get(h0, {})
        per = cyl // p**(3 * h0)
        check(f"p{p} L4-ENT count at h0={h0} == p-1 = {p-1}", len(chains) == p - 1,
              f"u set {sorted(chains)}")
        check(f"p{p} L4-ENT per-chain mass at h0={h0} == q^-{3*h0}",
              all(v == per for v in chains.values()),
              f"got {sorted(chains.values())} want {per}")
    check(f"p{p} L4-ENT chain count CONSTANT across h0 in {h0_list}",
          len({len(ent.get(h, {})) for h in h0_list}) == 1)
    results[f'p{p}_entrance'] = {h: dict(ent.get(h, {})) for h in h0_list}
    results[f'p{p}_ladder_counts'] = {str(k): v for k, v in sorted(ladder.items()) if k in pts}

def run_ent_extension_p3():
    """Marked O(3^7) extension box, entrance leg h0=3 only (FC4)."""
    p, N = 3, 7
    cyl = p**(2 * (N - 1))
    log(f"\n=== ENTRANCE EXTENSION p=3, N=7 (marked extension, FC4) ===")
    ent3 = {}
    pN = p**N
    for b in range(0, pN, p):
        for c in range(0, pN, p):
            loops, term, shift = classify(b, c, p, N)
            if loops and loops[0][0] == 3:
                ent3.setdefault(loops[0][1], 0)
                ent3[loops[0][1]] += 1
    per = cyl // p**9
    check("p3 L4-ENT(ext N=7) count at h0=3 == 2", len(ent3) == 2, f"u set {sorted(ent3)}")
    check(f"p3 L4-ENT(ext N=7) per-chain mass at h0=3 == q^-9 ({per} members)",
          all(v == per for v in ent3.values()), f"got {sorted(ent3.values())}")
    return ent3

def run_L4_constancy(p, gam, results):
    pts = SEALED[p]['points']
    inleg = [(1, 3), (1, 5), (1, 7)] if p == 2 else [(1, 3), (1, 5)]
    crossleg = [(1, 3), (2, 5), (3, 7)] if p == 2 else [(1, 3), (2, 5)]
    Tin = [len(gam.get(pt, {})) for pt in inleg]
    Tx = [len(gam.get(pt, {})) for pt in crossleg]
    check(f"p{p} L4 in-component T constant on {inleg} [M4b-T shadow]",
          len(set(Tin)) == 1 and Tin[0] == (p - 1) ** 2, f"T={Tin}")
    check(f"p{p} L4 cross-component T constant on {crossleg} [XHD-u-X count face]",
          len(set(Tx)) == 1 and Tx[0] == (p - 1) ** 2, f"T={Tx}")
    results[f'p{p}_L4'] = {'in': Tin, 'cross': Tx}

def cubic_census(p, results):
    """L2/L3: full cubic box (a,b,c) mod p^N, (a,b,c)-bar=(1,0,0); Newton unit root,
    Hensel block, classify; rows per prefix class a mod p^2."""
    N = SEALED[p]['N']; pts = SEALED[p]['points']; pN = p**N
    log(f"\n=== CUBIC CENSUS p={p}, N={N} ({(p**(N-1))**3} members) ===")
    blockcls = {}
    for b in range(0, pN, p):
        for c in range(0, pN, p):
            loops, term, _ = classify(b, c, p, N)
            blockcls[(b, c)] = ((loops[0][0], term[1], loops[0][1], term[2])
                                if term[0] == 'RAM' and len(loops) == 1 else None)
    inv = [0] * pN
    for u in range(1, pN):
        if u % p:
            inv[u] = pow(u, -1, pN)
    rows = {}       # prefix a mod p^2 -> {(h0,h1) -> {chain: count}}
    hensel_bad = 0
    for a in range(1, pN, p):
        pref = a % p**2
        rowa = rows.setdefault(pref, {})
        for b in range(0, pN, p):
            for c in range(0, pN, p):
                r = pN - 1  # -1 mod p^N, lift of the unit root
                for _ in range(3):
                    fr = (((r + a) * r + b) * r + c) % pN
                    fpr = ((3 * r + 2 * a) * r + b) % pN
                    r = (r - fr * inv[fpr]) % pN
                if (((r + a) * r + b) * r + c) % pN != 0:
                    hensel_bad += 1; continue
                B = (a + r) % pN
                C = (b + r * B) % pN
                if c != (-r * C) % pN or B % p != 0 or C % p != 0:
                    hensel_bad += 1; continue
                g = blockcls[(B, C)]
                if g:
                    h0, h1, u, lead = g
                    rowa.setdefault((h0, h1), {}).setdefault((u, lead), 0)
                    rowa[(h0, h1)][(u, lead)] += 1
    check(f"p{p} L2/L3 Hensel pipeline: 0 factorization failures", hensel_bad == 0,
          f"bad={hensel_bad}")
    classsize = p**(3 * N - 4)  # p^{3(N-1)} cylinder members / p prefix classes
    prefs = sorted(rows)
    check(f"p{p} L3 prefix classes == {p} representatives of the source cell",
          len(prefs) == p, f"{prefs}")
    base = prefs[0]  # a == 1 mod p^2: THE fixed representative+prefix (FC2)
    l2pts = [(1, 3), (2, 5), (3, 7)] if p == 2 else [(1, 3), (2, 5)]
    for pt in l2pts:
        E = pts[pt]
        chains = rows[base].get(pt, {})
        ok = (len(chains) == (p - 1) ** 2
              and all(v * p**E == classsize for v in chains.values()))
        check(f"p{p} L2 per-chain conditional mass at {pt} == q^-{E} "
              f"[rep a={base} mod p^2]", ok,
              f"counts {sorted(set(chains.values()))} want {classsize // p**E}")
    ok3 = all(rows[pr] == rows[base] for pr in prefs[1:])
    check(f"p{p} L3 rows IDENTICAL across all {p} representatives", ok3,
          "" if ok3 else "differing prefixes: " +
          str([pr for pr in prefs[1:] if rows[pr] != rows[base]]))
    results[f'p{p}_L2_row'] = {str(k): sum(v.values()) for k, v in sorted(rows[base].items())}
    return rows

GP = os.path.expanduser("~/.local/bin/gp")

def oracle_layer(p, gam_members, results, cap=40, prec=24):
    """L5 oracle: PARI factorpadic on sampled gamma_H cubics; verdict must be
    (linear) x (irreducible ramified quadratic) = sigma-type (2,1)ram, and the
    quadratic factor must equal the census's Hensel block mod p^N."""
    N = SEALED[p]['N']; pN = p**N
    tasks = []  # (h0, h1, a, b_f, c_f, B, C, shift)
    for (h0, h1), mem in sorted(gam_members.items()):
        step = max(1, len(mem) // cap)
        for (B, C, u, shift) in mem[::step][:cap]:
            r = pN - 1  # one lift of the unit root -1
            a_f, b_f, c_f = (B - r) % pN, (C - r * B) % pN, (-r * C) % pN
            tasks.append((h0, h1, a_f, b_f, c_f, B, C, shift))
    lines = ["default(parisize, 64000000);"]
    for i, (h0, h1, a, b, c, B, C, s) in enumerate(tasks):
        lines.append(
            f"F = factorpadic(x^3 + {a}*x^2 + {b}*x + {c}, {p}, {prec});"
            f" nf = matsize(F)[1];"
            f" degs = vecsort(vector(nf, j, poldegree(F[j,1])));"
            f" if(nf == 2 && degs == [1,2],"
            f"   g = if(poldegree(F[1,1])==2, F[1,1], F[2,1]);"
            f"   V = Vec(liftall(g));"
            f"   print(\"R{i} OK \", V[1], \" \", V[2], \" \", V[3]),"
            f"   print(\"R{i} BAD \", nf));")
    script = "/tmp/hn3_oracle.gp"
    with open(script, "w") as fh:
        fh.write("\n".join(lines) + "\nquit\n")
    out = subprocess.run([GP, "-q", "-f", script], capture_output=True, text=True, timeout=1200)
    ok_all, n_checked = True, 0
    replies = {ln.split()[0]: ln.split() for ln in out.stdout.splitlines() if ln.startswith("R")}
    for i, (h0, h1, a, b, c, B, C, s) in enumerate(tasks):
        w = replies.get(f"R{i}")
        good = False
        if w and w[1] == "OK" and len(w) == 5 and int(w[2]) == 1:
            q1, q0 = int(w[3]), int(w[4])
            if q1 % pN == B and q0 % pN == C:   # factor == census Hensel block mod p^N
                Qs = (s * s + q1 * s + q0) % p**prec  # recentered const term
                good = (val(Qs, p, prec) == h1)       # the ramified (2,h1) read
        ok_all &= good
        n_checked += 1
        if not good:
            check(f"p{p} L5 oracle member {(h0,h1)} #{i} f=x^3+{a}x^2+{b}x+{c}",
                  False, str(w))
    check(f"p{p} L5 oracle: all {n_checked} sampled verdicts = (1)x(2)ram, "
          f"factor == Hensel block, v(Q(shift)) = h1", ok_all)
    results[f'p{p}_oracle_checked'] = n_checked

def run_p(p, do_cubic=True, do_oracle=True):
    results = {}
    gam, gam_members, ladder, ladder_members, ent, cyl = run_block_layers(p, results)
    run_ladder_det_ent(p, gam, gam_members, ladder, ladder_members, ent, results)
    run_L4_constancy(p, gam, results)
    if p == 3:
        run_ent_extension_p3()
    if do_cubic:
        cubic_census(p, results)
    if do_oracle:
        oracle_layer(p, gam_members, results)
    return results

def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "all"
    allres = {}
    if mode in ("p2", "all"):
        allres.update(run_p(2))
    if mode in ("p3", "all"):
        allres.update(run_p(3))
    allres['failures'] = [list(f) for f in FAILURES]
    allres['verdict'] = "PASS" if not FAILURES else f"FAIL ({len(FAILURES)} mismatches)"
    outp = os.path.join(HERE, "results", f"case_hn3_results_{mode}.json")
    with open(outp, "w") as fh:
        json.dump(allres, fh, indent=1, default=str)
    log(f"\n==== CASE-HN3 [{mode}] VERDICT: {allres['verdict']} ====")
    log(f"results -> {outp}")

if __name__ == "__main__":
    main()
