#!/usr/bin/env python3
"""k2close_pe1_ext.py — K2CLOSE-PE1 (first hostile pass on the assembled
K2-CLOSE program): the verifier's OWN independent probe.  Fresh
implementations throughout — nothing imported from k2close_enum.py /
k2close_verdicts.py except (read-only) the committed artifacts they wrote.

PROBES
  A  K2-L11 kernel identity: {v in Z^4 : deg v = 0, phi v = 0} == <I1, I3>
     (integral saturation), by direct parameterization + brute-force box.
  B  Independent closed-partition state spaces for spot shapes (GS-02,
     GS-08, GS-11, GS-40, AS-03, AS-10), transcribed BY HAND from the
     committed shape table, via full Bell-partition enumeration + a fresh
     integer-lattice membership routine (NOT the runners' BFS):
       - GS-40: total closed partitions must be 53, none SD-L7 protected;
       - GS-11 / AS-10: no closed partition protected (T-invariant check
         done exhaustively, not by shortcut);
       - GS-08: corner c01/c11 (I3 imposed) universal protection; c10/c00
         kill states exist; full merge nets -1;
       - GS-02: kill (glue-merge DEAD) state exists in every corner;
       - AS-03: full merge net -2 (= PROT2K under odd char), generic
         (-1,-1) unprotected.
  C  T-invariant audit of the whole committed verdict table (re-parsed):
     NOVEL <=> (main: |T|>=2 or GS-40) / (annex: |T|>=2 and not 2^k);
     every main CONDITIONAL has |T| <= 1.
  D  GLUE-DEGEN independent census straight from the md5-pinned
     survk2_instrument_results.json: glued bottom groups (>= 2 distinct
     interior books) at beta_min on the three glued towers; per group the
     multiset of per-cell 'res' strings must be single-valued (one in-vivo
     class); tally 28 net-0 + 10 net +-1 over exactly 38 groups/29 rows.
  E  SPOT-1..4 of K2CLOSE_LEGS23 S4, re-run via the committed
     survk2_derive_checks.legal_drains_g2 (read-only import).

Verdict lines are printed per probe; any FAIL is a finding for the PE1
report, not a repair (this pass fixes nothing).
"""
import json, os, itertools, hashlib, collections
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
FAILS = []
def check(name, ok, detail=""):
    print(("PASS" if ok else "FAIL"), name, detail)
    if not ok:
        FAILS.append((name, detail))

# ---------- fresh exact integer lattice membership (fraction-free Gauss) ----
def in_lattice(gens, v):
    """v in Z-span(gens)? Solve over Q by Gaussian elimination, then check
    the solution is integral via iterative reduction (Hermite-style)."""
    # Hermite normal form by column ops on the generator matrix (rows=dim).
    import copy
    gens = [list(g) for g in gens if any(g)]
    if not gens:
        return not any(v)
    v = list(v)
    dim = len(v)
    rows = [list(g) for g in gens]
    # integer row echelon (like HNF on rows): eliminate column by column
    rows = [r[:] for r in rows]
    pivots = []
    col = 0
    r0 = 0
    while col < dim and r0 < len(rows):
        # find rows with nonzero in col at/after r0; gcd-reduce them
        idxs = [i for i in range(r0, len(rows)) if rows[i][col] != 0]
        if not idxs:
            col += 1
            continue
        # extended gcd cascade
        i0 = idxs[0]
        rows[r0], rows[i0] = rows[i0], rows[r0]
        for i in range(r0 + 1, len(rows)):
            while rows[i][col] != 0:
                q = rows[r0][col] // rows[i][col]
                rows[r0] = [a - q * b for a, b in zip(rows[r0], rows[i])]
                rows[r0], rows[i] = rows[i], rows[r0]
        if rows[r0][col] < 0:
            rows[r0] = [-a for a in rows[r0]]
        pivots.append((r0, col))
        r0 += 1
        col += 1
    # reduce v
    w = v[:]
    for (r, c) in pivots:
        if w[c] != 0:
            if w[c] % rows[r][c] != 0:
                return False
            q = w[c] // rows[r][c]
            w = [a - q * b for a, b in zip(w, rows[r])]
    return not any(w)

def in_qspan(gens, v):
    gens = [list(g) for g in gens if any(g)]
    if not gens:
        return not any(v)
    rows = [[Fraction(x) for x in g] for g in gens]
    w = [Fraction(x) for x in v]
    dim = len(w)
    r0 = 0
    for col in range(dim):
        piv = next((i for i in range(r0, len(rows)) if rows[i][col] != 0),
                   None)
        if piv is None:
            continue
        rows[r0], rows[piv] = rows[piv], rows[r0]
        for i in range(len(rows)):
            if i != r0 and rows[i][col] != 0:
                f = rows[i][col] / rows[r0][col]
                rows[i] = [a - f * b for a, b in zip(rows[i], rows[r0])]
        if w[col] != 0:
            f = w[col] / rows[r0][col]
            w = [a - f * b for a, b in zip(w, rows[r0])]
        r0 += 1
    return not any(w)

# ---------- Probe A: the K2-L11 kernel --------------------------------------
# coords (x0, x1, ps0, ps1)
I1 = (1, -1, 0, -1)
I3 = (0, 0, 1, -2)
def probe_A():
    ok = True
    N = 6
    for v in itertools.product(range(-N, N + 1), repeat=4):
        deg = v[0] + v[1]
        phi = 2 * v[2] + v[3] - v[1]
        inker = (deg == 0 and phi == 0)
        # candidate decomposition alpha = v[0], beta = v[2]
        a, b = v[0], v[2]
        dec = tuple(a * x + b * y for x, y in zip(I1, I3))
        indec = (dec == v)
        if inker != indec:
            ok = False
            print("  kernel mismatch at", v)
    check("A.kernel == <I1,I3> integrally (box +-6)", ok)
    # saturation: I2 = I1 - I3, box-(b) identity = I1 + I3
    check("A.I2 == I1 - I3", tuple(x - y for x, y in zip(I1, I3))
          == (1, -1, -1, 1))
    check("A.box(b) x0ps0=x1ps1^3 == I1 + I3",
          tuple(x + y for x, y in zip(I1, I3)) == (1, -1, 1, -3))

# ---------- Probe B: independent state spaces --------------------------------
# hand transcription from committed k2close_shape_table.md:
#   cell -> (fiber, dt, K, net)
SHAPES = {
 "GS-02": [(0, 0, (), -1), (1, 0, (1,), +1)],
 "GS-08": [(0, 0, (0,), -1), (0, 0, (1, 1), +1), (1, 0, (1,), -1)],
 "GS-11": [(0, 0, (0,), -2), (0, 0, (1, 1), +1), (1, 0, (1,), -1)],
 "GS-40": [(0, 0, (0,), -2), (0, 0, (1, 1), +1), (0, 1, (0, 1), +4),
           (0, 1, (1, 1, 1), -1),
           (1, 0, (1,), -1), (1, 1, (0,), -2), (1, 1, (1, 1), +1)],
 "AS-03": [(0, 0, (), -1), (1, 1, (), -1)],
 "AS-10": [(0, 0, (), -1), (1, 0, (0,), +2), (2, 1, (0,), +2)],
}
def monos(shape, r):
    out = []
    for (f, dt, K, net) in shape:
        v = [0] * (4 + r)
        v[dt] += 1
        for k in K:
            v[2 + k] += 1
        v[4 + f] = 1
        out.append((tuple(v), net))
    return out

def vsub(a, b):
    return tuple(x - y for x, y in zip(a, b))

def hp(blocks, ms, base):
    g = list(base)
    for b in blocks:
        bs = sorted(b)
        for i in bs[1:]:
            g.append(vsub(ms[i][0], ms[bs[0]][0]))
    return g

def closed_partitions(ms, base=(), exclude=()):
    n = len(ms)
    idx = list(range(n))
    def parts(seq):
        if not seq:
            yield []
            return
        first, rest = seq[0], seq[1:]
        for p in parts(rest):
            for i in range(len(p)):
                yield p[:i] + [[first] + p[i]] + p[i + 1:]
            yield [[first]] + p
    out = []
    D = len(ms[0][0])
    for p in parts(idx):
        H = hp(p, ms, base)
        # closed: cross-block diffs not in H
        okc = True
        reps = [min(b) for b in p]
        for i in range(len(p)):
            for j in range(i + 1, len(p)):
                if in_lattice(H, vsub(ms[reps[j]][0], ms[reps[i]][0])):
                    okc = False
        if not okc:
            continue
        if any(in_lattice(H, e) for e in exclude):
            continue
        out.append((p, H))
    return out

def prot(blocks, ms, annex=False):
    nz = sorted(n for n in (sum(ms[i][1] for i in b) for b in blocks) if n)
    if not nz:
        return "DEAD"
    if nz in ([1], [-1], [-1, 1]):
        return "PROT"
    if annex and len(nz) == 1 and abs(nz[0]) & (abs(nz[0]) - 1) == 0:
        return "PROT2K"
    return "UNPROT"

def probe_B():
    D6 = lambda r: ([0]*0)
    def ivecs(r):
        i1 = (1, -1, 0, -1) + (0,) * r
        i3 = (0, 0, 1, -2) + (0,) * r
        return i1, i3
    # GS-40: 53 closed partitions, none protected; ID-CLOSURE on all
    ms = monos(SHAPES["GS-40"], 2)
    i1, i3 = ivecs(2)
    cps = closed_partitions(ms)
    check("B.GS-40 closed partitions == 53", len(cps) == 53,
          f"got {len(cps)}")
    check("B.GS-40 no protected state",
          all(prot(p, ms) not in ("PROT", "PROT2K") for p, H in cps))
    # ID-CLOSURE on every state: rho-free part of H inside <I1,I3>
    ok = True
    for p, H in cps:
        # for every v in the +-2 coefficient box over H's generators that
        # is rho-free, check v in <I1,I3> by the CLOSED-FORM decomposition
        # (valid by probe A: kernel == <I1,I3> with alpha=v[0], beta=v[2])
        for coeffs in itertools.product(range(-2, 3), repeat=len(H)):
            v = [0] * 6
            for c, g in zip(coeffs, H):
                if c:
                    v = [a + c * b for a, b in zip(v, g)]
            if any(v[4:]):
                continue
            a, b = v[0], v[2]
            dec = [a * x + b * y for x, y in zip(i1, i3)]
            if dec != v:
                ok = False
    check("B.GS-40 ID-CLOSURE (coeff box +-2) on all 53 states", ok)
    # GS-11 / AS-10: exhaustive no-protected
    ms = monos(SHAPES["GS-11"], 2)
    cps = closed_partitions(ms)
    check("B.GS-11 no protected state (exhaustive, no shortcut)",
          all(prot(p, ms) not in ("PROT", "PROT2K") for p, H in cps),
          f"{len(cps)} states")
    ms = monos(SHAPES["AS-10"], 3)
    cps = closed_partitions(ms)
    check("B.AS-10 no protected/PROT2K state (annex criterion)",
          all(prot(p, ms, annex=True) not in ("PROT", "PROT2K")
              for p, H in cps), f"{len(cps)} states")
    # GS-08 corners
    ms = monos(SHAPES["GS-08"], 2)
    i1, i3 = ivecs(2)
    for cname, base, excl, want_safe in (
            ("c11", [i1, i3], [], True), ("c01", [i3], [i1], True),
            ("c10", [i1], [i3], False), ("c00", [], [i1, i3], False)):
        cps = closed_partitions(ms, base, excl)
        safe = all(prot(p, ms) == "PROT" for p, H in cps)
        check(f"B.GS-08 corner {cname} safe=={want_safe}",
              safe == want_safe, f"{len(cps)} states")
    fm = [[0, 1, 2]]
    check("B.GS-08 full merge nets -1",
          prot(fm, monos(SHAPES["GS-08"], 2)) == "PROT")
    # GS-02: kill state in every corner
    ms = monos(SHAPES["GS-02"], 2)
    ok = True
    for cname, base, excl in (("c11", [i1, i3], []), ("c01", [i3], [i1]),
                              ("c10", [i1], [i3]), ("c00", [], [i1, i3])):
        cps = closed_partitions(ms, base, excl)
        if not any(prot(p, ms) in ("DEAD", "UNPROT") for p, H in cps):
            ok = False
    check("B.GS-02 kill state exists in all four corners", ok)
    # AS-03
    ms = monos(SHAPES["AS-03"], 2)
    cps = closed_partitions(ms)
    fm = next(p for p, H in cps if len(p) == 1) if \
        any(len(p) == 1 for p, H in cps) else None
    check("B.AS-03 full merge PROT2K + generic UNPROT",
          fm is not None and prot(fm, ms, annex=True) == "PROT2K"
          and any(prot(p, ms, annex=True) == "UNPROT" for p, H in cps))

# ---------- Probe C: T-invariant audit of the committed verdict table -------
def probe_C():
    import re
    rows = []
    sec = None
    for line in open(os.path.join(HERE, "k2close_verdict_table.md")):
        if line.startswith("## Main"):
            sec = "main"
        elif line.startswith("## Annex"):
            sec = "annex"
        elif line.startswith("## Tallies"):
            sec = None
        m = re.match(r"\| (GS|AS)-(\d+) \| \d+ \| \d+ \| ([+-]\d+) \|.*?"
                     r"\*\*(\w+)\*\*", line)
        if m and sec:
            rows.append((sec, f"{m.group(1)}-{m.group(2)}",
                         int(m.group(3)), m.group(4)))
    check("C.53 rows parsed", len(rows) == 53, f"got {len(rows)}")
    ok = True
    for sec, sid, T, verdict in rows:
        if sec == "main":
            want_novel = abs(T) >= 2 or sid == "GS-40"
        else:
            want_novel = abs(T) >= 2 and (abs(T) & (abs(T) - 1)) != 0
        if (verdict == "NOVEL") != want_novel:
            ok = False
            print("  verdict/invariant clash:", sec, sid, T, verdict)
    check("C.NOVEL <=> invariant rule (+GS-40) across all 53", ok)
    nov = sorted(sid for _, sid, _, v in rows if v == "NOVEL")
    check("C.NOVEL set", nov == ["AS-10", "GS-11", "GS-19", "GS-20",
                                 "GS-21", "GS-30", "GS-34", "GS-35",
                                 "GS-40"], str(nov))

# ---------- Probe D: GLUE-DEGEN straight from the pinned instrument ---------
def probe_D():
    f = os.path.join(HERE, "survk2_instrument_results.json")
    got = hashlib.md5(open(f, "rb").read()).hexdigest()
    check("D.pin md5", got == "1ac516df8292ac5d57a88e430de3d1e4", got)
    inst = json.load(open(f))
    glued = []
    rows = set()
    for rec in inst["grprec"]:
        books = set()
        for c in rec["cells"]:
            books.add(tuple(tuple(e) for e in c["ce"] if e[0] != "0"))
        if len(books) >= 2:
            glued.append(rec)
            rows.add((rec["tower"], tuple(rec["key"])))
    check("D.38 glued groups / 29 rows / 3 towers",
          len(glued) == 38 and len(rows) == 29 and
          {t for t, k in rows} == {"SDG2BF", "SDG2BZ", "SDW4G2F"},
          f"{len(glued)}/{len(rows)}")
    single = all(len({c["res"] for c in rec["cells"]}) == 1
                 for rec in glued)
    check("D.every glued group single in-vivo residue class", single)
    nets = collections.Counter()
    for rec in glued:
        s = [x for x in rec["signed"]]
        nets[tuple(sorted(s))] += 1
    n0 = sum(v for k, v in nets.items() if k == (0,))
    n1 = sum(v for k, v in nets.items() if k in ((1,), (-1,)))
    check("D.28 net-0 + 10 net +-1", n0 == 28 and n1 == 10, str(dict(nets)))

# ---------- Probe E: SPOT-1..4 ----------------------------------------------
def probe_E():
    import survk2_derive_checks as SD
    inv = {n: SD.legal_drains_g2(n, {0}) for n in (0, 1, 2, 3)}
    def keys(n):
        return {(K, p) for (K, p, rem, seq) in inv[n]}
    check("E.SPOT-1 A={0} inventory",
          keys(0) == {((), 0)} and keys(1) == {((), 0)}
          and keys(2) == {((0,), 0), ((), 1)}
          and keys(3) == {((0,), 0), ((), 1)},
          f"{[sorted(keys(n)) for n in (0, 1, 2, 3)]}")
    inv3 = SD.legal_drains_g2(3, {0, 1})
    ex = [(K, p) for (K, p, rem, seq) in inv3 if 3 - rem == 2 and p == 0]
    check("E.SPOT-2 exchange class members at A={0,1}",
          sorted(K for K, p in ex) == [(0,), (1, 1)], str(ex))
    inv3a = SD.legal_drains_g2(3, {0})
    check("E.SPOT-2b under A={0} only C0 survives",
          [(K, p) for (K, p, rem, seq) in inv3a
           if 3 - rem == 2 and p == 0] == [((0,), 0)])
    check("E.SPOT-3 no {C1,C1,C1} single window at n<=3",
          all(K != (1, 1, 1) and sum(1 for k in K if k == 1) <= 2
              for n in (0, 1, 2, 3)
              for (K, p, rem, seq) in SD.legal_drains_g2(n, {0, 1})))

def main():
    probe_A()
    probe_B()
    probe_C()
    probe_D()
    probe_E()
    print("EXT-PROBE FINAL:", "GREEN (0 fails)" if not FAILS
          else f"RED ({len(FAILS)} fails): {FAILS}")

if __name__ == "__main__":
    main()
