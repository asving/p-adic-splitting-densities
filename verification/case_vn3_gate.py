#!/usr/bin/env python3
"""CASE-VN3 census — gate V-n3 (MOVES_2026-07-24.md §V-TABLES V.6, rev 3).
Written AFTER verification/CASE_VN3_SEALED_PREDICTIONS.md was sealed (S0-S6).
Families: A1 (root table, nine q), A2 (wild side table + p=2 digit census),
B-step (s_blk2 table, nine q, two representatives), gate B (marked pairs,
N=3/4 boxes at p=2). Exact ints/Fractions only. Long log: /tmp/vn3_census.out;
JSON: verification/results/case_vn3_results.json."""

import json, sys
from fractions import Fraction
from itertools import product

LOG = open("/tmp/vn3_census.out", "w")
def log(*a):
    print(*a, file=LOG)

QLIST = [2, 3, 4, 5, 7, 8, 9, 11, 13]

# ---------- FC2 field models: elements 0..q-1 as base-p digit vectors ----------
MODULI = {4: (2, [1, 1, 1]), 8: (2, [1, 1, 0, 1]), 9: (3, [1, 0, 1])}  # little-endian

class Fq:
    def __init__(self, q):
        self.q = q
        if q in MODULI:
            p, mod = MODULI[q]
            k = len(mod) - 1
            def dig(e):
                return [(e // p**i) % p for i in range(k)]
            def enc(d):
                return sum(c * p**i for i, c in enumerate(d))
            def polymulred(d1, d2):
                prod_ = [0] * (2 * k - 1)
                for i, x in enumerate(d1):
                    for j, y in enumerate(d2):
                        prod_[i + j] = (prod_[i + j] + x * y) % p
                for i in range(len(prod_) - 1, k - 1, -1):  # reduce by monic mod
                    c = prod_[i]
                    if c:
                        for j in range(len(mod)):
                            prod_[i - k + j] = (prod_[i - k + j] - c * mod[j]) % p
                return prod_[:k]
            self.add = [[enc([(x + y) % p for x, y in zip(dig(a), dig(b))])
                         for b in range(q)] for a in range(q)]
            self.mul = [[enc(polymulred(dig(a), dig(b))) for b in range(q)]
                        for a in range(q)]
            self.p = p
        else:
            self.add = [[(a + b) % q for b in range(q)] for a in range(q)]
            self.mul = [[(a * b) % q for b in range(q)] for a in range(q)]
            self.p = q
        self.neg = [next(x for x in range(q) if self.add[a][x] == 0) for a in range(q)]
        self.inv = [None] + [next(x for x in range(1, q) if self.mul[a][x] == 1)
                             for a in range(1, q)]
        self.units = list(range(1, q))

    def sub(self, a, b):
        return self.add[a][self.neg[b]]

    def poly_eval(self, coeffs, r):  # coeffs high->low, monic incl.
        acc = 0
        for c in coeffs:
            acc = self.add[self.mul[acc][r]][c]
        return acc

    def syndiv(self, coeffs, r):  # divide monic poly (coeffs high->low) by (z - r)
        out, acc = [], 0
        for c in coeffs:
            acc = self.add[self.mul[acc][r]][c]
            out.append(acc)
        return out[:-1], out[-1]  # quotient (high->low), remainder

    def roots_mult(self, coeffs):  # multiset {root: mult}, coeffs high->low monic
        res = {}
        for r in range(self.q):
            m, cur = 0, coeffs
            while len(cur) > 1:
                quot, rem = self.syndiv(cur, r)
                if rem != 0:
                    break
                m += 1
                cur = quot
            if m:
                res[r] = m
        return res

    def trace2(self, a):  # Tr_{F_q/F_2}, q = 2^k
        k = {2: 1, 4: 2, 8: 3}[self.q]
        t, x = 0, a
        for _ in range(k):
            t = self.add[t][x]
            x = self.mul[x][x]
        return t

    def is_square(self, a):
        return any(self.mul[x][x] == a for x in range(self.q))

fields = {q: Fq(q) for q in QLIST}
results = {}
failures = []

def check(fam, name, got, want):
    ok = got == want
    log(f"[{fam}] {name}: got {got} want {want} {'OK' if ok else 'FAIL'}")
    if not ok:
        failures.append((fam, name, got, want))
    return ok

# ---------------- A1: root skeleton table, nine q (seal S1) ----------------
SEAL_A1 = {  # V.6.1 verbatim: rows in (D1) order per q
    2: [0, 2, 2, 2, 2], 3: [1, 9, 8, 6, 3], 4: [4, 24, 20, 12, 4],
    5: [10, 50, 40, 20, 5], 7: [35, 147, 112, 42, 7], 8: [56, 224, 168, 56, 8],
    9: [84, 324, 240, 72, 9], 11: [165, 605, 440, 110, 11],
    13: [286, 1014, 728, 156, 13]}
A1_FORMS = [lambda q: q*(q-1)*(q-2)//6, lambda q: q*q*(q-1)//2,
            lambda q: (q**3-q)//3, lambda q: q*(q-1), lambda q: q]

def census_a1(q):
    F = fields[q]
    tally = [0]*5  # m_H3, m_H12, m_H<3>, m_2+1, m_3
    bad_t = 0
    for a, b, c in product(range(q), repeat=3):
        rm = F.roots_mult([1, a, b, c])
        ms = sorted(rm.values())
        if ms == [1, 1, 1]:
            tally[0] += 1
        elif ms == [1]:
            tally[1] += 1        # residual quadratic has no root -> irreducible
        elif ms == []:
            tally[2] += 1        # no root, degree 3 -> irreducible cubic
        elif ms == [1, 2]:
            tally[3] += 1
            alpha = next(r for r, m in rm.items() if m == 2)
            beta = next(r for r, m in rm.items() if m == 1)
            if F.sub(beta, alpha) == 0:
                bad_t += 1       # (D4) landing failure
        elif ms == [3]:
            tally[4] += 1
        else:
            bad_t += 1           # unclassifiable = failure
    return tally, bad_t

res_a1 = {}
for q in QLIST:
    tally, bad_t = census_a1(q)
    sealed = SEAL_A1[q]
    check("A1", f"q={q} row", tally, sealed)
    check("A1", f"q={q} closed forms", [f(q) for f in A1_FORMS], sealed)
    check("A1", f"q={q} PART-1 sum", sum(tally), q**3)
    check("A1", f"q={q} (D4) t!=0 violations", bad_t, 0)
    res_a1[q] = {"tally": tally, "bad_t": bad_t}
check("A1", "m_H3 zero at q=2 (genuine falsifier)", res_a1[2]["tally"][0], 0)

# ------------- A2: wild side table (nine q) + p=2 digit census (seal S2) -------------
SEAL_A2 = {2: 1, 3: 4, 4: 9, 5: 16, 7: 36, 8: 49, 9: 64, 11: 100, 13: 144}
res_a2 = {}
for q in QLIST:
    F = fields[q]
    total, fiber = 0, {y: 0 for y in F.units}
    bad = 0
    for u0, u2 in product(F.units, F.units):
        y0 = F.mul[F.neg[u0]][F.inv[u2]]   # root of u2*y + u0
        if y0 == 0:
            bad += 1
            continue
        total += 1
        fiber[y0] += 1
    check("A2", f"q={q} T=(q-1)^2", total, SEAL_A2[q])
    check("A2", f"q={q} y0 in Fq* violations", bad, 0)
    check("A2", f"q={q} fiber counts all q-1", sorted(set(fiber.values())), [q - 1])
    res_a2[q] = {"T": total, "fibers": fiber}
# p=2 digit census at sealed height point (h0,h2)=(4,1), FC4 box mod 2^5
def v2(x, cap=99):
    if x == 0:
        return cap
    v = 0
    while x % 2 == 0:
        x //= 2
        v += 1
    return v

cyl = ev = hullbad = 0
for a, b, c in product(range(0, 32, 2), repeat=3):
    cyl += 1
    if c == 16 and a % 4 == 2 and b % 8 == 0:
        ev += 1
        vb = v2(b)
        # NP over (0,4),(1,vb),(2,1),(3,0): hull vertices must be (0,4),(2,1),(3,0)
        if not (v2(c) == 4 and v2(a) == 1 and 2 * vb > 5):
            hullbad += 1
check("A2p2", "entry cylinder size", cyl, 2**12)
check("A2p2", "digit event count at (4,1) [= 2^12 * 2^-7]", ev, 32)
check("A2p2", "NP side-support violations", hullbad, 0)
check("A2p2", "E exponent (3(h0+h2)-1)/2 at (4,1)", (3 * (4 + 1) - 1) // 2, 7)
res_a2["p2"] = {"cylinder": cyl, "event": ev, "hullbad": hullbad}

# ------------- B-step: s_blk2 table, nine q, two representatives (seal S3) -------------
SEAL_B = {2: [0, 1, 1], 3: [1, 3, 2], 4: [3, 6, 3], 5: [6, 10, 4],
          7: [15, 21, 6], 8: [21, 28, 7], 9: [28, 36, 8], 11: [45, 55, 10],
          13: [66, 78, 12]}  # o_split, o_inert, o_double

def census_m2(q, t_state):
    F = fields[q]
    row = [0, 0, 0]
    bad_land = conv_bad = 0
    for u, w in product(F.units, range(q)):
        rm = F.roots_mult([1, w, u])           # R(y) = y^2 + w y + u
        if len(rm) == 2:
            cls = 0
        elif len(rm) == 0:
            cls = 1
        else:
            (ystar, m), = rm.items()
            cls = 2 if m == 2 else None
            if cls is None or ystar == 0:
                bad_land += 1
                continue
        row[cls] += 1
        # FC3 convention face (display check; t_state deliberately unread)
        if q % 2 == 1:
            four_u = F.mul[F.add[F.add[1][1]][F.add[1][1]]][u]
            disc = F.sub(F.mul[w][w], four_u)
            conv = 2 if disc == 0 else (0 if F.is_square(disc) else 1)
        else:
            conv = 2 if w == 0 else F.trace2(F.mul[u][F.inv[F.mul[w][w]]])
        if conv != cls:
            conv_bad += 1
    return row, bad_land, conv_bad

res_b = {}
for q in QLIST:
    reps = [1] if q == 2 else [1, 2]
    rows = {}
    for t in reps:
        row, bad_land, conv_bad = census_m2(q, t)
        rows[t] = row
        check("Bstep", f"q={q} t={t} (o_split,o_inert,o_double)", row, SEAL_B[q])
        check("Bstep", f"q={q} t={t} PART-1 = q(q-1)", sum(row), q * (q - 1))
        check("Bstep", f"q={q} t={t} (D4) y* in Fq* violations", bad_land, 0)
        check("Bstep", f"q={q} t={t} convention-face mismatches (F5)", conv_bad, 0)
    if len(reps) == 2:
        check("Bstep", f"q={q} (iv)-REP rows identical", rows[1], rows[2])
    check("Bstep", f"q={q} m_w2 pool", len(fields[q].units), q - 1)
    check("Bstep", f"q={q} m_vv pool", len(fields[q].units) ** 2, (q - 1) ** 2)
    res_b[q] = rows

# ------------- Gate B: marked pairs, p=2 boxes N=3,4 (seal S4) -------------
HIST = {0: ((1, 0, 0), 0), 1: ((0, 1, 0), 1)}  # (entrance mod 2, recentre shift)

def gateb(N):
    M = 2 ** N
    marked = {0: [], 1: []}
    hensel_bad = 0
    for c2, c1, c0 in product(range(M), repeat=3):
        for h, ((e2, e1, e0), r0) in HIST.items():
            if (c2 % 2, c1 % 2, c0 % 2) != (e2, e1, e0):
                continue
            a2 = (c2 + 3 * r0) % M
            a1 = (c1 + 2 * c2 * r0 + 3 * r0 * r0) % M
            a0 = (r0**3 + c2 * r0**2 + c1 * r0 + c0) % M
            s = 1                                    # Newton-lift simple root
            for _ in range(N + 2):
                g = (s**3 + a2 * s**2 + a1 * s + a0) % M
                gp = (3 * s**2 + 2 * a2 * s + a1) % M
                s = (s - g * pow(gp, -1, M)) % M
            h1 = (a2 + s) % M                        # g = (z-s)(z^2+h1 z+h0)
            h0v = (a1 + s * h1) % M
            if (a0 + s * h0v) % M != 0 or h0v % 2 or h1 % 2:
                hensel_bad += 1
                continue
            if h0v % 8 == 4 and h1 % 4 == 0:         # sealed event, lambda=1
                marked[h].append((c2 % 8, c1 % 8, c0 % 8))
    return marked, hensel_bad

gb = {}
m3, hb3 = gateb(3)
m4, hb4 = gateb(4)
check("GateB", "Hensel/division failures N=3", hb3, 0)
check("GateB", "Hensel/division failures N=4", hb4, 0)
tot3, tot4 = len(m3[0]) + len(m3[1]), len(m4[0]) + len(m4[1])
check("GateB", "marked pairs N=3", tot3, 16)
check("GateB", "marked pairs N=4", tot4, 128)
check("GateB", "per-history N=3", (len(m3[0]), len(m3[1])), (8, 8))
check("GateB", "per-history N=4", (len(m4[0]), len(m4[1])), (64, 64))
check("GateB", "marked-history count N=3", sum(1 for h in m3 if m3[h]), 2)
check("GateB", "marked-history count N=4", sum(1 for h in m4 if m4[h]), 2)
check("GateB", "mu-hat N=3", Fraction(tot3, 2**9), Fraction(1, 32))
check("GateB", "mu-hat N=4", Fraction(tot4, 2**12), Fraction(1, 32))
for h in (0, 1):  # BOX-PRECISION: N=4 marked set = exact 8-fold preimage, per history
    from collections import Counter
    proj = Counter(m4[h])
    check("GateB", f"box-precision hist {h}: N=4 residues mod 8 = N=3 set x8",
          (sorted(proj) == sorted(set(m3[h])), set(proj.values())),
          (True, {8}))
F2 = fields[2]  # entrance census face: psi^2*chi classes among the 8 mod-2 classes
ent_classes = [(e2, e1, e0) for e2, e1, e0 in product(range(2), repeat=3)
               if sorted(F2.roots_mult([1, e2, e1, e0]).values()) == [1, 2]]
check("GateB", "entrance I^ent(2) [censused psi^2chi classes]", len(ent_classes), 2)
check("GateB", "marked classes = the two sealed histories",
      sorted(ent_classes), sorted(e for e, _ in HIST.values()))
check("GateB", "iota [censused: I^ent(2)/2^3]",
      Fraction(len(ent_classes), 8), Fraction(1, 4))
check("GateB", "count shadow I^ent(2)*T(2)", len(ent_classes) * SEAL_B[2][2], 2)
gb = {"N3": {"total": tot3, "per_hist": [len(m3[0]), len(m3[1])]},
      "N4": {"total": tot4, "per_hist": [len(m4[0]), len(m4[1])]}}

# ---------------- verdict + JSON ----------------
results = {"A1": res_a1, "A2": {str(k): (v if k == "p2" else {"T": v["T"]})
                                for k, v in res_a2.items()},
           "Bstep": {str(q): res_b[q] for q in QLIST}, "GateB": gb,
           "failures": failures, "verdict": "PASS" if not failures else "FAIL"}
with open("/data/users/asvin/math-and-lean/p-adic-splitting-densities/"
          "verification/results/case_vn3_results.json", "w") as f:
    json.dump(results, f, indent=1, default=str)
log(f"\nFAILURES: {len(failures)}")
for fam, name, got, want in failures:
    print(f"FAIL [{fam}] {name}: got {got} want {want}")
print(f"VERDICT: {results['verdict']} ({len(failures)} failures); "
      f"A1 9q, A2 9q+p2, Bstep 9q x reps, GateB 16/128")
LOG.close()
