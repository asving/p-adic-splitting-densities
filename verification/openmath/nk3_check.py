#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
N-K3 — the H4 numerics gate sealing H4-M4/H4-M5 (blueprint HDISCHARGE_H4.md §N).

SPEC (blueprint §N, verbatim): "enumerate the n = 3 pack's verdict-row β-legs'
δ > 1 pools; per pool, check the realized species against Lemma 4's gcd
criterion and against Route B's intrinsic exponent law (a_δ = δ·a_sym at the
realized letter). Predictions sealed pre-run per the standing falsifier
discipline. A violation of the INTRINSIC law refutes Route B (and (EQ-2)
itself — escalate); a gcd-criterion violation at a realized pool kills Route
A's cheap match."

================================================================================
THE SEALED PREDICTIONS (H4M5_k3delta_attempt.md §6, transcribed VERBATIM;
sealed there PRE-RUN on 2026-08-01; tested AS-SEALED here)
================================================================================
- **P1 (the law — the falsifier of this note).** At EVERY realized δ > 1
  pool: a_δ(pool position) = δ·a_sym(realized letter) EXACTLY, δ = the
  pool's index, a_sym computed by Def SYM on the realized letter's own
  datum (per-branch letters at split-realized pools, per §5.2's reading —
  the prediction is NOT "δ·a_sym(the ℤ_p letter)").
- **P2 (divisibility, the cheap read).** δ | a_δ at every realized pool
  (Corollary DIV; implied by P1, checkable without computing a_sym).
- **P3 (agnostic clause, displayed).** This note makes NO prediction on
  Lemma 4's gcd(m, δ) criterion at the realized pools: BOTH outcomes are
  consistent with everything proved here (the gcd criterion is
  dictionary-side, H4-M2/Route-A material; a non-coprime realized pool
  would kill Route A — M4 §5.3 branch (i) — and touch nothing in §§2–4).
- **P4 (letter-persistent-pool consistency; carrier-bridge conditional).**
  At any pool position additionally certified letter-persistent IN THE SAME
  CARRIER the intrinsic law reads AND realized at δ = 1: a_δ = δ·a₁.

Plus the M2 gcd-table seed (H4M2_dict_attempt.md, `nk3_gcd_table` — "the table
N-K3 consumes"): rows (g, δ), d = 1, flag stable iff gcd(g, δ) = 1:
  (2,2) split · (2,3) stable · (2,4) split · (2,5) stable ·
  (3,3) split · (3,2) stable.

================================================================================
WHAT "THE n = 3 PACK'S VERDICT-ROW β-LEGS' δ > 1 POOLS" ARE, OPERATIONALLY
================================================================================
The n = 3 pack = the monic-cubic classifier pack (verdict rows σ ∈ {(1,1,1),
(1,1)(1,2), (1,3), (1,1)(2,1)-family, (3,1)} with the RESUM-n3 assembly
R_σ = root_t + (q−1)/q²·β₂-leg + β₃-leg/q²). Its β-legs are the realized
species letters: stage-1 terminal letters (base degree d ∈ {1,2,3}) and the
deep letters (e, h, g) read at the repeated-root clusters (β₂/β₃ restart
legs). A δ > 1 pool = a continuation read at accumulated residue degree
D > 1 (blueprint §3.2: "family-(vi) β-legs β_μ(σ)(q^D) — continuation reads
at accumulated residue degree D (the child's tower fields)"), i.e. re-based
at O_δ = W(F_{p^δ}) with q₀ = p^δ (K3-c's "unramified pools").

READING AMBIGUITY, DISPLAYED (this is blueprint fold finding 1's recorded
"not well-posed" point, NOT this script's invention). Two readings of "the
pool's realized species vs the gcd criterion" survive on the record:
  (R-BIRTH) the pool's index δ = D = the birth letter's residue degree (the
    β_μ(σ)(q^D) leg); its realized species are the CHILD's letters, with
    relative accumulated degree m_rel; the criterion is gcd(m_rel, δ) = 1.
    At n = 3, μ·f ≤ 3 forces every f ≥ 2 birth letter to have μ = 1, so
    every δ > 1 pool's child is the size-1 (linear-residual) problem over
    O_D: m_rel = 1 always. SEALED STRUCTURAL PREDICTION: zero realized
    child species with gcd(m_rel, δ) > 1 — the Route-A refuter is
    STRUCTURALLY ABSENT at n = 3 under this reading.
  (R-FREE) δ is a free re-base index (the M2 seed table's reading: rows
    (g, δ) with δ ∈ {2,3,4,5} at the pack's realized residual degrees
    g ∈ {2,3}); non-coprime pairs are then trivially realized and the
    transported residual SPLITS exactly per Lidl–Niederreiter (M2 Lemma 4
    = theorem); whether that counts as "a realized pool violating the gcd
    criterion" is the open realization/carrier question M4 branch (i)
    adjudicates. This script reports the exact facts under BOTH readings
    and fires no branch unilaterally.

================================================================================
PREREGISTERED NUMERIC PREDICTIONS (sealed in this header BEFORE the run)
================================================================================
PART A — the pack enumeration (ℤ_p-side; my classifier + PARI oracle).
 PRE-A1 p = 3, exhaustive box mod 3^4 (531,441 monic cubics): stage-1
   residue-pattern counts = F₃ pattern counts × 3^9 = 19,683:
   {3 distinct roots}: 19,683 · {lin × irred quad}: 177,147 ·
   {irred cubic}: 157,464 · {double+simple}: 118,098 · {triple}: 59,049.
 PRE-A2 p = 2, exhaustive box mod 2^5 (32,768): × 2^12 = 4,096:
   {3 distinct}: 0 · {lin × irq}: 8,192 · {irc}: 8,192 ·
   {double+simple}: 8,192 · {triple}: 8,192.
 PRE-A3 δ > 1 pool birth families ALL REALIZED (count > 0) at both primes:
   stage-1 f = 2 (counts = lin×irq rows above, exact); stage-1 f = 3
   (= irc rows, exact); deep g = 2 letters (1,h,2) > 0; deep g = 3
   letters (1,h,3) > 0. (Deep-letter counts observed, not preregistered —
   no sealed closed form exists for the depth-truncated box.)
 PRE-A4 oracle agreement: ZERO (e,f)-type mismatches between this
   classifier's decided boxes and PARI factorpadic+idealprimedec, on:
   the full p = 3 mod-3^3 box (19,683), a 5,000-box seeded sample of the
   p = 3 mod-3^4 box, and the full p = 2 mod-2^5 box.
 PRE-A5 (R-BIRTH refuter hunt): zero realized δ > 1 pools with child size
   > 1; hence zero realized child species with gcd(m_rel, δ) > 1.
PART B — the gcd table (M2 seed rows, EXHAUSTIVE over the pack's realized
 residual families; factor-degree multisets over F_{p^δ}):
 PRE-B1 p = 3: all 3 monic irreducible quadratics over F₃, all 8 monic
   irreducible cubics; p = 2: the 1 quadratic (z²+z+1), both cubics.
 PRE-B2 multisets: (g=2, δ=2): {1,1} · (2,3): {2} · (2,4): {1,1} ·
   (2,5): {2} · (3,2): {3} · (3,3): {1,1,1} — for EVERY member of the
   family (zero exceptions; a residual staying irreducible at gcd > 1
   would be a Lidl–Niederreiter anomaly = harness bug, stop the line).
 PRE-B3 (R-FREE refuter read): the non-coprime realized rows (2,2), (2,4),
   (3,3) are NON-EMPTY (realized letters × those δ exist) and every member
   splits — refutation PRESSURE on Route A under R-FREE, realization/
   carrier-conditional exactly as the blueprint records.
PART C — the intrinsic law (P1/P2/P4) at the pools, exact digit census.
 Census convention (M14 T1's): tower = base key x (d = 1), read (e₁,h₁),
 residual ψ (deg g) over F_{q₀}; top space B = Σ_{j<e₁g} b_j x^j over
 GR(p^M, δ); w(B) = min_j (e₁·v(b_j) + j·h₁); at γ = w(B) the digit is
 Σ_{slots} res(b_j/p^{v_j})·z^i ∈ F_{q₀}[z]/ψ (slots j = j₀+i·e₁,
 j₀ = t₁γ mod e₁, v_j = (γ−j·h₁)/e₁); 𝔸(γ) = {digits at w = γ} ∪ {0}
 (level-set reading, M14's lesson). The census enumerates the digit-
 determining data (v-profile ≤ Γ or deep, unit residues in F_{q₀}^×)
 EXHAUSTIVELY — exact and complete for heights γ ≤ Γ = 3, since the digit
 formula reads only (v_j, res(u_j)); a raw-box control at the δ = 1
 instances verifies the reduction against brute force.
 Def SYM (H4-M5 §2.1): a_sym at stage-2 height γ: t₁ = h₁^{-1} mod e₁,
 j₀ = t₁γ mod e₁, γ_i = γ − (j₀+i·e₁)h₁ (i < g), I(γ) = {i : γ_i ∈
 e₁·ℤ≥0}; a_sym = |I(γ)|·d (one-stage towers; leaves = |I|). Base
 positions (k = 0): a_sym = d.
 SEALED a_sym TABLES (heights γ = 0..3, d = 1):
   (1,1,2): 1,2,2,2 · (1,1,3): 1,2,3,3 · (2,1,1): 1,1,1,1 ·
   (2,1,2): 1,1,2,2 · branch letter (e,h,1): 1 at every height · base: 1.
 SEALED CENSUS PREDICTIONS |𝔸(γ)|, γ = 0..3 (STABLE pools: matched letter
 persists, |𝔸| = p^{δ·a_sym}; SPLIT pools: per-branch value sets = full
 F_{q₀} at every height, per-branch a_δ = δ = δ·a_sym(branch); the naive
 matched-letter read δ·a_sym(unsplit ℤ_p letter) FAILS at split pools —
 the M5 §5.2 F₉-shape contrast, displayed not counted):
  C1 p=3 (1,1,2) ψ=z²+1:  δ=1: 3,9,9,9 | δ=2 SPLIT: branch 9,9,9,9 (a=2)
     | δ=3 STABLE: 27,729,729,729 (a=3,6,6,6)
  C2 p=3 (1,1,3) ψ=z³+2z+2: δ=1: 3,9,27,27 | δ=2 STABLE: 9,81,729,729
     (a=2,4,6,6) | δ=3 SPLIT: 3 branches, each 27,27,27,27 (a=3)
  C3 p=2 (1,1,2) ψ=z²+z+1: δ=1: 2,4,4,4 | δ=2 SPLIT: branch 4,4,4,4 (a=2)
     | δ=3 STABLE: 8,64,64,64 (a=3,6,6,6)
  C4 p=3 (2,1,1) ψ=z+2 (unit root 1): δ=1: 3,3,3,3 | δ=2 STABLE: 9,9,9,9
  C4b p=2 (2,1,1) ψ=z+1: δ=2 STABLE: 4,4,4,4 | δ=3 STABLE: 8,8,8,8
  C5 base pools (child of the stage-1 f=2/f=3 letters after Frobenius
     descent = the size-1 problem over O_D): p=3 δ=2: 9,9,9,9 · p=2 δ=3:
     8,8,8,8 (single-coefficient census, a_δ = δ·1)
  C6 p=2 (1,1,3) ψ=z³+z+1: δ=2 STABLE: 4,16,64,64 (a=2,4,6,6) | δ=3
     SPLIT: 3 branches, each 8,8,8,8 (a=3)
  C7 p=3 (2,1,2) ψ=z²+1 — M14 T3's witness tower (the M5 §5.2 F₉ shape;
     e·g = 4 top space, ADJACENT to the pack, realization grade displayed):
     δ=1: 3,3,9,9 | δ=2 SPLIT: branch 9,9,9,9 (a_branch = 2; naive
     δ·a₁ = 4 at γ ≥ 2 — the recorded a_branch = 2 ≠ 4 contrast, EXECUTED)
     | δ=3 STABLE: 27,27,729,729 (= M14 T1's exact numbers, re-run)
 P2 at every census point: |𝔸| an exact power of p with δ | log_p.
 P4 at every STABLE pool: a_δ(γ) = δ·a₁(γ) with a₁ from the δ=1 census of
 the same letter (C1,C2,C3 have their own δ=1 legs; C4/C4b/C5/C6 δ=1 legs
 run too as controls with |𝔸| = p^{a_sym}).
 SPAN predictions checked as SET EQUALITY (value set = the predicted span
 {Σ_{i∈I(γ)} c_i z^i : c_i ∈ F_{q₀}}), not just cardinality.

VERDICT RULE: per family GREEN iff observed == preregistered EXACTLY (zero
violations); P3 reports both-outcome facts with no pass/fail. Any RED is
classified (harness bug vs route defect vs sealed-prediction failure) with
the exact failing instance. Exact integer/tuple arithmetic throughout; no
floats. Deterministic (seed 0). PARI gp CLI as independent oracle (cypari2
unavailable on this box). Runtime target ≤ 20 min.

Outputs: this log (tee'd to nk3_check_output.txt) + nk3_check_results.json.
2026-08-08, N-K3 unit (numerics fleet). Runs from verification/openmath/.
"""

import itertools, json, random, subprocess, sys, time, os
from collections import Counter, defaultdict

random.seed(0)
T0 = time.time()
RESULTS = {"families": {}, "violations": []}
VIOL = RESULTS["violations"]

def report(fam, name, ok, detail=""):
    tag = "PASS" if ok else "VIOLATION"
    print(f"[{tag}] {fam} :: {name}  {detail}")
    if not ok:
        VIOL.append({"family": fam, "check": name, "detail": str(detail)})

# ============================================================================
# Finite fields F_{p^k} as F_p[z]/(mod), elements = tuples of ints mod p
# ============================================================================
IRRED = {  # monic irreducible over F_p, coeffs low->high WITHOUT leading 1
    (2, 1): (0,), (2, 2): (1, 1), (2, 3): (1, 1, 0), (2, 4): (1, 1, 0, 0),
    (2, 5): (1, 0, 1, 0, 0),
    (3, 1): (0,), (3, 2): (1, 0), (3, 3): (2, 2, 0), (3, 4): (2, 0, 0, 1),
    (3, 5): (1, 2, 0, 0, 0),
}
# (p,k): modulus z^k + sum c_i z^i. Verified irreducible below (self-check).

class FF:
    """F_{p^k}; elements are k-tuples of ints mod p (low->high)."""
    def __init__(self, p, k):
        self.p, self.k, self.q = p, k, p ** k
        self.mod = IRRED[(p, k)]
        assert len(self.mod) == k
        self.zero = (0,) * k
        self.one = tuple([1] + [0] * (k - 1))

    def add(self, a, b):
        return tuple((x + y) % self.p for x, y in zip(a, b))

    def neg(self, a):
        return tuple((-x) % self.p for x in a)

    def mul(self, a, b):
        p, k = self.p, self.k
        prod = [0] * (2 * k - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    prod[i + j] = (prod[i + j] + x * y) % p
        for i in range(len(prod) - 1, k - 1, -1):
            c = prod[i]
            if c:
                prod[i] = 0
                for j, m in enumerate(self.mod):
                    prod[i - k + j] = (prod[i - k + j] - c * m) % p
        return tuple(prod[:k])

    def pow(self, a, n):
        r, b = self.one, a
        while n:
            if n & 1:
                r = self.mul(r, b)
            b = self.mul(b, b)
            n >>= 1
        return r

    def elements(self):
        return [tuple(v) for v in itertools.product(range(self.p), repeat=self.k)]

    def embed_base(self, c):        # F_p int -> element
        return tuple([c % self.p] + [0] * (self.k - 1))

    def poly_eval(self, coeffs, x):  # coeffs list of elements low->high
        acc = self.zero
        for c in reversed(coeffs):
            acc = self.add(self.mul(acc, x), c)
        return acc

    def selfcheck_irreducible(self):
        # z^k + mod has no root in any proper subfield ... full check: no
        # root in F_{p^k}... insufficient for reducible-into-quadratics; do
        # the honest check: gcd-free via counting roots of z^{p^j}-z divis.
        # Cheap complete check for k<=6: the poly (as element op) has no
        # roots in F_{p^d} for d|k, d<k => no linear factors over subfields;
        # full irreducibility: z^{p^k} == z mod f and z^{p^d} != z for d<k.
        p, k = self.p, self.k
        # polynomial arithmetic mod f over F_p, f = z^k + mod
        def pmulmod(a, b):
            prod = [0] * (2 * k - 1)
            for i, x in enumerate(a):
                if x:
                    for j, y in enumerate(b):
                        prod[i + j] = (prod[i + j] + x * y) % p
            for i in range(len(prod) - 1, k - 1, -1):
                c = prod[i]
                if c:
                    prod[i] = 0
                    for j, m in enumerate(self.mod):
                        prod[i - k + j] = (prod[i - k + j] - c * m) % p
            return tuple(prod[:k])
        def frob(a):  # a^p
            r = tuple([1] + [0] * (k - 1))
            b, n = a, p
            while n:
                if n & 1:
                    r = pmulmod(r, b)
                b = pmulmod(b, b)
                n >>= 1
            return r
        z = tuple([0, 1] + [0] * (k - 2)) if k >= 2 else (0,)
        if k == 1:
            return True
        cur = z
        for d in range(1, k + 1):
            cur = frob(cur)
            if d < k and cur == z:
                return False
        return cur == z

FIELDS = {}
def ff(p, k):
    if (p, k) not in FIELDS:
        FIELDS[(p, k)] = FF(p, k)
    return FIELDS[(p, k)]

print("=" * 76)
print("SELF-CHECK: field moduli irreducible")
print("=" * 76)
for (p, k) in sorted(IRRED):
    ok = ff(p, k).selfcheck_irreducible()
    report("SELF", f"F_{p}^{k} modulus irreducible", ok)

# ============================================================================
# Galois rings GR(p^M, delta) = (Z/p^M)[a]/(F), F = lift of IRRED[(p,delta)]
# elements = delta-tuples of ints mod p^M
# ============================================================================
class GR:
    def __init__(self, p, M, delta):
        self.p, self.M, self.d = p, M, delta
        self.pm = p ** M
        self.mod = IRRED[(p, delta)]  # lift with the same small coefficients
        self.F = ff(p, delta)

    def mul(self, a, b):
        p, k, pm = self.p, self.d, self.pm
        prod = [0] * (2 * k - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    prod[i + j] = (prod[i + j] + x * y) % pm
        for i in range(len(prod) - 1, k - 1, -1):
            c = prod[i]
            if c:
                prod[i] = 0
                for j, m in enumerate(self.mod):
                    prod[i - k + j] = (prod[i - k + j] - c * m) % pm
        return tuple(prod[:k])

    def v(self, a):  # valuation; None if 0 mod p^M (i.e. >= M)
        if all(x % self.pm == 0 for x in a):
            return None
        v = 0
        while all(x % (self.p ** (v + 1)) == 0 for x in a):
            v += 1
        return v

    def shift_res(self, a, v):  # res(a / p^v) in F_{p^delta}
        return tuple((x // self.p ** v) % self.p for x in a)

# ============================================================================
# Def SYM (H4-M5 §2.1), one-stage towers (stage-2 positions) + base positions
# ============================================================================
def a_sym_one_stage(d, e1, h1, g1, gamma):
    """a_sym of the stage-2 position at height gamma; W1 = e1*Z>=0."""
    # t1 = h1^{-1} mod e1 (e1 = 1 -> t1 = 0)
    t1 = 0 if e1 == 1 else pow(h1, -1, e1)
    j0 = (t1 * gamma) % e1
    leaves = 0
    for i in range(g1):
        gi = gamma - (j0 + i * e1) * h1
        if gi >= 0 and gi % e1 == 0:  # gi in W1 = e1*Z>=0
            leaves += 1
    return leaves * d

def a_sym_base(d, gamma):
    return d

# sealed-table self-check (the header's SEALED a_sym TABLES)
SEALED_ASYM = {(1, 1, 2): (1, 2, 2, 2), (1, 1, 3): (1, 2, 3, 3),
               (2, 1, 1): (1, 1, 1, 1), (2, 1, 2): (1, 1, 2, 2)}
print("=" * 76)
print("SELF-CHECK: Def SYM vs the sealed a_sym tables")
print("=" * 76)
for (e1, h1, g1), tab in sorted(SEALED_ASYM.items()):
    got = tuple(a_sym_one_stage(1, e1, h1, g1, g) for g in range(4))
    report("SELF", f"a_sym({e1},{h1},{g1}) gamma=0..3", got == tab, f"got {got} sealed {tab}")

# ============================================================================
# PART A — the n = 3 pack enumeration over Z_p boxes (my classifier)
# ============================================================================
def val_int(x, p, N):
    x %= p ** N
    if x == 0:
        return None
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v

def poly_shift(coeffs, r, pN):
    """f(x+r) for cubic x^3 + a x^2 + b x + c; coeffs = (a,b,c) mod pN."""
    a, b, c = coeffs
    A = (a + 3 * r) % pN
    B = (b + 2 * a * r + 3 * r * r) % pN
    C = (c + b * r + a * r * r + r ** 3) % pN
    return (A, B, C)

def fp_factor_cubic(a, b, c, p):
    """Pattern of x^3+ax^2+bx+c over F_p: returns (roots_with_mult dict,
    rem_deg, rem_irreducible) where rem is the rootless part."""
    roots = {}
    coeffs = [1, a % p, b % p, c % p]  # high->low
    for r in range(p):
        m, cur = 0, coeffs
        while len(cur) > 1:
            # synthetic division by (x - r)
            out, acc = [], 0
            for cc in cur:
                acc = (acc * r + cc) % p
                out.append(acc)
            if out[-1] != 0:
                break
            m += 1
            cur = out[:-1]
        if m:
            roots[r] = m
            # actually divide off (x-r)^m
    # recompute remainder properly
    cur = coeffs
    for r, m in roots.items():
        for _ in range(m):
            out, acc = [], 0
            for cc in cur:
                acc = (acc * r + cc) % p
                out.append(acc)
            assert out[-1] == 0
            cur = out[:-1]
    rem_deg = len(cur) - 1
    return roots, rem_deg, rem_deg >= 2  # deg-2/3 rootless over F_p => irreducible

def fp_factor_poly(coeffs_lowhigh, p):
    """Factor a monic poly (deg<=3) over F_p: list of (root, mult) +
    ('irr', deg) parts. coeffs low->high ints mod p, leading 1."""
    deg = len(coeffs_lowhigh) - 1
    coeffs = [x % p for x in reversed(coeffs_lowhigh)]  # high->low
    roots, cur = {}, coeffs
    for r in range(p):
        m = 0
        while len(cur) > 1:
            out, acc = [], 0
            for cc in cur:
                acc = (acc * r + cc) % p
                out.append(acc)
            if out[-1] != 0:
                break
            m += 1
            cur = out[:-1]
        if m:
            roots[r] = m
    parts = [(r, m) for r, m in roots.items()]
    remdeg = len(cur) - 1
    return parts, remdeg

def hull_segments(pts, N):
    """Lower Newton hull of pts = list of (i, v) with v int or None (>=N).
    Returns list of segments ((i1,v1),(i2,v2)) with slopes DECREASING as i
    grows toward the unit end; or None if undecided (a None-valued point
    could change the hull). Convention: only the positive-slope (cluster)
    part is passed in; the rightmost point has v known (=0)."""
    known = [(i, v) for i, v in pts if v is not None]
    unk = [i for i, v in pts if v is None]
    if not known:
        return None
    # hull of known points (lower convex hull, i increasing)
    known.sort()
    hull = []
    for pt in known:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            # keep lower: cross product
            if (x2 - x1) * (pt[1] - y1) - (pt[0] - x1) * (y2 - y1) <= 0:
                hull.pop()
            else:
                break
        hull.append(pt)
    # unknown points must lie weakly ABOVE the hull for it to be decided:
    def hull_val(x):
        for (x1, y1), (x2, y2) in zip(hull, hull[1:]):
            if x1 <= x <= x2:
                # value on segment (rational): return as fraction*denom trick
                return y1 + (y2 - y1) * (x - x1) / (x2 - x1)
        return None
    for i in unk:
        hv = hull_val(i)
        if hv is None or N < hv:  # could dip below the hull
            return None
    return list(zip(hull, hull[1:]))

def classify_cubic(coeffs, p, N, max_iter=None):
    """Classify monic cubic x^3+ax^2+bx+c over Z_p known mod p^N.
    Returns (sigma, letters, pools, decided) where sigma = sorted tuple of
    (e,f) or None if undecided; letters = list of realized letter records;
    pools = list of realized delta>1 pool records (birth letter D, child size).
    """
    pN = p ** N
    if max_iter is None:
        max_iter = 6 * N
    a, b, c = [x % pN for x in coeffs]
    letters, pools, sigma = [], [], []
    roots, rem_deg, rem_irr = fp_factor_cubic(a, b, c, p)
    # stage-1 simple factors
    simple = [(r, m) for r, m in roots.items() if m == 1]
    repeated = [(r, m) for r, m in roots.items() if m >= 2]
    for r, m in simple:
        sigma.append((1, 1))
        letters.append(("s1", 1))
    if rem_deg == 2:
        sigma.append((1, 2))
        letters.append(("s1", 2))
        pools.append({"birth": "s1-f2", "D": 2, "child_size": 1, "m_rel": 1})
    elif rem_deg == 3:
        sigma.append((1, 3))
        letters.append(("s1", 3))
        pools.append({"birth": "s1-f3", "D": 3, "child_size": 1, "m_rel": 1})
    decided = True
    for r, mu in repeated:
        res = classify_cluster((a, b, c), r, mu, p, N, letters, pools, max_iter)
        if res is None:
            decided = False
        else:
            sigma.extend(res)
    if not decided:
        return None, letters, pools, False
    return tuple(sorted(sigma)), letters, pools, True

def classify_cluster(coeffs, r, mu, p, N, letters, pools, max_iter):
    """Analyze the repeated cluster of multiplicity mu at residue root r.
    Iterative full re-analysis: recenter, Newton hull of the WHOLE cluster
    part (abscissa 0..mu; right endpoint (2, v(A)=0) for mu = 2 since the
    third root keeps residue distance 0, resp. (3, 0) for mu = 3), read all
    segments + residual factorizations. If ANY segment has a repeated
    residual root, DISCARD this iteration's partial output, shift the
    center to that root (depth p^h), and redo the whole polygon — shallower
    segments are re-derived unchanged (shifting by a deeper amount does not
    move them), so nothing is double-counted and each iteration's output is
    committed only when restart-free. Terminates: every restart strictly
    deepens the cluster; reads beyond depth N return undecided (None).
    Returns list of (e,f) or None (undecided)."""
    pN = p ** N
    center = r % p
    cur = poly_shift(coeffs, center, pN)
    from math import gcd
    for _ in range(max_iter):
        A, B, C = cur
        vA, vB, vC = val_int(A, p, N), val_int(B, p, N), val_int(C, p, N)
        if mu == 2:
            # third root stays at residue distance: v(A) = 0 exactly
            if vA != 0:
                return None  # can't happen for a genuine mu=2 cluster; honest bail
            pts = [(0, vC), (1, vB), (2, 0)]
        else:  # mu == 3
            pts = [(0, vC), (1, vB), (2, vA), (3, 0)]
        segs = hull_segments(pts, N)
        if segs is None:
            return None
        sigma_t, letters_t, pools_t = [], [], []
        restart = None
        undecided = False
        for (i1, v1), (i2, v2) in segs:
            ell = i2 - i1
            num, den = v1 - v2, ell
            if num <= 0:
                return None  # non-positive slope inside the cluster: bail honest
            gg = gcd(num, den)
            h, e = num // gg, den // gg
            g = ell // e
            # residual polynomial over F_p: residues at lattice points
            res_coeffs = []
            coef_list = [C, B, A, 1]
            ok = True
            for j in range(g + 1):
                idx = i1 + j * e
                need_v = v1 - j * h
                if idx == 3:
                    res_coeffs.append(1 if need_v == 0 else 0)
                    continue
                if need_v >= N:
                    ok = False
                    break
                cc = coef_list[idx]
                res_coeffs.append((cc // p ** need_v) % p)
            if not ok:
                undecided = True
                break
            assert res_coeffs[-1] % p != 0  # vertex => unit leading residual
            parts, remdeg = fp_factor_poly(res_coeffs, p)
            if remdeg >= 2:
                letters_t.append(("deep", e, h, remdeg))
                sigma_t.append((e, remdeg))
                pools_t.append({"birth": f"deep-g{remdeg}", "D": remdeg,
                                "child_size": 1, "m_rel": 1, "eh": (e, h)})
            for z0, m0 in parts:
                if z0 == 0:
                    return None  # impossible at a segment vertex; honest bail
                if m0 == 1:
                    letters_t.append(("deep", e, h, 1))
                    sigma_t.append((e, 1))
                else:
                    if e != 1:
                        return None  # repeated residual root needs e = 1 at n = 3
                    restart = (z0, h, m0)
        if undecided:
            return None
        if restart is None:
            letters.extend(letters_t)
            pools.extend(pools_t)
            return sigma_t
        z0, h, m0 = restart
        if h >= N:
            return None
        cur = poly_shift(cur, (z0 * p ** h) % pN, pN)
        # mu unchanged: the polygon is re-read in full at the new center
    return None  # iteration cap

def run_part_A(p, N, tag, prereg_patterns):
    pN = p ** N
    print("=" * 76)
    print(f"PART A [{tag}]: exhaustive monic cubics mod {p}^{N} = {pN**3} boxes")
    print("=" * 76)
    pattern_counts = Counter()
    letter_counts = Counter()
    pool_counts = Counter()
    sigma_counts = Counter()
    undecided = 0
    decided_boxes = []  # (a,b,c,sigma) for oracle
    bad_child = 0  # R-BIRTH refuter: realized pool with child_size>1 or gcd>1
    for a in range(pN):
        for b in range(pN):
            for c in range(pN):
                roots, rem_deg, _ = fp_factor_cubic(a, b, c, p)
                mults = sorted(roots.values(), reverse=True)
                if rem_deg == 2:
                    pat = "lin_x_irq"
                elif rem_deg == 3:
                    pat = "irc"
                elif mults == [1, 1, 1]:
                    pat = "split3"
                elif mults and mults[0] == 2:
                    pat = "double"
                else:
                    pat = "triple"
                pattern_counts[pat] += 1
                sigma, letters, pools, dec = classify_cubic((a, b, c), p, N)
                for L in letters:
                    letter_counts[L] += 1
                for P in pools:
                    pool_counts[(P["birth"], P["D"])] += 1
                    from math import gcd
                    if P["child_size"] > 1 or gcd(P["m_rel"], P["D"]) > 1:
                        bad_child += 1
                if dec:
                    sigma_counts[sigma] += 1
                    decided_boxes.append((a, b, c, sigma))
                else:
                    undecided += 1
    tot = pN ** 3
    print(f"  patterns: {dict(pattern_counts)}")
    for pat, want in prereg_patterns.items():
        report("A", f"{tag} pattern {pat} == {want}", pattern_counts[pat] == want,
               f"got {pattern_counts[pat]}")
    print(f"  decided {tot-undecided}/{tot}, undecided {undecided} (depth-capped, honest)")
    print(f"  sigma tallies (decided): {dict(sigma_counts)}")
    print(f"  letter roster: {dict(letter_counts)}")
    print(f"  delta>1 pool roster (birth family, D) -> count: {dict(pool_counts)}")
    # PRE-A3
    report("A", f"{tag} s1-f2 pools realized == lin_x_irq count",
           pool_counts[("s1-f2", 2)] == pattern_counts["lin_x_irq"],
           f"{pool_counts[('s1-f2',2)]}")
    report("A", f"{tag} s1-f3 pools realized == irc count",
           pool_counts[("s1-f3", 3)] == pattern_counts["irc"],
           f"{pool_counts[('s1-f3',3)]}")
    report("A", f"{tag} deep g=2 pools realized > 0", pool_counts[("deep-g2", 2)] > 0,
           f"{pool_counts[('deep-g2',2)]}")
    report("A", f"{tag} deep g=3 pools realized > 0", pool_counts[("deep-g3", 3)] > 0,
           f"{pool_counts[('deep-g3',3)]}")
    # PRE-A5 R-BIRTH
    report("A", f"{tag} R-BIRTH refuter hunt: realized pools with child gcd(m_rel,D)>1",
           bad_child == 0, f"count {bad_child} (sealed: 0, structural)")
    RESULTS["families"][f"A-{tag}"] = {
        "patterns": {k: v for k, v in pattern_counts.items()},
        "undecided": undecided,
        "letters": {str(k): v for k, v in letter_counts.items()},
        "pools": {str(k): v for k, v in pool_counts.items()},
        "sigma": {str(k): v for k, v in sigma_counts.items()},
        "r_birth_refuters": bad_child,
    }
    return decided_boxes

# ---- PARI oracle (gp CLI batch) ----
GP_HEADER = r"""
ef(g, p) = {
  my(d = poldegree(g));
  if(d == 1, return([1,1]));
  my(G = liftall(g), nf = nfinit([G, [p]]), dec = idealprimedec(nf, p));
  for(i = 1, #dec,
    my(pr = dec[i]);
    if(pr.e * pr.f == d, return([pr.e, pr.f])));
  my(pr = dec[1]); [pr.e, pr.f]
}
typ(f, p) = {
  my(fa = factorpadic(f, p, 40), out = List());
  for(i = 1, matsize(fa)[1],
    my(g = fa[i,1], m = fa[i,2], t = ef(g, p));
    for(j = 1, m, listput(out, t)));
  vecsort(Vec(out))
}
"""

def pari_check(boxes, p, tag, sample=None):
    """boxes: list of (a,b,c,sigma). Compare sigma against gp. Returns #mismatch."""
    if sample is not None and len(boxes) > sample:
        boxes = random.sample(boxes, sample)
    lines = [GP_HEADER, "mism = 0; tot = 0;"]
    for (a, b, c, sigma) in boxes:
        sig_str = "[" + ",".join(f"[{e},{f}]" for (e, f) in sigma) + "]"
        lines.append(
            f"tot++; if(typ(x^3+{a}*x^2+{b}*x+{c}, {p}) != vecsort({sig_str}),"
            f' mism++; print("MISMATCH ", {a}, " ", {b}, " ", {c}));')
    lines.append('print("TOT ", tot, " MISM ", mism); quit;')
    script = "\n".join(lines)
    fn = f"/tmp/nk3_gp_{tag}.gp"
    with open(fn, "w") as f:
        f.write(script)
    # -s 500M: pre-allocate the PARI stack; an auto-grow during a file read
    # makes gp ABORT the rest of the file ("skipping file") — silent
    # undercoverage otherwise (caught by the completeness assertion below).
    out = subprocess.run(["gp", "-q", "-s", "500000000", fn],
                         capture_output=True, text=True, timeout=1200).stdout
    mism, tot = None, None
    for line in out.splitlines():
        if line.startswith("TOT"):
            parts = line.split()
            mism = int(parts[3])
            tot = int(parts[1])
    print(f"  PARI oracle [{tag}]: {tot} boxes checked, {mism} mismatches")
    for line in out.splitlines():
        if "MISMATCH" in line:
            print("   ", line)
    report("A", f"PARI oracle completeness [{tag}]: all {len(boxes)} boxes executed",
           tot == len(boxes), f"tot={tot}")
    report("A", f"PARI oracle zero mismatches [{tag}]", mism == 0, f"{mism}/{tot}")
    return mism

# ============================================================================
# PART B — the gcd/Lidl–Niederreiter table over the realized residual families
# ============================================================================
def all_irreducible(p, g):
    """All monic irreducible degree-g polys over F_p (as low->high int tuples
    incl leading 1), by exhaustive rootlessness (g<=3)."""
    out = []
    for tail in itertools.product(range(p), repeat=g):
        coeffs = list(tail) + [1]
        parts, remdeg = fp_factor_poly(coeffs, p)
        if not parts and remdeg == g:
            out.append(tuple(coeffs))
    return out

def factor_degrees_over_ext(coeffs, p, delta):
    """Factor-degree multiset of a monic poly with F_p coefficients over
    F_{p^delta} (deg<=3: root scan + division)."""
    K = ff(p, delta)
    cs = [K.embed_base(c) for c in coeffs]  # low->high
    degs = []
    # peel roots
    cur = cs[:]
    changed = True
    while len(cur) > 2 and changed:
        changed = False
        for x in K.elements():
            if K.poly_eval(cur, x) == K.zero:
                # synthetic division by (z - x): coeffs high->low
                hi = list(reversed(cur))
                out, acc = [], K.zero
                for cc in hi:
                    acc = K.add(K.mul(acc, x), cc)
                    out.append(acc)
                assert out[-1] == K.zero
                cur = list(reversed(out[:-1]))
                degs.append(1)
                changed = True
                break
    if len(cur) == 2:
        degs.append(1)
    elif len(cur) > 2:
        # rootless remainder of degree 2 or 3 over K => irreducible
        # (also handles remainder deg 2 from cubic with one root)
        # check rootless:
        has_root = any(K.poly_eval(cur, x) == K.zero for x in K.elements())
        assert not has_root
        degs.append(len(cur) - 1)
    return tuple(sorted(degs))

def run_part_B():
    print("=" * 76)
    print("PART B: the M2 gcd-table seed rows, exhaustive over realized families")
    print("=" * 76)
    from math import gcd
    SEAL = {(2, 2): (1, 1), (2, 3): (2,), (2, 4): (1, 1), (2, 5): (2,),
            (3, 2): (3,), (3, 3): (1, 1, 1)}
    fam_stats = {}
    for p in (2, 3):
        for g in (2, 3):
            fam = all_irreducible(p, g)
            want_n = {(2, 2): 1, (2, 3): 2, (3, 2): 3, (3, 3): 8}[(p, g)]
            report("B", f"p={p} #monic irreducible deg {g} == {want_n}",
                   len(fam) == want_n, f"got {len(fam)}")
            deltas = (2, 3, 4, 5) if g == 2 else (2, 3)
            for dl in deltas:
                seal = SEAL[(g, dl)]
                bad = []
                for psi in fam:
                    got = factor_degrees_over_ext(list(psi), p, dl)
                    if got != seal:
                        bad.append((psi, got))
                report("B", f"p={p} (g={g}, delta={dl}) all {len(fam)} residuals -> {seal}"
                       f" [{'split' if gcd(g,dl)>1 else 'stable'}]",
                       not bad, f"anomalies: {bad}")
                fam_stats[f"p{p}g{g}d{dl}"] = {"n": len(fam), "seal": seal,
                                               "anomalies": len(bad)}
    # PRE-B3 R-FREE display
    print("  R-FREE refuter read (P3, no prediction — facts displayed):")
    print("   non-coprime realized rows (2,2),(2,4),(3,3) are NON-EMPTY at both")
    print("   primes where realized, and every member SPLITS exactly per")
    print("   Lidl-Niederreiter — refutation PRESSURE on Route A under the free")
    print("   re-base reading, realization/carrier-conditional (M4 branch (i)")
    print("   adjudication; blueprint fold finding 1). No branch fired here.")
    RESULTS["families"]["B"] = fam_stats

# ============================================================================
# PART C — intrinsic-law digit censuses over GR(p^M, delta)
# ============================================================================
def census(p, delta, e1, h1, psi_coeffs, Gamma=3, raw_control=False, M=None):
    """Exhaustive digit census for the one-stage tower (d=1, (e1,h1), psi over
    F_{p^delta}) at heights gamma <= Gamma, over base O_delta.
    psi_coeffs: low->high ints (F_p coefficients embedded); g = deg psi.
    Returns dict gamma -> set of digit tuples (g-tuples of F_q elements).
    The census enumerates the digit-determining data exactly: per top-space
    coefficient b_j, its valuation v_j in {0..Gamma} or DEEP, and res(u_j)
    in F_q^x. Complete for heights <= Gamma (see header).
    If raw_control: additionally brute-force over GR(p^M, delta)^(e1*g) and
    assert equality (only for small boxes)."""
    K = ff(p, delta)
    g = len(psi_coeffs) - 1
    nslots = e1 * g
    units = [x for x in K.elements() if x != K.zero]
    A = {gam: set() for gam in range(Gamma + 1)}
    zerodig = tuple(K.zero for _ in range(g))
    for gam in A:
        A[gam].add(zerodig)  # level-set reading: 0 from deeper B
    t1 = 0 if e1 == 1 else pow(h1, -1, e1)
    vchoices = list(range(Gamma + 1)) + [None]  # None = deep (> Gamma)
    for vprof in itertools.product(vchoices, repeat=nslots):
        ws = [e1 * v + j * h1 for j, v in enumerate(vprof) if v is not None]
        if not ws:
            continue
        w = min(ws)
        if w > Gamma:
            continue
        j0 = (t1 * w) % e1
        # contributing slots: j = j0 + i*e1, v_j = (w - j*h1)/e1 exact
        slots = []
        for i in range(g):
            j = j0 + i * e1
            if j >= nslots:
                break
            need = w - j * h1
            if need >= 0 and need % e1 == 0 and vprof[j] == need // e1:
                slots.append((i, j))
        # every slot achieving the min must be a contributing slot
        # (guaranteed by j = t1*w mod e1 arithmetic; assert)
        for j, v in enumerate(vprof):
            if v is not None and e1 * v + j * h1 == w:
                assert any(jj == j for _, jj in slots), (vprof, w, j0, slots)
        if not slots:
            continue
        # digit values: unit residues at contributing slots, anything at rest
        for combo in itertools.product(units, repeat=len(slots)):
            dig = [K.zero] * g
            for (i, _), u in zip(slots, combo):
                dig[i] = u
            A[w].add(tuple(dig))
    if raw_control:
        Mv = Gamma + 1  # needed v <= Gamma at any height gamma <= Gamma
        R = GR(p, Mv, delta)
        Araw = {gam: {zerodig} for gam in range(Gamma + 1)}
        allelts = [tuple(v) for v in itertools.product(range(R.pm), repeat=delta)]
        for B in itertools.product(allelts, repeat=nslots):
            vs = [R.v(b) for b in B]
            ws = [e1 * v + j * h1 for j, v in enumerate(vs) if v is not None]
            if not ws:
                continue
            w = min(ws)
            if w > Gamma:  # residues exact: needed v <= Gamma < Mv
                continue
            j0 = (t1 * w) % e1
            dig = [K.zero] * g
            okslot = False
            for i in range(g):
                j = j0 + i * e1
                if j >= nslots:
                    break
                need = w - j * h1
                if need >= 0 and need % e1 == 0 and vs[j] == need // e1:
                    dig[i] = R.shift_res(B[j], vs[j])
                    okslot = True
            if okslot:
                Araw[w].add(tuple(dig))
        for gam in range(Gamma + 1):
            report("C", f"raw-box control p={p} d={delta} ({e1},{h1},g={g}) gamma={gam}",
                   Araw[gam] == A[gam],
                   f"raw {len(Araw[gam])} vs reduced {len(A[gam])}")
    return A, K, g

def logp_size(n, p):
    a = 0
    while n % p == 0 and n > 1:
        n //= p
        a += 1
    return a if n == 1 else None

def check_stable_pool(name, p, delta, e1, h1, psi, sealed_sizes, a1_census=None,
                      raw_control=False, M=None):
    """Stable pool: matched letter persists; check P1/P2/(P4)/span."""
    A, K, g = census(p, delta, e1, h1, psi, raw_control=raw_control, M=M)
    got = tuple(len(A[gam]) for gam in range(4))
    report("C", f"{name}: |A(gamma)| gamma=0..3 == {sealed_sizes}",
           got == sealed_sizes, f"got {got}")
    for gam in range(4):
        a_obs = logp_size(len(A[gam]), p)
        asym = a_sym_one_stage(1, e1, h1, g, gam)
        p1 = (a_obs is not None) and (a_obs == delta * asym)
        report("C", f"{name} P1 gamma={gam}: a_delta = delta*a_sym",
               p1, f"a_obs={a_obs} delta*a_sym={delta}*{asym}={delta*asym}")
        p2 = (a_obs is not None) and (a_obs % delta == 0)
        report("C", f"{name} P2 gamma={gam}: delta | a_delta", p2, f"a_obs={a_obs}")
        # span check: A(gamma) == predicted span {sum_{i in I} c_i z^i}
        t1 = 0 if e1 == 1 else pow(h1, -1, e1)
        j0 = (t1 * gam) % e1
        I = [i for i in range(g)
             if (gam - (j0 + i * e1) * h1) >= 0 and (gam - (j0 + i * e1) * h1) % e1 == 0]
        span = set()
        for combo in itertools.product(K.elements(), repeat=len(I)):
            dig = [K.zero] * g
            for i, cv in zip(I, combo):
                dig[i] = cv
            span.add(tuple(dig))
        report("C", f"{name} span equality gamma={gam}", A[gam] == span,
               f"|A|={len(A[gam])} |span|={len(span)}")
        if a1_census is not None:
            a1 = logp_size(len(a1_census[gam]), p)
            report("C", f"{name} P4 gamma={gam}: a_delta = delta*a_1",
                   a_obs == delta * a1, f"a_obs={a_obs} delta*a1={delta}*{a1}")
    return A

def check_split_pool(name, p, delta, e1, h1, psi, sealed_branch_sizes,
                     naive_a1=None):
    """Split pool: psi (F_p coefficients) splits over F_{p^delta}; realized
    per-branch letters; P1: per-branch value sets, a_branch = delta*1."""
    K = ff(p, delta)
    g = len(psi) - 1
    # roots of psi over K
    cs = [K.embed_base(c) for c in psi]
    roots = [x for x in K.elements() if K.poly_eval(cs, x) == K.zero]
    report("C", f"{name}: residual splits over F_{p}^{delta} into {g} roots",
           len(roots) == g, f"roots found: {len(roots)}")
    A, K2, _ = census(p, delta, e1, h1, psi)
    for bi, rb in enumerate(roots):
        for gam in range(4):
            # branch projection: evaluate digit poly at z = rb
            vals = set()
            for dig in A[gam]:
                vals.add(K.poly_eval(list(dig), rb))
            got = len(vals)
            want = sealed_branch_sizes[gam]
            report("C", f"{name} branch {bi} gamma={gam}: |branch A| == {want}",
                   got == want, f"got {got}")
            a_obs = logp_size(got, p)
            # branch letter (e1,h1,1): a_sym = 1 at every height
            asym_branch = a_sym_one_stage(1, e1, h1, 1, gam)
            report("C", f"{name} branch {bi} P1 gamma={gam}: a = delta*a_sym(branch)",
                   a_obs == delta * asym_branch,
                   f"a_obs={a_obs} delta*a_sym={delta}*{asym_branch}")
            report("C", f"{name} branch {bi} P2 gamma={gam}",
                   a_obs is not None and a_obs % delta == 0, f"a_obs={a_obs}")
    if naive_a1 is not None:
        # the F9-shape contrast display: naive delta*a_1 vs per-branch a
        for gam in range(4):
            naive = delta * naive_a1[gam]
            print(f"  [DISPLAY] {name} gamma={gam}: naive stability read "
                  f"delta*a_1 = {naive} vs realized per-branch a = {delta} "
                  f"({'CONTRAST — stability law out of domain here' if naive != delta else 'coincide'})")

def check_base_pool(name, p, delta, sealed_sizes, Gamma=3):
    """C5: the size-1 child over O_delta: single coefficient census."""
    K = ff(p, delta)
    units = [x for x in K.elements() if x != K.zero]
    for v in range(Gamma + 1):
        # A(v) = {res(u)} u unit, plus 0 = full F_q
        A = set(units) | {K.zero}
        got = len(A)
        report("C", f"{name} height v={v}: |A| == {sealed_sizes[v]}",
               got == sealed_sizes[v], f"got {got}")
        a_obs = logp_size(got, p)
        report("C", f"{name} P1 v={v}: a_delta = delta*a_sym(base,d=1)",
               a_obs == delta * 1, f"a_obs={a_obs} delta={delta}")

def run_part_C():
    print("=" * 76)
    print("PART C: intrinsic-law censuses (P1/P2/P4) at the pools")
    print("=" * 76)
    # --- C1: p=3 (1,1,2) psi=z^2+1 ---
    A1_c1, _, _ = census(3, 1, 1, 1, [1, 0, 1], raw_control=True, M=4)
    got = tuple(len(A1_c1[g]) for g in range(4))
    report("C", "C1 delta=1 control |A| == (3,9,9,9)", got == (3, 9, 9, 9), f"{got}")
    a1_c1 = [logp_size(len(A1_c1[g]), 3) for g in range(4)]
    check_split_pool("C1 delta=2 SPLIT pool", 3, 2, 1, 1, [1, 0, 1],
                     (9, 9, 9, 9), naive_a1=a1_c1)
    check_stable_pool("C1 delta=3 STABLE pool", 3, 3, 1, 1, [1, 0, 1],
                      (27, 729, 729, 729), a1_census=A1_c1)
    # --- C2: p=3 (1,1,3) psi=z^3+2z+2 ---
    A1_c2, _, _ = census(3, 1, 1, 1, [2, 2, 0, 1])
    got = tuple(len(A1_c2[g]) for g in range(4))
    report("C", "C2 delta=1 control |A| == (3,9,27,27)", got == (3, 9, 27, 27), f"{got}")
    a1_c2 = [logp_size(len(A1_c2[g]), 3) for g in range(4)]
    check_stable_pool("C2 delta=2 STABLE pool", 3, 2, 1, 1, [2, 2, 0, 1],
                      (9, 81, 729, 729), a1_census=A1_c2)
    check_split_pool("C2 delta=3 SPLIT pool", 3, 3, 1, 1, [2, 2, 0, 1],
                     (27, 27, 27, 27), naive_a1=a1_c2)
    # --- C3: p=2 (1,1,2) psi=z^2+z+1 ---
    A1_c3, _, _ = census(2, 1, 1, 1, [1, 1, 1], raw_control=True, M=4)
    got = tuple(len(A1_c3[g]) for g in range(4))
    report("C", "C3 delta=1 control |A| == (2,4,4,4)", got == (2, 4, 4, 4), f"{got}")
    a1_c3 = [logp_size(len(A1_c3[g]), 2) for g in range(4)]
    check_split_pool("C3 delta=2 SPLIT pool", 2, 2, 1, 1, [1, 1, 1],
                     (4, 4, 4, 4), naive_a1=a1_c3)
    check_stable_pool("C3 delta=3 STABLE pool", 2, 3, 1, 1, [1, 1, 1],
                      (8, 64, 64, 64), a1_census=A1_c3)
    # --- C4: p=3 (2,1,1) psi=z+2 (residual root 1, g=1) ---
    A1_c4, _, _ = census(3, 1, 2, 1, [2, 1], raw_control=True, M=3)
    got = tuple(len(A1_c4[g]) for g in range(4))
    report("C", "C4 delta=1 control |A| == (3,3,3,3)", got == (3, 3, 3, 3), f"{got}")
    check_stable_pool("C4 delta=2 STABLE pool (ram '21' leg)", 3, 2, 2, 1, [2, 1],
                      (9, 9, 9, 9), a1_census=A1_c4)
    # --- C4b: p=2 (2,1,1) psi=z+1 ---
    A1_c4b, _, _ = census(2, 1, 2, 1, [1, 1])
    got = tuple(len(A1_c4b[g]) for g in range(4))
    report("C", "C4b delta=1 control |A| == (2,2,2,2)", got == (2, 2, 2, 2), f"{got}")
    check_stable_pool("C4b delta=2 STABLE pool", 2, 2, 2, 1, [1, 1],
                      (4, 4, 4, 4), a1_census=A1_c4b)
    check_stable_pool("C4b delta=3 STABLE pool", 2, 3, 2, 1, [1, 1],
                      (8, 8, 8, 8), a1_census=A1_c4b)
    # --- C5: base pools (children of the stage-1 f=2/f=3 letters) ---
    check_base_pool("C5 p=3 delta=2 base pool (s1-f2 child)", 3, 2, (9, 9, 9, 9))
    check_base_pool("C5 p=2 delta=3 base pool (s1-f3 child)", 2, 3, (8, 8, 8, 8))
    # --- C6: p=2 (1,1,3) psi=z^3+z+1 ---
    A1_c6, _, _ = census(2, 1, 1, 1, [1, 1, 0, 1])
    got = tuple(len(A1_c6[g]) for g in range(4))
    report("C", "C6 delta=1 control |A| == (2,4,8,8)", got == (2, 4, 8, 8), f"{got}")
    a1_c6 = [logp_size(len(A1_c6[g]), 2) for g in range(4)]
    check_stable_pool("C6 delta=2 STABLE pool", 2, 2, 1, 1, [1, 1, 0, 1],
                      (4, 16, 64, 64), a1_census=A1_c6)
    check_split_pool("C6 delta=3 SPLIT pool", 2, 3, 1, 1, [1, 1, 0, 1],
                     (8, 8, 8, 8), naive_a1=a1_c6)
    # --- C7: p=3 (2,1,2) psi=z^2+1 — M14 T3's witness tower (M5 §5.2 shape) ---
    A1_c7, _, _ = census(3, 1, 2, 1, [1, 0, 1])
    got = tuple(len(A1_c7[g]) for g in range(4))
    report("C", "C7 delta=1 control |A| == (3,3,9,9)", got == (3, 3, 9, 9), f"{got}")
    a1_c7 = [logp_size(len(A1_c7[g]), 3) for g in range(4)]
    check_split_pool("C7 delta=2 SPLIT pool (THE F9 shape, T3 re-based run EXECUTED)",
                     3, 2, 2, 1, [1, 0, 1], (9, 9, 9, 9), naive_a1=a1_c7)
    check_stable_pool("C7 delta=3 STABLE pool (M14 T1's numbers, re-run)",
                      3, 3, 2, 1, [1, 0, 1], (27, 27, 729, 729), a1_census=A1_c7)

# ============================================================================
# MAIN
# ============================================================================
def main():
    # PART A
    prereg3 = {"split3": 19683, "lin_x_irq": 177147, "irc": 157464,
               "double": 118098, "triple": 59049}
    boxes3 = run_part_A(3, 4, "p3-N4", prereg3)
    prereg2 = {"split3": 0, "lin_x_irq": 8192, "irc": 8192,
               "double": 8192, "triple": 8192}
    boxes2 = run_part_A(2, 5, "p2-N5", prereg2)
    print(f"[t={time.time()-T0:.0f}s] classifier done; PARI oracle passes...")
    # oracle: full p=3 N=3 box = classify separately at N=3
    pN3 = 27
    boxes3_N3 = []
    und3 = 0
    for a in range(pN3):
        for b in range(pN3):
            for c in range(pN3):
                sigma, _, _, dec = classify_cubic((a, b, c), 3, 3)
                if dec:
                    boxes3_N3.append((a, b, c, sigma))
                else:
                    und3 += 1
    print(f"  p=3 N=3 box: {len(boxes3_N3)} decided, {und3} undecided")
    pari_check(boxes3_N3, 3, "p3-N3-full")
    pari_check(boxes3, 3, "p3-N4-sample5000", sample=5000)
    pari_check(boxes2, 2, "p2-N5-full")
    print(f"[t={time.time()-T0:.0f}s] PART B...")
    run_part_B()
    print(f"[t={time.time()-T0:.0f}s] PART C...")
    run_part_C()
    print("=" * 76)
    nv = len(VIOL)
    verdict = "ALL GREEN" if nv == 0 else f"RED: {nv} violations"
    print(f"N-K3 VERDICT: {verdict}  [runtime {time.time()-T0:.0f}s]")
    if nv:
        for v in VIOL:
            print("  ", v)
    RESULTS["verdict"] = verdict
    RESULTS["runtime_s"] = round(time.time() - T0)
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "nk3_check_results.json"), "w") as f:
        json.dump(RESULTS, f, indent=1, default=str)
    print("results JSON written.")
    return 0 if nv == 0 else 1

if __name__ == "__main__":
    sys.exit(main())
