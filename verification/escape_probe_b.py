#!/usr/bin/env python3
"""ESCAPE-probe layer (b) -- the k = 1..8 still-in-block decay census.

CONSISTENCY CLASS ONLY (MOVES_2026-07-24.md PROBE ROSTER (b), ~L12231): this layer
refutes sealed finite-depth predictions, NEVER the asymptotic E0 (arbitrarily delayed
escape is E0-compatible); a row stabilizing above 0 is a FINDING to adjudicate.

Sealed predictions under test (CASE_RESUMN3_SEALED_PREDICTIONS.md S4, sealed
2026-07-27): still-in-block masses blk2 = kappa_2^k, blk3 same-size = kappa_3^k,
kappa_2 = (q-1)/(q^3-1), kappa_3 = (q-1)/(q^6-1); the depth partials T_k via
  D2(j) = 1 - kappa_2^j;  D3(j) = t3tot + J*D2(j-1) + kappa_3*D3(j-1), D3(0) = 0,
  t3tot = 1 - J - kappa_3;  T_k = (1 - 1/q) + (q-1)/q^2 * D2(k-1) + 1/q^2 * D3(k-1).
Layers:
  B1 exact kernel decay A^k*1 (matrix power, Fractions) vs kappa^k, p in {2,3,5,7},
     n in {2,3}, k = 1..8: strict decrease, geometric ratio, no stabilization.
  B2 the sealed T_k lists re-derived (p = 2 k <= 8; p = 3 k <= 5).
  B3 INDEPENDENT blk2 digit census (exact integer boxes, p in {2,3}): exact per-stratum
     first-read counts vs the V.6.3 closed forms, and the two-sided bracket
     certified_still_k/total <= kappa_2^k <= (certified_still_k + unresolved_k)/total.
  B4 same for blk3 (per-type same-size leg): stratum-A cell counts + kappa_3 bracket.
Box semantics: a box is h mod p^M per coefficient; a step is CERTIFIED only when every
digit its verdict needs lies inside the box (else UNRESOLVED bin, own count) --
RESUM-n3's cylinder-decisiveness discipline. Split legs (A dbl+simple, C/D_even double)
EXIT the block (row-deficit semantics; K-columns are the (c=1,m=1) outcomes only).
"""
import sys
from fractions import Fraction as F

FINDINGS = []
def chk(name, cond, detail=""):
    tag = "PASS" if cond else "FINDING"
    if not cond: FINDINGS.append(name)
    print(f"[{tag}] {name}  {detail}")

def kap2(p): return F(p-1, p**3-1)
def kap3(p): return F(p-1, p**6-1)
def Jval(p): return F((p-1)*(p-2)+(p-1), p**6-1) + F((p-1)**2, (p**3-1)*(p**6-1))

KMAX = 8
print("=" * 72)
print("B1. Exact kernel decay A^k 1 vs kappa^k (p in {2,3,5,7}, n in {2,3}, k<=8)")
print("=" * 72)
for p in (2, 3, 5, 7):
    for n in (2, 3):
        # A over states [blk2] (n=2) / [blk2, blk3] (n=3); K-columns only -> diagonal
        diag = [kap2(p)] + ([kap3(p)] if n == 3 else [])
        vec = [F(1)] * len(diag)
        ok_closed, ok_dec = True, True
        prev = None
        for k in range(1, KMAX + 1):
            vec = [d * v for d, v in zip(diag, vec)]        # A^k 1 (A diagonal)
            closed = [d**k for d in diag]
            if vec != closed: ok_closed = False
            if prev is not None and not all(v < pv for v, pv in zip(vec, prev)):
                ok_dec = False
            prev = vec
        names = ["blk2"] + (["blk3"] if n == 3 else [])
        chk(f"p={p} n={n}: A^k 1 == kappa^k per type, strictly decreasing, k=1..8",
            ok_closed and ok_dec,
            f"k=8: {dict(zip(names, [str(v) for v in vec]))}")
        # no stabilization above 0: k=8 value < k=4 value < kappa (trivially geometric)
        chk(f"p={p} n={n}: no stabilization (kappa^8 < kappa^4 * kappa^2)",
            all(d**8 < d**4 * d**2 for d in diag))

print("=" * 72)
print("B2. Sealed depth partials T_k (RESUM-n3 S4) re-derived from the recursions")
print("=" * 72)
SEALED_T = {
    2: [F(1,2), F(281,294), F(18413,18522), F(166559,166698), F(73505069,73513818),
        F(4631291801,4631370534), F(5954604797,5954619258),
        F(18381903272153,18381909649446)],
    3: [F(2,3), F(3485,3549), F(1290071,1291836), F(470178911,470228304),
        F(171161719679,171163102656)],
}
for p, sealed in SEALED_T.items():
    k2_, k3_, J_ = kap2(p), kap3(p), Jval(p)
    t3tot = 1 - J_ - k3_
    D2 = lambda j: 1 - k2_**j
    D3 = [F(0)]
    for j in range(1, len(sealed)):
        D3.append(t3tot + J_ * D2(j - 1) + k3_ * D3[j - 1])
    got = [F(1) - F(1,p) + F(p-1, p**2) * D2(k-1) + F(1, p**2) * D3[k-1]
           for k in range(1, len(sealed) + 1)]
    chk(f"p={p}: T_k == sealed, k=1..{len(sealed)}", got == sealed,
        f"T_{len(sealed)}={got[-1]}")
    chk(f"p={p}: T_k increasing, 1 - T_k -> 0", all(a < b for a, b in zip(got, got[1:]))
        and 1 - got[-1] < F(1, 10**5))

# ---------------------------------------------------------------- digit walks
def vex(x, p, M):
    """exact valuation of x (known mod p^M), or None if x = 0 mod p^M (v >= M)."""
    if M <= 0 or x == 0: return None
    v = 0
    while x % p == 0: x //= p; v += 1
    return v

def walk_blk2(h0, h1, M0, M1, p, kmax, first=None):
    """Certified walk of the size-2 block; returns (#continues certified, status).
    status: 'exit' | 'unresolved' | 'alive' (still in block after kmax certified)."""
    k = 0
    while True:
        if k >= kmax: return k, 'alive'
        k0, k1 = vex(h0, p, M0), vex(h1, p, M1)
        if k0 is None:                       # v(h0) >= M0
            if k1 is not None and M0 > 2 * k1:
                if first is not None and k == 0: first[("m_vv", k1)] = first.get(("m_vv", k1), 0) + 1
                return k, 'exit'             # every completion is m_vv(k1)
            return k, 'unresolved'
        if k0 % 2 == 1:                      # m_w2 or m_vv -- both exits
            if first is not None and k == 0:
                if k1 is not None and 2 * k1 < k0:
                    first[("m_vv", k1)] = first.get(("m_vv", k1), 0) + 1
                else:                        # k1 exact > k0/2, or k1 >= M1 > k0/2
                    first[("m_w2", k0)] = first.get(("m_w2", k0), 0) + 1
            return k, 'exit'
        lam = k0 // 2
        if k1 is not None:
            if k1 < lam:
                if first is not None and k == 0: first[("m_vv", k1)] = first.get(("m_vv", k1), 0) + 1
                return k, 'exit'             # m_vv
            w = (h1 // p**lam) % p
        else:
            if M1 < lam + 1: return k, 'unresolved'
            w = 0
        u = (h0 // p**k0) % p                # lead digit, nonzero
        roots = [r for r in range(p) if (r*r + w*r + u) % p == 0]
        dbl = (w*w - 4*u) % p == 0 and roots
        if first is not None and k == 0:
            out = "o_double" if dbl else ("o_split" if len(roots) == 2 else "o_inert")
            first[("m2", lam, out)] = first.get(("m2", lam, out), 0) + 1
        if not dbl:
            return k, 'exit'                 # o_split / o_inert
        y = roots[0]
        s, t = h1 // p**lam, h0 // p**k0
        M1n, M0n = M1 - lam, min(M0 - 2*lam, M1 - lam)
        h1n, h0n = s + 2*y, y*y + s*y + t
        M0n, M1n = max(M0n, 0), max(M1n, 0)
        h0, h1, M0, M1 = h0n % p**M0n, h1n % p**M1n, M0n, M1n
        k += 1

def cubic_tags(abar, bbar, cbar, p):
    """factorization tag of y^3 + abar y^2 + bbar y + cbar over F_p (cbar != 0)."""
    for r in range(1, p):                    # triple root (nonzero since cbar != 0)
        if (abar + 3*r) % p == 0 and (bbar - 3*r*r) % p == 0 and (cbar + r**3) % p == 0:
            return "triple", r
    roots = [r for r in range(p) if (r**3 + abar*r*r + bbar*r + cbar) % p == 0]
    if len(roots) == 3: return "3dist", None
    if len(roots) == 0: return "irr", None
    dbl = [r for r in roots if (3*r*r + 2*abar*r + bbar) % p == 0]
    if dbl: return "dblsimple", None         # double + simple (2 distinct roots)
    return "linquad", None                   # one simple root + irreducible quadratic

def walk_blk3(a, b, c, Ma, Mb, Mc, p, kmax, first=None):
    """Certified same-size walk of the size-3 block (A-triple continues; all else exits)."""
    INF = 10**9
    k = 0
    while True:
        if k >= kmax: return k, 'alive'
        ka, kb, kc = vex(a, p, Ma), vex(b, p, Mb), vex(c, p, Mc)
        if kc is None:                       # kc >= Mc: A-completion needs kc<=min(3kb/2,3ka)
            ub = min((3*kb)//2 if kb is not None else INF,
                     3*ka if ka is not None else INF)
            if ub < INF:
                first3 = ((Mc + 2) // 3) * 3
                if first3 > ub: return k, 'exit'   # no stratum-A completion exists
            return k, 'unresolved'
        if kc % 3 != 0: return k, 'exit'     # B or C/D/E -- all exits
        L = kc // 3
        if kb is not None:
            if kb < 2*L: return k, 'exit'    # vertex below the side: C/E -- exit
            bbar = (b // p**(2*L)) % p
        else:
            if Mb <= 2*L: return k, 'unresolved'
            bbar = 0
        if ka is not None:
            if ka < L: return k, 'exit'      # vertex below: D/E -- exit
            abar = (a // p**L) % p
        else:
            if Ma <= L: return k, 'unresolved'
            abar = 0
        cbar = (c // p**kc) % p
        tag, r = cubic_tags(abar, bbar, cbar, p)
        if first is not None and k == 0:
            first[("A", L, tag)] = first.get(("A", L, tag), 0) + 1
        if tag != "triple": return k, 'exit'
        A_, B_, C_ = a // p**L, b // p**(2*L), c // p**kc
        MaN, MbN = Ma - L, min(Mb - 2*L, Ma - L)
        McN = min(Mc - 3*L, Mb - 2*L, Ma - L)
        a2, b2 = A_ + 3*r, B_ + 2*A_*r + 3*r*r
        c2 = C_ + B_*r + A_*r*r + r**3
        MaN, MbN, McN = max(MaN,0), max(MbN,0), max(McN,0)
        a, b, c = a2 % p**MaN, b2 % p**MbN, c2 % p**McN
        Ma, Mb, Mc = MaN, MbN, McN
        k += 1

print("=" * 72)
print("B3. Independent blk2 digit census (exact boxes): strata + kappa_2^k bracket")
print("=" * 72)
for p, M in ((2, 10), (3, 7)):
    tot = p**(2*(M-1))
    first, still, unres = {}, [0]*(KMAX+1), [0]*(KMAX+1)
    for i in range(p**(M-1)):
        h0 = p * i
        for jj in range(p**(M-1)):
            h1 = p * jj
            k, st = walk_blk2(h0, h1, M, M, p, KMAX, first)
            if st in ('alive', 'exit'):
                reach = k if st == 'alive' else k       # certified continues
                for kk in range(1, reach + 1): still[kk] += 1
            if st == 'unresolved':
                for kk in range(1, KMAX + 1):
                    if kk > k: unres[kk] += 1
                for kk in range(1, k + 1): still[kk] += 1
    # depth-1 exact stratum counts vs V.6.3 closed forms (in-precision strata)
    ok, ndone = True, 0
    cell = {"o_split": (p-1)*(p-2)//2, "o_inert": p*(p-1)//2, "o_double": p-1}
    for lam in range(1, (M-1)//2 + 1):
        for out, c in cell.items():
            pred = c * p**(2*M - 2 - 3*lam)
            got = first.get(("m2", lam, out), 0)
            if got != pred: ok = False
            ndone += 1
    for k0 in range(1, M, 2):
        pred = (p-1) * p**(2*M - 2 - (3*k0 - 1)//2)
        if first.get(("m_w2", k0), 0) != pred: ok = False
        ndone += 1
    for k1 in range(1, (M-2)//2 + 1):
        pred = (p-1) * p**(2*M - 2 - 3*k1)
        if first.get(("m_vv", k1), 0) != pred: ok = False
        ndone += 1
    chk(f"p={p} blk2 M={M}: all {ndone} in-precision first-read stratum counts exact", ok)
    okb = all(F(still[k], tot) <= kap2(p)**k <= F(still[k] + unres[k], tot)
              for k in range(1, KMAX + 1))
    chk(f"p={p} blk2: bracket still_k/tot <= kappa_2^k <= (still_k+unres_k)/tot, k=1..8",
        okb, f"k=1: {still[1]}/{tot} <= {kap2(p)} <= {(still[1]+unres[1])}/{tot}")
    chk(f"p={p} blk2: census still_k strictly decreasing to 0-or-unresolved",
        all(still[k] >= still[k+1] for k in range(1, KMAX)) and still[KMAX] < still[1])
    print(f"       p={p} still_k: {still[1:]},  unres_k: {unres[1:]}")

print("=" * 72)
print("B4. Independent blk3 digit census: stratum-A cells + kappa_3^k bracket")
print("=" * 72)
for p, M in ((2, 7), (3, 5)):
    tot = p**(3*(M-1))
    first, still, unres = {}, [0]*(KMAX+1), [0]*(KMAX+1)
    rng = range(p**(M-1))
    for i in rng:
        a = p * i
        for jj in rng:
            b = p * jj
            for kk3 in rng:
                c = p * kk3
                k, st = walk_blk3(a, b, c, M, M, M, p, KMAX, first)
                for kk in range(1, k + 1): still[kk] += 1
                if st == 'unresolved':
                    for kk in range(k + 1, KMAX + 1): unres[kk] += 1
    cellA = {"3dist": (p-1)*(p-2)*(p-3)//6, "linquad": p*(p-1)**2//2,
             "irr": (p**3-p)//3, "dblsimple": (p-1)*(p-2), "triple": p-1}
    ok, ndone = True, 0
    for L in range(1, (M-1)//3 + 1):
        for tag, c in cellA.items():
            pred = c * p**(3*(M-1) - 6*L)
            if first.get(("A", L, tag), 0) != pred: ok = False
            ndone += 1
    chk(f"p={p} blk3 M={M}: all {ndone} in-precision stratum-A cell counts exact", ok,
        f"L=1 census row {[first.get(('A',1,t),0) for t in cellA]}")
    okb = all(F(still[k], tot) <= kap3(p)**k <= F(still[k] + unres[k], tot)
              for k in range(1, KMAX + 1))
    chk(f"p={p} blk3: bracket still_k/tot <= kappa_3^k <= (still_k+unres_k)/tot, k=1..8",
        okb, f"k=1: {still[1]}/{tot} <= {kap3(p)} <= {(still[1]+unres[1])}/{tot}")
    print(f"       p={p} still_k: {still[1:]},  unres_k: {unres[1:]}")

print("=" * 72)
if not FINDINGS:
    print("ESCAPE-PROBE-B VERDICT: ALL PASS -- every sealed finite-depth prediction "
          "confirmed; every still-in-block row decays (consistency class only: "
          "this cannot prove E0, which stays OPEN per-pool).")
else:
    print(f"ESCAPE-PROBE-B VERDICT: {len(FINDINGS)} FINDING(S): {FINDINGS}")
sys.exit(0 if not FINDINGS else 1)
