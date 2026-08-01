#!/usr/bin/env python3
"""ADM-U7 numeric falsifier: realized strata with PARTIAL right-end on-line slots.

Three explicit realized instances at p = 2 (order-1 parent types, order-2 reads):
  A: n=4, type (e1,f1,h1)=(1,2,1)  -> free-slot right end k_s=1 < ell=2, beta=0 PARTIAL
  B: n=3, type (e1,f1,h1)=(1,2,2)  -> K7's shape realized at the m∤n monic top, beta=1 PARTIAL
  C: n=4, type (e1,f1,h1)=(1,2,1)  -> m|n monic-top chain k_s=ell, beta=0 at pinned slot;
     K_D-slots FULL; CEN-W monic-top display EXACT despite displayed-(ADM) failing at slot ell.

All types have f0=1 (phi1 = x), e = e1 = 1, d = f1 = 2, m = 2, V^ = 2*h1,
ledger weights {0, h1} (w(x) = h1), w(c1*x + c0) = min(v2(c1) + h1, v2(c0)).
"""
import sys
from math import inf

p = 2
def v2(n):
    if n == 0: return inf
    n = abs(n); v = 0
    while n % 2 == 0: n //= 2; v += 1
    return v

def polydiv(f, g):
    """f, g integer coeff lists (low->high), g monic. Return (q, r) exact over Z."""
    f = f[:]; dg = len(g) - 1; q = [0]*(max(len(f)-dg, 0))
    for i in range(len(f)-1, dg-1, -1):
        c = f[i]
        q[i-dg] = c
        for j in range(dg+1):
            f[i-dg+j] -= c*g[j]
    while len(f) > dg: f.pop()
    return q, f

def polymul(a, b):
    r = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): r[i+j] += x*y
    return r

def development(f, phi):
    out = []
    while f:
        q, r = polydiv(f, phi)
        r = r + [0]*(len(phi)-1-len(r))
        out.append(r[:len(phi)-1])
        f = q
        if all(c == 0 for c in f): break
    return out  # list of [c0, c1] coefficient pairs (deg < 2)

def w_lin(c, h1):
    c0 = c[0]; c1 = c[1] if len(c) > 1 else 0
    return min(v2(c1) + h1, v2(c0))

def lower_hull_principal(pts):
    """pts = [(k, u_k)] with u possibly inf. Return principal (neg-slope) vertex chain."""
    pts = [(k, u) for k, u in pts if u != inf]
    hull = []
    for pt in pts:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            if (y2 - y1)*(pt[0] - x2) >= (pt[1] - y2)*(x2 - x1): hull.pop()
            else: break
        hull.append(pt)
    out = [hull[0]]
    for a, b in zip(hull, hull[1:]):
        if (b[1]-a[1]) < 0: out.append(b)
        else: break
    return out

def s_of(beta, wts, e=1):
    return sum(max(0, -(-(beta - wt)//e)) if beta > wt else 0 for wt in wts)

def dimG(beta, wts, e=1):
    return sum(1 for wt in wts if wt % e == beta % e and wt <= beta)

def slot_count_bruteforce(N, beta_exact, h1):
    """#{a=(c0,c1) mod 2^N : w(a) == beta_exact}; also attained graded values at beta."""
    cnt = 0; vals = {}
    for c0 in range(2**N):
        for c1 in range(2**N):
            w = w_lin([c0, c1], h1)
            if w == beta_exact:
                cnt += 1
                # graded class witness: (c0, c1) truncated to the beta-level in-form:
                # for these types the in-form is (c0 / 2^beta mod 2) if beta < h1 contributes only c0;
                # generally record (c0 >> beta & 1, c1 >> (beta - h1) & 1 if beta >= h1 else None)
                key = (c0 >> beta_exact & 1 if v2(c0) == beta_exact else 0,
                       (c1 >> (beta_exact - h1) & 1) if beta_exact >= h1 and v2(c1) + h1 == beta_exact else 0)
                vals[key] = vals.get(key, 0) + 1
    return cnt, vals

def report_instance(name, f, phi2, h1, n):
    Vhat = 2*h1
    wts = [0, h1]; d = 2
    dev = development(f, phi2)
    ell = len(dev) - 1
    ws = [w_lin(a, h1) for a in dev]
    us = [ws[k] + k*Vhat for k in range(len(dev))]
    print(f"--- instance {name}: f coeffs(low->high) = {f}, phi2 = {phi2}, (h1={h1}, Vhat={Vhat})")
    print(f"    development a_k = {dev}")
    print(f"    w(a_k) = {ws},  u_k = {us},  ell = {ell}")
    chain = lower_hull_principal(list(enumerate(us)))
    print(f"    principal chain vertices: {chain}")
    ks = chain[-1][0]
    online = []
    for (k1, u1), (k2, u2) in zip(chain, chain[1:]):
        # e_S from slope in lowest terms
        from math import gcd
        hS = u1 - u2; eS = k2 - k1; g = gcd(hS, eS); hS //= g; eS //= g
        k = k1
        while k <= k2:
            u_line = u1 - (k - k1)*(u1-u2)//(k2-k1) if (k - k1)*(u1-u2) % (k2-k1) == 0 else None
            if u_line is not None and (k - k1) % eS == 0:
                online.append((k, u_line - k*Vhat))
            k += 1
    online = sorted(set(online))
    print(f"    on-line slots (k, beta_k): {online},  right end k_s = {ks}")
    for k, beta in online:
        dg = dimG(beta, wts)
        status = "FULL" if dg == d else ("PARTIAL" if dg > 0 else "EMPTY-SLOT")
        role = "RIGHT-END" if k == ks else "non-end"
        classmax = max(wt for wt in wts if wt % 1 == beta % 1)
        print(f"      slot k={k}: beta={beta}, dim G_beta = {dg} vs d={d} -> {status}"
              f"  [{role}; class-max wt = {classmax}; clearance beta-classmax = {beta-classmax}]")
    return dev, ws, us, chain, online, ks

# ---------- instance A: n=4, h1=1 ----------
phi2A = [4, 2, 1]              # x^2 + 2x + 4
gA    = [12, 6, 1]             # x^2 + 6x + 12   (delta = 4x + 8, w = 3 = Vhat+1)
hA    = [3, -4, 1]             # (x-1)(x-3)      (unit roots)
fA    = polymul(gA, hA)
devA, wsA, usA, chainA, onlineA, ksA = report_instance("A (n=4 free right end)", fA, phi2A, 1, 4)
assert usA[0] == 3 and usA[1] == 2, "instance A polygon heights changed"
assert chainA == [(0, 3), (1, 2)], f"instance A principal chain {chainA}"
assert dict(onlineA)[1] == 0 and dimG(0, [0, 1]) == 1, "A: right-end beta=0 must be PARTIAL"
assert dict(onlineA)[0] == 3 and dimG(3, [0, 1]) == 2, "A: slot 0 must be FULL"

# window census per slot, N = 4 (DET: 3 <= N-1)
N = 4
for beta, slotk in [(3, 0), (0, 1)]:
    cnt, vals = slot_count_bruteforce(N, beta, 1)
    led = p**(2*N - s_of(beta, [0, 1])) - p**(2*N - s_of(beta+1, [0, 1]))
    dg = dimG(beta, [0, 1])
    image_law = (p**dg - 1) * p**(2*N - s_of(beta, [0, 1]) - dg)
    full_display = (p**2 - 1) * p**(2*N - s_of(beta, [0, 1]) - 2)
    nonzero_classes = {k for k in vals if k != (0, 0)}
    print(f"    [A census] slot {slotk} (beta={beta}): brute {cnt} | LED {led} | image-law {image_law}"
          f" | naive-FULL display {full_display} | attained nonzero classes {len(nonzero_classes)}"
          f" (FULL would need {p**2 - 1}) | fibers uniform: {len(set(vals.values())) == 1}")
    assert cnt == led == image_law, f"A slot {slotk}: image law mismatch"
    if beta == 0:
        assert cnt != full_display, "A right-end: naive FULL display should FAIL"
        assert len(nonzero_classes) == p**dimG(beta, [0,1]) - 1

# order-1 realization sanity: R_1(f) on the slope -1 face ~ psi1 = y^2+y+1, ord = 1
c0, c1, c2 = fA[0], fA[1], fA[2]
assert v2(c0) == 2 and v2(c1) >= 1 and v2(c2) == 0
r = [ (c0 // 4) % 2, (c1 // 2) % 2, c2 % 2 ]
print(f"    [A order-1] face residual coeffs (y^0,y^1,y^2) = {r} -> psi1 = y^2+y+1: {r == [1, 1, 1]}")
assert r == [1, 1, 1]

# ---------- instance B: n=3, h1=2 (K7's shape) ----------
phi2B = [16, 4, 1]             # x^2 + 4x + 16
gB    = [80, 12, 1]            # x^2 + 12x + 80  (delta = 8x + 64, w = 5 = Vhat+1)
fB    = polymul(gB, [-2, 1])   # g * (x - 2)
devB, wsB, usB, chainB, onlineB, ksB = report_instance("B (n=3 monic top; K7 shape)", fB, phi2B, 2, 3)
assert chainB == [(0, 6), (1, 5)], f"instance B chain {chainB} != K7's (0,6)->(1,5)"
assert dict(onlineB)[1] == 1 and dimG(1, [0, 2]) == 1, "B: top-slot beta=1 must be PARTIAL"
# LED-top anchor cap: a_1 is monic of degree m' = 1: w(a_1) <= w* = wt(j*) = w(x) = 2
assert wsB[1] <= 2, "LED-top anchor cap violated?!"
print(f"    [B] top slot beta = {wsB[1]} < w* = 2 (anchor): LED-top(ii) regime; K7 shape REALIZED at n=3")

# ---------- instance C: n=4 m|n, k_s = ell ----------
gC  = [12, 6, 1]               # x^2 + 6x + 12
gC2 = [20, 2, 1]               # x^2 + 2x + 20  (delta~ = 0x + 16, w = 4)
fC  = polymul(gC, gC2)
devC, wsC, usC, chainC, onlineC, ksC = report_instance("C (n=4 m|n full chain)", fC, phi2A, 1, 4)
assert chainC == [(0, 7), (1, 5), (2, 4)], f"instance C chain {chainC}"
bC = dict(onlineC)
assert bC[2] == 0 and dimG(0, [0, 1]) == 1, "C: ell-slot beta=0 partial-by-letter"
assert bC[1] == 3 and bC[0] == 7, "C: K_D slots"
# NON-END margin tightness: beta_1 = beta_2 + (e_S*Vhat + h_S) = 0 + 2 + 1 = 3
assert bC[1] == bC[2] + 2 + 1

# CEN-W monic-top display vs truth at N = 8 (DET: 7 <= N-1), per-slot independence
N = 8
truth = 1
for beta, slotk in [(7, 0), (3, 1)]:
    cnt, vals = slot_count_bruteforce(N, beta, 1)
    led = p**(2*N - s_of(beta, [0, 1])) - p**(2*N - s_of(beta+1, [0, 1]))
    assert cnt == led, f"C slot {slotk} brute {cnt} != LED {led}"
    truth *= cnt
Eprime = sum((2*N - s_of(b, [0, 1])) for b in (7, 3)) - 2*2
display = p**Eprime * (p**2 - 1) * (p**2 - 1)   # q^E' * prod_S M_{(1,1)}(q^2), M_{(1,1)}(Q) = Q-1
print(f"    [C census] truth (product of slot counts) = {truth} | CEN-W monic-top display = {display}"
      f" -> {'EXACT' if truth == display else 'MISMATCH'} (while displayed-(ADM) FAILS at slot ell)")
assert truth == display, "C: monic-top display expected EXACT (over-fencing witness)"

# separability of all three f (disc != 0 via square-free gcd over Q): cheap check
def derivative(f): return [i*c for i, c in enumerate(f)][1:]
def poly_gcd_deg(f, g):
    from fractions import Fraction
    f = [Fraction(c) for c in f]; g = [Fraction(c) for c in g]
    while any(c != 0 for c in g):
        while f and f[-1] == 0: f.pop()
        while g and g[-1] == 0: g.pop()
        if len(f) < len(g): f, g = g, f; continue
        lead = f[-1]/g[-1]
        for j in range(len(g)): f[len(f)-len(g)+j] -= lead*g[j]
        f.pop()
        f, g = g, f
    while f and f[-1] == 0: f.pop()
    return len(f) - 1
for nm, f in [("A", fA), ("B", fB), ("C", fC)]:
    assert poly_gcd_deg(f, derivative(f)) == 0, f"{nm} not separable"
print("separability: A, B, C all square-free over Q  OK")
print("ALL ASSERTIONS PASS")
