#!/usr/bin/env python3
"""ilnres_pe1_ext.py — ILNRES-PE1 hostile-pass independent leg (NEW file,
verification only; commits nothing, edits nothing).

Hand-re-derives DS-CASE instances of ILNRES_2026-08-08.md S6 step (3) with a
FRESH polynomial layer: plain Python-int coefficient lists, own divmod, own
Phi-adic development — no reuse of grb_order2_check's padd/pmul/pdivmod/dev.
Consumed from committed code: ONLY the tower objects (Phi_j coefficient lists,
integers e/h/g/d0) and the integer split data C.split (S2 layer) — i.e. the
shared DEFINITIONS, not the arithmetic under test.

Instances (Zp towers so coefficients are literal integers):
  A. X3-FLAT-H2/Zp3, rung 2, one Case-II pair (e1 = 1 substitution leg).
  B. X5-TCTRL-d1/Zp3, rung 3, one off-DCX Case-II pair (DS-CASE re-derived)
     AND one DCX3-flagged pair (Q1 != 0 verified by hand; outer locus checked).
Checks per instance: substitution identity Phi_{r-1}^{e} = Phi_r - Chat as an
exact polynomial identity; dev support in {0,1} rel slots; E1c/E0c construction
== dev digits; degree chain; E1 != 0 => CII_r; the algebraic identity
BP_r = E0c + E1c*Phi_r re-verified directly.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import engine_ext; engine_ext.install()
from iterlaw4_probe import Tower4, Composite4

FAIL = []
def chk(name, ok, detail=""):
    print(f"  [{'ok' if ok else 'FAIL'}] {name} {detail}")
    if not ok: FAIL.append((name, detail))

# ---------- fresh integer-polynomial layer (independent of grb) ----------
def znorm(A):
    A = list(A)
    while A and A[-1] == 0: A.pop()
    return A
def zadd(A, B):
    n = max(len(A), len(B))
    return znorm([(A[i] if i < len(A) else 0) + (B[i] if i < len(B) else 0)
                  for i in range(n)])
def zsub(A, B): return zadd(A, [-b for b in B])
def zmul(A, B):
    if not A or not B: return []
    out = [0]*(len(A)+len(B)-1)
    for i, a in enumerate(A):
        for j, b in enumerate(B):
            out[i+j] += a*b
    return znorm(out)
def zpow(A, k):
    out = [1]
    for _ in range(k): out = zmul(out, A)
    return out
def zdivmod(A, B):          # B monic (integer long division, exact)
    A = list(A); dB = len(B)-1
    assert B[-1] == 1, "divisor not monic"
    Q = {}
    while len(znorm(A))-1 >= dB and znorm(A):
        A = znorm(A); d = len(A)-1; c = A[-1]; Q[d-dB] = c
        for j, b in enumerate(B):
            A[d-dB+j] -= c*b
    Qd = max(Q) if Q else -1
    return znorm([Q.get(i, 0) for i in range(Qd+1)]), znorm(A)
def zdev(A, Phi):
    out = []; A = znorm(A)
    while A:
        q, r = zdivmod(A, Phi)
        out.append(r); A = q
    return out

def load(name, kind, p, d0, rs, tag):
    T4 = Tower4(kind, p, d0, rs[0], rs[1], rs[2], rs[3], tag)
    C = Composite4(T4, with_shadow=False)
    T3 = T4.T3; T = T3.T
    e = [T.e0, T.e1, T3.e2, T4.e3]; g = [T.g0, T.g1, T3.g2, T4.g3]
    Phi = [znorm(T.Phi0), znorm(T.Phi1), znorm(T.Phi2), znorm(T3.Phi3)]
    return C, e, g, Phi, p

def splits(C, gam):
    s = C.split(gam)
    return {4: s[0], 3: s[1], 2: s[2], 1: s[3]}, s[7]   # s_j dict, u

def cii_chain(e, g, Ta, Tb):
    T = {j: Ta[j] + Tb[j] for j in (1, 2, 3)}
    d = {j: T[j] // e[j-1] for j in (1, 2, 3)}
    cii = {1: (g[0] == 1 and d[1] == 1)}
    for r in (2, 3):
        cii[r] = (g[r-1] == 1) and (d[r] == 1 or
                                    (cii[r-1] and T[r] == e[r-1]-1))
    return cii, T, d

def rederive(label, C, e, g, Phi, p, ga, gb, rung, expect_dcx=False):
    print(f"-- {label}: pair=({ga},{gb}) rung={rung}")
    sa, ua = splits(C, ga); sb, ub = splits(C, gb)
    cii, T, dlt = cii_chain(e, g, sa, sb)
    U = ua + ub
    # BP_r rebuilt from raw splits (monomial product, own arithmetic)
    BP = zmul([p**U], zpow(Phi[0], T[1]))
    for j in range(2, rung+1):
        BP = zmul(BP, zpow(Phi[j-1], T[j]))
    # substitution identity at level r-1 (g=1): Phi_{r-1}^{e} = Phi_r - Chat
    r = rung
    Chat = zsub(Phi[r], zpow(Phi[r-1], e[r-1]))          # Chat = Phi_r - Phi^e
    chk("WELLDEF deg Chat < deg Phi_{r-1}"
        if g[r-1] == 1 else "g>=2 (no Chat needed)",
        g[r-1] != 1 or len(Chat)-1 < len(Phi[r-1])-1,
        f"(deg Chat={len(Chat)-1}, deg Phi_(r-1)={len(Phi[r-1])-1})")
    chk("Phi_r monic", Phi[r][-1] == 1)
    # IH digits: dev of inner product BP_{r-1} at Phi_{r-1}
    BPin = zmul([p**U], zpow(Phi[0], T[1]))
    for j in range(2, r):
        BPin = zmul(BPin, zpow(Phi[j-1], T[j]))
    ddIH = zdev(BPin, Phi[r-1])
    chk(f"IH support in rel slots {{0,1}} (r-1={r-1})",
        all(not znorm(c) for c in ddIH[2:]), f"len={len(ddIH)}")
    # the S6 construction
    eg = e[r-1]*g[r-1]
    E1c, E0c = [], []
    hi_fired = False
    for j, c in enumerate(ddIH):
        if not znorm(c): continue
        a = T[r] + j
        if a >= eg:
            assert g[r-1] == 1, "overflow at g>=2 (would refute S4.4)"
            hi_fired = True
            E1c = zadd(E1c, zmul(c, zpow(Phi[r-1], a-eg)))
        else:
            E0c = zadd(E0c, zmul(c, zpow(Phi[r-1], a)))
    if hi_fired:
        # Chat = Phi_r - Phi^e  =>  E0c -= E1c * (-Chat)?  Note S6 uses
        # Phi^e = Phi_r - Chat_S6 with Chat_S6 = Phi_r - Phi^e = Chat. So
        # E0c = lo - E1c*Chat ... with Phi^e = Phi_r - Chat:
        E0c = zsub(E0c, zmul(E1c, Chat))
    # identity BP_r = E0c + E1c*Phi_r (hand identity, exact)
    chk("identity BP_r == E0c + E1c*Phi_r",
        znorm(zsub(BP, zadd(E0c, zmul(E1c, Phi[r])))) == [])
    # direct development (own dev), support + equality
    dd = zdev(BP, Phi[r])
    chk("direct dev support in rel slots {0,1}",
        all(not znorm(c) for c in dd[2:]), f"len={len(dd)}")
    E0 = dd[0] if len(dd) > 0 else []
    E1 = dd[1] if len(dd) > 1 else []
    dPhir = len(Phi[r]) - 1
    if not expect_dcx:
        chk("deg E1c < deg Phi_r", (len(E1c)-1) < dPhir or not E1c)
        chk("deg E0c < deg Phi_r", (len(E0c)-1) < dPhir or not E0c)
        chk("construction == dev (E0)", znorm(zsub(E0c, E0)) == [])
        chk("construction == dev (E1)", znorm(zsub(E1c, E1)) == [])
        chk("E1 != 0 => CII_r", (not znorm(E1)) or cii[r],
            f"(E1 nonzero: {bool(znorm(E1))}, CII_{r}: {cii[r]})")
        chk("Case II predicate consistency: hi fired => CII_r",
            (not hi_fired) or cii[r])
    else:
        # DCX leg: verify Q1 != 0 by hand and the outer locus
        E1IH = ddIH[1] if len(ddIH) > 1 else []
        chk("E1IH != 0 (DCX prerequisite)", bool(znorm(E1IH)))
        Q1, R1 = zdivmod(zmul(E1IH, Chat), Phi[r-1])
        chk("Q1 != 0 (second-round overflow live)", bool(znorm(Q1)))
        track = (T[r] == 2*e[r-1]-2 and dlt[r] == 1) or e[r-1] == 1
        chk("track-extreme", track, f"(T_{r}={T[r]}, e={e[r-1]})")
        outer = (g[r-1] == 1 and sa[r] == e[r-1]-1 and sb[r] == e[r-1]-1
                 and cii[r-1])
        chk("outer locus (OB-OUT by hand)", outer,
            f"(s={sa[r]},{sb[r]}, e-1={e[r-1]-1}, CII_{r-1}={cii[r-1]})")
        # measured clause: support still within {0,1} on DCX
        chk("[measured] on-DCX support still in {0,1}",
            all(not znorm(c) for c in dd[2:]))
    print(f"   T={T} delta={dlt} cii={cii} degE0={len(E0)-1} degE1={len(E1)-1}"
          f" hi_fired={hi_fired}")

# ---------------- instance A: X3-FLAT-H2/Zp3, rung 2 ----------------
C, e, g, Phi, p = load("X3-FLAT-H2", "Zp", 3, 2,
                       [(3,1,1),(1,2,1),(2,1,1),(1,1,1)], "PE1-X3")
G0 = C.Gamma0
# hunt one Case-II (hi-firing) off-DCX pair and re-derive
found = None
for ga in range(G0, G0+12):
    for gb in range(G0, G0+12):
        sa, ua = splits(C, ga); sb, ub = splits(C, gb)
        cii, T, dlt = cii_chain(e, g, sa, sb)
        # rung 2: e1=1,g1=1 -> eg=1; hi fires iff T2+top>=1; off DCX2 needed:
        # DCX2 flag needs E1IH!=0 & track & Q1!=0 — pick a NON-track pair
        if T[2] >= 1 and not ((T[2] == 2*e[1]-2 and dlt[2] == 1) or e[1] == 1):
            found = (ga, gb); break
    if found: break
# e1=1 means ALWAYS track at rung 2 (e==1 branch): every hi-firing pair is
# track-extreme; off-DCX2 then requires Q1==0. Take the first pair and let the
# checks adjudicate (the committed census says dcx2=16 of 144, so most pairs
# are off).
ga, gb = G0, G0
import itertools
picked = None
for ga, gb in itertools.product(range(G0, G0+12), repeat=2):
    sa, ua = splits(C, ga); sb, ub = splits(C, gb)
    cii, T, dlt = cii_chain(e, g, sa, sb)
    U = ua + ub
    BPin = zmul([p**U], zpow(Phi[0], T[1]))
    ddIH = zdev(BPin, Phi[1])
    E1IH = ddIH[1] if len(ddIH) > 1 else []
    Chat1 = zsub(Phi[2], zpow(Phi[1], e[1]))
    q1 = zdivmod(zmul(E1IH, Chat1), Phi[1])[0] if znorm(E1IH) else []
    dcx2 = bool(znorm(E1IH)) and bool(znorm(q1)) and \
           ((T[2] == 2*e[1]-2 and dlt[2] == 1) or e[1] == 1)
    if not dcx2 and znorm(E1IH):     # hi fires via the E1IH slot (e1 = 1)
        picked = (ga, gb)
        break
rederive("A: X3-FLAT-H2/Zp3 rung 2 (Case II, off DCX2)",
         C, e, g, Phi, p, *picked, 2)

# ---------------- instance B: X5-TCTRL-d1/Zp3, rung 3 ----------------
C, e, g, Phi, p = load("X5-TCTRL-d1", "Zp", 3, 1,
                       [(2,1,1),(2,1,1),(1,1,1),(2,1,1)], "PE1-X5")
G0 = C.Gamma0
off_pick, dcx_pick = None, None
for ga, gb in itertools.product(range(G0, G0+16), repeat=2):
    sa, ua = splits(C, ga); sb, ub = splits(C, gb)
    cii, T, dlt = cii_chain(e, g, sa, sb)
    U = ua + ub
    # rung-3 DCX3 flag (constructive, rebuilt by hand)
    BPin = zmul([p**U], zpow(Phi[0], T[1]))
    BPin = zmul(BPin, zpow(Phi[1], T[2]))
    ddIH = zdev(BPin, Phi[2])
    E1IH = ddIH[1] if len(ddIH) > 1 else []
    Chat2 = zsub(Phi[3], zpow(Phi[2], e[2]))
    q1 = zdivmod(zmul(E1IH, Chat2), Phi[2])[0] if znorm(E1IH) else []
    track = (T[3] == 2*e[2]-2 and dlt[3] == 1) or e[2] == 1
    dcx3 = bool(znorm(E1IH)) and track and bool(znorm(q1))
    # also require inner off DCX2 for a clean rung-3 instance
    BP1 = zmul([p**U], zpow(Phi[0], T[1]))
    dd1 = zdev(BP1, Phi[1])
    E1IH1 = dd1[1] if len(dd1) > 1 else []
    Chat1 = zsub(Phi[2], zpow(Phi[1], e[1]))
    q1a = zdivmod(zmul(E1IH1, Chat1), Phi[1])[0] if znorm(E1IH1) else []
    dcx2 = bool(znorm(E1IH1)) and bool(znorm(q1a)) and \
           ((T[2] == 2*e[1]-2 and dlt[2] == 1) or e[1] == 1)
    if dcx2: continue
    if dcx3 and dcx_pick is None: dcx_pick = (ga, gb)
    if (not dcx3) and znorm(E1IH) and off_pick is None:
        off_pick = (ga, gb)
    if off_pick and dcx_pick: break
rederive("B1: X5-TCTRL-d1/Zp3 rung 3 (Case II, off DCX3, E1IH!=0)",
         C, e, g, Phi, p, *off_pick, 3)
rederive("B2: X5-TCTRL-d1/Zp3 rung 3 (DCX3-flagged pair — NR-3 witness)",
         C, e, g, Phi, p, *dcx_pick, 3, expect_dcx=True)

print()
if FAIL:
    print(f"PE1-EXT: {len(FAIL)} FAILURES"); sys.exit(1)
print("PE1-EXT: ALL HAND RE-DERIVATIONS PASS")
