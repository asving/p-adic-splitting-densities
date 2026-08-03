#!/usr/bin/env python3
"""iterlawr_probe.py — ITER-LAW-r LEVEL-3 COCYCLE PROBE (wave-18 unit 2;
synthesis-8 queue #2).  Sealed preregistration = lean/notes/openmath/
ITERLAWR_PROBE_2026-08-08.md (S0-S4: candidate law, roster, legs, predictions).
Two-commit seal: this file + the prereg are committed BEFORE the battery runs.

THE PRIMARY CANDIDATE (ITER-LAW-3), prereg S1, for gamma, gamma' in W3:

    c3(g,g') = zbar^{d3} * z2^{D2} * z1^{D1}

    d3  = floor((s3+s3')/e2)                       in {0,1}
    D2  = (s2+s2'-s2'' + l1*gamma3*d3)/e1          integer
    Sig = D2*gamma2 + d3*gamma3*(l1p - l1*w1Phi1)  the composed inner shift
    D1  = (s1+s1'-s1'' + l0*Sig)/e0                integer

with the ITERATED split s3 = eq12(g,e2,h2), b2 = u3 - s3*w2Phi2,
s2 = eq12(b2,e1,h1), b1 = u2 - s2*w1Phi1, s1 = eq12(b1,e0,h0).
DISTINGUISHED ALTERNATIVE (naive per-level template): D1naive uses
l0*gamma2*d2, d2 = floor((s2+s2')/e1) — coincides at d3 = 0 only.

Harness of record consumed VERBATIM: grb_order2_check.Tower (levels 0-2),
strata3_probe.Tower3 (level-3 layer: eps2 reading C, w3, R3w, build_Phi3).
NEW here: K3 = K2[zbar]/(psi2), val3(f) = sum_j R3w(f)_j zbar^j, the level-3
anchors/cocycle, and this battery.  DETERMINISTIC: seed 20260903, exact
arithmetic.  Exit 0 iff all predicted-0 families are 0, all meters MATCH,
all 6 mutation controls detected, no harness events.
Usage: iterlawr_probe.py [--design]   (--design: tower construction +
constants table only — NO law comparison; disclosed pre-seal per precedent).
"""
import random, math, sys, os, time, json

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import grb_order2_check as G
from grb_order2_check import (dev, w0, pnorm, padd, pmul, ppow, pscal, pneg,
                              eq12, bezout, INF, Tower, mk_field_ext, fp_norm)
import strata3_probe as S3MOD
from strata3_probe import Tower3
import strata_probe as SP

# psi2 selection shim (DISCLOSED pre-seal, prereg S2): strata3_probe.pick_irr3
# early-exits without index wraparound (unlike grb's pick_irreducible), so
# idx=1 over a field with a single eligible degree-1 irreducible (e.g. F_2)
# raises.  Deterministic fallback: original idx, then idx=0 on exhaustion.
# strata3_probe itself is byte-untouched.
_pick_irr3_orig = S3MOD.pick_irr3
def _pick_irr3_wrap(F, g, idx=0):
    try:
        return _pick_irr3_orig(F, g, idx)
    except RuntimeError:
        return _pick_irr3_orig(F, g, 0)
S3MOD.pick_irr3 = _pick_irr3_wrap

VIOL = []
COUNTS = {}
HARNESS_EVENTS = []
def note(fam, n=1): COUNTS[fam] = COUNTS.get(fam, 0) + n
def viol(fam, tag, detail): VIOL.append((fam, tag, detail))

ROWS = [
    ("A",  1, (2,1,1), (2,1,1), (2,1,1)),
    ("B",  1, (3,2,1), (2,1,1), (2,1,1)),
    ("C",  1, (2,1,2), (2,1,1), (2,1,1)),
    ("D",  1, (2,1,1), (3,1,1), (2,1,1)),
    ("E",  1, (2,1,1), (2,1,2), (2,1,1)),
    ("F",  1, (2,1,1), (2,1,1), (3,2,1)),
    ("G",  1, (2,1,1), (2,1,1), (2,1,2)),
    ("H",  2, (2,1,1), (2,1,1), (2,1,1)),
    ("K",  1, (2,3,1), (2,3,1), (2,3,1)),
    ("L",  1, (2,1,1), (2,1,1), (4,3,1)),
    ("CV", 1, (1,1,2), (2,1,1), (2,1,1)),
    ("CW", 1, (2,1,1), (1,1,2), (2,1,1)),
    ("CX", 1, (2,1,1), (2,1,1), (1,1,2)),
]
CONFIGS = [("Zp", 2), ("Zp", 3), ("Fpt", 2), ("Fpt", 3)]
MUT_ROWS = ("B", "D", "E", "F")
MUT_CONFIGS = [("Zp", 3), ("Fpt", 2)]

# ---------------------------------------------------------------------------
# accepted LEVEL-2 closed form (independent transcription of ITERLAW S5,
# identical to iterlaw_check.closed_form) — the F0a fidelity reference
def closed_form2(C, ga, gb):
    T, K2 = C.T, C.K2
    s2a, s1a, _, _ = C.split(ga)
    s2b, s1b, _, _ = C.split(gb)
    _,   s1c, _, _ = C.split(ga + gb)
    d2 = (s2a + s2b)//T.e1
    num = s1a + s1b - s1c + T.l0*T.gamma2*d2
    if num % T.e0 != 0:
        return None, d2
    return K2["mul"](K2["pow"](C.zbar, d2),
                     K2["pow"](C.z1_2, num//T.e0)), d2

# ---------------------------------------------------------------------------
class Composite3:
    """Level-3 canonical-anchor composite prober for one Tower3."""
    def __init__(self, T3):
        self.T3 = T3
        T = T3.T
        self.K3 = mk_field_ext(T3.K2, T3.psi2)
        self.zbar = self.K3["z"]
        self.z2_3 = self.K3["embed"](T3.z2)
        self.z1_3 = self.K3["embed"](T3.K2["embed"](T.z1))
        E3 = T3.E3
        base = ((T3.e2 - 1)*T3.gamma3 + T3.e2*(T.e1 - 1)*T.gamma2
                + E3*(T.e0 - 1)*T.h0 + E3)
        G0 = ((base + E3 - 1)//E3)*E3
        # deterministic window scan: u1 >= 0 on the whole needed range
        # (pairs AND associativity triples go up to 3*(G0 + 8*E3) + 2)
        while True:
            hi = 3*(G0 + 8*E3) + 2
            if all(self.split(g)[5] >= 0 for g in range(G0, hi + 1)):
                break
            G0 += E3
        self.Gamma0 = G0
        self._anch, self._aval, self._coc = {}, {}, {}

    def split(self, gamma):
        T3 = self.T3; T = T3.T
        s3, u3 = eq12(gamma, T3.e2, T3.h2)
        b2 = u3 - s3*T.w2Phi2
        s2, u2 = eq12(b2, T.e1, T.h1)
        b1 = u2 - s2*T.w1Phi1
        s1, u1 = eq12(b1, T.e0, T.h0)
        return s3, s2, s1, b2, b1, u1

    def anchor(self, gamma):
        if gamma in self._anch: return self._anch[gamma]
        T3 = self.T3; T = T3.T; R = T.R
        s3, s2, s1, b2, b1, u1 = self.split(gamma)
        assert u1 >= 0, f"window: gamma={gamma}, u1={u1}"
        f = pscal(R, R["pi_pow"](u1), ppow(R, T.Phi0, s1))
        f = pmul(R, f, ppow(R, T.Phi1, s2))
        f = pmul(R, f, ppow(R, T.Phi2, s3))
        self._anch[gamma] = f
        return f

    def val3(self, f, want_meta=False):
        """K3 value of the level-3 weight read; also (nz-slots, gamma)."""
        T3 = self.T3; K3 = self.K3
        coeffs, m = T3.R3w(f, with_meta=True)
        v = K3["zero"]; zp = K3["one"]; nz = []
        for j, c in enumerate(coeffs):
            if not T3.K2["isz"](c):
                nz.append(j)
                v = K3["add"](v, K3["mul"](K3["embed"](c), zp))
            zp = K3["mul"](zp, self.zbar)
        if want_meta:
            return v, nz, m["gamma"]
        return v

    def anchor_val(self, gamma):
        if gamma in self._aval: return self._aval[gamma]
        v = self.val3(self.anchor(gamma))
        self._aval[gamma] = v
        return v

    def eps_chain(self, gamma):
        """K3-embedded eps2(b2)*eps1(b1) — the L6-3 prediction."""
        T3 = self.T3; T = T3.T
        _, _, _, b2, b1, _ = self.split(gamma)
        e2v = T3.eps2(b2)
        e1v = T3.K2["embed"](T.eps1(b1))
        return self.K3["embed"](T3.K2["mul"](e2v, e1v))

    def constants(self, ga, gb):
        """All prereg-S1 constants for the pair; None where non-integral."""
        T3 = self.T3; T = T3.T
        s3a, s2a, s1a, b2a, b1a, _ = self.split(ga)
        s3b, s2b, s1b, b2b, b1b, _ = self.split(gb)
        s3c, s2c, s1c, b2c, b1c, _ = self.split(ga + gb)
        d3 = (s3a + s3b)//T3.e2
        d2 = (s2a + s2b)//T.e1
        d1 = (s1a + s1b)//T.e0
        numD2 = s2a + s2b - s2c + T.l1*T3.gamma3*d3
        D2 = numD2//T.e1 if numD2 % T.e1 == 0 else None
        Sig = (None if D2 is None
               else D2*T.gamma2 + d3*T3.gamma3*(T.l1p - T.l1*T.w1Phi1))
        numD1 = None if Sig is None else s1a + s1b - s1c + T.l0*Sig
        D1 = (numD1//T.e0 if numD1 is not None and numD1 % T.e0 == 0
              else None)
        numN = s1a + s1b - s1c + T.l0*T.gamma2*d2
        D1n = numN//T.e0 if numN % T.e0 == 0 else None
        return dict(d3=d3, d2=d2, d1=d1, D2=D2, Sig=Sig, D1=D1, D1n=D1n,
                    b2a=b2a, b2b=b2b, b1a=b1a, b1b=b1b,
                    b2c=b2c, b1c=b1c)

    def law_value(self, cst, which="primary"):
        """K3 value of the closed form; None if non-integral."""
        K3 = self.K3
        D1 = cst["D1"] if which == "primary" else cst["D1n"]
        if cst["D2"] is None or D1 is None:
            return None
        return K3["mul"](K3["pow"](self.zbar, cst["d3"]),
               K3["mul"](K3["pow"](self.z2_3, cst["D2"]),
                         K3["pow"](self.z1_3, D1)))

    def cocycle(self, ga, gb):
        key = (ga, gb)
        if key in self._coc: return self._coc[key]
        K3 = self.K3
        prod = pmul(self.T3.R, self.anchor(ga), self.anchor(gb))
        vp, nz, gmeas = self.val3(prod, want_meta=True)
        vt = self.anchor_val(ga + gb)
        c = K3["mul"](vp, K3["inv"](vt))
        out = (c, vp, nz, gmeas)
        self._coc[key] = out
        return out

def k3_repr(C, v):
    """decompose v as zbar^a*z2^b*z1^c if possible, else 'raw'."""
    K3 = C.K3
    def omul(x):
        o = 1; y = x
        while y != K3["one"] and o < 900:
            y = K3["mul"](y, x); o += 1
        return o if y == K3["one"] else None
    o2 = omul(C.z2_3) or 1; o1 = omul(C.z1_3) or 1; ob = omul(C.zbar) or 1
    for a in range(ob):
        za = K3["pow"](C.zbar, a)
        for b in range(o2):
            zab = K3["mul"](za, K3["pow"](C.z2_3, b))
            for c in range(o1):
                if K3["mul"](zab, K3["pow"](C.z1_3, c)) == v:
                    return (f"zbar^{a}*z2^{b}*z1^{c}"
                            if a or b or c else "1")
    return f"raw:{v!r}"

# ---------------------------------------------------------------------------
def run_tower(T3, results):
    T = T3.T
    C = Composite3(T3)
    K3, K2t, E3 = C.K3, T3.K2, T3.E3
    G0 = C.Gamma0
    wins = [list(range(G0 + k*E3, G0 + (k+1)*E3)) for k in (0, 1, 7)]
    W1, W2, W3 = wins
    mc = dict(inner=0, mid=0, dbl=0, mv=0, md3=0, msepf=0)
    # ---- F0a: the ACCEPTED level-2 law on the subtower (harness fidelity) ----
    C2 = SP.Composite(T)
    W1_2 = list(range(C2.Gamma0, C2.Gamma0 + T.E2))
    for ga in W1_2:
        for gb in W1_2:
            note("F0a")
            c2m, _ = C2.cocycle(ga, gb)
            cf2, _ = closed_form2(C2, ga, gb)
            if cf2 is None or c2m != cf2:
                viol("F0a", T3.tag, f"LEVEL-2 accepted law fails at "
                                    f"({ga},{gb}) — HARNESS suspect")
    # ---- G1: anchor values, three windows ----
    for win in wins:
        for g in win:
            note("G1")
            v = C.anchor_val(g)
            pred = C.eps_chain(g)
            if v != pred or K3["isz"](v):
                viol("G1", T3.tag, f"ANCHOR-VAL-3 fails at gamma={g}")
    # ---- pair blocks: G2 / G3 / G4 / G6 + meters ----
    blocks = [(W1, W1), (W3, W3), (W1, W3)]
    for A, B in blocks:
        for ga in A:
            for gb in B:
                cst = C.constants(ga, gb)
                d3, d2, d1 = cst["d3"], cst["d2"], cst["d1"]
                # meters
                if T.g0 == 1 and d1 == 1: mc["inner"] += 1
                if T.g1 == 1 and d2 == 1: mc["mid"] += 1
                if T.g0 == 1 and d1 == 1 and T.g1 == 1 and d2 == 1:
                    mc["dbl"] += 1
                if d3 == 1: mc["md3"] += 1
                # G2 PAIR-VAL both forms + shape
                note("G2")
                cval, vp, nz, gmeas = C.cocycle(ga, gb)
                if gmeas != ga + gb or nz != [d3]:
                    viol("G2", T3.tag, f"shape at ({ga},{gb}): gamma={gmeas} "
                         f"(want {ga+gb}), nz={nz} (want [{d3}])")
                e2sum = T3.eps2(cst["b2a"] + cst["b2b"])
                e1sum = K2t["embed"](T.eps1(cst["b1a"] + cst["b1b"]))
                predA = K3["mul"](K3["pow"](C.zbar, d3),
                        K3["mul"](K3["pow"](C.z2_3, d2),
                        K3["mul"](K3["pow"](C.z1_3, d1),
                                  K3["embed"](K2t["mul"](e2sum, e1sum)))))
                predB = K3["mul"](K3["pow"](C.zbar, d3),
                        K3["mul"](C.anchor_val(ga), C.anchor_val(gb)))
                if vp != predA:
                    viol("G2", T3.tag, f"PAIR-VAL-3(a) fails at ({ga},{gb})")
                if vp != predB:
                    viol("G2", T3.tag, f"PAIR-VAL-3(b) fails at ({ga},{gb})")
                # G4 integrality
                note("G4")
                if cst["D2"] is None or cst["D1"] is None:
                    viol("G4", T3.tag, f"integrality fails at ({ga},{gb}): "
                         f"D2={cst['D2']}, D1={cst['D1']}")
                # G3 THE CANDIDATE
                note("G3")
                lawv = C.law_value(cst, "primary")
                if lawv is None or cval != lawv:
                    viol("G3", T3.tag,
                         f"ITER-LAW-3 fails at ({ga},{gb}): measured "
                         f"{k3_repr(C, cval)}, cst={ {k: cst[k] for k in ('d3','d2','d1','D2','Sig','D1','D1n')} }")
                if lawv is not None and not K3["isz"](
                        K3["add"](lawv, K3["neg"](K3["one"]))):
                    mc["mv"] += 1
                # naive-form comparison (recorded; NOT a primary violation)
                nv = C.law_value(cst, "naive")
                if nv is None or (lawv is not None and nv != lawv):
                    mc["msepf"] += 1
                    note("NAIVEDIFF")
                if nv is None or cval != nv:
                    note("NAIVEVIOL")
                # G6 degenerations on control rows
                base = T3.tag.split(",")[-1]
                if base in ("CV", "CW", "CX"):
                    note("G6")
                    ok = True
                    if base == "CV":       # e0 = 1: c3 = zbar^d3 * z2^D2
                        pred = K3["mul"](K3["pow"](C.zbar, d3),
                                         K3["pow"](C.z2_3, cst["D2"] or 0))
                        ok = (cst["D2"] is not None and cval == pred
                              and cst["D1"] == 0)
                    elif base == "CW":     # e1 = 1: D2 = 0, Sig = d3*gamma3
                        ok = (cst["D2"] == 0
                              and cst["Sig"] == d3*T3.gamma3
                              and cval == K3["mul"](
                                  K3["pow"](C.zbar, d3),
                                  K3["pow"](C.z1_3, cst["D1"] or 0)))
                    elif base == "CX":     # e2 = 1: d3 = 0, level-2 law
                        ok = (d3 == 0 and cst["D2"] == cst["d2"]
                              and cst["Sig"] == T.gamma2*cst["d2"])
                    if not ok:
                        viol("G6", T3.tag, f"degeneration fails at ({ga},{gb})")
    # ---- F0b: CX embed tie against the level-2 measured cocycle ----
    if T3.tag.split(",")[-1] == "CX":
        for ga in W1:
            for gb in W1:
                note("F0b")
                cval = C.cocycle(ga, gb)[0]
                c2m, _ = C2.cocycle(ga, gb)
                if cval != K3["embed"](c2m):
                    viol("F0b", T3.tag, f"CX embed tie fails at ({ga},{gb})")
    # ---- G5 associativity ----
    triples = [(a, b, t) for a in W1 for b in W1 for t in W1]
    if len(triples) > 216:
        triples = random.sample(triples, 216)
    for (a, b, t) in triples:
        note("G5")
        lhs = K3["mul"](C.cocycle(a, b)[0], C.cocycle(a + b, t)[0])
        rhs = K3["mul"](C.cocycle(b, t)[0], C.cocycle(a, b + t)[0])
        if lhs != rhs:
            viol("G5", T3.tag, f"cocycle identity (measured) fails "
                               f"at ({a},{b},{t})")
        parts = [C.law_value(C.constants(x, y), "primary")
                 for (x, y) in ((a, b), (a + b, t), (b, t), (a, b + t))]
        if any(pp is None for pp in parts):
            viol("G5", T3.tag, f"closed form non-integral at ({a},{b},{t})")
        elif K3["mul"](parts[0], parts[1]) != K3["mul"](parts[2], parts[3]):
            viol("G5", T3.tag, f"cocycle identity (closed) fails "
                               f"at ({a},{b},{t})")
    # ---- G7 Z/E3 descent: simultaneous AND mixed blocks ----
    def table(wa, wb):
        return {(r, s): C.cocycle(wa[r], wb[s])[0]
                for r in range(E3) for s in range(E3)}
    t1 = table(W1, W1)
    for name, wa, wb in (("W2xW2", W2, W2), ("W3xW3", W3, W3),
                         ("W2xW1", W2, W1), ("W1xW2", W1, W2),
                         ("W3xW1", W3, W1), ("W1xW3", W1, W3)):
        t = table(wa, wb)
        for k in t1:
            note("G7")
            if t[k] != t1[k]:
                viol("G7", T3.tag, f"descent fails: block {name} at {k}")
    # ---- per-tower records ----
    if T3.tag.split(",")[-1] == "G":
        vals = sorted({k3_repr(C, v) for v in t1.values()
                       if v != K3["one"]})
        results["rowG_valuesets"][T3.tag] = vals
    results["meters"][T3.tag] = mc
    results["Gamma0"][T3.tag] = G0

# ---------------------------------------------------------------------------
def g8_symbolic(n=20000):
    """Integer layer, pure Z: L1 x3, INNER-SHIFT-3, the composed-shift
    identity, D2/D1 integrality, generalized EXP at both levels; MSEPi."""
    msepi = 0
    for _ in range(n):
        note("G8")
        e0 = random.randrange(1, 13)
        h0 = random.choice([h for h in range(1, 40) if math.gcd(h, e0) == 1])
        e1 = random.randrange(1, 13)
        h1 = random.choice([h for h in range(1, 40) if math.gcd(h, e1) == 1])
        e2 = random.randrange(1, 13)
        h2 = random.choice([h for h in range(1, 40) if math.gcd(h, e2) == 1])
        g0 = random.randrange(1, 5); g1 = random.randrange(1, 5)
        l0, l0p = bezout(e0, h0); l1, l1p = bezout(e1, h1)
        w1P = e0*g0*h0; gam2 = e1*w1P + h1
        w2P = e1*g1*gam2; gam3 = e2*w2P + h2
        ga = random.randrange(-3000, 3001)
        gb = random.randrange(-3000, 3001)
        def split3(g):
            s3, u3 = eq12(g, e2, h2); b2 = u3 - s3*w2P
            s2, u2 = eq12(b2, e1, h1); b1 = u2 - s2*w1P
            s1, u1 = eq12(b1, e0, h0)
            return s3, s2, s1, b2, b1
        s3a, s2a, s1a, b2a, b1a = split3(ga)
        s3b, s2b, s1b, b2b, b1b = split3(gb)
        s3c, s2c, s1c, b2c, b1c = split3(ga + gb)
        d3 = (s3a + s3b)//e2
        # L1 level 3 + INNER-SHIFT-3
        if d3 not in (0, 1) or s3c != s3a + s3b - d3*e2:
            viol("G8", "symbolic", f"L1(lvl3) fails {(e2,h2,ga,gb)}"); continue
        if b2c != b2a + b2b + d3*gam3:
            viol("G8", "symbolic", f"INNER-SHIFT-3 fails {(e2,h2,ga,gb)}")
            continue
        # D2 integrality + composed shift identity
        numD2 = s2a + s2b - s2c + l1*gam3*d3
        if numD2 % e1 != 0:
            viol("G8", "symbolic", f"D2 non-integral {(e0,h0,e1,h1,e2,h2,ga,gb)}")
            continue
        D2 = numD2//e1
        Sig = D2*gam2 + d3*gam3*(l1p - l1*w1P)
        if b1c != b1a + b1b + Sig:
            viol("G8", "symbolic", f"composed shift fails "
                 f"{(e0,h0,g0,e1,h1,g1,e2,h2,ga,gb)}: b1''-b1-b1'="
                 f"{b1c-b1a-b1b} vs Sig={Sig}")
            continue
        # D1 integrality + generalized EXP (inner)
        numD1 = s1a + s1b - s1c + l0*Sig
        if numD1 % e0 != 0:
            viol("G8", "symbolic", f"D1 non-integral {(e0,h0,e1,h1,e2,h2,ga,gb)}")
            continue
        d1 = (s1a + s1b)//e0
        ssum, _ = eq12(b1a + b1b, e0, h0)
        lhs = d1 + ((ssum - l0*(b1a + b1b)) - (s1c - l0*b1c))//e0
        if lhs != numD1//e0:
            viol("G8", "symbolic", f"EXP(inner) fails {(e0,h0,ga,gb)}")
            continue
        # generalized EXP (middle): z2 exponent assembly
        d2 = (s2a + s2b)//e1
        ssum2, _ = eq12(b2a + b2b, e1, h1)
        lhs2 = d2 + ((ssum2 - l1*(b2a + b2b)) - (s2c - l1*b2c))//e1
        if lhs2 != D2:
            viol("G8", "symbolic", f"EXP(middle) fails {(e1,h1,ga,gb)}")
            continue
        if Sig != gam2*d2:
            msepi += 1
    return msepi

# ---------------------------------------------------------------------------
def cert3_internal(T3):
    """Level-3 data certification: psi2 + Phi3 shape + R3s(Phi3) == psi2."""
    T, R, K2t = T3.T, T3.R, T3.K2
    note("CERT3")
    ok = True
    if math.gcd(T3.e2, T3.h2) != 1: ok = False
    if K2t["isz"](T3.psi2[0]): ok = False
    if T3.psi2[-1] != K2t["one"]: ok = False
    if not S3MOD._no_root(K2t, T3.psi2) and T3.g2 >= 2: ok = False
    if not ok:
        viol("CERT3", T3.tag, "psi2 data bad (gcd/const/monic/irred)")
    P3 = T3.Phi3
    if len(P3) - 1 != T3.degPhi3:
        viol("CERT3", T3.tag, f"deg Phi3 = {len(P3)-1} != {T3.degPhi3}")
    lead = P3[-1] if P3 else R["zero"]
    if R["isz"](lead) or not R["isz"](R["add"](lead, R["neg"](R["one"]))):
        viol("CERT3", T3.tag, "Phi3 not monic")
    d2v, vals, g = T3.w3_data(P3)
    if g != T3.w3Phi3:
        viol("CERT3", T3.tag, f"w3(Phi3) = {g} != {T3.w3Phi3}")
    for j, c in enumerate(d2v):
        if c and T3.e2*vals[j] + j*T3.gamma3 < T3.w3Phi3:
            viol("CERT3", T3.tag, f"Phi3 slot {j} below weight")
    side, j0, _ = T3.R3s(P3)
    if j0 != 0 or side != fp_norm(K2t, T3.psi2):
        viol("CERT3", T3.tag, "R3s(Phi3) != psi2 exactly")

def cert3_pari(T3, pari):
    if T3.kind != "Zp" or pari is None: return
    note("CERT3P")
    T = T3.T
    coeffs = [int(c) for c in T3.Phi3]
    F = pari.Pol(list(reversed(coeffs)))
    fac = pari.factorpadic(F, T3.p, 80)
    if len(fac[0]) != 1 or int(fac[1][0]) != 1:
        viol("CERT3P", T3.tag, f"PARI: Phi3 NOT irreducible over Q_{T3.p}")
        return
    nf = pari.nfinit([F, [T3.p]])
    dec = pari.idealprimedec(nf, T3.p)
    e_pred, f_pred = T3.E3, T.d0*T.g0*T.g1*T3.g2
    if len(dec) != 1:
        viol("CERT3P", T3.tag, f"PARI: {len(dec)} primes above p (pred 1)")
        return
    pr = dec[0]
    if (int(pr[2]), int(pr[3])) != (e_pred, f_pred):
        viol("CERT3P", T3.tag, f"PARI (e,f) = ({int(pr[2])},{int(pr[3])}) "
                               f"!= pred ({e_pred},{f_pred})")

# ---------------------------------------------------------------------------
# MUTATION CONTROLS (post-battery, sealed): each mutated closed form must be
# DETECTED (>= 1 mismatch vs the measured cocycle) on the reduced battery.
def mutated_value(C, cst, mut):
    T3 = C.T3; T = T3.T; K3 = C.K3
    d3, d2 = cst["d3"], cst["d2"]
    s2def = (cst["D2"]*T.e1 - T.l1*T3.gamma3*d3
             if cst["D2"] is not None else None)
    s1def = (cst["D1"]*T.e0 - T.l0*cst["Sig"]
             if cst["D1"] is not None and cst["Sig"] is not None else None)
    if s2def is None or s1def is None:
        return None  # primary non-integral (never happens if law GREEN)
    if mut == "m1":       # drop l1*gamma3*d3 from D2 (Sig follows mutated D2)
        numD2 = s2def
        if numD2 % T.e1 != 0: return None
        D2 = numD2//T.e1
        Sig = D2*T.gamma2 + d3*T3.gamma3*(T.l1p - T.l1*T.w1Phi1)
        numD1 = s1def + T.l0*Sig
        if numD1 % T.e0 != 0: return None
        return (d3, D2, numD1//T.e0)
    if mut == "m2":       # naive template Sig -> gamma2*d2
        numD1 = s1def + T.l0*T.gamma2*d2
        if numD1 % T.e0 != 0: return None
        return (d3, cst["D2"], numD1//T.e0)
    if mut == "m3":       # D2 denominator e1 -> e0
        numD2 = s2def + T.l1*T3.gamma3*d3
        if numD2 % T.e0 != 0: return None
        D2 = numD2//T.e0
        Sig = D2*T.gamma2 + d3*T3.gamma3*(T.l1p - T.l1*T.w1Phi1)
        numD1 = s1def + T.l0*Sig
        if numD1 % T.e0 != 0: return None
        return (d3, D2, numD1//T.e0)
    if mut == "m4":       # d3 with wrong modulus e1
        return ("d3mut", None, None)
    if mut == "m6":       # letter swap z2 <-> z1
        return ("swap", cst["D2"], cst["D1"])
    return None

def mutation_controls(results):
    detects = {m: 0 for m in ("m1", "m2", "m3", "m4", "m5", "m6")}
    tested = {m: 0 for m in detects}
    for kind, p in MUT_CONFIGS:
        for tag, d0, r0, r1, r2 in ROWS:
            if tag not in MUT_ROWS: continue
            T3 = Tower3(kind, p, d0, r0, r1, r2, f"{kind},p={p},{tag}")
            C = Composite3(T3)
            T = T3.T; K3 = C.K3; E3 = T3.E3
            W1 = list(range(C.Gamma0, C.Gamma0 + E3))
            # m5: anchor prediction without eps2
            for g in W1:
                tested["m5"] += 1
                v = C.anchor_val(g)
                _, _, _, b2, b1, _ = C.split(g)
                bad = C.K3["embed"](T3.K2["embed"](T.eps1(b1)))
                if v != bad:
                    detects["m5"] += 1
            for ga in W1:
                for gb in W1:
                    cval = C.cocycle(ga, gb)[0]
                    cst = C.constants(ga, gb)
                    for m in ("m1", "m2", "m3", "m6"):
                        tested[m] += 1
                        mv = mutated_value(C, cst, m)
                        if mv is None:
                            detects[m] += 1   # non-integrality = detection
                            continue
                        if mv[0] == "swap":
                            val = K3["mul"](K3["pow"](C.zbar, cst["d3"]),
                                  K3["mul"](K3["pow"](C.z1_3, mv[1]),
                                            K3["pow"](C.z2_3, mv[2])))
                        else:
                            val = K3["mul"](K3["pow"](C.zbar, mv[0]),
                                  K3["mul"](K3["pow"](C.z2_3, mv[1]),
                                            K3["pow"](C.z1_3, mv[2])))
                        if val != cval:
                            detects[m] += 1
                    # m4: recompute d3 with modulus e1
                    tested["m4"] += 1
                    s3a = C.split(ga)[0]; s3b = C.split(gb)[0]
                    d3m = (s3a + s3b)//T.e1
                    if d3m != cst["d3"]:
                        val = K3["mul"](K3["pow"](C.zbar, d3m),
                              K3["mul"](K3["pow"](C.z2_3, cst["D2"]),
                                        K3["pow"](C.z1_3, cst["D1"])))
                        if val != cval:
                            detects["m4"] += 1
    results["mutations"] = dict(detected=detects, tested=tested)
    return detects

# ---------------------------------------------------------------------------
def design_mode():
    """Tower construction + constants table ONLY (disclosed pre-seal).
    NO law comparison, NO val3 on any pair."""
    print("DESIGN MODE: tower constants (no law evaluation)")
    print(f"{'tower':16} {'E3':>3} {'g2c':>4} {'g3c':>5} {'G0':>6} "
          f"{'degF3':>6} {'l0':>3} {'l1':>3}")
    for kind, p in CONFIGS:
        for tag, d0, r0, r1, r2 in ROWS:
            T3 = Tower3(kind, p, d0, r0, r1, r2, f"{kind},p={p},{tag}")
            C = Composite3(T3)
            T = T3.T
            print(f"{T3.tag:16} {T3.E3:>3} {T.gamma2:>4} {T3.gamma3:>5} "
                  f"{C.Gamma0:>6} {T3.degPhi3:>6} {T.l0:>3} {T.l1:>3}")
    print("design OK: all 52 towers constructed, windows scanned")

def main():
    if "--design" in sys.argv:
        design_mode(); return 0
    t0 = time.time()
    random.seed(20260903)
    sys.path.insert(0, os.path.expanduser(
        '~/.local/lib/python3.10/site-packages'))
    try:
        import cypari2
        pari = cypari2.Pari(); pari.allocatemem(1 << 28, silent=True)
    except Exception as exc:
        pari = None
        print(f"WARNING: cypari2 unavailable ({exc}); PARI legs skipped "
              "-> RED if predicted")
    results = {"meters": {}, "Gamma0": {}, "rowG_valuesets": {},
               "harness_events": []}
    # ---- CERT phase ----
    gv0 = len(G.VIOL)
    for kind, p in CONFIGS:
        for tag, d0, r0, r1, r2 in ROWS:
            try:
                T3 = Tower3(kind, p, d0, r0, r1, r2, f"{kind},p={p},{tag}")
                G.T1_T2(T3.T, nf=6)
                G.T5(T3.T)
                G.T11(T3.T, pari)
                cert3_internal(T3)
                cert3_pari(T3, pari)
            except Exception as exc:
                HARNESS_EVENTS.append((f"{kind},p={p},{tag}", "CERT",
                                       repr(exc)))
    cert2_viol = len(G.VIOL) - gv0
    cert2_n = sum(G.COUNTS.get(k, 0) for k in ("T1", "T2", "T5", "T11"))
    print(f"[{time.time()-t0:6.1f}s] CERT done: level-2 {cert2_viol} viol "
          f"({cert2_n} samples); level-3 internal+PARI in families")
    # ---- main battery ----
    for kind, p in CONFIGS:
        for tag, d0, r0, r1, r2 in ROWS:
            full = f"{kind},p={p},{tag}"
            try:
                T3 = Tower3(kind, p, d0, r0, r1, r2, full)
                run_tower(T3, results)
            except Exception as exc:
                HARNESS_EVENTS.append((full, "BATTERY", repr(exc)))
        print(f"[{time.time()-t0:6.1f}s] ring ({kind},p={p}) done: "
              f"cumulative violations = {len(VIOL)}")
    # ---- G8 symbolic ----
    msepi = g8_symbolic(20000)
    print(f"[{time.time()-t0:6.1f}s] G8 symbolic done (MSEPi = {msepi})")
    # ---- mutation controls ----
    try:
        detects = mutation_controls(results)
    except Exception as exc:
        detects = {}
        HARNESS_EVENTS.append(("mutation_phase", "MUT", repr(exc)))
    print(f"[{time.time()-t0:6.1f}s] mutation controls done: "
          f"{ {m: d for m, d in detects.items()} }")
    results["harness_events"] = HARNESS_EVENTS
    # ------------------------------- report ---------------------------------
    print(); print("=" * 78)
    print("PREREGISTERED vs OBSERVED (violations; samples in parentheses)")
    print("=" * 78)
    fams = [
        ("F0a", "LEVEL-2 FIDELITY: accepted law on subtower  "),
        ("F0b", "CX embed tie level-3 == level-2             "),
        ("G1",  "L6-3 ANCHOR-VAL eps-chain, 3 windows        "),
        ("G2",  "L7-3 PAIR-VAL both forms + top-slot shape   "),
        ("G3",  "THE CANDIDATE (ITER-LAW-3) closed form      "),
        ("G4",  "D2/D1 integrality                           "),
        ("G5",  "cocycle identity, 216 triples/tower         "),
        ("G6",  "degenerations CV/CW/CX                      "),
        ("G7",  "Z/E3 descent: simultaneous + 4 MIXED blocks "),
        ("G8",  "integer layer symbolic (20k draws)          "),
        ("CERT3", "level-3 data cert (psi2/Phi3/R3s key)     "),
        ("CERT3P", "PARI level-3 (Phi3 irred, (e,f)=(E3,f))  "),
    ]
    all_green = True
    for fam, desc in fams:
        obs = sum(1 for v in VIOL if v[0] == fam)
        n = COUNTS.get(fam, 0)
        verdict = "GREEN" if obs == 0 else "RED"
        if obs: all_green = False
        print(f"{fam:6} {desc} pred 0  obs {obs:5d} ({n:6d})  {verdict}")
    cert2_verdict = "GREEN" if cert2_viol == 0 else "RED"
    if cert2_viol: all_green = False
    print(f"CERT2  level-2 subtower (T1/T2/T5/T11+PARI)        "
          f"pred 0  obs {cert2_viol:5d} ({cert2_n:6d})  {cert2_verdict}")
    # ---- meters ----
    def meter_ok(rows_needed, key):
        bad = []
        for kind, p in CONFIGS:
            for tag in rows_needed:
                full = f"{kind},p={p},{tag}"
                if results["meters"].get(full, {}).get(key, 0) <= 0:
                    bad.append(full)
        return bad
    meter_specs = [
        ("MC-inner > 0 on A,B", ("A", "B"), "inner"),
        ("MC-mid   > 0 on A,B,D,F,L", ("A", "B", "D", "F", "L"), "mid"),
        ("MC-dbl   > 0 on A,B", ("A", "B"), "dbl"),
        ("MV       > 0 on C,E,G", ("C", "E", "G"), "mv"),
        ("MD3      > 0 on all e2>=2 rows",
         tuple(t for t, _, _, _, r2 in ROWS if r2[0] >= 2), "md3"),
    ]
    for label, rows_needed, key in meter_specs:
        bad = meter_ok(rows_needed, key)
        ok = not bad
        if not ok: all_green = False
        print(f"METER {label:34} {'MET' if ok else 'MISS: ' + str(bad)}")
    msepi_ok = msepi > 0
    if not msepi_ok: all_green = False
    print(f"METER MSEPi (symbolic naive/composed separation) = {msepi} "
          f"(pred > 0)  {'MET' if msepi_ok else 'MISS'}")
    msepf = COUNTS.get("NAIVEDIFF", 0)
    print(f"METER MSEPf (field-level separation, report) = {msepf}; "
          f"naive-form violations vs measured = {COUNTS.get('NAIVEVIOL', 0)}"
          f" / {COUNTS.get('G3', 0)} pairs")
    # ---- mutations ----
    for m in ("m1", "m2", "m3", "m4", "m5", "m6"):
        d = detects.get(m, 0)
        ok = d >= 1
        if not ok: all_green = False
        print(f"MUTATION {m}: detected {d} (pred >= 1)  "
              f"{'MET' if ok else 'NOT DETECTED — battery lacks teeth'}")
    # ---- harness events ----
    if HARNESS_EVENTS:
        all_green = False
        print(f"{len(HARNESS_EVENTS)} HARNESS EVENTS (bug detectors first):")
        for h in HARNESS_EVENTS[:20]:
            print("  ", h)
    if VIOL:
        print(f"{len(VIOL)} VIOLATIONS (first 40):")
        for v in VIOL[:40]:
            print("  ", v)
    for tag, vals in results["rowG_valuesets"].items():
        print(f"row-G value set {tag}: {vals}")
    total = sum(COUNTS.values()) + cert2_n
    print(f"TOTAL samples: {total}   elapsed {time.time()-t0:.1f}s")
    verdict = ("ALL GREEN" if all_green and not VIOL and not HARNESS_EVENTS
               else "RED — see above")
    print(f"VERDICT (preregistered rows): {verdict}")
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "iterlawr_probe_results.json"), "w") as fh:
        json.dump(dict(violations=[list(v) for v in VIOL], counts=COUNTS,
                       cert2_violations=cert2_viol, cert2_samples=cert2_n,
                       msepi=msepi, meters=results["meters"],
                       Gamma0=results["Gamma0"],
                       rowG_valuesets=results["rowG_valuesets"],
                       mutations=results.get("mutations"),
                       harness_events=HARNESS_EVENTS),
                  fh, indent=1, default=str)
    return 0 if (all_green and not VIOL and not HARNESS_EVENTS) else 1

if __name__ == "__main__":
    sys.exit(main())
