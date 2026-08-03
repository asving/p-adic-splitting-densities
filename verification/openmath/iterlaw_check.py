#!/usr/bin/env python3
"""iterlaw_check.py — the PROOF-STEP falsifier for the ITER-LAW note
(lean/notes/openmath/ITERLAW_2026-08-08.md; SYNTHESIS PASS 7 queue #6).

CHARGE (sealed pre-run; two-commit seal): test the PROVED identity end-to-end on
FRESH draws — fresh tower rows (none in the strata-probe roster, except the
designed gate row X = the row-N SHAPE, re-instantiated fresh), fresh seed, fresh
windows including one (Γ₀+7E₂) outside every previously probed window — and probe
the PROOF'S STEPS (the lemma chain), not only the end law.  A RED in any family
first goes through the bug-detector rows (CERT + F4's exact development identity);
a RED surviving classification means THE NOTE IS WRONG and is this unit's headline
result (exact witness printed).  This runner reuses the harness calculus
(grb_order2_check Tower/R2w, strata_probe Composite) BECAUSE the theorem is a
statement ABOUT those operators (they are the definitions, not an oracle); the
independent-implementation leg belongs to the acceptance arc (F2c standing rule),
not to this seal.

================================ TOWER ROSTER =================================
(d0; e0,h0,g0; e1,h1,g1) over all four rings {Z_2, Z_3, F_2[[t]], F_3[[t]]}:
  P (1; 3,2,1; 2,1,1)  E2=6  g0=1, e0=3: Case II live (inner wrap needs the
                              standard-lift reduction); l0 = 2 nontrivial
  Q (2; 4,3,1; 2,1,1)  E2=8  g0=1, e0=4, d0=2: Case II at E2 beyond every
                              probed roster row (probe had E2 <= 6); l0 = 3
  R (1; 2,1,2; 2,1,1)  E2=4  g0=2: Case I with inner wrap (single-digit route)
  S (1; 3,1,2; 2,1,2)  E2=6  g0=2, g1=2: K2 a genuine extension (zbar not in K1)
  U (1; 2,3,2; 3,2,1)  E2=6  e1=3, h1=2: nontrivial outer track (l1 = 2)
  V (1; 1,1,2; 2,1,2)  E2=2  e0=1 CONTROL: COR-3 D-REAL degeneration c = zbar^d2
  W (1; 3,1,1; 1,1,2)  E2=3  e1=1 CONTROL: COR-3 degeneration c = z1^d1, d2 = 0
  X (2; 2,1,1; 2,1,2)  E2=4  the row-N SHAPE: the S6.6/DITER-S3 NOT-CYCLIC gate

========================= PREREGISTERED PREDICTIONS ===========================
(violation counts; sample counts printed at run time; RED = observed != predicted)
F1  L6 ANCHOR-VAL: val(phi_gamma) == eps1(gamma1(gamma)) != 0, every letter of
    windows W1 = [G0, G0+E2), W2 = W1+E2, W3 = W1+7E2.        PREDICTED: 0.
F2  L7 PAIR-VAL, BOTH displayed forms, on pair blocks W1xW1, W3xW3, W1xW3:
    (a) val(phi_a phi_b) == zbar^d2 * z1^d1 * eps1(beta_a+beta_b),
    (b)                  == zbar^d2 * val(phi_a) * val(phi_b),
    plus the shape clause: the weight read is the SINGLE nonzero coefficient at
    slot y^d2, at gamma = ga+gb.                              PREDICTED: 0.
F3  THEOREM (ITER-LAW): measured cocycle == closed form
    zbar^d2 * z1^((s1a+s1b-s1c+l0*gamma2*d2)/e0), same pair blocks. PREDICTED: 0.
F4  Case-II development identity (the proof's ONLY lift-form-consuming step): at
    every block pair with g0 == 1 and d1 == 1, the Phi1-development of the anchor
    product is EXACTLY [slot S2: -chat*pi^(U+h0)*Phi0^(S1-e0),
    slot S2+1: pi^U*Phi0^(S1-e0)], zeros elsewhere.           PREDICTED: 0
    violations; coverage counter > 0 on rows P and Q (else the run is declared
    NON-PROBATIVE for Case II — a seal failure, not a math verdict).
F5  COR-2 B0a associativity c(a,b)c(a+b,t) == c(b,t)c(a,b+t), triples from W1
    (all E2^3 if <= 216 else 216 sampled), MEASURED cocycles AND closed forms
    separately.                                               PREDICTED: 0.
F6  COR-1 integrality (s1a+s1b-s1c+l0*gamma2*d2) % e0 == 0, all block pairs.
                                                              PREDICTED: 0.
F7  COR-3 degenerations: row V (e0=1): c == zbar^d2 exactly; row W (e1=1):
    d2 == 0 and c == z1^d1 exactly; all block pairs.          PREDICTED: 0.
F8  COR-4 representative independence: the (rho,sigma) cocycle table on W2 and
    on W3 each equals the table on W1.                        PREDICTED: 0.
F9  The integer layer on 20,000 symbolic draws (no field, pure Z): L1 EQ12-ADD;
    L4's exponent tie l0p*s(b) - l0*u(b) == (s(b) - l0*b)/e0 (integrality
    included); L2 INNER-SHIFT; Lemma EXP.                     PREDICTED: 0.
F10 The S6.6 gate at row X: cyc_adjudicate == NOT-CYCLIC at ALL FOUR rings, and
    the measured non-1 value set == the ITER-LAW-predicted set. PREDICTED:
    NOT-CYCLIC 4/4, 0 set mismatches.
CERT tower-data certification of ALL rows: G.T1_T2 (6 samples) + G.T5 internal,
    G.T11 (PARI factorpadic) on the Z_p instances.            PREDICTED: 0.

DETERMINISTIC: random.seed(20260825).  EXACT arithmetic only.  Exit 0 iff all
families GREEN.  JSON: iterlaw_check_results.json.
"""
import random, sys, os, time, json, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import grb_order2_check as G
from grb_order2_check import (dev, w0, pnorm, padd, pmul, ppow, pscal, pneg,
                              eq12, bezout, INF, Tower)
import strata_probe as SP

VIOL = []
COUNTS = {}
def note(fam, n=1): COUNTS[fam] = COUNTS.get(fam, 0) + n
def viol(fam, tag, detail): VIOL.append((fam, tag, detail))

ROWS = [
    ("P", 1, (3,2,1), (2,1,1)),
    ("Q", 2, (4,3,1), (2,1,1)),
    ("R", 1, (2,1,2), (2,1,1)),
    ("S", 1, (3,1,2), (2,1,2)),
    ("U", 1, (2,3,2), (3,2,1)),
    ("V", 1, (1,1,2), (2,1,2)),
    ("W", 1, (3,1,1), (1,1,2)),
    ("X", 2, (2,1,1), (2,1,2)),
]
CONFIGS = [("Zp", 2), ("Zp", 3), ("Fpt", 2), ("Fpt", 3)]

def closed_form(C, ga, gb):
    """The THEOREM's right-hand side (independent transcription of the S5
    display; C.iter_law is the probe-era implementation of the same formula —
    both are computed and compared to each other as a transcription check)."""
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

def pair_val_and_shape(C, ga, gb):
    """val(phi_ga*phi_gb) with the L7 shape clause checked; returns
    (value, d2, shape_ok_detail_or_None)."""
    T, K2 = C.T, C.K2
    s2a = C.split(ga)[0]; s2b = C.split(gb)[0]
    d2 = (s2a + s2b)//T.e1
    prod = pmul(T.R, C.anchor(ga), C.anchor(gb))
    coeffs, meta = T.R2w(prod, with_meta=True)
    nz = [j for j, c in enumerate(coeffs) if not T.K1["isz"](c)]
    shape_bad = None
    if meta["gamma"] != ga + gb or nz != [d2]:
        shape_bad = (f"gamma={meta['gamma']} (want {ga+gb}), nz={nz} "
                     f"(want [{d2}])")
    v = K2["zero"]; zp = K2["one"]
    for c in coeffs:
        if not T.K1["isz"](c):
            v = K2["add"](v, K2["mul"](K2["embed"](c), zp))
        zp = K2["mul"](zp, C.zbar)
    return v, d2, shape_bad

def run_tower(T, results):
    C = SP.Composite(T)
    K2, K1, E2, R = C.K2, T.K1, T.E2, T.R
    G0 = C.Gamma0
    wins = [list(range(G0 + k*E2, G0 + (k+1)*E2)) for k in (0, 1, 7)]
    W1, W2, W3 = wins
    z1K2 = C.z1_2
    # ---- F1 ANCHOR-VAL on all three windows ----
    for win in wins:
        for g in win:
            note("F1")
            v = C.anchor_val(g)
            pred = K2["embed"](T.eps1(C.split(g)[3]))
            if v != pred or K2["isz"](v):
                viol("F1", T.tag, f"ANCHOR-VAL fails at gamma={g}")
    # ---- pair blocks: F2 / F3 / F4 / F6 / F7 ----
    blocks = [(W1, W1), (W3, W3), (W1, W3)]
    caseII = 0
    for A, B in blocks:
        for ga in A:
            for gb in B:
                s2a, s1a, u1a, b1a = C.split(ga)
                s2b, s1b, u1b, b1b = C.split(gb)
                d2 = (s2a + s2b)//T.e1
                d1 = (s1a + s1b)//T.e0
                # F2 PAIR-VAL both forms + shape
                note("F2")
                v, d2v, shape_bad = pair_val_and_shape(C, ga, gb)
                if shape_bad is not None:
                    viol("F2", T.tag, f"shape at ({ga},{gb}): {shape_bad}")
                predA = K2["mul"](K2["pow"](C.zbar, d2),
                        K2["mul"](K2["pow"](z1K2, d1),
                                  K2["embed"](T.eps1(b1a + b1b))))
                predB = K2["mul"](K2["pow"](C.zbar, d2),
                        K2["mul"](K2["embed"](T.eps1(b1a)),
                                  K2["embed"](T.eps1(b1b))))
                if v != predA:
                    viol("F2", T.tag, f"PAIR-VAL(a) fails at ({ga},{gb})")
                if v != predB:
                    viol("F2", T.tag, f"PAIR-VAL(b) fails at ({ga},{gb})")
                # F6 integrality
                note("F6")
                s1c = C.split(ga + gb)[1]
                num = s1a + s1b - s1c + T.l0*T.gamma2*d2
                if num % T.e0 != 0:
                    viol("F6", T.tag, f"integrality fails at ({ga},{gb})")
                # F3 THEOREM
                note("F3")
                c, d2m = C.cocycle(ga, gb)
                cf, _ = closed_form(C, ga, gb)
                pf = C.iter_law(ga, gb)
                if cf is None or c != cf:
                    viol("F3", T.tag, f"ITER-LAW fails at ({ga},{gb}): "
                         f"measured {SP.k2_repr(C, c)}")
                if pf is None or cf != pf:
                    viol("F3", T.tag,
                         f"closed-form transcription mismatch at ({ga},{gb})")
                # F4 Case-II development identity
                if T.g0 == 1 and d1 == 1:
                    note("F4"); caseII += 1
                    U = u1a + u1b; S1 = s1a + s1b; S2 = s2a + s2b
                    prod = pmul(R, C.anchor(ga), C.anchor(gb))
                    dv = dev(R, prod, T.Phi1)
                    chat = T.liftK0(T.psi0[0])
                    A0 = pnorm(R, pneg(R, pscal(R, R["pi_pow"](U + T.h0),
                              pmul(R, chat, ppow(R, T.Phi0, S1 - T.e0)))))
                    A1 = pscal(R, R["pi_pow"](U), ppow(R, T.Phi0, S1 - T.e0))
                    ok = (len(dv) == S2 + 2 and pnorm(R, dv[S2]) == A0
                          and pnorm(R, dv[S2+1]) == A1
                          and all(not dv[j] for j in range(S2)))
                    if not ok:
                        viol("F4", T.tag, f"Case-II development fails at "
                                          f"({ga},{gb})")
                # F7 degenerations
                if T.e0 == 1 or T.e1 == 1:
                    note("F7")
                    if T.e0 == 1 and c != K2["pow"](C.zbar, d2):
                        viol("F7", T.tag, f"e0=1 degeneration fails ({ga},{gb})")
                    if T.e1 == 1 and (d2 != 0 or c != K2["pow"](z1K2, d1)):
                        viol("F7", T.tag, f"e1=1 degeneration fails ({ga},{gb})")
    # ---- F5 B0a associativity (measured AND closed-form) ----
    triples = [(a, b, t) for a in W1 for b in W1 for t in W1]
    if len(triples) > 216:
        triples = random.sample(triples, 216)
    for (a, b, t) in triples:
        note("F5")
        lhs = K2["mul"](C.cocycle(a, b)[0], C.cocycle(a + b, t)[0])
        rhs = K2["mul"](C.cocycle(b, t)[0], C.cocycle(a, b + t)[0])
        if lhs != rhs:
            viol("F5", T.tag, f"B0a (measured) fails at ({a},{b},{t})")
        parts = [closed_form(C, a, b)[0], closed_form(C, a + b, t)[0],
                 closed_form(C, b, t)[0], closed_form(C, a, b + t)[0]]
        if any(pp is None for pp in parts):
            viol("F5", T.tag, f"closed form non-integral at ({a},{b},{t})")
        elif K2["mul"](parts[0], parts[1]) != K2["mul"](parts[2], parts[3]):
            viol("F5", T.tag, f"B0a (closed form) fails at ({a},{b},{t})")
    # ---- F8 representative independence ----
    def table(win):
        return {(r, s): C.cocycle(win[r], win[s])[0]
                for r in range(E2) for s in range(E2)}
    t1 = table(W1)
    for name, win in (("W2", W2), ("W3", W3)):
        t = table(win)
        for k in t1:
            note("F8")
            if t[k] != t1[k]:
                viol("F8", T.tag, f"rep-dependence {name} at {k}")
    # ---- F10 gate row ----
    rec = None
    if T.tag.endswith(",X"):
        tab = {(r, s): (t1[(r, s)], None) for (r, s) in t1}
        verdict, is_cyc = SP.cyc_adjudicate(C, tab)
        measured = {SP.k2_repr(C, c) for c in t1.values() if c != K2["one"]}
        predicted = set()
        for r in range(E2):
            for s in range(E2):
                cf, _ = closed_form(C, W1[r], W1[s])
                if cf != K2["one"]:
                    predicted.add(SP.k2_repr(C, cf))
        note("F10")
        if is_cyc:
            viol("F10", T.tag, f"gate row CYCLIC: {verdict}")
        if measured != predicted:
            viol("F10", T.tag, f"value-set mismatch: measured "
                 f"{sorted(measured)} vs predicted {sorted(predicted)}")
        rec = dict(tower=T.tag, verdict=verdict, cyclic=is_cyc,
                   values=sorted(measured))
        results["gate"].append(rec)
    results["caseII"][T.tag] = caseII

def f9_symbolic(n=20000):
    for _ in range(n):
        note("F9")
        e0 = random.randrange(1, 13)
        h0 = random.choice([h for h in range(1, 40)
                            if __import__("math").gcd(h, e0) == 1])
        e1 = random.randrange(1, 13)
        h1 = random.choice([h for h in range(1, 40)
                            if __import__("math").gcd(h, e1) == 1])
        g0 = random.randrange(1, 5)
        l0, l0p = bezout(e0, h0)
        w1P = e0*g0*h0; g2 = e1*w1P + h1
        # L4 exponent tie + integrality
        b = random.randrange(-500, 501)
        s, u = eq12(b, e0, h0)
        if (s - l0*b) % e0 != 0 or l0p*s - l0*u != (s - l0*b)//e0:
            viol("F9", "symbolic", f"L4 fails at e0={e0},h0={h0},b={b}")
            continue
        # L1
        b2 = random.randrange(-500, 501)
        s2_, u2_ = eq12(b2, e0, h0)
        d1 = (s + s2_)//e0
        ss, uu = eq12(b + b2, e0, h0)
        if d1 not in (0, 1) or ss != s + s2_ - d1*e0 or uu != u + u2_ + d1*h0:
            viol("F9", "symbolic", f"L1 fails at e0={e0},h0={h0}")
            continue
        # L2 INNER-SHIFT
        ga = random.randrange(-500, 501); gb = random.randrange(-500, 501)
        def gamma1(g):
            s2g, u2g = eq12(g, e1, h1)
            return u2g - s2g*w1P, s2g
        ba, s2a = gamma1(ga); bb, s2b = gamma1(gb); bc, _ = gamma1(ga + gb)
        d2 = (s2a + s2b)//e1
        if bc != ba + bb + d2*g2:
            viol("F9", "symbolic", f"L2 fails at ({e0},{h0},{e1},{h1},{g0})")
            continue
        # Lemma EXP
        sa, _ = eq12(ba, e0, h0); sb, _ = eq12(bb, e0, h0)
        dd1 = (sa + sb)//e0
        ssum, _ = eq12(ba + bb, e0, h0)
        bpp = ba + bb + d2*g2
        spp, _ = eq12(bpp, e0, h0)
        lhs = dd1 + ((ssum - l0*(ba + bb)) - (spp - l0*bpp))//e0
        num = sa + sb - spp + l0*g2*d2
        if num % e0 != 0 or lhs != num//e0:
            viol("F9", "symbolic", "EXP fails at "
                 f"({e0},{h0},{e1},{h1},{g0},{ga},{gb})")

def main():
    t0 = time.time()
    random.seed(20260825)
    sys.path.insert(0, os.path.expanduser(
        '~/.local/lib/python3.10/site-packages'))
    try:
        import cypari2
        pari = cypari2.Pari(); pari.allocatemem(1 << 28, silent=True)
    except Exception as exc:
        pari = None
        print(f"WARNING: cypari2 unavailable ({exc}); CERT/T11 leg skipped "
              "-> RED if predicted")
    results = {"gate": [], "caseII": {}}
    # ---- CERT ----
    gv0 = len(G.VIOL)
    for kind, p in CONFIGS:
        for tag, d0, r0, r1 in ROWS:
            T = Tower(kind, p, d0, r0, r1, f"{kind},p={p},{tag}")
            G.T1_T2(T, nf=6)
            G.T5(T)
            G.T11(T, pari)
    cert_viol = len(G.VIOL) - gv0
    cert_n = sum(G.COUNTS.get(k, 0) for k in ("T1", "T2", "T5", "T11"))
    print(f"[{time.time()-t0:6.1f}s] CERT done: {cert_viol} violations "
          f"({cert_n} samples) on rows P/Q/R/S/U/V/W/X")
    # ---- main families ----
    for kind, p in CONFIGS:
        for tag, d0, r0, r1 in ROWS:
            T = Tower(kind, p, d0, r0, r1, f"{kind},p={p},{tag}")
            run_tower(T, results)
        print(f"[{time.time()-t0:6.1f}s] ring ({kind},p={p}) done: "
              f"cumulative violations = {len(VIOL)}")
    # ---- F9 ----
    f9_symbolic(20000)
    print(f"[{time.time()-t0:6.1f}s] F9 symbolic done")
    # ------------------------------- report ---------------------------------
    print()
    print("=" * 78)
    print("PREDICTED vs OBSERVED (violation counts; samples in parentheses)")
    print("=" * 78)
    fams = [
        ("F1", "L6 ANCHOR-VAL letters, 3 windows            "),
        ("F2", "L7 PAIR-VAL both forms + single-slot shape  "),
        ("F3", "THEOREM (ITER-LAW) closed form              "),
        ("F4", "Case-II development identity (bug-det+proof)"),
        ("F5", "COR-2 B0a associativity, measured + closed  "),
        ("F6", "COR-1 exponent integrality                  "),
        ("F7", "COR-3 degenerations (rows V, W)             "),
        ("F8", "COR-4 representative independence W2/W3==W1 "),
        ("F9", "integer layer L1/L4/L2/EXP, symbolic        "),
        ("F10", "S6.6 NOT-CYCLIC gate at row X              "),
    ]
    all_green = True
    for fam, desc in fams:
        obs = sum(1 for v in VIOL if v[0] == fam)
        n = COUNTS.get(fam, 0)
        verdict = "GREEN" if obs == 0 else "RED"
        if verdict == "RED": all_green = False
        print(f"{fam:3} {desc} pred 0  obs {obs:5d} ({n:6d})  {verdict}")
    cert_verdict = "GREEN" if cert_viol == 0 else "RED"
    if cert_viol: all_green = False
    print(f"CERT tower-data certification (T1/T2/T5/T11+PARI)          "
          f"pred 0  obs {cert_viol:5d} ({cert_n:6d})  {cert_verdict}")
    cov = results["caseII"]
    pq = {t: c for t, c in cov.items() if t.endswith(",P") or t.endswith(",Q")}
    cov_ok = all(c > 0 for c in pq.values()) and len(pq) == 8
    if not cov_ok: all_green = False
    print(f"F4 Case-II coverage on rows P/Q (pred > 0 each): "
          f"{sorted(pq.values())}  {'MET' if cov_ok else 'NOT MET'}")
    ncyc = sum(0 if r['cyclic'] else 1 for r in results["gate"])
    print(f"F10 gate: NOT-CYCLIC {ncyc}/{len(results['gate'])} (pred 4/4)")
    if ncyc != 4 or len(results["gate"]) != 4: all_green = False
    for r in results["gate"]:
        print(f"    {r['tower']:12} {r['verdict']}  values={r['values']}")
    if VIOL:
        print(f"{len(VIOL)} VIOLATIONS (first 30):")
        for v in VIOL[:30]:
            print("  ", v)
    print(f"TOTAL samples: {sum(COUNTS.values()) + cert_n}   "
          f"elapsed {time.time()-t0:.1f}s")
    print(f"VERDICT (preregistered rows): "
          f"{'ALL GREEN' if all_green and not VIOL else 'RED — see above'}")
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "iterlaw_check_results.json"), "w") as fh:
        json.dump(dict(violations=[list(v) for v in VIOL], counts=COUNTS,
                       cert_violations=cert_viol, cert_samples=cert_n,
                       caseII_coverage=results["caseII"],
                       gate=results["gate"]), fh, indent=1, default=str)
    return 0 if (all_green and not VIOL) else 1

if __name__ == "__main__":
    sys.exit(main())
