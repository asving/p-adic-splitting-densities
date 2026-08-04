#!/usr/bin/env python3
"""liftcorner_checks.py — LIFT-CORNER unit (NR-1): the lift-ORBIT transport
battery at g0 = 1 AND delta1 = 1.  Prereg sheet: the S2 table of
lean/notes/openmath/LIFTCORNER_2026-08-08.md (of record there; two-commit
seal: note skeleton + this runner BEFORE any full run; verdict at commit 2).

NEW vs wave-18 (iterlawlift_corner.py, consumed READ-ONLY as a library):
wave-18 probed the LAWFUL slice (residue c' = c0, xi = 1).  This battery
realizes the xi != 1 direction of the orbit — lifts whose order-1 residual is
y + c' with c' != c0, i.e. lawful lifts of the CONJUGATE psi0^(xi),
xi := c0/c' — with the LEDGER TRANSPORTED per W-2 clause 3 (corner-degenerate:
psi0 -> y + c', z1 -> z1' = -c', every deeper byte carried verbatim; sound at
g0 = 1 because degree-1 extension arithmetic is modulus-independent — the
runner ASSERTS psi1-byte carryover and shared K2 representation).
CANDIDATE: the display transports by the letter, c' = zbar^{d2} (z1')^{D1};
chi-ratio c_base = c' * xi^{D1}.  Families Q1-Q10 + TRS/CERT/ENG-GATE per the
sealed sheet.  Seed 20260911.  Exit 0 iff all GREEN.  --shakedown = reduced
crash-freedom run (1 ring, 2 rows, 1 twist, no json).
"""
import random, sys, os, time, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import grb_order2_check as G
from grb_order2_check import (pnorm, padd, pmul, ppow, pscal, mk_field_ext)
import strata_probe as SP
import iterlawlift_corner as LC          # wave-18 machinery, read-only

VIOL, COUNTS = [], {}
def note(fam, n=1): COUNTS[fam] = COUNTS.get(fam, 0) + n
def viol(fam, tag, detail): VIOL.append((fam, tag, detail))

def make_orbit_tower(kind, p, d0, r0, r1, tag, c0p, spec):
    """Fresh Tower with the LEDGER TRANSPORTED to psi0' = y + c0p, the
    standard lift rebuilt on it, then perturbation spec applied (tails/mids).
    c0p == base c0 gives the xi = 1 (lawful) slice.  Returns (T, psi1_base)."""
    T = LC.make_tower(kind, p, d0, r0, r1, tag)
    psi1_base = [tuple(c) for c in T.psi1]
    K0 = T.K0
    T.psi0 = [c0p, K0["one"]]
    T.K1 = mk_field_ext(K0, T.psi0)
    T.z1 = T.K1["z"]
    R = T.R
    Phi1 = []
    for k, c in enumerate(T.psi0):
        if K0["isz"](c):
            continue
        term = pscal(R, R["pi_pow"]((T.g0 - k)*T.h0),
                     pmul(R, T.liftK0(c), ppow(R, T.Phi0, T.e0*k)))
        Phi1 = padd(R, Phi1, term)
    T.Phi1_std = pnorm(R, Phi1)
    LC.apply_pert(T, spec)               # sets T.Phi1, rebuilds T.Phi2
    # carryover soundness assertions (disclosure (c) of the sheet)
    assert [tuple(c) for c in T.psi1] == psi1_base, "psi1 byte drift"
    return T

def measured_cocycle(T, C, ga, gb):
    v, d2, shape_bad = LC.val_and_shape(T, C, ga, gb)
    vt = C.anchor_val(ga + gb)
    return C.K2["mul"](v, C.K2["inv"](vt)), d2, shape_bad, v

def run_block(T, C, tag, base_cc, xi1, results):
    """Full transported battery on tower T + chi/wrong-letter legs against the
    cached base cocycles base_cc (same (ring,row) standard tower)."""
    K2, E2 = C.K2, T.E2
    W1 = list(range(C.Gamma0, C.Gamma0 + E2))
    W3 = [g + 7*E2 for g in W1]
    xi2 = K2["embed"](xi1)               # xi in K2
    z1old2 = K2["embed"](results["z1_base"][tag.split(":")[0]])
    for g in W1 + W3:
        note("AV")
        v = C.anchor_val(g)
        if v != K2["embed"](T.eps1(C.split(g)[3])) or K2["isz"](v):
            viol("AV", tag, f"ANCHOR-VAL at gamma={g}")
    ncov = nteeth = nfire = 0
    for A, B in ((W1, W1), (W1, W3)):
        for ga in A:
            for gb in B:
                d1 = (C.split(ga)[1] + C.split(gb)[1])//T.e0
                if d1 == 1:
                    ncov += 1
                note("PV")
                c, d2, shape_bad, v = measured_cocycle(T, C, ga, gb)
                predA = K2["mul"](K2["pow"](C.zbar, d2),
                        K2["mul"](K2["pow"](C.z1_2, d1),
                                  K2["embed"](T.eps1(C.split(ga)[3] + C.split(gb)[3]))))
                predB = K2["mul"](K2["pow"](C.zbar, d2),
                        K2["mul"](K2["embed"](T.eps1(C.split(ga)[3])),
                                  K2["embed"](T.eps1(C.split(gb)[3]))))
                if shape_bad is not None or v != predA or v != predB:
                    viol("PV", tag, f"({ga},{gb}): {shape_bad or 'value'}")
                    if d1 == 0: viol("LOC", tag, f"PV red at d1=0 ({ga},{gb})")
                note("INT"); note("TLAW"); note("TRS")
                cf, _, num = LC.closed_form(T, C, ga, gb)
                if num % T.e0 != 0:
                    viol("INT", tag, f"({ga},{gb})")
                    if d1 == 0: viol("LOC", tag, f"INT red at d1=0")
                    continue
                D1 = num//T.e0
                if cf is None or c != cf:
                    viol("TLAW", tag, f"({ga},{gb}) d1={d1} d2={d2}")
                    if d1 == 0: viol("LOC", tag, f"TLAW red at d1=0")
                pf = C.iter_law(ga, gb)
                if (cf is None) != (pf is None) or (cf is not None and cf != pf):
                    viol("TRS", tag, f"({ga},{gb})")
                # Q7 CHI: measured base == measured twisted * xi^{D1}
                note("CHI")
                if base_cc[(ga, gb)] != K2["mul"](c, K2["pow"](xi2, D1)):
                    viol("CHI", tag, f"({ga},{gb}) D1={D1}")
                # Q9 WRONGLET (only meaningful on xi != 1 towers)
                if not xi1_is_one(T, xi1):
                    note("WRONGLET")
                    wrong = K2["mul"](K2["pow"](C.zbar, d2),
                                      K2["pow"](z1old2, D1))
                    mism = (c != wrong)
                    pred = (K2["pow"](xi2, D1) != K2["one"])
                    if pred: nteeth += 1
                    if mism: nfire += 1
                    if mism != pred:
                        viol("WRONGLET", tag, f"({ga},{gb}) mism={mism} pred={pred}")
    results["cov"][tag] = ncov
    if not xi1_is_one(T, xi1):
        results["teeth"][tag] = nteeth
        results["fires"][tag] = nfire
    if ncov == 0:
        viol("COV", tag, "no delta1=1 pairs")
    if not xi1_is_one(T, xi1) and nteeth == 0:
        viol("COV", tag, "no xi^{D1} != 1 pairs: chi-leg non-probative")

def xi1_is_one(T, xi1):
    return xi1 == T.K1["one"]

def main():
    shakedown = "--shakedown" in sys.argv
    t0 = time.time()
    random.seed(20260911)
    rows = LC.ROWS if not shakedown else [r for r in LC.ROWS if r[0] in ("CB", "CF")]
    configs = LC.CONFIGS if not shakedown else [("Zp", 3)]
    results = {"cov": {}, "teeth": {}, "fires": {}, "z1_base": {},
               "towers": [], "gate_pass": 0}
    ntw = 0
    for kind, p in configs:
        for tag, d0, r0, r1 in rows:
            itag = f"{kind},p={p},{tag}"
            # base (standard) tower: chi cache + CERT
            T0 = LC.make_tower(kind, p, d0, r0, r1, itag)
            if not shakedown:
                G.T1_T2(T0, nf=4); G.T5(T0)
            C0 = SP.Composite(T0)
            results["z1_base"][itag] = T0.z1
            base_cc = {}
            W1 = list(range(C0.Gamma0, C0.Gamma0 + T0.E2))
            for ga in W1:
                for gb in W1 + [g + 7*T0.E2 for g in W1]:
                    base_cc[(ga, gb)] = measured_cocycle(T0, C0, ga, gb)[0]
            c0 = T0.psi0[0]
            # orbit draws: xi=1 dense controls on CB/CF; xi != 1 on |K0| > 2
            draws = []
            if tag in ("CB", "CF"):
                draws.append((c0, [("W1-dense", None)]))
            twists = [c for c in T0.K0["elements"]()
                      if not T0.K0["isz"](c) and c != c0][:1 if shakedown else 2]
            for c0p in twists:
                draws.append((c0p, [("W0-pure", []), ("W1-dense", None)]))
            for c0p, variants in draws:
                for vname, spec in variants:
                    Ts = LC.make_tower(kind, p, d0, r0, r1, itag)
                    if spec is None:
                        spec = LC.dense_spec(Ts)
                    del Ts
                    T = make_orbit_tower(kind, p, d0, r0, r1, itag, c0p, spec)
                    vtag = f"{itag}:{vname}:c'={c0p}"
                    note("GATE")
                    ok, why = LC.lawful_check(T)
                    if not ok:
                        viol("GATE", vtag, why)
                        continue
                    results["gate_pass"] += 1
                    ntw += 1
                    C = SP.Composite(T)
                    assert C.K2["one"] == C0.K2["one"]   # shared representation
                    # xi := c0/c' in K1 (1-tuples at g0 = 1); z1 = xi * z1'
                    xi1 = T.K1["mul"]((c0,), T.K1["inv"]((c0p,)))
                    run_block(T, C, vtag, base_cc, xi1, results)
            print(f"[{time.time()-t0:6.1f}s] {itag} done, viol={len(VIOL)}")
    if not shakedown:
        import engine_ext
        try:
            nnew = engine_ext.agreement_gate(full=False)
            if nnew:
                viol("ENGGATE", "engine_ext", f"{nnew} new gate violations")
        except Exception as exc:
            viol("ENGGATE", "engine_ext", f"gate raised: {exc}")
        note("ENGGATE")
    cert_viol = len(G.VIOL)
    fams = ["GATE", "AV", "TLAW", "PV", "INT", "LOC", "CHI", "COV",
            "WRONGLET", "TRS", "ENGGATE"]
    all_green = True
    print("=" * 72)
    for fam in fams:
        obs = sum(1 for v in VIOL if v[0] == fam)
        if obs: all_green = False
        print(f"{fam:9} pred 0  obs {obs:5d}  ({COUNTS.get(fam,0):6d})  "
              f"{'GREEN' if obs == 0 else 'RED'}")
    tot_fires = sum(results["fires"].values())
    if cert_viol: all_green = False
    print(f"CERT      pred 0  obs {cert_viol:5d}  internal T1/T2(nf=4)+T5  "
          f"{'GREEN' if cert_viol == 0 else 'RED'}")
    print(f"WRONGLET total fires {tot_fires} (pred > 0)"
          if not shakedown else "")
    if not shakedown and tot_fires == 0:
        all_green = False; print("RED: wrong-letter control toothless")
    print(f"orbit towers gate-passed: {results['gate_pass']}; "
          f"coverage min d1-pairs {min(results['cov'].values()) if results['cov'] else 0}; "
          f"teeth min {min(results['teeth'].values()) if results['teeth'] else 0}")
    for v in VIOL[:25]:
        print("  ", v)
    print(f"TOTAL checks {sum(COUNTS.values())}  elapsed {time.time()-t0:.1f}s")
    print(f"VERDICT: {'ALL GREEN' if all_green and not VIOL else 'RED'}")
    if not shakedown:
        with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                               "liftcorner_checks_results.json"), "w") as fh:
            json.dump(dict(violations=[list(v) for v in VIOL], counts=COUNTS,
                           cert_violations=cert_viol,
                           cov=results["cov"], teeth=results["teeth"],
                           fires=results["fires"],
                           sp_bugdetector=len(SP.VIOL), lc_counts=len(LC.VIOL)),
                      fh, indent=1, default=str)
    return 0 if (all_green and not VIOL) else 1

if __name__ == "__main__":
    sys.exit(main())
