#!/usr/bin/env python3
"""iterlaw_cor4_mixed.py — COR-4 MIXED-BLOCK SUPPLEMENT to the sealed ITER-LAW
falsifier (verification/openmath/iterlaw_check.py, seal commit ab7c31c).

WHY THIS FILE EXISTS (pass-PC GAP remedy, errata round 2026-08-03; finding
archived in lean/notes/openmath/ITERLAW_passPC_report.md, finding 2 [GAP]):
the sealed falsifier's F8 family compares the cocycle tables on W2xW2 and
W3xW3 against W1xW1 — i.e. SIMULTANEOUS translation of both representatives.
COR-4 (ITERLAW_2026-08-08.md S6.4) asserts representative independence when
EITHER argument's representative is changed SEPARATELY; the mixed blocks
W2xW1, W1xW2, W3xW1, W1xW3 were never compared to the base table.  This
supplement closes exactly that gap.  The sealed falsifier stays BYTE-UNTOUCHED;
this is a supplement under the errata unit's charge, NOT the F2c independent
reimplementation (that is verification/openmath/iterlaw_f2c_reimpl.py, pass PE).

ATTRIBUTION / FIDELITY NOTE: this script deliberately REUSES the harness
calculus (grb_order2_check.Tower, strata_probe.Composite — the note's
definitions) and TRANSCRIBES from the sealed iterlaw_check.py: the tower
roster ROWS/CONFIGS, the window schedule (W1 = [Gamma0, Gamma0+E2),
W2 = W1+E2, W3 = W1+7E2), the table() construction, and closed_form().
Fidelity to the sealed harness semantics is the point of the supplement.
New here: the FOUR mixed blocks per family, a fresh random-offset window W4
(own seed), two FRESH tower rows Y/Z (own choice, E2 = 8 and 10 — both >= 8),
and a closed-form tie on every mixed entry.

================================ TOWER ROSTER =================================
Rows P,Q,R,S,U,V,W,X: transcribed verbatim from the sealed iterlaw_check.py
(same shapes, same deterministic Tower construction => same instances).
FRESH rows (this supplement's own; not in the sealed roster nor the
strata-probe roster; shapes chosen for E2 >= 8 duty):
  Y (1; 4,1,1; 2,1,1)  E2=8   g0=1, e0=4: Case-II-live shapes in mixed
                              products; E2 >= 8 duty
  Z (1; 2,1,1; 5,2,1)  E2=10  e1=5, h1=2: nontrivial outer Bezout (l1=3);
                              E2 >= 8 duty, largest table (100 entries)
All rows over all four rings {Z_2, Z_3, F_2[[t]], F_3[[t]]}  =>  40 families.

========================= PREREGISTERED PREDICTIONS ===========================
COR-4 is PROVED (ITERLAW_2026-08-08.md S6.4: phi_{gamma+E2} = pi*phi_gamma
exactly; all s-values and carries depend only on residues mod E2), so:
M1  mixed block W2xW1 == base table W1xW1 entrywise.        PREDICTED: 0.
M2  mixed block W1xW2 == base table W1xW1 entrywise.        PREDICTED: 0.
M3  mixed block W3xW1 == base table W1xW1 entrywise.        PREDICTED: 0.
M4  mixed block W1xW3 == base table W1xW1 entrywise.        PREDICTED: 0.
M5  fresh-window mixed blocks W4xW1 and W1xW4 == base table (W4 = W1 + m*E2,
    m drawn per family from [2,50]\\{7}, seed 20260808).     PREDICTED: 0.
CF  every mixed-block value == the ITER-LAW closed form evaluated at the
    ACTUAL (unreduced) mixed arguments.                     PREDICTED: 0.
CERT-Y/Z  tower-data certification of the two fresh rows only (T1_T2 nf=6,
    T5, T11+PARI on Z_p) — sealed rows were certified by the sealed run.
                                                            PREDICTED: 0.
DETERMINISTIC: random.seed(20260808) (own seed; sealed seed was 20260825).
EXACT arithmetic only.  Exit 0 iff all families GREEN.
JSON: iterlaw_cor4_mixed_results.json.
"""
import random, sys, os, time, json

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import grb_order2_check as G
from grb_order2_check import Tower, pmul
import strata_probe as SP

VIOL = []
COUNTS = {}
def note(fam, n=1): COUNTS[fam] = COUNTS.get(fam, 0) + n
def viol(fam, tag, detail): VIOL.append((fam, tag, detail))

# Rows P..X transcribed from the sealed iterlaw_check.py ROWS (attribution
# above); Y/Z are this supplement's fresh rows.
ROWS = [
    ("P", 1, (3,2,1), (2,1,1)),
    ("Q", 2, (4,3,1), (2,1,1)),
    ("R", 1, (2,1,2), (2,1,1)),
    ("S", 1, (3,1,2), (2,1,2)),
    ("U", 1, (2,3,2), (3,2,1)),
    ("V", 1, (1,1,2), (2,1,2)),
    ("W", 1, (3,1,1), (1,1,2)),
    ("X", 2, (2,1,1), (2,1,2)),
    # fresh rows (this supplement only):
    ("Y", 1, (4,1,1), (2,1,1)),
    ("Z", 1, (2,1,1), (5,2,1)),
]
FRESH = {"Y", "Z"}
CONFIGS = [("Zp", 2), ("Zp", 3), ("Fpt", 2), ("Fpt", 3)]

def closed_form(C, ga, gb):
    """Transcribed from the sealed iterlaw_check.py closed_form() (which is
    itself an independent transcription of the note's S5 display)."""
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

def run_tower(T, results):
    C = SP.Composite(T)
    E2, G0 = T.E2, None
    G0 = C.Gamma0
    # window schedule: W1/W2/W3 as in the sealed falsifier; W4 fresh (own seed)
    m4 = random.choice([m for m in range(2, 51) if m != 7])
    wins = {k: list(range(G0 + off*E2, G0 + (off+1)*E2))
            for k, off in (("W1", 0), ("W2", 1), ("W3", 7), ("W4", m4))}
    W1 = wins["W1"]

    def table(A, B):
        return {(r, s): C.cocycle(A[r], B[s])[0]
                for r in range(E2) for s in range(E2)}

    t_base = table(W1, W1)
    blocks = [("M1", "W2", "W1"), ("M2", "W1", "W2"),
              ("M3", "W3", "W1"), ("M4", "W1", "W3"),
              ("M5", "W4", "W1"), ("M5", "W1", "W4")]
    for fam, na, nb in blocks:
        A, B = wins[na], wins[nb]
        t = table(A, B)
        for k in t_base:
            note(fam)
            if t[k] != t_base[k]:
                viol(fam, T.tag, f"mixed-block rep-dependence {na}x{nb} at {k}")
            # CF: closed form at the ACTUAL mixed arguments
            note("CF")
            r, s = k
            cf, _ = closed_form(C, A[r], B[s])
            if cf is None or t[k] != cf:
                viol("CF", T.tag, f"closed-form mismatch {na}x{nb} at {k}")
    results["m4_offset"][T.tag] = m4

def main():
    t0 = time.time()
    random.seed(20260808)
    sys.path.insert(0, os.path.expanduser(
        '~/.local/lib/python3.10/site-packages'))
    try:
        import cypari2
        pari = cypari2.Pari(); pari.allocatemem(1 << 28, silent=True)
    except Exception as exc:
        pari = None
        print(f"WARNING: cypari2 unavailable ({exc}); CERT/T11 leg on fresh "
              "rows skipped -> RED if predicted")
    results = {"m4_offset": {}}
    # ---- CERT on the FRESH rows only (sealed rows certified by the seal) ----
    gv0 = len(G.VIOL)
    gc0 = sum(G.COUNTS.get(k, 0) for k in ("T1", "T2", "T5", "T11"))
    for kind, p in CONFIGS:
        for tag, d0, r0, r1 in ROWS:
            if tag not in FRESH: continue
            T = Tower(kind, p, d0, r0, r1, f"{kind},p={p},{tag}")
            G.T1_T2(T, nf=6)
            G.T5(T)
            G.T11(T, pari)
    cert_viol = len(G.VIOL) - gv0
    cert_n = sum(G.COUNTS.get(k, 0) for k in ("T1", "T2", "T5", "T11")) - gc0
    print(f"[{time.time()-t0:6.1f}s] CERT (fresh rows Y/Z only) done: "
          f"{cert_viol} violations ({cert_n} samples)")
    # ---- mixed blocks on all 40 families ----
    for kind, p in CONFIGS:
        for tag, d0, r0, r1 in ROWS:
            T = Tower(kind, p, d0, r0, r1, f"{kind},p={p},{tag}")
            run_tower(T, results)
        print(f"[{time.time()-t0:6.1f}s] ring ({kind},p={p}) done: "
              f"cumulative violations = {len(VIOL)}")
    # ------------------------------- report ---------------------------------
    print()
    print("=" * 78)
    print("PREDICTED vs OBSERVED (violation counts; samples in parentheses)")
    print("=" * 78)
    fams = [
        ("M1", "mixed block W2xW1 == base W1xW1              "),
        ("M2", "mixed block W1xW2 == base W1xW1              "),
        ("M3", "mixed block W3xW1 == base W1xW1              "),
        ("M4", "mixed block W1xW3 == base W1xW1              "),
        ("M5", "fresh-window mixed W4xW1 & W1xW4 == base     "),
        ("CF", "closed form at actual mixed arguments        "),
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
    print(f"CERT fresh rows Y/Z (T1/T2/T5/T11+PARI)              "
          f"pred 0  obs {cert_viol:5d} ({cert_n:6d})  {cert_verdict}")
    if VIOL:
        print(f"{len(VIOL)} VIOLATIONS (first 30):")
        for v in VIOL[:30]:
            print("  ", v)
    total = sum(COUNTS.values()) + cert_n
    print(f"W4 offsets drawn (family -> m): "
          f"{sorted(set(results['m4_offset'].values()))} (per-family in JSON)")
    print(f"TOTAL samples: {total}   elapsed {time.time()-t0:.1f}s")
    print(f"VERDICT: {'ALL GREEN' if all_green and not VIOL else 'RED — see above'}")
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "iterlaw_cor4_mixed_results.json"), "w") as fh:
        json.dump(dict(violations=[list(v) for v in VIOL], counts=COUNTS,
                       cert_violations=cert_viol, cert_samples=cert_n,
                       total_samples=total, seed=20260808,
                       m4_offsets=results["m4_offset"]), fh, indent=1,
                  default=str)
    return 0 if (all_green and not VIOL) else 1

if __name__ == "__main__":
    sys.exit(main())
