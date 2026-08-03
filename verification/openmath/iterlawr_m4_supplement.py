#!/usr/bin/env python3
"""iterlawr_m4_supplement.py — the m4 TEETH SUPPLEMENT to the sealed
ITER-LAW-r probe (prereg S4b bracket in ITERLAWR_PROBE_2026-08-08.md; the
unit's one allowed additional sealed cycle).  The sealed runner
iterlawr_probe.py is BYTE-UNTOUCHED and imported as a module; the CANDIDATE
LAW IS IDENTICAL — this supplement adds only mutation-m4 detection power.

Diagnosis being cured (main run, exit 1): mutation m4 (delta3 computed with
modulus e1 instead of e2) scored 0 detections because every m4-teeth tower
of the reduced battery (rows B/D/E/F, all g2 = 1) has zbar = 1: pick_irr3
returns psi2 = y - 1 over K2 = F_p there, so the top letter is trivial and a
wrong zbar-EXPONENT is field-invisible.  (The delta3 modulus is still pinned
STRUCTURALLY by the sealed G2 top-slot shape clause nz == [d3] on all 13,440
pairs, including e1 != e2 rows D/F/L.)  Cure: rows with e1 != e2 AND g2 = 2
(zbar a root of an irreducible quadratic, hence zbar != 1 ALWAYS):

    M4A (1; 2,1,1; 3,1,1; 2,1,2)   e1=3 != e2=2, K3 = F_{p^2}
    M4B (1; 2,1,1; 2,1,1; 3,2,2)   e1=2 != e2=3, h2=2, K3 = F_{p^2}

over all four rings (8 towers).  PREREGISTERED (sealed pre-run, commit A):
  S1  the full sealed per-tower battery (run_tower VERBATIM from the sealed
      module: F0a/G1-G7 + meters) on both rows:      PREDICTED 0 violations.
  S2  m4 detection (the sealed mutation transcribed verbatim, only the
      roster changed): d3m = floor((s3+s3')/e1); on pairs with d3m != d3 the
      mutated value zbar^{d3m} z2^{D2} z1^{D1} must differ from the measured
      cocycle:                     PREDICTED >= 1 detection on EACH tower.
  S3  m4 divergence-pair coverage (d3m != d3):  PREDICTED > 0 on each tower.
Seed 20260904 (fresh).  Exit 0 iff S1 = 0 violations and S2/S3 met on 8/8.
JSON: iterlawr_m4_supplement_results.json.
"""
import random, sys, os, time, json

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import iterlawr_probe as IP          # the SEALED module, byte-untouched
from strata3_probe import Tower3

SUPP_ROWS = [
    ("M4A", 1, (2,1,1), (3,1,1), (2,1,2)),
    ("M4B", 1, (2,1,1), (2,1,1), (3,2,2)),
]

def main():
    t0 = time.time()
    random.seed(20260904)
    results = {"meters": {}, "Gamma0": {}, "rowG_valuesets": {},
               "m4": {}}
    detect = {}
    for kind, p in IP.CONFIGS:
        for tag, d0, r0, r1, r2 in SUPP_ROWS:
            full = f"{kind},p={p},{tag}"
            T3 = Tower3(kind, p, d0, r0, r1, r2, full)
            # S1: the sealed battery, verbatim
            IP.run_tower(T3, results)
            # S2/S3: the sealed m4 mutation, verbatim, on W1xW1
            C = IP.Composite3(T3)
            T = T3.T; K3 = C.K3
            W1 = list(range(C.Gamma0, C.Gamma0 + T3.E3))
            det = div = 0
            for ga in W1:
                for gb in W1:
                    cval = C.cocycle(ga, gb)[0]
                    cst = C.constants(ga, gb)
                    s3a = C.split(ga)[0]; s3b = C.split(gb)[0]
                    d3m = (s3a + s3b)//T.e1
                    if d3m != cst["d3"]:
                        div += 1
                        val = K3["mul"](K3["pow"](C.zbar, d3m),
                              K3["mul"](K3["pow"](C.z2_3, cst["D2"]),
                                        K3["pow"](C.z1_3, cst["D1"])))
                        if val != cval:
                            det += 1
            detect[full] = (det, div)
            results["m4"][full] = dict(detected=det, divergent=div)
            print(f"[{time.time()-t0:6.1f}s] {full}: m4 detected {det} "
                  f"on {div} divergence pairs")
    print()
    viols = len(IP.VIOL)
    s1 = "GREEN" if viols == 0 else "RED"
    print(f"S1 sealed battery on M4A/M4B: pred 0  obs {viols} "
          f"({sum(IP.COUNTS.values())} samples)  {s1}")
    ok23 = all(d >= 1 and v > 0 for d, v in detect.values()) \
           and len(detect) == 8
    print(f"S2/S3 m4 detection >= 1 + coverage > 0 on 8/8 towers: "
          f"{'MET' if ok23 else 'MISS'}")
    if IP.VIOL:
        for v in IP.VIOL[:20]: print("  ", v)
    if IP.HARNESS_EVENTS:
        print("HARNESS EVENTS:", IP.HARNESS_EVENTS)
    ok = viols == 0 and ok23 and not IP.HARNESS_EVENTS
    print(f"SUPPLEMENT VERDICT: {'ALL GREEN' if ok else 'RED/MISS'}   "
          f"elapsed {time.time()-t0:.1f}s")
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
              "iterlawr_m4_supplement_results.json"), "w") as fh:
        json.dump(dict(violations=[list(v) for v in IP.VIOL],
                       counts=IP.COUNTS, m4=results["m4"],
                       meters=results["meters"], Gamma0=results["Gamma0"],
                       harness_events=IP.HARNESS_EVENTS),
                  fh, indent=1, default=str)
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
