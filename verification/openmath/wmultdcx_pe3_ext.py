#!/usr/bin/env python3
"""wmultdcx_pe3_ext.py — PE3 (round-3) spot instrument.

Charge 3 leg: spot-re-derive sealed PID-MAX divergence records via the
committed independent machinery (wmultdcx_pe1_ext.py, consumed READ-ONLY),
on instances neither PE1 (8 detailed) nor PE2 (W3NEST/W3FTOP) audited:

  * W3G2B (1067,1067) — g0 = 2, d0 = 2 tower (never spot-audited);
                         sealed: level 1 maxnz 1 > c 0.
  * W4DEEP (1483,1483) — m = 4 depth tower (never in a detailed list);
                         sealed: level 1 maxnz 3 > c 2.

PE3's hand derivations (in WMULTDCX_passPE3_report.md, done BEFORE this
script ran) fix the expected gamma-chain / u-chain / splits / pools /
carries; this script confirms the tree-level maxima, the sealed records,
and the W-D4/W-D6(P-divisor)/W-D6c bookkeeping on the same instances.

Hand values (PE3):
  W3G2B : gamma = (1, 14, 87, 349)  [w1Phi1 = e0*g0*h0 = 4;
          w_{j+1}Phi_{j+1} = e_j*g_j*gamma_{j+1}];
          u = {1: 39, 2: 131, 3: 349}, su = {1: 1, 2: 1, 3: 1};
          split(1067) = (s1..s4) = (0, 2, 1, 1), tail 18; sigma = (0, 4, 2);
          pools = (1, 5) -> cs = [0, 1]; D = 3, kdef = 1, clause 4 >= 4 live;
          P-divisor pools (P0 = 4, P1 = 3): cP = (0, 1) -> the level-1
          divergent mass MUST ride an excess channel (W-D6c at g0 = 2).
  W4DEEP: gamma = (1, 7, 29, 117, 469);
          u = {1: 44, 2: 88, 3: 176, 4: 469}, su = {1: 2, 2: 0, 3: 0, 4: 1};
          split(1483) = (2, 1, 1, 1, 1), tail 12; sigma = (4, 2, 2, 2);
          pools -> cs = [2, 2, 2]; D = 3, kdef = 1, clause 5 >= 4 live;
          W-D7(i) hand: a = (1, 1, 1), b = (1, 1, 1), a + b = cs  OK.
"""
import sys, os, json

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import wmultdcx_pe1_ext as X
import rmengine_pe_reimpl as PE

TARGETS = [
    ("W3G2B", (1067, 1067)),
    ("W4DEEP", (1483, 1483)),
]

HAND = {
    ("W3G2B", (1067, 1067)): dict(u={1: 39, 2: 131, 3: 349},
                                  su={1: 1, 2: 1, 3: 1},
                                  cs=[0, 1], D=3, kdef=1, live=True),
    ("W4DEEP", (1483, 1483)): dict(u={1: 44, 2: 88, 3: 176, 4: 469},
                                   su={1: 2, 2: 0, 3: 0, 4: 1},
                                   cs=[2, 2, 2], D=3, kdef=1, live=True),
}


def main():
    sealed = json.load(open(os.path.join(HERE, "wmultdcx_stress_results.json")))
    sealed_div = [(d[1], tuple(d[2]["key"]), d[2]["level"], d[2]["maxnz"],
                   d[2]["c"]) for d in sealed["pid_divergences"]]
    ROSTER = {s[0]: s for s in __import__("wmultdcx_stress").ROSTER}

    print("== PE3 spot instrument (rides PE1's independent machinery) ==")
    bad = 0
    for tag, key in TARGETS:
        spec = ROSTER[tag]
        E = PE.Eng(spec[1], spec[2], spec[3], spec[4], spec[5], tag)
        PE.prep(E)
        _, su = X.my_uchain(E)
        prin = tuple(su[l + 1] for l in range(E.m))
        rec = X.run_instance(E, prin, key[0], key[1], verbose=True)
        hd = HAND[(tag, key)]
        print(f"\n  {tag} {key}: u={rec['u']} su={rec['su']} cs={rec['cs']} "
              f"D={rec['D']} kdef={rec['kdef']} live={rec['live']} "
              f"track={rec['track']} ncells={rec['ncells']}")
        hu = {k: rec['u'][k] for k in hd['u']}
        hs = {k: rec['su'][k] for k in hd['su']}
        okh = (hu == hd['u'] and hs == hd['su'] and rec['cs'] == hd['cs']
               and rec['D'] == hd['D'] and rec['kdef'] == hd['kdef']
               and rec['live'] == hd['live'])
        print(f"    HAND-DERIVATION TIE (u-chain/su/pools/D/kdef/live): "
              f"{'OK' if okh else 'MISMATCH'}")
        if not okh:
            bad += 1
            print(f"    hand: {hd}")
        sd = [d for d in sealed_div if d[0] == tag and d[1] == key]
        print(f"    MY maxnz per level: {rec['maxnz']}")
        if not sd:
            bad += 1
            print("    NO sealed divergence record found for this key!")
        for d in sd:
            lvl, mx, c = d[2], d[3], d[4]
            ok = (rec["maxnz"][lvl - 1] == mx and rec["cs"][lvl - 1] == c
                  and mx > c)
            print(f"    sealed divergence level {lvl}: maxnz {mx} > c {c}  "
                  f"-> MY verdict: {'CONFIRMED' if ok else 'MISMATCH'}")
            if not ok:
                bad += 1
        print(f"    W-D4 fails: {rec['wd4_fail']}  W-D6 fails: "
              f"{rec['wd6_fail']}  W-D6c fails: {rec['wd6c_fail']}  "
              f"beyond-floor cells: {rec['beyond']} "
              f"(on dead rows: {rec['beyond_dead']})")
        if rec['wd4_fail'] or rec['wd6_fail'] or rec['wd6c_fail']:
            bad += 1
    print(f"\nPE3 SPOT VERDICT: {'ALL CONFIRMED' if bad == 0 else f'{bad} MISMATCHES'}")
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
