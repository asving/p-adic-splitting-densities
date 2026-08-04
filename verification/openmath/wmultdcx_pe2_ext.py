#!/usr/bin/env python3
"""wmultdcx_pe2_ext.py — PE2 (round-2) spot instrument.

Charge item 3 leg: spot-re-derive sealed PID-MAX divergences with the
PE1 independent machinery (wmultdcx_pe1_ext.py, consumed READ-ONLY), on
instances PE1 never ran in detail:

  * W3NEST (295,295)  — sealed: level 1 maxnz 2 > c 1; level 2 maxnz 3 > c 2
  * W3FTOP (77,77)    — sealed: level 1 maxnz 2 > c 1; level 2 maxnz 3 > c 2
                         (flat-top e_2 = 1, D = 0, kdef = 2 row)

(4 of the 72 sealed divergence records; both towers absent from PE1's
8-instance detailed list.)  PE2's hand derivations (in the PE2 report) fix
the expected u-chain / pools / carries; this script confirms the tree-level
maxima and the W-D4/W-D6/W-D6c bookkeeping on the same instances, and
verifies the sealed records exactly.
"""
import sys, os, json

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import wmultdcx_pe1_ext as X
import rmengine_pe_reimpl as PE

TARGETS = [
    ("W3NEST", (295, 295)),
    ("W3FTOP", (77, 77)),
]

# PE2 hand-derived expectations (see WMULTDCX_passPE2_report.md):
HAND = {
    ("W3NEST", (295, 295)): dict(u={1: 15, 2: 35, 3: 93}, su={1: 1, 2: 1, 3: 1},
                                 cs=[1, 2], D=3, kdef=1, live=True),
    ("W3FTOP", (77, 77)):   dict(u={1: 9, 2: 23, 3: 23}, su={1: 1, 2: 1, 3: 0},
                                 cs=[1, 2], D=0, kdef=2, live=True),
}


def main():
    sealed = json.load(open(os.path.join(HERE, "wmultdcx_stress_results.json")))
    sealed_div = [(d[1], tuple(d[2]["key"]), d[2]["level"], d[2]["maxnz"],
                   d[2]["c"]) for d in sealed["pid_divergences"]]
    ROSTER = {s[0]: s for s in __import__("wmultdcx_stress").ROSTER}

    print("== PE2 spot instrument (rides PE1's independent machinery) ==")
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
        # hand-derivation tie
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
        # sealed-record tie
        sd = [d for d in sealed_div if d[0] == tag and d[1] == key]
        print(f"    MY maxnz per level: {rec['maxnz']}")
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
              f"beyond-floor cells: {rec['beyond']}")
        if rec['wd4_fail'] or rec['wd6_fail'] or rec['wd6c_fail']:
            bad += 1
    print(f"\nPE2 SPOT VERDICT: {'ALL CONFIRMED' if bad == 0 else f'{bad} MISMATCHES'}")
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
