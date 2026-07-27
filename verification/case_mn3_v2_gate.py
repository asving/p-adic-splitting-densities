#!/usr/bin/env python3
"""case_mn3_v2_gate.py — CASE-MN3 V2 threshold re-seal census (p=3, N=1..7).

Seal: CASE_MN3_V2_SEALED_PREDICTIONS.md (committed BEFORE this script).
Engine: imported UNCHANGED from case_mn3_gate (the v1 gate). This script only
adds the v2 evaluation: per-level realized set == {field-size pass, N* <= N},
sharpness (absence below threshold), 5 first-appearance counts, content checks.
Run: uv run --with numpy python3 case_mn3_v2_gate.py <N>   (one level per run)
     uv run --with numpy python3 case_mn3_v2_gate.py verdict
Long output -> /tmp/mn3v2_census.out (append); JSON -> results/case_mn3_v2_results.json
"""
import json, os, sys, time
from case_mn3_gate import (build_catalogue, excluded_letters, census,
                           sealed_target, lname, GROUPW)

HERE = os.path.dirname(os.path.abspath(__file__))
OUTPATH = '/tmp/mn3v2_census.out'
JSONPATH = os.path.join(HERE, 'results', 'case_mn3_v2_results.json')
P = 3


def nstar(k):
    """The SEALED per-letter threshold table (S1 of the v2 seal), p = 3."""
    G, e, l, a, fl, fr, lam, sel = k
    if G == 'R':
        if e >= 2:
            return 2
        if l == 3:
            return 1
        if l == 2:
            return 1 if a == 1 else 3
        if a == 0:
            return 2 if fr == (2,) else 4
        return 3 if a == 1 else (2 if fl == (2,) else 3)
    if G == 'Q3':
        if e == 3:
            return 2
        if e == 2:
            return 5 if fr == (1,) else 2
        if l == 3:
            return 4
        if l == 2:
            return 6 if a == 0 else 4
        if a == 0:
            return 3 if fr == (2,) else 7
        return 6 if a == 1 else (5 if fl == (2,) else 6)
    if G == 'Q2':
        if e == 2:
            return 2
        return 3 if l == 2 else (4 if a == 0 else 3)
    return 2                                      # Q1 and the four I letters


# P3 first-appearance counts: (letter, N*, sealed count); bonus flagged.
P3 = [(('R', 1, 2, 1, (1,), (), ((2, 1),), (2, 1)), 1, 3, 'a'),
      (('R', 3, 1, 0, (), (), ((1, 1),), (1, 1)), 2, 18, 'b'),
      (('R', 2, 1, 0, (), (1,), ((1, 1),), (1, 1)), 2, 36, 'c'),
      (('R', 1, 1, 0, (), (2,), ((1, 1),), (1, 1)), 2, 108, 'd'),
      (('Q3', 3, 1, 0, (), (), ((1, 1),), (1, 1)), 2, 36, 'e'),
      (('R', 1, 1, 1, (1,), (1,), ((1, 1),), (1, 1)), 3, 108, 'bonus')]
LOOP_Q2 = ('Q2', 1, 2, 0, (), (), ((1, 2),), (1, 2))
LOOP_Q3 = ('Q3', 1, 3, 0, (), (), ((1, 3),), (1, 3))


def run_level(N):
    cat = build_catalogue()
    catset = set(cat)
    excl = excluded_letters(cat, P)
    assert len(excl) == 2
    res = census(P, N, catset)
    realized = {k for k in catset if res['hits'].get(k, 0) > 0}
    predicted = {k for k in catset if k not in excl and nstar(k) <= N}
    early = sorted(lname(k) for k in realized - predicted)   # V1 falsifier
    missing = sorted(lname(k) for k in predicted - realized)  # V2 falsifier
    offmenu = [(lname(a), lname(b), n) for (a, b), n in res['trans'].items()
               if b[0] != sealed_target(a)]
    loopseal = ({LOOP_Q2} if N >= 3 else set()) | ({LOOP_Q3} if N >= 4 else set())
    loops = {k for k in realized if k[0] in ('Q2', 'Q3') and k[7] != 'V'
             and k[7] == (1, GROUPW[k[0]])}
    counts = [(tag, lname(k), ns, want, res['hits'].get(k, 0))
              for k, ns, want, tag in P3 if ns == N]
    v = dict(V1_early=not early, V2_missing=not missing,
             V4_strays=not res['strays'], V4_offmenu=not offmenu,
             V4_faults=not res['faults'], V4_loops=loops == loopseal,
             V3_counts=all(w == got for _, _, _, w, got in counts))
    lines = [f'== V2 CENSUS p=3 N={N} (box 3^{3 * N} = {3 ** (3 * N)}; '
             f'{res["secs"]}s) ==',
             f'  realized {len(realized)}/53 vs predicted {len(predicted)}',
             f'  V1 early (below N*): {early or 0} -> '
             f'{"PASS" if v["V1_early"] else "FAIL"}',
             f'  V2 missing (predicted, absent): {missing or 0} -> '
             f'{"PASS" if v["V2_missing"] else "FAIL"}',
             f'  V4 strays {len(res["strays"])} offmenu {len(offmenu)} '
             f'faults {len(res["faults"])} loops {sorted(lname(k) for k in loops)}'
             f' -> {"PASS" if v["V4_strays"] and v["V4_offmenu"] and v["V4_faults"] and v["V4_loops"] else "FAIL"}',
             f'  undecided (reported): {res["undec"]}; unverified: {res["unver"]}']
    for tag, ln, ns, want, got in counts:
        lines.append(f'  V3 count ({tag}) {ln} @N*={ns}: sealed {want}, '
                     f'censused {got} -> {"PASS" if want == got else "FAIL"}')
    lines.append('  hits: ' + json.dumps(
        {lname(k): res['hits'].get(k, 0) for k in cat if res['hits'].get(k, 0)}))
    data = json.load(open(JSONPATH)) if os.path.exists(JSONPATH) else {}
    data[f'N{N}'] = dict(
        box=3 ** (3 * N), secs=res['secs'], realized=len(realized),
        predicted=len(predicted), early=early, missing=missing,
        strays={lname(k): x for k, x in res['strays'].items()},
        offmenu=offmenu, faults=res['faults'],
        loops=sorted(lname(k) for k in loops),
        counts=[(t, l, ns, w, g) for t, l, ns, w, g in counts],
        hits={lname(k): res['hits'].get(k, 0) for k in cat},
        undecided=res['undec'], unverified=res['unver'],
        verdicts={k: bool(x) for k, x in v.items()})
    os.makedirs(os.path.dirname(JSONPATH), exist_ok=True)
    json.dump(data, open(JSONPATH, 'w'), indent=1)
    with open(OUTPATH, 'a') as fh:
        fh.write('\n'.join(lines) + '\n')
    print(f'N={N}: ' + '  '.join(f'{k}:{"PASS" if x else "FAIL"}'
                                 for k, x in v.items()))
    return all(v.values())


def verdict():
    data = json.load(open(JSONPATH))
    ok = True
    for N in range(1, 8):
        d = data.get(f'N{N}')
        if d is None:
            print(f'N={N}: MISSING')
            ok = False
            continue
        ok &= all(d['verdicts'].values())
        print(f'N={N}: realized {d["realized"]}/predicted {d["predicted"]} '
              + '  '.join(f'{k}:{"P" if x else "F"}'
                          for k, x in d['verdicts'].items()))
    print('V2 GATE:', 'PASS' if ok else 'FAIL')
    return 0 if ok else 1


if __name__ == '__main__':
    if sys.argv[1] == 'verdict':
        sys.exit(verdict())
    sys.exit(0 if run_level(int(sys.argv[1])) else 1)
