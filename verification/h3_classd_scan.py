#!/usr/bin/env python3
"""H3 (ADM) carrier-lattice (CLASS-d) scan — the G-ADM-1 re-run gate — plus
the G-ADM-2 instrumentation spec (unit ADM-U5, lean/blueprints/HDISCHARGE_H3.md
sections 1.3-1.4).

PROVENANCE.  Re-homed from /tmp/h3_classd.py (the F-ADM-2 probe, machine clock
2026-08-01); computational content preserved EXACTLY (same `check`, same three
grids).  The scan transcribes the census carrier's exact wt lattice — verified
against the LANDED Lean carrier `LeanUrat.Scaffold.CensusData` + derived defs
(lean/LeanUrat/Scaffold/ValueSide/CensusCore.lean, post-ADM-U0 head):
  Vrec:    V_0 = V_1 = 0,  V_{i+2} = e_{i+1} f_{i+1} (e_{i+1} V_{i+1} + h_{i+1})
  wphi:    w(phi_0) = 0,   w(phi_i) = e_i V_i + h_i          (i >= 1)
  ledgerE: 1 at stage 0, e_i at stages i >= 1 (REVISION-3 radix)
  period:  prod_i ledgerE_i;   d: prod_i f_i
  J:       prod_i Fin(ledgerE_i) x Fin(f_i);  wt(j) = sum_i (a_i + ledgerE_i b_i) w(phi_i)
(CLASS-d) at datum D:  #{j in J : wt(j) = c mod period} = d for every class c.

G-ADM-1 (the gate this file re-runs; pinned at HDISCHARGE_H3 section 1.3(b),
finding F-ADM-2).  Pinned outcomes, asserted below — any drift exits nonzero:
  (i)   r = 1 grid, axioms-as-written (triangular AND coprime):   0 failures;
  (ii)  r = 1 grid, coprime-only:                                 0 failures;
  (iii) r = 2 grid, coprime-only:                                88 failures;
        smallest countermodel (e1,h1,e2,h2,f0,f1,f2) = (2,1,2,1,1,1,1):
        d = 1, period = 4, weights {0,1,5,6}, class counts
        {0:1, 1:2, 2:1, 3:0} (mechanism: w(phi_2) = 5 = w(phi_1) = 1 mod 4,
        the two class digits collide; class 3 empty, class 1 doubled).
Force of the finding: (CLASS-d) at r >= 2 is NOT derivable from the carrier
axioms {e,f >= 1, gcd(h_i, e_i) = 1} + the Vrec/wphi weight recursion alone —
matching O-9's own attribution ("at general order it follows from (GR-B)").
Whether the failing probe types are OM-REALIZED is NOT claimed (that is
G-ADM-2's question).  Consumers: ADM-U2 takes (CLASS-d) as a NAMED hypothesis;
ADM-U3's unconditional range is r <= 1.

FINDING-10 RE-RUN DUTY (Codex pass-1 finding 10, ACCEPTED; duty assigned to
this unit).  The countermodels refute derivability from the EXPECTED
post-ADM-U0 axiom set only.  If ADM-U0's adjudication lands a DIFFERENT axiom
set, this scan must be RE-RUN under it before the "not a carrier theorem"
conclusion is reused.  DUTY DISCHARGED AT HEAD, 2026-08-01: ADM-U0 has LANDED
(CensusCore.lean docstring "ADM-U0 REPAIR RECORD": `triangular` DROPPED;
axiom rows exactly he/hf/h_coprime) — the landed set IS the coprime-only set
grids (ii)/(iii) test, so F-ADM-2 stands under the landed carrier unchanged.
Mechanism kept live for any future carrier change: the grids take the axiom
predicate as a parameter (AXIOM_SETS below); a re-run under a new set is
`scan_r1(new_pred)` / `scan_r2(new_pred)` plus a fresh pinning of the counts.

================================================================================
G-ADM-2 INSTRUMENTATION SPEC (unit ADM-U5 deliverable 2 — the gate itself is
NOT run by this unit; HDISCHARGE_H3 section 1.3 "Numerics gates", finding 7)
================================================================================

ROLE.  G-ADM-2 is a falsifier-ROUTER, not an adjudicator (Codex pass-1
finding 7): an explicit realized PARTIAL-slot instance kills track A and fires
track B (unit ADM-U6a takes the instance as its worked gate); an all-FULL
no-hit only SUPPORTS track A — the proof burden stays with ADM-U7's
hostile-passed argument.  A no-hit is never cited as proof.

HOST.  The order-2 census harness verification/openmath/o9_order2_census_check
.py (the O-9 section-10 K1-K4 lineage) and its H2-N2 fiber machinery:
`run_n2_config(p, n, M, mins)` builds per-(parent-realization rho, marked psi)
fiber accumulators fib = {floors, joint: Counter(read-vector -> count), size,
shape=(pkey, s_idx, g, mu), ehg=(e, h)}; `n2_online_slots(floors, e, h, g,
mu)` returns the on-line slots of the fiber's floor chain.  Working-level
determinacy (beta <= e*M - 1) is already enforced upstream (CAP slots in
`n2_slot_data`).  THE HARNESS FILE IS NOT EDITED: wiring lives in a NEW runner
verification/openmath/gadm2_attainment_run.py that imports the harness and
this module.

QUANTITY LOGGED.  Abstract (the blueprint's display): the attainment profile
"dim G_{beta_k} vs d" of every realized stratum datum — per on-line slot
beta_k, is the slot value-attained FULL (read image all of F_{r+1}; the
(q^{dim G_beta} - 1)-factor slot of O-9 rev4/5 section 5.1) or PARTIAL (image
a proper nonzero subset)?  Concrete order-2 realization, in the harness's own
coordinates — for each fiber fib and each on-line slot k:
  q      := p^g                    (g = deg psi; order-2 residue field F_q)
  A_k    := {v != 0 : v in the slot-k marginal support of fib['joint']}
            (attained floor-height reads; the vec entry 0 is the
             STRICTLY-ABOVE-FLOOR class, not the digit 0 — digits are nonzero
             length-g tuples over F_p, per res1)
  n_att  := #A_k
  FULL(k)    :<=> n_att = q - 1        (every nonzero value attained)
  PARTIAL(k) :<=> 0 < n_att < q - 1    (the ROUTER predicate: any such row at
                                        any config = track A DEAD, fire ADM-U6a)
  n_att = 0 at an on-line slot: ANOMALY (pinned/vanishing read — junction /
  H2-N1 territory); logged informational, never routed on.
  subgroup_ok := A_k + {0} closed under componentwise F_p addition — the
  section-5.1 shape prediction (image an additive subgroup, so n_att + 1 a
  power of p); a False here is logged as a SHAPE anomaly for the disposition,
  it does not route.

COVERAGE (the unit's charge: n <= 5, p in {2,3,5}, N <= the harness caps).
The harness's existing 10-config battery (n <= 4, p in {2,3,5}, M <= 6, full +
restricted modes) PLUS n = 5 restricted-mode configs under the box budget
p^(sum_i (M - m_i)) <= 10^7; suggested schedule (runner may tighten to budget):
  (p, n, M, mins) = (2, 5, 6, (4,3,2,2,1)),  (3, 5, 5, (3,3,2,2,1)),
                    (5, 5, 3, (2,2,1,1,1)).
Restricted-mode soundness rides the harness's own pooling note (a stratum
fully inside the superset has the same census/fibers in any mode; the
`delta_ceils` guard).  Determinacy: only beta <= e*M - 1 slots are read (CAP
otherwise) — the harness cap IS the N-cap.

HOOK POINTS (exact; the runner imports, never edits).
  H1 extraction: for each config, fibers = run_n2_config(p, n, M, mins); for
     each ((pkey, rkey), fib): (online, ok) = n2_online_slots(fib['floors'],
     e, h, g, mu) with (e, h) = fib['ehg'], (_, _, g, mu) = fib['shape'];
     if ok: rows = attainment_profile(fib, p, online)   [this module, below];
     if not ok: tally chain_anomaly (matches the harness's own `chain` tally).
  H2 schedule: the coverage list above.
  H3 emission: gadm2_emit(rows, path) — one JSON line per (config, fiber,
     on-line slot) to verification/logs/gadm2_attainment_<UTC-stamp>.jsonl.
     Row schema (all keys always present):
       {"gate": "G-ADM-2", "p", "n", "M", "mins", "pkey": str(pkey),
        "rkey": str(rkey), "g", "mu", "e", "h", "slot", "floor_beta", "q",
        "n_att", "full": bool, "partial": bool, "anomaly_empty": bool,
        "subgroup_ok": bool, "fiber_size"}
  H4 disposition: aggregate to verification/logs/GADM2_DISPOSITION.md (the
     one-page disposition the blueprint requires; committed log + disposition
     = the gate's deliverable).  Verdict line, exactly one of:
       ALL-FULL: every logged on-line slot FULL -> track A SUPPORTED (only);
         the K7 shape remains abstract-only so far; ADM-U7 proceeds.
       PARTIAL-SLOT HIT: <first partial row verbatim> -> track A DEAD;
         ADM-U6a fires with this instance as its worked gate.
     plus tallies: fibers, slots, anomaly_empty, subgroup_ok failures, chain
     anomalies, CAP-truncated slot fraction (coverage honesty).

NON-GOALS of this unit: running G-ADM-2; editing the harness; treating a
no-hit as proof.  Reference hooks + a synthetic self-test are implemented
below (`python3 h3_classd_scan.py --selftest-gadm2`).

Run:  python3 h3_classd_scan.py                 (G-ADM-1 re-run gate; exit 0
                                                 iff all pinned counts hold)
      python3 h3_classd_scan.py --selftest-gadm2 (G-ADM-2 hook self-test)
"""
import itertools
import json
import sys
from math import gcd

# ---------------------------------------------------------------------------
# G-ADM-1: the (CLASS-d) lattice scan (verbatim re-home of /tmp/h3_classd.py)
# ---------------------------------------------------------------------------

def check(r, e, h, f):
    """Exact (CLASS-d) check at the census datum (r, e, h, f); e, h, f are
    lists of length r+1 (stage 0 first; e[0], h[0] unread by the ledger).
    Returns (ok, d, period, cls) with cls = {class c: #{j : wt(j) = c mod
    period}}; ok <=> every class count equals d and every class is attained.
    Transcribes CensusCore.lean's Vrec/wphi/ledgerE/period/J/wt exactly."""
    V = [0] * (r + 3)
    # Vrec: V0=0, V1=0, V_{i+2} = e_{i+1} f_{i+1} (e_{i+1} V_{i+1} + h_{i+1})
    for i in range(0, r + 1):
        idx = i + 2
        if i + 1 <= r:
            V[idx] = e[i + 1] * f[i + 1] * (e[i + 1] * V[i + 1] + h[i + 1])

    def wphi(i):
        if i == 0:
            return 0
        return e[i] * V[i] + h[i]

    ledgerE = [1] + [e[i] for i in range(1, r + 1)]
    period = 1
    for i in range(r + 1):
        period *= ledgerE[i]
    d = 1
    for i in range(r + 1):
        d *= f[i]
    Js = itertools.product(*[[(a, b) for a in range(ledgerE[i])
                              for b in range(f[i])] for i in range(r + 1)])
    wts = []
    for j in Js:
        wt = sum((j[i][0] + ledgerE[i] * j[i][1]) * wphi(i)
                 for i in range(r + 1))
        wts.append(wt)
    cls = {}
    for w in wts:
        cls[w % period] = cls.get(w % period, 0) + 1
    ok = all(v == d for v in cls.values()) and len(cls) == period
    return ok, d, period, cls


# Axiom sets as first-class predicates on a stage row (e_i, h_i), i >= 1 —
# the finding-10 re-run mechanism.  e, f >= 1 is enforced by the grid ranges.
AXIOM_SETS = {
    # the PRE-ADM-U0 as-built rows: triangular (e_i | h_i) AND coprime —
    # jointly degenerate (force e_i = 1 at i >= 1; finding F-ADM-1)
    'as-written': lambda e_i, h_i: (e_i == 1 or h_i % e_i == 0)
                                   and gcd(h_i, e_i) == 1,
    # the LANDED post-ADM-U0 rows (CensusCore.lean head: he/hf/h_coprime)
    'coprime-only': lambda e_i, h_i: gcd(h_i, e_i) == 1,
}


def scan_r1(pred, e1s=range(1, 5), h1s=range(1, 7), f0s=range(1, 4),
            f1s=range(1, 4)):
    """r = 1 grid under axiom predicate `pred`; returns the failure list."""
    bad = []
    for e1 in e1s:
        for h1 in h1s:
            if not pred(e1, h1):
                continue
            for f0 in f0s:
                for f1 in f1s:
                    ok, d, per, cls = check(1, [1, e1], [0, h1], [f0, f1])
                    if not ok:
                        bad.append((('r1', e1, h1, f0, f1), d, per, cls))
    return bad


def scan_r2(pred):
    """r = 2 grid (the original probe grid, verbatim ranges) under `pred`."""
    bad = []
    for e1 in range(1, 4):
        for h1 in range(1, 5):
            for e2 in range(1, 4):
                for h2 in range(1, 5):
                    if not (pred(e1, h1) and pred(e2, h2)):
                        continue
                    for f0, f1, f2 in itertools.product(range(1, 3), repeat=3):
                        ok, d, per, cls = check(2, [1, e1, e2], [0, h1, h2],
                                                [f0, f1, f2])
                        if not ok:
                            bad.append((('r2', e1, h1, e2, h2, f0, f1, f2),
                                        d, per))
    return bad


def gate_gadm1():
    """The G-ADM-1 re-run gate: reproduce the pinned counts exactly."""
    # grid (i): original as-written r=1 grid (f0 in 1..3 — original ranges)
    bad = scan_r1(AXIOM_SETS['as-written'])
    # grid (ii): original coprime-only r=1 grid had f0 in 1..2
    bad2 = scan_r1(AXIOM_SETS['coprime-only'], f0s=range(1, 3))
    # grid (iii): r=2 coprime-only
    bad3 = scan_r2(AXIOM_SETS['coprime-only'])
    print("axioms-as-written r=1 failures:", len(bad))
    print("coprime-only r=1 failures:", len(bad2))
    for x in bad2[:5]:
        print("  ", x)
    print("coprime-only r=2 failures:", len(bad3))
    for x in bad3[:8]:
        print("  ", x)
    pinned = (len(bad) == 0 and len(bad2) == 0 and len(bad3) == 88)
    # the pinned smallest countermodel and its class profile
    key0 = ('r2', 2, 1, 2, 1, 1, 1, 1)
    cm_ok = bad3 and bad3[0][0] == key0 and bad3[0][1:] == (1, 4)
    _, d0, per0, cls0 = check(2, [1, 2, 2], [0, 1, 1], [1, 1, 1])
    prof_ok = (d0, per0) == (1, 4) and \
        {c: cls0.get(c, 0) for c in range(4)} == {0: 1, 1: 2, 2: 1, 3: 0}
    print("ADM-U0 alignment: landed axiom set (CensusCore.lean head) = "
          "coprime-only = the tested set; F-ADM-2 stands (finding-10 duty "
          "discharged at head, 2026-08-01).")
    if pinned and cm_ok and prof_ok:
        print("G-ADM-1 RE-RUN GATE: PASS (pinned counts 0/0/88; smallest "
              "countermodel (2,1,2,1,1,1,1) d=1 period=4 classes "
              "{0:1,1:2,2:1,3:0})")
        return 0
    print("G-ADM-1 RE-RUN GATE: FAIL — pinned counts drifted "
          f"(got {len(bad)}/{len(bad2)}/{len(bad3)}, cm_ok={cm_ok}, "
          f"prof_ok={prof_ok}); if the carrier changed, this is the "
          "finding-10 re-run duty firing: re-pin under the landed axiom set.")
    return 1


# ---------------------------------------------------------------------------
# G-ADM-2 reference hooks (spec above; the gate run itself is NOT this unit)
# ---------------------------------------------------------------------------

def _is_subgroup(att, p, g):
    """Is att + {0} closed under componentwise F_p addition?  Digits are
    length-g tuples over F_p (res1 format); the harness's above-floor marker
    (the int 0) must NOT be passed in."""
    zero = tuple([0] * g)
    S = set(att) | {zero}
    for x in S:
        for y in S:
            if tuple((a + b) % p for a, b in zip(x, y)) not in S:
                return False
    return True


def attainment_profile(fib, p, online):
    """H1 extraction hook: per-slot attainment rows for one fiber accumulator
    (the o9_order2_census_check.py N2 format — see spec).  `online` from
    n2_online_slots.  Returns a list of dicts (schema keys minus the config
    and stratum keys, which the runner adds)."""
    _pkey, _s_idx, g, mu = fib['shape']
    e, h = fib['ehg']
    q = p ** g
    rows = []
    for k in online:
        support = {key[k] for key, c in fib['joint'].items() if c > 0}
        att = {v for v in support if v != 0}
        n_att = len(att)
        rows.append(dict(
            slot=k, floor_beta=fib['floors'][k], q=q, n_att=n_att,
            full=(n_att == q - 1), partial=(0 < n_att < q - 1),
            anomaly_empty=(n_att == 0),
            subgroup_ok=_is_subgroup(att, p, g),
            fiber_size=fib['size'], g=g, mu=mu, e=e, h=h))
    return rows


def gadm2_emit(rows, path, config, pkey, rkey):
    """H3 emission hook: append one JSON line per row, schema per spec."""
    p, n, M, mins = config
    with open(path, 'a') as fh:
        for row in rows:
            rec = dict(gate='G-ADM-2', p=p, n=n, M=M,
                       mins=list(mins) if mins else None,
                       pkey=str(pkey), rkey=str(rkey))
            rec.update(row)
            fh.write(json.dumps(rec, default=str) + '\n')


def selftest_gadm2():
    """Synthetic fiber in the harness accumulator format; known profile."""
    from collections import Counter
    p, g = 2, 2                                    # q = 4; digits: 2-tuples
    a, b, c = (1, 0), (0, 1), (1, 1)
    fib = dict(
        # slot 0: all three nonzero values attained -> FULL (n_att = 3)
        # slot 1: only {a} attained -> PARTIAL (n_att = 1); {a,0} IS closed
        # slot 2: always above floor -> anomaly_empty
        joint=Counter({(a, a, 0): 1, (b, 0, 0): 1, (c, a, 0): 2}),
        floors=[3, 5, 7], size=4,
        shape=(('pk',), 0, g, 2), ehg=(1, 1))
    rows = attainment_profile(fib, p, online=[0, 1, 2])
    exp = [dict(full=True, partial=False, anomaly_empty=False, n_att=3),
           dict(full=False, partial=True, anomaly_empty=False, n_att=1),
           dict(full=False, partial=False, anomaly_empty=True, n_att=0)]
    ok = True
    for row, ex in zip(rows, exp):
        for kk, vv in ex.items():
            if row[kk] != vv:
                print(f"  MISMATCH slot {row['slot']} {kk}: "
                      f"got {row[kk]}, want {vv}")
                ok = False
    # subgroup check: {a,b,c,0} closed (full F_4 as F_2-space); {a,0} closed;
    # and a genuinely non-closed set {a,b} (a+b=c missing) must fail
    ok &= rows[0]['subgroup_ok'] and rows[1]['subgroup_ok']
    ok &= not _is_subgroup({a, b}, p, g)
    print("G-ADM-2 hook self-test:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == '__main__':
    if '--selftest-gadm2' in sys.argv[1:]:
        sys.exit(selftest_gadm2())
    sys.exit(gate_gadm1())
