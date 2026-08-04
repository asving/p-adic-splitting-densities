# WMULTDCX_STRESS — sealed adversarial battery: countermodel hunt on the pool-floor LAW-DCX-(m+1) BEFORE any proof attempt (the W-MULT-DCX unit, countermodel-first phase)

Runner of record: `verification/openmath/wmultdcx_stress.py` (sealed with
this note at commit 1, run AFTER the seal; verdict = commit 2 from
artifacts).  A violation of the law on any battery pair is a COUNTERMODEL
and a unit SUCCESS, reported with its full pool trace.  A divergence of
the pool IDENTIFICATION instrument is equally a unit product (the
composite law can mask compensating errors; the identification is the
real target).

## S0. Authority, provenance, consumption

Charge: the (W-MULT-DCX) unit inherits RMENGINE S6.2/S7.2 as design input
(RMENGINE_2026-08-08.md S11 queue); this phase stresses the LAW before
the proof unit consumes it.  The object: LAW-DCX-(m+1) as displayed at
RMENGINE S6.1 — pools/carries

    u_m := gamma_{m+1};  u_{l-1} := (u_l - s_l(u_l)*gamma_l)/e_{l-1}
    pool_1 := (s_1+s_1') + s_1(u_1);            c_1 := |_ pool_1/e_0 _|
    pool_l := (s_l+s_l') + s_l(u_l) + c_{l-1};  c_l := |_ pool_l/e_{l-1} _|
    DCX_{m+1} = TRACK  AND  (s_m+s_m') + s_m(u_m) + c_{m-1} >= 2 e_{m-1},
    TRACK := (s_{m+1} = s_{m+1}' = e_m - 1) AND E1IH != 0.

Evidence going in: m=1 PROVED ([IL3]); m=2 SEALED-CONFIRMED conjecture
(DCX3 v2, 0/11,808 after v1 was REFUTED by the deficit-2 stratum — the
carry cap at 1 died on the first fresh deep-pool shapes); m>=3
census-grade only (D5 896/896; PE 2,208/0).  The pool identification
("the maximal promotion count into level l is |_ pool_l/e_{l-1} _|") is
RM-GEN S8 row 11c: HEURISTIC, conjecture-supported, NOT derived.

Consumption, all read-only and byte-untouched: `rmengine_pe_reimpl.py`
(Eng/prep imported; its own law census `law_leg` used ONLY as a
consistency tie), the sealed harness chain underneath it
(`grb_order2_check`, `strata3_probe`, `iterlawr_probe`, `iterlaw4_probe`,
`iterlawn_diag`), and the committed artifacts
`rmengine_pe_reimpl_results.json` (tie leg).  The law census in the
runner is an independent reimplementation from the S6.1 display; the
measured side is the diag-D5 operationalization (full locus clause per
pair, Q1 computed for every E1IH != 0 pair — NOT gated on TRACK first).

## S1. What the battery attacks (the corners no prior evidence touched)

* **A — double-nested carries.** c_1 > 0 AND c_2 > 0 simultaneously,
  including c_1 = 2 deep pools (e_0 in {3,4}, s_1(u_1) in {2,3}).  Every
  prior m=3 live row had single nesting (D5: c_2 > 0 always, c_1 > 0 on
  3/12/18 rows, maxc 1 except M3B's lone c_2 = 2 row).
* **B — top-deficit strata at m >= 3.** Direct top mass D = 2e-2
  (deficit-2: liveness rides c_{m-1} = 2 exactly), D = 2e-1 (deficit-1),
  and the just-miss dead edge top = 2e-1.  The m=2 analogue of the
  deficit-2 stratum is what killed candidate v1; it has NEVER been
  realized at m >= 3 (design meter: >= 60 predicted deficit-2 rows).
* **C — flat interior levels (e_i = 1, d_0 = 1).** s == 0 at flat reads,
  so pools degenerate to carry pass-through; shapes where the law is
  DECIDED BY THE CARRY ALONE: W3FTOP (e = (2,2,1,2): law = TRACK and
  c_2 >= 2), W3FDBL (e = (3,1,1,2): law = TRACK and c_1 >= 2 through
  two flat levels).  The prior flat law census was 16 + 64 pairs with
  live 0 + 3.
* **D — threshold edges.** pool_l at exact multiples of e_{l-1}; direct
  rows kdef <= 0 at m=3 (e_2 = 3 — none existed in ANY prior m=3 data);
  top exactly 2e (edge-live) and 2e-1 (must-die).
* **E — g_0 >= 2.** The pool divisor is the LITERAL e_{l-1}, not
  e_{l-1} g_{l-1} (sealed at m=2 only: DS7/EX3).  First m=3 stress:
  W3G2A (e_0 = 3, g_0 = 2, d_0 = 1, deep pool), W3G2B (d_0 = 2), W3G2P5
  (p = 5, d_0 = 2).
* **F — m=4 (LAW-DCX-5).** Prior data: M4A only (maxc = 1, no deficits,
  no nesting depth).  Here: triple nesting c_1, c_2, c_3 > 0 (design
  meter 182 rows on W4DEEP), c_1 = 2 at m=4, a flat interior level, and
  the first eq-characteristic LAW-DCX-5 data (W4NESTF, F_2[[t]]).
* **G — both residue characteristics** (Z_3, Z_5, F_2[[t]]).

Roster: 18 battery towers + 2 consistency replicas (XM3A/XM3B), frozen
from a 49-candidate integer design scan (`wmultdcx_stress_design.json`;
h-tracks tuned for s_l(u_l) leverage exactly as the DCX3 EX-roster
retune).  ~13k pairs total.

## S2. The pool-identification instrument (leg 3 — the heuristic hit directly)

Two-stage promotion-tracking reduction tree (the DCX3 TraceTree lifted to
level m): stage 1 reduces a*a' seeded with the FORMAL anchor-exponent
cell (b = pi^(u_1+u_1'), j = sA+sB — NOT the dev of the product
polynomial, whose Phi-adic re-expansion fakes untracked promotions; this
was caught and fixed at smoke on the committed replicas), stage 2 reduces
E1IH*Chat_m seeded per (exit-cofactor x Chat d-cell) with promotion
counts pc_l inherited.  Exact linear bookkeeping: both stages must
reassemble the canonical divisions (verdict leg).  Q1 is split into
promotion-profile parts; per traced instance:

* **PID-MAX** (row 11c literally): no NONZERO Q1 part carries
  pc_l > c_l (l = 1..m-1).
* **PID-DEF** (DCX3 C2 one level up): live row with top deficit
  k = 2e_{m-1} - D >= 1 ==> every nonzero Q1 part has pc_{m-1} >= k.
* **PID-DIR** (DCX3 C3): direct live rows carry a nonzero pc_{m-1} = 0
  part (census).

Working predictions, disclosed (NOT seals — the identification is
heuristic-grade): 0 divergences at g_0 = 1; NO prediction at g_0 >= 2 —
first mechanism data there, and the smoke run on the ALREADY-COMMITTED
XM3B (d_0 = 2, g_0 = 2) already shows PID-MAX divergences (c_1 = 0 rows
whose Q1 carries a pc_1 = 1 part — rebuild-path mass), disclosed
pre-seal.  Traced: track rows dedup'd by split key, capped 40/tower
(14 at m=4), live + edge-dead + nested prioritized.

## S3. Preregistered legs, predictions, controls (all law-keyed)

* **LAW-DCX-4 / LAW-DCX-5 lines** (one per m): law == meas pairwise,
  BOTH inclusions, every window pair.  The law is conjecture-grade at
  m >= 3: prediction FROM the conjecture is 0 violations; any violation
  = COUNTERMODEL FOUND (unit success), full pool trace dumped.
* **STRUCT** (predicted-0): u-chain in Z_{>=0}; L-CAP c_l <= 2.
* **CONS** (predicted-0): PID stage trees == canonical divisions (all
  four reassemblies per trace); my census == PE.law_leg fresh AND ==
  committed rmengine_pe_reimpl_results.json on XM3A/XM3B; zero harness
  events.
* **PID legs** as in S2.
* **CONTROLS (teeth; SEPARATE verdict; each must trip >= 1 pair or
  CONTROL FAILURE):** CAP1 (carry capped at 1 — the refuted-v1 pattern),
  NOCARRY (top carry deleted), EG (divisor e*g), THRP1/THRM1 (threshold
  +-1), NOU (u-chain terms deleted).  Design scan verified each differs
  from the primary on battery rows.
* **COVERAGE meters:** nested12 >= 20, c1eq2 >= 10, justmiss_top >= 10,
  flat_pass >= 5 (+ deficit2live and nested123 reported).

## S4. Fences

1. GREEN everywhere does NOT upgrade the law: it stays conjecture at
   every m >= 2 (instance evidence on the probed class only).  This unit
   proves nothing; it hunts.
2. PID divergences refute (or scope) the ROW-11c IDENTIFICATION reading
   they test, not the composite law (the LAW lines own the law).
3. No claim off the probed windows/shapes; no claim at g_m >= 2; the
   d_0 >= 2 flat corners (off amended T-scope) stay untouched.
4. Harness-level assertion failures are HARNESS EVENTS, not law verdicts.
5. Design disclosure: the pre-seal `--design` scan used tower data +
   E1IH-side track censuses + INTEGER law-side strata only (no Q1, no
   meas, no PID) — the DCX3 design convention; plus the disclosed smoke
   run on the two committed replica shapes only.

## S5. VERDICT (commit 2, from the artifacts) — PENDING AT SEAL
