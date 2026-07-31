# TREE-COMPLETENESS AUDIT (unit TREE, 2026-08-02) — tree vs ROOT ASSEMBLY

**Charge (Phase-C leg).** Walk `docs/MATH_COMPLETION_TREE_2026-08-01.md` (original +
DELTAs 1–3, corrected readings governing) node by node against
`docs/ROOT_ASSEMBLY_2026-08-02.md` (at REVISION 3): every root-mandatory node must be
CONSUMED at a named ROOT step or EVICTED with a recorded adjudication; every eviction's
warrant cited; every node whose status the deltas changed must match the ROOT's status
ledger. Audited at repo HEAD 85670f7 (tree byte-stable since DELTA 3; ROOT unit of
record ea0336f). This is a read-only audit: no status is upgraded or downgraded here.

**Method.** Full read of both documents; per-node disposition classed as:
**CONSUMED(step)** — named at a ROOT §2 step or §3/§4 ledger row; **EVICTED(warrant)** —
off the mandatory path with the recorded adjudication cited; **CLOSED** — a settled
verdict row (proved/refuted) with no open residue for the ROOT to consume;
**GOVERNANCE** — a delta node whose content is an executed re-organization, visible in
the ROOT's structure; **ANNEX** — out of critical path by standing directive, recorded.
Status-match column: does the ROOT's displayed grade agree with the tree+deltas (or
supersede it consistently via a later named harvest)?

**Scope note.** Post-ROOT-R3 ledger events at HEAD (85670f7: O4T VERIFIED leaf #7;
O-9 r4 FULL-attainment (ADM) direction; CU-2t light r3, +1 GD-4 row, ROOT touch owed)
postdate the audited text and are NOT charged against it; they are DELTA-4/VC4 material.

---

## 1. Node-by-node table

### 1.1 Root claim + annex

| node | disposition | status match | note |
|---|---|---|---|
| (U-GEN) | CONSUMED — ROOT §1 (0)/(SQ)/(R) + "Relation to the tree's root" | ✓ | operative claim, per D1.5(a) |
| (U-DENS) | CONSUMED — ROOT §1 clause (0); one-directional U-GEN ⇒ U-DENS | ✓ | D1.5(a) downgrade reflected verbatim |
| A-1 (projective bridge) | ANNEX — ROOT §1 Relation + §3.3 (S3) row (owner annex A-1) | ✓ | standing directive; (S3) positioned at REVISION 2 |
| A-2 (L7/htameFE) | ANNEX — ROOT §3.3 final paragraph + §4 [DCD] NOT consumed | ✓ | 2026-07-21 retirement stands |

### 1.2 Literature imports

| node | disposition | status match | note |
|---|---|---|---|
| LIT-1 GMN | CONSUMED — §4 item 1 (Steps 7/8/11/12/13/14/15) | ✓ LITERATURE-CONDITIONAL (D1.5(b)); TAMS-pagination duty = §3.3 row | |
| LIT-2 Serre LF | CONSUMED — §4 item 4 (Steps 1/12/13, B-6) | ✓ | DVR clause audited; K-11 bridge named at Step 1 |
| LIT-3 coprime Hensel | CONSUMED — §4 item 5 (Step 12); numbers+Mathlib probe = §3.3 row | ✓ LITERATURE-CANDIDATE (D1.5(c)) | |
| LIT-4 OM-SAT | CONSUMED by content, NOT by id — via GMN Cor 1.20/3.8 pins (Steps 11/12) | ~ | ADVISORY A-2 below: id + its "K = ℚ_p exactly" scope caveat absent from §4 roster; K_δ re-scope rides (UB-X)(a) only generically |
| LIT-5 BNS | EVICTED — §4 "Explicitly NOT consumed"; warrant D2.4 + D3.1 (zero root-side touch-points) | ✓ route-R-QNT-only outright | |
| LIT-6 Denef–Igusa | EVICTED/out-of-path — §4 item 9: measure route ONLY, not consumed by the count-native assembly | ✓ | warrant = tree LIT-6 row itself |
| LIT-7 DCD | ANNEX — §4 NOT-consumed line (annex A-2 only) | ✓ | |
| LIT-8 (split 8a–8e) | CONSUMED — §4 item 7 (Steps 1/13/15, B-layer); per-use-site transcription = §3.3 row | ✓ D1.5(d) split reflected | |

### 1.3 Base lemmas (June skeleton)

| node | disposition | status match | note |
|---|---|---|---|
| B-1..B-7 | CONSUMED — Step 2 (grades inlined, VC1 finding 3), B-6 also Step 3; §3.2 B-layer verification row (B-1, B-2doc, B-3doc, B-4, B-5, B-6, B-7 — completed across VC1/VC2/VC3) | ✓ | the three-class completeness was restored by V2-4 + B4 |
| B-8 | SUPERSEDED — Step 2: "cited nowhere" | ✓ | matches tree §2.1 |

### 1.4 The verified core (T-layer)

| node | disposition | status match | note |
|---|---|---|---|
| T-1..T-9, T-U | CONSUMED — Step 2, with the D1.5(e)/(f) re-scopes (T-1 symbolic; T-8 formal+(REG-p)-conditional), the D-9 T-7 split (T-7s here; [1v]-FULL re-owned by O-11), TB-CAP D-12r-conditional | ✓ | Step 19 consumes T-U; §U.SQ.6 row-by-row correspondence honestly ASSERTED, §3.3 audit row (VC3 A8) |
| T-11 (JOINT-D1) | NOT NAMED in ROOT | ~ | ADVISORY A-1: tree says "accepted as part of the T-1 perimeter", so consumption is arguable via Step 2's T-1; the id itself appears nowhere (tree-§4 criterion-4 display) |

### 1.5 Kernel rows K-1..K-15

| node | disposition | status match | note |
|---|---|---|---|
| K-1 ksub, K-2 w17ii | CLOSED (PROVED/VERIFIED-LEAN, no open residue) — not named in ROOT | ✓ | Lean-interface rows; nothing left for the composition to consume; display-only absence |
| K-3 (refuted) | CLOSED; repaired math = O-6 → EVICTED route R-QNT (D1.4) | ✓ | caterpillar countermodel cited at Step 3 |
| K-4, K-6 (refuted) | repairs CONSUMED — route through D-15 (Step 6 Delivers; Step 11 Delivers) | ✓ | |
| K-5 (refuted) | CLOSED; the per-site true statement = O-1 → Step 6 | ✓ | id absent, content homed |
| K-7 (refuted) | CLOSED as refutation; repaired carrier form = O-14b → **NO HOME** | ✗ | GAP G-1 below — the repaired-math pointer dangles |
| K-8 (plausibly-false) | CLOSED; adapted-cell math = O-10 → Step 15 (D-8 guard) | ✓ | |
| K-9 cl6 | level-1 CONSUMED at Step 14 (M08 Thm 2); order ≥ 2 = O-9 (Step 14); n = 2 pack = anchor | ✓ | id absent, all three faces homed |
| K-10 cl15_align | CONSUMED via Steps 7/8 + §4 GMN Thm 4.18 pin | ✓ | id absent, content homed |
| K-11 e·f bridge | CONSUMED — Step 1 Consumes-line (K-11/M16 audited bridge) | ✓ | |
| K-12 (n = 2 drainage) | CONSUMED — §1 verified instances + §3.2 faithfulness-audit row (D1.5(g)) | ✓ grade held pending the record, as the delta requires | |
| K-13 (REG-p) finiteness | CONSUMED — Step 4 | ✓ | |
| K-14 MarkGraft duties | (I0)/(I1)/(I3-rc) CONSUMED — Step 10 Delivers + D2.3 walk (D-15 for the box level) | ~ | ADVISORY A-4: duty **(I2)** (of the tree row's "(I0)–(I3)") appears in neither the D2.3 consumer walk nor the ROOT |
| K-15 (Lean seams) | CLOSED — tree row: "no open mathematics" | ✓ | nothing to consume; display-only absence |

### 1.6 Open leaves O-1..O-14

| node | disposition | status match | note |
|---|---|---|---|
| O-1 thr-tier | CONSUMED — Step 6 (Thm 2), P(O-1thr r4) named §3.2 | ✓ | sheared-convention pin = §3.3 row |
| O-1 δ-tier | EVICTED — rides D-16, route R-QNT (D1.6 slot 2 + D1.4/D2.4); §3.3 NOT-on-ledger names D-16 | ✓ | |
| O-2a | CONSUMED — Step 7, P(O-2a r5) named §3.2; D-5 carrier design displayed as its proved content | ✓ | D-13 split executed |
| O-2b (OB1/TT-DET′/MF-MATCH) | EVICTED — §3.3 NOT-on-ledger; warrant D2.1 line 2 + D2.4 (consumer table: only consumer = D-16, struck at D1.4) | ✓ | MF-MATCH covered as part of the package (D2.3 deferred tier), not by name |
| O-3 (→ K-RUN-C) | CONSUMED — Steps 10/11 (CU-1 VERIFIED leaf #5; CUC/CU-2t with R2 arc); replacement warrant = O3adj REPLACE, D2.3 | ✓ | clause-3 re-key (D2.1 line 1) consumed at Step 9; LC-COH = §3.3 row |
| O-4 | CONSUMED — Step 13 (M05 core at V2-upheld scope; O4T arc; (AGR) relocated §3.2 per VC1 finding 10) | ✓ (ROOT ahead of DELTA 3, consistently) | D1.4 mandatory-route adjudication cited at Step 13 |
| O-5 + D-7a/b/c | CONSUMED — Step 12, P(O5t r3) named §3.2; GD-7 flags = §3.3 row | ✓ | |
| O-6, O-7, O-8a | EVICTED — §3.3 NOT-on-ledger; warrant D1.4 (route R-QNT) + D2.4 | ✓ | K-OB-D: see ADVISORY A-3 |
| O-8a's `cl3_tails` (X2-TAILS) | **NO HOME** | ✗ | GAP G-5: the tree marks it "a SEPARATE open estimate (owner §H-DOMAINS family)" — the O-6/O-7/O-8a eviction does not by its terms carry a SEPARATE item, and no ROOT row names it |
| O-8b | CONSUMED — Step 16 ((R1)–(R4) = (H4a) §3.1; (UB-X) = (H4b); P(O-8b/M14) §3.2 per VC3 B2) | ✓ | |
| O-9 | CONSUMED — Step 14 ((GR-B)/(FRESH)/(ADM) rows §3.1; D3.2 index fix governs; r2/r3 arc synced) | ✓ (ROOT ahead of D3.7's "repair + re-pass owed", consistently) | |
| O-10 | CONSUMED — Step 15, VERIFIED leaf #6 at scope; K-LOC/(I-τ) = §3.3 interface row | ✓ (D3.4 PROVED-UNVERIFIED → VERIFIED at the later 7b28562 harvest — a lawful progression, passes named) | |
| O-11 | CONSUMED — Step 18 at the D-9 corrected set; r2/r3 arc + pass 3 owed §3.2 | ✓ | but see GAP G-4 (H.6 fences) |
| O-12 | CONSUMED — Step 5, VERIFIED leaf #2 at honest scope; OL-O12-1/OL-O12-2 = §3.3 rows | ✓ (D2.5) | (SL≥2) display added at VC2 |
| O-13 | CONSUMED — Step 3, VERIFIED leaf #1; D-12r = §3.1 row; VAL-DIV displayed non-consumed | ✓ (D2.5) | |
| O-14a′ | CONSUMED — Step 9 (Consumes-list added VC1; MacLane loci pinned VC2) | ✓ | Conjecture 5.4.C displayed non-consumed |
| O-14a (guarded vertex law) | PARTIAL — the ≥ 2 disposition (item 28) = §3.3 PARKED row; the guarded e′ = 1 law + D-10's "suffices for every consumer" clause have NO consumption/eviction line | ✗ | GAP G-3 |
| O-14b (cl19 carrier ladder) | **NO HOME** — not consumed, not evicted, absent from the NOT-on-ledger list | ✗ | GAP G-1 |
| O-14c (hStateNe) | **NO HOME** — same class | ✗ | GAP G-2 |
| O-14d | EVICTED (engineering) — §3.3 Item-27/28 row, warrant D-10 ("excluded from the criterion") | ✓ | |

### 1.7 DELTA-1 nodes D-1..D-16

| node | disposition | status match |
|---|---|---|
| D-1, D-2, D-4 | CONSUMED — Step 1 (Dfloor, VERIFIED leaf #3; B3-repaired perimeter: Σα = 1 + interpolation, identity concluded at Step 19) | ✓ (D2.5) |
| D-3 | CONSUMED — Step 16 (collapsed to scope hygiene by the arbitrary-DVR route + O-8b slice; residue = (UB-X)(a)) | ✓ |
| D-5 | CONSUMED — Step 7 (carrier design = O-2a rev 5 proved content) + §3.3 disposition row; wider invariance clause carried per-leaf (Steps 3/6/10) | ✓ |
| D-6 | CONSUMED — Step 5 | ✓ (PROVED-UNVERIFIED@𝔅_n → VERIFIED inside leaf #2) |
| D-7a/b/c | CONSUMED — Step 12 | ✓ |
| D-8 (+D-8r) | CONSUMED — Step 15 (guard confirmed sharper; D-8r resolved in the adapted regime) | ✓ (D3.4) |
| D-9 (+D-9k) | CONSUMED — Step 18 dependency set; D-9k = Step 17 Delivers ("escape input at the pack") | ✓ |
| D-10 | GOVERNANCE — executed: Step 9 + §3.3 Item-27/28 row; BUT its O-14a/b/c criterion clause is the source of gaps G-1..G-3 | ~ |
| D-11 | CONSUMED — Steps 17/18b (stratified per VC1 finding 2); r3 arc, pass 3 owed §3.2 | ✓ (D3.7 recorded-not-adjudicated → ROOT adjudicated, consistent) |
| D-12 (+D-12r) | CONSUMED — Step 3; D-12r = §3.1 row (consumer list completed at VC3 A6(ii)) | ✓ |
| D-13 | GOVERNANCE — executed (Step 7 + the O-2b eviction); id unnamed | ✓ |
| D-14 | CONSUMED — Step 6 (Thm 1) | ✓ |
| D-15 | CONSUMED — Step 6 (Thm 3; owns ALL box-level lift quantification per O3adj §3.2 = D2.1 line 3) | ✓ |
| D-16 | EVICTED — §3.3 NOT-on-ledger; warrant D1.4 (struck, rates-only) + D2.4 | ✓ |

### 1.8 DELTA-2/3 nodes: GD families, CU pieces, satellites

| node | disposition | status match |
|---|---|---|
| GD-1 | CONSUMED — Step 7 (OL-2a-1) + §3.3 (KP)/(KPirr) row + Step 12 flags | ✓ |
| GD-2, GD-3 | CONSUMED — Step 8 (GD23 VERIFIED leaf #4; order ≤ 1 outright; ≥ 2 = (GR-B) §3.1 (H1)) | ✓ (tree D3.6 pass-2-landed → ROOT rev-4-VERIFIED at the later c43b13b harvest, consistent) |
| GD-4, GD-6 | CONSUMED — §3.3 row (incl. the CU-2t R2 (T-DEC)/(T-VERD) +2-row honesty correction) + Step 18 entry via D-a | ✓ |
| GD-5 (+S-1, C.1.5) | CONSUMED — §3.3 S-1 audit row (C.1.5 named per VC1 finding 5) + Step 6 | ✓ |
| GD-7 | CONSUMED — §3.3 five-flags row (Step 12) | ✓ |
| GD-8 | CONSUMED — §3.3 order-≥ 2 row; (REP-IRR)/CU-2t-deep quarantine displayed | ✓ |
| CU-1 | CONSUMED — Step 10, VERIFIED leaf #5; (FRESH)/(GR-B)/pins conditionality displayed | ✓ |
| CU-2, CU-2t, CU-3, CU-4, CU-5, CU-7 | CONSUMED — Step 11 (R2 arc; re-pass owed §3.2) | ✓ (D3.5 → R2, consistent) |
| CU-6 (OB2) | EVICTED — §3.3 NOT-on-ledger; warrant D3.1 (CUC §6.1 audit, signed off; re-confirmed by D-11 M3 at Step 17) | ✓ |
| K-OB-A, K-OB-B, K-OB-E | CONSUMED — Step 11 (CU-5 satellites, "K-OB-A/B/E") | ✓ |
| K-OB-C | EVICTED — §3.3 NOT-on-ledger; warrant D2.1 line 4 / D2.4 | ✓ |
| K-OB-D | EVICTED by containment only (sole consumer O-7, route R-QNT) — never named in any eviction list | ~ ADVISORY A-3 |
| K-DICT-OB1, K-DICT-OB2 | EVICTED — = OB1/OB2 above (D2.4, D3.1) | ✓ |
| K-RUN clause 4 | CONSUMED — Step 11 (CU-4, F4-S/F4-C; (E-N) touch displayed §3.1) | ✓ |
| LC-COH | HOMED — §3.3 row, consumed by nothing (as D2.1 line 1 requires) | ✓ |
| D3.2 index fix | CONSUMED — Step 14 ("the DELTA-3 §D3.2 index fix governs") | ✓ |
| D3.6 registry | HOMED — §3 header (CUC §0 registry = the live P(·) key, metadata) | ✓ |

---

## 2. Eviction register (complete; each warrant cited)

O-2b/OB1 (+TT-DET′/MF-MATCH) ← D2.1 line 2 + D2.4 · OB2/CU-6 (+BNS §2 pin) ← D3.1 ·
LIT-5/BNS ← D2.4 + D3.1 (zero touch-points) · K-OB-C ← D2.1 line 4 · D-16 + O-1 δ-tier ←
D1.4 + D2.4 · O-6/O-7/O-8a ← D1.4 · O-14d + items 27/28 ← D-10 + tree §3 priority note
(parked fence events per the authority) · A-1/A-2 (htameFE, projective) ← standing
directive (tree §1 annex) · LIT-6 ← measure-route-only (tree LIT-6 row) · LIT-7 ← annex
(tree LIT-7 row). All of these appear in the ROOT's §3.3 NOT-on-ledger paragraph, §4
NOT-consumed list, or a named §3.3 row — EXCEPT K-OB-D (containment, unrecorded: A-3).

## 3. Status-delta consistency (delta-changed nodes vs ROOT ledger)

All checked, all consistent: D1.5(a) root downgrade → §1 Relation ✓ · (b) LIT-1
conditional → §4.1 ✓ · (c) LIT-3 candidate → §4.5 ✓ · (d) LIT-8 split → §4.7 ✓ ·
(e) T-1 re-scope → Step 2 ✓ · (f) T-8 re-scope → Step 2 ✓ · (g) K-12 audit duty →
§3.2 ✓ · (h) O-12 → Step 5 ✓ · (i) O-13 → Step 3 ✓ · D2.5 Dfloor/O-12/O-13 VERIFIED →
Steps 1/5/3 ✓ · D2.1 lines 1–5 executed → Steps 9/6/11 + §3.3 ✓ · D3.1 → Step 17 M3 +
§3.3 ✓ · D3.2 → Step 14 ✓ · D3.3/D3.7(O-9) → Step 14 (ROOT ahead by the named
r2/r3 arc — lawful) ✓ · D3.4 (O-10) → Step 15 (VERIFIED at the later 7b28562 harvest,
passes named — lawful) ✓ · D3.5 (CU-2t) → Step 11 (R2 arc) ✓ · D3.6 path → §6 dispatch ✓.
No contradiction found anywhere; every ROOT grade that exceeds the tree's DELTA-3
snapshot traces to a named later harvest (c43b13b or 7b28562). A DELTA 4 folding the
wave-10/14 + VC1–VC3 state back into the tree is owed but was already announced by
DELTA 3's closing line.

## 4. Findings

**GAPS (must be adjudicated or homed before the tree-§4 criterion-4 audit can pass):**

* **G-1 (O-14b, cl19 repaired carrier form).** OPEN node; DELTA-1 §D-10 explicitly puts
  it inside "all leaves proved" (O-14a/a′/b/c each closed); it is consumed at NO ROOT
  step, appears in NO eviction list, and the §3.3 NOT-on-ledger paragraph omits it.
  K-7's "repaired carrier form = part of leaf O-14" pointer dangles with it. Likely
  resolution: engine-internal/Lean-side, consumed by nothing mandatory — but that
  adjudication is exactly what is owed on record.
* **G-2 (O-14c, hStateNe derivability).** Same class as G-1: OPEN per D-10's criterion
  clause, no ROOT home, no recorded eviction.
* **G-3 (O-14a, the guarded vertex-transport law).** Partially covered: the ≥ 2
  disposition (sign-off item 28) is parked at the §3.3 Item-27/28 row. NOT covered: the
  e′ = 1 guarded law itself and D-10's clause "the guarded law suffices for every
  consumer" — no ROOT consumption or eviction line (nearest content: GD-2's clause-(c)
  HK52 trap, which is the countermodel, not the law). One recorded line owed.
* **G-4 (T-5's six H.6 fences gating [1v]-FULL).** Tree T-5: "Its six H.6 fences gate
  the [1v]-FULL event (table value-correctness, leaf O-11)"; tree O-11 K3 repeats the
  gating. ROOT Step 18 assembles K3 from T-7s + O-9 + O-8b and NO ROOT text mentions
  the fences (grep-zero). Either the O-11 r2/r3 assembly superseded the H-domain route
  (then a recorded supersession line is owed) or a K3 conditionality is undisplayed.
* **G-5 (`cl3_tails` / X2-TAILS).** Tree O-8 row: "a SEPARATE open estimate (owner
  §H-DOMAINS family)" — by its own wording NOT part of O-8a, so the O-6/O-7/O-8a R-QNT
  eviction does not carry it; no ROOT row names it. One recorded line (R-QNT or a
  §3.3 home) owed.

**ADVISORIES (display/bookkeeping, no missing mathematics identified):**

* **A-1 (T-11/JOINT-D1).** §2.2 VERIFIED-DUAL node absent from ROOT by id; consumption
  arguable via Step 2's T-1 ("accepted as part of the T-1 perimeter"). Criterion-4
  display item.
* **A-2 (LIT-4/OM-SAT).** Consumed by content via the GMN Cor 1.20/3.8 pins (Steps
  11/12) but absent from the §4 roster by id, and its audited "K = ℚ_p exactly" scope
  caveat (tree D-3: re-derive or re-scope at K_δ) is covered only generically by
  (UB-X)(a). A roster line would close it.
* **A-3 (K-OB-D).** Evicted only by containment (sole consumer O-7 → R-QNT); no eviction
  list names it — the only IFK REV-1 obligation with no explicit disposition line.
* **A-4 (K-14 duty (I2)).** The tree's K-14 row prices duties (I0)–(I3); the D2.3
  consumer walk and ROOT Step 10 serve (I0)/(I1)/(I3-rc) only. Where (I2) went
  (served, re-attributed, or engineering) is unrecorded.
* **A-5 (refuted-row ids).** K-5/K-7/K-8/K-10 and closed rows K-1/K-2/K-15, K-3, K-9
  appear in ROOT by content but not by id — relevant only to the tree-§4 criterion-4
  reading "every node id appears in the document or in its explicitly-argued pruning
  list"; content homes exist for all EXCEPT K-7's (→ G-1).

## 5. VERDICT

**GAPS( G-1 O-14b · G-2 O-14c · G-3 O-14a-guarded-law · G-4 H.6-fences@K3 ·
G-5 cl3_tails )** — plus advisories A-1..A-5.

Everything else — all literature imports, the B/T layers, all fifteen kernel rows'
open content, all fourteen leaves and their delta splits, all sixteen D-nodes, the
eight GD families, the seven CU pieces, and every recorded eviction — is CONSUMED at a
named ROOT step or EVICTED with its warrant on record, and every delta-changed status
matches the ROOT ledger or is superseded by a named later harvest. The five gaps are
bookkeeping/adjudication debts (four are one-recorded-line items; G-4 may hide a real
undisplayed conditionality on Step 18's K3 and should be adjudicated first). No gap
touches the (ROOT-C) hypothesis list (H1)–(H4b) itself.

— unit TREE, 2026-08-02. Inputs byte-read in full; grep evidence for every absence
claim (T-11, JOINT-D1, K-1/K-2 ids, ksub, w17ii, O-14b, O-14c, cl19, hStateNe, K-OB-D,
LIT-4, OM-SAT, K-15, MF-MATCH, H.6, cl3_tails, X2-TAILS: zero occurrences in
`docs/ROOT_ASSEMBLY_2026-08-02.md`).
