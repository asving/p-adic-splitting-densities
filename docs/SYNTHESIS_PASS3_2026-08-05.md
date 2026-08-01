# SYNTHESIS PASS 3 (discharge-campaign series) — cross-row unifications, dedup, and the shortest path to literature-only

Directive window 2026-08-05 (machine clock 2026-08-01 — the ledger's Unit-C
convention). Standing charge: the periodic whole-proof synthesis duty ("spend
effort synthesizing and cutting down on the proof by finding big unifying
ideas"). **Series note:** `lean/notes/SYNTHESIS_PASS{1,2,4}_*.md` are the
corpus-era series; this is the DISCHARGE-era pass the fleet ledger names
"Synthesis pass 3" (BRIDGE_ADJUDICATIONS §"H8 FAN-OUT", "Synthesis pass 3
running in parallel"). Nothing here edits ROOT, blueprints, or Lean — findings
and recommendations only; the orchestrator adjudicates.

**State read (sources consumed):** ROOT_ASSEMBLY_2026-08-02.md §§0–3 at
REVISION 12 (twelve §3.1 rows ↔ (H1)–(H9); RE-ACCEPTED at VC14+VC15, two
consecutive clean model-diverse passes — the suspension arc closed); all nine
`lean/blueprints/HDISCHARGE_H*.md` (door tables + §0/§1); the ledger tail
through "H8 FAN-OUT: 11/11"; the landed `lean/LeanUrat/Scaffold/HDischarge/`
tree (34 files, ~6.5k lines: H9 1/1 complete, H5 16/19, H2 9/14 + the U10→U10b
arc, H4 7/11, H3 12/18, H8 11/11; H7 fleet IN FLIGHT — Rows.lean landed; H6/H1
not dispatched). Member already RETIRED end-to-end: **(NSF-KEY)** (H9 lead
adjudication + `H9/NsfKeyProp.lean`).

---

## §1 Cross-row unifying mechanisms (the four charged candidates + two more)

### F1 — VERIFIED (candidate a): the interior/terminal decomposition already
### exists as H8's predicate-parametric first-entrance calculus; make it the
### shared engine before H6 dispatches

The same partition mechanism recurs in four rows, currently on course to be
derived twice more:

* **H8 (landed, generic):** `H8/CutFirst.lean` + `H8/CutPartition.lean` —
  `firstEntAbove_unique`/`firstEntAbove_exists`, `read_cut_exhaustive`,
  `shallow_block_disjoint`/`block_block_disjoint`, `read_cut_partition` — ALL
  parametric in an arbitrary entrance predicate `E : History p F → Prop`
  (exhaustive-exclusive read ownership at the first entrance into E).
* **H2 (landed, special case):** `DictIII/Hyps.lean` `InteriorChain` (a₀ ≥ 2 ∧
  every sel exists with μ ≥ 2) — the "no entrance into the decided class"
  complement; the U10b interior guard.
* **H6 (planned):** (T-DEC)'s exhaustiveness clause — "any OTHER
  verdict-carrying emission site is the deep corner" — is exactly
  `read_cut_exhaustive` instantiated at E = decided (`DecIrr ∨ DecHen`,
  `DictIII/CU2t.lean`), plus the corner class.
* **H9 (adjacent):** leaf-completeness (all leaves (τ-irr)/(τ-hen)) is the
  tree-level face of the same partition.

**Obstruction:** carrier mismatch. H8's layer is locked to `MovesC.History`
(via `MovesT.Defs`); H2/H6's predicates live on `DictIII.EHist`
(`DictIII/Carriers.lean:55`). Both are node-list structures; the calculus
consumes only the prefix order (`ProperPrefix`).

**Recommendation (small, do BEFORE the H6 fleet):** hoist the ~200-line
first-entrance layer carrier-generic — parametrize over the node list (or a
prefix-ordered type) in `Scaffold/Shared/FirstEntrance.lean`; re-derive H8's
`History` instance; H6's (T-DEC-cor) exhaustiveness and any DictIII
interior/terminal complement then consume `read_cut_exhaustive` at
E = DecIrr ∨ DecHen instead of re-proving prefix combinatorics on `EHist`.
One lemma family, four consumers, and the H2 guard/H6 seam become literal
complements of the same E.

### F2 — VERIFIED (candidate b): (GR-B)'s FGMN brief is already single-homed;
### what is MISSING is the shared Lean carrier — pull H1 wave-0 forward

The consumption picture is confirmed and wider than charged. (GR-B)/(H1)
content enters as a **named hypothesis** in FIVE other fleets:

* H2: the door table's (c-GR) consumes (GR-B)(2′)+(3)+(4); the reduction spine
  is (GR-B) + (TRANS-DEEP) ⇒ (FRESH); "(GR-B) line clause" fields in
  `H2/FreshLaws.lean:119`, `H2/FreshReduction.lean:19,80`.
* H3: finding (F-ADM-2) — (CLASS-d) is NOT a bare-carrier theorem at r ≥ 2
  (88 lattice failures at r = 2); "supplied at consumption sites by (GR-B),
  the (H1) group — **cross-lead seam with H1**" (HDISCHARGE_H3 §1.3(b));
  `H3/AdmCarrier.lean:154` binds it as ADM-U2's `hclass`.
* H6: (T-READ)(c)'s order-≥ 2 half "rides (H1) … `OL2min` at the requested
  level enters as a named hypothesis" (HDISCHARGE_H6 §3.3(c)).
* H7: KL-0 frame kernel "the (GR-B)/HC2 apparatus" (HDISCHARGE_H7 §3, line
  497).
* H8: (K-CUT-s) `supply_cell`'s owner column cites "surfaces of the (H1)
  dictionary group" (HDISCHARGE_H8 §1.3).

The FGMN faithfulness brief itself (HDISCHARGE_H1 §1.2's per-clause table +
TR-1..TR-7 + OP-A1..A4, target artifact `GRB_order2_attempt.md` +
verifybrief) is correctly ONE unit — do **not** split it per row; one-home
discipline holds (the VC7-4 precedent).

**The gap:** each fleet binds its own LOCAL Prop for the same clause bundle
(H3's `hclass`, H2's line-clause fields, H6's planned `OL2min`, H7's opaque
`KLoc`/frame params) — and H1, the fleet that will define THE rows, is LAST in
the queue. When H1(a) lands, retirement would require a 5-fleet re-key sweep.

**Recommendation:** pull **H1 wave 0** (`H1/Defs.lean`, the hypothesis-row
carriers — MECH, already compile-probed per the blueprint header) forward NOW,
before the H7 Tier-M and H6 waves bind their local Props; H7/H6 consume it at
dispatch; H2/H3 re-key in their follow-up cycles. Retirement of (H1)(a) then
propagates by instantiating ONE structure. (This does not start H1's math; it
lands its interface.)

### F3 — REFUTED as charged (candidate c): the (O1)/(O2′)/(O3) booking algebra
### is single-homed in H5; H4's "rate" connection is a recorded mislabel

Grep across all nine blueprints: (O1)/(O2′)/(O3) occurs ONLY in HDISCHARGE_H5
(11 hits; the (RE)/(ROW-Σ) content, landed as `H5/Defs.lean` `Booking`/
`REWitness` + `H5/RowSigma.lean`). H4 has ZERO occurrences, and HDISCHARGE_H4
§0 itself records the swarm dispatch's "quantitative stabilization rates"
gloss as a **CONTEXT-NOTE MISLABEL** matching no repo artifact. No shared
carrier is needed; do not create one. (The real H4↔H5 adjacency is only the
generic evaluation seam at Step 18's K2/K3, already attributed per REVISION 8.)

### F4 — Dedup (the one true (c)-adjacent duplication): two ℝ≥0∞ Tonelli
### Pi-product engines

`H8/Lemma33.lean:40` `private lemma tsum_pi_prod` (dependent form,
`α : Fin k → Type u`) re-proves `ValueSide/MassId.lean:558`
`tsum_pi_fin_prod` (`f : Fin k → ℕ → ℝ≥0∞`) — same engine
(`Fin.consEquiv` + `ENNReal.tsum_prod'`), both recorded as checked-absent from
Mathlib. H8's is strictly more general and PRIVATE. This is the SYN2-S1
de-privatize class. **Recommendation:** hoist H8's dependent form to a shared
module (e.g. `Scaffold/Shared/ENNRealTonelli.lean`), re-derive MassId's as the
ℕ-instance; fold into the standing de-privatize sweep (40 `private` decls now
in HDischarge/). Note the deeper rhyme — H5's (ROW-Σ) telescoping (Σ_F m(F)·∏ᵢ
(Σ β) with leg normalization, ℚ(q)) and H8's regroup (tsum/∏, ℝ≥0∞) are the
same weighted sum-product mechanism in two semirings; a common abstraction is
NOT worth forcing (different carriers, both already proved), but reviewers
should be told they are twins so passes on one inform the other.

### F5 — Staleness (contradiction-class): the Lean hypothesis surface
### `RootHyps` is SIX-row (REVISION 5) against ROOT's TWELVE-row REVISION 12

`Scaffold/Hypotheses.lean` declares in its own header "This file transcribes
ROOT ASSEMBLY at REVISION 5" and carries h1..h6 fields ONLY: **no
h7_itau/h7_kloc, no h8_kcut, no h9 fields; h5_pack lacks PACK-i..iv;**
`ClauseRHyps`/`ClauseUBHyps` therefore enumerate stale per-clause sets. This
is the exact "stale-hypothesis-enumeration genre" VC13 killed at doc level
(REVISION 12's global enumeration audit) — alive on the Lean side, where the
BP-division contract says "never a parallel second hypothesis surface." The
fleets know: `H8/R2RootSync.lean:150` records the owed "one-line `RootHyps`
extension (`h8_kcut : Prop` field)"; H8 meanwhile landed the LOCAL
`VTreeCutSeam` (sanctioned as a residual seam, but the top-level row still
owes its RootHyps home). **Recommendation:** execute the BP_VI sync as ONE
unit riding the r14 batch window (F6): twelve-row field extension + attribution
display sync + a greppable enumeration-audit anchor keyed to ROOT §1, so the
next ROOT revision fails loudly here instead of silently.

### F6 — One r14 batch, one bar re-run (the counter economics)

Queued ROOT edits now: VC15's 4 advisories, the (NSF-KEY) retirement spec
(HDISCHARGE_H9 §1.4), H8's row re-scope spec (`H8/R2RootSync.lean`,
orchestrator-owned), H4's ROOT-sync draft, D12R-U4 (auto-blocked by the
hardened prover template — correctly), plus F5's Lean shadow. Every ROOT
landing resets the acceptance counter (re-earned only on identical text).
**Recommendation:** land them as ONE batched r14 + ONE bar re-run
(VC16/VC17), and do NOT hold r14 for (K1-CANON)/r15 — genuinely open math
must not gate hygiene. Freeze r14's content list in the ledger before drafting
so late arrivals queue for r15 instead of re-opening r14.

### F7 — One-home for the "K1 scope" question (pre-empt a three-way gloss)

Three units currently analyze what K1's tree quantifier ranges over: H9's
(K1-CANON) discharge design (§3, warrant note H9-C1 — "K1's bare quantifier
does not inherit its sources' guard"), H8's (K-CUT-g) graft-completeness +
the H8-R1 charge-(vi) adjudication against M04 §5.5 (K1), and (NSF-INT)'s
claim (ii) (M04 scope = the guarded TREE-N corpus). Same seam, three pens —
the two-classifications genre. **Recommendation:** write H9-C1 as THE K1-scope
reference; H8-R1's adjudication and H6's K4-CYL display CITE it rather than
re-deriving the scope analysis.

### F8 — Shared compiled-witness module for the DictIII chains (candidate d,
### scoped verdict)

A universal witness library across fleets is NOT warranted — witnesses live on
different carriers (EHist, MovesC.History, BnMember, bridge trees) and a
forced merge buys nothing. But WITHIN the DictIII carrier the duplication is
real and imminent: H2's `DictIIIProbes.lean` already builds `duplicateEHist`
(the all-terminal duplicate world — the F-4 refuter) and `interiorEHist` (the
guarded interior world, actual slope, ∃! realized), and H6's waves A/B need
exactly the decided-chain instances (DecIrr positive gate = sel μ = 1; DecHen
= length-1 root-decided; the probed `TDecRow` witness shape).
**Recommendation:** promote the H2 probe chains to
`Scaffold/DictIII/TestChains.lean` before H6 dispatch; H6 extends rather than
rebuilds. Keep the per-fleet GATE theorems where they are (they are
row-specific); share only the instances.

### F9 — BP_III supersession needs an explicit unit-ID map (dedup-audit
### standard)

The ledger adjudicated that BP_III's 55 remaining blocks concentrate in Wave 1
(14 units, GD23 dictionary face = H1 territory) and Wave 5 (7 units, terminal
seam = H6 territory), deferring BP_III mop-up INTO those blueprints. Neither
HDISCHARGE_H1 nor H6 lists the superseded BP_III unit IDs. Under the standing
dedup-audit standard ("is every NEW declaration a genuine addition?"), the
H6/H1 fleets must land their units AS the BP_III identifiers where they
coincide (e.g. H6's demand map already pins `TerminalSeamHyps`,
`terminalDatum`, `cu2t_*` from BP_III §1.3/§1.9) — **add the one-line ID map
to each dispatch** so BP_III wave 1/5 cannot be re-dispatched in parallel.

---

## §2 The shortest path to literature-only (ranked: consumers unblocked / effort)

**Mechanical-now batch (dispatch in the current follow-up cycle, parallel):**

1. **(K1-CANON) note + hostile pass** (H9 §3; warrant note H9-C1 + gates
   g-A..g-D). Retires (NSF-INT) — I-1/I-2/I-3 already on file — and with it
   the ENTIRE (H9) row at the spec'd r15. Cheapest full-row closure on the
   board; also serves F7.
2. **H8 hostile pass** — the ledger's own verdict: "(H8) is a
   RATIFICATION-AWAY from discharge" (Lean core 11/11; residual re-attributed
   to (H1)/(H7)/CL-8/TREE-EXP rows per §1.3 + H8-B3 construction work).
3. **D-12r**: the two faithfulness briefs (HEN-LIFT as HL-a/b/c ← Neukirch II
   §4/LIT-3; OM-SAT ← GMN Cor 3.8 + Def 3.9) + the D12R-U4 retirement
   adjudication (already in the r14 queue). Pure literature-retarget; the
   reduction is dual-accepted on file.
4. **(E-N)**: EN-U1 walk RESCOPE-CLEAN + EN-U2 falsifier HIT already landed
   and the ROOT row already rewritten to the witness-backed scoped display;
   only EN-U3 residual rides the follow-up cycle.
5. **(H4a) = (R1)–(R4)**: Route B proof note composed + gated (H4-M5, task
   record) — remaining: fire the named §3.2 pass P(O-8b/M14) on the composite,
   then the row retires (the ROOT-sync draft is written). "Expected
   mechanical" grade confirmed by the fleet.
6. **H5 mop-up**: the one open (PACK-ii) bound + the C4 gate; C5 stays
   BLOCKED/DATA until the n = 3 tables exist (route-a) or O-14d populates the
   member (route-b) — that data pass is the (PACK)/(H5) retirement event and
   is FINITE, executable work.

**Moderate:** 7. **(ADM)** — ADM-U0 `triangular` repair (definition-change
authority; makes K6 expressible), then the track-A hostile pass over realized
shape families; (CLASS-d) binds the F2 shared carrier. 8. **(H6)** machine-side
members ((T-DEC-dec)/(T-DEC-cor)/(T-VERD) + binding clause) — construction-
conformance once C0 (TRM) exists; consume F1's generic partition; item (vii)
stays displayed (no general-n carrier at HEAD). 9. **(H7)** — Tier S in
flight; K-LOC core = the GMN Thm 2.26 retarget (its own brief, single-row) +
KL kernels; (I-τ) presentation write-up.

**The frontier (the one door-2 retarget that collapses parts of MULTIPLE rows
at once):** 10. **(H1)(a) — the FGMN Thm 4.2/§5 retarget + composed-march
write-up** (GRB_order2 unit, TR-1..TR-7, OP-A1..A4). Direct consumers waiting:
H2's (c-GR), H3's (CLASS-d)/general-order census, H6's (T-READ) order-≥ 2
half, H7's KL-0 frame, H8's (K-CUT-s) supply — plus ROOT Steps 10/14/16/18/18b.
This is the single highest-leverage math unit in the campaign; staff it as the
dedicated campaign AFTER the H6 fleet, with F2's carrier already down.
11. **(H1)(b)/(c)/(d)** ride the same ladder (KP-STEP in gr(w_{j+1}); GD-6
run-binding; the KEY1 order-≥ 2 block). 12. **(FRESH) residue (TRANS-DEEP)**
— gated on B2-FINAL/GD-≥ 2; hardest, shared vehicle with (H1)'s tower.

**Watch item (F11-class):** if H2's reduction theorem (FRESH-RED) is ever used
to retire (H2), the traded-in kernel (TRANS-DEEP)(F)/(L)/(J) MUST enter §3.1
as a displayed row — it currently exists only inside HDISCHARGE_H2 §5. Same
discipline for any H8-B3 escalation.

---

## §3 Revised priority list for the remaining fleets

1. **H7 fleet (in flight):** finish Tier S; DEFER Tier M semantic units until
   (i) F2's shared carrier lands and (ii) the GMN 2.26 faithfulness brief is
   written — Tier S must never be cited as (H7) evidence (blueprint's own
   fence).
2. **Interleave the four MECH shared units now** (one small wave, before H6):
   F2 H1-wave-0 carrier pull-forward; F1 FirstEntrance hoist; F8 TestChains
   promotion; F4 Tonelli de-privatize.
3. **H6 fleet next** — the biggest cross-blueprint unblock (BP_IV S5b/D4 +
   BP_V spine's `TerminalSeamRows`/`RootRows` + BP_III wave-5's 7 blocks).
   Order waves A → D(K4/RootRows packaging early, to break the recorded
   "cross-blueprint SEAM FAILURE") → B → C; consume F1's generic layer;
   carry F9's BP_III ID map.
4. **Follow-up cycle in parallel with H6:** the §2 mechanical-now batch
   ((K1-CANON), H8 pass, D-12r briefs, EN-U3, P(O-8b/M14), H5 PACK-ii/C4).
5. **r14 BATCH + one bar re-run** once H6's ROOT-facing specs are written
   (F6): all queued edits + F5's twelve-row Lean sync; then r15 = (H9) closure
   when (K1-CANON) lands.
6. **H1 fleet last as planned** (wave 0 already advanced) — the GRB order-≥ 2
   write-up as the dedicated math campaign, then (b)/(d), with (c) parallel;
   (TRANS-DEEP)/H2-U9 rides the same campaign.

Findings F1–F9 above each carry their evidence pointers; execution of any of
them is an orchestrator adjudication, not this pass's.
