# HDISCHARGE_H9 — the (H9) = (NSF) discharge blueprint

**Lead:** H9 discharge lead (Fable), hypothesis-discharge swarm (Asvin directive
2026-08-05, ledger 5a624c3). **Written:** 2026-08-01 machine clock (the
2026-08-05-dispatch session), immediately after the UNIT C EXECUTED ledger entry
(commits dfdb558/322ec54) and the VC14 COMPOSITION-SOUND record (counter ONE of 2,
VC15 deciding, r14 queued behind the bar).

**Authority chain read for this blueprint:** `docs/ROOT_ASSEMBLY_2026-08-02.md`
(ROOT-C) block lines ~254–341 + the §3.1 (H9) row (line ~1474);
`lean/notes/openmath/R11_REPAIR_DESIGN_V5_2026-08-04.md` §2.5 ((NSF-KEY-RET) R-0..R-5,
(NSF-INT-RET) I-1..I-3, the M02 record, the two channels) + §7 (Unit C, order, terminal
semantics); `lean/notes/openmath/D11_rev4_2026-08-04.md` §4 (the (H9) display + the
(q-1)–(q-6) quotes) + §4A ((CH-COV), I-2 closure) + §4B (the (NSF-INT) leaf proof);
`lean/notes/openmath/D11r4_pass1_2026-08-04.md` (gap 5) / `D11r4_pass2_2026-08-04.md`
(gap 3); `lean/notes/openmath/UNITC_ripple.md` + `UNITC_diff_confirm.md`;
`lean/notes/openmath/M04-series-tie_fable.md` §§5.4–5.5; `M02-count-tie_fable.md`;
ledger tail through the VC14 entry. Lean HEAD re-read this session:
`MovesU/BridgeD3_treeCarrier.lean` (the guarded carrier), `BridgeD4_vtLaws.lean`
(`bridgeVt_nsFree`), `BridgeD7_canonical.lean` (`bridgeCanonical_pin`,
`bridgeCanonical_level0`), `MovesU/Defs.lean` (ClassifierSpec docstring = (q-4),
`VPSound`), `MovesU/DefsLedger.lean` (`TreeSeam.count_tie`, `TreePin.vt_surj`),
`MovesT/Defs.lean` (VTree fields `nsLeaf`/`hns_leaf`, `fiberAt` clauses, `NsFree`,
`Realizes`), `MovesT/E11_treeN.lean` (`hdet`), `BridgeD16_vtSurj.lean`.

**Reuse note (no duplication):** BP_I–BP_VI carry no (H9)-specific units — the (H9)
row was born at ROOT r11 (REVISION 10), after those blueprints froze; the carriers this
blueprint consumes (`bridgeTree`, `bridgeCanonical_pin`, `bridgeVt_*`, `fiberAt`,
`NsFree`, `treeN.hdet`) are EXISTING corpus declarations (BP_I's bridge cluster + the
MovesT campaign), reused verbatim, never re-declared. The five new Lean units below are
new THEOREMS about those carriers, in a new Scaffold/HDischarge/H9 module.

---

## 0. The group, verbatim scope, and door summary

**(H9) = (NSF), the ns-routing interface row** (ROOT §3.1, NEW at REVISION 10, r11).
THE TARGET (the row's conditional statement): at any instantiation satisfying (q-4)'s
interface pin (the ClassifierSpec docstring: `some σ` = complete finite realizable
tree, all leaves (τ-irr)/(τ-hen), certified at level N), every K1/K4-labeled box lies
in the decided-ns-free counted corpus and D-15's exact-classification package applies
with no a.e. weakening. Two members, retiring SEPARATELY (round-4 finding 4); the two
displayed premises of the first member are housed IN the member (one-home):

| member | content | door | status after this blueprint's session |
|---|---|---|---|
| (NSF-KEY) | as-built keying conformance (ONE proposition, §1.1) | EXECUTED-ADJUDICATION (Unit C ran; no further proving) + a compiled-proposition bonus unit (H9-U1) | **RETIRED** — adjudicated this session (ledger entry "H9 LEAD ADJUDICATION"); r14 edit spec at §1.4, QUEUED behind the Unit-D bar |
| (NSF-INT) | the interface implication chain pin → predicate → corpus (claims (i)+(ii)) | PROVE — **already proved conditionally**: I-1 (the §4B leaf proof) ON FILE, I-2 closed, I-3 GRANTED (r4 pass 2) | OPEN, priced — residual = exactly the (K1-CANON) discharge (§3); after it, retirement is a ledger adjudication + the §3.6 r15 spec |
| — premise: marks-vocabulary (§1.4 of O-1thr) | a mark is the RECORD of an NsHalts event (§1.4's sole generation rule) | CARRIED (no separate discharge owed per (NSF-INT-RET) as corrected at ROOT r11 — see §4) | displayed; compiled conformance gate H9-U4 (probe-proved); optional hygiene unit H9-D3 |
| — premise: (K1-CANON) | K1's "canonical tree" denotes (q-4)'s pinned notion at every consumed Step-18 site | PROVE (interface-lemma form, §3; the M04-side pin display is the OPTIONAL recording edit, sign-off-gated) | OPEN — the note H9-C1 + hostile pass H9-C2 are this blueprint's main new work |

Consumption (unchanged, ROOT row): enters Step 18's K1/K4 chain and Step 17's M3 leg
(via Steps 11/12); clause (R) + inherited (UB). Two channels (design §2.5): (ch-1)
label-blind exact combinatorics; (ch-2) mass-mediated semantic tie at Step 19's
squeeze; (CH-COV) audit CLEAN at the walked closure, residue (CH-RES) carried.

**What "discharged" means per member — displayed once, to prevent fiat:** (NSF-KEY)
retires by the six-artifact iff (NSF-KEY-RET) — executed, adjudicated, DONE. (NSF-INT)
retires by I-1 + I-2 + I-3 + a separate (K1-CANON) discharge — three of four on file;
this blueprint does NOT declare it retired. Nothing else in this file is a discharge
claim; the Lean units are conformance/witness theorems, not retirement events.

---

## 1. (NSF-KEY) — the adjudication (member DONE), the bonus unit, and the owed r14 spec

### 1.1 The proposition (verbatim, one home)

> At the wired instance: for every n, p, level N, box f, and σ — if the wired
> classifier labels f (`bridgeCanonical … N f = some σ`) then f fibers a carried tree
> of the σ-carrier satisfying `MovesT.NsFree` (no ns-marked chain) at threshold ≤ N.

History: KNOWN FALSE AT HEAD from the M02 record (the exact-square poison V₀: carried
because `bridgeTree` had no ns-free conjunct; labeled "totally split"; c_{V₀}(N) =
p^{N−2} against (SCALE)) — an obligation certain to fire, which fired.

### 1.2 The adjudication (executed retirement — the one sanctioned fiat-free case)

**VERDICT: RETIRED.** Full entry: ledger `BRIDGE_ADJUDICATIONS_2026-07-30.md`, "H9
LEAD ADJUDICATION" (this session). Two independent grounds:

* **(a) the six-artifact iff:** R-0 sign-off (ledger, Asvin verbatim: "sign-off
  granted on the NsFree repair!"); R-1 the verbatim conjunct diff at HEAD
  (`BridgeD3_treeCarrier.lean:94-96`, re-read this session) + the closed pre-edit
  ripple enumeration (`UNITC_ripple.md`, 41 matches / 8 files / 2 destructuring
  re-points / 1 new projection); R-2 statement texts byte-identical (`count_tie`,
  `canonical_stable`, `VPSound` — re-scoped THROUGH the carrier only); R-3 the three
  per-statement validations (treeN discharge candidate sorry-free at the hdet scope;
  `bridgeCanonical_stable` re-proved green; the V₀-dead record = `bridgeVt_nsFree`
  compiled + consuming wiring recompiled — VPSound REMAINS the open kernel, no proof
  promised); R-4 `lake build` green (8579 jobs) + AxChk census identical (740
  footprints, 0 sorryAx); R-5 fresh-context Codex diff confirmation
  (`UNITC_diff_confirm.md`, 7 checks, VERDICT: CONFIRMED).
* **(b) truth at HEAD, machine-checkable:** the §1.1 proposition was COMPILE-PROBED AS
  A THEOREM against built HEAD this session — statement + 6-line proof from
  `bridgeCanonical_pin` (proved, both directions) + `bridgeVt_nsFree` +
  `bridgeCanonical_level0`; axiom footprint {propext, Classical.choice, Quot.sound}.
  Verbatim statement + probe-verified proof body: unit **H9-U1** (§6). This upgrades
  the design's "holds by construction of (†7)" to a compiled proposition.

**Bounds (the adjudication's own honesty lines):** (i) (H9) NOT closed — (NSF-INT)
stands priced; (ii) NO carrier non-vacuity claim (§5.2); (iii) the
BridgeD16/TreePin.vt_surj completeness residue stands (§5.1); (iv) ROOT REVISION 12
still displays KNOWN FALSE AT HEAD — adjudicated conservative-stale on record
(overpriced, never underpriced); cure = r14, queued (§1.4).

### 1.3 Consequences already in force (no ROOT edit needed for these)

Design §2.5 retirement EFFECT: the design-graph node N2's BLOCKED-PENDING clause drops
"(NSF-KEY) execution" (its other clause, the (CH-COV) audit, was EXECUTED at r4 §4A —
outcome CLEAN, residue (CH-RES)); exact squares and every window-degenerate locus now
fiber NO carried tree and drain to `none`/env(N) — (q-6)'s intended drainage, by
construction. M02's flagged step (intended `ReadsOf` semantics; no compiled
countermodel while `canPolicy` is designer-sorried) is inherited verbatim.

### 1.4 The owed ROOT r14 edit spec (SPEC ONLY — this unit does NOT edit ROOT)

**Sequencing (on record at the VC14 ledger entry, honored here):** r14 executes AFTER
the Unit-D bar closes (VC15 is the deciding pass on the frozen REVISION-12 text; an
r14 landing now would reset the counter ONE → ZERO). Execute r14 as ONE batch with any
VC15 dispositions. r14 is a TEXT CHANGE: on landing, the counter resets to ZERO of 2
and the bar re-runs on the REVISION-13 text — this is the design's displayed cost of
the E9-class status sync, accepted at Unit C's dispatch.

Edits (operative displays only; historical/revision records untouched per the r13
global-enumeration-audit convention):

* **E-r14-1 — §1 (ROOT-C), the (H9) block (lines ~334–341):** replace the (NSF-KEY)
  clause "…, **KNOWN FALSE AT HEAD** (the M02 exact-square poison V₀), retiring ONLY
  by the repair design's sign-off-gated Unit C ((NSF-KEY-RET))" by: "…, **RETIRED**
  (Unit C executed at the 2026-08-05 sign-off's dispatch: all six (NSF-KEY-RET)
  artifacts on file — ledger 'UNIT C EXECUTED' + 'H9 LEAD ADJUDICATION' entries; holds
  at HEAD by construction of (†7) over the guarded carrier, compiled-proposition
  record H9-U1); the row's OPEN member is (NSF-INT) (its two displayed premises
  housed in-member; (K1-CANON) discharge owed)".
* **E-r14-2 — §3.1 (H9) row (line ~1474):** (a) the (NSF-KEY) member block: KNOWN
  FALSE record re-labeled RETIREMENT PROVENANCE (historical); executed status +
  artifact pointers (UNITC_ripple.md, UNITC_diff_confirm.md, the two ledger entries);
  (b) the stale carrier quote "`bridgeTree` carries NO ns-free conjunct at HEAD"
  re-displayed as the guarded carrier verbatim (`… ∧ MovesT.NsFree V`); (c) the
  RETIREMENT clause "(NSF-KEY) ONLY by the design's Unit C per (NSF-KEY-RET), NEVER by
  any leaf text" → "(NSF-KEY) RETIRED by Unit C per (NSF-KEY-RET) (executed;
  artifacts on file)"; (d) the row's closing display rule "The (H9) target must NEVER
  be displayed as covering the HEAD wiring while (NSF-KEY) is unretired" → "the
  target's as-built keying face now holds at HEAD ((NSF-KEY) retired; compiled record
  H9-U1 once landed); the target must NOT be displayed as discharged while (NSF-INT)
  stands priced ((K1-CANON) owed)".
* **E-r14-3 — Step 18's K1-a/K4 lines + Step 17's M3 leg (the E9 homes):** the (H9)
  display gains "(NSF-KEY) executed/retired as of r14" and re-states the residual
  price as "(NSF-INT) (incl. its (K1-CANON) premise)"; two-channel attribution and
  (CH-COV)/(CH-RES) status unchanged.
* **E-r14-4 — member-granular (H9) enumerations (r13 audit rule):** §1's display
  (covered by E-r14-1), the 6(iii)–(ix)+7 residue list's (H9) mention, Step 16/19
  closers + final ∎ IF they carry member granularity (at r13 they carry row labels
  only — verify at execution); sync all to "one open member" phrasing.
* **E-r14-5 — the §3.2 D-11 [V] row cross-reference:** no member-status change lives
  there (it prices passes, not (H9)); verify only that no "(NSF-KEY) unretired"
  phrase leaked in.
* **E-r14-6 — `docs/PROJECT_STATE.md`:** sync the same statuses (Unit C executed;
  (NSF-KEY) retired; (H9) open at (NSF-INT)/(K1-CANON); r14 record).

Falsifier for the editor: after r14, `grep -n "KNOWN FALSE AT HEAD"
docs/ROOT_ASSEMBLY_2026-08-02.md` must hit ONLY historical/revision-record sections
(§16-class records and the §3.1 provenance clause), no operative display.

---

## 2. (NSF-INT) — door PROVE: three of four retirement artifacts ON FILE

### 2.1 The member (verbatim shape) and the artifact ledger

(NSF-INT), the interface implication chain (pin → predicate → corpus). At every
consumed site of Step 18's K1/K4 chain: **(i)** irr/hen-terminal completeness excludes
ns-marks — a complete finite realizable tree with all leaves (τ-irr)/(τ-hen) carries
no ns-marks (in particular the Hensel payload carries none) — so every box labeled
under (q-4)'s pin fibers a tree that is decided ns-free in (q-1)'s sense; **(ii)**
M04's "complete-finite-realizable" scope coincides with the guarded TREE-N corpus
((q-3)'s all-leaves-(τ-irr)/(τ-hen), `hdet`-guarded trees) at every consumed site.
The interface quotes (q-1)–(q-6) are CONTEXT, not proof.

Retirement per (NSF-INT-RET) (design V5 §2.5, corrected at ROOT r11 / leaf REVISION 3):

| artifact | content | status |
|---|---|---|
| I-1 | the §4B leaf proof (D11_rev4 §4B): claim (i) proved from the §1.4 displays + the marks-vocabulary premise (interior states have children ⟹ principal face exists ⟹ ¬NsHalts; maximal (τ-irr) chains are saturated ⟹ ¬NsHalts; payload members are not states); claim (ii) site-by-site — K4 leg at the pin directly, K1 leg UNDER (K1-CANON) | **ON FILE** |
| I-2 | the closed consumed-site list {K1 (M04 §5.5 (K1) + Lemma 3.3), K4 (M04 §5.5 (K4) + D-15 = O-1thr Thm 3(b)/(c))}, identity with §4A's walked closure displayed; closure relative to (CH-RES) | **ON FILE / CLOSED** |
| I-3 | the hostile pass's ACCEPT of §4B as a proof | **GRANTED** (r4 pass 2 adjudicated the conditional argument VALID; pass-2 gap 3 fixed the scope of the grant: it verifies (K1-CANON) ⇒ the K1 scope conclusion, and cannot itself establish (K1-CANON)) |
| + (K1-CANON) discharge | leaf-external; the M04-side pin display or the interface-lemma form | **OPEN — §3 of this blueprint** |

**Consequence:** the ONLY work standing between (NSF-INT) and retirement is the
(K1-CANON) discharge. This blueprint therefore spends its proof effort there.

**Hygiene note (not a retirement condition):** the D-11 leaf's own acceptance bar
(two consecutive clean passes on the REVISION-3 text) still owes one confirming pass —
a §3.2 [V]-row item at ROOT, tracked there, NOT in (NSF-INT-RET). If a future pass
found §4B defective, I-3 would re-open; this blueprint's §3 note is written to be
robust to that (it re-quotes rather than assumes the §4B walk).

**Riders unchanged, at their own homes:** (E-N) (whether thr(T) ≤ N in D_σ(N) is
redundant — OPEN at O-1thr rev 4, priced in (H3)'s company at its own row); the
numerical decided_σ(N) = D_σ(N) tie (the count_tie/finiteness_stack row).

### 2.2 Claim (i)'s compiled conformance face (probe-proved this session)

The paper proof of (i) stands at I-1 and is NOT re-proved here. What this blueprint
ADDS: the Lean carrier conforms to (i)'s vocabulary — at any `fiberAt` witness, the
mark/halt tie is a THEOREM of the built corpus (fiberAt clause (2)'s dichotomy per
maximal chain: (IrrHalts ∧ ¬nsLeaf ∧ irr-verdict) ∨ (NsHalts ∧ ¬IrrHalts ∧ nsLeaf ∧
ns-verdict); `hns_leaf` confines marks to maximal chains; payload = `henV`, not a
chain, so no mark can attach). Units H9-U2 (all-maximal-irr ⟹ NsFree), H9-U3 (the ⟺),
H9-U4 (marks record NsHalts events) — §6, all probe-proved, Lean-core. These are
CONFORMANCE WITNESSES (the as-built carrier satisfies the interface reading), not a
formalization of O-1thr §1.4 itself; the paper premise keeps its paper home.

---

## 3. (K1-CANON) — the discharge design (the blueprint's main new work)

### 3.1 The premise (verbatim, ROOT §3.1 (H9) row)

> **(K1-CANON)** — at every consumed Step-18 site, K1's "canonical tree" denotes
> (q-4)'s pinned notion; equivalently (the interface-lemma form), every tree at which
> the mandatory path invokes K1 satisfies the all-leaves-(τ-irr)/(τ-hen) guard.

Provenance: r4 pass-1 gap 5 (the source-inheritance inference WITHDRAWN — a theorem's
quantifier does not inherit its source lemmas' restriction; the `hdet` guard scopes
one machine-checked candidate, not K1; three admissible routes displayed —
guard-in-definition, guard-in-statement, proved interface lemma — none on file);
r4 pass-2 gap 3 (I-3's accept is conditional and cannot supply it).

### 3.2 Door: PROVE the interface-lemma form. Deliverable: note H9-C1

**Primary route = the interface-lemma form** (the pass's route (γ)), as a leaf-external
note `lean/notes/openmath/K1CANON_discharge.md`, because it needs NO statement change:
the M04-side pin display (route guard-in-statement) is demoted to an OPTIONAL recording
edit (§3.5) so the (H9) closure is not gated on a sign-off.

**What changed since gap 5 was filed — why this is now provable rather than
re-assertable:** gap 5's complaint was that NO display tied K1's consumed range to the
guarded corpus. Two displays now exist that did not then: (a) as-built — Unit C made
the carrier ITSELF guarded (`bridgeTree`'s third conjunct; read-off `bridgeVt_nsFree`),
and units H9-U3/U5 compile the translation NsFree ⟺ all-maximal-chains-(τ-irr)-halted
at realized trees, so "the trees the wired classifier ranges over satisfy the guard"
is a THEOREM, not a walk assertion; (b) intended — (q-4)'s docstring clause carries the
guard verbatim. The note's job reduces to: every K1 invocation on the mandatory path
ranges over exactly those trees.

### 3.3 The note's skeleton (section-by-section; honest open points named)

* **(C1-0) Claim + bookkeeping.** The §3.1 display verbatim; the discharge grade
  sought (premise of (NSF-INT)'s grade, discharged by adjudication-by-inspection
  against named quotes + compiled units); the gate (one hostile Codex pass,
  quote-and-classify); what it does NOT touch (no leaf edit, no ROOT edit, no Lean
  statement change).
* **(C1-1) The closed K1 invocation-site list** (= I-2's K1 restriction): (s-a) ROOT
  Step 18's K1-a line; (s-b) M04 §5.5 Theorem 4's proof, the step "K4 turns the LHS
  into Σ_{T type σ} μ(fiber T). K1 + Lemma 3.3 turn it into the shallow convolution".
  Identity with §4A's walked closure displayed; closure carried RELATIVE to (CH-RES)
  (same corpus-relative grade as §4A — no stronger completeness claimed).
* **(C1-2) The consumed-range display, per site.** At (s-b): K1 is invoked at the
  index set of the post-K4 sum; that sum is produced FROM decided_σ(N), and decided_σ
  is "DEFINED from the canonical map (never a free field)" ((q-4) quote) — so the
  consumed range = {trees fibered by `some σ`-labeled boxes within threshold} = the
  σ-carrier's trees. At (s-a): ROOT's K1-a line consumes the SAME regrouping at the
  same corpus (quote the line at execution). Range displays, both instantiation
  layers: as-built = `bridgeCanonical_pin`'s ∃-range, i.e. `bridgeTree` (compiled);
  intended = (q-4)'s pinned trees (displayed docstring).
* **(C1-3) The guard at that range.** As-built: the carrier's third conjunct
  (`bridgeVt_nsFree`), translated to leaf vocabulary by H9-U5 (every carried tree has
  all maximal chains IrrHalts — probe-proved); the hen leg: carrier hen-content lives
  in `henV` (payload; `hhen`'s (1,g)-shape), never a chain, so "all leaves
  (τ-irr)/(τ-hen)" = "all maximal chains (τ-irr)" + payload — exactly U5's conclusion
  (§4B claim (i) item 3's Lean face). Intended: (q-4)'s clause verbatim.
* **(C1-4) Conclusion (the interface-lemma form) + the denotation corollary.** Every
  tree at which the mandatory path invokes K1 satisfies the guard (both layers); hence
  the (q-3)-scoped source lemmas' proved range covers every consumed K1 instance, and
  K1's "canonical tree" AT THE CONSUMED SITES denotes the pinned notion — which is the
  (K1-CANON) display. Trees outside the guard — if K1's bare quantifier admits any —
  are invoked nowhere on the mandatory path ((CH-RES)-relative).
* **(C1-5) Honest cruxes, displayed for the verifier to attack:** (x-1) "K1 is invoked
  only at the post-K4 range" rests on Theorem 4's quoted proof order + the walked
  closure — corpus-relative, residue (CH-RES) carried, NOT absolute; (x-2) the
  compiled U3/U5 translation is at `fiberAt` witnesses (realized trees) — exactly the
  carrier's `RealizedSelf` scope, no broader; (x-3) the intended-layer leg reads
  (q-4)'s text as the definition of "labeled" — legitimate HERE because the claim
  being proved IS the denotation statement (no circularity: the pin text is quoted as
  the range's definition, not as K1's).

### 3.4 Gate + downstream (what fires on ACCEPT)

H9-C2: one adversarial Codex pass on H9-C1 (fresh context; charge: quote-and-classify,
critical-vs-gap; verify (a) C1-1 = I-2's K1 restriction, (b) each step consumes only
displayed quotes/compiled units, (c) no smuggled absolute-completeness claim). ≥1
clean pass required; the (NSF-INT) retirement adjudication (H9-C3) then cites
I-1 + I-2 + I-3 + this discharge, enters the ledger, and writes the r15 spec (§3.6).
On REJECT: fold findings, revise, re-pass; if the verifier shows the interface-lemma
form UNDERDETERMINED by the quotes on file, fall back to §3.5 (the sign-off route).

### 3.5 OPTIONAL recording edit (sign-off-gated; NOT required for discharge)

M04 §5.5 (K1) gains a scope parenthetical after "each complete finite realizable
canonical tree": "(canonical tree := the (q-3)/TREE-N scope — all leaves
(τ-irr)/(τ-hen); at the wired instance, the carrier's `MovesT.NsFree` clause, which
equals this guard at realized trees [H9-U3/U5])". Statement-fence: K1 = OL-1, an OPEN
KERNEL consumed by ROOT Step 18 and M04 Theorem 4 — narrowing its quantifier is a
statement change ⟹ Asvin sign-off + Codex conformance check (warrant: C1-2 shows the
narrowing loses no consumed instance; Theorem 4's proof unchanged). **Coordination
flag (H8):** (H8) = (K-CUT) owns M04 Lemma 3.3's hypothesis at the same Step-18 K1
regrouping; the K1-quantifier parenthetical does not touch Lemma 3.3's hypothesis
(disjoint objects), but both edits would live in M04 §5.5 — the H8 lead must see this
spec before either edits M04.

### 3.6 The r15 edit spec (fires only after H9-C3; SPEC ONLY)

On (NSF-INT) retirement: §1 (ROOT-C) (H9) block → both members retired, row moves out
of the open-hypothesis enumeration (the ELEVEN remaining rows ↔ (H1)–(H8) bijection
must be re-displayed — same genre as r11's twelve-row edit, reversed); §3.1 (H9) row →
retirement record (artifacts: I-1/I-2/I-3 + K1CANON_discharge.md + its pass + the
ledger entries); Step 17/18 displays drop the (H9) price from their Consumes lines
(keep the historical pointer); the 6(iii)–(ix)+7 residue list drops (H9); counter
consequences as at r14 (text change; batch with pending VC dispositions). Execute only
via the standing ROOT-editor unit, never from this blueprint.

---

## 4. The marks-vocabulary premise — CARRIED, hardened, not re-owed

Display (§4B): "a mark is the RECORD of an NsHalts event; no other display of §1.4
generates or permits a mark" — §1.4's SOLE displayed generation rule, consumed by
claim (i). Per (NSF-INT-RET) as corrected at ROOT r11, retirement requires a separate
discharge of (K1-CANON) ONLY — the marks premise is NOT separately owed: it is
grounded in an on-file display (the (τ-ns)/"MARKED" line of (q-1)), and r4 pass 2
adjudicated claim (i)'s proof VALID with the premise displayed. This blueprint does
NOT invent a new obligation. It adds: (a) the compiled conformance gate H9-U4 (marks
record NsHalts events at the built carrier — probe-proved); (b) an OPTIONAL hygiene
unit H9-D3 (§5.3) if a future pass ever contests the reading.

---

## 5. Residues recorded (Unit C fallout + known-open gates; none block §§1–3)

### 5.1 The BridgeD16 / TreePin.vt_surj completeness residue (Phase-B queue)

From `UNITC_ripple.md` (pre-edit record, re-verified this session): BridgeD16's
`bridge_vt_surj` proves the completeness direction at an INLINED 2-clause subtype
(`{V // V.typemult = σ.1 ∧ RealizedSelf n p V}` — never names `bridgeTree`), and
`TreePin.vt_surj` (DefsLedger) demands: every realized typemult-σ VTree within
threshold lies in the carrier image. After Unit C the carrier image contains ONLY
ns-free trees, while M02 §2's V₀ is realized-but-not-carried — so the as-typed
vt_surj obligation is REFUTABLE at the intended semantics at the eventual
instantiation (no compiled countermodel while `canPolicy` is designer-sorried — M02's
flagged step, inherited). DISPOSITION: an OPEN OBLIGATION on the vt_surj SUPPLIER
(the eventual TreePin instantiation unit), NOT on Unit C and NOT on this blueprint;
the expected repair is an ns-free hypothesis on the field (`MovesT.NsFree V →`) — a
STATEMENT CHANGE on a DefsLedger structure field ⟹ statement-fence: sign-off + Codex
adjudication brief (H9-D1 below specs the brief only). BridgeD16's header sentence
("IB-D3's `Tree σ` is definitionally this subtype") is STALE post-repair —
comment-truth fix rides the same future unit (comment-only, no fence).

### 5.2 Compiled carrier non-vacuity — OPEN, recorded, NOT promised

No compiled element of `bridgeTree n p σ` exists at HEAD (post-Unit-C the former
paper-witness V₀ is expelled BY DESIGN; realization of a positive witness is blocked
on the same seam as always: `canPolicy` designer-sorried; nearest assets = the
G1_toyGate toy trees + the M18/IFK-U6 probes). Consequence displayed honestly:
H9-U1/U5 and `count_tie` at the guarded instance are implications over the carrier
and would be vacuously satisfiable at an empty carrier — their VALUE as conformance
witnesses is real (they pin the wiring's shape) but they are NOT existence claims.
Non-vacuity belongs to the realization/instantiation seam ([3t]/TreePin), tracked
there; gate H9-D2 records the falsifier shape for WHEN that seam lands: exhibit
`T₀ : bridgeTree n p σ` for concrete (n,p,σ) and check `bridgeCanonical` labels its
fiber. BLOCKED — assign no prover.

### 5.3 Optional hygiene (assign only if contested): H9-D3

O-1thr §1.4-side display edit making the sole-generation-rule reading an explicit
definitional clause ("marks are generated by (τ-ns) halts and by nothing else").
Statement change on a consumed leaf ⟹ sign-off + pass; LOW priority (pass 2 accepted
the current reading); do NOT dispatch by default.

---

## 6. LEAN UNIT SPECS (verbatim; ALL FIVE COMPILE-PROBED against built HEAD this session)

**Probe protocol run (the BP_VI/BP_IV lesson honored):** every statement below was
compiled against the built corpus BEFORE being written in, via a temporary root-level
probe file (`lake env lean`, HEAD = commit 322ec54's tree + the swarm's untouched
LeanUrat). Result: NOT ONLY well-typed — all five PROVED, with the exact proof bodies
below, zero sorries; `#print axioms` = {propext, Classical.choice, Quot.sound} (spot
checks on U1/U3/U4/U5). The probe file was deleted (blueprint-only unit); the prover
fan-out re-creates it as the real module. Difficulty: ALL EASY (transcription + build
+ census wiring). If any body fails on re-run, the corpus moved under us — STOP and
re-adjudicate, do not weaken statements.

**Target file (ONE module, the units chain):**
`lean/LeanUrat/Scaffold/HDischarge/H9/NsfKeyProp.lean`

Header duties: module docstring naming (H9)=(NSF), this blueprint, the ledger
adjudication entry, and the NON-claims (§5.2 non-vacuity note verbatim); imports
`LeanUrat.MovesU.BridgeD7_canonical` + `LeanUrat.MovesU.BridgeD4_vtLaws` (transitively
supplies MovesT.Defs, BridgeD3); namespace `LeanUrat.Scaffold.HDischarge.H9`;
`open LeanUrat.MovesU`. Wire into the Scaffold census per Scaffold convention
(`Scaffold/AxChk.lean` if that is the standing census home — prover checks; plain
`lake build` must stay green; AxChk_baseline footprint identical).

### H9-U2 `nsFree_of_maximal_irrHalts` [EASY, probe-proved]
```lean
theorem nsFree_of_maximal_irrHalts {p : ℕ} [Fact p.Prime] {F : Type*}
    [Field F] [Finite F] {n N m : ℕ} {pol : MovesD.CanonPolicy p F}
    (Tr : MovesT.VTree p F) (T : MovesD.TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (x : MovesD.Box p m)
    (hfib : Tr.fiberAt T χ x)
    (hirr : ∀ H ∈ Tr.chains, MovesT.IsMaximalIn Tr.chains H → MovesT.IrrHalts H) :
    MovesT.NsFree Tr := by
  intro H hH hns
  obtain ⟨hmem, hmax⟩ := Tr.hns_leaf H hns
  rcases hfib.2.1 H hmem hmax with h1 | h2
  · exact h1.2.1 hns
  · exact h2.2.1 (hirr H hmem hmax)
```
Content: §4B claim (i)'s Lean face at a `fiberAt` witness — the (q-3) leaf guard
forces mark-freeness. Consumes `hns_leaf` (marks only at maximal chains) + `fiberAt`
clause (2)'s dichotomy.

### H9-U3 `nsFree_iff_maximal_irrHalts` [EASY, probe-proved; depends U2]
```lean
theorem nsFree_iff_maximal_irrHalts {p : ℕ} [Fact p.Prime] {F : Type*}
    [Field F] [Finite F] {n N m : ℕ} {pol : MovesD.CanonPolicy p F}
    (Tr : MovesT.VTree p F) (T : MovesD.TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (x : MovesD.Box p m)
    (hfib : Tr.fiberAt T χ x) :
    MovesT.NsFree Tr ↔
      ∀ H ∈ Tr.chains, MovesT.IsMaximalIn Tr.chains H → MovesT.IrrHalts H := by
  constructor
  · intro hnf H hmem hmax
    rcases hfib.2.1 H hmem hmax with h1 | h2
    · exact h1.1
    · exact absurd h2.2.2.1 (hnf H hmem)
  · exact nsFree_of_maximal_irrHalts Tr T χ x hfib
```
Content: at realized trees the two guard vocabularies COINCIDE — `NsFree`/`hdet`
(mark vocabulary) ⟺ all-maximal-chains-(τ-irr)-halted ((q-3) leaf vocabulary). The
compiled scope-coincidence kernel consumed by the (K1-CANON) note (C1-3).

### H9-U4 `nsLeaf_nsHalts_of_fiberAt` [EASY, probe-proved]
```lean
theorem nsLeaf_nsHalts_of_fiberAt {p : ℕ} [Fact p.Prime] {F : Type*}
    [Field F] [Finite F] {n N m : ℕ} {pol : MovesD.CanonPolicy p F}
    (Tr : MovesT.VTree p F) (T : MovesD.TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (x : MovesD.Box p m)
    (hfib : Tr.fiberAt T χ x)
    (H : MovesC.History p F) (hns : Tr.nsLeaf H) :
    MovesT.NsHalts T (some H) x := by
  obtain ⟨hmem, hmax⟩ := Tr.hns_leaf H hns
  rcases hfib.2.1 H hmem hmax with h1 | h2
  · exact absurd hns h1.2.1
  · exact h2.1
```
Content: marks RECORD NsHalts events at the built carrier — the marks-vocabulary
premise's compiled conformance face (§4). NOTE: `History` lives in `MovesC` (probe
lesson: `MovesT.History` does not resolve).

### H9-U1 `nsfKey_prop` — THE compiled (NSF-KEY) proposition [EASY, probe-proved]
```lean
theorem nsfKey_prop (n p : ℕ) [Fact p.Prime]
    (boxeq : ∀ N : ℕ, Box p n N ≃ MovesD.Box p (n * N))
    (N : ℕ) (f : Box p n N) (σ : SplittingType n)
    (h : bridgeCanonical n p boxeq N f = some σ) :
    ∃ (hN : 0 < N) (T : bridgeTree n p σ),
      bridgeThr n p σ T ≤ N ∧
      (bridgeVt n p σ T).fiberAt (bridgeTm p n N) (bridgeChart n N hN)
        (boxeq N f) ∧
      MovesT.NsFree (bridgeVt n p σ T) := by
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    rw [bridgeCanonical_level0] at h
    exact absurd h (by simp)
  · obtain ⟨T, hthr, hfib⟩ := (bridgeCanonical_pin n p boxeq N hN f σ).mp h
    exact ⟨hN, T, hthr, hfib, bridgeVt_nsFree n p σ T⟩
```
Content: §1.1 verbatim in as-built vocabulary — label ⟹ carried ns-free fibering tree
within threshold. The (NSF-KEY) adjudication's ground (b). At the generic `boxeq`
binder (the pin theorem's own generality); the wired instance specializes it.

### H9-U5 `bridgeVt_maximal_irrHalts` [EASY, probe-proved; depends U3]
```lean
theorem bridgeVt_maximal_irrHalts (n p : ℕ) [Fact p.Prime]
    (σ : SplittingType n) (T : bridgeTree n p σ) :
    ∀ H ∈ (bridgeVt n p σ T).chains,
      MovesT.IsMaximalIn (bridgeVt n p σ T).chains H → MovesT.IrrHalts H := by
  obtain ⟨x, hfib⟩ := bridgeVt_realizedSelf n p σ T
  exact (nsFree_iff_maximal_irrHalts _ _ _ _ hfib).mp (bridgeVt_nsFree n p σ T)
```
Content: every CARRIED tree satisfies the (q-3) guard in the LEAF vocabulary (all
maximal chains (τ-irr)-halted) — the as-built half of (K1-CANON)'s C1-3, via the
carrier's own `RealizedSelf` witness. (Hen content is payload `henV`, not a chain —
no chain-side hen case exists at this carrier; displayed in the docstring.)

**Falsifier/negative-control gates for the prover:** (g-1) `#print axioms` on all
five = Lean-core exactly; (g-2) `lake env lean LeanUrat/AxChk_baseline.lean`
footprint identical (stop-the-line on regression); (g-3) statements land VERBATIM —
any elaboration failure is a corpus-moved event, not a license to weaken (parent
statement-fence); (g-4) grep the module for `sorry` = zero; (g-5) the module must NOT
declare any element of `bridgeTree` (§5.2 — non-vacuity is not this unit's claim).

---

## 7. Wave order, dependencies, difficulty

```
WAVE 0 (THIS session, done):     A0 ledger adjudication entry  [DONE]
                                 A1 blueprint (this file)      [DONE]
WAVE 1 (Lean, ONE prover):       U2 → U3 → U4 → U1 → U5 in ONE module
                                 (file order as §6; U4/U1 independent of U3;
                                  U5 needs U3; all probe-proved)     [EASY]
WAVE 2 (paper, ONE writer,       C1 the K1CANON_discharge.md note (§3.3
        parallel with Wave 1):      skeleton; cites U3/U5 as "probe-proved,
                                    landing as Wave 1" until Wave 1 lands)
                                                                  [MEDIUM]
WAVE 3 (gate):                   C2 Codex hostile pass on C1 → fold → ≥1 clean
WAVE 4 (ledger, lead):           C3 (NSF-INT) retirement adjudication + r15 spec
                                 (fires ONLY on C2 ACCEPT)
QUEUED EXTERNALLY:               r14 ROOT edit (§1.4 spec; ROOT editor, after
                                 the VC15 bar closes) · r15 (§3.6, after C3)
OPTIONAL/SIGN-OFF:               C4 = §3.5 M04 pin display (coordinate with H8)
                                 D3 = §5.3 O-1thr hygiene display
PHASE-B QUEUE (blocked):         D1 = §5.1 vt_surj re-scope brief (fence-gated)
                                 D2 = §5.2 non-vacuity witness (realization seam)
```

Parallelism summary: Waves 1 and 2 run concurrently (2 agents); everything else is
sequential gating. Total NEW prover load: 1 easy Lean unit-module + 1 medium note +
1 Codex pass. No numerics fleet needed: the standing M02/PARI exact-square record and
N2-density-tie census are the row's numerics of record; no new numeric claim is made
by any unit here (negative control g-5 keeps it that way).

---

## 8. Codex adversarial review of this blueprint (directive requirement)

Charge given: fresh-context read of the FULL blueprint; quote-and-classify every
defect (critical = breaks a logical chain / misstates an authority; gap = missing
justification); attack specifically (1) the (NSF-KEY) adjudication's grounds and
bounds, (2) the r14 spec's faithfulness to E9/(NSF-KEY-RET)/the bar sequencing,
(3) the (K1-CANON) note design's cruxes (x-1)–(x-3) — especially circularity risk at
the intended layer, (4) the Lean specs' fidelity to the quoted corpus, (5) fiat-
discharge leaks. Verdict + disposition table appended below after the run.

[REVIEW PENDING — appended on completion]
