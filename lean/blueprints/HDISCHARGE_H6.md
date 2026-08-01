# HDISCHARGE_H6 — the terminal-seam conformance group (T-DEC)/(T-READ)/(T-VERD) + D-11 item (vii)

**Unit:** H6 discharge lead, hypothesis-discharge swarm (Asvin directive 2026-08-05,
ledger `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` §"THE HYPOTHESIS-DISCHARGE
SWARM"). **Door 3** (construction-conformance dominant). Blueprint-only unit: NO
Scaffold `.lean` file lands with this unit; prover fan-outs run separately.

**Authority for content:** `docs/ROOT_ASSEMBLY_2026-08-02.md` (ROOT) §1 (ROOT-C)(H6)
+ §3.1 row "(T-DEC)/(T-READ)/(T-VERD) + D-11 item (vii)" (line ~1471) + Step 11;
CUC = `lean/notes/openmath/CU_cluster_phaseB.md` §§9.2/9.2a/9.4/9.5 (CU-2t R4,
ADJUDICATED VERIFIED at scope, leaf #9 — VERIFIED **modulo exactly these rows**);
`docs/MATH_COMPLETION_TREE_2026-08-01.md` §D4.2 (item (vii)'s routing adjudication);
BP_III §1.3/§1.9 + wave 5 (the least-landed BP_III wave); BP_IV §1.0/§1.5/§1.6
(the blocked consumers); BP_V §1 (RootRows charter).

**Probe discipline:** every Lean statement in §4 was compile-probed GREEN against
the built corpus on 2026-08-05 (machine clock 2026-08-01), probe file
`lean/ProbeH6.lean` (transient, deleted; imports: `Scaffold.DictIII.{CU2t, Hyps,
CU1}`, `MovesU.DefsLedger`, `MovesT.V9_irrSat`, `Scaffold.ValueSide.Hyps`,
`HC2.Defs`). Zero errors; only unused-binder warnings at the phantom-key probe
(expected — see §3.5).

---

## §0 THE GROUP, EXACTLY (what must be discharged, and what "discharged" means)

Four members, all [M] hypothesis-grade since ROOT REVISION 5 (findings VC5-1/VC5-2:
open propositions consumed on clause (R)'s mandatory path cannot sit in [T]):

* **(T-DEC)** — split at CU-2t R3 (81589e9): **(T-DEC-dec)** emission discipline at
  decided sites (the engine's verdict-carrying terminal record fires after a
  branch's saturated selection (μ_last = 1) as the τ-irr booking, and at the base
  read's Hensel/−∞ booking as the τ-hen booking — both DEC configurations, bound to
  their branch); **(T-DEC-cor)** the corner fence (any OTHER verdict-carrying
  emission site is the deep exact-key corner k′ ≥ 1, μ_{k′} ≥ 2, j₀ = 1 at level
  k′+1 — NOT covered by the CU-2t tie; fenced to Corollary CU-2t-deep at its own
  conditionality; the exhaustiveness clause itself is engine bookkeeping).
* **(T-READ)** — at a (T-DEC-dec) site the emitted terminal record's shape/position
  fields (e, h, ℓ, s, u), sel = ⊥, are the (c1)-shape datum of the level-(k′+1)
  polygon side ((RC-read), Definition RC, CUC §9.2a). Graded at R4 (CU2tp G-α) in
  the GD-2/GD-5 read-semantics-conformance family, NOT GD-4: at k′ ≥ 1 an OL-2-min
  instance + the genuinely new terminal-BINDING clause (which stays GD-4); at
  k′ = 0 an OL-5-type terminal sibling with NO OL-residue sibling, owed from
  scratch. **NO displayed machine-side home on file — purely owed.**
* **(T-VERD)** — the emitted verdict pair is the record function of the emitted
  prefix: (accE_{k′}, accF_{k′}) on DEC(τ-irr), (1, f₀) on DEC(τ-hen) ((RC-verd)).
  Machine-side home (corroboration only): O-1thr §1.4's record mechanics
  ("IrrHalts ⟺ μ_last = 1"; "irrVerdict = (accE, accF) a pure record function").
* **D-11 widened-charge item (vii)** — general-n H.6 in-fence conformance of the
  BUILT tables: the six H.6 fences (XHD-d-EX(∂), M4b-T-AUD, U-R-COUNT, XHD-u-X,
  H-LIST-GEN, E-POS — the [2b]-parked perimeter of T-5's dual acceptance) GATE the
  [1v]-FULL event at every n; that the built per-n tables sit INSIDE them is proved
  nowhere at general n. Sealed n = 3 evidence: V-n3 178/178, H-n3 151/151 — flags,
  not proofs (MATH tree §D4.2). Escalation fence: if a built pack ever NEEDS fenced
  territory (sharpest: H-LIST-GEN beyond class (TRI)), the kernel so touched becomes
  ADDITIONAL open mathematics beyond this row.

**Consumption (ROOT, exact):** clause (R) at Step 11's route (CU-2t's §9.5
terminal-verdict conditionality) → Step 18 through D-a/K4-CYL; through the
terminal-seam leaf labels riding O5triple's counting into Step 18's K1 ("CU leaf
labels", Steps 11/12 → Step 17's M3/Theorem-E leg); item (vii) at Step 18's K3-a.
Clause (UB) inherits the same content transported at q ↦ q^δ. NOT (0)/(SQ).

**Discharge semantics (the swarm rule):** hypothesis content stays hypothesis until
PROVED. Nothing below discharges any member by fiat. The deliverable is (i) faithful
TYPED Lean rows (the current renderings are defective — §2), (ii) the
construction-conformance theorems that discharge the machine-side members at the
as-built engine, (iii) the honest residue display for what stays open ((T-READ)'s
order-≥ 2 leg rides (H1); item (vii)'s general-n content has no Lean-typable carrier
at HEAD), and (iv) the K4/RootRows packaging that unblocks the blocked BP_IV/BP_V
consumers WITHOUT weakening any signature.

---

## §1 THE DOWNSTREAM LEAN DEMAND MAP (who is waiting, at what signature)

| consumer | demanded identifier | status at HEAD | source |
|---|---|---|---|
| BP_IV S5b `seriesTie_of_kernels` + D4 `valueSide_massTie` (K4/D-a binder) | `TerminalSeamRows n p X F` (X : ClassifierSpec n p, F : FiberSeries n p X) | **BLOCKED — identifier declared NOWHERE** ("cross-blueprint SEAM FAILURE", `ValueSide/Hyps.lean` H4 ledger; blocked probes recorded in `SeriesTie.lean` S5b block + `DensityTie.lean` D4 block) | BP_IV §1.5/§1.6 |
| BP_V spine `HypRows n`/`HypR`/`HypUB` | `RootRows.TDec n`, `RootRows.TRead n`, `RootRows.TVerd n`, `RootRows.FenceVII n` in `Scaffold/RowStatements.lean` | module ABSENT; BP_V §5.4 binding directive: bodies = verbatim row statements | BP_V §1 |
| `Scaffold/Hypotheses.lean` `RootHyps n` | fields `h6_tdec`/`h6_tread`/`h6_tverd`/`h6_vii` | LANDED as bare `Prop` fields (transcription device, True-instantiable; the header demands typed carriers eventually) | Hypotheses.lean §rows |
| BP_III wave 5 (III-H5, III-S1–S8) | `TerminalSeamHyps`, `terminalDatum`, `RCConsistent`, `cu2t_*` in `DictIII/CU2t.lean` | III-S1a ONLY landed (`DecIrr`/`DecHen`); III-H5 display DEGENERATE (§2); III-H9 `GMNCor120_38` BLOCKED on a type error (§2) | BP_III §1.3/§1.9; `DictIII/Hyps.lean` BLOCKED block |
| BP_IV M7 (`MassId.lean`) | D-15/ThmE rows (H6-adjacent, NOT this group's) | owner-blocked, out of scope here | BP_IV H4 ledger |

The K4-facing signature is pinned by the blocked consumers verbatim:
`(K4 : TerminalSeamRows n p X F)` with `{X : ClassifierSpec n p} {F : FiberSeries
n p X}` in scope and `[Fact p.Prime]` available. Any Prop-valued structure at
exactly that application shape unblocks S5b/D4 (fence: their binder lists must
reach the BP_VI spine VERBATIM — no weaker signature may be compiled against).

---

## §2 DEFECT CENSUS — why the as-displayed wave-5 statements cannot be "proved" faithfully

These are the reasons wave 5 is the least-landed BP_III wave. Each defect is a
statement-fidelity failure against CUC §9.2/9.2a/9.4; the §4 units supersede the
displays as NEW declarations in `Scaffold/HDischarge/H6/` (landed BP_III
declarations are NOT touched — the fenced `DecIrr`/`DecHen` in `DictIII/CU2t.lean`
stand; a reconciliation unit records the divergence).

* **D-1 (III-H5 `tDECcor` vacuous).** BP_III §1.3 displays
  `tDECcor : DecHen f H → H.a0 = 1 ∨ ∃ D, D.rootOrder = 1` — this is the SECOND
  CONJUNCT of `DecHen`'s own definition. Provable by `fun h => h.2`. Carries zero
  (T-DEC-cor) content (the corner fence mentions no corner).
* **D-2 (III-H5 `tREAD` provable from reader laws).** The display
  `tREAD : ConsF → ∀ i S, R.side i = some S → S ∈ D.principalSides i` follows
  from `R.side_spec` (an iff whose forward direction contains it) — independent of
  `ConsF`. The actual (T-READ) constrains the EMITTED TERMINAL RECORD's fields;
  no emitted record appears in the display.
* **D-3 (III-H5 `tVERD` ill-typed).** The display concludes `EF = terminalDatum f H`
  with `EF : ℕ × ℕ` and `terminalDatum f H : TerminalDatum` — does not elaborate;
  and the repaired `EF = (terminalDatum f H).verdict` is RCConsistent's own third
  conjunct (vacuous as a row given the intended hypotheses).
* **D-4 (III-H5 `tDECdec` contentless).** Concluding `H.nodes ≠ []` from
  `DecIrr H ∨ DecHen f H` prices no emission discipline (and is false at nothing —
  both disjuncts already imply nonemptiness under the landed definitions).
* **D-5 (`terminalDatum` reads the record, not the polygon).** BP_III §1.9's
  `terminalDatum.slope := H.nodes.getLast?.bind fun ν => some (ν.e, ν.h)` takes the
  slope OFF THE LAST NODE. CUC §9.2: the read entry λ_{k′+1} is a function of
  (f, c) through the level-(k′+1) GMN read — "(RC-read) is a polygon read of f
  over the prefix's chain" (§9.2a non-circularity display). As displayed, RC's
  read clause degenerates to record-echoes-record.
* **D-6 (`GMNCor120_38`/`terminalDatum.verdict` type error).** `MovesT.accE/accF :
  MovesC.History p F → ℕ` applied to `H.nodes : List ENodeData` — hard elaboration
  error, recorded verbatim in `DictIII/Hyps.lean`'s BLOCKED(III-H9) block. Needs
  E-side accumulators (a NEW definition, chartered at §4 A1 — the architect ruling
  that block asked for; this blueprint IS the ruling proposal, Codex-reviewed).
* **D-7 (`DecHen`'s ∃-over-lawless-data disjunct).** `∃ D : GMNData f (Theta H),
  D.rootOrder = 1` is trivially witnessed (`GMNData` carries NO laws:
  `⟨fun _ => [], fun _ => 0, fun _ => 0, 1⟩`). The j₀ = 1 clause must be keyed at
  THE GIVEN semantic read D, not existentially quantified.
* **D-8 (`DecIrr` index/position drift).** Landed `DecIrr`: ∃ position k ≥ 1
  (0-indexed `H.nodes[k]?`) with sel = some (g, 1). CUC §9.2 DEC(τ-irr): k′ ≥ 1
  reads with THE LAST saturated. Two drifts: (a) `1 ≤ k` at 0-indexed lookup
  excludes single-read (k′ = 1) saturated seams; (b) ∃-any-position vs
  last-position (a mid-history μ = 1 selection at a non-final node would satisfy
  the landed form). Whether the W-laws collapse (b) is NOT on record; as bare
  defs on `EHist` the drift stands.

**Fence note:** D-1..D-8 are all in UNLANDED displays (BP_III §1.3/§1.9 text) or in
LANDED-but-quarantined-by-BLOCKED-record positions (III-S1a's `DecIrr`/`DecHen`
are landed; the §4 units define seam-corrected predicates alongside, plus unit R1
records the divergence for the BP_III owner's adjudication — no landed statement
is edited by this group).

---

## §3 MEMBER-BY-MEMBER DOOR ASSIGNMENT + ARGUMENT SKETCHES

Door menu (directive): PROVE | LITERATURE-RETARGET | CONSTRUCTION-CONFORMANCE.
**LITERATURE-RETARGET is closed for every member**: all four are conformance
obligations about THIS project's engine/tables — no published statement is about
our records (the only adjacent literature, GMN Cor 1.20/3.8 + LIT-3 Hensel, is
consumed by Lemma CU-2t ITSELF via the pinned §3.3 rows, not by the (H6) rows).

### 3.1 (T-DEC-dec) — door: CONSTRUCTION-CONFORMANCE (machine face largely on record)

**Content split.** (i) SOUNDNESS-of-site: verdict-carrying emissions occur only at
DEC configurations (jointly with (T-DEC-cor), §3.2). (ii) DISCIPLINE/completeness:
a run reaching a DEC configuration books there — the τ-irr booking at μ_last = 1,
the τ-hen booking at the base Hensel/−∞ site.

**Machine face on record (τ-irr leg).** `MovesT.V9_irrSat.irr_iff_mu_one`
(PROVED, Lean-core): `IrrHalts H ↔ ν.μ = 1` at the last node under `HistLawful`.
This IS O-1thr §1.4's "IrrHalts ⟺ μ_last = 1" at the corpus. The conformance
theorem (unit B3a) re-keys it through the dress `machineProj` (landed, CU-1
III-U1) to the seam-corrected `DecIrrSeam`: a coherent lawful machine history
IrrHalts-halts iff its dressed continuing part is a DecIrrSeam. Honest open
points: (a) `machineProj`'s EWF certificate carries the ONE recorded W3 sorry
(interior μ ≥ 2 is decision-layer, not coherence — CU1.lean unit-III-U1 record);
the unit consumes `machineProj.val` fieldwise lemmas only, NOT the EWF subtype
row, so the W3 sorry is not inherited — verify at gate. (b) The sel-transport
(machine `Node.μ/g` ↦ E-side `ENodeData.sel`) is `nodeToE`'s per-field lemma —
cite, don't re-prove.

**τ-hen leg.** The base booking (a₀ = 1 or j₀ = 1) is the root reduction datum
(MovesT §2.3 (τ-hen)); at a₀ = 1 the seam object is (ρ₀) + machine record with NO
terminal ENodeData (CUC §9.1 carrier note, R4 M-γ: W3 permits a terminal NODE only
at a₀ ≥ 2). The row's ∃-emission clause is therefore GUARDED at `2 ≤ H.a0` on the
hen leg (§4 A7's `tDECdec` field — the a₀ = 1 booking is carried by the machine
record, priced at the CU-4/Dfloor face, not by this row). This guard is the R4
M-γ display transcribed; WITHOUT it the row would over-assert and be refutable at
a₀ = 1 Hensel sites.

### 3.2 (T-DEC-cor) — door: CONSTRUCTION-CONFORMANCE (exhaustiveness = leaf catalogue)

**Content.** Verdict-carrying emission sites ⊆ DEC ∪ DeepCorner (k′ ≥ 1, μ_{k′} ≥ 2,
j₀ = 1 at level k′+1). At the AS-BUILT engine the τ-irr rule fires ONLY at
saturation (the `IrrHalts` equation; `irr_iff_mu_one` forces μ_last = 1 under
lawfulness) and the τ-hen rule only at the base — so the as-built engine plausibly
NEVER corner-books, discharging the fence VACUOUSLY at the engine. Sketch (unit
B3b): the corpus leaf catalogue — a leaf is IrrHalts / hen-booked / ns-booked;
ns-leaves are fenced off the carried tree by the Unit-C `NsFree` conjunct on
`bridgeTree` (LANDED 2026-08-05 dispatch, ledger "UNIT C EXECUTED"); IrrHalts ⇒
DecIrrSeam (B3a); hen-booked ⇒ DecHenSeam. Honest open points: (a) the leaf
trichotomy at the carried tree needs the `VTree.chains`/leaf-species inventory —
quarry `MovesT/E9_fiberDisjoint.lean` (its proof case-splits on `IrrHalts H` at a
leaf) and `MovesT.Defs.IrrHaltsAsChild`; whether a clean "leaf ⇒ IrrHalts ∨ hen ∨
ns" lemma exists on record is UNVERIFIED — if absent, B3b states it as the unit's
one honest sorry with the inventory routed to the GD-4 owner brief (CUC §9.4 scope
note: the §9.2a inventory closure rides the same note). (b) corner-unreachability
is engine-strength: do NOT claim it for the PAPER machine (GD-8 territory —
whether the paper engine ever corner-books is explicitly GD-8, CUC §9.4).

### 3.3 (T-READ) — doors split per the R4 grading (the genuinely mathematical member)

**(a) k′ = 0 leg (DEC(τ-hen); OL-5-type terminal sibling, owed from scratch) —
door: PROVE, at the corpus base-polygon layer.** Statement: at a hen-decided seam
the emitted record's (e, h, ℓ, s, u) equal the (c1)-shape datum of the unique side
of N₁⁻(f) (a₀ = 1 ∧ j₀ = 0 branch: the unique finite side, length 1 — CUC §9.3(i)
"total length 1 and exactly one side"; j₀ = 1 branch: the slope-−∞ side, length 1,
§9.2 convention). Proof route: level 1 is UNCONDITIONAL territory ("level 1
unconditional" — the (c1) display's own bracket); the corpus has the real polygon
API (`OM/` NPVertices modules; `DictIII/O2aOrder1.lean`'s order-≤ 1 `GMNData`
construction + `laws_pin_fields` + the `ol6Gate` world; `DictIII/GDOrder1.lean`).
Sketch: (i) construct the level-1 `GMNData` from the corpus polygon of f̄/f
w.r.t. φ₁ = the ψ̂₀-lift (III-A6's landed constructor); (ii) the discipline: at
a₀ = 1 Hensel bookings the residual factor is simple ⇒ N₁ side unique of length 1
(the (D3)/(L3+) PROVED face); at j₀ = 1 the exact-key −∞ side (division
witness); (iii) the emitted record's fields are WRITTEN from that read — this is
where the machine-side home must first EXIST: depends on unit C0 (TRM). HARD;
the ONE member-leg where new mathematics-grade Lean proof is owed with no
sibling anywhere in the OL residue.

**(b) k′ ≥ 1 terminal-BINDING clause (GD-4 bookkeeping) — door:
CONSTRUCTION-CONFORMANCE.** "The emitted terminal record IS the record of the
level-(k′+1) stage read" — the exact clause OL-6 supplies for continuing records
and exempts for terminal ones. At the corpus: the leaf's record fields are read
data BY CONSTRUCTION (Node fields are the read's outputs; `MovesJ.ReadsOf`'s
per-read clause `SideReads (H.nodes[i]) B Nd Φnext` pins each recorded node to
f's development in frame i). The terminal analogue: once C0 materializes the
terminal read, the binding is definitional-to-easy (the emitted ν is DEFINED as
that read's record). MED.

**(c) k′ ≥ 1 read-semantics half (OL-2-min instance) — door: PROVE at order ≤ 1,
DISPLAY-ROUTE at order ≥ 2.** The math half is an OL-2-min INSTANCE at level
k′+1 (CUC §9.4 pricing: "already-priced GD-2-family residue"). Order ≤ 1: prove
against the landed order-≤ 1 dictionary (`GDOrder1`/`O2aOrder1` — the same
read-conformance content CU-1's step consumed; VERIFIED leaf #4's Lean face).
Order ≥ 2: rides (H1) — the H1 lead's group; this blueprint only DISPLAYS the
routing (`OL2min` at the requested level enters as a named hypothesis; NO
order-≥ 2 proof is attempted here). The unit displays the exact split so the
residue is priced once, at (H1).

### 3.4 (T-VERD) — door: CONSTRUCTION-CONFORMANCE (record function, quarry on record)

Machine face: `irrVerdictOf H = irrVerdict (max (accE H) 1) (max (accF H) 1)` —
definitionally the record function; T-V8's `acc_pos` kills the max-guards under
`NodeDataLawful`; `henVerdict g` at the base. The conformance content (unit B2):
the DRESS COMMUTATION — the E-side record function equals the machine's through
`machineProj`: `eAccE (machineProj M hM).val.continuingPart = MovesT.accE M`
(resp. eAccF/accF with the f₀ factor bookkeeping). Sketch: `machineEHist`'s
fieldwise lemmas (nodeToE per-field: `e ↦ e`, selections `(g, μ) ↦ sel`) +
`List.map` over the node re-key; the root-datum split (machine root read ↦
(ψ̂₀, a₀)) supplies the f₀ factor. **Definitional risk flagged for review:** the
E-side `eAccF := f₀ · ∏ (sel g's)` (§4 A1) must match O-2a Thm 2(B)'s
(accE_{k′}, accF_{k′}); the k′ = 0 boundary forces the f₀-included form
((accE₀, accF₀) = (1, f₀) — CUC §9.2 verdict display), and the machine's
`accF = ∏ ν.g` includes the root node's g = f₀ (root read = residue-factor
choice), so the two factorizations must reconcile through the root-datum split.
This reconciliation IS unit B2's content — if it fails at the as-built nodeToE,
the failure is a compiled obstruction to report, not to paper over. MED.

### 3.5 D-11 item (vii) — door: CONSTRUCTION-CONFORMANCE at n ≤ 3 (sealed flags);
general n stays [M] with an honest typing device

At HEAD there is NO Lean carrier for the H-LIST height-resummation domains or the
six fence kernels (they live in the tree/assembly notes, [2b]-parked). Faithful
Lean options considered: (i) transcribe the six kernels as typed general lemmas —
REJECTED: the kernels are explicitly OFF the mandatory path ("consumed by no
mandatory step" — VC10's hunt confirmed zero consumption); transcribing them
as provable statements would ADD open mathematics the root does not consume
(exactly the escalation the ROOT row fences). (ii) The `RootHyps` transcription
device (corpus precedent, `Scaffold/Hypotheses.lean` header): a plain structure
with the six fences as named bare-`Prop` slots + the conformance conjunction,
True-instantiable, with the header honesty note verbatim ("the conditionality
claim of record MUST list consumed fields as UNPINNED named assumptions until
their typed carriers land"). CHOSEN: (ii) at unit D2, typed-upgrade path
displayed: when the value-side H-LIST carrier lands (D-11/BP_IV territory), each
slot is re-typed at it and this row's device note is retired. The n = 3 sealed
gates (V-n3 178/178, H-n3 151/151, off-census q = 16/25 — `verification/`
artifacts of the T-5/T-7 dual acceptance) are cross-referenced as FLAGS in the
docstring; no Lean `decide` gate is feasible (the gates are PARI/sympy sealed
runs, not Lean-computable at HEAD). The escalation fence is displayed in the
docstring verbatim. Consumption keying: Step 18's K3-a — the row rides into
`RootRows.FenceVII n` (unit D3) and `RootHyps.h6_vii`'s intended instantiation
(unit D4).
