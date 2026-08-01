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

---

## §4 LEAN UNIT SPECS (all statements probe-verified 2026-08-05; see header)

**Target directory:** `lean/LeanUrat/Scaffold/HDischarge/H6/` — new modules in
`namespace LeanUrat.Scaffold.HDischarge.H6`, imports by module as probed:
`Mathlib`, `LeanUrat.Scaffold.DictIII.{CU2t, Hyps, CU1}`, `LeanUrat.MovesU.DefsLedger`,
`LeanUrat.MovesT.V9_irrSat`, `LeanUrat.Scaffold.ValueSide.Hyps`, `LeanUrat.HC2.Defs`.
File plan: `Emission.lean` (A1–A7), `EngineConform.lean` (B0–B3), `TerminalRead.lean`
(C0–C2), `RowsK4.lean` (D1), `Fence.lean` (D2), `RowStatements.lean` (D3–D4),
`Reconcile.lean` (R1). Standing variable block per file:
`variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]` +
`open LeanUrat.Scaffold.DictIII` + `open LeanUrat.MovesU`.

### Wave A — carriers + the repaired rows (statement-only; no proofs beyond MECH)

**A1 (MECH).** E-side accumulators (cures defect D-6; the architect-ruling
proposal the III-H9 BLOCKED block requested):
```lean
def eAccE (H : EHist p F) : ℕ := (H.nodes.map fun ν => ν.e).prod

def eAccF (H : EHist p F) : ℕ :=
  H.psi0.natDegree * (H.nodes.map fun ν => (ν.sel.elim 1 Prod.fst)).prod
```
Deps: —. Gate: at `H.nodes = []` both reduce to `(1, f₀)` by `simp` (the CUC
§9.2 k′ = 0 boundary (accE₀, accF₀) = (1, f₀) — an `example` lands with the unit).

**A2 (EASY).** Seam decidedness, repaired (cures D-7/D-8 alongside the landed
predicates — NEW names, fenced pair untouched):
```lean
def DecIrrSeam (H : EHist p F) : Prop :=
  H.nodes ≠ [] ∧
    (H.nodes.getLast?.elim False fun ν => ∃ g, ν.sel = some (g, 1))

def DecHenSeam (f : Polynomial ℤ_[p]) (H : EHist p F)
    (D : GMNData f (Theta H)) : Prop :=
  H.nodes = [] ∧
    (H.a0 = 1 ∨ ∃ S ∈ D.principalSides 0, S.isNegInfty = true)

def DecSeam (f : Polynomial ℤ_[p]) (H : EHist p F)
    (D : GMNData f (Theta H)) : Prop :=
  DecIrrSeam H ∨ DecHenSeam f H D
```
Reading: H is 𝐇° (the seam continuing part; all nodes selection-carrying —
enforced at consumption via `TerminalEmission.reaches_continuing`, A6). Deps: —.

**A3 (EASY).** The deep exact-key corner (CUC §9.4 (T-DEC-cor) shape):
```lean
def DeepCorner (f : Polynomial ℤ_[p]) (H : EHist p F)
    (D : GMNData f (Theta H)) : Prop :=
  H.nodes ≠ [] ∧
    (H.nodes.getLast?.elim False fun ν => ∃ g μ, ν.sel = some (g, μ) ∧ 2 ≤ μ) ∧
    ∃ S ∈ D.principalSides H.nodes.length, S.isNegInfty = true
```
Deps: —. (Level convention, displayed: `D.principalSides i` at 0-indexed i =
the paper's level-(i+1) read; `H.nodes.length = k′` ⇒ index k′ = level k′+1 —
the same convention as BP_III §1.9's `cu2t_readForcing`.)

**A4 (EASY).** The forced terminal datum, repaired (cures D-5/D-6):
```lean
structure TerminalDatumD where
  slope : Option (ℕ × ℕ)
  verdict : ℕ × ℕ

open scoped Classical in
noncomputable def terminalDatumD (f : Polynomial ℤ_[p]) (H : EHist p F)
    (D : GMNData f (Theta H)) : TerminalDatumD :=
  { slope := (D.principalSides H.nodes.length).head?.bind fun S =>
      if S.isNegInfty then none else some (S.e, S.h)
    verdict := if DecIrrSeam H then (eAccE H, eAccF H) else (1, H.psi0.natDegree) }
```
Deps: A1, A2. (`head?` is junk-tolerant; on DEC seams the side is forced unique —
the wave-5 forcing lemma III-S4 remains BP_III's unit and is NOT re-owned here.)

**A5 (EASY).** Definition RC, repaired (cures D-5's downstream; CUC §9.2a at
the corrected keying):
```lean
def RCConsistentD (f : Polynomial ℤ_[p]) (H : EHist p F)
    (D : GMNData f (Theta H)) (ν : ENodeData) (EF : ℕ × ℕ) : Prop :=
  ν.sel = none ∧
  (∃ S ∈ D.principalSides H.nodes.length,
    (ν.e, ν.h, ν.ℓ, ν.s, ν.u) = (S.e, S.h, S.ℓ, S.s, S.u)) ∧
  EF = (terminalDatumD f H D).verdict
```
Deps: A4. Non-circularity displayed in the docstring (D is polygon data of f
over Θ(𝐇°); no clause mentions the true factor — CUC §9.2a's display
transcribed). The §9.2a datum-granularity caveat rides the docstring (field
inventory closure is GD-4-owner territory, consumed by nothing here).

**A6 (EASY).** The terminal-emission interface (the quantifier domain the CUC
§9.4 rows need and the BP_III display lacked — the root cause of D-1..D-4):
```lean
structure TerminalEmission (p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] where
  reaches : Polynomial ℤ_[p] → EHist p F → Prop
  emits : Polynomial ℤ_[p] → EHist p F → ENodeData → (ℕ × ℕ) → Prop
  emits_terminal : ∀ f H ν EF, emits f H ν EF → ν.sel = none
  emits_reaches : ∀ f H ν EF, emits f H ν EF → reaches f H
  reaches_continuing : ∀ f H, reaches f H → ∀ ν ∈ H.nodes, ν.sel ≠ none
```
Deps: —.

**A7 (EASY, statement-only).** THE REPAIRED (H6) TRIO (supersedes III-H5's
display; cures D-1..D-4):
```lean
structure TerminalSeamHypsE (p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] (E : TerminalEmission p F) : Prop where
  tDECdec : ∀ f H (D : GMNData f (Theta H)),
    E.reaches f H → (DecIrrSeam H ∨ (DecHenSeam f H D ∧ 2 ≤ H.a0)) →
    ∃ ν EF, E.emits f H ν EF
  tDECcor : ∀ f H ν EF (D : GMNData f (Theta H)),
    E.emits f H ν EF → DecSeam f H D ∨ DeepCorner f H D
  tREAD : ∀ f H ν EF (D : GMNData f (Theta H)) (R : GMNReader f (Theta H) D),
    E.emits f H ν EF → DecSeam f H D → ConsF f H D R →
    ∃ S ∈ D.principalSides H.nodes.length,
      (ν.e, ν.h, ν.ℓ, ν.s, ν.u) = (S.e, S.h, S.ℓ, S.s, S.u)
  tVERD : ∀ f H ν EF (D : GMNData f (Theta H)),
    E.emits f H ν EF → DecSeam f H D →
    EF = (terminalDatumD f H D).verdict
```
Deps: A2, A3, A4, A6. Field ↔ CUC row map in the docstring (tDECdec = emission
discipline with the a₀ ≥ 2 hen guard per R4 M-γ, §3.1; tDECcor = the corner
fence/exhaustiveness; tREAD = (RC-read) supply; tVERD = (RC-verd) supply; the RC
tie: emits + DecSeam + tREAD + tVERD ⇒ `RCConsistentD` — unit D1's lemma). These
rows are [M]: statement-only here; discharge = waves B/C at the canonical engine
+ the ROOT-level adjudication.

### Wave B — construction-conformance at the as-built engine

**B0 (EASY, statement-only).** Engine-tie canonicity (what "the engine's
emission" means; deliberately does NOT tie shape fields — (T-READ)'s machine
home is owed, §3.3(a)):
```lean
structure EngineTied (n p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] (E : TerminalEmission p F) : Prop where
  reaches_engine : ∀ f H, E.reaches f H →
    ∃ M : MovesC.History p F, MovesC.HistoryCoherent M ∧
      LeanUrat.MovesJ.ReadsOf p F n f M ∧
      (machineEHist M).continuingPart = H
  emits_irr_verdict : ∀ f H ν EF, E.emits f H ν EF → DecIrrSeam H →
    ∃ M : MovesC.History p F, MovesC.HistoryCoherent M ∧
      LeanUrat.MovesJ.ReadsOf p F n f M ∧
      (machineEHist M).continuingPart = H ∧
      MovesT.IrrHalts M ∧
      EF = (MovesT.accE M, MovesT.accF M)
```
Deps: A2, A6; corpus `machineEHist` (CU1, landed; used INSTEAD of `machineProj`
— FOOTPRINT RULE: `machineProj` bundles the `EWF` certificate whose W3 row is
CU1's one recorded honest sorry, so any statement binding it inherits `sorryAx`;
`machineEHist` is the certificate-free value (`machineProj_val`), keeping every
H6 row Lean-core-eligible; coherence rides as an explicit conjunct),
`MovesJ.ReadsOf` (HC2/Defs), `MovesT.IrrHalts/accE/accF`.

**B1 (MED).** The canonical site/verdict emission `engineEmissionSV n p F :
TerminalEmission p F`: `reaches` := B0's `reaches_engine` right-hand side;
`emits` := B0's `emits_irr_verdict` right-hand side on the irr leg + the hen
booking on the base leg, ν existentially free in shape fields AT HEAD
(docstring: the shape supply is unit C0's TRM; until C0 lands, `tREAD` at this
emission is intentionally NOT provable — the honest state). Prove the three
interface laws + `EngineTied n p F (engineEmissionSV n p F)`. Deps: B0.

**B2 (MED).** (T-VERD) dress commutation at the engine:
`eAccE (machineProj M hM).val.continuingPart = MovesT.accE M` (resp. eAccF/accF
with the f₀ root-datum split — §3.4's flagged reconciliation; statement finalized
against `machineEHist`'s fieldwise lemmas at E-phase). If the as-built nodeToE
refutes the f₀ factorization, report the compiled obstruction verbatim — do NOT
adjust `eAccF` silently. Then `tVERD` for `engineEmissionSV` on the irr leg.
Deps: A1, B1; quarry `machineEHist` fieldwise lemmas (CU1), T-V8 `acc_pos`.

**B3a (MED).** (T-DEC-dec) at the engine: via `MovesT.irr_iff_mu_one` (PROVED) +
the nodeToE sel-transport — a lawful coherent M IrrHalts iff its dressed
continuing part is `DecIrrSeam`; conclude `tDECdec`'s irr leg for
`engineEmissionSV`. Hen leg (a₀ ≥ 2 booking from the root-datum split) may split
off as B3a′. Deps: B1; quarry `irr_iff_mu_one`, `HistLawful`.

**B3b (HARD).** (T-DEC-cor) at the engine: the leaf catalogue (leaf ⇒ IrrHalts ∨
hen-booked ∨ ns-booked) + `NsFree` fencing (Unit C's landed `bridgeTree`
conjunct) ⇒ `tDECcor` for `engineEmissionSV` with `DeepCorner` never reached.
Honest sorry permitted at the catalogue lemma if absent from the corpus (§3.2
open point (a)); the sorry's row routes to the GD-4 owner brief. Deps: B1, B3a;
quarry `E9_fiberDisjoint`, `IrrHaltsAsChild`, `MovesT.NsFree`, `bridgeTree`.

### Wave C — the (T-READ) mathematics

**C0 (HARD, design-first).** TRM — the terminal-read materialization: a NEW def
at the machine leaf producing the level-(k′+1) read record (the machine-side
home CUC §9.4 says is "purely owed"). Design constraints: (i) extends the
`ReadsOf` per-read clause pattern (`IsDevelopment` + `SideReads` at index
`H.nodes.length`, no successor key demanded); (ii) touches NO fenced
MovesC/MovesT statement — a NEW `terminalReadRecord` def + its `SideReads`-style
spec; (iii) its E-side dress fills `engineEmissionSV`'s ν slot (upgrading B1's
existential freedom to the definite emission `engineEmission`; `EngineTied`
re-proof rides along). Deliverables: def + spec + upgraded emission. The final
signature is the unit prover's E-phase probe duty (this blueprint fixes design
constraints, not the signature — flagged, not fenced).

**C1 (HARD).** (T-READ) k′ = 0 conformance at order ≤ 1 (§3.3(a), the PROVE
door): `tREAD` for `engineEmission` restricted to `DecHenSeam` seams, against
the order-≤ 1 `GMNData` constructor. Both branches (a₀ = 1 unique finite side;
j₀ = 1 slope-−∞ side). Deps: C0; quarry `DictIII/O2aOrder1.lean`
(`laws_pin_fields`, `ol6Gate`), `OM/` polygon modules (`rg "NP|polygon"
LeanUrat/OM` before E-phase), `DictIII/GDOrder1.lean`.

**C2 (MED).** (T-READ) k′ ≥ 1: the terminal-binding clause at the engine
(definitional once C0 lands — §3.3(b)) + the OL-2-min instance routing (§3.3(c)):
`tREAD`'s k′ ≥ 1 face proved from `OL2min` at the requested level AS A NAMED
HYPOTHESIS + the binding; order ≤ 1 instance discharged from GDOrder1, order ≥ 2
displayed as the (H1) consumption (NO proof attempted — one displayed router
lemma). Deps: C0; `DictIII/Hyps.OL2min`.

### Wave D — packaging: the K4 row, the fence device, RootRows

**D1 (EASY).** THE K4-FACING ROW + the RC tie lemma (unblocks BP_IV S5b/D4).
**Form-fixing self-catch (pre-Codex, recorded as defect D-9 against this
blueprint's own first draft):** the ∀-form `∀ E, EngineTied → TerminalSeamHypsE`
is REFUTABLE — `EngineTied` deliberately leaves emitted SHAPE fields untied
(§3.3(a): the machine home is owed), so an adversarial engine-tied emission
pairing a genuinely machine-realized decided seam (non-vacuity anchor: U31
`gate_readsOf_inert2` supplies realized `ReadsOf` histories) with junk-shape ν
violates tREAD while satisfying every `EngineTied` field. The faithful closed
form is EXISTENTIAL-WITH-COVERING — "a conformant emission presentation of the
engine exists, covering every machine-realized seam":
```lean
def EngineCovers (n p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] (E : TerminalEmission p F) : Prop :=
  ∀ (f : Polynomial ℤ_[p]) (H : EHist p F),
    (∃ M : MovesC.History p F, MovesC.HistoryCoherent M ∧
      LeanUrat.MovesJ.ReadsOf p F n f M ∧
      (machineEHist M).continuingPart = H) →
    E.reaches f H

structure TerminalSeamRows (n p : ℕ) [Fact p.Prime] (X : ClassifierSpec n p)
    (FF : FiberSeries n p X) : Prop where
  seam : ∀ (F' : Type) [Field F'] [Finite F'],
    ∃ E : TerminalEmission p F',
      EngineTied n p F' E ∧ EngineCovers n p F' E ∧ TerminalSeamHypsE p F' E
```
(EngineCovers signature to be probed by the unit prover at E-phase — it reuses
B0's `reaches_engine` right-hand side verbatim, so no new elaboration risk; the
∃/covering combination excludes both failure modes: the all-False emission fails
covering wherever a realized seam exists, and adversarial junk emissions are not
demanded to conform — only the WITNESS is.) Discharge shape: C0's TRM +
waves B/C construct the witness. Plus
`rc_of_rows : TerminalSeamHypsE … → E.emits f H ν EF → DecSeam f H D →
ConsF f H D R → RCConsistentD f H D ν EF` (the §9.4 tie — the repaired III-S8).
Probed: the S5b-shaped binder context `(seam : TreeSeam n p X FF)
(K4 : TerminalSeamRows n p X FF)` elaborates GREEN (structure shape unchanged
by the field's internal form). Keying honesty (docstring, verbatim): the (X, FF)
keys are the CONSUMPTION-SITE keys; `ClassifierSpec` is abstract (no run
structure), so the label tie "X's leaf labels are the engine's announced
verdicts" is the BP_VI spine's instantiation seam, NOT statable here — the keys
are phantom at HEAD. **DESIGN QUESTION (displayed for the Codex pass + the
orchestrator):** phantom keys vs. a label-tie field once Movement I exposes the
classifier's run structure; adding a field later is a consumer-visible change —
flag at the BP_IV seam before landing it. Deps: A7, B0.

**D2 (MECH).** Item (vii)'s typing device (§3.5; the RootHyps precedent):
```lean
structure FenceVII (n : ℕ) (P : LeanUrat.Scaffold.ValueSide.AssembledPack n) where
  xhdDEx : Prop
  m4bTAud : Prop
  urCount : Prop
  xhdUX : Prop
  hListGen : Prop
  ePos : Prop
  inFence : xhdDEx ∧ m4bTAud ∧ urCount ∧ xhdUX ∧ hListGen ∧ ePos
```
Docstring carries VERBATIM: the six-fence roster with H.x pointers ((1)
XHD-d-EX(∂) H.2.3 · (2) M4b-T-AUD H.5.1 · (3) U-R-COUNT H.4.2/H.5.3 · (4)
XHD-u-X H.4.3 · (5) H-LIST-GEN beyond (TRI) · (6) E-POS ⟨w_E, v⟩ ≥ 1); the
sealed-flag note (V-n3 178/178, H-n3 151/151, off-census q = 16/25 — evidence,
not proofs); the escalation fence; the typed-upgrade path (re-type each slot at
the H-LIST carrier when D-11/BP_IV lands it); the RootHyps-header honesty note
(True-instantiable device — consumed fields are UNPINNED named assumptions until
typed). Deps: — (parallel with wave A).

**D3 (EASY).** RootRows H6 bodies (BP_V §5.4 coordination — delivered as
`HDischarge.H6.RowStatements` content for BP_V's `Scaffold/RowStatements.lean`
to re-export when it lands; NO local alias of any BP_V name): `TDecRow n` :=
A7's tDECdec + tDECcor faces ∀-quantified over (p, F′, engine-tied E); `TReadRow
n` := the tREAD face; `TVerdRow n` := the tVERD face; `FenceVIIRow n` := the D2
device's conformance face ∀-quantified over packs. E-phase probes each body
before landing. Deps: A7, B0, D2.

**D4 (MECH).** `RootHyps` intended-instantiation display: a doc block +
`example` showing `h6_tdec := TDecRow n` (etc.) — the typed carriers the
Hypotheses.lean header demands, displayed; NO edit to `Hypotheses.lean` (its
owner is the spine lead). Deps: D3.

**R1 (EASY).** Reconciliation record: `DecIrrSeam`/`DecHenSeam` vs the landed
`DecIrr`/`DecHen` — one lemma per direction where provable, one compiled
divergence witness per failure (D-7's trivial `GMNData` witness as an `example`;
D-8's position drift). Routed to the BP_III owner for the eventual
single-predicate adjudication. Deps: A2.

### Gates (falsifiers/numerics)

* **G1 (non-vacuity, MECH-MED, lands with A7):** a compiled countermodel
  emission `E_junk` with `¬ TerminalSeamHypsE p F E_junk` (junk shape fields at
  a decided seam violate tREAD/tVERD) — the repaired rows are NOT tautologies
  (the exact failure mode of the superseded III-H5 display, D-1..D-4).
* **G2 (positive gate, MED, lands with B1):** a toy seam + emission satisfying
  the trio WITH a witnessed reach and a witnessed emission
  (HK23_twoNodeGatePos style) — the rows are satisfiable NON-VACUOUSLY. The
  all-False emission satisfies `TerminalSeamHypsE` trivially (every field
  vacuous), so a gate without a positive reach/emit witness certifies nothing;
  this gate must exhibit both.
* **G3 (item (vii) flags, lands with D2):** docstring cross-reference to the
  sealed V-n3/H-n3 artifacts (no Lean gate feasible — §3.5).
* **Footprint:** per-file `lake env lean` during waves +
  `lake build LeanUrat.AxChk_baseline` at division checkpoints; footprint
  regression = stop-the-line (repo standing rule).

### Wave shape (dependencies; minimal, parallelizable)

```
A1 ∥ A2 ∥ A3 ∥ A6 ∥ D2          (5-way parallel start)
A4 (A1,A2) → A5 (A4)
A7 (A2,A3,A4,A6) [+G1] ; R1 (A2)
B0 (A2,A6) → B1 (B0) [+G2] → B2 (A1,B1) ∥ B3a (B1) → B3b (B1,B3a)
C0 (B1) → C1 (C0) ∥ C2 (C0)
D1 (A7,B0) → BP_IV S5b/D4 UNBLOCK NOTICE to the value-side owner
D3 (A7,B0,D2) → D4 (D3)
```
Critical path to unblocking BP_IV: A-wave → A7 → D1 (all EASY — one prover-day).
The open-mathematics core: C0 → C1 (HARD; (T-READ)'s k′ = 0 leg). Item (vii)'s
general-n content acquires NO proof unit here (correct: it is [M]; §3.5).

**Unit count: 18** (A1–A7, B0/B1/B2/B3a/B3b, C0–C2, D1–D4, R1) **+ 3 gates.**

---

## §5 CODEX ADVERSARIAL REVIEW (directive requirement)

Disposition table appended below after the review runs.
