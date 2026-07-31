/-  TV-F2 (BRIDGE BP3, cluster c5; E-phase skeleton) — the SHARED-WITNESS
    CO-DESIGN SEAM: the coherence laws tying the TV-F1 polynomial packs to the
    measured side's own fields (rowVal / μcell / ιsh / entCount), plus the
    EXPLICIT GATE DELIVERABLE (blueprint REV 2, finding 10): the jcell_sum
    candidate typed at the (T, M) keys BEFORE the TV-F5 prover runs.
    Blueprint: lean/notes/BRIDGE_BP3_TV_2026-07-30.md §3.E + §4 (TV-F2).
    deps: TV-E1, TV-E2 (the measuredOf carrier — see resolution (1)), TV-F1
    (the packs).  Consumers: TV-F3 (interp/degree laws), TV-F4 (cellP wiring),
    TV-F5 (assembly), TV-F6 (combined seam producer).

    RESOLUTIONS (recorded per the E-phase minimal-resolution rule):
    (1) TV-E1/E2's `measuredOf` is NOT on disk at writing time (the E-cluster
      writes concurrently), so the seam is typed PARAMETRICALLY over a pinned
      pair (T, M) with a KEYING CARRIER `SeamKeys` (the E-DEV-9 pattern —
      carrier typed in the consuming unit; precedent: TV_G1's parametric
      supply over (T, hp)).  The F-prover instantiates every ∃ below at the
      SHARED measuredOf witness once E1/E2 land (Q5 ruling: shared witness
      allowed; the sharing itself is certified by TV-F6's combined producer).
    (2) The coherence laws are stated in `MovesS.RatBurdens`' own evalAt form,
      with the OKat memberships carried as in-bundle fields (tg_ok/j_ok/…), so
      the TV-F5 re-packaging into RatBurdens is field-for-field.
    (3) `j_val` (rowVal = jP eval AT split routes) is typed here although the
      blueprint's F2 list names only the tgP leg at non-split routes: F3's
      "tg_interp/j_interp (routeOf case split)" requires the split-route row
      leg, and the seam must supply it — minimal resolution, recorded.
    (4) GATE DELIVERABLE: `SeamCoherent.jcell_sum` is the jcell_sum candidate
      at the (T, M) keys ("jP := the cell sum at split routes"); the
      datum-keyed candidate is TV-F1's `jPGof_val` (typed there, as its
      docstring records).  Both are now TYPE-CHECKED claims, discharging the
      REV-2 gate duty at the seam rather than in the prover.
    (5) `hdom : EntDomOrder0 V` rides the ι-leg (TV-F1's `iotaPGof` requires
      it) — an EXTRA named premise beyond `ratBurdens_exists`'s row
      (V7_rbC.lean:42).  Whether it leaks into the final assembly is TV-F5's
      "verify no E-only premise leaked" duty; the byte-identical pack there
      does NOT carry it — if the prover cannot discharge it from the row, the
      exit is escalation (named-hypothesis addition, flagged), never a forced
      proof.
    (6) Keying faithfulness is carried by the coherence laws themselves; the
      two typing-time compatibility fields (`datum_term`, `cellKey_out`) are
      the minimal recorded ties.  Adjusting them is a co-design-seam move on
      THESE new carriers only (record at this docstring) — never on the
      RatBurdens interface.
    [QUEUE ITEM 14 EXECUTED, 2026-07-31 (Asvin sign-off; ledger
    lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md item 14): `ratBurdens_iota`
    re-pointed at initRat_comp's FULL 4-conjunct ∃ (V7_rbB) + the TV-F1 spec
    projections `iotaPGof_census`/`iotaPGof_val` — the SeamCoherent ι-legs
    (iota_ok/iota_val/iota_count) are now PROVED at the measuredOf witness
    for any entKey-canonical keying: TV_F2b.lean (this file untouched except
    this record — no import-graph change).  `seam_coherence_exists` below
    keeps its ONE honest sorry for the remaining legs: `tg_val` is BLOCKED
    on the named Phase-B row `RealizationComplete` (V2_valB:272 — the val_b
    rowVal bridge; see the TV_F2b header record), `j_val`/`jcell_val`/
    `jcell_sum` remain with the F-prover (μcellH re-index), and the full
    SeamKeys witness (datum/cellKey fields) remains the co-design
    construction duty.] -/
import LeanUrat.MovesV.TV_F1
import LeanUrat.MovesV.V7_ts

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.MovesV

/-- TV-F2 keying carrier: how the table-side keys (e, τ, o / cells /
entrance shapes) read back into the CTS datum vocabulary that TV-F1's packs
are keyed by.  At the intended witness (tableShape_inst's literal table +
measuredOf) every field is the evident projection (all equivs `Equiv.refl`).
`datum_term` records the cont/terminal case split (an outcome of the pinned
table is exactly a MoveData/TermData — TV-F1's recorded resolution);
`cellKey_out` ties a split-route cell's datum to its outcome's datum. -/
structure SeamKeys {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (T : MovesS.TableShape n)
    (M : MovesS.MeasuredSide T) where
  datum : ∀ e (τ : T.State e), T.Out e τ →
    MoveData n C ⊕ (Σ v : VLabel n, TermData n C v)
  datum_term : ∀ e (τ : T.State e) (o : T.Out e τ),
    (datum e τ o).isRight = true ↔ MovesS.routeOf (T.odata e τ o) = .termFin
  cellKey : ∀ e (τ : T.State e), M.Cell e τ →
    Σ d : MoveData n C, V.DCellO d.s d.m d.o d.α
  cellKey_out : ∀ e (τ : T.State e) (c : M.Cell e τ),
    MovesS.routeOf (T.odata e τ (M.cellOut e τ c)) = .split →
    Sum.inl (cellKey e τ c).1 = datum e τ (M.cellOut e τ c)
  entKey : ∀ e (τ : T.State e), M.EntShape e τ → Σ β₀ : S.Cell, V.EntIx β₀

/-- TV-F2 pack, tg leg: the (iv)-POLY pack of a table outcome, through the
keying (continuing datum → `tgPGof`, terminal datum → `tgPGofT`). -/
noncomputable def seamTgP {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S} (X : XHD n S TE V)
    (cp : CellPolyPack n C S V) {T : MovesS.TableShape n}
    {M : MovesS.MeasuredSide T} (K : SeamKeys V T M)
    (e : ℕ) (τ : T.State e) (o : T.Out e τ) : MovesS.PolyGeom :=
  match K.datum e τ o with
  | .inl d => tgPGof V X cp d
  | .inr vd => tgPGofT V X cp vd.2

/-- TV-F2 pack, J leg: the per-outcome J pack through the keying (split
routes are continuing, so the `.inr` filler `tgPGofT` is never consumed by a
split-guarded law — recorded; the total data field is demanded by
`RatBurdens.jP`). -/
noncomputable def seamJP {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S} (X : XHD n S TE V)
    (cp : CellPolyPack n C S V) (J : JCells n C S V)
    {T : MovesS.TableShape n} {M : MovesS.MeasuredSide T}
    (K : SeamKeys V T M) (e : ℕ) (τ : T.State e) (o : T.Out e τ) :
    MovesS.PolyGeom :=
  match K.datum e τ o with
  | .inl d => jPGof V X cp J d
  | .inr vd => tgPGofT V X cp vd.2

/-- TV-F2 pack, per-cell J leg: TV-F1's `jCellPGof` (= the PRESCRIBED
`jcellPG`) at the keyed (datum, digit cell) of a measured cell. -/
noncomputable def seamJPCell {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {TE : TmplEvents n S} (X : XHD n S TE V)
    (cp : CellPolyPack n C S V) {T : MovesS.TableShape n}
    {M : MovesS.MeasuredSide T} (K : SeamKeys V T M)
    (e : ℕ) (τ : T.State e) (c : M.Cell e τ) : MovesS.PolyGeom :=
  jCellPGof X cp (K.cellKey e τ c).1 (K.cellKey e τ c).2

/-- TV-F2 pack, ι leg: TV-F1's `iotaPGof` (choice over the PROVED
`ratBurdens_iota` ∃) at the keyed (pool cell, entrance index). -/
noncomputable def seamIotaP {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S} (X : XHD n S TE V)
    (hEU : EntU V) (hEC : EntCount V) (hA : AffEnt n) (hdom : EntDomOrder0 V)
    {T : MovesS.TableShape n} {M : MovesS.MeasuredSide T}
    (K : SeamKeys V T M) (e : ℕ) (τ : T.State e) (ε : M.EntShape e τ) :
    MovesS.PolyGeom :=
  iotaPGof V X hEU hEC hA hdom (K.entKey e τ ε).1 (K.entKey e τ ε).2

/-- TV-F2 THE SEAM-COHERENCE BUNDLE (blueprint §3.E / §4 TV-F2): the F3
interp laws stated against the co-designed measured fields — rowVal = tgP
eval at non-split routes (`tg_val`), rowVal = jP eval at split routes
(`j_val`, resolution (3)), μcell = jPCell eval at split routes (`jcell_val`),
ιsh = ιP eval (`iota_val`), entCount = ιP.countT eval (`iota_count`) — plus
the REV-2 GATE DELIVERABLE `jcell_sum` (jP := the cell sum at split routes,
type-checked here at the (T, M) keys; the datum-keyed candidate is TV-F1's
`jPGof_val`).  The OKat memberships ride as in-bundle fields so every value
law is in `MovesS.RatBurdens`' own evalAt form.  At the intended measuredOf
witness the value laws are rfl-or-lemma genre (the co-design: E1/E2 DEFINE
rowVal/μcell/ιsh/entCount as exactly these evaluations' carriers). -/
structure SeamCoherent {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S} (X : XHD n S TE V)
    (cp : CellPolyPack n C S V) (J : JCells n C S V)
    (hEU : EntU V) (hEC : EntCount V) (hA : AffEnt n) (hdom : EntDomOrder0 V)
    {T : MovesS.TableShape n} {M : MovesS.MeasuredSide T}
    (K : SeamKeys V T M) : Prop where
  tg_ok : ∀ e (τ : T.State e) (o : T.Out e τ) (q₀ : ℚ), q₀ ∈ M.Pools →
    (seamTgP V X cp K e τ o).val ∈ MovesS.OKat q₀
  tg_val : ∀ e (τ : T.State e) (o : T.Out e τ) (q₀ : ℚ) (h : q₀ ∈ M.Pools),
    MovesS.routeOf (T.odata e τ o) ≠ .split →
    ((MovesS.evalAt q₀ ⟨(seamTgP V X cp K e τ o).val, tg_ok e τ o q₀ h⟩ : ℚ) : ℝ)
      = M.rowVal e τ o q₀
  j_ok : ∀ e (τ : T.State e) (o : T.Out e τ) (q₀ : ℚ), q₀ ∈ M.Pools →
    (seamJP V X cp J K e τ o).val ∈ MovesS.OKat q₀
  j_val : ∀ e (τ : T.State e) (o : T.Out e τ) (q₀ : ℚ) (h : q₀ ∈ M.Pools),
    MovesS.routeOf (T.odata e τ o) = .split →
    ((MovesS.evalAt q₀ ⟨(seamJP V X cp J K e τ o).val, j_ok e τ o q₀ h⟩ : ℚ) : ℝ)
      = M.rowVal e τ o q₀
  jcell_ok : ∀ e (τ : T.State e) (c : M.Cell e τ) (q₀ : ℚ), q₀ ∈ M.Pools →
    (seamJPCell X cp K e τ c).val ∈ MovesS.OKat q₀
  jcell_val : ∀ e (τ : T.State e) (c : M.Cell e τ) (x : M.Rep e τ) (q₀ : ℚ)
    (h : q₀ ∈ M.Pools),
    MovesS.routeOf (T.odata e τ (M.cellOut e τ c)) = .split →
    M.activeState q₀ e τ →
    ((MovesS.evalAt q₀ ⟨(seamJPCell X cp K e τ c).val, jcell_ok e τ c q₀ h⟩ : ℚ) : ℝ)
      = M.μcell e τ x c q₀
  iota_ok : ∀ e (τ : T.State e) (ε : M.EntShape e τ) (q₀ : ℚ), q₀ ∈ M.Pools →
    (seamIotaP V X hEU hEC hA hdom K e τ ε).val ∈ MovesS.OKat q₀
  iota_val : ∀ e (τ : T.State e) (ε : M.EntShape e τ) (q₀ : ℚ)
    (h : q₀ ∈ M.Pools),
    ((MovesS.evalAt q₀ ⟨(seamIotaP V X hEU hEC hA hdom K e τ ε).val,
        iota_ok e τ ε q₀ h⟩ : ℚ) : ℝ)
      = M.ιsh e τ ε q₀
  iota_count : ∀ e (τ : T.State e) (ε : M.EntShape e τ) (q₀ : ℚ),
    q₀ ∈ M.Pools →
    ((seamIotaP V X hEU hEC hA hdom K e τ ε).countT.eval q₀ : ℚ)
      = (M.entCount e τ ε q₀ : ℚ)
  jcell_sum : ∀ e (τ : T.State e) (o : T.Out e τ),
    MovesS.routeOf (T.odata e τ o) = .split →
    ∑ c ∈ M.cells e τ o, (seamJPCell X cp K e τ c).val
      = (seamJP V X cp J K e τ o).val

/-- TV-F2 UNIT CLAIM (the co-design seam, gate-first): a pinned pair (T, M)
with a keying under which the TV-F1 packs cohere with the measured fields —
to be PROVED at the shared measuredOf witness (T := tableShape_inst's table,
M := the E1/E2 field map), where every value law is rfl-or-lemma genre.
Premise row = `ratBurdens_exists`'s row (V7_rbC.lean:42) + `hdom`
(resolution (5)).  Sketch: instantiate T/M/K at the literal witness; tg_val
via cp.count aggregated over the outcome fiber (the V4-6 μcellH carrier);
jcell_val via `jcellPG`'s val against μcellH (V5-7b); iota_val/iota_count via
`initRat_comp`'s spec projections (V7_rbB/V3-9c); jcell_sum by
`Finset.sum_congr` over the `J.bcells` roster re-indexed to `M.cells`
(TV-F1's `jPGof_val` is the datum-keyed form). -/
theorem seam_coherence_exists {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hTie : MDomTie V TE X.d) (J : JCells n C S V) (hEU : EntU V)
    (hEC : EntCount V) (hA : AffEnt n) (hdom : EntDomOrder0 V) :
    ∃ (T : MovesS.TableShape n) (M : MovesS.MeasuredSide T)
      (K : SeamKeys V T M),
      TablePins C T ∧
      (∀ q₀ ∈ V.Pools, ∀ N : ℕ, Nonempty (V.Box q₀ N) →
        Fintype.card (M.Box q₀ N) = @Fintype.card _ (V.finB q₀ N)) ∧
      SeamCoherent V X cp J hEU hEC hA hdom K := by
  sorry

end LeanUrat.MovesV
