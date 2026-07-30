/-  TV-E1 (BRIDGE BP3, cluster c4; E-phase skeleton) — `measuredOf` DATA
    BLOCK 1: the shared (V, X, cp)-keyed `MovesS.MeasuredSide` construction
    over the LITERAL tableShape_inst table.
    Blueprint: lean/notes/BRIDGE_BP3_TV_2026-07-30.md §3.E + §4 (TV-E1).
    deps: none.  Consumers: TV-E2 (data block 2), TV-E3/E4/E5a/E5b/E6 (the
    LedgerIV law groups), TV-E7 (assembly), TV-E8 (non-vacuity gate), and
    cluster F (TV-F2/F5 — the Q5-RULED SHARED witness).
    E-PHASE RESOLUTIONS (recorded per the statement-writer charge):
    (1) `tableShape_inst` (V7_ts:69) is an ∃-THEOREM, but the §3.E field map
        reads the table DEFINITIONALLY ("τ : T.State e = StateOf n C e =
        ⟨⟨s, α⟩, hblk⟩ and T.Out e τ = Σ m, Outc m — the tableShape_inst
        witness is literal, all equivs Equiv.refl").  A choice-extracted
        witness has no definitional face, so the witness is re-materialized
        VERBATIM as the def `ctsTable` below (body = tableShape_inst's own
        structure literal, V7_ts:100-131); `ctsTable_pins` restates its
        proved TablePins bundle.  Additive only — V7_ts is untouched.
    (2) `measuredOf` spans BOTH data blocks (a structure literal cannot be
        split across units): TV-E1 owns the def + the block-1 field pins;
        TV-E2 pins block 2 (entrance/kstep/activity) on the SAME def.
    (3) The prescribed field values ride as CO-DESIGN PIN lemmas (sorried,
        rfl-genre at the intended literal — the TV-F1 precedent); pins whose
        statement needs a cast across a pinned carrier equality (cellOut,
        μcell, cellEvt, Rep, cellLvl/cellInst, HDom) are NOT pre-typed:
        [REV 2, finding 13] the transport/equality lemma layer (Sigma-cell
        casts, double-dite definedness case lemmas, toStepCells transport)
        is the E-fleet's execution deliverable, with the pre-authorized
        E1a (carriers) / E1b (transport lemmas) split if over budget. -/
import LeanUrat.MovesV.V7_ts

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.MovesV

/-- TV-E1 [table carrier]: THE literal `tableShape_inst` witness as a DEF —
`State := StateOf n C` (the CellIdx-carrying block-e slice), `Out :=
Σ letter, outcome`, the REAL bounds `Wloc := C.Wloc` / `Wstate :=
(C.bd s).Wstate`, odata rosters through the attach map (all transcribed
verbatim from V7_ts:100-131, which compiled green).  `T := ctsTable C hfin`
is the ONE table every E/F-cluster unit shares (Q5 ruling).  deps: none. -/
noncomputable def ctsTable {n : ℕ} (C : CtsFamily n)
    (hfin : Finite (Skeleton n)) : MovesS.TableShape n where
  State := StateOf n C
  fin := fun e => by
    haveI := hfin
    have : Finite (StateOf n C e) := by unfold StateOf; infer_instance
    exact Fintype.ofFinite _
  deq := fun e => Classical.decEq _
  VType := VLabel n
  deqV := inferInstance
  finV := by
    haveI := hfin
    apply Fintype.ofInjective
      (β := Fin (n + 1) × Fin (n + 1))
      (fun v : VLabel n =>
        (⟨(v.1.1 : ℕ), by
            have h1 : ((v.1.1 : ℕ)) ≤ (v.1.1 : ℕ) * (v.1.2 : ℕ) :=
              Nat.le_mul_of_pos_right _ v.1.2.pos
            have := v.2; omega⟩,
         ⟨(v.1.2 : ℕ), by
            have h2 : ((v.1.2 : ℕ)) ≤ (v.1.1 : ℕ) * (v.1.2 : ℕ) :=
              Nat.le_mul_of_pos_left _ v.1.1.pos
            have := v.2; omega⟩))
    intro a b hab
    simp only [Prod.mk.injEq, Fin.mk.injEq] at hab
    apply Subtype.ext
    apply Prod.ext
    · exact PNat.coe_injective hab.1
    · exact PNat.coe_injective hab.2
  vdeg := fun v => v.1.1 * v.1.2
  vEquiv := Equiv.refl _
  vdeg_spec := by intro v; simp [PNat.mul_coe]
  Out := fun _ τ => Σ m : (C.bd τ.1.1).Letter, (C.bd τ.1.1).Outc m
  finO := by
    intro e τ
    haveI := (C.bd τ.1.1).finL
    haveI := (C.bd τ.1.1).finO
    infer_instance
  odata := fun _ τ o =>
    { mem := ((C.bd τ.1.1).omem o.1 o.2).attach.map (fun x =>
        { size := x.1.size
          δ := x.1.δ
          status := match hs : x.1.status with
            | Sum.inl v => Sum.inl v
            | Sum.inr sk => Sum.inr
                ⟨⟨sk, memberTgtCell C τ.1.2 x.1 x.2 hs⟩,
                  (C.bd τ.1.1).omem_size o.1 o.2 x.1 x.2 sk hs⟩ })
      hm := by
        have hne := (C.bd τ.1.1).omem_ne o.1 o.2
        intro hcontra
        apply hne
        simpa using hcontra }
  Wloc := fun _ τ o => C.Wloc τ.1.1 o.1
  Wstate := fun _ τ => (C.bd τ.1.1).Wstate

/-- TV-E1 [table pins]: `TablePins C (ctsTable C hfin)` — the proved bundle of
`tableShape_inst`, restated at the def.  Sketch: verbatim the first bullet of
tableShape_inst's proof (every equiv `Equiv.refl`, weight ties `rfl`, odata
tie through the attach map; V7_ts:132-147).  Supplies TV-E7's TablePins
conjunct.  deps: ctsTable. -/
theorem ctsTable_pins {n : ℕ} (C : CtsFamily n) (hfin : Finite (Skeleton n)) :
    TablePins C (ctsTable C hfin) := by
  sorry

/-- TV-E1 [roster nonemptiness]: the odata rosters of `ctsTable` are nonempty
(the second conjunct of `tableShape_inst`; proof = each odata's own `hm`). -/
theorem ctsTable_odata_ne {n : ℕ} (C : CtsFamily n)
    (hfin : Finite (Skeleton n)) :
    ∀ (e : ℕ) (τ : (ctsTable C hfin).State e) (o : (ctsTable C hfin).Out e τ),
      ((ctsTable C hfin).odata e τ o).mem ≠ [] := by
  sorry

/-- TV-E1 [the cell carrier, §3.E display]: `Cell e τ := Σ o : T.Out e τ,
DCellO s o.1 o.2 α` at τ = ⟨⟨s, α⟩, hblk⟩ — the per-outcome digit-cell fibers
of the CTS classifier (`cellOut := Sigma.fst` across this carrier). -/
def measCell {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (hfin : Finite (Skeleton n))
    (e : ℕ) (τ : (ctsTable C hfin).State e) : Type :=
  Σ o : (ctsTable C hfin).Out e τ, V.DCellO τ.1.1 o.1 o.2 τ.1.2

/-- TV-E1 (+ TV-E2 block 2): `measuredOf V X cp hfin` — THE real MeasuredSide
field map replacing the degenerate A28 core (V7_msA), keyed to (V, X, cp)
ONLY (the Q5 SHARED witness).  BLOCK 1 (this unit): `Pools := V.Pools` (the
three MeasuredSide pool laws ARE CtsCells' pools_pp/pools_closed/
pools_infinite, MovesV/Defs:685-689); `Box := V.Box`, `finB := V.finB`,
`boxpos := V.boxpos` (the guarded |Box| card tie becomes rfl-genre);
`Cell := measCell` with `cellOut := Sigma.fst`; `Hgt := Σ D : ℕ, Hpt D`;
`HDom` from the LISTED domains `V.cdom`/`V.cdomT` (the `cdomAllMem`
Σ-embedding pattern, V4_part1A); `μcell` := the μcellH carrier (V4-6,
V4_part1A:28); `cellEvt` := the REV-6 double-dite over `V.cellEvt`/
`V.cellEvtT` (definedness casing by route and assignment); `Rep` := the
REV-5 per-pool representative family (the E-phase notes in V7_msA's header
own the exact shape); `cellLvl`/`cellInst` wired per the Q5 RULING
(per-cell `cp.count` — adjudicated; the coarse sizeP/stInst option is
RETIRED).  BLOCK 2 (TV-E2): entrance block, activeState, rowVal, kstep,
markedVal/gwt residue fields.  The prescribed values are pinned by the
CO-DESIGN PIN lemmas here and in TV-E2; the cast-dependent pins are the
E-fleet's transport-layer deliverable [REV 2, finding 13].
deps: ctsTable, measCell. -/
noncomputable def measuredOf {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V)
    (hfin : Finite (Skeleton n)) :
    MovesS.MeasuredSide (ctsTable C hfin) :=
  sorry

/-- TV-E1 CO-DESIGN PIN: `Pools := V.Pools` (rfl-genre at the intended
literal; adjustable only with a record — the TV-F1 pin discipline). -/
theorem measuredOf_pools {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V)
    (hfin : Finite (Skeleton n)) :
    (measuredOf V X cp hfin).Pools = V.Pools := by
  sorry

/-- TV-E1 CO-DESIGN PIN: `Box := V.Box` (rfl-genre; makes TV-E7's guarded
|Box| cardinality tie rfl-genre modulo Fintype-instance transport). -/
theorem measuredOf_box {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V)
    (hfin : Finite (Skeleton n)) :
    (measuredOf V X cp hfin).Box = V.Box := by
  sorry

/-- TV-E1 CO-DESIGN PIN: `Hgt := Σ D : ℕ, Hpt D` (the Σ-embedded height
carrier of the μcellH/cdomAllMem pattern). -/
theorem measuredOf_hgt {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V)
    (hfin : Finite (Skeleton n)) :
    (measuredOf V X cp hfin).Hgt = (Σ D : ℕ, Hpt D) := by
  sorry

/-- TV-E1 CO-DESIGN PIN: `Cell e τ = measCell V hfin e τ` (the §3.E cell
carrier; the downstream cast layer across this equality is the E-fleet's
transport deliverable, finding 13). -/
theorem measuredOf_cell {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V)
    (hfin : Finite (Skeleton n)) :
    ∀ (e : ℕ) (τ : (ctsTable C hfin).State e),
      (measuredOf V X cp hfin).Cell e τ = measCell V hfin e τ := by
  sorry

end LeanUrat.MovesV
