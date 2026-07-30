/-  TV-F1 (BRIDGE BP3, cluster c2; E-phase skeleton) — the RatBurdens PolyGeom
    DATA MAP in the CTS vocabulary.
    Blueprint: lean/notes/BRIDGE_BP3_TV_2026-07-30.md §3.E + §4 (TV-F1).
    deps: none.  Consumers: TV-F2 (co-design seam), TV-F3 (interp/degree laws),
    TV-F4 (cellP wiring, Q5-ruled per-cell cp.count), TV-F5 (assembly at the
    shared measuredOf witness).
    Legs per the blueprint sketch:
      (a) tgP packs "from cp via dataOf/tblOf/pathProdPoly (V2-5)" — DATUM-keyed
          here (minimal resolution, recorded: an outcome of tableShape_inst's
          table is exactly a (s, m, o, α) tuple + a cont/terminal case split,
          i.e. a `MoveData`/`TermData`; the V2-5 `dataOf`/`tblOf` route recovers
          the same datum from a bare move through `moveOf_bij`, so keying the
          pack by the datum is the equivalent move-free form);
      (b) jP packs at split routes — the CELL SUM (jcell_sum forces
          jP := Σ_cells jPCell; the val-spec is displayed as `jPGof_val`);
      (c) jPCell := `jcellPG` (V5-7b) — PRESCRIBED BODY, transcribed verbatim;
          its countS = 1 leg is rfl (V7_rbA precedent, restated here);
      (d) ιP := choice over `ratBurdens_iota`'s ∃ (V7_rbB, proved) — PRESCRIBED
          BODY, transcribed verbatim with its two spec projections.
    CO-DESIGN PINS (recorded): `tgPGof_countT`/`tgPGofT_countT`/`jPGof_val` are
    F1-local typing-time pins on the sorried defs; the TV-F2 seam may adjust
    them (any adjustment is a statement change on THESE spec lemmas only, to be
    recorded at the F2 gate — never on the RatBurdens interface). -/
import LeanUrat.MovesV.V2_valB
import LeanUrat.MovesV.V7_rbB

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- TV-F1(a) [tg pack, continuing datum]: the (iv)-POLY pack presenting the
measured row value of the continuing outcome datum `d` (consumed by
`tg_interp` at non-split routes).  countT = the datum's own T-table entry
(the `tblOf` reading, pinned by `tgPGof_countT` below); countS = the
state-count leg and geom = the XHD-s height-sum leg are co-designed with
`rowVal` at the TV-F2 seam.  Sketch: transcribe `jcellPG`'s pack pattern at
the outcome level, with `cp`'s count polynomial aggregated over the outcome's
cell fiber and the `Gcell` height sums summed per `gcell_denom_sum`.
deps: none (V2-5 + V5-7b machinery, all proved). -/
noncomputable def tgPGof {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S} (X : XHD n S TE V)
    (cp : CellPolyPack n C S V) (d : MoveData n C) : MovesS.PolyGeom :=
  sorry

/-- TV-F1(a′) [tg pack, terminal datum]: the terminal twin of `tgPGof`
(`tblOfT` reading, `GcellT` height sums). -/
noncomputable def tgPGofT {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S} (X : XHD n S TE V)
    (cp : CellPolyPack n C S V) {v : VLabel n} (d : TermData n C v) :
    MovesS.PolyGeom :=
  sorry

/-- TV-F1 pin: `tgPGof`'s T-count leg IS the datum's table entry (the
`tblOf`/`dataOf` reading collapsed through `moveOf_bij` to the datum key).
CO-DESIGN PIN — adjustable only at the TV-F2 seam, with a record. -/
theorem tgPGof_countT {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S} (X : XHD n S TE V)
    (cp : CellPolyPack n C S V) (d : MoveData n C) :
    (tgPGof V X cp d).countT = C.T d.s d.m d.o d.α d.tix := by
  sorry

/-- TV-F1 pin, terminal twin. -/
theorem tgPGofT_countT {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S} (X : XHD n S TE V)
    (cp : CellPolyPack n C S V) {v : VLabel n} (d : TermData n C v) :
    (tgPGofT V X cp d).countT = C.T d.s d.m d.o d.α d.tix := by
  sorry

/-- TV-F1(c) [jPCell wiring]: PRESCRIBED BODY — "jPCell := jcellPG" (blueprint
§3.E; V5-7b's per-cell pack through `cp` and the XHD-s cell face). -/
noncomputable def jCellPGof {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {TE : TmplEvents n S} (X : XHD n S TE V)
    (cp : CellPolyPack n C S V) (d : MoveData n C)
    (c : V.DCellO d.s d.m d.o d.α) : MovesS.PolyGeom :=
  jcellPG cp X.sC d c

/-- TV-F1(c) countS = 1 leg (the V7_rbA `ratBurdens_tg_j` precedent, restated
at the F1 wiring; rfl at `jcellPG`'s literal countS := 1 field). -/
theorem jCellPGof_countS_one {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {TE : TmplEvents n S} (X : XHD n S TE V)
    (cp : CellPolyPack n C S V) (d : MoveData n C)
    (c : V.DCellO d.s d.m d.o d.α) :
    (jCellPGof X cp d c).countS = 1 :=
  rfl

/-- TV-F1(b) [j pack, split route]: the per-outcome J pack — jcell_sum FORCES
its val to be the cell sum, so it is DEFINED as (a pack presenting) that sum;
the val-spec is `jPGof_val`.  Sketch: common-denominator assembly over the
outcome's `J.bcells` roster via `gcell_denom_sum`'s closure pattern (the
summed-denominator lemma already proved in Defs). -/
noncomputable def jPGof {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S} (X : XHD n S TE V)
    (cp : CellPolyPack n C S V) (J : JCells n C S V) (d : MoveData n C) :
    MovesS.PolyGeom :=
  sorry

/-- TV-F1(b) val-spec: `jPGof`'s value IS the cell sum of the jPCell values
over the split-route roster (the jcell_sum candidate, displayed at F1 and
type-checked here per the TV-F2 gate deliverable; blueprint §3.E "jcell_sum
forces jP := the cell sum — co-design jP as that sum").
CO-DESIGN PIN — adjustable only at the TV-F2 seam, with a record. -/
theorem jPGof_val {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S} (X : XHD n S TE V)
    (cp : CellPolyPack n C S V) (J : JCells n C S V) (d : MoveData n C) :
    (jPGof V X cp J d).val
      = ∑ c ∈ J.bcells d.s d.m d.o d.α, (jCellPGof X cp d c).val := by
  sorry

/-- TV-F1(d) [ιP]: PRESCRIBED BODY — "ιP := choice over ratBurdens_iota's ∃"
(blueprint §4 TV-F1; the ∃ is PROVED at V7_rbB from `initRat_comp`). -/
noncomputable def iotaPGof {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S} (X : XHD n S TE V)
    (hEU : EntU V) (hEC : EntCount V) (hA : AffEnt n)
    (hdom : EntDomOrder0 V) (β₀ : S.Cell) (i : V.EntIx β₀) :
    MovesS.PolyGeom :=
  (ratBurdens_iota V X hEU hEC hA hdom β₀ i).choose

/-- TV-F1(d) spec, countS leg (choose_spec projection of the proved ∃). -/
theorem iotaPGof_countS_one {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S} (X : XHD n S TE V)
    (hEU : EntU V) (hEC : EntCount V) (hA : AffEnt n)
    (hdom : EntDomOrder0 V) (β₀ : S.Cell) (i : V.EntIx β₀) :
    (iotaPGof V X hEU hEC hA hdom β₀ i).countS = 1 :=
  (ratBurdens_iota V X hEU hEC hA hdom β₀ i).choose_spec.1

/-- TV-F1(d) spec, geom leg: the weight-only entrance geometry `Gent`. -/
theorem iotaPGof_geom {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S} (X : XHD n S TE V)
    (hEU : EntU V) (hEC : EntCount V) (hA : AffEnt n)
    (hdom : EntDomOrder0 V) (β₀ : S.Cell) (i : V.EntIx β₀) :
    (iotaPGof V X hEU hEC hA hdom β₀ i).geom = X.sEnt.Gent β₀ i :=
  (ratBurdens_iota V X hEU hEC hA hdom β₀ i).choose_spec.2

end LeanUrat.MovesV
