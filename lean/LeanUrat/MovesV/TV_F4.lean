/-  TV-F4 (BRIDGE BP3, cluster c5; E-phase skeleton) — the cellP FAMILY +
    act_iff + cellP_count + cellP_nonzero via cp.count's PER-CELL polynomials
    (Q5 IS RULED: per-cell cp.count wiring, option (b); the coarse
    sizeP/stInst option (a) is RETIRED — recorded below).
    Blueprint: lean/notes/BRIDGE_BP3_TV_2026-07-30.md §3.E + §4 (TV-F4).
    deps: TV-F2 (the seam carrier).  Consumers: TV-F5.

    PIN INVENTORY (the blueprint's own disclosure duty, as-typed):
    - `seamCellP` := cp.P at the keyed (datum, digit cell) — the ADJUDICATED
      per-cell wiring (Q5 ruling option (b)); its value law against the CTS
      counts is `CellPolyPack.count` (V-side), and the measured tie demanded
      by `RatBurdens.cellP_count` is the `cell_count` field below.
    - REJECTED ALTERNATIVE (recorded, retired from the menu): option (a),
      the coarse per-state `sizeP`/`stInst` wiring — kept only as this
      record; no unit types it.
    - Typing-time observation for the prover (recorded, not resolved):
      cp's own degree law is `cp.deg : (cp.P s m o α c).natDegree ≤ C.Wloc
      s m` (a Wloc-genre bound), while `RatBurdens.cellP_deg` demands
      ≤ T.Wstate e τ = (C.bd τ.s).Wstate at the pinned table — the
      reconciliation (Wloc-vs-Wstate) is co-design content at the witness;
      if it FAILS at the real bounds, that is a statement-fence event on the
      wiring choice (return to the orchestrator, do not weaken RatBurdens). -/
import LeanUrat.MovesV.TV_F3

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.MovesV

/-- TV-F4 wiring (Q5 option (b), the adjudicated per-cell cp.count polys):
the cellP family at a measured cell := cp's per-cell count polynomial at the
keyed (datum, digit cell). -/
noncomputable def seamCellP {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} (cp : CellPolyPack n C S V)
    {T : MovesS.TableShape n} {M : MovesS.MeasuredSide T}
    (K : SeamKeys V T M) (e : ℕ) (τ : T.State e) (c : M.Cell e τ) :
    Polynomial ℚ :=
  cp.P (K.cellKey e τ c).1.s (K.cellKey e τ c).1.m (K.cellKey e τ c).1.o
    (K.cellKey e τ c).1.α (K.cellKey e τ c).2

/-- TV-F4 THE COFINITE-ACTIVITY FACE (mirrors `RatBurdens`' cellP law roster
field-for-field at `seamCellP`): degree bound, nonvanishing on the working
block range, the count law at active pools, and `act_iff` keyed to the
family.  Prop bundle, not parametric universals (they can fail at a bad
keying — honest-sorries discipline; the ∃ below asserts them at the
co-designed witness). -/
structure SeamCellLaws {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} (cp : CellPolyPack n C S V)
    {T : MovesS.TableShape n} {M : MovesS.MeasuredSide T}
    (K : SeamKeys V T M) : Prop where
  cell_deg : ∀ e (τ : T.State e) (c : M.Cell e τ),
    (seamCellP cp K e τ c).natDegree ≤ T.Wstate e τ
  cell_nonzero : ∀ e ∈ Finset.Icc 1 n, ∀ (τ : T.State e) (c : M.Cell e τ),
    seamCellP cp K e τ c ≠ 0
  cell_count : ∀ e (τ : T.State e) (c : M.Cell e τ) (q₀ : ℚ),
    q₀ ∈ M.Pools → M.activeState q₀ e τ →
    ((seamCellP cp K e τ c).eval q₀ : ℚ)
      = ((M.cellInst e τ c q₀ (M.cellLvl e τ c)).card : ℚ)
  cell_act_iff : ∀ q₀ ∈ M.Pools, ∀ e ∈ Finset.Icc 1 n, ∀ τ : T.State e,
    M.activeState q₀ e τ ↔ ∀ c : M.Cell e τ, (seamCellP cp K e τ c).eval q₀ ≠ 0

/-- TV-F4 UNIT CLAIM: the cluster witness additionally carries the cellP
laws (cumulative ∃ — the ONE shared witness thread, blueprint finding 7).
Sketch: cell_count from `cp.count` at the keyed datum through E1's cellInst
census (the co-design makes both count the same box event); cell_act_iff
from E2's `activeState := V.activeState ∘ toStepCells.symm` against V's
`act_size` (active ↔ sizeP eval ≠ 0) transported to the per-cell family;
cell_nonzero from the active-pool count law + pools_infinite (a nonzero
count at cofinitely many pools forces P ≠ 0). -/
theorem seam_cell_exists {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hTie : MDomTie V TE X.d) (J : JCells n C S V) (hEU : EntU V)
    (hEC : EntCount V) (hA : AffEnt n) (hdom : EntDomOrder0 V) :
    ∃ (T : MovesS.TableShape n) (M : MovesS.MeasuredSide T)
      (K : SeamKeys V T M),
      TablePins C T ∧
      (∀ q₀ ∈ V.Pools, ∀ N : ℕ, Nonempty (V.Box q₀ N) →
        Fintype.card (M.Box q₀ N) = @Fintype.card _ (V.finB q₀ N)) ∧
      SeamCoherent V X cp J hEU hEC hA hdom K ∧
      SeamDegreeLaws V X cp J hEU hEC hA hdom K ∧
      SeamCellLaws cp K := by
  sorry

end LeanUrat.MovesV
