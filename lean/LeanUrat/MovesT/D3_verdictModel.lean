/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-D3 `verdictModel_inst` [hard, split D3a/D3b] — THE W4-2(c) RE-KEY:
`VerdictModelT` built from the τ emission; `vdict_cell` from the IN-CORPUS
`vdict_cell_of_child_cell` (PROVED — the rev-2 `hvc` owner-row is retired);
caps from T-C1/T-C2's family theorem; NO ns cap (§0 refutation record).
NON-DEGENERACY GATE: T-G1's `toy_vdict_nonconstant`. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

/-- τ's cell-data locality is an in-corpus LEMMA (REV 3, Codex-2 #17; REV 6: at
SOME-STATES — the scoped `child_cell`). PROVED. -/
theorem vdict_cell_of_child_cell (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (H : History p F) (x x' : Box p m)
    (hx : T.mem (some H) x) (hx' : T.mem (some H) x')
    (hc : CA.cellOf (.st H) x = CA.cellOf (.st H) x') :
    ∀ ν, T.child (some H) ν x ↔ T.child (some H) ν x' := by
  intro ν
  rw [CA.child_cell H ν x hx, CA.child_cell H ν x' hx', hc]

/-- root locality of the (τ-hen) payload: it reads only the χ-coordinates (T-C1). -/
theorem henPayload_cell (χ : Fin n → Fin m) {x x' : Box p m}
    (h : ∀ b : Fin n, x (χ b) = x' (χ b)) : henPayload χ x = henPayload χ x' := by
  have hr : redPoly χ x = redPoly χ x' := by
    unfold redPoly
    congr 1
    apply Finset.sum_congr rfl
    intro b _
    rw [h b]
  unfold henPayload henDegrees
  rw [hr]

open Classical in
/-- D3a: the verdict model at the τ emission (data fields closed; law fields are the
unit's E-phase obligations). `vdict none := none` — hen is level-0-only (7069); the
root's payload is `rootVdict`. -/
noncomputable def vModelOf (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (χ : Fin n → Fin m)
    (hdi : KBTot T) (capData : CapData T CA χ) :
    VerdictModelT T CA χ where
  vdict := fun o x =>
    match o with
    | none => none
    | some H =>
        if IrrHalts H then some (irrVerdictOf H)
        else if NsHalts T (some H) x then some (nsVerdictOf H) else none
  halt_iff := by
    intro H x hmem
    by_cases hirr : IrrHalts H
    · simp [hirr]
    · by_cases hns : NsHalts T (some H) x
      · simp [hirr, hns]
      · simp [hirr, hns]
  vdict_irr := by
    intro H x hmem hirr
    simp [hirr]
  vdict_ns := by
    intro H x hmem hnirr hns
    simp [hnirr, hns]
  vdict_cell := by
    intro o x x' hx hx' hc
    cases o with
    | none => rfl
    | some H =>
        have hchild := vdict_cell_of_child_cell T CA H x x' hx hx' hc
        have hns : NsHalts T (some H) x ↔ NsHalts T (some H) x' := by
          unfold NsHalts
          constructor
          · rintro ⟨_, h2⟩
            exact ⟨hx', fun ν => (hchild ν).not.mp (h2 ν)⟩
          · rintro ⟨_, h2⟩
            exact ⟨hx, fun ν => (hchild ν).not.mpr (h2 ν)⟩
        by_cases hirr : IrrHalts H
        · simp [hirr]
        · by_cases h : NsHalts T (some H) x
          · simp [hirr, h, hns.mp h]
          · have h' : ¬ NsHalts T (some H) x' := fun hc' => h (hns.mpr hc')
            simp [hirr, h, h']
  rootVdict := fun x => henPayload χ x
  rootVdict_law := fun _ => rfl
  rootVdict_cell := by
    intro x x' h
    exact henPayload_cell χ h
  capHen := 1
  capHen_law := by
    refine ⟨rfl, ?_⟩
    intro x x' h
    exact henPayload_cell χ h
  capIrr := capData.capIrrOf
  capIrr_law := capData.cap_law

end LeanUrat.MovesT
