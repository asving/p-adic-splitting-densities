import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.DefsL
import LeanUrat.MovesGr.Defs

open Polynomial LeanUrat.Moves LeanUrat.MovesGr LeanUrat.MovesGr.SideVal

variable {p : ℕ} [Fact p.Prime]

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 800000

namespace LeanUrat.MovesGr

theorem L2_degZero_subring (S : SideVal p) (Rg : GradedRingStr S) : letI := Rg.ring; ∃ (R0 : Subring S.Gr), ∀ x : S.Gr, x ∈ R0 ↔ (∀ γ ≠ (0:ℤ), (x γ : S.grPiece γ) = 0) := by
  letI := Rg.ring
  have hdecomp : ∀ (x : S.Gr), (∀ γ ≠ (0:ℤ), x γ = 0) →
      x = DirectSum.of (fun γ => S.grPiece γ) 0 (x 0) := by
    intro x hx
    refine DFinsupp.ext (fun j => ?_)
    rcases eq_or_ne j 0 with hj | hj
    · subst hj; simp
    · rw [hx j hj]; symm; exact DirectSum.of_eq_of_ne _ _ _ hj
  refine ⟨{ carrier := {x | ∀ γ ≠ (0:ℤ), x γ = 0}
            mul_mem' := ?_
            one_mem' := ?_
            add_mem' := ?_
            zero_mem' := ?_
            neg_mem' := ?_ }, fun x => Iff.rfl⟩
  · intro a b ha hb γ hγ
    rw [hdecomp a ha, hdecomp b hb, Rg.mul_of 0 0 (a 0) (b 0),
      DirectSum.of_eq_of_ne _ _ _ (by simpa using hγ)]
  · intro γ hγ
    rw [Rg.one_def]
    show (DirectSum.of (fun γ => S.grPiece γ) (S.deg 1) (S.mkPiece 1)) γ = 0
    exact DirectSum.of_eq_of_ne _ _ _ (by
      have : S.deg 1 = 0 := by simp [SideVal.deg, S.w_one]
      rw [this]; exact hγ)
  -- GAP (flagged for human review, NOT an axiom): the three additive-closure fields below
  -- are NOT derivable from `GradedRingStr S`. That structure ties only `ring`'s MULTIPLICATION
  -- to the grading (`mul_of`) and the unit (`one_def`); it asserts NOTHING relating `ring`'s
  -- `AddCommGroup`/`Zero` to the canonical `DirectSum` additive structure used by `x γ`.
  -- Machine-confirmed (2026-07-26): `(a + b) γ` / `(0 : S.Gr) γ` / `(-a) γ` use `Rg.ring`'s
  -- `HAdd`/`Zero`/`Neg`, a DISTINCT instance from the DirectSum one, so `DirectSum.add_apply`
  -- /`zero_apply`/`neg_apply` do not apply and the components are opaque. Fixable only by
  -- strengthening `GradedRingStr` (e.g. a field `ring`'s additive structure = DirectSum's,
  -- discharged definitionally by the intended `ring := DirectSum.commRing` in
  -- `L1_gradedRingStr_exists`) — a statement change requiring sign-off. Multiplication and
  -- unit closure (above) and the membership iff ARE fully proved.
  · intro a b ha hb γ hγ
    sorry
  · intro γ hγ
    sorry
  · intro a ha γ hγ
    sorry

end LeanUrat.MovesGr
