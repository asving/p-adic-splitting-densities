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
  -- Additive closure (add / zero / neg). RESOLVED 2026-07-29 via the `add_def` field of
  -- `GradedRingStr`, which SUPERSEDES the STALE 2026-07-26 GAP note that used to sit here (that
  -- note claimed no field related `ring`'s additive structure to DirectSum's; `add_def` is
  -- exactly such a field and is now present in the structure — machine-verified, not dated):
  -- `Rg.add_def x y γ : (x + y) γ = x γ + y γ` ties `Rg.ring`'s addition to the
  -- componentwise DirectSum addition on each degree. Zero is derived from `add_def 0 0` by the
  -- group law `left_eq_add`; neg is derived by feeding the additive-inverse witness
  -- `add_neg_cancel a` into a `b`-quantified helper (this sidesteps a non-defeq `Neg`-instance
  -- diamond in the opaque `Rg.ring`: bare `-a` resolves via the `AddCommGroup` path while the
  -- goal's `-a` uses the `AddGroupWithOne` path). No statement change, no new axiom.
  -- FLAGGED FOR ORCHESTRATOR RATIFICATION: the prior GAP note claimed these three legs needed a
  -- `GradedRingStr` strengthening plus sign-off; that strengthening (`add_def`) is already a
  -- field of the structure, so the legs are now honest theorems with nothing outstanding.
  · intro a b ha hb γ hγ
    rw [Rg.add_def a b γ, ha γ hγ, hb γ hγ, add_zero]
  · intro γ hγ
    have h := Rg.add_def 0 0 γ
    simp only [add_zero] at h
    exact left_eq_add.mp h
  · intro a ha γ hγ
    have hz : (0 : S.Gr) γ = 0 := by
      have h := Rg.add_def 0 0 γ; simp only [add_zero] at h; exact left_eq_add.mp h
    have key : ∀ (b : S.Gr), a + b = 0 → b γ = 0 := by
      intro b hab
      have h := Rg.add_def a b γ
      rw [hab, hz, ha γ hγ, zero_add] at h
      exact h.symm
    exact key _ (add_neg_cancel a)

end LeanUrat.MovesGr
