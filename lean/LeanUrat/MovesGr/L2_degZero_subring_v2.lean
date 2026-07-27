/-
MovesGr unit L2_degZero_subring (v2 — restructured second attempt, 2026-07-26).
Statement byte-identical to lean/LeanUrat/MovesGr/MANIFEST.json.

RESTRUCTURE vs. the first attempt (L2_degZero_subring.lean, 3 sorries): the whole
additive gap is reduced to the SINGLE equation `hadd` below — ring addition agrees with
DirectSum addition on degree-0 `of`-elements. From that one equation the ring zero
(`of 0 0 + of 0 0 = of 0 0` + cancellation) and ring negation
(`of 0 a + of 0 (-a) = 0` + uniqueness of inverses) are DERIVED, so `zero_mem'` and
`neg_mem'` are no longer independent gaps. `mul_mem'`, `one_mem'`, and the membership
iff are fully proved.

HISTORY: `hadd` could not be closed against the original 4-field `GradedRingStr` (the
fields contained NO occurrence of `Rg.ring`'s `+`; machine-confirmed by attempt 1). The
fix was the §8.1 blueprint proposal, OPTION (a) SIGNED OFF by Asvin 2026-07-28: the
`add_def` field of `GradedRingStr` ties `Rg.ring`'s addition to the DirectSum's.

STATUS NOW: FULLY PROVED. `hadd` is exactly `Rg.add_def` composed with additivity of
`DirectSum.of` (the one-line term below); everything else was already machine-checked.
-/
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
  -- Decomposition (pure DirectSum, no ring): degree-0-supported ⇒ an `of`-element.
  have hdecomp : ∀ (x : S.Gr), (∀ γ ≠ (0:ℤ), x γ = 0) →
      x = DirectSum.of (fun γ => S.grPiece γ) 0 (x 0) := by
    intro x hx
    refine DFinsupp.ext (fun j => ?_)
    rcases eq_or_ne j 0 with hj | hj
    · subst hj; simp
    · rw [hx j hj]; symm; exact DirectSum.of_eq_of_ne _ _ _ hj
  -- The former single gap, closed by `Rg.add_def` (option (a), signed off 2026-07-28):
  -- ring `+` = DirectSum `+` on degree-0 `of`-elements.
  have hadd : ∀ a b : S.grPiece 0,
      DirectSum.of (fun γ => S.grPiece γ) 0 a + DirectSum.of (fun γ => S.grPiece γ) 0 b
        = DirectSum.of (fun γ => S.grPiece γ) 0 (a + b) := by
    intro a b
    refine DFinsupp.ext fun j => ?_
    rw [Rg.add_def]
    rcases eq_or_ne j 0 with hj | hj
    · subst hj; simp
    · rw [DirectSum.of_eq_of_ne _ _ _ hj, DirectSum.of_eq_of_ne _ _ _ hj,
        DirectSum.of_eq_of_ne _ _ _ hj, add_zero]
  -- Derived: the ring zero is `of 0 0` (idempotent + cancellation).
  have hzero : DirectSum.of (fun γ => S.grPiece γ) 0 (0 : S.grPiece 0) = (0 : S.Gr) := by
    have h1 := hadd 0 0
    rw [add_zero] at h1
    exact add_right_cancel (h1.trans (zero_add _).symm)
  -- Derived: ring negation of a degree-0 `of`-element (uniqueness of additive inverses).
  have hneg : ∀ a : S.grPiece 0,
      -(DirectSum.of (fun γ => S.grPiece γ) 0 a) = DirectSum.of (fun γ => S.grPiece γ) 0 (-a) := by
    intro a
    have h1 := hadd a (-a)
    rw [add_neg_cancel, hzero] at h1
    exact neg_eq_of_add_eq_zero_right h1
  refine ⟨{ carrier := {x | ∀ γ ≠ (0:ℤ), x γ = 0}
            mul_mem' := ?_
            one_mem' := ?_
            add_mem' := ?_
            zero_mem' := ?_
            neg_mem' := ?_ }, fun x => Iff.rfl⟩
  -- mul: degree-0 · degree-0 ⊆ degree-0, via the genuine graded product (`mul_of` + `pmul`).
  · intro a b ha hb γ hγ
    rw [hdecomp a ha, hdecomp b hb, Rg.mul_of 0 0 (a 0) (b 0),
      DirectSum.of_eq_of_ne _ _ _ (by simpa using hγ)]
  -- one: `1 = [1]` sits in degree `deg 1 = 0` (`one_def` + `w_one`).
  · intro γ hγ
    rw [Rg.one_def]
    show (DirectSum.of (fun γ => S.grPiece γ) (S.deg 1) (S.mkPiece 1)) γ = 0
    exact DirectSum.of_eq_of_ne _ _ _ (by
      have h : S.deg 1 = 0 := by simp [SideVal.deg, S.w_one]
      rw [h]; exact hγ)
  -- add: via the single gap equation `hadd`.
  · intro a b ha hb γ hγ
    rw [hdecomp a ha, hdecomp b hb, hadd (a 0) (b 0),
      DirectSum.of_eq_of_ne _ _ _ hγ]
  -- zero: via the derived `hzero`.
  · intro γ hγ
    rw [← hzero, DirectSum.of_eq_of_ne _ _ _ hγ]
  -- neg: via the derived `hneg`.
  · intro a ha γ hγ
    rw [hdecomp a ha, hneg (a 0), DirectSum.of_eq_of_ne _ _ _ hγ]

end LeanUrat.MovesGr

#print axioms LeanUrat.MovesGr.L2_degZero_subring
