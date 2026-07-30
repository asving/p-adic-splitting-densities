import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.DefsL
import LeanUrat.MovesGr.Defs

open Polynomial LeanUrat.Moves LeanUrat.MovesGr LeanUrat.MovesGr.SideVal

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- Inlined `L0_initialForm_ne_zero`: the initial form of a nonzero element is nonzero. -/
private theorem if_ne_zero (S : SideVal p) {f : Polynomial ℤ_[p]} (hf : f ≠ 0) :
    S.initialForm f ≠ 0 := by
  intro h
  have h2 := congrArg (fun x : S.Gr => x (S.deg f)) h
  simp only [SideVal.initialForm, DirectSum.of_eq_same, DirectSum.zero_apply] at h2
  simp only [SideVal.mkPiece, Submodule.Quotient.mk_eq_zero] at h2
  have hlt : (S.deg f : WithTop ℤ) < S.w f := h2
  rw [S.deg_eq hf] at hlt
  exact lt_irrefl _ hlt

theorem L1_gr_domain_iff_val (S : SideVal p) (Rg : GradedRingStr S) : (letI := Rg.ring; IsDomain S.Gr) ↔ (∀ f g, f ≠ 0 → g ≠ 0 → S.w (f * g) = S.w f + S.w g) := by
  letI := Rg.ring
  constructor
  · intro _hdom f g hf hg
    have hfg : f * g ≠ 0 := mul_ne_zero hf hg
    have hif : S.initialForm (f * g) = S.initialForm f * S.initialForm g := Rg.if_mul f g hf hg
    have hmulof : S.initialForm f * S.initialForm g
        = DirectSum.of (fun γ => S.grPiece γ) (S.deg f + S.deg g)
            (S.pmul (S.deg f) (S.deg g) (S.mkPiece f) (S.mkPiece g)) := Rg.mul_of _ _ _ _
    have heq : DirectSum.of (fun γ => S.grPiece γ) (S.deg (f * g)) (S.mkPiece (f * g))
        = DirectSum.of (fun γ => S.grPiece γ) (S.deg f + S.deg g)
            (S.pmul (S.deg f) (S.deg g) (S.mkPiece f) (S.mkPiece g)) := hif.trans hmulof
    have hdeg : S.deg (f * g) = S.deg f + S.deg g := by
      by_contra hne
      have hcomp := congrArg (fun x : S.Gr => x (S.deg (f * g))) heq
      simp only [DirectSum.of_eq_same] at hcomp
      rw [DirectSum.of_eq_of_ne (S.deg f + S.deg g) (S.deg (f * g)) _ hne] at hcomp
      -- hcomp : S.mkPiece (f*g) = 0, an equation of quotient pieces (no S.Gr instance ambiguity)
      simp only [SideVal.mkPiece, Submodule.Quotient.mk_eq_zero] at hcomp
      have hlt : (S.deg (f * g) : WithTop ℤ) < S.w (f * g) := hcomp
      rw [S.deg_eq hfg] at hlt
      exact lt_irrefl _ hlt
    have hcast : (↑(S.deg (f * g)) : WithTop ℤ) = ↑(S.deg f) + ↑(S.deg g) := by
      rw [hdeg, WithTop.coe_add]
    rw [S.deg_eq hfg, S.deg_eq hf, S.deg_eq hg] at hcast
    exact hcast
  · intro hval
    haveI hnt : Nontrivial S.Gr := nontrivial_of_ne _ _ (if_ne_zero S one_ne_zero)
    haveI hnzd : NoZeroDivisors S.Gr :=
      { eq_zero_or_eq_zero_of_mul_eq_zero := by
          intro a b hab
          sorry }
    exact NoZeroDivisors.to_isDomain _
