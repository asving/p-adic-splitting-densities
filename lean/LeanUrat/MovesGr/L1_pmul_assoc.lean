import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.DefsL
import LeanUrat.MovesGr.Defs

open Polynomial LeanUrat.Moves LeanUrat.MovesGr LeanUrat.MovesGr.SideVal

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesGr

/-- HEq of two quotient classes across an index equality, given equal underlying representatives. -/
private lemma mk_heq_of {p : ℕ} [Fact p.Prime] (S : SideVal p) {i j : ℤ} (h : i = j)
    (a : S.ge i) (b : S.ge j) (hab : (a : Polynomial ℤ_[p]) = (b : Polynomial ℤ_[p])) :
    HEq (Submodule.Quotient.mk a : S.grPiece i) (Submodule.Quotient.mk b : S.grPiece j) := by
  subst h
  exact heq_of_eq (congrArg _ (Subtype.ext hab))

/-- The underlying polynomial of `mulToGe` is the product of the underlying polynomials. -/
private lemma coe_mulToGe {p : ℕ} [Fact p.Prime] (S : SideVal p) {γ δ : ℤ}
    (a : S.ge γ) (b : S.ge δ) :
    ((S.mulToGe γ δ a b : S.ge (γ + δ)) : Polynomial ℤ_[p])
      = (a : Polynomial ℤ_[p]) * (b : Polynomial ℤ_[p]) := rfl

/-- Inlined `L0_pmul_mk` (dep not yet built to `.olean`): the piece product of two classes is the
class of the ambient product (definitional). -/
private lemma l0_pmul_mk {p : ℕ} [Fact p.Prime] (S : SideVal p) (γ δ : ℤ) (a : S.ge γ) (b : S.ge δ) :
    S.pmul γ δ (Submodule.Quotient.mk a) (Submodule.Quotient.mk b)
      = Submodule.Quotient.mk (S.mulToGe γ δ a b) := rfl

end LeanUrat.MovesGr

open LeanUrat.MovesGr in
theorem L1_pmul_assoc (S : SideVal p) (Rg : GradedRingStr S) (γ δ ε : ℤ) (x : S.grPiece γ) (y : S.grPiece δ) (z : S.grPiece ε) : HEq (S.pmul (γ + δ) ε (S.pmul γ δ x y) z) (S.pmul γ (δ + ε) x (S.pmul δ ε y z)) := by
  induction x using Submodule.Quotient.induction_on with | _ a =>
  induction y using Submodule.Quotient.induction_on with | _ b =>
  induction z using Submodule.Quotient.induction_on with | _ c =>
  simp only [l0_pmul_mk]
  apply mk_heq_of S (add_assoc γ δ ε)
  simp only [coe_mulToGe]
  ring
