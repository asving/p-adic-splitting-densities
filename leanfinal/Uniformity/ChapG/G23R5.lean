/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G23R4

/-!
# Uniformity.ChapG.G23R5 — `card_resTop`: the TOP-level admissible set is a copy of `P`

**Chapter G, NODE G.23R5** (`blueprint/CHAP-G_base_cases_menus.md` AMENDMENT §A-8, the
REPLACEMENT ROUTE for the refuted G.23a). At the levels `(2k+1, k+1)` the two digits are
*exactly* determined by the class (G.23R2's realization half) and *determine* the class
(G.23R2's uniqueness half), so `p ↦ (⟦π^(2k)·p̃₀⟧, ⟦π^k·p̃₁⟧)` is a bijection `P ≃ resTop π P k`
for any lift `p̃` of the digits.

DEPENDS: G.23R2, G.23R4 · landed `IsLocalRing.residue_surjective` (via
`Ideal.Quotient.mk_surjective`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] {π : O}

theorem card_resTop (hπ : Irreducible π)
    (P : Set (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O)) (k : ℕ) :
    Nat.card (resTop π P k) = Nat.card P := by
  classical
  have hsurj : Function.Surjective (IsLocalRing.residue O) := Ideal.Quotient.mk_surjective
  set sec : IsLocalRing.ResidueField O → O := Function.surjInv hsurj with hsecdef
  have hsec : ∀ β, IsLocalRing.residue O (sec β) = β := fun β => Function.surjInv_eq hsurj β
  refine (Nat.card_eq_of_bijective
    (fun p : P =>
      (⟨(Ideal.Quotient.mk _ (π ^ (2 * k) * sec p.val.1),
          Ideal.Quotient.mk _ (π ^ k * sec p.val.2)),
        ⟨sec p.val.1, sec p.val.2, rfl, by rw [hsec, hsec]; exact p.property⟩⟩ :
        resTop π P k)) ⟨?_, ?_⟩).symm
  · rintro ⟨p, hp⟩ ⟨q, hq⟩ hpq
    have h := congrArg Subtype.val hpq
    have e1 := residue_eq_of_mk_pow_mul_eq hπ (by omega : 2 * k < 2 * k + 1) (congrArg Prod.fst h)
    have e2 := residue_eq_of_mk_pow_mul_eq hπ (by omega : k < k + 1) (congrArg Prod.snd h)
    rw [hsec, hsec] at e1
    rw [hsec, hsec] at e2
    exact Subtype.ext (Prod.ext_iff.2 ⟨e1, e2⟩)
  · rintro ⟨x, y₀, y₁, rfl, hP⟩
    refine ⟨⟨(IsLocalRing.residue O y₀, IsLocalRing.residue O y₁), hP⟩, ?_⟩
    refine Subtype.ext (Prod.ext_iff.2 ⟨?_, ?_⟩)
    · exact mk_pow_mul_eq_of_residue_eq hπ (le_refl _) (by rw [hsec])
    · exact mk_pow_mul_eq_of_residue_eq hπ (le_refl _) (by rw [hsec])

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.card_resTop

end AxCheck
