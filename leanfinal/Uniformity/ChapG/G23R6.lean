/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G23R5

/-!
# Uniformity.ChapG.G23R6 — `card_resAdm`: `#S = #P · q^(N−2k−1) · q^(N−k−1)`

**Chapter G, NODE G.23R6** (`blueprint/CHAP-G_base_cases_menus.md` AMENDMENT §A-8, the
REPLACEMENT ROUTE for the refuted G.23a). A-1's admissible-set count, written at
`N = 2k+1+r` so that `N−2k−1 = r` and `N−k−1 = k+r`, i.e. subtraction-free as
`#(resAdm) = #P · q^(k+2r)`.

Route: `resAdm_eq_preimage` (G.23R4) + `card_preimage_prodResFactor` (G.23R1) +
`card_resTop` (G.23R5), then one cancellation of the positive factor `q^(3k+2)`.

DEPENDS: G.23R1, G.23R4, G.23R5 · landed `residueCard_pos`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] {π : O}

theorem card_resAdm (hπ : Irreducible π)
    (P : Set (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O)) (k r : ℕ) :
    Nat.card (resAdm π P k (2 * k + 1 + r)) = Nat.card P * residueCard O ^ (k + 2 * r) := by
  have h₀ : 2 * k + 1 ≤ 2 * k + 1 + r := by omega
  have h₁ : k + 1 ≤ 2 * k + 1 + r := by omega
  have hpre := card_preimage_prodResFactor (O := O) h₀ h₁ (resTop π P k)
  rw [← resAdm_eq_preimage hπ h₀ h₁, card_resTop hπ P k] at hpre
  have e1 : residueCard O ^ (2 * k + 1) * residueCard O ^ (k + 1)
      = residueCard O ^ (3 * k + 2) := by rw [← pow_add]; congr 1; omega
  have e2 : residueCard O ^ (2 * k + 1 + r) * residueCard O ^ (2 * k + 1 + r)
      = residueCard O ^ (k + 2 * r) * residueCard O ^ (3 * k + 2) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  rw [e1, e2] at hpre
  refine Nat.eq_of_mul_eq_mul_right (pow_pos (residueCard_pos O) (3 * k + 2)) ?_
  rw [hpre]; ring

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.card_resAdm

end AxCheck
