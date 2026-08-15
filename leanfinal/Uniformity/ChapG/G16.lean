/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G14
import Uniformity.ChapG.G15

/-!
# Uniformity.ChapG.G16 — `card_tangAdm`, the subtraction-free admissible-set count

**Chapter G, NODE G.16** (`blueprint/CHAP-G_base_cases_menus.md` §4). At level `N = t + r`,
`#tangAdm · q^⌈t/2⌉ = q^(t + 2r)` — the subtraction-free form of
`#tangAdm = q^(N−t) · q^(N−⌈t/2⌉)`.

DEPENDS: G.14, G.15.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] {π : O}

theorem card_tangAdm (hπ : Irreducible π) (t r : ℕ) :
    Nat.card (tangAdm π t (t + r)) * residueCard O ^ ((t + 1) / 2)
      = residueCard O ^ (t + 2 * r) := by
  have hle : (t + 1) / 2 ≤ t + r := by omega
  set r' : ℕ := t + r - (t + 1) / 2 with hr'def
  have hr'eq : (t + 1) / 2 + r' = t + r := by omega
  have hcard1 : Nat.card (dvdSet π t (t + r)) = residueCard O ^ r := card_dvdSet hπ
  have hcard2 : Nat.card (dvdSet π ((t + 1) / 2) (t + r)) = residueCard O ^ r' := by
    have hthis := card_dvdSet (O := O) (π := π) hπ (k := (t + 1) / 2) (r := r')
    rwa [hr'eq] at hthis
  have hprod : Nat.card (tangAdm π t (t + r))
      = Nat.card (dvdSet π t (t + r)) * Nat.card (dvdSet π ((t + 1) / 2) (t + r)) := by
    show Nat.card (dvdSet π t (t + r) ×ˢ dvdSet π ((t + 1) / 2) (t + r) : Set _) = _
    rw [Nat.card_coe_set_eq, Set.ncard_prod, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  rw [hprod, hcard1, hcard2, ← pow_add, ← pow_add]
  congr 1
  omega

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.card_tangAdm

end AxCheck
