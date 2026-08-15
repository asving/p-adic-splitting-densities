/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G13
import Uniformity.ChapG.G17
import Uniformity.ChapG.G19

/-!
# Uniformity.ChapG.G20 — `card_depthSet`, the depth stratum count

**Chapter G, NODE G.20** (`blueprint/CHAP-G_base_cases_menus.md` §4). At level `N = t + 1 + r`
(so `t < N`), the depth-exactly-`t` stratum satisfies `#(depthSet) + q^(t+2r+1) = q^(t+2r+2)` —
the subtraction-free form of `#(depthSet π N t) = (q−1)·q^(2N−t−1)`.

DEPENDS: G.13, G.17, G.19.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] {π : O}

theorem card_depthSet (hπ : Irreducible π) (t r : ℕ) :
    Nat.card (depthSet π (t + 1 + r) t) + residueCard O ^ (t + 2 * r + 1)
      = residueCard O ^ (t + 2 * r + 2) := by
  have hsub : tangSet π (t + 1 + r) (t + 1) ⊆ tangSet π (t + 1 + r) t :=
    tangSet_antitone hπ (by omega)
  have hkey := Set.ncard_sdiff_add_ncard_of_subset hsub
  rw [← Nat.card_coe_set_eq (tangSet π (t + 1 + r) t \ tangSet π (t + 1 + r) (t + 1)),
    ← Nat.card_coe_set_eq (tangSet π (t + 1 + r) (t + 1)),
    ← Nat.card_coe_set_eq (tangSet π (t + 1 + r) t)] at hkey
  have e1 : Nat.card (tangSet π (t + 1 + r) t) = residueCard O ^ (t + 2 * r + 2) := by
    have h := card_tangSet (O := O) (π := π) hπ t (1 + r)
    rwa [show t + (1 + r) = t + 1 + r by omega,
      show t + 2 * (1 + r) = t + 2 * r + 2 by ring] at h
  have e2 : Nat.card (tangSet π (t + 1 + r) (t + 1)) = residueCard O ^ (t + 2 * r + 1) := by
    have h := card_tangSet (O := O) (π := π) hπ (t + 1) r
    rwa [show t + 1 + 2 * r = t + 2 * r + 1 by ring] at h
  rw [e1, e2] at hkey
  exact hkey

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.card_depthSet

end AxCheck
