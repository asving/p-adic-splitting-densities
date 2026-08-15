/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G16
import Uniformity.ChapG.G18
import Uniformity.Density.CensusGen

/-!
# Uniformity.ChapG.G17 — `card_tangSet`, THE FILTRATION COUNT

**Chapter G, NODE G.17** (`blueprint/CHAP-G_base_cases_menus.md` §4). **The filtration count.**
At level `N = t + r`, `#(tangSet π (t+r) t) = q^(t + 2r)` — i.e. `q^(2N−t)` classes admit a
centre of tangency depth `≥ t`.

DEPENDS: G.03, G.04, G.09, G.10, G.11, G.13, G.15, G.16, G.18 · landed
`UniformityCheck.card_certSet_gen`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] {π : O}

/-- **The tangency-filtration count.** At level `N = t+r`, exactly `q^(t+2r) = q^(2N−t)` classes
admit a centre of tangency depth `≥ t`. This is the level-exact form of W-11's per-node drainage
census, and its `r = 0` case is W-11 clause (iii)'s exact drainage law. -/
theorem card_tangSet (hπ : Irreducible π) (t r : ℕ) :
    Nat.card (tangSet π (t + r) t) = residueCard O ^ (t + 2 * r) := by
  obtain ⟨cert, hcert, hshift, huniq, hset⟩ := tangCert hπ t r
  have hgen := UniformityCheck.card_certSet_gen
    (O := O) (n := 2) (N := t + r) (m := (t + 1) / 2) (by omega : (t + 1) / 2 ≤ t + r)
    (fun g => readEquiv g) (tangAdm π t (t + r)) cert hcert hshift huniq
  have hsetEq : {c : Coeff O 2 (t + r) | ∃ γ, cert γ c} = tangSet π (t + r) t := by
    ext c; exact hset c
  rw [hsetEq] at hgen
  rw [hgen, mul_comm]
  exact card_tangAdm hπ t r

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.card_tangSet

end AxCheck
