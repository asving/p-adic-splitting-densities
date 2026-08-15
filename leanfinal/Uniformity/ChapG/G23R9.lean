/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.CensusGen
import Uniformity.ChapG.G23R6
import Uniformity.ChapG.G23R8

/-!
# Uniformity.ChapG.G23R9 — **THE COUNT FORMULA** `card_resClassSet`

**Chapter G, NODE G.23R9** (`blueprint/CHAP-G_base_cases_menus.md` AMENDMENT §A-8, the
REPLACEMENT ROUTE for the refuted G.23a). The headline of the route: at level
`N = 2k+1+r`, the classes carrying a residual pair in a *translation-invariant* class `P` at a
centre of depth `≥ 2k` number

  `#P · q^(2k+2r)`  ( `= #P · q^(2N−2k−2)` ).

Route (A-1 verbatim): `card_certSet_gen` at centre modulus `m = k` on the family `resCert`
(G.23R8), whose admissible set has `#(resAdm) = #P · q^(k+2r)` (G.23R6); the centre contributes
`q^k`, and `q^k · #P · q^(k+2r) = #P · q^(2k+2r)`.

**This node replaces G.23a on the critical path.** G.23a asserted a per-PAIR count and is
refuted (A-1); this node counts a translation-invariant CLASS and is what G.41 and G.42 consume
— at `P = {p | AniForm p}` (G.38, `#P = q(q−1)/2`) it gives `#inertStratum = ((q−1)/2)·q^(2N−2k−1)`
in one step, in both residue characteristics, and at `P = {p | SepPair p}` (G.39) it gives
G.42.

DEPENDS: G.23R6, G.23R8 · landed `UniformityCheck.card_certSet_gen` (`CensusGen.lean:64`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] {π : O}

/-- **THE COUNT FORMULA of the replacement route.** At level `N = 2k+1+r`, the classes carrying
a residual pair in the translation-invariant class `P` at a centre of depth `≥ 2k` number
`#P · q^(2k+2r) = #P · q^(2N−2k−2)`. -/
theorem card_resClassSet (hπ : Irreducible π)
    {P : Set (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O)}
    (hP : TransInvariant P) (k r : ℕ) :
    Nat.card (resClassSet π P k (2 * k + 1 + r))
      = Nat.card P * residueCard O ^ (2 * k + 2 * r) := by
  obtain ⟨cert, hcert, hshift, huniq, hset⟩ := resCert hπ hP k r
  have hgen := UniformityCheck.card_certSet_gen
    (O := O) (n := 2) (N := 2 * k + 1 + r) (m := k) (by omega : k ≤ 2 * k + 1 + r)
    (fun g => readEquiv g) (resAdm π P k (2 * k + 1 + r)) cert hcert hshift huniq
  have hsetEq : {c : Coeff O 2 (2 * k + 1 + r) | ∃ γ, cert γ c}
      = resClassSet π P k (2 * k + 1 + r) := by ext c; exact hset c
  rw [hsetEq, card_resAdm hπ P k r] at hgen
  have hcollect : residueCard O ^ k * (Nat.card P * residueCard O ^ (k + 2 * r))
      = Nat.card P * residueCard O ^ (2 * k + 2 * r) := by
    rw [show 2 * k + 2 * r = k + (k + 2 * r) by omega, pow_add]
    ring
  rw [hgen, hcollect]

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.card_resClassSet

end AxCheck
