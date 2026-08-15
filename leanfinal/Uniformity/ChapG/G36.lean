/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G17
import Uniformity.ChapG.G35

/-!
# Uniformity.ChapG.G36 — `undecidedCount_two_eq`, THE CHAPTER'S HEADLINE NODE

**Chapter G, NODE G.36** (`blueprint/CHAP-G_base_cases_menus.md` §6). **The exact `n = 2`
drainage law.** `undecidedCount O 2 N = q^N`, for every complete DVR with finite residue field,
every `N`, both characteristics. This sharpens the landed lossy bound `undecidedCount_le`
(which only gives `q^(3M)` at level `2M`) to the exact law.

DEPENDS: G.17, G.35 · landed `undecidedCount`, `IsDiscreteValuationRing.exists_irreducible`.

**PROOF.** Pick an irreducible `π` (every DVR has one). By G.35
(`Menu.undecidedSet_eq_tangSet`), `undecidedSet O 2 N = Menu.tangSet π N N`, so
`undecidedCount O 2 N = Nat.card (Menu.tangSet π N N)`. By G.17 (`Menu.card_tangSet`) with
`t := N, r := 0`, this is `residueCard O ^ (N + 2 * 0) = residueCard O ^ N`.

**TEETH.** `W11-EXHAUST` / P-4 (0/150 violations on 30 census rows, both characteristics) →
Lean theorem; `W11-T-DRAIN` (30 firings) → Lean theorem.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **G.36, the chapter's headline node.** The exact `n = 2` drainage law:
`undecidedCount O 2 N = q^N`. -/
theorem undecidedCount_two_eq [IsAdicComplete (maximalIdeal O) O] (N : ℕ) :
    undecidedCount O 2 N = residueCard O ^ N := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  rw [undecidedCount, Menu.undecidedSet_eq_tangSet hπ N]
  simpa using Menu.card_tangSet hπ N 0

section AxCheck
#print axioms Uniformity.Density.undecidedCount_two_eq
end AxCheck

end Uniformity.Density
