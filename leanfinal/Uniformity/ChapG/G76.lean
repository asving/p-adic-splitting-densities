/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G52
import Uniformity.ChapG.G73
import Uniformity.ChapG.G74
import Uniformity.ChapG.G75

/-!
# Uniformity.ChapG.G76 — `card_le_undecidedCount_three`

**Chapter G, NODE G.76** (`blueprint/CHAP-G_base_cases_menus.md` §10). **`q^N ≤
undecidedCount O 3 N`** — the `n = 3` σ-undecided lower bound, at general `O`, unconditional.
This is the (weaker, always-available) lower HALF of HEX3-BOX-1's bracket `q^N ≤ U₃^σ ≤ U₃^conv`
(H-1/H-2 of the chapter's honesty block: chapter G proves no more of the bracket than this).

DEPENDS: G.52, G.73, G.74, G.75 · landed `undecidedCount`, `UndecidedAt`, `DecidedAt`.

**PROOF.** Every class of `species3 N` is undecided: G.74 supplies a `c3split` lift and G.75
supplies a `c3ram`-or-`c3linRam` lift of the *same* class, and `c3split` is pairwise distinct
from both (G.52's `c3_pairwise_ne`), so no single type can be decided on it. Hence
`species3 N ⊆ undecidedSet O 3 N`, and `card_species3` (G.73) reads off the count.

**⚠ WHAT THIS BOUND DOES AND DOES NOT DO.** It is compatible with drainage (normalized,
`q^N / q^(3N) = q^(-2N) → 0`); it obstructs nothing, and its only role is to make
`undecidedCount O 3 N` provably nonzero.

**TEETH.** `HEX3-SPECIES` → executable regression; `HEX3-LAW` → executable regression.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- The `n = 3` σ-undecided count is at least `q^N`: the `q^N` classes with both separation
coordinates hidden admit both a split lift and a ramified lift. -/
theorem card_le_undecidedCount_three (N : ℕ) :
    residueCard O ^ N ≤ undecidedCount O 3 N := by
  have hsub : Menu.species3 (O := O) N ⊆ undecidedSet O 3 N := by
    intro c hc σ hdec
    obtain ⟨πw, hπw⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨a_s, ha_s, ht_s⟩ := exists_split3_lift hc
    obtain ⟨a_r, ha_r, ht_r⟩ := exists_ram3_lift hπw hc
    have e1 : typeOf (monicPoly a_s) = σ := hdec a_s ha_s
    have e2 : typeOf (monicPoly a_r) = σ := hdec a_r ha_r
    rw [ht_s] at e1
    rcases ht_r with ht_r | ht_r
    · rw [ht_r] at e2
      exact c3_pairwise_ne.2.2.2.1 (e1.trans e2.symm)
    · rw [ht_r] at e2
      exact c3_pairwise_ne.2.2.1 (e1.trans e2.symm)
  have hcard : Nat.card (Menu.species3 (O := O) N) ≤ Nat.card (undecidedSet O 3 N) :=
    Nat.card_le_card_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)
  rwa [Menu.card_species3] at hcard

end Uniformity.Density

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.card_le_undecidedCount_three

end AxCheck
