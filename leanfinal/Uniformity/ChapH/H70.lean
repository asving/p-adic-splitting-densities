/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.Drainage

/-!
# Uniformity.ChapH.H70 — `undecidedSeq` is ANTITONE

**Chapter H, NODE H.70** (`blueprint/CHAP-H_general_induction.md` §10, source `EFF.GENIND.201`,
`ANNEX-LEMMA GENIND-C2D`). For every complete DVR `O` with finite residue field, every `n`, and
every `T ≤ W`, the conservative-undecided *fraction* cannot increase when the window grows:
`undecidedSeq O n W ≤ undecidedSeq O n T`.

Split-mandated into two declarations, per the node:

* `undecidedSet_preimage_subset` — the containment, which is the mathematical content;
* `undecidedSeq_antitone` — the ratio, which is bookkeeping.

DEPENDS: landed `undecidedSet`, `undecidedCount`, `undecidedSeq`, `UndecidedAt`, `DecidedAt`
(`Drainage.lean`, `GenuineDensity.lean`), `coeffFactor`, `coeffFactor_proj`,
`card_preimage_coeffFactor`, `card_coeff`, `residueCard`, `residueCard_pos` (`LocalData.lean`).

**The source's compressed citation is discharged here.** `EFF.GENIND.201`'s proof needs the read
to be monotone in the window ("the same certificate would decide every lift at window `W`") and
cites the conservative-drain convention for it. In `leanfinal`, `DecidedAt O n σ N c` is *by
definition* "every lift of `c` has type `σ`", so window monotonicity is a consequence of the
definition via `coeffFactor_proj`, not a convention: the lemma is unconditional at general `O`
with no drain convention assumed.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density

open IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)]

/-- **The containment.** Every window-`W` undecided class truncates to a window-`T` undecided
class. Contrapositively: if some `σ` were decided on the truncation at level `T`, then — since
truncating a lift of the level-`W` class gives a lift of the level-`T` class
(`coeffFactor_proj`) — the *same* `σ` would be decided on the class at level `W`. -/
theorem undecidedSet_preimage_subset {n T W : ℕ} (h : T ≤ W) :
    undecidedSet O n W ⊆ coeffFactor (O := O) (n := n) h ⁻¹' undecidedSet O n T := by
  intro c hc σ hσ
  refine hc σ ?_
  intro a ha
  refine hσ a ?_
  rw [← coeffFactor_proj (O := O) n h a, ha]

/-- **`GENIND-C2D`.** The conservative-undecided fraction is antitone in the window. -/
theorem undecidedSeq_antitone (n : ℕ) : Antitone (undecidedSeq O n) := by
  intro T W h
  -- the counting step: the window-`W` undecided set injects into the fibre-product of the
  -- window-`T` one, and the fibres of `coeffFactor` all have the same size.
  have hcard : undecidedCount O n W
      ≤ Nat.card (coeffFactor (O := O) (n := n) h ⁻¹' undecidedSet O n T) := by
    rw [undecidedCount, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard (undecidedSet_preimage_subset (O := O) (n := n) h) (Set.toFinite _)
  have hkey := card_preimage_coeffFactor (O := O) n h (undecidedSet O n T)
  rw [card_coeff, card_coeff] at hkey
  have hnat : undecidedCount O n W * residueCard O ^ (n * T)
      ≤ undecidedCount O n T * residueCard O ^ (n * W) := by
    calc undecidedCount O n W * residueCard O ^ (n * T)
        ≤ Nat.card (coeffFactor (O := O) (n := n) h ⁻¹' undecidedSet O n T)
            * residueCard O ^ (n * T) := Nat.mul_le_mul_right _ hcard
      _ = undecidedCount O n T * residueCard O ^ (n * W) := hkey
  have hq : (0 : ℝ) < (residueCard O : ℝ) := by exact_mod_cast residueCard_pos O
  rw [undecidedSeq, undecidedSeq, div_le_div_iff₀ (pow_pos hq _) (pow_pos hq _)]
  exact_mod_cast hnat

end Uniformity.Density

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.undecidedSet_preimage_subset
#print axioms Uniformity.Density.undecidedSeq_antitone

end AxCheck
