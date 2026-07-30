/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar

/-!
# HC1.CL17_packEtyp2 — TYP conjunct 2 at `packE`, unfolded (BP5 CL-17)

**Unit CL-17** (blueprint `lean/notes/BRIDGE_BP5_CLEANUP_2026-07-30.md` §3.2 + §4).

**Informal statement.** `TYPStmt'` conjunct 2 (R2, span pricing) at `packE T rl`:
`Nat.card` of the additive closure of the single-coordinate slot images at level
(b, γ') equals `p ^ aDim b γ'`.

**Proof sketch (blueprint §3.2 TYP conjunct 2).** The closure in R2's display,
instantiated at `packE`, is literally `T.alphabet b γ'` — the same union of
single-slot image ranges, via the extension-vs-subtype-`Pi.single` rewriting
lemma: `Pi.single (c : Coord) y` restricted to the level set equals the extension
of the subtype `Pi.single ⟨c, h⟩ y` (for `c ∉ lvl` both sides contribute
`{0} ⊆ closure`; R2's `⋃ c ∈ K.lvl` form only ranges over members, so only the
member case arises). Then `(T7_alphabetSpan T b γ').2.2.symm`
(`p ^ aDim = Nat.card 𝔸` — PROVED Lean-core at HEAD) with `packE.aDim = T.aDim`
(rfl). Degenerate cases are consistent: empty level set — both closures are `⊥`,
`Nat.card = 1 = p ^ 0` with `aDim = Nat.log p 1 = 0`; off-lattice γ' — the singles
are 0 and `T.alphabet` is the same object.

**Deps.** CL-09 (fold-back only); `T7_alphabetSpan` (PROVED Lean-core at HEAD).

**E-PHASE RESOLUTIONS RECORDED.** CL-09's `packE` has NOT landed at HEAD (sibling
cluster); this unit states the conjunct's DEFINITIONAL UNFOLDING in tower
vocabulary, transcribing R2's conjunct-2 display verbatim with the display-(8)
field values: `packE.lvl _ ↦ T.levelSet`, `packE.Digit ↦ ↥(T.stg 0).FQ`,
`packE.G.inγ γ' (packE.slotCoeff _ b z)` ↦
`T.inGr γ' (T.slotCoeff b (fun c' => if c' ∈ T.levelSet b γ' then z c' else 0))`,
`packE.aDim _ ↦ T.aDim`; the closure lives in `packE.G.Gr γ' = T.grQ γ'` (the
Gr-pin, rfl at `packE`). Fold-back to the literal `TYPStmt'` conjunct = CL-19 glue
(rfl-adjacent); `rl` does not occur in the unfolded conjunct and is omitted.
Transcription note: `Pi.single c y` carries an explicit type ascription
`(… : T.Coord → ↥(T.stg 0).FQ)` at its pointwise application — an elaboration aid
only (the Pi family is not inferable inside the restriction lambda), no semantic
content.

difficulty: routine-opus (fiddly). Size: ~60.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open scoped Classical

/-- **CL-17 (`packE_typ2`)** — `TYPStmt'` conjunct 2 at `packE`, unfolded (see the
module docstring): span pricing — the additive closure of the single-coordinate
slot-image ranges at (b, γ') has cardinality `p ^ aDim b γ'`. Up to the
extension-vs-subtype-`Pi.single` rewrite, the closure IS `T.alphabet b γ'` and the
equation is T7's exactness conjunct, symmetrized. -/
theorem packE_typ2 {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (b : ℕ) (γ' : ℚ) :
    Nat.card ↥(AddSubgroup.closure
        (⋃ c ∈ T.levelSet b γ', Set.range fun y : ↥(T.stg 0).FQ =>
          T.inGr γ' (T.slotCoeff b
            (fun c' => if c' ∈ T.levelSet b γ'
              then (Pi.single c y : T.Coord → ↥(T.stg 0).FQ) c' else 0))))
      = p ^ T.aDim b γ' := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.packE_typ2
