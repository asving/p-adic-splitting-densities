/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E02
import Mathlib.Data.List.Chain

/-!
# Uniformity.ChapE.E05 — `LadderData`: the σ-ladder and its two derived recursions

**Chapter E, NODE E.05** [def] (`blueprint/CHAP-E_sigma_ladder.md` §3, **as REPAIRED by
amendment A-E.1/E-D1 and A-E.1/E-D2**), ENV-E1 (the arithmetic arena: threshold and degree
bookkeeping, no local base `O`).

A **ladder** is a base rung (E.01) together with a list of higher rungs, chained by the threshold
recursion: the base has `T = 0` (`EFF.HE7.47`'s level-0 datum, `T_0 := 0`) and each successive
rung's threshold is the previous rung's `nextT` (`T_{i+1} = L_i·u_i`, E.02). Two numbers are
derived along the ladder:

* `degAt D₀ i` — the key degree at level `i`, `D_{i+1} = D_i·L_i` seeded by `D₀` (`EFF.HE7.47`);
* `boundAt i` — the (LIFT) threshold, `EFF.HE7.23`'s recursion `bound_{i+1} = (L_i−1)u_i +
  ℓ_i·bound_i` seeded at `bound_0 = 0` (so `boundAt 0 = base.nextBound 0`).

The level-1 instance reconciles with CHAP-H's `GenreDatum`: a `GenreDatum G` yields the base rung
`(G.e₁, G.f₁, G.h, 0)` — the slot/lift layer H.51–H.58 is stated on exactly those three numbers —
and with CHAP-B's polygon data on the `e₁ = 1` slice (B.11 `npHgt`, B.14 `suppVal`, the level-1
heights E's seam layer reads). Neither reconciliation is a declaration here: this node is the
ladder's arithmetic shape only, and the carrier data (`Φ_i`, the fields, the point sets) lives in
§4's `SlotCarrier`/`BlockData`/`RungInterface`.

## The two amendment repairs, and what they did not change

* **A-E.1/E-D1 (`List.get?` does not exist at the pin).** The blueprint's original bodies read
  `(Λ.rungs.get? i)`; at `v4.31.0` + our mathlib that constant is gone. The signed (repaired)
  spelling is the `getElem?` notation `Λ.rungs[i]?` — same `Option RungDatum` semantics, `getD`
  defaults unchanged.
* **A-E.1/E-D2 (`List.Chain` is deprecated, with a changed type).** `List.Chain R a l` still
  elaborates but is deprecated and its replacement `List.IsChain R l` takes no head argument, so
  the field is signed `hchain : List.IsChain rungFollows (base :: rungs)`. The two forms are
  definitionally equal (`List.Chain R a l` reduces to `List.IsChain R (a :: l)`; machine-checked
  at the amendment), so this is a spelling change with no content. `leanspec/Leanspec/ChapE.lean`
  still displays the deprecated form and records the divergence at its own defect list (E-D1,
  E-D2); **the landed form is the blueprint's**, i.e. this file.

The `getD 1` / `getD Λ.base` defaults are a contract for TOTALITY, not elegance: they are never
consulted at in-range indices, because every consumer carries an `i < rungs.length` hypothesis
(E.06's `hi`, and the fullness/threshold consumers downstream). An out-of-range read is not a
corpus configuration. A later refactor may re-derive the recursions as a `List.foldl` over
`rungs.take i` with a proved equivalence, provided `degAt`/`boundAt` keep these names and types.

Definitional, no proof obligation. DEPENDS: E.01, E.02 · mathlib `List.IsChain` (with its
constructors `List.IsChain.singleton`, `List.IsChain.cons_cons` — the gate frames of E.65/E.68
build through them), the `l[i]?` `getElem?` notation.

ARITHMETIC AUDIT (the corpus's own displayed instances, machine-evaluated at this node's landing
and reproduced here as the intended reading, NOT as Lean gates — the executable frame table is
E.68's). Take the base rung `(e₁,f₁,h,0) = (2,1,1,0)` and the single higher rung `(2,1,5,2)` (the
`q = 3` level-2 frame, whose `T = 2 = base.nextT` is exactly `rungFollows`). With seed `D₀ = 1`:
`degAt 1 0 = 1·2 = 2 = D′ = e₁f₁` and `degAt 1 1 = 2·2 = 4 = D″ = D′·ℓd_r`; `boundAt 0 =
(2−1)·1 + 2·0 = 1 = (D′−1)h` and `boundAt 1 = (2−1)·5 + 2·1 = 7 = (ℓd_r−1)u + ℓ(D′−1)h`, matching
`EFF.HE7.23`'s two displayed instances `bound₁ = (D′−1)h`, `bound₂ = (ℓd_r−1)u + ℓ(D′−1)h`, and
E.02's audit line `thr₂ = 7`. That ladder is a genuine `LadderData` — all four `RungDatum` side
conditions hold at both rungs, `hbase` is `rfl` and `hchain` is
`IsChain.cons_cons (rfl : r₂.T = base.nextT) (IsChain.singleton _)` — so the structure is
inhabited by a corpus frame and not merely by a degenerate one-rung ladder.

SOURCE: `EFF.HE7.47`/`.107` (the level recursion; the level-0 datum with `T_0 := 0`; "levels 1
and 2 are byte-unchanged"); `EFF.HE7.23` (`bound_0 = 0` and the two displayed instances);
`EFF.T2.35` (HE7-INSTANCE's `d = dv₂ = ℓ·dv = ℓe₁v`, `T = T₂ = ℓd_ru` — the value-normalization
multiplier `c_{i+1} = ℓ_i·c_i` is carried by the carrier, §4, not here).

TEETH: as E.02 (Q3 / HE7-LIFT2, five level-2 frames' thresholds against exhaustive enumeration);
E.68 executes the five-frame threshold table through `boundAt`.

ENVIRONMENT: ENV-E1.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- The threshold chain: rung `r'` follows `r` when `r'.T = r.nextT` (`EFF.HE7.47`'s
`T_{i+1} := L_i · u_i`). -/
def rungFollows (r r' : RungDatum) : Prop := r'.T = r.nextT

/-- A **ladder**: a base rung (threshold `0`) together with the list of higher rungs, chained by
the threshold recursion `rungFollows`. -/
structure LadderData where
  /-- The base rung (level 0 → 1): `(e₁, f₁, h, 0)` in corpus letters. -/
  base : RungDatum
  /-- The higher rungs, in ascending level order. -/
  rungs : List RungDatum
  hbase : base.T = 0
  -- [repaired: A-E.1/E-D2] was `List.Chain rungFollows base rungs`; `List.Chain` is deprecated at
  -- the pin and its replacement takes no head argument.  The two forms are definitionally equal.
  hchain : List.IsChain rungFollows (base :: rungs)

/-- The key degree at level `i` (`D₀` the seed; `D_{i+1} = D_i·L_i`, `EFF.HE7.47`). -/
def LadderData.degAt (Λ : LadderData) (D₀ : ℕ) : ℕ → ℕ
  | 0 => D₀ * Λ.base.slotCount
  -- [repaired: A-E.1/E-D1] was `(Λ.rungs.get? i)`: `List.get?` does not exist at the pin.
  | (i + 1) => Λ.degAt D₀ i * ((Λ.rungs[i]?).map RungDatum.slotCount |>.getD 1)

/-- The (LIFT) threshold at level `i` (`EFF.HE7.23`'s recursion, seeded at `bound_0 = 0`). -/
def LadderData.boundAt (Λ : LadderData) : ℕ → ℕ
  | 0 => Λ.base.nextBound 0
  -- [repaired: A-E.1/E-D1] was `(Λ.rungs.get? i)`.
  | (i + 1) => ((Λ.rungs[i]?).getD Λ.base).nextBound (Λ.boundAt i)

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.rungFollows
#print axioms Uniformity.Density.Ladder.LadderData
#print axioms Uniformity.Density.Ladder.LadderData.mk
#print axioms Uniformity.Density.Ladder.LadderData.degAt
#print axioms Uniformity.Density.Ladder.LadderData.boundAt

end AxCheck
