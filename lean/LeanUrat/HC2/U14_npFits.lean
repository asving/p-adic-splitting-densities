/-
Unit U14.NP_fits  (HC-2 campaign, E-phase — blueprint §5 Layer C)
moves_ref: §C C.2 "N(H,Z) := 1 + the largest BASE level occurring among the coordinates of
T(H,Z)'s equations"; MovesD W4-4 (NP-ID) — THIS UNIT IS NP-ID's ⊆ direction.
deps: U3 (supports ⊆ band), MovesD `bandS`/`NPband` (shape-level band replica), the Defs
addendum `inFreshBandC` (the raw-coordinate band mirror).
difficulty: medium-hard (the htH ↔ bandS arithmetic).
hypothesis_fields: none beyond PrefSet membership.
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- NP-ID ⊆: for a shape-matched member, every fresh-band coordinate's level is bounded by
the SHAPE's band bound — `NPband` dominates the history's constrained levels (the band
levels are shape-pinned through `MatchesHist`'s line data). -/
theorem NP_fits {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {H : History p F} {pol : CanonPolicy p F} {P : Shape n}
    (hH : H ∈ PrefSet n pol P) :
    ∀ (i : ℕ) (hi : i < H.nodes.length) (c : Coord),
      inFreshBandC H n i (H.nodes[i]'hi) c →
      c.1 + 1 ≤ (P : ShapePrefix).NPband n := by
  sorry

/-- Box form (C.2's "N ≥ N(H,Z)" largeness at the shape bound): at `N ≥ NPband`, every
constructed fresh support coordinate has base level `< N` — the system fits the box. -/
theorem NP_fits_box {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n N : ℕ} {H : History p F} {pol : CanonPolicy p F} {P : Shape n}
    (hH : H ∈ PrefSet n pol P) {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (hNP : (P : ShapePrefix).NPband n ≤ N) :
    ∀ (i : ℕ) (hi : i < H.nodes.length), ∀ cl ∈ (mkFresh H n N S vOf i hi).clauses,
      ∀ c ∈ cl.support, (boxChart n N c).1 + 1 ≤ N := by
  sorry

end LeanUrat.MovesJ
