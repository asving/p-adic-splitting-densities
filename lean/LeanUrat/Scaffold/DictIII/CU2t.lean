/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.DictIII.GMNReader

/-!
# Scaffold/DictIII/CU2t — the terminal seam (BP_III §1.9)

E-phase transcription of `lean/blueprints/BP_III.md` §1.9 (Step 11's CU-2t,
VERIFIED-at-scope leaf #9).  This file currently holds unit III-S1a: the
decidedness predicates `DecIrr` and `DecHen`, transcribed VERBATIM.  Source of
record: CUC §9.2.  `DecIrr` intentionally carries no unused polynomial `f`
(REV2 finding 21).

Display adjustment (III-S1a; the same sanctioned convention as the
Carriers.lean header): the §1.9 display writes the node lookup as
`H.nodes.get? k`, but `List.get?` was REMOVED from the Lean-4.31/Mathlib
environment pinned here; the surviving spelling of the SAME function is
`H.nodes[k]?` (`getElem?`, of which `List.get?` was the deprecated alias).
The proposition is unchanged; no other token differs from the display.
-/

namespace LeanUrat.Scaffold.DictIII

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- CU-2t decidedness, branch (i): some node at index ≥ 1 selects residual
    multiplicity μ = 1 (the terminal "irreducible read" verdict). -/
def DecIrr (H : EHist p F) : Prop :=
  ∃ k ν g, 1 ≤ k ∧ H.nodes[k]? = some ν ∧ ν.sel = some (g, 1)
  -- `.get?` → `[k]?`: header note

/-- CU-2t decidedness, branch (ii): a length-1 history decided at the root —
    either a₀ = 1 outright, or some semantic datum reads root order 1. -/
def DecHen (f : Polynomial ℤ_[p]) (H : EHist p F) : Prop :=
  H.nodes.length = 1 ∧
    (H.a0 = 1 ∨
      ∃ D : GMNData f (Theta H), D.rootOrder = 1)

end LeanUrat.Scaffold.DictIII
