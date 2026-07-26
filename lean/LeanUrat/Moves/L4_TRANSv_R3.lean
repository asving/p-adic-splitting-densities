/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.L4_TRANSviii_b_R3

/-!
# Moves/L4_TRANSv — the degree-0 coefficient field is F' = K⟨z̄⟩  [ROUND 3]

**Unit `L4.TRANSv`** (MANIFEST_R3).  MOVES §B2-DEF D.7(v), ~2213-2240: the degree-0
coefficient field surjects onto `F' = K⟮z̄⟯` (large-weight surjectivity).

Round-2 was FAITHLESS (internally impossible at `a = 0`: it forced `B ≠ 0` while demanding
`digPrime B = 0`, contradicting `digPrime_nonzero`).  The R3 statement drops the
unconditional `B ≠ 0` and guards it by `a ≠ 0 → B ≠ 0`, so `a = 0` is realized by `B = 0`.

**Structure of this proof.**  `L4.TRANSv` is the corollary of the manifest dependency
`L4.TRANSviii_b` (on disk, imported): fix any target weight above the child S6b threshold
`σ.w Φhat` — here `σ.w Φhat + 1` — and forget the realized-weight clause.  The large-weight
surjectivity body (g slot realizers via `hS6b` at parent weights clearing the DEF-8
threshold, distinct z-positions, `K⟮z̄⟯`-basis) lives in that unit, not here.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 400000

open Polynomial LeanUrat.Moves

namespace LeanUrat.Moves

/-- **L4.TRANSv** — the degree-0 coefficient field surjects onto `F' = K⟮z̄⟯`.  Corollary of
`L4_TRANSviii_b` at the weight `σ.w Φhat + 1` (which clears the DEF-8 threshold), forgetting
the realized-weight clause. -/
theorem L4_TRANSv {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g) (hmon : ψ.Monic) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (zbar : Fˣ) (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0) (a : F) (ha : a ∈ σ.nextField zbar) : ∃ B : Polynomial ℤ_[p], inC Φhat B ∧ σ.digPrime zbar B = a ∧ (a ≠ 0 → B ≠ 0) := by
  obtain ⟨B, hmem, hdig, hnz⟩ :=
    L4_TRANSviii_b σ ψ g hg hmon hψ hψz Φhat hlift zbar hzbar (σ.w Φhat + 1) (by omega) a ha
  exact ⟨B, hmem, hdig, fun ha0 => (hnz ha0).1⟩

end LeanUrat.Moves
