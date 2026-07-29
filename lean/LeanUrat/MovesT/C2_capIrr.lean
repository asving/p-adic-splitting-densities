/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-C2 `tbcap_irr` — the (τ-irr) per-class cross-level cap law (MOVES 7161–7187):
the cap is N(η′,⊤) = `capIrrOf` = `jetTopLevel` (Defs §2.11); cross-level constancy
via T-D7 (NP-ID); the family law quantified over ALL presented N AND box sizes
(REV 4, Codex-3 #5). `capIrrOf` is DECLARED in Defs.lean (§2.5 order note (8)). -/

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

/-- cross-level constancy: via T-D7 (NP-ID), each side's pinned-equation level set =
`bandLevels (P : ShapePrefix) n` — shape data. -/
theorem capIrr_uniform {P : Shape n} (i : PrefIdx n pol P)
    {N N' m m' : ℕ} (J : JetSetup (reprOf i) n N m) (J' : JetSetup (reprOf i) n N' m') :
    capIrrOf J = capIrrOf J' := by
  sorry

theorem tbcap_irr {P : Shape n} (S : Presented p F n N m pol P)
    (i : PrefIdx n pol P) (hirr : IrrHalts (reprOf i))
    (x x' : Box p m)
    (hagree : ∀ c : Fin m, levelIdx (n := n) c < capIrrOf (S.jet i) → x c = x' c) :
    (x ∈ S.fiber i ↔ x' ∈ S.fiber i) := by
  sorry

/-- the COMPATIBLE FAMILY across all presented N and box sizes (Codex-2 #5 / Codex-3
#5): one cap per class — from `tbcap_irr` + `capIrr_uniform`. This theorem discharges
`CapIrrLaw` (§2.9) at cap := capIrrOf J₀, i.e. T-D3's cap datum. -/
theorem tbcap_irr_family {P : Shape n} (i : PrefIdx n pol P)
    (hirr : IrrHalts (reprOf i))
    (J₀ : JetSetup (reprOf i) n N m) :
    ∀ (N' m' : ℕ) (S : Presented p F n N' m' pol P) (x x' : Box p m'),
      (∀ c : Fin m', levelIdx (n := n) c < capIrrOf J₀ → x c = x' c) →
      (x ∈ S.fiber i ↔ x' ∈ S.fiber i) := by
  sorry

/-- the NPband corollary — T-D7a's conclusion an EXPLICIT premise `hnp`. -/
theorem tbcap_irr_npband {P : Shape n} (S : Presented p F n N m pol P)
    (i : PrefIdx n pol P) (hirr : IrrHalts (reprOf i))
    (hnp : transportedLevels (S.jet i) (topLocus p m) ⊆ bandLevels (P : ShapePrefix) n)
    (x x' : Box p m)
    (hagree : ∀ c : Fin m, levelIdx (n := n) c < (P : ShapePrefix).NPband n → x c = x' c) :
    (x ∈ S.fiber i ↔ x' ∈ S.fiber i) := by
  sorry

end LeanUrat.MovesT
