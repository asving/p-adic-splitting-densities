/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-V6 `tau_total` — COVERING, the case analysis (no orphan) (MOVES 7112–7119):
(i) every realized child receives EXACTLY ONE disposition (from `hdi.dichotomy`,
exclusivity by μ-arithmetic); (ii) a childless realized state IS the (ns) status AND
carries B(iii)'s all-heights vanishing datum (from `hdi.ns_lumps` + `tie`). PROVED
(E-phase: both halves discharged from the KB-TOT bundle). -/

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem tau_total (T : TreeModel p F n N m pol) (hdi : KBTot T)
    (H : History p F) (x : Box p m) (hmem : T.mem (some H) x) :
    (∀ (ν : Node p F) (hν : NodeExtends H ν), T.child (some H) ν x →
      ((ν.μ = 1 ∧ IrrHalts (H.snoc ν hν)) ∨
        (2 ≤ ν.μ ∧ T.mem (some (H.snoc ν hν)) x)) ∧
      ¬ (ν.μ = 1 ∧ 2 ≤ ν.μ)) ∧
    ((∀ ν : Node p F, ¬ T.child (some H) ν x) →
      NsHalts T (some H) x ∧
      ∃ (J : JetSetup H n N m) (Lf : NsLumpFamily T J), ∀ M, x ∈ Lf.L M) := by
  constructor
  · intro ν hν hchild
    refine ⟨hdi.dichotomy H x hmem ν hν hchild, ?_⟩
    rintro ⟨h1, h2⟩
    omega
  · intro hnochild
    refine ⟨⟨hmem, hnochild⟩, ?_⟩
    obtain ⟨J, _, _, ⟨Lf⟩⟩ := hdi.ns_lumps H ⟨x, hmem⟩
    exact ⟨J, Lf, (Lf.tie x hmem).mp hnochild⟩

end LeanUrat.MovesT
