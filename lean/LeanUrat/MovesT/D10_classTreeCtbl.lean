/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesT.D9_shapeCtbl
import LeanUrat.MovesD.D2a_finite

/-! # T-D10 `classTree_countable` — MovesS §W4-SYNC S-7: `ClassTree` (Defs §2.9 — the
REV-5 key-unique `Finset` carrier, §0 record #12 dead BY CARRIER) is countable:
countable-of-finite fibers over countable Shape data. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

instance (n : ℕ) (pol : CanonPolicy p F) : Countable (ClassTree n pol) := by
  -- countable-of-finite fibers over countable Shape data: inject `ClassTree` into the
  -- tuple of its four DATA components (the Prop fields are proof-irrelevant), each a
  -- Finset/Multiset over a countable carrier (`Shape n` countable via T-D9,
  -- `PrefIdx n pol P` finite via MovesD.D2a, `Vd` a subtype of `Multiset (ℕ × ℕ)`).
  apply Function.Injective.countable
    (f := fun ct : ClassTree n pol => (ct.addrs, ct.leafV, ct.nsMark, ct.rootV))
  rintro ⟨a1, h1a, l1, h1b, m1, h1c, r1, h1d⟩ ⟨a2, h2a, l2, h2b, m2, h2c, r2, h2d⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  rfl

end LeanUrat.MovesT
