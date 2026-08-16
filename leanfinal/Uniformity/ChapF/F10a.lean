/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapF.F08
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Uniformity.ChapF.F10a — `finrank K (TwistedAlgebra cc) = E` (clause (iii)'s count)

**Chapter F, NODE F.10, split file a of 2** (split-mandated by the blueprint) [theorem]
(`blueprint/CHAP-F_weld_layer.md` §5), ENV-F1. "One K-line per dv-height, i.e.
`dim_K 𝒜(T) = E`" — `EFF.GRTJC.89` clause (iii)'s consumer column; the graded shadow
GENHN-2 cites as frame. Stated on the abstract object only; the corpus's `(DMULT-w)`-riding
enters where an instance is claimed (F.11).

Was an `axiom` stub at stage 0e; PROVED here (unit OM-9, 2026-08-16; the gate's F.29 leg 3
executed the value `finrank = 2` at both primes, F-D5(i) form).
-/

namespace Uniformity.Density.Weld

theorem TwistedAlgebra.finrank_eq {E : ℕ} [NeZero E] {K : Type*} [Field K]
    (cc : CarryCocycle E K) : Module.finrank K (TwistedAlgebra cc) = E := by
  show Module.finrank K (ZMod E → K) = E
  rw [Module.finrank_pi, ZMod.card]

end Uniformity.Density.Weld
