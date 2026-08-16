/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapF.F08
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Uniformity.ChapF.F13 — the count form of the twisted layer

**Chapter F, NODE F.13** [lemma] (`blueprint/CHAP-F_weld_layer.md` §5), ENV-F1 +
`[Finite K]`. `Nat.card (TwistedAlgebra cc) = (Nat.card K) ^ E` — together with F.10a's
finrank this is the cardinality/dimension pair the count laws consume, the WZ-BOX-7-
compliant packaging (cancellation identities and cardinalities; honesty F-3). The two
landed theorems that replace type-preservation claims in the consuming count layer are the
interface citations (DEPENDS-as-annotation, GC-13(b)): **H.87** (`carry_cancel`/
`carry_cancel_char_two`) and **H.61** (`TriangularUnitPivot.card_fibre`); no F node
re-proves either, and no F node states a twist-map type-preservation claim in their place.

Was an `axiom` stub at stage 0e; PROVED here (unit OM-9, 2026-08-16; gate values 16/9
re-fired numerically at om9_weld_cert.py LEG C2, extended to `E = 3`).
-/

namespace Uniformity.Density.Weld

theorem TwistedAlgebra.nat_card {E : ℕ} [NeZero E] {K : Type*} [Field K] [Finite K]
    (cc : CarryCocycle E K) :
    Nat.card (TwistedAlgebra cc) = Nat.card K ^ E := by
  show Nat.card (ZMod E → K) = Nat.card K ^ E
  rw [Nat.card_fun, Nat.card_zmod]

end Uniformity.Density.Weld
