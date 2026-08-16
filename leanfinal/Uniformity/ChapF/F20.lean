/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Data.Int.Basic

/-!
# Uniformity.ChapF.F20 — `JAGridLaw`: JA-GRID-CORR's UNCONDITIONAL half

**Chapter F, NODE F.20** [interface-carrier] (`blueprint/CHAP-F_weld_layer.md` §7), ENV-F1.
THEOREM JA-GRID at its C2-4-pinned scope (J-D0's grid leg). Governing form
`THEOREM JA-GRID-CORR` (`EFF.GRTJA.07`'s supersession, TERMINAL C2-4): **only the arithmetic
grid identity (eq-(12-int) digits = abscissa/side coordinates) and the carry clause are
unconditional; the print T-point additionally needs `u(V) ≥ 0`.** J-D0 consumes both AT THAT
GRADE (`EFF.JD0.25`'s priced-supplier table; BOX-1's own wording: "rides JA-GRID at GRTJA's
arc grade"), so this carrier is GRTJA arc 1/2 like F.19 — carried, never upgraded.

**The scope-pin is honoured by OMISSION.** The `u ≥ 0` proviso's unbounded-grid form is
HYP.21 — OUT of cone (§3 row 1) — so the print T-point clause is deliberately absent from
the carrier: nothing here states it, and no consumer can read it out of this Prop.

**Faithfulness.** The abstract shape (digit = coordinate + carry) is the eq-(12-int)
identity's skeleton; the concrete grid objects are the sites'. CARRIED, not proved.

Signature byte-identical to the stage-0e gate (`leanspec/Leanspec/ChapF.lean`).
-/

namespace Uniformity.Density.Weld

/-- JA-GRID-CORR's unconditional half (`EFF.GRTJA.07`, terminal C2-4): the integer-grid
digit/coordinate identity with its carry clause, as an abstract indexed law. Carried at
GRTJA arc 1/2; the print T-point clause (needs `u(V) ≥ 0`) is deliberately absent. -/
def JAGridLaw {ι : Type*} (digit : ι → ℤ) (coord : ι → ℤ) (carry : ι → ℤ) : Prop :=
  ∀ i, digit i = coord i + carry i

end Uniformity.Density.Weld
