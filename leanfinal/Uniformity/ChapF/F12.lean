/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.Field.Basic

/-!
# Uniformity.ChapF.F12 — `W1Transport`: the W-1 transport carrier (HYP.139, MATH-class)

**Chapter F, NODE F.12** [interface-carrier] (`blueprint/CHAP-F_weld_layer.md` §5), ENV-F1.
`GENHN-BOX-2`'s sub-residue, at ledger strength — verbatim from the census: "Residue is NOT
the cite but the transport: W-1 (harness w, 𝑅 → FGMN objects) stays ATTEMPT"; GRTJC
L1990–1993: "Transport of the harness w and 𝑅 to the FGMN objects is still W-1 (ATTEMPT) —
and the corpus's own march-level dictionary for that transport, TR-3′-GEN, is OPEN at
general order." The transport law (`EFF.GRTJC.69`): `𝑅_λ = c_λ·R^{GMN}_λ` with `c_λ` a
LINE-WISE unit.

**Class MATH, distinct from F.11's CARRY: it does NOT discharge with a transcription fold.**
The `ι`-indexed shape is the transport's SIGNATURE only — the mathematics (that the unit
system exists compatibly at general order) is exactly what is OPEN; stating more would
manufacture a discharge. What the abstract carrier CAN carry is made machine-precise in
`F12w.lean` (unit OM-9): the carrier is equivalent to equality of vanishing loci, so the
MATH content of HYP.139 lives entirely in the site instantiation, not in this existential.

Binder spelling per A-W.1/F-D2 (`λ` is the lambda keyword; the type is unchanged).
Signatures byte-identical to the stage-0e gate. Landed by unit OM-9 (2026-08-16).
-/

namespace Uniformity.Density.Weld

/-- `W-1` (HYP.139) at ledger strength: the harness-to-FGMN transport dictionary exists at
the site's order — a line-wise unit system relating the two residual operators. MATH-class
obligation; chapter I's field, riding under `GenhnBox2`. Abstract shape: the two operator
families and the unit system are site data. -/
def W1Transport {K : Type*} [Field K] {ι : Type*}
    (Rharness RGMN : ι → K) : Prop :=
  ∃ c : ι → Kˣ, ∀ l, Rharness l = (c l : K) * RGMN l

end Uniformity.Density.Weld
