/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.Field.Basic

/-!
# Uniformity.ChapF.F19 — `JAResLaw`: THEOREM JA-RES at its recorded scope

**Chapter F, NODE F.19** [interface-carrier] (`blueprint/CHAP-F_weld_layer.md` §7), ENV-F1.
The per-slot law that is `JD0-BOX-2`'s residual leg and JB-DEV(iii)(RES)'s supplier.
Verbatim scope from `EFF.GRTJA.08`: level `m ≥ 2`, shared keys below `m`; IF `(VD-(m−1))`
holds at every on-line digit `a_i` of `A` (the PER-DIGIT PROVISO), THEN for every attained
abscissa `i`: `c_i = z_{m−1}^{−i·A_{m−1}} · C_i` — the print's order-`m` residual coefficient
equals the harness packed digit times the PURE CHARACTER in the abscissa.

**Grade: GRTJA arc 1/2 — the single priced input on J-D0's critical path (honesty F-7);
carried, never upgraded.** Unconditional at `m = 2` (the proviso is `(VD-1)` = W2-L3,
`EFF.GRTW2.14`, consumed); proviso-scoped at `m ≥ 3`, root-inclusive `[r2]`. F.04's residual
leg is deliberately not a third conjunct: the sites consume it through THIS form, so the
grade cap stays visible where chapter I reads it.

**Faithfulness.** The carrier fixes the law's SHAPE (one `z`-power per abscissa — exactly
what F.05's strikes instantiate); the per-digit proviso and the root-inclusive perimeter are
instance-side hypotheses (they quantify over tower digits F has no carrier for). JA-BOX-1's
refuted slot-independent form is fenced by construction: the exponent is `abscissa i * A`,
never a constant. CARRIED, not proved — the instance is the priced supplier obligation
chapter I sees through F.04's provenance.

Signature byte-identical to the stage-0e gate (`leanspec/Leanspec/ChapF.lean`).
-/

namespace Uniformity.Density.Weld

/-- JA-RES at recorded scope (`EFF.GRTJA.08`): the per-slot pure-character law relating
print residual coefficients to harness packed digits. Carried at GRTJA arc 1/2. -/
def JAResLaw {K : Type*} [Field K] {ι : Type*}
    (printCoeff harnessDigit : ι → K) (z : Kˣ) (A : ℤ) (abscissa : ι → ℤ) : Prop :=
  ∀ i, printCoeff i = (z ^ (-(abscissa i * A)) : Kˣ) * harnessDigit i

end Uniformity.Density.Weld
