/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H02

/-!
# Uniformity.ChapH.H03 — CS necessity, the arithmetic half

**Chapter H, NODE H.03** (`blueprint/CHAP-H_general_induction.md` §3). *For every genre datum
`G = (Q; e₁, f₁, μ; h)` (H.01) the composite block's abscissa length is at least `4`:*
`4 ≤ G.sideLen = e₁ · μ · f₁`.

The two side conditions of `GenreDatum` that carry the whole content are `hkey : 2 ≤ e₁ f₁`
("else the event is order-1 α/β") and `hmul : 2 ≤ μ`; multiplying them gives `4 ≤ μ (e₁ f₁)`,
which is `sideLen` after a commutation.

DEPENDS: H.01, H.02.

**⚠ SCOPE FENCE** (blueprint, mandatory). This node proves the *arithmetic* half of necessity
**only**. The step "a CS event **is** a repeated residual factor `(ψ, μ)` with `μ ≥ 2` and
`e · deg ψ ≥ 2` on a side of the stage polygon", and the step "the polygon of a stage with `m`
keys spans abscissas `[0, m]`, so `m ≥ 4`", are **geometric** and have no node — they are the
content of `GENIND-1(i)`'s partition (honesty item H-3). The passage from `4 ≤ L` to `m ≥ 4` to
`n ≥ 4` is H.04's third clause, **under the explicit hypotheses** `L ≤ m` and `m · D ≤ n`.

SOURCE: `EFF.GENIND.11` (§S5.1 *Necessity*, verbatim: *"The side's abscissa length is `e·g` with
`g ≥ μ·deg ψ`, so length `≥ e·μ·deg ψ ≥ 2·2·1 = 4` (case `e ≥ 2`, `ψ` linear) or `≥ 1·2·2 = 4`
(case `e = 1`, `deg ψ ≥ 2`) — in every case `≥ 4`"*); `EFF.GENIND.43` (the criterion in one line).

TEETH: `GT-CRIT` (`EFF.GENIND.11`, executable regression + planted grammar-acceptance mutant,
§S11 P-8 "0/22") and `GN-T-CRIT` (`EFF.GENHN.07`, planted mutant, fired 2/2: "grammar bound
`e₁f₁μ ≥ 4` dropped to `≥ 3` must accept an order-1 `(3)`-child fake") — both discharged here as
**Lean theorem**.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **NODE H.03.** *CS necessity, the arithmetic half.* The composite block's abscissa length
`L = e₁ μ f₁` is at least `4`, for every genre datum. Both `n = 4` solutions are saturating
(genre E `(2,1,2)` and genre F `(1,2,2)` both give `L = 4`); the enumeration of the equality case
is H.04. -/
theorem GenreDatum.four_le_sideLen (G : GenreDatum) : 4 ≤ G.sideLen :=
  calc (4 : ℕ) = 2 * 2 := rfl
    _ ≤ G.μ * (G.e₁ * G.f₁) := Nat.mul_le_mul G.hmul G.hkey
    _ = G.sideLen := by
        rw [GenreDatum.sideLen, ← Nat.mul_assoc, Nat.mul_comm G.μ G.e₁]

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.GenreDatum.four_le_sideLen

end AxCheck
