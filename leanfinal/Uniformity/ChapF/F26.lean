/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Field.Basic

/-!
# Uniformity.ChapF.F26 — `DmultW`: the `(DMULT-w)` tier at its HEAD provenance

**Chapter F, NODE F.26** [interface-carrier] (`blueprint/CHAP-F_weld_layer.md` §7), ENV-F1.
Verbatim shape from `EFF.GRTJC.69`: there is a unit `ω(λ, μ) ∈ Kˣ`, **independent of `f`
and `g`** (line-only), with `𝑅_{λ+μ}(f·g) = ω(λ,μ) · y^{δ(λ,μ)} · 𝑅_λ(f) · 𝑅_μ(g)` and the
wrap exponent `δ(λ,μ) ∈ {0,1}`. This is the tier W-9's chain actually rides.

**FRAGILE — the quantifier order IS the content.** `∃ ω` sits AFTER the line pair
`(lam, mu)` and BEFORE `(f, g)`: that placement is the exact meaning of "independent of `f`
and `g`". A type-checked commute of those quantifiers would be a defect, not a variant; the
`Iff.rfl` fence below the declaration pins the signed body against drift. Binder spelling
`lam`/`mu` per A-W.1/F-D2 (`λ` is the lambda keyword; the type is unchanged). The `•`-form
keeps `ω` visibly a unit.

**Status at HEAD, carried honestly.** DERIVED from [FGMN] Thm 4.2's rank-one freeness via
LEMMA JC-RANKMULT (`EFF.GRTJC.129`, Annex #6); the corpus's earlier "quoted product
identity" claim is WITHDRAWN. The literature import underneath is therefore the `(IN-3)`
FGMN graded package (`EFF.GRTJC.43`; FGMN cites PDF-VERIFIED at `EFF.GRTJC.125`, Annex #3),
and per Part V that exercised cite is an **owner gate-(b) item**: `[cite: FGMN Thm 4.2
(rank-one freeness), via EFF.GRTJC.43's (IN-3) package]`, routed through chapter I's cite
block. **CARRIED, not proved** — this node states the tier, it does not discharge it.

**The strong tier is OUT.** `(DMULT-s)` — the `ω ≡ 1` sharpening (`EFF.GRTJC.69`'s first
tier, HYP.77) — is §3 row 5, `BLOCKED: OUT-OF-CONE`; nothing here asserts it, and the
displayed derivation `ω(λ,μ) = c_{λ+μ}/(c_λ c_μ)` is precisely "the 2-coboundary of the
line-wise unit system; nothing gives `ω ≡ 1`". That mechanism is machine-checked one file
over, at the carrier vocabulary: `F12w.lean`'s `lineCobdry`, `lineCobdry_cocycle` and
`lineCobdry_eq_one_iff` (unit OM-9). Consumer split carried verbatim: "(COORD-B)(2),
(MULT-B), JC-CARRY-m, W-8 and JC-BOX-4's corner closure need only (DMULT-w)" — the
mechanism being that the normalized coordinate `ρ_λ = 𝑅_λ/a_λ` is invariant under ANY
line-wise rescaling.

DEPENDS-as-annotation: F.07 (the δ shadow's shape) — no import, the carrier is abstract in
`δ`. Signature byte-identical to the stage-0e gate.
-/

namespace Uniformity.Density.Weld

open Polynomial

/-- The (DMULT-w) tier (`EFF.GRTJC.69`): residual multiplicativity up to a line-only unit,
with the {0,1} wrap exponent. Carried; discharge rides the gate-(b) FGMN cite. -/
def DmultW {K : Type*} [Field K] {Λ : Type*} [Add Λ]
    (R : Λ → K[X] → K[X]) (y : K[X]) (δ : Λ → Λ → ℕ) : Prop :=
  ∀ lam mu : Λ, ∃ ω : Kˣ, ∀ f g : K[X],
    R (lam + mu) (f * g) = (ω : K) • (y ^ δ lam mu * R lam f * R mu g)

-- Below the contract line: the quantifier-order fence. `∃ ω` between the line pair and
-- `(f, g)` is the signed body; this pin fails to elaborate if the carrier ever drifts.
example {K : Type*} [Field K] {Λ : Type*} [Add Λ]
    (R : Λ → K[X] → K[X]) (y : K[X]) (δ : Λ → Λ → ℕ) :
    DmultW R y δ ↔
      ∀ lam mu : Λ, ∃ ω : Kˣ, ∀ f g : K[X],
        R (lam + mu) (f * g) = (ω : K) • (y ^ δ lam mu * R lam f * R mu g) := Iff.rfl

end Uniformity.Density.Weld
