/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H73

/-!
# Uniformity.ChapH.H78 — `composedSigma`, the tower (composed) dictionary

**Chapter H, NODE H.78** (`blueprint/CHAP-H_general_induction.md` §11, the σ dictionary and the
`(e, f)`-forcing chain). For an outer genre datum `G = (Q; e₁, f₁, μ; h)` and inner data
`(e₂, f₂)`, the composed dictionary is H.73's `stageSigma` with `(e₁, f₁)` replaced by
`(e₁e₂, f₁f₂)`:

* `ram      ↦ ⟨{(2 e₁e₂, f₁f₂)}⟩`
* `twoSided ↦ ⟨{(e₁e₂, f₁f₂), (e₁e₂, f₁f₂)}⟩`
* `inert    ↦ ⟨{(e₁e₂, 2 f₁f₂)}⟩`

This is the σ-composition FORMULA `(e, f) ↦ (e₁e₂ · e_s, f₁f₂ · f_s)` — the part of the REFUTED
`T(b)` that SURVIVES (`EFF.GENHN.17`), applied to the composed-key pins.

**⚠ THIS IS A DEFINITION, NOT A THEOREM, AND ITS PERIMETER IS THE FULL INNER SIDE.**
`EFF.GENHN.44`'s CONDITIONALITY: *"(iii)'s perimeter is the FULL inner side, and the `[r3]` round
says so after the `[r2]` rider over-covered … PARTIAL-side inner `μ₂ = 2` leaves (`e₂f₂μ₂ < μ₁`,
first live `n = 10`) ride `[GENHN-TOW-1]` item (4), not (iii)"*, with a **fired** machine
counter-witness (the `n = 10` PE2-P member over `ℚ₂`, whose σ *"no proved display prices"*).
Chapter H defines the composed dictionary and proves its degree consistency (H.79); it makes **no
claim** about which leaves carry it. A statement asserting that `composedSigma` is the σ of any
actual polynomial would be out of chapter (honesty item H-5(2)/H-10) and is not made here or
anywhere downstream of this file.

The σ *values* stay with the executable regression (`genhnr2_supp.py`'s corrected-read-vs-PARI
rows: *"corrected `{(4,2)}` exact on every decided leaf; 3-stage `n = 16`:
`{(16,1)}/{(8,1),(8,1)}` exact"*); the Lean obligation that accompanies a dictionary of this shape
is the degree consistency `(composedSigma G e₂ f₂ ℓ).degree = 2 * (keyDeg G * (e₂ * f₂))`, which
is NODE H.79.

Definitional, no proof obligation.

DEPENDS: H.01 (`GenreDatum`), H.73 (`StageLeaf`) · landed `Uniformity.FactorizationType`.

SOURCE: `EFF.GENHN.44` (`T(b)′` clause (iii), the composed dictionary verbatim:
*"`composed-RAM (p₀ odd on dv₂, p₀ ≤ 2p₁) ↦ {(2e₁e₂, f₁f₂)}`;
`composed-2SIDED/SPLITEQ/SPLTAIL ↦ {(e₁e₂, f₁f₂)} ×2`; `composed-INERT ↦ {(e₁e₂, 2f₁f₂)}` — the
σ-composition FORMULA `(e, f) ↦ (e₁e₂·e_s, f₁f₂·f_s)` of the sealed (b) SURVIVES, applied to the
composed pins; inner `μ₂ ≥ 3` is `[GENHN-HE(μ₂)]`"*); `EFF.GENHN.17` (the refutation of `T(b)`,
and what survives).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- `T(b)′`(iii)'s composed dictionary: the σ-composition FORMULA `(e, f) ↦ (e₁e₂·e_s, f₁f₂·f_s)` —
the part of the REFUTED `T(b)` that SURVIVES, applied to the composed-key pins. -/
def composedSigma (G : GenreDatum) (e₂ f₂ : ℕ) : StageLeaf → FactorizationType
  | .ram      => ⟨{(2 * (G.e₁ * e₂), G.f₁ * f₂)}⟩
  | .twoSided => ⟨{(G.e₁ * e₂, G.f₁ * f₂), (G.e₁ * e₂, G.f₁ * f₂)}⟩
  | .inert    => ⟨{(G.e₁ * e₂, 2 * (G.f₁ * f₂))}⟩

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.composedSigma

end AxCheck
