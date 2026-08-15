/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H02
import Uniformity.ChapH.H78

/-!
# Uniformity.ChapH.H79 — the composed (tower) dictionary is degree-exhausting

**Chapter H, NODE H.79** (`blueprint/CHAP-H_general_induction.md` §11, the σ dictionary and the
`(e, f)`-forcing chain). H.78's `composedSigma G e₂ f₂` is H.73's stage dictionary with the ambient
key `(e₁, f₁)` replaced by the composed key `(e₁e₂, f₁f₂)`. This file proves that each of its three
σ-blocks exhausts the **composed** block degree `2·D₂`, where `D₂ = D′·e₂f₂ = e₁e₂ · f₁f₂` and
`D′ = keyDeg G = e₁f₁`:

* `ram`: `(2e₁e₂) · f₁f₂ = 2D₂` ✓
* `twoSided`: `2 × (e₁e₂ · f₁f₂) = 2D₂` ✓
* `inert`: `e₁e₂ · (2f₁f₂) = 2D₂` ✓

The second statement, `composedDeg_eq`, is the regrouping `D′·(e₂f₂) = (e₁e₂)·(f₁f₂)` that the
forcing chain of `EFF.GENHN.42`(i) uses to identify the two ways of writing `D₂`.

**Arithmetic audit (recomputed fresh, at the `n = 8` first-live tower and the `n = 16` 3-stage
row).** `n = 8`: the tower datum is `(e₁f₁, μ₁) = (2, 4)` with inner `(e₂f₂, μ₂) = (2, 2)`, so
`D′ = 2`, `e₂f₂ = 2`, `D₂ = 4` and `2D₂ = 8 = n` ✓. `EFF.GENHN.47`'s table gives the three PE1
members' true σ as `{(8,1)}` — degree `8` ✓ — and the *refuted* stage-shadow readings `{(4,2)}` and
`{(4,1)²}` are **also** of degree `8` ✓, *"which is exactly why only PARI could separate them"*.
`n = 16`, 3-stage: `{(16,1)}` and `{(8,1),(8,1)}` are both of degree `16` ✓.

**Degree consistency is necessary and NOT sufficient** — recording that asymmetry is the point of
the audit. This file proves the necessary half; the oracle (`genhnr2_supp.py`'s corrected-read-
vs-PARI rows: *"corrected `{(4,2)}` exact on every decided leaf; 3-stage `n = 16`:
`{(16,1)}/{(8,1),(8,1)}` exact"*) supplies the rest. In particular, and per H.78's fence, **nothing
here claims `composedSigma` is the σ of any actual polynomial**, nor which leaves carry it:
`EFF.GENHN.44`'s clause (iii) has the FULL inner side as its perimeter, and PARTIAL-side inner
`μ₂ = 2` leaves (`e₂f₂μ₂ < μ₁`, first live at `n = 10`) ride `[GENHN-TOW-1]` item (4) instead, with
a fired machine counter-witness. That is honesty item H-5(2)/H-10, and it stays out of chapter.

DEPENDS: H.01 (`GenreDatum`), H.02 (`GenreDatum.keyDeg`), H.78 (`composedSigma`) · landed
`FactorizationType.degree`.

SOURCE: `EFF.GENHN.44`'s own *arithmetic audit*, verbatim: *"Block degree at `μ₂ = 2` is
`2D₂ = 2e₁e₂f₁f₂`. RAM: `2e₁e₂ · f₁f₂ = 2D₂` ✓. 2SIDED: `2 × (e₁e₂ · f₁f₂) = 2D₂` ✓. INERT:
`e₁e₂ · 2f₁f₂ = 2D₂` ✓. All three exhaust the block ✓. Composition with S7's level-1 dictionary:
substituting `(e₁, f₁) ↦ (e₁e₂, f₁f₂)` into `.15`'s three rows reproduces this table exactly ✓ —
i.e. the dictionary really is S7's, re-based."*; `EFF.GENHN.42`(i) (`D₂ := D′e₂f₂`, and the forcing
chain's `e₁e₂ · f₁f₂ = D₂`).

TEETH: as H.78 (`genhnr2_supp.py`'s corrected-read-vs-PARI rows) → **Lean theorem** for the degree.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **The composed degree, regrouped.** `D₂ = D′ · e₂f₂ = (e₁e₂) · (f₁f₂)`: the two ways
`EFF.GENHN.42`(i) writes the composed key degree agree. -/
theorem composedDeg_eq (G : GenreDatum) (e₂ f₂ : ℕ) :
    G.keyDeg * (e₂ * f₂) = (G.e₁ * e₂) * (G.f₁ * f₂) := by
  simp only [GenreDatum.keyDeg]; ring

/-- **The composed dictionary is degree-exhausting at the composed degree.** Each of the three
σ-blocks of `composedSigma G e₂ f₂` has total degree `2 · D₂` with `D₂ = keyDeg G · (e₂ f₂)`. -/
theorem composedSigma_degree (G : GenreDatum) (e₂ f₂ : ℕ) (l : StageLeaf) :
    (composedSigma G e₂ f₂ l).degree = 2 * (G.keyDeg * (e₂ * f₂)) := by
  rw [composedDeg_eq]
  cases l <;>
    simp [composedSigma, FactorizationType.degree, Multiset.map_cons, Multiset.sum_cons] <;>
    ring

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.composedDeg_eq
#print axioms Uniformity.Density.Induction.composedSigma_degree

end AxCheck
