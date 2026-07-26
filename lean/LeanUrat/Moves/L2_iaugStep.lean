/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.L5_landBox
import LeanUrat.Moves.L5_landVertex

/-!
# Moves/L2_iaugStep — (I-aug) chord slope after an increment (D.4)

The landing box (`L5.landBox`, phrased on the anchored ψ-order `μ`) gives, in the PARENT
valuation `w`, for `j < μ`:

  `w(B_j) + j·ehg > w f = w(B_μ) + μ·ehg`,   with `ehg = e·h·g = w(Φ̂)`,

so the chord from `(j, w(B_j))` to the pinned vertex `(μ, w(B_μ))` descends with slope
`(w(B_j) − w(B_μ))/(μ − j) > ehg`. Rearranged, cleared of denominators:

  `ehg·(μ − j) < w(B_j) − w(B_μ)`.   (MOVES ~2085-2094.)

## Proof structure

* The strict box inequality `w f < w(B_j) + j·ehg` for `j < μ` is the imported dep unit
  `L5.landBox`; the pinned-vertex identity `w(B_μ) + μ·ehg = w f` is the imported dep unit
  `L5.landVertex`.  The arithmetic rearrangement into the cleared-denominator chord is proved
  here in full.
* Both dep units carry the hypotheses `hψ : Irreducible ψ` and `hψz : ψ ≠ X`.  `Irreducible ψ`
  is now a hypothesis of THIS unit (the MOVES §B2-DEF repair fence-change, semantic-audit
  approved: the tower only ever applies `iaugStep` at an irreducible residual minimal
  polynomial ψ; cf. blueprint gap G4 scoping `iaugStep` to the irreducible key).  `ψ ≠ X` is
  DERIVED below from the hypotheses at hand: `j < μ` forces `μ ≥ 1`, so `ψ^μ ∣ Ranch` with
  `ψ = X` would give `Ranch.coeff 0 = 0`, contradicting the anchor normalization `hanch.1`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.Moves

theorem L2_iaugStep {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (hψ : Irreducible ψ) (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (μ : ℕ) (a : ℤ) (Ranch : Polynomial ↥σ.K) (hanch : HasAnchorK (σ.R f) a Ranch) (hord : OrdPsiPoly ψ Ranch μ) (B : ℕ → Polynomial ℤ_[p]) (N : ℕ) (hdev : IsDevelopment Φhat f B N) (j : ℕ) (hj : j < μ) (hjnz : B j ≠ 0) : (σ.e : ℤ) * σ.h * g * ((μ : ℤ) - j) < σ.w (B j) - σ.w (B μ) := by
  -- `ψ` data carried by the standard lift.
  have hmon : ψ.Monic := hlift.1
  have hg : ψ.natDegree = g := hlift.2.1
  -- `j < μ` forces `μ ≥ 1`.
  have hμpos : 0 < μ := lt_of_le_of_lt (Nat.zero_le j) hj
  -- DERIVED: `ψ ≠ X` — else `X^μ ∣ Ranch` with `μ ≥ 1` kills the anchored constant term.
  have hψz : ψ ≠ Polynomial.X := by
    intro heq
    have hXdvd : Polynomial.X ∣ Ranch := by
      refine dvd_trans (dvd_pow_self Polynomial.X hμpos.ne') ?_
      rw [← heq]; exact hord.1
    exact hanch.1 (Polynomial.X_dvd_iff.mp hXdvd)
  -- With `hψ : Irreducible ψ` now a hypothesis, fire the two dep units and rearrange.
  have hbox := L5_landBox σ ψ g hg hmon hψ hψz Φhat hlift f hf μ a Ranch hanch hord B N hdev j hj hjnz
  have hpin := (L5_landVertex σ ψ g hg hmon hψ hψz Φhat hlift f hf μ a Ranch hanch hord B N hdev).1
  -- ARITHMETIC CORE: `ehg·(μ−j) = μ·ehg − j·ehg`, then the chord follows linearly.
  have expand : (σ.e : ℤ) * σ.h * g * ((μ : ℤ) - j)
      = (μ : ℤ) * ((σ.e : ℤ) * σ.h * g) - (j : ℤ) * ((σ.e : ℤ) * σ.h * g) := by ring
  rw [expand]
  linarith

end LeanUrat.Moves
