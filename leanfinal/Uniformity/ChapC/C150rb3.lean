/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C26
import Uniformity.ChapC.C29
import Uniformity.ChapC.C43
import Uniformity.ChapC.C51
import Uniformity.ChapC.C118a
import Uniformity.ChapC.C118b

/-!
# Uniformity.ChapC.C150rb3 — READY batch 3: the composedKey-unblocked §7-tail/§8 family

Unit RB3. Attempts the four names from `runs/wave-b/verdict_CCUR.md`'s "Batch 3 — the
now-composedKey-unblocked §7-tail/§8 family" list. **Two land, two are genuinely BLOCKED**
(real proof-content gaps, precisely named below and in `runs/wave-b/verdict_RB3.md`; no
`sorry`, no new axiom, no weakened restatement for either).

## Landed

* `side_degree_conservation` (C.70) — a direct two-lemma assembly: C.26's
  `natDegree_dvResPoly` (the residual polynomial's degree IS `dvSideDeg`) composed with C.08's
  `dvSideLen_eq` (`dvSideLen = ℓ · dvSideDeg`).
* `window_band1` (C.58) — a direct two-lemma assembly from the A-C.7 congruence-stability
  toolkit: `dv2_read_congr_min` (the capped level-2 pin law) plus `C118b.eq_of_min_eq_of_lt`
  gives clause (a); `C118b.dv2Res_congr_of_lt` gives clause (b), both fed by
  `C118a.monicPoly_coeff_congr` + `C118a.dev_blocks_congr` turning the `proj`-congruence
  hypothesis into a coefficientwise `π^N`-divisibility on the two members' `j`-th
  `composedKey`-digit.

## BLOCKED (genuine proof-content gaps, not naming)

* `refine_invariants` (C.56) — GENTOW-2(i)+(ii), the composed-key Hensel refinement step.
  `composedKey` (C.43) is landed, clearing the ONLY blocker `RESCHEDULE_C56_2026-08-16.md`
  named, but the theorem's actual content is a one-step Newton–Hensel refinement of
  `composedKey T` against a `μ₂`-th-power residual `(X - C s)^μ₂` at slope `(lam, 1)`: no
  landed lemma transports a witness `f ∈ towerLocus T μ₂`'s dv2-residual pattern to
  `composedKey T`'s own residual at that slope (the `hne`/`hres` are stated about `f`, not
  about `composedKey T`, and the conclusion is entirely about `composedKey T -
  k2DigitLift T s lam`), nor is there a landed "subtract the digit lift, the corrected key
  is still monic/right-degree/`IsTestKey`" one-step-refinement lemma. This is new mathematics
  on the scale of C.47's `composedKey_isTestKey` or C.131w's `shadow_floor` (~200-900 new
  lines each), not a wrap.
* `shadow_persistence` (C.74 family) — needs (1) an "upward" bridge lemma from the
  coefficientwise `hbudget` valuation floor (on
  `(dev F.key (dev (composedKey T) g j') b).coeff a`) to a `dv2Hgt`/`dv2Pin`-level lower bound
  on `shadowDev T g j - dev (composedKey T) g j`; the landed C.131w machinery
  (`dv2Hgt_dev_floor`, `dev_coeff_paid_floor`) only supplies the OPPOSITE direction (an overall
  height floor descending to per-digit floors), and is besides bespoke to the θ/margin grid
  calculus, not `addVal`/`hbudget`'s shape. And (2) additivity of `biRead`/`shadowDev` in the
  polynomial argument (`biRead_add`, plus monicity of `biRead F (composedKey T)`) to combine
  `(composedKey T)^μ₂ + g`'s shadow discrepancy from the two summands' separately-established
  discrepancies via the C131y `dv2Hgt_add_eq_left_of_lt`/`dv2Res_add_deep` perturbation
  pattern — neither `biRead_add` nor that monicity fact is landed anywhere in the corpus
  (checked: `grep -rn "biRead_add\|biRead.*Monic" Uniformity/ChapC/*.lean` returns nothing).

## Status

Sorry-free, axiom-free (Lean core only) for the two landed theorems.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density.Leaf
open Uniformity.Density.Tower.C118a Uniformity.Density.Tower.C118b

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### NODE C.70 — `side_degree_conservation`: the side-length/residual-degree identity -/

/-- **NODE C.70 — `side_degree_conservation`** (leanspec-signed, verbatim). The side's
horizontal length `L_λ` is `ℓ` times the residual polynomial's degree: C.08's spacing law
(`dvSideLen = ℓ · dvSideDeg`) composed with C.26's exactness law
(`(dvResPoly …).natDegree = dvSideDeg`). -/
theorem side_degree_conservation (F : KeyFrame O π) (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {H₀ : ℕ} (hpin : F.Pin H₀)
    {f : Polynomial O} {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hf : f.Monic) (hpure : IsDvPure F f u ℓ)
    (hne : (dvSideSet F f u ℓ).Nonempty) {M₀ : ℕ}
    (hp : dvHgt F f (dvSideMin F f u ℓ hne) = (M₀ : ℕ∞)) :
    dvSideLen F f u ℓ hne = ℓ * (dvResPoly F H₀ hpin f u ℓ hne M₀ hp).natDegree := by
  rw [dvSideLen_eq F hℓ hcop hne, (natDegree_dvResPoly F hπ H₀ hpin hℓ hcop hne hp).1]

/-! ### NODE C.58 — `window_band1`: congruence-stability of the composed window below a band -/

/-- **NODE C.58 — `window_band1`** (leanspec-signed, verbatim). Two coefficient vectors
congruent mod `𝔪^N` (`proj`-equal) give the same `composedKey`-digit pin and coherent
residual read at any slot `j` whose pin sits strictly below the window `F.e₁ · T.e₂ · N`. -/
theorem window_band1 {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {μ₂ N : ℕ} {a a' : Fin (μ₂ * T.D₂) → O}
    (hc : proj O (μ₂ * T.D₂) N a = proj O (μ₂ * T.D₂) N a')
    (ha : monicPoly a ∈ towerLocus T μ₂) {j m : ℕ} (hj : j < μ₂)
    (hm : dv2Pin (T.levelDatum hπ) (composedKey T) (monicPoly a) j = (m : ℕ∞))
    (hband : m < F.e₁ * T.e₂ * N) :
    dv2Pin (T.levelDatum hπ) (composedKey T) (monicPoly a') j = (m : ℕ∞) ∧
    dv2Res (T.levelDatum hπ) (dev (composedKey T) (monicPoly a') j)
      = dv2Res (T.levelDatum hπ) (dev (composedKey T) (monicPoly a) j) := by
  have hcg0 : ∀ i, π ^ N ∣ (monicPoly a - monicPoly a').coeff i :=
    C118a.monicPoly_coeff_congr hπ hc
  have hcg : ∀ i, π ^ N ∣ (dev (composedKey T) (monicPoly a) j
      - dev (composedKey T) (monicPoly a') j).coeff i :=
    C118a.dev_blocks_congr hπ hcg0 (composedKey T) j
  have hlt : dv2Pin (T.levelDatum hπ) (composedKey T) (monicPoly a) j
      < (((F.e₁ * (T.levelDatum hπ).ℓ) * N : ℕ) : ℕ∞) := by
    show dv2Pin (T.levelDatum hπ) (composedKey T) (monicPoly a) j
      < (((F.e₁ * T.e₂) * N : ℕ) : ℕ∞)
    rw [hm]
    exact_mod_cast hband
  have hmin := dv2_read_congr_min (T.levelDatum hπ) hπ (Ψ := composedKey T) hc j
  have hpin' : dv2Pin (T.levelDatum hπ) (composedKey T) (monicPoly a') j
      = dv2Pin (T.levelDatum hπ) (composedKey T) (monicPoly a) j :=
    C118b.eq_of_min_eq_of_lt hmin hlt
  refine ⟨hpin'.trans hm, ?_⟩
  exact (C118b.dv2Res_congr_of_lt (T.levelDatum hπ) hπ hcg hlt).symm

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.side_degree_conservation
#print axioms Uniformity.Density.Tower.window_band1

end AxCheck
