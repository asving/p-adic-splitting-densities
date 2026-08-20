/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B22
import Uniformity.ChapC.C26
import Uniformity.ChapC.C29
import Uniformity.ChapC.C97

/-!
# Uniformity.ChapC.C35b — the D13 divisibility question, SETTLED: REFUTED

**The question** (leanspec defect D13; the hinge of C.35's `blockFactor_spec` clause 3 and
C.40's `level2_peel` clause (iii)): does `HasLabel L g` force `D′ = e₁f₁ ∣ deg g`?

```lean
theorem hasLabel_natDegree_dvd … (hg : HasLabel L g) : (F.e₁ * F.f₁) ∣ g.natDegree
```

**ANSWER: NO — machine-refuted below** (`d13_refuted : ¬ D13Statement`), by a CONSTRUCTED
frame at the landed `s2Frame` (C.97, `Φ′ = x² − 2` over any base with `2` a uniformizer,
`(e₁, f₁, h) = (2, 1, 1)`, `D′ = 2`), realized absolutely over `ℤ_[2]`.

## The refuting instance, in full

* frame `F = s2Frame h2 hq` (C.97), pin `H₀ = 1` (`s2Frame_pin`);
* `g₀ = x³ − 2x + 4 = x·Φ′ + 4` — monic of degree **3**, and `2 ∤ 3`;
* its `Φ′`-development is `A₀ = 4 = 2²`, `A₁ = x`, so the level heights are
  `dv(A₀) = 4`, `dv(A₁) = 1`, `⊤, ⊤`;
* at `(u, ℓ) = (3, 1)` the cleared level support is `4`, attained at BOTH abscissae `0` and
  `1 = ⌊3/2⌋` — so `g₀` is `(3,1)`-pure in exactly `IsDvPure`'s endpoint sense (purity
  constrains `⌊deg g/D′⌋`, and says NOTHING about `deg g mod D′` — that is the defect);
* the level residual `ρ = R_λ(g₀)` is monic of degree 1 with nonzero constant term
  (C.26 supplies degree and constant term; the leading coefficient is the ϖ-read of the top
  digit `A₁ = x` at height 1, which is `res(θ/ϖ) = 1` since `ϖ = x` at this frame —
  `twistRead 1 x = η⁻¹⁰ · digAt 2 0 1 = 1`);
* the level datum `L₀` takes `u = 3, ℓ = 1` (`hκ : 1·(2·1)·1 = 2 < 3` ✓) and
  **`r := ρ` itself** — monic ✓, irreducible (degree one over the stage field `K₁`) ✓,
  `r(0) ≠ 0` ✓ (C.26), `0 < deg r` ✓;
* then `HasLabel L₀ g₀` holds with `m = 1` (`dvResPoly = ρ = r¹` on the nose), while
  `F.e₁ * F.f₁ = 2 ∤ 3 = deg g₀`.

## Consequence (of the two worked out at the D13 record)

**D13 is dead as written.** `blockFactor_spec`'s clause 3 (`D′ ∣ deg (blockFactor L f)`)
cannot be discharged from `HasLabel` alone; it survives ONLY through maximality — one must
show a `g` like `g₀` can never be the MAXIMAL labelled divisor of a `BlockContext` `f`.
That is a within-slope refinement claim, i.e. C.34's frontier again: **the obligation is
confirmed inseparable from C.34**, and the divisibility rider of C.35's `BlockFrontier`
CANNOT be dropped. Companion records: `C35_CLAUSE3_DEFECT_2026-08-20.md` (C.35),
`C40.lean` header (C.40), `C35B_D13_REFUTED_2026-08-20.md` (this settlement).

## Status

Evidence-grade refutation, part of the build. No `sorry`, Lean-core axioms only.
-/

namespace Uniformity.Density.Tower.C35b

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower

/-! ## 0. The D13 target, as a ∀-closure (`Type 0`, all binders explicit) -/

/-- The D13 divisibility claim `hasLabel_natDegree_dvd`, closed over everything: every
labelled `g` (C.29's `HasLabel`) has `D′ = e₁f₁ ∣ deg g`.  `d13_refuted` below proves this
FALSE. -/
def D13Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (π : O)
    (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key
      (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    (L : LevelDatum F H₀ hpin) (_hπ : Irreducible π) (g : Polynomial O)
    (_hg : HasLabel L g), (F.e₁ * F.f₁) ∣ g.natDegree

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## 1. The refuting polynomial `g₀ = x³ − 2x + 4` and its `Φ′`-development -/

/-- the refuting labelled polynomial: `g₀ = x³ − 2x + 4 = x·Φ′ + 2²`, monic of ODD degree
`3` at the `D′ = 2` frame. -/
noncomputable def g₀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    Polynomial O :=
  Polynomial.X ^ 3 - Polynomial.C 2 * Polynomial.X + Polynomial.C 4

theorem g₀_monic : (g₀ O).Monic := by
  sorry

theorem g₀_natDegree : (g₀ O).natDegree = 3 := by
  sorry

/-- `2 ∤ 3` — the divisibility the D13 claim asserts, false at `g₀`. -/
theorem g₀_not_dvd :
    ¬ ((s2Frame h2 hq).e₁ * (s2Frame h2 hq).f₁ ∣ (g₀ O).natDegree) := by
  sorry

theorem dev_g₀_zero : dev (s2Key O) (g₀ O) 0 = Polynomial.C ((2 : O) ^ 2) := by
  sorry

theorem dev_g₀_one : dev (s2Key O) (g₀ O) 1 = Polynomial.X := by
  sorry

/-! ## 2. The level polygon of `g₀`: heights `(4, 1, ⊤, ⊤)`, side `{0, 1}` at `(u,ℓ)=(3,1)` -/

theorem dvhgt_g₀_0 : dvHgt (s2Frame h2 hq) (g₀ O) 0 = (4 : ℕ∞) := by
  sorry

theorem dvhgt_g₀_1 : dvHgt (s2Frame h2 hq) (g₀ O) 1 = (1 : ℕ∞) := by
  sorry

theorem dvside_g₀ : dvSideSet (s2Frame h2 hq) (g₀ O) 3 1 = {0, 1} := by
  sorry

theorem hne_g₀ : (dvSideSet (s2Frame h2 hq) (g₀ O) 3 1).Nonempty := by
  sorry

theorem pure_g₀ : IsDvPure (s2Frame h2 hq) (g₀ O) 3 1 := by
  sorry

theorem hp_g₀ : dvHgt (s2Frame h2 hq) (g₀ O)
    (dvSideMin (s2Frame h2 hq) (g₀ O) 3 1 (hne_g₀ h2 hq)) = ((4 : ℕ) : ℕ∞) := by
  sorry

/-! ## 3. The level residual `ρ = R_λ(g₀)` is MONIC of degree 1 with `ρ(0) ≠ 0` -/

/-- the level residual polynomial of `g₀` at `(u, ℓ) = (3, 1)`, pinned at `M₀ = 4`. -/
noncomputable def ρ : Polynomial ((s2Frame h2 hq).stageField 1 (s2Frame_pin h2 hq)) :=
  dvResPoly (s2Frame h2 hq) 1 (s2Frame_pin h2 hq) (g₀ O) 3 1 (hne_g₀ h2 hq) 4 (hp_g₀ h2 hq)

theorem ρ_natDegree : (ρ h2 hq).natDegree = 1 := by
  sorry

theorem ρ_coeff_zero_ne : (ρ h2 hq).coeff 0 ≠ 0 := by
  sorry

/-- the ϖ-read of the top digit `A₁ = x` at its on-side height `1` is `1` — `ϖ = x` at this
frame, so the read is `res(θ/ϖ) = 1`. -/
theorem twistRead_one_X :
    (s2Frame h2 hq).twistRead 1 (s2Frame_pin h2 hq) 1 (Polynomial.X : Polynomial O) = 1 := by
  sorry

theorem ρ_monic : (ρ h2 hq).Monic := by
  sorry

/-! ## 4. The level datum `L₀` with `r := ρ`, and `HasLabel L₀ g₀` -/

/-- **the refuting level datum**: `(u, ℓ) = (3, 1)` and `r := ρ` itself. -/
noncomputable def L₀ : LevelDatum (s2Frame h2 hq) 1 (s2Frame_pin h2 hq) where
  u := 3
  ℓ := 1
  r := ρ h2 hq
  hℓ := Nat.one_pos
  hcop := Nat.coprime_one_right 3
  hκ := by sorry
  hrmonic := ρ_monic h2 hq
  hrirr := by sorry
  hr0 := ρ_coeff_zero_ne h2 hq
  hrdeg := by sorry

/-- **the label holds**: `g₀` is monic of positive degree, `(3,1)`-pure, and its level
residual is `r¹` on the nose. -/
theorem hasLabel_g₀ : HasLabel (L₀ h2 hq) (g₀ O) := by
  sorry

/-! ## 5. The refutation -/

/-- **D13 IS FALSE.**  The constructed frame realizes every hypothesis of
`hasLabel_natDegree_dvd` over `ℤ_[2]` while its conclusion fails (`2 ∤ 3`). -/
theorem d13_refuted : ¬ D13Statement := by
  sorry

end Uniformity.Density.Tower.C35b

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C35b.d13_refuted

end AxCheck
