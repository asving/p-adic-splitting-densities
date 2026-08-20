/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C53
import Uniformity.ChapB.B15
import Uniformity.ChapB.B18
import Uniformity.ChapB.B30

/-!
# Uniformity.ChapC.C53c — `TriangularDigitRead` machine-REFUTED

**Sub-unit of NODE C.53** (companion to `C53_LEG2_REFUTED_2026-08-20.md`): the PROSE refutation
of C.53 leg 2 (`TriangularDigitRead`, `C53.lean`), converted into a machine-checked theorem, by
the record's explicit numeric instance.  Nothing here is signed; nothing in `C53.lean` or
`C53b.lean` is edited.  Pattern: `C35b.lean` (`d13_refuted` + `hasLabel_natDegree_dvd_false`).

## The refuting instance (the record's, verbatim)

* frame `linFrame hπ : KeyFrame O π` — `Φ′ = X + π`, `(e₁, f₁, h) = (1, 1, 1)`, `D′ = 1`,
  over any DVR base; pin `H₀ = 1`;
* tower `linTower hπ : TowerDatum (linFrame hπ) 1 _` — `(e₂, f₂, u₂) = (2, 1, 3)`,
  `ψ₂ = T + 1`; fences: `hcomp : 2 ≤ 2`, `hcop : Coprime 3 2`, `hfloor : 2·1·1 = 2 < 3`;
* derived: `D₂ = 2`, `E₂ = 6`, `μ₂ = 1`, `n = μ₂D₂ = 2`, floors `(4, 2)` at slots `0, 1`;
* `f₂ = 1` and `f₁ = 1` make C.43's `composedKey` explicitly `Φ₂ = (X+π)² − C w` for a single
  constant `w : O` (`slotIdx 3 = 0`, one `stageLiftIA` summand), so `Φ₂.coeff 1 = 2π` EXACTLY —
  no appeal to C.47's `cLift` bounds and, crucially, **no appeal to C.50's transcribed
  `gridWeight` scope note** (corpus prose): the numeric route needs only landed theorems.
* At window `N = 2`, class `c = 0`, and residue characteristic ≠ 2 (`IsUnit (2 : O)`):
  RAW-BOX contains `0` (witness `a = 0`, `addVal 0 = ⊤`), DIGIT-BOX does not — any lift `a`
  of `0` has `a 1 ∈ 𝔪²`, so the slot-1 two-key digit `a 1 − 2π` has `addVal = 1 < 2 = floor`.
* Absolute realization: `O = ℤ_[3]`, `π = 3` (both `Irreducible (3 : ℤ_[3])` and
  `IsUnit (2 : ℤ_[3])` hold), so nothing is vacuous.

**Why NOT the `s2Frame` workhorse** (today's C.27/C.35b/C.61 counterexample frame): there the
residue characteristic IS 2, `2π = 4` collapses into the uniformizer tower, and the obstructing
digit of `X^{D₂}` migrates into the `stageLiftO` correction constant — exactly the computation
the record's instance is designed to avoid.  The linear frame keeps the obstructing digit
`a 1 − 2π` independent of the (opaque) lift constant `w`.

## Deliverables (the OPEN list; filled in committed increments)

1. `linKey` + coefficient facts — DONE below.
2. frame legs: `linKey_irr` (Eisenstein), heights/`suppVal`/purity/`sideSet`/pin, `resirr`.
3. `linFrame : KeyFrame O π`, `linFrame_pin : (linFrame hπ).Pin 1`.
4. stage-field `Field` instance; `linTower : TowerDatum (linFrame hπ) 1 _`.
5. `composedKey_linTower : ∃ w : O, composedKey (linTower hπ) = (X + C π)^2 − C w`.
6. the slot-1 digit: `(dev Φ′ (dev Φ₂ (monicPoly a) 0) 1).coeff 0 = a 1 − 2π`.
7. `budgetFloor (linTower hπ) 1 0 0 1 = 2` (numeral).
8. `triangularDigitRead_false_at : ¬ TriangularDigitRead (linTower hπ) 1 2` given `IsUnit 2`.
9. absolute closure over `ℤ_[3]`:
   `triangularDigitRead_false : ¬ ∀ …(guards `Irreducible π`, `0 < μ₂`, `1 ≤ F.h`)…,
   TriangularDigitRead T μ₂ N`, its unguarded corollary, the exact-binder companion at
   GOAL 3's printed shape (faithfulness machine-checked, per the C35b pattern), and the
   conjunction corollary `¬ (TowerBudgetIff T μ₂ ∧ TriangularDigitRead T μ₂ N)` (the two-leg
   discharge route of `budgetBoxRead_of_legs`, closed).

## Status

In progress; every committed state compiles green with zero `sorry` and Lean-core axioms only.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C53c

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## 1. The linear key `Φ′ = X + π` -/

/-- the refuting frame's stage key: `Φ′ = X + π`, monic of degree `1 = e₁f₁`. -/
noncomputable def linKey (π : O) : Polynomial O := Polynomial.X + Polynomial.C π

theorem linKey_monic : (linKey π).Monic := monic_X_add_C π

theorem linKey_natDegree : (linKey π).natDegree = 1 := natDegree_X_add_C π

theorem linKey_coeff0 : (linKey π).coeff 0 = π := by simp [linKey]

theorem linKey_coeff1 : (linKey π).coeff 1 = 1 := by simp [linKey, coeff_C]

/-! ## 2. The frame legs — the `X`-adic polygon of `Φ′ = X + π`

Mirrors `C97.lean`'s `s2Key_*` battery at `(u, ℓ) = (h, e₁) = (1, 1)`: the two heights are
`addVal π = 1` and `addVal 1 = 0`, the cleared support value is `1`, both endpoints attain it,
the side is `{0, 1}`, and the pin is `H₀ = 1`. -/

/-- height `1` at abscissa `0` — where `Irreducible π` enters as `addVal O π = 1`. -/
theorem linKey_h0 (hπ : Irreducible π) : npHgt X (linKey π) 0 = (1 : ℕ∞) := by
  rw [npHgt_X, linKey_coeff0, addVal_uniformizer hπ]

/-- height `0` at abscissa `1`: `Φ′` is monic. -/
theorem linKey_h1 : npHgt X (linKey π) 1 = (0 : ℕ∞) := by
  rw [npHgt_X, linKey_coeff1]
  exact (IsDiscreteValuationRing.addVal O).map_one

/-- the cleared support value at the slope `h/e₁ = 1/1` is `1`: the two cleared terms are
`1·1 + 0 = 1` and `1·0 + 1 = 1`. -/
theorem linKey_supp (hπ : Irreducible π) : suppVal X (linKey π) 1 1 = (1 : ℕ∞) := by
  rw [suppVal, linKey_natDegree, show Finset.range 2 = {0, 1} from rfl]
  simp [linKey_h0 hπ, linKey_h1]

/-- **`Φ′` is `(1,1)`-pure**: both endpoints of the abscissa range `0 … 1` attain the support
value — the polygon is the single side of slope `−1`. -/
theorem linKey_pure (hπ : Irreducible π) : IsPure X (linKey π) 1 1 := by
  have hdd : (linKey π).natDegree / (X : Polynomial O).natDegree = 1 := by
    simp [linKey_natDegree]
  refine ⟨?_, ?_⟩
  · rw [OnSide, linKey_h0 hπ, linKey_supp hπ]; simp
  · rw [hdd, OnSide, linKey_h1, linKey_supp hπ]; simp

theorem linKey_ne : (sideSet X (linKey π) 1 1).Nonempty :=
  sideSet_nonempty (μ := 1) monic_X (by simp) linKey_monic (by simp [linKey_natDegree]) 1 1

theorem linKey_zero_mem (hπ : Irreducible π) : 0 ∈ sideSet X (linKey π) 1 1 := by
  classical
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by simp [linKey_natDegree]), ?_⟩
  exact (linKey_pure hπ).1

theorem linKey_one_mem (hπ : Irreducible π) : 1 ∈ sideSet X (linKey π) 1 1 := by
  classical
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by simp [linKey_natDegree]), ?_⟩
  have := (linKey_pure hπ).2
  rwa [show (linKey π).natDegree / (X : Polynomial O).natDegree = 1 from by
    simp [linKey_natDegree]] at this

theorem linKey_sideMin (hπ : Irreducible π) :
    sideMin X (linKey π) 1 1 linKey_ne = 0 :=
  Nat.le_zero.mp (Finset.min'_le _ 0 (linKey_zero_mem hπ))

theorem linKey_sideMax (hπ : Irreducible π) :
    sideMax X (linKey π) 1 1 linKey_ne = 1 := by
  classical
  refine le_antisymm ?_ (Finset.le_max' _ 1 (linKey_one_mem hπ))
  have hmem : sideMax X (linKey π) 1 1 linKey_ne ∈ sideSet X (linKey π) 1 1 :=
    Finset.max'_mem _ _
  have h := Finset.mem_range.mp (Finset.mem_filter.mp hmem).1
  rw [linKey_natDegree] at h
  omega

/-- the side has residual degree `d = (1 − 0)/1 = 1`, which is the frame's `f₁`. -/
theorem linKey_sideDeg (hπ : Irreducible π) :
    sideDeg X (linKey π) 1 1 linKey_ne = 1 := by
  rw [sideDeg, linKey_sideMax hπ, linKey_sideMin hπ]

/-- **the pin numeral**: the polygon height at the side's left endpoint is `1`, so the GC-1 pin
of this frame is `H₀ = 1`. -/
theorem linKey_pinHgt (hπ : Irreducible π) :
    npHgt X (linKey π) (sideMin X (linKey π) 1 1 linKey_ne) = (1 : ℕ∞) := by
  rw [linKey_sideMin hπ, linKey_h0 hπ]

/-- **`Φ′ = X + π` is irreducible — EISENSTEIN at the maximal ideal** (`C97.lean`'s
`s2Key_irr` argument at the linear key): `𝔪 = (π)`, the constant coefficient `π` lies in `𝔪`
but not in `𝔪² = (π²)` — otherwise `π = π²c`, whence `π·(1 − πc) = 0`, whence (`O` a domain,
`π ≠ 0`) `1 = πc` and `π` is a unit — and the leading coefficient `1` does not lie in `𝔪`. -/
theorem linKey_irr (hπ : Irreducible π) : Irreducible (linKey π) := by
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {π} := hπ.maximalIdeal_eq
  have hE : (linKey π).IsEisensteinAt (IsLocalRing.maximalIdeal O) := by
    constructor
    · rw [(linKey_monic (π := π)).leadingCoeff]
      exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal O).ne_top
    · intro n hn
      rw [linKey_natDegree] at hn
      interval_cases n
      rw [linKey_coeff0, hmax, Ideal.mem_span_singleton]
    · rw [linKey_coeff0, hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      rintro ⟨c, hc⟩
      have h0 : π * (1 - π * c) = 0 := by linear_combination hc
      rcases mul_eq_zero.mp h0 with h | h
      · exact hπ.ne_zero h
      · exact hπ.not_isUnit ⟨⟨π, c, by linear_combination -h, by linear_combination -h⟩, rfl⟩
  exact hE.irreducible inferInstance (linKey_monic).isPrimitive
    (by rw [linKey_natDegree]; norm_num)

/-- the D9 private-helper pattern (C.04/C.12/C.19/C.22/C.44/C.97): the order-0 key `X` is a key,
so `resField X` is a field. -/
private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by rw [Polynomial.map_X]; exact Polynomial.irreducible_X

/-- **the frame's residual read is irreducible of degree `1`** — B.30's `natDegree_resPoly`
supplies `natDegree = sideDeg = 1` together with `coeff 0 ≠ 0`; a degree-one polynomial over the
field `resField X` is irreducible (mirrors `C97.lean`'s `s2Key_resirr`). -/
theorem linKey_resirr (hπ : Irreducible π) (H₀ : ℕ)
    (hH : npHgt X (linKey π) (sideMin X (linKey π) 1 1 linKey_ne) = (H₀ : ℕ∞)) :
    Irreducible (resPoly π X (linKey π) 1 1 linKey_ne H₀) ∧
      (resPoly π X (linKey π) 1 1 linKey_ne H₀).natDegree = 1 := by
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  have htop : suppVal X (linKey π) 1 1 ≠ ⊤ := by
    rw [linKey_supp hπ]; exact ENat.coe_ne_top 1
  obtain ⟨hdeg, hc0⟩ :=
    natDegree_resPoly hπ isKey_X Nat.one_pos (Nat.coprime_one_left 1) htop linKey_ne hH
  rw [linKey_sideDeg hπ] at hdeg
  have hne0 : resPoly π X (linKey π) 1 1 linKey_ne H₀ ≠ 0 := fun hz => hc0 (by rw [hz]; simp)
  exact ⟨irreducible_of_degree_eq_one ((degree_eq_iff_natDegree_eq hne0).mpr hdeg), hdeg⟩

/-! ## 3. The frame -/

/-- **The refuting frame** `(e₁, f₁, h; Φ′) = (1, 1, 1; X + π)`, over any DVR with a chosen
uniformizer `π`.  Supply, not a signed object: its purpose is to instantiate refutations (this
file) with the obstructing digit kept clear of the lift constants (see the module docstring's
"why not `s2Frame`" note). -/
noncomputable def linFrame (hπ : Irreducible π) : KeyFrame O π where
  e₁ := 1
  f₁ := 1
  h := 1
  key := linKey π
  he₁ := Nat.one_pos
  hf₁ := Nat.one_pos
  hcop := Nat.coprime_one_left 1
  hmonic := linKey_monic
  hdeg := by rw [linKey_natDegree]
  hirr := linKey_irr hπ
  hpure := linKey_pure hπ
  hne := linKey_ne
  hresirr := fun H₀ hH => linKey_resirr hπ H₀ hH

/-- the frame's four numerals, by `rfl`. -/
theorem linFrame_data (hπ : Irreducible π) :
    (linFrame hπ).e₁ = 1 ∧ (linFrame hπ).f₁ = 1 ∧ (linFrame hπ).h = 1 ∧
      (linFrame hπ).key = Polynomial.X + Polynomial.C π :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **the pin exists**: `linFrame` is pinned at `H₀ = 1`. -/
theorem linFrame_pin (hπ : Irreducible π) : (linFrame hπ).Pin 1 :=
  linKey_pinHgt hπ

/-! ## 4. The tower datum — **the corpus's first `TowerDatum` VALUE**

Until this declaration the corpus landed NO `TowerDatum` value at all (PROJECT_STATE append
#103 (5): the inhabitation gap flagged as the live vacuity risk for C.72/C.73's
∀-over-`TowerDatum` statements).  `linTower` inhabits that binder: `(e₂, f₂, u₂) = (2, 1, 3)`,
`ψ₂ = T + 1` over the stage field, fences `2 ≤ 2·1`, `Coprime 3 2`, `2·(1·1)·1 = 2 < 3`. -/

/-- the `Field` structure on the frame's stage field, from `hresirr` (the C.97
`s2StageFieldInst` pattern; reducible so the `CommRing` it induces is the ambient
`AdjoinRoot` one). -/
@[reducible] noncomputable def linStageFieldInst (hπ : Irreducible π)
    (H₀ : ℕ) (hpin : (linFrame hπ).Pin H₀) : Field ((linFrame hπ).stageField H₀ hpin) :=
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  haveI : Fact (Irreducible ((linFrame hπ).frameRes H₀ hpin)) :=
    ⟨((linFrame hπ).hresirr H₀ hpin).1⟩
  AdjoinRoot.instField

/-- **the refuting tower datum** `(e₂, f₂, u₂) = (2, 1, 3)`, `ψ₂ = T + 1` (written `T − (−1)`
so that mathlib's `irreducible_X_sub_C` applies verbatim; the two are equal by `sub_neg_eq_add`,
see `linTower_psi`). -/
noncomputable def linTower (hπ : Irreducible π) :
    TowerDatum (linFrame hπ) 1 (linFrame_pin hπ) :=
  letI : Field ((linFrame hπ).stageField 1 (linFrame_pin hπ)) :=
    linStageFieldInst hπ 1 (linFrame_pin hπ)
  { e₂ := 2
    f₂ := 1
    u₂ := 3
    ψ₂ := Polynomial.X - Polynomial.C (-1)
    he₂ := by norm_num
    hf₂ := Nat.one_pos
    hcomp := by norm_num
    hcop := by decide
    hfloor := by show 2 * (1 * 1) * 1 < 3; norm_num
    hψmonic := monic_X_sub_C (-1)
    hψirr := irreducible_X_sub_C (-1)
    hψdeg := natDegree_X_sub_C (-1)
    hψ0 := by
      simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, neg_neg]
      exact one_ne_zero }

/-- the tower's three numerals and the two derived constants `D₂ = 2`, `E₂ = 6`, by `rfl`. -/
theorem linTower_data (hπ : Irreducible π) :
    (linTower hπ).e₂ = 2 ∧ (linTower hπ).f₂ = 1 ∧ (linTower hπ).u₂ = 3 ∧
      (linTower hπ).D₂ = 2 ∧ (linTower hπ).E₂ = 6 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `ψ₂` is `T + 1` on the nose. -/
theorem linTower_psi (hπ : Irreducible π) :
    (linTower hπ).ψ₂ = Polynomial.X + Polynomial.C 1 := by
  show Polynomial.X - Polynomial.C (-1) = _
  rw [map_neg, sub_neg_eq_add]

end Uniformity.Density.Tower.C53c

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C53c.linKey
#print axioms Uniformity.Density.Tower.C53c.linKey_irr
#print axioms Uniformity.Density.Tower.C53c.linFrame
#print axioms Uniformity.Density.Tower.C53c.linFrame_pin

end AxCheck
