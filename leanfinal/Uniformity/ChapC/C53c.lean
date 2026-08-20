/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C53
import Uniformity.ChapC.C53b
import Uniformity.ChapC.C128
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

## Deliverables — ALL LANDED (2026-08-20, committed increments A–F)

1. `linKey` + coefficient facts (§1).
2. frame legs: `linKey_irr` (Eisenstein), heights/`suppVal`/purity/`sideSet`/pin, `resirr` (§2).
3. `linFrame : KeyFrame O π`, `linFrame_pin : (linFrame hπ).Pin 1` (§3).
4. stage-field `Field` instance; `linTower : TowerDatum (linFrame hπ) 1 _` (§4) —
   **the corpus's FIRST `TowerDatum` value** (append #103 (5)'s inhabitation gap, closed).
5. `linTower_composedKey : ∃ w : O, composedKey (linTower hπ) = (X + C π)² − C w`, and
   `linPhi2_coeff1 : Φ₂.coeff 1 = 2π` EXACTLY (§5).
6. the obstructing digit `linDigit : (dev Φ′ (dev Φ₂ (monicPoly a) 0) 1).coeff 0 = a 1 − 2π`
   (§6), the two `dev` steps being `div_modByMonic_unique` instances.
7. the floor numeral `budgetFloor (linTower hπ) 1 0 0 1 = 2` (inline `by decide`, §8).
8. ★ `triangularDigitRead_false_at : ¬ TriangularDigitRead (linTower hπ) 1 N` for EVERY
   `N ≥ 2`, given `IsUnit (2 : O)` (§8); `legs_incompatible` (the two-leg discharge route of
   `budgetBoxRead_of_legs`, closed); `budgetBoxRead_false_of_leg1` (the VACUITY finding at the
   record's exact conditionality: GIVEN C.52's signed leg 1, `BudgetBoxRead` is false, so
   `towerLocus_fibration_of_frontier` is a true theorem with a false hypothesis).
9. absolute closure over `ℤ_[3]` (§9): `h3_padic`, `unit2_padic3`, and
   ★ `triangularDigitRead_statement_false : ¬ TriangularDigitReadStatement` — the ∀-closed
   GOAL-3 binder family WITH all guards (`Irreducible π`, `0 < μ₂`, `1 ≤ F.h`, `2 ≤ N`),
   refuted outright (C35b faithfulness pattern).

## Status

COMPLETE.  Zero `sorry`; axiom footprint Lean-core only (AxCheck footer).  The
`C53_LEG2_REFUTED_2026-08-20.md` record's status line "argued FALSE in prose, NOT
machine-checked" is superseded by this file: the refutation IS machine-checked, by the
record's own numeric instance, with no dependence on C.50's transcribed `gridWeight` scope
note (corpus prose) — only landed theorems.
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

/-! ## 5. The composed key, explicitly

`f₂ = 1` and `f₁ = 1` collapse C.43's display to a single constant correction:
`Φ₂ = Φ′² − C w` with `w = resLift(…) · π³` — one `stageLiftIA` summand (`slotIdx 3 = 0`), no
appeal to C.47's `cLift` bounds and no appeal to C.50's transcribed `gridWeight` scope note.
Everything the refutation needs is then `Φ₂.coeff 1 = 2π` exactly. -/

theorem linFrame_slotIdx3 (hπ : Irreducible π) : (linFrame hπ).slotIdx 3 = 0 := by
  change ((List.range 1).find? (fun i => (i * 1) % 1 == 3 % 1)).getD 0 = 0
  rfl

/-- **the composed key of the refuting tower is `Φ′² − C w`** for a single (opaque) lift
constant `w`; the correction is `π³`-divisible, though only its constancy is consumed below. -/
theorem linTower_composedKey (hπ : Irreducible π) :
    ∃ w : O, composedKey (linTower hπ)
      = (Polynomial.X + Polynomial.C π) ^ 2 - Polynomial.C w := by
  refine ⟨resLift ((linFrame hπ).stageCoord 1 (linFrame_pin hπ)
      (- (linTower hπ).ψ₂.coeff 0
        * (linFrame hπ).stageLetter 1 (linFrame_pin hπ) ^ wrapExp (linTower hπ) 0) 0)
      * π ^ 3, ?_⟩
  rw [composedKey]
  simp only [show (linTower hπ).f₂ = 1 from rfl, Finset.sum_range_one, Nat.sub_zero,
    mul_zero, pow_zero, mul_one]
  rw [stageLiftO_of_f1 _ _ _ rfl]
  simp only [show (linTower hπ).u₂ = 3 from rfl, one_mul, linFrame_slotIdx3 hπ,
    show (linFrame hπ).h = 1 from rfl, show (linFrame hπ).e₁ = 1 from rfl, zero_mul,
    Nat.sub_zero, Nat.div_one, pow_zero, mul_one]
  rfl

/-- `Φ₂.coeff 1 = 2π` **exactly** — the obstructing digit's seed. -/
theorem linPhi2_coeff1 (hπ : Irreducible π) :
    (composedKey (linTower hπ)).coeff 1 = 2 * π := by
  obtain ⟨w, hw⟩ := linTower_composedKey hπ
  have hsq : ((Polynomial.X : Polynomial O) + Polynomial.C π) ^ 2
      = Polynomial.X ^ 2 + Polynomial.C (2 * π) * Polynomial.X + Polynomial.C (π ^ 2) := by
    have h2 : (Polynomial.C (2 * π) : Polynomial O) = 2 * Polynomial.C π := by
      rw [map_mul, map_ofNat]
    rw [h2, map_pow]; ring
  rw [hw, hsq]
  simp [coeff_X_pow, coeff_C, ← map_pow]

theorem linPhi2_monic (hπ : Irreducible π) : (composedKey (linTower hπ)).Monic :=
  composedKey_monic (linTower hπ)

theorem linPhi2_natDegree (hπ : Irreducible π) :
    (composedKey (linTower hπ)).natDegree = 2 :=
  composedKey_natDegree_D₂ (linTower hπ) hπ

/-! ## 6. The obstructing digit

For `f = monicPoly a = X² + a₁X + a₀` the two-key digit at slot `(j, a′, b) = (0, 0, 1)` is the
CONSTANT `a₁ − 2π`: the level-2 digit is `f %ₘ Φ₂ = f − Φ₂` (equal degrees, equal leading
coefficients), and the level-1 digit `1` of the resulting linear polynomial is its leading
coefficient.  Both `dev` steps are `div_modByMonic_unique` instances. -/

private theorem monicPoly_two (a : Fin 2 → O) :
    monicPoly a = Polynomial.X ^ 2 + Polynomial.C (a 1) * Polynomial.X + Polynomial.C (a 0) := by
  rw [monicPoly, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  ring

/-- the level-2 digit `0` of `monicPoly a`: subtraction of the composed key. -/
private theorem dev_quad (w : O) (a : Fin 2 → O) :
    dev ((Polynomial.X + Polynomial.C π) ^ 2 - Polynomial.C w) (monicPoly a) 0
      = Polynomial.C (a 1 - 2 * π) * Polynomial.X + Polynomial.C (a 0 - (π ^ 2 - w)) := by
  have hdegq : ((Polynomial.X + Polynomial.C π) ^ 2 - Polynomial.C w).degree = 2 := by
    rw [Polynomial.degree_sub_eq_left_of_degree_lt, Polynomial.degree_pow,
      Polynomial.degree_X_add_C]
    · rfl
    · rw [Polynomial.degree_pow, Polynomial.degree_X_add_C]
      exact lt_of_le_of_lt Polynomial.degree_C_le (by decide)
  have hq : ((Polynomial.X + Polynomial.C π) ^ 2 - Polynomial.C w).Monic := by
    rw [sub_eq_add_neg]
    refine ((monic_X_add_C π).pow 2).add_of_left ?_
    rw [Polynomial.degree_neg, Polynomial.degree_pow, Polynomial.degree_X_add_C]
    exact lt_of_le_of_lt Polynomial.degree_C_le (by decide)
  show monicPoly a %ₘ _ = _
  refine (Polynomial.div_modByMonic_unique 1 _ hq ⟨?_, ?_⟩).2
  · rw [monicPoly_two]
    simp only [map_sub, map_mul, map_pow, map_ofNat]
    ring
  · rw [hdegq]
    refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) (by decide)
    · exact lt_of_le_of_lt Polynomial.degree_C_le (by decide)

/-- the level-1 digit `1` of a linear polynomial: its leading coefficient. -/
private theorem dev_lin_one (c₁ c₀ : O) :
    dev (Polynomial.X + Polynomial.C π)
      (Polynomial.C c₁ * Polynomial.X + Polynomial.C c₀) 1 = Polynomial.C c₁ := by
  have hmon : (Polynomial.X + Polynomial.C π).Monic := monic_X_add_C π
  have hdiv : (Polynomial.C c₁ * Polynomial.X + Polynomial.C c₀) /ₘ
        (Polynomial.X + Polynomial.C π) = Polynomial.C c₁ := by
    refine (Polynomial.div_modByMonic_unique (Polynomial.C c₁)
      (Polynomial.C (c₀ - c₁ * π)) hmon ⟨?_, ?_⟩).1
    · simp only [map_sub, map_mul]
      ring
    · rw [Polynomial.degree_X_add_C]
      exact lt_of_le_of_lt Polynomial.degree_C_le (by decide)
  show (Polynomial.C c₁ * Polynomial.X + Polynomial.C c₀) /ₘ
      (Polynomial.X + Polynomial.C π) %ₘ (Polynomial.X + Polynomial.C π) = _
  rw [hdiv]
  refine (Polynomial.modByMonic_eq_self_iff hmon).mpr ?_
  rw [Polynomial.degree_X_add_C]
  exact lt_of_le_of_lt Polynomial.degree_C_le (by decide)

/-- **the obstructing digit**: the slot-`(0,0,1)` two-key digit of `monicPoly a` is the constant
`a₁ − 2π`. -/
theorem linDigit (hπ : Irreducible π) (a : Fin 2 → O) :
    (dev (linFrame hπ).key
      (dev (composedKey (linTower hπ)) (monicPoly a) 0) 1).coeff 0 = a 1 - 2 * π := by
  obtain ⟨w, hw⟩ := linTower_composedKey hπ
  have hkey : (linFrame hπ).key = Polynomial.X + Polynomial.C π := rfl
  rw [hkey, hw, dev_quad w a, dev_lin_one, Polynomial.coeff_C_zero]

/-! ## 7. Valuation bookkeeping

**Disclosure:** the two `private` lemmas are verbatim reproductions of `C53.lean`'s `private`
cluster (`le_addVal_iff_pow_dvd'`, `mem_pow_maximalIdeal_iff'`) — private there, hence not
importable; the same RE-PLAN candidate (promote to `Density/LocalData.lean`) applies. -/

private theorem le_addVal_iff_pow_dvd (hπ : Irreducible π) (m : ℕ) (x : O) :
    ((m : ℕ) : ℕ∞) ≤ addVal O x ↔ π ^ m ∣ x := by
  rw [← hπ.addVal_pow m]
  exact addVal_le_iff_dvd

private theorem mem_pow_maximalIdeal_iff (hπ : Irreducible π) (m : ℕ) (x : O) :
    x ∈ (IsLocalRing.maximalIdeal O) ^ m ↔ π ^ m ∣ x := by
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

/-! ## 8. THE REFUTATION — `TriangularDigitRead` is FALSE at the instance

At `c = 0` and any window `N ≥ 2`: RAW-BOX contains the zero class (witness `a = 0`,
`addVal 0 = ⊤`), so the iff hands over a lift `a` of `0` clearing the DIGIT floors; at slot
`(0, 0, 1)` that demands `2 ≤ addVal (a₁ − 2π)` (the floor is `2`, the digit is `a₁ − 2π` by
`linDigit`), i.e. `π² ∣ a₁ − 2π`; but `π² ∣ a₁` (a lift of `0` at level `N ≥ 2`), so
`π² ∣ 2π`, and `2` a unit forces `π² ∣ π` — `2 ≤ addVal π = 1`.  Contradiction. -/

theorem triangularDigitRead_false_at [Finite (IsLocalRing.ResidueField O)]
    (hπ : Irreducible π) (h2 : IsUnit (2 : O)) {N : ℕ} (hN : 2 ≤ N) :
    ¬ TriangularDigitRead (linTower hπ) 1 N := by
  intro h
  -- RAW-BOX ∋ 0, so the iff produces a DIGIT-BOX witness over the zero class
  obtain ⟨a, ha, hfl⟩ := (h 0).mpr
    ⟨0, by funext i; simp [proj], fun i => by
      rw [Pi.zero_apply, (addVal O).map_zero]; exact le_top⟩
  -- the slot-(0,0,1) digit floor, retyped by defeq to the `Fin 2` index (`1 * D₂ ≡ 2`,
  -- `budgetFloor (linTower hπ) 1 0 0 1 ≡ 2`), then read through `linDigit`
  have hbf : budgetFloor (linTower hπ) 1 0 0 1 = 2 := by
    simp only [budgetFloor, slotOffset, TowerDatum.E₂,
      show (linTower hπ).e₂ = 2 from rfl, show (linTower hπ).f₂ = 1 from rfl,
      show (linTower hπ).u₂ = 3 from rfl, show (linFrame hπ).h = 1 from rfl,
      show (linFrame hπ).e₁ = 1 from rfl]
    decide
  have hkey0 := hfl 0 0 1 Nat.one_pos (show (0 : ℕ) < 1 * 1 by norm_num)
    (show (1 : ℕ) < 2 * 1 by norm_num)
  rw [hbf] at hkey0
  have hkey : ((2 : ℕ) : ℕ∞) ≤ addVal O
      ((dev (linFrame hπ).key
        (dev (composedKey (linTower hπ)) (monicPoly (n := 2) a) 0) 1).coeff 0) := hkey0
  rw [linDigit hπ a] at hkey
  have hdvd := (le_addVal_iff_pow_dvd hπ 2 _).1 hkey
  -- a lift of the zero class has `π² ∣ a₁`
  have ha1 : π ^ 2 ∣ a (1 : Fin 2) := by
    have h0 : Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ N) (a (1 : Fin 2)) = 0 :=
      congrFun ha (1 : Fin 2)
    have hmem : a (1 : Fin 2) ∈ (IsLocalRing.maximalIdeal O) ^ N :=
      Ideal.Quotient.eq_zero_iff_mem.mp h0
    exact dvd_trans (pow_dvd_pow π hN) ((mem_pow_maximalIdeal_iff hπ N _).mp hmem)
  -- hence `π² ∣ 2π`, and `2` a unit makes that `π² ∣ π`
  have h2π : π ^ 2 ∣ 2 * π := by
    have := dvd_sub ha1 hdvd
    rwa [sub_sub_cancel] at this
  have hππ : π ^ 2 ∣ π := (mul_comm (2 : O) π ▸ h2.dvd_mul_right.mp) h2π
  -- `2 ≤ addVal π = 1`
  have habs : ((2 : ℕ) : ℕ∞) ≤ addVal O π := (le_addVal_iff_pow_dvd hπ 2 π).2 hππ
  rw [addVal_uniformizer hπ, show ((1 : ℕ∞)) = ((1 : ℕ) : ℕ∞) from rfl, Nat.cast_le] at habs
  omega

/-- **the two-leg discharge route of `budgetBoxRead_of_legs` is CLOSED** at the instance:
no pair of Props with these two names can both hold. -/
theorem legs_incompatible [Finite (IsLocalRing.ResidueField O)]
    (hπ : Irreducible π) (h2 : IsUnit (2 : O)) {N : ℕ} (hN : 2 ≤ N) :
    ¬ (TowerBudgetIff (linTower hπ) 1 ∧ TriangularDigitRead (linTower hπ) 1 N) :=
  fun ⟨_, hl2⟩ => triangularDigitRead_false_at hπ h2 hN hl2

/-- **the vacuity finding, machine-checked at exactly the record's conditionality**: GIVEN
C.52's signed leg 1 (`TowerBudgetIff`, still OPEN), the frontier Prop `BudgetBoxRead` — the
hypothesis of `C53.lean`'s `towerLocus_fibration_of_frontier` — is FALSE at the instance.
So the moment leg 1 lands, `towerLocus_fibration_of_frontier` is certified a true theorem
with a false hypothesis, and the live route is `towerLocus_fibration_of_leg1` (C53b). -/
theorem budgetBoxRead_false_of_leg1 [Finite (IsLocalRing.ResidueField O)]
    (hπ : Irreducible π) (h2 : IsUnit (2 : O)) {N : ℕ} (hN : 2 ≤ N)
    (hleg1 : TowerBudgetIff (linTower hπ) 1) : ¬ BudgetBoxRead (linTower hπ) 1 N := by
  intro hbbr
  refine triangularDigitRead_false_at hπ h2 hN ?_
  intro c
  refine Iff.trans ?_ (hbbr c)
  constructor
  · rintro ⟨a, ha, hdig⟩
    exact ⟨a, ha,
      (hleg1 (monicPoly a) (monicPoly_monic a) (monicPoly_natDegree a)).2 hdig⟩
  · rintro ⟨a, ha, hmem⟩
    exact ⟨a, ha,
      (hleg1 (monicPoly a) (monicPoly_monic a) (monicPoly_natDegree a)).1 hmem⟩

/-! ## 9. The absolute closure over `ℤ_[3]`, and the ∀-statement refuted

`Irreducible (3 : ℤ_[3])` and `IsUnit (2 : ℤ_[3])` both hold, so nothing above is vacuous, and
the ∀-closed statement — WITH the guards `Irreducible π`, `0 < μ₂`, `1 ≤ F.h`, `2 ≤ N` — is
FALSE outright. -/

theorem h3_padic : Irreducible (3 : ℤ_[3]) := by
  simpa using PadicInt.irreducible_p (p := 3)

theorem unit2_padic3 : IsUnit (2 : ℤ_[3]) := by
  have hcast : (2 : ℤ_[3]) = ((2 : ℤ) : ℤ_[3]) := by norm_cast
  have hnlt : ¬ ‖((2 : ℤ) : ℤ_[3])‖ < 1 := by
    rw [PadicInt.norm_int_lt_one_iff_dvd]
    norm_num
  rw [hcast, PadicInt.isUnit_iff]
  exact le_antisymm (PadicInt.norm_le_one _) (not_lt.mp hnlt)

/-- **GOAL 3's binder family, closed over everything** — with all four guards (`Irreducible π`,
`0 < μ₂`, `1 ≤ F.h`, and a window guard `2 ≤ N`) INCLUDED, so that the refutation below
defeats even the guarded reading, per the C35b faithfulness pattern. -/
def TriangularDigitReadStatement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] (π : O) (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : F.Pin H₀) (T : TowerDatum F H₀ hpin) (μ₂ N : ℕ),
    Irreducible π → 0 < μ₂ → 1 ≤ F.h → 2 ≤ N → TriangularDigitRead T μ₂ N

/-- **C.53 leg 2 is FALSE** — the prose refutation of `C53_LEG2_REFUTED_2026-08-20.md`,
machine-checked at its own explicit numeric instance, realized absolutely over `ℤ_[3]`. -/
theorem triangularDigitRead_statement_false : ¬ TriangularDigitReadStatement := fun hax =>
  triangularDigitRead_false_at h3_padic unit2_padic3 le_rfl
    (hax ℤ_[3] (3 : ℤ_[3]) (linFrame h3_padic) 1 (linFrame_pin h3_padic)
      (linTower h3_padic) 1 2 h3_padic Nat.one_pos le_rfl le_rfl)

end Uniformity.Density.Tower.C53c

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C53c.linKey
#print axioms Uniformity.Density.Tower.C53c.linKey_irr
#print axioms Uniformity.Density.Tower.C53c.linFrame
#print axioms Uniformity.Density.Tower.C53c.linFrame_pin
#print axioms Uniformity.Density.Tower.C53c.linTower
#print axioms Uniformity.Density.Tower.C53c.linTower_composedKey
#print axioms Uniformity.Density.Tower.C53c.linPhi2_coeff1
#print axioms Uniformity.Density.Tower.C53c.linDigit
#print axioms Uniformity.Density.Tower.C53c.triangularDigitRead_false_at
#print axioms Uniformity.Density.Tower.C53c.legs_incompatible
#print axioms Uniformity.Density.Tower.C53c.budgetBoxRead_false_of_leg1
#print axioms Uniformity.Density.Tower.C53c.triangularDigitRead_statement_false

end AxCheck
