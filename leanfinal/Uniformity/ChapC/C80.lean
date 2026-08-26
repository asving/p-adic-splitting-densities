/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C04
import Uniformity.ChapC.C43
import Uniformity.ChapC.C67
import Uniformity.ChapC.C44
import Uniformity.ChapC.C97

/-!
# Uniformity.ChapC.C80 — the TOWER-BORNE probe: `tie_pure_power` and C.77 (iii) REFUTED

**Chapter C, NODES C.80 (`tie_pure_power`) and C.77 (`partial_projection`, clause (iii)).**
Both signed statements are **FALSE**, machine-checked at a NEW tower-borne probe — the sixth
and seventh members of the EXACT-DEGREE (D-CARRY) family.  Both stay at their leanspec stubs.

## Why a new probe was needed (HX_SWEEP §7's corrected brief, executed)

The three remaining D-CARRY candidates are TOWER-BORNE (`BlockContext (T.levelDatum hπ) f`),
and the two landed probe frames cannot reach them: the `s2` probe's hand-built `L₀` is not a
`TowerDatum.levelDatum` (`hcomp : 2 ≤ e₂f₂` fails at `ℓ = d_r = 1`), and the `linFrame`
route is IMPOSSIBLE (`D′ = 1` has no floor slack — the provenance gap needs
`deg f = D′·m̄ + s`, `0 < s < D′`, invisible to the polygon's floored top abscissa).

**The probe built here**: over the `s2Frame` (`Φ′ = x² − 2`, `D′ = 2`), the depth-2 tower
datum `s2Tower = (e₂, f₂, u₂) = (2, 1, 5)` (exactly `s2Witness`'s rung-2 data, landed as a
standalone `TowerDatum` — also the s2-specific worked witness that append #102 (5) noted was
argued-not-witnessed), and the monic DEGREE-5 polynomial

```
f₅ = (x + 1)·Φ′² + (4x + 8) = x⁵ + x⁴ − 4x³ − 4x² + 8x + 12 .
```

`keyDeg₂ = D₂ = 4 ∤ 5 = deg f₅`; the `Φ′`-digits are `(8 + 4x, 0, x + 1)` with height
profile `(5, ⊤, 0)`; the `(5, 2)`-side is `{0, 2}` at cleared value `10`, so `f₅` is pure
with side degree `1`; and `f₅` is squarefree.  NUMERIC PRE-CERTIFICATION:
`verification/dv_ledger_cert.py`'s session companion run (2026-08-20; digits, heights,
purity, gcd(f, f′) = 1, all exact over ℤ) — the construction was certified before a line of
Lean.

## The residue-field collapse that closes the residual leg

`K₁ = (s2Frame).stageField` has `Nat.card = 2` (C.04's `card_stageField` at `hq`), so EVERY
nonzero element is `1` and every degree-1 polynomial with nonzero endpoints IS `X + 1`.
Hence `dvResPoly f₅ = X + 1 = towerLabel s2Tower` (both are degree-1 with nonzero constant
and leading coefficients — C.26's `natDegree_dvResPoly` on one side, C.44's `towerLabel_spec`
on the other), which supplies BOTH C.80's residual-power hypothesis (`c = 1`, `μ₂ = 1`) and
the `BlockContext` residual leg — no twist arithmetic needed.

## The refutations

`HasLabel (s2Tower.levelDatum hπ) f₅` holds (purity + residual `= r¹`), so `f₅` is its own
block (the C67 maximality trick), and:

* **C.80 `tie_pure_power`**: hypotheses all hold at `μ₂ = 1`; conclusion demands
  `deg (blockFactor) = D₂·μ₂`, i.e. **`5 = 4`** — while its FIRST conjunct
  `mult₂ = μ₂` is TRUE (`⌊5/4⌋ = 1`): the same fail-on-exact-survive-on-floor signature as
  C.67, at a tower-borne datum.
* **C.77 `partial_projection`**: needs only `BlockContext`; its clause (iii) demands
  `deg (blockFactor) = D₂ · mult₂ = 4` — **`5 = 4`**.  (Clauses (i)–(ii) are not
  adjudicated; the ∀-closure of the conjunction is refuted through (iii).)

C.78 (`partial_block_decision`) is NOT adjudicated here — its conclusion shape differs;
it stays a candidate in the HX_SWEEP §7 registry.

## Status

Zero `sorry`; axiom footprint Lean-core only (AxCheck footer).  No cite.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C80

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower Uniformity.Density.Tower.C35b

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## 1. The tower datum `(2, 1, 5)` over `s2Frame` — `s2Witness`'s rung 2, standalone -/

/-- **the s2 tower datum** `(e₂, f₂, u₂) = (2, 1, 5)`, `ψ₂ = T − 1` — the depth-2 slice of
C.97's `s2Witness`, landed as a standalone `TowerDatum` (the s2-specific witness of
append #102 (5)). -/
noncomputable def s2Tower : TowerDatum (s2Frame h2 hq) 1 (s2Frame_pin h2 hq) :=
  letI : Field ((s2Frame h2 hq).stageField 1 (s2Frame_pin h2 hq)) :=
    s2StageFieldInst h2 hq 1 (s2Frame_pin h2 hq)
  { e₂ := 2
    f₂ := 1
    u₂ := 5
    ψ₂ := Polynomial.X - Polynomial.C 1
    he₂ := by norm_num
    hf₂ := Nat.one_pos
    hcomp := by norm_num
    hcop := by decide
    hfloor := by show 2 * ((s2Frame h2 hq).e₁ * (s2Frame h2 hq).f₁) * (s2Frame h2 hq).h < 5
                 rw [e1_eq h2 hq, f1_eq h2 hq, h_eq h2 hq]; norm_num
    hψmonic := monic_X_sub_C 1
    hψirr := irreducible_X_sub_C 1
    hψdeg := natDegree_X_sub_C 1
    hψ0 := by
      simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, ne_eq, neg_eq_zero]
      exact one_ne_zero }

theorem s2Tower_data :
    (s2Tower h2 hq).e₂ = 2 ∧ (s2Tower h2 hq).f₂ = 1 ∧ (s2Tower h2 hq).u₂ = 5 ∧
      (s2Tower h2 hq).D₂ = 4 ∧ (s2Tower h2 hq).E₂ = 10 := by
  refine ⟨rfl, rfl, rfl, ?_, rfl⟩
  show ((s2Frame h2 hq).e₁ * (s2Frame h2 hq).f₁) * (2 * 1) = 4
  rw [e1_eq h2 hq, f1_eq h2 hq]

/-! ## 2. The probe `f₅` and its `Φ′`-development -/

/-- **the probe**: `f₅ = (x+1)Φ′² + (4x + 8)`, monic of degree `5` — floor slack `s = 1`
against `D′ = 2`, so `keyDeg₂ = 4 ∤ 5`. -/
noncomputable def f₅ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    Polynomial O :=
  (Polynomial.X + Polynomial.C 1) * (s2Key O) ^ 2 + (Polynomial.C 4 * Polynomial.X + Polynomial.C 8)

theorem f₅_monic : (f₅ O).Monic := by
  refine Polynomial.Monic.add_of_left ((monic_X_add_C (1 : O)).mul (s2Key_monic.pow 2)) ?_
  have hd : (((Polynomial.X + Polynomial.C 1) : Polynomial O) * (s2Key O) ^ 2).degree = 5 := by
    rw [Polynomial.degree_mul, Polynomial.degree_pow, Polynomial.degree_X_add_C, s2Key_deg]
    rfl
  rw [hd]
  refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
  · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) (by decide)
  · exact lt_of_le_of_lt Polynomial.degree_C_le (by decide)

theorem f₅_natDegree : (f₅ O).natDegree = 5 := by
  have hd : ((f₅ O)).degree = 5 := by
    rw [f₅]
    have hleft : (((Polynomial.X + Polynomial.C 1) : Polynomial O) * (s2Key O) ^ 2).degree = 5 := by
      rw [Polynomial.degree_mul, Polynomial.degree_pow, Polynomial.degree_X_add_C, s2Key_deg]
      rfl
    rw [Polynomial.degree_add_eq_left_of_degree_lt, hleft]
    rw [hleft]
    refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) (by decide)
    · exact lt_of_le_of_lt Polynomial.degree_C_le (by decide)
  rw [Polynomial.natDegree, hd]
  rfl

/-- the three `Φ′`-digits of `f₅`: `(8 + 4x, 0, x + 1)`. -/
theorem dev_f₅_zero : dev (s2Key O) (f₅ O) 0 = Polynomial.C 4 * Polynomial.X + Polynomial.C 8 := by
  show (f₅ O) %ₘ (s2Key O) = _
  refine (Polynomial.div_modByMonic_unique ((Polynomial.X + Polynomial.C 1) * (s2Key O))
    _ s2Key_monic ⟨by rw [f₅]; ring, ?_⟩).2
  rw [s2Key_deg]
  refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
  · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) (by decide)
  · exact lt_of_le_of_lt Polynomial.degree_C_le (by decide)

private theorem f₅_div : (f₅ O) /ₘ (s2Key O) = (Polynomial.X + Polynomial.C 1) * (s2Key O) := by
  refine (Polynomial.div_modByMonic_unique ((Polynomial.X + Polynomial.C 1) * (s2Key O))
    (Polynomial.C 4 * Polynomial.X + Polynomial.C 8) s2Key_monic ⟨by rw [f₅]; ring, ?_⟩).1
  rw [s2Key_deg]
  refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
  · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) (by decide)
  · exact lt_of_le_of_lt Polynomial.degree_C_le (by decide)

theorem dev_f₅_one : dev (s2Key O) (f₅ O) 1 = 0 := by
  show ((f₅ O) /ₘ (s2Key O)) %ₘ (s2Key O) = 0
  rw [f₅_div]
  exact (Polynomial.modByMonic_eq_zero_iff_dvd s2Key_monic).mpr ⟨_, mul_comm _ _⟩

theorem dev_f₅_two : dev (s2Key O) (f₅ O) 2 = Polynomial.X + Polynomial.C 1 := by
  show (((f₅ O) /ₘ (s2Key O)) /ₘ (s2Key O)) %ₘ (s2Key O) = _
  rw [f₅_div]
  have hdiv : (((Polynomial.X + Polynomial.C 1) : Polynomial O) * (s2Key O)) /ₘ (s2Key O)
      = Polynomial.X + Polynomial.C 1 := by
    refine (Polynomial.div_modByMonic_unique (Polynomial.X + Polynomial.C 1) 0 s2Key_monic
      ⟨by ring, ?_⟩).1
    rw [s2Key_deg, Polynomial.degree_zero]
    exact WithBot.bot_lt_coe 2
  rw [hdiv]
  refine (Polynomial.modByMonic_eq_self_iff s2Key_monic).mpr ?_
  rw [s2Key_deg, Polynomial.degree_X_add_C]
  decide

/-! ## 3. The height profile `(5, ⊤, 0)`, the side `{0, 2}`, and purity -/

include h2 hq in
theorem dvhgt_f₅_0 : dvHgt (s2Frame h2 hq) (f₅ O) 0 = (5 : ℕ∞) := by
  rw [dvHgt, key_eq h2 hq, dev_f₅_zero, KeyFrame.stageHeight_eq_inf]
  have h4 : (4 : O) ≠ 0 := by
    rw [show (4 : O) = 2 ^ 2 by norm_num]
    exact pow_ne_zero 2 h2.ne_zero
  have hdeg : ((Polynomial.C (4 : O) * Polynomial.X + Polynomial.C 8)).natDegree = 1 :=
    Polynomial.natDegree_linear h4
  rw [hdeg, show Finset.range (1 + 1) = {0, 1} from rfl]
  simp only [Finset.inf_insert, Finset.inf_singleton, e1_eq h2 hq, h_eq h2 hq,
    Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_zero,
    Polynomial.coeff_X_one, Polynomial.coeff_C, gaussVal_C]
  norm_num
  rw [show (8 : O) = 2 ^ 3 by norm_num, addVal_two_pow h2,
    show (4 : O) = 2 ^ 2 by norm_num, addVal_two_pow h2]
  decide

include h2 hq in
theorem dvhgt_f₅_1 : dvHgt (s2Frame h2 hq) (f₅ O) 1 = ⊤ := by
  rw [dvHgt, key_eq h2 hq, dev_f₅_one]
  exact sh_zero h2 hq

include h2 hq in
theorem dvhgt_f₅_2 : dvHgt (s2Frame h2 hq) (f₅ O) 2 = (0 : ℕ∞) := by
  rw [dvHgt, key_eq h2 hq, dev_f₅_two, KeyFrame.stageHeight_eq_inf]
  have hdeg : ((Polynomial.X + Polynomial.C (1 : O))).natDegree = 1 := natDegree_X_add_C 1
  rw [hdeg, show Finset.range (1 + 1) = {0, 1} from rfl]
  simp only [Finset.inf_insert, Finset.inf_singleton, e1_eq h2 hq, h_eq h2 hq,
    Polynomial.coeff_add, Polynomial.coeff_X_zero, Polynomial.coeff_X_one,
    Polynomial.coeff_C, gaussVal_C]
  norm_num

private theorem dev_f₅_ge_three (j : ℕ) (hj : 3 ≤ j) : dev (s2Key O) (f₅ O) j = 0 := by
  refine dev_eq_zero_of_lt s2Key_monic (by rw [s2Key_natDegree]; norm_num) _ _ ?_
  rw [f₅_natDegree, s2Key_natDegree]
  omega

include h2 hq in
theorem dvhgt_f₅_ge_three (j : ℕ) (hj : 3 ≤ j) :
    dvHgt (s2Frame h2 hq) (f₅ O) j = ⊤ := by
  rw [dvHgt, key_eq h2 hq, dev_f₅_ge_three j hj]
  exact sh_zero h2 hq

include h2 hq in
theorem dvsupp_f₅ : dvSupp (s2Frame h2 hq) (f₅ O) 5 2 = (10 : ℕ∞) := by
  rw [dvSupp, f₅_natDegree, show Finset.range (5 + 1) = {0, 1, 2, 3, 4, 5} from rfl]
  simp only [Finset.inf_insert, Finset.inf_singleton, dvhgt_f₅_0 h2 hq, dvhgt_f₅_1 h2 hq,
    dvhgt_f₅_2 h2 hq, dvhgt_f₅_ge_three h2 hq 3 (by norm_num),
    dvhgt_f₅_ge_three h2 hq 4 (by norm_num), dvhgt_f₅_ge_three h2 hq 5 (by norm_num)]
  decide

include h2 hq in
theorem dvside_f₅_zero_mem : 0 ∈ dvSideSet (s2Frame h2 hq) (f₅ O) 5 2 := by
  classical
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by rw [f₅_natDegree]; norm_num), ?_, ?_⟩
  · rw [dvsupp_f₅ h2 hq, dvhgt_f₅_0 h2 hq]
    decide
  · rw [dvhgt_f₅_0 h2 hq]
    decide

include h2 hq in
theorem dvside_f₅_two_mem : 2 ∈ dvSideSet (s2Frame h2 hq) (f₅ O) 5 2 := by
  classical
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by rw [f₅_natDegree]; norm_num), ?_, ?_⟩
  · rw [dvsupp_f₅ h2 hq, dvhgt_f₅_2 h2 hq]
    decide
  · rw [dvhgt_f₅_2 h2 hq]
    decide

include h2 hq in
/-- **`f₅` is `(5, 2)`-pure**: both endpoints of the floored abscissa range `0 … ⌊5/2⌋ = 2`
are on the side — the tower-borne provenance gap in action (`deg f₅ = 5` is INVISIBLE). -/
theorem pure_f₅ : IsDvPure (s2Frame h2 hq) (f₅ O) 5 2 := by
  constructor
  · exact dvside_f₅_zero_mem h2 hq
  · have hidx : (f₅ O).natDegree / ((s2Frame h2 hq).e₁ * (s2Frame h2 hq).f₁) = 2 := by
      rw [f₅_natDegree, e1_eq h2 hq, f1_eq h2 hq]
    rw [hidx]
    exact dvside_f₅_two_mem h2 hq

/-! ## 4. The side endpoints and the level residual `ρ₅` -/

include h2 hq in
theorem hne_f₅ : (dvSideSet (s2Frame h2 hq) (f₅ O) 5 2).Nonempty :=
  ⟨0, dvside_f₅_zero_mem h2 hq⟩

include h2 hq in
theorem dvsidemin_f₅ : dvSideMin (s2Frame h2 hq) (f₅ O) 5 2 (hne_f₅ h2 hq) = 0 :=
  Nat.le_zero.mp (Finset.min'_le _ 0 (dvside_f₅_zero_mem h2 hq))

include h2 hq in
theorem hp_f₅ : dvHgt (s2Frame h2 hq) (f₅ O)
    (dvSideMin (s2Frame h2 hq) (f₅ O) 5 2 (hne_f₅ h2 hq)) = ((5 : ℕ) : ℕ∞) := by
  rw [dvsidemin_f₅ h2 hq, dvhgt_f₅_0 h2 hq]
  rfl

include h2 hq in
theorem dvsidemax_f₅ : dvSideMax (s2Frame h2 hq) (f₅ O) 5 2 (hne_f₅ h2 hq) = 2 := by
  classical
  refine le_antisymm (Finset.max'_le _ _ _ ?_) (Finset.le_max' _ 2 (dvside_f₅_two_mem h2 hq))
  intro y hy
  have hrange := Finset.mem_range.mp (Finset.mem_filter.mp hy).1
  have hon := (Finset.mem_filter.mp hy).2
  rw [f₅_natDegree] at hrange
  interval_cases y
  · norm_num
  · exact absurd (dvhgt_f₅_1 h2 hq) hon.2
  · norm_num
  · exact absurd (dvhgt_f₅_ge_three h2 hq 3 (by norm_num)) hon.2
  · exact absurd (dvhgt_f₅_ge_three h2 hq 4 (by norm_num)) hon.2
  · exact absurd (dvhgt_f₅_ge_three h2 hq 5 (by norm_num)) hon.2

include h2 hq in
theorem dvsidedeg_f₅ : dvSideDeg (s2Frame h2 hq) (f₅ O) 5 2 (hne_f₅ h2 hq) = 1 := by
  rw [dvSideDeg, dvsidemax_f₅ h2 hq, dvsidemin_f₅ h2 hq]

/-- the level residual of `f₅` at `(5, 2)`, pinned at `M₀ = 5`. -/
noncomputable def ρ₅ : Polynomial ((s2Frame h2 hq).stageField 1 (s2Frame_pin h2 hq)) :=
  dvResPoly (s2Frame h2 hq) 1 (s2Frame_pin h2 hq) (f₅ O) 5 2 (hne_f₅ h2 hq) 5 (hp_f₅ h2 hq)

include h2 hq in
theorem ρ₅_spec : (ρ₅ h2 hq).natDegree = 1 ∧ (ρ₅ h2 hq).coeff 0 ≠ 0 := by
  have h := natDegree_dvResPoly (s2Frame h2 hq) h2 1 (s2Frame_pin h2 hq)
    (by norm_num : 0 < 2) (by decide : Nat.Coprime 5 2) (hne_f₅ h2 hq) (hp_f₅ h2 hq)
  rw [dvsidedeg_f₅ h2 hq] at h
  exact h

/-! ## 5. The residue-field collapse: `|K₁| = 2` identifies the residual with the label -/

private theorem eq_one_of_card_two {K : Type} [Field K] (hcard : Nat.card K = 2)
    {z : K} (hz : z ≠ 0) : z = 1 := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hu : Nat.card Kˣ = 1 := by rw [Nat.card_units, hcard]
  haveI : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp hu).1
  have h1 : hz.isUnit.unit = 1 := Subsingleton.elim _ _
  calc z = ((hz.isUnit.unit : Kˣ) : K) := (hz.isUnit.unit_spec).symm
    _ = 1 := by rw [h1]; rfl

private theorem eq_X_add_one_of_card_two {K : Type} [Field K] (hcard : Nat.card K = 2)
    {p : Polynomial K} (hd : p.natDegree = 1) (h0 : p.coeff 0 ≠ 0) :
    p = Polynomial.X + Polynomial.C 1 := by
  have hne0 : p ≠ 0 := fun hz => by simp [hz] at hd
  have h1 : p.coeff 1 ≠ 0 := by
    have := Polynomial.leadingCoeff_ne_zero.mpr hne0
    rwa [show p.leadingCoeff = p.coeff p.natDegree from rfl, hd] at this
  have hp : p = Polynomial.C (p.coeff 1) * Polynomial.X + Polynomial.C (p.coeff 0) :=
    Polynomial.eq_X_add_C_of_degree_le_one (Polynomial.natDegree_le_iff_degree_le.mp (le_of_eq hd))
  rw [hp, eq_one_of_card_two hcard h1, eq_one_of_card_two hcard h0, map_one, one_mul]

include h2 hq in
theorem card_K₁ : Nat.card ((s2Frame h2 hq).stageField 1 (s2Frame_pin h2 hq)) = 2 := by
  rw [KeyFrame.card_stageField (s2Frame h2 hq) h2 1 (s2Frame_pin h2 hq), hq, f1_eq h2 hq,
    pow_one]

include h2 hq in
/-- ★ **the residual IS the label**: `ρ₅ = towerLabel s2Tower` — both are degree-1 with
nonzero endpoints over the 2-element field `K₁`, hence both are `X + 1`. -/
theorem ρ₅_eq_towerLabel : ρ₅ h2 hq = towerLabel (s2Tower h2 hq) := by
  letI : Field ((s2Frame h2 hq).stageField 1 (s2Frame_pin h2 hq)) :=
    s2StageFieldInst h2 hq 1 (s2Frame_pin h2 hq)
  have hspec := towerLabel_spec (s2Tower h2 hq) h2
  have hdeg : (towerLabel (s2Tower h2 hq)).natDegree = 1 := hspec.2.2.1
  rw [eq_X_add_one_of_card_two (card_K₁ h2 hq) (ρ₅_spec h2 hq).1 (ρ₅_spec h2 hq).2,
    eq_X_add_one_of_card_two (card_K₁ h2 hq) hdeg hspec.2.2.2]

/-! ## 6. `Squarefree f₅` — divisibility descent at degree 5

The `g₀_squarefree` argument (C67), run at the quintic.  A repeated factor may be normalized
MONIC (its leading coefficient squares into `f₅`'s leading `1`); the two live degrees are
handled by coefficient systems: `deg p = 2` forces `2 ∣ b`, `2 ∣ c` and then the identity
`3 = 2·(e − b′c′e²)`; `deg p = 1` splits on `2 ∣ a`, each branch reaching `2 ∣ 3` or
`2 ∣ a ∧ 2 ∤ a`. -/

private theorem f₅_eq : (f₅ O)
    = Polynomial.X ^ 5 + Polynomial.X ^ 4 - Polynomial.C 4 * Polynomial.X ^ 3
      - Polynomial.C 4 * Polynomial.X ^ 2 + Polynomial.C 8 * Polynomial.X
      + Polynomial.C 12 := by
  rw [f₅, s2Key]
  simp only [map_ofNat, map_one]
  ring

private theorem eq_sum_three {p : Polynomial O} (h : p.natDegree ≤ 3) :
    p = Polynomial.C (p.coeff 3) * Polynomial.X ^ 3 + Polynomial.C (p.coeff 2) * Polynomial.X ^ 2
      + Polynomial.C (p.coeff 1) * Polynomial.X + Polynomial.C (p.coeff 0) := by
  ext n
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C]
  match n with
  | 0 => simp
  | 1 => simp
  | 2 => simp
  | 3 => simp
  | (m + 4) =>
    have : p.coeff (m + 4) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp [this]

include h2 in
theorem f₅_squarefree : Squarefree (f₅ O) := by
  have hprime : Prime (2 : O) := UniqueFactorizationMonoid.irreducible_iff_prime.mp h2
  have h2dvd3 : ¬ (2 : O) ∣ 3 := by
    intro h3
    obtain ⟨t, ht⟩ := h3
    exact h2.not_isUnit (isUnit_of_dvd_one ⟨t - 1, by linear_combination ht⟩)
  have h4ne : (4 : O) ≠ 0 := by
    rw [show (4 : O) = 2 ^ 2 by norm_num]
    exact pow_ne_zero 2 h2.ne_zero
  intro p hp
  by_contra hpu
  have hg0 : (f₅ O) ≠ 0 := (f₅_monic (O := O)).ne_zero
  have hpne : p ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hp
    exact hg0 (zero_dvd_iff.mp hp)
  obtain ⟨q, hq⟩ := hp
  have hqne : q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hq
    exact hg0 hq
  have hlead : p.leadingCoeff * (p.leadingCoeff * q.leadingCoeff) = 1 := by
    have h1 := congrArg Polynomial.leadingCoeff hq
    rw [(f₅_monic (O := O)).leadingCoeff, Polynomial.leadingCoeff_mul,
      Polynomial.leadingCoeff_mul] at h1
    linear_combination -h1
  have hAunit : IsUnit p.leadingCoeff := isUnit_of_dvd_one ⟨_, hlead.symm⟩
  have hdeg5 : p.natDegree + p.natDegree + q.natDegree = 5 := by
    have h := congrArg Polynomial.natDegree hq
    rw [f₅_natDegree, Polynomial.natDegree_mul (mul_ne_zero hpne hpne) hqne,
      Polynomial.natDegree_mul hpne hpne] at h
    omega
  -- kill the constant case; then normalize `p` monic
  rcases Nat.lt_or_ge p.natDegree 1 with hd0 | hd1
  · have hdp : p.natDegree = 0 := by omega
    have hc : IsUnit (p.coeff 0) := by
      have h : p.leadingCoeff = p.coeff 0 := by
        rw [show p.leadingCoeff = p.coeff p.natDegree from rfl, hdp]
      rwa [h] at hAunit
    exact hpu ((Polynomial.eq_C_of_natDegree_eq_zero hdp) ▸ Polynomial.isUnit_C.mpr hc)
  obtain ⟨u, hu⟩ := hAunit
  set P : Polynomial O := Polynomial.C (↑u⁻¹ : O) * p with hP
  have hune : (↑u⁻¹ : O) ≠ 0 := Units.ne_zero u⁻¹
  have hPdeg : P.natDegree = p.natDegree := by
    rw [hP, Polynomial.natDegree_C_mul hune]
  have hPmonic : P.Monic := by
    rw [Polynomial.Monic, hP, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, ← hu]
    exact Units.inv_mul u
  have hQ : f₅ O = P * P * (Polynomial.C (↑u : O) * Polynomial.C (↑u : O) * q) := by
    have hcanC : (Polynomial.C (↑u⁻¹ : O)) * Polynomial.C (↑u : O) = 1 := by
      rw [← Polynomial.C_mul, Units.inv_mul, Polynomial.C_1]
    rw [hP, hq]
    calc p * p * q
        = ((Polynomial.C (↑u⁻¹ : O)) * Polynomial.C (↑u : O))
          * (((Polynomial.C (↑u⁻¹ : O)) * Polynomial.C (↑u : O)) * (p * p * q)) := by
          rw [hcanC]; ring
      _ = Polynomial.C ↑u⁻¹ * p * (Polynomial.C ↑u⁻¹ * p)
          * (Polynomial.C ↑u * Polynomial.C ↑u * q) := by ring
  set Q : Polynomial O := Polynomial.C (↑u : O) * Polynomial.C (↑u : O) * q with hQdef
  have hQne : Q ≠ 0 := by
    rw [hQdef]
    exact mul_ne_zero (mul_ne_zero (Polynomial.C_ne_zero.mpr (Units.ne_zero u))
      (Polynomial.C_ne_zero.mpr (Units.ne_zero u))) hqne
  have hQmonic : Q.Monic := by
    have hPP : (P * P).Monic := hPmonic.mul hPmonic
    have h1 := congrArg Polynomial.leadingCoeff hQ
    rw [(f₅_monic (O := O)).leadingCoeff, Polynomial.leadingCoeff_mul, hPP] at h1
    rw [Polynomial.Monic]
    linear_combination -h1
  have hQdeg : P.natDegree + P.natDegree + Q.natDegree = 5 := by
    have h := congrArg Polynomial.natDegree hQ
    have hPne : P ≠ 0 := hPmonic.ne_zero
    rw [f₅_natDegree, Polynomial.natDegree_mul (mul_ne_zero hPne hPne) hQne,
      Polynomial.natDegree_mul hPne hPne] at h
    omega
  -- the two live degrees
  rcases Nat.lt_or_ge p.natDegree 2 with hd1' | hd2
  · -- `deg P = 1`, `deg Q = 3`
    have hdP : P.natDegree = 1 := by omega
    have hdQ : Q.natDegree = 3 := by omega
    have hPform : P = Polynomial.X + Polynomial.C (P.coeff 0) := by
      have h := Polynomial.eq_X_add_C_of_degree_le_one
        (Polynomial.natDegree_le_iff_degree_le.mp (le_of_eq hdP))
      have hc1 : P.coeff 1 = 1 := by
        have hm := hPmonic
        rwa [Polynomial.Monic, show P.leadingCoeff = P.coeff P.natDegree from rfl, hdP] at hm
      rw [hc1, map_one, one_mul] at h
      exact h
    have hc3 : Q.coeff 3 = 1 := by
      have hm := hQmonic
      rwa [Polynomial.Monic, show Q.leadingCoeff = Q.coeff Q.natDegree from rfl, hdQ] at hm
    have hQform : Q = Polynomial.X ^ 3
        + Polynomial.C (Q.coeff 2) * Polynomial.X ^ 2
        + Polynomial.C (Q.coeff 1) * Polynomial.X + Polynomial.C (Q.coeff 0) := by
      have h := eq_sum_three (O := O) (p := Q) (le_of_eq hdQ)
      rw [hc3, map_one, one_mul] at h
      exact h
    set a := P.coeff 0
    set B := Q.coeff 2
    set C' := Q.coeff 1
    set D := Q.coeff 0
    have hcanon : (f₅ O)
        = Polynomial.C (B + 2 * a) * Polynomial.X ^ 4
          + Polynomial.C (C' + 2 * a * B + a ^ 2) * Polynomial.X ^ 3
          + Polynomial.C (D + 2 * a * C' + a ^ 2 * B) * Polynomial.X ^ 2
          + Polynomial.C (2 * a * D + a ^ 2 * C') * Polynomial.X
          + Polynomial.C (a ^ 2 * D) + Polynomial.X ^ 5 := by
      rw [hQ, hPform, hQform]
      simp only [map_add, map_mul, map_pow, map_ofNat, map_one]
      ring
    have hval := fun k => congrArg (fun r : Polynomial O => r.coeff k) (f₅_eq.symm.trans hcanon)
    have s3 : (-4 : O) = C' + 2 * a * B + a ^ 2 := by
      have h := hval 3
      simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] at h
      norm_num at h
      linear_combination h
    have s1 : (8 : O) = 2 * a * D + a ^ 2 * C' := by
      have h := hval 1
      simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] at h
      norm_num at h
      linear_combination h
    have s0 : (12 : O) = a ^ 2 * D := by
      have h := hval 0
      simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] at h
      norm_num at h
      linear_combination h
    by_cases ha : (2 : O) ∣ a
    · -- `2 ∣ a`: `a′²D = 3` and `a′(D + a′C′) = 2` with `2 ∣ C′` force `2 ∣ 3`
      obtain ⟨a', ha'⟩ := ha
      have hC : (2 : O) ∣ C' :=
        ⟨-2 - 2 * a' * B - 2 * a' ^ 2, by linear_combination (-1 : O) * s3
          - (2 * B + a + 2 * a') * ha'⟩
      have hD3 : a' ^ 2 * D = 3 := by
        refine mul_left_cancel₀ h4ne ?_
        linear_combination (-1 : O) * s0 - D * (a + 2 * a') * ha'
      have hsplit : a' * (D + a' * C') = 2 := by
        refine mul_left_cancel₀ h4ne ?_
        linear_combination (-1 : O) * s1 - (2 * D + C' * (a + 2 * a')) * ha'
      have h2a' : ¬ (2 : O) ∣ a' := by
        intro hdvd
        obtain ⟨t, ht⟩ := hdvd
        exact h2dvd3 ⟨2 * t ^ 2 * D, by linear_combination (-1 : O) * hD3
          + (a' + 2 * t) * D * ht⟩
      have h2sum : (2 : O) ∣ D + a' * C' := by
        have hd2 : (2 : O) ∣ a' * (D + a' * C') := ⟨1, by linear_combination hsplit⟩
        rcases hprime.dvd_mul.mp hd2 with h | h
        · exact absurd h h2a'
        · exact h
      have h2D : (2 : O) ∣ D := by
        obtain ⟨t, ht⟩ := h2sum
        obtain ⟨w, hw⟩ := hC
        exact ⟨t - a' * w, by linear_combination ht - a' * hw⟩
      obtain ⟨t, ht⟩ := h2D
      exact h2dvd3 ⟨a' ^ 2 * t, by linear_combination (-1 : O) * hD3 + a' ^ 2 * ht⟩
    · -- `2 ∤ a`: `2 ∣ C′` (from `s1` + `s0`), then `s3` makes `a²` even
      have h2a2 : ¬ (2 : O) ∣ a ^ 2 := by
        intro hdvd
        rcases hprime.dvd_mul.mp (show (2 : O) ∣ a * a by rw [← pow_two]; exact hdvd) with h | h <;>
          exact ha h
      have hC2 : (2 : O) ∣ C' := by
        have h1 : (2 : O) ∣ a ^ 2 * C' := ⟨4 - a * D, by linear_combination (-1 : O) * s1⟩
        exact (hprime.dvd_mul.mp h1).resolve_left h2a2
      refine h2a2 ?_
      obtain ⟨w, hw⟩ := hC2
      exact ⟨-2 - w - a * B, by linear_combination (-1 : O) * s3 - hw⟩
  · -- `deg P = 2`, `deg Q = 1`
    have hdP : P.natDegree = 2 := by omega
    have hdQ : Q.natDegree = 1 := by omega
    have hc2 : P.coeff 2 = 1 := by
      have hm := hPmonic
      rwa [Polynomial.Monic, show P.leadingCoeff = P.coeff P.natDegree from rfl, hdP] at hm
    have hPform : P = Polynomial.X ^ 2 + Polynomial.C (P.coeff 1) * Polynomial.X
        + Polynomial.C (P.coeff 0) := by
      have h := eq_sum_three (O := O) (p := P) (by omega)
      have hc3' : P.coeff 3 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hc2, hc3', map_zero, zero_mul, zero_add, map_one, one_mul] at h
      exact h
    have hQform : Q = Polynomial.X + Polynomial.C (Q.coeff 0) := by
      have h := Polynomial.eq_X_add_C_of_degree_le_one
        (Polynomial.natDegree_le_iff_degree_le.mp (le_of_eq hdQ))
      have hc1 : Q.coeff 1 = 1 := by
        have hm := hQmonic
        rwa [Polynomial.Monic, show Q.leadingCoeff = Q.coeff Q.natDegree from rfl, hdQ] at hm
      rw [hc1, map_one, one_mul] at h
      exact h
    set b := P.coeff 1
    set c := P.coeff 0
    set e := Q.coeff 0
    have hcanon : (f₅ O)
        = Polynomial.C (2 * b + e) * Polynomial.X ^ 4
          + Polynomial.C (b ^ 2 + 2 * c + 2 * b * e) * Polynomial.X ^ 3
          + Polynomial.C (2 * b * c + b ^ 2 * e + 2 * c * e) * Polynomial.X ^ 2
          + Polynomial.C (c ^ 2 + 2 * b * c * e) * Polynomial.X
          + Polynomial.C (c ^ 2 * e) + Polynomial.X ^ 5 := by
      rw [hQ, hPform, hQform]
      simp only [map_add, map_mul, map_pow, map_ofNat, map_one]
      ring
    have hval := fun k => congrArg (fun r : Polynomial O => r.coeff k) (f₅_eq.symm.trans hcanon)
    have s4 : (1 : O) = 2 * b + e := by
      have h := hval 4
      simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] at h
      norm_num at h
      linear_combination h
    have s3 : (-4 : O) = b ^ 2 + 2 * c + 2 * b * e := by
      have h := hval 3
      simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] at h
      norm_num at h
      linear_combination h
    have s1 : (8 : O) = c ^ 2 + 2 * b * c * e := by
      have h := hval 1
      simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] at h
      norm_num at h
      linear_combination h
    have s0 : (12 : O) = c ^ 2 * e := by
      have h := hval 0
      simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] at h
      norm_num at h
      linear_combination h
    have h2b : (2 : O) ∣ b := by
      have h1 : (2 : O) ∣ b * b := ⟨-2 - c - b * e, by linear_combination (-1 : O) * s3⟩
      exact (hprime.dvd_mul.mp h1).elim id id
    have h2e : ¬ (2 : O) ∣ e := by
      intro hdvd
      obtain ⟨t, ht⟩ := hdvd
      exact h2.not_isUnit (isUnit_of_dvd_one ⟨b + t, by linear_combination s4 + ht⟩)
    have h2c : (2 : O) ∣ c := by
      have h1 : (2 : O) ∣ c * (c * e) := ⟨6, by linear_combination (-1 : O) * s0⟩
      rcases hprime.dvd_mul.mp h1 with h | h
      · exact h
      · rcases hprime.dvd_mul.mp h with h' | h'
        · exact h'
        · exact absurd h' h2e
    obtain ⟨b', hb'⟩ := h2b
    obtain ⟨c', hc'⟩ := h2c
    -- `e·s1 − s0` gives `12 + 8b′c′e² = 8e`; divide by 4: `3 + 2b′c′e² = 2e` — `2 ∣ 3`
    have hkey : (3 : O) + 2 * b' * c' * e ^ 2 = 2 * e := by
      refine mul_left_cancel₀ h4ne ?_
      linear_combination (-e) * s1 + s0 - 2 * e ^ 2 * c * hb' - 4 * e ^ 2 * b' * hc'
    exact h2dvd3 ⟨e - b' * c' * e ^ 2, by linear_combination hkey⟩

/-! ## 7. The label, the block, and THE REFUTATIONS -/

include h2 hq in
theorem f₅_key_not_dvd : ¬ (s2Frame h2 hq).key ∣ (f₅ O) := by
  rw [key_eq h2 hq]
  intro hdvd
  have h0 : dev (s2Key O) (f₅ O) 0 = 0 := by
    show (f₅ O) %ₘ (s2Key O) = 0
    exact (Polynomial.modByMonic_eq_zero_iff_dvd s2Key_monic).mpr hdvd
  rw [dev_f₅_zero] at h0
  have h4 : (4 : O) = 0 := by
    have := congrArg (fun r : Polynomial O => r.coeff 1) h0
    simpa using this
  rw [show (4 : O) = 2 ^ 2 by norm_num] at h4
  exact pow_ne_zero 2 h2.ne_zero h4

include h2 hq in
theorem hasLabel_f₅ : HasLabel ((s2Tower h2 hq).levelDatum h2) (f₅ O) := by
  refine ⟨f₅_monic, by rw [f₅_natDegree]; norm_num, pure_f₅ h2 hq,
    hne_f₅ h2 hq, 5, hp_f₅ h2 hq, 1, Nat.one_pos, ?_⟩
  rw [pow_one]
  show ρ₅ h2 hq = ((s2Tower h2 hq).levelDatum h2).r
  rw [ρ₅_eq_towerLabel h2 hq]
  rfl

include h2 hq in
theorem blockContext_f₅ : BlockContext ((s2Tower h2 hq).levelDatum h2) (f₅ O) := by
  refine ⟨f₅_monic, f₅_squarefree h2, f₅_key_not_dvd h2 hq, hne_f₅ h2 hq, 5, hp_f₅ h2 hq,
    ?_, ?_⟩
  · show 0 < dvSideDeg (s2Frame h2 hq) (f₅ O) 5 2 (hne_f₅ h2 hq)
    rw [dvsidedeg_f₅ h2 hq]
    norm_num
  · show ((s2Tower h2 hq).levelDatum h2).r ∣ ρ₅ h2 hq
    rw [ρ₅_eq_towerLabel h2 hq]
    exact dvd_rfl

include h2 hq in
theorem blockFactor_f₅ :
    blockFactorLeaky ((s2Tower h2 hq).levelDatum h2) (f₅ O) = f₅ O :=
  blockFactorLeaky_eq_of_frontier ((s2Tower h2 hq).levelDatum h2) (hasLabel_f₅ h2 hq) dvd_rfl
    (fun _ _ h => h)

include h2 hq in
theorem keyDeg₂_s2Tower : ((s2Tower h2 hq).levelDatum h2).keyDeg₂ = 4 := by
  have hr : ((s2Tower h2 hq).levelDatum h2).r.natDegree = 1 := by
    have h := (towerLabel_spec (s2Tower h2 hq) h2).2.2.1
    exact h
  rw [LevelDatum.keyDeg₂, e1_eq h2 hq, f1_eq h2 hq,
    show ((s2Tower h2 hq).levelDatum h2).ℓ = 2 from rfl, hr]

include h2 hq in
/-- ★ **the FLOOR conjunct survives at the probe**: `mult₂ = ⌊5/4⌋ = 1`. -/
theorem mult₂_f₅ : mult₂Leaky ((s2Tower h2 hq).levelDatum h2) (f₅ O) = 1 := by
  rw [mult₂Leaky, blockFactor_f₅ h2 hq, f₅_natDegree, keyDeg₂_s2Tower h2 hq]

end Uniformity.Density.Tower.C80

namespace Uniformity.Density.Tower.C80

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower Uniformity.Density.Tower.C35b

/-! ## 8. The ∀-closures, refuted absolutely over `ℤ_[2]` -/

/-- The signed C.80 `tie_pure_power`, closed over everything. -/
def TiePurePowerStatement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (π : O)
    (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key
      (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (_hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (f : Polynomial O) (_hctx : BlockContext (T.levelDatum hπ) f)
    (μ₂ : ℕ) (_hμ₂ : 0 < μ₂)
    (_hres : ∀ (hne : (dvSideSet F f T.u₂ T.e₂).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F f (dvSideMin F f T.u₂ T.e₂ hne) = (M₀ : ℕ∞)),
      ∃ c : F.stageField H₀ hpin, c ≠ 0 ∧
        dvResPoly F H₀ hpin f T.u₂ T.e₂ hne M₀ hp
          = Polynomial.C c * (towerLabel T) ^ μ₂),
    mult₂Leaky (T.levelDatum hπ) f = μ₂ ∧
    (blockFactorLeaky (T.levelDatum hπ) f).natDegree = T.D₂ * μ₂

/-- The signed C.77 `partial_projection`, closed over everything. -/
def PartialProjectionStatement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (π : O)
    (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key
      (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (_hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    (f : Polynomial O) (_hctx : BlockContext (T.levelDatum hπ) f),
    (dev (composedKey T) f (f.natDegree / T.D₂)).Monic ∧
    ((T.D₂ ∣ f.natDegree) → dev (composedKey T) f (f.natDegree / T.D₂) = 1) ∧
    (blockFactorLeaky (T.levelDatum hπ) f).natDegree =
      T.D₂ * mult₂Leaky (T.levelDatum hπ) f

private theorem hres_f₅ :
    ∀ (hne : (dvSideSet (s2Frame h2_padic rc2) (f₅ ℤ_[2])
        (s2Tower h2_padic rc2).u₂ (s2Tower h2_padic rc2).e₂).Nonempty) (M₀ : ℕ)
      (hp : dvHgt (s2Frame h2_padic rc2) (f₅ ℤ_[2])
        (dvSideMin (s2Frame h2_padic rc2) (f₅ ℤ_[2])
          (s2Tower h2_padic rc2).u₂ (s2Tower h2_padic rc2).e₂ hne) = (M₀ : ℕ∞)),
      ∃ c : (s2Frame h2_padic rc2).stageField 1 (s2Frame_pin h2_padic rc2), c ≠ 0 ∧
        dvResPoly (s2Frame h2_padic rc2) 1 (s2Frame_pin h2_padic rc2) (f₅ ℤ_[2])
          (s2Tower h2_padic rc2).u₂ (s2Tower h2_padic rc2).e₂ hne M₀ hp
          = Polynomial.C c * (towerLabel (s2Tower h2_padic rc2)) ^ 1 := by
  intro hne M₀ hp
  have hM : M₀ = 5 := by
    have h5 : (M₀ : ℕ∞) = ((5 : ℕ) : ℕ∞) := hp.symm.trans (hp_f₅ h2_padic rc2)
    exact_mod_cast h5
  subst hM
  letI : Field ((s2Frame h2_padic rc2).stageField 1 (s2Frame_pin h2_padic rc2)) :=
    s2StageFieldInst h2_padic rc2 1 (s2Frame_pin h2_padic rc2)
  refine ⟨1, one_ne_zero, ?_⟩
  rw [pow_one, map_one, one_mul]
  show ρ₅ h2_padic rc2 = towerLabel (s2Tower h2_padic rc2)
  exact ρ₅_eq_towerLabel h2_padic rc2

/-- ★ **NODE C.80's signed `tie_pure_power` is FALSE** — at `(s2Tower, f₅, μ₂ = 1)` over
`ℤ_[2]` every hypothesis holds and the exact-degree conjunct demands `5 = 4`, while the
floor conjunct `mult₂ = 1` is TRUE at the same instance (`mult₂_f₅`). -/
theorem tiePurePower_false : ¬ TiePurePowerStatement := by
  intro hax
  have h := hax ℤ_[2] (2 : ℤ_[2]) (s2Frame h2_padic rc2) 1
    (s2Frame_pin h2_padic rc2) (s2Tower h2_padic rc2) h2_padic le_rfl (f₅ ℤ_[2])
    (blockContext_f₅ h2_padic rc2) 1 Nat.one_pos (hres_f₅)
  have h2c := h.2
  rw [blockFactor_f₅ h2_padic rc2, f₅_natDegree, (s2Tower_data h2_padic rc2).2.2.2.1,
    mul_one] at h2c
  norm_num at h2c

/-- ★ **NODE C.77's signed `partial_projection` is FALSE** (through clause (iii)) — at
`(s2Tower, f₅)` over `ℤ_[2]`, `BlockContext` alone is demanded and the clause requires
`5 = 4 · 1`. -/
theorem partialProjection_false : ¬ PartialProjectionStatement := by
  intro hax
  have h := hax ℤ_[2] (2 : ℤ_[2]) (s2Frame h2_padic rc2) 1
    (s2Frame_pin h2_padic rc2) (s2Tower h2_padic rc2) h2_padic le_rfl (f₅ ℤ_[2])
    (blockContext_f₅ h2_padic rc2)
  have h3 := h.2.2
  rw [blockFactor_f₅ h2_padic rc2, f₅_natDegree, (s2Tower_data h2_padic rc2).2.2.2.1,
    mult₂_f₅ h2_padic rc2, mul_one] at h3
  norm_num at h3

end Uniformity.Density.Tower.C80

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C80.s2Tower
#print axioms Uniformity.Density.Tower.C80.f₅_squarefree
#print axioms Uniformity.Density.Tower.C80.pure_f₅
#print axioms Uniformity.Density.Tower.C80.ρ₅_eq_towerLabel
#print axioms Uniformity.Density.Tower.C80.hasLabel_f₅
#print axioms Uniformity.Density.Tower.C80.blockContext_f₅
#print axioms Uniformity.Density.Tower.C80.blockFactor_f₅
#print axioms Uniformity.Density.Tower.C80.mult₂_f₅
#print axioms Uniformity.Density.Tower.C80.tiePurePower_false
#print axioms Uniformity.Density.Tower.C80.partialProjection_false

end AxCheck
