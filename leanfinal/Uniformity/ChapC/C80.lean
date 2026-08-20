/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
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

end Uniformity.Density.Tower.C80
