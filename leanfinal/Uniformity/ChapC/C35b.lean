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

-- the `[Finite (ResidueField O)]` binder is `s2Frame`'s signed (unused) carried hypothesis;
-- the pure-polynomial helpers below don't consume it.
set_option linter.unusedSectionVars false

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

/-! ## 1. Frame arithmetic at the landed `s2Frame` (C.97; the C66-cert helper set) -/

theorem e1_eq : (s2Frame h2 hq).e₁ = 2 := rfl
theorem f1_eq : (s2Frame h2 hq).f₁ = 1 := rfl
theorem h_eq : (s2Frame h2 hq).h = 1 := rfl
theorem key_eq : (s2Frame h2 hq).key = s2Key O := rfl

theorem s2Key_deg : (s2Key O).degree = 2 := by
  rw [Polynomial.degree_eq_natDegree (s2Key_monic (O := O)).ne_zero, s2Key_natDegree]
  rfl

theorem gaussVal_C (a : O) : gaussVal (Polynomial.C a) = IsDiscreteValuationRing.addVal O a := by
  simp [gaussVal]

include h2 in
theorem addVal_two_pow (k : ℕ) : IsDiscreteValuationRing.addVal O ((2 : O) ^ k) = (k : ℕ∞) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, AddValuation.map_mul, ih, addVal_uniformizer h2]
      push_cast; ring

include h2 hq in
theorem sh_C (a : O) :
    (s2Frame h2 hq).stageHeight (Polynomial.C a) = 2 • IsDiscreteValuationRing.addVal O a := by
  rw [KeyFrame.stageHeight_eq_inf]
  simp [e1_eq, h_eq, gaussVal_C]

include h2 hq in
theorem sh_C_pow (k : ℕ) :
    (s2Frame h2 hq).stageHeight (Polynomial.C ((2 : O) ^ k)) = ((2 * k : ℕ) : ℕ∞) := by
  rw [sh_C h2 hq, addVal_two_pow h2]
  push_cast; rw [two_nsmul]; ring

theorem sh_zero : (s2Frame h2 hq).stageHeight (0 : Polynomial O) = ⊤ := by
  rw [KeyFrame.stageHeight_eq_inf]
  simp only [e1_eq, h_eq]
  simp only [Polynomial.natDegree_zero, show Finset.range (0 + 1) = {0} from rfl,
    Finset.inf_singleton, Polynomial.coeff_zero, map_zero,
    (gaussVal_eq_top_iff (O := O)).mpr rfl]
  simp

/-- the stage height of the top digit `x` is `1` — this is `dv(θ) = 1`, i.e. `ϖ = x` at
this frame. -/
theorem sh_X : (s2Frame h2 hq).stageHeight (Polynomial.X : Polynomial O) = 1 := by
  rw [KeyFrame.stageHeight_eq_inf]
  simp only [Polynomial.natDegree_X, show Finset.range (1 + 1) = {0, 1} from rfl,
    Finset.inf_insert, Finset.inf_singleton, Polynomial.coeff_X_zero, Polynomial.coeff_X_one,
    e1_eq h2 hq, h_eq h2 hq, gaussVal_C, AddValuation.map_zero, AddValuation.map_one]
  simp

/-! ## 2. The refuting polynomial `g₀ = x³ − 2x + 4` and its `Φ′`-development -/

/-- the refuting labelled polynomial: `g₀ = x³ − 2x + 4 = x·Φ′ + 2²`, monic of ODD degree
`3` at the `D′ = 2` frame. -/
noncomputable def g₀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    Polynomial O :=
  Polynomial.X ^ 3 - Polynomial.C 2 * Polynomial.X + Polynomial.C 4

theorem g₀_eq_pow_add :
    (g₀ O) = Polynomial.X ^ 3 + (Polynomial.C (-2) * Polynomial.X + Polynomial.C 4) := by
  rw [g₀, map_neg]; ring

theorem g₀_monic : (g₀ O).Monic := by
  rw [g₀_eq_pow_add]
  exact Polynomial.monic_X_pow_add
    (lt_of_le_of_lt Polynomial.degree_linear_le (by decide))

theorem g₀_natDegree : (g₀ O).natDegree = 3 := by
  have hdeg : (g₀ O).degree = 3 := by
    rw [g₀_eq_pow_add,
      Polynomial.degree_add_eq_left_of_degree_lt (by
        rw [Polynomial.degree_X_pow]
        exact lt_of_le_of_lt Polynomial.degree_linear_le (by decide)),
      Polynomial.degree_X_pow]
    rfl
  exact Polynomial.natDegree_eq_of_degree_eq_some hdeg

/-- `2 ∤ 3` — the divisibility the D13 claim asserts, false at `g₀`. -/
theorem g₀_not_dvd :
    ¬ ((s2Frame h2 hq).e₁ * (s2Frame h2 hq).f₁ ∣ (g₀ O).natDegree) := by
  rw [e1_eq h2 hq, f1_eq h2 hq, g₀_natDegree]
  omega

theorem g₀_divmod :
    (g₀ O) /ₘ (s2Key O) = Polynomial.X ∧ (g₀ O) %ₘ (s2Key O) = Polynomial.C ((2 : O) ^ 2) := by
  refine Polynomial.div_modByMonic_unique _ _ s2Key_monic ⟨?_, ?_⟩
  · simp only [g₀, s2Key, show ((2 : O) ^ 2) = 4 from by norm_num, map_ofNat]
    ring
  · rw [s2Key_deg]
    exact lt_of_le_of_lt Polynomial.degree_C_le (by decide)

theorem dev_g₀_zero : dev (s2Key O) (g₀ O) 0 = Polynomial.C ((2 : O) ^ 2) := g₀_divmod.2

theorem dev_g₀_one : dev (s2Key O) (g₀ O) 1 = Polynomial.X := by
  show ((g₀ O) /ₘ (s2Key O)) %ₘ (s2Key O) = Polynomial.X
  rw [g₀_divmod.1, Polynomial.modByMonic_eq_self_iff s2Key_monic, s2Key_deg,
    Polynomial.degree_X]
  decide

theorem dev_g₀_two : dev (s2Key O) (g₀ O) 2 = 0 :=
  dev_eq_zero_of_lt s2Key_monic (by rw [s2Key_natDegree]; norm_num) _ 2
    (by rw [g₀_natDegree, s2Key_natDegree]; norm_num)

theorem dev_g₀_three : dev (s2Key O) (g₀ O) 3 = 0 :=
  dev_eq_zero_of_lt s2Key_monic (by rw [s2Key_natDegree]; norm_num) _ 3
    (by rw [g₀_natDegree, s2Key_natDegree]; norm_num)

/-! ## 3. The level polygon of `g₀`: heights `(4, 1, ⊤, ⊤)`, side `{0, 1}` at `(u,ℓ)=(3,1)` -/

theorem dvhgt_g₀_0 : dvHgt (s2Frame h2 hq) (g₀ O) 0 = (4 : ℕ∞) := by
  rw [dvHgt, key_eq, dev_g₀_zero, sh_C_pow h2 hq 2]; rfl

theorem dvhgt_g₀_1 : dvHgt (s2Frame h2 hq) (g₀ O) 1 = (1 : ℕ∞) := by
  rw [dvHgt, key_eq, dev_g₀_one, sh_X]

theorem dvhgt_g₀_2 : dvHgt (s2Frame h2 hq) (g₀ O) 2 = ⊤ := by
  rw [dvHgt, key_eq, dev_g₀_two, sh_zero]

theorem dvhgt_g₀_3 : dvHgt (s2Frame h2 hq) (g₀ O) 3 = ⊤ := by
  rw [dvHgt, key_eq, dev_g₀_three, sh_zero]

theorem dvsupp_g₀ : dvSupp (s2Frame h2 hq) (g₀ O) 3 1 = 4 := by
  rw [dvSupp]
  simp only [g₀_natDegree, show Finset.range (3 + 1) = {0, 1, 2, 3} from rfl,
    Finset.inf_insert, Finset.inf_singleton, dvhgt_g₀_0 h2 hq, dvhgt_g₀_1 h2 hq,
    dvhgt_g₀_2 h2 hq, dvhgt_g₀_3 h2 hq]
  simp
  decide

theorem dvside_g₀ : dvSideSet (s2Frame h2 hq) (g₀ O) 3 1 = {0, 1} := by
  classical
  ext j
  simp only [dvSideSet, Finset.mem_filter, Finset.mem_range, g₀_natDegree,
    Finset.mem_insert, Finset.mem_singleton, DvOnSide, dvsupp_g₀ h2 hq]
  constructor
  · rintro ⟨hj, -, hne⟩
    interval_cases j
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd (dvhgt_g₀_2 h2 hq) hne
    · exact absurd (dvhgt_g₀_3 h2 hq) hne
  · rintro (rfl | rfl)
    · exact ⟨by norm_num, by rw [dvhgt_g₀_0 h2 hq]; simp, by rw [dvhgt_g₀_0 h2 hq]; simp⟩
    · exact ⟨by norm_num, by rw [dvhgt_g₀_1 h2 hq]; simp; decide,
        by rw [dvhgt_g₀_1 h2 hq]; simp⟩

theorem hne_g₀ : (dvSideSet (s2Frame h2 hq) (g₀ O) 3 1).Nonempty :=
  ⟨0, by rw [dvside_g₀ h2 hq]; simp⟩

/-- **`g₀` is `(3,1)`-pure**: both endpoint abscissae `0` and `⌊3/2⌋ = 1` are on the side. -/
theorem pure_g₀ : IsDvPure (s2Frame h2 hq) (g₀ O) 3 1 := by
  constructor
  · rw [dvside_g₀ h2 hq]; simp
  · rw [show (g₀ O).natDegree / ((s2Frame h2 hq).e₁ * (s2Frame h2 hq).f₁) = 1 from by
        rw [g₀_natDegree, e1_eq, f1_eq]]
    rw [dvside_g₀ h2 hq]; simp

theorem dvsidemin_g₀ : dvSideMin (s2Frame h2 hq) (g₀ O) 3 1 (hne_g₀ h2 hq) = 0 :=
  le_antisymm (Finset.min'_le _ 0 (by rw [dvside_g₀ h2 hq]; simp)) (Nat.zero_le _)

theorem hp_g₀ : dvHgt (s2Frame h2 hq) (g₀ O)
    (dvSideMin (s2Frame h2 hq) (g₀ O) 3 1 (hne_g₀ h2 hq)) = ((4 : ℕ) : ℕ∞) := by
  rw [dvsidemin_g₀ h2 hq, dvhgt_g₀_0 h2 hq]; rfl

theorem dvsidedeg_g₀ : dvSideDeg (s2Frame h2 hq) (g₀ O) 3 1 (hne_g₀ h2 hq) = 1 := by
  have hmax : dvSideMax (s2Frame h2 hq) (g₀ O) 3 1 (hne_g₀ h2 hq) = 1 := by
    refine le_antisymm (Finset.max'_le _ _ _ ?_)
      (Finset.le_max' _ 1 (by rw [dvside_g₀ h2 hq]; simp))
    intro y hy
    rw [dvside_g₀ h2 hq] at hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · norm_num
    · exact le_of_eq (by simpa using hy)
  rw [dvSideDeg, hmax, dvsidemin_g₀ h2 hq]

/-! ## 4. The level residual `ρ = R_λ(g₀)` is MONIC of degree 1 with `ρ(0) ≠ 0` -/

/-- the level residual polynomial of `g₀` at `(u, ℓ) = (3, 1)`, pinned at `M₀ = 4`. -/
noncomputable def ρ : Polynomial ((s2Frame h2 hq).stageField 1 (s2Frame_pin h2 hq)) :=
  dvResPoly (s2Frame h2 hq) 1 (s2Frame_pin h2 hq) (g₀ O) 3 1 (hne_g₀ h2 hq) 4 (hp_g₀ h2 hq)

/-- C.26 at the instance: `deg ρ = d = 1` and `ρ(0) ≠ 0`. -/
theorem ρ_spec : (ρ h2 hq).natDegree = 1 ∧ (ρ h2 hq).coeff 0 ≠ 0 := by
  have h := natDegree_dvResPoly (s2Frame h2 hq) h2 1 (s2Frame_pin h2 hq)
    Nat.one_pos (Nat.coprime_one_right 3) (hne_g₀ h2 hq) (hp_g₀ h2 hq)
  rw [dvsidedeg_g₀ h2 hq] at h
  exact h

theorem ρ_natDegree : (ρ h2 hq).natDegree = 1 := (ρ_spec h2 hq).1

theorem ρ_coeff_zero_ne : (ρ h2 hq).coeff 0 ≠ 0 := (ρ_spec h2 hq).2

/-! ### The slot arithmetic at `k = 1`: `i(1) = 1`, `q(1) = 0`, window `{0}` -/

theorem slotIdx_one : (s2Frame h2 hq).slotIdx 1 = 1 := by
  change ((List.range 2).find? (fun i => (i * 1) % 2 == 1 % 2)).getD 0 = 1
  rfl

theorem twistExp_one : (s2Frame h2 hq).twistExp 1 = 0 := by
  rw [KeyFrame.twistExp, slotIdx_one h2 hq, e1_eq h2 hq]

theorem slotWindow_one : (s2Frame h2 hq).slotWindow 1 = {0} := by
  rw [KeyFrame.slotWindow]
  ext t
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton,
    f1_eq h2 hq, e1_eq h2 hq, h_eq h2 hq, slotIdx_one h2 hq]
  omega

theorem slotRes_one_X :
    (s2Frame h2 hq).slotRes 1 (s2Frame_pin h2 hq) 1 (Polynomial.X : Polynomial O) = 1 := by
  rw [KeyFrame.slotRes, slotWindow_one h2 hq, Finset.sum_singleton]
  have hidx : (s2Frame h2 hq).slotIdx 1 + (s2Frame h2 hq).e₁ * 0 = 1 := by
    rw [slotIdx_one h2 hq, e1_eq h2 hq]
  rw [hidx]
  have hdig : (1 - 1 * (s2Frame h2 hq).h) / (s2Frame h2 hq).e₁ = 0 := by
    rw [h_eq h2 hq, e1_eq h2 hq]
  rw [hdig, Polynomial.coeff_X_one, digAt_zero, map_one, map_one, map_one, pow_zero, mul_one]

/-- the ϖ-read of the top digit `A₁ = x` at its on-side height `1` is `1` — `ϖ = x` at this
frame, so the read is `res(θ/ϖ) = 1`. -/
theorem twistRead_one_X :
    (s2Frame h2 hq).twistRead 1 (s2Frame_pin h2 hq) 1 (Polynomial.X : Polynomial O) = 1 := by
  simp only [KeyFrame.twistRead, twistExp_one h2 hq, pow_zero, one_mul]
  exact slotRes_one_X h2 hq

/-- the leading coefficient of `ρ` is the ϖ-read of `A₁ = x` at height `1`, i.e. `1`. -/
theorem ρ_coeff_one : (ρ h2 hq).coeff 1 = 1 := by
  unfold ρ
  rw [dvResPoly, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow,
    if_pos (by rw [dvsidedeg_g₀ h2 hq]; omega), dvsidemin_g₀ h2 hq,
    show (4 - 1 * 3 : ℕ) = 1 from rfl, show (0 + 1 * 1 : ℕ) = 1 from rfl,
    key_eq h2 hq, dev_g₀_one]
  exact twistRead_one_X h2 hq

theorem ρ_monic : (ρ h2 hq).Monic :=
  Polynomial.monic_of_natDegree_le_of_coeff_eq_one 1
    (le_of_eq (ρ_natDegree h2 hq)) (ρ_coeff_one h2 hq)

/-! ## 5. The level datum `L₀` with `r := ρ`, and `HasLabel L₀ g₀` -/

/-- **the refuting level datum**: `(u, ℓ) = (3, 1)` and `r := ρ` itself.  `hκ` reads
`1·(2·1)·1 = 2 < 3`; `r` is monic (leading read `1`), irreducible (degree one over the stage
field `K₁`), with `r(0) ≠ 0` (C.26). -/
noncomputable def L₀ : LevelDatum (s2Frame h2 hq) 1 (s2Frame_pin h2 hq) where
  u := 3
  ℓ := 1
  r := ρ h2 hq
  hℓ := Nat.one_pos
  hcop := Nat.coprime_one_right 3
  hκ := by rw [e1_eq h2 hq, f1_eq h2 hq, h_eq h2 hq]; omega
  hrmonic := ρ_monic h2 hq
  hrirr := by
    letI : Field ((s2Frame h2 hq).stageField 1 (s2Frame_pin h2 hq)) :=
      s2StageFieldInst h2 hq 1 (s2Frame_pin h2 hq)
    have hne0 : (ρ h2 hq) ≠ 0 := fun hz => ρ_coeff_zero_ne h2 hq (by rw [hz]; simp)
    exact irreducible_of_degree_eq_one
      ((Polynomial.degree_eq_iff_natDegree_eq hne0).mpr (ρ_natDegree h2 hq))
  hr0 := ρ_coeff_zero_ne h2 hq
  hrdeg := by rw [ρ_natDegree h2 hq]; norm_num

/-- **the label holds**: `g₀` is monic of positive degree, `(3,1)`-pure, and its level
residual is `r¹` on the nose. -/
theorem hasLabel_g₀ : HasLabel (L₀ h2 hq) (g₀ O) := by
  refine ⟨g₀_monic, by rw [g₀_natDegree]; norm_num, pure_g₀ h2 hq,
    hne_g₀ h2 hq, 4, hp_g₀ h2 hq, 1, Nat.one_pos, ?_⟩
  rw [pow_one]
  rfl

/-! ## 6. The refutation, absolute over `ℤ_[2]` -/

section Absolute

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

instance instFin2 : Finite (IsLocalRing.ResidueField ℤ_[2]) :=
  Finite.of_equiv (ZMod 2) (PadicInt.residueField (p := 2)).symm.toEquiv

theorem rc2 : residueCard ℤ_[2] = 2 := by
  have : Nat.card (IsLocalRing.ResidueField ℤ_[2]) = Nat.card (ZMod 2) :=
    Nat.card_congr (PadicInt.residueField (p := 2)).toEquiv
  rw [residueCard, this, Nat.card_eq_fintype_card, ZMod.card]

theorem h2_padic : Irreducible (2 : ℤ_[2]) := by simpa using PadicInt.irreducible_p (p := 2)

/-- the label and the degree obstruction, both inhabited at the REAL base `ℤ_[2]` —
nothing in the refutation is vacuous. -/
example : HasLabel (L₀ h2_padic rc2) (g₀ ℤ_[2]) ∧ (g₀ ℤ_[2]).natDegree = 3 ∧
    (s2Frame h2_padic rc2).e₁ * (s2Frame h2_padic rc2).f₁ = 2 :=
  ⟨hasLabel_g₀ h2_padic rc2, g₀_natDegree, rfl⟩

/-- **D13 IS FALSE.**  The constructed frame realizes every hypothesis of
`hasLabel_natDegree_dvd` over `ℤ_[2]` while its conclusion fails (`2 ∤ 3`). -/
theorem d13_refuted : ¬ D13Statement := fun hax =>
  g₀_not_dvd h2_padic rc2
    (hax ℤ_[2] 2 (s2Frame h2_padic rc2) 1 (s2Frame_pin h2_padic rc2)
      (L₀ h2_padic rc2) h2_padic (g₀ ℤ_[2]) (hasLabel_g₀ h2_padic rc2))

end Absolute

end Uniformity.Density.Tower.C35b

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C35b.hasLabel_g₀
#print axioms Uniformity.Density.Tower.C35b.d13_refuted

end AxCheck
