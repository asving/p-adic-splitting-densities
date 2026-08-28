/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C136d0
import Uniformity.ChapC.C136d1
import Uniformity.ChapC.C136d2
import Uniformity.ChapC.C136d3
import Uniformity.ChapC.C136d3ad

/-!
# Uniformity.ChapC.C136e0 — the μ₅ refinement stack's base: D4-00..D4-04 [D4A 2026-08-28]

**Unit D4A** of the deep-witness campaign
(`docs/in-progress/DEEP_WITNESS_CAMPAIGN_2026-08-28.md` §6.3, rows D4-00, D4-01, D4-02,
D4-03, D4-04).  One file for the five chained rows (recorded deviation: §5 names
declarations, not files; the five rows are consumed as one dependency chain, exactly as the
D3 stack's C136d0/C136d3ad landed the matching shapes one level down).

The μ₅ stack mirrors the landed μ₄ D3 series ONE LEVEL UP, with `g16` (= the T5/D3-19
chain's `keyAt 4`) in place of `g8` and the [G5F]-adjudicated REFINEMENT side
`(u₅, ℓ₅) = (171, 1)` in place of `(85, 2)` — per the [G5F 2026-08-28] record, `(1,1,171)`
is source-faithful OPERATOR data over the depth-four tower, never a fifth proper
`DeepTower` stage:

* **D4-00 (support shell).**  The `keyAt4`-development support layer
  `dv4Hgt`/`dv4Pin`/`dv4Supp` (mirror of C136d0's `dv3Hgt`/`dv3Pin`/`dv3Supp`, one level
  up: the inner read is now the LEVEL-3 cleared support `dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ · u₃ ℓ₃` —
  this equality of shapes IS the tower recursion), and the zero/ne-top/add/negation bank
  plus the full endpoint/minimizer/convolution bank (mirror of C136d0's Parts 1 and 3).
  Parameter-free: no S2 numeral occurs in Parts 1–3; the bank is generic over any level
  datum `L`, inner key/sides `(Ψ₂, u₂, ℓ₂)`, `(Ψ₃, u₃, ℓ₃)`, and outer key/side
  `(Ψ₄, u₄, ℓ₄)`, threading the monicity/degree/positivity hypotheses that C136d0's own
  `dv3Supp` laws demand.
* **D4-01 (μ₅ value/product).**  The S2 numeral instantiation
  `s2Hgt₅ g := toZ (dv4Supp L Φ₂ 21 2 g₈ 85 2 g16 g 171 1)` with the zero/finiteness/add
  laws and the tower-height tooth `s2Hgt₅ g16 = 171 = u₅` (mirror of C136d0's
  `s2Hgt₄ g₈ = 85`); the UNCONDITIONAL product law `s2Hgt₅_mul_unconditional`/
  `s2Hgt₅_mul_all` lands in Part 6, fired at D4-02's discharged survival (mirroring how
  D3-04 landed in C136d3ad Part 4 — the row text's "survival folded into D4-02").
* **D4-02 (μ₄ survival — THE GENUINE NEW CORE).**  Endpoint survival modulo `keyAt4`:
  the generic μ-key predicates at the level-4 valuation (`Mu4Equiv`/`Mu4Dvd`/`Mu4Minimal`/
  `Mu4Prime`/`IsMu4Key`), the `%ₘ`/`/ₘ` survival core, and `dv4ResSurv_of_mu4Key`, then
  the S2 discharge `s2_dv4ResSurv_at_171` from the landed μ₄ key theorem
  `C136d3.s2Mu4KeyPoly_g16` (itself proved through the μ₄ normalized product
  `C136d2.s2Mu4NormRes_mul` — the row's demanded mechanism enters exactly there), the
  landed grade `C136d2.g16_exactGrade` (`= 170`), and the [G5F] tight floor
  `1·170 = 170 < 171`.  Recorded deviation: the pattern followed is the D3AD survival
  mirror (`C136d3ad.dv3ResSurv_of_mu3Key`, the closer landed template named by the
  campaign brief), not a literal port of `C132nv3b.s2_dvSupp_mul_modByComposedKey_eq`;
  the inner μ₄ multiplicativity `hmul` is supplied by D3-04's landed unconditional
  `s2Hgt₄_mul_all` through the `toZ` bridge.
* **D4-03 (valuation/grades).**  `s2Hgt₅_one_eq_zero`, the genuine UNCONDITIONAL
  `AddValuation` packaging `s2AddVal₅` directly from the product law (the D3-05 pattern,
  C136d1), and the full `S2Mu5ExactGrade`/`S2Mu5AboveGrade` grade-predicate bank.
* **D4-04 (grade-line coordinates — the refinement gate).**  With `e' = 1`: published
  Def 3.12's line arithmetic at level 5 (`(e₅,h₅) = (1,171)`) has the UNIQUE slot residue
  `0` (`s₅(β) = β % 1 = 0`, `u₅(β) = β` — no division, no excluded parity class), the μ₅
  grade-line gate `S2Mu5SlotOnGrade` admits EVERY abscissa residue, and
  `S2Mu5PrevGrade β := 1 ∣ β` is ALL grades (`S2Mu5PrevGrade_all`) — this is exactly where
  `(1,1,171)` genuinely differs from the proper stages, per the [G5F] record and G5's row
  text.  The level-4 ε-data Bézout pair `(1, −42)` is pinned for row D4-05's ε-exponent.

## What this unit does NOT claim (honesty scope)

No μ₅ coefficient/graded/normalized operator (rows D4-05..D4-09), no normalizer exact
grade (D4-10), no recipe/leaf (D4-11/12), no μ₅ key predicates on top of the μ₅ valuation
(D4-13..16), no `FGMNSourceData`/calculus record (D4-17/18).  The `(1,1,171)` triple is
consumed strictly as OPERATOR data over the landed depth-four tower — no
`DeepTower.hproper` proof is forged or implied (the [G5F] record's carrier-boundary
clause).  The OPEN-RP1-TRANSPORT faithfulness split is inherited exactly as the D3 stack
left it — cited, never re-derived or re-opened.

**DEPENDS.** C136d0 (D3-00/01/02: the `dv3` layer and its full bank, `s2Hgt₄`,
`s2g8_monic`/`s2g8_natDegree`) · C136d1 (D3-05: `s2Hgt₄_one_eq_zero`,
`S2Mu4ExactGrade` + `S2Mu4ExactGrade_iff_dv3Supp`) · C136d2 (D3-14: `g16`, `g16_monic`,
`g16_natDegree`, `g16_exactGrade`) · C136d3 (D3-15/16/19: `S2Mu4KeyPoly`,
`s2Mu4KeyPoly_g16`, `s2DepthFourKeyChain` + its `keyAt 4 = g16` pin) · C136d3ad
(D3-03/04: `s2Hgt₄_mul_all`; the survival-mirror proof pattern) · C132nv1 (`s2Φ₂_monic`,
`s2Φ₂_natDegree`) · C130rp0 (`toZ_lt_toZ_iff`) · C130nv (`toZ_add`) · C130s6 (`toZ` bank) ·
C130nv2 (`weight_read`, `succ_le_of_weight_succ_le`, `dev_zero_pin`) · C118a
(`inf_range_ext`, `smul_top_pos`, `dev_zero_any`) · B.02–B.05, B32a, B35a, B39b (the `dev`
bank).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement invented
beyond the rows' sketches and the μ₄→μ₅ porting pattern.  New statement shapes (every
`def` and every theorem introducing a new predicate) are trust-boundary declarations
flagged for human review.  Verdict: `runs/wave-c/verdict_D4A.md`.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C136e0

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C132nv0
open Uniformity.Density.Tower.C130nv2 (weight_read succ_le_of_weight_succ_le dev_zero_pin)
open Uniformity.Density.Tower.C136d0

/-! ## Part 1 — D4-00: the `Ψ₄`-development support layer and its law bank

The three definitions mirror C136d0's `dv3Hgt`/`dv3Pin`/`dv3Supp` one level up: the inner
read is the level-3 cleared support at the inner key/sides `(Ψ₂, u₂, ℓ₂)`, `(Ψ₃, u₃, ℓ₃)`.
The bank then mirrors C136d0's Part 1 lemma-for-lemma, with C136d0's own `dv3Supp` laws
consumed as the inner facts exactly where C136d0 consumed C132nv0's `dv2Supp` laws. -/

section Generic

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- The level-4 slot height of a coefficient: the LEVEL-3 cleared support at the inner
key/sides.  This equality of shapes IS the tower recursion (mirror of C136d0's
`dv3Hgt L Ψ₂ u₂ ℓ₂ A := dv2Supp L Ψ₂ A u₂ ℓ₂`, one level up). -/
noncomputable def dv4Hgt {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ₂ : Polynomial O) (u₂ ℓ₂ : ℕ) (Ψ₃ : Polynomial O) (u₃ ℓ₃ : ℕ)
    (A : Polynomial O) : ℕ∞ :=
  dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ A u₃ ℓ₃

/-- Anti-drift pin: the layer's inner read IS `dv3Supp` at the inner key/sides. -/
theorem dv4Hgt_eq_dv3Supp {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ₂ : Polynomial O) (u₂ ℓ₂ : ℕ) (Ψ₃ : Polynomial O) (u₃ ℓ₃ : ℕ) (A : Polynomial O) :
    dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ A = dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ A u₃ ℓ₃ := rfl

/-- The level-4 pins of `f` at the outer key `Ψ₄`: the level-4 slot heights of the
`Ψ₄`-development coefficients (B.02's `dev`, three levels up). -/
noncomputable def dv4Pin {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ₂ : Polynomial O) (u₂ ℓ₂ : ℕ) (Ψ₃ : Polynomial O) (u₃ ℓ₃ : ℕ)
    (Ψ₄ f : Polynomial O) (j : ℕ) : ℕ∞ :=
  dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ (dev Ψ₄ f j)

/-- The level-4 cleared support `inf_j (ℓ₄·dv4Pin_j + u₄·j)` — B.14's shape at the level-4
polygon.  The range bound mirrors C136d0's, as C.11's does two levels down. -/
noncomputable def dv4Supp {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ₂ : Polynomial O) (u₂ ℓ₂ : ℕ) (Ψ₃ : Polynomial O) (u₃ ℓ₃ : ℕ)
    (Ψ₄ f : Polynomial O) (u₄ ℓ₄ : ℕ) : ℕ∞ :=
  (Finset.range (f.natDegree + 1)).inf
    (fun j => ℓ₄ • dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f j + (u₄ * j : ℕ∞))

/-! ### The inner-height shims (mirror of C136d0's shims, one level up)

Free from C136d0's `dv3Supp` bank, exactly as C136d0's `dv3Hgt` shims were free from
C132nv0's `dv2Supp` bank. -/

/-- `dv4Hgt` of `0` is `⊤` (free from C136d0's `dv3Supp_zero_eq_top`). -/
theorem dv4Hgt_zero {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ₂ : Polynomial O) (u₂ : ℕ) {ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (Ψ₃ : Polynomial O) (u₃ : ℕ)
    {ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃) :
    dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ (0 : Polynomial O) = ⊤ :=
  dv3Supp_zero_eq_top L Ψ₂ u₂ hℓ₂ Ψ₃ u₃ hℓ₃

/-- a nonzero polynomial has finite `dv4Hgt` (free from C136d0's
`dv3Supp_ne_top_of_ne_zero`). -/
theorem dv4Hgt_ne_top_of_ne_zero {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {Ψ₂ : Polynomial O} (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree) (u₂ ℓ₂ : ℕ)
    {Ψ₃ : Polynomial O} (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree) (u₃ ℓ₃ : ℕ)
    {A : Polynomial O} (hA : A ≠ 0) : dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ A ≠ ⊤ :=
  dv3Supp_ne_top_of_ne_zero L hΨ₂ hΨ₂d u₂ ℓ₂ hΨ₃ hΨ₃d u₃ ℓ₃ hA

/-- The ultrametric inequality for `dv4Hgt` (free from C136d0's
`min_dv3Supp_le_dv3Supp_add`). -/
theorem min_dv4Hgt_le_dv4Hgt_add {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {Ψ₂ : Polynomial O} (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree) {u₂ ℓ₂ : ℕ}
    (hℓ₂ : 0 < ℓ₂) {Ψ₃ : Polynomial O} (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree)
    {u₃ ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃) (A B : Polynomial O) :
    min (dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ A) (dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ B)
      ≤ dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ (A + B) :=
  min_dv3Supp_le_dv3Supp_add L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ A B

/-- The ultrametric EQUALITY off ties for `dv4Hgt` (free from C136d0's
`dv3Supp_add_eq`). -/
theorem dv4Hgt_add_eq {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {Ψ₂ : Polynomial O} (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree) {u₂ ℓ₂ : ℕ}
    (hℓ₂ : 0 < ℓ₂) {Ψ₃ : Polynomial O} (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree)
    {u₃ ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃) {A B : Polynomial O}
    (hne : dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ A ≠ dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ B) :
    dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ (A + B)
      = min (dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ A) (dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ B) :=
  dv3Supp_add_eq L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ hne

/-- `dv4Hgt` is negation-invariant (free from C136d0's `dv3Supp_neg`). -/
theorem dv4Hgt_neg {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {Ψ₂ : Polynomial O} (hΨ₂ : Ψ₂.Monic) (u₂ ℓ₂ : ℕ) {Ψ₃ : Polynomial O} (hΨ₃ : Ψ₃.Monic)
    (u₃ ℓ₃ : ℕ) (A : Polynomial O) :
    dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ (-A) = dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ A :=
  dv3Supp_neg L hΨ₂ u₂ ℓ₂ hΨ₃ A u₃ ℓ₃

/-! ### The `dv4Supp` zero/ne-top/add/negation bank (mirror of C136d0's Part 1, one level up) -/

/-- `dv4Pin` vanishes to `⊤` past the degree (mirror of C136d0's `dv3Pin_top_of_gt`). -/
theorem dv4Pin_top_of_gt {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ₂ : Polynomial O) (u₂ : ℕ) {ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (Ψ₃ : Polynomial O) (u₃ : ℕ)
    {ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃) {Ψ₄ : Polynomial O} (hΨ₄ : Ψ₄.Monic)
    (hΨ₄d : 0 < Ψ₄.natDegree) (f : Polynomial O) {j : ℕ} (hj : f.natDegree < j) :
    dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f j = ⊤ := by
  have hjd : j ≤ j * Ψ₄.natDegree := Nat.le_mul_of_pos_right _ hΨ₄d
  rw [dv4Pin, dev_eq_zero_of_lt hΨ₄ hΨ₄d f j (by omega), dv4Hgt]
  exact dv3Supp_zero_eq_top L Ψ₂ u₂ hℓ₂ Ψ₃ u₃ hℓ₃

/-- `dv4Supp` of `0` is `⊤` (mirror of C136d0's `dv3Supp_zero_eq_top`; no outer monicity
needed, since `dev` of the zero polynomial vanishes for ANY divisor). -/
theorem dv4Supp_zero_eq_top {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ₂ : Polynomial O) (u₂ : ℕ) {ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (Ψ₃ : Polynomial O) (u₃ : ℕ)
    {ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃) (Ψ₄ : Polynomial O) (u₄ : ℕ) {ℓ₄ : ℕ} (hℓ₄ : 0 < ℓ₄) :
    dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ (0 : Polynomial O) u₄ ℓ₄ = ⊤ := by
  rw [dv4Supp]
  simp only [Polynomial.natDegree_zero, Nat.zero_add, Finset.range_one, Finset.inf_singleton]
  rw [dv4Pin, C118a.dev_zero_any, dv4Hgt, dv3Supp_zero_eq_top L Ψ₂ u₂ hℓ₂ Ψ₃ u₃ hℓ₃,
    C118a.smul_top_pos hℓ₄, top_add]

/-- `dv4Supp` read over any range past the degree (mirror of C136d0's
`dv3Supp_eq_inf_range`; the added abscissae have `dv4Pin = ⊤` by `dv4Pin_top_of_gt`). -/
theorem dv4Supp_eq_inf_range {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ₂ : Polynomial O) (u₂ : ℕ) {ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (Ψ₃ : Polynomial O) (u₃ : ℕ)
    {ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃) {Ψ₄ : Polynomial O} (hΨ₄ : Ψ₄.Monic)
    (hΨ₄d : 0 < Ψ₄.natDegree) {u₄ ℓ₄ : ℕ} (hℓ₄ : 0 < ℓ₄)
    (f : Polynomial O) {M : ℕ} (hM : f.natDegree < M) :
    dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄
      = (Finset.range M).inf
          (fun j => ℓ₄ • dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f j + (u₄ * j : ℕ∞)) := by
  rw [dv4Supp]
  have h := C118a.inf_range_ext (m := f.natDegree) (M := M - 1) (by omega)
      (fun j => ℓ₄ • dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f j + (u₄ * j : ℕ∞)) (fun i hi1 _ => by
        rw [dv4Pin_top_of_gt L Ψ₂ u₂ hℓ₂ Ψ₃ u₃ hℓ₃ hΨ₄ hΨ₄d f hi1,
          C118a.smul_top_pos hℓ₄, top_add])
  rw [h, show M - 1 + 1 = M by omega]

/-- a nonzero polynomial has finite `dv4Supp` (mirror of C136d0's
`dv3Supp_ne_top_of_ne_zero`; the per-slot step is C136d0's `dv3Supp_ne_top_of_ne_zero`
applied at `dv4Hgt`'s underlying `dv3Supp`, rather than a fresh degree argument). -/
theorem dv4Supp_ne_top_of_ne_zero {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {Ψ₂ : Polynomial O} (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree) (u₂ ℓ₂ : ℕ)
    {Ψ₃ : Polynomial O} (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree) (u₃ ℓ₃ : ℕ)
    {Ψ₄ : Polynomial O} (hΨ₄ : Ψ₄.Monic) (hΨ₄d : 0 < Ψ₄.natDegree) (u₄ ℓ₄ : ℕ)
    {f : Polynomial O} (hf : f ≠ 0) : dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄ ≠ ⊤ := by
  intro htop
  rw [dv4Supp] at htop
  have hall : ∀ j ∈ Finset.range (f.natDegree + 1), dev Ψ₄ f j = 0 := by
    intro j hj
    have hle := Finset.inf_le
      (f := fun j => ℓ₄ • dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f j + (u₄ * j : ℕ∞)) hj
    rw [htop] at hle
    have hterm : ℓ₄ • dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f j + ((u₄ : ℕ∞) * (j : ℕ∞)) = ⊤ :=
      top_le_iff.mp hle
    have hleft : ℓ₄ • dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f j = ⊤ := by
      rcases WithTop.add_eq_top.mp hterm with h | h
      · exact h
      · rw [← Nat.cast_mul] at h
        exact absurd h (ENat.coe_ne_top _)
    have hdvtop : dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f j = ⊤ := by
      by_contra hx
      rw [nsmul_eq_mul] at hleft
      exact WithTop.mul_ne_top (ENat.coe_ne_top ℓ₄) hx hleft
    rw [dv4Pin, dv4Hgt] at hdvtop
    by_contra hne
    exact absurd hdvtop (dv3Supp_ne_top_of_ne_zero L hΨ₂ hΨ₂d u₂ ℓ₂ hΨ₃ hΨ₃d u₃ ℓ₃ hne)
  have hrec : ∑ j ∈ Finset.range (f.natDegree + 1), dev Ψ₄ f j * Ψ₄ ^ j = f :=
    sum_dev_eq hΨ₄ hΨ₄d f
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_mul_of_pos_right _ hΨ₄d))
  refine hf ?_
  rw [← hrec]
  exact Finset.sum_eq_zero fun j hj => by rw [hall j hj, zero_mul]

/-- ★ **the `dv4Supp` ultrametric inequality** (mirror of C136d0's
`min_dv3Supp_le_dv3Supp_add`): per-slot, `dev` is additive (B32a) and `dv4Hgt` is
ultrametric (C136d0's `min_dv3Supp_le_dv3Supp_add`, one level down). -/
theorem min_dv4Supp_le_dv4Supp_add {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {Ψ₂ : Polynomial O} (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree) {u₂ ℓ₂ : ℕ}
    (hℓ₂ : 0 < ℓ₂) {Ψ₃ : Polynomial O} (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree)
    {u₃ ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃) {Ψ₄ : Polynomial O} (hΨ₄ : Ψ₄.Monic)
    (hΨ₄d : 0 < Ψ₄.natDegree) {u₄ ℓ₄ : ℕ} (hℓ₄ : 0 < ℓ₄) (f g : Polynomial O) :
    min (dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄) (dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄)
      ≤ dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ (f + g) u₄ ℓ₄ := by
  set M := max (max f.natDegree g.natDegree) (f + g).natDegree + 1 with hMdef
  rw [dv4Supp_eq_inf_range L Ψ₂ u₂ hℓ₂ Ψ₃ u₃ hℓ₃ hΨ₄ hΨ₄d hℓ₄ f (M := M) (by omega),
    dv4Supp_eq_inf_range L Ψ₂ u₂ hℓ₂ Ψ₃ u₃ hℓ₃ hΨ₄ hΨ₄d hℓ₄ g (M := M) (by omega),
    dv4Supp_eq_inf_range L Ψ₂ u₂ hℓ₂ Ψ₃ u₃ hℓ₃ hΨ₄ hΨ₄d hℓ₄ (f + g) (M := M) (by omega)]
  refine Finset.le_inf fun j hj => ?_
  have hmono : Monotone fun x : ℕ∞ => ℓ₄ • x + ((u₄ : ℕ∞) * (j : ℕ∞)) := by
    intro x y hxy
    exact add_le_add (nsmul_le_nsmul_right hxy ℓ₄) le_rfl
  have hs : min (dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f j) (dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g j)
      ≤ dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ (f + g) j := by
    rw [dv4Pin, dv4Pin, dv4Pin, dev_add_of_monic hΨ₄ f g j, dv4Hgt, dv4Hgt, dv4Hgt]
    exact min_dv3Supp_le_dv3Supp_add L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ (dev Ψ₄ f j) (dev Ψ₄ g j)
  calc min ((Finset.range M).inf fun i => ℓ₄ • dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f i + (u₄ * i : ℕ∞))
        ((Finset.range M).inf fun i => ℓ₄ • dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g i + (u₄ * i : ℕ∞))
      ≤ min (ℓ₄ • dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f j + (u₄ * j : ℕ∞))
        (ℓ₄ • dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g j + (u₄ * j : ℕ∞)) :=
        min_le_min (Finset.inf_le hj) (Finset.inf_le hj)
    _ = ℓ₄ • min (dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f j) (dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g j)
          + (u₄ * j : ℕ∞) :=
        (hmono.map_min).symm
    _ ≤ ℓ₄ • dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ (f + g) j + (u₄ * j : ℕ∞) := hmono hs

/-- `dv4Supp` is negation-invariant (per-slot mirror of C136d0's `dv3Supp_neg`, through
B39b's `dev_neg` and C136d0's `dv3Supp_neg` at `dv4Hgt`'s underlying `dv3Supp`). -/
theorem dv4Supp_neg {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {Ψ₂ : Polynomial O} (hΨ₂ : Ψ₂.Monic) (u₂ ℓ₂ : ℕ) {Ψ₃ : Polynomial O} (hΨ₃ : Ψ₃.Monic)
    (u₃ ℓ₃ : ℕ) {Ψ₄ : Polynomial O} (hΨ₄ : Ψ₄.Monic) (f : Polynomial O) (u₄ ℓ₄ : ℕ) :
    dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ (-f) u₄ ℓ₄
      = dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄ := by
  rw [dv4Supp, dv4Supp, Polynomial.natDegree_neg]
  refine Finset.inf_congr rfl fun j _ => ?_
  rw [dv4Pin, dv4Pin, dev_neg hΨ₄, dv4Hgt, dv4Hgt, dv3Supp_neg L hΨ₂ u₂ ℓ₂ hΨ₃ _ u₃ ℓ₃]

/-- the strict half of equality off ties: the lower side wins outright (mirror of
C136d0's `dv3Supp_add_eq_of_lt`). -/
theorem dv4Supp_add_eq_of_lt {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {Ψ₂ : Polynomial O} (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree) {u₂ ℓ₂ : ℕ}
    (hℓ₂ : 0 < ℓ₂) {Ψ₃ : Polynomial O} (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree)
    {u₃ ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃) {Ψ₄ : Polynomial O} (hΨ₄ : Ψ₄.Monic)
    (hΨ₄d : 0 < Ψ₄.natDegree) {u₄ ℓ₄ : ℕ} (hℓ₄ : 0 < ℓ₄) {f g : Polynomial O}
    (hlt : dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄
      < dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄) :
    dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ (f + g) u₄ ℓ₄
      = dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄ := by
  have hge : dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄
      ≤ dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ (f + g) u₄ ℓ₄ := by
    have h := min_dv4Supp_le_dv4Supp_add (u₂ := u₂) (u₃ := u₃) (u₄ := u₄) L hΨ₂ hΨ₂d hℓ₂
      hΨ₃ hΨ₃d hℓ₃ hΨ₄ hΨ₄d hℓ₄ f g
    rwa [min_eq_left hlt.le] at h
  refine le_antisymm ?_ hge
  have h2 : min (dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ (f + g) u₄ ℓ₄)
      (dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄)
      ≤ dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄ := by
    have h3 := min_dv4Supp_le_dv4Supp_add (u₂ := u₂) (u₃ := u₃) (u₄ := u₄) L hΨ₂ hΨ₂d hℓ₂
      hΨ₃ hΨ₃d hℓ₃ hΨ₄ hΨ₄d hℓ₄ (f + g) (-g)
    rw [dv4Supp_neg L hΨ₂ u₂ ℓ₂ hΨ₃ u₃ ℓ₃ hΨ₄] at h3
    calc min (dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ (f + g) u₄ ℓ₄)
          (dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄)
        ≤ dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ ((f + g) + -g) u₄ ℓ₄ := h3
      _ = dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄ := by rw [add_neg_cancel_right]
  by_contra hcon
  exact absurd h2 (not_le.mpr (lt_min (not_le.mp hcon) hlt))

/-- ★ **the `dv4Supp` ultrametric EQUALITY OFF TIES** (mirror of C136d0's
`dv3Supp_add_eq`, the E.10 `hgt_add_eq` law three levels up). -/
theorem dv4Supp_add_eq {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {Ψ₂ : Polynomial O} (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree) {u₂ ℓ₂ : ℕ}
    (hℓ₂ : 0 < ℓ₂) {Ψ₃ : Polynomial O} (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree)
    {u₃ ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃) {Ψ₄ : Polynomial O} (hΨ₄ : Ψ₄.Monic)
    (hΨ₄d : 0 < Ψ₄.natDegree) {u₄ ℓ₄ : ℕ} (hℓ₄ : 0 < ℓ₄) {f g : Polynomial O}
    (hne : dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄
      ≠ dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄) :
    dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ (f + g) u₄ ℓ₄
      = min (dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄)
          (dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄) := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [min_eq_left h.le]
    exact dv4Supp_add_eq_of_lt L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ hΨ₄ hΨ₄d hℓ₄ h
  · rw [min_eq_right h.le, add_comm]
    exact dv4Supp_add_eq_of_lt L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ hΨ₄ hΨ₄d hℓ₄ h

end Generic

/-! ## Part 2 — D4-00 (endpoint face): the `dv4Supp` outer endpoint/minimizer bank

Mirror of C136d0's Part 3 (itself the mirror of C132nv2's Parts 1–3), one level up,
leaving ONE explicit hypothesis, `Dv4ResSurv` — the μ₄-residual survival for `Ψ₄`-digit
products, playing exactly the role `Dv3ResSurv` played one level down.  It is discharged
in Part 5 (row D4-02) for the S2 numerals `(Ψ₄, u₄, ℓ₄) = (g16, 171, 1)`; every other
declaration here is UNCONDITIONAL, parameter-free (no S2 numeral), and mirrors its
`dv3Supp` counterpart by the substitution `dv3Hgt L Ψ₂ u₂ ℓ₂ ↦ dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃`,
`Ψ₃ ↦ Ψ₄`, `Dv3OnSide ↦ Dv4OnSide`, `dv3SideSet/dv3SideMin ↦ dv4SideSet/dv4SideMin`. -/

section GenericEndpoint

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **The on-side predicate at the `dv4`-level.**  The abscissa `j` attains the cleared
level-4 support at slope `−u₄/ℓ₄`, AND its level-4 pin is finite (mirror of C136d0's
`Dv3OnSide`, one level up). -/
def Dv4OnSide {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ₂ : Polynomial O) (u₂ ℓ₂ : ℕ) (Ψ₃ : Polynomial O) (u₃ ℓ₃ : ℕ)
    (Ψ₄ f : Polynomial O) (u₄ ℓ₄ j : ℕ) : Prop :=
  dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄
      = ℓ₄ • dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f j + (u₄ * j : ℕ∞) ∧
    dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f j ≠ ⊤

/-- **The on-side abscissae, as a `Finset`** (mirror of C136d0's `dv3SideSet`). -/
noncomputable def dv4SideSet {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ₂ : Polynomial O) (u₂ ℓ₂ : ℕ) (Ψ₃ : Polynomial O) (u₃ ℓ₃ : ℕ)
    (Ψ₄ f : Polynomial O) (u₄ ℓ₄ : ℕ) : Finset ℕ :=
  open Classical in
  (Finset.range (f.natDegree + 1)).filter
    (fun j => Dv4OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄ j)

/-- **The side's left endpoint** (mirror of C136d0's `dv3SideMin`). -/
noncomputable def dv4SideMin {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ₂ : Polynomial O) (u₂ ℓ₂ : ℕ) (Ψ₃ : Polynomial O) (u₃ ℓ₃ : ℕ)
    (Ψ₄ f : Polynomial O) (u₄ ℓ₄ : ℕ)
    (h : (dv4SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄).Nonempty) : ℕ :=
  (dv4SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄).min' h

variable {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
  {Ψ₂ Ψ₃ Ψ₄ : Polynomial O}

/-- Membership in `dv4SideSet` projects to the on-side predicate. -/
theorem dv4OnSide_of_mem_dv4SideSet {u₂ ℓ₂ u₃ ℓ₃ : ℕ} {f : Polynomial O} {u₄ ℓ₄ j : ℕ}
    (hj : j ∈ dv4SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄) :
    Dv4OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄ j := by
  classical
  exact (Finset.mem_filter.mp (show j ∈ (Finset.range (f.natDegree + 1)).filter
    (Dv4OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄) from hj)).2

/-- An on-side slot lies in `dv4SideSet`. -/
theorem mem_dv4SideSet_of_dv4OnSide {u₂ ℓ₂ u₃ : ℕ} (hℓ₂ : 0 < ℓ₂) {ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃)
    (hΨ₄ : Ψ₄.Monic) (hΨ₄d : 0 < Ψ₄.natDegree) {f : Polynomial O} {u₄ ℓ₄ j : ℕ}
    (hj : Dv4OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄ j) :
    j ∈ dv4SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄ := by
  classical
  simp only [dv4SideSet, Finset.mem_filter, Finset.mem_range]
  refine ⟨?_, hj⟩
  by_contra hdeg
  exact hj.2 (dv4Pin_top_of_gt L Ψ₂ u₂ hℓ₂ Ψ₃ u₃ hℓ₃ hΨ₄ hΨ₄d f (by omega))

/-- **The chosen minimizer is on-side.** -/
theorem dv4OnSide_dv4SideMin {u₂ ℓ₂ u₃ ℓ₃ : ℕ} (f : Polynomial O) (u₄ ℓ₄ : ℕ)
    (hne : (dv4SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄).Nonempty) :
    Dv4OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄
      (dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄ hne) :=
  dv4OnSide_of_mem_dv4SideSet L (Finset.min'_mem _ hne)

/-- **The chosen minimizer is the LEFTMOST on-side slot.** -/
theorem dv4SideMin_le_of_dv4OnSide {u₂ ℓ₂ u₃ : ℕ} (hℓ₂ : 0 < ℓ₂) {ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃)
    (hΨ₄ : Ψ₄.Monic) (hΨ₄d : 0 < Ψ₄.natDegree) {f : Polynomial O} {u₄ ℓ₄ j : ℕ}
    (hne : (dv4SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄).Nonempty)
    (hj : Dv4OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄ j) :
    dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄ hne ≤ j :=
  Finset.min'_le _ _ (mem_dv4SideSet_of_dv4OnSide L hℓ₂ hℓ₃ hΨ₄ hΨ₄d hj)

/-- Every slot strictly left of the chosen minimizer is strictly off the side. -/
theorem not_dv4OnSide_of_lt_dv4SideMin {u₂ ℓ₂ u₃ : ℕ} (hℓ₂ : 0 < ℓ₂) {ℓ₃ : ℕ}
    (hℓ₃ : 0 < ℓ₃) (hΨ₄ : Ψ₄.Monic) (hΨ₄d : 0 < Ψ₄.natDegree) {f : Polynomial O}
    {u₄ ℓ₄ j : ℕ} (hne : (dv4SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄).Nonempty)
    (hlt : j < dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄ hne) :
    ¬ Dv4OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄ j :=
  fun hj => absurd (dv4SideMin_le_of_dv4OnSide L hℓ₂ hℓ₃ hΨ₄ hΨ₄d hne hj) (by omega)

/-- **The unique lowest convolution pair.** -/
theorem dv4OnSide_endpoint_unique {u₂ ℓ₂ u₃ : ℕ} (hℓ₂ : 0 < ℓ₂) {ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃)
    (hΨ₄ : Ψ₄.Monic) (hΨ₄d : 0 < Ψ₄.natDegree) {g z : Polynomial O} {u₄ ℓ₄ j i : ℕ}
    (hng : (dv4SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄).Nonempty)
    (hnz : (dv4SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z u₄ ℓ₄).Nonempty)
    (hsum : j + i = dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄ hng
      + dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z u₄ ℓ₄ hnz)
    (hj : Dv4OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄ j)
    (hi : Dv4OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z u₄ ℓ₄ i) :
    j = dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄ hng
      ∧ i = dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z u₄ ℓ₄ hnz := by
  have h1 := dv4SideMin_le_of_dv4OnSide L hℓ₂ hℓ₃ hΨ₄ hΨ₄d hng hj
  have h2 := dv4SideMin_le_of_dv4OnSide L hℓ₂ hℓ₃ hΨ₄ hΨ₄d hnz hi
  omega

/-- The height at the chosen minimizer is a natural number. -/
theorem exists_dv4SideMin_height {u₂ ℓ₂ u₃ ℓ₃ : ℕ} (f : Polynomial O) (u₄ ℓ₄ : ℕ)
    (hne : (dv4SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄).Nonempty) :
    ∃ H : ℕ, dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f
      (dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄ hne) = (H : ℕ∞) :=
  ENat.ne_top_iff_exists.1 (dv4OnSide_dv4SideMin L f u₄ ℓ₄ hne).2 |>.imp fun _ h => h.symm

/-- **The support value, read off any on-side slot.** -/
theorem dv4Supp_eq_of_dv4OnSide {u₂ ℓ₂ u₃ ℓ₃ : ℕ} {f : Polynomial O} {u₄ ℓ₄ j H : ℕ}
    (hH : dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f j = (H : ℕ∞))
    (hj : Dv4OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄ j) :
    dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄ = ((ℓ₄ * H + u₄ * j : ℕ) : ℕ∞) := by
  rw [hj.1, hH, weight_read]

/-- **The support infimum lies below the weighted pin at every abscissa** (mirror of
C136d0's `dv3Supp_le_term`, including past-degree abscissae via `dv4Pin_top_of_gt`). -/
theorem dv4Supp_le_term (hΨ₄ : Ψ₄.Monic) (hΨ₄d : 0 < Ψ₄.natDegree) (u₂ : ℕ) {ℓ₂ : ℕ}
    (hℓ₂ : 0 < ℓ₂) (u₃ : ℕ) {ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃) (f : Polynomial O) (u₄ : ℕ)
    {ℓ₄ : ℕ} (hℓ₄ : 0 < ℓ₄) (j : ℕ) :
    dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄
      ≤ ℓ₄ • dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f j + (u₄ * j : ℕ∞) := by
  by_cases hj : j ≤ f.natDegree
  · unfold dv4Supp
    exact Finset.inf_le (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  · rw [dv4Pin_top_of_gt L Ψ₂ u₂ hℓ₂ Ψ₃ u₃ hℓ₃ hΨ₄ hΨ₄d f (by omega),
      C118a.smul_top_pos hℓ₄, top_add]
    exact le_top

/-- **The support line lies below the level-4 polygon**, ℕ-cleared. -/
theorem le_dv4Weight (hΨ₄ : Ψ₄.Monic) (hΨ₄d : 0 < Ψ₄.natDegree) {u₂ ℓ₂ u₃ : ℕ}
    (hℓ₂ : 0 < ℓ₂) {ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃) {f : Polynomial O} {u₄ ℓ₄ : ℕ} (hℓ₄ : 0 < ℓ₄)
    {S H j : ℕ} (hS : dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄ = (S : ℕ∞))
    (hH : dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f j = (H : ℕ∞)) :
    S ≤ ℓ₄ * H + u₄ * j := by
  have h := dv4Supp_le_term (Ψ₂ := Ψ₂) (Ψ₃ := Ψ₃) L hΨ₄ hΨ₄d u₂ hℓ₂ u₃ hℓ₃ f u₄ hℓ₄ j
  rw [hS, hH, weight_read] at h
  exact_mod_cast h

/-- **Off the side the support line is strictly below the polygon.** -/
theorem lt_dv4Weight (hΨ₄ : Ψ₄.Monic) (hΨ₄d : 0 < Ψ₄.natDegree) {u₂ ℓ₂ u₃ : ℕ}
    (hℓ₂ : 0 < ℓ₂) {ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃) {f : Polynomial O} {u₄ ℓ₄ : ℕ} (hℓ₄ : 0 < ℓ₄)
    {S H j : ℕ} (hS : dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄ = (S : ℕ∞))
    (hH : dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f j = (H : ℕ∞))
    (hns : ¬ Dv4OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄ j) : S < ℓ₄ * H + u₄ * j := by
  rcases eq_or_lt_of_le (le_dv4Weight L hΨ₄ hΨ₄d hℓ₂ hℓ₃ hℓ₄ hS hH) with heq | hlt
  · refine absurd ⟨?_, hH ▸ ENat.coe_ne_top H⟩ hns
    rw [hS, hH, weight_read, ← heq]
  · exact hlt

/-! ### The ONE explicit hypothesis: `Dv4ResSurv` (mirror of C136d0's `Dv3ResSurv`)

Every `dev Ψ₄` output has degree `< Ψ₄.natDegree` UNCONDITIONALLY (B03's `degree_dev_lt`),
so a digit PRODUCT `A * B` has degree `< 2 * Ψ₄.natDegree` — at most two `Ψ₄`-development
slots, `0` (the reduced remainder) and `1` (the bare quotient).  `Dv4ResSurv` packages
exactly the two facts the pricing bank needs about those two slots, in the digit heights
alone: the EXACT value at the reduced slot (row D4-02's content) and the STRICT slot-`1`
carry bound.  Discharged for `(Ψ₄, u₄, ℓ₄) = (g16, 171, 1)` in Part 5 below. -/

/-- **THE ONE explicit hypothesis ("μ₄-residual survival")**: for any two
`Ψ₄`-digit-bounded `A, B` of known `dv4Hgt` heights, their product's `Ψ₄`-reduced value is
EXACTLY the sum of the heights, and its carry (slot `1`) value is bounded STRICTLY above
the line. -/
def Dv4ResSurv {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ₂ : Polynomial O) (u₂ ℓ₂ : ℕ) (Ψ₃ : Polynomial O) (u₃ ℓ₃ : ℕ)
    (Ψ₄ : Polynomial O) (u₄ ℓ₄ : ℕ) : Prop :=
  ∀ ⦃A B : Polynomial O⦄ ⦃Ha Hb : ℕ⦄,
    A.natDegree < Ψ₄.natDegree → B.natDegree < Ψ₄.natDegree →
    dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ A = (Ha : ℕ∞) →
    dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ B = (Hb : ℕ∞) →
    dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ (dev Ψ₄ (A * B) 0) = ((Ha + Hb : ℕ) : ℕ∞) ∧
    ℓ₄ • ((Ha + Hb : ℕ) : ℕ∞) + 1
      ≤ ℓ₄ • dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ (dev Ψ₄ (A * B) 1) + (u₄ : ℕ∞)

/-- A product of two outer digits is SHORT (degree `< 2 · deg Ψ₄`; mirror of C136d0's
`natDegree_dev3_mul_lt`). -/
theorem natDegree_dev4_mul_lt (hΨ₄ : Ψ₄.Monic) (hΨ₄d : 0 < Ψ₄.natDegree)
    {g z : Polynomial O} {j i : ℕ} (hgj : dev Ψ₄ g j ≠ 0) (hzi : dev Ψ₄ z i ≠ 0) :
    (dev Ψ₄ g j * dev Ψ₄ z i).natDegree < 2 * Ψ₄.natDegree := by
  rw [natDegree_mul hgj hzi]
  have h1 : (dev Ψ₄ g j).natDegree < Ψ₄.natDegree :=
    natDegree_lt_natDegree hgj (degree_dev_lt hΨ₄ hΨ₄d g j)
  have h2 : (dev Ψ₄ z i).natDegree < Ψ₄.natDegree :=
    natDegree_lt_natDegree hzi (degree_dev_lt hΨ₄ hΨ₄d z i)
  omega

/-- ★ **The convolution term estimate, `≥`-direction, level four** (mirror of C136d0's
`le_line_dev3_term`): every term of the outer convolution of `g · z` weighs at least
`Sg + Sz` at every slot `J`.  UNCONDITIONAL beyond `Dv4ResSurv`. -/
theorem le_line_dev4_term (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree) {u₂ ℓ₂ : ℕ}
    (hℓ₂ : 0 < ℓ₂) (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree) {u₃ ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃)
    (hΨ₄ : Ψ₄.Monic) (hΨ₄d : 0 < Ψ₄.natDegree) {u₄ ℓ₄ : ℕ} (hℓ₄ : 0 < ℓ₄)
    (hSurv4 : Dv4ResSurv L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ u₄ ℓ₄) {g z : Polynomial O} {Sg Sz : ℕ}
    (hSg : dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄ = (Sg : ℕ∞))
    (hSz : dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z u₄ ℓ₄ = (Sz : ℕ∞)) (J j i : ℕ) :
    ((Sg + Sz : ℕ) : ℕ∞)
      ≤ ℓ₄ • dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ (dev Ψ₄ (dev Ψ₄ g j * dev Ψ₄ z i * Ψ₄ ^ (j + i)) J)
        + (u₄ * J : ℕ∞) := by
  by_cases hgj : dev Ψ₄ g j = 0
  · rw [hgj, zero_mul, zero_mul, dev_of_zero, dv4Hgt_zero L Ψ₂ u₂ hℓ₂ Ψ₃ u₃ hℓ₃,
      C118a.smul_top_pos hℓ₄, top_add]
    exact le_top
  by_cases hzi : dev Ψ₄ z i = 0
  · rw [hzi, mul_zero, zero_mul, dev_of_zero, dv4Hgt_zero L Ψ₂ u₂ hℓ₂ Ψ₃ u₃ hℓ₃,
      C118a.smul_top_pos hℓ₄, top_add]
    exact le_top
  have hHa' : dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g j ≠ ⊤ := by
    rw [dv4Pin, dv4Hgt]
    exact dv3Supp_ne_top_of_ne_zero L hΨ₂ hΨ₂d u₂ ℓ₂ hΨ₃ hΨ₃d u₃ ℓ₃ hgj
  have hHb' : dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z i ≠ ⊤ := by
    rw [dv4Pin, dv4Hgt]
    exact dv3Supp_ne_top_of_ne_zero L hΨ₂ hΨ₂d u₂ ℓ₂ hΨ₃ hΨ₃d u₃ ℓ₃ hzi
  obtain ⟨Ha, hHa⟩ := ENat.ne_top_iff_exists.1 hHa'
  obtain ⟨Hb, hHb⟩ := ENat.ne_top_iff_exists.1 hHb'
  have h1 : Sg ≤ ℓ₄ * Ha + u₄ * j := le_dv4Weight L hΨ₄ hΨ₄d hℓ₂ hℓ₃ hℓ₄ hSg hHa.symm
  have h2 : Sz ≤ ℓ₄ * Hb + u₄ * i := le_dv4Weight L hΨ₄ hΨ₄d hℓ₂ hℓ₃ hℓ₄ hSz hHb.symm
  rcases Nat.lt_or_ge J (j + i) with hJlt | hJge
  · rw [dev_mul_pow_of_lt hΨ₄ (j + i) _ J hJlt, dv4Hgt_zero L Ψ₂ u₂ hℓ₂ Ψ₃ u₃ hℓ₃,
      C118a.smul_top_pos hℓ₄, top_add]
    exact le_top
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hJge
  rw [dev_mul_pow hΨ₄ (j + i) _ s]
  have hAdeg : (dev Ψ₄ g j).natDegree < Ψ₄.natDegree :=
    natDegree_lt_natDegree hgj (degree_dev_lt hΨ₄ hΨ₄d g j)
  have hBdeg : (dev Ψ₄ z i).natDegree < Ψ₄.natDegree :=
    natDegree_lt_natDegree hzi (degree_dev_lt hΨ₄ hΨ₄d z i)
  have hnat : Sg + Sz ≤ ℓ₄ * (Ha + Hb) + u₄ * (j + i) := by
    calc Sg + Sz ≤ (ℓ₄ * Ha + u₄ * j) + (ℓ₄ * Hb + u₄ * i) := Nat.add_le_add h1 h2
      _ = ℓ₄ * (Ha + Hb) + u₄ * (j + i) := by ring
  match s with
  | 0 =>
    have hval := (hSurv4 hAdeg hBdeg hHa.symm hHb.symm).1
    rw [Nat.add_zero, hval]
    have : ((Sg + Sz : ℕ) : ℕ∞) ≤ ((ℓ₄ * (Ha + Hb) + u₄ * (j + i) : ℕ) : ℕ∞) := by
      exact_mod_cast hnat
    refine le_trans this (le_of_eq ?_)
    rw [nsmul_eq_mul]; push_cast; ring
  | 1 =>
    have hval := (hSurv4 hAdeg hBdeg hHa.symm hHb.symm).2
    have hweak : ℓ₄ • ((Ha + Hb : ℕ) : ℕ∞)
        ≤ ℓ₄ • dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ (dev Ψ₄ (dev Ψ₄ g j * dev Ψ₄ z i) 1)
          + (u₄ : ℕ∞) :=
      le_trans le_self_add hval
    have hstep : ((Sg + Sz : ℕ) : ℕ∞) ≤ ℓ₄ • ((Ha + Hb : ℕ) : ℕ∞) + (u₄ * (j + i) : ℕ∞) := by
      rw [nsmul_eq_mul]
      exact_mod_cast hnat
    refine le_trans hstep (le_trans (add_le_add hweak le_rfl) (le_of_eq ?_))
    push_cast; ring
  | (s + 2) =>
    rw [dev_eq_zero_of_lt hΨ₄ hΨ₄d _ (s + 2) (by
      have := natDegree_dev4_mul_lt hΨ₄ hΨ₄d hgj hzi
      nlinarith), dv4Hgt_zero L Ψ₂ u₂ hℓ₂ Ψ₃ u₃ hℓ₃, C118a.smul_top_pos hℓ₄, top_add]
    exact le_top

/-- ★ **The strict convolution term estimate, level four** (mirror of C136d0's
`lt_line_dev3_term`, the survival direction): every term of the outer convolution OTHER
than an exact-slot on-side pair weighs at least `Sg + Sz + 1`. -/
theorem lt_line_dev4_term (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree) {u₂ ℓ₂ : ℕ}
    (hℓ₂ : 0 < ℓ₂) (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree) {u₃ ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃)
    (hΨ₄ : Ψ₄.Monic) (hΨ₄d : 0 < Ψ₄.natDegree) {u₄ ℓ₄ : ℕ} (hℓ₄ : 0 < ℓ₄)
    (hSurv4 : Dv4ResSurv L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ u₄ ℓ₄) {g z : Polynomial O} {Sg Sz : ℕ}
    (hSg : dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄ = (Sg : ℕ∞))
    (hSz : dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z u₄ ℓ₄ = (Sz : ℕ∞)) {J j i : ℕ}
    (hbad : ¬ (j + i = J ∧ Dv4OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄ j
      ∧ Dv4OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z u₄ ℓ₄ i)) :
    ((Sg + Sz + 1 : ℕ) : ℕ∞)
      ≤ ℓ₄ • dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ (dev Ψ₄ (dev Ψ₄ g j * dev Ψ₄ z i * Ψ₄ ^ (j + i)) J)
        + (u₄ * J : ℕ∞) := by
  by_cases hgj : dev Ψ₄ g j = 0
  · rw [hgj, zero_mul, zero_mul, dev_of_zero, dv4Hgt_zero L Ψ₂ u₂ hℓ₂ Ψ₃ u₃ hℓ₃,
      C118a.smul_top_pos hℓ₄, top_add]
    exact le_top
  by_cases hzi : dev Ψ₄ z i = 0
  · rw [hzi, mul_zero, zero_mul, dev_of_zero, dv4Hgt_zero L Ψ₂ u₂ hℓ₂ Ψ₃ u₃ hℓ₃,
      C118a.smul_top_pos hℓ₄, top_add]
    exact le_top
  have hHa' : dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g j ≠ ⊤ := by
    rw [dv4Pin, dv4Hgt]
    exact dv3Supp_ne_top_of_ne_zero L hΨ₂ hΨ₂d u₂ ℓ₂ hΨ₃ hΨ₃d u₃ ℓ₃ hgj
  have hHb' : dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z i ≠ ⊤ := by
    rw [dv4Pin, dv4Hgt]
    exact dv3Supp_ne_top_of_ne_zero L hΨ₂ hΨ₂d u₂ ℓ₂ hΨ₃ hΨ₃d u₃ ℓ₃ hzi
  obtain ⟨Ha, hHa⟩ := ENat.ne_top_iff_exists.1 hHa'
  obtain ⟨Hb, hHb⟩ := ENat.ne_top_iff_exists.1 hHb'
  have hAdeg : (dev Ψ₄ g j).natDegree < Ψ₄.natDegree :=
    natDegree_lt_natDegree hgj (degree_dev_lt hΨ₄ hΨ₄d g j)
  have hBdeg : (dev Ψ₄ z i).natDegree < Ψ₄.natDegree :=
    natDegree_lt_natDegree hzi (degree_dev_lt hΨ₄ hΨ₄d z i)
  rcases Nat.lt_or_ge J (j + i) with hJlt | hJge
  · rw [dev_mul_pow_of_lt hΨ₄ (j + i) _ J hJlt, dv4Hgt_zero L Ψ₂ u₂ hℓ₂ Ψ₃ u₃ hℓ₃,
      C118a.smul_top_pos hℓ₄, top_add]
    exact le_top
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hJge
  rw [dev_mul_pow hΨ₄ (j + i) _ s]
  match s with
  | 0 =>
    have hoff : ¬ Dv4OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄ j
        ∨ ¬ Dv4OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z u₄ ℓ₄ i := by
      by_contra hcon
      push Not at hcon
      exact hbad ⟨by omega, hcon.1, hcon.2⟩
    have hstrict : Sg + Sz + 1 ≤ ℓ₄ * (Ha + Hb) + u₄ * (j + i) := by
      rcases hoff with hng | hnz
      · have h1 : Sg < ℓ₄ * Ha + u₄ * j :=
          lt_dv4Weight L hΨ₄ hΨ₄d hℓ₂ hℓ₃ hℓ₄ hSg hHa.symm hng
        have h2 : Sz ≤ ℓ₄ * Hb + u₄ * i := le_dv4Weight L hΨ₄ hΨ₄d hℓ₂ hℓ₃ hℓ₄ hSz hHb.symm
        calc Sg + Sz + 1 ≤ (ℓ₄ * Ha + u₄ * j) + (ℓ₄ * Hb + u₄ * i) := by omega
          _ = ℓ₄ * (Ha + Hb) + u₄ * (j + i) := by ring
      · have h1 : Sg ≤ ℓ₄ * Ha + u₄ * j := le_dv4Weight L hΨ₄ hΨ₄d hℓ₂ hℓ₃ hℓ₄ hSg hHa.symm
        have h2 : Sz < ℓ₄ * Hb + u₄ * i :=
          lt_dv4Weight L hΨ₄ hΨ₄d hℓ₂ hℓ₃ hℓ₄ hSz hHb.symm hnz
        calc Sg + Sz + 1 ≤ (ℓ₄ * Ha + u₄ * j) + (ℓ₄ * Hb + u₄ * i) := by omega
          _ = ℓ₄ * (Ha + Hb) + u₄ * (j + i) := by ring
    have hval := (hSurv4 hAdeg hBdeg hHa.symm hHb.symm).1
    rw [Nat.add_zero, hval]
    have hcast : ((Sg + Sz + 1 : ℕ) : ℕ∞) ≤ ((ℓ₄ * (Ha + Hb) + u₄ * (j + i) : ℕ) : ℕ∞) := by
      exact_mod_cast hstrict
    refine le_trans hcast (le_of_eq ?_)
    rw [nsmul_eq_mul]; push_cast; ring
  | 1 =>
    have h1 : Sg ≤ ℓ₄ * Ha + u₄ * j := le_dv4Weight L hΨ₄ hΨ₄d hℓ₂ hℓ₃ hℓ₄ hSg hHa.symm
    have h2 : Sz ≤ ℓ₄ * Hb + u₄ * i := le_dv4Weight L hΨ₄ hΨ₄d hℓ₂ hℓ₃ hℓ₄ hSz hHb.symm
    have hval := (hSurv4 hAdeg hBdeg hHa.symm hHb.symm).2
    have hstep : ((Sg + Sz + 1 : ℕ) : ℕ∞)
        ≤ (ℓ₄ • ((Ha + Hb : ℕ) : ℕ∞) + 1) + (u₄ * (j + i) : ℕ∞) := by
      rw [nsmul_eq_mul]
      have hnat : Sg + Sz + 1 ≤ (ℓ₄ * (Ha + Hb) + 1) + u₄ * (j + i) := by
        have h3 : Sg + Sz ≤ (ℓ₄ * Ha + u₄ * j) + (ℓ₄ * Hb + u₄ * i) := Nat.add_le_add h1 h2
        have h4 : (ℓ₄ * Ha + u₄ * j) + (ℓ₄ * Hb + u₄ * i)
            = ℓ₄ * (Ha + Hb) + u₄ * (j + i) := by ring
        omega
      exact_mod_cast hnat
    refine le_trans hstep (le_trans (add_le_add hval le_rfl) (le_of_eq ?_))
    push_cast; ring
  | (s + 2) =>
    rw [dev_eq_zero_of_lt hΨ₄ hΨ₄d _ (s + 2) (by
      have h := natDegree_dev4_mul_lt hΨ₄ hΨ₄d hgj hzi
      nlinarith), dv4Hgt_zero L Ψ₂ u₂ hℓ₂ Ψ₃ u₃ hℓ₃, C118a.smul_top_pos hℓ₄, top_add]
    exact le_top

/-- The finite-sum ultrametric for `dv4Hgt`, in the weighted form the outer convolution
consumes (mirror of C136d0's `le_weight_dv3Hgt_sum`; free from Part 1's `dv4Hgt` zero/
ultrametric-add shims). -/
private theorem le_weight_dv4Hgt_sum (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree) {u₃ ℓ₃ : ℕ}
    (hℓ₃ : 0 < ℓ₃) {ℓ₄ : ℕ} (hℓ₄ : 0 < ℓ₄)
    {ι : Type*} (s : Finset ι) (G : ι → Polynomial O) {c d : ℕ∞}
    (hall : ∀ p ∈ s, c ≤ ℓ₄ • dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ (G p) + d) :
    c ≤ ℓ₄ • dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ (∑ p ∈ s, G p) + d := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty, dv4Hgt_zero L Ψ₂ u₂ hℓ₂ Ψ₃ u₃ hℓ₃, C118a.smul_top_pos hℓ₄,
      top_add]
    exact le_top
  | cons a t hat ih =>
    rw [Finset.sum_cons]
    have hmono : Monotone (fun x : ℕ∞ => ℓ₄ • x + d) :=
      fun x y hxy => add_le_add (nsmul_le_nsmul_right hxy ℓ₄) le_rfl
    calc c ≤ min (ℓ₄ • dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ (G a) + d)
          (ℓ₄ • dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ (∑ p ∈ t, G p) + d) :=
          le_min (hall a (Finset.mem_cons_self a t))
            (ih fun p hp => hall p (Finset.mem_cons.2 (Or.inr hp)))
      _ = ℓ₄ • min (dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ (G a))
            (dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ (∑ p ∈ t, G p)) + d :=
          (hmono.map_min).symm
      _ ≤ ℓ₄ • dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ (G a + ∑ p ∈ t, G p) + d :=
          hmono (min_dv4Hgt_le_dv4Hgt_add L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ _ _)

/-- ★ **The `dv4Supp` product law, `≥`-direction, UNIVERSAL** (mirror of C136d0's
`dv3Supp_add_le_dv3Supp_mul`; the level-four B.33, three levels up): every zero case
included.  This is the "≥" half of the eventual μ₅ product law; the "≤" half needs
`Dv4ResSurv` at the chosen minimizers, assembled below. -/
theorem dv4Supp_add_le_dv4Supp_mul (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree) {u₃ ℓ₃ : ℕ}
    (hℓ₃ : 0 < ℓ₃) (hΨ₄ : Ψ₄.Monic) (hΨ₄d : 0 < Ψ₄.natDegree) {u₄ ℓ₄ : ℕ} (hℓ₄ : 0 < ℓ₄)
    (hSurv4 : Dv4ResSurv L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ u₄ ℓ₄) (g z : Polynomial O) :
    dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄ + dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z u₄ ℓ₄
      ≤ dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ (g * z) u₄ ℓ₄ := by
  rcases eq_or_ne g 0 with rfl | hg
  · rw [zero_mul, dv4Supp_zero_eq_top L Ψ₂ u₂ hℓ₂ Ψ₃ u₃ hℓ₃ Ψ₄ u₄ hℓ₄]
    exact le_top
  rcases eq_or_ne z 0 with rfl | hz
  · rw [mul_zero, dv4Supp_zero_eq_top L Ψ₂ u₂ hℓ₂ Ψ₃ u₃ hℓ₃ Ψ₄ u₄ hℓ₄]
    exact le_top
  obtain ⟨Sg, hSg⟩ := ENat.ne_top_iff_exists.1
    (dv4Supp_ne_top_of_ne_zero L hΨ₂ hΨ₂d u₂ ℓ₂ hΨ₃ hΨ₃d u₃ ℓ₃ hΨ₄ hΨ₄d u₄ ℓ₄ hg)
  obtain ⟨Sz, hSz⟩ := ENat.ne_top_iff_exists.1
    (dv4Supp_ne_top_of_ne_zero L hΨ₂ hΨ₂d u₂ ℓ₂ hΨ₃ hΨ₃d u₃ ℓ₃ hΨ₄ hΨ₄d u₄ ℓ₄ hz)
  rw [← hSg, ← hSz, ← Nat.cast_add]
  set N := g.natDegree + z.natDegree + 1 with hN
  have hgN : g.natDegree < N * Ψ₄.natDegree :=
    lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right N hΨ₄d)
  have hzN : z.natDegree < N * Ψ₄.natDegree :=
    lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right N hΨ₄d)
  have hgrep : ∑ j ∈ Finset.range N, dev Ψ₄ g j * Ψ₄ ^ j = g := sum_dev_eq hΨ₄ hΨ₄d g hgN
  have hzrep : ∑ i ∈ Finset.range N, dev Ψ₄ z i * Ψ₄ ^ i = z := sum_dev_eq hΨ₄ hΨ₄d z hzN
  have hrep : g * z = ∑ p ∈ Finset.range N ×ˢ Finset.range N,
      dev Ψ₄ g p.1 * dev Ψ₄ z p.2 * Ψ₄ ^ (p.1 + p.2) := by
    have h1 : g * z = (∑ j ∈ Finset.range N, dev Ψ₄ g j * Ψ₄ ^ j)
        * (∑ i ∈ Finset.range N, dev Ψ₄ z i * Ψ₄ ^ i) := by rw [hgrep, hzrep]
    rw [h1, Finset.sum_mul_sum, Finset.sum_product]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
      rw [pow_add]; ring
  rw [dv4Supp]
  refine Finset.le_inf fun J _ => ?_
  have hdev : dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ (g * z) J
      = dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ (∑ p ∈ Finset.range N ×ˢ Finset.range N,
          dev Ψ₄ (dev Ψ₄ g p.1 * dev Ψ₄ z p.2 * Ψ₄ ^ (p.1 + p.2)) J) := by
    rw [dv4Pin]
    congr 1
    conv_lhs => rw [hrep]
    exact dev_finsetSum hΨ₄ _ _ J
  rw [hdev]
  exact le_weight_dv4Hgt_sum L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ hℓ₄ _ _
    (fun p _ => le_line_dev4_term L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ hΨ₄ hΨ₄d hℓ₄ hSurv4
      hSg.symm hSz.symm J p.1 p.2)

/-! ### The endpoint/minimizer assembly (mirror of C136d0's endpoint assembly)

`Dv4ResSurv` supplies the endpoint's own survival directly (its first clause, applied at
the CHOSEN minimizers) — so every theorem below closes with `Dv4ResSurv` alone, no
separate endpoint hypothesis, exactly as one level down. -/

/-- Every on-side abscissa lies within the development range (mirror of C136d0's
`dv3SideMin_le_natDegree`). -/
theorem dv4SideMin_le_natDegree {u₂ ℓ₂ u₃ ℓ₃ : ℕ} (f : Polynomial O) (u₄ ℓ₄ : ℕ)
    (hne : (dv4SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄).Nonempty) :
    dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄ hne ≤ f.natDegree := by
  classical
  have hmem := Finset.min'_mem (dv4SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄) hne
  have h := (Finset.mem_filter.mp (show dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄ hne ∈
    (Finset.range (f.natDegree + 1)).filter
      (fun j => Dv4OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄ j) from hmem)).1
  rw [Finset.mem_range] at h
  omega

/-- ★ **The endpoint survives, DERIVED from `Dv4ResSurv`** (mirror of C136d0's
`dv3_endpoint_dev_le`): the product's development coefficient at the SUM of the chosen
minimizers has inner value at most `Hg + Hz`. -/
private theorem dv4_endpoint_dev_le (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree) {u₃ ℓ₃ : ℕ}
    (hℓ₃ : 0 < ℓ₃) (hΨ₄ : Ψ₄.Monic) (hΨ₄d : 0 < Ψ₄.natDegree) {u₄ ℓ₄ : ℕ} (hℓ₄ : 0 < ℓ₄)
    (hSurv4 : Dv4ResSurv L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ u₄ ℓ₄) {g z : Polynomial O}
    (hng : (dv4SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄).Nonempty)
    (hnz : (dv4SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z u₄ ℓ₄).Nonempty) {Hg Hz : ℕ}
    (hHg : dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g
      (dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄ hng) = (Hg : ℕ∞))
    (hHz : dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z
      (dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z u₄ ℓ₄ hnz) = (Hz : ℕ∞)) :
    dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ (dev Ψ₄ (g * z)
        (dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄ hng
          + dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z u₄ ℓ₄ hnz))
      ≤ ((Hg + Hz : ℕ) : ℕ∞) := by
  classical
  set jg := dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄ hng with hjg
  set jz := dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z u₄ ℓ₄ hnz with hjz
  have hSg : dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄ = ((ℓ₄ * Hg + u₄ * jg : ℕ) : ℕ∞) :=
    dv4Supp_eq_of_dv4OnSide L hHg (dv4OnSide_dv4SideMin L g u₄ ℓ₄ hng)
  have hSz : dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z u₄ ℓ₄ = ((ℓ₄ * Hz + u₄ * jz : ℕ) : ℕ∞) :=
    dv4Supp_eq_of_dv4OnSide L hHz (dv4OnSide_dv4SideMin L z u₄ ℓ₄ hnz)
  set N := g.natDegree + z.natDegree + 1 with hN
  have hgN : g.natDegree < N * Ψ₄.natDegree :=
    lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right N hΨ₄d)
  have hzN : z.natDegree < N * Ψ₄.natDegree :=
    lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right N hΨ₄d)
  have hgrep : ∑ j ∈ Finset.range N, dev Ψ₄ g j * Ψ₄ ^ j = g := sum_dev_eq hΨ₄ hΨ₄d g hgN
  have hzrep : ∑ i ∈ Finset.range N, dev Ψ₄ z i * Ψ₄ ^ i = z := sum_dev_eq hΨ₄ hΨ₄d z hzN
  have hrep : g * z = ∑ p ∈ Finset.range N ×ˢ Finset.range N,
      dev Ψ₄ g p.1 * dev Ψ₄ z p.2 * Ψ₄ ^ (p.1 + p.2) := by
    have h1 : g * z = (∑ j ∈ Finset.range N, dev Ψ₄ g j * Ψ₄ ^ j)
        * (∑ i ∈ Finset.range N, dev Ψ₄ z i * Ψ₄ ^ i) := by rw [hgrep, hzrep]
    rw [h1, Finset.sum_mul_sum, Finset.sum_product]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
      rw [pow_add]; ring
  have hp0 : ((jg, jz) : ℕ × ℕ) ∈ Finset.range N ×ˢ Finset.range N := by
    refine Finset.mem_product.2 ⟨Finset.mem_range.2 ?_, Finset.mem_range.2 ?_⟩
    · have := dv4SideMin_le_natDegree L g u₄ ℓ₄ hng
      omega
    · have := dv4SideMin_le_natDegree L z u₄ ℓ₄ hnz
      omega
  have hT0 : dev Ψ₄ (dev Ψ₄ g jg * dev Ψ₄ z jz * Ψ₄ ^ (jg + jz)) (jg + jz)
      = dev Ψ₄ (dev Ψ₄ g jg * dev Ψ₄ z jz) 0 := by
    have h := dev_mul_pow hΨ₄ (jg + jz) (dev Ψ₄ g jg * dev Ψ₄ z jz) 0
    rwa [Nat.add_zero] at h
  have hsplit : dev Ψ₄ (g * z) (jg + jz)
      = dev Ψ₄ (dev Ψ₄ g jg * dev Ψ₄ z jz) 0
        + ∑ p ∈ (Finset.range N ×ˢ Finset.range N).erase (jg, jz),
            dev Ψ₄ (dev Ψ₄ g p.1 * dev Ψ₄ z p.2 * Ψ₄ ^ (p.1 + p.2)) (jg + jz) := by
    have hdev : dev Ψ₄ (g * z) (jg + jz)
        = ∑ p ∈ Finset.range N ×ˢ Finset.range N,
            dev Ψ₄ (dev Ψ₄ g p.1 * dev Ψ₄ z p.2 * Ψ₄ ^ (p.1 + p.2)) (jg + jz) := by
      conv_lhs => rw [hrep]
      exact dev_finsetSum hΨ₄ _ _ (jg + jz)
    rw [hdev, ← hT0]
    exact (Finset.add_sum_erase _ _ hp0).symm
  have hallR : ∀ p ∈ (Finset.range N ×ˢ Finset.range N).erase (jg, jz),
      ((ℓ₄ * (Hg + Hz) + u₄ * (jg + jz) + 1 : ℕ) : ℕ∞)
        ≤ ℓ₄ • dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃
            (dev Ψ₄ (dev Ψ₄ g p.1 * dev Ψ₄ z p.2 * Ψ₄ ^ (p.1 + p.2)) (jg + jz))
          + (u₄ * (jg + jz) : ℕ∞) := by
    intro p hp
    have hbad : ¬ (p.1 + p.2 = jg + jz ∧ Dv4OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄ p.1
        ∧ Dv4OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z u₄ ℓ₄ p.2) := by
      rintro ⟨hsum, h1, h2⟩
      obtain ⟨e1, e2⟩ := dv4OnSide_endpoint_unique L hℓ₂ hℓ₃ hΨ₄ hΨ₄d hng hnz hsum h1 h2
      exact (Finset.mem_erase.1 hp).1 (Prod.ext_iff.2 ⟨e1, e2⟩)
    refine le_trans (le_of_eq ?_)
      (lt_line_dev4_term L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ hΨ₄ hΨ₄d hℓ₄ hSurv4 hSg hSz hbad)
    push_cast; ring
  have hRw := le_weight_dv4Hgt_sum L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ hℓ₄ _ _ hallR
  have hR : ((Hg + Hz : ℕ) : ℕ∞) + 1
      ≤ dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃
          (∑ p ∈ (Finset.range N ×ˢ Finset.range N).erase (jg, jz),
            dev Ψ₄ (dev Ψ₄ g p.1 * dev Ψ₄ z p.2 * Ψ₄ ^ (p.1 + p.2)) (jg + jz)) :=
    succ_le_of_weight_succ_le hRw
  have hAdeg : (dev Ψ₄ g jg).natDegree < Ψ₄.natDegree := by
    rcases eq_or_ne (dev Ψ₄ g jg) 0 with h0 | hne
    · rw [h0, natDegree_zero]; exact hΨ₄d
    · exact natDegree_lt_natDegree hne (degree_dev_lt hΨ₄ hΨ₄d g jg)
  have hBdeg : (dev Ψ₄ z jz).natDegree < Ψ₄.natDegree := by
    rcases eq_or_ne (dev Ψ₄ z jz) 0 with h0 | hne
    · rw [h0, natDegree_zero]; exact hΨ₄d
    · exact natDegree_lt_natDegree hne (degree_dev_lt hΨ₄ hΨ₄d z jz)
  have hval : dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ (dev Ψ₄ (dev Ψ₄ g jg * dev Ψ₄ z jz) 0)
      = ((Hg + Hz : ℕ) : ℕ∞) :=
    (hSurv4 hAdeg hBdeg hHg hHz).1
  rw [hsplit]
  set T := dev Ψ₄ (dev Ψ₄ g jg * dev Ψ₄ z jz) 0 with hT
  set R := ∑ p ∈ (Finset.range N ×ˢ Finset.range N).erase (jg, jz),
      dev Ψ₄ (dev Ψ₄ g p.1 * dev Ψ₄ z p.2 * Ψ₄ ^ (p.1 + p.2)) (jg + jz) with hRdef
  rcases eq_or_ne (dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ T) (dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ R)
    with heq | hne
  · exfalso
    have h1 : ((Hg + Hz : ℕ) : ℕ∞) + 1 ≤ ((Hg + Hz : ℕ) : ℕ∞) := by
      calc ((Hg + Hz : ℕ) : ℕ∞) + 1 ≤ dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ R := hR
        _ = dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ T := heq.symm
        _ = ((Hg + Hz : ℕ) : ℕ∞) := hval
    rw [show ((Hg + Hz : ℕ) : ℕ∞) + 1 = ((Hg + Hz + 1 : ℕ) : ℕ∞) by push_cast; ring] at h1
    exact absurd (by exact_mod_cast h1 : Hg + Hz + 1 ≤ Hg + Hz) (by omega)
  · rw [dv4Hgt_add_eq L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ hne, hval]
    exact min_le_left _ _

/-- ★ **The endpoint lemma, level four, value form** (mirror of C136d0's
`dv3Supp_mul_of_endpoint_le`): given `Dv4ResSurv`, the product's cleared support is
EXACTLY the sum of the factors' supports, read at the sum of the chosen minimizers. -/
theorem dv4Supp_mul_of_endpoint_le (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree) {u₃ ℓ₃ : ℕ}
    (hℓ₃ : 0 < ℓ₃) (hΨ₄ : Ψ₄.Monic) (hΨ₄d : 0 < Ψ₄.natDegree) {u₄ ℓ₄ : ℕ} (hℓ₄ : 0 < ℓ₄)
    (hSurv4 : Dv4ResSurv L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ u₄ ℓ₄) {g z : Polynomial O}
    (hng : (dv4SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄).Nonempty)
    (hnz : (dv4SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z u₄ ℓ₄).Nonempty) {Hg Hz : ℕ}
    (hHg : dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g
      (dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄ hng) = (Hg : ℕ∞))
    (hHz : dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z
      (dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z u₄ ℓ₄ hnz) = (Hz : ℕ∞)) :
    dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ (g * z) u₄ ℓ₄
      = ((ℓ₄ * (Hg + Hz)
          + u₄ * (dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄ hng
            + dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z u₄ ℓ₄ hnz) : ℕ) : ℕ∞) := by
  set jg := dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄ hng with hjg
  set jz := dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z u₄ ℓ₄ hnz with hjz
  have hSg := dv4Supp_eq_of_dv4OnSide L hHg (dv4OnSide_dv4SideMin L g u₄ ℓ₄ hng)
  have hSz := dv4Supp_eq_of_dv4OnSide L hHz (dv4OnSide_dv4SideMin L z u₄ ℓ₄ hnz)
  have hup := dv4_endpoint_dev_le L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ hΨ₄ hΨ₄d hℓ₄ hSurv4
    hng hnz hHg hHz
  refine le_antisymm ?_ ?_
  · refine le_trans
      (dv4Supp_le_term L hΨ₄ hΨ₄d u₂ hℓ₂ u₃ hℓ₃ (g * z) u₄ hℓ₄ (jg + jz)) ?_
    refine le_trans (add_le_add (nsmul_le_nsmul_right hup ℓ₄) le_rfl) (le_of_eq ?_)
    rw [nsmul_eq_mul]; push_cast; ring
  · refine le_trans (le_of_eq ?_)
      (dv4Supp_add_le_dv4Supp_mul L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ hΨ₄ hΨ₄d hℓ₄ hSurv4 g z)
    rw [hSg, hSz]; push_cast; ring

/-- ★ **The endpoint lemma, level four, minimizer form** (mirror of C136d0's
`dv3OnSide_mul_endpoint`): the sum of the chosen minimizers IS a product minimizer. -/
theorem dv4OnSide_mul_endpoint (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree) {u₃ ℓ₃ : ℕ}
    (hℓ₃ : 0 < ℓ₃) (hΨ₄ : Ψ₄.Monic) (hΨ₄d : 0 < Ψ₄.natDegree) {u₄ ℓ₄ : ℕ} (hℓ₄ : 0 < ℓ₄)
    (hSurv4 : Dv4ResSurv L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ u₄ ℓ₄) {g z : Polynomial O}
    (hng : (dv4SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄).Nonempty)
    (hnz : (dv4SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z u₄ ℓ₄).Nonempty) {Hg Hz : ℕ}
    (hHg : dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g
      (dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄ hng) = (Hg : ℕ∞))
    (hHz : dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z
      (dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z u₄ ℓ₄ hnz) = (Hz : ℕ∞)) :
    Dv4OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ (g * z) u₄ ℓ₄
      (dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄ hng
        + dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z u₄ ℓ₄ hnz) := by
  set jg := dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄ hng with hjg
  set jz := dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z u₄ ℓ₄ hnz with hjz
  have hval := dv4Supp_mul_of_endpoint_le L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ hΨ₄ hΨ₄d hℓ₄
    hSurv4 hng hnz hHg hHz
  have hup' : dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ (g * z) (jg + jz) ≤ ((Hg + Hz : ℕ) : ℕ∞) :=
    dv4_endpoint_dev_le L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ hΨ₄ hΨ₄d hℓ₄ hSurv4 hng hnz hHg hHz
  have hlow := dv4Supp_le_term (Ψ₂ := Ψ₂) (Ψ₃ := Ψ₃) L hΨ₄ hΨ₄d u₂ hℓ₂ u₃ hℓ₃ (g * z)
    u₄ hℓ₄ (jg + jz)
  rw [hval] at hlow
  have hhgt_ne : dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ (g * z) (jg + jz) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) hup'
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hhgt_ne
  have hcle : c ≤ Hg + Hz := by rw [← hc] at hup'; exact_mod_cast hup'
  have hcge : Hg + Hz ≤ c := by
    rw [← hc, nsmul_eq_mul] at hlow
    have hnat : ℓ₄ * (Hg + Hz) + u₄ * (jg + jz) ≤ ℓ₄ * c + u₄ * (jg + jz) := by
      exact_mod_cast hlow
    have hmul : ℓ₄ * (Hg + Hz) ≤ ℓ₄ * c := by omega
    exact Nat.le_of_mul_le_mul_left hmul hℓ₄
  have hcexact : dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ (g * z) (jg + jz)
      = ((Hg + Hz : ℕ) : ℕ∞) := by
    rw [← hc]; exact_mod_cast (show c = Hg + Hz by omega)
  refine ⟨?_, by rw [hcexact]; exact ENat.coe_ne_top _⟩
  rw [hval, hcexact, nsmul_eq_mul]
  push_cast; ring

/-- The chosen product minimizer is BOUNDED BY the sum of the factors' minimizers (mirror
of C136d0's `dv3SideMin_mul_le`). -/
theorem dv4SideMin_mul_le (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree) {u₃ ℓ₃ : ℕ}
    (hℓ₃ : 0 < ℓ₃) (hΨ₄ : Ψ₄.Monic) (hΨ₄d : 0 < Ψ₄.natDegree) {u₄ ℓ₄ : ℕ} (hℓ₄ : 0 < ℓ₄)
    (hSurv4 : Dv4ResSurv L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ u₄ ℓ₄) {g z : Polynomial O}
    (hng : (dv4SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄).Nonempty)
    (hnz : (dv4SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z u₄ ℓ₄).Nonempty) {Hg Hz : ℕ}
    (hHg : dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g
      (dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄ hng) = (Hg : ℕ∞))
    (hHz : dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z
      (dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z u₄ ℓ₄ hnz) = (Hz : ℕ∞))
    (hne : (dv4SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ (g * z) u₄ ℓ₄).Nonempty) :
    dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ (g * z) u₄ ℓ₄ hne
      ≤ dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄ hng
        + dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z u₄ ℓ₄ hnz :=
  dv4SideMin_le_of_dv4OnSide L hℓ₂ hℓ₃ hΨ₄ hΨ₄d hne
    (dv4OnSide_mul_endpoint L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ hΨ₄ hΨ₄d hℓ₄ hSurv4
      hng hnz hHg hHz)

/-- ★ **The consumption shape, level four** (mirror of C136d0's
`dv3Supp_mul_eq_add_of_endpoint_le`): given `Dv4ResSurv`, the level-four product law
fires — `dv4Supp (g · z) = dv4Supp g + dv4Supp z`. -/
theorem dv4Supp_mul_eq_add_of_endpoint_le (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree) {u₃ ℓ₃ : ℕ}
    (hℓ₃ : 0 < ℓ₃) (hΨ₄ : Ψ₄.Monic) (hΨ₄d : 0 < Ψ₄.natDegree) {u₄ ℓ₄ : ℕ} (hℓ₄ : 0 < ℓ₄)
    (hSurv4 : Dv4ResSurv L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ u₄ ℓ₄) {g z : Polynomial O}
    (hng : (dv4SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄).Nonempty)
    (hnz : (dv4SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z u₄ ℓ₄).Nonempty) {Hg Hz : ℕ}
    (hHg : dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g
      (dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄ hng) = (Hg : ℕ∞))
    (hHz : dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z
      (dv4SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z u₄ ℓ₄ hnz) = (Hz : ℕ∞)) :
    dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ (g * z) u₄ ℓ₄
      = dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g u₄ ℓ₄
        + dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ z u₄ ℓ₄ := by
  rw [dv4Supp_mul_of_endpoint_le L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ hΨ₄ hΨ₄d hℓ₄ hSurv4
      hng hnz hHg hHz,
    dv4Supp_eq_of_dv4OnSide L hHg (dv4OnSide_dv4SideMin L g u₄ ℓ₄ hng),
    dv4Supp_eq_of_dv4OnSide L hHz (dv4OnSide_dv4SideMin L z u₄ ℓ₄ hnz)]
  push_cast
  ring

/-- The level-4 side set of a nonzero polynomial is nonempty (the dv4 twin of
`C136d3ad.dv3SideSet_nonempty_of_ne_zero`). -/
theorem dv4SideSet_nonempty_of_ne_zero (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree) {u₃ ℓ₃ : ℕ}
    (hℓ₃ : 0 < ℓ₃) (hΨ₄ : Ψ₄.Monic) (hΨ₄d : 0 < Ψ₄.natDegree) {u₄ ℓ₄ : ℕ} (hℓ₄ : 0 < ℓ₄)
    {f : Polynomial O} (hf : f ≠ 0) :
    (dv4SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄).Nonempty := by
  classical
  have hfin : dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄ ≠ ⊤ :=
    dv4Supp_ne_top_of_ne_zero L hΨ₂ hΨ₂d u₂ ℓ₂ hΨ₃ hΨ₃d u₃ ℓ₃ hΨ₄ hΨ₄d u₄ ℓ₄ hf
  obtain ⟨j₁, _, hj₁⟩ :=
    Finset.exists_mem_eq_inf (Finset.range (f.natDegree + 1))
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
      (fun j => ℓ₄ • dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f j + (u₄ * j : ℕ∞))
  have hside : dv4Supp L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f u₄ ℓ₄
      = ℓ₄ • dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f j₁ + (u₄ * j₁ : ℕ∞) := hj₁
  have hhgt₁ : dv4Pin L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ f j₁ ≠ ⊤ := by
    intro htop
    apply hfin
    rw [hside, htop, C118a.smul_top_pos hℓ₄, top_add]
  exact ⟨j₁, mem_dv4SideSet_of_dv4OnSide L hℓ₂ hℓ₃ hΨ₄ hΨ₄d ⟨hside, hhgt₁⟩⟩

end GenericEndpoint

/-! ## Part 3 — D4-02 (generic face): the μ-key predicates at the level-4 valuation and
the survival core

`C136d3ad` Parts 1–2's shapes (FGMN Def 1.2/1.4 and the `%ₘ`/`/ₘ` survival core), one
level up: the valuation is the level-4 inner read `dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ · u₃ ℓ₃`
(= `dv4Hgt L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃`, definitionally) instead of `dv2Supp L Ψ₂ · u₂ ℓ₂`.
Generic over any level datum and inner key/sides — despite the "4" the declarations carry
no S2 numeral.  The inner multiplicativity is threaded as the one honest explicit
hypothesis `hmul` (dischargeable at S2 from D3-04's landed `s2Hgt₄_mul_all`, Part 5). -/

section GenericKey

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}

/-- FGMN Def 1.2's `g ∼µ h` at the level-4 valuation (one-level-up twin of
`C136d3ad.Mu3Equiv`). -/
def Mu4Equiv (L : LevelDatum F H₀ hpin) (Ψ₂ : Polynomial O) (u₂ ℓ₂ : ℕ)
    (Ψ₃ : Polynomial O) (u₃ ℓ₃ : ℕ) (g h : Polynomial O) : Prop :=
  (dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃ < dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ (g - h) u₃ ℓ₃ ∧
    dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃ = dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ h u₃ ℓ₃) ∨ (g = 0 ∧ h = 0)

/-- FGMN Def 1.2's `Ψ₄ ∣µ g` at the level-4 valuation (twin of `C136d3ad.Mu3Dvd`). -/
def Mu4Dvd (L : LevelDatum F H₀ hpin) (Ψ₂ : Polynomial O) (u₂ ℓ₂ : ℕ)
    (Ψ₃ : Polynomial O) (u₃ ℓ₃ : ℕ) (Ψ₄ g : Polynomial O) : Prop :=
  ∃ q : Polynomial O, Mu4Equiv L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ g (Ψ₄ * q)

/-- FGMN Def 1.2's µ-minimality at the level-4 valuation (twin of
`C136d3ad.Mu3Minimal`). -/
def Mu4Minimal (L : LevelDatum F H₀ hpin) (Ψ₂ : Polynomial O) (u₂ ℓ₂ : ℕ)
    (Ψ₃ : Polynomial O) (u₃ ℓ₃ : ℕ) (Ψ₄ : Polynomial O) : Prop :=
  0 < Ψ₄.natDegree ∧
    ∀ g : Polynomial O, g ≠ 0 → g.natDegree < Ψ₄.natDegree →
      ¬ Mu4Dvd L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g

/-- The prime clause of FGMN Def 1.2's µ-irreducibility at the level-4 valuation (twin of
`C136d3ad.Mu3Prime`). -/
def Mu4Prime (L : LevelDatum F H₀ hpin) (Ψ₂ : Polynomial O) (u₂ ℓ₂ : ℕ)
    (Ψ₃ : Polynomial O) (u₃ ℓ₃ : ℕ) (Ψ₄ : Polynomial O) : Prop :=
  ∀ g h : Polynomial O,
    Mu4Dvd L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ (g * h) →
      Mu4Dvd L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ g ∨ Mu4Dvd L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ h

/-- FGMN Def 1.4's key-polynomialhood at the level-4 valuation (twin of
`C136d3ad.IsMu3Key`). -/
def IsMu4Key (L : LevelDatum F H₀ hpin) (Ψ₂ : Polynomial O) (u₂ ℓ₂ : ℕ)
    (Ψ₃ : Polynomial O) (u₃ ℓ₃ : ℕ) (Ψ₄ : Polynomial O) : Prop :=
  Ψ₄.Monic ∧ Mu4Minimal L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ ∧ Mu4Prime L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄

variable (L : LevelDatum F H₀ hpin) {Ψ₂ Ψ₃ : Polynomial O}

/-- `0` is μ₄-divisible by anything (witness `0`; twin of `C136d3ad.mu3Dvd_zero`). -/
theorem mu4Dvd_zero {u₂ ℓ₂ u₃ ℓ₃ : ℕ} (Ψ₄ : Polynomial O) :
    Mu4Dvd L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ (0 : Polynomial O) :=
  ⟨0, Or.inr ⟨rfl, mul_zero Ψ₄⟩⟩

/-- ★ **The `≤` half** (twin of `C136d3ad.dv2Supp_mul_modByKey_le`, one level up): for
`a, b` of degree `< deg Ψ₄`, reducing `a·b` modulo the μ₄-key `Ψ₄` does not raise the
level-4 value above the sum of the factors' values. -/
theorem dv3Supp_mul_modByKey_le (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree) {u₃ ℓ₃ : ℕ}
    (hℓ₃ : 0 < ℓ₃)
    (hmul : ∀ ⦃g z : Polynomial O⦄, g ≠ 0 → z ≠ 0 →
      dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ (g * z) u₃ ℓ₃
        = dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃ + dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ z u₃ ℓ₃)
    {Ψ₄ : Polynomial O} (hkey : IsMu4Key L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄) {a b : Polynomial O}
    (ha : a.natDegree < Ψ₄.natDegree) (hb : b.natDegree < Ψ₄.natDegree) :
    dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ ((a * b) %ₘ Ψ₄) u₃ ℓ₃
      ≤ dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ a u₃ ℓ₃ + dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ b u₃ ℓ₃ := by
  obtain ⟨hΨ₄m, hΨ₄min, hΨ₄pr⟩ := hkey
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [zero_mul, Polynomial.zero_modByMonic, dv3Supp_zero_eq_top L Ψ₂ u₂ hℓ₂ Ψ₃ u₃ hℓ₃,
      top_add]
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [mul_zero, Polynomial.zero_modByMonic, dv3Supp_zero_eq_top L Ψ₂ u₂ hℓ₂ Ψ₃ u₃ hℓ₃,
      add_top]
  set r := (a * b) %ₘ Ψ₄ with hrdef
  set q0 := (a * b) /ₘ Ψ₄ with hq0def
  have hab : r + Ψ₄ * q0 = a * b := Polynomial.modByMonic_add_div (a * b) Ψ₄
  rw [← hmul ha0 hb0]
  by_contra hcon
  rw [not_le] at hcon
  -- `hcon : dv3Supp (a·b) < dv3Supp r`
  have hmin' : min (dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ r u₃ ℓ₃) (dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ (Ψ₄ * q0) u₃ ℓ₃)
      ≤ dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ (a * b) u₃ ℓ₃ := by
    have h := min_dv3Supp_le_dv3Supp_add (u₂ := u₂) (u₃ := u₃) L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃
      r (Ψ₄ * q0)
    rwa [hab] at h
  have hy : dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ (Ψ₄ * q0) u₃ ℓ₃ < dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ r u₃ ℓ₃ := by
    by_contra hge
    rw [not_lt] at hge
    rw [min_eq_left hge] at hmin'
    exact absurd hmin' (not_le.mpr hcon)
  have heq' : dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ (a * b) u₃ ℓ₃
      = dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ (Ψ₄ * q0) u₃ ℓ₃ := by
    rw [← hab, add_comm]
    exact dv3Supp_add_eq_of_lt L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ hy
  -- initial equivalence `a·b ∼µ Ψ₄·q0`, hence `Ψ₄ ∣µ a·b`
  have hMuDvd : Mu4Dvd L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ (a * b) := by
    refine ⟨q0, Or.inl ⟨?_, heq'⟩⟩
    have hsub : a * b - Ψ₄ * q0 = r := by rw [← hab]; ring
    rw [hsub]
    exact hcon
  -- contradiction: μ-primality + μ-minimality at the digit-bounded factors
  rcases hΨ₄pr a b hMuDvd with h | h
  · exact hΨ₄min.2 a ha0 ha h
  · exact hΨ₄min.2 b hb0 hb h

/-- ★ **The EQUALITY** (twin of `C136d3ad.dv2Supp_mul_modByKey_eq`, one level up):
reduction modulo the μ₄-key preserves the product's level-4 value exactly. -/
theorem dv3Supp_mul_modByKey_eq (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree) {u₃ ℓ₃ : ℕ}
    (hℓ₃ : 0 < ℓ₃)
    (hmul : ∀ ⦃g z : Polynomial O⦄, g ≠ 0 → z ≠ 0 →
      dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ (g * z) u₃ ℓ₃
        = dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃ + dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ z u₃ ℓ₃)
    {Ψ₄ : Polynomial O} (hkey : IsMu4Key L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄) {a b : Polynomial O}
    (ha : a.natDegree < Ψ₄.natDegree) (hb : b.natDegree < Ψ₄.natDegree) :
    dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ ((a * b) %ₘ Ψ₄) u₃ ℓ₃
      = dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ a u₃ ℓ₃ + dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ b u₃ ℓ₃ := by
  refine le_antisymm
    (dv3Supp_mul_modByKey_le L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ hmul hkey ha hb) ?_
  obtain ⟨hΨ₄m, hΨ₄min, hΨ₄pr⟩ := hkey
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [zero_mul, Polynomial.zero_modByMonic, dv3Supp_zero_eq_top L Ψ₂ u₂ hℓ₂ Ψ₃ u₃ hℓ₃]
    exact le_top
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [mul_zero, Polynomial.zero_modByMonic, dv3Supp_zero_eq_top L Ψ₂ u₂ hℓ₂ Ψ₃ u₃ hℓ₃]
    exact le_top
  rw [← hmul ha0 hb0]
  set r := (a * b) %ₘ Ψ₄ with hrdef
  rcases eq_or_ne r 0 with hr0 | hr0
  · rw [hr0, dv3Supp_zero_eq_top L Ψ₂ u₂ hℓ₂ Ψ₃ u₃ hℓ₃]
    exact le_top
  set q0 := (a * b) /ₘ Ψ₄ with hq0def
  have hab : r + Ψ₄ * q0 = a * b := Polynomial.modByMonic_add_div (a * b) Ψ₄
  have hΨ₄d : 0 < Ψ₄.natDegree := hΨ₄min.1
  have hΨ₄ne1 : Ψ₄ ≠ 1 := fun h1 => by simp [h1] at hΨ₄d
  have hrdeg : r.natDegree < Ψ₄.natDegree :=
    Polynomial.natDegree_modByMonic_lt (a * b) hΨ₄m hΨ₄ne1
  by_contra hcon
  rw [not_le] at hcon
  -- `hcon : dv3Supp r < dv3Supp (a·b)` — the tie analysis forces
  -- `dv3Supp r = dv3Supp (Ψ₄·q0)`
  have htie : dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ r u₃ ℓ₃ = dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ (Ψ₄ * q0) u₃ ℓ₃ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have heqX : dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ (a * b) u₃ ℓ₃
          = dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ r u₃ ℓ₃ := by
        rw [← hab]
        exact dv3Supp_add_eq_of_lt L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ hlt
      rw [heqX] at hcon
      exact lt_irrefl _ hcon
    · have heqX : dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ (a * b) u₃ ℓ₃
          = dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ (Ψ₄ * q0) u₃ ℓ₃ := by
        rw [← hab, add_comm]
        exact dv3Supp_add_eq_of_lt L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ hgt
      rw [heqX] at hcon
      exact lt_irrefl _ (hcon.trans hgt)
  -- initial equivalence `r ∼µ Ψ₄·(−q0)`, hence `Ψ₄ ∣µ r` — excluded by μ-minimality
  have hMuDvd : Mu4Dvd L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ r := by
    refine ⟨-q0, Or.inl ⟨?_, ?_⟩⟩
    · have hsub : r - Ψ₄ * -q0 = a * b := by rw [mul_neg, sub_neg_eq_add, hab]
      rw [hsub]
      exact hcon
    · rw [mul_neg, dv3Supp_neg L hΨ₂ u₂ ℓ₂ hΨ₃ _ u₃ ℓ₃]
      exact htie
  exact hΨ₄min.2 r hr0 hrdeg hMuDvd

/-- ★ **The sharp slot-1 relation** (twin of `C136d3ad.dv2Supp_add_le_key_quot_add`, one
level up): `µ₄(a) + µ₄(b) ≤ µ₄(Ψ₄) + µ₄((a·b) /ₘ Ψ₄)`. -/
theorem dv3Supp_add_le_key_quot_add (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree) {u₃ ℓ₃ : ℕ}
    (hℓ₃ : 0 < ℓ₃)
    (hmul : ∀ ⦃g z : Polynomial O⦄, g ≠ 0 → z ≠ 0 →
      dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ (g * z) u₃ ℓ₃
        = dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃ + dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ z u₃ ℓ₃)
    {Ψ₄ : Polynomial O} (hkey : IsMu4Key L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄) {a b : Polynomial O}
    (ha : a.natDegree < Ψ₄.natDegree) (hb : b.natDegree < Ψ₄.natDegree) :
    dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ a u₃ ℓ₃ + dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ b u₃ ℓ₃
      ≤ dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ Ψ₄ u₃ ℓ₃
        + dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ ((a * b) /ₘ Ψ₄) u₃ ℓ₃ := by
  set r := (a * b) %ₘ Ψ₄ with hrdef
  set q0 := (a * b) /ₘ Ψ₄ with hq0def
  rcases eq_or_ne q0 0 with hq00 | hq00
  · rw [hq00, dv3Supp_zero_eq_top L Ψ₂ u₂ hℓ₂ Ψ₃ u₃ hℓ₃, add_top]
    exact le_top
  rcases eq_or_ne a 0 with rfl | ha0
  · exact absurd (by rw [hq0def, zero_mul, Polynomial.zero_divByMonic]) hq00
  rcases eq_or_ne b 0 with rfl | hb0
  · exact absurd (by rw [hq0def, mul_zero, Polynomial.zero_divByMonic]) hq00
  have hΨ₄m : Ψ₄.Monic := hkey.1
  have hab : r + Ψ₄ * q0 = a * b := Polynomial.modByMonic_add_div (a * b) Ψ₄
  have heq0 : dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ r u₃ ℓ₃
      = dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ a u₃ ℓ₃ + dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ b u₃ ℓ₃ :=
    dv3Supp_mul_modByKey_eq L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ hmul hkey ha hb
  have hXab : dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ (a * b) u₃ ℓ₃
      = dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ a u₃ ℓ₃ + dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ b u₃ ℓ₃ :=
    hmul ha0 hb0
  have heqXr : dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ (a * b) u₃ ℓ₃ = dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ r u₃ ℓ₃ := by
    rw [hXab, heq0]
  rw [← hXab, ← hmul hΨ₄m.ne_zero hq00]
  -- `min(dv3Supp(a·b), dv3Supp r) ≤ dv3Supp(Ψ₄·q0)`, and slot 0 collapses the `min`
  have hmin : min (dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ (a * b) u₃ ℓ₃) (dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ r u₃ ℓ₃)
      ≤ dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ (Ψ₄ * q0) u₃ ℓ₃ := by
    have h := min_dv3Supp_le_dv3Supp_add (u₂ := u₂) (u₃ := u₃) L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃
      (a * b) (-r)
    rw [dv3Supp_neg L hΨ₂ u₂ ℓ₂ hΨ₃ _ u₃ ℓ₃] at h
    have hsub : a * b + -r = Ψ₄ * q0 := by rw [← hab]; ring
    rwa [hsub] at h
  rwa [← heqXr, min_self] at hmin

/-- Slot 1 of a short product's `Ψ₄`-development is the bare quotient
(`C136d3ad`'s private `dev_one_eq_quot`, re-proved verbatim — generic in the key). -/
private theorem dev_one_eq_quot {Ψ₄ : Polynomial O} (hΨ₄m : Ψ₄.Monic) {a b : Polynomial O}
    (ha : a.natDegree < Ψ₄.natDegree) (hb : b.natDegree < Ψ₄.natDegree) :
    dev Ψ₄ (a * b) 1 = (a * b) /ₘ Ψ₄ := by
  have hunfold : dev Ψ₄ (a * b) 1 = dev Ψ₄ ((a * b) /ₘ Ψ₄) 0 := rfl
  rw [hunfold, dev_zero_pin]
  set q0 := (a * b) /ₘ Ψ₄ with hq0def
  rcases eq_or_ne q0 0 with h0 | h0
  · rw [h0, Polynomial.zero_modByMonic]
  · have hqdeg : q0.natDegree < Ψ₄.natDegree := by
      rw [hq0def, Polynomial.natDegree_divByMonic _ hΨ₄m]
      have hABdeg : (a * b).natDegree ≤ a.natDegree + b.natDegree :=
        Polynomial.natDegree_mul_le
      omega
    exact (Polynomial.modByMonic_eq_self_iff hΨ₄m).mpr
      (by rw [Polynomial.degree_eq_natDegree h0, Polynomial.degree_eq_natDegree hΨ₄m.ne_zero]
          exact_mod_cast hqdeg)

/-- ★ **THE D4-02 GENERIC DISCHARGE** (the one-level-up mirror of
`C136d3ad.dv3ResSurv_of_mu3Key`): `Dv4ResSurv L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ u₄ ℓ₄` holds at ANY
level datum and inner key/sides with multiplicative level-4 value, for ANY μ₄-key `Ψ₄` of
known level-4 grade `KΨ₄`, at ANY outer pair `(u₄, ℓ₄)` clearing the OUTER floor
`ℓ₄ · KΨ₄ < u₄` (at S2: `KΨ₄ = 170`, `(u₄, ℓ₄) = (171, 1)`, `1·170 < 171` — the [G5F]
tight floor). -/
theorem dv4ResSurv_of_mu4Key (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree) {u₃ ℓ₃ : ℕ}
    (hℓ₃ : 0 < ℓ₃)
    (hmul : ∀ ⦃g z : Polynomial O⦄, g ≠ 0 → z ≠ 0 →
      dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ (g * z) u₃ ℓ₃
        = dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃ + dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ z u₃ ℓ₃)
    {Ψ₄ : Polynomial O} (hkey : IsMu4Key L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄)
    {KΨ₄ : ℕ} (hKΨ₄ : dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ Ψ₄ u₃ ℓ₃ = (KΨ₄ : ℕ∞))
    {u₄ ℓ₄ : ℕ} (hℓ₄ : 0 < ℓ₄) (hfence : ℓ₄ * KΨ₄ < u₄) :
    Dv4ResSurv L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ Ψ₄ u₄ ℓ₄ := by
  intro A B Ha Hb hA hB hHa hHb
  have hHa' : dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ A u₃ ℓ₃ = (Ha : ℕ∞) := hHa
  have hHb' : dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ B u₃ ℓ₃ = (Hb : ℕ∞) := hHb
  constructor
  · -- slot-0 equality = `Dv4ResSurv`'s first clause, verbatim
    show dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ (dev Ψ₄ (A * B) 0) u₃ ℓ₃ = ((Ha + Hb : ℕ) : ℕ∞)
    rw [dev_zero_pin, dv3Supp_mul_modByKey_eq L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ hmul hkey hA hB,
      hHa', hHb']
    push_cast
    ring
  · -- slot-1 strict carry bound, from the sharp relation + the OUTER floor
    show ℓ₄ • ((Ha + Hb : ℕ) : ℕ∞) + 1
      ≤ ℓ₄ • dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ (dev Ψ₄ (A * B) 1) u₃ ℓ₃ + (u₄ : ℕ∞)
    rw [dev_one_eq_quot hkey.1 hA hB]
    have hsharp := dv3Supp_add_le_key_quot_add L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ hmul hkey hA hB
    rw [hHa', hHb', hKΨ₄] at hsharp
    set Hq0 := dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ ((A * B) /ₘ Ψ₄) u₃ ℓ₃ with hHq0def
    rcases eq_or_ne Hq0 ⊤ with hq0top | hq0ne
    · rw [hq0top, C118a.smul_top_pos hℓ₄, top_add]
      exact le_top
    · obtain ⟨Hq0', hHq0'⟩ := ENat.ne_top_iff_exists.1 hq0ne
      rw [← hHq0'] at hsharp ⊢
      have hnat : Ha + Hb ≤ KΨ₄ + Hq0' := by exact_mod_cast hsharp
      have hgoal : ℓ₄ * (Ha + Hb) + 1 ≤ ℓ₄ * Hq0' + u₄ := by
        have h1 : ℓ₄ * (Ha + Hb) ≤ ℓ₄ * (KΨ₄ + Hq0') := Nat.mul_le_mul le_rfl hnat
        have h2 : ℓ₄ * (KΨ₄ + Hq0') = ℓ₄ * KΨ₄ + ℓ₄ * Hq0' := Nat.mul_add ℓ₄ KΨ₄ Hq0'
        omega
      calc ℓ₄ • ((Ha + Hb : ℕ) : ℕ∞) + 1 = ((ℓ₄ * (Ha + Hb) + 1 : ℕ) : ℕ∞) := by
            rw [nsmul_eq_mul]; push_cast; ring
        _ ≤ ((ℓ₄ * Hq0' + u₄ : ℕ) : ℕ∞) := by exact_mod_cast hgoal
        _ = ℓ₄ • ((Hq0' : ℕ) : ℕ∞) + ((u₄ : ℕ) : ℕ∞) := by
            rw [nsmul_eq_mul]; push_cast; ring

end GenericKey

/-! ## Part 4 — D4-01: the μ₅ value table `s2Hgt₅` and the tooth `s2Hgt₅ g16 = 171 = u₅`

The S2 numeral instantiation of the Part-1 bank, at the [G5F]-adjudicated μ₅ refinement
occurrence: `s2Hgt₅ g := toZ (dv4Supp L Φ₂ 21 2 g₈ 85 2 g16 g 171 1)`, where
`L := (s2Tower h2 hq).levelDatum h2` is the SAME level datum every S2 table reads,
`Φ₂ := s2DepthTwoKeyAt h2 hq 2` at its landed side `(21, 2)`, `g₈` at the D3 campaign's
side `(85, 2)`, and the development key is D3-14's landed `g16` — the depth-four chain's
`keyAt 4` (`C136d3.s2DepthFourKeyChain_keyAt_four`) — at the refinement side
`(u₅, ℓ₅) = (171, 1)`.  Mirror of C136d0's Part 2, one level up. -/

section S2

open Uniformity.Density.Tower.C80 Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C130rp0
open Uniformity.Density.Tower.C132nv1
open Uniformity.Density.Tower.C132rp10b
open Uniformity.Density.Tower.C136d1 Uniformity.Density.Tower.C136d2
open Uniformity.Density.Tower.C136d3 Uniformity.Density.Tower.C136d3ad

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ### Plumbing: the development key IS the depth-four chain's `keyAt 4` -/

/-- Anti-drift pin: the development key IS the depth-four chain's `keyAt 4`
(C136d3's `s2DepthFourKeyChain_keyAt_four`, read through the `KeyChain` field). -/
theorem s2g16_eq_keyChain_four :
    (g16 h2 hq : Polynomial O) = (s2DepthFourKeyChain h2 hq).keyAt 4 :=
  (s2DepthFourKeyChain_keyAt_four h2 hq).symm

/-! ### The VALUE table `s2Hgt₅` and its shape/zero/finiteness/add laws -/

/-- **the S2 μ₅ VALUE table**: the corpus's `e₅`-cleared μ₅ support at the S2 refinement
side `(u₅, ℓ₅) = (171, 1)`, developed in the depth-four key `g16`, whose coefficients are
read by the μ₄ support at the D3 campaign's side `(85, 2)` — the level datum every S2
table reads. -/
noncomputable def s2Hgt₅ (g : Polynomial O) : WithTop ℤ :=
  toZ (dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
    (g8 h2 hq) 85 2 (g16 h2 hq) g 171 1)

/-- Anti-drift pin (the "field shape" tooth): the table IS `dv4Supp` at the S2 numerals —
nothing fresh, mirroring `C136d0.s2Hgt₄_eq_dv3Supp` one level up. -/
theorem s2Hgt₅_eq_dv4Supp (g : Polynomial O) :
    s2Hgt₅ h2 hq g = toZ (dv4Supp ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) 85 2 (g16 h2 hq) g 171 1) := rfl

/-- The table read at the depth-four chain slot: `s2Hgt₅` develops in `keyAt 4` of the
landed depth-four `KeyChain` (the C136d3 carrier this file consumes). -/
theorem s2Hgt₅_eq_keyChain_dev (g : Polynomial O) :
    s2Hgt₅ h2 hq g = toZ (dv4Supp ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) 85 2
      ((s2DepthFourKeyChain h2 hq).keyAt 4) g 171 1) := by
  rw [s2Hgt₅, ← s2g16_eq_keyChain_four h2 hq]

/-- the `hgt_zero` field at μ₅ (mirror of `s2Hgt₄_zero`). -/
theorem s2Hgt₅_zero : s2Hgt₅ h2 hq (0 : Polynomial O) = ⊤ := by
  rw [s2Hgt₅, dv4Supp_zero_eq_top _ _ _ (by norm_num) _ _ (by norm_num) _ _ (by norm_num),
    toZ_top]

/-- every nonzero polynomial has finite μ₅ height (mirror of `s2Hgt₄_ne_top`). -/
theorem s2Hgt₅_ne_top {g : Polynomial O} (hg : g ≠ 0) : s2Hgt₅ h2 hq g ≠ ⊤ := by
  rw [s2Hgt₅, ne_eq, toZ_eq_top_iff]
  exact dv4Supp_ne_top_of_ne_zero _ (s2Φ₂_monic h2 hq)
    (by rw [s2Φ₂_natDegree h2 hq]; norm_num) 21 2 (s2g8_monic h2 hq)
    (by rw [s2g8_natDegree h2 hq]; norm_num) 85 2 (g16_monic h2 hq)
    (by rw [g16_natDegree h2 hq]; norm_num) 171 1 hg

/-- the μ₅ ultrametric inequality (mirror of `s2Hgt₄_add_ge`). -/
theorem s2Hgt₅_add_ge (g g' : Polynomial O) :
    min (s2Hgt₅ h2 hq g) (s2Hgt₅ h2 hq g') ≤ s2Hgt₅ h2 hq (g + g') := by
  rw [s2Hgt₅, s2Hgt₅, s2Hgt₅, ← toZ_min]
  exact toZ_le_toZ_iff.mpr (min_dv4Supp_le_dv4Supp_add _ (s2Φ₂_monic h2 hq)
    (by rw [s2Φ₂_natDegree h2 hq]; norm_num) (by norm_num) (s2g8_monic h2 hq)
    (by rw [s2g8_natDegree h2 hq]; norm_num) (by norm_num) (g16_monic h2 hq)
    (by rw [g16_natDegree h2 hq]; norm_num) (by norm_num) g g')

/-- the μ₅ ultrametric equality off ties (mirror of `s2Hgt₄_add_eq`). -/
theorem s2Hgt₅_add_eq (g g' : Polynomial O) (hne : s2Hgt₅ h2 hq g ≠ s2Hgt₅ h2 hq g') :
    s2Hgt₅ h2 hq (g + g') = min (s2Hgt₅ h2 hq g) (s2Hgt₅ h2 hq g') := by
  have hne' : dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
        (g8 h2 hq) 85 2 (g16 h2 hq) g 171 1
      ≠ dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
        (g8 h2 hq) 85 2 (g16 h2 hq) g' 171 1 :=
    fun heq => hne (congrArg toZ heq)
  rw [s2Hgt₅, s2Hgt₅, s2Hgt₅, ← toZ_min]
  exact congrArg toZ (dv4Supp_add_eq _ (s2Φ₂_monic h2 hq)
    (by rw [s2Φ₂_natDegree h2 hq]; norm_num) (by norm_num) (s2g8_monic h2 hq)
    (by rw [s2g8_natDegree h2 hq]; norm_num) (by norm_num) (g16_monic h2 hq)
    (by rw [g16_natDegree h2 hq]; norm_num) (by norm_num) hne')

/-! ### The tower-height tooth `s2Hgt₅ g16 = 171 = u₅`

Mirror of `C136d0.s2Hgt₄_g8`: `g16`'s own development in itself has `dev = 0` at `j = 0`
and `dev = 1` at `j = 1`; the inner μ₄ reads of the two digit values `0`/`1` are `⊤`
(Part 1's `dv4Hgt_zero`) and `0` (D3-05's landed `s2Hgt₄_one_eq_zero`, transported across
the `s2Hgt₄_eq_dv3Supp` anti-drift pin).  Rather than expanding all 17 slots of the inf,
the value is pinned by antisymmetry: the slot-1 term reads exactly `171`, and every other
slot's term is `⊤` (slot 0) or at least `171·j ≥ 171` (slots `j ≥ 1`). -/

/-- the inner μ₄ read of the digit `0` is `⊤` (Part 1's `dv4Hgt_zero` at the S2
numerals). -/
private theorem s2_dv4Hgt_zero :
    dv4Hgt ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) 85 2
      (0 : Polynomial O) = (⊤ : ℕ∞) :=
  dv4Hgt_zero _ _ _ (by norm_num) _ _ (by norm_num)

/-- the inner μ₄ read of the digit `1` is `0` — literally D3-05's `s2Hgt₄ 1 = 0` tooth,
transported across the `s2Hgt₄_eq_dv3Supp` anti-drift pin (no fresh computation). -/
private theorem s2_dv4Hgt_one :
    dv4Hgt ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) 85 2
      (1 : Polynomial O) = (0 : ℕ∞) := by
  apply C130s6.toZ_inj
  rw [dv4Hgt, ← s2Hgt₄_eq_dv3Supp h2 hq, s2Hgt₄_one_eq_zero h2 hq]
  rfl

private theorem g16_one_mod : (1 : Polynomial O) %ₘ g16 h2 hq = 1 :=
  (Polynomial.modByMonic_eq_self_iff (g16_monic h2 hq)).mpr
    (Polynomial.degree_lt_degree
      (by rw [Polynomial.natDegree_one, g16_natDegree h2 hq]; norm_num))

private theorem g16_dev0 : dev (g16 h2 hq) (g16 h2 hq : Polynomial O) 0 = 0 := by
  have h := dev_mul_pow_of_lt (g16_monic h2 hq) 1 1 0 Nat.one_pos
  rwa [one_mul, pow_one] at h

private theorem g16_dev1 : dev (g16 h2 hq) (g16 h2 hq : Polynomial O) 1 = 1 := by
  have h := dev_mul_pow (g16_monic h2 hq) 1 (1 : Polynomial O) 0
  rw [Nat.add_zero, one_mul, pow_one] at h
  rw [h]
  exact g16_one_mod h2 hq

/-- ★ **the tower-height tooth**: `s2Hgt₅ g16 = 171 = u₅`, the μ₅ analogue of
`C136d0.s2Hgt₄_g8`'s `s2Hgt₄ g₈ = 85 = u₄` (row D4-01's signed value pin). -/
theorem s2Hgt₅_g16 : s2Hgt₅ h2 hq (g16 h2 hq) = ((171 : ℤ) : WithTop ℤ) := by
  have hval : dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) 85 2 (g16 h2 hq) (g16 h2 hq) 171 1 = ((171 : ℕ) : ℕ∞) := by
    refine le_antisymm ?_ ?_
    · have h := dv4Supp_le_term (Ψ₂ := s2DepthTwoKeyAt h2 hq 2) (Ψ₃ := g8 h2 hq)
        (ℓ₂ := 2) (ℓ₃ := 2) (ℓ₄ := 1) ((s2Tower h2 hq).levelDatum h2) (g16_monic h2 hq)
        (by rw [g16_natDegree h2 hq]; norm_num) 21 (by norm_num) 85 (by norm_num)
        (g16 h2 hq) 171 (by norm_num) 1
      rw [dv4Pin, g16_dev1 h2 hq, s2_dv4Hgt_one h2 hq] at h
      simpa using h
    · rw [dv4Supp]
      refine Finset.le_inf fun j hj => ?_
      match j with
      | 0 =>
        rw [dv4Pin, g16_dev0 h2 hq, s2_dv4Hgt_zero h2 hq,
          C118a.smul_top_pos (by norm_num : (0 : ℕ) < 1), top_add]
        exact le_top
      | (j + 1) =>
        refine le_trans ?_ le_add_self
        exact_mod_cast Nat.le_mul_of_pos_right 171 (Nat.succ_pos j)
  rw [s2Hgt₅, hval, toZ_coe]
  norm_num

/-- the tooth at the depth-four chain slot: `s2Hgt₅ (keyAt 4) = 171` (the form the D4
stack's chain-level consumers read). -/
theorem s2Hgt₅_keyChain_four :
    s2Hgt₅ h2 hq ((s2DepthFourKeyChain h2 hq).keyAt 4) = ((171 : ℤ) : WithTop ℤ) := by
  rw [← s2g16_eq_keyChain_four h2 hq]
  exact s2Hgt₅_g16 h2 hq

/-! ## Part 5 — ★ D4-02: the S2 discharge at `(g16, 171, 1)` and the μ₅ product law

Mirror of `C136d3ad` Parts 3–4, one level up.  The landed μ₄ key theorem
`C136d3.s2Mu4KeyPoly_g16` is `s2Hgt₄`-anchored (`WithTop ℤ`-valued); the generic Part-3
predicates are `ℕ∞`-valued.  The bridge is the `toZ` order isomorphism
(`C130rp0.toZ_lt_toZ_iff` / `C130s6.toZ_inj`), exactly the value bridge C136d3ad used one
level down.  The inner μ₄ multiplicativity `hmul` is D3-04's landed unconditional
`s2Hgt₄_mul_all`, read backwards through `toZ` — this is where the μ₄ normalized-product
mechanism (already consumed by the key theorem's criterion) enters this row. -/

/-- The `toZ` bridge for initial equivalence: the generic `ℕ∞`-valued `Mu4Equiv` at the S2
numerals IS the landed `s2Hgt₄`-anchored `S2Mu4InitialEquiv` (mirror of
`C136d3ad.mu3Equiv_iff_s2`). -/
private theorem mu4Equiv_iff_s2 (g h : Polynomial O) :
    Mu4Equiv ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
        (g8 h2 hq) 85 2 g h
      ↔ S2Mu4InitialEquiv h2 hq g h := by
  unfold Mu4Equiv S2Mu4InitialEquiv
  constructor
  · rintro (⟨hlt, heq⟩ | hz)
    · refine Or.inl ⟨?_, ?_⟩
      · rw [s2Hgt₄_eq_dv3Supp, s2Hgt₄_eq_dv3Supp]
        exact toZ_lt_toZ_iff.mpr hlt
      · rw [s2Hgt₄_eq_dv3Supp, s2Hgt₄_eq_dv3Supp]
        exact congrArg toZ heq
    · exact Or.inr hz
  · rintro (⟨hlt, heq⟩ | hz)
    · rw [s2Hgt₄_eq_dv3Supp, s2Hgt₄_eq_dv3Supp] at hlt
      rw [s2Hgt₄_eq_dv3Supp, s2Hgt₄_eq_dv3Supp] at heq
      exact Or.inl ⟨toZ_lt_toZ_iff.mp hlt, toZ_inj heq⟩
    · exact Or.inr hz

/-- The `toZ` bridge for μ₄-divisibility (mirror of `C136d3ad.mu3Dvd_iff_s2`). -/
private theorem mu4Dvd_iff_s2 (φ g : Polynomial O) :
    Mu4Dvd ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
        (g8 h2 hq) 85 2 φ g
      ↔ S2Mu4Dvd h2 hq φ g :=
  exists_congr fun q => mu4Equiv_iff_s2 h2 hq g (φ * q)

/-- ★ **The D3-16 key proof, bridged**: `g16` is a μ₄ key in the generic `ℕ∞`-valued
sense — `C136d3.s2Mu4KeyPoly_g16` read through the `toZ` bridge (mirror of
`C136d3ad.s2_isMu3Key_g8`). -/
theorem s2_isMu4Key_g16 :
    IsMu4Key ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) 85 2 (g16 h2 hq) := by
  obtain ⟨hmon, hmin, hirr⟩ := s2Mu4KeyPoly_g16 h2 hq
  refine ⟨hmon,
    ⟨hmin.1, fun g hg hdeg hdvd => hmin.2 g hg hdeg ((mu4Dvd_iff_s2 h2 hq _ g).mp hdvd)⟩,
    fun g h hdvd => ?_⟩
  rcases hirr.2.2 g h ((mu4Dvd_iff_s2 h2 hq _ (g * h)).mp hdvd) with h' | h'
  · exact Or.inl ((mu4Dvd_iff_s2 h2 hq _ g).mpr h')
  · exact Or.inr ((mu4Dvd_iff_s2 h2 hq _ h).mpr h')

/-- The key's own level-4 grade, `ℕ∞`-cleared: `dv3Supp L Φ₂ 21 2 g₈ g16 85 2 = 170` —
literally D3-14's `C136d2.g16_exactGrade` read through D3-05's
`S2Mu4ExactGrade_iff_dv3Supp` (mirror of `C136d3ad.s2_dv2Supp_g8`). -/
theorem s2_dv3Supp_g16 :
    dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
      (g16 h2 hq) 85 2 = ((170 : ℕ) : ℕ∞) :=
  (S2Mu4ExactGrade_iff_dv3Supp h2 hq).mp (g16_exactGrade h2 hq)

/-- The inner multiplicativity at `(g₈, 85, 2)`: D3-04's landed UNCONDITIONAL
`s2Hgt₄_mul_all` read backwards through `toZ` (the `hmul` supplier — mirror of
`C136d3ad.s2_dv2Supp_mul`, with the endpoint machinery already absorbed one level
down). -/
private theorem s2_dv3Supp_mul (g z : Polynomial O) :
    dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
        (g * z) 85 2
      = dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
          g 85 2
        + dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
          z 85 2 := by
  apply C130s6.toZ_inj
  rw [C130nv.toZ_add, ← s2Hgt₄_eq_dv3Supp h2 hq, ← s2Hgt₄_eq_dv3Supp h2 hq,
    ← s2Hgt₄_eq_dv3Supp h2 hq]
  exact s2Hgt₄_mul_all h2 hq g z

/-- ★ ★ **ROW D4-02 DISCHARGED: the μ₄-residual survival at `(g16, 171, 1)`** — the ONE
explicit hypothesis of Part 2, now UNCONDITIONAL at the S2 depth-four refinement
instance.  Fence: `1 · 170 = 170 < 171` (the [G5F] tight floor). -/
theorem s2_dv4ResSurv_at_171 :
    Dv4ResSurv ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) 85 2 (g16 h2 hq) 171 1 := by
  refine dv4ResSurv_of_mu4Key ((s2Tower h2 hq).levelDatum h2) (s2Φ₂_monic h2 hq)
    (by rw [s2Φ₂_natDegree h2 hq]; norm_num) (by norm_num) (s2g8_monic h2 hq)
    (by rw [s2g8_natDegree h2 hq]; norm_num) (by norm_num) ?_ (s2_isMu4Key_g16 h2 hq)
    (s2_dv3Supp_g16 h2 hq) (by norm_num) (by norm_num)
  intro g z hg hz
  exact s2_dv3Supp_mul h2 hq g z

/-- The S2 depth-four side set of a nonzero polynomial is nonempty (the μ₅ twin of
`C136d3ad.s2_dv3SideSet_nonempty_at_85`). -/
theorem s2_dv4SideSet_nonempty_at_171 {g : Polynomial O} (hg : g ≠ 0) :
    (dv4SideSet ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) 85 2 (g16 h2 hq) g 171 1).Nonempty := by
  exact dv4SideSet_nonempty_of_ne_zero ((s2Tower h2 hq).levelDatum h2) (s2Φ₂_monic h2 hq)
    (by rw [s2Φ₂_natDegree h2 hq]; norm_num) (by norm_num) (s2g8_monic h2 hq)
    (by rw [s2g8_natDegree h2 hq]; norm_num) (by norm_num) (g16_monic h2 hq)
    (by rw [g16_natDegree h2 hq]; norm_num) (by norm_num) hg

/-! ### ★ row D4-01's product clause: the UNCONDITIONAL μ₅ product law -/

/-- ★ **ROW D4-01, nonzero factors** (the μ₅ twin of
`C136d3ad.s2Hgt₄_mul_unconditional`): `s2Hgt₅ (g·z) = s2Hgt₅ g + s2Hgt₅ z` for
`g, z ≠ 0` — Part 2's endpoint assembly fired at the discharged survival. -/
theorem s2Hgt₅_mul_unconditional {g z : Polynomial O} (hg : g ≠ 0) (hz : z ≠ 0) :
    s2Hgt₅ h2 hq (g * z) = s2Hgt₅ h2 hq g + s2Hgt₅ h2 hq z := by
  have hng := s2_dv4SideSet_nonempty_at_171 h2 hq hg
  have hnz := s2_dv4SideSet_nonempty_at_171 h2 hq hz
  obtain ⟨Hg, hHg⟩ := exists_dv4SideMin_height ((s2Tower h2 hq).levelDatum h2) g 171 1 hng
  obtain ⟨Hz, hHz⟩ := exists_dv4SideMin_height ((s2Tower h2 hq).levelDatum h2) z 171 1 hnz
  have hmul4 : dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
        (g8 h2 hq) 85 2 (g16 h2 hq) (g * z) 171 1
      = dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
          (g8 h2 hq) 85 2 (g16 h2 hq) g 171 1
        + dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
          (g8 h2 hq) 85 2 (g16 h2 hq) z 171 1 :=
    dv4Supp_mul_eq_add_of_endpoint_le ((s2Tower h2 hq).levelDatum h2) (s2Φ₂_monic h2 hq)
      (by rw [s2Φ₂_natDegree h2 hq]; norm_num) (by norm_num) (s2g8_monic h2 hq)
      (by rw [s2g8_natDegree h2 hq]; norm_num) (by norm_num) (g16_monic h2 hq)
      (by rw [g16_natDegree h2 hq]; norm_num) (by norm_num) (s2_dv4ResSurv_at_171 h2 hq)
      hng hnz hHg hHz
  rw [s2Hgt₅_eq_dv4Supp h2 hq (g * z), s2Hgt₅_eq_dv4Supp h2 hq g,
    s2Hgt₅_eq_dv4Supp h2 hq z, ← C130nv.toZ_add]
  exact congrArg toZ hmul4

/-- ★ **ROW D4-01, zero cases folded in** (the μ₅ twin of `C136d3ad.s2Hgt₄_mul_all`):
`AddValuation.of`'s `hmul` shape. -/
theorem s2Hgt₅_mul_all (x y : Polynomial O) :
    s2Hgt₅ h2 hq (x * y) = s2Hgt₅ h2 hq x + s2Hgt₅ h2 hq y := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [zero_mul, s2Hgt₅_zero h2 hq, top_add]
  rcases eq_or_ne y 0 with rfl | hy
  · rw [mul_zero, s2Hgt₅_zero h2 hq, add_top]
  exact s2Hgt₅_mul_unconditional h2 hq hx hy

/-! ## Part 6 — D4-03: the μ₅ `AddValuation` packaging and the grade-predicate bank

Mirror of `C136d1`'s D3-05 section, one level up: the `h1`-shape bridging tooth, the
genuine UNCONDITIONAL `AddValuation.of` packaging directly from the product law (no
nonemptiness-gap machinery — D4-01/02 already landed the unconditional product law), and
the full `S2Mu5ExactGrade`/`S2Mu5AboveGrade` bank. -/

/-- ★ **the `h1`-shape bridging tooth**: `s2Hgt₅ 1 = 0` in `AddValuation.of`'s exact `h1`
shape — the μ₅ twin of `C136d1.s2Hgt₄_one_eq_zero`. -/
theorem s2Hgt₅_one_eq_zero : s2Hgt₅ h2 hq (1 : Polynomial O) = 0 := by
  have hdev0 : dev (g16 h2 hq) (1 : Polynomial O) 0 = 1 := g16_one_mod h2 hq
  have hval : dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) 85 2 (g16 h2 hq) (1 : Polynomial O) 171 1 = ((0 : ℕ) : ℕ∞) := by
    rw [dv4Supp, Polynomial.natDegree_one, show Finset.range (0 + 1) = {0} by decide,
      Finset.inf_singleton, dv4Pin, hdev0, s2_dv4Hgt_one h2 hq]
    simp
  rw [s2Hgt₅, hval, C130s6.toZ_coe]
  rfl

/-- ★ **the genuine (UNCONDITIONAL) `AddValuation` instance for `s2Hgt₅`**, directly from
`AddValuation.of` at D4-01's already-unconditional `s2Hgt₅_mul_all` — the μ₅ twin of
`C136d1.s2AddVal₄`. -/
noncomputable def s2AddVal₅ : AddValuation (Polynomial O) (WithTop ℤ) :=
  AddValuation.of (s2Hgt₅ h2 hq) (s2Hgt₅_zero h2 hq) (s2Hgt₅_one_eq_zero h2 hq)
    (s2Hgt₅_add_ge h2 hq) (s2Hgt₅_mul_all h2 hq)

/-- Anti-drift restriction pin: `s2AddVal₅` evaluates to exactly `s2Hgt₅`. -/
theorem s2AddVal₅_apply (A : Polynomial O) : s2AddVal₅ h2 hq A = s2Hgt₅ h2 hq A := rfl

/-! ### The concrete S2 μ₅ instantiation of the exact/above grade predicates -/

/-- `S2Mu5ExactGrade β g ↔ μ₅(g) = β` (the μ₅ analogue of `C136d1.S2Mu4ExactGrade`). -/
def S2Mu5ExactGrade (β : ℕ) (g : Polynomial O) : Prop :=
  s2Hgt₅ h2 hq g = (β : WithTop ℤ)

/-- `S2Mu5AboveGrade β g ↔ μ₅(g) > β` (the μ₅ analogue of `C136d1.S2Mu4AboveGrade`). -/
def S2Mu5AboveGrade (β : ℕ) (g : Polynomial O) : Prop :=
  (β : WithTop ℤ) < s2Hgt₅ h2 hq g

theorem S2Mu5ExactGrade_iff_dv4Supp {β : ℕ} {g : Polynomial O} :
    S2Mu5ExactGrade h2 hq β g ↔
      dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
        85 2 (g16 h2 hq) g 171 1 = (β : ℕ∞) := by
  unfold S2Mu5ExactGrade
  rw [s2Hgt₅_eq_dv4Supp]
  constructor
  · intro h
    exact toZ_inj (by rw [h]; norm_cast)
  · intro h
    rw [h]; norm_cast

theorem S2Mu5AboveGrade_iff_dv4Supp {β : ℕ} {g : Polynomial O} :
    S2Mu5AboveGrade h2 hq β g ↔
      (β : ℕ∞) < dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
        (g8 h2 hq) 85 2 (g16 h2 hq) g 171 1 := by
  unfold S2Mu5AboveGrade
  rw [s2Hgt₅_eq_dv4Supp]
  rw [show (β : WithTop ℤ) = toZ (β : ℕ∞) by norm_cast]
  exact toZ_lt_toZ_iff

theorem S2Mu5ExactGrade_exists {g : Polynomial O} (hg : g ≠ 0) :
    ∃ β : ℕ, S2Mu5ExactGrade h2 hq β g := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1
    (dv4Supp_ne_top_of_ne_zero ((s2Tower h2 hq).levelDatum h2) (s2Φ₂_monic h2 hq)
      (by rw [s2Φ₂_natDegree h2 hq]; norm_num) 21 2 (s2g8_monic h2 hq)
      (by rw [s2g8_natDegree h2 hq]; norm_num) 85 2 (g16_monic h2 hq)
      (by rw [g16_natDegree h2 hq]; norm_num) 171 1 hg)
  exact ⟨n, (S2Mu5ExactGrade_iff_dv4Supp h2 hq).mpr hn.symm⟩

theorem S2Mu5ExactGrade_unique {β β' : ℕ} {g : Polynomial O}
    (h1 : S2Mu5ExactGrade h2 hq β g) (h2' : S2Mu5ExactGrade h2 hq β' g) : β = β' := by
  unfold S2Mu5ExactGrade at h1 h2'
  rw [h1] at h2'
  exact_mod_cast h2'

/-- ★ **the grade arithmetic** — `S2Mu5ExactGrade` is closed under multiplication with
grades adding, UNCONDITIONALLY (off D4-01's `s2Hgt₅_mul_all`). -/
theorem S2Mu5ExactGrade_mul {β β' : ℕ} {g h : Polynomial O}
    (hg : S2Mu5ExactGrade h2 hq β g) (hh : S2Mu5ExactGrade h2 hq β' h) :
    S2Mu5ExactGrade h2 hq (β + β') (g * h) := by
  unfold S2Mu5ExactGrade at hg hh ⊢
  rw [s2Hgt₅_mul_all h2 hq, hg, hh, S2Grade_natCast_add]

theorem S2Mu5ExactGrade_not_above {β : ℕ} {g : Polynomial O}
    (hg : S2Mu5ExactGrade h2 hq β g) : ¬ S2Mu5AboveGrade h2 hq β g := by
  unfold S2Mu5ExactGrade at hg
  unfold S2Mu5AboveGrade
  rw [hg]
  exact lt_irrefl _

theorem S2Mu5ExactGrade_not_zero {β : ℕ} {g : Polynomial O}
    (hg : S2Mu5ExactGrade h2 hq β g) : g ≠ 0 := by
  intro h0
  unfold S2Mu5ExactGrade at hg
  rw [h0, s2Hgt₅_zero] at hg
  exact WithTop.top_ne_coe hg

theorem S2Mu5ExactGrade_zero_false (β : ℕ) :
    ¬ S2Mu5ExactGrade h2 hq β (0 : Polynomial O) :=
  fun hg => S2Mu5ExactGrade_not_zero h2 hq hg rfl

theorem S2Mu5AboveGrade_zero (β : ℕ) : S2Mu5AboveGrade h2 hq β (0 : Polynomial O) := by
  unfold S2Mu5AboveGrade
  rw [s2Hgt₅_zero]
  exact_mod_cast WithTop.coe_lt_top (β : ℤ)

theorem S2Mu5ExactGrade_eq_addVal (β : ℕ) (g : Polynomial O) :
    S2Mu5ExactGrade h2 hq β g ↔ s2AddVal₅ h2 hq g = (β : WithTop ℤ) := by
  unfold S2Mu5ExactGrade
  rw [s2AddVal₅_apply]

theorem S2Mu5AboveGrade_eq_addVal (β : ℕ) (g : Polynomial O) :
    S2Mu5AboveGrade h2 hq β g ↔ (β : WithTop ℤ) < s2AddVal₅ h2 hq g := by
  unfold S2Mu5AboveGrade
  rw [s2AddVal₅_apply]

/-- **tooth**: `h₅(g16) = 171 = u₅` re-read as an exact grade, off `s2Hgt₅_g16`. -/
theorem tooth_g16 : S2Mu5ExactGrade h2 hq 171 (g16 h2 hq : Polynomial O) := by
  unfold S2Mu5ExactGrade
  rw [s2Hgt₅_g16]
  norm_cast

/-! ## Part 7 — D4-04: grade-line coordinates at `e' = 1` — the refinement gate

Mirror of `C136d1`'s D3-06 Part 0 + Part 1 (published Def 3.12's line arithmetic and the
grade-line gate) at the μ₅ refinement numerals, PLUS the `PrevGrade` collapse (model:
`C132rp6.S2Mu3PrevGrade` / `C136d2.S2Mu4PrevGrade`).  This is exactly where `(1,1,171)`
genuinely differs from the proper stages, per the [G5F] record and G5's row text: with
`e' = 1` the Def-3.12 slot residue is IDENTICALLY 0 (no abscissa class is excluded — no
parity gate), the on-line inner grade needs no division, and EVERY grade is a
preceding-group grade. -/

/-! ### Part 0 — published Def 3.12's grade-line arithmetic at levels 5 and 4 -/

/-- ★ **Def 3.12 at `i = 5`, uniqueness** (`(e₅,h₅) = (1,171)`): the unique solution of
`u·1 + s·171 = β`, `0 ≤ s < 1` is `s₅(β) = 0`, `u₅(β) = β` — **the unique slot residue is
0** (row D4-04's first signed exit; contrast `C136d1.s2Mu4_def312_level4`, whose residue
`β % 2` genuinely varies). -/
theorem s2Mu5_def312_level5 (β : ℕ) (u s : ℤ) (h : u * 1 + s * 171 = (β : ℤ))
    (hs0 : 0 ≤ s) (hs1 : s < 1) : s = 0 ∧ u = (β : ℤ) := by omega

/-- **Def 3.12 at `i = 5`, existence**: the collapsed pair `(u, s) = (β, 0)` does solve
the equation with the required range constraint. -/
theorem s2Mu5_def312_level5_exists (β : ℕ) :
    (β : ℤ) * 1 + 0 * 171 = (β : ℤ) ∧ (0 : ℤ) ≤ 0 ∧ (0 : ℤ) < 1 := by norm_num

/-- the slot-residue collapse, ℕ-cleared: at `e' = 1` the Def-3.12 residue `β % 1` is `0`
for EVERY grade `β`. -/
theorem s2Mu5_slot_residue_zero (β : ℕ) : β % 1 = 0 := Nat.mod_one β

/-- **§3.3's Bézout pair at `i = 4`**: `(ℓ₄, ℓ₄′) = (1, −42)` solves `ℓ₄·h₄ + ℓ₄′·e₄ = 1`
with `0 ≤ ℓ₄ < e₄` at `(e₄, h₄) = (2, 85)` — the ε-data one level down from the μ₅ gate,
pinned here for row D4-05's ε-exponent (mirror of `C136d1.s2Mu4_bezout_level3`). -/
theorem s2Mu5_bezout_level4 :
    (1 : ℤ) * 85 + (-42) * 2 = 1 ∧ (0 : ℤ) ≤ 1 ∧ (1 : ℤ) < 2 := by norm_num

/-! ### Part 1 — the μ₅ grade-line gate `S2Mu5SlotOnGrade` -/

/-- ★ **the μ₅ grade-line gate**: `1·μ₄(A_s) + 171·s = β` — slot `s` of the
`g16`-development of `g` sits exactly on the μ₅ grade-`β` line (the `e' = 1` mirror of
`C136d1.S2Mu4SlotOnGrade`). -/
def S2Mu5SlotOnGrade (β : ℕ) (g : Polynomial O) (s : ℕ) : Prop :=
  1 • dv4Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
      85 2 (g16 h2 hq) g s
    + ((171 * s : ℕ) : ℕ∞) = (β : ℕ∞)

theorem s2Mu5SlotOnGrade_iff {β s : ℕ} {g : Polynomial O} :
    S2Mu5SlotOnGrade h2 hq β g s ↔
      ∃ m : ℕ, dv4Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
          (g8 h2 hq) 85 2 (g16 h2 hq) g s = (m : ℕ∞) ∧ 1 * m + 171 * s = β := by
  unfold S2Mu5SlotOnGrade
  constructor
  · intro h
    have hne : dv4Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
        (g8 h2 hq) 85 2 (g16 h2 hq) g s ≠ ⊤ := by
      intro htop
      rw [htop, C118a.smul_top_pos (by norm_num : (0 : ℕ) < 1), top_add] at h
      exact WithTop.top_ne_coe h
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
    refine ⟨m, hm.symm, ?_⟩
    rw [← hm, nsmul_eq_mul] at h
    exact_mod_cast h
  · rintro ⟨m, hm, hβ⟩
    rw [hm, nsmul_eq_mul, ← hβ]
    push_cast
    ring

/-- **the refinement-gate residue law** (the μ₅ mirror of
`C136d1.s2Mu4SlotOnGrade_parity`, with the residue class COLLAPSED): every on-line slot
has the trivial residue `s % 1 = 0 = β % 1` — at `e' = 1` NO abscissa class is excluded
by the gate's arithmetic, unlike the μ₄ parity gate. -/
theorem s2Mu5SlotOnGrade_residue {β s : ℕ} {g : Polynomial O}
    (_h : S2Mu5SlotOnGrade h2 hq β g s) : s % 1 = β % 1 := by
  simp [Nat.mod_one]

/-- ★ **the inner exact-grade pin** (eq (10)'s second conjunct at `e' = 1`): on the gate,
the development coefficient `A_s` has EXACTLY the on-line inner μ₄ grade `β − 171·s` —
NO division by `e'`, since `e' = 1` (contrast `C136d1.s2Mu4SlotOnGrade_inner_exact`'s
`(β − 85·s)/2`). -/
theorem s2Mu5SlotOnGrade_inner_exact {β s : ℕ} {g : Polynomial O}
    (h : S2Mu5SlotOnGrade h2 hq β g s) :
    S2Mu4ExactGrade h2 hq (β - 171 * s) (dev (g16 h2 hq) g s) := by
  obtain ⟨m, hm, hβ⟩ := (s2Mu5SlotOnGrade_iff h2 hq).mp h
  have hdiv : β - 171 * s = m := by omega
  rw [dv4Pin, dv4Hgt] at hm
  rw [hdiv]
  exact (S2Mu4ExactGrade_iff_dv3Supp h2 hq).mpr hm

/-- an on-line slot bounds the cleared μ₅ support (mirror of
`C136d1.dv3Supp_le_of_mu4SlotOnGrade`). -/
theorem dv4Supp_le_of_mu5SlotOnGrade {β s : ℕ} {g : Polynomial O}
    (h : S2Mu5SlotOnGrade h2 hq β g s) :
    dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
      85 2 (g16 h2 hq) g 171 1 ≤ (β : ℕ∞) := by
  obtain ⟨m, hm, hβ⟩ := (s2Mu5SlotOnGrade_iff h2 hq).mp h
  have hs : s ≤ g.natDegree := by
    by_contra hs
    rw [dv4Pin_top_of_gt ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21
      (by norm_num) (g8 h2 hq) 85 (by norm_num) (g16_monic h2 hq)
      (by rw [g16_natDegree h2 hq]; norm_num) g (not_le.mp hs)] at hm
    exact absurd hm (by exact WithTop.top_ne_coe)
  have hle : dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) 85 2 (g16 h2 hq) g 171 1
      ≤ 1 • dv4Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
          (g8 h2 hq) 85 2 (g16 h2 hq) g s + ((171 : ℕ∞) * (s : ℕ∞)) := by
    rw [dv4Supp]
    exact Finset.inf_le (Finset.mem_range.mpr (by omega))
  have heq : 1 • dv4Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) 85 2 (g16 h2 hq) g s + ((171 : ℕ∞) * (s : ℕ∞)) = (β : ℕ∞) := by
    rw [hm, nsmul_eq_mul, ← hβ]
    push_cast
    ring
  rw [heq] at hle
  exact hle

/-! ### Part 2 — ★ `PrevGrade` is ALL grades -/

/-- The μ₅ preceding-group predicate in full-current-group cleared coordinates (the μ₅
analogue of `C132rp6.S2Mu3PrevGrade` and `C136d2.S2Mu4PrevGrade`, at `e' = 1`). -/
def S2Mu5PrevGrade (β : ℕ) : Prop := 1 ∣ β

/-- The consumable mod form of `S2Mu5PrevGrade` (mirror of
`C132rp6.S2Mu3PrevGrade_iff_mod`). -/
theorem S2Mu5PrevGrade_iff_mod (β : ℕ) : S2Mu5PrevGrade β ↔ β % 1 = 0 := by
  unfold S2Mu5PrevGrade
  omega

/-- ★ **ROW D4-04's second signed exit: `PrevGrade` is ALL grades** — at the `(1,1,171)`
refinement EVERY grade is a preceding-group grade (contrast: μ₄'s
`S2Mu4PrevGrade = 2 ∣ β` excludes the odd grades; this collapse is exactly the [G5F]
clause "1 divides every cleared grade"). -/
theorem S2Mu5PrevGrade_all (β : ℕ) : S2Mu5PrevGrade β := one_dvd β

end S2

end Uniformity.Density.Tower.C136e0

/-! ## Axiom footprint -/

section AxCheck

-- Part 1 — D4-00: the dv4 support layer and its bank
#print axioms Uniformity.Density.Tower.C136e0.dv4Hgt
#print axioms Uniformity.Density.Tower.C136e0.dv4Hgt_eq_dv3Supp
#print axioms Uniformity.Density.Tower.C136e0.dv4Pin
#print axioms Uniformity.Density.Tower.C136e0.dv4Supp
#print axioms Uniformity.Density.Tower.C136e0.dv4Hgt_zero
#print axioms Uniformity.Density.Tower.C136e0.dv4Hgt_ne_top_of_ne_zero
#print axioms Uniformity.Density.Tower.C136e0.min_dv4Hgt_le_dv4Hgt_add
#print axioms Uniformity.Density.Tower.C136e0.dv4Hgt_add_eq
#print axioms Uniformity.Density.Tower.C136e0.dv4Hgt_neg
#print axioms Uniformity.Density.Tower.C136e0.dv4Pin_top_of_gt
#print axioms Uniformity.Density.Tower.C136e0.dv4Supp_zero_eq_top
#print axioms Uniformity.Density.Tower.C136e0.dv4Supp_eq_inf_range
#print axioms Uniformity.Density.Tower.C136e0.dv4Supp_ne_top_of_ne_zero
#print axioms Uniformity.Density.Tower.C136e0.min_dv4Supp_le_dv4Supp_add
#print axioms Uniformity.Density.Tower.C136e0.dv4Supp_neg
#print axioms Uniformity.Density.Tower.C136e0.dv4Supp_add_eq_of_lt
#print axioms Uniformity.Density.Tower.C136e0.dv4Supp_add_eq
-- Part 2 — D4-00 (endpoint face): the endpoint/minimizer/convolution bank
#print axioms Uniformity.Density.Tower.C136e0.Dv4OnSide
#print axioms Uniformity.Density.Tower.C136e0.dv4SideSet
#print axioms Uniformity.Density.Tower.C136e0.dv4SideMin
#print axioms Uniformity.Density.Tower.C136e0.dv4OnSide_of_mem_dv4SideSet
#print axioms Uniformity.Density.Tower.C136e0.mem_dv4SideSet_of_dv4OnSide
#print axioms Uniformity.Density.Tower.C136e0.dv4OnSide_dv4SideMin
#print axioms Uniformity.Density.Tower.C136e0.dv4SideMin_le_of_dv4OnSide
#print axioms Uniformity.Density.Tower.C136e0.not_dv4OnSide_of_lt_dv4SideMin
#print axioms Uniformity.Density.Tower.C136e0.dv4OnSide_endpoint_unique
#print axioms Uniformity.Density.Tower.C136e0.exists_dv4SideMin_height
#print axioms Uniformity.Density.Tower.C136e0.dv4Supp_eq_of_dv4OnSide
#print axioms Uniformity.Density.Tower.C136e0.dv4Supp_le_term
#print axioms Uniformity.Density.Tower.C136e0.le_dv4Weight
#print axioms Uniformity.Density.Tower.C136e0.lt_dv4Weight
#print axioms Uniformity.Density.Tower.C136e0.Dv4ResSurv
#print axioms Uniformity.Density.Tower.C136e0.natDegree_dev4_mul_lt
#print axioms Uniformity.Density.Tower.C136e0.le_line_dev4_term
#print axioms Uniformity.Density.Tower.C136e0.lt_line_dev4_term
#print axioms Uniformity.Density.Tower.C136e0.dv4Supp_add_le_dv4Supp_mul
#print axioms Uniformity.Density.Tower.C136e0.dv4SideMin_le_natDegree
#print axioms Uniformity.Density.Tower.C136e0.dv4Supp_mul_of_endpoint_le
#print axioms Uniformity.Density.Tower.C136e0.dv4OnSide_mul_endpoint
#print axioms Uniformity.Density.Tower.C136e0.dv4SideMin_mul_le
#print axioms Uniformity.Density.Tower.C136e0.dv4Supp_mul_eq_add_of_endpoint_le
#print axioms Uniformity.Density.Tower.C136e0.dv4SideSet_nonempty_of_ne_zero
-- Part 3 — D4-02 (generic face): the μ-key predicates and the survival core
#print axioms Uniformity.Density.Tower.C136e0.Mu4Equiv
#print axioms Uniformity.Density.Tower.C136e0.Mu4Dvd
#print axioms Uniformity.Density.Tower.C136e0.Mu4Minimal
#print axioms Uniformity.Density.Tower.C136e0.Mu4Prime
#print axioms Uniformity.Density.Tower.C136e0.IsMu4Key
#print axioms Uniformity.Density.Tower.C136e0.mu4Dvd_zero
#print axioms Uniformity.Density.Tower.C136e0.dv3Supp_mul_modByKey_le
#print axioms Uniformity.Density.Tower.C136e0.dv3Supp_mul_modByKey_eq
#print axioms Uniformity.Density.Tower.C136e0.dv3Supp_add_le_key_quot_add
#print axioms Uniformity.Density.Tower.C136e0.dv4ResSurv_of_mu4Key
-- Part 4 — D4-01: the μ₅ value table and the tooth
#print axioms Uniformity.Density.Tower.C136e0.s2g16_eq_keyChain_four
#print axioms Uniformity.Density.Tower.C136e0.s2Hgt₅
#print axioms Uniformity.Density.Tower.C136e0.s2Hgt₅_eq_dv4Supp
#print axioms Uniformity.Density.Tower.C136e0.s2Hgt₅_eq_keyChain_dev
#print axioms Uniformity.Density.Tower.C136e0.s2Hgt₅_zero
#print axioms Uniformity.Density.Tower.C136e0.s2Hgt₅_ne_top
#print axioms Uniformity.Density.Tower.C136e0.s2Hgt₅_add_ge
#print axioms Uniformity.Density.Tower.C136e0.s2Hgt₅_add_eq
#print axioms Uniformity.Density.Tower.C136e0.s2Hgt₅_g16
#print axioms Uniformity.Density.Tower.C136e0.s2Hgt₅_keyChain_four
-- Part 5 — D4-02: the S2 discharge and the μ₅ product law
#print axioms Uniformity.Density.Tower.C136e0.s2_isMu4Key_g16
#print axioms Uniformity.Density.Tower.C136e0.s2_dv3Supp_g16
#print axioms Uniformity.Density.Tower.C136e0.s2_dv4ResSurv_at_171
#print axioms Uniformity.Density.Tower.C136e0.s2_dv4SideSet_nonempty_at_171
#print axioms Uniformity.Density.Tower.C136e0.s2Hgt₅_mul_unconditional
#print axioms Uniformity.Density.Tower.C136e0.s2Hgt₅_mul_all
-- Part 6 — D4-03: the AddValuation packaging and the grade bank
#print axioms Uniformity.Density.Tower.C136e0.s2Hgt₅_one_eq_zero
#print axioms Uniformity.Density.Tower.C136e0.s2AddVal₅
#print axioms Uniformity.Density.Tower.C136e0.s2AddVal₅_apply
#print axioms Uniformity.Density.Tower.C136e0.S2Mu5ExactGrade
#print axioms Uniformity.Density.Tower.C136e0.S2Mu5AboveGrade
#print axioms Uniformity.Density.Tower.C136e0.S2Mu5ExactGrade_iff_dv4Supp
#print axioms Uniformity.Density.Tower.C136e0.S2Mu5AboveGrade_iff_dv4Supp
#print axioms Uniformity.Density.Tower.C136e0.S2Mu5ExactGrade_exists
#print axioms Uniformity.Density.Tower.C136e0.S2Mu5ExactGrade_unique
#print axioms Uniformity.Density.Tower.C136e0.S2Mu5ExactGrade_mul
#print axioms Uniformity.Density.Tower.C136e0.S2Mu5ExactGrade_not_above
#print axioms Uniformity.Density.Tower.C136e0.S2Mu5ExactGrade_not_zero
#print axioms Uniformity.Density.Tower.C136e0.S2Mu5ExactGrade_zero_false
#print axioms Uniformity.Density.Tower.C136e0.S2Mu5AboveGrade_zero
#print axioms Uniformity.Density.Tower.C136e0.S2Mu5ExactGrade_eq_addVal
#print axioms Uniformity.Density.Tower.C136e0.S2Mu5AboveGrade_eq_addVal
#print axioms Uniformity.Density.Tower.C136e0.tooth_g16
-- Part 7 — D4-04: the refinement-gate grade-line coordinates
#print axioms Uniformity.Density.Tower.C136e0.s2Mu5_def312_level5
#print axioms Uniformity.Density.Tower.C136e0.s2Mu5_def312_level5_exists
#print axioms Uniformity.Density.Tower.C136e0.s2Mu5_slot_residue_zero
#print axioms Uniformity.Density.Tower.C136e0.s2Mu5_bezout_level4
#print axioms Uniformity.Density.Tower.C136e0.S2Mu5SlotOnGrade
#print axioms Uniformity.Density.Tower.C136e0.s2Mu5SlotOnGrade_iff
#print axioms Uniformity.Density.Tower.C136e0.s2Mu5SlotOnGrade_residue
#print axioms Uniformity.Density.Tower.C136e0.s2Mu5SlotOnGrade_inner_exact
#print axioms Uniformity.Density.Tower.C136e0.dv4Supp_le_of_mu5SlotOnGrade
#print axioms Uniformity.Density.Tower.C136e0.S2Mu5PrevGrade
#print axioms Uniformity.Density.Tower.C136e0.S2Mu5PrevGrade_iff_mod
#print axioms Uniformity.Density.Tower.C136e0.S2Mu5PrevGrade_all

end AxCheck
