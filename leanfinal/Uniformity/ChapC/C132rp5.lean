/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C132rp4
import Uniformity.ChapC.C132nv2
import Uniformity.ChapC.C132nv3b
import Uniformity.ChapC.C130rp9
import Uniformity.ChapC.C130kp5

/-!
# Uniformity.ChapC.C132rp5 — the μ₃ recursive coefficient convolution (μ₃ campaign, node M3-RP5)

**[M3-RP5, 2026-08-27]** (`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6, row M3-RP5):
every μ₃ graded coefficient of a PRODUCT is the convolution of the factors' μ₃ coefficients —
the μ₃ analogue of `C130rp4.s2GradedCoeff_mul` (the μ₂ coefficient-target shape,
`C130rp4.lean:626-709`), with the μ₂ residual multiplicativity `s2NormRes_mul`
(`C130rp9.lean:258-302`) doing the coefficient calculation that `twistRead` arithmetic did at
μ₂.  GENUINELY-NEW mechanism; the informal argument, in full:

## The informal argument

Write `A_j = dev Φ₂ g j`, `B_k = dev Φ₂ z k` for the `Φ₂`-development digits, `μ₂` for the
landed cleared level-two value (`dvSupp (s2Frame) · 5 2`), and fix μ₃ exact grades
`μ₃(g) = β`, `μ₃(z) = β'` (`S2Mu3ExactGrade`, i.e. `dv2Supp L Φ₂ · 21 2 = β, β'`).

1. **Which digit products contribute** (Part 0): digit products have degree
   `≤ 3 + 3 < 8 = 2·deg Φ₂`, so their own `Φ₂`-development stops at index 1 and the `S`-th
   development digit of `g·z` splits into exactly two diagonals,
   `dev Φ₂ (g·z) S = Σ_{j+k=S} (A_j·B_k) %ₘ Φ₂  +  Σ_{j+k=S−1} (A_j·B_k) /ₘ Φ₂` —
   the generalization of `C130rp4.dev_mul_conv_split` from the frame key `Φ′` to an
   arbitrary monic `Ψ` (the proof needed only monicity + positive degree; re-derived here
   because the depth-two side deliberately has no `KeyFrame`).
2. **Why the gate forces the convolution support** (pricing): `dv2Supp g = β` prices every
   slot, `2·μ₂(A_j) + 21j ≥ β`, i.e. `μ₂(A_j) ≥ ⌈(β−21j)/2⌉`.  At the product's on-line
   inner grade `m = (β+β'−21S)/2`:
   * **carry diagonal**: nv3b's sharp quotient bound `μ₂(A_j)+μ₂(B_k) ≤ 10 + μ₂(A_jB_k /ₘ Φ₂)`
     (`s2_le_composedKey_quot_add` + `s2_dvSupp_Φ₂ = 10`) with `j+k = S−1` gives
     `μ₂(quotient) ≥ (m+11) − 10 = m+1` — STRICTLY above `m`, because the odd step `21`
     forces the half-step `⌈(2m+21)/2⌉ = m+11.  Killed by the μ₂ zero-above law.
   * **off-parity main terms** (`j ≢ β (mod 2)`): both round-ups fire,
     `⌈(β−21j)/2⌉+⌈(β'−21k)/2⌉ ≥ m+1` — killed the same way.
   * the surviving on-parity abscissae `j = β%2 + 2t` reindex exactly onto the convolution
     range `t ≤ T` (RP4's abscissa arithmetic).
3. **Where μ₂ residual multiplicativity enters** — twice, and this is the new mechanism:
   (a) *termwise product read*: at exact μ₂ grades, `eval₁ R₂_{m₁+m₂}(A·B) =
   eval₁ R₂_{m₁}(A) · eval₁ R₂_{m₂}(B)` via the strip `R₂_m = N₂ · X^{j₀}` (C130rp8's
   reconstruction; the `X`-power is invisible at the collapsed evaluation point `1`) and the
   UNIVERSAL `s2NormRes_mul` (Cor 4.12(3)); (b) *reduction invisibility*: the main-diagonal
   term is the REDUCED product `(A·B) %ₘ Φ₂ = A·B − Φ₂·Q`, and the discrepancy's read
   `eval₁ R₂_m(Φ₂·Q)` is NOT killed by pricing (nv3b records the bound `μ₂(Φ₂·Q) ≥ m` as
   TIGHT — equality is not landed-forbidden) but by its VALUE: at exact grade the strip and
   `s2NormRes_mul` give `eval₁ N₂(Φ₂)·eval₁ N₂(Q)`, and `N₂(Φ₂) = X + 1`
   (`C130kp5.s2NormRes_composedKey`) evaluates at the collapsed letter `1` to `1 + 1 = 0` in
   the two-element field (`C130rp2.tooth_char_two`).  This is the S2 shadow of the paper's
   own mechanism: `R_{r−1}` of the key vanishes at the evaluation point `z_{r−1}`, which is
   exactly why Definition 3.13's coefficients cannot see reduction modulo `φ_r`.
4. **Where RP4's carry shows up**: the product-side abscissa `S = (β+β')%2 + 2(T+c)` equals
   the factor-abscissa sum `(β%2+2t) + (β'%2+2(T−t))` precisely at `c = s2Mu3Carry β β' =
   (β%2)(β'%2)` (`s2Mu3Carry_parity`); the aux carries an abstract `c` pinned by the linear
   relation (all arithmetic stays `omega`-linear), the headline instantiates.
5. **The ε ≡ 1 collapse kills the ε-bookkeeping — VERIFIED, not assumed**: the coefficient
   `s2Mu3Coeff` carries the ε-factor already collapsed (`s2Mu3Eps ≡ 1`, RP1's
   `s2Mu3EpsOf_eq_one`, proved for EVERY nonzero letter), so the ε-cocycle identity the
   published Definition 3.12/3.13 would require (`ε₂(α)·ε₂(α') / ε₂(α+α')` matching the
   twist) never appears: no statement below mentions ε, and via RP1's letter-display pin
   `s2Mu3Coeff_letter_display` each side of the convolution re-expands to the ε-dressed
   published display for every nonzero candidate letter.  The one leg NOT re-derived here is
   RP1's inherited leg (2): `s2GradedRes = R_{2,α}` remains C130rp1's standing ϖ-read trust
   boundary (OPEN-RP1-TRANSPORT, review queue) — no theorem below consumes it.

## What lands

* Part 0 — `dev_mul_conv_split_monic`: the two-diagonal convolution split at an arbitrary
  monic `Ψ` of positive degree (generalizes `C130rp4.dev_mul_conv_split` off the frame).
* Part 1 — the μ₂-side eval calculus: `s2GradedRes_finsetSum_of_le` (floored finite-sum
  additivity), ★ `eval_one_gradedRes_key_mul` (the `Φ₂`-multiple kill: mechanism 3(b)),
  ★ `eval_one_gradedRes_modByKey` (reduction invisibility), `eval_one_gradedRes_mul_of_exact`
  and ★ `eval_one_gradedRes_mul_of_le` (the floored termwise product read).
* Part 2 — ★ `s2Mu3Coeff_eq_eval_of_le`: the μ₃ FLOOR read — under `μ₃(g) ≥ β` and the line
  equation `2m + 21s = β`, the gated coefficient equals `eval₁ R₂_m(A_s)` with NO gate
  hypothesis (an off-gate slot reads `0` on both sides).  RP1's `s2Mu3Coeff_eq_eval`
  requires the gate; the convolution needs exactly this gate-free form.
* Part 3 — ★ the headline `s2Mu3Coeff_mul` (the row's statement):
  `R₃c_{β+β'}(g·z)(T + (β%2)(β'%2)) = Σ_{t≤T} R₃c_β(g)(t) · R₃c_{β'}(z)(T−t)` at μ₃ exact
  grades, for every `T`; companions `s2Mu3Coeff_mul_zero_of_odd` (the below-twist
  coefficient vanishes in the odd×odd carry genre) and `s2Mu3Coeff_mul_of_prevGrade`
  (plain convolution at even `β'`, published Cor 4.12(2)'s scope) — the exact μ₂ trio's
  shapes (`C130rp4.lean:626-709`) one level up.
* Part 4 — teeth at `g = z = Φ₂` (grade `21+21 = 42`, the odd×odd carry pair):
  `tooth_mu3Coeff_mul_Φ₂Φ₂` (`R₃c₄₂(Φ₂²)(1) = 1`, the convolution firing through RP1's
  landed `tooth_mu3Coeff_Φ₂` on both factors) and `tooth_mu3Coeff_mul_zero_Φ₂Φ₂`
  (`R₃c₄₂(Φ₂²)(0) = 0`, the carry-forced vanish).

## What this node does NOT claim (honesty scope)

* No polynomial-level assembly (`R₃(g·z) = X^c·(R₃(g)·R₃(z))` as a `Polynomial.ext`), no
  `S2Mu3PrevGrade` packaging: M3-RP6 (this file supplies its coefficient inputs).
* No μ₃ normalized operator, no μ₃ grade-of: M3-RP8.
* The identification `s2GradedRes = R_{2,α}` stays RP1's inherited OPEN (leg 2 above).

**DEPENDS.** C132rp4 (`s2Mu3Carry`, `s2Mu3Carry_parity`) · C132rp1 (`s2Mu3Coeff`,
`S2Mu3SlotOnGrade`, `s2Mu3SlotOnGrade_iff`, `s2Mu3Coeff_eq_eval`,
`s2Mu3Coeff_eq_zero_of_grade_lt`, `s2Mu3Coeff_eq_zero_of_dv2Pin_top`, `dv2Hgt_eq_dvSupp`,
`tooth_mu3Coeff_Φ₂`) · C132rp0 (`S2Mu3ExactGrade` + iff/mul, `tooth_Φ₂`) · C132nv3b
(`s2_dvSupp_mul_modByComposedKey_eq`, `s2_le_composedKey_quot_add`, `s2_dvSupp_Φ₂`) ·
C132nv2 (`dv2Supp_le_term`) · C132nv1 (`s2Φ₂_monic`, `s2Φ₂_natDegree`) · C130rp9
(`s2NormRes_mul`) · C130rp8 (`s2NormRes_mul_X_pow_of_exact`) · C130rp2
(`s2GradedRes_add_of_le`, `tooth_char_two`) · C130rp1 (`s2GradedRes_zero_of_above`,
`s2GradedRes_zero`) · C130rp0 (`S2ExactGrade_iff_dvSupp`, `S2AboveGrade_iff_dvSupp`) ·
C130kp5 (`s2NormRes_composedKey`) · C130nv3 (`s2_dvSupp_mul`) · C130s6
(`min_dvSupp_le_dvSupp_add`, `dvSupp_zero_eq_top`) · C130s2 (`s2DepthTwoKeyAt_two`) ·
B.03/B.04/B.05/B35a (`degree_dev_lt`, `dev_eq_zero_of_lt`, `sum_dev_eq`, `dev_mul_pow`,
`dev_mul_pow_of_lt`, `dev_finsetSum`) · C130nv2 (`dev_zero_pin`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`; no statement invented
beyond the row's sketch and the μ₂ trio's shapes.

**Flagged for human review** (parent CLAUDE.md trust boundary — new statements):
`dev_mul_conv_split_monic`, `eval_one_gradedRes_key_mul`, `eval_one_gradedRes_modByKey`,
`eval_one_gradedRes_mul_of_le`, `s2Mu3Coeff_eq_eval_of_le`, `s2Mu3Coeff_mul`,
`s2Mu3Coeff_mul_zero_of_odd`, `s2Mu3Coeff_mul_of_prevGrade`.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C132rp5

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130rp0
open Uniformity.Density.Tower.C130rp1 Uniformity.Density.Tower.C130rp2
open Uniformity.Density.Tower.C130rp8 Uniformity.Density.Tower.C130rp9
open Uniformity.Density.Tower.C130nv3 Uniformity.Density.Tower.C130kp5
open Uniformity.Density.Tower.C132nv1 Uniformity.Density.Tower.C132nv2
open Uniformity.Density.Tower.C132nv3b Uniformity.Density.Tower.C132rp0
open Uniformity.Density.Tower.C132rp1 Uniformity.Density.Tower.C132rp4
open Uniformity.Density.Tower.C80
open Uniformity.Density.Tower.C130nv2 (dev_zero_pin)

section Generic

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-! ## Part 0 — the convolution split of a product development digit, at an arbitrary monic
key

`C130rp4.dev_mul_conv_split` verbatim, with the `KeyFrame` bundling replaced by the bare
hypotheses its proof actually consumes (`Ψ.Monic`, `0 < Ψ.natDegree`) — the depth-two key
`Φ₂` carries no frame, so the frame-based statement cannot fire at μ₃. -/

/-- development digits have degree below the key (with the zero digit included) —
`C130rp4.natDegree_dev_le`, unbundled. -/
private theorem natDegree_dev_le_of_monic {Ψ : Polynomial O} (hΨ : Ψ.Monic)
    (hΨd : 0 < Ψ.natDegree) (f : Polynomial O) (j : ℕ) :
    (dev Ψ f j).natDegree ≤ Ψ.natDegree - 1 := by
  rcases eq_or_ne (dev Ψ f j) 0 with h0 | h0
  · rw [h0, Polynomial.natDegree_zero]
    omega
  · have h := Polynomial.natDegree_lt_natDegree h0 (degree_dev_lt hΨ hΨd f j)
    omega

/-- the development of a two-digit product stops at index 1 — `C130rp4.dev_dev_mul_eq_zero`,
unbundled. -/
private theorem dev_dev_mul_eq_zero_of_monic {Ψ : Polynomial O} (hΨ : Ψ.Monic)
    (hΨd : 0 < Ψ.natDegree) (g z : Polynomial O) (j i : ℕ) {t : ℕ} (ht : 2 ≤ t) :
    dev Ψ (dev Ψ g j * dev Ψ z i) t = 0 := by
  refine dev_eq_zero_of_lt hΨ hΨd _ t ?_
  have h1 := natDegree_dev_le_of_monic hΨ hΨd g j
  have h2 := natDegree_dev_le_of_monic hΨ hΨd z i
  have h3 := Polynomial.natDegree_mul_le (p := dev Ψ g j) (q := dev Ψ z i)
  calc (dev Ψ g j * dev Ψ z i).natDegree
      ≤ (dev Ψ g j).natDegree + (dev Ψ z i).natDegree := h3
    _ < 2 * Ψ.natDegree := by omega
    _ ≤ t * Ψ.natDegree := Nat.mul_le_mul_right _ ht

/-- ★ **the convolution split at an arbitrary monic key** (`C130rp4.dev_mul_conv_split`
generalized off the frame): the `s`-th `Ψ`-development digit of `g·z` is the reduced main
diagonal plus the carry diagonal,
`dev Ψ (g·z) s = Σ_{j≤s} (g_j·z_{s−j}) %ₘ Ψ + Σ_{j≤s−1} dev Ψ (g_j·z_{s−1−j}) 1`. -/
theorem dev_mul_conv_split_monic {Ψ : Polynomial O} (hΨ : Ψ.Monic) (hΨd : 0 < Ψ.natDegree)
    (g z : Polynomial O) (s : ℕ) :
    dev Ψ (g * z) s
      = (∑ j ∈ Finset.range (s + 1), (dev Ψ g j * dev Ψ z (s - j)) %ₘ Ψ)
        + ∑ j ∈ Finset.range s, dev Ψ (dev Ψ g j * dev Ψ z (s - 1 - j)) 1 := by
  classical
  set N := g.natDegree + z.natDegree + 1 + s with hN
  have hgN : g.natDegree < N * Ψ.natDegree :=
    lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right N hΨd)
  have hzN : z.natDegree < N * Ψ.natDegree :=
    lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right N hΨd)
  have hrep : g * z = ∑ p ∈ Finset.range N ×ˢ Finset.range N,
      dev Ψ g p.1 * dev Ψ z p.2 * Ψ ^ (p.1 + p.2) := by
    have h1 : g * z = (∑ j ∈ Finset.range N, dev Ψ g j * Ψ ^ j)
        * (∑ i ∈ Finset.range N, dev Ψ z i * Ψ ^ i) := by
      rw [sum_dev_eq hΨ hΨd g hgN, sum_dev_eq hΨ hΨd z hzN]
    rw [h1, Finset.sum_mul_sum, Finset.sum_product]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
      rw [pow_add]; ring
  have hdev : dev Ψ (g * z) s
      = ∑ p ∈ Finset.range N ×ˢ Finset.range N,
          dev Ψ (dev Ψ g p.1 * dev Ψ z p.2 * Ψ ^ (p.1 + p.2)) s := by
    conv_lhs => rw [hrep]
    exact dev_finsetSum hΨ _ _ s
  have hterm : ∀ p ∈ Finset.range N ×ˢ Finset.range N,
      dev Ψ (dev Ψ g p.1 * dev Ψ z p.2 * Ψ ^ (p.1 + p.2)) s
        = (if p.1 + p.2 = s then (dev Ψ g p.1 * dev Ψ z p.2) %ₘ Ψ else 0)
          + (if p.1 + p.2 + 1 = s
             then dev Ψ (dev Ψ g p.1 * dev Ψ z p.2) 1 else 0) := by
    intro p _
    rcases lt_trichotomy (p.1 + p.2) s with hlt | heq | hgt
    · rcases eq_or_ne (p.1 + p.2 + 1) s with heq1 | hne1
      · rw [if_neg (by omega), if_pos heq1, zero_add]
        have h := dev_mul_pow hΨ (p.1 + p.2) (dev Ψ g p.1 * dev Ψ z p.2) 1
        rw [heq1] at h
        exact h
      · rw [if_neg (by omega), if_neg (by omega), add_zero]
        have h := dev_mul_pow hΨ (p.1 + p.2) (dev Ψ g p.1 * dev Ψ z p.2)
          (s - (p.1 + p.2))
        rw [show p.1 + p.2 + (s - (p.1 + p.2)) = s from by omega] at h
        rw [h]
        exact dev_dev_mul_eq_zero_of_monic hΨ hΨd g z p.1 p.2 (by omega)
    · rw [if_pos heq, if_neg (by omega), add_zero, ← heq]
      have h := dev_mul_pow hΨ (p.1 + p.2) (dev Ψ g p.1 * dev Ψ z p.2) 0
      rw [Nat.add_zero] at h
      rw [h, dev_zero_pin]
    · rw [if_neg (by omega), if_neg (by omega), add_zero]
      exact dev_mul_pow_of_lt hΨ (p.1 + p.2) _ s hgt
  rw [hdev, Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  congr 1
  · rw [← Finset.sum_filter]
    have himg : (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = s)
        = (Finset.range (s + 1)).image (fun j => (j, s - j)) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨⟨hp1, hp2⟩, hsum⟩
        exact ⟨p.1, by omega, by
          rw [Prod.ext_iff]
          exact ⟨rfl, by omega⟩⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨⟨by omega, by omega⟩, by omega⟩
    rw [himg, Finset.sum_image (fun a _ b _ hab => by
      have := congrArg Prod.fst hab
      simpa using this)]
  · rw [← Finset.sum_filter]
    have himg : (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 + 1 = s)
        = (Finset.range s).image (fun j => (j, s - 1 - j)) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨⟨hp1, hp2⟩, hsum⟩
        exact ⟨p.1, by omega, by
          rw [Prod.ext_iff]
          exact ⟨rfl, by omega⟩⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨⟨by omega, by omega⟩, by omega⟩
    rw [himg, Finset.sum_image (fun a _ b _ hab => by
      have := congrArg Prod.fst hab
      simpa using this)]

end Generic

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 1 — the μ₂-side eval calculus

The convolution reads the μ₃ coefficient through `eval 1 ∘ s2GradedRes m`; this part supplies
that composite's sum/product/kill laws.  Private ℕ∞ cast helpers first (the corpus
private-copy genre). -/

private theorem coe_le_add_of_le {a b : ℕ} {x y : ℕ∞} (hx : (a : ℕ∞) ≤ x)
    (hy : (b : ℕ∞) ≤ y) : ((a + b : ℕ) : ℕ∞) ≤ x + y := by
  push_cast
  exact add_le_add hx hy

private theorem coe_lt_add_of_lt_of_le {a b : ℕ} {x y : ℕ∞} (hx : (a : ℕ∞) < x)
    (hy : (b : ℕ∞) ≤ y) : ((a + b : ℕ) : ℕ∞) < x + y := by
  rcases eq_or_ne x ⊤ with rfl | hx'
  · rw [top_add]
    exact lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self (a + b))) le_top
  obtain ⟨u, hu⟩ := ENat.ne_top_iff_exists.1 hx'
  rcases eq_or_ne y ⊤ with rfl | hy'
  · rw [add_top]
    exact lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self (a + b))) le_top
  obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.1 hy'
  rw [← hu] at hx ⊢
  rw [← hv] at hy ⊢
  have h1 : a < u := by exact_mod_cast hx
  have h2' : b ≤ v := by exact_mod_cast hy
  calc ((a + b : ℕ) : ℕ∞) < ((u + v : ℕ) : ℕ∞) := Nat.cast_lt.mpr (by omega)
    _ = (u : ℕ∞) + (v : ℕ∞) := by push_cast; rfl

/-- a common `dvSupp` floor passes to finite sums (`C130s6.min_dvSupp_le_dvSupp_add`,
iterated — the level-two mirror of `C130rp4.le_stageHeight_finsetSum`). -/
private theorem le_dvSupp_finsetSum {ι : Type*} (s : Finset ι) (f : ι → Polynomial O)
    {k : ℕ∞} (hf : ∀ i ∈ s, k ≤ dvSupp (s2Frame h2 hq) (f i) 5 2) :
    k ≤ dvSupp (s2Frame h2 hq) (∑ i ∈ s, f i) 5 2 := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty, dvSupp_zero_eq_top (s2Frame h2 hq) 5 (by norm_num : (0 : ℕ) < 2)]
    exact le_top
  | cons a t hat ih =>
    rw [Finset.sum_cons]
    exact le_trans (le_min (hf a (Finset.mem_cons_self a t))
        (ih fun i hi => hf i (Finset.mem_cons.2 (Or.inr hi))))
      (min_dvSupp_le_dvSupp_add (s2Frame h2 hq) (by norm_num : (0 : ℕ) < 2) _ _)

/-- **floored finite-sum additivity of the μ₂ graded operator**
(`C130rp2.s2GradedRes_add_of_le`, iterated): if every summand's μ₂ support clears `m`, the
grade-`m` residual of the sum is the sum of the residuals. -/
theorem s2GradedRes_finsetSum_of_le {ι : Type*} (s : Finset ι) (f : ι → Polynomial O)
    {m : ℕ} (hf : ∀ i ∈ s, (m : ℕ∞) ≤ dvSupp (s2Frame h2 hq) (f i) 5 2) :
    s2GradedRes h2 hq m (∑ i ∈ s, f i) = ∑ i ∈ s, s2GradedRes h2 hq m (f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact s2GradedRes_zero h2 hq m
  | cons a t hat ih =>
    rw [Finset.sum_cons, Finset.sum_cons,
      s2GradedRes_add_of_le h2 hq (hf a (Finset.mem_cons_self a t))
        (le_dvSupp_finsetSum h2 hq t f fun i hi => hf i (Finset.mem_cons.2 (Or.inr hi))),
      ih fun i hi => hf i (Finset.mem_cons.2 (Or.inr hi))]

/-- ★ **the `Φ₂`-multiple kill** (the file's new mechanism, docstring point 3(b)): any
multiple of the depth-two key, priced at or above the read grade, evaluates to `0` — at
exact grade the strip and the UNIVERSAL `s2NormRes_mul` factor the read through
`N₂(Φ₂) = X + 1` (`C130kp5.s2NormRes_composedKey`), whose value at the collapsed letter `1`
is `1 + 1 = 0` in the two-element field (`C130rp2.tooth_char_two`); above grade the zero law
fires.  The S2 shadow of the paper's "`R_{r−1}(φ_r)` vanishes at `z_{r−1}`". -/
theorem eval_one_gradedRes_key_mul {m : ℕ} (Q : Polynomial O)
    (hm : (m : ℕ∞) ≤ dvSupp (s2Frame h2 hq) (s2DepthTwoKeyAt h2 hq 2 * Q) 5 2) :
    Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
      (s2GradedRes h2 hq m (s2DepthTwoKeyAt h2 hq 2 * Q)) = 0 := by
  rcases lt_or_eq_of_le hm with hlt | heq
  · rw [s2GradedRes_zero_of_above h2 hq ((S2AboveGrade_iff_dvSupp h2 hq).mpr hlt),
      Polynomial.eval_zero]
  · have hex : S2ExactGrade h2 hq m (s2DepthTwoKeyAt h2 hq 2 * Q) :=
      (S2ExactGrade_iff_dvSupp h2 hq).mpr heq.symm
    rw [← s2NormRes_mul_X_pow_of_exact h2 hq hex, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, one_pow, mul_one, s2NormRes_mul h2 hq, Polynomial.eval_mul,
      s2DepthTwoKeyAt_two h2 hq, s2NormRes_composedKey h2 hq, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one, tooth_char_two h2 hq, zero_mul]

/-- ★ **reduction invisibility** (docstring point 3(b), packaged): for short factors
(`deg < 4 = deg Φ₂`), reducing the product modulo `Φ₂` does not change the evaluated grade-`m`
read, for ANY `m` below the product's slot-0 price — the discrepancy `Φ₂·Q` splits off by
floored additivity (its floor is nv3b's sharp quotient bound) and dies by the `Φ₂`-multiple
kill, NOT by pricing. -/
theorem eval_one_gradedRes_modByKey {A B : Polynomial O} (hA : A.natDegree < 4)
    (hB : B.natDegree < 4) {m : ℕ}
    (hm : (m : ℕ∞) ≤ dvSupp (s2Frame h2 hq) A 5 2 + dvSupp (s2Frame h2 hq) B 5 2) :
    Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
        (s2GradedRes h2 hq m ((A * B) %ₘ s2DepthTwoKeyAt h2 hq 2))
      = Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2) (s2GradedRes h2 hq m (A * B)) := by
  have hmodfloor : (m : ℕ∞)
      ≤ dvSupp (s2Frame h2 hq) ((A * B) %ₘ s2DepthTwoKeyAt h2 hq 2) 5 2 := by
    rw [s2_dvSupp_mul_modByComposedKey_eq h2 hq A B hA hB]
    exact hm
  have hquotfloor : (m : ℕ∞) ≤ dvSupp (s2Frame h2 hq)
      (s2DepthTwoKeyAt h2 hq 2 * ((A * B) /ₘ s2DepthTwoKeyAt h2 hq 2)) 5 2 := by
    rw [s2_dvSupp_mul h2 hq]
    exact hm.trans (s2_le_composedKey_quot_add h2 hq A B hA hB)
  conv_rhs => rw [← Polynomial.modByMonic_add_div (A * B) (s2DepthTwoKeyAt h2 hq 2)]
  rw [s2GradedRes_add_of_le h2 hq hmodfloor hquotfloor, Polynomial.eval_add,
    eval_one_gradedRes_key_mul h2 hq _ hquotfloor, add_zero]

/-- **the evaluated termwise product read at exact μ₂ grades** (docstring point 3(a)):
`eval₁ R₂_{m₁+m₂}(A·B) = eval₁ R₂_{m₁}(A) · eval₁ R₂_{m₂}(B)` — the strip is invisible at
`1`, and `s2NormRes_mul` multiplies the normalized reads. -/
theorem eval_one_gradedRes_mul_of_exact {m₁ m₂ : ℕ} {A B : Polynomial O}
    (hA : S2ExactGrade h2 hq m₁ A) (hB : S2ExactGrade h2 hq m₂ B) :
    Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2) (s2GradedRes h2 hq (m₁ + m₂) (A * B))
      = Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2) (s2GradedRes h2 hq m₁ A)
        * Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2) (s2GradedRes h2 hq m₂ B) := by
  have hAB : S2ExactGrade h2 hq (m₁ + m₂) (A * B) := by
    rw [S2ExactGrade_iff_dvSupp h2 hq] at hA hB ⊢
    rw [s2_dvSupp_mul h2 hq, hA, hB]
    push_cast
    ring
  rw [← s2NormRes_mul_X_pow_of_exact h2 hq hAB, ← s2NormRes_mul_X_pow_of_exact h2 hq hA,
    ← s2NormRes_mul_X_pow_of_exact h2 hq hB, s2NormRes_mul h2 hq]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, one_pow, mul_one]

/-- ★ **the FLOORED termwise product read** (the convolution's per-term workhorse): only
support floors `μ₂(A) ≥ m₁`, `μ₂(B) ≥ m₂` are assumed — a strictly-above factor kills BOTH
sides (its own read by the zero law; the product side because μ₂ is multiplicative,
`s2_dvSupp_mul`), and the exact-exact case is the strip/`s2NormRes_mul` read above. -/
theorem eval_one_gradedRes_mul_of_le {m₁ m₂ : ℕ} {A B : Polynomial O}
    (hA : (m₁ : ℕ∞) ≤ dvSupp (s2Frame h2 hq) A 5 2)
    (hB : (m₂ : ℕ∞) ≤ dvSupp (s2Frame h2 hq) B 5 2) :
    Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2) (s2GradedRes h2 hq (m₁ + m₂) (A * B))
      = Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2) (s2GradedRes h2 hq m₁ A)
        * Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2) (s2GradedRes h2 hq m₂ B) := by
  rcases lt_or_eq_of_le hA with hAlt | hAeq
  · have habove : ((m₁ + m₂ : ℕ) : ℕ∞) < dvSupp (s2Frame h2 hq) (A * B) 5 2 := by
      rw [s2_dvSupp_mul h2 hq]
      exact coe_lt_add_of_lt_of_le hAlt hB
    rw [s2GradedRes_zero_of_above h2 hq ((S2AboveGrade_iff_dvSupp h2 hq).mpr habove),
      s2GradedRes_zero_of_above h2 hq ((S2AboveGrade_iff_dvSupp h2 hq).mpr hAlt),
      Polynomial.eval_zero, zero_mul]
  rcases lt_or_eq_of_le hB with hBlt | hBeq
  · have habove : ((m₁ + m₂ : ℕ) : ℕ∞) < dvSupp (s2Frame h2 hq) (A * B) 5 2 := by
      rw [s2_dvSupp_mul h2 hq, add_comm (dvSupp (s2Frame h2 hq) A 5 2)]
      have h := coe_lt_add_of_lt_of_le hBlt hA
      rwa [Nat.add_comm m₂ m₁] at h
    rw [s2GradedRes_zero_of_above h2 hq ((S2AboveGrade_iff_dvSupp h2 hq).mpr habove),
      s2GradedRes_zero_of_above h2 hq ((S2AboveGrade_iff_dvSupp h2 hq).mpr hBlt),
      Polynomial.eval_zero, mul_zero]
  · exact eval_one_gradedRes_mul_of_exact h2 hq
      ((S2ExactGrade_iff_dvSupp h2 hq).mpr hAeq.symm)
      ((S2ExactGrade_iff_dvSupp h2 hq).mpr hBeq.symm)

/-! ## Part 2 — ★ the μ₃ FLOOR read, and the slot pricing floor

RP1's `s2Mu3Coeff_eq_eval` requires the gate to HOLD; the convolution needs the gate-free
form: under only the support floor `μ₃(g) ≥ β` and the line equation `2m + 21s = β`, the
gated coefficient equals the evaluated inner read — an off-gate slot prices strictly above
`m`, so BOTH sides are `0` (the coefficient by its `if`, the read by the zero-above law). -/

private theorem s2Mu3Coeff_eq_zero_of_not_gate {β t : ℕ} {g : Polynomial O}
    (h : ¬ S2Mu3SlotOnGrade h2 hq β g (β % 2 + 2 * t)) :
    s2Mu3Coeff h2 hq β g t = 0 := by
  unfold s2Mu3Coeff
  rw [if_neg h]

/-- **the level-two slot pricing floor** (mirror of `C130rp4.ceil_le_dvHgt_of_le_dvSupp`, one
level up): a cleared μ₃ support floor `β ≤ dv2Supp(f)` prices EVERY `Φ₂`-development slot's
μ₂ value at or above the rounded-up on-line height `⌈(β − 21j)/2⌉` — no line membership,
parity, or range hypothesis. -/
theorem ceil_le_dvSupp_dev {β : ℕ} {f : Polynomial O} (j : ℕ)
    (hβ : (β : ℕ∞) ≤ dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2)
      f 21 2) :
    (((β - 21 * j + 1) / 2 : ℕ) : ℕ∞)
      ≤ dvSupp (s2Frame h2 hq) (dev (s2DepthTwoKeyAt h2 hq 2) f j) 5 2 := by
  have hterm := hβ.trans (dv2Supp_le_term ((s2Tower h2 hq).levelDatum h2)
    (s2Φ₂_monic h2 hq) (by rw [s2Φ₂_natDegree h2 hq]; norm_num) f 21
    (by norm_num : (0 : ℕ) < 2) j)
  rw [dv2Pin, dv2Hgt_eq_dvSupp h2 hq] at hterm
  rcases eq_or_ne (dvSupp (s2Frame h2 hq) (dev (s2DepthTwoKeyAt h2 hq 2) f j) 5 2) ⊤
    with hT | hT
  · rw [hT]
    exact le_top
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hT
  rw [← hc] at hterm ⊢
  have hnat : β ≤ 2 * c + 21 * j := by
    rw [nsmul_eq_mul] at hterm
    exact_mod_cast hterm
  exact_mod_cast (by omega : (β - 21 * j + 1) / 2 ≤ c)

/-- development digits of the depth-two key are short: `natDegree (dev Φ₂ f j) < 4`
(private copy of `C132nv3.natDegree_dev_composedKey_lt_four`, the private-copy pattern). -/
private theorem natDegree_dev_Φ₂_lt (f : Polynomial O) (j : ℕ) :
    (dev (s2DepthTwoKeyAt h2 hq 2) f j).natDegree < 4 := by
  rcases eq_or_ne (dev (s2DepthTwoKeyAt h2 hq 2) f j) 0 with h0 | h0
  · rw [h0, Polynomial.natDegree_zero]
    norm_num
  · have h := Polynomial.natDegree_lt_natDegree h0
      (degree_dev_lt (s2Φ₂_monic h2 hq) (by rw [s2Φ₂_natDegree h2 hq]; norm_num) f j)
    rwa [s2Φ₂_natDegree h2 hq] at h

private theorem natDegree_quot_lt' {A B : Polynomial O} (hA : A.natDegree < 4)
    (hB : B.natDegree < 4) :
    ((A * B) /ₘ s2DepthTwoKeyAt h2 hq 2).natDegree < (s2DepthTwoKeyAt h2 hq 2).natDegree := by
  have hΨdeg : (s2DepthTwoKeyAt h2 hq 2).natDegree = 4 := s2Φ₂_natDegree h2 hq
  rw [Polynomial.natDegree_divByMonic _ (s2Φ₂_monic h2 hq)]
  have h := Polynomial.natDegree_mul_le (p := A) (q := B)
  omega

/-- the carry digit IS the `Φ₂`-quotient (private copy of `C132nv3b.s2_dev_one_eq_quot`). -/
private theorem dev_Φ₂_mul_one {A B : Polynomial O} (hA : A.natDegree < 4)
    (hB : B.natDegree < 4) :
    dev (s2DepthTwoKeyAt h2 hq 2) (A * B) 1 = (A * B) /ₘ s2DepthTwoKeyAt h2 hq 2 := by
  have hunfold : dev (s2DepthTwoKeyAt h2 hq 2) (A * B) 1
      = dev (s2DepthTwoKeyAt h2 hq 2) ((A * B) /ₘ s2DepthTwoKeyAt h2 hq 2) 0 := rfl
  rw [hunfold, dev_zero_pin]
  rcases eq_or_ne ((A * B) /ₘ s2DepthTwoKeyAt h2 hq 2) 0 with h0 | h0
  · rw [h0, Polynomial.zero_modByMonic]
  · exact (Polynomial.modByMonic_eq_self_iff (s2Φ₂_monic h2 hq)).mpr
      (by rw [Polynomial.degree_eq_natDegree h0,
            Polynomial.degree_eq_natDegree (s2Φ₂_monic h2 hq).ne_zero]
          exact_mod_cast natDegree_quot_lt' h2 hq hA hB)

/-- ★ **the μ₃ floor read** (the convolution's gate-free coefficient bridge): with the line
equation `2m + 21·(β%2+2t) = β` and the support floor `(β : ℕ∞) ≤ dv2Supp(g)`, the μ₃
coefficient at index `t` IS the evaluated μ₂ grade-`m` read of the slot digit — with NO gate
hypothesis.  On the gate this is RP1's `s2Mu3Coeff_eq_eval`; off the gate the slot prices
strictly above `m` and both sides vanish. -/
theorem s2Mu3Coeff_eq_eval_of_le {β t m : ℕ} {g : Polynomial O}
    (hm : 2 * m + 21 * (β % 2 + 2 * t) = β)
    (hβ : (β : ℕ∞) ≤ dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2)
      g 21 2) :
    s2Mu3Coeff h2 hq β g t
      = Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
          (s2GradedRes h2 hq m (dev (s2DepthTwoKeyAt h2 hq 2) g (β % 2 + 2 * t))) := by
  have hterm := hβ.trans (dv2Supp_le_term ((s2Tower h2 hq).levelDatum h2)
    (s2Φ₂_monic h2 hq) (by rw [s2Φ₂_natDegree h2 hq]; norm_num) g 21
    (by norm_num : (0 : ℕ) < 2) (β % 2 + 2 * t))
  rcases eq_or_ne (dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g
      (β % 2 + 2 * t)) ⊤ with hT | hT
  · rw [s2Mu3Coeff_eq_zero_of_dv2Pin_top h2 hq hT]
    rw [dv2Pin, dv2Hgt_eq_dvSupp h2 hq] at hT
    have hdv : (m : ℕ∞)
        < dvSupp (s2Frame h2 hq) (dev (s2DepthTwoKeyAt h2 hq 2) g (β % 2 + 2 * t)) 5 2 := by
      rw [hT]
      exact lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self m)) le_top
    rw [s2GradedRes_zero_of_above h2 hq ((S2AboveGrade_iff_dvSupp h2 hq).mpr hdv),
      Polynomial.eval_zero]
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hT
    have hle : m ≤ n := by
      rw [← hn, nsmul_eq_mul] at hterm
      have hnat : β ≤ 2 * n + 21 * (β % 2 + 2 * t) := by exact_mod_cast hterm
      omega
    rcases eq_or_lt_of_le hle with heq | hlt
    · exact s2Mu3Coeff_eq_eval h2 hq
        ((s2Mu3SlotOnGrade_iff h2 hq).mpr
          ⟨m, by rw [← hn]; exact_mod_cast congrArg Nat.cast heq.symm, by omega⟩)
        (by rw [← hn]; exact_mod_cast congrArg Nat.cast heq.symm)
    · have hnotgate : ¬ S2Mu3SlotOnGrade h2 hq β g (β % 2 + 2 * t) := by
        intro hgate
        obtain ⟨m', hm', hβ'⟩ := (s2Mu3SlotOnGrade_iff h2 hq).mp hgate
        rw [← hn] at hm'
        have hnm' : n = m' := by exact_mod_cast hm'
        omega
      rw [s2Mu3Coeff_eq_zero_of_not_gate h2 hq hnotgate]
      have hpin : dvSupp (s2Frame h2 hq) (dev (s2DepthTwoKeyAt h2 hq 2) g (β % 2 + 2 * t))
          5 2 = (n : ℕ∞) := by
        have h' := hn.symm
        rw [dv2Pin, dv2Hgt_eq_dvSupp h2 hq] at h'
        exact h'
      have hdv : (m : ℕ∞)
          < dvSupp (s2Frame h2 hq) (dev (s2DepthTwoKeyAt h2 hq 2) g (β % 2 + 2 * t)) 5 2 := by
        rw [hpin]
        exact_mod_cast hlt
      rw [s2GradedRes_zero_of_above h2 hq ((S2AboveGrade_iff_dvSupp h2 hq).mpr hdv),
        Polynomial.eval_zero]

/-! ## Part 3 — ★ NODE M3-RP5: the μ₃ coefficient convolution

The auxiliary form carries the carry as an ABSTRACT `c` pinned by the linear parity relation
(so every arithmetic goal stays `omega`-linear, mirroring `C130rp4.s2GradedCoeff_mul_aux`);
the public headline instantiates `c = s2Mu3Carry β β'` through RP4's `s2Mu3Carry_parity`. -/

private theorem s2Mu3Coeff_mul_aux {β β' c : ℕ} {g z : Polynomial O}
    (hg : S2Mu3ExactGrade h2 hq β g) (hz : S2Mu3ExactGrade h2 hq β' z)
    (hcpar : β % 2 + β' % 2 = (β + β') % 2 + 2 * c) (T : ℕ) :
    s2Mu3Coeff h2 hq (β + β') (g * z) (T + c)
      = ∑ t ∈ Finset.range (T + 1),
          s2Mu3Coeff h2 hq β g t * s2Mu3Coeff h2 hq β' z (T - t) := by
  have hsg : dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2
      = (β : ℕ∞) := (S2Mu3ExactGrade_iff_dv2Supp h2 hq).mp hg
  have hsz : dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) z 21 2
      = (β' : ℕ∞) := (S2Mu3ExactGrade_iff_dv2Supp h2 hq).mp hz
  have hsgz : dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) (g * z) 21 2
      = ((β + β' : ℕ) : ℕ∞) :=
    (S2Mu3ExactGrade_iff_dv2Supp h2 hq).mp (S2Mu3ExactGrade_mul h2 hq hg hz)
  rcases Nat.lt_or_ge (β + β') (21 * ((β + β') % 2 + 2 * (T + c))) with hcase | hcase
  · -- the grade line is exhausted: both sides vanish
    rw [s2Mu3Coeff_eq_zero_of_grade_lt h2 hq hcase]
    refine (Finset.sum_eq_zero fun t ht => ?_).symm
    rw [Finset.mem_range] at ht
    rcases (by omega : β < 21 * (β % 2 + 2 * t) ∨ β' < 21 * (β' % 2 + 2 * (T - t)))
      with h | h
    · rw [s2Mu3Coeff_eq_zero_of_grade_lt h2 hq h, zero_mul]
    · rw [s2Mu3Coeff_eq_zero_of_grade_lt h2 hq h, mul_zero]
  · -- the convolution case: read the product through the μ₃ floor read
    obtain ⟨m, hm⟩ : ∃ m, 2 * m + 21 * ((β + β') % 2 + 2 * (T + c)) = β + β' :=
      ⟨(β + β' - 21 * ((β + β') % 2 + 2 * (T + c))) / 2, by omega⟩
    rw [s2Mu3Coeff_eq_eval_of_le h2 hq hm (le_of_eq hsgz.symm),
      dev_mul_conv_split_monic (s2Φ₂_monic h2 hq) (by rw [s2Φ₂_natDegree h2 hq]; norm_num)
        g z ((β + β') % 2 + 2 * (T + c))]
    obtain ⟨S, hSdef⟩ : ∃ S, (β + β') % 2 + 2 * (T + c) = S := ⟨_, rfl⟩
    rw [hSdef] at hm ⊢
    -- per-slot floors on the two diagonals
    have hmainfloor : ∀ j ∈ Finset.range (S + 1),
        (m : ℕ∞) ≤ dvSupp (s2Frame h2 hq)
          ((dev (s2DepthTwoKeyAt h2 hq 2) g j * dev (s2DepthTwoKeyAt h2 hq 2) z (S - j))
            %ₘ s2DepthTwoKeyAt h2 hq 2) 5 2 := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [s2_dvSupp_mul_modByComposedKey_eq h2 hq _ _ (natDegree_dev_Φ₂_lt h2 hq g j)
        (natDegree_dev_Φ₂_lt h2 hq z (S - j))]
      refine le_trans (Nat.cast_le.mpr (show m ≤ (β - 21 * j + 1) / 2
          + (β' - 21 * (S - j) + 1) / 2 from by omega)) ?_
      exact coe_le_add_of_le (ceil_le_dvSupp_dev h2 hq j (le_of_eq hsg.symm))
        (ceil_le_dvSupp_dev h2 hq (S - j) (le_of_eq hsz.symm))
    have hcarryfloor : ∀ j ∈ Finset.range S,
        ((m + 1 : ℕ) : ℕ∞) ≤ dvSupp (s2Frame h2 hq)
          (dev (s2DepthTwoKeyAt h2 hq 2)
            (dev (s2DepthTwoKeyAt h2 hq 2) g j * dev (s2DepthTwoKeyAt h2 hq 2) z (S - 1 - j))
            1) 5 2 := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [dev_Φ₂_mul_one h2 hq (natDegree_dev_Φ₂_lt h2 hq g j)
        (natDegree_dev_Φ₂_lt h2 hq z (S - 1 - j))]
      have hsharp := s2_le_composedKey_quot_add h2 hq _ _ (natDegree_dev_Φ₂_lt h2 hq g j)
        (natDegree_dev_Φ₂_lt h2 hq z (S - 1 - j))
      rw [s2_dvSupp_Φ₂ h2 hq] at hsharp
      have hsum := le_trans (coe_le_add_of_le
        (ceil_le_dvSupp_dev h2 hq j (le_of_eq hsg.symm))
        (ceil_le_dvSupp_dev h2 hq (S - 1 - j) (le_of_eq hsz.symm))) hsharp
      rcases eq_or_ne (dvSupp (s2Frame h2 hq)
          ((dev (s2DepthTwoKeyAt h2 hq 2) g j * dev (s2DepthTwoKeyAt h2 hq 2) z (S - 1 - j))
            /ₘ s2DepthTwoKeyAt h2 hq 2) 5 2) ⊤ with hT | hT
      · rw [hT]
        exact le_top
      obtain ⟨q, hq'⟩ := ENat.ne_top_iff_exists.1 hT
      rw [← hq'] at hsum ⊢
      have hnat : (β - 21 * j + 1) / 2 + (β' - 21 * (S - 1 - j) + 1) / 2 ≤ 10 + q := by
        rw [show (10 : ℕ∞) + (q : ℕ∞) = ((10 + q : ℕ) : ℕ∞) from by push_cast; rfl] at hsum
        exact_mod_cast hsum
      exact_mod_cast (show m + 1 ≤ q from by omega)
    -- split the read: floored additivity over the two diagonals, then over each sum
    rw [s2GradedRes_add_of_le h2 hq
        (le_dvSupp_finsetSum h2 hq _ _ hmainfloor)
        (le_dvSupp_finsetSum h2 hq _ _ fun j hj =>
          le_trans (Nat.cast_le.mpr (Nat.le_succ m)) (hcarryfloor j hj)),
      Polynomial.eval_add,
      s2GradedRes_finsetSum_of_le h2 hq _ _ hmainfloor,
      s2GradedRes_finsetSum_of_le h2 hq _ _ (fun j hj =>
        le_trans (Nat.cast_le.mpr (Nat.le_succ m)) (hcarryfloor j hj)),
      Polynomial.eval_finsetSum, Polynomial.eval_finsetSum]
    -- the carry diagonal reads zero: it prices STRICTLY above the line
    have hcarryzero : (∑ j ∈ Finset.range S,
        Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2) (s2GradedRes h2 hq m
          (dev (s2DepthTwoKeyAt h2 hq 2)
            (dev (s2DepthTwoKeyAt h2 hq 2) g j * dev (s2DepthTwoKeyAt h2 hq 2) z (S - 1 - j))
            1))) = 0 :=
      Finset.sum_eq_zero fun j hj => by
        rw [s2GradedRes_zero_of_above h2 hq ((S2AboveGrade_iff_dvSupp h2 hq).mpr
          (lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self m)) (hcarryfloor j hj))),
          Polynomial.eval_zero]
    rw [hcarryzero, add_zero]
    -- the main diagonal: off-parity terms read zero, on-parity terms reindex to `t`
    have hoff : ∀ j ∈ Finset.range (S + 1),
        Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2) (s2GradedRes h2 hq m
          ((dev (s2DepthTwoKeyAt h2 hq 2) g j * dev (s2DepthTwoKeyAt h2 hq 2) z (S - j))
            %ₘ s2DepthTwoKeyAt h2 hq 2)) ≠ 0 → j % 2 = β % 2 := by
      intro j hj hne
      rw [Finset.mem_range] at hj
      by_contra hpar
      refine hne ?_
      have habove : (m : ℕ∞) < dvSupp (s2Frame h2 hq)
          ((dev (s2DepthTwoKeyAt h2 hq 2) g j * dev (s2DepthTwoKeyAt h2 hq 2) z (S - j))
            %ₘ s2DepthTwoKeyAt h2 hq 2) 5 2 := by
        rw [s2_dvSupp_mul_modByComposedKey_eq h2 hq _ _ (natDegree_dev_Φ₂_lt h2 hq g j)
          (natDegree_dev_Φ₂_lt h2 hq z (S - j))]
        refine lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self m)) ?_
        refine le_trans (Nat.cast_le.mpr (show m + 1 ≤ (β - 21 * j + 1) / 2
            + (β' - 21 * (S - j) + 1) / 2 from by omega)) ?_
        exact coe_le_add_of_le (ceil_le_dvSupp_dev h2 hq j (le_of_eq hsg.symm))
          (ceil_le_dvSupp_dev h2 hq (S - j) (le_of_eq hsz.symm))
      rw [s2GradedRes_zero_of_above h2 hq ((S2AboveGrade_iff_dvSupp h2 hq).mpr habove),
        Polynomial.eval_zero]
    rw [← Finset.sum_filter_of_ne hoff]
    have himg : (Finset.range (S + 1)).filter (fun j => j % 2 = β % 2)
        = (Finset.range (T + 1)).image (fun t => β % 2 + 2 * t) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hj, hpar⟩
        exact ⟨j / 2, by omega, by omega⟩
      · rintro ⟨t, ht, rfl⟩
        omega
    rw [himg, Finset.sum_image (fun a _ b _ hab => by omega)]
    -- termwise: the surviving read IS the product of μ₃ coefficients
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_range] at ht
    rw [show S - (β % 2 + 2 * t) = β' % 2 + 2 * (T - t) from by omega]
    rcases Nat.lt_or_ge β (21 * (β % 2 + 2 * t)) with hbig | hok
    · -- the g-side slot is past its grade line: both sides vanish
      have habove : (m : ℕ∞) < dvSupp (s2Frame h2 hq)
          ((dev (s2DepthTwoKeyAt h2 hq 2) g (β % 2 + 2 * t)
              * dev (s2DepthTwoKeyAt h2 hq 2) z (β' % 2 + 2 * (T - t)))
            %ₘ s2DepthTwoKeyAt h2 hq 2) 5 2 := by
        rw [s2_dvSupp_mul_modByComposedKey_eq h2 hq _ _
          (natDegree_dev_Φ₂_lt h2 hq g (β % 2 + 2 * t))
          (natDegree_dev_Φ₂_lt h2 hq z (β' % 2 + 2 * (T - t)))]
        refine lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self m)) ?_
        refine le_trans (Nat.cast_le.mpr (show m + 1 ≤ (β - 21 * (β % 2 + 2 * t) + 1) / 2
            + (β' - 21 * (β' % 2 + 2 * (T - t)) + 1) / 2 from by omega)) ?_
        exact coe_le_add_of_le
          (ceil_le_dvSupp_dev h2 hq (β % 2 + 2 * t) (le_of_eq hsg.symm))
          (ceil_le_dvSupp_dev h2 hq (β' % 2 + 2 * (T - t)) (le_of_eq hsz.symm))
      rw [s2Mu3Coeff_eq_zero_of_grade_lt h2 hq hbig, zero_mul,
        s2GradedRes_zero_of_above h2 hq ((S2AboveGrade_iff_dvSupp h2 hq).mpr habove),
        Polynomial.eval_zero]
    rcases Nat.lt_or_ge β' (21 * (β' % 2 + 2 * (T - t))) with hbig' | hok'
    · -- the z-side slot is past its grade line: both sides vanish
      have habove : (m : ℕ∞) < dvSupp (s2Frame h2 hq)
          ((dev (s2DepthTwoKeyAt h2 hq 2) g (β % 2 + 2 * t)
              * dev (s2DepthTwoKeyAt h2 hq 2) z (β' % 2 + 2 * (T - t)))
            %ₘ s2DepthTwoKeyAt h2 hq 2) 5 2 := by
        rw [s2_dvSupp_mul_modByComposedKey_eq h2 hq _ _
          (natDegree_dev_Φ₂_lt h2 hq g (β % 2 + 2 * t))
          (natDegree_dev_Φ₂_lt h2 hq z (β' % 2 + 2 * (T - t)))]
        refine lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self m)) ?_
        refine le_trans (Nat.cast_le.mpr (show m + 1 ≤ (β - 21 * (β % 2 + 2 * t) + 1) / 2
            + (β' - 21 * (β' % 2 + 2 * (T - t)) + 1) / 2 from by omega)) ?_
        exact coe_le_add_of_le
          (ceil_le_dvSupp_dev h2 hq (β % 2 + 2 * t) (le_of_eq hsg.symm))
          (ceil_le_dvSupp_dev h2 hq (β' % 2 + 2 * (T - t)) (le_of_eq hsz.symm))
      rw [s2Mu3Coeff_eq_zero_of_grade_lt h2 hq hbig', mul_zero,
        s2GradedRes_zero_of_above h2 hq ((S2AboveGrade_iff_dvSupp h2 hq).mpr habove),
        Polynomial.eval_zero]
    · -- both slots at or below their lines: the survival core fires
      have hj2 : 2 * ((β - 21 * (β % 2 + 2 * t)) / 2) + 21 * (β % 2 + 2 * t) = β := by
        omega
      have hk2 : 2 * ((β' - 21 * (β' % 2 + 2 * (T - t))) / 2)
          + 21 * (β' % 2 + 2 * (T - t)) = β' := by omega
      rw [s2Mu3Coeff_eq_eval_of_le h2 hq hj2 (le_of_eq hsg.symm),
        s2Mu3Coeff_eq_eval_of_le h2 hq hk2 (le_of_eq hsz.symm)]
      have hf1 : (((β - 21 * (β % 2 + 2 * t)) / 2 : ℕ) : ℕ∞)
          ≤ dvSupp (s2Frame h2 hq) (dev (s2DepthTwoKeyAt h2 hq 2) g (β % 2 + 2 * t)) 5 2 :=
        le_trans (Nat.cast_le.mpr (by omega))
          (ceil_le_dvSupp_dev h2 hq (β % 2 + 2 * t) (le_of_eq hsg.symm))
      have hf2 : (((β' - 21 * (β' % 2 + 2 * (T - t))) / 2 : ℕ) : ℕ∞)
          ≤ dvSupp (s2Frame h2 hq)
              (dev (s2DepthTwoKeyAt h2 hq 2) z (β' % 2 + 2 * (T - t))) 5 2 :=
        le_trans (Nat.cast_le.mpr (by omega))
          (ceil_le_dvSupp_dev h2 hq (β' % 2 + 2 * (T - t)) (le_of_eq hsz.symm))
      rw [eval_one_gradedRes_modByKey h2 hq (natDegree_dev_Φ₂_lt h2 hq g (β % 2 + 2 * t))
          (natDegree_dev_Φ₂_lt h2 hq z (β' % 2 + 2 * (T - t)))
          (le_trans (Nat.cast_le.mpr (show m ≤ (β - 21 * (β % 2 + 2 * t)) / 2
              + (β' - 21 * (β' % 2 + 2 * (T - t))) / 2 from by omega))
            (coe_le_add_of_le hf1 hf2)),
        show m = (β - 21 * (β % 2 + 2 * t)) / 2
            + (β' - 21 * (β' % 2 + 2 * (T - t))) / 2 from by omega]
      exact eval_one_gradedRes_mul_of_le h2 hq hf1 hf2

/-- ★ **NODE M3-RP5, the headline — the μ₃ recursive coefficient convolution** (the row's
statement; the μ₃ analogue of `C130rp4.s2GradedCoeff_mul`, with RP4's carry): at μ₃ exact
grades, for EVERY `T`,
`R₃c_{β+β′}(g·z)(T + (β%2)(β′%2)) = Σ_{t≤T} R₃c_β(g)(t) · R₃c_{β′}(z)(T−t)`. -/
theorem s2Mu3Coeff_mul {β β' : ℕ} {g z : Polynomial O}
    (hg : S2Mu3ExactGrade h2 hq β g) (hz : S2Mu3ExactGrade h2 hq β' z) (T : ℕ) :
    s2Mu3Coeff h2 hq (β + β') (g * z) (T + s2Mu3Carry β β')
      = ∑ t ∈ Finset.range (T + 1),
          s2Mu3Coeff h2 hq β g t * s2Mu3Coeff h2 hq β' z (T - t) :=
  s2Mu3Coeff_mul_aux h2 hq hg hz (s2Mu3Carry_parity β β') T

/-- ★ **the below-twist coefficient vanishes** (the odd×odd carry companion, mirror of
`C130rp4.s2GradedCoeff_mul_zero_of_odd`): in the carry genre the product's index-`0`
coefficient is `0` — its single slot `0` prices strictly above the line (the two odd
half-gaps merge into a full step). -/
theorem s2Mu3Coeff_mul_zero_of_odd {β β' : ℕ} {g z : Polynomial O}
    (hg : S2Mu3ExactGrade h2 hq β g) (hz : S2Mu3ExactGrade h2 hq β' z)
    (hβ : β % 2 = 1) (hβ' : β' % 2 = 1) :
    s2Mu3Coeff h2 hq (β + β') (g * z) 0 = 0 := by
  have hsg : dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2
      = (β : ℕ∞) := (S2Mu3ExactGrade_iff_dv2Supp h2 hq).mp hg
  have hsz : dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) z 21 2
      = (β' : ℕ∞) := (S2Mu3ExactGrade_iff_dv2Supp h2 hq).mp hz
  have hsgz : dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) (g * z) 21 2
      = ((β + β' : ℕ) : ℕ∞) :=
    (S2Mu3ExactGrade_iff_dv2Supp h2 hq).mp (S2Mu3ExactGrade_mul h2 hq hg hz)
  rw [s2Mu3Coeff_eq_eval_of_le h2 hq
      (show 2 * ((β + β') / 2) + 21 * ((β + β') % 2 + 2 * 0) = β + β' from by omega)
      (le_of_eq hsgz.symm),
    show (β + β') % 2 + 2 * 0 = 0 from by omega,
    dev_mul_conv_split_monic (s2Φ₂_monic h2 hq) (by rw [s2Φ₂_natDegree h2 hq]; norm_num)
      g z 0,
    Finset.range_one, Finset.sum_singleton, Finset.range_zero, Finset.sum_empty, add_zero,
    show (0 : ℕ) - 0 = 0 from rfl]
  have habove : (((β + β') / 2 : ℕ) : ℕ∞) < dvSupp (s2Frame h2 hq)
      ((dev (s2DepthTwoKeyAt h2 hq 2) g 0 * dev (s2DepthTwoKeyAt h2 hq 2) z 0)
        %ₘ s2DepthTwoKeyAt h2 hq 2) 5 2 := by
    rw [s2_dvSupp_mul_modByComposedKey_eq h2 hq _ _ (natDegree_dev_Φ₂_lt h2 hq g 0)
      (natDegree_dev_Φ₂_lt h2 hq z 0)]
    refine lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self ((β + β') / 2))) ?_
    refine le_trans (Nat.cast_le.mpr (show (β + β') / 2 + 1 ≤ (β - 21 * 0 + 1) / 2
        + (β' - 21 * 0 + 1) / 2 from by omega)) ?_
    exact coe_le_add_of_le (ceil_le_dvSupp_dev h2 hq 0 (le_of_eq hsg.symm))
      (ceil_le_dvSupp_dev h2 hq 0 (le_of_eq hsz.symm))
  rw [s2GradedRes_zero_of_above h2 hq ((S2AboveGrade_iff_dvSupp h2 hq).mpr habove),
    Polynomial.eval_zero]

/-- **the PrevGrade specialization** (published Cor 4.12(2)'s scope at the μ₃ occurrence,
mirror of `C130rp4.s2GradedCoeff_mul_of_prevGrade`): an even second grade gives the PLAIN
convolution at every index — no carry shift. -/
theorem s2Mu3Coeff_mul_of_prevGrade {β β' : ℕ} {g z : Polynomial O}
    (hg : S2Mu3ExactGrade h2 hq β g) (hz : S2Mu3ExactGrade h2 hq β' z)
    (hβ' : β' % 2 = 0) (T : ℕ) :
    s2Mu3Coeff h2 hq (β + β') (g * z) T
      = ∑ t ∈ Finset.range (T + 1),
          s2Mu3Coeff h2 hq β g t * s2Mu3Coeff h2 hq β' z (T - t) := by
  have h := s2Mu3Coeff_mul_aux h2 hq hg hz (c := 0) (by omega) T
  rwa [Nat.add_zero] at h

/-! ## Part 4 — teeth at the odd×odd carry pair `g = z = Φ₂` (grade `21 + 21 = 42`)

The convolution firing through TWO landed teeth: RP0's `tooth_Φ₂` supplies the exact grades,
RP1's `tooth_mu3Coeff_Φ₂` the factor values, RP4's `tooth_carry_Φ₂Φ₂` the carry `1`. -/

/-- **tooth (the convolution computes, carry genre)**: `R₃c₄₂(Φ₂·Φ₂)(1) = 1` — index
`0 + carry = 1`, value `1·1`. -/
theorem tooth_mu3Coeff_mul_Φ₂Φ₂ :
    s2Mu3Coeff h2 hq 42
      ((s2DepthTwoKeyAt h2 hq 2 : Polynomial O) * s2DepthTwoKeyAt h2 hq 2) 1 = 1 := by
  have h := s2Mu3Coeff_mul h2 hq (tooth_Φ₂ h2 hq) (tooth_Φ₂ h2 hq) 0
  rw [Finset.range_one, Finset.sum_singleton, tooth_carry_Φ₂Φ₂] at h
  norm_num [tooth_mu3Coeff_Φ₂ h2 hq] at h
  exact h

/-- **tooth (the below-twist vanish fires)**: `R₃c₄₂(Φ₂·Φ₂)(0) = 0` — the odd×odd
carry-forced zero at the landed pair. -/
theorem tooth_mu3Coeff_mul_zero_Φ₂Φ₂ :
    s2Mu3Coeff h2 hq 42
      ((s2DepthTwoKeyAt h2 hq 2 : Polynomial O) * s2DepthTwoKeyAt h2 hq 2) 0 = 0 := by
  have h := s2Mu3Coeff_mul_zero_of_odd h2 hq (tooth_Φ₂ h2 hq) (tooth_Φ₂ h2 hq)
    (by norm_num) (by norm_num)
  norm_num at h
  exact h

end S2

end Uniformity.Density.Tower.C132rp5

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C132rp5.dev_mul_conv_split_monic
#print axioms Uniformity.Density.Tower.C132rp5.s2GradedRes_finsetSum_of_le
#print axioms Uniformity.Density.Tower.C132rp5.eval_one_gradedRes_key_mul
#print axioms Uniformity.Density.Tower.C132rp5.eval_one_gradedRes_modByKey
#print axioms Uniformity.Density.Tower.C132rp5.eval_one_gradedRes_mul_of_exact
#print axioms Uniformity.Density.Tower.C132rp5.eval_one_gradedRes_mul_of_le
#print axioms Uniformity.Density.Tower.C132rp5.ceil_le_dvSupp_dev
#print axioms Uniformity.Density.Tower.C132rp5.s2Mu3Coeff_eq_eval_of_le
#print axioms Uniformity.Density.Tower.C132rp5.s2Mu3Coeff_mul
#print axioms Uniformity.Density.Tower.C132rp5.s2Mu3Coeff_mul_zero_of_odd
#print axioms Uniformity.Density.Tower.C132rp5.s2Mu3Coeff_mul_of_prevGrade
#print axioms Uniformity.Density.Tower.C132rp5.tooth_mu3Coeff_mul_Φ₂Φ₂
#print axioms Uniformity.Density.Tower.C132rp5.tooth_mu3Coeff_mul_zero_Φ₂Φ₂

end AxCheck
