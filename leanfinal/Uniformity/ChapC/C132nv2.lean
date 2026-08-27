/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130nv2
import Uniformity.ChapC.C132nv0
import Uniformity.ChapC.C132nv1

/-!
# Uniformity.ChapC.C132nv2 — the `dv2Supp` outer endpoint/minimizer bank (μ₃ campaign, node M3-NV2)

**[M3-NV2, 2026-08-27]** (`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6, row M3-NV2): ports
the parameter-free endpoint/minimizer bank (C.07 + `C130nv2`'s Part 1) and the
convolution-pricing bank (`C130nv2.lean:475-784`'s term estimates and endpoint assembly, and
the "generic once one supplies survival" pattern of `C130nv3.lean:153-210`) ONE LEVEL UP, from
`dvSupp`/`F.key` to `dv2Supp`/`Ψ`, leaving ONE explicit hypothesis, `Dv2ResSurv`.

## Why a hypothesis is unavoidable here (and why it is exactly one)

At level 1, `F.stageHeight` is a genuine valuation pulled back from the leaf prime `X`
(`stageHeight_mul`, `C130nv2.lean:203`), and the one-step MacLane expansion
(`stageHeight_le_modByMonic`/`stageHeight_le_divByMonic`, `C130nv2.lean:296-376`) is proved from
`X`'s purity — a **degree bookkeeping** argument with no level-2 analogue, because `dv2Hgt L A :=
dvSupp F A L.u L.ℓ` (C.11) is a level-1 SUPPORT (an `inf`, C.06), not a valuation: `dvSupp` is
only "≥"-multiplicative unconditionally (`dvSupp_add_le_dvSupp_mul`) and EXACTLY multiplicative
conditional on its own endpoint survival (`dvSupp_mul_eq_add_of_endpoint_le`) — this is precisely
the NV0–NV4 story one level down. So `dv2Hgt`'s behaviour on a Ψ-development digit PRODUCT
cannot be derived generically; it is exactly the campaign's own "μ₂-residual survival" content
(§5: "survival must be proved from the landed μ₂ normalized residual product"), landed
separately at node M3-NV3 (`s2NormRes_mul`, degree-`<4` coefficients).

**`Dv2ResSurv L Ψ u₂ ℓ₂`** (below) packages, as ONE named hypothesis, exactly the two facts
`le_line_dev2_term`/`lt_line_dev2_term` need about a digit PRODUCT's own `Ψ`-development (slots
`0` and `1` — a digit product has degree `< 2·deg Ψ`, so `dev` beyond slot `1` is definitionally
`0`, `dv2Hgt`-free by `dv2Hgt_zero`): the EXACT value at the reduced slot (mirroring NV3's
"reduction modulo `Φ₂` preserves the product ... value") and the STRICT slot-`1` carry bound
(mirroring `lt_weight_dev_slot`'s conclusion, `C130nv2.lean:441-468`, but stated directly in the
digit heights rather than derived from admissibility, since `dv2Hgt` has no key-height numeral
to be admissible against here). Every other declaration in this file is UNCONDITIONAL,
parameter-free (no S2 numeral, no concrete `u₂`/`ℓ₂`), and mirrors its `dvSupp` counterpart by
substitution `F.stageHeight ↦ dv2Hgt L`, `F.key ↦ Ψ`, `dvHgt F ↦ dv2Pin L Ψ`,
`dvSupp F ↦ dv2Supp L Ψ`, `DvOnSide F ↦ Dv2OnSide L Ψ`, `dvSideSet/dvSideMin F ↦
dv2SideSet/dv2SideMin L Ψ`.

## What this node does NOT claim (honesty scope)

No unconditional level-two product law for `dv2Supp` — that needs `Dv2ResSurv` as an explicit
premise, discharged only at node M3-NV3 (not here). This file states no theorem about a
concrete `Ψ` (e.g. `Φ₂`); the numeral instantiation is M3-NV4's job.

**DEPENDS.** C132nv0 (`dv2Pin_top_of_gt`, `dv2Supp` bank) · C132nv1 (imported for the chain
head, per the campaign row; not directly consumed) · C130nv2 (`weight_read`, the cast-cleared
`(u,ℓ)`-weight normal form — pure `ℕ∞` arithmetic, no frame dependence) · B.02–B.05/B35a
(`dev`, `dev_mul_pow`, `dev_mul_pow_of_lt`, `dev_zero_pin`, `dev_eq_zero_of_lt`, `dev_of_zero`,
generic over any monic divisor).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement invented
beyond the row's sketch (the one explicit hypothesis is documented above and named, never
smuggled in as a silent premise).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C132nv2

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C132nv0
open Uniformity.Density.Tower.C130nv2 (weight_read succ_le_of_weight_succ_le)

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## Part 0 — free shims: `dv2Hgt`'s zero and ultrametric-add, read off the level-1 bank -/

/-- `dv2Hgt` of `0` is `⊤` (mirror of `KeyFrame.stageHeight_zero`; free from `dv2Hgt`'s
definition as `dvSupp F · L.u L.ℓ` and C130s6's `dvSupp_zero_eq_top`). -/
theorem dv2Hgt_zero {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) :
    dv2Hgt L (0 : Polynomial O) = ⊤ := dvSupp_zero_eq_top F L.u L.hℓ

/-- The ultrametric inequality for `dv2Hgt` (mirror of `KeyFrame.min_stageHeight_le_add`;
free from `dv2Hgt`'s definition and C130s6's `min_dvSupp_le_dvSupp_add`). -/
theorem min_dv2Hgt_le_dv2Hgt_add {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (A B : Polynomial O) :
    min (dv2Hgt L A) (dv2Hgt L B) ≤ dv2Hgt L (A + B) :=
  min_dvSupp_le_dvSupp_add F L.hℓ A B

/-- The ultrametric EQUALITY off ties for `dv2Hgt` (mirror of C130s6's `dvSupp_add_eq`; free
from `dv2Hgt`'s definition). -/
theorem dv2Hgt_add_eq {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {A B : Polynomial O} (hne : dv2Hgt L A ≠ dv2Hgt L B) :
    dv2Hgt L (A + B) = min (dv2Hgt L A) (dv2Hgt L B) :=
  dvSupp_add_eq F L.hℓ hne

/-! ## Part 1 — the minimizer choice at `dv2Supp`: `Dv2OnSide`, `dv2SideSet`, `dv2SideMin`

Pure combinatorics (mirror of C.07 + `C130nv2`'s Part 1): the only fact consumed about the
underlying height is `dv2Pin_top_of_gt` (C132nv0), which excludes past-degree abscissae from
the side exactly as `dvHgt_eq_top_of_natDegree_lt` did one level down. No new mathematics. -/

/-- **The on-side predicate at the `dv2`-level.** The abscissa `j` attains the cleared level-2
support at slope `−u₂/ℓ₂`, AND its level-2 pin is finite (mirror of C.07(a)). -/
def Dv2OnSide {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) (Ψ f : Polynomial O)
    (u₂ ℓ₂ j : ℕ) : Prop :=
  dv2Supp L Ψ f u₂ ℓ₂ = ℓ₂ • dv2Pin L Ψ f j + (u₂ * j : ℕ∞) ∧ dv2Pin L Ψ f j ≠ ⊤

/-- **The on-side abscissae, as a `Finset`** (mirror of C.07(b)). -/
noncomputable def dv2SideSet {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ f : Polynomial O) (u₂ ℓ₂ : ℕ) : Finset ℕ :=
  open Classical in (Finset.range (f.natDegree + 1)).filter (fun j => Dv2OnSide L Ψ f u₂ ℓ₂ j)

/-- **The side's left endpoint** (mirror of C.07(c)). -/
noncomputable def dv2SideMin {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ f : Polynomial O) (u₂ ℓ₂ : ℕ) (h : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) : ℕ :=
  (dv2SideSet L Ψ f u₂ ℓ₂).min' h

variable {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) {Ψ : Polynomial O}

/-- Membership in `dv2SideSet` projects to the on-side predicate. -/
theorem dv2OnSide_of_mem_dv2SideSet {f : Polynomial O} {u₂ ℓ₂ j : ℕ}
    (hj : j ∈ dv2SideSet L Ψ f u₂ ℓ₂) : Dv2OnSide L Ψ f u₂ ℓ₂ j := by
  classical
  exact (Finset.mem_filter.mp (show j ∈ (Finset.range (f.natDegree + 1)).filter
    (Dv2OnSide L Ψ f u₂ ℓ₂) from hj)).2

/-- An on-side slot lies in `dv2SideSet`. -/
theorem mem_dv2SideSet_of_dv2OnSide (hΨ : Ψ.Monic) (hΨd : 0 < Ψ.natDegree)
    {f : Polynomial O} {u₂ ℓ₂ j : ℕ}
    (hj : Dv2OnSide L Ψ f u₂ ℓ₂ j) : j ∈ dv2SideSet L Ψ f u₂ ℓ₂ := by
  classical
  simp only [dv2SideSet, Finset.mem_filter, Finset.mem_range]
  refine ⟨?_, hj⟩
  by_contra hdeg
  exact hj.2 (dv2Pin_top_of_gt L hΨ hΨd f (by omega))

/-- **The chosen minimizer is on-side.** -/
theorem dv2OnSide_dv2SideMin (f : Polynomial O) (u₂ ℓ₂ : ℕ)
    (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) :
    Dv2OnSide L Ψ f u₂ ℓ₂ (dv2SideMin L Ψ f u₂ ℓ₂ hne) :=
  dv2OnSide_of_mem_dv2SideSet L (Finset.min'_mem _ hne)

/-- **The chosen minimizer is the LEFTMOST on-side slot.** -/
theorem dv2SideMin_le_of_dv2OnSide (hΨ : Ψ.Monic) (hΨd : 0 < Ψ.natDegree)
    {f : Polynomial O} {u₂ ℓ₂ j : ℕ}
    (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) (hj : Dv2OnSide L Ψ f u₂ ℓ₂ j) :
    dv2SideMin L Ψ f u₂ ℓ₂ hne ≤ j :=
  Finset.min'_le _ _ (mem_dv2SideSet_of_dv2OnSide L hΨ hΨd hj)

/-- Every slot strictly left of the chosen minimizer is strictly off the side. -/
theorem not_dv2OnSide_of_lt_dv2SideMin (hΨ : Ψ.Monic) (hΨd : 0 < Ψ.natDegree)
    {f : Polynomial O} {u₂ ℓ₂ j : ℕ}
    (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) (hlt : j < dv2SideMin L Ψ f u₂ ℓ₂ hne) :
    ¬ Dv2OnSide L Ψ f u₂ ℓ₂ j :=
  fun hj => absurd (dv2SideMin_le_of_dv2OnSide L hΨ hΨd hne hj) (by omega)

/-- **The unique lowest convolution pair.** -/
theorem dv2OnSide_endpoint_unique (hΨ : Ψ.Monic) (hΨd : 0 < Ψ.natDegree)
    {g z : Polynomial O} {u₂ ℓ₂ j i : ℕ}
    (hng : (dv2SideSet L Ψ g u₂ ℓ₂).Nonempty) (hnz : (dv2SideSet L Ψ z u₂ ℓ₂).Nonempty)
    (hsum : j + i = dv2SideMin L Ψ g u₂ ℓ₂ hng + dv2SideMin L Ψ z u₂ ℓ₂ hnz)
    (hj : Dv2OnSide L Ψ g u₂ ℓ₂ j) (hi : Dv2OnSide L Ψ z u₂ ℓ₂ i) :
    j = dv2SideMin L Ψ g u₂ ℓ₂ hng ∧ i = dv2SideMin L Ψ z u₂ ℓ₂ hnz := by
  have h1 := dv2SideMin_le_of_dv2OnSide L hΨ hΨd hng hj
  have h2 := dv2SideMin_le_of_dv2OnSide L hΨ hΨd hnz hi
  omega

/-- The height at the chosen minimizer is a natural number. -/
theorem exists_dv2SideMin_height (f : Polynomial O) (u₂ ℓ₂ : ℕ)
    (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) :
    ∃ H : ℕ, dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne) = (H : ℕ∞) :=
  ENat.ne_top_iff_exists.1 (dv2OnSide_dv2SideMin L f u₂ ℓ₂ hne).2 |>.imp fun _ h => h.symm

/-- **The support value, read off any on-side slot.** -/
theorem dv2Supp_eq_of_dv2OnSide {f : Polynomial O} {u₂ ℓ₂ j H : ℕ}
    (hH : dv2Pin L Ψ f j = (H : ℕ∞)) (hj : Dv2OnSide L Ψ f u₂ ℓ₂ j) :
    dv2Supp L Ψ f u₂ ℓ₂ = ((ℓ₂ * H + u₂ * j : ℕ) : ℕ∞) := by
  rw [hj.1, hH, weight_read]

/-- **The support infimum lies below the weighted pin at every abscissa** (mirror of
C131y's `dvSupp_le_term`, including past-degree abscissae via `dv2Pin_top_of_gt`). -/
theorem dv2Supp_le_term (hΨ : Ψ.Monic) (hΨd : 0 < Ψ.natDegree)
    (f : Polynomial O) (u₂ : ℕ) {ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (j : ℕ) :
    dv2Supp L Ψ f u₂ ℓ₂ ≤ ℓ₂ • dv2Pin L Ψ f j + (u₂ * j : ℕ∞) := by
  by_cases hj : j ≤ f.natDegree
  · unfold dv2Supp
    exact Finset.inf_le (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  · rw [dv2Pin_top_of_gt L hΨ hΨd f (by omega), C118a.smul_top_pos hℓ₂, top_add]
    exact le_top

/-- **The support line lies below the level-2 polygon**, ℕ-cleared. -/
theorem le_dv2Weight (hΨ : Ψ.Monic) (hΨd : 0 < Ψ.natDegree) {f : Polynomial O} {u₂ ℓ₂ : ℕ}
    (hℓ₂ : 0 < ℓ₂)
    {S H j : ℕ} (hS : dv2Supp L Ψ f u₂ ℓ₂ = (S : ℕ∞)) (hH : dv2Pin L Ψ f j = (H : ℕ∞)) :
    S ≤ ℓ₂ * H + u₂ * j := by
  have h := dv2Supp_le_term L hΨ hΨd f u₂ hℓ₂ j
  rw [hS, hH, weight_read] at h
  exact_mod_cast h

/-- **Off the side the support line is strictly below the polygon.** -/
theorem lt_dv2Weight (hΨ : Ψ.Monic) (hΨd : 0 < Ψ.natDegree) {f : Polynomial O} {u₂ ℓ₂ : ℕ}
    (hℓ₂ : 0 < ℓ₂)
    {S H j : ℕ} (hS : dv2Supp L Ψ f u₂ ℓ₂ = (S : ℕ∞)) (hH : dv2Pin L Ψ f j = (H : ℕ∞))
    (hns : ¬ Dv2OnSide L Ψ f u₂ ℓ₂ j) : S < ℓ₂ * H + u₂ * j := by
  rcases eq_or_lt_of_le (le_dv2Weight L hΨ hΨd hℓ₂ hS hH) with heq | hlt
  · refine absurd ⟨?_, hH ▸ ENat.coe_ne_top H⟩ hns
    rw [hS, hH, weight_read, ← heq]
  · exact hlt

/-! ## Part 2 — the ONE explicit hypothesis: `Dv2ResSurv`

Every `dev Ψ` output has degree `< Ψ.natDegree` UNCONDITIONALLY (B03's `degree_dev_lt`), so a
digit PRODUCT `A * B` (`A, B` both `Ψ`-development digits) has degree `< 2 * Ψ.natDegree` — it
therefore has at most two `Ψ`-development slots, `0` (the reduced remainder) and `1` (the bare
quotient; `dev_eq_zero_of_lt` kills every slot `≥ 2`). `Dv2ResSurv` packages exactly the two
facts the pricing bank below needs about those two slots, in the digit heights alone — see the
file docstring for why this is unavoidable and why it is exactly one hypothesis. -/

/-- **THE ONE explicit hypothesis ("μ₂-residual survival")**: for any two `Ψ`-digit-bounded
`A, B` (degree `< Ψ.natDegree`) of known `dv2Hgt` heights `Ha, Hb`, their product's `Ψ`-reduced
value is EXACTLY `Ha + Hb` (NV3's "reduction modulo `Φ₂` preserves the product ... value"), and
its carry (slot `1`) value is bounded STRICTLY above the line (the admissibility slack, folded
in since `dv2Hgt` carries no free key-height numeral to be admissible against). Discharged at
node M3-NV3 for `Ψ = Φ₂`, degree-`<4` coefficients, from the landed μ₂ normalized residual
product `s2NormRes_mul` (`C130rp9.lean:290`) — NOT here. -/
def Dv2ResSurv {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) (Ψ : Polynomial O)
    (u₂ ℓ₂ : ℕ) : Prop :=
  ∀ ⦃A B : Polynomial O⦄ ⦃Ha Hb : ℕ⦄,
    A.natDegree < Ψ.natDegree → B.natDegree < Ψ.natDegree →
    dv2Hgt L A = (Ha : ℕ∞) → dv2Hgt L B = (Hb : ℕ∞) →
    dv2Hgt L (dev Ψ (A * B) 0) = ((Ha + Hb : ℕ) : ℕ∞) ∧
    ℓ₂ • ((Ha + Hb : ℕ) : ℕ∞) + 1 ≤ ℓ₂ • dv2Hgt L (dev Ψ (A * B) 1) + (u₂ : ℕ∞)

variable {u₂ ℓ₂ : ℕ}

/-- A product of two outer digits is SHORT (degree `< 2 · deg Ψ`; mirror of
`natDegree_dev_mul_lt`, `C130nv2.lean:487`). -/
theorem natDegree_dev2_mul_lt (hΨ : Ψ.Monic) (hΨd : 0 < Ψ.natDegree) {g z : Polynomial O}
    {j i : ℕ} (hgj : dev Ψ g j ≠ 0) (hzi : dev Ψ z i ≠ 0) :
    (dev Ψ g j * dev Ψ z i).natDegree < 2 * Ψ.natDegree := by
  rw [natDegree_mul hgj hzi]
  have h1 : (dev Ψ g j).natDegree < Ψ.natDegree :=
    natDegree_lt_natDegree hgj (degree_dev_lt hΨ hΨd g j)
  have h2 : (dev Ψ z i).natDegree < Ψ.natDegree :=
    natDegree_lt_natDegree hzi (degree_dev_lt hΨ hΨd z i)
  omega

/-- ★ **The convolution term estimate, `≥`-direction, level two** (mirror of `le_line_dev_term`,
`C130nv2.lean:500-540`): every term of the outer convolution of `g · z` weighs at least
`Sg + Sz` at every slot `J`.  UNCONDITIONAL beyond `Dv2ResSurv` — no admissibility numeral, since
`Dv2ResSurv` already carries the needed slack. -/
theorem le_line_dev2_term (hΨ : Ψ.Monic) (hΨd : 0 < Ψ.natDegree) (hℓ₂ : 0 < ℓ₂)
    (hSurv2 : Dv2ResSurv L Ψ u₂ ℓ₂) {g z : Polynomial O} {Sg Sz : ℕ}
    (hSg : dv2Supp L Ψ g u₂ ℓ₂ = (Sg : ℕ∞)) (hSz : dv2Supp L Ψ z u₂ ℓ₂ = (Sz : ℕ∞))
    (J j i : ℕ) :
    ((Sg + Sz : ℕ) : ℕ∞)
      ≤ ℓ₂ • dv2Hgt L (dev Ψ (dev Ψ g j * dev Ψ z i * Ψ ^ (j + i)) J) + (u₂ * J : ℕ∞) := by
  by_cases hgj : dev Ψ g j = 0
  · rw [hgj, zero_mul, zero_mul, dev_of_zero, dv2Hgt_zero, C118a.smul_top_pos hℓ₂, top_add]
    exact le_top
  by_cases hzi : dev Ψ z i = 0
  · rw [hzi, mul_zero, zero_mul, dev_of_zero, dv2Hgt_zero, C118a.smul_top_pos hℓ₂, top_add]
    exact le_top
  have hHa' : dv2Pin L Ψ g j ≠ ⊤ := by
    rw [dv2Pin, dv2Hgt]; exact dvSupp_ne_top_of_ne_zero F L.u L.ℓ hgj
  have hHb' : dv2Pin L Ψ z i ≠ ⊤ := by
    rw [dv2Pin, dv2Hgt]; exact dvSupp_ne_top_of_ne_zero F L.u L.ℓ hzi
  obtain ⟨Ha, hHa⟩ := ENat.ne_top_iff_exists.1 hHa'
  obtain ⟨Hb, hHb⟩ := ENat.ne_top_iff_exists.1 hHb'
  have h1 : Sg ≤ ℓ₂ * Ha + u₂ * j := le_dv2Weight L hΨ hΨd hℓ₂ hSg hHa.symm
  have h2 : Sz ≤ ℓ₂ * Hb + u₂ * i := le_dv2Weight L hΨ hΨd hℓ₂ hSz hHb.symm
  rcases Nat.lt_or_ge J (j + i) with hJlt | hJge
  · rw [dev_mul_pow_of_lt hΨ (j + i) _ J hJlt, dv2Hgt_zero, C118a.smul_top_pos hℓ₂, top_add]
    exact le_top
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hJge
  rw [dev_mul_pow hΨ (j + i) _ s]
  have hAdeg : (dev Ψ g j).natDegree < Ψ.natDegree := natDegree_lt_natDegree hgj (degree_dev_lt hΨ hΨd g j)
  have hBdeg : (dev Ψ z i).natDegree < Ψ.natDegree := natDegree_lt_natDegree hzi (degree_dev_lt hΨ hΨd z i)
  have hnat : Sg + Sz ≤ ℓ₂ * (Ha + Hb) + u₂ * (j + i) := by
    calc Sg + Sz ≤ (ℓ₂ * Ha + u₂ * j) + (ℓ₂ * Hb + u₂ * i) := Nat.add_le_add h1 h2
      _ = ℓ₂ * (Ha + Hb) + u₂ * (j + i) := by ring
  match s with
  | 0 =>
    have hval := (hSurv2 hAdeg hBdeg hHa.symm hHb.symm).1
    rw [Nat.add_zero, hval]
    have : ((Sg + Sz : ℕ) : ℕ∞) ≤ ((ℓ₂ * (Ha + Hb) + u₂ * (j + i) : ℕ) : ℕ∞) := by exact_mod_cast hnat
    refine le_trans this (le_of_eq ?_)
    rw [nsmul_eq_mul]; push_cast; ring
  | 1 =>
    have hval := (hSurv2 hAdeg hBdeg hHa.symm hHb.symm).2
    have hweak : ℓ₂ • ((Ha + Hb : ℕ) : ℕ∞) ≤ ℓ₂ • dv2Hgt L (dev Ψ (dev Ψ g j * dev Ψ z i) 1) + (u₂ : ℕ∞) :=
      le_trans le_self_add hval
    have hstep : ((Sg + Sz : ℕ) : ℕ∞) ≤ ℓ₂ • ((Ha + Hb : ℕ) : ℕ∞) + (u₂ * (j + i) : ℕ∞) := by
      rw [nsmul_eq_mul]
      exact_mod_cast hnat
    refine le_trans hstep (le_trans (add_le_add hweak le_rfl) (le_of_eq ?_))
    push_cast; ring
  | (s + 2) =>
    rw [dev_eq_zero_of_lt hΨ hΨd _ (s + 2) (by
      have := natDegree_dev2_mul_lt hΨ hΨd hgj hzi
      nlinarith), dv2Hgt_zero, C118a.smul_top_pos hℓ₂, top_add]
    exact le_top

/-- ★ **The strict convolution term estimate, level two** (mirror of `lt_line_dev_term`,
`C130nv2.lean:545-620`, the survival direction): every term of the outer convolution OTHER
than an exact-slot on-side pair weighs at least `Sg + Sz + 1`. -/
theorem lt_line_dev2_term (hΨ : Ψ.Monic) (hΨd : 0 < Ψ.natDegree) (hℓ₂ : 0 < ℓ₂)
    (hSurv2 : Dv2ResSurv L Ψ u₂ ℓ₂) {g z : Polynomial O} {Sg Sz : ℕ}
    (hSg : dv2Supp L Ψ g u₂ ℓ₂ = (Sg : ℕ∞)) (hSz : dv2Supp L Ψ z u₂ ℓ₂ = (Sz : ℕ∞))
    {J j i : ℕ} (hbad : ¬ (j + i = J ∧ Dv2OnSide L Ψ g u₂ ℓ₂ j ∧ Dv2OnSide L Ψ z u₂ ℓ₂ i)) :
    ((Sg + Sz + 1 : ℕ) : ℕ∞)
      ≤ ℓ₂ • dv2Hgt L (dev Ψ (dev Ψ g j * dev Ψ z i * Ψ ^ (j + i)) J) + (u₂ * J : ℕ∞) := by
  by_cases hgj : dev Ψ g j = 0
  · rw [hgj, zero_mul, zero_mul, dev_of_zero, dv2Hgt_zero, C118a.smul_top_pos hℓ₂, top_add]
    exact le_top
  by_cases hzi : dev Ψ z i = 0
  · rw [hzi, mul_zero, zero_mul, dev_of_zero, dv2Hgt_zero, C118a.smul_top_pos hℓ₂, top_add]
    exact le_top
  have hHa' : dv2Pin L Ψ g j ≠ ⊤ := by
    rw [dv2Pin, dv2Hgt]; exact dvSupp_ne_top_of_ne_zero F L.u L.ℓ hgj
  have hHb' : dv2Pin L Ψ z i ≠ ⊤ := by
    rw [dv2Pin, dv2Hgt]; exact dvSupp_ne_top_of_ne_zero F L.u L.ℓ hzi
  obtain ⟨Ha, hHa⟩ := ENat.ne_top_iff_exists.1 hHa'
  obtain ⟨Hb, hHb⟩ := ENat.ne_top_iff_exists.1 hHb'
  have hAdeg : (dev Ψ g j).natDegree < Ψ.natDegree :=
    natDegree_lt_natDegree hgj (degree_dev_lt hΨ hΨd g j)
  have hBdeg : (dev Ψ z i).natDegree < Ψ.natDegree :=
    natDegree_lt_natDegree hzi (degree_dev_lt hΨ hΨd z i)
  rcases Nat.lt_or_ge J (j + i) with hJlt | hJge
  · rw [dev_mul_pow_of_lt hΨ (j + i) _ J hJlt, dv2Hgt_zero, C118a.smul_top_pos hℓ₂, top_add]
    exact le_top
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hJge
  rw [dev_mul_pow hΨ (j + i) _ s]
  match s with
  | 0 =>
    have hoff : ¬ Dv2OnSide L Ψ g u₂ ℓ₂ j ∨ ¬ Dv2OnSide L Ψ z u₂ ℓ₂ i := by
      by_contra hcon
      push Not at hcon
      exact hbad ⟨by omega, hcon.1, hcon.2⟩
    have hstrict : Sg + Sz + 1 ≤ ℓ₂ * (Ha + Hb) + u₂ * (j + i) := by
      rcases hoff with hng | hnz
      · have h1 : Sg < ℓ₂ * Ha + u₂ * j := lt_dv2Weight L hΨ hΨd hℓ₂ hSg hHa.symm hng
        have h2 : Sz ≤ ℓ₂ * Hb + u₂ * i := le_dv2Weight L hΨ hΨd hℓ₂ hSz hHb.symm
        calc Sg + Sz + 1 ≤ (ℓ₂ * Ha + u₂ * j) + (ℓ₂ * Hb + u₂ * i) := by omega
          _ = ℓ₂ * (Ha + Hb) + u₂ * (j + i) := by ring
      · have h1 : Sg ≤ ℓ₂ * Ha + u₂ * j := le_dv2Weight L hΨ hΨd hℓ₂ hSg hHa.symm
        have h2 : Sz < ℓ₂ * Hb + u₂ * i := lt_dv2Weight L hΨ hΨd hℓ₂ hSz hHb.symm hnz
        calc Sg + Sz + 1 ≤ (ℓ₂ * Ha + u₂ * j) + (ℓ₂ * Hb + u₂ * i) := by omega
          _ = ℓ₂ * (Ha + Hb) + u₂ * (j + i) := by ring
    have hval := (hSurv2 hAdeg hBdeg hHa.symm hHb.symm).1
    rw [Nat.add_zero, hval]
    have hcast : ((Sg + Sz + 1 : ℕ) : ℕ∞) ≤ ((ℓ₂ * (Ha + Hb) + u₂ * (j + i) : ℕ) : ℕ∞) := by
      exact_mod_cast hstrict
    refine le_trans hcast (le_of_eq ?_)
    rw [nsmul_eq_mul]; push_cast; ring
  | 1 =>
    have h1 : Sg ≤ ℓ₂ * Ha + u₂ * j := le_dv2Weight L hΨ hΨd hℓ₂ hSg hHa.symm
    have h2 : Sz ≤ ℓ₂ * Hb + u₂ * i := le_dv2Weight L hΨ hΨd hℓ₂ hSz hHb.symm
    have hval := (hSurv2 hAdeg hBdeg hHa.symm hHb.symm).2
    have hstep : ((Sg + Sz + 1 : ℕ) : ℕ∞)
        ≤ (ℓ₂ • ((Ha + Hb : ℕ) : ℕ∞) + 1) + (u₂ * (j + i) : ℕ∞) := by
      rw [nsmul_eq_mul]
      have hnat : Sg + Sz + 1 ≤ (ℓ₂ * (Ha + Hb) + 1) + u₂ * (j + i) := by
        have h3 : Sg + Sz ≤ (ℓ₂ * Ha + u₂ * j) + (ℓ₂ * Hb + u₂ * i) := Nat.add_le_add h1 h2
        have h4 : (ℓ₂ * Ha + u₂ * j) + (ℓ₂ * Hb + u₂ * i)
            = ℓ₂ * (Ha + Hb) + u₂ * (j + i) := by ring
        omega
      exact_mod_cast hnat
    refine le_trans hstep (le_trans (add_le_add hval le_rfl) (le_of_eq ?_))
    push_cast; ring
  | (s + 2) =>
    rw [dev_eq_zero_of_lt hΨ hΨd _ (s + 2) (by
      have h := natDegree_dev2_mul_lt hΨ hΨd hgj hzi
      nlinarith), dv2Hgt_zero, C118a.smul_top_pos hℓ₂, top_add]
    exact le_top

/-- The finite-sum ultrametric for `dv2Hgt`, in the weighted form the outer convolution
consumes (mirror of `le_weight_stageHeight_sum`, `C130nv2.lean:210-229`; free from `dv2Hgt`'s
zero/ultrametric-add shims, Part 0). -/
private theorem le_weight_dv2Hgt_sum (hℓ₂ : 0 < ℓ₂)
    {ι : Type*} (s : Finset ι) (G : ι → Polynomial O) {c d : ℕ∞}
    (hall : ∀ p ∈ s, c ≤ ℓ₂ • dv2Hgt L (G p) + d) :
    c ≤ ℓ₂ • dv2Hgt L (∑ p ∈ s, G p) + d := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty, dv2Hgt_zero, C118a.smul_top_pos hℓ₂, top_add]
    exact le_top
  | cons a t hat ih =>
    rw [Finset.sum_cons]
    have hmono : Monotone (fun x : ℕ∞ => ℓ₂ • x + d) :=
      fun x y hxy => add_le_add (nsmul_le_nsmul_right hxy ℓ₂) le_rfl
    calc c ≤ min (ℓ₂ • dv2Hgt L (G a) + d) (ℓ₂ • dv2Hgt L (∑ p ∈ t, G p) + d) :=
          le_min (hall a (Finset.mem_cons_self a t))
            (ih fun p hp => hall p (Finset.mem_cons.2 (Or.inr hp)))
      _ = ℓ₂ • min (dv2Hgt L (G a)) (dv2Hgt L (∑ p ∈ t, G p)) + d := (hmono.map_min).symm
      _ ≤ ℓ₂ • dv2Hgt L (G a + ∑ p ∈ t, G p) + d := hmono (min_dv2Hgt_le_dv2Hgt_add L _ _)

/-- ★ **The `dv2Supp` product law, `≥`-direction, UNIVERSAL** (mirror of
`dvSupp_add_le_dvSupp_mul`, `C130nv2.lean:645-689`; the level-two B.33, one level up): every
zero case included. This is the "≥" half of NV4's eventual product law; the "≤" half needs
`Dv2ResSurv` at the chosen minimizers, assembled in Part 3 below. -/
theorem dv2Supp_add_le_dv2Supp_mul (hΨ : Ψ.Monic) (hΨd : 0 < Ψ.natDegree) (hℓ₂ : 0 < ℓ₂)
    (hSurv2 : Dv2ResSurv L Ψ u₂ ℓ₂) (g z : Polynomial O) :
    dv2Supp L Ψ g u₂ ℓ₂ + dv2Supp L Ψ z u₂ ℓ₂ ≤ dv2Supp L Ψ (g * z) u₂ ℓ₂ := by
  rcases eq_or_ne g 0 with rfl | hg
  · rw [zero_mul, dv2Supp_zero_eq_top L Ψ u₂ hℓ₂]
    exact le_top
  rcases eq_or_ne z 0 with rfl | hz
  · rw [mul_zero, dv2Supp_zero_eq_top L Ψ u₂ hℓ₂]
    exact le_top
  obtain ⟨Sg, hSg⟩ := ENat.ne_top_iff_exists.1 (dv2Supp_ne_top_of_ne_zero L hΨ hΨd u₂ ℓ₂ hg)
  obtain ⟨Sz, hSz⟩ := ENat.ne_top_iff_exists.1 (dv2Supp_ne_top_of_ne_zero L hΨ hΨd u₂ ℓ₂ hz)
  rw [← hSg, ← hSz, ← Nat.cast_add]
  set N := g.natDegree + z.natDegree + 1 with hN
  have hgN : g.natDegree < N * Ψ.natDegree :=
    lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right N hΨd)
  have hzN : z.natDegree < N * Ψ.natDegree :=
    lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right N hΨd)
  have hgrep : ∑ j ∈ Finset.range N, dev Ψ g j * Ψ ^ j = g := sum_dev_eq hΨ hΨd g hgN
  have hzrep : ∑ i ∈ Finset.range N, dev Ψ z i * Ψ ^ i = z := sum_dev_eq hΨ hΨd z hzN
  have hrep : g * z = ∑ p ∈ Finset.range N ×ˢ Finset.range N,
      dev Ψ g p.1 * dev Ψ z p.2 * Ψ ^ (p.1 + p.2) := by
    have h1 : g * z = (∑ j ∈ Finset.range N, dev Ψ g j * Ψ ^ j)
        * (∑ i ∈ Finset.range N, dev Ψ z i * Ψ ^ i) := by rw [hgrep, hzrep]
    rw [h1, Finset.sum_mul_sum, Finset.sum_product]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
      rw [pow_add]; ring
  rw [dv2Supp]
  refine Finset.le_inf fun J _ => ?_
  have hdev : dv2Pin L Ψ (g * z) J
      = dv2Hgt L (∑ p ∈ Finset.range N ×ˢ Finset.range N,
          dev Ψ (dev Ψ g p.1 * dev Ψ z p.2 * Ψ ^ (p.1 + p.2)) J) := by
    rw [dv2Pin]
    congr 1
    conv_lhs => rw [hrep]
    exact dev_finsetSum hΨ _ _ J
  rw [hdev]
  exact le_weight_dv2Hgt_sum L hℓ₂ _ _
    (fun p _ => le_line_dev2_term L hΨ hΨd hℓ₂ hSurv2 hSg.symm hSz.symm J p.1 p.2)

/-! ## Part 3 — the endpoint/minimizer assembly (mirror of `C130nv2.lean`'s Part 5, `641-784`)

Unlike Part 5's `hup`/`hsurv`, taken as an EXPLICIT input there (NV-3's job to supply, one
level down), here `Dv2ResSurv` already supplies the endpoint's own survival directly
(`Dv2ResSurv`'s first clause, applied at the CHOSEN minimizers) — so every theorem below closes
with `Dv2ResSurv` alone, no separate endpoint hypothesis. -/

/-- Every on-side abscissa lies within the development range (mirror of
`dvSideMin_le_natDegree`, `C130nv3.lean:161-168`). -/
theorem dv2SideMin_le_natDegree (f : Polynomial O) (u₂ ℓ₂ : ℕ)
    (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) : dv2SideMin L Ψ f u₂ ℓ₂ hne ≤ f.natDegree := by
  classical
  have hmem := Finset.min'_mem (dv2SideSet L Ψ f u₂ ℓ₂) hne
  have h := (Finset.mem_filter.mp (show dv2SideMin L Ψ f u₂ ℓ₂ hne ∈
    (Finset.range (f.natDegree + 1)).filter (fun j => Dv2OnSide L Ψ f u₂ ℓ₂ j) from hmem)).1
  rw [Finset.mem_range] at h
  omega

/-- ★ **The endpoint survives, DERIVED from `Dv2ResSurv`** (mirror of the assembled content of
`stageHeight_dev_endpoint_le_of_surv`, `C130nv3.lean:153-271`, but with the endpoint's own
survival now supplied by `Dv2ResSurv` rather than taken as `hsurv`): the product's development
coefficient at the SUM of the chosen minimizers has stage value at most `Hg + Hz`. -/
private theorem dv2_endpoint_dev_le (hΨ : Ψ.Monic) (hΨd : 0 < Ψ.natDegree) (hℓ₂ : 0 < ℓ₂)
    (hSurv2 : Dv2ResSurv L Ψ u₂ ℓ₂) {g z : Polynomial O}
    (hng : (dv2SideSet L Ψ g u₂ ℓ₂).Nonempty) (hnz : (dv2SideSet L Ψ z u₂ ℓ₂).Nonempty)
    {Hg Hz : ℕ}
    (hHg : dv2Pin L Ψ g (dv2SideMin L Ψ g u₂ ℓ₂ hng) = (Hg : ℕ∞))
    (hHz : dv2Pin L Ψ z (dv2SideMin L Ψ z u₂ ℓ₂ hnz) = (Hz : ℕ∞)) :
    dv2Hgt L (dev Ψ (g * z)
        (dv2SideMin L Ψ g u₂ ℓ₂ hng + dv2SideMin L Ψ z u₂ ℓ₂ hnz)) ≤ ((Hg + Hz : ℕ) : ℕ∞) := by
  classical
  set jg := dv2SideMin L Ψ g u₂ ℓ₂ hng with hjg
  set jz := dv2SideMin L Ψ z u₂ ℓ₂ hnz with hjz
  have hSg : dv2Supp L Ψ g u₂ ℓ₂ = ((ℓ₂ * Hg + u₂ * jg : ℕ) : ℕ∞) :=
    dv2Supp_eq_of_dv2OnSide L hHg (dv2OnSide_dv2SideMin L g u₂ ℓ₂ hng)
  have hSz : dv2Supp L Ψ z u₂ ℓ₂ = ((ℓ₂ * Hz + u₂ * jz : ℕ) : ℕ∞) :=
    dv2Supp_eq_of_dv2OnSide L hHz (dv2OnSide_dv2SideMin L z u₂ ℓ₂ hnz)
  set N := g.natDegree + z.natDegree + 1 with hN
  have hgN : g.natDegree < N * Ψ.natDegree :=
    lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right N hΨd)
  have hzN : z.natDegree < N * Ψ.natDegree :=
    lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right N hΨd)
  have hgrep : ∑ j ∈ Finset.range N, dev Ψ g j * Ψ ^ j = g := sum_dev_eq hΨ hΨd g hgN
  have hzrep : ∑ i ∈ Finset.range N, dev Ψ z i * Ψ ^ i = z := sum_dev_eq hΨ hΨd z hzN
  have hrep : g * z = ∑ p ∈ Finset.range N ×ˢ Finset.range N,
      dev Ψ g p.1 * dev Ψ z p.2 * Ψ ^ (p.1 + p.2) := by
    have h1 : g * z = (∑ j ∈ Finset.range N, dev Ψ g j * Ψ ^ j)
        * (∑ i ∈ Finset.range N, dev Ψ z i * Ψ ^ i) := by rw [hgrep, hzrep]
    rw [h1, Finset.sum_mul_sum, Finset.sum_product]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
      rw [pow_add]; ring
  have hp0 : ((jg, jz) : ℕ × ℕ) ∈ Finset.range N ×ˢ Finset.range N := by
    refine Finset.mem_product.2 ⟨Finset.mem_range.2 ?_, Finset.mem_range.2 ?_⟩
    · have := dv2SideMin_le_natDegree L g u₂ ℓ₂ hng
      omega
    · have := dv2SideMin_le_natDegree L z u₂ ℓ₂ hnz
      omega
  have hT0 : dev Ψ (dev Ψ g jg * dev Ψ z jz * Ψ ^ (jg + jz)) (jg + jz)
      = dev Ψ (dev Ψ g jg * dev Ψ z jz) 0 := by
    have h := dev_mul_pow hΨ (jg + jz) (dev Ψ g jg * dev Ψ z jz) 0
    rwa [Nat.add_zero] at h
  have hsplit : dev Ψ (g * z) (jg + jz)
      = dev Ψ (dev Ψ g jg * dev Ψ z jz) 0
        + ∑ p ∈ (Finset.range N ×ˢ Finset.range N).erase (jg, jz),
            dev Ψ (dev Ψ g p.1 * dev Ψ z p.2 * Ψ ^ (p.1 + p.2)) (jg + jz) := by
    have hdev : dev Ψ (g * z) (jg + jz)
        = ∑ p ∈ Finset.range N ×ˢ Finset.range N,
            dev Ψ (dev Ψ g p.1 * dev Ψ z p.2 * Ψ ^ (p.1 + p.2)) (jg + jz) := by
      conv_lhs => rw [hrep]
      exact dev_finsetSum hΨ _ _ (jg + jz)
    rw [hdev, ← hT0]
    exact (Finset.add_sum_erase _ _ hp0).symm
  have hallR : ∀ p ∈ (Finset.range N ×ˢ Finset.range N).erase (jg, jz),
      ((ℓ₂ * (Hg + Hz) + u₂ * (jg + jz) + 1 : ℕ) : ℕ∞)
        ≤ ℓ₂ • dv2Hgt L
            (dev Ψ (dev Ψ g p.1 * dev Ψ z p.2 * Ψ ^ (p.1 + p.2)) (jg + jz))
          + (u₂ * (jg + jz) : ℕ∞) := by
    intro p hp
    have hbad : ¬ (p.1 + p.2 = jg + jz ∧ Dv2OnSide L Ψ g u₂ ℓ₂ p.1 ∧ Dv2OnSide L Ψ z u₂ ℓ₂ p.2) := by
      rintro ⟨hsum, h1, h2⟩
      obtain ⟨e1, e2⟩ := dv2OnSide_endpoint_unique L hΨ hΨd hng hnz hsum h1 h2
      exact (Finset.mem_erase.1 hp).1 (Prod.ext_iff.2 ⟨e1, e2⟩)
    refine le_trans (le_of_eq ?_) (lt_line_dev2_term L hΨ hΨd hℓ₂ hSurv2 hSg hSz hbad)
    push_cast; ring
  have hRw := le_weight_dv2Hgt_sum L hℓ₂ _ _ hallR
  have hR : ((Hg + Hz : ℕ) : ℕ∞) + 1
      ≤ dv2Hgt L (∑ p ∈ (Finset.range N ×ˢ Finset.range N).erase (jg, jz),
          dev Ψ (dev Ψ g p.1 * dev Ψ z p.2 * Ψ ^ (p.1 + p.2)) (jg + jz)) :=
    succ_le_of_weight_succ_le hRw
  have hAdeg : (dev Ψ g jg).natDegree < Ψ.natDegree := by
    rcases eq_or_ne (dev Ψ g jg) 0 with h0 | hne
    · rw [h0, natDegree_zero]; exact hΨd
    · exact natDegree_lt_natDegree hne (degree_dev_lt hΨ hΨd g jg)
  have hBdeg : (dev Ψ z jz).natDegree < Ψ.natDegree := by
    rcases eq_or_ne (dev Ψ z jz) 0 with h0 | hne
    · rw [h0, natDegree_zero]; exact hΨd
    · exact natDegree_lt_natDegree hne (degree_dev_lt hΨ hΨd z jz)
  have hval : dv2Hgt L (dev Ψ (dev Ψ g jg * dev Ψ z jz) 0) = ((Hg + Hz : ℕ) : ℕ∞) :=
    (hSurv2 hAdeg hBdeg hHg hHz).1
  rw [hsplit]
  set T := dev Ψ (dev Ψ g jg * dev Ψ z jz) 0 with hT
  set R := ∑ p ∈ (Finset.range N ×ˢ Finset.range N).erase (jg, jz),
      dev Ψ (dev Ψ g p.1 * dev Ψ z p.2 * Ψ ^ (p.1 + p.2)) (jg + jz) with hRdef
  rcases eq_or_ne (dv2Hgt L T) (dv2Hgt L R) with heq | hne
  · exfalso
    have h1 : ((Hg + Hz : ℕ) : ℕ∞) + 1 ≤ ((Hg + Hz : ℕ) : ℕ∞) := by
      calc ((Hg + Hz : ℕ) : ℕ∞) + 1 ≤ dv2Hgt L R := hR
        _ = dv2Hgt L T := heq.symm
        _ = ((Hg + Hz : ℕ) : ℕ∞) := hval
    rw [show ((Hg + Hz : ℕ) : ℕ∞) + 1 = ((Hg + Hz + 1 : ℕ) : ℕ∞) by push_cast; ring] at h1
    exact absurd (by exact_mod_cast h1 : Hg + Hz + 1 ≤ Hg + Hz) (by omega)
  · rw [dv2Hgt_add_eq L hne, hval]
    exact min_le_left _ _

/-- ★ **NODE NV-2's endpoint lemma, level two, value form** (mirror of
`dvSupp_mul_of_endpoint_le`, `C130nv2.lean:700-727`): given `Dv2ResSurv`, the product's cleared
support is EXACTLY the sum of the factors' supports, read at the sum of the chosen minimizers. -/
theorem dv2Supp_mul_of_endpoint_le (hΨ : Ψ.Monic) (hΨd : 0 < Ψ.natDegree) (hℓ₂ : 0 < ℓ₂)
    (hSurv2 : Dv2ResSurv L Ψ u₂ ℓ₂) {g z : Polynomial O}
    (hng : (dv2SideSet L Ψ g u₂ ℓ₂).Nonempty) (hnz : (dv2SideSet L Ψ z u₂ ℓ₂).Nonempty)
    {Hg Hz : ℕ}
    (hHg : dv2Pin L Ψ g (dv2SideMin L Ψ g u₂ ℓ₂ hng) = (Hg : ℕ∞))
    (hHz : dv2Pin L Ψ z (dv2SideMin L Ψ z u₂ ℓ₂ hnz) = (Hz : ℕ∞)) :
    dv2Supp L Ψ (g * z) u₂ ℓ₂
      = ((ℓ₂ * (Hg + Hz) + u₂ * (dv2SideMin L Ψ g u₂ ℓ₂ hng + dv2SideMin L Ψ z u₂ ℓ₂ hnz) : ℕ) : ℕ∞) := by
  set jg := dv2SideMin L Ψ g u₂ ℓ₂ hng with hjg
  set jz := dv2SideMin L Ψ z u₂ ℓ₂ hnz with hjz
  have hSg := dv2Supp_eq_of_dv2OnSide L hHg (dv2OnSide_dv2SideMin L g u₂ ℓ₂ hng)
  have hSz := dv2Supp_eq_of_dv2OnSide L hHz (dv2OnSide_dv2SideMin L z u₂ ℓ₂ hnz)
  have hup := dv2_endpoint_dev_le L hΨ hΨd hℓ₂ hSurv2 hng hnz hHg hHz
  refine le_antisymm ?_ ?_
  · refine le_trans (dv2Supp_le_term L hΨ hΨd (g * z) u₂ hℓ₂ (jg + jz)) ?_
    refine le_trans (add_le_add (nsmul_le_nsmul_right hup ℓ₂) le_rfl) (le_of_eq ?_)
    rw [nsmul_eq_mul]; push_cast; ring
  · refine le_trans (le_of_eq ?_) (dv2Supp_add_le_dv2Supp_mul L hΨ hΨd hℓ₂ hSurv2 g z)
    rw [hSg, hSz]; push_cast; ring

/-- ★ **NODE NV-2's endpoint lemma, level two, minimizer form** (mirror of
`dvOnSide_mul_endpoint`, `C130nv2.lean:731-739`): the sum of the chosen minimizers IS a product
minimizer. -/
theorem dv2OnSide_mul_endpoint (hΨ : Ψ.Monic) (hΨd : 0 < Ψ.natDegree) (hℓ₂ : 0 < ℓ₂)
    (hSurv2 : Dv2ResSurv L Ψ u₂ ℓ₂) {g z : Polynomial O}
    (hng : (dv2SideSet L Ψ g u₂ ℓ₂).Nonempty) (hnz : (dv2SideSet L Ψ z u₂ ℓ₂).Nonempty)
    {Hg Hz : ℕ}
    (hHg : dv2Pin L Ψ g (dv2SideMin L Ψ g u₂ ℓ₂ hng) = (Hg : ℕ∞))
    (hHz : dv2Pin L Ψ z (dv2SideMin L Ψ z u₂ ℓ₂ hnz) = (Hz : ℕ∞)) :
    Dv2OnSide L Ψ (g * z) u₂ ℓ₂
      (dv2SideMin L Ψ g u₂ ℓ₂ hng + dv2SideMin L Ψ z u₂ ℓ₂ hnz) := by
  set jg := dv2SideMin L Ψ g u₂ ℓ₂ hng with hjg
  set jz := dv2SideMin L Ψ z u₂ ℓ₂ hnz with hjz
  have hval := dv2Supp_mul_of_endpoint_le L hΨ hΨd hℓ₂ hSurv2 hng hnz hHg hHz
  have hup' : dv2Pin L Ψ (g * z) (jg + jz) ≤ ((Hg + Hz : ℕ) : ℕ∞) :=
    dv2_endpoint_dev_le L hΨ hΨd hℓ₂ hSurv2 hng hnz hHg hHz
  have hlow := dv2Supp_le_term L hΨ hΨd (g * z) u₂ hℓ₂ (jg + jz)
  rw [hval] at hlow
  have hhgt_ne : dv2Pin L Ψ (g * z) (jg + jz) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) hup'
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hhgt_ne
  have hcle : c ≤ Hg + Hz := by rw [← hc] at hup'; exact_mod_cast hup'
  have hcge : Hg + Hz ≤ c := by
    rw [← hc, nsmul_eq_mul] at hlow
    have hnat : ℓ₂ * (Hg + Hz) + u₂ * (jg + jz) ≤ ℓ₂ * c + u₂ * (jg + jz) := by
      exact_mod_cast hlow
    have hmul : ℓ₂ * (Hg + Hz) ≤ ℓ₂ * c := by omega
    exact Nat.le_of_mul_le_mul_left hmul hℓ₂
  have hcexact : dv2Pin L Ψ (g * z) (jg + jz) = ((Hg + Hz : ℕ) : ℕ∞) := by
    rw [← hc]; exact_mod_cast (show c = Hg + Hz by omega)
  refine ⟨?_, by rw [hcexact]; exact ENat.coe_ne_top _⟩
  rw [hval, hcexact, nsmul_eq_mul]
  push_cast; ring

/-- The chosen product minimizer is BOUNDED BY the sum of the factors' minimizers (mirror of
`dvSideMin_mul_le`, `C130nv2.lean:767-780`). -/
theorem dv2SideMin_mul_le (hΨ : Ψ.Monic) (hΨd : 0 < Ψ.natDegree) (hℓ₂ : 0 < ℓ₂)
    (hSurv2 : Dv2ResSurv L Ψ u₂ ℓ₂) {g z : Polynomial O}
    (hng : (dv2SideSet L Ψ g u₂ ℓ₂).Nonempty) (hnz : (dv2SideSet L Ψ z u₂ ℓ₂).Nonempty)
    {Hg Hz : ℕ}
    (hHg : dv2Pin L Ψ g (dv2SideMin L Ψ g u₂ ℓ₂ hng) = (Hg : ℕ∞))
    (hHz : dv2Pin L Ψ z (dv2SideMin L Ψ z u₂ ℓ₂ hnz) = (Hz : ℕ∞))
    (hne : (dv2SideSet L Ψ (g * z) u₂ ℓ₂).Nonempty) :
    dv2SideMin L Ψ (g * z) u₂ ℓ₂ hne ≤ dv2SideMin L Ψ g u₂ ℓ₂ hng + dv2SideMin L Ψ z u₂ ℓ₂ hnz :=
  dv2SideMin_le_of_dv2OnSide L hΨ hΨd hne (dv2OnSide_mul_endpoint L hΨ hΨd hℓ₂ hSurv2 hng hnz hHg hHz)

/-- ★ **The NV-4 consumption shape, level two** (mirror of `dvSupp_mul_eq_add_of_endpoint_le`,
`C130nv2.lean:784-796`): given `Dv2ResSurv`, the level-two product law fires —
`dv2Supp (g · z) = dv2Supp g + dv2Supp z`. -/
theorem dv2Supp_mul_eq_add_of_endpoint_le (hΨ : Ψ.Monic) (hΨd : 0 < Ψ.natDegree) (hℓ₂ : 0 < ℓ₂)
    (hSurv2 : Dv2ResSurv L Ψ u₂ ℓ₂) {g z : Polynomial O}
    (hng : (dv2SideSet L Ψ g u₂ ℓ₂).Nonempty) (hnz : (dv2SideSet L Ψ z u₂ ℓ₂).Nonempty)
    {Hg Hz : ℕ}
    (hHg : dv2Pin L Ψ g (dv2SideMin L Ψ g u₂ ℓ₂ hng) = (Hg : ℕ∞))
    (hHz : dv2Pin L Ψ z (dv2SideMin L Ψ z u₂ ℓ₂ hnz) = (Hz : ℕ∞)) :
    dv2Supp L Ψ (g * z) u₂ ℓ₂ = dv2Supp L Ψ g u₂ ℓ₂ + dv2Supp L Ψ z u₂ ℓ₂ := by
  rw [dv2Supp_mul_of_endpoint_le L hΨ hΨd hℓ₂ hSurv2 hng hnz hHg hHz,
    dv2Supp_eq_of_dv2OnSide L hHg (dv2OnSide_dv2SideMin L g u₂ ℓ₂ hng),
    dv2Supp_eq_of_dv2OnSide L hHz (dv2OnSide_dv2SideMin L z u₂ ℓ₂ hnz)]
  push_cast
  ring

end Uniformity.Density.Tower.C132nv2

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C132nv2.dv2Hgt_zero
#print axioms Uniformity.Density.Tower.C132nv2.min_dv2Hgt_le_dv2Hgt_add
#print axioms Uniformity.Density.Tower.C132nv2.dv2Hgt_add_eq
#print axioms Uniformity.Density.Tower.C132nv2.Dv2OnSide
#print axioms Uniformity.Density.Tower.C132nv2.dv2SideSet
#print axioms Uniformity.Density.Tower.C132nv2.dv2SideMin
#print axioms Uniformity.Density.Tower.C132nv2.dv2OnSide_of_mem_dv2SideSet
#print axioms Uniformity.Density.Tower.C132nv2.mem_dv2SideSet_of_dv2OnSide
#print axioms Uniformity.Density.Tower.C132nv2.dv2OnSide_dv2SideMin
#print axioms Uniformity.Density.Tower.C132nv2.dv2SideMin_le_of_dv2OnSide
#print axioms Uniformity.Density.Tower.C132nv2.not_dv2OnSide_of_lt_dv2SideMin
#print axioms Uniformity.Density.Tower.C132nv2.dv2OnSide_endpoint_unique
#print axioms Uniformity.Density.Tower.C132nv2.exists_dv2SideMin_height
#print axioms Uniformity.Density.Tower.C132nv2.dv2Supp_eq_of_dv2OnSide
#print axioms Uniformity.Density.Tower.C132nv2.dv2Supp_le_term
#print axioms Uniformity.Density.Tower.C132nv2.le_dv2Weight
#print axioms Uniformity.Density.Tower.C132nv2.lt_dv2Weight
#print axioms Uniformity.Density.Tower.C132nv2.Dv2ResSurv
#print axioms Uniformity.Density.Tower.C132nv2.natDegree_dev2_mul_lt
#print axioms Uniformity.Density.Tower.C132nv2.le_line_dev2_term
#print axioms Uniformity.Density.Tower.C132nv2.lt_line_dev2_term
#print axioms Uniformity.Density.Tower.C132nv2.dv2Supp_add_le_dv2Supp_mul
#print axioms Uniformity.Density.Tower.C132nv2.dv2SideMin_le_natDegree
#print axioms Uniformity.Density.Tower.C132nv2.dv2Supp_mul_of_endpoint_le
#print axioms Uniformity.Density.Tower.C132nv2.dv2OnSide_mul_endpoint
#print axioms Uniformity.Density.Tower.C132nv2.dv2SideMin_mul_le
#print axioms Uniformity.Density.Tower.C132nv2.dv2Supp_mul_eq_add_of_endpoint_le

end AxCheck
