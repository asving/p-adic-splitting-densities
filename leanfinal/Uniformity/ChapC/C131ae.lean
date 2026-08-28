/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C131ac
import Uniformity.ChapC.C131ad
import Uniformity.ChapC.C118a
import Uniformity.ChapC.C118b
import Uniformity.ChapC.C131v
import Uniformity.ChapC.C109
import Uniformity.ChapC.C131ae0
import Uniformity.HenselFactorization

/-!
# Uniformity.ChapC.C131ae — Chapter C, NODE C.131ae′

(`docs/in-progress/DV_GRADED_ENGINE_V2_2026-08-24.md` §5 node table.)

**C.131ae′** (`mem_towerLocus_of_budget`, C.52's Step 2, `EFF.GENTOW1.21`): budget floors on
`f`'s two-key development digits imply `f ∈ towerLocus T μ₂`.

## The missing mechanism this file supplies

The 2026-08-18 record (`C52_BLOCKED_2026-08-18.md`) and C.53's own honest header
(`C53.lean`, `TowerBudgetIff`) both name the same obstruction: no landed theorem transfers
`IsDvPure`/`dvResPoly` across an additive perturbation of strictly higher weight ("the
dv-graded product law"; the 2026-08-24 fleet's `composedKey_pow_mem_towerLocus` supplies
Step 1's EXACT half, but the ADDITIVE perturbation half was never built at the
`dv`-carrier). This file builds exactly that half — turning the same crank chapter B
already turned for `suppVal`/`gaussVal` (B32a/B32b) and for `resMk` (B35a), but only the
pieces genuinely needed here, not the full B41a-style `pure_add_of_lt` cluster (which needs
a dv-level `sideMin_of_pure`/`height_eq_of_pure`/`resPoly_coeff_of_pure` family that is not
landed and is not built here either):

* an ultrametric **equality-off-ties** law for `suppVal` (hence for `KeyFrame.stageHeight`
  and `dvHgt`), proved from the easy ultrametric inequality (B32b) plus
  negation-invariance — no purity hypothesis needed;
* a **slot-read invariance** law: `KeyFrame.slotRes`/`KeyFrame.twistRead` at a fixed height
  are unchanged by adding a polynomial whose `stageHeight` strictly exceeds that height (the
  ADD analogue of C.26's *private* vanishing lemma `slotRes_eq_zero_of_lt`, independently
  re-derived here from the same public primitives — `KeyFrame.slotRes`,
  `C109asm.digAt_congr` — since the private original is not importable and duplicating a
  short public-primitive argument under a fresh name is the documented RE-PLAN pattern, not
  a copy of signed text).

Given these, the whole side-set/side-data comparison between `f` and `Φ₂^{μ₂}` becomes a
UNIFORM tie-break argument (every abscissa, not just the two purity endpoints), which is
what lets this file avoid replicating B41a's much larger apparatus.

## The assembly

`hbud` supplies, via a two-variable lift (`Qg`) and C.131ad's `dev_coeff_floor`/C.131u's
`dvAbove_of_forall_coeff_floor`, a `DvAbove` floor of `μ₂·E₂ + 1` on
`g := f − Φ₂^{μ₂}`. Since `Φ₂^{μ₂}`'s own `dv`-support is EXACTLY `μ₂·E₂` (read off its top
digit via `dev_top_eq_one`, C.131v), every abscissa on `Φ₂^{μ₂}`'s side has `g`'s
competing term strictly higher, so the tie-break law transfers the height there UNCHANGED;
every abscissa off `Φ₂^{μ₂}`'s side has both terms strictly above `μ₂·E₂`, so it stays off
`f`'s side too. This identifies `f`'s and `Φ₂^{μ₂}`'s side sets exactly, and the slot-read
invariance law transfers the residual polynomial coefficient-by-coefficient.

## C.131af′

The reverse direction (`budget_of_mem_towerLocus`) is NOT landed in this file. It needs the
two-key digit correspondence in the opposite sense — recovering `f`'s raw box digits from a
*known* locus membership — which is the pointwise cousin of C.53's `TriangularDigitRead`
and needs the census/conversion apparatus (`shadowDev`, `xNF`, C.131v's discrepancy
identification) at the level of a single scalar digit rather than a counted class. No
landed object supplies this identification, and building it is a second undertaking of
comparable size to the one below. No `sorry`, no axiom, no statement weakening: the node is
simply absent — see `runs/wave-b/verdict_C131ae.md`.

## Status

C.131ae′ (`mem_towerLocus_of_budget`): LANDED, sorry-free. Footprint Lean-core plus the
DECLARED cite `fgmn_dv_exact_mul`, inherited only through `composedKey_pow_mem_towerLocus`
(C.131ac) — see the AxCheck footer for exactly which declarations carry it.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C131ae

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C131a Uniformity.Density.Tower.C131f
open Uniformity.Density.Tower.C131u Uniformity.Density.Tower.C131ad

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## Part 1 — negation-invariance and the ultrametric equality-off-ties law

**[UNT 2026-08-28]** MOVED to `C131ae0.lean` (same namespace, so every reference below is
unaffected) to break a textual import cycle blocking the physical retirement of the
declared cite `fgmn_dv_exact_mul` — see `C66b.lean`'s `[H0LEG 2026-08-28]` note and
`runs/wave-c/verdict_UNT.md`. The moved decls: `addVal_neg_one`, `addVal_neg`,
`gaussVal_neg`, `dev_zero_any`, `dev_neg_of_monic`, `suppVal_neg`,
`suppVal_add_eq_left_of_lt` (former lines 92–160 here, byte-identical in the new file). -/

/-- The stage height is an ultrametric equality off ties: adding a `B` of strictly higher
stage height than `A` leaves `A`'s stage height unchanged. -/
theorem stageHeight_add_eq_left_of_lt (F : KeyFrame O π) {A B : Polynomial O}
    (h : F.stageHeight A < F.stageHeight B) :
    F.stageHeight (A + B) = F.stageHeight A :=
  suppVal_add_eq_left_of_lt Polynomial.monic_X (by simp) F.he₁ F.h h

/-- The `dv`-level height is an ultrametric equality off ties, at a fixed `Φ′`-development
coordinate `j`. -/
theorem dvHgt_add_eq_left_of_lt (F : KeyFrame O π) {A B : Polynomial O} {j : ℕ}
    (h : dvHgt F A j < dvHgt F B j) :
    dvHgt F (A + B) j = dvHgt F A j := by
  show F.stageHeight (dev F.key (A + B) j) = F.stageHeight (dev F.key A j)
  rw [dev_add_of_monic F.hmonic]
  exact stageHeight_add_eq_left_of_lt F h

/-- The `dv`-level height is ultrametric (the easy, always-true direction, no tie needed). -/
theorem dvHgt_add_ge (F : KeyFrame O π) (A B : Polynomial O) (j : ℕ) :
    min (dvHgt F A j) (dvHgt F B j) ≤ dvHgt F (A + B) j := by
  show min (F.stageHeight (dev F.key A j)) (F.stageHeight (dev F.key B j))
    ≤ F.stageHeight (dev F.key (A + B) j)
  rw [dev_add_of_monic F.hmonic]
  exact min_suppVal_le_suppVal_add Polynomial.monic_X (by simp) F.he₁ F.h _ _

/-- The `dv`-level linear term (`ℓ • height + u·j`) is ultrametric. -/
theorem dv_term_add_ge (F : KeyFrame O π) (A B : Polynomial O) (u ℓ j : ℕ) :
    min (ℓ • dvHgt F A j + (u * j : ℕ∞)) (ℓ • dvHgt F B j + (u * j : ℕ∞))
      ≤ ℓ • dvHgt F (A + B) j + (u * j : ℕ∞) := by
  have hmin := dvHgt_add_ge F A B j
  rcases le_total (dvHgt F A j) (dvHgt F B j) with hc | hc
  · rw [min_eq_left hc] at hmin
    calc min (ℓ • dvHgt F A j + (u * j : ℕ∞)) (ℓ • dvHgt F B j + (u * j : ℕ∞))
        ≤ ℓ • dvHgt F A j + (u * j : ℕ∞) := min_le_left _ _
      _ ≤ ℓ • dvHgt F (A + B) j + (u * j : ℕ∞) := by gcongr
  · rw [min_eq_right hc] at hmin
    calc min (ℓ • dvHgt F A j + (u * j : ℕ∞)) (ℓ • dvHgt F B j + (u * j : ℕ∞))
        ≤ ℓ • dvHgt F B j + (u * j : ℕ∞) := min_le_right _ _
      _ ≤ ℓ • dvHgt F (A + B) j + (u * j : ℕ∞) := by gcongr

/-! ## Part 2 — slot-read invariance under a high-height perturbation -/

/-- The window-position/digit-index arithmetic identity (independently re-derived from
`F.slotIdx_spec`; C.21/C.26 carry the same fact `private`). -/
private theorem digAt_index_spec (F : KeyFrame O π) (k t : ℕ) (ht : t ∈ F.slotWindow k) :
    F.e₁ * ((k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁) + (F.slotIdx k + F.e₁ * t) * F.h
      = k := by
  have hle : (F.slotIdx k + F.e₁ * t) * F.h ≤ k := by
    have := Finset.mem_filter.mp (by simpa only [KeyFrame.slotWindow] using ht)
    exact this.2
  have hdvd : F.e₁ ∣ k - (F.slotIdx k + F.e₁ * t) * F.h := by
    refine (Nat.modEq_iff_dvd' hle).mp ?_
    calc (F.slotIdx k + F.e₁ * t) * F.h
        = F.slotIdx k * F.h + F.e₁ * (t * F.h) := by ring
      _ ≡ F.slotIdx k * F.h + 0 [MOD F.e₁] :=
          Nat.ModEq.add_left _ ((Nat.modEq_zero_iff_dvd).mpr ⟨t * F.h, rfl⟩)
      _ = F.slotIdx k * F.h := by ring
      _ ≡ k [MOD F.e₁] := (F.slotIdx_spec k).2
  rw [Nat.mul_div_cancel' hdvd, Nat.sub_add_cancel hle]

/-- The Gauss valuation of a constant polynomial is the underlying scalar's valuation. -/
private theorem gaussVal_C (c : O) : gaussVal (Polynomial.C c) = addVal O c := by
  rw [gaussVal, Polynomial.natDegree_C, Finset.range_one, Finset.inf_singleton,
    Polynomial.coeff_C_zero]

/-- The stage height of `1` is `0`. -/
theorem stageHeight_one (F : KeyFrame O π) : F.stageHeight (1 : Polynomial O) = 0 := by
  rw [F.stageHeight_eq_inf]
  simp only [Polynomial.natDegree_one, Finset.range_one, Finset.inf_singleton,
    Polynomial.coeff_one_zero, gaussVal_C, IsDiscreteValuationRing.addVal_one,
    Nat.cast_zero, smul_zero, mul_zero, zero_add]

/-- `π^k ∣ x` from a valuation floor (independently re-derived; C.26 carries the same fact
`private` as `pow_dvd_of_le_addVal`). -/
private theorem dvd_of_le_addVal (hπ : Irreducible π) {k : ℕ} {x : O}
    (h : (k : ℕ∞) ≤ addVal O x) : π ^ k ∣ x := by
  rw [← addVal_le_iff_dvd, hπ.addVal_pow]
  exact h

/-- A coefficient consulted below a strict stage-height floor is divisible far enough to
kill the corresponding digit read (independently re-derived; C.26 carries the analogous
argument `private` inside `slotRes_eq_zero_of_lt`). -/
private theorem addVal_coeff_of_stageHeight_lt (F : KeyFrame O π) {B : Polynomial O}
    {k pos m : ℕ} (hspec : F.e₁ * m + pos * F.h = k) (hk : (k : ℕ∞) < F.stageHeight B) :
    ((m + 1 : ℕ) : ℕ∞) ≤ addVal O (B.coeff pos) := by
  have hstep : F.stageHeight B ≤ F.e₁ • addVal O (B.coeff pos) + (F.h * pos : ℕ∞) := by
    rw [F.stageHeight_eq_inf]
    by_cases hposle : pos ≤ B.natDegree
    · have hle := Finset.inf_le
        (f := fun i => F.e₁ • gaussVal (Polynomial.C (B.coeff i)) + (F.h * i : ℕ∞))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hposle))
      rwa [gaussVal_C] at hle
    · have hz : B.coeff pos = 0 := B.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hz, addVal_zero, C118a.smul_top_pos F.he₁, top_add]
      exact le_top
  have hlt : (k : ℕ∞) < F.e₁ • addVal O (B.coeff pos) + (F.h * pos : ℕ∞) :=
    lt_of_lt_of_le hk hstep
  rcases eq_or_ne (addVal O (B.coeff pos)) ⊤ with hT | hT
  · rw [hT]; exact le_top
  · obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.mp hT
    rw [← hv] at hlt ⊢
    simp only [nsmul_eq_mul] at hlt
    have hnat : k < F.e₁ * v + F.h * pos := by exact_mod_cast hlt
    have hmv : F.e₁ * m < F.e₁ * v := by
      have hstep2 : F.e₁ * m + pos * F.h < F.e₁ * v + F.h * pos := by rw [hspec]; exact hnat
      have hc : pos * F.h = F.h * pos := Nat.mul_comm pos F.h
      omega
    have hmv' : m < v := Nat.lt_of_mul_lt_mul_left hmv
    exact_mod_cast (by omega : m + 1 ≤ v)

/-- **Slot-read invariance.** `KeyFrame.slotRes` at a fixed height `k` is unchanged by
adding a `B` whose stage height strictly exceeds `k`. -/
theorem slotRes_add_eq_left_of_lt (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    {A B : Polynomial O} {k : ℕ} (hk : (k : ℕ∞) < F.stageHeight B) :
    F.slotRes H₀ hpin k (A + B) = F.slotRes H₀ hpin k A := by
  rw [KeyFrame.slotRes, KeyFrame.slotRes]
  refine Finset.sum_congr rfl fun t ht => ?_
  set m := (k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁ with hmdef
  set pos := F.slotIdx k + F.e₁ * t with hposdef
  have hspec : F.e₁ * m + pos * F.h = k := digAt_index_spec F k t ht
  have hb : ((m + 1 : ℕ) : ℕ∞) ≤ addVal O (B.coeff pos) :=
    addVal_coeff_of_stageHeight_lt F hspec hk
  have hdvd : π ^ (m + 1) ∣ B.coeff pos := dvd_of_le_addVal hπ hb
  have hdig : digAt π m (A.coeff pos) = digAt π m ((A + B).coeff pos) := by
    refine C109asm.digAt_congr hπ ?_
    have heq : (A + B).coeff pos - A.coeff pos = B.coeff pos := by
      rw [Polynomial.coeff_add]; ring
    rw [heq]
    exact hdvd
  rw [hdig]

/-- **Slot-read invariance, at the ϖ-normalized read.** `KeyFrame.twistRead` at a fixed
height `k` is unchanged by adding a `B` whose stage height strictly exceeds `k`. -/
theorem twistRead_add_eq_left_of_lt (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    {A B : Polynomial O} {k : ℕ} (hk : (k : ℕ∞) < F.stageHeight B) :
    F.twistRead H₀ hpin k (A + B) = F.twistRead H₀ hpin k A := by
  rw [KeyFrame.twistRead, KeyFrame.twistRead, slotRes_add_eq_left_of_lt F hπ H₀ hpin hk]

/-! ## Part 3 — the box-digit weight floor from `hbud`, via a two-variable lift -/

/-- Digits of `F.key`-development always have degree below `F.e₁ * F.f₁`. -/
private theorem natDegree_dev_lt' (F : KeyFrame O π) (A : Polynomial O) (b : ℕ) :
    (dev F.key A b).natDegree < F.e₁ * F.f₁ := by
  have hpos : 0 < F.key.natDegree := by rw [F.hdeg]; exact Nat.mul_pos F.he₁ F.hf₁
  have hlt := degree_dev_lt F.hmonic hpos A b
  rw [← F.hdeg]
  rcases eq_or_ne (dev F.key A b) 0 with h0 | h0
  · rw [h0, Polynomial.natDegree_zero]; exact hpos
  · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr
      (by rwa [Polynomial.degree_eq_natDegree F.hmonic.ne_zero] at hlt)

/-- The budget floor converts to a `wtCoeff`-plus-offset bound, `ℕ`-subtraction safely (`j`
in range so `j·E₂ ≤ μ₂·E₂ + 1`). -/
private theorem budgetFloor_wtCoeff_bound {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) {μ₂ j a b : ℕ} (hj : j < μ₂) (c : O)
    (hle : (budgetFloor T μ₂ j a b : ℕ∞) ≤ addVal O c) :
    ((μ₂ * T.E₂ + 1 - j * T.E₂ : ℕ) : ℕ∞) ≤ wtCoeff T c a b := by
  have hposE : 0 < F.e₁ * T.e₂ := Nat.mul_pos F.he₁ T.he₂
  rcases eq_or_ne (addVal O c) ⊤ with hT | hT
  · have hwtop : wtCoeff T c a b = ⊤ := by
      rw [wtCoeff, hT, C118a.smul_top_pos hposE, top_add]
    rw [hwtop]; exact le_top
  · obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.mp hT
    have hle' : budgetFloor T μ₂ j a b ≤ v := by
      have hle2 : (budgetFloor T μ₂ j a b : ℕ∞) ≤ (v : ℕ∞) := hv ▸ hle
      exact_mod_cast hle2
    have hgw : μ₂ * T.E₂ + 1 ≤ gridWeight T v a b j := (budgetFloor_le_iff T a b hj v).mp hle'
    have hgwu : μ₂ * T.E₂ + 1 ≤ (F.e₁ * T.e₂) * v + (a * (T.e₂ * F.h) + b * T.u₂) + j * T.E₂ := by
      simpa only [gridWeight, slotOffset] using hgw
    have hnat : μ₂ * T.E₂ + 1 - j * T.E₂ ≤ (F.e₁ * T.e₂) * v + (a * (T.e₂ * F.h) + b * T.u₂) := by
      omega
    have hwc : wtCoeff T c a b
        = (((F.e₁ * T.e₂) * v + (a * (T.e₂ * F.h) + b * T.u₂) : ℕ) : ℕ∞) := by
      rw [wtCoeff, ← hv]
      push_cast [nsmul_eq_mul]
      ring
    rw [hwc]
    exact_mod_cast hnat

/-- The inner two-variable lift of the composed-key digit `dev (composedKey T) g j`, one
`F.key`-digit at a time. -/
noncomputable def qgInner {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (g : Polynomial O) (j : ℕ) : Polynomial (Polynomial O) :=
  ∑ b ∈ Finset.range (T.e₂ * T.f₂ + 1),
    Polynomial.C (dev F.key (dev (composedKey T) g j) b) * Polynomial.X ^ b

/-- The two-variable lift of `g`'s ENTIRE composed-key/`F.key` double development, up to
coordinate `μ₂` (exclusive). -/
noncomputable def Qg {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (g : Polynomial O) (μ₂ : ℕ) : Polynomial (Polynomial O) :=
  ∑ j ∈ Finset.range μ₂, qgInner T g j * K_T T ^ j

theorem eval_qgInner {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (g : Polynomial O) (j : ℕ) :
    Polynomial.eval F.key (qgInner T g j)
      = ∑ b ∈ Finset.range (T.e₂ * T.f₂ + 1), dev F.key (dev (composedKey T) g j) b * F.key ^ b := by
  rw [qgInner, Polynomial.eval_finsetSum]
  simp

/-- `composedKey T` has positive degree (from `T.hcomp` and `F.natDegree_key_pos`, through
C.131v's `composedKey_natDegree_mul`). -/
private theorem composedKey_natDegree_pos {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) : 0 < (composedKey T).natDegree := by
  rw [Uniformity.Density.Tower.C131v.composedKey_natDegree_mul T hπ]
  exact Nat.mul_pos (by have := T.hcomp; omega) F.natDegree_key_pos

/-- Reconstruction: the inner lift evaluates back to the composed-key digit. -/
theorem eval_qgInner_eq {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (g : Polynomial O) (j : ℕ) :
    Polynomial.eval F.key (qgInner T g j) = dev (composedKey T) g j := by
  rw [eval_qgInner]
  have hcdeg : (composedKey T).natDegree = (T.e₂ * T.f₂) * F.key.natDegree :=
    Uniformity.Density.Tower.C131v.composedKey_natDegree_mul T hπ
  have hcpos : 0 < (composedKey T).natDegree := composedKey_natDegree_pos T hπ
  have hdeglt : (dev (composedKey T) g j).degree < (composedKey T).degree :=
    degree_dev_lt (composedKey_monic T) hcpos g j
  have hnatlt : (dev (composedKey T) g j).natDegree < (composedKey T).natDegree := by
    rcases eq_or_ne (dev (composedKey T) g j) 0 with h0 | h0
    · rw [h0, Polynomial.natDegree_zero]; exact hcpos
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr
        (by rwa [Polynomial.degree_eq_natDegree (composedKey_monic T).ne_zero] at hdeglt)
  have hlt : (dev (composedKey T) g j).natDegree < (T.e₂ * T.f₂ + 1) * F.key.natDegree := by
    rw [hcdeg] at hnatlt
    have hle2 : (T.e₂ * T.f₂) * F.key.natDegree ≤ (T.e₂ * T.f₂ + 1) * F.key.natDegree := by
      have := F.natDegree_key_pos
      nlinarith
    omega
  exact sum_dev_eq F.hmonic F.natDegree_key_pos (dev (composedKey T) g j) hlt

/-- Reconstruction: `Qg` evaluates back to `g`, provided `g`'s degree fits inside `μ₂`
composed-key digits. -/
theorem eval_Qg {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} (hπ : Irreducible π)
    (T : TowerDatum F H₀ hpin) (g : Polynomial O) {μ₂ : ℕ}
    (hg : g.natDegree < μ₂ * T.D₂) :
    Polynomial.eval F.key (Qg T g μ₂) = g := by
  have hcdeg : (composedKey T).natDegree = (T.e₂ * T.f₂) * F.key.natDegree :=
    Uniformity.Density.Tower.C131v.composedKey_natDegree_mul T hπ
  have hcpos : 0 < (composedKey T).natDegree := composedKey_natDegree_pos T hπ
  have hDeq : T.D₂ = (composedKey T).natDegree := by
    rw [hcdeg, TowerDatum.D₂, F.hdeg]; ring
  rw [Qg, Polynomial.eval_finsetSum]
  have hstep : ∀ j ∈ Finset.range μ₂,
      Polynomial.eval F.key (qgInner T g j * K_T T ^ j)
        = dev (composedKey T) g j * composedKey T ^ j := by
    intro j _
    rw [Polynomial.eval_mul, Polynomial.eval_pow, eval_K_T T hπ, eval_qgInner_eq T hπ g j]
  rw [Finset.sum_congr rfl hstep]
  refine sum_dev_eq (composedKey_monic T) hcpos g ?_
  rwa [← hDeq]

/-! ## Part 4 — the `DvAbove` floor on `g` -/

/-- Every term of `Qg T g μ₂` clears the grid weight `μ₂·E₂ + 1`. -/
theorem le_WT_Qg {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} (hπ : Irreducible π)
    (T : TowerDatum F H₀ hpin) {f g : Polynomial O} {μ₂ : ℕ}
    (hbud : ∀ j a b : ℕ, j < μ₂ → a < F.e₁ * F.f₁ → b < T.e₂ * T.f₂ →
      (budgetFloor T μ₂ j a b : ℕ∞)
        ≤ addVal O ((dev F.key (dev (composedKey T) f j) b).coeff a))
    (hgdig : ∀ j, j < μ₂ → dev (composedKey T) g j = dev (composedKey T) f j) :
    ((μ₂ * T.E₂ + 1 : ℕ) : ℕ∞) ≤ WT T (Qg T g μ₂) := by
  rw [Qg]
  refine le_WT_sum T (Finset.range μ₂) _ fun j hj => ?_
  have hjlt : j < μ₂ := Finset.mem_range.mp hj
  set wj : ℕ := μ₂ * T.E₂ + 1 - j * T.E₂ with hwjdef
  have hwjadd : wj + j * T.E₂ = μ₂ * T.E₂ + 1 := by
    have h1 : j * T.E₂ ≤ μ₂ * T.E₂ := mul_le_mul_right' hjlt.le T.E₂
    rw [hwjdef]; omega
  have hinner : (wj : ℕ∞) ≤ WT T (qgInner T g j) := by
    rw [qgInner]
    refine le_WT_sum T (Finset.range (T.e₂ * T.f₂ + 1)) _ fun b hbmem => ?_
    have hble : b ≤ T.e₂ * T.f₂ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hbmem)
    refine le_WT_C_mul_X_pow T _ b fun a => ?_
    by_cases ha : a < F.e₁ * F.f₁
    · by_cases hb : b < T.e₂ * T.f₂
      · have hcoeq : (dev F.key (dev (composedKey T) g j) b).coeff a
            = (dev F.key (dev (composedKey T) f j) b).coeff a := by
          rw [hgdig j hjlt]
        rw [hcoeq]
        exact budgetFloor_wtCoeff_bound T hjlt
          ((dev F.key (dev (composedKey T) f j) b).coeff a) (hbud j a b hjlt ha hb)
      · have hbtop : b = T.e₂ * T.f₂ := by omega
        have hdev0 : dev F.key (dev (composedKey T) g j) b = 0 := by
          refine dev_eq_zero_of_lt F.hmonic (by rw [F.hdeg]; exact Nat.mul_pos F.he₁ F.hf₁) _ b ?_
          rw [hbtop, F.hdeg]
          calc (dev (composedKey T) g j).natDegree
              < (composedKey T).natDegree := by
                have hcpos : 0 < (composedKey T).natDegree := composedKey_natDegree_pos T hπ
                have hdeglt : (dev (composedKey T) g j).degree < (composedKey T).degree :=
                  degree_dev_lt (composedKey_monic T) hcpos g j
                rcases eq_or_ne (dev (composedKey T) g j) 0 with h0 | h0
                · rw [h0, Polynomial.natDegree_zero]; exact hcpos
                · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr
                    (by rwa [Polynomial.degree_eq_natDegree
                      (composedKey_monic T).ne_zero] at hdeglt)
            _ = (T.e₂ * T.f₂) * (F.e₁ * F.f₁) := by
                rw [Uniformity.Density.Tower.C131v.composedKey_natDegree_mul T hπ, F.hdeg]
        rw [hdev0]
        simp
    · have hz : (dev F.key (dev (composedKey T) g j) b).coeff a = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (natDegree_dev_lt' F _ b)
          (not_lt.mp ha))
      rw [hz, wtCoeff_zero]
      exact le_top
  calc ((μ₂ * T.E₂ + 1 : ℕ) : ℕ∞)
      = ((wj : ℕ) : ℕ∞) + ((j * T.E₂ : ℕ) : ℕ∞) := by
        rw [← hwjadd]; push_cast; ring
    _ ≤ WT T (qgInner T g j) + WT T (K_T T ^ j) := add_le_add hinner (le_WT_K_T_pow T hπ j)
    _ ≤ WT T (qgInner T g j * K_T T ^ j) := WT_mul T _ _

/-- **The `DvAbove` floor on `g`.** -/
theorem dvAbove_g {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} (hπ : Irreducible π)
    (T : TowerDatum F H₀ hpin) {f g : Polynomial O} {μ₂ : ℕ}
    (hg : g.natDegree < μ₂ * T.D₂)
    (hbud : ∀ j a b : ℕ, j < μ₂ → a < F.e₁ * F.f₁ → b < T.e₂ * T.f₂ →
      (budgetFloor T μ₂ j a b : ℕ∞)
        ≤ addVal O ((dev F.key (dev (composedKey T) f j) b).coeff a))
    (hgdig : ∀ j, j < μ₂ → dev (composedKey T) g j = dev (composedKey T) f j) :
    DvAbove F g T.u₂ T.e₂ ((μ₂ * T.E₂ + 1 : ℕ) : ℕ∞) := by
  have hWT : ((μ₂ * T.E₂ + 1 : ℕ) : ℕ∞) ≤ WT T (Qg T g μ₂) := le_WT_Qg hπ T hbud hgdig
  refine dvAbove_of_forall_coeff_floor F g T.u₂ T.e₂ _ T.he₂ fun b a => ?_
  have h := dev_coeff_floor T (Qg T g μ₂) hWT b a
  rw [eval_Qg hπ T g hg] at h
  simp only [wtCoeff, nsmul_eq_mul, Nat.cast_add, Nat.cast_mul] at h
  simp only [nsmul_eq_mul, Nat.cast_mul]
  exact h

end Uniformity.Density.Tower.C131ae

/-! ## Part 5 — the main assembly, NODE C.131ae′ -/

namespace Uniformity.Density.Tower

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf
open C131ae

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- ★ **NODE C.131ae′ (`EFF.GENTOW1.21`, C.52's Step 2).** Budget floors on every two-key
development digit of `f` imply `f ∈ towerLocus T μ₂`.

Proof plan: `g := f − Φ₂^{μ₂}` inherits a `DvAbove` floor of `μ₂E₂ + 1` from `hbud`
(Part 3–4). `Φ₂^{μ₂}`'s own `dv`-support is exactly `μ₂E₂` (read off the top digit). Every
abscissa clears `μ₂E₂` (the easy ultrametric inequality); abscissae on `Φ₂^{μ₂}`'s side keep
their exact height (the tie-break law, Part 1) and their exact residual digit (the slot-read
invariance law, Part 2); abscissae off `Φ₂^{μ₂}`'s side stay off `f`'s side too. This
identifies `f`'s side data with `Φ₂^{μ₂}`'s exactly. -/
theorem mem_towerLocus_of_budget {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)]
    {μ₂ : ℕ} (hμ₂ : 0 < μ₂) {f : Polynomial O} (hf : f.Monic)
    (hdeg : f.natDegree = μ₂ * T.D₂)
    (hbud : ∀ j a b : ℕ, j < μ₂ → a < F.e₁ * F.f₁ → b < T.e₂ * T.f₂ →
      (budgetFloor T μ₂ j a b : ℕ∞)
        ≤ addVal O ((dev F.key (dev (composedKey T) f j) b).coeff a)) :
    f ∈ towerLocus T μ₂ := by
  classical
  obtain ⟨hXmon, hXdeg, hXpure, hXres⟩ := composedKey_pow_mem_towerLocus T hπ hh hμ₂
  set g : Polynomial O := f - composedKey T ^ μ₂ with hgdef
  have hNeq : f.natDegree = (composedKey T ^ μ₂).natDegree := hdeg.trans hXdeg.symm
  have hfpos : 0 < f.natDegree := by
    rw [hdeg, TowerDatum.D₂]
    exact Nat.mul_pos hμ₂ (Nat.mul_pos (Nat.mul_pos F.he₁ F.hf₁) (Nat.mul_pos T.he₂ T.hf₂))
  -- degree of `g`
  have hglt : g.natDegree < f.natDegree := by
    have hdlt : g.degree < (f.natDegree : WithBot ℕ) := by
      rw [hgdef]
      exact Uniformity.Hensel.degree_sub_lt_of_monic_of_natDegree_eq hf hXmon hNeq
    rcases eq_or_ne g 0 with h0 | h0
    · rw [h0, Polynomial.natDegree_zero]; exact hfpos
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hdlt
  have hgDeg : g.natDegree < μ₂ * T.D₂ := by rw [← hdeg]; exact hglt
  have heqpoly : composedKey T ^ μ₂ + g = f := by rw [hgdef]; ring
  -- the composed-key digits of `g` agree with `f`'s, below `μ₂`
  have hcomposedKeyPos : 0 < (composedKey T).natDegree := composedKey_natDegree_pos T hπ
  have hgdig : ∀ j, j < μ₂ → dev (composedKey T) g j = dev (composedKey T) f j := by
    intro j hj
    have hsub := Uniformity.Density.Tower.C131v.dev_sub (composedKey_monic T) f
      (composedKey T ^ μ₂) j
    have htop := dev_pow_self (composedKey_monic T) hcomposedKeyPos μ₂ j
    rw [if_neg (Nat.ne_of_lt hj)] at htop
    rw [hgdef, hsub, htop, sub_zero]
  -- the `DvAbove` floor on `g`
  have hDvAboveG : DvAbove F g T.u₂ T.e₂ ((μ₂ * T.E₂ + 1 : ℕ) : ℕ∞) :=
    dvAbove_g hπ T hgDeg hbud hgdig
  -- `Φ₂^{μ₂}`'s own `dv`-support is exactly `μ₂ * E₂`
  have htopidx : (composedKey T ^ μ₂).natDegree / (F.e₁ * F.f₁) = μ₂ * T.e₂ * T.f₂ := by
    rw [hXdeg, TowerDatum.D₂]
    have hD : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
    rw [show μ₂ * (F.e₁ * F.f₁ * (T.e₂ * T.f₂)) = (μ₂ * T.e₂ * T.f₂) * (F.e₁ * F.f₁) by ring]
    exact Nat.mul_div_cancel _ hD
  have hXtop : dev F.key (composedKey T ^ μ₂) (μ₂ * T.e₂ * T.f₂) = 1 := by
    have hdegeq : (composedKey T ^ μ₂).natDegree = (μ₂ * T.e₂ * T.f₂) * F.key.natDegree := by
      rw [hXdeg, TowerDatum.D₂, F.hdeg]; ring
    exact Uniformity.Density.Tower.C131v.dev_top_eq_one F.hmonic F.natDegree_key_pos
      (μ₂ * T.e₂ * T.f₂) (composedKey T ^ μ₂) hXmon hdegeq
  have hXtopHgt : dvHgt F (composedKey T ^ μ₂) (μ₂ * T.e₂ * T.f₂) = 0 := by
    show F.stageHeight (dev F.key (composedKey T ^ μ₂) (μ₂ * T.e₂ * T.f₂)) = 0
    rw [hXtop, stageHeight_one]
  have hmemtop : (μ₂ * T.e₂ * T.f₂) ∈ dvSideSet F (composedKey T ^ μ₂) T.u₂ T.e₂ := by
    have h := hXpure.2
    rwa [htopidx] at h
  have honmemtop : DvOnSide F (composedKey T ^ μ₂) T.u₂ T.e₂ (μ₂ * T.e₂ * T.f₂) :=
    dvOnSide_of_mem_dvSideSet hmemtop
  have hXsupp : dvSupp F (composedKey T ^ μ₂) T.u₂ T.e₂ = ((μ₂ * T.E₂ : ℕ) : ℕ∞) := by
    have heq := honmemtop.1
    rw [hXtopHgt, smul_zero, zero_add] at heq
    rw [heq, TowerDatum.E₂]
    exact_mod_cast (by ring : T.u₂ * (μ₂ * T.e₂ * T.f₂) = μ₂ * (T.e₂ * T.f₂ * T.u₂))
  -- every abscissa clears `μ₂E₂` on `Φ₂^{μ₂}`'s own polygon
  have hXterm_ge : ∀ i : ℕ, ((μ₂ * T.E₂ : ℕ) : ℕ∞)
      ≤ T.e₂ • dvHgt F (composedKey T ^ μ₂) i + (T.u₂ * i : ℕ∞) := by
    intro i
    rw [← hXsupp]
    by_cases hile : i ≤ (composedKey T ^ μ₂).natDegree
    · exact Finset.inf_le (f := fun j => T.e₂ • dvHgt F (composedKey T ^ μ₂) j + (T.u₂ * j : ℕ∞))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hile))
    · have hz : dvHgt F (composedKey T ^ μ₂) i = ⊤ := C118a.dvHgt_top_of_gt F _ (by omega)
      rw [hz, C118a.smul_top_pos T.he₂, top_add]
      exact le_top
  -- the tie-break: on `Φ₂^{μ₂}`'s side, `f`'s height agrees exactly
  have htie : ∀ i : ℕ, DvOnSide F (composedKey T ^ μ₂) T.u₂ T.e₂ i →
      dvHgt F f i = dvHgt F (composedKey T ^ μ₂) i := by
    intro i hon
    have hstrict : dvHgt F (composedKey T ^ μ₂) i < dvHgt F g i := by
      by_contra hcon
      push_neg at hcon
      have hgterm : ((μ₂ * T.E₂ + 1 : ℕ) : ℕ∞) ≤ T.e₂ • dvHgt F g i + (T.u₂ * i : ℕ∞) :=
        hDvAboveG i
      have hXterm_eq :
          ((μ₂ * T.E₂ : ℕ) : ℕ∞) = T.e₂ • dvHgt F (composedKey T ^ μ₂) i + (T.u₂ * i : ℕ∞) :=
        hXsupp.symm.trans hon.1
      have hle : T.e₂ • dvHgt F g i ≤ T.e₂ • dvHgt F (composedKey T ^ μ₂) i :=
        nsmul_le_nsmul_right hcon T.e₂
      have hchain : ((μ₂ * T.E₂ + 1 : ℕ) : ℕ∞) ≤ ((μ₂ * T.E₂ : ℕ) : ℕ∞) :=
        calc ((μ₂ * T.E₂ + 1 : ℕ) : ℕ∞) ≤ T.e₂ • dvHgt F g i + (T.u₂ * i : ℕ∞) := hgterm
          _ ≤ T.e₂ • dvHgt F (composedKey T ^ μ₂) i + (T.u₂ * i : ℕ∞) := by gcongr
          _ = ((μ₂ * T.E₂ : ℕ) : ℕ∞) := hXterm_eq.symm
      have : μ₂ * T.E₂ + 1 ≤ μ₂ * T.E₂ := by exact_mod_cast hchain
      omega
    have hadd := dvHgt_add_eq_left_of_lt F hstrict
    rwa [heqpoly] at hadd
  -- off `Φ₂^{μ₂}`'s side, `f`'s term stays strictly above `μ₂E₂`
  have hoff : ∀ i : ℕ, ¬ DvOnSide F (composedKey T ^ μ₂) T.u₂ T.e₂ i →
      ((μ₂ * T.E₂ : ℕ) : ℕ∞) < T.e₂ • dvHgt F f i + (T.u₂ * i : ℕ∞) := by
    intro i hnon
    have hge := hXterm_ge i
    have hne : T.e₂ • dvHgt F (composedKey T ^ μ₂) i + (T.u₂ * i : ℕ∞) ≠ ((μ₂ * T.E₂ : ℕ) : ℕ∞) := by
      intro heq0
      by_cases hfin : dvHgt F (composedKey T ^ μ₂) i = ⊤
      · rw [hfin, C118a.smul_top_pos T.he₂, top_add] at heq0
        exact (ENat.coe_ne_top _) heq0.symm
      · exact hnon ⟨hXsupp.trans heq0.symm, hfin⟩
    have hgt : ((μ₂ * T.E₂ : ℕ) : ℕ∞) < T.e₂ • dvHgt F (composedKey T ^ μ₂) i + (T.u₂ * i : ℕ∞) :=
      lt_of_le_of_ne hge (Ne.symm hne)
    have hXge1 : ((μ₂ * T.E₂ + 1 : ℕ) : ℕ∞)
        ≤ T.e₂ • dvHgt F (composedKey T ^ μ₂) i + (T.u₂ * i : ℕ∞) := by
      have h1 : ((μ₂ * T.E₂ : ℕ) : ℕ∞) + 1 ≤ T.e₂ • dvHgt F (composedKey T ^ μ₂) i + (T.u₂ * i : ℕ∞) :=
        Order.add_one_le_of_lt hgt
      calc ((μ₂ * T.E₂ + 1 : ℕ) : ℕ∞) = ((μ₂ * T.E₂ : ℕ) : ℕ∞) + 1 := by push_cast; ring
        _ ≤ _ := h1
    have hgterm : ((μ₂ * T.E₂ + 1 : ℕ) : ℕ∞) ≤ T.e₂ • dvHgt F g i + (T.u₂ * i : ℕ∞) := hDvAboveG i
    have hmin : min (T.e₂ • dvHgt F (composedKey T ^ μ₂) i + (T.u₂ * i : ℕ∞))
        (T.e₂ • dvHgt F g i + (T.u₂ * i : ℕ∞)) ≤ T.e₂ • dvHgt F f i + (T.u₂ * i : ℕ∞) := by
      rw [← heqpoly]
      exact dv_term_add_ge F _ g T.u₂ T.e₂ i
    have hfterm : ((μ₂ * T.E₂ + 1 : ℕ) : ℕ∞) ≤ T.e₂ • dvHgt F f i + (T.u₂ * i : ℕ∞) :=
      le_trans (le_min hXge1 hgterm) hmin
    calc ((μ₂ * T.E₂ : ℕ) : ℕ∞) < ((μ₂ * T.E₂ + 1 : ℕ) : ℕ∞) := by
          have : (μ₂ * T.E₂ : ℕ) < μ₂ * T.E₂ + 1 := by omega
          exact_mod_cast this
      _ ≤ T.e₂ • dvHgt F f i + (T.u₂ * i : ℕ∞) := hfterm
  -- `f`'s own `dv`-support is exactly `μ₂E₂`
  have hfsupp : dvSupp F f T.u₂ T.e₂ = ((μ₂ * T.E₂ : ℕ) : ℕ∞) := by
    have hon0 : DvOnSide F (composedKey T ^ μ₂) T.u₂ T.e₂ 0 :=
      dvOnSide_of_mem_dvSideSet hXpure.1
    have heq0 := htie 0 hon0
    apply le_antisymm
    · calc dvSupp F f T.u₂ T.e₂
          ≤ T.e₂ • dvHgt F f 0 + (T.u₂ * 0 : ℕ∞) :=
            Finset.inf_le (f := fun j => T.e₂ • dvHgt F f j + (T.u₂ * j : ℕ∞))
              (Finset.mem_range.mpr (by omega))
        _ = T.e₂ • dvHgt F (composedKey T ^ μ₂) 0 + (T.u₂ * 0 : ℕ∞) := by rw [heq0]
        _ = ((μ₂ * T.E₂ : ℕ) : ℕ∞) := hon0.1.symm.trans hXsupp
    · refine Finset.le_inf fun i _ => ?_
      by_cases hon : DvOnSide F (composedKey T ^ μ₂) T.u₂ T.e₂ i
      · rw [htie i hon]; exact (hon.1.symm.trans hXsupp).symm.le
      · exact (hoff i hon).le
  -- so every abscissa on `Φ₂^{μ₂}`'s side is on `f`'s side too
  have honF : ∀ i : ℕ, DvOnSide F (composedKey T ^ μ₂) T.u₂ T.e₂ i → DvOnSide F f T.u₂ T.e₂ i := by
    intro i hon
    have heqhgt := htie i hon
    refine ⟨?_, ?_⟩
    · rw [hfsupp, heqhgt]; exact hXsupp.symm.trans hon.1
    · rw [heqhgt]; exact hon.2
  -- membership: `IsDvPure`
  have hIsDvPure : IsDvPure F f T.u₂ T.e₂ := by
    have htopidxF : f.natDegree / (F.e₁ * F.f₁) = μ₂ * T.e₂ * T.f₂ := by
      rw [hNeq]; exact htopidx
    refine ⟨?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
        honF 0 (dvOnSide_of_mem_dvSideSet hXpure.1)⟩
    · rw [htopidxF]
      have hdivle : f.natDegree / (F.e₁ * F.f₁) ≤ f.natDegree := Nat.div_le_self _ _
      rw [htopidxF] at hdivle
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
        honF (μ₂ * T.e₂ * T.f₂) (dvOnSide_of_mem_dvSideSet hmemtop)⟩
  -- the side-set identification: `f` and `Φ₂^{μ₂}` share the same `dvSideSet`
  have hOnIff : ∀ i : ℕ, DvOnSide F f T.u₂ T.e₂ i ↔ DvOnSide F (composedKey T ^ μ₂) T.u₂ T.e₂ i := by
    intro i
    refine ⟨fun hi => ?_, honF i⟩
    by_contra hcon
    have hthis := hoff i hcon
    rw [← hi.1, hfsupp] at hthis
    exact absurd hthis (lt_irrefl _)
  have hsideEq : dvSideSet F f T.u₂ T.e₂ = dvSideSet F (composedKey T ^ μ₂) T.u₂ T.e₂ := by
    ext i
    simp only [dvSideSet, Finset.mem_filter, Finset.mem_range, hNeq]
    exact and_congr_right (fun _ => hOnIff i)
  refine ⟨hf, hdeg, hIsDvPure, ?_⟩
  -- the exact residual, `∀`-quantified
  intro hne M₀ hp
  have hneX : (dvSideSet F (composedKey T ^ μ₂) T.u₂ T.e₂).Nonempty := hsideEq ▸ hne
  have hminEq : dvSideMin F f T.u₂ T.e₂ hne
      = dvSideMin F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX :=
    Uniformity.Density.Tower.C118b.min'_congr hsideEq hne hneX
  have hmaxEq : dvSideMax F f T.u₂ T.e₂ hne
      = dvSideMax F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX :=
    Uniformity.Density.Tower.C118b.max'_congr hsideEq hne hneX
  have hdegEq : dvSideDeg F f T.u₂ T.e₂ hne
      = dvSideDeg F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX := by
    rw [dvSideDeg, dvSideDeg, hminEq, hmaxEq]
  -- the pinned height at the shared left endpoint
  have hminmemX : dvSideMin F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX
      ∈ dvSideSet F (composedKey T ^ μ₂) T.u₂ T.e₂ := Finset.min'_mem _ _
  have honminX : DvOnSide F (composedKey T ^ μ₂) T.u₂ T.e₂
      (dvSideMin F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX) := dvOnSide_of_mem_dvSideSet hminmemX
  have hfinX : dvHgt F (composedKey T ^ μ₂)
      (dvSideMin F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX) ≠ ⊤ := honminX.2
  obtain ⟨M0X, hpX0⟩ := ENat.ne_top_iff_exists.mp hfinX
  have hpX : dvHgt F (composedKey T ^ μ₂)
      (dvSideMin F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX) = (M0X : ℕ∞) := hpX0.symm
  have hMeq : M₀ = M0X := by
    have hp' : dvHgt F f (dvSideMin F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX) = (M₀ : ℕ∞) := by
      rw [← hminEq]; exact hp
    have htieAtMin := htie (dvSideMin F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX) honminX
    rw [htieAtMin] at hp'
    exact_mod_cast hp'.symm.trans hpX
  -- the side-line equation at the left endpoint
  have hlineMinNat : T.e₂ * M0X
      + T.u₂ * dvSideMin F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX = μ₂ * T.E₂ := by
    have hle := honminX.1
    rw [hpX] at hle
    have hcast := hle.symm.trans hXsupp
    simp only [nsmul_eq_mul] at hcast
    exact_mod_cast hcast
  -- the length law, cleared: `dvSideMax = dvSideMin + e₂ * d`
  have hmaxeq : dvSideMax F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX
      = dvSideMin F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX
        + T.e₂ * dvSideDeg F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX := by
    have hlen := dvSideLen_eq F T.he₂ T.hcop hneX
    rw [dvSideLen] at hlen
    have hmaxmemX : dvSideMax F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX
        ∈ dvSideSet F (composedKey T ^ μ₂) T.u₂ T.e₂ := Finset.max'_mem _ _
    have hle : dvSideMin F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX
        ≤ dvSideMax F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX := Finset.min'_le _ _ hmaxmemX
    omega
  -- `u₂ * d ≤ M0X`: no slot ever asks for more than the pinned left height
  have htu2d : T.u₂ * dvSideDeg F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX ≤ M0X := by
    have hmaxmemX : dvSideMax F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX
        ∈ dvSideSet F (composedKey T ^ μ₂) T.u₂ T.e₂ := Finset.max'_mem _ _
    have honmaxX := dvOnSide_of_mem_dvSideSet hmaxmemX
    have hge : (T.u₂ * dvSideMax F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX : ℕ∞)
        ≤ dvSupp F (composedKey T ^ μ₂) T.u₂ T.e₂ := by
      rw [honmaxX.1]; exact le_add_self
    rw [hXsupp, hmaxeq] at hge
    have hgeNat : T.u₂ * (dvSideMin F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX
        + T.e₂ * dvSideDeg F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX) ≤ μ₂ * T.E₂ := by
      exact_mod_cast hge
    have hexpand : T.u₂ * (dvSideMin F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX
        + T.e₂ * dvSideDeg F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX)
        = T.u₂ * dvSideMin F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX
          + T.u₂ * T.e₂ * dvSideDeg F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX := by ring
    rw [hexpand] at hgeNat
    have hfinal : T.u₂ * T.e₂ * dvSideDeg F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX ≤ T.e₂ * M0X := by
      omega
    have hfactor : T.u₂ * T.e₂ * dvSideDeg F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX
        = T.e₂ * (T.u₂ * dvSideDeg F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX) := by ring
    rw [hfactor] at hfinal
    exact Nat.le_of_mul_le_mul_left hfinal T.he₂
  have htu2 : ∀ t : ℕ, t ≤ dvSideDeg F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX → T.u₂ * t ≤ M0X := by
    intro t ht
    have : T.u₂ * t ≤ T.u₂ * dvSideDeg F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX :=
      mul_le_mul_left' ht T.u₂
    omega
  -- the per-consulted-slot height comparison
  have hgHeight : ∀ t : ℕ, t ≤ dvSideDeg F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX →
      ((M0X - T.u₂ * t : ℕ) : ℕ∞) <
        dvHgt F g (dvSideMin F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX + t * T.e₂) := by
    intro t ht
    have htu := htu2 t ht
    set i := dvSideMin F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX + t * T.e₂ with hidef
    have hlineval : T.e₂ * (M0X - T.u₂ * t) + T.u₂ * i = μ₂ * T.E₂ := by
      have hexp : T.u₂ * i = T.u₂ * dvSideMin F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX
          + T.e₂ * (T.u₂ * t) := by
        rw [hidef]; ring
      rw [hexp, mul_tsub]
      have hle2 : T.e₂ * (T.u₂ * t) ≤ T.e₂ * M0X := mul_le_mul_left' htu T.e₂
      omega
    by_contra hcon
    push_neg at hcon
    have hmono : T.e₂ • dvHgt F g i ≤ T.e₂ • ((M0X - T.u₂ * t : ℕ) : ℕ∞) :=
      nsmul_le_nsmul_right hcon T.e₂
    have hstep : T.e₂ • dvHgt F g i + (T.u₂ * i : ℕ∞)
        ≤ T.e₂ • ((M0X - T.u₂ * t : ℕ) : ℕ∞) + (T.u₂ * i : ℕ∞) := by gcongr
    have hcast : T.e₂ • ((M0X - T.u₂ * t : ℕ) : ℕ∞) + (T.u₂ * i : ℕ∞)
        = ((T.e₂ * (M0X - T.u₂ * t) + T.u₂ * i : ℕ) : ℕ∞) := by
      push_cast [nsmul_eq_mul]; ring
    rw [hcast, hlineval] at hstep
    have hchain : ((μ₂ * T.E₂ + 1 : ℕ) : ℕ∞) ≤ ((μ₂ * T.E₂ : ℕ) : ℕ∞) :=
      le_trans (hDvAboveG i) hstep
    have : μ₂ * T.E₂ + 1 ≤ μ₂ * T.E₂ := by exact_mod_cast hchain
    omega
  -- the coefficient-by-coefficient match
  have hResEq : dvResPoly F H₀ hpin f T.u₂ T.e₂ hne M₀ hp
      = dvResPoly F H₀ hpin (composedKey T ^ μ₂) T.u₂ T.e₂ hneX M0X hpX := by
    refine Polynomial.ext fun t => ?_
    unfold dvResPoly
    rw [Uniformity.Hensel.coeff_sum_range_C_mul_X_pow,
      Uniformity.Hensel.coeff_sum_range_C_mul_X_pow, hdegEq]
    by_cases htle : t ≤ dvSideDeg F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX
    · rw [if_pos (Nat.lt_succ_of_le htle), if_pos (Nat.lt_succ_of_le htle), hMeq, hminEq]
      have hcomm : M0X - t * T.u₂ = M0X - T.u₂ * t := by rw [Nat.mul_comm]
      rw [hcomm]
      have hdevsum : dev F.key (composedKey T ^ μ₂)
          (dvSideMin F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX + t * T.e₂)
          + dev F.key g (dvSideMin F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX + t * T.e₂)
          = dev F.key f (dvSideMin F (composedKey T ^ μ₂) T.u₂ T.e₂ hneX + t * T.e₂) := by
        rw [← dev_add_of_monic F.hmonic, heqpoly]
      rw [← hdevsum]
      exact twistRead_add_eq_left_of_lt F hπ H₀ hpin (hgHeight t htle)
    · rw [if_neg (by omega), if_neg (by omega)]
  rw [hResEq]
  exact hXres hneX M0X hpX

end Uniformity.Density.Tower

/-! ## Axiom footprint

Every declaration below is Lean-core (`propext, Classical.choice, Quot.sound`) EXCEPT the
ones explicitly marked — those carry the DECLARED cite `fgmn_dv_exact_mul` (C66b, gate (b))
purely because they consume `composedKey_pow_mem_towerLocus` (C.131ac), which itself carries
it by design. -/

section AxCheck

open Uniformity.Density.Tower.C131ae

#print axioms Uniformity.Density.Tower.C131ae.addVal_neg
#print axioms Uniformity.Density.Tower.C131ae.gaussVal_neg
#print axioms Uniformity.Density.Tower.C131ae.dev_neg_of_monic
#print axioms Uniformity.Density.Tower.C131ae.suppVal_neg
#print axioms Uniformity.Density.Tower.C131ae.suppVal_add_eq_left_of_lt
#print axioms Uniformity.Density.Tower.C131ae.stageHeight_add_eq_left_of_lt
#print axioms Uniformity.Density.Tower.C131ae.dvHgt_add_eq_left_of_lt
#print axioms Uniformity.Density.Tower.C131ae.dvHgt_add_ge
#print axioms Uniformity.Density.Tower.C131ae.dv_term_add_ge
#print axioms Uniformity.Density.Tower.C131ae.gaussVal_C
#print axioms Uniformity.Density.Tower.C131ae.stageHeight_one
#print axioms Uniformity.Density.Tower.C131ae.slotRes_add_eq_left_of_lt
#print axioms Uniformity.Density.Tower.C131ae.twistRead_add_eq_left_of_lt
#print axioms Uniformity.Density.Tower.C131ae.budgetFloor_wtCoeff_bound
#print axioms Uniformity.Density.Tower.C131ae.qgInner
#print axioms Uniformity.Density.Tower.C131ae.Qg
#print axioms Uniformity.Density.Tower.C131ae.eval_qgInner
#print axioms Uniformity.Density.Tower.C131ae.composedKey_natDegree_pos
#print axioms Uniformity.Density.Tower.C131ae.eval_qgInner_eq
#print axioms Uniformity.Density.Tower.C131ae.eval_Qg
#print axioms Uniformity.Density.Tower.C131ae.le_WT_Qg
#print axioms Uniformity.Density.Tower.C131ae.dvAbove_g
-- `le_WT_Qg`/`dvAbove_g` only consume `hbud`/`budgetFloor` arithmetic (Lean-core, confirmed
-- above); the node itself is the ONLY declaration here that consumes
-- `composedKey_pow_mem_towerLocus`, hence the ONLY one carrying `fgmn_dv_exact_mul`:
#print axioms Uniformity.Density.Tower.mem_towerLocus_of_budget

end AxCheck
