/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C133mh4
import Uniformity.ChapC.C133mh5
import Uniformity.ChapC.C133mh8
import Uniformity.ChapC.C133mh14

/-!
# Uniformity.ChapC.C133mh9 — `[MH9L 2026-08-28]`: node MH.9 (+ the transcription of MH9M's
law) — THE FINAL ENGINE NODE: the above-line mixed read law (AMR), Lemma S, and Theorem A

**Node MH.9** (`docs/in-progress/HENSEL_ENGINE_2026-08-26.md`, the `[MH9M 2026-08-28]`
addendum; verdict `runs/wave-c/verdict_MH9M.md`).  This file transcribes MH9M's
mathematics-level discharge into Lean, in the verdict's nine-node order:

1. `dvLinePoly` + `dvLinePoly_coeff` — the bounded grade-line polynomial (MH9M.1).
2. `dvLinePoly_dvWindowLift` — the window lift's line read (packages
   `C133mh5.twistRead_dvWindowLift`).
3. `dvLinePoly_mul_of_isDvPure` — **Law AMR** (MH9M.2): for monic pure `p` with pin
   `(Mp, P := R(p), b := deg P)` and `z` in the degree window with support floor at grade
   `d = ℓM + uj₀`, `dvLinePoly (Mp+M) (A+b) (p·z) = P · dvLinePoly M A z`.
4. `lemmaS : C133mh5.LemmaSStatement O` — the graded solve (MH9M.3), discharging the
   signed statement shape at `C133mh5.lean:830` byte-as-is.
5. `dvSupp_sub_succ_of_same_residual` — equal grade-`w` line reads contract the
   difference's support one grade.
6. `monic_of_dvGradedLimit` — the separatedness packaging of `C133mh8`'s limit
   (OPEN-MH9-LIMIT-MONIC).
7. `eq_zero_of_forall_dvSupp` — bounded degree + unbounded support ⟹ `0`.
8. `isDvPure_one` / `dvHgt_one_zero` / `dvResPoly_one` — the unit branch
   (OPEN-MH9-UNIT-BRANCH).
9. ★ `theoremA : C133mh14.TheoremAStatement O` — the seven-step assembly (MH9M.4),
   discharging the signed statement shape at `C133mh14.lean:264` byte-as-is; it consumes
   NO cite (`C133mh14.blockFrontier_of_context_of_theoremA` consumes it directly).

## OPEN-MH9-PRIVATE-PRICING (Part 0)

MH.3's pricing/extraction helpers (`carry_term_floor`, `read_kill`, `modKey_term_floor`,
`modKey_term_succ_floor`, `pair_line_le/lt`, `dvResPoly_coeff_of_le/gt`,
`exists_key_height_lt`, `natDegree_dev_lt_frame`, the ℕ∞ weight readers) are `private` in
`C133mh3` and cannot cross files; per the verdict's OPEN-MH9-PRIVATE-PRICING they are
re-declared here **byte-identical in mechanism** (source: `C133mh3.lean` Parts 0/2/4/6,
credited per declaration), as are C133mh5's private `dev_finsetSum`, C133mh14's private
`exists_pin`, and C133mh11's private `dvResPoly_pin_congr` (OPEN-MH9-UNIVERSAL-PIN).
The standing D9 `Field` reconstruction is re-declared per the C.04 convention.

## DEPENDS

C133mh0 (M4 `dv_pure_add_of_lt`, `twistRead_one`) · C133mh1 (TW-δ, via C133mh3's landed
root) · C133mh3 (Theorem M: `dvSupp_mul`, `dvSideDeg_mul`, `m1TwistProductLaw`,
`dvResPoly_mul_gen`) · C133mh4 (M-monic + `dvHgt_dvSideMin_eq_mul_dvSideDeg_of_isDvPure`) ·
C133mh5 (side/window lifts + clause lemmas, Bézout, `le_dvSupp_succ_of_lineReads_eq_zero`,
`LemmaSStatement`) · C133mh8 (`exists_dvGradedLimit`, `gaussVal_of_shifted_dvSupp`) ·
C133mh14 (`TheoremAStatement`) · the C130nv2/rp2/rp4, C131y, C130s6, C118a, C131ae banks ·
C.06–C.08/C.25/C.26/C.29/C.34/C.35 vocabulary · B-chapter `dev`/`gaussVal` calculus.

## Status

Footprints Lean-core only — see the AxCheck footer (`theoremA` consumes no cite).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C133mh9

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C131y
open Uniformity.Density.Tower.C130nv2 Uniformity.Density.Tower.C130rp2
open Uniformity.Density.Tower.C130rp4

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## Part 0 — private plumbing and the OPEN-MH9-PRIVATE-PRICING copies

Every declaration in this part is a re-declaration of a landed `private` helper (its
source file is named in the docstring); none is new mathematics. -/

/-- Local D9 reconstruction (standing convention; source: C133mh3 Part 0). -/
private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by
    simpa using (Polynomial.irreducible_X (R := IsLocalRing.ResidueField O))

@[reducible] private noncomputable def localFieldStageField (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : F.Pin H₀) : Field (F.stageField H₀ hpin) :=
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  haveI : Fact (Irreducible (F.frameRes H₀ hpin)) := ⟨(F.hresirr H₀ hpin).1⟩
  AdjoinRoot.instField

/-- Every outer digit is a digit (source: C133mh3's private `natDegree_dev_lt_frame`). -/
private theorem natDegree_dev_lt_frame (F : KeyFrame O π) (f : Polynomial O) (j : ℕ) :
    (dev F.key f j).natDegree < F.e₁ * F.f₁ := by
  have hpos : 0 < F.key.natDegree := F.natDegree_key_pos
  have hlt : (dev F.key f j).degree < F.key.degree := degree_dev_lt F.hmonic hpos f j
  rw [← F.hdeg]
  rcases eq_or_ne (dev F.key f j) 0 with h0 | h0
  · rw [h0, Polynomial.natDegree_zero]; exact hpos
  · refine (Polynomial.natDegree_lt_iff_degree_lt h0).mpr ?_
    rwa [Polynomial.degree_eq_natDegree F.hmonic.ne_zero] at hlt

/-- The key's height is a nat with `ℓ·V < u` under the strict floor (source: C133mh3's
private `exists_key_height_lt`). -/
private theorem exists_key_height_lt (F : KeyFrame O π) {u ℓ : ℕ}
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u) :
    ∃ V : ℕ, F.stageHeight F.key = (V : ℕ∞) ∧ ℓ * V < u := by
  obtain ⟨V, hV⟩ := ENat.ne_top_iff_exists.1 (F.stageHeight_ne_top F.hmonic.ne_zero)
  have htop : F.stageHeight F.key ≤ ((F.h * F.key.natDegree : ℕ) : ℕ∞) := by
    rw [F.stageHeight_eq_inf]
    refine le_trans (Finset.inf_le (Finset.self_mem_range_succ F.key.natDegree)) ?_
    rw [F.hmonic.coeff_natDegree, GateKit.gaussVal_C, addVal_one, smul_zero, zero_add,
      Nat.cast_mul]
  rw [← hV] at htop
  have hVle : V ≤ F.h * F.key.natDegree := by exact_mod_cast htop
  refine ⟨V, hV.symm, ?_⟩
  calc ℓ * V ≤ ℓ * (F.h * F.key.natDegree) := Nat.mul_le_mul_left ℓ hVle
    _ = ℓ * ((F.e₁ * F.f₁) * F.h) := by rw [F.hdeg]; ring
    _ < u := hfloor

/-- Non-strict ℕ∞ weight reader (source: C133mh3's private `le_of_weight_le`). -/
private theorem le_of_weight_le {ℓ u J c : ℕ} {x : ℕ∞} (hℓ : 0 < ℓ)
    (h : ((ℓ * c + u * J : ℕ) : ℕ∞) ≤ ℓ • x + ((u * J : ℕ) : ℕ∞)) :
    ((c : ℕ) : ℕ∞) ≤ x := by
  rcases eq_or_ne x ⊤ with rfl | hT
  · exact le_top
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 hT
  rw [← ha] at h ⊢
  rw [nsmul_eq_mul] at h
  have hnat : ℓ * c + u * J ≤ ℓ * a + u * J := by exact_mod_cast h
  exact_mod_cast Nat.le_of_mul_le_mul_left (by omega : ℓ * c ≤ ℓ * a) hℓ

set_option linter.unusedVariables false in
/-- Strict ℕ∞ weight reader (source: C133mh3's private `succ_le_of_weight_succ_le'`). -/
private theorem succ_le_of_weight_succ_le' {ℓ u J c : ℕ} {x : ℕ∞} (hℓ : 0 < ℓ)
    (h : ((ℓ * c + u * J + 1 : ℕ) : ℕ∞) ≤ ℓ • x + ((u * J : ℕ) : ℕ∞)) :
    ((c + 1 : ℕ) : ℕ∞) ≤ x := by
  rcases eq_or_ne x ⊤ with rfl | hT
  · exact le_top
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 hT
  rw [← ha] at h ⊢
  rw [nsmul_eq_mul] at h
  have hnat : ℓ * c + u * J + 1 ≤ ℓ * a + u * J := by exact_mod_cast h
  have hca : c < a := Nat.lt_of_mul_lt_mul_left (by omega : ℓ * c < ℓ * a)
  exact_mod_cast hca

/-- Off-side slots price strictly above the support line (source: C133mh3's private
`succ_dvSupp_le_of_not_dvOnSide`). -/
private theorem succ_dvSupp_le_of_not_dvOnSide {F : KeyFrame O π} {f : Polynomial O}
    {u ℓ : ℕ} (hℓ : 0 < ℓ) {S : ℕ} (hS : dvSupp F f u ℓ = (S : ℕ∞)) {j : ℕ}
    (hoff : ¬ DvOnSide F f u ℓ j) :
    ((S + 1 : ℕ) : ℕ∞) ≤ ℓ • dvHgt F f j + (u * j : ℕ∞) := by
  rcases eq_or_ne (dvHgt F f j) ⊤ with hT | hT
  · rw [hT, C118a.smul_top_pos hℓ, top_add]
    exact le_top
  obtain ⟨H, hH⟩ := ENat.ne_top_iff_exists.1 hT
  have hlt := lt_dvWeight hℓ hS hH.symm hoff
  rw [← hH, weight_read]
  exact_mod_cast hlt

/-- Both factors clear their lines ⟹ the pair prices `≥ Sg + Sz` (source: C133mh3's
private `pair_line_le`). -/
private theorem pair_line_le {F : KeyFrame O π} {u ℓ : ℕ} (hℓ : 0 < ℓ)
    {g z : Polynomial O} {Sg Sz : ℕ}
    (hSg : dvSupp F g u ℓ = (Sg : ℕ∞)) (hSz : dvSupp F z u ℓ = (Sz : ℕ∞)) (j i : ℕ) :
    ((Sg + Sz : ℕ) : ℕ∞) ≤ ℓ • (dvHgt F g j + dvHgt F z i) + ((u * (j + i) : ℕ) : ℕ∞) := by
  have hg' := dvSupp_le_term F g u hℓ j
  have hz' := dvSupp_le_term F z u hℓ i
  rw [hSg] at hg'
  rw [hSz] at hz'
  calc ((Sg + Sz : ℕ) : ℕ∞) = (Sg : ℕ∞) + (Sz : ℕ∞) := by push_cast; ring
    _ ≤ (ℓ • dvHgt F g j + (u * j : ℕ∞)) + (ℓ • dvHgt F z i + (u * i : ℕ∞)) :=
        add_le_add hg' hz'
    _ = ℓ • (dvHgt F g j + dvHgt F z i) + ((u * (j + i) : ℕ) : ℕ∞) := by
        rw [nsmul_add]
        push_cast
        ring

/-- A not-both-on-side pair prices STRICTLY above (source: C133mh3's private
`pair_line_lt`). -/
private theorem pair_line_lt {F : KeyFrame O π} {u ℓ : ℕ} (hℓ : 0 < ℓ)
    {g z : Polynomial O} {Sg Sz : ℕ}
    (hSg : dvSupp F g u ℓ = (Sg : ℕ∞)) (hSz : dvSupp F z u ℓ = (Sz : ℕ∞)) {j i : ℕ}
    (hbad : ¬ (DvOnSide F g u ℓ j ∧ DvOnSide F z u ℓ i)) :
    ((Sg + Sz + 1 : ℕ) : ℕ∞) ≤ ℓ • (dvHgt F g j + dvHgt F z i) + ((u * (j + i) : ℕ) : ℕ∞) := by
  rcases not_and_or.mp hbad with hoff | hoff
  · have hg' := succ_dvSupp_le_of_not_dvOnSide hℓ hSg hoff
    have hz' := dvSupp_le_term F z u hℓ i
    rw [hSz] at hz'
    calc ((Sg + Sz + 1 : ℕ) : ℕ∞) = ((Sg + 1 : ℕ) : ℕ∞) + (Sz : ℕ∞) := by push_cast; ring
      _ ≤ (ℓ • dvHgt F g j + (u * j : ℕ∞)) + (ℓ • dvHgt F z i + (u * i : ℕ∞)) :=
          add_le_add hg' hz'
      _ = ℓ • (dvHgt F g j + dvHgt F z i) + ((u * (j + i) : ℕ) : ℕ∞) := by
          rw [nsmul_add]
          push_cast
          ring
  · have hg' := dvSupp_le_term F g u hℓ j
    have hz' := succ_dvSupp_le_of_not_dvOnSide hℓ hSz hoff
    rw [hSg] at hg'
    calc ((Sg + Sz + 1 : ℕ) : ℕ∞) = (Sg : ℕ∞) + ((Sz + 1 : ℕ) : ℕ∞) := by push_cast; ring
      _ ≤ (ℓ • dvHgt F g j + (u * j : ℕ∞)) + (ℓ • dvHgt F z i + (u * i : ℕ∞)) :=
          add_le_add hg' hz'
      _ = ℓ • (dvHgt F g j + dvHgt F z i) + ((u * (j + i) : ℕ) : ℕ∞) := by
          rw [nsmul_add]
          push_cast
          ring

/-- Main-diagonal term floor (source: C133mh3's private `modKey_term_floor`). -/
private theorem modKey_term_floor (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) {g z : Polynomial O} {Sg Sz : ℕ}
    (hSg : dvSupp F g u ℓ = (Sg : ℕ∞)) (hSz : dvSupp F z u ℓ = (Sz : ℕ∞))
    {j i κ s : ℕ} (hs : j + i = s) (hκ : ℓ * κ + u * s = Sg + Sz) :
    (κ : ℕ∞) ≤ F.stageHeight ((dev F.key g j * dev F.key z i) %ₘ F.key) := by
  have hp := pair_line_le hℓ hSg hSz j i
  rw [hs, show Sg + Sz = ℓ * κ + u * s from hκ.symm] at hp
  have hx : ((κ : ℕ) : ℕ∞) ≤ dvHgt F g j + dvHgt F z i := le_of_weight_le hℓ hp
  refine le_trans hx (le_trans (le_of_eq ?_) (stageHeight_le_modByMonic hπ F hh _))
  exact (stageHeight_mul hπ F hh (dev F.key g j) (dev F.key z i)).symm

/-- Main-diagonal STRICT floor at a not-both-on-side pair (source: C133mh3's private
`modKey_term_succ_floor`). -/
private theorem modKey_term_succ_floor (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) {g z : Polynomial O} {Sg Sz : ℕ}
    (hSg : dvSupp F g u ℓ = (Sg : ℕ∞)) (hSz : dvSupp F z u ℓ = (Sz : ℕ∞))
    {j i κ s : ℕ} (hs : j + i = s) (hκ : ℓ * κ + u * s = Sg + Sz)
    (hbad : ¬ (DvOnSide F g u ℓ j ∧ DvOnSide F z u ℓ i)) :
    ((κ + 1 : ℕ) : ℕ∞) ≤ F.stageHeight ((dev F.key g j * dev F.key z i) %ₘ F.key) := by
  have hp := pair_line_lt hℓ hSg hSz hbad
  rw [hs, show Sg + Sz + 1 = ℓ * κ + u * s + 1 by omega] at hp
  have hx : ((κ + 1 : ℕ) : ℕ∞) ≤ dvHgt F g j + dvHgt F z i :=
    succ_le_of_weight_succ_le' hℓ hp
  refine le_trans hx (le_trans (le_of_eq ?_) (stageHeight_le_modByMonic hπ F hh _))
  exact (stageHeight_mul hπ F hh (dev F.key g j) (dev F.key z i)).symm

/-- Carry-diagonal STRICT floor (source: C133mh3's private `carry_term_floor`; the
strict floor `ℓ·V < u` pays here). -/
private theorem carry_term_floor (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) {V : ℕ} (hV : F.stageHeight F.key = (V : ℕ∞))
    (hadm' : ℓ * V < u) {g z : Polynomial O} {Sg Sz : ℕ}
    (hSg : dvSupp F g u ℓ = (Sg : ℕ∞)) (hSz : dvSupp F z u ℓ = (Sz : ℕ∞))
    {j i κ s : ℕ} (hs : j + i + 1 = s) (hκ : ℓ * κ + u * s = Sg + Sz) :
    ((κ + 1 : ℕ) : ℕ∞) ≤ F.stageHeight (dev F.key (dev F.key g j * dev F.key z i) 1) := by
  rcases eq_or_ne (dev F.key g j) 0 with h0 | h0
  · rw [h0, zero_mul, dev_of_zero F.key 1, F.stageHeight_zero]
    exact le_top
  rcases eq_or_ne (dev F.key z i) 0 with h0' | h0'
  · rw [h0', mul_zero, dev_of_zero F.key 1, F.stageHeight_zero]
    exact le_top
  have hshort : (dev F.key g j * dev F.key z i).natDegree < 2 * F.key.natDegree :=
    natDegree_dev_mul_lt F h0 h0'
  have hslot := lt_weight_dev_slot hπ F hh hℓ hV hadm' hshort (s := 1) Nat.one_pos
  have hp := pair_line_le hℓ hSg hSz j i
  rw [show ℓ • (dvHgt F g j + dvHgt F z i)
      = ℓ • F.stageHeight (dev F.key g j * dev F.key z i) from by
    rw [stageHeight_mul hπ F hh]; rfl] at hp
  have key : ((ℓ * κ + u * s + 1 : ℕ) : ℕ∞)
      ≤ ℓ • F.stageHeight (dev F.key (dev F.key g j * dev F.key z i) 1)
        + ((u * s : ℕ) : ℕ∞) := by
    calc ((ℓ * κ + u * s + 1 : ℕ) : ℕ∞)
        = ((Sg + Sz : ℕ) : ℕ∞) + 1 := by rw [hκ]; push_cast; ring
      _ ≤ (ℓ • F.stageHeight (dev F.key g j * dev F.key z i)
            + ((u * (j + i) : ℕ) : ℕ∞)) + 1 := add_le_add hp le_rfl
      _ = (ℓ • F.stageHeight (dev F.key g j * dev F.key z i) + 1)
            + ((u * (j + i) : ℕ) : ℕ∞) := add_right_comm _ _ _
      _ ≤ (ℓ • F.stageHeight (dev F.key (dev F.key g j * dev F.key z i) 1)
            + (u * 1 : ℕ∞)) + ((u * (j + i) : ℕ) : ℕ∞) := add_le_add hslot le_rfl
      _ = ℓ • F.stageHeight (dev F.key (dev F.key g j * dev F.key z i) 1)
            + ((u * s : ℕ) : ℕ∞) := by
          rw [← hs]
          push_cast
          ring
  exact succ_le_of_weight_succ_le' hℓ key

/-- The read-kill lemma (source: C133mh3's private `read_kill`). -/
private theorem read_kill (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h)
    (H₀ : ℕ) (hpin : F.Pin H₀) {u ℓ : ℕ} (hℓ : 0 < ℓ) {g z : Polynomial O} {Sg Sz : ℕ}
    (hSg : dvSupp F g u ℓ = (Sg : ℕ∞)) (hSz : dvSupp F z u ℓ = (Sz : ℕ∞))
    {j i κ s : ℕ} (hs : j + i = s) (hκ : ℓ * κ + u * s = Sg + Sz)
    (hbad : ¬ (DvOnSide F g u ℓ j ∧ DvOnSide F z u ℓ i)) :
    F.twistRead H₀ hpin κ ((dev F.key g j * dev F.key z i) %ₘ F.key) = 0 := by
  have hx := modKey_term_succ_floor hπ hh hℓ hSg hSz hs hκ hbad
  refine twistRead_eq_zero_of_lt F hπ H₀ hpin (lt_of_lt_of_le ?_ hx)
  exact_mod_cast Nat.lt_succ_self κ

/-- In-range coefficient of `dvResPoly` (source: C133mh3's private
`dvResPoly_coeff_of_le`). -/
private theorem dvResPoly_coeff_of_le {F : KeyFrame O π} (H₀ : ℕ) (hpin : F.Pin H₀)
    {f : Polynomial O} {u ℓ : ℕ} (hne₂ : (dvSideSet F f u ℓ).Nonempty) {M₀ : ℕ}
    (hp₂ : dvHgt F f (dvSideMin F f u ℓ hne₂) = (M₀ : ℕ∞)) {t : ℕ}
    (ht : t ≤ dvSideDeg F f u ℓ hne₂) :
    (dvResPoly F H₀ hpin f u ℓ hne₂ M₀ hp₂).coeff t
      = F.twistRead H₀ hpin (M₀ - t * u) (dev F.key f (dvSideMin F f u ℓ hne₂ + t * ℓ)) := by
  rw [dvResPoly, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow,
    if_pos (Nat.lt_succ_of_le ht)]

/-- Beyond-range coefficient of `dvResPoly` (source: C133mh3's private
`dvResPoly_coeff_of_gt`). -/
private theorem dvResPoly_coeff_of_gt {F : KeyFrame O π} (H₀ : ℕ) (hpin : F.Pin H₀)
    {f : Polynomial O} {u ℓ : ℕ} (hne₂ : (dvSideSet F f u ℓ).Nonempty) {M₀ : ℕ}
    (hp₂ : dvHgt F f (dvSideMin F f u ℓ hne₂) = (M₀ : ℕ∞)) {t : ℕ}
    (ht : dvSideDeg F f u ℓ hne₂ < t) :
    (dvResPoly F H₀ hpin f u ℓ hne₂ M₀ hp₂).coeff t = 0 := by
  rw [dvResPoly, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow, if_neg (by omega)]

/-- `dev` over finite sums (source: C133mh5's private `dev_finsetSum`). -/
private theorem dev_finsetSum {φ : Polynomial O} (hφ : φ.Monic) {ι : Type*} (s : Finset ι)
    (f : ι → Polynomial O) (j : ℕ) :
    dev φ (∑ i ∈ s, f i) j = ∑ i ∈ s, dev φ (f i) j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dev_of_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, dev_add_of_monic hφ, ih, Finset.sum_insert ha]

/-- Pin existence at a nonempty side (source: C133mh14's private `exists_pin`). -/
private theorem dvOnSide_of_mem' {F : KeyFrame O π} {u ℓ j : ℕ} {f : Polynomial O}
    (hj : j ∈ dvSideSet F f u ℓ) : DvOnSide F f u ℓ j := by
  classical
  exact (Finset.mem_filter.mp (show j ∈ (Finset.range (f.natDegree + 1)).filter
    (DvOnSide F f u ℓ) from hj)).2

private theorem exists_pin (F : KeyFrame O π) {f : Polynomial O} {u ℓ : ℕ}
    (hne : (dvSideSet F f u ℓ).Nonempty) :
    ∃ M : ℕ, dvHgt F f (dvSideMin F f u ℓ hne) = (M : ℕ∞) := by
  obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.1 (dvOnSide_of_mem' (Finset.min'_mem _ hne)).2
  exact ⟨M, hM.symm⟩

/-- Pin proof-irrelevance for `dvResPoly` (OPEN-MH9-UNIVERSAL-PIN; source: C133mh11's
private `dvResPoly_pin_congr` / C133mh14's private `dvResPoly_congr` at `x = y`). -/
private theorem dvResPoly_pin_congr (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} {x : Polynomial O}
    (hne hne' : (dvSideSet F x u ℓ).Nonempty) {M M' : ℕ}
    (hp : dvHgt F x (dvSideMin F x u ℓ hne) = (M : ℕ∞))
    (hp' : dvHgt F x (dvSideMin F x u ℓ hne') = (M' : ℕ∞)) :
    dvResPoly F H₀ hpin x u ℓ hne M hp = dvResPoly F H₀ hpin x u ℓ hne' M' hp' := by
  have hM : M = M' := by exact_mod_cast hp.symm.trans hp'
  subst hM
  rfl

/-! ### Part 0b — small new private glue (strict slot floor, difference floors) -/

/-- Strict slot floor: a support floor one grade above the `(m, j)` line prices the slot
strictly above `m` (the strict companion of C130rp2's `le_dvHgt_of_le_dvSupp`). -/
private theorem lt_dvHgt_of_succ_le_dvSupp {F : KeyFrame O π} {f : Polynomial O}
    {u ℓ β m j : ℕ} (hℓ : 0 < ℓ) (hβ : ((β + 1 : ℕ) : ℕ∞) ≤ dvSupp F f u ℓ)
    (hm : ℓ * m + u * j = β) :
    ((m : ℕ) : ℕ∞) < dvHgt F f j := by
  have hterm := dvSupp_le_term F f u hℓ j
  have h : ((β + 1 : ℕ) : ℕ∞) ≤ ℓ • dvHgt F f j + (u * j : ℕ∞) := le_trans hβ hterm
  rcases eq_or_ne (dvHgt F f j) ⊤ with hT | hT
  · rw [hT]; exact_mod_cast lt_top_iff_ne_top.mpr (ENat.coe_ne_top m)
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hT
  rw [← hc, weight_read] at h
  rw [← hc]
  have hnat : β + 1 ≤ ℓ * c + u * j := by exact_mod_cast h
  have hmc : m < c := Nat.lt_of_mul_lt_mul_left (by omega : ℓ * m < ℓ * c)
  exact_mod_cast hmc

/-- Difference floor: a common support floor passes to the difference
(via `C130s6.dvSupp_neg` and `C130s6.min_dvSupp_le_dvSupp_add`). -/
private theorem le_dvSupp_sub' (F : KeyFrame O π) {u ℓ : ℕ} (hℓ : 0 < ℓ)
    {x y : Polynomial O} {c : ℕ∞}
    (hx : c ≤ dvSupp F x u ℓ) (hy : c ≤ dvSupp F y u ℓ) :
    c ≤ dvSupp F (x - y) u ℓ := by
  have hy' : c ≤ dvSupp F (-y) u ℓ := by rwa [C130s6.dvSupp_neg]
  calc c ≤ min (dvSupp F x u ℓ) (dvSupp F (-y) u ℓ) := le_min hx hy'
    _ ≤ dvSupp F (x + -y) u ℓ := C130s6.min_dvSupp_le_dvSupp_add F hℓ x (-y)
    _ = dvSupp F (x - y) u ℓ := by rw [sub_eq_add_neg]

/-- On-line arithmetic: `ℓ(M − tu) + u(j₀ + tℓ) = ℓM + uj₀` when the subtraction is
genuine (the grade-line pricing identity used throughout MH9M). -/
private theorem line_arith {ℓ u M j₀ t : ℕ} (h : t * u ≤ M) :
    ℓ * (M - t * u) + u * (j₀ + t * ℓ) = ℓ * M + u * j₀ := by
  have h1 : ℓ * (M - t * u) = ℓ * M - ℓ * (t * u) := Nat.mul_sub ℓ M (t * u)
  have h2 : u * (j₀ + t * ℓ) = u * j₀ + ℓ * (t * u) := by ring
  have h3 : ℓ * (t * u) ≤ ℓ * M := Nat.mul_le_mul_left ℓ h
  omega

/-! ## Part 1 — node 1: the bounded grade-line polynomial (MH9M.1) -/

/-- ★ **MH.9 node 1 — `dvLinePoly`** (MH9M.1's displayed definition): the bounded
grade-`(ℓM + uj₀)` line polynomial — coefficient `t` is the height-`(M − tu)` ϖ-read of the
development digit at abscissa `j₀ + tℓ`, over the window `t < A`. -/
noncomputable def dvLinePoly (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    (u ℓ j₀ M A : ℕ) (f : Polynomial O) : Polynomial (F.stageField H₀ hpin) :=
  ∑ t ∈ Finset.range A,
    Polynomial.C (F.twistRead H₀ hpin (M - t * u) (dev F.key f (j₀ + t * ℓ)))
      * Polynomial.X ^ t

/-- ★ MH.9 node 1, the coefficient lemma. -/
theorem dvLinePoly_coeff (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    (u ℓ j₀ M A : ℕ) (f : Polynomial O) (t : ℕ) :
    (dvLinePoly F H₀ hpin u ℓ j₀ M A f).coeff t
      = if t < A then F.twistRead H₀ hpin (M - t * u) (dev F.key f (j₀ + t * ℓ)) else 0 := by
  rw [dvLinePoly, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow]

/-- MH.9 node 1, degree bound: the window caps the degree. -/
theorem natDegree_dvLinePoly_le (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    (u ℓ j₀ M A : ℕ) (f : Polynomial O) :
    (dvLinePoly F H₀ hpin u ℓ j₀ M A f).natDegree ≤ A - 1 := by
  rw [dvLinePoly]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun t ht => ?_
  have ht' : t < A := Finset.mem_range.mp ht
  exact le_trans (Polynomial.natDegree_C_mul_X_pow_le _ t) (by omega)

/-- MH.9 node 1, zero law: the line polynomial of `0` is `0`. -/
theorem dvLinePoly_zero (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ) (hpin : F.Pin H₀)
    (u ℓ j₀ M A : ℕ) :
    dvLinePoly F H₀ hpin u ℓ j₀ M A (0 : Polynomial O) = 0 := by
  rw [dvLinePoly]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [dev_of_zero F.key, C133mh5.twistRead_zero F hπ H₀ hpin, Polynomial.C_0, zero_mul]

/-! ## Part 2 — node 2: the window lift's line read -/

/-- ★ **MH.9 node 2 — `dvLinePoly_dvWindowLift`**: on any window strictly containing the
degree, the line polynomial of the Λ-window lift is `ψ` itself (packages
`C133mh5.twistRead_dvWindowLift` coefficientwise). -/
theorem dvLinePoly_dvWindowLift (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) {u ℓ j₀ M A : ℕ} (hℓ : 0 < ℓ)
    (ψ : Polynomial (F.stageField H₀ hpin))
    (hfull : F.e₁ * F.f₁ * F.h + u * ψ.natDegree < M)
    (hA : ψ.natDegree < A) :
    dvLinePoly F H₀ hpin u ℓ j₀ M A (C133mh5.dvWindowLift F H₀ hpin u ℓ j₀ M ψ) = ψ := by
  refine Polynomial.ext fun t => ?_
  rw [dvLinePoly_coeff]
  split_ifs with hlt
  · rw [show M - t * u = M - u * t by rw [Nat.mul_comm]]
    exact C133mh5.twistRead_dvWindowLift F hπ H₀ hpin hℓ ψ hfull t
  · exact (ψ.coeff_eq_zero_of_natDegree_lt (by omega)).symm

/-! ## Part 3 — node 3: ★ Law AMR, the above-line mixed read law (MH9M.2) -/

set_option maxHeartbeats 1600000 in
/-- ★ **MH.9 node 3 — Law AMR (`dvLinePoly_mul_of_isDvPure`)**, MH9M.2's exact statement:
for monic positive pure `p` with `D′ ∣ deg p`, left pin `(hnep, Mp, hpp)`,
`P := R(p)`, `b := deg P`, and `z` in the degree window `deg z < ℓ(A·D′)` with support
floor `ℓM + uj₀ ≤ W(z)` (`j₀ < ℓ`, `0 < A`, `u(A−1) ≤ M`):

`dvLinePoly (Mp+M) (A+b) (p·z) = P · dvLinePoly M A z`.

Proof route (MH9M.2): the `W(z) > d` branch by strict pricing on both sides; at
`W(z) = d`, `dev_mul_conv_split` at `J = j₀ + nℓ`, `K = Mp + M − nu`; the carry diagonal
dies by `carry_term_floor`; off-pair main terms by `read_kill`; surviving pairs
`(tℓ, j₀ + sℓ)`, `t + s = n`, read via `C133mh3.m1TwistProductLaw` (TW-δ cancels the
carry exactly — the η^δ of `C133mh1.twistExp_add_carry` is absorbed by the C.22 twist). -/
theorem dvLinePoly_mul_of_isDvPure (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h)
    (H₀ : ℕ) (hpin : F.Pin H₀) {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    {p : Polynomial O} (hpm : p.Monic) (hppos : 0 < p.natDegree)
    (hpd : F.e₁ * F.f₁ ∣ p.natDegree) (hppure : IsDvPure F p u ℓ)
    (hnep : (dvSideSet F p u ℓ).Nonempty) {Mp : ℕ}
    (hpp : dvHgt F p (dvSideMin F p u ℓ hnep) = (Mp : ℕ∞))
    {j₀ M A : ℕ} (hj₀ : j₀ < ℓ) (hA : 0 < A) (hM : u * (A - 1) ≤ M)
    {z : Polynomial O}
    (hzdeg : z.natDegree < ℓ * (A * (F.e₁ * F.f₁)))
    (hzsupp : ((ℓ * M + u * j₀ : ℕ) : ℕ∞) ≤ dvSupp F z u ℓ) :
    dvLinePoly F H₀ hpin u ℓ j₀ (Mp + M)
        (A + (dvResPoly F H₀ hpin p u ℓ hnep Mp hpp).natDegree) (p * z)
      = dvResPoly F H₀ hpin p u ℓ hnep Mp hpp
          * dvLinePoly F H₀ hpin u ℓ j₀ M A z := by
  classical
  obtain ⟨V, hV, hadm'⟩ := exists_key_height_lt F hfloor
  have hp0 : p ≠ 0 := hpm.ne_zero
  -- the pure endpoint pins for `p` (MH9M.2's opening paragraph)
  have hmin0 : dvSideMin F p u ℓ hnep = 0 := dvSideMin_eq_zero_of_isDvPure hppure hnep
  have hbdeg : (dvResPoly F H₀ hpin p u ℓ hnep Mp hpp).natDegree = dvSideDeg F p u ℓ hnep :=
    (natDegree_dvResPoly F hπ H₀ hpin hℓ hcop hnep hpp).1
  have hMp : Mp = u * dvSideDeg F p u ℓ hnep :=
    C133mh4.dvHgt_dvSideMin_eq_mul_dvSideDeg_of_isDvPure F hpm hppos hℓ hcop hppure hpd hnep hpp
  have hSp0 : dvSupp F p u ℓ = ((ℓ * Mp + u * dvSideMin F p u ℓ hnep : ℕ) : ℕ∞) :=
    dvSupp_eq_of_dvOnSide hpp (dvOnSide_dvSideMin F p u ℓ hnep)
  have hSp : dvSupp F p u ℓ = ((ℓ * Mp : ℕ) : ℕ∞) := by
    rw [hSp0, hmin0, Nat.mul_zero, Nat.add_zero]
  rw [hbdeg]
  -- the trivial `z = 0` branch
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [mul_zero, dvLinePoly_zero F hπ H₀ hpin, dvLinePoly_zero F hπ H₀ hpin, mul_zero]
  -- `z ≠ 0`: the support of `z` is finite
  obtain ⟨jw, hjwmem⟩ := dvSideSet_nonempty F hz0 u hℓ
  have hjwON := dvOnSide_of_mem_dvSideSet hjwmem
  obtain ⟨Hw, hHw⟩ := ENat.ne_top_iff_exists.1 hjwON.2
  have hSzeq : dvSupp F z u ℓ = ((ℓ * Hw + u * jw : ℕ) : ℕ∞) :=
    dvSupp_eq_of_dvOnSide hHw.symm hjwON
  have hd_le : ℓ * M + u * j₀ ≤ ℓ * Hw + u * jw := by
    rw [hSzeq] at hzsupp
    exact_mod_cast hzsupp
  rcases Nat.lt_or_ge (ℓ * M + u * j₀) (ℓ * Hw + u * jw) with hLt | hGe
  · -- STRICTLY-ABOVE branch (`W(z) > d`): both line polynomials vanish
    have hzline : dvLinePoly F H₀ hpin u ℓ j₀ M A z = 0 := by
      refine Polynomial.ext fun t => ?_
      rw [dvLinePoly_coeff, Polynomial.coeff_zero]
      split_ifs with hlt
      · have hut : t * u ≤ M := by
          have h1 : t * u ≤ (A - 1) * u := Nat.mul_le_mul_right u (by omega)
          have h2 : (A - 1) * u = u * (A - 1) := Nat.mul_comm _ _
          omega
        refine twistRead_eq_zero_of_lt F hπ H₀ hpin
          (lt_dvHgt_of_succ_le_dvSupp hℓ ?_ (line_arith hut))
        rw [hSzeq]
        exact_mod_cast (by omega : ℓ * M + u * j₀ + 1 ≤ ℓ * Hw + u * jw)
      · rfl
    have hWpz : dvSupp F (p * z) u ℓ = ((ℓ * Mp + (ℓ * Hw + u * jw) : ℕ) : ℕ∞) := by
      rw [C133mh3.dvSupp_mul hπ hh H₀ hpin hℓ hfloor hp0 hz0, hSp, hSzeq]
      push_cast
      ring
    rw [hzline, mul_zero]
    refine Polynomial.ext fun n => ?_
    rw [dvLinePoly_coeff, Polynomial.coeff_zero]
    split_ifs with hlt
    · have hun : n * u ≤ Mp + M := by
        have h1 : n * u ≤ (A + dvSideDeg F p u ℓ hnep - 1) * u :=
          Nat.mul_le_mul_right u (by omega)
        have h2 : (A + dvSideDeg F p u ℓ hnep - 1) * u
            = u * (A - 1) + u * dvSideDeg F p u ℓ hnep := by
          rw [show A + dvSideDeg F p u ℓ hnep - 1 = A - 1 + dvSideDeg F p u ℓ hnep by omega]
          ring
        omega
      refine twistRead_eq_zero_of_lt F hπ H₀ hpin
        (lt_dvHgt_of_succ_le_dvSupp hℓ ?_ (line_arith hun))
      rw [hWpz]
      have h3 : ℓ * (Mp + M) = ℓ * Mp + ℓ * M := Nat.mul_add ℓ Mp M
      exact_mod_cast (by omega : ℓ * (Mp + M) + u * j₀ + 1 ≤ ℓ * Mp + (ℓ * Hw + u * jw))
    · rfl
  · -- EQUALITY branch (`W(z) = d`): the mixed read law proper
    have hSz' : dvSupp F z u ℓ = ((ℓ * M + u * j₀ : ℕ) : ℕ∞) := by
      rw [hSzeq]
      congr 1
      omega
    -- z-side classification: on-side abscissae are `j₀ + sℓ`, `s < A`, height `M − su`
    have hzside : ∀ i : ℕ, DvOnSide F z u ℓ i → ∃ s : ℕ,
        i = j₀ + s * ℓ ∧ s < A ∧ s * u ≤ M ∧ dvHgt F z i = ((M - s * u : ℕ) : ℕ∞) := by
      intro i hON
      obtain ⟨Hi, hHi⟩ := ENat.ne_top_iff_exists.1 hON.2
      have hline : ℓ * Hi + u * i = ℓ * M + u * j₀ := by
        have h1 := hON.1
        rw [hSz', ← hHi, weight_read] at h1
        exact_mod_cast h1.symm
      have hmod : i % ℓ = j₀ % ℓ := by
        have h2 : (u * i) % ℓ = (u * j₀) % ℓ := by
          have h3 : (ℓ * Hi + u * i) % ℓ = (ℓ * M + u * j₀) % ℓ := by rw [hline]
          rwa [Nat.mul_add_mod, Nat.mul_add_mod] at h3
        exact Nat.ModEq.cancel_left_of_coprime hcop.symm h2
      have hj₀i : j₀ ≤ i := by
        rcases Nat.lt_or_ge i j₀ with hc | hc
        · have hi' : i % ℓ = i := Nat.mod_eq_of_lt (by omega)
          have hj' : j₀ % ℓ = j₀ := Nat.mod_eq_of_lt hj₀
          omega
        · exact hc
      obtain ⟨s, hs⟩ := (Nat.modEq_iff_dvd' hj₀i).mp (Nat.ModEq.symm hmod)
      have hieq : i = j₀ + s * ℓ := by
        have := Nat.mul_comm ℓ s
        omega
      have hheight : Hi + u * s = M := by
        have h4 : u * (j₀ + s * ℓ) = u * j₀ + ℓ * (u * s) := by ring
        rw [hieq, h4] at hline
        have h6 : ℓ * (Hi + u * s) = ℓ * M := by rw [Nat.mul_add]; omega
        exact Nat.eq_of_mul_eq_mul_left hℓ h6
      have hsA : s < A := by
        by_contra hge
        push Not at hge
        have hdev0 : dev F.key z i = 0 := by
          refine dev_eq_zero_of_lt F.hmonic F.natDegree_key_pos z i ?_
          rw [F.hdeg]
          have h5 : ℓ * (A * (F.e₁ * F.f₁)) ≤ s * ℓ * (F.e₁ * F.f₁) := by
            have h6 : A * ℓ ≤ s * ℓ := Nat.mul_le_mul_right ℓ hge
            calc ℓ * (A * (F.e₁ * F.f₁)) = A * ℓ * (F.e₁ * F.f₁) := by ring
              _ ≤ s * ℓ * (F.e₁ * F.f₁) := Nat.mul_le_mul_right _ h6
          have h7 : s * ℓ * (F.e₁ * F.f₁) ≤ i * (F.e₁ * F.f₁) :=
            Nat.mul_le_mul_right _ (by omega)
          omega
        exact hON.2 (by rw [dvHgt, hdev0]; exact F.stageHeight_zero)
      have hHival : Hi = M - s * u := by
        have := Nat.mul_comm u s
        omega
      refine ⟨s, hieq, hsA, by have := Nat.mul_comm u s; omega, ?_⟩
      rw [← hHi, hHival]
    -- p-side classification: on-side abscissae are `tℓ`, `t ≤ b`, height `Mp − tu`
    have hpside : ∀ r : ℕ, DvOnSide F p u ℓ r → ∃ t : ℕ,
        r = t * ℓ ∧ t ≤ dvSideDeg F p u ℓ hnep ∧
        dvHgt F p r = ((Mp - t * u : ℕ) : ℕ∞) := by
      intro r hON
      obtain ⟨Hr, hHr⟩ := ENat.ne_top_iff_exists.1 hON.2
      have hline : ℓ * Hr + u * r = ℓ * Mp := by
        have h1 := hON.1
        rw [hSp, ← hHr, weight_read] at h1
        exact_mod_cast h1.symm
      have hmodr : (0 : ℕ) ≡ r [MOD ℓ] := by
        have h1 := dvOnSide_modEq F hℓ hcop (dvOnSide_dvSideMin F p u ℓ hnep) hON
        rwa [hmin0] at h1
      obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' (Nat.zero_le r)).mp hmodr
      have hreq : r = t * ℓ := by
        have := Nat.mul_comm ℓ t
        omega
      have hrmax : r ≤ ℓ * dvSideDeg F p u ℓ hnep := by
        have h1 : r ≤ dvSideMax F p u ℓ hnep :=
          Finset.le_max' _ _ (mem_dvSideSet_of_dvOnSide hON)
        rwa [dvSideMax_eq_of_isDvPure hppure hnep,
          natDegree_div_eq_of_isDvPure hℓ hcop hppure hnep] at h1
      have htb : t ≤ dvSideDeg F p u ℓ hnep := by
        have h2 : t * ℓ ≤ dvSideDeg F p u ℓ hnep * ℓ := by
          have := Nat.mul_comm ℓ (dvSideDeg F p u ℓ hnep)
          omega
        exact Nat.le_of_mul_le_mul_right h2 hℓ
      have hheight : Hr + u * t = Mp := by
        have h4 : u * (t * ℓ) = ℓ * (u * t) := by ring
        rw [hreq] at hline
        rw [h4] at hline
        have h6 : ℓ * (Hr + u * t) = ℓ * Mp := by rw [Nat.mul_add]; omega
        exact Nat.eq_of_mul_eq_mul_left hℓ h6
      have hHrval : Hr = Mp - t * u := by
        have := Nat.mul_comm u t
        omega
      exact ⟨t, hreq, htb, by rw [← hHr, hHrval]⟩
    -- the coefficientwise identity
    refine Polynomial.ext fun n => ?_
    rw [dvLinePoly_coeff]
    by_cases hn : n < A + dvSideDeg F p u ℓ hnep
    case neg =>
      rw [if_neg hn]
      have hdegL : (dvLinePoly F H₀ hpin u ℓ j₀ M A z).natDegree ≤ A - 1 :=
        natDegree_dvLinePoly_le F H₀ hpin u ℓ j₀ M A z
      refine (Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt Polynomial.natDegree_mul_le ?_)).symm
      omega
    case pos =>
      rw [if_pos hn]
      have hun : n * u ≤ Mp + M := by
        have h1 : n * u ≤ (A + dvSideDeg F p u ℓ hnep - 1) * u :=
          Nat.mul_le_mul_right u (by omega)
        have h2 : (A + dvSideDeg F p u ℓ hnep - 1) * u
            = u * (A - 1) + u * dvSideDeg F p u ℓ hnep := by
          rw [show A + dvSideDeg F p u ℓ hnep - 1 = A - 1 + dvSideDeg F p u ℓ hnep by omega]
          ring
        omega
      have hκnat : ℓ * (Mp + M - n * u) + u * (j₀ + n * ℓ)
          = ℓ * Mp + (ℓ * M + u * j₀) := by
        have h1 := line_arith (ℓ := ℓ) (j₀ := j₀) hun
        have h2 : ℓ * (Mp + M) = ℓ * Mp + ℓ * M := Nat.mul_add ℓ Mp M
        omega
      rw [dev_mul_conv_split F p z (j₀ + n * ℓ)]
      have hmainfl : ∀ j ∈ Finset.range (j₀ + n * ℓ + 1),
          ((Mp + M - n * u : ℕ) : ℕ∞)
            ≤ F.stageHeight ((dev F.key p j * dev F.key z (j₀ + n * ℓ - j)) %ₘ F.key) := by
        intro j hj
        have hjle := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        exact modKey_term_floor hπ hh hℓ hSp hSz' (by omega) hκnat
      have hcarryfl : ∀ j ∈ Finset.range (j₀ + n * ℓ),
          ((Mp + M - n * u : ℕ) : ℕ∞)
            ≤ F.stageHeight (dev F.key (dev F.key p j
                * dev F.key z (j₀ + n * ℓ - 1 - j)) 1) := by
        intro j hj
        have hjlt := Finset.mem_range.mp hj
        exact le_trans (by exact_mod_cast Nat.le_succ (Mp + M - n * u))
          (carry_term_floor hπ hh hℓ hV hadm' hSp hSz' (by omega) hκnat)
      rw [twistRead_add_of_le F hπ H₀ hpin
        (le_stageHeight_finsetSum F _ _ hmainfl) (le_stageHeight_finsetSum F _ _ hcarryfl),
        twistRead_finsetSum_of_le F hπ H₀ hpin _ _ hmainfl,
        twistRead_finsetSum_of_le F hπ H₀ hpin _ _ hcarryfl]
      have hcarry0 : ∑ j ∈ Finset.range (j₀ + n * ℓ),
          F.twistRead H₀ hpin (Mp + M - n * u) (dev F.key (dev F.key p j
            * dev F.key z (j₀ + n * ℓ - 1 - j)) 1) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        have hjlt := Finset.mem_range.mp hj
        refine twistRead_eq_zero_of_lt F hπ H₀ hpin (lt_of_lt_of_le ?_
          (carry_term_floor hπ hh hℓ hV hadm' hSp hSz' (by omega) hκnat))
        exact_mod_cast Nat.lt_succ_self (Mp + M - n * u)
      rw [hcarry0, add_zero]
      -- reindex the surviving main diagonal to the `ℓ`-grid
      have himg : ((Finset.range (n + 1)).image fun t => t * ℓ)
          ⊆ Finset.range (j₀ + n * ℓ + 1) := by
        intro j hj
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hj
        have ht' : t ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
        have h1 : t * ℓ ≤ n * ℓ := Nat.mul_le_mul_right ℓ ht'
        exact Finset.mem_range.mpr (by omega)
      have hvanish : ∀ j ∈ Finset.range (j₀ + n * ℓ + 1),
          j ∉ ((Finset.range (n + 1)).image fun t => t * ℓ) →
          F.twistRead H₀ hpin (Mp + M - n * u)
            ((dev F.key p j * dev F.key z (j₀ + n * ℓ - j)) %ₘ F.key) = 0 := by
        intro j hj hnot
        have hjle := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        refine read_kill hπ hh H₀ hpin hℓ hSp hSz' (by omega) hκnat ?_
        rintro ⟨hb1, hb2⟩
        obtain ⟨t, hteq, htb, -⟩ := hpside j hb1
        refine hnot (Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr ?_, hteq.symm⟩)
        by_contra hgt
        push Not at hgt
        have h1 : (n + 1) * ℓ ≤ t * ℓ := Nat.mul_le_mul_right ℓ (by omega)
        have h2 : (n + 1) * ℓ = n * ℓ + ℓ := by ring
        omega
      rw [← Finset.sum_subset himg hvanish,
        Finset.sum_image (fun x _ y _ hxy => by
          have hx : x * ℓ = y * ℓ := hxy
          exact Nat.eq_of_mul_eq_mul_right hℓ hx)]
      rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      refine Finset.sum_congr rfl fun t ht => ?_
      have htn : t ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
      have htℓ : t * ℓ ≤ n * ℓ := Nat.mul_le_mul_right ℓ htn
      have hi : j₀ + n * ℓ - t * ℓ = j₀ + (n - t) * ℓ := by
        have h1 : (n - t) * ℓ = n * ℓ - t * ℓ := Nat.sub_mul n t ℓ
        omega
      by_cases hc1 : t ≤ dvSideDeg F p u ℓ hnep
      · by_cases hc2 : n - t < A
        · -- the surviving genre: the twist law fires (TW-δ cancels the carry)
          have hut1 : t * u ≤ Mp := by
            have h1 : t * u ≤ dvSideDeg F p u ℓ hnep * u := Nat.mul_le_mul_right u hc1
            have h2 : dvSideDeg F p u ℓ hnep * u = u * dvSideDeg F p u ℓ hnep :=
              Nat.mul_comm _ _
            omega
          have hut2 : (n - t) * u ≤ M := by
            have h1 : (n - t) * u ≤ (A - 1) * u := Nat.mul_le_mul_right u (by omega)
            have h2 : (A - 1) * u = u * (A - 1) := Nat.mul_comm _ _
            omega
          have hka : ((Mp - t * u : ℕ) : ℕ∞) ≤ dvHgt F p (t * ℓ) := by
            refine le_dvHgt_of_le_dvSupp hℓ (le_of_eq hSp.symm) ?_
            have h3 := line_arith (ℓ := ℓ) (u := u) (j₀ := 0) hut1
            have h4 : u * (0 + t * ℓ) = u * (t * ℓ) := by ring
            omega
          have hkb : ((M - (n - t) * u : ℕ) : ℕ∞) ≤ dvHgt F z (j₀ + (n - t) * ℓ) :=
            le_dvHgt_of_le_dvSupp hℓ (le_of_eq hSz'.symm) (line_arith hut2)
          have hsum' : (Mp - t * u) + (M - (n - t) * u) = Mp + M - n * u := by
            have h1 : t * u + (n - t) * u = n * u := by
              rw [← Nat.add_mul]
              congr 1
              omega
            omega
          rw [hi, ← hsum',
            C133mh3.m1TwistProductLaw π F hπ hh H₀ hpin _ _
              (natDegree_dev_lt_frame F p _) (natDegree_dev_lt_frame F z _)
              (Mp - t * u) (M - (n - t) * u) hka hkb]
          have hPc : (dvResPoly F H₀ hpin p u ℓ hnep Mp hpp).coeff t
              = F.twistRead H₀ hpin (Mp - t * u) (dev F.key p (t * ℓ)) := by
            rw [dvResPoly_coeff_of_le H₀ hpin hnep hpp hc1, hmin0, Nat.zero_add]
          have hLc : (dvLinePoly F H₀ hpin u ℓ j₀ M A z).coeff (n - t)
              = F.twistRead H₀ hpin (M - (n - t) * u) (dev F.key z (j₀ + (n - t) * ℓ)) := by
            rw [dvLinePoly_coeff, if_pos hc2]
          rw [hPc, hLc]
        · -- z-side overflow (`A ≤ n − t`): both sides vanish
          rw [dvLinePoly_coeff, if_neg hc2, mul_zero]
          refine read_kill hπ hh H₀ hpin hℓ hSp hSz' (by omega) hκnat ?_
          rintro ⟨hb1, hb2⟩
          rw [hi] at hb2
          obtain ⟨s, hseq, hsA, -, -⟩ := hzside _ hb2
          have h1 : (n - t) * ℓ = s * ℓ := by omega
          have h2 : n - t = s := Nat.eq_of_mul_eq_mul_right hℓ h1
          omega
      · -- p-side overflow (`b < t`): both sides vanish
        rw [dvResPoly_coeff_of_gt H₀ hpin hnep hpp (by omega), zero_mul]
        refine read_kill hπ hh H₀ hpin hℓ hSp hSz' (by omega) hκnat ?_
        rintro ⟨hb1, hb2⟩
        obtain ⟨t', ht'eq, ht'b, -⟩ := hpside _ hb1
        have h1 : t * ℓ = t' * ℓ := ht'eq
        have h2 : t = t' := Nat.eq_of_mul_eq_mul_right hℓ h1
        omega

/-! ## Part 4 — node 4: ★ Lemma S (MH9M.3), discharging the signed statement shape -/

set_option maxHeartbeats 1600000 in
/-- ★ **MH.9 node 4 — Lemma S HOLDS**: the signed statement shape
`C133mh5.LemmaSStatement` (C133mh5.lean:830, consumed byte-as-is) is discharged by the
MH9M.3 assembly: the pure endpoint formulas pin `(a, b, M₁, M₂, w₁, w₂)`; the unique
`j₀ < ℓ` representative of `c mod ℓ` gives the genuine decompositions
`c − w₂ = ℓMU + uj₀`, `c − w₁ = ℓMV + uj₀`, `c = ℓMc + uj₀`; the fullness chain
`ℓ(MU − u(a−1)) ≥ u(ℓ−j₀) ≥ u > ℓ(D′h)`; the stage-field Bézout solve on
`Ebar := dvLinePoly j₀ Mc (a+b) e`; the window lifts `U, V`; Law AMR at `(p₂, U)` and
`(p₁, V)`; and `C133mh5.le_dvSupp_succ_of_lineReads_eq_zero` for the `c + 1` contraction. -/
theorem lemmaS : C133mh5.LemmaSStatement O := by
  intro π F hπ hh H₀ hpin u ℓ hℓ hcop hfloor p₁ p₂ h1m h2m h1pos h2pos h1d h2d h1pure h2pure
    hne₁ hne₂ M₁ M₂ hpn₁ hpn₂ hGH w₁ w₂ hw₁ hw₂ e c hedeg hcw hce
  classical
  letI : Field (F.stageField H₀ hpin) := localFieldStageField F H₀ hpin
  have hu : 0 < u := lt_of_le_of_lt (Nat.zero_le _) hfloor
  set G := dvResPoly F H₀ hpin p₁ u ℓ hne₁ M₁ hpn₁ with hGdef
  set HR := dvResPoly F H₀ hpin p₂ u ℓ hne₂ M₂ hpn₂ with hHdef
  -- pure endpoint pins (MH9M.3's opening formulas)
  have hGdeg : G.natDegree = dvSideDeg F p₁ u ℓ hne₁ := by
    rw [hGdef]
    exact (natDegree_dvResPoly F hπ H₀ hpin hℓ hcop hne₁ hpn₁).1
  have hHdeg : HR.natDegree = dvSideDeg F p₂ u ℓ hne₂ := by
    rw [hHdef]
    exact (natDegree_dvResPoly F hπ H₀ hpin hℓ hcop hne₂ hpn₂).1
  have hM₁val : M₁ = u * G.natDegree := by
    rw [hGdeg]
    exact C133mh4.dvHgt_dvSideMin_eq_mul_dvSideDeg_of_isDvPure F h1m h1pos hℓ hcop h1pure
      h1d hne₁ hpn₁
  have hM₂val : M₂ = u * HR.natDegree := by
    rw [hHdeg]
    exact C133mh4.dvHgt_dvSideMin_eq_mul_dvSideDeg_of_isDvPure F h2m h2pos hℓ hcop h2pure
      h2d hne₂ hpn₂
  have hdeg₁G : p₁.natDegree = ℓ * G.natDegree * (F.e₁ * F.f₁) := by
    rw [hGdeg, ← natDegree_div_eq_of_isDvPure hℓ hcop h1pure hne₁]
    exact (Nat.div_mul_cancel h1d).symm
  have hdeg₂G : p₂.natDegree = ℓ * HR.natDegree * (F.e₁ * F.f₁) := by
    rw [hHdeg, ← natDegree_div_eq_of_isDvPure hℓ hcop h2pure hne₂]
    exact (Nat.div_mul_cancel h2d).symm
  have haG : 0 < G.natDegree := by
    rcases Nat.eq_zero_or_pos G.natDegree with h0 | hpos
    · rw [h0, Nat.mul_zero, Nat.zero_mul] at hdeg₁G
      omega
    · exact hpos
  have hbH : 0 < HR.natDegree := by
    rcases Nat.eq_zero_or_pos HR.natDegree with h0 | hpos
    · rw [h0, Nat.mul_zero, Nat.zero_mul] at hdeg₂G
      omega
    · exact hpos
  have hmin₁ : dvSideMin F p₁ u ℓ hne₁ = 0 := dvSideMin_eq_zero_of_isDvPure h1pure hne₁
  have hmin₂ : dvSideMin F p₂ u ℓ hne₂ = 0 := dvSideMin_eq_zero_of_isDvPure h2pure hne₂
  have hS₁ : dvSupp F p₁ u ℓ = ((ℓ * M₁ : ℕ) : ℕ∞) := by
    rw [dvSupp_eq_of_dvOnSide hpn₁ (dvOnSide_dvSideMin F p₁ u ℓ hne₁), hmin₁,
      Nat.mul_zero, Nat.add_zero]
  have hS₂ : dvSupp F p₂ u ℓ = ((ℓ * M₂ : ℕ) : ℕ∞) := by
    rw [dvSupp_eq_of_dvOnSide hpn₂ (dvOnSide_dvSideMin F p₂ u ℓ hne₂), hmin₂,
      Nat.mul_zero, Nat.add_zero]
  have hw₁ℓ : w₁ = ℓ * M₁ := by
    have h1 : ((w₁ : ℕ) : ℕ∞) = ((ℓ * M₁ : ℕ) : ℕ∞) := hw₁.symm.trans hS₁
    exact_mod_cast h1
  have hw₂ℓ : w₂ = ℓ * M₂ := by
    have h1 : ((w₂ : ℕ) : ℕ∞) = ((ℓ * M₂ : ℕ) : ℕ∞) := hw₂.symm.trans hS₂
    exact_mod_cast h1
  have hw₁uv : w₁ = ℓ * (u * G.natDegree) := by rw [hw₁ℓ, hM₁val]
  have hw₂uv : w₂ = ℓ * (u * HR.natDegree) := by rw [hw₂ℓ, hM₂val]
  -- the unique `j₀ < ℓ` representing `c` under multiplication by `u` (totient inverse)
  obtain ⟨j₀, hj₀, hj₀mod⟩ : ∃ j₀ : ℕ, j₀ < ℓ ∧ u * j₀ ≡ c [MOD ℓ] := by
    have hφ : 0 < Nat.totient ℓ := Nat.totient_pos.mpr hℓ
    refine ⟨(u ^ (Nat.totient ℓ - 1) * c) % ℓ, Nat.mod_lt _ hℓ, ?_⟩
    have h2 : u * u ^ (Nat.totient ℓ - 1) = u ^ Nat.totient ℓ := by
      conv_rhs => rw [show Nat.totient ℓ = Nat.totient ℓ - 1 + 1 by omega]
      rw [pow_succ]
      ring
    have h1 : u * ((u ^ (Nat.totient ℓ - 1) * c) % ℓ) ≡ u ^ Nat.totient ℓ * c [MOD ℓ] :=
      calc u * ((u ^ (Nat.totient ℓ - 1) * c) % ℓ)
          ≡ u * (u ^ (Nat.totient ℓ - 1) * c) [MOD ℓ] :=
            Nat.ModEq.mul_left u (Nat.mod_modEq _ ℓ)
        _ = u ^ Nat.totient ℓ * c := by rw [← mul_assoc, h2]
    have h3 : u ^ Nat.totient ℓ * c ≡ 1 * c [MOD ℓ] :=
      Nat.ModEq.mul_right c (Nat.ModEq.pow_totient hcop)
    have h4 := h1.trans h3
    rwa [one_mul] at h4
  -- the genuine decompositions `c = ℓ·Mc + u·j₀`, `c − w₂ = ℓ·MU + u·j₀`, `c − w₁ = ℓ·MV + u·j₀`
  have hjc : u * j₀ < w₁ := by
    have h7 : u * (j₀ + 1) ≤ u * ℓ := Nat.mul_le_mul_left u (by omega)
    have h8 : u * (j₀ + 1) = u * j₀ + u := by ring
    have h9 : u * ℓ = ℓ * u := Nat.mul_comm u ℓ
    have h10 : ℓ * u ≤ ℓ * (u * G.natDegree) :=
      Nat.mul_le_mul_left ℓ (Nat.le_mul_of_pos_right u haG)
    omega
  have hjc₂ : u * j₀ < w₂ := by
    have h7 : u * (j₀ + 1) ≤ u * ℓ := Nat.mul_le_mul_left u (by omega)
    have h8 : u * (j₀ + 1) = u * j₀ + u := by ring
    have h9 : u * ℓ = ℓ * u := Nat.mul_comm u ℓ
    have h10 : ℓ * u ≤ ℓ * (u * HR.natDegree) :=
      Nat.mul_le_mul_left ℓ (Nat.le_mul_of_pos_right u hbH)
    omega
  have hujc : u * j₀ ≤ c := by omega
  obtain ⟨Mc, hMcdvd⟩ := (Nat.modEq_iff_dvd' hujc).mp hj₀mod
  have hMceq : c = ℓ * Mc + u * j₀ := by omega
  have hM₂Mc : M₂ ≤ Mc := by
    have h1 : ℓ * M₂ ≤ ℓ * Mc := by omega
    exact Nat.le_of_mul_le_mul_left h1 hℓ
  have hM₁Mc : M₁ ≤ Mc := by
    have h1 : ℓ * M₁ ≤ ℓ * Mc := by omega
    exact Nat.le_of_mul_le_mul_left h1 hℓ
  have hMU : c - w₂ = ℓ * (Mc - M₂) + u * j₀ := by
    have h1 : ℓ * (Mc - M₂) = ℓ * Mc - ℓ * M₂ := Nat.mul_sub ℓ Mc M₂
    omega
  have hMV : c - w₁ = ℓ * (Mc - M₁) + u * j₀ := by
    have h1 : ℓ * (Mc - M₁) = ℓ * Mc - ℓ * M₁ := Nat.mul_sub ℓ Mc M₁
    omega
  -- the fullness chain `ℓ(MU − u(a−1)) ≥ u(ℓ−j₀) ≥ u > ℓ(D′h)` (MH9M.3)
  have hfull₁ : F.e₁ * F.f₁ * F.h + u * (G.natDegree - 1) < Mc - M₂ := by
    by_contra hcon
    push Not at hcon
    have e1 : ℓ * (Mc - M₂) ≤ ℓ * (F.e₁ * F.f₁ * F.h + u * (G.natDegree - 1)) :=
      Nat.mul_le_mul_left ℓ hcon
    have e2 : ℓ * (F.e₁ * F.f₁ * F.h + u * (G.natDegree - 1))
        = ℓ * ((F.e₁ * F.f₁) * F.h) + ℓ * (u * (G.natDegree - 1)) := Nat.mul_add ℓ _ _
    have e3 : ℓ * (u * G.natDegree) ≤ ℓ * (Mc - M₂) + u * j₀ := by omega
    have e4 : ℓ * (u * G.natDegree) = ℓ * (u * (G.natDegree - 1)) + ℓ * u := by
      have h5 : u * G.natDegree = u * (G.natDegree - 1) + u := by
        have h6 : G.natDegree = G.natDegree - 1 + 1 := by omega
        calc u * G.natDegree = u * (G.natDegree - 1 + 1) := by rw [← h6]
          _ = u * (G.natDegree - 1) + u := by ring
      rw [h5, Nat.mul_add]
    have e5 : u * j₀ + u ≤ ℓ * u := by
      have h7 : u * (j₀ + 1) ≤ u * ℓ := Nat.mul_le_mul_left u (by omega)
      have h8 : u * (j₀ + 1) = u * j₀ + u := by ring
      have h9 : u * ℓ = ℓ * u := Nat.mul_comm u ℓ
      omega
    omega
  have hfull₂ : F.e₁ * F.f₁ * F.h + u * (HR.natDegree - 1) < Mc - M₁ := by
    by_contra hcon
    push Not at hcon
    have e1 : ℓ * (Mc - M₁) ≤ ℓ * (F.e₁ * F.f₁ * F.h + u * (HR.natDegree - 1)) :=
      Nat.mul_le_mul_left ℓ hcon
    have e2 : ℓ * (F.e₁ * F.f₁ * F.h + u * (HR.natDegree - 1))
        = ℓ * ((F.e₁ * F.f₁) * F.h) + ℓ * (u * (HR.natDegree - 1)) := Nat.mul_add ℓ _ _
    have e3 : ℓ * (u * HR.natDegree) ≤ ℓ * (Mc - M₁) + u * j₀ := by omega
    have e4 : ℓ * (u * HR.natDegree) = ℓ * (u * (HR.natDegree - 1)) + ℓ * u := by
      have h5 : u * HR.natDegree = u * (HR.natDegree - 1) + u := by
        have h6 : HR.natDegree = HR.natDegree - 1 + 1 := by omega
        calc u * HR.natDegree = u * (HR.natDegree - 1 + 1) := by rw [← h6]
          _ = u * (HR.natDegree - 1) + u := by ring
      rw [h5, Nat.mul_add]
    have e5 : u * j₀ + u ≤ ℓ * u := by
      have h7 : u * (j₀ + 1) ≤ u * ℓ := Nat.mul_le_mul_left u (by omega)
      have h8 : u * (j₀ + 1) = u * j₀ + u := by ring
      have h9 : u * ℓ = ℓ * u := Nat.mul_comm u ℓ
      omega
    omega
  -- monic residuals (M-monic), the error line, and the Bézout solve
  have hGmon : G.Monic := by
    rw [hGdef]
    exact C133mh4.dvResPoly_monic_of_isDvPure F hπ hh H₀ hpin h1m h1pos hℓ hcop h1pure
      h1d hne₁ hpn₁
  have hHmon : HR.Monic := by
    rw [hHdef]
    exact C133mh4.dvResPoly_monic_of_isDvPure F hπ hh H₀ hpin h2m h2pos hℓ hcop h2pure
      h2d hne₂ hpn₂
  set Ebar := dvLinePoly F H₀ hpin u ℓ j₀ Mc (G.natDegree + HR.natDegree) e with hEbardef
  have hEdeg : Ebar.degree < G.degree + HR.degree := by
    have h1 : Ebar.natDegree ≤ G.natDegree + HR.natDegree - 1 := by
      rw [hEbardef]
      exact natDegree_dvLinePoly_le F H₀ hpin u ℓ j₀ Mc (G.natDegree + HR.natDegree) e
    have h2 : Ebar.natDegree < G.natDegree + HR.natDegree := by omega
    calc Ebar.degree ≤ (Ebar.natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
      _ < ((G.natDegree + HR.natDegree : ℕ) : WithBot ℕ) := by exact_mod_cast h2
      _ = G.degree + HR.degree := by
          rw [Polynomial.degree_eq_natDegree hGmon.ne_zero,
            Polynomial.degree_eq_natDegree hHmon.ne_zero]
          push_cast
          rfl
  obtain ⟨Ubar, Vbar, hUbardeg', hVbardeg', hbez⟩ :=
    C133mh5.exists_stageField_bezout_degree_lt F H₀ hpin hGmon hHmon hGH Ebar hEdeg
  have hUbardeg : Ubar.natDegree < G.natDegree := by
    rcases eq_or_ne Ubar 0 with h0 | h0
    · rw [h0, Polynomial.natDegree_zero]
      exact haG
    · exact Polynomial.natDegree_lt_natDegree h0 hUbardeg'
  have hVbardeg : Vbar.natDegree < HR.natDegree := by
    rcases eq_or_ne Vbar 0 with h0 | h0
    · rw [h0, Polynomial.natDegree_zero]
      exact hbH
    · exact Polynomial.natDegree_lt_natDegree h0 hVbardeg'
  have hfullU : F.e₁ * F.f₁ * F.h + u * Ubar.natDegree < Mc - M₂ := by
    have h1 : u * Ubar.natDegree ≤ u * (G.natDegree - 1) := Nat.mul_le_mul_left u (by omega)
    omega
  have hfullV : F.e₁ * F.f₁ * F.h + u * Vbar.natDegree < Mc - M₁ := by
    have h1 : u * Vbar.natDegree ≤ u * (HR.natDegree - 1) := Nat.mul_le_mul_left u (by omega)
    omega
  -- the window-lift correctors
  set Uw := C133mh5.dvWindowLift F H₀ hpin u ℓ j₀ (Mc - M₂) Ubar with hUwdef
  set Vw := C133mh5.dvWindowLift F H₀ hpin u ℓ j₀ (Mc - M₁) Vbar with hVwdef
  have hUwdeg : Uw.natDegree < ℓ * (G.natDegree * (F.e₁ * F.f₁)) := by
    rw [hUwdef]
    exact C133mh5.natDegree_dvWindowLift_lt' F H₀ hpin hj₀ Ubar hUbardeg
  have hVwdeg : Vw.natDegree < ℓ * (HR.natDegree * (F.e₁ * F.f₁)) := by
    rw [hVwdef]
    exact C133mh5.natDegree_dvWindowLift_lt' F H₀ hpin hj₀ Vbar hVbardeg
  have hUdeg : Uw.natDegree < p₁.natDegree := by
    rw [hdeg₁G]
    have h2 : ℓ * (G.natDegree * (F.e₁ * F.f₁)) = ℓ * G.natDegree * (F.e₁ * F.f₁) := by ring
    omega
  have hVdeg : Vw.natDegree < p₂.natDegree := by
    rw [hdeg₂G]
    have h2 : ℓ * (HR.natDegree * (F.e₁ * F.f₁)) = ℓ * HR.natDegree * (F.e₁ * F.f₁) := by ring
    omega
  have hUwsupp : ((ℓ * (Mc - M₂) + u * j₀ : ℕ) : ℕ∞) ≤ dvSupp F Uw u ℓ := by
    rw [hUwdef]
    exact C133mh5.le_dvSupp_dvWindowLift F hπ H₀ hpin hℓ Ubar hfullU
  have hVwsupp : ((ℓ * (Mc - M₁) + u * j₀ : ℕ) : ℕ∞) ≤ dvSupp F Vw u ℓ := by
    rw [hVwdef]
    exact C133mh5.le_dvSupp_dvWindowLift F hπ H₀ hpin hℓ Vbar hfullV
  have hUsupp : ((c - w₂ : ℕ) : ℕ∞) ≤ dvSupp F Uw u ℓ := by
    rw [show (c - w₂ : ℕ) = ℓ * (Mc - M₂) + u * j₀ from hMU]
    exact hUwsupp
  have hVsupp : ((c - w₁ : ℕ) : ℕ∞) ≤ dvSupp F Vw u ℓ := by
    rw [show (c - w₁ : ℕ) = ℓ * (Mc - M₁) + u * j₀ from hMV]
    exact hVwsupp
  -- the product support floors
  have hWU : ((c : ℕ) : ℕ∞) ≤ dvSupp F (p₂ * Uw) u ℓ := by
    rcases eq_or_ne Uw 0 with h0 | h0
    · rw [h0, mul_zero, C130s6.dvSupp_zero_eq_top F u hℓ]
      exact le_top
    · rw [C133mh3.dvSupp_mul hπ hh H₀ hpin hℓ hfloor h2m.ne_zero h0, hw₂]
      calc ((c : ℕ) : ℕ∞) = ((w₂ + (c - w₂) : ℕ) : ℕ∞) := by
            congr 1
            omega
        _ = ((w₂ : ℕ) : ℕ∞) + ((c - w₂ : ℕ) : ℕ∞) := by push_cast; ring
        _ ≤ ((w₂ : ℕ) : ℕ∞) + dvSupp F Uw u ℓ := add_le_add le_rfl hUsupp
  have hWV : ((c : ℕ) : ℕ∞) ≤ dvSupp F (p₁ * Vw) u ℓ := by
    rcases eq_or_ne Vw 0 with h0 | h0
    · rw [h0, mul_zero, C130s6.dvSupp_zero_eq_top F u hℓ]
      exact le_top
    · rw [C133mh3.dvSupp_mul hπ hh H₀ hpin hℓ hfloor h1m.ne_zero h0, hw₁]
      calc ((c : ℕ) : ℕ∞) = ((w₁ + (c - w₁) : ℕ) : ℕ∞) := by
            congr 1
            omega
        _ = ((w₁ : ℕ) : ℕ∞) + ((c - w₁ : ℕ) : ℕ∞) := by push_cast; ring
        _ ≤ ((w₁ : ℕ) : ℕ∞) + dvSupp F Vw u ℓ := add_le_add le_rfl hVsupp
  have hWx : ((c : ℕ) : ℕ∞) ≤ dvSupp F (e - (p₂ * Uw + p₁ * Vw)) u ℓ :=
    le_dvSupp_sub' F hℓ hce
      (le_trans (le_min hWU hWV) (C130s6.min_dvSupp_le_dvSupp_add F hℓ _ _))
  -- Law AMR at `(p₂, U)` and `(p₁, V)`, folded to the shared grade heights `Mc`
  have hAMR₂ : dvLinePoly F H₀ hpin u ℓ j₀ Mc (G.natDegree + HR.natDegree) (p₂ * Uw)
      = HR * dvLinePoly F H₀ hpin u ℓ j₀ (Mc - M₂) G.natDegree Uw := by
    have h1 := dvLinePoly_mul_of_isDvPure hπ hh H₀ hpin hℓ hcop hfloor h2m h2pos h2d h2pure
      hne₂ hpn₂ hj₀ haG (by omega : u * (G.natDegree - 1) ≤ Mc - M₂) hUwdeg hUwsupp
    rw [← hHdef] at h1
    rwa [show M₂ + (Mc - M₂) = Mc from by omega] at h1
  have hAMR₁ : dvLinePoly F H₀ hpin u ℓ j₀ Mc (HR.natDegree + G.natDegree) (p₁ * Vw)
      = G * dvLinePoly F H₀ hpin u ℓ j₀ (Mc - M₁) HR.natDegree Vw := by
    have h1 := dvLinePoly_mul_of_isDvPure hπ hh H₀ hpin hℓ hcop hfloor h1m h1pos h1d h1pure
      hne₁ hpn₁ hj₀ hbH (by omega : u * (HR.natDegree - 1) ≤ Mc - M₁) hVwdeg hVwsupp
    rw [← hGdef] at h1
    rwa [show M₁ + (Mc - M₁) = Mc from by omega] at h1
  have hLU : dvLinePoly F H₀ hpin u ℓ j₀ (Mc - M₂) G.natDegree Uw = Ubar := by
    rw [hUwdef]
    exact dvLinePoly_dvWindowLift F hπ H₀ hpin hℓ Ubar hfullU hUbardeg
  have hLV : dvLinePoly F H₀ hpin u ℓ j₀ (Mc - M₁) HR.natDegree Vw = Vbar := by
    rw [hVwdef]
    exact dvLinePoly_dvWindowLift F hπ H₀ hpin hℓ Vbar hfullV hVbardeg
  -- the `c + 1` contraction (grade-`c` reads cancel by the Bézout identity)
  have hcontr : ((c + 1 : ℕ) : ℕ∞) ≤ dvSupp F (e - (p₂ * Uw + p₁ * Vw)) u ℓ := by
    refine C133mh5.le_dvSupp_succ_of_lineReads_eq_zero F hπ hh H₀ hpin hℓ hWx ?_
    intro j k hline hheight
    -- classify the grade-`c` point: `j = j₀ + sℓ`, `k = Mc − su`
    have hlineMc : ℓ * k + u * j = ℓ * Mc + u * j₀ := by omega
    have hmod : j % ℓ = j₀ % ℓ := by
      have h2 : (u * j) % ℓ = (u * j₀) % ℓ := by
        have h3 : (ℓ * k + u * j) % ℓ = (ℓ * Mc + u * j₀) % ℓ := by rw [hlineMc]
        rwa [Nat.mul_add_mod, Nat.mul_add_mod] at h3
      exact Nat.ModEq.cancel_left_of_coprime hcop.symm h2
    have hj₀j : j₀ ≤ j := by
      rcases Nat.lt_or_ge j j₀ with hc' | hc'
      · have hj' : j % ℓ = j := Nat.mod_eq_of_lt (by omega)
        have hj'' : j₀ % ℓ = j₀ := Nat.mod_eq_of_lt hj₀
        omega
      · exact hc'
    obtain ⟨s, hs⟩ := (Nat.modEq_iff_dvd' hj₀j).mp (Nat.ModEq.symm hmod)
    have hjeq : j = j₀ + s * ℓ := by
      have := Nat.mul_comm ℓ s
      omega
    have hkMc : k + u * s = Mc := by
      have h4 : u * (j₀ + s * ℓ) = u * j₀ + ℓ * (u * s) := by ring
      rw [hjeq, h4] at hlineMc
      have h6 : ℓ * (k + u * s) = ℓ * Mc := by rw [Nat.mul_add]; omega
      exact Nat.eq_of_mul_eq_mul_left hℓ h6
    have hkeq : k = Mc - s * u := by
      have := Nat.mul_comm u s
      omega
    -- floors at `(j, k)` for the three summands and the difference
    have hkx : ((k : ℕ) : ℕ∞) ≤ dvHgt F (e - (p₂ * Uw + p₁ * Vw)) j :=
      le_of_eq hheight.symm
    have hke : ((k : ℕ) : ℕ∞) ≤ dvHgt F e j := le_dvHgt_of_le_dvSupp hℓ hce hline
    have hkU : ((k : ℕ) : ℕ∞) ≤ dvHgt F (p₂ * Uw) j := le_dvHgt_of_le_dvSupp hℓ hWU hline
    have hkV : ((k : ℕ) : ℕ∞) ≤ dvHgt F (p₁ * Vw) j := le_dvHgt_of_le_dvSupp hℓ hWV hline
    -- the read of `e` splits along `e = x + (p₂U + p₁V)`
    have hsplitdev : dev F.key e j
        = dev F.key (e - (p₂ * Uw + p₁ * Vw)) j
          + (dev F.key (p₂ * Uw) j + dev F.key (p₁ * Vw) j) := by
      have h1 : e = (e - (p₂ * Uw + p₁ * Vw)) + (p₂ * Uw + p₁ * Vw) := by ring
      conv_lhs => rw [h1]
      rw [dev_add_of_monic F.hmonic, dev_add_of_monic F.hmonic]
    have hreade : F.twistRead H₀ hpin k (dev F.key e j)
        = F.twistRead H₀ hpin k (dev F.key (e - (p₂ * Uw + p₁ * Vw)) j)
          + (F.twistRead H₀ hpin k (dev F.key (p₂ * Uw) j)
             + F.twistRead H₀ hpin k (dev F.key (p₁ * Vw) j)) := by
      rw [hsplitdev,
        twistRead_add_of_le F hπ H₀ hpin hkx
          (le_trans (le_min hkU hkV) (F.min_stageHeight_le_add _ _)),
        twistRead_add_of_le F hπ H₀ hpin hkU hkV]
    by_cases hsAB : s < G.natDegree + HR.natDegree
    · -- in-window: the three reads are the `s`-coefficients; Bézout cancels them
      have hEc : F.twistRead H₀ hpin k (dev F.key e j) = Ebar.coeff s := by
        rw [hEbardef, dvLinePoly_coeff, if_pos hsAB, hjeq, hkeq]
      have hUc : F.twistRead H₀ hpin k (dev F.key (p₂ * Uw) j) = (HR * Ubar).coeff s := by
        have h1 : (dvLinePoly F H₀ hpin u ℓ j₀ Mc (G.natDegree + HR.natDegree)
            (p₂ * Uw)).coeff s = (HR * Ubar).coeff s := by
          rw [hAMR₂, hLU]
        rw [dvLinePoly_coeff, if_pos hsAB] at h1
        rw [hjeq, hkeq]
        exact h1
      have hVc : F.twistRead H₀ hpin k (dev F.key (p₁ * Vw) j) = (G * Vbar).coeff s := by
        have h1 : (dvLinePoly F H₀ hpin u ℓ j₀ Mc (HR.natDegree + G.natDegree)
            (p₁ * Vw)).coeff s = (G * Vbar).coeff s := by
          rw [hAMR₁, hLV]
        rw [dvLinePoly_coeff, if_pos (by omega : s < HR.natDegree + G.natDegree)] at h1
        rw [hjeq, hkeq]
        exact h1
      have hbezc : (HR * Ubar).coeff s + (G * Vbar).coeff s = Ebar.coeff s := by
        rw [← Polynomial.coeff_add, hbez]
      rw [hEc, hUc, hVc, hbezc] at hreade
      have h9 : F.twistRead H₀ hpin k (dev F.key (e - (p₂ * Uw + p₁ * Vw)) j)
          + Ebar.coeff s = 0 + Ebar.coeff s := by
        rw [zero_add]
        exact hreade.symm
      exact add_right_cancel h9
    · -- out-window: all three reads vanish by the degree windows
      have hsℓD : (G.natDegree + HR.natDegree) * ℓ * (F.e₁ * F.f₁)
          ≤ s * ℓ * (F.e₁ * F.f₁) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right ℓ (by omega))
      have hsj : s * ℓ * (F.e₁ * F.f₁) ≤ j * (F.e₁ * F.f₁) :=
        Nat.mul_le_mul_right _ (by omega)
      have hre : F.twistRead H₀ hpin k (dev F.key e j) = 0 := by
        have hdev0 : dev F.key e j = 0 := by
          refine dev_eq_zero_of_lt F.hmonic F.natDegree_key_pos e j ?_
          rw [F.hdeg]
          have h1 : p₁.natDegree + p₂.natDegree
              = (G.natDegree + HR.natDegree) * ℓ * (F.e₁ * F.f₁) := by
            rw [hdeg₁G, hdeg₂G]
            ring
          omega
        rw [hdev0]
        exact C133mh5.twistRead_zero F hπ H₀ hpin k
      have hrU : F.twistRead H₀ hpin k (dev F.key (p₂ * Uw) j) = 0 := by
        have hdev0 : dev F.key (p₂ * Uw) j = 0 := by
          rcases eq_or_ne Uw 0 with h0 | h0
          · rw [h0, mul_zero, dev_of_zero]
          · refine dev_eq_zero_of_lt F.hmonic F.natDegree_key_pos _ j ?_
            rw [F.hdeg]
            have h1 : (p₂ * Uw).natDegree = p₂.natDegree + Uw.natDegree :=
              Polynomial.natDegree_mul h2m.ne_zero h0
            have h2 : p₂.natDegree + Uw.natDegree
                < (G.natDegree + HR.natDegree) * ℓ * (F.e₁ * F.f₁) := by
              have h3 : (G.natDegree + HR.natDegree) * ℓ * (F.e₁ * F.f₁)
                  = ℓ * HR.natDegree * (F.e₁ * F.f₁)
                    + ℓ * (G.natDegree * (F.e₁ * F.f₁)) := by ring
              rw [hdeg₂G] at *
              omega
            omega
        rw [hdev0]
        exact C133mh5.twistRead_zero F hπ H₀ hpin k
      have hrV : F.twistRead H₀ hpin k (dev F.key (p₁ * Vw) j) = 0 := by
        have hdev0 : dev F.key (p₁ * Vw) j = 0 := by
          rcases eq_or_ne Vw 0 with h0 | h0
          · rw [h0, mul_zero, dev_of_zero]
          · refine dev_eq_zero_of_lt F.hmonic F.natDegree_key_pos _ j ?_
            rw [F.hdeg]
            have h1 : (p₁ * Vw).natDegree = p₁.natDegree + Vw.natDegree :=
              Polynomial.natDegree_mul h1m.ne_zero h0
            have h2 : p₁.natDegree + Vw.natDegree
                < (G.natDegree + HR.natDegree) * ℓ * (F.e₁ * F.f₁) := by
              have h3 : (G.natDegree + HR.natDegree) * ℓ * (F.e₁ * F.f₁)
                  = ℓ * G.natDegree * (F.e₁ * F.f₁)
                    + ℓ * (HR.natDegree * (F.e₁ * F.f₁)) := by ring
              rw [hdeg₁G] at *
              omega
            omega
        rw [hdev0]
        exact C133mh5.twistRead_zero F hπ H₀ hpin k
      rw [hre, hrU, hrV] at hreade
      simpa using hreade.symm
  exact ⟨Uw, Vw, hUdeg, hVdeg, hUsupp, hVsupp, hcontr⟩

/-! ## Part 5 — node 5: equal line reads contract the difference -/

/-- ★ **MH.9 node 5 — `dvSupp_sub_succ_of_same_residual`**: two polynomials with support
floor `w` and EQUAL grade-`w` line reads have difference of support `≥ w + 1` (the
initialization helper; by `C133mh5.le_dvSupp_succ_of_lineReads_eq_zero`). -/
theorem dvSupp_sub_succ_of_same_residual (F : KeyFrame O π) (hπ : Irreducible π)
    (hh : 0 < F.h) (H₀ : ℕ) (hpin : F.Pin H₀) {u ℓ : ℕ} (hℓ : 0 < ℓ)
    {x y : Polynomial O} {w : ℕ}
    (hx : ((w : ℕ) : ℕ∞) ≤ dvSupp F x u ℓ) (hy : ((w : ℕ) : ℕ∞) ≤ dvSupp F y u ℓ)
    (hreads : ∀ j k : ℕ, ℓ * k + u * j = w →
      F.twistRead H₀ hpin k (dev F.key x j) = F.twistRead H₀ hpin k (dev F.key y j)) :
    ((w + 1 : ℕ) : ℕ∞) ≤ dvSupp F (x - y) u ℓ := by
  have hWxy : ((w : ℕ) : ℕ∞) ≤ dvSupp F (x - y) u ℓ := le_dvSupp_sub' F hℓ hx hy
  refine C133mh5.le_dvSupp_succ_of_lineReads_eq_zero F hπ hh H₀ hpin hℓ hWxy ?_
  intro j k hline hheight
  have hky : ((k : ℕ) : ℕ∞) ≤ dvHgt F y j := le_dvHgt_of_le_dvSupp hℓ hy hline
  have hkxy : ((k : ℕ) : ℕ∞) ≤ dvHgt F (x - y) j := le_of_eq hheight.symm
  have hsplitdev : dev F.key x j = dev F.key (x - y) j + dev F.key y j := by
    have h1 : x = (x - y) + y := by ring
    conv_lhs => rw [h1]
    rw [dev_add_of_monic F.hmonic]
  have hreadx : F.twistRead H₀ hpin k (dev F.key x j)
      = F.twistRead H₀ hpin k (dev F.key (x - y) j)
        + F.twistRead H₀ hpin k (dev F.key y j) := by
    rw [hsplitdev, twistRead_add_of_le F hπ H₀ hpin hkxy hky]
  rw [hreads j k hline] at hreadx
  have h9 : F.twistRead H₀ hpin k (dev F.key (x - y) j)
      + F.twistRead H₀ hpin k (dev F.key y j)
      = 0 + F.twistRead H₀ hpin k (dev F.key y j) := by
    rw [zero_add]
    exact hreadx.symm
  exact add_right_cancel h9

/-! ## Part 6 — node 6: the limit is monic (OPEN-MH9-LIMIT-MONIC) -/

/-- ★ **MH.9 node 6 — `monic_of_dvGradedLimit`**: a fixed-degree monic sequence with the
`exists_dvGradedLimit` tail bound has a monic limit of that exact degree — the
separatedness packaging: for every `N`, a late iterate puts
`gaussVal (P − p k) ≥ N` (`C133mh8.gaussVal_of_shifted_dvSupp`), so
`addVal (P.coeff d − 1) ≥ N` (`gaussVal_le_addVal_coeff`), hence `⊤`
(`addVal_eq_top_iff`), i.e. the top coefficient is `1`. -/
theorem monic_of_dvGradedLimit (hπ : Irreducible π) (F : KeyFrame O π) {u ℓ : ℕ}
    (hℓ : 0 < ℓ) {d : ℕ} {p : ℕ → Polynomial O} {P : Polynomial O}
    (hmon : ∀ k, (p k).Monic) (hdeg : ∀ k, (p k).natDegree = d)
    (hPdeg : P.natDegree < d + 1)
    (htail : ∀ k : ℕ, ((k : ℕ) : ℕ∞) ≤ dvSupp F (P - p k) u ℓ) :
    P.Monic ∧ P.natDegree = d := by
  -- separatedness at the top coefficient
  have hcoeff : ∀ N : ℕ, ((N : ℕ) : ℕ∞) ≤ addVal O (P.coeff d - 1) := by
    intro N
    have hdeg' : (P - p (ℓ * F.e₁ * N + ℓ * F.h * (F.e₁ * F.f₁ - 1)
        + u * (d + 1 - 1))).natDegree < d + 1 :=
      lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
        (max_lt (by omega) (by rw [hdeg]; omega))
    have hg : ((N : ℕ) : ℕ∞) ≤ gaussVal (P - p (ℓ * F.e₁ * N
        + ℓ * F.h * (F.e₁ * F.f₁ - 1) + u * (d + 1 - 1))) :=
      C133mh8.gaussVal_of_shifted_dvSupp hπ F hℓ hdeg' (htail _)
    have h2 : (p (ℓ * F.e₁ * N + ℓ * F.h * (F.e₁ * F.f₁ - 1)
        + u * (d + 1 - 1))).coeff d = 1 := by
      have h3 := (hmon (ℓ * F.e₁ * N + ℓ * F.h * (F.e₁ * F.f₁ - 1)
        + u * (d + 1 - 1))).coeff_natDegree
      rwa [hdeg (ℓ * F.e₁ * N + ℓ * F.h * (F.e₁ * F.f₁ - 1) + u * (d + 1 - 1))] at h3
    calc ((N : ℕ) : ℕ∞)
        ≤ gaussVal (P - p (ℓ * F.e₁ * N + ℓ * F.h * (F.e₁ * F.f₁ - 1)
            + u * (d + 1 - 1))) := hg
      _ ≤ addVal O ((P - p (ℓ * F.e₁ * N + ℓ * F.h * (F.e₁ * F.f₁ - 1)
            + u * (d + 1 - 1))).coeff d) := gaussVal_le_addVal_coeff _ d
      _ = addVal O (P.coeff d - 1) := by rw [Polynomial.coeff_sub, h2]
  have htop : P.coeff d = 1 := by
    have h0 : P.coeff d - 1 = 0 := by
      by_contra hne
      have hne' : addVal O (P.coeff d - 1) ≠ ⊤ := fun hT =>
        hne (IsDiscreteValuationRing.addVal_eq_top_iff.mp hT)
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hne'
      have h1 := hcoeff (n + 1)
      rw [← hn] at h1
      exact absurd (by exact_mod_cast h1 : n + 1 ≤ n) (by omega)
    exact sub_eq_zero.mp h0
  have hdegP : P.natDegree = d := by
    have h1 : d ≤ P.natDegree :=
      Polynomial.le_natDegree_of_ne_zero (by rw [htop]; exact one_ne_zero)
    omega
  refine ⟨?_, hdegP⟩
  show P.coeff P.natDegree = 1
  rw [hdegP, htop]

/-! ## Part 7 — node 7: unbounded support forces zero -/

/-- ★ **MH.9 node 7 — `eq_zero_of_forall_dvSupp`**: a degree-bounded polynomial whose
support clears every natural floor is `0` (`gaussVal_of_shifted_dvSupp` +
`gaussVal_eq_top_iff`). -/
theorem eq_zero_of_forall_dvSupp (hπ : Irreducible π) (F : KeyFrame O π) {u ℓ : ℕ}
    (hℓ : 0 < ℓ) {d : ℕ} {x : Polynomial O} (hdeg : x.natDegree < d)
    (hW : ∀ N : ℕ, ((N : ℕ) : ℕ∞) ≤ dvSupp F x u ℓ) : x = 0 := by
  rw [← gaussVal_eq_top_iff (a := x)]
  by_contra hne
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hne
  have hg : ((n + 1 : ℕ) : ℕ∞) ≤ gaussVal x :=
    C133mh8.gaussVal_of_shifted_dvSupp hπ F hℓ hdeg (hW _)
  rw [← hn] at hg
  exact absurd (by exact_mod_cast hg : n + 1 ≤ n) (by omega)

/-! ## Part 8 — node 8: the unit branch (OPEN-MH9-UNIT-BRANCH) -/

/-- The unit is its own key remainder (degree `0 <` the key's). -/
private theorem one_modByMonic_key (F : KeyFrame O π) : (1 : Polynomial O) %ₘ F.key = 1 := by
  refine (Polynomial.modByMonic_eq_self_iff F.hmonic).mpr ?_
  rw [Polynomial.degree_one, Polynomial.degree_eq_natDegree F.hmonic.ne_zero]
  exact_mod_cast F.natDegree_key_pos

/-- ★ MH.9 node 8a — the unit's level height at abscissa `0` is `0`. -/
theorem dvHgt_one_zero (F : KeyFrame O π) : dvHgt F (1 : Polynomial O) 0 = 0 := by
  rw [dvHgt, dev_zero_pin, one_modByMonic_key F]
  exact C131ae.stageHeight_one F

/-- MH.9 node 8 helper — the unit's cleared support is `0`. -/
theorem dvSupp_one (F : KeyFrame O π) (u ℓ : ℕ) : dvSupp F (1 : Polynomial O) u ℓ = 0 := by
  rw [dvSupp, Polynomial.natDegree_one, Finset.range_one, Finset.inf_singleton,
    dvHgt_one_zero F, smul_zero]
  simp

/-- ★ MH.9 node 8b — the unit is pure at every direction. -/
theorem isDvPure_one (F : KeyFrame O π) (u ℓ : ℕ) : IsDvPure F (1 : Polynomial O) u ℓ := by
  have hON : DvOnSide F (1 : Polynomial O) u ℓ 0 := by
    constructor
    · rw [dvSupp_one F u ℓ, dvHgt_one_zero F, smul_zero]
      simp
    · rw [dvHgt_one_zero F]
      simp
  have hmem : (0 : ℕ) ∈ dvSideSet F (1 : Polynomial O) u ℓ := mem_dvSideSet_of_dvOnSide hON
  constructor
  · exact hmem
  · rw [Polynomial.natDegree_one, Nat.zero_div]
    exact hmem

/-- ★ MH.9 node 8c — the unit's level residual is `1`, at every side witness and pin
(`C133mh0.twistRead_one` through the singleton side `{0}`). -/
theorem dvResPoly_one (F : KeyFrame O π) (hh : 0 < F.h) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} (hne : (dvSideSet F (1 : Polynomial O) u ℓ).Nonempty) (M : ℕ)
    (hp : dvHgt F (1 : Polynomial O) (dvSideMin F (1 : Polynomial O) u ℓ hne) = (M : ℕ∞)) :
    dvResPoly F H₀ hpin (1 : Polynomial O) u ℓ hne M hp = 1 := by
  classical
  have hrange : ∀ j : ℕ, j ∈ dvSideSet F (1 : Polynomial O) u ℓ → j = 0 := by
    intro j hj
    have h2 := (Finset.mem_filter.mp (show j
      ∈ (Finset.range ((1 : Polynomial O).natDegree + 1)).filter
        (DvOnSide F (1 : Polynomial O) u ℓ) from hj)).1
    rw [Polynomial.natDegree_one] at h2
    have h3 := Finset.mem_range.mp h2
    omega
  have hmin : dvSideMin F (1 : Polynomial O) u ℓ hne = 0 :=
    hrange _ (Finset.min'_mem _ hne)
  have hmax : dvSideMax F (1 : Polynomial O) u ℓ hne = 0 :=
    hrange _ (Finset.max'_mem _ hne)
  have hdeg0 : dvSideDeg F (1 : Polynomial O) u ℓ hne = 0 := by
    rw [dvSideDeg, hmin, hmax]
    simp
  have hM0 : M = 0 := by
    have h1 : dvHgt F (1 : Polynomial O) (dvSideMin F (1 : Polynomial O) u ℓ hne)
        = (0 : ℕ∞) := by
      rw [hmin]
      exact dvHgt_one_zero F
    rw [hp] at h1
    exact_mod_cast h1
  refine Polynomial.ext fun t => ?_
  rw [dvResPoly, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow, hdeg0]
  by_cases ht : t = 0
  · subst ht
    rw [if_pos (by omega), hmin, hM0]
    simp only [Nat.zero_mul, Nat.sub_zero, Nat.add_zero]
    rw [dev_zero_pin, one_modByMonic_key F, C133mh0.twistRead_one F H₀ hpin hh,
      Polynomial.coeff_one_zero]
  · rw [if_neg (by omega), Polynomial.coeff_one, if_neg ht]

/-! ### Part 8b — private helpers for the Theorem A assembly -/

/-- M4 transported across `x + y = z` (`subst` packaging of `C133mh0.dv_pure_add_of_lt`,
with the side witness explicit). -/
private theorem dv_pure_add_of_lt' (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    {x y z : Polynomial O} (hz : x + y = z) (hx : x.Monic) (hxpure : IsDvPure F x u ℓ)
    (hxne : (dvSideSet F x u ℓ).Nonempty) {Mx m : ℕ}
    (hMx : dvHgt F x (dvSideMin F x u ℓ hxne) = (Mx : ℕ∞))
    (hxsupp : dvSupp F x u ℓ = (m : ℕ∞))
    (hydeg : y.degree < x.degree)
    (hy : ((m + 1 : ℕ) : ℕ∞) ≤ dvSupp F y u ℓ) :
    z.Monic ∧ z.natDegree = x.natDegree ∧ IsDvPure F z u ℓ ∧
      ∃ hne' : (dvSideSet F z u ℓ).Nonempty,
      ∃ hpinM' : dvHgt F z (dvSideMin F z u ℓ hne') = (Mx : ℕ∞),
        dvResPoly F H₀ hpin z u ℓ hne' Mx hpinM'
          = dvResPoly F H₀ hpin x u ℓ hxne Mx hMx := by
  subst hz
  exact C133mh0.dv_pure_add_of_lt F hπ H₀ hpin hℓ hcop hx hxpure (hxne := hxne)
    hMx hxsupp hydeg hy

/-- A pure polynomial's pinned support, read off the abscissa-`0` height. -/
private theorem dvSupp_of_pure_hgt0 (F : KeyFrame O π) {x : Polynomial O} {u ℓ m : ℕ}
    (hpure : IsDvPure F x u ℓ) (h0 : dvHgt F x 0 = ((m : ℕ) : ℕ∞)) :
    dvSupp F x u ℓ = ((ℓ * m : ℕ) : ℕ∞) := by
  have hne' : (dvSideSet F x u ℓ).Nonempty := ⟨0, hpure.1⟩
  have hmin : dvSideMin F x u ℓ hne' = 0 := dvSideMin_eq_zero_of_isDvPure hpure hne'
  have hp' : dvHgt F x (dvSideMin F x u ℓ hne') = ((m : ℕ) : ℕ∞) := by
    rw [hmin]
    exact h0
  have h1 := dvSupp_eq_of_dvOnSide hp' (dvOnSide_dvSideMin F x u ℓ hne')
  rwa [hmin, Nat.mul_zero, Nat.add_zero] at h1

/-- A pure polynomial's pin at any side witness, read off the abscissa-`0` height. -/
private theorem pin_of_pure_hgt0 (F : KeyFrame O π) {x : Polynomial O} {u ℓ m : ℕ}
    (hpure : IsDvPure F x u ℓ) (h0 : dvHgt F x 0 = ((m : ℕ) : ℕ∞))
    (hne' : (dvSideSet F x u ℓ).Nonempty) :
    dvHgt F x (dvSideMin F x u ℓ hne') = ((m : ℕ) : ℕ∞) := by
  rw [dvSideMin_eq_zero_of_isDvPure hpure hne']
  exact h0

/-- The side degree of a pure polynomial, read off its exact degree formula. -/
private theorem dvSideDeg_of_pure_deg (F : KeyFrame O π) {f : Polynomial O} {u ℓ n : ℕ}
    (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) (hpure : IsDvPure F f u ℓ)
    (hne : (dvSideSet F f u ℓ).Nonempty)
    (hdeg : f.natDegree = ℓ * n * (F.e₁ * F.f₁)) : dvSideDeg F f u ℓ hne = n := by
  have h1 := natDegree_div_eq_of_isDvPure hℓ hcop hpure hne
  have hD : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  have h2 : f.natDegree / (F.e₁ * F.f₁) = ℓ * n := by
    rw [hdeg]
    exact Nat.mul_div_cancel _ hD
  rw [h2] at h1
  exact (Nat.eq_of_mul_eq_mul_left hℓ h1).symm

/-- On the base line of a pure polynomial, an on-grid read is the residual coefficient
(junk-total: no height-attainment hypothesis is needed). -/
private theorem lineRead_eq_dvResPoly_coeff (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) {f : Polynomial O} (hfpure : IsDvPure F f u ℓ)
    (hne : (dvSideSet F f u ℓ).Nonempty) {M₀ : ℕ}
    (hp : dvHgt F f (dvSideMin F f u ℓ hne) = (M₀ : ℕ∞))
    {j k t : ℕ} (hj : j = t * ℓ) (hk : ℓ * k + u * j = ℓ * M₀)
    (ht : t ≤ dvSideDeg F f u ℓ hne) :
    F.twistRead H₀ hpin k (dev F.key f j)
      = (dvResPoly F H₀ hpin f u ℓ hne M₀ hp).coeff t := by
  have hmin : dvSideMin F f u ℓ hne = 0 := dvSideMin_eq_zero_of_isDvPure hfpure hne
  have hcoeff := dvResPoly_coeff_of_le H₀ hpin hne hp ht
  rw [hmin, Nat.zero_add] at hcoeff
  have hkval : k = M₀ - t * u := by
    have h4 : u * (t * ℓ) = ℓ * (u * t) := by ring
    rw [hj, h4] at hk
    have h6 : ℓ * (k + u * t) = ℓ * M₀ := by rw [Nat.mul_add]; omega
    have h7 := Nat.eq_of_mul_eq_mul_left hℓ h6
    have := Nat.mul_comm u t
    omega
  rw [hj, hkval, hcoeff]

/-- On the base line of a pure polynomial, an off-grid read vanishes (the slot prices
strictly above the line). -/
private theorem lineRead_eq_zero_offgrid (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    {f : Polynomial O} (hfpure : IsDvPure F f u ℓ) {w : ℕ}
    (hW : dvSupp F f u ℓ = ((w : ℕ) : ℕ∞))
    {j k : ℕ} (hline : ℓ * k + u * j = w) (hoff : ¬ ℓ ∣ j) :
    F.twistRead H₀ hpin k (dev F.key f j) = 0 := by
  have hne' : (dvSideSet F f u ℓ).Nonempty := ⟨0, hfpure.1⟩
  have hnot : ¬ DvOnSide F f u ℓ j := by
    intro hON
    have hmin : dvSideMin F f u ℓ hne' = 0 := dvSideMin_eq_zero_of_isDvPure hfpure hne'
    have h1 := dvOnSide_modEq F hℓ hcop (dvOnSide_dvSideMin F f u ℓ hne') hON
    rw [hmin] at h1
    obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' (Nat.zero_le j)).mp h1
    exact hoff ⟨t, by omega⟩
  have hstrict := succ_dvSupp_le_of_not_dvOnSide hℓ hW hnot
  rw [show (w + 1 : ℕ) = ℓ * k + u * j + 1 by omega] at hstrict
  have h2 : ((k + 1 : ℕ) : ℕ∞) ≤ dvHgt F f j := succ_le_of_weight_succ_le' hℓ hstrict
  refine twistRead_eq_zero_of_lt F hπ H₀ hpin (lt_of_lt_of_le ?_ h2)
  exact_mod_cast Nat.lt_succ_self k

/-- The Theorem A iteration invariant (MH9M.4's pack): monicity, the two fixed degrees,
purity, the two abscissa-`0` height pins, the two exact ∀-pin residuals, and the
grade-`(w + k + 1)` error floor. -/
@[reducible] private def TAInv (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀) (u ℓ : ℕ)
    (g : Polynomial O) (G H : Polynomial (F.stageField H₀ hpin)) (k : ℕ)
    (a b : Polynomial O) : Prop :=
  a.Monic ∧ b.Monic ∧
  a.natDegree = ℓ * G.natDegree * (F.e₁ * F.f₁) ∧
  b.natDegree = ℓ * H.natDegree * (F.e₁ * F.f₁) ∧
  IsDvPure F a u ℓ ∧ IsDvPure F b u ℓ ∧
  dvHgt F a 0 = ((u * G.natDegree : ℕ) : ℕ∞) ∧
  dvHgt F b 0 = ((u * H.natDegree : ℕ) : ℕ∞) ∧
  (∀ (hne₁ : (dvSideSet F a u ℓ).Nonempty) (M₁ : ℕ)
    (hp₁ : dvHgt F a (dvSideMin F a u ℓ hne₁) = (M₁ : ℕ∞)),
    dvResPoly F H₀ hpin a u ℓ hne₁ M₁ hp₁ = G) ∧
  (∀ (hne₂ : (dvSideSet F b u ℓ).Nonempty) (M₂ : ℕ)
    (hp₂ : dvHgt F b (dvSideMin F b u ℓ hne₂) = (M₂ : ℕ∞)),
    dvResPoly F H₀ hpin b u ℓ hne₂ M₂ hp₂ = H) ∧
  ((ℓ * (u * G.natDegree) + ℓ * (u * H.natDegree) + k + 1 : ℕ) : ℕ∞)
    ≤ dvSupp F (g - a * b) u ℓ

/-! ## Part 9 — node 9: ★★ THEOREM A (MH9M.4), the engine's final node -/

set_option maxHeartbeats 1600000 in
/-- ★★ **MH.9 node 9 — THEOREM A HOLDS**: the signed statement shape
`C133mh14.TheoremAStatement` (C133mh14.lean:264, consumed byte-as-is) is discharged by
the MH9M.4 seven-step assembly:

1. positive-degree branches initialize with `C133mh5.dvSideLift` (its clause lemmas give
   monicity, degrees, purity, weights/heights, exact residuals);
2. equal support-line reads + node 5 give initial error weight `w + 1`;
3. Lemma S (node 4) at `c = w + k + 1` followed by `C133mh0.dv_pure_add_of_lt` iterates,
   with the quadratic corrector priced at `2c − w ≥ c + 1`;
4. `C133mh8.exists_dvGradedLimit` on the two fixed degree windows; node 6 makes the
   limits monic of the exact degrees;
5. a late iterate + `C133mh0.dv_pure_add_of_lt` transfers purity/height/residual to the
   limits (∀-pin form via `dvResPoly_pin_congr`);
6. node 7 forces `g = g₁∞ · g₂∞` exactly;
7. constant-factor branches via node 8 (`(1, g)` / `(g, 1)`).

No cite is consumed: the footprint is Lean-core (AxCheck footer). -/
theorem theoremA [IsAdicComplete (IsLocalRing.maximalIdeal O) O] :
    C133mh14.TheoremAStatement O := by
  intro π F hπ hh H₀ hpin u ℓ hℓ hcop hfloor g hgmon hgpos hgd hgpure hne M₀ hp
    G H hGmon hHmon hGH hG0 hH0 hres
  classical
  letI : Field (F.stageField H₀ hpin) := localFieldStageField F H₀ hpin
  have hu : 0 < u := lt_of_le_of_lt (Nat.zero_le _) hfloor
  have hDpos : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  have hming : dvSideMin F g u ℓ hne = 0 := dvSideMin_eq_zero_of_isDvPure hgpure hne
  have hgdegℓ : g.natDegree = ℓ * dvSideDeg F g u ℓ hne * (F.e₁ * F.f₁) := by
    rw [← natDegree_div_eq_of_isDvPure hℓ hcop hgpure hne]
    exact (Nat.div_mul_cancel hgd).symm
  -- OPEN-MH9-UNIT-BRANCH, `G = 1`: take `(1, g)`
  rcases Nat.eq_zero_or_pos G.natDegree with haG0 | haG
  · have hG1 : G = 1 := Polynomial.eq_one_of_monic_natDegree_zero hGmon haG0
    have hresH : ∀ (hne₂ : (dvSideSet F g u ℓ).Nonempty) (M₂ : ℕ)
        (hp₂ : dvHgt F g (dvSideMin F g u ℓ hne₂) = (M₂ : ℕ∞)),
        dvResPoly F H₀ hpin g u ℓ hne₂ M₂ hp₂ = H := by
      intro hne₂ M₂ hp₂
      rw [dvResPoly_pin_congr F H₀ hpin hne₂ hne hp₂ hp, hres, hG1, one_mul]
    have hHdeg : H.natDegree = dvSideDeg F g u ℓ hne := by
      rw [← hresH hne M₀ hp]
      exact (natDegree_dvResPoly F hπ H₀ hpin hℓ hcop hne hp).1
    have hM₀val : M₀ = u * dvSideDeg F g u ℓ hne :=
      C133mh4.dvHgt_dvSideMin_eq_mul_dvSideDeg_of_isDvPure F hgmon hgpos hℓ hcop hgpure
        hgd hne hp
    have hgt_g : dvHgt F g 0 = ((u * H.natDegree : ℕ) : ℕ∞) := by
      rw [← hming, hp, hM₀val, hHdeg]
    refine ⟨1, g, (one_mul g).symm, Polynomial.monic_one, hgmon, ?_, ?_,
      isDvPure_one F u ℓ, hgpure, ?_, hgt_g, ?_, hresH⟩
    · rw [haG0, Nat.mul_zero, Polynomial.natDegree_one]
    · rw [hgdegℓ, ← hHdeg]
      ring
    · rw [haG0, Nat.mul_zero, Nat.cast_zero]
      exact dvHgt_one_zero F
    · intro hne₁ M₁ hp₁
      rw [hG1]
      exact dvResPoly_one F hh H₀ hpin hne₁ M₁ hp₁
  -- OPEN-MH9-UNIT-BRANCH, `H = 1`: take `(g, 1)`
  rcases Nat.eq_zero_or_pos H.natDegree with hbH0 | hbH
  · have hH1 : H = 1 := Polynomial.eq_one_of_monic_natDegree_zero hHmon hbH0
    have hresG : ∀ (hne₁ : (dvSideSet F g u ℓ).Nonempty) (M₁ : ℕ)
        (hp₁ : dvHgt F g (dvSideMin F g u ℓ hne₁) = (M₁ : ℕ∞)),
        dvResPoly F H₀ hpin g u ℓ hne₁ M₁ hp₁ = G := by
      intro hne₁ M₁ hp₁
      rw [dvResPoly_pin_congr F H₀ hpin hne₁ hne hp₁ hp, hres, hH1, mul_one]
    have hGdeg : G.natDegree = dvSideDeg F g u ℓ hne := by
      rw [← hresG hne M₀ hp]
      exact (natDegree_dvResPoly F hπ H₀ hpin hℓ hcop hne hp).1
    have hM₀val : M₀ = u * dvSideDeg F g u ℓ hne :=
      C133mh4.dvHgt_dvSideMin_eq_mul_dvSideDeg_of_isDvPure F hgmon hgpos hℓ hcop hgpure
        hgd hne hp
    have hgt_g : dvHgt F g 0 = ((u * G.natDegree : ℕ) : ℕ∞) := by
      rw [← hming, hp, hM₀val, hGdeg]
    refine ⟨g, 1, (mul_one g).symm, hgmon, Polynomial.monic_one, ?_, ?_, hgpure,
      isDvPure_one F u ℓ, hgt_g, ?_, hresG, ?_⟩
    · rw [hgdegℓ, ← hGdeg]
      ring
    · rw [hbH0, Nat.mul_zero, Polynomial.natDegree_one]
    · rw [hbH0, Nat.mul_zero, Nat.cast_zero]
      exact dvHgt_one_zero F
    · intro hne₂ M₂ hp₂
      rw [hH1]
      exact dvResPoly_one F hh H₀ hpin hne₂ M₂ hp₂
  -- MAIN BRANCH: `0 < deg G`, `0 < deg H`
  have hdvSg : dvSideDeg F g u ℓ hne = G.natDegree + H.natDegree := by
    have h1 := (natDegree_dvResPoly F hπ H₀ hpin hℓ hcop hne hp).1
    rw [hres] at h1
    rw [← h1, Polynomial.natDegree_mul hGmon.ne_zero hHmon.ne_zero]
  have hdegg : g.natDegree = ℓ * (G.natDegree + H.natDegree) * (F.e₁ * F.f₁) := by
    rw [hgdegℓ, hdvSg]
  have hM₀val : M₀ = u * (G.natDegree + H.natDegree) := by
    rw [C133mh4.dvHgt_dvSideMin_eq_mul_dvSideDeg_of_isDvPure F hgmon hgpos hℓ hcop hgpure
      hgd hne hp, hdvSg]
  have hSg : dvSupp F g u ℓ = ((ℓ * (u * (G.natDegree + H.natDegree)) : ℕ) : ℕ∞) := by
    have h1 := dvSupp_eq_of_dvOnSide hp (dvOnSide_dvSideMin F g u ℓ hne)
    rw [hming, Nat.mul_zero, Nat.add_zero, hM₀val] at h1
    exact h1
  have hSg' : dvSupp F g u ℓ
      = ((ℓ * (u * G.natDegree) + ℓ * (u * H.natDegree) : ℕ) : ℕ∞) := by
    rw [hSg]
    exact congrArg (fun n : ℕ => (n : ℕ∞)) (by ring)
  -- initialization data (MH9M.4 step 1): the side lifts and their clause lemmas
  have hΛGmon : (C133mh5.dvSideLift F H₀ hpin u ℓ G).Monic :=
    C133mh5.dvSideLift_monic F H₀ hpin hℓ G haG
  have hΛHmon : (C133mh5.dvSideLift F H₀ hpin u ℓ H).Monic :=
    C133mh5.dvSideLift_monic F H₀ hpin hℓ H hbH
  have hΛGne : C133mh5.dvSideLift F H₀ hpin u ℓ G ≠ 0 := hΛGmon.ne_zero
  have hΛHne : C133mh5.dvSideLift F H₀ hpin u ℓ H ≠ 0 := hΛHmon.ne_zero
  have hΛGdeg : (C133mh5.dvSideLift F H₀ hpin u ℓ G).natDegree
      = ℓ * G.natDegree * (F.e₁ * F.f₁) := by
    rw [C133mh5.natDegree_dvSideLift F H₀ hpin hℓ G haG]
    ring
  have hΛHdeg : (C133mh5.dvSideLift F H₀ hpin u ℓ H).natDegree
      = ℓ * H.natDegree * (F.e₁ * F.f₁) := by
    rw [C133mh5.natDegree_dvSideLift F H₀ hpin hℓ H hbH]
    ring
  have hΛGpure : IsDvPure F (C133mh5.dvSideLift F H₀ hpin u ℓ G) u ℓ :=
    C133mh5.isDvPure_dvSideLift F hπ H₀ hpin hℓ hfloor G haG hG0
  have hΛHpure : IsDvPure F (C133mh5.dvSideLift F H₀ hpin u ℓ H) u ℓ :=
    C133mh5.isDvPure_dvSideLift F hπ H₀ hpin hℓ hfloor H hbH hH0
  have hΛGhgt : dvHgt F (C133mh5.dvSideLift F H₀ hpin u ℓ G) 0
      = ((u * G.natDegree : ℕ) : ℕ∞) := by
    have h1 := C133mh5.dvHgt_dvSideLift_slot F hπ H₀ hpin hℓ hfloor G haG hG0
    rwa [Nat.zero_mul, Nat.sub_zero] at h1
  have hΛHhgt : dvHgt F (C133mh5.dvSideLift F H₀ hpin u ℓ H) 0
      = ((u * H.natDegree : ℕ) : ℕ∞) := by
    have h1 := C133mh5.dvHgt_dvSideLift_slot F hπ H₀ hpin hℓ hfloor H hbH hH0
    rwa [Nat.zero_mul, Nat.sub_zero] at h1
  have hΛGres : ∀ (hne₁ : (dvSideSet F (C133mh5.dvSideLift F H₀ hpin u ℓ G) u ℓ).Nonempty)
      (M₁ : ℕ) (hp₁ : dvHgt F (C133mh5.dvSideLift F H₀ hpin u ℓ G)
        (dvSideMin F (C133mh5.dvSideLift F H₀ hpin u ℓ G) u ℓ hne₁) = (M₁ : ℕ∞)),
      dvResPoly F H₀ hpin (C133mh5.dvSideLift F H₀ hpin u ℓ G) u ℓ hne₁ M₁ hp₁ = G :=
    fun hne₁ M₁ hp₁ => C133mh5.dvResPoly_dvSideLift F hπ H₀ hpin hh hℓ hcop hfloor G
      hGmon haG hG0 hne₁ M₁ hp₁
  have hΛHres : ∀ (hne₂ : (dvSideSet F (C133mh5.dvSideLift F H₀ hpin u ℓ H) u ℓ).Nonempty)
      (M₂ : ℕ) (hp₂ : dvHgt F (C133mh5.dvSideLift F H₀ hpin u ℓ H)
        (dvSideMin F (C133mh5.dvSideLift F H₀ hpin u ℓ H) u ℓ hne₂) = (M₂ : ℕ∞)),
      dvResPoly F H₀ hpin (C133mh5.dvSideLift F H₀ hpin u ℓ H) u ℓ hne₂ M₂ hp₂ = H :=
    fun hne₂ M₂ hp₂ => C133mh5.dvResPoly_dvSideLift F hπ H₀ hpin hh hℓ hcop hfloor H
      hHmon hbH hH0 hne₂ M₂ hp₂
  -- the initialization product's data
  have hprodmon : (C133mh5.dvSideLift F H₀ hpin u ℓ G
      * C133mh5.dvSideLift F H₀ hpin u ℓ H).Monic := hΛGmon.mul hΛHmon
  have hproddeg : (C133mh5.dvSideLift F H₀ hpin u ℓ G
      * C133mh5.dvSideLift F H₀ hpin u ℓ H).natDegree
      = ℓ * (G.natDegree + H.natDegree) * (F.e₁ * F.f₁) := by
    rw [Polynomial.natDegree_mul hΛGne hΛHne, hΛGdeg, hΛHdeg]
    ring
  have hΛGdvd : F.e₁ * F.f₁ ∣ (C133mh5.dvSideLift F H₀ hpin u ℓ G).natDegree :=
    ⟨ℓ * G.natDegree, by rw [hΛGdeg]; ring⟩
  have hΛHdvd : F.e₁ * F.f₁ ∣ (C133mh5.dvSideLift F H₀ hpin u ℓ H).natDegree :=
    ⟨ℓ * H.natDegree, by rw [hΛHdeg]; ring⟩
  have hprodpure : IsDvPure F (C133mh5.dvSideLift F H₀ hpin u ℓ G
      * C133mh5.dvSideLift F H₀ hpin u ℓ H) u ℓ :=
    C133mh3.isDvPure_mul hπ hh H₀ hpin hℓ hcop hfloor hΛGne hΛHne hΛGdvd hΛHdvd
      hΛGpure hΛHpure
  have hprodpos : 0 < (C133mh5.dvSideLift F H₀ hpin u ℓ G
      * C133mh5.dvSideLift F H₀ hpin u ℓ H).natDegree := by
    rw [hproddeg]
    exact Nat.mul_pos (Nat.mul_pos hℓ (by omega)) hDpos
  have hproddvd : F.e₁ * F.f₁ ∣ (C133mh5.dvSideLift F H₀ hpin u ℓ G
      * C133mh5.dvSideLift F H₀ hpin u ℓ H).natDegree :=
    ⟨ℓ * (G.natDegree + H.natDegree), by rw [hproddeg]; ring⟩
  have hneprod : (dvSideSet F (C133mh5.dvSideLift F H₀ hpin u ℓ G
      * C133mh5.dvSideLift F H₀ hpin u ℓ H) u ℓ).Nonempty :=
    dvSideSet_nonempty F hprodmon.ne_zero u hℓ
  obtain ⟨Mprod, hpprod⟩ := exists_pin F hneprod
  have hproddvS : dvSideDeg F (C133mh5.dvSideLift F H₀ hpin u ℓ G
      * C133mh5.dvSideLift F H₀ hpin u ℓ H) u ℓ hneprod
      = G.natDegree + H.natDegree :=
    dvSideDeg_of_pure_deg F hℓ hcop hprodpure hneprod hproddeg
  have hMprodval : Mprod = u * (G.natDegree + H.natDegree) := by
    rw [C133mh4.dvHgt_dvSideMin_eq_mul_dvSideDeg_of_isDvPure F hprodmon hprodpos hℓ hcop
      hprodpure hproddvd hneprod hpprod, hproddvS]
  have hRprod : ∀ (hneP : (dvSideSet F (C133mh5.dvSideLift F H₀ hpin u ℓ G
      * C133mh5.dvSideLift F H₀ hpin u ℓ H) u ℓ).Nonempty) (MP : ℕ)
      (hpP : dvHgt F (C133mh5.dvSideLift F H₀ hpin u ℓ G
        * C133mh5.dvSideLift F H₀ hpin u ℓ H)
        (dvSideMin F (C133mh5.dvSideLift F H₀ hpin u ℓ G
          * C133mh5.dvSideLift F H₀ hpin u ℓ H) u ℓ hneP) = (MP : ℕ∞)),
      dvResPoly F H₀ hpin (C133mh5.dvSideLift F H₀ hpin u ℓ G
        * C133mh5.dvSideLift F H₀ hpin u ℓ H) u ℓ hneP MP hpP = G * H := by
    intro hneP MP hpP
    have hng : (dvSideSet F (C133mh5.dvSideLift F H₀ hpin u ℓ G) u ℓ).Nonempty :=
      ⟨0, hΛGpure.1⟩
    have hnz : (dvSideSet F (C133mh5.dvSideLift F H₀ hpin u ℓ H) u ℓ).Nonempty :=
      ⟨0, hΛHpure.1⟩
    obtain ⟨MG', hpG'⟩ := exists_pin F hng
    obtain ⟨MH', hpH'⟩ := exists_pin F hnz
    rw [C133mh3.dvResPoly_mul_gen hπ hh H₀ hpin hℓ hcop hfloor hΛGne hΛHne hng hnz hneP
        hpG' hpH' hpP,
      C133mh5.dvResPoly_dvSideLift F hπ H₀ hpin hh hℓ hcop hfloor G hGmon haG hG0 hng
        MG' hpG',
      C133mh5.dvResPoly_dvSideLift F hπ H₀ hpin hh hℓ hcop hfloor H hHmon hbH hH0 hnz
        MH' hpH']
  have hWΛeq : dvSupp F (C133mh5.dvSideLift F H₀ hpin u ℓ G
      * C133mh5.dvSideLift F H₀ hpin u ℓ H) u ℓ
      = ((ℓ * (u * G.natDegree) + ℓ * (u * H.natDegree) : ℕ) : ℕ∞) := by
    rw [C133mh3.dvSupp_mul hπ hh H₀ hpin hℓ hfloor hΛGne hΛHne,
      C133mh5.dvSupp_dvSideLift F hπ H₀ hpin hℓ hfloor G haG,
      C133mh5.dvSupp_dvSideLift F hπ H₀ hpin hℓ hfloor H hbH]
    push_cast
    ring
  -- MH9M.4 step 2: the initial error floor via equal base-line reads (node 5)
  have hreads0 : ∀ j k' : ℕ,
      ℓ * k' + u * j = ℓ * (u * G.natDegree) + ℓ * (u * H.natDegree) →
      F.twistRead H₀ hpin k' (dev F.key g j)
        = F.twistRead H₀ hpin k' (dev F.key (C133mh5.dvSideLift F H₀ hpin u ℓ G
            * C133mh5.dvSideLift F H₀ hpin u ℓ H) j) := by
    intro j k' hline
    by_cases hgrid : ℓ ∣ j
    · obtain ⟨t, ht⟩ := hgrid
      have hjt : j = t * ℓ := by
        have := Nat.mul_comm ℓ t
        omega
      have hMg2 : ℓ * M₀ = ℓ * (u * G.natDegree) + ℓ * (u * H.natDegree) := by
        rw [hM₀val]
        ring
      have hMp2 : ℓ * Mprod = ℓ * (u * G.natDegree) + ℓ * (u * H.natDegree) := by
        rw [hMprodval]
        ring
      have hut : u * t ≤ u * (G.natDegree + H.natDegree) := by
        have h4 : u * (t * ℓ) = ℓ * (u * t) := by ring
        rw [hjt] at hline
        have h5' : ℓ * (u * G.natDegree) + ℓ * (u * H.natDegree)
            = ℓ * (u * (G.natDegree + H.natDegree)) := by ring
        have h6 : ℓ * (k' + u * t) = ℓ * (u * (G.natDegree + H.natDegree)) := by
          rw [Nat.mul_add]
          omega
        have h7 := Nat.eq_of_mul_eq_mul_left hℓ h6
        omega
      have htle : t ≤ G.natDegree + H.natDegree := Nat.le_of_mul_le_mul_left hut hu
      rw [lineRead_eq_dvResPoly_coeff F H₀ hpin hℓ hgpure hne hp hjt (by omega)
          (by rw [hdvSg]; exact htle),
        lineRead_eq_dvResPoly_coeff F H₀ hpin hℓ hprodpure hneprod hpprod hjt (by omega)
          (by rw [hproddvS]; exact htle),
        hres, hRprod hneprod Mprod hpprod]
    · rw [lineRead_eq_zero_offgrid F hπ H₀ hpin hℓ hcop hgpure hSg' hline hgrid,
        lineRead_eq_zero_offgrid F hπ H₀ hpin hℓ hcop hprodpure hWΛeq hline hgrid]
  have herr0 : ((ℓ * (u * G.natDegree) + ℓ * (u * H.natDegree) + 0 + 1 : ℕ) : ℕ∞)
      ≤ dvSupp F (g - C133mh5.dvSideLift F H₀ hpin u ℓ G
          * C133mh5.dvSideLift F H₀ hpin u ℓ H) u ℓ := by
    have h5 := dvSupp_sub_succ_of_same_residual F hπ hh H₀ hpin hℓ
      (le_of_eq hSg'.symm) (le_of_eq hWΛeq.symm) hreads0
    rw [show (ℓ * (u * G.natDegree) + ℓ * (u * H.natDegree) + 0 + 1 : ℕ)
        = ℓ * (u * G.natDegree) + ℓ * (u * H.natDegree) + 1 by omega]
    exact h5
  have hinit : TAInv F H₀ hpin u ℓ g G H 0
      (C133mh5.dvSideLift F H₀ hpin u ℓ G) (C133mh5.dvSideLift F H₀ hpin u ℓ H) :=
    ⟨hΛGmon, hΛHmon, hΛGdeg, hΛHdeg, hΛGpure, hΛHpure, hΛGhgt, hΛHhgt, hΛGres, hΛHres,
      herr0⟩
  -- MH9M.4 step 3: the Lemma S + M4 step
  have hstepEx : ∀ (k : ℕ) (a b : Polynomial O), TAInv F H₀ hpin u ℓ g G H k a b →
      ∃ a' b' : Polynomial O, TAInv F H₀ hpin u ℓ g G H (k + 1) a' b' ∧
        ((k : ℕ) : ℕ∞) ≤ dvSupp F (a' - a) u ℓ ∧
        ((k : ℕ) : ℕ∞) ≤ dvSupp F (b' - b) u ℓ := by
    intro k a b hInv
    obtain ⟨hm1, hm2, hd1, hd2, hp1, hp2, hh1, hh2, hr1, hr2, herr⟩ := hInv
    have hne₁ : (dvSideSet F a u ℓ).Nonempty := ⟨0, hp1.1⟩
    have hne₂ : (dvSideSet F b u ℓ).Nonempty := ⟨0, hp2.1⟩
    have hpn₁ : dvHgt F a (dvSideMin F a u ℓ hne₁) = ((u * G.natDegree : ℕ) : ℕ∞) :=
      pin_of_pure_hgt0 F hp1 hh1 hne₁
    have hpn₂ : dvHgt F b (dvSideMin F b u ℓ hne₂) = ((u * H.natDegree : ℕ) : ℕ∞) :=
      pin_of_pure_hgt0 F hp2 hh2 hne₂
    have hSa : dvSupp F a u ℓ = ((ℓ * (u * G.natDegree) : ℕ) : ℕ∞) :=
      dvSupp_of_pure_hgt0 F hp1 hh1
    have hSb : dvSupp F b u ℓ = ((ℓ * (u * H.natDegree) : ℕ) : ℕ∞) :=
      dvSupp_of_pure_hgt0 F hp2 hh2
    have hapos : 0 < a.natDegree := by
      rw [hd1]
      exact Nat.mul_pos (Nat.mul_pos hℓ haG) hDpos
    have hbpos : 0 < b.natDegree := by
      rw [hd2]
      exact Nat.mul_pos (Nat.mul_pos hℓ hbH) hDpos
    have hadvd : F.e₁ * F.f₁ ∣ a.natDegree := ⟨ℓ * G.natDegree, by rw [hd1]; ring⟩
    have hbdvd : F.e₁ * F.f₁ ∣ b.natDegree := ⟨ℓ * H.natDegree, by rw [hd2]; ring⟩
    have hcopres : IsCoprime (dvResPoly F H₀ hpin a u ℓ hne₁ (u * G.natDegree) hpn₁)
        (dvResPoly F H₀ hpin b u ℓ hne₂ (u * H.natDegree) hpn₂) := by
      rw [hr1 hne₁ (u * G.natDegree) hpn₁, hr2 hne₂ (u * H.natDegree) hpn₂]
      exact hGH
    have hdegab : (a * b).natDegree = a.natDegree + b.natDegree :=
      Polynomial.natDegree_mul hm1.ne_zero hm2.ne_zero
    have hdgab : g.natDegree = a.natDegree + b.natDegree := by
      rw [hd1, hd2, hdegg]
      ring
    have hedeg : (g - a * b).natDegree < a.natDegree + b.natDegree := by
      rcases eq_or_ne (g - a * b) 0 with h0 | h0
      · rw [h0, Polynomial.natDegree_zero]
        omega
      · have hdd : (g - a * b).degree < g.degree := by
          refine Polynomial.degree_sub_lt ?_ hgmon.ne_zero ?_
          · rw [Polynomial.degree_eq_natDegree hgmon.ne_zero,
              Polynomial.degree_eq_natDegree (hm1.mul hm2).ne_zero, hdegab, hdgab]
          · rw [hgmon.leadingCoeff, (hm1.mul hm2).leadingCoeff]
        have h2 : (g - a * b).degree < ((a.natDegree + b.natDegree : ℕ) : WithBot ℕ) := by
          rw [← hdgab, ← Polynomial.degree_eq_natDegree hgmon.ne_zero]
          exact hdd
        exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr h2
    obtain ⟨U, V, hUdeg, hVdeg, hUsupp, hVsupp, hcontr⟩ :=
      lemmaS π F hπ hh H₀ hpin u ℓ hℓ hcop hfloor a b hm1 hm2 hapos hbpos hadvd hbdvd
        hp1 hp2 hne₁ hne₂ (u * G.natDegree) (u * H.natDegree) hpn₁ hpn₂ hcopres
        (ℓ * (u * G.natDegree)) (ℓ * (u * H.natDegree)) hSa hSb
        (g - a * b) (ℓ * (u * G.natDegree) + ℓ * (u * H.natDegree) + k + 1) hedeg
        (by omega) herr
    obtain ⟨hm1', hdeq1', hp1', hne1', hpin1', hres1'⟩ :=
      dv_pure_add_of_lt' F hπ H₀ hpin hℓ hcop rfl hm1 hp1 hne₁ hpn₁ hSa
        (Polynomial.degree_lt_degree hUdeg)
        (le_trans (by exact_mod_cast (show ℓ * (u * G.natDegree) + 1
          ≤ ℓ * (u * G.natDegree) + ℓ * (u * H.natDegree) + k + 1
            - ℓ * (u * H.natDegree) by omega)) hUsupp)
    obtain ⟨hm2', hdeq2', hp2', hne2', hpin2', hres2'⟩ :=
      dv_pure_add_of_lt' F hπ H₀ hpin hℓ hcop rfl hm2 hp2 hne₂ hpn₂ hSb
        (Polynomial.degree_lt_degree hVdeg)
        (le_trans (by exact_mod_cast (show ℓ * (u * H.natDegree) + 1
          ≤ ℓ * (u * G.natDegree) + ℓ * (u * H.natDegree) + k + 1
            - ℓ * (u * G.natDegree) by omega)) hVsupp)
    have hh1' : dvHgt F (a + U) 0 = ((u * G.natDegree : ℕ) : ℕ∞) := by
      have h1 := hpin1'
      rwa [dvSideMin_eq_zero_of_isDvPure hp1' hne1'] at h1
    have hh2' : dvHgt F (b + V) 0 = ((u * H.natDegree : ℕ) : ℕ∞) := by
      have h1 := hpin2'
      rwa [dvSideMin_eq_zero_of_isDvPure hp2' hne2'] at h1
    have hr1' : ∀ (hneA : (dvSideSet F (a + U) u ℓ).Nonempty) (MA : ℕ)
        (hpA : dvHgt F (a + U) (dvSideMin F (a + U) u ℓ hneA) = (MA : ℕ∞)),
        dvResPoly F H₀ hpin (a + U) u ℓ hneA MA hpA = G := by
      intro hneA MA hpA
      rw [dvResPoly_pin_congr F H₀ hpin hneA hne1' hpA hpin1', hres1']
      exact hr1 hne₁ (u * G.natDegree) hpn₁
    have hr2' : ∀ (hneB : (dvSideSet F (b + V) u ℓ).Nonempty) (MB : ℕ)
        (hpB : dvHgt F (b + V) (dvSideMin F (b + V) u ℓ hneB) = (MB : ℕ∞)),
        dvResPoly F H₀ hpin (b + V) u ℓ hneB MB hpB = H := by
      intro hneB MB hpB
      rw [dvResPoly_pin_congr F H₀ hpin hneB hne2' hpB hpin2', hres2']
      exact hr2 hne₂ (u * H.natDegree) hpn₂
    have herr' : ((ℓ * (u * G.natDegree) + ℓ * (u * H.natDegree) + (k + 1) + 1 : ℕ) : ℕ∞)
        ≤ dvSupp F (g - (a + U) * (b + V)) u ℓ := by
      have hUV : ((ℓ * (u * G.natDegree) + ℓ * (u * H.natDegree) + (k + 1) + 1 : ℕ) : ℕ∞)
          ≤ dvSupp F (U * V) u ℓ := by
        rcases eq_or_ne U 0 with h0 | h0
        · rw [h0, zero_mul, C130s6.dvSupp_zero_eq_top F u hℓ]
          exact le_top
        rcases eq_or_ne V 0 with h0' | h0'
        · rw [h0', mul_zero, C130s6.dvSupp_zero_eq_top F u hℓ]
          exact le_top
        rw [C133mh3.dvSupp_mul hπ hh H₀ hpin hℓ hfloor h0 h0']
        calc ((ℓ * (u * G.natDegree) + ℓ * (u * H.natDegree) + (k + 1) + 1 : ℕ) : ℕ∞)
            ≤ ((ℓ * (u * G.natDegree) + ℓ * (u * H.natDegree) + k + 1
                  - ℓ * (u * H.natDegree)
                + (ℓ * (u * G.natDegree) + ℓ * (u * H.natDegree) + k + 1
                  - ℓ * (u * G.natDegree)) : ℕ) : ℕ∞) := by
              exact_mod_cast (show ℓ * (u * G.natDegree) + ℓ * (u * H.natDegree) + (k + 1) + 1
                ≤ ℓ * (u * G.natDegree) + ℓ * (u * H.natDegree) + k + 1
                    - ℓ * (u * H.natDegree)
                  + (ℓ * (u * G.natDegree) + ℓ * (u * H.natDegree) + k + 1
                    - ℓ * (u * G.natDegree)) by omega)
          _ = ((ℓ * (u * G.natDegree) + ℓ * (u * H.natDegree) + k + 1
                  - ℓ * (u * H.natDegree) : ℕ) : ℕ∞)
              + ((ℓ * (u * G.natDegree) + ℓ * (u * H.natDegree) + k + 1
                  - ℓ * (u * G.natDegree) : ℕ) : ℕ∞) := by
              push_cast
              ring
          _ ≤ dvSupp F U u ℓ + dvSupp F V u ℓ := add_le_add hUsupp hVsupp
      have hid : g - (a + U) * (b + V)
          = (g - a * b - (b * U + a * V)) - U * V := by ring
      rw [hid]
      refine le_dvSupp_sub' F hℓ ?_ hUV
      exact le_trans (by exact_mod_cast (show ℓ * (u * G.natDegree)
        + ℓ * (u * H.natDegree) + (k + 1) + 1
        ≤ ℓ * (u * G.natDegree) + ℓ * (u * H.natDegree) + k + 1 + 1 by omega)) hcontr
    refine ⟨a + U, b + V,
      ⟨hm1', hm2', by rw [hdeq1']; exact hd1, by rw [hdeq2']; exact hd2, hp1', hp2',
        hh1', hh2', hr1', hr2', herr'⟩, ?_, ?_⟩
    · rw [show a + U - a = U by ring]
      exact le_trans (by exact_mod_cast (show k ≤ ℓ * (u * G.natDegree)
        + ℓ * (u * H.natDegree) + k + 1 - ℓ * (u * H.natDegree) by omega)) hUsupp
    · rw [show b + V - b = V by ring]
      exact le_trans (by exact_mod_cast (show k ≤ ℓ * (u * G.natDegree)
        + ℓ * (u * H.natDegree) + k + 1 - ℓ * (u * G.natDegree) by omega)) hVsupp
  -- the recursively chosen invariant sequence
  let SInv : ℕ → Type _ := fun k =>
    {ab : Polynomial O × Polynomial O // TAInv F H₀ hpin u ℓ g G H k ab.1 ab.2}
  let stepF : ∀ k : ℕ, SInv k → SInv (k + 1) := fun k x =>
    ⟨⟨(hstepEx k x.val.1 x.val.2 x.property).choose,
      (hstepEx k x.val.1 x.val.2 x.property).choose_spec.choose⟩,
      (hstepEx k x.val.1 x.val.2 x.property).choose_spec.choose_spec.1⟩
  let seq : ∀ k : ℕ, SInv k := fun k =>
    Nat.rec (motive := SInv)
      ⟨⟨C133mh5.dvSideLift F H₀ hpin u ℓ G, C133mh5.dvSideLift F H₀ hpin u ℓ H⟩, hinit⟩
      stepF k
  have hINV : ∀ k : ℕ, TAInv F H₀ hpin u ℓ g G H k (seq k).val.1 (seq k).val.2 :=
    fun k => (seq k).property
  have hstep1 : ∀ k : ℕ, ((k : ℕ) : ℕ∞)
      ≤ dvSupp F ((seq (k + 1)).val.1 - (seq k).val.1) u ℓ := fun k =>
    (hstepEx k (seq k).val.1 (seq k).val.2 (seq k).property).choose_spec.choose_spec.2.1
  have hstep2 : ∀ k : ℕ, ((k : ℕ) : ℕ∞)
      ≤ dvSupp F ((seq (k + 1)).val.2 - (seq k).val.2) u ℓ := fun k =>
    (hstepEx k (seq k).val.1 (seq k).val.2 (seq k).property).choose_spec.choose_spec.2.2
  -- MH9M.4 step 4: the graded limits, monic of the exact degrees (node 6)
  have hdeg1w : ∀ k : ℕ, ((seq k).val.1).natDegree
      < ℓ * G.natDegree * (F.e₁ * F.f₁) + 1 := by
    intro k
    have h1 := (hINV k).2.2.1
    omega
  have hdeg2w : ∀ k : ℕ, ((seq k).val.2).natDegree
      < ℓ * H.natDegree * (F.e₁ * F.f₁) + 1 := by
    intro k
    have h1 := (hINV k).2.2.2.1
    omega
  obtain ⟨P₁, hP₁win, hP₁tail⟩ := C133mh8.exists_dvGradedLimit hπ F hℓ
    (ℓ * G.natDegree * (F.e₁ * F.f₁) + 1) (fun k => (seq k).val.1) hdeg1w hstep1
  obtain ⟨P₂, hP₂win, hP₂tail⟩ := C133mh8.exists_dvGradedLimit hπ F hℓ
    (ℓ * H.natDegree * (F.e₁ * F.f₁) + 1) (fun k => (seq k).val.2) hdeg2w hstep2
  obtain ⟨hP₁mon, hP₁d⟩ := monic_of_dvGradedLimit hπ F hℓ
    (fun k => (hINV k).1) (fun k => (hINV k).2.2.1) hP₁win hP₁tail
  obtain ⟨hP₂mon, hP₂d⟩ := monic_of_dvGradedLimit hπ F hℓ
    (fun k => (hINV k).2.1) (fun k => (hINV k).2.2.2.1) hP₂win hP₂tail
  -- MH9M.4 step 5: purity/height/residual transfer at a late iterate (M4 once more)
  obtain ⟨im1, -, id1, -, ip1, -, ih1, -, ir1, -, -⟩ :=
    hINV (ℓ * (u * G.natDegree) + 1)
  have hpnq1 : dvHgt F ((seq (ℓ * (u * G.natDegree) + 1)).val.1)
      (dvSideMin F ((seq (ℓ * (u * G.natDegree) + 1)).val.1) u ℓ ⟨0, ip1.1⟩)
      = ((u * G.natDegree : ℕ) : ℕ∞) := pin_of_pure_hgt0 F ip1 ih1 ⟨0, ip1.1⟩
  have hSq1 : dvSupp F ((seq (ℓ * (u * G.natDegree) + 1)).val.1) u ℓ
      = ((ℓ * (u * G.natDegree) : ℕ) : ℕ∞) := dvSupp_of_pure_hgt0 F ip1 ih1
  have hydeg1 : (P₁ - (seq (ℓ * (u * G.natDegree) + 1)).val.1).degree
      < ((seq (ℓ * (u * G.natDegree) + 1)).val.1).degree := by
    rcases eq_or_ne (P₁ - (seq (ℓ * (u * G.natDegree) + 1)).val.1) 0 with h0 | h0
    · rw [h0, Polynomial.degree_zero]
      exact bot_lt_iff_ne_bot.mpr fun hbot => im1.ne_zero (Polynomial.degree_eq_bot.mp hbot)
    · have hdeq : P₁.degree = ((seq (ℓ * (u * G.natDegree) + 1)).val.1).degree := by
        rw [Polynomial.degree_eq_natDegree hP₁mon.ne_zero,
          Polynomial.degree_eq_natDegree im1.ne_zero, hP₁d, id1]
      have hdd := Polynomial.degree_sub_lt hdeq hP₁mon.ne_zero
        (by rw [hP₁mon.leadingCoeff, im1.leadingCoeff])
      rwa [hdeq] at hdd
  obtain ⟨-, -, hP₁pure, hneP₁, hpinP₁, hresP₁⟩ :=
    dv_pure_add_of_lt' F hπ H₀ hpin hℓ hcop
      (show (seq (ℓ * (u * G.natDegree) + 1)).val.1
        + (P₁ - (seq (ℓ * (u * G.natDegree) + 1)).val.1) = P₁ by ring)
      im1 ip1 ⟨0, ip1.1⟩ hpnq1 hSq1 hydeg1 (hP₁tail (ℓ * (u * G.natDegree) + 1))
  have hP₁hgt : dvHgt F P₁ 0 = ((u * G.natDegree : ℕ) : ℕ∞) := by
    have h1 := hpinP₁
    rwa [dvSideMin_eq_zero_of_isDvPure hP₁pure hneP₁] at h1
  have hP₁res : ∀ (hne₁ : (dvSideSet F P₁ u ℓ).Nonempty) (M₁ : ℕ)
      (hp₁ : dvHgt F P₁ (dvSideMin F P₁ u ℓ hne₁) = (M₁ : ℕ∞)),
      dvResPoly F H₀ hpin P₁ u ℓ hne₁ M₁ hp₁ = G := by
    intro hne₁ M₁ hp₁
    rw [dvResPoly_pin_congr F H₀ hpin hne₁ hneP₁ hp₁ hpinP₁, hresP₁]
    exact ir1 ⟨0, ip1.1⟩ (u * G.natDegree) hpnq1
  obtain ⟨jm1, jm2, -, jd2, -, jp2, -, jh2, -, jr2, -⟩ :=
    hINV (ℓ * (u * H.natDegree) + 1)
  have hpnq2 : dvHgt F ((seq (ℓ * (u * H.natDegree) + 1)).val.2)
      (dvSideMin F ((seq (ℓ * (u * H.natDegree) + 1)).val.2) u ℓ ⟨0, jp2.1⟩)
      = ((u * H.natDegree : ℕ) : ℕ∞) := pin_of_pure_hgt0 F jp2 jh2 ⟨0, jp2.1⟩
  have hSq2 : dvSupp F ((seq (ℓ * (u * H.natDegree) + 1)).val.2) u ℓ
      = ((ℓ * (u * H.natDegree) : ℕ) : ℕ∞) := dvSupp_of_pure_hgt0 F jp2 jh2
  have hydeg2 : (P₂ - (seq (ℓ * (u * H.natDegree) + 1)).val.2).degree
      < ((seq (ℓ * (u * H.natDegree) + 1)).val.2).degree := by
    rcases eq_or_ne (P₂ - (seq (ℓ * (u * H.natDegree) + 1)).val.2) 0 with h0 | h0
    · rw [h0, Polynomial.degree_zero]
      exact bot_lt_iff_ne_bot.mpr fun hbot => jm2.ne_zero (Polynomial.degree_eq_bot.mp hbot)
    · have hdeq : P₂.degree = ((seq (ℓ * (u * H.natDegree) + 1)).val.2).degree := by
        rw [Polynomial.degree_eq_natDegree hP₂mon.ne_zero,
          Polynomial.degree_eq_natDegree jm2.ne_zero, hP₂d, jd2]
      have hdd := Polynomial.degree_sub_lt hdeq hP₂mon.ne_zero
        (by rw [hP₂mon.leadingCoeff, jm2.leadingCoeff])
      rwa [hdeq] at hdd
  obtain ⟨-, -, hP₂pure, hneP₂, hpinP₂, hresP₂⟩ :=
    dv_pure_add_of_lt' F hπ H₀ hpin hℓ hcop
      (show (seq (ℓ * (u * H.natDegree) + 1)).val.2
        + (P₂ - (seq (ℓ * (u * H.natDegree) + 1)).val.2) = P₂ by ring)
      jm2 jp2 ⟨0, jp2.1⟩ hpnq2 hSq2 hydeg2 (hP₂tail (ℓ * (u * H.natDegree) + 1))
  have hP₂hgt : dvHgt F P₂ 0 = ((u * H.natDegree : ℕ) : ℕ∞) := by
    have h1 := hpinP₂
    rwa [dvSideMin_eq_zero_of_isDvPure hP₂pure hneP₂] at h1
  have hP₂res : ∀ (hne₂ : (dvSideSet F P₂ u ℓ).Nonempty) (M₂ : ℕ)
      (hp₂ : dvHgt F P₂ (dvSideMin F P₂ u ℓ hne₂) = (M₂ : ℕ∞)),
      dvResPoly F H₀ hpin P₂ u ℓ hne₂ M₂ hp₂ = H := by
    intro hne₂ M₂ hp₂
    rw [dvResPoly_pin_congr F H₀ hpin hne₂ hneP₂ hp₂ hpinP₂, hresP₂]
    exact jr2 ⟨0, jp2.1⟩ (u * H.natDegree) hpnq2
  -- MH9M.4 step 6: exact multiplication (node 7)
  have hgP : g = P₁ * P₂ := by
    have hdegsub : (g - P₁ * P₂).natDegree
        < ℓ * G.natDegree * (F.e₁ * F.f₁) + ℓ * H.natDegree * (F.e₁ * F.f₁) + 1 := by
      have h1 : (P₁ * P₂).natDegree
          ≤ ℓ * G.natDegree * (F.e₁ * F.f₁) + ℓ * H.natDegree * (F.e₁ * F.f₁) := by
        refine le_trans Polynomial.natDegree_mul_le ?_
        omega
      have h2 : g.natDegree = ℓ * G.natDegree * (F.e₁ * F.f₁)
          + ℓ * H.natDegree * (F.e₁ * F.f₁) := by
        rw [hdegg]
        ring
      have h3 := Polynomial.natDegree_sub_le g (P₁ * P₂)
      have h4 : (g - P₁ * P₂).natDegree
          ≤ ℓ * G.natDegree * (F.e₁ * F.f₁) + ℓ * H.natDegree * (F.e₁ * F.f₁) :=
        le_trans h3 (max_le (by omega) h1)
      omega
    have hWall : ∀ N : ℕ, ((N : ℕ) : ℕ∞) ≤ dvSupp F (g - P₁ * P₂) u ℓ := by
      intro N
      obtain ⟨km1, -, -, -, -, -, -, -, -, -, kerr⟩ := hINV N
      have hid : g - P₁ * P₂
          = (g - (seq N).val.1 * (seq N).val.2)
            - ((P₁ - (seq N).val.1) * P₂ + (seq N).val.1 * (P₂ - (seq N).val.2)) := by
        ring
      rw [hid]
      refine le_dvSupp_sub' F hℓ
        (le_trans (by exact_mod_cast (show N ≤ ℓ * (u * G.natDegree)
          + ℓ * (u * H.natDegree) + N + 1 by omega)) kerr)
        (le_trans (le_min ?_ ?_) (C130s6.min_dvSupp_le_dvSupp_add F hℓ _ _))
      · rcases eq_or_ne (P₁ - (seq N).val.1) 0 with h0 | h0
        · rw [h0, zero_mul, C130s6.dvSupp_zero_eq_top F u hℓ]
          exact le_top
        · rw [C133mh3.dvSupp_mul hπ hh H₀ hpin hℓ hfloor h0 hP₂mon.ne_zero]
          exact le_trans (hP₁tail N) le_self_add
      · rcases eq_or_ne (P₂ - (seq N).val.2) 0 with h0 | h0
        · rw [h0, mul_zero, C130s6.dvSupp_zero_eq_top F u hℓ]
          exact le_top
        · rw [C133mh3.dvSupp_mul hπ hh H₀ hpin hℓ hfloor km1.ne_zero h0]
          exact le_trans (hP₂tail N) le_add_self
    exact sub_eq_zero.mp (eq_zero_of_forall_dvSupp hπ F hℓ hdegsub hWall)
  -- the assembly
  refine ⟨P₁, P₂, hgP, hP₁mon, hP₂mon, ?_, ?_, hP₁pure, hP₂pure, hP₁hgt, hP₂hgt,
    hP₁res, hP₂res⟩
  · rw [hP₁d]
    ring
  · rw [hP₂d]
    ring

end Uniformity.Density.Tower.C133mh9

/-! ## AxCheck footer -/

section AxCheck

#print axioms Uniformity.Density.Tower.C133mh9.dvLinePoly
#print axioms Uniformity.Density.Tower.C133mh9.dvLinePoly_coeff
#print axioms Uniformity.Density.Tower.C133mh9.natDegree_dvLinePoly_le
#print axioms Uniformity.Density.Tower.C133mh9.dvLinePoly_zero
#print axioms Uniformity.Density.Tower.C133mh9.dvLinePoly_dvWindowLift
#print axioms Uniformity.Density.Tower.C133mh9.dvLinePoly_mul_of_isDvPure
#print axioms Uniformity.Density.Tower.C133mh9.lemmaS
#print axioms Uniformity.Density.Tower.C133mh9.dvSupp_sub_succ_of_same_residual
#print axioms Uniformity.Density.Tower.C133mh9.monic_of_dvGradedLimit
#print axioms Uniformity.Density.Tower.C133mh9.eq_zero_of_forall_dvSupp
#print axioms Uniformity.Density.Tower.C133mh9.dvHgt_one_zero
#print axioms Uniformity.Density.Tower.C133mh9.dvSupp_one
#print axioms Uniformity.Density.Tower.C133mh9.isDvPure_one
#print axioms Uniformity.Density.Tower.C133mh9.dvResPoly_one
#print axioms Uniformity.Density.Tower.C133mh9.theoremA

end AxCheck
