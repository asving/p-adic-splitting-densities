/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C133mh0
import Uniformity.ChapC.C133mh3
import Uniformity.ChapB.B35a
import Uniformity.HenselFactorization

/-!
# Uniformity.ChapC.C133mh5 — `[MH5S 2026-08-28]`: the corrected side lift Λ (node MH.5),
with the Lemma S prefix (node MH.7)

**Nodes MH.5 and MH.7** (`docs/in-progress/HENSEL_ENGINE_2026-08-26.md` §4.1, §4.2, §9).

## MH.5 — the corrected side lift Λ

§4.1's initialization lift, built through the PUBLIC C131f `stageLiftO` pins (the private
C.46/C.47 helpers are NOT consumed, per the §9 row's fence), fed the **inverse-twisted**
target `η^{q(M)}·κ` so that the C.22 twist cancels exactly and the ϖ-read of the digit is
`κ` on the nose — the "[MHDISP 2026-08-27: corrected supply]" clause.  This route needs NO
`Finite (ResidueField O)` hypothesis (unlike the C.14 `exists_twistRead_preimage`
alternative flagged in the same amendment).

Three layers land here, each with its §4.1 clause lemmas:

* `twistLiftO` — the single digit: degree `< D′` (`natDegree_twistLiftO_lt`), exact height
  (`stageHeight_twistLiftO`), exact ϖ-read (`twistRead_twistLiftO`), zero-target law
  (`twistLiftO_zero`).
* `dvWindowLift` — the **Λ-window lift** (§4.2's "the §4.1 lift without the monic top
  term"): a residual-side polynomial `ψ` placed on the grade-`(ℓ·M₀ + u·j₀)` line at
  abscissae `j₀ + t·ℓ`, heights `M₀ − u·t`.  Clauses: slot support (`dev_dvWindowLift`,
  `dev_dvWindowLift_off`), degree window (`natDegree_dvWindowLift_lt`, and the Lemma-S
  window `natDegree_dvWindowLift_lt'`), pinned W-height `≥` the grade
  (`le_dvSupp_dvWindowLift`), and the slotwise read identity (`twistRead_dvWindowLift`).
* `dvSideLift` — the **monic-top variant Λ(P) = Φ′^{dℓ} + Σ_{t<d} B_t Φ′^{tℓ}** used at the
  §4.4 initialization.  The §4.1 clause list, verbatim: monic of degree `ℓ·d·D′`
  (`dvSideLift_monic`, `natDegree_dvSideLift`); digits at abscissae `tℓ` with heights
  exactly `u(d−t)`, `⊤` where `P.coeff t = 0` (`dev_dvSideLift_top/slot/past/off`,
  `dvHgt_dvSideLift_top/slot/slot_top`); pure (`isDvPure_dvSideLift`); `W = u·d·ℓ` with
  `M₀ = u·d` (`dvSupp_dvSideLift`, `dvHgt_dvSideLift_sideMin`); and `R(Λ(P)) = P` exactly
  (`dvResPoly_dvSideLift`).

## MH.7 — the Lemma S prefix

* `le_dvSupp_succ_of_lineReads_eq_zero` — **window read-faithfulness** (MH.0b's window
  half, Lemma S's closing step): `W ≥ c` and all grade-`c` line reads zero force
  `W ≥ c+1`.  Unconditional, through the landed `C133mh3.m1DigitFaithful`.
* `exists_bezout_degree_lt` / `bezout_degree_lt_unique` — §4.2's Bézout-with-degree-control
  solve: for coprime `G, H` the decomposition `E = H·Ū + G·V̄` with `deg Ū < deg G`,
  `deg V̄ < deg H` exists and is unique (the "injective, hence bijective by equal finite
  K-dimensions" K-linear map, in solved form).  `exists_stageField_bezout_degree_lt` /
  `stageField_bezout_degree_lt_unique` instantiate it at the stage field through the
  standing D9 local `Field` reconstruction (C.04 exports no instance).

## Honest scope: what does NOT land here

The assembled Lemma S (§4.2) needs the grade-`c` MIXED product read law — Theorem M
clause 3 at an arbitrary grade above the support line — which is open (the landed
`C133mh3.dvResPoly_mul_gen` reads at the support line only).  Lemma S is therefore
recorded as the named open statement shape **`LemmaSStatement`** (`Prop`-valued def,
nothing asserted — the C133mh1 statement-shape pattern): it is the MH.9 unit's carried
hypothesis, exactly §4.2's data and conclusion in landed vocabulary.

## DEPENDS

C131f public pins (`stageLiftO` degree/residue/height, root-namespace aliases) · C.19/C.22
(`stageLetter`, `stageLetter_ne_zero`, `twistRead`) · C.06/C.07/C.25/C.29/C.35 (`dvHgt`,
`dvSupp`, `dvSideSet`, `dvResPoly`, `IsDvPure`, pure-endpoint calculus) · B.04/B.05/B.06/
B32a/B35a (`dev` calculus) · C133mh0 (`twistRead_one`) · C133mh3 (`m1DigitFaithful`) ·
C118a/C131ae (`stageHeight_zero/one`, `smul_top_pos`).  **Status:** sorry-free, zero new
axiom, footprint Lean-core only — see the AxCheck footer.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C133mh5

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## Part 0 — D9 plumbing and `dev` helpers (private; standing convention) -/

/-- Local D9 reconstruction (C.04 exports no global instance; standing convention at
C.04/C.12/C.26/C.47/C.80/C.97/C133mh1/C133mh3). -/
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

/-- Every outer digit is a digit: `deg (dev Φ′ f j) < D′ = e₁f₁` (C.26/C133mh3's private twin). -/
private theorem natDegree_dev_lt_frame (F : KeyFrame O π) (f : Polynomial O) (j : ℕ) :
    (dev F.key f j).natDegree < F.e₁ * F.f₁ := by
  have hpos : 0 < F.key.natDegree := F.natDegree_key_pos
  have hlt : (dev F.key f j).degree < F.key.degree := degree_dev_lt F.hmonic hpos f j
  rw [← F.hdeg]
  rcases eq_or_ne (dev F.key f j) 0 with h0 | h0
  · rw [h0, Polynomial.natDegree_zero]; exact hpos
  · refine (Polynomial.natDegree_lt_iff_degree_lt h0).mpr ?_
    rwa [Polynomial.degree_eq_natDegree F.hmonic.ne_zero] at hlt

/-- `dev` is additive over finite sums (B32a's `dev_add_of_monic`, iterated). -/
private theorem dev_finsetSum {φ : Polynomial O} (hφ : φ.Monic) {ι : Type*} (s : Finset ι)
    (f : ι → Polynomial O) (j : ℕ) :
    dev φ (∑ i ∈ s, f i) j = ∑ i ∈ s, dev φ (f i) j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dev_of_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, dev_add_of_monic hφ, ih, Finset.sum_insert ha]

/-- The development of a key power is the delta family. -/
private theorem dev_key_pow (F : KeyFrame O π) (n j : ℕ) :
    dev F.key (F.key ^ n) j = if j = n then 1 else 0 := by
  have hone : F.key ^ n = 1 * F.key ^ n := (one_mul _).symm
  rcases lt_trichotomy j n with hlt | rfl | hgt
  · rw [if_neg (Nat.ne_of_lt hlt), hone]
    exact dev_mul_pow_of_lt F.hmonic n 1 j hlt
  · rw [if_pos rfl, hone]
    have hshift := dev_mul_pow F.hmonic j (1 : Polynomial O) 0
    rw [Nat.add_zero] at hshift
    rw [hshift, C130nv2.dev_zero_pin]
    exact (Polynomial.modByMonic_eq_self_iff F.hmonic).mpr
      (Polynomial.degree_lt_degree (by simpa using F.natDegree_key_pos))
  · rw [if_neg (Nat.ne_of_gt hgt), hone]
    obtain ⟨s, rfl⟩ : ∃ s, j = n + s := ⟨j - n, by omega⟩
    rw [dev_mul_pow F.hmonic n 1 s]
    refine dev_eq_zero_of_lt F.hmonic F.natDegree_key_pos 1 s ?_
    rw [Polynomial.natDegree_one]
    exact Nat.mul_pos (by omega) F.natDegree_key_pos

/-! ## Part 1 — the digit lift `twistLiftO` (§4.1's corrected supply) -/

/-- **The Λ digit.**  The public C131f stage lift fed the INVERSE-TWISTED target
`η^{q(M)}·κ` (§4.1 "[MHDISP 2026-08-27: corrected supply]"), so the C.22 twist cancels and
the ϖ-read returns `κ` exactly; the zero target lifts to the zero digit. -/
noncomputable def twistLiftO (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀) (M : ℕ)
    (κ : F.stageField H₀ hpin) : Polynomial O :=
  open Classical in
  if κ = 0 then 0
  else F.stageLiftO H₀ hpin M (F.stageLetter H₀ hpin ^ F.twistExp M * κ)

/-- ★ MH.5 digit clause 0 — the zero target lifts to the zero digit. -/
theorem twistLiftO_zero (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀) (M : ℕ) :
    twistLiftO F H₀ hpin M 0 = 0 := by
  rw [twistLiftO, if_pos rfl]

/-- ★ MH.5 digit clause 1 (degree) — every Λ digit is a digit: `deg < D′`. -/
theorem natDegree_twistLiftO_lt (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀) (M : ℕ)
    (κ : F.stageField H₀ hpin) :
    (twistLiftO F H₀ hpin M κ).natDegree < F.e₁ * F.f₁ := by
  rw [twistLiftO]
  split
  · simpa using Nat.mul_pos F.he₁ F.hf₁
  · exact F.natDegree_stageLiftO_lt H₀ hpin M _

/-- The ϖ-read of the zero polynomial vanishes at every height (C131aa's private helper,
made public: the off-slot supply for window read identities). -/
theorem twistRead_zero (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ) (hpin : F.Pin H₀)
    (k : ℕ) :
    F.twistRead H₀ hpin k (0 : Polynomial O) = 0 := by
  classical
  rw [KeyFrame.twistRead, KeyFrame.slotRes, Finset.sum_eq_zero]
  · simp
  intro t ht
  rw [Polynomial.coeff_zero, digAt_eq hπ (mul_zero (π ^
    ((k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁))).symm]
  simp

/-- ★ MH.5 digit clause 2 (height) — above the fullness threshold a nonzero target lifts at
EXACTLY the prescribed height. -/
theorem stageHeight_twistLiftO (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) {M : ℕ} (hM : F.e₁ * F.f₁ * F.h < M) {κ : F.stageField H₀ hpin}
    (hκ : κ ≠ 0) :
    F.stageHeight (twistLiftO F H₀ hpin M κ) = (M : ℕ∞) := by
  letI : Field (F.stageField H₀ hpin) := localFieldStageField F H₀ hpin
  have hη := F.stageLetter_ne_zero hπ H₀ hpin
  have htarget : F.stageLetter H₀ hpin ^ F.twistExp M * κ ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hη) hκ
  rw [twistLiftO, if_neg hκ]
  exact F.stageHeight_stageLiftO hπ H₀ hpin hM htarget

/-- ★ MH.5 digit clause 3 (the read identity) — the ϖ-read of the Λ digit is the target,
on the nose: the inverse twist in the supply cancels the C.22 twist exactly. -/
theorem twistRead_twistLiftO (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) {M : ℕ} (hM : F.e₁ * F.f₁ * F.h < M) (κ : F.stageField H₀ hpin) :
    F.twistRead H₀ hpin M (twistLiftO F H₀ hpin M κ) = κ := by
  letI : Field (F.stageField H₀ hpin) := localFieldStageField F H₀ hpin
  have hη := F.stageLetter_ne_zero hπ H₀ hpin
  rcases eq_or_ne κ 0 with rfl | hκ
  · rw [twistLiftO_zero]
    exact twistRead_zero F hπ H₀ hpin M
  · rw [twistLiftO, if_neg hκ]
    have hslot := F.slotRes_stageLiftO hπ H₀ hpin hM
      (F.stageLetter H₀ hpin ^ F.twistExp M * κ)
    rw [KeyFrame.twistRead, hslot, inv_pow]
    field_simp

/-! ## Part 2 — the Λ-window lift (§4.2's lift, no monic top) -/

/-- **The Λ-window lift.**  A residual-side polynomial `ψ` placed on the grade-`(ℓM₀ + uj₀)`
line: digit `t` at abscissa `j₀ + t·ℓ`, height `M₀ − u·t` (each term prices exactly
`ℓ(M₀ − ut) + u(j₀ + tℓ) = ℓM₀ + uj₀` on the `dv` lattice). -/
noncomputable def dvWindowLift (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    (u ℓ j₀ M₀ : ℕ) (ψ : Polynomial (F.stageField H₀ hpin)) : Polynomial O :=
  ∑ t ∈ Finset.range (ψ.natDegree + 1),
    twistLiftO F H₀ hpin (M₀ - u * t) (ψ.coeff t) * F.key ^ (j₀ + t * ℓ)

/-- ★ MH.5 window clause (slot support, on-grid) — the development of the window lift at
abscissa `j₀ + t·ℓ` is exactly the Λ digit of `ψ.coeff t`, for EVERY `t` (beyond the degree
both sides are `0`). -/
theorem dev_dvWindowLift (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ j₀ M₀ : ℕ} (hℓ : 0 < ℓ) (ψ : Polynomial (F.stageField H₀ hpin)) (t : ℕ) :
    dev F.key (dvWindowLift F H₀ hpin u ℓ j₀ M₀ ψ) (j₀ + t * ℓ)
      = twistLiftO F H₀ hpin (M₀ - u * t) (ψ.coeff t) := by
  classical
  have hterm : ∀ s : ℕ, s ≠ t →
      dev F.key (twistLiftO F H₀ hpin (M₀ - u * s) (ψ.coeff s) * F.key ^ (j₀ + s * ℓ))
        (j₀ + t * ℓ) = 0 := by
    intro s hst
    rcases lt_or_gt_of_ne hst with hlt | hgt
    · -- `s < t`: shift by `key^(j₀+sℓ)`, then the digit dies by degree
      have hle : s * ℓ ≤ t * ℓ := Nat.mul_le_mul_right ℓ (le_of_lt hlt)
      have hsplit : j₀ + t * ℓ = (j₀ + s * ℓ) + (t - s) * ℓ := by
        rw [Nat.sub_mul]; omega
      rw [hsplit, dev_mul_pow F.hmonic]
      refine dev_eq_zero_of_lt F.hmonic F.natDegree_key_pos _ _ ?_
      rw [F.hdeg]
      have h1 := natDegree_twistLiftO_lt F H₀ hpin (M₀ - u * s) (ψ.coeff s)
      have h2 : F.e₁ * F.f₁ ≤ (t - s) * ℓ * (F.e₁ * F.f₁) :=
        Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) hℓ)
      omega
    · -- `s > t`: the target abscissa sits strictly left of the shift
      have hlt' : j₀ + t * ℓ < j₀ + s * ℓ := by
        have := (Nat.mul_lt_mul_right hℓ).mpr hgt
        omega
      exact dev_mul_pow_of_lt F.hmonic _ _ _ hlt'
  have hmain : dev F.key
      (twistLiftO F H₀ hpin (M₀ - u * t) (ψ.coeff t) * F.key ^ (j₀ + t * ℓ)) (j₀ + t * ℓ)
      = twistLiftO F H₀ hpin (M₀ - u * t) (ψ.coeff t) := by
    have hshift := dev_mul_pow F.hmonic (j₀ + t * ℓ)
      (twistLiftO F H₀ hpin (M₀ - u * t) (ψ.coeff t)) 0
    rw [Nat.add_zero] at hshift
    rw [hshift, C130nv2.dev_zero_pin]
    refine (Polynomial.modByMonic_eq_self_iff F.hmonic).mpr ?_
    refine Polynomial.degree_lt_degree ?_
    rw [F.hdeg]
    exact natDegree_twistLiftO_lt F H₀ hpin _ _
  rw [dvWindowLift, dev_finsetSum F.hmonic]
  refine (Finset.sum_eq_single t (fun s _ hst => hterm s hst) ?_).trans hmain
  intro hnt
  have htdeg : ψ.natDegree < t := by
    by_contra hcon
    exact hnt (Finset.mem_range.mpr (by omega))
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt htdeg, twistLiftO_zero, zero_mul]
  exact dev_of_zero F.key _

/-- ★ MH.5 window clause (slot support, off-grid) — off the arithmetic progression
`j₀ + ℓℕ` every development digit of the window lift vanishes. -/
theorem dev_dvWindowLift_off (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ j₀ M₀ : ℕ} (ψ : Polynomial (F.stageField H₀ hpin)) {j : ℕ}
    (hj : ∀ t : ℕ, j ≠ j₀ + t * ℓ) :
    dev F.key (dvWindowLift F H₀ hpin u ℓ j₀ M₀ ψ) j = 0 := by
  classical
  rw [dvWindowLift, dev_finsetSum F.hmonic]
  refine Finset.sum_eq_zero fun s _ => ?_
  rcases lt_or_ge j (j₀ + s * ℓ) with hlt | hge
  · exact dev_mul_pow_of_lt F.hmonic _ _ _ hlt
  · obtain ⟨r, hr⟩ : ∃ r, j = (j₀ + s * ℓ) + r := ⟨j - (j₀ + s * ℓ), by omega⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact hj s (by omega)
    rw [hr, dev_mul_pow F.hmonic]
    refine dev_eq_zero_of_lt F.hmonic F.natDegree_key_pos _ _ ?_
    rw [F.hdeg]
    have h1 := natDegree_twistLiftO_lt F H₀ hpin (M₀ - u * s) (ψ.coeff s)
    have h2 : F.e₁ * F.f₁ ≤ r * (F.e₁ * F.f₁) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega

/-- ★ MH.5 window clause (degree, master bound) — the window lift lives strictly below
`(j₀ + deg ψ·ℓ + 1)·D′`. -/
theorem natDegree_dvWindowLift_lt (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    (u ℓ j₀ M₀ : ℕ) (ψ : Polynomial (F.stageField H₀ hpin)) :
    (dvWindowLift F H₀ hpin u ℓ j₀ M₀ ψ).natDegree
      < (j₀ + ψ.natDegree * ℓ + 1) * (F.e₁ * F.f₁) := by
  have hpos : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  have h5 : 0 < (j₀ + ψ.natDegree * ℓ + 1) * (F.e₁ * F.f₁) :=
    Nat.mul_pos (by omega) hpos
  have hbound : (dvWindowLift F H₀ hpin u ℓ j₀ M₀ ψ).natDegree
      ≤ (j₀ + ψ.natDegree * ℓ + 1) * (F.e₁ * F.f₁) - 1 := by
    rw [dvWindowLift]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun t ht => ?_
    have ht' : t ≤ ψ.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    have h1 : (twistLiftO F H₀ hpin (M₀ - u * t) (ψ.coeff t)
        * F.key ^ (j₀ + t * ℓ)).natDegree
        ≤ (twistLiftO F H₀ hpin (M₀ - u * t) (ψ.coeff t)).natDegree
          + (j₀ + t * ℓ) * (F.e₁ * F.f₁) := by
      refine le_trans Polynomial.natDegree_mul_le ?_
      rw [Polynomial.natDegree_pow, F.hdeg]
    have h2 := natDegree_twistLiftO_lt F H₀ hpin (M₀ - u * t) (ψ.coeff t)
    have h3 : (j₀ + t * ℓ) * (F.e₁ * F.f₁)
        ≤ (j₀ + ψ.natDegree * ℓ) * (F.e₁ * F.f₁) := by
      refine Nat.mul_le_mul_right _ ?_
      have := Nat.mul_le_mul_right ℓ ht'
      omega
    have h4 : (j₀ + ψ.natDegree * ℓ + 1) * (F.e₁ * F.f₁)
        = (j₀ + ψ.natDegree * ℓ) * (F.e₁ * F.f₁) + F.e₁ * F.f₁ := by ring
    omega
  omega

/-- ★ MH.5 window clause (degree, the Lemma-S window): with the offset below `ℓ` and
`deg ψ < a`, the lift stays strictly below `ℓ·a·D′` — §4.2's `deg U < deg p₁`. -/
theorem natDegree_dvWindowLift_lt' (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ j₀ M₀ a : ℕ} (hj₀ : j₀ < ℓ) (ψ : Polynomial (F.stageField H₀ hpin))
    (ha : ψ.natDegree < a) :
    (dvWindowLift F H₀ hpin u ℓ j₀ M₀ ψ).natDegree < ℓ * (a * (F.e₁ * F.f₁)) := by
  have h := natDegree_dvWindowLift_lt F H₀ hpin u ℓ j₀ M₀ ψ
  have h3 : j₀ + ψ.natDegree * ℓ + 1 ≤ a * ℓ := by
    have h4 : ψ.natDegree * ℓ ≤ (a - 1) * ℓ := Nat.mul_le_mul_right ℓ (by omega)
    have h4' : (a - 1) * ℓ = a * ℓ - 1 * ℓ := Nat.sub_mul a 1 ℓ
    have h4'' : ℓ ≤ a * ℓ := Nat.le_mul_of_pos_left ℓ (by omega)
    omega
  have h5 : (j₀ + ψ.natDegree * ℓ + 1) * (F.e₁ * F.f₁)
      ≤ ℓ * (a * (F.e₁ * F.f₁)) := by
    calc (j₀ + ψ.natDegree * ℓ + 1) * (F.e₁ * F.f₁)
        ≤ (a * ℓ) * (F.e₁ * F.f₁) := Nat.mul_le_mul_right _ h3
      _ = ℓ * (a * (F.e₁ * F.f₁)) := by ring
  omega

/-- ★ MH.5 window clause (height) — the pinned W-height: the window lift prices at or above
its grade `ℓ·M₀ + u·j₀` (with equality at any nonzero slot; `≥` is what §4.2 consumes). -/
theorem le_dvSupp_dvWindowLift (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) {u ℓ j₀ M₀ : ℕ} (hℓ : 0 < ℓ)
    (ψ : Polynomial (F.stageField H₀ hpin))
    (hfull : F.e₁ * F.f₁ * F.h + u * ψ.natDegree < M₀) :
    ((ℓ * M₀ + u * j₀ : ℕ) : ℕ∞) ≤ dvSupp F (dvWindowLift F H₀ hpin u ℓ j₀ M₀ ψ) u ℓ := by
  classical
  rw [dvSupp]
  refine Finset.le_inf fun j _ => ?_
  by_cases hgrid : ∃ t : ℕ, j = j₀ + t * ℓ
  · obtain ⟨t, rfl⟩ := hgrid
    rw [dvHgt, dev_dvWindowLift F H₀ hpin hℓ ψ t]
    by_cases hct : ψ.coeff t = 0
    · rw [hct, twistLiftO_zero, C118a.stageHeight_zero, C118a.smul_top_pos hℓ, top_add]
      exact le_top
    · have htdeg : t ≤ ψ.natDegree := by
        by_contra hcon
        exact hct (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
      have hMt : F.e₁ * F.f₁ * F.h < M₀ - u * t := by
        have := Nat.mul_le_mul_left u htdeg
        omega
      rw [stageHeight_twistLiftO F hπ H₀ hpin hMt hct]
      have h4 : u * t ≤ M₀ := by omega
      have h5 : ℓ * (u * t) ≤ ℓ * M₀ := Nat.mul_le_mul_left ℓ h4
      have hn : ℓ * M₀ + u * j₀ = ℓ * (M₀ - u * t) + u * (j₀ + t * ℓ) := by
        have h1 : ℓ * (M₀ - u * t) = ℓ * M₀ - ℓ * (u * t) := Nat.mul_sub ℓ M₀ (u * t)
        have h2 : u * (j₀ + t * ℓ) = u * j₀ + ℓ * (u * t) := by ring
        omega
      have hweight : ((ℓ * M₀ + u * j₀ : ℕ) : ℕ∞)
          = ℓ • (((M₀ - u * t : ℕ) : ℕ∞)) + (u * (j₀ + t * ℓ) : ℕ∞) := by
        simpa [nsmul_eq_mul] using congrArg (fun n : ℕ => (n : ℕ∞)) hn
      exact hweight.le
  · rw [dvHgt, dev_dvWindowLift_off F H₀ hpin ψ (fun t ht => hgrid ⟨t, ht⟩),
      C118a.stageHeight_zero, C118a.smul_top_pos hℓ, top_add]
    exact le_top

/-- ★ MH.5 window clause (the read identity) — the grade-line ϖ-read of the window lift
returns `ψ` slotwise: at abscissa `j₀ + t·ℓ` and height `M₀ − u·t` the read is `ψ.coeff t`,
for EVERY `t`. -/
theorem twistRead_dvWindowLift (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) {u ℓ j₀ M₀ : ℕ} (hℓ : 0 < ℓ)
    (ψ : Polynomial (F.stageField H₀ hpin))
    (hfull : F.e₁ * F.f₁ * F.h + u * ψ.natDegree < M₀) (t : ℕ) :
    F.twistRead H₀ hpin (M₀ - u * t)
        (dev F.key (dvWindowLift F H₀ hpin u ℓ j₀ M₀ ψ) (j₀ + t * ℓ))
      = ψ.coeff t := by
  rw [dev_dvWindowLift F H₀ hpin hℓ ψ t]
  by_cases hct : ψ.coeff t = 0
  · rw [hct, twistLiftO_zero]
    exact twistRead_zero F hπ H₀ hpin _
  · have htdeg : t ≤ ψ.natDegree := by
      by_contra hcon
      exact hct (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
    have hMt : F.e₁ * F.f₁ * F.h < M₀ - u * t := by
      have := Nat.mul_le_mul_left u htdeg
      omega
    exact twistRead_twistLiftO F hπ H₀ hpin hMt _

/-! ## Part 3 — the monic-top side lift Λ(P) (§4.1's initialization, §4.4's consumer) -/

/-- **The side lift Λ(P) := Φ′^{dℓ} + Σ_{t<d} B_t·Φ′^{tℓ}** (§4.1): the monic-top variant,
with the sub-top digits supplied by the window lift of `P.eraseLead` at offset `0` and top
height `M₀ = u·d`. -/
noncomputable def dvSideLift (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    (u ℓ : ℕ) (P : Polynomial (F.stageField H₀ hpin)) : Polynomial O :=
  F.key ^ (P.natDegree * ℓ)
    + dvWindowLift F H₀ hpin u ℓ 0 (u * P.natDegree) P.eraseLead

/-- Fullness at every sub-top slot, from the strict floor: `D′h < u ≤ u(d−t)`. -/
private theorem slot_full (F : KeyFrame O π) {u ℓ d t : ℕ} (hℓ : 0 < ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u) (ht : t < d) :
    F.e₁ * F.f₁ * F.h < u * (d - t) := by
  have h1 : F.e₁ * F.f₁ * F.h ≤ ℓ * (F.e₁ * F.f₁ * F.h) :=
    Nat.le_mul_of_pos_left _ hℓ
  have h2 : u ≤ u * (d - t) := Nat.le_mul_of_pos_right u (by omega)
  omega

/-- The window part of `Λ(P)` sits strictly below the monic top. -/
private theorem window_degree_lt (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (P : Polynomial (F.stageField H₀ hpin))
    (hd : 0 < P.natDegree) :
    (dvWindowLift F H₀ hpin u ℓ 0 (u * P.natDegree) P.eraseLead).degree
      < (F.key ^ (P.natDegree * ℓ)).degree := by
  refine Polynomial.degree_lt_degree ?_
  rw [Polynomial.natDegree_pow, F.hdeg]
  have h1 := natDegree_dvWindowLift_lt F H₀ hpin u ℓ 0 (u * P.natDegree) P.eraseLead
  have he : P.eraseLead.natDegree ≤ P.natDegree - 1 := Polynomial.eraseLead_natDegree_le P
  have h2 : 0 + P.eraseLead.natDegree * ℓ + 1 ≤ P.natDegree * ℓ := by
    have h3 : P.eraseLead.natDegree * ℓ ≤ (P.natDegree - 1) * ℓ := Nat.mul_le_mul_right ℓ he
    have h4 : (P.natDegree - 1) * ℓ = P.natDegree * ℓ - 1 * ℓ := Nat.sub_mul _ 1 ℓ
    have h5 : ℓ ≤ P.natDegree * ℓ := Nat.le_mul_of_pos_left ℓ hd
    omega
  have h6 : (0 + P.eraseLead.natDegree * ℓ + 1) * (F.e₁ * F.f₁)
      ≤ P.natDegree * ℓ * (F.e₁ * F.f₁) := Nat.mul_le_mul_right _ h2
  omega

/-- ★ MH.5 Λ clause 2a (top digit) — `dev Λ(P) (dℓ) = 1`. -/
theorem dev_dvSideLift_top (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (P : Polynomial (F.stageField H₀ hpin)) :
    dev F.key (dvSideLift F H₀ hpin u ℓ P) (P.natDegree * ℓ) = 1 := by
  rw [dvSideLift, dev_add_of_monic F.hmonic, dev_key_pow, if_pos rfl]
  have hw := dev_dvWindowLift F H₀ hpin (u := u) (j₀ := 0) (M₀ := u * P.natDegree) hℓ P.eraseLead P.natDegree
  rw [zero_add] at hw
  rw [hw, Polynomial.eraseLead_coeff, if_pos rfl, twistLiftO_zero, add_zero]

/-- ★ MH.5 Λ clause 2b (slot digits) — below the top, `dev Λ(P) (tℓ)` is the Λ digit of
`P.coeff t` at height `u(d−t)`. -/
theorem dev_dvSideLift_slot (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (P : Polynomial (F.stageField H₀ hpin)) {t : ℕ}
    (ht : t < P.natDegree) :
    dev F.key (dvSideLift F H₀ hpin u ℓ P) (t * ℓ)
      = twistLiftO F H₀ hpin (u * (P.natDegree - t)) (P.coeff t) := by
  rw [dvSideLift, dev_add_of_monic F.hmonic, dev_key_pow]
  have hne : t * ℓ ≠ P.natDegree * ℓ := by
    intro he
    exact absurd (Nat.eq_of_mul_eq_mul_right hℓ he) (by omega)
  rw [if_neg hne, zero_add]
  have hw := dev_dvWindowLift F H₀ hpin (u := u) (j₀ := 0) (M₀ := u * P.natDegree) hℓ P.eraseLead t
  rw [zero_add] at hw
  rw [hw, Polynomial.eraseLead_coeff, if_neg (Nat.ne_of_lt ht)]
  congr 1
  rw [Nat.mul_sub]

/-- ★ MH.5 Λ clause 2c (past the top) — grid digits beyond `dℓ` vanish. -/
theorem dev_dvSideLift_past (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (P : Polynomial (F.stageField H₀ hpin)) {t : ℕ}
    (ht : P.natDegree < t) :
    dev F.key (dvSideLift F H₀ hpin u ℓ P) (t * ℓ) = 0 := by
  rw [dvSideLift, dev_add_of_monic F.hmonic, dev_key_pow]
  have hne : t * ℓ ≠ P.natDegree * ℓ := by
    intro he
    exact absurd (Nat.eq_of_mul_eq_mul_right hℓ he) (by omega)
  rw [if_neg hne, zero_add]
  have hw := dev_dvWindowLift F H₀ hpin (u := u) (j₀ := 0) (M₀ := u * P.natDegree) hℓ P.eraseLead t
  rw [zero_add] at hw
  rw [hw, Polynomial.eraseLead_coeff, if_neg (by omega : t ≠ P.natDegree),
    Polynomial.coeff_eq_zero_of_natDegree_lt ht, twistLiftO_zero]

/-- ★ MH.5 Λ clause 2d (off-grid) — off the progression `ℓℕ` every digit vanishes. -/
theorem dev_dvSideLift_off (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} (P : Polynomial (F.stageField H₀ hpin)) {j : ℕ}
    (hj : ∀ t : ℕ, j ≠ t * ℓ) :
    dev F.key (dvSideLift F H₀ hpin u ℓ P) j = 0 := by
  rw [dvSideLift, dev_add_of_monic F.hmonic, dev_key_pow,
    if_neg (hj P.natDegree), zero_add]
  refine dev_dvWindowLift_off F H₀ hpin P.eraseLead fun t => ?_
  simpa using hj t

/-- ★ MH.5 Λ clause 1 (monic) — `Λ(P)` is monic. -/
theorem dvSideLift_monic (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (P : Polynomial (F.stageField H₀ hpin))
    (hd : 0 < P.natDegree) :
    (dvSideLift F H₀ hpin u ℓ P).Monic :=
  (F.hmonic.pow (P.natDegree * ℓ)).add_of_left (window_degree_lt F H₀ hpin hℓ P hd)

/-- ★ MH.5 Λ clause 1 (degree) — `deg Λ(P) = ℓ·d·D′` (written `d·ℓ·D′`). -/
theorem natDegree_dvSideLift (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (P : Polynomial (F.stageField H₀ hpin))
    (hd : 0 < P.natDegree) :
    (dvSideLift F H₀ hpin u ℓ P).natDegree = P.natDegree * ℓ * (F.e₁ * F.f₁) := by
  have hdeq : (dvSideLift F H₀ hpin u ℓ P).degree
      = (F.key ^ (P.natDegree * ℓ)).degree := by
    rw [dvSideLift]
    exact Polynomial.degree_add_eq_left_of_degree_lt (window_degree_lt F H₀ hpin hℓ P hd)
  rw [Polynomial.natDegree_eq_of_degree_eq hdeq, Polynomial.natDegree_pow, F.hdeg]

/-- ★ MH.5 Λ clause 2 (heights, top) — the top digit sits at height `0`. -/
theorem dvHgt_dvSideLift_top (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (P : Polynomial (F.stageField H₀ hpin)) :
    dvHgt F (dvSideLift F H₀ hpin u ℓ P) (P.natDegree * ℓ) = 0 := by
  rw [dvHgt, dev_dvSideLift_top F H₀ hpin hℓ P, C131ae.stageHeight_one]

/-- ★ MH.5 Λ clause 2 (heights, slots) — a surviving slot sits at height EXACTLY `u(d−t)`. -/
theorem dvHgt_dvSideLift_slot (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) {u ℓ : ℕ} (hℓ : 0 < ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u) (P : Polynomial (F.stageField H₀ hpin))
    {t : ℕ} (ht : t < P.natDegree) (hc : P.coeff t ≠ 0) :
    dvHgt F (dvSideLift F H₀ hpin u ℓ P) (t * ℓ) = ((u * (P.natDegree - t) : ℕ) : ℕ∞) := by
  rw [dvHgt, dev_dvSideLift_slot F H₀ hpin hℓ P ht]
  exact stageHeight_twistLiftO F hπ H₀ hpin (slot_full F hℓ hfloor ht) hc

/-- ★ MH.5 Λ clause 2 (heights, dead slots) — where `P.coeff t = 0` the height is `⊤`. -/
theorem dvHgt_dvSideLift_slot_top (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (P : Polynomial (F.stageField H₀ hpin))
    {t : ℕ} (ht : t < P.natDegree) (hc : P.coeff t = 0) :
    dvHgt F (dvSideLift F H₀ hpin u ℓ P) (t * ℓ) = ⊤ := by
  rw [dvHgt, dev_dvSideLift_slot F H₀ hpin hℓ P ht, hc, twistLiftO_zero,
    C118a.stageHeight_zero]

/-- ★ MH.5 Λ clause 4 (the weight pin) — `W(Λ(P)) = ℓ·(u·d)` exactly (§4.1's `uℓd`). -/
theorem dvSupp_dvSideLift (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) {u ℓ : ℕ} (hℓ : 0 < ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u) (P : Polynomial (F.stageField H₀ hpin))
    (hd : 0 < P.natDegree) :
    dvSupp F (dvSideLift F H₀ hpin u ℓ P) u ℓ = ((ℓ * (u * P.natDegree) : ℕ) : ℕ∞) := by
  classical
  have hDpos : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  have hnatdeg := natDegree_dvSideLift F H₀ hpin (u := u) hℓ P hd
  have htopmul : ℓ • (⊤ : ℕ∞) = ⊤ := C118a.smul_top_pos hℓ
  have hweight : ∀ t : ℕ, t ≤ P.natDegree →
      ((ℓ * (u * P.natDegree) : ℕ) : ℕ∞)
        = ℓ • (((u * (P.natDegree - t) : ℕ) : ℕ∞)) + (u * (t * ℓ) : ℕ∞) := by
    intro t ht
    have hn : ℓ * (u * P.natDegree) = ℓ * (u * (P.natDegree - t)) + u * (t * ℓ) := by
      have h1 : u * (P.natDegree - t) = u * P.natDegree - u * t := Nat.mul_sub u _ t
      have h2 : ℓ * (u * P.natDegree - u * t)
          = ℓ * (u * P.natDegree) - ℓ * (u * t) := Nat.mul_sub ℓ _ _
      have h3 : u * (t * ℓ) = ℓ * (u * t) := by ring
      have h4 : u * t ≤ u * P.natDegree := Nat.mul_le_mul_left u ht
      have h5 : ℓ * (u * t) ≤ ℓ * (u * P.natDegree) := Nat.mul_le_mul_left ℓ h4
      rw [h1, h2, h3]
      omega
    simpa [nsmul_eq_mul] using congrArg (fun n : ℕ => (n : ℕ∞)) hn
  rw [dvSupp]
  apply le_antisymm
  · -- ≤ : attained at the monic top slot `dℓ`
    have hmem : P.natDegree * ℓ
        ∈ Finset.range ((dvSideLift F H₀ hpin u ℓ P).natDegree + 1) := by
      rw [hnatdeg]
      refine Finset.mem_range.mpr ?_
      have := Nat.le_mul_of_pos_right (P.natDegree * ℓ) hDpos
      omega
    refine le_trans (Finset.inf_le hmem) ?_
    rw [dvHgt_dvSideLift_top F H₀ hpin hℓ P, smul_zero, zero_add]
    exact le_of_eq (by push_cast; ring)
  · -- ≥ : every abscissa prices at or above the line
    refine Finset.le_inf fun b _ => ?_
    by_cases hgrid : ∃ t : ℕ, b = t * ℓ
    · obtain ⟨t, rfl⟩ := hgrid
      rcases lt_trichotomy t P.natDegree with hlt | rfl | hgt
      · by_cases hc : P.coeff t = 0
        · rw [dvHgt_dvSideLift_slot_top F H₀ hpin hℓ P hlt hc, htopmul, top_add]
          exact le_top
        · rw [dvHgt_dvSideLift_slot F hπ H₀ hpin hℓ hfloor P hlt hc]
          exact (hweight t hlt.le).le
      · rw [dvHgt_dvSideLift_top F H₀ hpin hℓ P, smul_zero, zero_add]
        exact le_of_eq (by push_cast; ring)
      · rw [dvHgt, dev_dvSideLift_past F H₀ hpin hℓ P hgt, C118a.stageHeight_zero,
          htopmul, top_add]
        exact le_top
    · rw [dvHgt, dev_dvSideLift_off F H₀ hpin P (fun t ht => hgrid ⟨t, ht⟩),
        C118a.stageHeight_zero, htopmul, top_add]
      exact le_top

/-- ★ MH.5 Λ clause 3 (purity) — `Λ(P)` is one-sided at slope `u/ℓ` (left endpoint from
`P.coeff 0 ≠ 0`, top from monicity). -/
theorem isDvPure_dvSideLift (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) {u ℓ : ℕ} (hℓ : 0 < ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u) (P : Polynomial (F.stageField H₀ hpin))
    (hd : 0 < P.natDegree) (hP0 : P.coeff 0 ≠ 0) :
    IsDvPure F (dvSideLift F H₀ hpin u ℓ P) u ℓ := by
  classical
  have hDpos : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  have hnatdeg := natDegree_dvSideLift F H₀ hpin (u := u) hℓ P hd
  have hsupp := dvSupp_dvSideLift F hπ H₀ hpin hℓ hfloor P hd
  have h0 : dvHgt F (dvSideLift F H₀ hpin u ℓ P) 0 = ((u * P.natDegree : ℕ) : ℕ∞) := by
    have h := dvHgt_dvSideLift_slot F hπ H₀ hpin hℓ hfloor P hd hP0
    rwa [Nat.zero_mul, Nat.sub_zero] at h
  have hquot : (dvSideLift F H₀ hpin u ℓ P).natDegree / (F.e₁ * F.f₁)
      = P.natDegree * ℓ := by
    rw [hnatdeg]
    exact Nat.mul_div_cancel _ hDpos
  rw [IsDvPure, hquot]
  constructor
  · simp only [dvSideSet, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_, ?_⟩
    · rw [hsupp, h0]
      push_cast [nsmul_eq_mul]
      ring
    · rw [h0]
      exact ENat.coe_ne_top _
  · simp only [dvSideSet, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ?_, ?_⟩
    · rw [hnatdeg]
      have := Nat.le_mul_of_pos_right (P.natDegree * ℓ) hDpos
      omega
    · rw [hsupp, dvHgt_dvSideLift_top F H₀ hpin hℓ P]
      push_cast [nsmul_eq_mul]
      ring
    · rw [dvHgt_dvSideLift_top F H₀ hpin hℓ P]
      exact ENat.coe_ne_top 0

/-- The side witness for `Λ(P)` (packaged for `dvResPoly` consumers). -/
theorem dvSideSet_dvSideLift_nonempty (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) {u ℓ : ℕ} (hℓ : 0 < ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u) (P : Polynomial (F.stageField H₀ hpin))
    (hd : 0 < P.natDegree) (hP0 : P.coeff 0 ≠ 0) :
    (dvSideSet F (dvSideLift F H₀ hpin u ℓ P) u ℓ).Nonempty :=
  ⟨0, (isDvPure_dvSideLift F hπ H₀ hpin hℓ hfloor P hd hP0).1⟩

/-- ★ MH.5 Λ clause 4 (the `M₀` pin) — the left-endpoint height is `u·d` (§4.1's `M₀`),
for EVERY side witness. -/
theorem dvHgt_dvSideLift_sideMin (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) {u ℓ : ℕ} (hℓ : 0 < ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u) (P : Polynomial (F.stageField H₀ hpin))
    (hd : 0 < P.natDegree) (hP0 : P.coeff 0 ≠ 0)
    (hne : (dvSideSet F (dvSideLift F H₀ hpin u ℓ P) u ℓ).Nonempty) :
    dvHgt F (dvSideLift F H₀ hpin u ℓ P)
        (dvSideMin F (dvSideLift F H₀ hpin u ℓ P) u ℓ hne)
      = ((u * P.natDegree : ℕ) : ℕ∞) := by
  have hpure := isDvPure_dvSideLift F hπ H₀ hpin hℓ hfloor P hd hP0
  rw [dvSideMin_eq_zero_of_isDvPure hpure hne]
  have h := dvHgt_dvSideLift_slot F hπ H₀ hpin hℓ hfloor P hd hP0
  rwa [Nat.zero_mul, Nat.sub_zero] at h

/-- ★ MH.5 Λ clause 5 (the residual identity) — **`R(Λ(P)) = P` exactly**, for every side
witness and finite pin (C131aa's `dvResPoly_testKey`, generalized from `L.r` to every monic
`P` with nonzero constant term). -/
theorem dvResPoly_dvSideLift (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) {u ℓ : ℕ} (hh : 0 < F.h) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u) (P : Polynomial (F.stageField H₀ hpin))
    (hPm : P.Monic) (hd : 0 < P.natDegree) (hP0 : P.coeff 0 ≠ 0)
    (hne : (dvSideSet F (dvSideLift F H₀ hpin u ℓ P) u ℓ).Nonempty) (M₀ : ℕ)
    (hp : dvHgt F (dvSideLift F H₀ hpin u ℓ P)
        (dvSideMin F (dvSideLift F H₀ hpin u ℓ P) u ℓ hne) = (M₀ : ℕ∞)) :
    dvResPoly F H₀ hpin (dvSideLift F H₀ hpin u ℓ P) u ℓ hne M₀ hp = P := by
  classical
  have hDpos : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  have hpure := isDvPure_dvSideLift F hπ H₀ hpin hℓ hfloor P hd hP0
  have hmin : dvSideMin F (dvSideLift F H₀ hpin u ℓ P) u ℓ hne = 0 :=
    dvSideMin_eq_zero_of_isDvPure hpure hne
  have hnatdeg := natDegree_dvSideLift F H₀ hpin (u := u) hℓ P hd
  have hquot : (dvSideLift F H₀ hpin u ℓ P).natDegree / (F.e₁ * F.f₁)
      = P.natDegree * ℓ := by
    rw [hnatdeg]
    exact Nat.mul_div_cancel _ hDpos
  have hside := natDegree_div_eq_of_isDvPure hℓ hcop hpure hne
  rw [hquot] at hside
  have hsideDeg : dvSideDeg F (dvSideLift F H₀ hpin u ℓ P) u ℓ hne = P.natDegree := by
    have h' : ℓ * dvSideDeg F (dvSideLift F H₀ hpin u ℓ P) u ℓ hne
        = ℓ * P.natDegree := by rw [← hside, Nat.mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hℓ h'
  have h0 : dvHgt F (dvSideLift F H₀ hpin u ℓ P) 0 = ((u * P.natDegree : ℕ) : ℕ∞) := by
    have h := dvHgt_dvSideLift_slot F hπ H₀ hpin hℓ hfloor P hd hP0
    rwa [Nat.zero_mul, Nat.sub_zero] at h
  have hM : M₀ = u * P.natDegree := by
    have hc : (M₀ : ℕ∞) = ((u * P.natDegree : ℕ) : ℕ∞) := by
      rw [← hp, hmin, h0]
    exact_mod_cast hc
  apply Polynomial.ext
  intro t
  rw [dvResPoly, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow, hsideDeg]
  by_cases ht : t ≤ P.natDegree
  · rw [if_pos (Nat.lt_succ_of_le ht), hmin, zero_add, hM]
    rcases eq_or_lt_of_le ht with rfl | htlt
    · rw [show u * P.natDegree - P.natDegree * u = 0 by
        rw [Nat.mul_comm P.natDegree u]; omega]
      rw [dev_dvSideLift_top F H₀ hpin hℓ P, C133mh0.twistRead_one F H₀ hpin hh]
      exact hPm.coeff_natDegree.symm
    · rw [dev_dvSideLift_slot F H₀ hpin hℓ P htlt,
        show u * P.natDegree - t * u = u * (P.natDegree - t) by
          rw [Nat.mul_sub, Nat.mul_comm t u]]
      exact twistRead_twistLiftO F hπ H₀ hpin (slot_full F hℓ hfloor htlt) _
  · rw [if_neg (by omega), P.coeff_eq_zero_of_natDegree_lt (by omega)]

/-! ## Part 4 — window read-faithfulness (MH.0b's window half; Lemma S's closing step) -/

/-- ★ **Window read-faithfulness** — `W(f) ≥ c` and all grade-`c` line reads zero force
`W(f) ≥ c + 1` (the cleared weight is integer-valued, so `> c` is `≥ c+1`).  Unconditional,
through the landed digit faithfulness `C133mh3.m1DigitFaithful`. -/
theorem le_dvSupp_succ_of_lineReads_eq_zero (F : KeyFrame O π) (hπ : Irreducible π)
    (hh : 0 < F.h) (H₀ : ℕ) (hpin : F.Pin H₀) {u ℓ : ℕ} (hℓ : 0 < ℓ)
    {f : Polynomial O} {c : ℕ}
    (hW : ((c : ℕ) : ℕ∞) ≤ dvSupp F f u ℓ)
    (hreads : ∀ j k : ℕ, ℓ * k + u * j = c → dvHgt F f j = (k : ℕ∞) →
      F.twistRead H₀ hpin k (dev F.key f j) = 0) :
    ((c + 1 : ℕ) : ℕ∞) ≤ dvSupp F f u ℓ := by
  classical
  by_contra hcon
  rw [not_le] at hcon
  rcases eq_or_ne (dvSupp F f u ℓ) ⊤ with hT | hT
  · rw [hT] at hcon
    exact absurd hcon not_top_lt
  obtain ⟨S, hS⟩ := ENat.ne_top_iff_exists.1 hT
  rw [← hS] at hcon hW
  have h1 : S < c + 1 := by exact_mod_cast hcon
  have h2 : c ≤ S := by exact_mod_cast hW
  have hSc : S = c := by omega
  -- the support is attained on the finite window
  rw [dvSupp] at hS
  obtain ⟨j, _, hjinf⟩ := Finset.exists_mem_eq_inf (Finset.range (f.natDegree + 1))
    Finset.nonempty_range_add_one (fun j => ℓ • dvHgt F f j + (u * j : ℕ∞))
  have hjeq : ℓ • dvHgt F f j + (u * j : ℕ∞) = ((c : ℕ) : ℕ∞) := by
    rw [← hjinf, ← hS, hSc]
  have hne : dvHgt F f j ≠ ⊤ := by
    intro hTj
    rw [hTj, C118a.smul_top_pos hℓ, top_add] at hjeq
    exact (ENat.top_ne_coe (c : ℕ)) hjeq
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hne
  have hline : ℓ * k + u * j = c := by
    have hcast : ((ℓ * k + u * j : ℕ) : ℕ∞) = ((c : ℕ) : ℕ∞) := by
      rw [← hjeq, ← hk]
      push_cast [nsmul_eq_mul]
      ring
    exact_mod_cast hcast
  exact C133mh3.m1DigitFaithful π F hπ hh H₀ hpin (dev F.key f j)
    (natDegree_dev_lt_frame F f j) k hk.symm (hreads j k hline hk.symm)

/-! ## Part 5 — the Bézout solve with degree control (MH.7 prefix, §4.2) -/

/-- ★ **Bézout with degree control, existence** (§4.2's K-linear solve, solved form): for
coprime `G, H` with `G` monic, every `E` below the joint degree decomposes as
`E = H·Ū + G·V̄` inside the degree windows. -/
theorem exists_bezout_degree_lt {K : Type*} [Field K] {G H : Polynomial K}
    (hG : G.Monic) (hH : H.Monic) (hcop : IsCoprime G H) (E : Polynomial K)
    (hE : E.degree < G.degree + H.degree) :
    ∃ U V : Polynomial K, U.degree < G.degree ∧ V.degree < H.degree ∧
      H * U + G * V = E := by
  obtain ⟨a, b, hab⟩ := hcop
  have hmod : (E * b) %ₘ G + G * ((E * b) /ₘ G) = E * b :=
    Polynomial.modByMonic_add_div (E * b) G
  have hUdeg : ((E * b) %ₘ G).degree < G.degree := Polynomial.degree_modByMonic_lt (E * b) hG
  have hGbot : G.degree ≠ ⊥ := fun hbot => hG.ne_zero (Polynomial.degree_eq_bot.mp hbot)
  have hHbot : H.degree ≠ ⊥ := fun hbot => hH.ne_zero (Polynomial.degree_eq_bot.mp hbot)
  refine ⟨(E * b) %ₘ G, E * a + H * ((E * b) /ₘ G), hUdeg, ?_, ?_⟩
  · -- the second window, by degree cancellation on `G·V = E − H·U`
    by_cases hV0 : E * a + H * ((E * b) /ₘ G) = 0
    · rw [hV0, Polynomial.degree_zero]
      exact bot_lt_iff_ne_bot.mpr hHbot
    · have hGV : G * (E * a + H * ((E * b) /ₘ G)) = E - H * ((E * b) %ₘ G) := by
        linear_combination E * hab + H * hmod
      have hHU : (H * ((E * b) %ₘ G)).degree < G.degree + H.degree := by
        rcases eq_or_ne ((E * b) %ₘ G) 0 with hz | hz
        · rw [hz, mul_zero, Polynomial.degree_zero]
          refine bot_lt_iff_ne_bot.mpr fun hbot => ?_
          rcases WithBot.add_eq_bot.mp hbot with h | h
          · exact hGbot h
          · exact hHbot h
        · rw [Polynomial.degree_mul, add_comm G.degree H.degree]
          exact WithBot.add_lt_add_left hHbot hUdeg
      have hdegsub : (E - H * ((E * b) %ₘ G)).degree < G.degree + H.degree :=
        lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hE hHU)
      have hdegGV : G.degree + (E * a + H * ((E * b) /ₘ G)).degree
          < G.degree + H.degree := by
        rw [← Polynomial.degree_mul, hGV]
        exact hdegsub
      exact (WithBot.add_lt_add_iff_left hGbot).mp hdegGV
  · linear_combination H * hmod + E * hab

/-- ★ **Bézout with degree control, uniqueness** (the injectivity half of §4.2's bijection:
`H·Ū = −G·V̄` forces `G ∣ Ū` by coprimality, then `Ū = 0` by degree). -/
theorem bezout_degree_lt_unique {K : Type*} [Field K] {G H U V U' V' : Polynomial K}
    (hG : G.Monic) (hcop : IsCoprime G H)
    (hU : U.degree < G.degree) (hU' : U'.degree < G.degree)
    (heq : H * U + G * V = H * U' + G * V') : U = U' ∧ V = V' := by
  have hdvd : G ∣ H * (U - U') := ⟨V' - V, by linear_combination heq⟩
  have hdvd' : G ∣ (U - U') := hcop.dvd_of_dvd_mul_left hdvd
  have hUU : U - U' = 0 := by
    by_contra hne
    have hdeg : (U - U').degree < G.degree :=
      lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hU hU')
    exact absurd (Polynomial.degree_le_of_dvd hdvd' hne) (not_le.mpr hdeg)
  have hUeq : U = U' := sub_eq_zero.mp hUU
  refine ⟨hUeq, ?_⟩
  have hGV : G * V = G * V' := by
    have h := heq
    rw [hUeq] at h
    exact add_left_cancel h
  exact mul_left_cancel₀ hG.ne_zero hGV

/-- The Bézout solve at the stage field (the §9 row's "locally reconstruct `Field K`":
C.04 exports no instance, so the D9 reconstruction is consumed here once and consumers get
an instance-free statement). -/
theorem exists_stageField_bezout_degree_lt (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {G H : Polynomial (F.stageField H₀ hpin)} (hG : G.Monic) (hH : H.Monic)
    (hcop : IsCoprime G H) (E : Polynomial (F.stageField H₀ hpin))
    (hE : E.degree < G.degree + H.degree) :
    ∃ U V : Polynomial (F.stageField H₀ hpin), U.degree < G.degree ∧ V.degree < H.degree ∧
      H * U + G * V = E := by
  letI : Field (F.stageField H₀ hpin) := localFieldStageField F H₀ hpin
  exact exists_bezout_degree_lt hG hH hcop E hE

/-- Uniqueness of the stage-field Bézout solve (instance-free statement). -/
theorem stageField_bezout_degree_lt_unique (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {G H U V U' V' : Polynomial (F.stageField H₀ hpin)} (hG : G.Monic)
    (hcop : IsCoprime G H) (hU : U.degree < G.degree) (hU' : U'.degree < G.degree)
    (heq : H * U + G * V = H * U' + G * V') : U = U' ∧ V = V' := by
  letI : Field (F.stageField H₀ hpin) := localFieldStageField F H₀ hpin
  exact bezout_degree_lt_unique hG hcop hU hU' heq

/-! ## Part 6 — Lemma S, the named open statement shape (the MH.9 carried hypothesis) -/

/-- ★ STATEMENT SHAPE — **Lemma S (graded solve, §4.2)**, nothing asserted (the C133mh1
statement-shape pattern).  Data: monic pure `p₁, p₂` with `D′ ∣ deg`, exact residual pins,
coprime residuals, weights `w₁, w₂`; an error `e` with `deg e < deg p₁ + deg p₂` and
`W(e) ≥ c ≥ w₁ + w₂`.  Conclusion: correctors `U, V` inside the degree windows with the
split weight bounds and the one-step contraction `W(e − (p₂U + p₁V)) ≥ c + 1`.  The open
leg is the grade-`c` MIXED product read law (Theorem M clause 3 above the support line);
this `Prop` is the exact carried hypothesis for the MH.9 assembly. -/
def LemmaSStatement (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] : Prop :=
  ∀ (π : O) (F : KeyFrame O π), Irreducible π → 0 < F.h →
  ∀ (H₀ : ℕ) (hpin : F.Pin H₀),
  ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ → ℓ * ((F.e₁ * F.f₁) * F.h) < u →
  ∀ p₁ p₂ : Polynomial O, p₁.Monic → p₂.Monic →
  0 < p₁.natDegree → 0 < p₂.natDegree →
  F.e₁ * F.f₁ ∣ p₁.natDegree → F.e₁ * F.f₁ ∣ p₂.natDegree →
  IsDvPure F p₁ u ℓ → IsDvPure F p₂ u ℓ →
  ∀ (hne₁ : (dvSideSet F p₁ u ℓ).Nonempty) (hne₂ : (dvSideSet F p₂ u ℓ).Nonempty)
    (M₁ M₂ : ℕ)
    (hp₁ : dvHgt F p₁ (dvSideMin F p₁ u ℓ hne₁) = (M₁ : ℕ∞))
    (hp₂ : dvHgt F p₂ (dvSideMin F p₂ u ℓ hne₂) = (M₂ : ℕ∞)),
  IsCoprime (dvResPoly F H₀ hpin p₁ u ℓ hne₁ M₁ hp₁)
      (dvResPoly F H₀ hpin p₂ u ℓ hne₂ M₂ hp₂) →
  ∀ w₁ w₂ : ℕ, dvSupp F p₁ u ℓ = (w₁ : ℕ∞) → dvSupp F p₂ u ℓ = (w₂ : ℕ∞) →
  ∀ (e : Polynomial O) (c : ℕ), e.natDegree < p₁.natDegree + p₂.natDegree →
    w₁ + w₂ ≤ c → ((c : ℕ) : ℕ∞) ≤ dvSupp F e u ℓ →
  ∃ U V : Polynomial O,
    U.natDegree < p₁.natDegree ∧ V.natDegree < p₂.natDegree ∧
    ((c - w₂ : ℕ) : ℕ∞) ≤ dvSupp F U u ℓ ∧
    ((c - w₁ : ℕ) : ℕ∞) ≤ dvSupp F V u ℓ ∧
    ((c + 1 : ℕ) : ℕ∞) ≤ dvSupp F (e - (p₂ * U + p₁ * V)) u ℓ

end Uniformity.Density.Tower.C133mh5

/-! ## AxCheck footer -/

section AxCheck

#print axioms Uniformity.Density.Tower.C133mh5.twistLiftO
#print axioms Uniformity.Density.Tower.C133mh5.twistLiftO_zero
#print axioms Uniformity.Density.Tower.C133mh5.natDegree_twistLiftO_lt
#print axioms Uniformity.Density.Tower.C133mh5.twistRead_zero
#print axioms Uniformity.Density.Tower.C133mh5.stageHeight_twistLiftO
#print axioms Uniformity.Density.Tower.C133mh5.twistRead_twistLiftO
#print axioms Uniformity.Density.Tower.C133mh5.dvWindowLift
#print axioms Uniformity.Density.Tower.C133mh5.dev_dvWindowLift
#print axioms Uniformity.Density.Tower.C133mh5.dev_dvWindowLift_off
#print axioms Uniformity.Density.Tower.C133mh5.natDegree_dvWindowLift_lt
#print axioms Uniformity.Density.Tower.C133mh5.natDegree_dvWindowLift_lt'
#print axioms Uniformity.Density.Tower.C133mh5.le_dvSupp_dvWindowLift
#print axioms Uniformity.Density.Tower.C133mh5.twistRead_dvWindowLift
#print axioms Uniformity.Density.Tower.C133mh5.dvSideLift
#print axioms Uniformity.Density.Tower.C133mh5.dev_dvSideLift_top
#print axioms Uniformity.Density.Tower.C133mh5.dev_dvSideLift_slot
#print axioms Uniformity.Density.Tower.C133mh5.dev_dvSideLift_past
#print axioms Uniformity.Density.Tower.C133mh5.dev_dvSideLift_off
#print axioms Uniformity.Density.Tower.C133mh5.dvSideLift_monic
#print axioms Uniformity.Density.Tower.C133mh5.natDegree_dvSideLift
#print axioms Uniformity.Density.Tower.C133mh5.dvHgt_dvSideLift_top
#print axioms Uniformity.Density.Tower.C133mh5.dvHgt_dvSideLift_slot
#print axioms Uniformity.Density.Tower.C133mh5.dvHgt_dvSideLift_slot_top
#print axioms Uniformity.Density.Tower.C133mh5.dvSupp_dvSideLift
#print axioms Uniformity.Density.Tower.C133mh5.isDvPure_dvSideLift
#print axioms Uniformity.Density.Tower.C133mh5.dvSideSet_dvSideLift_nonempty
#print axioms Uniformity.Density.Tower.C133mh5.dvHgt_dvSideLift_sideMin
#print axioms Uniformity.Density.Tower.C133mh5.dvResPoly_dvSideLift
#print axioms Uniformity.Density.Tower.C133mh5.le_dvSupp_succ_of_lineReads_eq_zero
#print axioms Uniformity.Density.Tower.C133mh5.exists_bezout_degree_lt
#print axioms Uniformity.Density.Tower.C133mh5.bezout_degree_lt_unique
#print axioms Uniformity.Density.Tower.C133mh5.exists_stageField_bezout_degree_lt
#print axioms Uniformity.Density.Tower.C133mh5.stageField_bezout_degree_lt_unique
#print axioms Uniformity.Density.Tower.C133mh5.LemmaSStatement

end AxCheck
