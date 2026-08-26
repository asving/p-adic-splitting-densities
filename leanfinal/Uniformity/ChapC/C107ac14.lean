/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C107gt5
import Uniformity.ChapC.C99r
import Uniformity.ChapC.C105

/-!
# Uniformity.ChapC.C107ac14 — Chapter C — the A-C.14 GENTOW5 supply-cascade landings

Unit AC14.  Amendment **A-C.14** (2026-08-25, this unit, delegated enactment) re-signed the
three GENTOW5-family leanspec axioms that unit GT5 (`runs/wave-b/verdict_GT5.md`) left
BLOCKED on omitted supply hypotheses — NODE C.89's `gentow5w_two` / `gentow5w_one_shape` and
NODE C.90's `gentow5_key_certificate` (`leanspec/Leanspec/ChapC.lean`).  This file lands the
leanfinal theorem twins the re-sign unblocks.

## The A-C.14 re-signs (enacted in leanspec, quoted sources at each hunk)

* **`gentow5w_two` / `gentow5w_one_shape`** gain the four `gentow2_Bpp` supply families
  `hprev` ([A-C.13] restored Cor 4.12(2) premise), `hnorm`/`hnormdeg`/`hnormz` (the B-1
  normalizer supply, GENTOW2_PROOF S5.2 ll.740–744) — the standing adjudication's own
  cascade flag (`docs/in-progress/GENTOW2_ADJUDICATION_2026-08-24.md` §2: "Cascade flag (not
  enacted here): C.89's `gentow5w_two` … and `gentow5w_one_shape` will need the same three
  families when their landing unit runs; flagged for the next A-C amendment"; §10 item 3).
* **`gentow5_key_certificate`** gains (i) the omitted third `hadm` conjunct
  `(Rres Φnext).coeff 0 ≠ 0` — the source's admissibility notion states it explicitly
  (GENTOW5_PROOF_2026-08-09.md ll.793–796: "psi_{i+1}^{(w_i)} is GENTOW2-A-ADMISSIBLE at
  each value of w_i — monic irreducible of degree f_{i+1} with nonzero constant term"), the
  identical repair A-C.12 enacted on the sibling `gentow2_A`; (ii) the depth-3 scope binder
  `hr3 : 3 ≤ r` (C93 census: "depth-3 scope, 𝒲-conditional"; GT5's secondary observation:
  `keyAt_deg` needs `1 ≤ r` and `Wle` only carries rungs `≥ 3`); and (iii) the RECIPE
  COUPLING `c`/`hψc`/`hres` of `ψ'` to `Φnext`, carried as explicit discharge-node supply
  (the C.101-`hunit` style).  (iii) repairs a **false-shape finding made by this unit**: the
  A-C.1 signing left `ψ'` a free binder, and instantiating `ψ' := X ^ f'` forces
  `Rres Φnext = wconj w (X ^ f') = X ^ f'` — contradicting `hadm`'s irreducibility at
  `f' ≥ 2` (and the new coeff-0 conjunct at every `f' ≥ 1`) at ANY inhabited configuration.
  The source ties `ψ'` to `Φnext` by construction ("keys Phi_1, ..., Phi_r built by THE
  RECIPE [… GAUGE-CORRECTED form — the S2.1 pin's vartheta-twisted khat_t]", S3 statement;
  clause (a)'s display "R_{nu_i}(Phi_{i+1}) = psi_{i+1}^{(w_i)} := w_i^{f_{i+1}} *
  psi_{i+1}(y / w_i)"); `hres` is exactly the depth-`r` B-law display, whose landed depth-2
  instance is C.101 (`C99r.gentow2_B`), with the gauge-correcting ϑ-twist appearing as the
  `thetaRatio` factor.

## What lands here, and at what honesty grade

* **`gentow5w_two` — FULL LANDING** (byte-faithful twin of the re-signed axiom).  The
  documented route, verbatim: "(i) the `i = 2` discharge from C.99" — the witness is
  `w := Rgr u' (chainNorm 2 u')` (nonzero by `Rgr_ne_zero` at the `d = 1` supply rows), and
  the per-`t` law IS the landed re-signed C.99 twin `C99r.gentow2_Bpp` at `r = 2`.
* **`gentow5_key_certificate` — FULL LANDING** (byte-faithful twin of the re-signed axiom).
  KP clause: `KP_criterion`'s five antecedents = `hmon`, `hdeg` (converted through
  `keyAt_deg` at `1 ≤ r`, from `hr3`), and the re-signed `hadm`'s three conjuncts.  `𝒲`
  clause: `hW` at the top rung `r` (needs `hr3`) yields the single `w ≠ 0` with
  `Rgr(chainNorm)·ϑ = w^(f'-t)`; rewriting `hres` through that law and computing
  `wconj w (X^f' − Σ C(c t)X^t) = X^f' − Σ C(w^(f'-t)·c t)X^t` (private helper
  `wconj_X_pow_sub_sum`) closes the conjugation display.
* **`gentow5w_one_shape` — the ONE REMAINING HOLD (adjudicated; no byte-faithful twin).**
  The re-signed supply makes its RATIO content provable at depth 1 (private
  `ratio_power_law`, the C99r algebra without the depth-2 fence — the fence guarded an
  AXIOM's unproved assertion; here the same algebra is machine-checked from the class
  fields, so no open law is asserted).  But the conclusion's LETTER SHAPE additionally
  needs the tie `Rgr u' (chainNorm 1 u') = letterZ 1 ^ k` — the audited
  **OPEN-LETTERS/OPEN-EVAL-ISO** gap (`runs/wave-b/verdict_GTB.md` C.102 row: "No class
  field relates `letterZ` to `ρ` or to `AdjoinRoot.root T.ψ₂`"), which this unit does NOT
  bridge.  Landed instead: `gentow5w_one_shape_of_letter_tie`, the conditional form whose
  extra hypothesis `htie : ∃ k, I.Rgr u' (I.chainNorm 1 u') = I.letterZ 1 ^ k` is EXACTLY
  the missing law — when an OPEN-LETTERS carrier lands, `htie` discharges and the
  byte-faithful twin is one application away.

## DEPENDS

C107gt5 (`GENTOW5W`, `Wle`) · C99r (`gentow2_Bpp`, the A-C.12/A-C.13 re-signed C.99 twin) ·
C105 (`wconj`) · C130pk (`FGMNCalculus`, `chainNorm`, `thetaRatio`) · C83 (`DeepTower`,
`trunc`) — all landed, imported (transitively).

## Status

Sorry-free.  Axiom footprint: Lean core only for every declaration (the class
`FGMNCalculus` is a HYPOTHESIS CARRIER; its fields are consumed as ordinary arguments).
No new `axiom`, no `unsafe`, no statement weakening: `gentow5w_two` and
`gentow5_key_certificate` are the re-signed leanspec types verbatim (modulo the design-§7
universe substitution `DeepTower ↦ DeepTower.{0, uKt}`);
`gentow5w_one_shape_of_letter_tie` is the re-signed `gentow5w_one_shape` type PLUS the one
named extra hypothesis `htie`, under a distinct name (deliberately NOT the leanspec name —
the hold is recorded, not bridged).
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace Uniformity.Density.Tower.C107ac14

open Uniformity.Density.Leaf IsLocalRing Uniformity.Density.Tower

universe uKt

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O}

/-! ## The general-depth ratio power law (private engine)

The C99r `gentow2_Bpp` algebra, verbatim, WITHOUT the depth-2 fence binders: pure class-field
algebra (`Rgr_mul` iterated — each step consuming `hprev` at its second grade `u'` —
`Rgr_ne_zero` at the B-1 supply, field cancellation), valid at every depth `r` GIVEN the
four supply families.  This does not assert the open `𝒲(i)` law: the burden sits in the
supply hypotheses (depth-`r` B-1), exactly the A-C.14 cascade design. -/

private theorem ratio_power_law {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower.{0, uKt} F H₀ hpin r) (e' f' u' : ℕ) (I : FGMNCalculus W e' f' u')
    (hf' : 0 < f')
    (hprev : 2 ≤ f' → I.PrevGrade u')
    (hnorm : ∀ d, 0 < d → d ≤ f' → I.ExactGrade (d * u') (I.chainNormBelow r (d * u')))
    (hnormdeg : ∀ d, 0 < d → d ≤ f' →
      (I.chainNormBelow r (d * u')).natDegree < (I.keyAt r).natDegree)
    (hnormz : ∀ d, 0 < d → d ≤ f' → I.chainNormBelow r (d * u') ≠ 0)
    {t : ℕ} (ht : t < f') :
    I.Rgr ((f' - t) * u') (I.chainNormBelow r ((f' - t) * u')) * I.thetaRatio (f' - t)
      = (I.Rgr u' (I.chainNormBelow r u')) ^ (f' - t) := by
  by_cases hf1 : f' = 1
  · subst f'
    have ht0 : t = 0 := by omega
    subst t
    have hgrade : I.ExactGrade u' (I.chainNormBelow r u') := by
      simpa using hnorm 1 one_pos le_rfl
    have hdeg : (I.chainNormBelow r u').natDegree < (I.keyAt r).natDegree := by
      simpa using hnormdeg 1 one_pos le_rfl
    have hnz : I.chainNormBelow r u' ≠ 0 := by
      simpa using hnormz 1 one_pos le_rfl
    have ha : I.Rgr u' (I.chainNormBelow r u') ≠ 0 :=
      I.Rgr_ne_zero u' _ hgrade hdeg hnz
    simp [FGMNCalculus.thetaRatio, ha]
  have hf2 : 2 ≤ f' := by omega
  set d := f' - t with hd
  have hd0 : 0 < d := Nat.sub_pos_of_lt ht
  have hdf : d ≤ f' := Nat.sub_le f' t
  have h1 : I.ExactGrade (1 * u') (I.chainNormBelow r (1 * u')) := hnorm 1 one_pos hf'
  have hbase : I.ExactGrade u' (I.chainNormBelow r u') := by simpa using h1
  have hpow : ∀ k : ℕ, 0 < k →
      I.ExactGrade (k * u') ((I.chainNormBelow r u') ^ k) ∧
      I.Rgr (k * u') ((I.chainNormBelow r u') ^ k) =
        (I.Rgr u' (I.chainNormBelow r u')) ^ k := by
    intro k hk
    induction k with
    | zero => exact absurd hk (lt_irrefl 0)
    | succ n ih =>
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        refine ⟨by simpa using hbase, by simp⟩
      · obtain ⟨ihg, ihr⟩ := ih hn
        have hmul := I.Rgr_mul (n * u') u' ((I.chainNormBelow r u') ^ n)
          (I.chainNormBelow r u') ihg hbase (hprev hf2)
        constructor
        · have : I.ExactGrade (n * u' + u')
              ((I.chainNormBelow r u') ^ n * I.chainNormBelow r u') := hmul.1
          simpa [pow_succ, Nat.succ_mul] using this
        · have : I.Rgr (n * u' + u')
              ((I.chainNormBelow r u') ^ n * I.chainNormBelow r u') =
              I.Rgr (n * u') ((I.chainNormBelow r u') ^ n) *
                I.Rgr u' (I.chainNormBelow r u') := hmul.2
          calc I.Rgr ((n + 1) * u') ((I.chainNormBelow r u') ^ (n + 1))
              = I.Rgr (n * u' + u')
                  ((I.chainNormBelow r u') ^ n * I.chainNormBelow r u') := by
                rw [pow_succ, Nat.succ_mul]
            _ = I.Rgr (n * u') ((I.chainNormBelow r u') ^ n) *
                  I.Rgr u' (I.chainNormBelow r u') := this
            _ = (I.Rgr u' (I.chainNormBelow r u')) ^ n *
                  I.Rgr u' (I.chainNormBelow r u') := by
                rw [ihr]
            _ = (I.Rgr u' (I.chainNormBelow r u')) ^ (n + 1) := by rw [pow_succ]
  have hane : I.Rgr (d * u') (I.chainNormBelow r (d * u')) ≠ 0 :=
    I.Rgr_ne_zero (d * u') (I.chainNormBelow r (d * u')) (hnorm d hd0 hdf)
      (hnormdeg d hd0 hdf) (hnormz d hd0 hdf)
  unfold FGMNCalculus.thetaRatio
  rw [mul_comm (I.Rgr (d * u') ((I.chainNormBelow r u') ^ d)) _, ← mul_assoc,
    mul_inv_cancel₀ hane, one_mul]
  exact (hpow d hd0).2

/-! ## NODE C.89, `gentow5w_two` — FULL LANDING (the `i = 2` discharge from C.99) -/

/-- **NODE C.89, `gentow5w_two`** — byte-faithful twin of the A-C.14 re-signed leanspec
axiom.  The documented route verbatim: the `𝒲` witness at depth 2 is
`w := Rgr u' (chainNorm 2 u')`, nonzero by `Rgr_ne_zero` at the `d = 1` supply rows, and the
per-`t` ratio law IS the landed re-signed C.99 (`C99r.gentow2_Bpp` at `r = 2`). -/
theorem gentow5w_two {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (W : DeepTower.{0, uKt} F H₀ hpin 2) (e' f' u' : ℕ) (I : FGMNCalculus W e' f' u')
    (he' : 0 < e') (hf' : 0 < f') (hcop : Nat.Coprime u' e')
    (hfloor : e' * W.Econst 2 < u')
    (hprev : 2 ≤ f' → I.PrevGrade u')
    (hnorm : ∀ d, 0 < d → d ≤ f' → I.ExactGrade (d * u') (I.chainNormBelow 2 (d * u')))
    (hnormdeg : ∀ d, 0 < d → d ≤ f' →
      (I.chainNormBelow 2 (d * u')).natDegree < (I.keyAt 2).natDegree)
    (hnormz : ∀ d, 0 < d → d ≤ f' → I.chainNormBelow 2 (d * u') ≠ 0) :
    GENTOW5W W e' f' u' I := by
  refine ⟨I.Rgr u' (I.chainNormBelow 2 u'), ?_, fun t ht => ?_⟩
  · have h := I.Rgr_ne_zero (1 * u') (I.chainNormBelow 2 (1 * u'))
      (hnorm 1 one_pos hf') (hnormdeg 1 one_pos hf') (hnormz 1 one_pos hf')
    simpa using h
  · exact C99r.gentow2_Bpp W e' f' u' (I := I) rfl he' hf' hcop hfloor hprev
      hnorm hnormdeg hnormz ht

/-! ## NODE C.89, `gentow5w_one_shape` — the ONE REMAINING HOLD (conditional form landed)

The byte-faithful twin is NOT declared: its letter shape needs the OPEN-LETTERS tie (module
docstring), which no class field or landed carrier supplies.  The conditional form below
carries that tie as the explicit hypothesis `htie` — exactly the missing law, so the hold is
recorded in the signature itself, not bridged. -/

/-- **NODE C.89, `gentow5w_one_shape`, conditional form** — the A-C.14 re-signed type PLUS
the one named extra hypothesis `htie` (the OPEN-LETTERS tie, exactly the missing law; see
the module docstring).  Everything else is proved: the ratio power law at depth 1 from the
supply families (`ratio_power_law`). -/
theorem gentow5w_one_shape_of_letter_tie {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (W : DeepTower.{0, uKt} F H₀ hpin 1) (e' f' u' : ℕ) (I : FGMNCalculus W e' f' u')
    (he' : 0 < e') (hf' : 0 < f') (hcop : Nat.Coprime u' e')
    (hfloor : e' * W.Econst 1 < u')
    (hprev : 2 ≤ f' → I.PrevGrade u')
    (hnorm : ∀ d, 0 < d → d ≤ f' → I.ExactGrade (d * u') (I.chainNormBelow 1 (d * u')))
    (hnormdeg : ∀ d, 0 < d → d ≤ f' →
      (I.chainNormBelow 1 (d * u')).natDegree < (I.keyAt 1).natDegree)
    (hnormz : ∀ d, 0 < d → d ≤ f' → I.chainNormBelow 1 (d * u') ≠ 0)
    -- the OPEN-LETTERS tie, carried explicitly (NOT in the leanspec signature; the audited
    -- gap `OPEN-LETTERS`/`OPEN-EVAL-ISO`, verdict_GTB.md C.102 row):
    (htie : ∃ k : ℕ, I.Rgr u' (I.chainNormBelow 1 u') = I.letterZ 1 ^ k) :
    ∃ k : ℕ, ∀ t, t < f' →
      I.Rgr ((f' - t) * u') (I.chainNormBelow 1 ((f' - t) * u')) * I.thetaRatio (f' - t)
        = (I.letterZ 1 ^ k) ^ (f' - t) := by
  obtain ⟨k, hk⟩ := htie
  refine ⟨k, fun t ht => ?_⟩
  rw [ratio_power_law W e' f' u' I hf' hprev hnorm hnormdeg hnormz ht, hk]

/-! ## The `wconj` twist display (private helper for C.90)

`wconj w (X^f' − Σ_{t<f'} C(c t)·X^t) = X^f' − Σ_{t<f'} C(w^(f'-t)·c t)·X^t` — the exact
computation behind the source display `psi^{(w)} := w^f · psi(y/w)` read on the digit-string
polynomial. -/

open Polynomial in
private theorem tail_natDegree_lt {K : Type uKt} [Field K] (f' : ℕ) (hf' : 0 < f')
    (c : ℕ → K) :
    (∑ t ∈ Finset.range f', C (c t) * X ^ t).natDegree < f' := by
  have h : (∑ t ∈ Finset.range f', C (c t) * X ^ t).natDegree ≤ f' - 1 := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun t ht => ?_
    have ht' : t < f' := Finset.mem_range.mp ht
    have h1 : (C (c t) * X ^ t).natDegree ≤ (X ^ t : Polynomial K).natDegree :=
      Polynomial.natDegree_C_mul_le (c t) (X ^ t)
    rw [Polynomial.natDegree_X_pow] at h1
    omega
  omega

open Polynomial in
private theorem wconj_X_pow_sub_sum {K : Type uKt} [Field K] (w : K) (hw : w ≠ 0)
    (f' : ℕ) (hf' : 0 < f') (c : ℕ → K) :
    wconj w (X ^ f' - ∑ t ∈ Finset.range f', C (c t) * X ^ t)
      = X ^ f' - ∑ t ∈ Finset.range f', C (w ^ (f' - t) * c t) * X ^ t := by
  have hdegP : (X ^ f' - ∑ t ∈ Finset.range f', C (c t) * X ^ t : Polynomial K).natDegree
      = f' := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt, Polynomial.natDegree_X_pow]
    rw [Polynomial.natDegree_X_pow]
    exact tail_natDegree_lt f' hf' c
  have hcompsum : (∑ t ∈ Finset.range f', C (c t) * X ^ t : Polynomial K).comp
        (C w⁻¹ * X)
      = ∑ t ∈ Finset.range f', C (c t) * (C w⁻¹ * X) ^ t := by
    rw [Polynomial.comp_eq_aeval, map_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, Polynomial.algebraMap_eq]
  have hkey : ∀ t, t < f' → w ^ f' * (w⁻¹ ^ t * c t) = w ^ (f' - t) * c t := by
    intro t ht
    have hsplit : w ^ f' = w ^ (f' - t) * w ^ t := by
      rw [← pow_add, Nat.sub_add_cancel (le_of_lt ht)]
    rw [hsplit, mul_assoc, ← mul_assoc (w ^ t), ← mul_pow, mul_inv_cancel₀ hw, one_pow,
      one_mul]
  unfold wconj
  rw [hdegP, Polynomial.sub_comp, hcompsum, mul_sub, Finset.mul_sum]
  congr 1
  · rw [Polynomial.pow_comp, Polynomial.X_comp, mul_pow, ← Polynomial.C_pow, ← mul_assoc,
      ← Polynomial.C_mul, ← mul_pow, mul_inv_cancel₀ hw, one_pow, Polynomial.C_1, one_mul]
  · refine Finset.sum_congr rfl fun t ht => ?_
    rw [mul_pow, ← Polynomial.C_pow, ← hkey t (Finset.mem_range.mp ht),
      Polynomial.C_mul, Polynomial.C_mul]
    ring

/-! ## NODE C.90, `gentow5_key_certificate` — FULL LANDING -/

/-- **NODE C.90, `gentow5_key_certificate`** — byte-faithful twin of the A-C.14 re-signed
leanspec axiom (GENTOW5-B clause (a), the key certificate at the depth-3 `𝒲`-conditional
scope).  KP clause: `KP_criterion` at the re-signed `hadm`'s three conjuncts, degree leg
through `keyAt_deg` (`1 ≤ r` from `hr3`).  `𝒲` clause: `hW` at the top rung yields the
single `w`; the recipe coupling `hres`/`hψc` plus the `wconj` twist display close
`Rres Φnext = wconj w ψ'`. -/
theorem gentow5_key_certificate {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower.{0, uKt} F H₀ hpin r) (e' f' u' : ℕ)
    (I : ∀ i, (hi : i ≤ r) → FGMNCalculus (W.trunc i hi) e' f' u')
    (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    (hW : Wle W e' f' u' I r)
    (hr3 : 3 ≤ r)
    (he' : 0 < e') (hf' : 0 < f') (hcop : Nat.Coprime u' e')
    (hfloor : e' * W.Econst r < u')
    (Φnext : Polynomial O) (hmon : Φnext.Monic)
    (hdeg : Φnext.natDegree = e' * f' * W.Dcum r)
    (ψ' : Polynomial ((W.trunc r le_rfl).fld r)) (hψm : ψ'.Monic) (hψd : ψ'.natDegree = f')
    (c : ℕ → (W.trunc r le_rfl).fld r)
    (hψc : ψ' = Polynomial.X ^ f'
      - ∑ t ∈ Finset.range f', Polynomial.C (c t) * Polynomial.X ^ t)
    (hres : (I r le_rfl).Rres Φnext
      = Polynomial.X ^ f' - ∑ t ∈ Finset.range f',
          Polynomial.C ((I r le_rfl).Rgr ((f' - t) * u')
              ((I r le_rfl).chainNormBelow r ((f' - t) * u'))
            * (I r le_rfl).thetaRatio (f' - t) * c t) * Polynomial.X ^ t)
    (hadm : Irreducible ((I r le_rfl).Rres Φnext) ∧
      ((I r le_rfl).Rres Φnext).natDegree = f' ∧
      ((I r le_rfl).Rres Φnext).coeff 0 ≠ 0) :
    (I r le_rfl).KP Φnext ∧
    ∃ w : (W.trunc r le_rfl).fld r, w ≠ 0 ∧
      (I r le_rfl).Rres Φnext = wconj w ψ' := by
  -- KP clause: `KP_criterion` with the now-supplied five antecedents.
  have hkdeg : ((I r le_rfl).keyAt r).natDegree = (W.trunc r le_rfl).Dcum r :=
    (I r le_rfl).keyAt_deg r (by omega) le_rfl
  have hdeg' : Φnext.natDegree = e' * f' * ((I r le_rfl).keyAt r).natDegree := by
    rw [hkdeg]; exact hdeg
  have hKP : (I r le_rfl).KP Φnext :=
    (I r le_rfl).KP_criterion Φnext hmon hdeg' hadm.1 hadm.2.1 hadm.2.2
  -- 𝒲 clause: the single `w` at the top rung, then the twist display.
  obtain ⟨w, hw0, hlaw⟩ := hW r hr3 le_rfl le_rfl
  refine ⟨hKP, w, hw0, ?_⟩
  rw [hres, hψc, wconj_X_pow_sub_sum w hw0 f' hf' c]
  congr 1
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [hlaw t (Finset.mem_range.mp ht)]

end Uniformity.Density.Tower.C107ac14

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C107ac14.gentow5w_two
#print axioms Uniformity.Density.Tower.C107ac14.gentow5w_one_shape_of_letter_tie
#print axioms Uniformity.Density.Tower.C107ac14.gentow5_key_certificate

end AxCheck
