/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130pk
import Uniformity.ChapC.C45
import Uniformity.ChapC.C56a
import Uniformity.ChapC.C53b
import Uniformity.ChapC.C84d

/-!
# Uniformity.ChapC.C99r — Chapter C — the A-C.12 re-signed GENTOW2 landings

Unit GTR. Target: the leanfinal twins of the five re-signed §10 GENTOW2 statements enacted
by amendment **A-C.12** (`docs/in-progress/GENTOW2_ADJUDICATION_2026-08-24.md`, unit GSW) in
`leanspec/Leanspec/ChapC.lean`. GTA/GTB/GTC/GSW's own units (`runs/wave-b/verdict_GT{A,B,C}.md`,
`verdict_GSW.md`) all ran against the PRE-re-sign statements and are superseded here for the
three nodes this file lands.

## What lands, and at what honesty grade

* **C.99 `gentow2_Bpp` — FULL LANDING**, byte-faithful twin of the re-signed leanspec axiom
  (`ChapC.lean:2462-2481`), theorem-shaped, promoted from
  `leanfinal/scratch/GSW_check.lean`'s `gentow2_Bpp_resigned_provable` (Lean-core certificate;
  promotion only — the algebra is untouched). This statement quantifies over an ARBITRARY
  `W : DeepTower F H₀ hpin r` (with `hr : r = 2` as a scope-fence HYPOTHESIS, not a type-level
  fix), so it needs no `TowerDatum.deepTower` and is a genuine landing, not a SUPPLY node.
* **C.99 `theta_letter_valued` — NOT ATTEMPTED, stays BLOCKED (OPEN-LETTERS).** Per the A-C.12
  adjudication §3: even after the same B-1 supply and the ℕ→ℤ exponent repair, the letter
  clause needs the γ-recursion/exponent-lattice dictionary (Def 3.12, published §3.3), which
  is in neither `FGMNCalculus` nor any landed carrier. No declaration is emitted for it here.
* **C.103 `gentow2_A` — FULL LANDING. C.101 `gentow2_B` — FULL LANDING.** Both are proved first
  in a general-`W₂` SUPPLY form (`gentow2_A_supply`/`gentow2_B_supply`, parameterized by an
  explicit `W₂ : DeepTower.{0, uKt} F H₀ hpin 2` standing in for `T.deepTower hπ`), because at
  the time this unit started `TowerDatum.deepTower` (leanspec `ChapC.lean:2420-2427`) had **no
  landed leanfinal declaration** (confirmed absent by repo-wide search; the sibling unit TDW was
  tasked with it in `C84d.lean`). **`C84d.lean` landed while this unit was in flight** (TDW:
  `TowerDatum.deepTower`/`TowerDatum.deepTower_data`, sorry-free, Lean-core), so the polling
  instruction applies: `gentow2_A`/`gentow2_B` below are the byte-faithful leanspec twins,
  each ONE LINE — `gentow2_A_supply`/`gentow2_B_supply` instantiated at `W₂ := T.deepTower hπ`,
  with the ambient `[I : FGMNCalculus (T.deepTower hπ) e' f' u']` resolved automatically for the
  supply lemma's own instance argument. No new proof content; the `_supply` forms are kept as
  the more general (and reusable, at any depth-2 `DeepTower`) internal lemmas.

## The two SUPPLY proofs, in one line each

`gentow2_A_supply`: `KP_criterion`'s five antecedents are exactly (i) `recipe3`'s Monic/degree
shape — a one-level-up repeat of C.47/C.53b's `composedKey_monic`/`composedKey_natDegree_D₂`
"leading term dominates" argument, now run on `recipe3` itself (private helpers
`recipe3_tail_natDegree_lt`, `recipe3_monic`, `recipe3_natDegree` below) — and (ii)–(iv) the
re-signed `hadm`'s three conjuncts (now including the added `coeff 0 ≠ 0`, GSW's exact repair).
Irreducibility is `KP_irred`. Non-equivalence with `composedKey T` runs `nuEquiv_iff_Rres` against
`KP_keyAt`/`Rres_keyAt` (`Rres (keyAt 2) = 1`) and the degree mismatch `f' > 0 = natDegree 1`.

`gentow2_B_supply`: one application of `Rres_recipe` at
`khat t := k2DigitLift T (c t) ((f' - t) * u')`, whose two premises are exactly the re-signed
`hlift`/`hliftdeg` (the latter converted from `< T.D₂` to `< (I.keyAt 2).natDegree` through
`hkey` + `composedKey_natDegree_D₂`), followed by rewriting each summand's `Rgr` term through
the re-signed `hunit` (`Finset.sum_congr`). No new mathematics, exactly per the A-C.12
adjudication's sketch (§5/§6).

## DEPENDS

C.42 (`TowerDatum`) · C.43 (`composedKey`) · C.44/C.45 (`towerLabel`, `towerLabelEquiv`) ·
C.47/C.53b (`composedKey_monic`, `composedKey_natDegree_D₂`) · C.56a (`k2DigitLift`) ·
C.83/C130pk (`DeepTower`, `FGMNCalculus`, `chainNorm`, `thetaRatio`) — all landed.

## Status

Sorry-free. Axiom footprint: Lean core only for every declaration below (`gentow2_Bpp`,
`recipe3`, `gentow2_A_supply`, `gentow2_B_supply`) — the class `FGMNCalculus` is a HYPOTHESIS
CARRIER (no `fgmn_calculus_exists`), so its fields are consumed as ordinary function
arguments, not axioms. No new `axiom`, no `unsafe`, no statement weakening: every conclusion
below is either the re-signed leanspec type verbatim (`gentow2_Bpp`) or that type with the
single named substitution `T.deepTower hπ ↦ W₂` recorded above (`gentow2_A_supply`,
`gentow2_B_supply`).
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace Uniformity.Density.Tower.C99r

open Uniformity.Density.Leaf IsLocalRing Uniformity.Density.Tower

universe uKt

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O}

/-! ## NODE C.99 — `gentow2_Bpp`, FULL LANDING

Byte-faithful twin of the re-signed leanspec axiom (`ChapC.lean:2462-2481`). Promoted from
`leanfinal/scratch/GSW_check.lean`'s `gentow2_Bpp_resigned_provable`: the only change from that
certificate is restoring the four scope-fence hypotheses `hr`, `he'`, `hcop`, `hfloor` that the
re-signed AXIOM keeps (the certificate's own note: "does not even consume `hr`, `he'`, `hcop`,
`hfloor` — the re-signed axiom keeps them; removing binders is a different amendment") and
switching `I` from an explicit argument to the leanspec instance-implicit `[I : FGMNCalculus …]`
binder — both cosmetic, the algebra is untouched. -/

/-- **NODE C.99, `gentow2_Bpp`** — `LEMMA GENTOW2-B″`, the single-`w` slot law, ratio form, with
the A-C.12 B-1 normalizer supply (`hnorm`/`hnormdeg`/`hnormz`; GENTOW2_PROOF S5.2, ll.740–744).
PROVED from the A-C.11 class fields alone (`Rgr_mul` iterated for the power law, `Rgr_ne_zero` at
the B-1 supply, field cancellation) — no scope fence, no floor arithmetic, no cite is consumed by
this algebra; `hr`, `he'`, `hcop`, `hfloor` are unused, carried only for fidelity to the signed
scope. -/
theorem gentow2_Bpp {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower.{0, uKt} F H₀ hpin r) (e' f' u' : ℕ) [I : FGMNCalculus W e' f' u']
    (hr : r = 2)   -- ⚠ SCOPE FENCE (A-C.1 self-catch, carried unchanged by A-C.12)
    (he' : 0 < e') (hf' : 0 < f') (hcop : Nat.Coprime u' e')
    (hfloor : e' * W.Econst r < u')
    (hnorm : ∀ d, 0 < d → d ≤ f' → I.ExactGrade (d * u') (I.chainNorm r (d * u')))
    (hnormdeg : ∀ d, 0 < d → d ≤ f' →
      (I.chainNorm r (d * u')).natDegree < (I.keyAt r).natDegree)
    (hnormz : ∀ d, 0 < d → d ≤ f' → I.chainNorm r (d * u') ≠ 0)
    {t : ℕ} (ht : t < f') :
    I.Rgr ((f' - t) * u') (I.chainNorm r ((f' - t) * u')) * I.thetaRatio (f' - t)
      = (I.Rgr u' (I.chainNorm r u')) ^ (f' - t) := by
  set d := f' - t with hd
  have hd0 : 0 < d := Nat.sub_pos_of_lt ht
  have hdf : d ≤ f' := Nat.sub_le f' t
  have h1 : I.ExactGrade (1 * u') (I.chainNorm r (1 * u')) := hnorm 1 one_pos hf'
  have hbase : I.ExactGrade u' (I.chainNorm r u') := by simpa using h1
  have hpow : ∀ k : ℕ, 0 < k →
      I.ExactGrade (k * u') ((I.chainNorm r u') ^ k) ∧
      I.Rgr (k * u') ((I.chainNorm r u') ^ k) = (I.Rgr u' (I.chainNorm r u')) ^ k := by
    intro k hk
    induction k with
    | zero => exact absurd hk (lt_irrefl 0)
    | succ n ih =>
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        refine ⟨by simpa using hbase, by simp⟩
      · obtain ⟨ihg, ihr⟩ := ih hn
        have hmul := I.Rgr_mul (n * u') u' ((I.chainNorm r u') ^ n) (I.chainNorm r u')
          ihg hbase
        constructor
        · have : I.ExactGrade (n * u' + u') ((I.chainNorm r u') ^ n * I.chainNorm r u') :=
            hmul.1
          simpa [pow_succ, Nat.succ_mul] using this
        · have : I.Rgr (n * u' + u') ((I.chainNorm r u') ^ n * I.chainNorm r u')
              = I.Rgr (n * u') ((I.chainNorm r u') ^ n) * I.Rgr u' (I.chainNorm r u') :=
            hmul.2
          calc I.Rgr ((n + 1) * u') ((I.chainNorm r u') ^ (n + 1))
              = I.Rgr (n * u' + u') ((I.chainNorm r u') ^ n * I.chainNorm r u') := by
                rw [pow_succ, Nat.succ_mul]
            _ = I.Rgr (n * u') ((I.chainNorm r u') ^ n) * I.Rgr u' (I.chainNorm r u') :=
                this
            _ = (I.Rgr u' (I.chainNorm r u')) ^ n * I.Rgr u' (I.chainNorm r u') := by
                rw [ihr]
            _ = (I.Rgr u' (I.chainNorm r u')) ^ (n + 1) := by rw [pow_succ]
  have hane : I.Rgr (d * u') (I.chainNorm r (d * u')) ≠ 0 :=
    I.Rgr_ne_zero (d * u') (I.chainNorm r (d * u')) (hnorm d hd0 hdf)
      (hnormdeg d hd0 hdf) (hnormz d hd0 hdf)
  unfold FGMNCalculus.thetaRatio
  rw [mul_comm (I.Rgr (d * u') ((I.chainNorm r u') ^ d)) _, ← mul_assoc,
    mul_inv_cancel₀ hane, one_mul]
  exact (hpow d hd0).2

/-! ## `theta_letter_valued` — NOT ATTEMPTED, stays BLOCKED

Per the A-C.12 adjudication (§3) the letter clause needs the γ-recursion / exponent-lattice
dictionary (published Definition 3.12, §3.3: "the value-0 Laurent monomials … form exactly the
group ⟨γ₁, γ₂⟩") — the audited `OPEN-LETTERS` gap. No class field and no landed carrier expresses
it, so no declaration is emitted here (per the unit's charge: do not attempt). -/

/-! ## Shared §10 infrastructure — `recipe3` (local mirror, not itself a numbered node)

Byte-mirror of the leanspec §10 shared abbreviation (`ChapC.lean:2446-2450`; also mirrored
locally in `leanfinal/scratch/GSW_check.lean`), needed to STATE both C.101 and C.103. -/

/-- the depth-3 recipe key (the R3-3-completed display; shared abbreviation for C.101/C.103). -/
noncomputable def recipe3 {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (e' f' u' : ℕ)
    (c : ℕ → AdjoinRoot (towerLabel T)) : Polynomial O :=
  (composedKey T) ^ (e' * f')
    - ∑ t ∈ Finset.range f', k2DigitLift T (c t) ((f' - t) * u') * (composedKey T) ^ (e' * t)

private theorem recipe3_eq {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (e' f' u' : ℕ) (c : ℕ → AdjoinRoot (towerLabel T)) :
    recipe3 T e' f' u' c
      = (composedKey T) ^ (e' * f')
        - ∑ t ∈ Finset.range f', k2DigitLift T (c t) ((f' - t) * u') * (composedKey T) ^ (e' * t) :=
  rfl

/-! ### Private degree bookkeeping for `recipe3` (one level up from C.47/C.53b's
`composedKey`-level "leading term dominates" argument; same shape, run again over `recipe3`) -/

private theorem recipe3_tail_natDegree_lt {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (e' f' u' : ℕ)
    (he' : 0 < e') (hf' : 0 < f') (c : ℕ → AdjoinRoot (towerLabel T))
    (hliftdeg : ∀ t, t < f' → (k2DigitLift T (c t) ((f' - t) * u')).natDegree < T.D₂) :
    ((Finset.range f').sum
        fun t => k2DigitLift T (c t) ((f' - t) * u') * (composedKey T) ^ (e' * t)).natDegree
      < (e' * f') * T.D₂ := by
  classical
  set D := T.D₂ with hDdef
  have hD : 0 < D := by
    have h1 : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
    have h2 : 0 < T.e₂ * T.f₂ := by have := T.hcomp; omega
    simpa [hDdef, TowerDatum.D₂] using Nat.mul_pos h1 h2
  have hpos : 0 < (e' * f') * D := Nat.mul_pos (Nat.mul_pos he' hf') hD
  have hbound : ((Finset.range f').sum
      fun t => k2DigitLift T (c t) ((f' - t) * u') * (composedKey T) ^ (e' * t)).natDegree
      ≤ (e' * f') * D - 1 := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun t ht => ?_
    have ht' : t < f' := Finset.mem_range.mp ht
    have h1 : (k2DigitLift T (c t) ((f' - t) * u') * (composedKey T) ^ (e' * t)).natDegree
        ≤ (k2DigitLift T (c t) ((f' - t) * u')).natDegree + e' * t * D := by
      refine le_trans Polynomial.natDegree_mul_le ?_
      rw [Polynomial.natDegree_pow, composedKey_natDegree_D₂ T hπ]
    have h2 : (k2DigitLift T (c t) ((f' - t) * u')).natDegree < D := hliftdeg t ht'
    have h3 : e' * (t + 1) ≤ e' * f' := Nat.mul_le_mul_left _ ht'
    have h4 : e' * (t + 1) = e' * t + e' := by ring
    have h5 : (e' * t + e') * D ≤ (e' * f') * D := Nat.mul_le_mul_right D (by omega)
    have h6 : (e' * t + e') * D = e' * t * D + e' * D := by ring
    have h7 : D ≤ e' * D := Nat.le_mul_of_pos_left _ he'
    omega
  omega

private theorem recipe3_monic {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (e' f' u' : ℕ)
    (he' : 0 < e') (hf' : 0 < f') (c : ℕ → AdjoinRoot (towerLabel T))
    (hliftdeg : ∀ t, t < f' → (k2DigitLift T (c t) ((f' - t) * u')).natDegree < T.D₂) :
    (recipe3 T e' f' u' c).Monic := by
  have htail : (-((Finset.range f').sum
      fun t => k2DigitLift T (c t) ((f' - t) * u') * (composedKey T) ^ (e' * t))).degree
      < ((composedKey T) ^ (e' * f')).degree := by
    rw [Polynomial.degree_neg]
    refine Polynomial.degree_lt_degree ?_
    rw [Polynomial.natDegree_pow, composedKey_natDegree_D₂ T hπ]
    exact recipe3_tail_natDegree_lt T hπ e' f' u' he' hf' c hliftdeg
  have hsplit : recipe3 T e' f' u' c
      = -((Finset.range f').sum
            fun t => k2DigitLift T (c t) ((f' - t) * u') * (composedKey T) ^ (e' * t))
        + (composedKey T) ^ (e' * f') := by
    rw [recipe3_eq, sub_eq_neg_add]
  rw [hsplit]
  exact ((composedKey_monic T).pow (e' * f')).add_of_right htail

private theorem recipe3_natDegree {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (e' f' u' : ℕ)
    (he' : 0 < e') (hf' : 0 < f') (c : ℕ → AdjoinRoot (towerLabel T))
    (hliftdeg : ∀ t, t < f' → (k2DigitLift T (c t) ((f' - t) * u')).natDegree < T.D₂) :
    (recipe3 T e' f' u' c).natDegree = e' * f' * T.D₂ := by
  have htail : (-((Finset.range f').sum
      fun t => k2DigitLift T (c t) ((f' - t) * u') * (composedKey T) ^ (e' * t))).degree
      < ((composedKey T) ^ (e' * f')).degree := by
    rw [Polynomial.degree_neg]
    refine Polynomial.degree_lt_degree ?_
    rw [Polynomial.natDegree_pow, composedKey_natDegree_D₂ T hπ]
    exact recipe3_tail_natDegree_lt T hπ e' f' u' he' hf' c hliftdeg
  have hsplit : recipe3 T e' f' u' c
      = -((Finset.range f').sum
            fun t => k2DigitLift T (c t) ((f' - t) * u') * (composedKey T) ^ (e' * t))
        + (composedKey T) ^ (e' * f') := by
    rw [recipe3_eq, sub_eq_neg_add]
  have hdegeq : (recipe3 T e' f' u' c).degree = ((composedKey T) ^ (e' * f')).degree := by
    rw [hsplit]
    exact Polynomial.degree_add_eq_right_of_degree_lt htail
  rw [Polynomial.natDegree_eq_of_degree_eq hdegeq, Polynomial.natDegree_pow,
    composedKey_natDegree_D₂ T hπ]

/-! ## NODE C.103 `gentow2_A` — SUPPLY (`gentow2_A_supply`)

The re-signed leanspec statement (`ChapC.lean:2580-2599`) with the single named substitution
`T.deepTower hπ ↦ W₂` (module docstring). Real proof of the re-signed content: `KP_criterion`'s
five antecedents assembled from `recipe3_monic`/`recipe3_natDegree` (the Monic/degree legs,
supplied by `hliftdeg`) and the re-signed `hadm`'s three conjuncts; irreducibility from
`KP_irred`; non-equivalence with `composedKey T` from `nuEquiv_iff_Rres` against
`KP_keyAt`/`Rres_keyAt` and the degree mismatch `f' > 0 = (1 : Polynomial _).natDegree`. -/

theorem gentow2_A_supply {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    (W₂ : DeepTower.{0, uKt} F H₀ hpin 2)   -- stand-in for the unlanded `T.deepTower hπ`
    (e' f' u' : ℕ) [I : FGMNCalculus W₂ e' f' u']
    (hkey : I.keyAt 2 = composedKey T)
    (ρ : W₂.fld 2 ≃+* AdjoinRoot T.ψ₂)
    (hκ : T.e₂ * T.f₂ * T.u₂ < u') (he' : 0 < e') (hf' : 0 < f')
    (hcop : Nat.Coprime u' e')
    (c : ℕ → AdjoinRoot (towerLabel T)) (hc0 : c 0 ≠ 0)
    (hliftdeg : ∀ t, t < f' → (k2DigitLift T (c t) ((f' - t) * u')).natDegree < T.D₂)
    (hadm : Irreducible (I.Rres (recipe3 T e' f' u' c)) ∧
      (I.Rres (recipe3 T e' f' u' c)).natDegree = f' ∧
      (I.Rres (recipe3 T e' f' u' c)).coeff 0 ≠ 0) :
    I.KP (recipe3 T e' f' u' c) ∧ Irreducible (recipe3 T e' f' u' c) ∧
    ¬ I.nuEquiv (recipe3 T e' f' u' c) (composedKey T) := by
  have hmonic : (recipe3 T e' f' u' c).Monic :=
    recipe3_monic T hπ e' f' u' he' hf' c hliftdeg
  have hdeg2 : (I.keyAt 2).natDegree = T.D₂ := by rw [hkey]; exact composedKey_natDegree_D₂ T hπ
  have hrecdeg : (recipe3 T e' f' u' c).natDegree = e' * f' * (I.keyAt 2).natDegree := by
    rw [hdeg2]; exact recipe3_natDegree T hπ e' f' u' he' hf' c hliftdeg
  have hKP : I.KP (recipe3 T e' f' u' c) :=
    I.KP_criterion (recipe3 T e' f' u' c) hmonic hrecdeg hadm.1 hadm.2.1 hadm.2.2
  have hIrr : Irreducible (recipe3 T e' f' u' c) := I.KP_irred _ hKP hmonic
  refine ⟨hKP, hIrr, fun hequiv => ?_⟩
  have hKPcomposed : I.KP (composedKey T) := by
    rw [← hkey]; exact I.KP_keyAt (by omega)
  have hRresEq : I.Rres (recipe3 T e' f' u' c) = I.Rres (composedKey T) :=
    (I.nuEquiv_iff_Rres (recipe3 T e' f' u' c) (composedKey T) hKP hKPcomposed).mp hequiv
  have hRreskey : I.Rres (composedKey T) = 1 := by
    rw [← hkey]; exact I.Rres_keyAt (by omega)
  rw [hRreskey] at hRresEq
  have hz : f' = 0 := by rw [← hadm.2.1, hRresEq, Polynomial.natDegree_one]
  omega

/-- **NODE C.103, `gentow2_A`** — the byte-faithful leanspec twin (`ChapC.lean:2580-2599`),
now that `TowerDatum.deepTower` has landed (TDW, `C84d.lean`): `gentow2_A_supply` instantiated
at `W₂ := T.deepTower hπ`. -/
theorem gentow2_A {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    (e' f' u' : ℕ) [I : FGMNCalculus (T.deepTower hπ) e' f' u']
    (hkey : I.keyAt 2 = composedKey T)
    (ρ : (T.deepTower hπ).fld 2 ≃+* AdjoinRoot T.ψ₂)
    (hκ : T.e₂ * T.f₂ * T.u₂ < u') (he' : 0 < e') (hf' : 0 < f')
    (hcop : Nat.Coprime u' e')
    (c : ℕ → AdjoinRoot (towerLabel T)) (hc0 : c 0 ≠ 0)
    (hliftdeg : ∀ t, t < f' → (k2DigitLift T (c t) ((f' - t) * u')).natDegree < T.D₂)
    (hadm : Irreducible (I.Rres (recipe3 T e' f' u' c)) ∧
      (I.Rres (recipe3 T e' f' u' c)).natDegree = f' ∧
      (I.Rres (recipe3 T e' f' u' c)).coeff 0 ≠ 0) :
    I.KP (recipe3 T e' f' u' c) ∧ Irreducible (recipe3 T e' f' u' c) ∧
    ¬ I.nuEquiv (recipe3 T e' f' u' c) (composedKey T) :=
  gentow2_A_supply T hπ hh (T.deepTower hπ) e' f' u' hkey ρ hκ he' hf' hcop c hc0 hliftdeg hadm

/-! ## NODE C.101 `gentow2_B` — SUPPLY (`gentow2_B_supply`)

The re-signed leanspec statement (`ChapC.lean:2535-2563`) with the same `T.deepTower hπ ↦ W₂`
substitution. Real proof: one application of `I.Rres_recipe` at
`khat t := k2DigitLift T (c t) ((f' - t) * u')` (grades = `hlift`; degrees = `hliftdeg`
converted to `< (I.keyAt 2).natDegree` via `hkey` + `composedKey_natDegree_D₂`), then
`Finset.sum_congr` rewriting each coefficient through the re-signed `hunit`. -/

theorem gentow2_B_supply {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    (W₂ : DeepTower.{0, uKt} F H₀ hpin 2)   -- stand-in for the unlanded `T.deepTower hπ`
    (e' f' u' : ℕ) [I : FGMNCalculus W₂ e' f' u']
    (hkey : I.keyAt 2 = composedKey T)
    (ρ : W₂.fld 2 ≃+* AdjoinRoot T.ψ₂)
    (hκ : T.e₂ * T.f₂ * T.u₂ < u') (he' : 0 < e') (hf' : 0 < f')
    (hcop : Nat.Coprime u' e')
    (c : ℕ → AdjoinRoot (towerLabel T)) (hc0 : c 0 ≠ 0)
    (hlift : ∀ t, t < f' →
      I.ExactGrade ((f' - t) * u') (k2DigitLift T (c t) ((f' - t) * u')))
    (hliftdeg : ∀ t, t < f' → (k2DigitLift T (c t) ((f' - t) * u')).natDegree < T.D₂)
    (hunit : ∀ t, t < f' →
      I.Rgr ((f' - t) * u') (k2DigitLift T (c t) ((f' - t) * u'))
        = I.Rgr ((f' - t) * u') (I.chainNorm 2 ((f' - t) * u'))
          * ρ.symm ((towerLabelEquiv T hπ) (c t))) :
    I.Rres (recipe3 T e' f' u' c)
      = Polynomial.X ^ f'
        - ∑ t ∈ Finset.range f',
            Polynomial.C (I.Rgr ((f' - t) * u') (I.chainNorm 2 ((f' - t) * u'))
              * ρ.symm ((towerLabelEquiv T hπ) (c t))) * Polynomial.X ^ t := by
  have hliftdeg' : ∀ t, t < f' →
      (k2DigitLift T (c t) ((f' - t) * u')).natDegree < (I.keyAt 2).natDegree := by
    intro t ht
    rw [hkey, composedKey_natDegree_D₂ T hπ]
    exact hliftdeg t ht
  have hrec : I.Rres (recipe3 T e' f' u' c)
      = Polynomial.X ^ f'
        - ∑ t ∈ Finset.range f',
            Polynomial.C (I.Rgr ((f' - t) * u') (k2DigitLift T (c t) ((f' - t) * u')))
              * Polynomial.X ^ t := by
    have h := I.Rres_recipe (fun t => k2DigitLift T (c t) ((f' - t) * u')) hlift hliftdeg'
    rw [hkey] at h
    exact h
  rw [hrec]
  have hsum : (∑ t ∈ Finset.range f',
        Polynomial.C (I.Rgr ((f' - t) * u') (k2DigitLift T (c t) ((f' - t) * u')))
          * Polynomial.X ^ t)
      = ∑ t ∈ Finset.range f',
          Polynomial.C (I.Rgr ((f' - t) * u') (I.chainNorm 2 ((f' - t) * u'))
              * ρ.symm ((towerLabelEquiv T hπ) (c t))) * Polynomial.X ^ t := by
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [hunit t (Finset.mem_range.mp ht)]
  rw [hsum]

/-- **NODE C.101, `gentow2_B`** — the byte-faithful leanspec twin (`ChapC.lean:2535-2563`),
now that `TowerDatum.deepTower` has landed (TDW, `C84d.lean`): `gentow2_B_supply` instantiated
at `W₂ := T.deepTower hπ`. -/
theorem gentow2_B {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    (e' f' u' : ℕ) [I : FGMNCalculus (T.deepTower hπ) e' f' u']
    (hkey : I.keyAt 2 = composedKey T)
    (ρ : (T.deepTower hπ).fld 2 ≃+* AdjoinRoot T.ψ₂)
    (hκ : T.e₂ * T.f₂ * T.u₂ < u') (he' : 0 < e') (hf' : 0 < f')
    (hcop : Nat.Coprime u' e')
    (c : ℕ → AdjoinRoot (towerLabel T)) (hc0 : c 0 ≠ 0)
    (hlift : ∀ t, t < f' →
      I.ExactGrade ((f' - t) * u') (k2DigitLift T (c t) ((f' - t) * u')))
    (hliftdeg : ∀ t, t < f' → (k2DigitLift T (c t) ((f' - t) * u')).natDegree < T.D₂)
    (hunit : ∀ t, t < f' →
      I.Rgr ((f' - t) * u') (k2DigitLift T (c t) ((f' - t) * u'))
        = I.Rgr ((f' - t) * u') (I.chainNorm 2 ((f' - t) * u'))
          * ρ.symm ((towerLabelEquiv T hπ) (c t))) :
    I.Rres (recipe3 T e' f' u' c)
      = Polynomial.X ^ f'
        - ∑ t ∈ Finset.range f',
            Polynomial.C (I.Rgr ((f' - t) * u') (I.chainNorm 2 ((f' - t) * u'))
              * ρ.symm ((towerLabelEquiv T hπ) (c t))) * Polynomial.X ^ t :=
  gentow2_B_supply T hπ hh (T.deepTower hπ) e' f' u' hkey ρ hκ he' hf' hcop c hc0 hlift hliftdeg
    hunit

end Uniformity.Density.Tower.C99r

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C99r.gentow2_Bpp
#print axioms Uniformity.Density.Tower.C99r.recipe3
#print axioms Uniformity.Density.Tower.C99r.gentow2_A_supply
#print axioms Uniformity.Density.Tower.C99r.gentow2_A
#print axioms Uniformity.Density.Tower.C99r.gentow2_B_supply
#print axioms Uniformity.Density.Tower.C99r.gentow2_B

end AxCheck
