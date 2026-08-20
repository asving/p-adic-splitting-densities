/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C35
import Uniformity.ChapC.C35b

/-!
# Uniformity.ChapC.C67 — `multiplicity_tie` REFUTED: the EXACT-degree conjunct is FALSE

**Chapter C, NODE C.67** [theorem] (leanspec `multiplicity_tie`, L2285).  **The signed
statement is FALSE**, machine-checked below at the workhorse frame `(s2Frame, L₀, g₀)` over
`ℤ_[2]` — the fourth member of the EXACT-DEGREE (D-CARRY) family to fall, and the one
`HX_SWEEP_2026-08-20.md` §6.3 predicted.  The signed statement stays at the leanspec stub
(no axiom, no `sorry`, no weakened restatement under the signed name).

## The mechanism (§6.3's analysis, now a theorem)

At `f := g₀ = x³ − 2x + 4` and `m := 1`:

* `hmult` HOLDS: the level residual of `g₀` is `ρ` itself (`ρ¹ ∣ ρ`, and `¬ ρ² ∣ ρ` by
  degrees) — `hmult_g₀`;
* `blockFactor L₀ g₀ = g₀`: `g₀` is a labelled divisor of itself and every labelled divisor
  of `g₀` trivially divides `g₀`, so the maximality existential is inhabited at `g₀` and
  C.35's `blockFactor_eq_of_frontier` pins the choice — `blockFactor_g₀`;
* conjunct 1 then demands `deg g₀ = L₀.keyDeg₂ · 1`, i.e. **`3 = 2`** — FALSE;
* ★ the sharpest detail, also machine-checked: **conjunct 2 (`mult₂ L f = m`) is TRUE at the
  same instance** (`mult₂_g₀ : ⌊3/2⌋ = 1`).  The statement fails on its EXACT-degree conjunct
  while its FLOOR conjunct survives — the D-CARRY fault line displayed in one instance
  (floor reads survive, exact-degree reads of labelled objects die; cf. the D13 refutation
  `C35B_D13_REFUTED_2026-08-20.md`).

## The one genuinely new ingredient: `Squarefree g₀`

`BlockContext` demands it, and §6.3 recorded it as "the one real piece of work" — the
`Separable → Squarefree` route is NOT available (over `O` the resultant `∓400` is a
non-unit, so `IsCoprime g₀ g₀'` fails).  Landed here directly (`g₀_squarefree`), over ANY
DVR in which `2` is a uniformizer, by elementary divisibility descent: a repeated factor
must be linear, `g₀ = (AX + a)²(BX + b)` forces the coefficient identities
`A²B = 1`, `A²b + 2AaB = 0`, `2Aab + a²B = −2`, whence `3a² = 2A²`; then `2 ∣ a` (2 prime,
`2 ∤ 3`), writing `a = 2a′` gives `A² = 2·(3a′²)`, so `2 ∣ A` — against `A` a unit (it
divides the leading coefficient `1`).  REUSABLE SUPPLY: this also completes the
`BlockContext L₀ g₀` package (`blockContext_g₀`), previously blocked on exactly this leg.

## Consumption fence

Nothing here proves or weakens C.67 for any OTHER instance; the refutation kills the signed
∀-statement (`multiplicityTie_false`, binders mirrored verbatim per the C35b `D13Statement`
pattern, realized absolutely over `ℤ_[2]`).  The honest repair direction (floor-form or a
`D′ ∣ deg`-guarded form) is a RE-SIGN and is OWNER-GATED; recorded, not enacted.

## Status

Zero `sorry`; axiom footprint Lean-core only (AxCheck footer).  No cite consumed: the
leanspec's `[cite:FGMN]` note describes the intended PROOF of the (false) statement, and no
FGMN name is touched here.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C67

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower Uniformity.Density.Tower.C35b

/-! ## 0. The signed C.67, as a ∀-closure (all binders mirrored) -/

/-- The signed `multiplicity_tie` (leanspec L2285), closed over everything —
`multiplicityTie_false` below proves this FALSE. -/
def MultiplicityTieStatement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (π : O)
    (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key
      (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    (L : LevelDatum F H₀ hpin) (_hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (f : Polynomial O) (_hctx : BlockContext L f) (m : ℕ) (_hm : 0 < m)
    (_hmult : ∀ (hne : (dvSideSet F f L.u L.ℓ).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F f (dvSideMin F f L.u L.ℓ hne) = (M₀ : ℕ∞)),
      L.r ^ m ∣ dvResPoly F H₀ hpin f L.u L.ℓ hne M₀ hp ∧
      ¬ L.r ^ (m + 1) ∣ dvResPoly F H₀ hpin f L.u L.ℓ hne M₀ hp),
    (blockFactor L f).natDegree = (F.e₁ * F.f₁) * L.ℓ * (L.r.natDegree * m) ∧
    mult₂ L f = m ∧
    IsDvPure F (blockFactor L f) L.u L.ℓ ∧
    ∀ (hne : (dvSideSet F (blockFactor L f) L.u L.ℓ).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F (blockFactor L f)
        (dvSideMin F (blockFactor L f) L.u L.ℓ hne) = (M₀ : ℕ∞)),
      dvResPoly F H₀ hpin (blockFactor L f) L.u L.ℓ hne M₀ hp = L.r ^ m

/-! ## 1. `Squarefree g₀` — the missing `BlockContext` leg, landed -/

section Squarefree

-- `[Finite (ResidueField O)]` is carried because C35b's whole `g₀` battery carries it (the
-- `s2Frame` signed signature's unused hypothesis); nothing here consumes it.
set_option linter.unusedSectionVars false

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **`g₀ = x³ − 2x + 4` is squarefree over any DVR in which `2` is a uniformizer.**
Divisibility descent; see the module docstring for the argument.  The `Separable` route is
unavailable (the resultant is a non-unit), so this is direct. -/
theorem g₀_squarefree (h2 : Irreducible (2 : O)) : Squarefree (g₀ O) := by
  have hprime : Prime (2 : O) := UniqueFactorizationMonoid.irreducible_iff_prime.mp h2
  intro p hp
  by_contra hpu
  have hg0 : (g₀ O) ≠ 0 := (g₀_monic (O := O)).ne_zero
  have hpne : p ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hp
    exact hg0 (zero_dvd_iff.mp hp)
  obtain ⟨q, hq⟩ := hp
  have hqne : q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hq
    exact hg0 hq
  -- the leading coefficient of `p` is a unit (it squares into `g₀`'s leading `1`)
  have hlead : p.leadingCoeff * (p.leadingCoeff * q.leadingCoeff) = 1 := by
    have h1 := congrArg Polynomial.leadingCoeff hq
    rw [(g₀_monic (O := O)).leadingCoeff, Polynomial.leadingCoeff_mul,
      Polynomial.leadingCoeff_mul] at h1
    linear_combination -h1
  have hAunit : IsUnit p.leadingCoeff := isUnit_of_dvd_one ⟨_, hlead.symm⟩
  -- degree bookkeeping: `2·deg p + deg q = 3`
  have hdeg3 : p.natDegree + p.natDegree + q.natDegree = 3 := by
    have h := congrArg Polynomial.natDegree hq
    rw [g₀_natDegree, Polynomial.natDegree_mul (mul_ne_zero hpne hpne) hqne,
      Polynomial.natDegree_mul hpne hpne] at h
    omega
  rcases Nat.lt_or_ge p.natDegree 1 with hd0 | hd1
  · -- constant repeated factor: its (leading) coefficient is a unit, so `p` is a unit
    have hdp : p.natDegree = 0 := by omega
    have hc : IsUnit (p.coeff 0) := by
      have h : p.leadingCoeff = p.coeff 0 := by
        rw [show p.leadingCoeff = p.coeff p.natDegree from rfl, hdp]
      rwa [h] at hAunit
    exact hpu ((Polynomial.eq_C_of_natDegree_eq_zero hdp) ▸ Polynomial.isUnit_C.mpr hc)
  · -- linear repeated factor: coefficient identities force `2 ∣ A` against `A` a unit
    have hdp : p.natDegree = 1 := by omega
    have hdq : q.natDegree = 1 := by omega
    have hpX : p = Polynomial.C (p.coeff 1) * Polynomial.X + Polynomial.C (p.coeff 0) :=
      Polynomial.eq_X_add_C_of_degree_le_one
        (Polynomial.natDegree_le_iff_degree_le.mp (le_of_eq hdp))
    have hqX : q = Polynomial.C (q.coeff 1) * Polynomial.X + Polynomial.C (q.coeff 0) :=
      Polynomial.eq_X_add_C_of_degree_le_one
        (Polynomial.natDegree_le_iff_degree_le.mp (le_of_eq hdq))
    set A := p.coeff 1 with hA_def
    set a := p.coeff 0 with ha_def
    set B := q.coeff 1 with hB_def
    set b := q.coeff 0 with hb_def
    have hA : IsUnit A := by
      have h : p.leadingCoeff = A := by
        rw [show p.leadingCoeff = p.coeff p.natDegree from rfl, hdp]
      rwa [h] at hAunit
    -- the canonical expansion of `(AX + a)²(BX + b)`
    have hcanon : g₀ O
        = Polynomial.C (A * A * B) * Polynomial.X ^ 3
          + Polynomial.C (A * A * b + 2 * (A * a * B)) * Polynomial.X ^ 2
          + Polynomial.C (2 * (A * a * b) + a * a * B) * Polynomial.X ^ 1
          + Polynomial.C (a * a * b) * Polynomial.X ^ 0 := by
      rw [hq, hpX, hqX]
      simp only [map_add, map_mul, map_ofNat]
      ring
    -- the three coefficient identities (curated `simp only` — the default set would split
    -- `C (A*A*B)` via `C_mul` and strand the `coeff` outside the association)
    have e3 : (1 : O) = A * A * B := by
      have h := congrArg (fun P : Polynomial O => P.coeff 3) hcanon
      simp only [g₀, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X] at h
      norm_num at h
      linear_combination h
    have e2 : (0 : O) = A * A * b + 2 * (A * a * B) := by
      have h := congrArg (fun P : Polynomial O => P.coeff 2) hcanon
      simp only [g₀, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X] at h
      norm_num at h
      linear_combination h
    have e1 : (-2 : O) = 2 * (A * a * b) + a * a * B := by
      have h := congrArg (fun P : Polynomial O => P.coeff 1) hcanon
      simp only [g₀, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X] at h
      norm_num at h
      linear_combination h
    -- `3a² = 2A²`
    have key : 3 * (a * a) = 2 * (A * A) := by
      linear_combination (A * A) * e1 + (-(2 * a * A)) * e2 + (3 * (a * a)) * e3
    -- `2 ∣ a`
    have h2a : (2 : O) ∣ a := by
      have h1 : (2 : O) ∣ 3 * (a * a) := key ▸ Dvd.intro _ rfl
      rcases hprime.dvd_mul.mp h1 with h3 | haa
      · exfalso
        have h1' : (2 : O) ∣ 1 := by
          have := dvd_sub h3 (dvd_refl (2 : O))
          norm_num at this
          exact this
        exact h2.not_isUnit (isUnit_of_dvd_one h1')
      · exact (hprime.dvd_mul.mp haa).elim id id
    obtain ⟨a', ha'⟩ := h2a
    -- `A² = 2·(3a′²)`, hence `2 ∣ A`
    have hAA : A * A = 2 * (3 * (a' * a')) := by
      apply mul_left_cancel₀ h2.ne_zero
      linear_combination (-1 : O) * key + (3 * (a + 2 * a')) * ha'
    have h2A : (2 : O) ∣ A := by
      have hAsq : (2 : O) ∣ A * A := Dvd.intro _ hAA.symm
      exact (hprime.dvd_mul.mp hAsq).elim id id
    -- `A` a unit + `2 ∣ A` ⟹ `2` a unit — against irreducibility
    obtain ⟨v, hv⟩ := hA.exists_right_inv
    exact h2.not_isUnit (isUnit_of_dvd_one (hv ▸ h2A.mul_right v))

end Squarefree

/-! ## 2. The `BlockContext`, the block, and the multiplicity hypothesis at the probe -/

section Probe

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-- `Φ′ = x² − 2` does not divide `g₀` — the mod is the nonzero constant `C 4`
(`g₀_divmod`). -/
theorem g₀_key_not_dvd : ¬ (s2Frame h2 hq).key ∣ g₀ O := by
  rw [key_eq h2 hq]
  intro hdvd
  have h0 : (g₀ O) %ₘ (s2Key O) = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd s2Key_monic).mpr hdvd
  rw [(g₀_divmod (O := O)).2] at h0
  exact pow_ne_zero 2 h2.ne_zero (Polynomial.C_eq_zero.mp h0)

/-- **the block context holds at `(L₀, g₀)`** — every leg was landed in C35b except
`Squarefree g₀`, supplied above. -/
theorem blockContext_g₀ : BlockContext (L₀ h2 hq) (g₀ O) :=
  ⟨g₀_monic, g₀_squarefree h2, g₀_key_not_dvd h2 hq, hne_g₀ h2 hq, 4, hp_g₀ h2 hq,
    by show 0 < dvSideDeg (s2Frame h2 hq) (g₀ O) 3 1 (hne_g₀ h2 hq)
       rw [dvsidedeg_g₀ h2 hq]; norm_num,
    by show (L₀ h2 hq).r ∣ ρ h2 hq
       rw [show (L₀ h2 hq).r = ρ h2 hq from rfl]⟩

/-- **`blockFactor L₀ g₀ = g₀`** — `g₀` inhabits the maximality existential (labelled,
divides itself, and every labelled divisor of `g₀` divides `g₀` trivially), so C.35's
uniqueness pins the choice. -/
theorem blockFactor_g₀ : blockFactor (L₀ h2 hq) (g₀ O) = g₀ O :=
  blockFactor_eq_of_frontier (L₀ h2 hq) (hasLabel_g₀ h2 hq) dvd_rfl (fun _ _ h' => h')

/-- ★ **the FLOOR conjunct of C.67 is TRUE at the probe**: `mult₂ L₀ g₀ = ⌊3/2⌋ = 1`.
The refutation below kills the EXACT-degree conjunct at the SAME instance — the D-CARRY
fault line in one display. -/
theorem mult₂_g₀ : mult₂ (L₀ h2 hq) (g₀ O) = 1 := by
  have hkd : (L₀ h2 hq).keyDeg₂ = 2 := by
    rw [LevelDatum.keyDeg₂, e1_eq h2 hq, f1_eq h2 hq,
      show (L₀ h2 hq).ℓ = 1 from rfl,
      show (L₀ h2 hq).r = ρ h2 hq from rfl, ρ_natDegree h2 hq]
  rw [mult₂, blockFactor_g₀ h2 hq, g₀_natDegree, hkd]

/-- **the multiplicity hypothesis of C.67 HOLDS at `m = 1`**: the level residual of `g₀` is
`ρ` itself, so `ρ¹ ∣ ρ` on the nose and `¬ ρ² ∣ ρ` by degrees. -/
theorem hmult_g₀ :
    ∀ (hne : (dvSideSet (s2Frame h2 hq) (g₀ O) (L₀ h2 hq).u (L₀ h2 hq).ℓ).Nonempty) (M₀ : ℕ)
      (hp : dvHgt (s2Frame h2 hq) (g₀ O)
        (dvSideMin (s2Frame h2 hq) (g₀ O) (L₀ h2 hq).u (L₀ h2 hq).ℓ hne) = (M₀ : ℕ∞)),
      (L₀ h2 hq).r ^ 1 ∣ dvResPoly (s2Frame h2 hq) 1 (s2Frame_pin h2 hq) (g₀ O)
        (L₀ h2 hq).u (L₀ h2 hq).ℓ hne M₀ hp ∧
      ¬ (L₀ h2 hq).r ^ (1 + 1) ∣ dvResPoly (s2Frame h2 hq) 1 (s2Frame_pin h2 hq) (g₀ O)
        (L₀ h2 hq).u (L₀ h2 hq).ℓ hne M₀ hp := by
  intro hne M₀ hp
  -- the pin forces `M₀ = 4`
  have hM : M₀ = 4 := by
    have h4 : (M₀ : ℕ∞) = ((4 : ℕ) : ℕ∞) := hp.symm.trans (hp_g₀ h2 hq)
    exact_mod_cast h4
  subst hM
  have hres : dvResPoly (s2Frame h2 hq) 1 (s2Frame_pin h2 hq) (g₀ O)
      (L₀ h2 hq).u (L₀ h2 hq).ℓ hne 4 hp = ρ h2 hq := rfl
  constructor
  · rw [pow_one, hres, show (L₀ h2 hq).r = ρ h2 hq from rfl]
  · rw [hres, show (L₀ h2 hq).r = ρ h2 hq from rfl]
    intro hdvd
    letI : Field ((s2Frame h2 hq).stageField 1 (s2Frame_pin h2 hq)) :=
      s2StageFieldInst h2 hq 1 (s2Frame_pin h2 hq)
    have hne0 : (ρ h2 hq) ≠ 0 := fun hz => ρ_coeff_zero_ne h2 hq (by rw [hz]; simp)
    have hle := Polynomial.natDegree_le_of_dvd hdvd hne0
    rw [Polynomial.natDegree_pow, ρ_natDegree h2 hq] at hle
    omega

end Probe

/-! ## 3. THE REFUTATION, absolute over `ℤ_[2]` -/

section Absolute

/-- ★ **NODE C.67's signed `multiplicity_tie` is FALSE.**  At `(s2Frame, L₀, g₀)` over
`ℤ_[2]` with `m = 1`: every hypothesis holds (`blockContext_g₀`, `hmult_g₀`), and the
EXACT-degree conjunct demands `3 = 2`. -/
theorem multiplicityTie_false : ¬ MultiplicityTieStatement := by
  intro hax
  have h := hax ℤ_[2] (2 : ℤ_[2]) (s2Frame h2_padic rc2) 1
    (s2Frame_pin h2_padic rc2) (L₀ h2_padic rc2) h2_padic (g₀ ℤ_[2])
    (blockContext_g₀ h2_padic rc2) 1 Nat.one_pos (hmult_g₀ h2_padic rc2)
  have h1 := h.1
  rw [blockFactor_g₀ h2_padic rc2, g₀_natDegree, e1_eq h2_padic rc2, f1_eq h2_padic rc2,
    show (L₀ h2_padic rc2).ℓ = 1 from rfl,
    show (L₀ h2_padic rc2).r = ρ h2_padic rc2 from rfl, ρ_natDegree h2_padic rc2] at h1
  norm_num at h1

end Absolute

end Uniformity.Density.Tower.C67

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C67.MultiplicityTieStatement
#print axioms Uniformity.Density.Tower.C67.g₀_squarefree
#print axioms Uniformity.Density.Tower.C67.blockContext_g₀
#print axioms Uniformity.Density.Tower.C67.blockFactor_g₀
#print axioms Uniformity.Density.Tower.C67.mult₂_g₀
#print axioms Uniformity.Density.Tower.C67.hmult_g₀
#print axioms Uniformity.Density.Tower.C67.multiplicityTie_false

end AxCheck
