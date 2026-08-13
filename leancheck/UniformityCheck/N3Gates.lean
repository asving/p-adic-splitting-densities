/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity
import UniformityCheck.N3Base
import UniformityCheck.N3Certs
import UniformityCheck.N3Norm
import UniformityCheck.CubicCount
import UniformityCheck.N3Density

/-!
# UniformityCheck.N3Gates — the five `n = 3` lower bounds and the certified brackets

The level-1 families (`{(1,3)}` and `{(1,1),(1,2)}`) are counted on the residue field by
`CubicCount` and transported here through `res1Equiv : Res O 1 ≃+* ResidueField O`; the level-2
families (`{(3,1)}` and `{(1,1),(2,1)}`) are counted by the valuation strata of `Counting`; the
split type gets the single deep class of `X(X-1)(X-π)`.

| type | certificate level | classes | lower bound |
|---|---|---|---|
| `c3split` `{(1,1)}³` | 3 | 1 | `1/q⁹` |
| `c3linInert` `{(1,1),(1,2)}` | 1 | `q²(q-1)/2` | `(q³-q²)/(2q³) = (q-1)/(2q)` |
| `c3inert` `{(1,3)}` | 1 | `(q³-q)/3` | `(q³-q)/(3q³)` |
| `c3linRam` `{(1,1),(2,1)}` | 2 | `q²(q-1)²` | `(q-1)²/q⁴` |
| `c3ram` `{(3,1)}` | 2 | `q²(q-1)` | `(q-1)/q⁴` |

`bracket_five` (N3Density) turns the five lower bounds into an upper bound on each type through
`sum_genuineDensity_le_one`, and `gate_bracket3_padic_two` / `_three` instantiate at `q = 2, 3`.
`gate_bracket3_hmenu3_two` / `_three` check, by `norm_num`, that the informal corpus's predicted
cubic densities (`lean/notes/openmath/HMENU3_PROOF_2026-08-08.md`, COROLLARY HM3.D) lie inside
every certified bracket.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace UniformityCheck

open Uniformity Uniformity.Density IsLocalRing Polynomial

/-! ## 1. Level 1 is the residue field -/

section Level1

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- `O ⧸ 𝔪 ^ 1 ≃+* O ⧸ 𝔪`. -/
noncomputable def res1Equiv (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] : Res O 1 ≃+* ResidueField O :=
  Ideal.quotEquivOfEq (pow_one (maximalIdeal O))

theorem res1Equiv_mk (x : O) :
    res1Equiv O (Ideal.Quotient.mk ((maximalIdeal O) ^ 1) x) = residue O x :=
  Ideal.quotEquivOfEq_mk _ x

/-- The level-1 class with prescribed residue coefficient vector. -/
noncomputable def liftRes1 (v : Fin 3 → ResidueField O) : Coeff O 3 1 :=
  fun i => (res1Equiv O).symm (v i)

theorem liftRes1_injective : Function.Injective (liftRes1 (O := O)) := fun _ _ h =>
  funext fun i => (res1Equiv O).symm.injective (congrFun h i)

theorem resVec_of_proj {v : Fin 3 → ResidueField O} {b : Fin 3 → O}
    (hb : proj O 3 1 b = liftRes1 v) : resVec b = v := by
  funext i
  have hi : (Ideal.Quotient.mk _ (b i) : Res O 1) = (res1Equiv O).symm (v i) := congrFun hb i
  have := congrArg (res1Equiv O) hi
  rw [res1Equiv_mk, RingEquiv.apply_symm_apply] at this
  exact this

theorem sub_mem_of_residue_eq {x y : O} (h : residue O x = residue O y) :
    x - y ∈ maximalIdeal O := by
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, h, sub_self]

/-! ### `{(1,3)}` -/

theorem cub3_eval {K : Type*} [CommRing K] (v : Fin 3 → K) (y : K) :
    (cub3 v).eval y = y ^ 3 + v 2 * y ^ 2 + v 1 * y + v 0 := by
  rw [cub3]
  simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C]

/-- **CUBIC INERT, level 1.** A class whose residue cubic has no root is `{(1,3)}`-decided. -/
theorem inert3_decided {v : Fin 3 → ResidueField O} (hv : NoRootCubic v) :
    DecidedAt O 3 c3inert 1 (liftRes1 v) := by
  intro b hb
  refine typeOf_inert3_of_residue_irreducible ?_
  have hres : resVec b = v := resVec_of_proj hb
  rw [monicPoly_eq_cub3, cub3_map, show (fun i => residue O (b i)) = v from hres]
  refine irreducible_of_degree_le_three_of_not_isRoot ?_ (fun y hy => ?_)
  · rw [cub3_natDegree]; decide
  · exact hv y (by rw [← cub3_eval v y]; exact hy)

/-! ### `{(1,1),(1,2)}` -/

theorem linAniCoeff_zero {K : Type*} [Field K] (ρ : K) (p : K × K) :
    linAniCoeff ρ p 0 = -(ρ * p.1) := by simp [linAniCoeff]

theorem linAniCoeff_one {K : Type*} [Field K] (ρ : K) (p : K × K) :
    linAniCoeff ρ p 1 = p.1 + ρ * p.2 := by simp [linAniCoeff]

theorem linAniCoeff_two {K : Type*} [Field K] (ρ : K) (p : K × K) :
    linAniCoeff ρ p 2 = -(p.2 + ρ) := by simp [linAniCoeff]

theorem aniK_neg {K : Type*} [Field K] (x y : K) : AniK (x, y) → AniK (x, -y) := by
  intro h t ht
  exact h (-t) (by simp only at ht ⊢; linear_combination ht)

/-- **LINEAR × INERT QUADRATIC, level 1.** -/
theorem linInert_decided_res {v : Fin 3 → ResidueField O} (hv : LinAni v) :
    DecidedAt O 3 c3linInert 1 (liftRes1 v) := by
  obtain ⟨ρbar, p, hp, rfl⟩ := hv
  obtain ⟨ρ, hρ⟩ := IsLocalRing.residue_surjective (R := O) ρbar
  obtain ⟨b₀, hb₀⟩ := IsLocalRing.residue_surjective (R := O) p.1
  obtain ⟨b₁, hb₁⟩ := IsLocalRing.residue_surjective (R := O) p.2
  intro b hb
  have hres : resVec b = linAniCoeff ρbar p := resVec_of_proj hb
  have hr : ∀ i, residue O (b i) = linAniCoeff ρbar p i := fun i => congrFun hres i
  have hani : Anisotropic ![b₀, -b₁] := by
    rw [anisotropic_iff_aniK]
    simp only [map_neg, hb₀, hb₁]
    exact aniK_neg p.1 p.2 hp
  refine typeOf_linInert_of_residue ρ b₀ (-b₁) hani ?_ ?_ ?_
  · refine sub_mem_of_residue_eq ?_
    rw [hr 2, map_sub, map_neg, hb₁, hρ, linAniCoeff_two]
    ring
  · refine sub_mem_of_residue_eq ?_
    rw [hr 1, map_sub, map_mul, map_neg, hb₀, hb₁, hρ, linAniCoeff_one]
    ring
  · have hid : b 0 + ρ * b₀ = b 0 - -(ρ * b₀) := by ring
    rw [hid]
    refine sub_mem_of_residue_eq ?_
    rw [hr 0, map_neg, map_mul, hb₀, hρ, linAniCoeff_zero]

/-! ### `{(3,1)}` -/

/-- **EISENSTEIN CUBIC, level 2.** -/
theorem ram3_decided {π : O} (hπ : Irreducible π)
    (x : exactSet π 1 2) (y z : dvdSet π 1 2) :
    DecidedAt O 3 c3ram 2 (![x.1, y.1, z.1] : Coeff O 3 2) := by
  intro b hb
  have hb0 : (Ideal.Quotient.mk _ (b 0) : Res O 2) = x.1 := congrFun hb 0
  have hb1 : (Ideal.Quotient.mk _ (b 1) : Res O 2) = y.1 := congrFun hb 1
  have hb2 : (Ideal.Quotient.mk _ (b 2) : Res O 2) = z.1 := congrFun hb 2
  have h0 : b 0 ∈ maximalIdeal O := by
    refine (mem_maximalIdeal_iff_dvd hπ _).2 ?_
    have := (dvd_res_iff hπ (k := 1) (N := 2) (by omega) (b 0)).1 (by rw [hb0]; exact x.2.1)
    simpa using this
  have h0' : b 0 ∉ (maximalIdeal O) ^ 2 := by
    intro hmem
    refine x.2.2 ?_
    rw [← hb0]
    exact (dvd_res_iff hπ (k := 2) (N := 2) (by omega) (b 0)).2
      ((mem_maximalIdeal_pow_iff_dvd hπ 2 _).1 hmem)
  have h1 : b 1 ∈ maximalIdeal O := by
    refine (mem_maximalIdeal_iff_dvd hπ _).2 ?_
    have := (dvd_res_iff hπ (k := 1) (N := 2) (by omega) (b 1)).1 (by rw [hb1]; exact y.2)
    simpa using this
  have h2 : b 2 ∈ maximalIdeal O := by
    refine (mem_maximalIdeal_iff_dvd hπ _).2 ?_
    have := (dvd_res_iff hπ (k := 1) (N := 2) (by omega) (b 2)).1 (by rw [hb2]; exact z.2)
    simpa using this
  exact typeOf_ram3_of_eisenstein h0 h0' h1 h2

end Level1

/-! ## 2. The five lower bounds -/

section Lowers

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- **G-INERT3.** `(q³ - q) / (3 q³) ≤ genuineDensity O 3 c3inert`. -/
theorem gate_inert3_lower :
    ((residueCard O : ℝ) ^ 3 - (residueCard O : ℝ)) / (3 * (residueCard O : ℝ) ^ 3)
      ≤ genuineDensity O 3 c3inert := by
  classical
  have hbound := genuineDensity_ge_of_inj (O := O) (n := 3) (N := 1) (σ := c3inert)
    (A := {v : Fin 3 → ResidueField O // NoRootCubic v})
    (fun v => liftRes1 v.1)
    (fun v w h => Subtype.ext (liftRes1_injective h))
    (fun v => inert3_decided v.2)
  have hcount := three_mul_card_noRootCubic (ResidueField O)
  have hcast : (3 : ℝ) * (Nat.card {v : Fin 3 → ResidueField O // NoRootCubic v} : ℝ)
      + (residueCard O : ℝ) = (residueCard O : ℝ) ^ 3 := by
    have := congrArg (fun n : ℕ => (n : ℝ)) hcount
    push_cast at this
    simpa [residueCard] using this
  have hq : (0 : ℝ) < (residueCard O : ℝ) := qR_pos
  refine le_trans (le_of_eq ?_) hbound
  rw [show (3 : ℕ) * 1 = 3 from rfl]
  field_simp
  linarith [hcast]

/-- **G-LININERT3.** `(q³ - q²) / (2 q³) ≤ genuineDensity O 3 c3linInert`. -/
theorem gate_linInert3_lower :
    ((residueCard O : ℝ) ^ 3 - (residueCard O : ℝ) ^ 2) / (2 * (residueCard O : ℝ) ^ 3)
      ≤ genuineDensity O 3 c3linInert := by
  classical
  have hbound := genuineDensity_ge_of_inj (O := O) (n := 3) (N := 1) (σ := c3linInert)
    (A := {v : Fin 3 → ResidueField O // LinAni v})
    (fun v => liftRes1 v.1)
    (fun v w h => Subtype.ext (liftRes1_injective h))
    (fun v => linInert_decided_res v.2)
  have hcount := two_mul_card_linAni (ResidueField O)
  have hcast : (2 : ℝ) * (Nat.card {v : Fin 3 → ResidueField O // LinAni v} : ℝ)
      + (residueCard O : ℝ) ^ 2 = (residueCard O : ℝ) ^ 3 := by
    have := congrArg (fun n : ℕ => (n : ℝ)) hcount
    push_cast at this
    simpa [residueCard] using this
  have hq : (0 : ℝ) < (residueCard O : ℝ) := qR_pos
  refine le_trans (le_of_eq ?_) hbound
  rw [show (3 : ℕ) * 1 = 3 from rfl]
  field_simp
  linarith [hcast]

/-- **G-RAM3.** `(q - 1) / q⁴ ≤ genuineDensity O 3 c3ram`. -/
theorem gate_ram3_lower :
    ((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ 4 ≤ genuineDensity O 3 c3ram := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hbound := genuineDensity_ge_of_inj (O := O) (n := 3) (N := 2) (σ := c3ram)
    (A := (exactSet π 1 2) × (dvdSet π 1 2) × (dvdSet π 1 2))
    (fun p => ![p.1.1, p.2.1.1, p.2.2.1])
    (by
      rintro ⟨x, y, z⟩ ⟨x', y', z'⟩ h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      have h2 := congrFun h 2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons] at h0 h1 h2
      exact Prod.ext (Subtype.ext h0) (Prod.ext (Subtype.ext h1) (Subtype.ext h2)))
    (fun p => ram3_decided hπ p.1 p.2.1 p.2.2)
  have he := card_exactSet_two (O := O) hπ
  have hd := card_dvdSet_two (O := O) hπ
  have hq2 : (2 : ℕ) ≤ residueCard O := two_le_residueCard O
  have hcards : Nat.card ((exactSet π 1 2) × (dvdSet π 1 2) × (dvdSet π 1 2))
      = Nat.card (exactSet π 1 2) * (Nat.card (dvdSet π 1 2) * Nat.card (dvdSet π 1 2)) := by
    rw [Nat.card_prod, Nat.card_prod]
  have hE : Nat.card (exactSet π 1 2) = residueCard O - 1 := by omega
  have hq1 : (1 : ℕ) ≤ residueCard O := by omega
  have hcast : (Nat.card ((exactSet π 1 2) × (dvdSet π 1 2) × (dvdSet π 1 2)) : ℝ)
      = ((residueCard O : ℝ) - 1) * (residueCard O : ℝ) ^ 2 := by
    rw [hcards, hd, hE]
    push_cast [Nat.cast_sub hq1]
    ring
  rw [hcast] at hbound
  refine le_trans (le_of_eq ?_) hbound
  have hq : (0 : ℝ) < (residueCard O : ℝ) := qR_pos
  rw [show (3 : ℕ) * 2 = 6 from rfl]
  field_simp

/-- **THE FIVE `n = 3` LOWER BOUNDS**, general `O`. -/
theorem lowers_three :
    1 / (residueCard O : ℝ) ^ 9 ≤ genuineDensity O 3 c3split
    ∧ ((residueCard O : ℝ) ^ 3 - (residueCard O : ℝ) ^ 2) / (2 * (residueCard O : ℝ) ^ 3)
        ≤ genuineDensity O 3 c3linInert
    ∧ ((residueCard O : ℝ) ^ 3 - (residueCard O : ℝ)) / (3 * (residueCard O : ℝ) ^ 3)
        ≤ genuineDensity O 3 c3inert
    ∧ ((residueCard O : ℝ) - 1) ^ 2 / (residueCard O : ℝ) ^ 4 ≤ genuineDensity O 3 c3linRam
    ∧ ((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ 4 ≤ genuineDensity O 3 c3ram :=
  ⟨gate_split3_lower, gate_linInert3_lower, gate_inert3_lower, gate_linRam_lower,
    gate_ram3_lower⟩

end Lowers

/-! ## 3. The certified brackets at `q = 2` and `q = 3` -/

section BracketPadic

/-- The five certified lower bounds over `ℤ_[2]`. -/
theorem lowers3_padic_two :
    (1 : ℝ) / 512 ≤ genuineDensity ℤ_[2] 3 c3split
    ∧ (1 : ℝ) / 4 ≤ genuineDensity ℤ_[2] 3 c3linInert
    ∧ (1 : ℝ) / 4 ≤ genuineDensity ℤ_[2] 3 c3inert
    ∧ (1 : ℝ) / 16 ≤ genuineDensity ℤ_[2] 3 c3linRam
    ∧ (1 : ℝ) / 16 ≤ genuineDensity ℤ_[2] 3 c3ram := by
  obtain ⟨hs, hi, hc, hr, ht⟩ := lowers_three (O := ℤ_[2])
  rw [residueCard_padicInt 2] at hs hi hc hr ht
  norm_num at hs hi hc hr ht ⊢
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- The five certified lower bounds over `ℤ_[3]`. -/
theorem lowers3_padic_three :
    (1 : ℝ) / 19683 ≤ genuineDensity ℤ_[3] 3 c3split
    ∧ (1 : ℝ) / 3 ≤ genuineDensity ℤ_[3] 3 c3linInert
    ∧ (8 : ℝ) / 27 ≤ genuineDensity ℤ_[3] 3 c3inert
    ∧ (4 : ℝ) / 81 ≤ genuineDensity ℤ_[3] 3 c3linRam
    ∧ (2 : ℝ) / 81 ≤ genuineDensity ℤ_[3] 3 c3ram := by
  obtain ⟨hs, hi, hc, hr, ht⟩ := lowers_three (O := ℤ_[3])
  rw [residueCard_padicInt 3] at hs hi hc hr ht
  norm_num at hs hi hc hr ht ⊢
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- **GATE BRACKET (n = 3), q = 2.** -/
theorem gate_bracket3_padic_two :
    ((1 : ℝ) / 512 ≤ genuineDensity ℤ_[2] 3 c3split
        ∧ genuineDensity ℤ_[2] 3 c3split ≤ 3 / 8)
    ∧ ((1 : ℝ) / 4 ≤ genuineDensity ℤ_[2] 3 c3linInert
        ∧ genuineDensity ℤ_[2] 3 c3linInert ≤ 319 / 512)
    ∧ ((1 : ℝ) / 4 ≤ genuineDensity ℤ_[2] 3 c3inert
        ∧ genuineDensity ℤ_[2] 3 c3inert ≤ 319 / 512)
    ∧ ((1 : ℝ) / 16 ≤ genuineDensity ℤ_[2] 3 c3linRam
        ∧ genuineDensity ℤ_[2] 3 c3linRam ≤ 223 / 512)
    ∧ ((1 : ℝ) / 16 ≤ genuineDensity ℤ_[2] 3 c3ram
        ∧ genuineDensity ℤ_[2] 3 c3ram ≤ 223 / 512) := by
  obtain ⟨hs, hi, hc, hr, ht⟩ := lowers3_padic_two
  obtain ⟨us, ui, uc, ur, ut⟩ := bracket_five hs hi hc hr ht
  exact ⟨⟨hs, by linarith⟩, ⟨hi, by linarith⟩, ⟨hc, by linarith⟩, ⟨hr, by linarith⟩,
    ⟨ht, by linarith⟩⟩

/-- **GATE BRACKET (n = 3), q = 3.** -/
theorem gate_bracket3_padic_three :
    ((1 : ℝ) / 19683 ≤ genuineDensity ℤ_[3] 3 c3split
        ∧ genuineDensity ℤ_[3] 3 c3split ≤ 5832 / 19683)
    ∧ ((1 : ℝ) / 3 ≤ genuineDensity ℤ_[3] 3 c3linInert
        ∧ genuineDensity ℤ_[3] 3 c3linInert ≤ 12392 / 19683)
    ∧ ((8 : ℝ) / 27 ≤ genuineDensity ℤ_[3] 3 c3inert
        ∧ genuineDensity ℤ_[3] 3 c3inert ≤ 11663 / 19683)
    ∧ ((4 : ℝ) / 81 ≤ genuineDensity ℤ_[3] 3 c3linRam
        ∧ genuineDensity ℤ_[3] 3 c3linRam ≤ 6803 / 19683)
    ∧ ((2 : ℝ) / 81 ≤ genuineDensity ℤ_[3] 3 c3ram
        ∧ genuineDensity ℤ_[3] 3 c3ram ≤ 6317 / 19683) := by
  obtain ⟨hs, hi, hc, hr, ht⟩ := lowers3_padic_three
  obtain ⟨us, ui, uc, ur, ut⟩ := bracket_five hs hi hc hr ht
  exact ⟨⟨hs, by linarith⟩, ⟨hi, by linarith⟩, ⟨hc, by linarith⟩, ⟨hr, by linarith⟩,
    ⟨ht, by linarith⟩⟩

/-- **HMENU3 containment, q = 2.** The corpus's predicted cubic densities
`(4/93, 28/93, 8/31, 22/93, 5/31)` all lie inside the certified brackets. -/
theorem gate_bracket3_hmenu3_two :
    ((1 : ℝ) / 512 ≤ 4 / 93 ∧ (4 : ℝ) / 93 ≤ 3 / 8)
    ∧ ((1 : ℝ) / 4 ≤ 28 / 93 ∧ (28 : ℝ) / 93 ≤ 319 / 512)
    ∧ ((1 : ℝ) / 4 ≤ 8 / 31 ∧ (8 : ℝ) / 31 ≤ 319 / 512)
    ∧ ((1 : ℝ) / 16 ≤ 22 / 93 ∧ (22 : ℝ) / 93 ≤ 223 / 512)
    ∧ ((1 : ℝ) / 16 ≤ 5 / 31 ∧ (5 : ℝ) / 31 ≤ 223 / 512) := by
  norm_num

/-- **HMENU3 containment, q = 3.** The corpus's predicted cubic densities
`(63/968, 351/968, 36/121, 93/484, 10/121)` all lie inside the certified brackets. -/
theorem gate_bracket3_hmenu3_three :
    ((1 : ℝ) / 19683 ≤ 63 / 968 ∧ (63 : ℝ) / 968 ≤ 5832 / 19683)
    ∧ ((1 : ℝ) / 3 ≤ 351 / 968 ∧ (351 : ℝ) / 968 ≤ 12392 / 19683)
    ∧ ((8 : ℝ) / 27 ≤ 36 / 121 ∧ (36 : ℝ) / 121 ≤ 11663 / 19683)
    ∧ ((4 : ℝ) / 81 ≤ 93 / 484 ∧ (93 : ℝ) / 484 ≤ 6803 / 19683)
    ∧ ((2 : ℝ) / 81 ≤ 10 / 121 ∧ (10 : ℝ) / 121 ≤ 6317 / 19683) := by
  norm_num

/-- The five HMENU3 values sum to exactly `1` at `q = 2` and at `q = 3` — an arithmetic check on
the corpus's own table, independent of anything proved here. -/
theorem hmenu3_sums_to_one :
    (4 : ℝ) / 93 + 28 / 93 + 8 / 31 + 22 / 93 + 5 / 31 = 1
    ∧ (63 : ℝ) / 968 + 351 / 968 + 36 / 121 + 93 / 484 + 10 / 121 = 1 := by
  norm_num

end BracketPadic

section AxCheck

#print axioms UniformityCheck.gate_split3_lower
#print axioms UniformityCheck.gate_linInert3_lower
#print axioms UniformityCheck.gate_inert3_lower
#print axioms UniformityCheck.gate_linRam_lower
#print axioms UniformityCheck.gate_ram3_lower
#print axioms UniformityCheck.lowers_three
#print axioms UniformityCheck.bracket_five
#print axioms UniformityCheck.gate_bracket3_padic_two
#print axioms UniformityCheck.gate_bracket3_padic_three
#print axioms UniformityCheck.gate_bracket3_hmenu3_two
#print axioms UniformityCheck.gate_bracket3_hmenu3_three
#print axioms UniformityCheck.typeOf_split3_of_residue
#print axioms UniformityCheck.typeOf_split3_of_deep
#print axioms UniformityCheck.typeOf_linInert_of_residue
#print axioms UniformityCheck.typeOf_linRam_of_residue
#print axioms UniformityCheck.typeOf_ram3_of_eisenstein
#print axioms UniformityCheck.typeOf_inert3_of_residue_irreducible
#print axioms UniformityCheck.three_mul_card_noRootCubic
#print axioms UniformityCheck.two_mul_card_linAni

end AxCheck

end UniformityCheck
