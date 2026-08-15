/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G56
import Uniformity.ChapG.G60
import Uniformity.ChapG.G61I

/-!
# Uniformity.ChapG.G61b — the bound `(q³−q²)/(2q³) ≤ decidedDensity O 3 c3linInert`

**Chapter G, NODE G.61b** (`blueprint/CHAP-G_base_cases_menus.md` §9), the second of the five
SPLIT-MANDATED sub-nodes of G.61: the family `{(1,1),(1,2)}` — a linear factor times an unramified
(inert) quadratic.

A **level-1** family, counted on the residue field. A class whose residue cubic factors as
`(X − ρ̄)(X² − b₁X + b₀)` with the quadratic part rootless is `{(1,1),(1,2)}`-decided. G.60b counts
those residue cubics subtraction-free (`2·#{LinAni} + q² = q³`), so the family has `(q³−q²)/2`
level-1 classes and the bound is `(q³−q²)/(2q³) = (q−1)/(2q)`.

DEPENDS: G.56 (`typeOf_linInert_of_residue`), G.60b (`two_mul_card_linAni`, `LinAni`), G.61.0
(`decidedDensity_ge_of_inj`, `liftRes1`, `liftRes1_injective`,
`residue_comp_of_proj_liftRes1`) · landed `AniForm` (`AnisotropicForms.lean:55`),
`monicPoly_monic`, `monicPoly_natDegree`, `qR_pos`; mathlib
`Polynomial.irreducible_of_degree_le_three_of_not_isRoot`, `IsLocalRing.residue_surjective`.
(The `Fin 2` expansion/evaluation lemmas are re-derived privately here: `QuadCert.lean`'s
`monicPoly_two_expand` / `monicPoly_two_eval` are stated over a discrete valuation ring, hence
unavailable over the residue FIELD, where this node's quadratic cofactor lives.)

PROOF sketch. Unpack `LinAni v` as `v = ![−ρ̄b₀, b₀ + ρ̄b₁, −(b₁ + ρ̄)]` with `AniForm (b₀, b₁)`.
Take the residual quadratic to be `g₀ := monicPoly ![b₀, −b₁] = X² − b₁X + b₀`: it is monic of
degree `2` by construction, and irreducible because `AniForm` says exactly that it has no root
(mathlib's degree-`≤ 3` criterion). The reduction of any lift `b` of `liftRes1 v` is `monicPoly v`
(`residue_comp_of_proj_liftRes1`), which equals `(X − C ρ̄) · g₀` by expanding both sides, so G.56
fires. Injectivity of `liftRes1` then feeds `decidedDensity_ge_of_inj` with
`A := {v // LinAni v}`.

⚠ RE-DERIVATION TARGET (blueprint H-9): `leancheck/UniformityCheck/N3Gates.lean`
(`linInert_decided_res`, `gate_linInert3_lower`) lands the same content. Re-derived here against
`leanfinal`'s own G.56 certificate, whose hypothesis shape is a residual FACTORIZATION
`f̄ = (X − ρ̄) g₀` with `g₀` monic of degree 2 and irreducible — not `leancheck`'s
`Anisotropic ![β₀, β₁]` plus three congruences — so the whole middle of the proof differs.
G.60b's `linAniCoeff` is private to that node, so the three coefficient values are read off the
`LinAni` witness by `rw`-then-`rfl` (definitional unfolding, which privacy does not block).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace Uniformity.Density

open IsLocalRing Polynomial Menu

/-! ## 1. The residual factorization, over any field -/

section Residual

variable {K : Type*} [Field K]

/-- Reducing a monic polynomial along a ring hom reduces its coefficient vector. -/
private theorem g61b_map_monicPoly {R S : Type*} [CommRing R] [IsDomain R] [CommRing S]
    [IsDomain S] (φ : R →+* S) {n : ℕ} (a : Fin n → R) :
    (monicPoly a).map φ = monicPoly (fun i => φ (a i)) := by
  simp only [monicPoly, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]

private theorem g61b_cubic_expand (a : Fin 3 → K) :
    monicPoly a = X ^ 3 + C (a 2) * X ^ 2 + C (a 1) * X + C (a 0) := by
  simp only [monicPoly, Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero,
    pow_one, mul_one]
  ring

/-- The `Fin 2` companion of `g61b_cubic_expand`. (`QuadCert.lean`'s `monicPoly_two_expand` is
stated over a discrete valuation ring, so it is unavailable over the residue FIELD.) -/
private theorem g61b_quad_expand (a : Fin 2 → K) :
    monicPoly a = X ^ 2 + C (a 1) * X + C (a 0) := by
  simp only [monicPoly, Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one]
  ring

private theorem g61b_quad_eval (a : Fin 2 → K) (x : K) :
    (monicPoly a).eval x = x ^ 2 + a 1 * x + a 0 := by
  rw [g61b_quad_expand]
  simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C]

/-- `X³ + c₂X² + c₁X + c₀ = (X − ρ)(X² − b₁X + b₀)` whenever the coefficients match. -/
private theorem g61b_cubic_factor {c : Fin 3 → K} (ρ : K) (p : K × K)
    (h0 : c 0 = -(ρ * p.1)) (h1 : c 1 = p.1 + ρ * p.2) (h2 : c 2 = -(p.2 + ρ)) :
    monicPoly c = (X - C ρ) * monicPoly (![p.1, -p.2] : Fin 2 → K) := by
  rw [g61b_cubic_expand, g61b_quad_expand, h0, h1, h2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_neg, map_add, map_mul]
  ring

/-- An anisotropic pair gives an irreducible monic quadratic. -/
private theorem g61b_irreducible_of_aniForm {p : K × K} (hp : AniForm p) :
    Irreducible (monicPoly (![p.1, -p.2] : Fin 2 → K)) := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ (fun y hy => ?_)
  · rw [Finset.mem_Icc, monicPoly_natDegree]
    omega
  · refine hp y ?_
    have hev : (monicPoly (![p.1, -p.2] : Fin 2 → K)).eval y = y ^ 2 - p.2 * y + p.1 := by
      rw [g61b_quad_eval]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    rw [← hev]
    exact hy

end Residual

/-! ## 2. The level-1 certificate -/

section Cert

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **LINEAR × INERT QUADRATIC, level 1.** A class whose residue cubic is a linear factor times a
rootless quadratic is `{(1,1),(1,2)}`-decided. -/
theorem linInert_decided_res [IsAdicComplete (maximalIdeal O) O]
    {v : Fin 3 → ResidueField O} (hv : LinAni v) :
    DecidedAt O 3 c3linInert 1 (liftRes1 v) := by
  obtain ⟨ρbar, p, hp, hveq⟩ := hv
  have hv0 : v 0 = -(ρbar * p.1) := by rw [hveq]; rfl
  have hv1 : v 1 = p.1 + ρbar * p.2 := by rw [hveq]; rfl
  have hv2 : v 2 = -(p.2 + ρbar) := by rw [hveq]; rfl
  obtain ⟨ρ, hρ⟩ := IsLocalRing.residue_surjective (R := O) ρbar
  intro b hb
  have hres : (fun i => residue O (b i)) = v := residue_comp_of_proj_liftRes1 hb
  refine typeOf_linInert_of_residue (ρ := ρ)
    (g₀ := monicPoly (![p.1, -p.2] : Fin 2 → ResidueField O))
    (monicPoly_monic _) (monicPoly_natDegree _) (g61b_irreducible_of_aniForm hp) ?_
  rw [g61b_map_monicPoly (residue O) b, hres, hρ]
  exact g61b_cubic_factor ρbar p hv0 hv1 hv2

end Cert

/-! ## 3. The gate -/

section Gate

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **G.61b.** `(q³ − q²) / (2 q³) ≤ decidedDensity O 3 c3linInert`, every `O`. A LOWER BOUND, not
the density. -/
theorem gate_linInert3_lower [IsAdicComplete (maximalIdeal O) O] :
    ((residueCard O : ℝ) ^ 3 - (residueCard O : ℝ) ^ 2) / (2 * (residueCard O : ℝ) ^ 3)
      ≤ decidedDensity O 3 c3linInert := by
  classical
  have hbound := decidedDensity_ge_of_inj (O := O) (n := 3) (N := 1) (σ := c3linInert)
    (A := {v : Fin 3 → ResidueField O // LinAni v})
    (fun v => liftRes1 v.1)
    (fun _ _ h => Subtype.ext (liftRes1_injective h))
    (fun v => linInert_decided_res v.2)
  have hcount := two_mul_card_linAni (ResidueField O)
  have hcast : (2 : ℝ) * (Nat.card {v : Fin 3 → ResidueField O // LinAni v} : ℝ)
      + (residueCard O : ℝ) ^ 2 = (residueCard O : ℝ) ^ 3 := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) hcount
    push_cast at h
    simpa [residueCard] using h
  have hq : (0 : ℝ) < (residueCard O : ℝ) := qR_pos
  refine le_trans (le_of_eq ?_) hbound
  rw [show (3 : ℕ) * 1 = 3 from rfl]
  field_simp
  linarith [hcast]

end Gate

end Uniformity.Density

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.linInert_decided_res
#print axioms Uniformity.Density.gate_linInert3_lower

end AxCheck
