/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G52
import Uniformity.ChapG.G61I
import Uniformity.Density.Drainage
import Uniformity.Density.TypeOfAlgebra

/-!
# Uniformity.ChapG.G61a — the split lower bound `1/q⁹ ≤ decidedDensity O 3 c3split`

**Chapter G, NODE G.61a** (`blueprint/CHAP-G_base_cases_menus.md` §9), the first of the five
SPLIT-MANDATED sub-nodes of G.61: the `{(1,1)}³` family.

**Why this family is DEEP (level 3, a single class), while the other four are level 1 or 2.**
Over a base with residue field `𝔽₂` there is NO monic cubic with three distinct residue roots, so
the split type has no level-1 certificate valid for every `O`. The general-`O` certificate is the
window-3 class of `X(X − 1)(X − π)`, i.e. `a ≡ (0, π, −(1 + π)) mod 𝔪³`, whose single class gives
the (deliberately crude, but uniform) bound `1/q⁹`. At `q ≥ 3` the level-1 family is far better —
that sharpening is not part of this node's mandated signature.

DEPENDS: G.52 (`c3split`), G.61.0 (`decidedDensity_ge_of_inj` is not used here; the single-class
`decidedDensity_ge_of_decided` from `Gates.lean:325` suffices) · landed `proj_eq_iff_dvd` (CN-07,
`DensityAPI.lean:124`), `CertSplit`/`typeOf_of_certSplit`, `qval`, `qder`, `splitType`
(`Drainage.lean`), `typeOf_mul` (`TypeOfAlgebra.lean:60`), `typeOf_of_natDegree_one`
(`TypeOf.lean:350`), `monicPoly_two_expand` (`QuadCert.lean:82`),
`HenselianLocalRing.is_henselian`.

PROOF sketch. Hensel at the simple residue root `1` produces a genuine root `r ≡ 1 (mod 𝔪)` of
`monicPoly a`. **Bootstrap:** since the other two roots of the model are `≡ 0`, both `r` and
`r − π` are units, so the exact power of `π` in `r(r − π)(r − 1) = −π³ w` is forced entirely onto
`r − 1`, giving `r ≡ 1 (mod 𝔪³)`. The quadratic cofactor `peel a r` then carries a SPLIT
certificate at the centre `0` with `w = 1`: its derivative `a₂ + r` has valuation exactly `1` and
its value `a₁ + a₂r + r²` has valuation `≥ 3`. `typeOf_of_certSplit` splits the cofactor, and
`typeOf_mul` assembles `{(1,1)} + {(1,1),(1,1)} = c3split`.

⚠ RE-DERIVATION TARGET (blueprint H-9): `leancheck/UniformityCheck/N3Certs.lean`
(`typeOf_split3_of_deep`) and `leancheck/UniformityCheck/N3Density.lean`
(`split3_decided`, `gate_split3_lower`) land the same content. **DEVIATION from the sub-node
brief:** the brief named G.55 (`typeOf_split3_of_residue`, three DISTINCT residue roots) as this
sub-node's type certificate, but G.55 cannot certify the deep class — at `q = 2` the class
`X(X − 1)(X − π)` reduces to `X²(X − 1)`, which has a REPEATED residue root. The deep certificate
`typeOf_split3_of_deep` is landed here instead (it has no `leanfinal` counterpart), together with
the private cubic-peeling toolkit it needs (mirroring the one `G75.lean` keeps private for its own
use; re-derived rather than imported, per the repo's non-import policy).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace Uniformity.Density

open IsLocalRing Polynomial

/-! ## 1. A private cubic-peeling toolkit

Re-derived against `leanfinal`'s own `monicPoly`/`typeOf` API; the same general-purpose cubic
algebra that `G75.lean` keeps private for its own use (cf. `leancheck`'s `N3Base.lean`). -/

section CubicToolkit

variable {K : Type*} [CommRing K] [IsDomain K] [IsDiscreteValuationRing K]

private theorem g61a_cubic_expand (a : Fin 3 → K) :
    monicPoly a = X ^ 3 + C (a 2) * X ^ 2 + C (a 1) * X + C (a 0) := by
  simp only [monicPoly, Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero,
    pow_one, mul_one]
  ring

private theorem g61a_cubic_eval (a : Fin 3 → K) (x : K) :
    (monicPoly a).eval x = x ^ 3 + a 2 * x ^ 2 + a 1 * x + a 0 := by
  rw [g61a_cubic_expand]
  simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C]

private theorem g61a_cubic_deriv_eval (a : Fin 3 → K) (x : K) :
    ((monicPoly a).derivative).eval x = 3 * x ^ 2 + 2 * a 2 * x + a 1 := by
  rw [g61a_cubic_expand]
  simp only [derivative_add, derivative_pow, derivative_X, derivative_C, derivative_mul,
    eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_zero, eval_one]
  ring

/-- The quadratic cofactor left after dividing `monicPoly a` by `X - r` (junk unless `r` is a
root; `g61a_cubic_peel` supplies the hypothesis). -/
private def g61a_peel (a : Fin 3 → K) (r : K) : Fin 2 → K := ![a 1 + a 2 * r + r ^ 2, a 2 + r]

@[simp] private theorem g61a_peel_zero (a : Fin 3 → K) (r : K) :
    g61a_peel a r 0 = a 1 + a 2 * r + r ^ 2 := rfl

@[simp] private theorem g61a_peel_one (a : Fin 3 → K) (r : K) : g61a_peel a r 1 = a 2 + r := rfl

private theorem g61a_cubic_peel (a : Fin 3 → K) (r : K) (hr : (monicPoly a).eval r = 0) :
    monicPoly a = (X - C r) * monicPoly (g61a_peel a r) := by
  have h : (C (a 0) : Polynomial K) = -(C (a 1) * C r + C (a 2) * C r ^ 2 + C r ^ 3) := by
    have hc : C (r ^ 3 + a 2 * r ^ 2 + a 1 * r + a 0) = (0 : Polynomial K) := by
      rw [← g61a_cubic_eval a r, hr, map_zero]
    simp only [map_add, map_mul, map_pow] at hc
    linear_combination hc
  rw [g61a_cubic_expand, monicPoly_two_expand, g61a_peel_zero, g61a_peel_one, h]
  simp only [map_add, map_mul, map_pow]
  ring

/-- Cancel a unit factor out of a divisibility. -/
private theorem g61a_dvd_of_isUnit_mul {c d e : K} (hu : IsUnit c) (h : d ∣ c * e) : d ∣ e := by
  obtain ⟨u, rfl⟩ := hu
  have he : e = ((↑u⁻¹ : K)) * ((u : K) * e) := by rw [← mul_assoc]; simp
  rw [he]
  exact h.mul_left _

variable [IsAdicComplete (maximalIdeal K) K]

/-- Hensel at a simple residue root of a monic cubic: the only place completeness is used. -/
private theorem g61a_exists_cubic_root (a : Fin 3 → K) (ρ : K)
    (h0 : ρ ^ 3 + a 2 * ρ ^ 2 + a 1 * ρ + a 0 ∈ maximalIdeal K)
    (h1 : IsUnit (3 * ρ ^ 2 + 2 * a 2 * ρ + a 1)) :
    ∃ r : K, (monicPoly a).eval r = 0 ∧ r - ρ ∈ maximalIdeal K := by
  obtain ⟨r, hr, hd⟩ :=
    HenselianLocalRing.is_henselian (monicPoly a) (monicPoly_monic a) ρ
      (by rw [g61a_cubic_eval]; exact h0) (by rw [g61a_cubic_deriv_eval]; exact h1)
  exact ⟨r, hr, hd⟩

end CubicToolkit

/-! ## 2. The deep split certificate -/

section Deep

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] {π : O}

/-- **`{(1,1)}³`, the DEEP certificate.** Every monic cubic congruent to `X(X − 1)(X − π)` modulo
`𝔪³` splits into three linear factors over `O`.

This is the split type's general-`O` certificate: it must be deep, because at `q = 2` no residue
cubic has three distinct roots. -/
theorem typeOf_split3_of_deep [IsAdicComplete (maximalIdeal O) O] (hπ : Irreducible π)
    {a : Fin 3 → O} (h0 : π ^ 3 ∣ a 0) (h1 : π ^ 3 ∣ (a 1 - π))
    (h2 : π ^ 3 ∣ (a 2 + (1 + π))) :
    typeOf (monicPoly a) = c3split := by
  have hπm : π ∈ maximalIdeal O := (mem_maximalIdeal_iff_dvd hπ π).2 dvd_rfl
  have hcube : ∀ x : O, π ^ 3 ∣ x → x ∈ maximalIdeal O := fun x hx =>
    (mem_maximalIdeal_iff_dvd hπ x).2 (dvd_trans (dvd_pow_self π (by norm_num)) hx)
  -- Hensel at the simple residue root `1`
  have hval1 : (1 : O) ^ 3 + a 2 * 1 ^ 2 + a 1 * 1 + a 0 ∈ maximalIdeal O := by
    have hid : (1 : O) ^ 3 + a 2 * 1 ^ 2 + a 1 * 1 + a 0
        = (a 2 + (1 + π)) + (a 1 - π) + a 0 := by ring
    rw [hid]
    exact Ideal.add_mem _ (Ideal.add_mem _ (hcube _ h2) (hcube _ h1)) (hcube _ h0)
  have hder1 : IsUnit (3 * (1 : O) ^ 2 + 2 * a 2 * 1 + a 1) := by
    refine notMem_maximalIdeal.1 (fun hmem => ?_)
    have hid : (1 : O) = (3 * (1 : O) ^ 2 + 2 * a 2 * 1 + a 1)
        - 2 * (a 2 + (1 + π)) - (a 1 - π) + π := by ring
    have hone : (1 : O) ∈ maximalIdeal O := by
      rw [hid]
      exact Ideal.add_mem _ (Ideal.sub_mem _ (Ideal.sub_mem _ hmem
        (Ideal.mul_mem_left _ _ (hcube _ h2))) (hcube _ h1)) hπm
    exact absurd hone (notMem_maximalIdeal.2 isUnit_one)
  obtain ⟨r, hr, hr1⟩ := g61a_exists_cubic_root a 1 hval1 hder1
  obtain ⟨u0, hu0⟩ := h0
  obtain ⟨u1, hu1⟩ := h1
  obtain ⟨u2, hu2⟩ := h2
  have ha0 : a 0 = π ^ 3 * u0 := hu0
  have ha1 : a 1 = π + π ^ 3 * u1 := by linear_combination hu1
  have ha2 : a 2 = -(1 + π) + π ^ 3 * u2 := by linear_combination hu2
  have hre : r ^ 3 + a 2 * r ^ 2 + a 1 * r + a 0 = 0 := by
    rw [← g61a_cubic_eval a r]; exact hr
  -- bootstrap: `r ≡ 1` improves from `mod 𝔪` to `mod 𝔪³`
  have hru : IsUnit r := by
    refine notMem_maximalIdeal.1 (fun hmem => ?_)
    have hone : (1 : O) ∈ maximalIdeal O := by
      have hid : (1 : O) = r - (r - 1) := by ring
      rw [hid]; exact Ideal.sub_mem _ hmem hr1
    exact absurd hone (notMem_maximalIdeal.2 isUnit_one)
  have hrπu : IsUnit (r - π) := by
    refine notMem_maximalIdeal.1 (fun hmem => ?_)
    have hone : (1 : O) ∈ maximalIdeal O := by
      have hid : (1 : O) = (r - π) - (r - 1) + π := by ring
      rw [hid]
      exact Ideal.add_mem _ (Ideal.sub_mem _ hmem hr1) hπm
    exact absurd hone (notMem_maximalIdeal.2 isUnit_one)
  have hfactor : r * (r - π) * (r - 1) = π ^ 3 * (-(u2 * r ^ 2 + u1 * r + u0)) := by
    have hre' := hre
    rw [ha0, ha1, ha2] at hre'
    linear_combination hre'
  have hr1cube : π ^ 3 ∣ (r - 1) :=
    g61a_dvd_of_isUnit_mul (hru.mul hrπu) ⟨-(u2 * r ^ 2 + u1 * r + u0), by rw [← hfactor]⟩
  -- the cofactor carries a SPLIT certificate at the centre `0`, with `w = 1`
  have hqder : qder (g61a_peel a r) 0 = a 2 + r := by
    simp only [qder, g61a_peel_one]; ring
  have hqval : qval (g61a_peel a r) 0 = a 1 + a 2 * r + r ^ 2 := by
    simp only [qval, g61a_peel_zero]; ring
  have hd1 : π ∣ qder (g61a_peel a r) 0 := by
    rw [hqder]
    obtain ⟨v, hv⟩ := hr1cube
    refine ⟨π ^ 2 * u2 + π ^ 2 * v - 1, ?_⟩
    have hrv : r = 1 + π ^ 3 * v := by linear_combination hv
    rw [ha2, hrv]; ring
  have hd2 : ¬ π ^ 2 ∣ qder (g61a_peel a r) 0 := by
    rw [hqder]
    rintro ⟨v', hv'⟩
    obtain ⟨v, hv⟩ := hr1cube
    have hrv : r = 1 + π ^ 3 * v := by linear_combination hv
    rw [ha2, hrv] at hv'
    have hcancel : π * (-1 + π ^ 2 * u2 + π ^ 2 * v - π * v') = 0 := by linear_combination hv'
    have hz := (mul_eq_zero.1 hcancel).resolve_left hπ.ne_zero
    have hdvd : π ∣ (1 : O) := ⟨π * u2 + π * v - v', by linear_combination -hz⟩
    exact hπ.not_isUnit (isUnit_of_dvd_one hdvd)
  have hv3 : π ^ 3 ∣ qval (g61a_peel a r) 0 := by
    rw [hqval]
    refine g61a_dvd_of_isUnit_mul hru ?_
    have hid : r * (a 1 + a 2 * r + r ^ 2) = -a 0 := by linear_combination hre
    rw [hid]
    exact dvd_neg.2 ⟨u0, hu0⟩
  have hsplit : typeOf (monicPoly (g61a_peel a r)) = splitType :=
    typeOf_of_certSplit hπ (N := 3)
      ⟨0, 1, by omega, by simpa using hd1, by simpa using hd2, by simpa using hv3⟩
  refine FactorizationType.ext ?_
  rw [g61a_cubic_peel a r hr, typeOf_mul (monic_X_sub_C r) (monicPoly_monic (g61a_peel a r)),
    typeOf_of_natDegree_one (monic_X_sub_C r) (natDegree_X_sub_C r), hsplit]
  rfl

/-- **THREE LINEAR FACTORS, level 3 (deep).** The single class of `X(X − 1)(X − π)`. -/
theorem split3_decided [IsAdicComplete (maximalIdeal O) O] (hπ : Irreducible π) :
    DecidedAt O 3 c3split 3 (proj O 3 3 ![0, π, -(1 + π)]) := by
  intro b hb
  have hd := (proj_eq_iff_dvd hπ (![0, π, -(1 + π)] : Fin 3 → O) b).1 hb.symm
  refine typeOf_split3_of_deep hπ ?_ ?_ ?_
  · simpa using hd 0
  · simpa using hd 1
  · have h := hd 2
    simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h
    have hid : b 2 + (1 + π) = b 2 - -(1 + π) := by ring
    rw [hid]; exact h

end Deep

/-! ## 3. The gate -/

section Gate

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **G.61a.** `1 / q⁹ ≤ decidedDensity O 3 c3split`, every `O`. A LOWER BOUND, not the density:
the deep class is one class at window `3`, and the true split density is much larger. -/
theorem gate_split3_lower [IsAdicComplete (maximalIdeal O) O] :
    1 / (residueCard O : ℝ) ^ 9 ≤ decidedDensity O 3 c3split := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have h := decidedDensity_ge_of_decided (split3_decided hπ)
  simpa using h

end Gate

end Uniformity.Density

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.typeOf_split3_of_deep
#print axioms Uniformity.Density.split3_decided
#print axioms Uniformity.Density.gate_split3_lower

end AxCheck
