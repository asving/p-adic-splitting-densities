/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G52
import Uniformity.ChapG.G58
import Uniformity.ChapG.G59
import Uniformity.ChapG.G73
import Uniformity.Density.ScaleExtraction
import Uniformity.Density.Transport

/-!
# Uniformity.ChapG.G75 — `exists_ram3_lift`

**Chapter G, NODE G.75** (`blueprint/CHAP-G_base_cases_menus.md` §10). Every class of
`species3 N` (the `q^N`-element species with `c 0 = c 1 = 0`, G.73) also has a **ramified**
lift, of type `c3ram` (when the chosen lift of `c 2` is literally `0`) or `c3linRam` (otherwise).
Hence no type is decided on it — this is the companion construction to G.74's split lift, and
together they feed G.76's `q^N ≤ undecidedCount O 3 N` bound.

DEPENDS: G.52, G.58, G.59, G.73 · landed `exists_monic_scaleRoots_typeOf` (`ScaleExtraction.lean`),
`exists_monicPoly_eq`, `monicPoly_coeff_lt` (`Transport.lean`), `typeOf_eisenstein`
(`NormLeaves.lean`, via G.58), `HenselianLocalRing.is_henselian`, `typeOf_mul`
(`TypeOfAlgebra.lean`), `typeOf_of_natDegree_one`, `typeOf_of_certRam` (`Drainage.lean`).

**⚠ THE CONSTRUCTION IS THIS CHAPTER'S, NOT THE CORPUS'S**, and genuinely new to `leanfinal` (no
`leancheck` re-derivation target — `species3`/the two explicit lifts have no counterpart there).
The blueprint's own PROOF sketch routes case 2 (`a₂ ≠ 0`) through a bespoke scale-and-peel with a
side condition tying the window `M` to the parity of `M − e`; the route below reaches the same
STATEMENT by a cleaner path that decouples the two cases entirely: for BOTH cases, rescale by
`π^m` (`m := N` in case 1, `m := addVal a₂` in case 2) to expose a window where the residual
shape is visible, choosing the rescaled constant term's exponent to be `2 * N + 1` — always odd,
independent of the rescaling exponent, which is what removes the parity bookkeeping. Case 2 then
peels a genuine root (not just a residual one) via Hensel and reads the cofactor's `CertRam` off
the algebraic identity the root equation forces; this needs its own small cubic-peeling toolkit
(`cubic_expand`/`peel`/`cubic_peel`/`exists_cubic_root`), re-derived privately here in
`leanfinal`'s own idiom (cf. `leancheck/UniformityCheck/N3Base.lean`, whose general-purpose
peeling lemmas are architecture, not census data, and are evidence this route is feasible).

**TEETH.** `HEX3-SPECIES` → executable regression; `HM3-ORACLE` → executable regression.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace Uniformity.Density

open IsLocalRing Polynomial

/-! ## 1. A private cubic-peeling toolkit

Re-derived against `leanfinal`'s own `monicPoly`/`typeOf` API (not imported from `leancheck`,
per the repo's non-import policy). The lemmas mirror `leancheck`'s `N3Base.lean` in content —
general-purpose cubic algebra, not census data, so re-deriving them is exactly the "known
feasible, re-derive against the local API" move the blueprint's H-9 policy describes. -/

section CubicToolkit

variable {K : Type*} [CommRing K] [IsDomain K] [IsDiscreteValuationRing K]

private theorem g75_cubic_expand (a : Fin 3 → K) :
    monicPoly a = X ^ 3 + C (a 2) * X ^ 2 + C (a 1) * X + C (a 0) := by
  simp only [monicPoly, Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero,
    pow_one, mul_one]
  ring

private theorem g75_cubic_eval (a : Fin 3 → K) (x : K) :
    (monicPoly a).eval x = x ^ 3 + a 2 * x ^ 2 + a 1 * x + a 0 := by
  rw [g75_cubic_expand]
  simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C]

private theorem g75_cubic_deriv_eval (a : Fin 3 → K) (x : K) :
    ((monicPoly a).derivative).eval x = 3 * x ^ 2 + 2 * a 2 * x + a 1 := by
  rw [g75_cubic_expand]
  simp only [derivative_add, derivative_pow, derivative_X, derivative_C, derivative_mul,
    eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_zero, eval_one]
  ring

/-- The three below-degree coefficients of a monic cubic, read off `g75_cubic_expand` directly
(avoiding any `Fin.mk`-vs-numeral bookkeeping that `monicPoly_coeff_lt` would otherwise force). -/
private theorem g75_coeff0 (a : Fin 3 → K) : (monicPoly a).coeff 0 = a 0 := by
  rw [g75_cubic_expand]; simp

private theorem g75_coeff1 (a : Fin 3 → K) : (monicPoly a).coeff 1 = a 1 := by
  rw [g75_cubic_expand]; simp

private theorem g75_coeff2 (a : Fin 3 → K) : (monicPoly a).coeff 2 = a 2 := by
  rw [g75_cubic_expand]; simp

/-- The quadratic cofactor left after dividing `monicPoly a` by `X - r` (junk unless `r` is a
root; `g75_cubic_peel` supplies the hypothesis). -/
private def g75_peel (a : Fin 3 → K) (r : K) : Fin 2 → K := ![a 1 + a 2 * r + r ^ 2, a 2 + r]

@[simp] private theorem g75_peel_zero (a : Fin 3 → K) (r : K) :
    g75_peel a r 0 = a 1 + a 2 * r + r ^ 2 := rfl
@[simp] private theorem g75_peel_one (a : Fin 3 → K) (r : K) : g75_peel a r 1 = a 2 + r := rfl

private theorem g75_cubic_peel (a : Fin 3 → K) (r : K) (hr : (monicPoly a).eval r = 0) :
    monicPoly a = (X - C r) * monicPoly (g75_peel a r) := by
  have h : (C (a 0) : Polynomial K) = -(C (a 1) * C r + C (a 2) * C r ^ 2 + C r ^ 3) := by
    have hc : C (r ^ 3 + a 2 * r ^ 2 + a 1 * r + a 0) = (0 : Polynomial K) := by
      rw [← g75_cubic_eval a r, hr, map_zero]
    simp only [map_add, map_mul, map_pow] at hc
    linear_combination hc
  rw [g75_cubic_expand, monicPoly_two_expand, g75_peel_zero, g75_peel_one, h]
  simp only [map_add, map_mul, map_pow]
  ring

/-- Cancel a unit factor out of a divisibility (cf. `leancheck`'s `dvd_of_isUnit_mul`). -/
private theorem g75_dvd_of_isUnit_mul {c d e : K} (hu : IsUnit c) (h : d ∣ c * e) : d ∣ e := by
  obtain ⟨u, rfl⟩ := hu
  have he : e = ((↑u⁻¹ : K)) * ((u : K) * e) := by rw [← mul_assoc]; simp
  rw [he]
  exact h.mul_left _

variable [IsAdicComplete (maximalIdeal K) K]

/-- Hensel at a simple residue root of a monic cubic: the only place completeness is used. -/
private theorem g75_exists_cubic_root (a : Fin 3 → K) (ρ : K)
    (h0 : ρ ^ 3 + a 2 * ρ ^ 2 + a 1 * ρ + a 0 ∈ maximalIdeal K)
    (h1 : IsUnit (3 * ρ ^ 2 + 2 * a 2 * ρ + a 1)) :
    ∃ r : K, (monicPoly a).eval r = 0 ∧ r - ρ ∈ maximalIdeal K := by
  obtain ⟨r, hr, hd⟩ :=
    HenselianLocalRing.is_henselian (monicPoly a) (monicPoly_monic a) ρ
      (by rw [g75_cubic_eval]; exact h0) (by rw [g75_cubic_deriv_eval]; exact h1)
  exact ⟨r, hr, hd⟩

end CubicToolkit

/-! ## 2. The two explicit lifts, combined -/

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O] {π : O}

/-- `π ∉ 𝔪 ^ 2`: an irreducible element is never in the square of its own maximal ideal (else it
would be a unit). -/
private theorem g75_notMem_sq (hπ : Irreducible π) : π ∉ (maximalIdeal O) ^ 2 := by
  rw [mem_maximalIdeal_pow_iff_dvd hπ 2]
  rintro ⟨z, hz⟩
  have heq : π * 1 = π * (π * z) := by linear_combination hz
  have hone : (1 : O) = π * z := mul_left_cancel₀ hπ.ne_zero heq
  exact hπ.not_isUnit (IsUnit.of_mul_eq_one z hone.symm)

/-- `¬ π ^ (k+1) ∣ π ^ k`: consecutive powers of an irreducible are never divisibility-adjacent
the wrong way. -/
private theorem g75_not_dvd_succ (hπ : Irreducible π) (k : ℕ) : ¬ (π : O) ^ (k + 1) ∣ π ^ k := by
  rw [pow_dvd_iff_le_addVal hπ, hπ.addVal_pow]
  intro hle
  have : (k + 1 : ℕ) ≤ k := by exact_mod_cast hle
  omega

theorem exists_ram3_lift (hπ : Irreducible π) {N : ℕ} {c : Coeff O 3 N} (hc : c ∈ Menu.species3 N) :
    ∃ a : Fin 3 → O, proj O 3 N a = c ∧
      (typeOf (monicPoly a) = c3ram ∨ typeOf (monicPoly a) = c3linRam) := by
  by_cases hc2 : c 2 = 0
  · -- CASE 1: the chosen residue class of the third coordinate is the zero class.
    set M : ℕ := 3 * N + 1 with hM
    set b : Fin 3 → O := ![π ^ M, 0, 0] with hb
    have hM0 : π ^ N ∣ π ^ M := pow_dvd_pow π (by omega)
    have hproj : proj O 3 N b = c := by
      funext i
      fin_cases i
      · change (Ideal.Quotient.mk _ (b 0) : Res O N) = c 0
        rw [hc.1, Ideal.Quotient.eq_zero_iff_mem]
        simp only [hb, Matrix.cons_val_zero]
        exact (mem_maximalIdeal_pow_iff_dvd hπ N _).2 hM0
      · change (Ideal.Quotient.mk _ (b 1) : Res O N) = c 1
        rw [hc.2]; simp [hb]
      · change (Ideal.Quotient.mk _ (b 2) : Res O N) = c 2
        rw [hc2]; simp [hb]
    have hb0 : b 0 = π ^ M := by simp [hb]
    have hb1 : b 1 = 0 := by simp [hb]
    have hb2 : b 2 = 0 := by simp [hb]
    have hdvd : ∀ i < (monicPoly b).natDegree,
        π ^ (N * ((monicPoly b).natDegree - i)) ∣ (monicPoly b).coeff i := by
      intro i hi
      rw [monicPoly_natDegree] at hi ⊢
      interval_cases i
      · rw [g75_coeff0, hb0]; exact pow_dvd_pow π (show N * 3 ≤ M by omega)
      · rw [g75_coeff1, hb1]; exact dvd_zero _
      · rw [g75_coeff2, hb2]; exact dvd_zero _
    obtain ⟨G, hGmon, hGdeg, hGeq, hGty⟩ :=
      exists_monic_scaleRoots_typeOf hπ (monicPoly_monic b) N hdvd
    rw [monicPoly_natDegree] at hGdeg
    obtain ⟨a', ha'⟩ := exists_monicPoly_eq hGmon hGdeg
    have hne : (π : O) ≠ 0 := hπ.ne_zero
    have hc0 : G.coeff 0 = π := by
      have h := congrArg (fun p : Polynomial O => p.coeff 0) hGeq
      simp only [coeff_scaleRoots, hGdeg, g75_coeff0, hb0] at h
      rw [← pow_mul] at h
      have h' : G.coeff 0 * π ^ (N * (3 - 0)) = π ^ M := h.symm
      rw [show N * (3 - 0) = 3 * N from by ring, hM,
        show 3 * N + 1 = 1 + 3 * N from by ring, pow_add, pow_one] at h'
      exact mul_right_cancel₀ (pow_ne_zero _ hne) h'
    have hc1 : G.coeff 1 = 0 := by
      have h := congrArg (fun p : Polynomial O => p.coeff 1) hGeq
      simp only [coeff_scaleRoots, hGdeg, g75_coeff1, hb1] at h
      rw [← pow_mul] at h
      exact (mul_eq_zero.1 h.symm).resolve_right (pow_ne_zero _ hne)
    have hc2' : G.coeff 2 = 0 := by
      have h := congrArg (fun p : Polynomial O => p.coeff 2) hGeq
      simp only [coeff_scaleRoots, hGdeg, g75_coeff2, hb2] at h
      rw [← pow_mul] at h
      exact (mul_eq_zero.1 h.symm).resolve_right (pow_ne_zero _ hne)
    have ha'0 : a' 0 = π := by rw [← g75_coeff0 a', ha']; exact hc0
    have ha'1 : a' 1 = 0 := by rw [← g75_coeff1 a', ha']; exact hc1
    have ha'2 : a' 2 = 0 := by rw [← g75_coeff2 a', ha']; exact hc2'
    have htyG : typeOf G = c3ram := by
      rw [← ha']
      have hlow : ∀ i < (monicPoly a').natDegree, (monicPoly a').coeff i ∈ maximalIdeal O := by
        intro i hi
        rw [monicPoly_natDegree] at hi
        interval_cases i
        · rw [g75_coeff0, ha'0]; exact (mem_maximalIdeal_iff_dvd hπ π).2 dvd_rfl
        · rw [g75_coeff1, ha'1]; exact Ideal.zero_mem _
        · rw [g75_coeff2, ha'2]; exact Ideal.zero_mem _
      have h0 : (monicPoly a').coeff 0 ∉ (maximalIdeal O) ^ 2 := by
        rw [g75_coeff0, ha'0]
        exact g75_notMem_sq hπ
      have hty := typeOf_eisenstein (monicPoly_monic a') (by rw [monicPoly_natDegree]; omega)
        hlow h0
      rw [monicPoly_natDegree] at hty
      exact hty
    exact ⟨b, hproj, Or.inl (by rw [hGty, htyG])⟩
  · -- CASE 2: the chosen residue class of the third coordinate is nonzero.
    obtain ⟨a₂, ha₂⟩ := Ideal.Quotient.mk_surjective (I := (maximalIdeal O) ^ N) (c 2)
    have ha₂ne : a₂ ≠ 0 := by
      rintro rfl; exact hc2 (by rw [← ha₂]; simp)
    obtain ⟨e, he⟩ := exists_addVal_eq ha₂ne
    have hdvde0 : π ^ e ∣ a₂ := (pow_dvd_iff_le hπ he e).2 (le_refl e)
    have hndvde : ¬ π ^ (e + 1) ∣ a₂ := by rw [pow_dvd_iff_le hπ he]; omega
    obtain ⟨u, hu⟩ := hdvde0
    have hdvde : π ^ e ∣ a₂ := ⟨u, hu⟩
    have hunotdvd : ¬ π ∣ u := by
      rintro ⟨v, hv⟩
      exact hndvde ⟨v, by rw [hu, hv]; ring⟩
    have huu : IsUnit u := isUnit_of_not_dvd hπ hunotdvd
    set M : ℕ := 3 * e + 2 * N + 1 with hM
    set b : Fin 3 → O := ![π ^ M, 0, a₂] with hb
    have hproj : proj O 3 N b = c := by
      funext i
      fin_cases i
      · change (Ideal.Quotient.mk _ (b 0) : Res O N) = c 0
        rw [hc.1, Ideal.Quotient.eq_zero_iff_mem]
        simp only [hb, Matrix.cons_val_zero]
        exact (mem_maximalIdeal_pow_iff_dvd hπ N _).2 (dvd_trans (pow_dvd_pow π (by omega)) dvd_rfl)
      · change (Ideal.Quotient.mk _ (b 1) : Res O N) = c 1
        rw [hc.2]; simp [hb]
      · change (Ideal.Quotient.mk _ (b 2) : Res O N) = c 2
        simp only [hb, Matrix.cons_val_two, Matrix.tail_cons]
        exact ha₂
    have hne : (π : O) ≠ 0 := hπ.ne_zero
    have hb0 : b 0 = π ^ M := by simp [hb]
    have hb1 : b 1 = 0 := by simp [hb]
    have hb2 : b 2 = a₂ := by simp [hb]
    have hdvd : ∀ i < (monicPoly b).natDegree,
        π ^ (e * ((monicPoly b).natDegree - i)) ∣ (monicPoly b).coeff i := by
      intro i hi
      rw [monicPoly_natDegree] at hi ⊢
      interval_cases i
      · rw [g75_coeff0, hb0]; exact pow_dvd_pow π (show e * 3 ≤ M by omega)
      · rw [g75_coeff1, hb1]; exact dvd_zero _
      · rw [g75_coeff2, hb2]; simpa using hdvde
    obtain ⟨G, hGmon, hGdeg, hGeq, hGty⟩ :=
      exists_monic_scaleRoots_typeOf hπ (monicPoly_monic b) e hdvd
    rw [monicPoly_natDegree] at hGdeg
    obtain ⟨a', ha'⟩ := exists_monicPoly_eq hGmon hGdeg
    have hc0 : G.coeff 0 = π ^ (2 * N + 1) := by
      have h := congrArg (fun p : Polynomial O => p.coeff 0) hGeq
      simp only [coeff_scaleRoots, hGdeg, g75_coeff0, hb0] at h
      rw [← pow_mul] at h
      have h' : G.coeff 0 * π ^ (e * (3 - 0)) = π ^ M := h.symm
      rw [show e * (3 - 0) = 3 * e from by ring, hM,
        show 3 * e + 2 * N + 1 = (2 * N + 1) + 3 * e from by ring, pow_add] at h'
      exact mul_right_cancel₀ (pow_ne_zero _ hne) h'
    have hc1 : G.coeff 1 = 0 := by
      have h := congrArg (fun p : Polynomial O => p.coeff 1) hGeq
      simp only [coeff_scaleRoots, hGdeg, g75_coeff1, hb1] at h
      rw [← pow_mul] at h
      exact (mul_eq_zero.1 h.symm).resolve_right (pow_ne_zero _ hne)
    have hc2' : G.coeff 2 = u := by
      have h := congrArg (fun p : Polynomial O => p.coeff 2) hGeq
      simp only [coeff_scaleRoots, hGdeg, g75_coeff2, hb2] at h
      rw [← pow_mul] at h
      have h' : G.coeff 2 * π ^ (e * (3 - 2)) = π ^ e * u := by rw [← hu]; exact h.symm
      rw [show e * (3 - 2) = e from by ring, mul_comm (π ^ e) u] at h'
      exact mul_right_cancel₀ (pow_ne_zero e hne) h'
    have ha'0 : a' 0 = π ^ (2 * N + 1) := by rw [← g75_coeff0 a', ha']; exact hc0
    have ha'1 : a' 1 = 0 := by rw [← g75_coeff1 a', ha']; exact hc1
    have ha'2 : a' 2 = u := by rw [← g75_coeff2 a', ha']; exact hc2'
    -- Find a genuine root of `monicPoly a'` near the unit `-u`.
    have huunit : IsUnit (-u) := huu.neg
    have h0mem : (-u) ^ 3 + a' 2 * (-u) ^ 2 + a' 1 * (-u) + a' 0 ∈ maximalIdeal O := by
      rw [ha'0, ha'1, ha'2]
      have hid : (-u) ^ 3 + u * (-u) ^ 2 + 0 * (-u) + π ^ (2 * N + 1) = π ^ (2 * N + 1) := by ring
      rw [hid]
      exact (mem_maximalIdeal_iff_dvd hπ _).2 (dvd_pow_self π (by omega))
    have h1unit : IsUnit (3 * (-u) ^ 2 + 2 * a' 2 * (-u) + a' 1) := by
      rw [ha'1, ha'2]
      have hid : 3 * (-u) ^ 2 + 2 * u * (-u) + 0 = u ^ 2 := by ring
      rw [hid]
      exact huu.pow 2
    obtain ⟨r, hr, hrρ⟩ := g75_exists_cubic_root a' (-u) h0mem h1unit
    have hru : IsUnit r := by
      refine notMem_maximalIdeal.1 (fun hmem => ?_)
      have hmemu : -u ∈ maximalIdeal O := by
        have heq : -u = r - (r - (-u)) := by ring
        rw [heq]
        exact Ideal.sub_mem _ hmem hrρ
      exact absurd hmemu (notMem_maximalIdeal.2 huunit)
    have hpeel := g75_cubic_peel a' r hr
    set hvec : Fin 2 → O := g75_peel a' r with hvecdef
    have hh1 : hvec 1 = a' 2 + r := g75_peel_one a' r
    have hh0 : hvec 0 = a' 1 + a' 2 * r + r ^ 2 := g75_peel_zero a' r
    have hreq : r ^ 3 + a' 2 * r ^ 2 + a' 1 * r + a' 0 = 0 := by
      rw [← g75_cubic_eval a' r]; exact hr
    rw [ha'0, ha'1, ha'2] at hreq
    have hh1eq : hvec 1 = u + r := by rw [hh1, ha'2]
    have hh0eq : hvec 0 = r * (u + r) := by rw [hh0, ha'1, ha'2]; ring
    have hr2unit : IsUnit (r ^ 2) := hru.pow 2
    have hval1 : r ^ 2 * hvec 1 = -(π ^ (2 * N + 1)) := by rw [hh1eq]; linear_combination hreq
    have hval0 : r * hvec 0 = -(π ^ (2 * N + 1)) := by rw [hh0eq]; linear_combination hreq
    have hqval0 : qval hvec 0 = hvec 0 := by simp [qval]
    have hqder0 : qder hvec 0 = hvec 1 := by simp [qder]
    have hnd : ¬ (π:O) ^ (2 * N + 2) ∣ π ^ (2 * N + 1) := by
      have := g75_not_dvd_succ hπ (2 * N + 1)
      simpa using this
    have hcertv1 : π ^ (2 * N + 1) ∣ hvec 0 :=
      g75_dvd_of_isUnit_mul hru (by rw [hval0]; exact dvd_neg.2 dvd_rfl)
    have hcertv2 : ¬ π ^ (2 * N + 2) ∣ hvec 0 := by
      intro hmem
      refine hnd ?_
      have h2 : π ^ (2 * N + 2) ∣ r * hvec 0 := hmem.mul_left r
      rw [hval0] at h2
      exact dvd_neg.1 h2
    have hcertd0 : π ^ (2 * N + 1) ∣ hvec 1 :=
      g75_dvd_of_isUnit_mul hr2unit (by rw [hval1]; exact dvd_neg.2 dvd_rfl)
    have hcertd : π ^ (N + 1) ∣ hvec 1 := dvd_trans (pow_dvd_pow π (by omega)) hcertd0
    have hCertRam : CertRam π hvec (2 * N + 2) :=
      ⟨0, N, by omega, by rw [hqval0]; exact hcertv1, by rw [hqval0]; exact hcertv2,
        by rw [hqder0]; exact hcertd⟩
    have htyram : typeOf (monicPoly hvec) = ramType := typeOf_of_certRam hπ hCertRam
    have htyG : typeOf G = c3linRam := by
      rw [← ha', hpeel]
      apply FactorizationType.ext
      rw [typeOf_mul (monic_X_sub_C r) (monicPoly_monic hvec)]
      have htyg : typeOf (X - C r) = (⟨({(1, 1)} : Multiset (ℕ × ℕ))⟩ : FactorizationType) :=
        typeOf_of_natDegree_one (monic_X_sub_C r) (natDegree_X_sub_C r)
      rw [htyg, htyram]
      rfl
    exact ⟨b, hproj, Or.inr (by rw [hGty, htyG])⟩

end Uniformity.Density

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.exists_ram3_lift

end AxCheck
