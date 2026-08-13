/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.GenuineDensity

/-!
# Uniformity.Density.QuadCert — the `n = 2` decidedness certificates

The `typeOf` certificates for monic quadratics over a complete DVR `O`, all resting on one
explicit computation: for `f = X² + a₁X + a₀` and `A = O[x]/(f) = AdjoinRoot f` with root `α`,
the `O`-basis `(1, α)` gives the multiplication matrix of `u + vα` as
`[[u, -v a₀], [v, u - v a₁]]`, hence

    N_{A/O}(u + v α)  =  u² - a₁ u v + a₀ v²                          (`norm_quad`)

— the classical binary norm form. From it:

* **RAM** (`typeOf_ram_of_eisenstein`): if `a₀ ∈ 𝔪 \ 𝔪²` and `a₁ ∈ 𝔪` (Eisenstein), then `f`
  is irreducible and `N(α) = a₀` has valuation `1`, so `f(g) = 1`, `e(g) = 2` and
  `typeOf f = ⟨{(2,1)}⟩`.
* **INERT** (`typeOf_inert_of_anisotropic`): if the binary form `u² - a₁uv + a₀v²` is
  **anisotropic mod 𝔪** (its only zero mod 𝔪 is `(0,0)` — equivalently the reduction of `f`
  has no root in the residue field), then `f` is irreducible and every norm valuation is even,
  so `f(g) = 2`, `e(g) = 1` and `typeOf f = ⟨{(1,2)}⟩`.
* **SPLIT** is `typeOf_split_of_unit` in `Gates.lean` (one Hensel lift).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing Polynomial

/-! ## 0. The named degree-≤2 types -/

/-- The degree-1 type `{(1,1)}`: one unramified linear factor. -/
def linType : FactorizationType := ⟨{(1, 1)}⟩

/-- The degree-2 SPLIT type `{(1,1),(1,1)}`: two unramified linear factors. -/
def splitType : FactorizationType := ⟨{(1, 1), (1, 1)}⟩

/-- The degree-2 INERT type `{(1,2)}`: one unramified quadratic factor. -/
def inertType : FactorizationType := ⟨{(1, 2)}⟩

/-- The degree-2 RAMIFIED type `{(2,1)}`: one totally ramified quadratic factor. -/
def ramType : FactorizationType := ⟨{(2, 1)}⟩

theorem linType_degree : linType.degree = 1 := by simp [linType, FactorizationType.degree]
theorem splitType_degree : splitType.degree = 2 := by
  simp [splitType, FactorizationType.degree]
theorem inertType_degree : inertType.degree = 2 := by
  simp [inertType, FactorizationType.degree]
theorem ramType_degree : ramType.degree = 2 := by simp [ramType, FactorizationType.degree]

private theorem card_data_ne {σ τ : FactorizationType}
    (h : Multiset.card σ.data ≠ Multiset.card τ.data) : σ ≠ τ := by
  intro hst; exact h (congrArg (fun ρ => Multiset.card ρ.data) hst)

theorem splitType_ne_linType : splitType ≠ linType :=
  card_data_ne (by simp [splitType, linType])
theorem splitType_ne_inertType : splitType ≠ inertType :=
  card_data_ne (by simp [splitType, inertType])
theorem splitType_ne_ramType : splitType ≠ ramType :=
  card_data_ne (by simp [splitType, ramType])
theorem inertType_ne_ramType : inertType ≠ ramType := by
  intro h
  have := congrArg (fun ρ => ρ.data) h
  simp [inertType, ramType] at this

/-! ## 1. The shape of a monic quadratic, and its binary norm form -/

section Quad

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem monicPoly_two_expand (a : Fin 2 → O) :
    monicPoly a = X ^ 2 + C (a 1) * X + C (a 0) := by
  simp only [monicPoly, Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one]
  ring

theorem monicPoly_two_eval (a : Fin 2 → O) (x : O) :
    (monicPoly a).eval x = x ^ 2 + a 0 + a 1 * x := by
  rw [monicPoly_two_expand]
  simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C]
  ring

theorem monicPoly_two_deriv_eval (a : Fin 2 → O) (x : O) :
    ((monicPoly a).derivative).eval x = 2 * x + a 1 := by
  rw [monicPoly_two_expand]
  simp only [derivative_add, derivative_pow, derivative_X, derivative_C, derivative_mul,
    eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_zero, eval_one]
  ring

/-- The power basis `(1, α)` of `O[x]/(f)` for a monic quadratic `f`. -/
noncomputable def quadPB (a : Fin 2 → O) : PowerBasis O (AdjoinRoot (monicPoly a)) :=
  AdjoinRoot.powerBasis' (monicPoly_monic a)

theorem quadPB_dim (a : Fin 2 → O) : (quadPB a).dim = 2 := monicPoly_natDegree a

/-- `(1, α)` as an honest `Module.Basis (Fin 2)`. -/
noncomputable def quadBasis (a : Fin 2 → O) :
    Module.Basis (Fin 2) O (AdjoinRoot (monicPoly a)) :=
  (quadPB a).basis.reindex (finCongr (quadPB_dim a))

theorem quadBasis_apply (a : Fin 2 → O) (i : Fin 2) :
    quadBasis a i = AdjoinRoot.root (monicPoly a) ^ (i : ℕ) := by
  rw [quadBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

theorem quadBasis_zero (a : Fin 2 → O) : quadBasis a 0 = 1 := by
  rw [quadBasis_apply]; simp

theorem quadBasis_one (a : Fin 2 → O) : quadBasis a 1 = AdjoinRoot.root (monicPoly a) := by
  rw [quadBasis_apply]; simp

/-- `eval₂` of a monic quadratic, in any `O`-algebra. (Stated for a general target so that
rewriting `monicPoly a` cannot touch the `AdjoinRoot` index.) -/
theorem eval₂_monicPoly_two {A : Type*} [CommRing A] (φ : O →+* A) (x : A) (a : Fin 2 → O) :
    (monicPoly a).eval₂ φ x = x ^ 2 + φ (a 1) * x + φ (a 0) := by
  rw [monicPoly_two_expand]
  simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]

/-- The defining relation `α² = -a₁ α - a₀`. -/
theorem root_sq (a : Fin 2 → O) :
    (AdjoinRoot.root (monicPoly a)) ^ 2
      = -(algebraMap O _ (a 1)) * AdjoinRoot.root (monicPoly a) - algebraMap O _ (a 0) := by
  have h := AdjoinRoot.eval₂_root (monicPoly a)
  rw [eval₂_monicPoly_two] at h
  have hof : (AdjoinRoot.of (monicPoly a) : O →+* AdjoinRoot (monicPoly a))
      = algebraMap O (AdjoinRoot (monicPoly a)) := rfl
  rw [hof] at h
  linear_combination h

private theorem repr_comb (a : Fin 2 → O) (c₀ c₁ : O) (i : Fin 2) :
    (quadBasis a).repr (c₀ • quadBasis a 0 + c₁ • quadBasis a 1) i
      = if i = 0 then c₀ else c₁ := by
  rw [map_add, map_smul, map_smul, Module.Basis.repr_self, Module.Basis.repr_self]
  fin_cases i <;> simp

/-- **The binary norm form.** `N(u + vα) = u² - a₁ u v + a₀ v²`. -/
theorem norm_quad (a : Fin 2 → O) (u v : O) :
    Algebra.norm O (algebraMap O (AdjoinRoot (monicPoly a)) u
        + algebraMap O (AdjoinRoot (monicPoly a)) v * AdjoinRoot.root (monicPoly a))
      = u ^ 2 - a 1 * u * v + a 0 * v ^ 2 := by
  classical
  set A := AdjoinRoot (monicPoly a) with hA
  set α : A := AdjoinRoot.root (monicPoly a) with hα
  set x : A := algebraMap O A u + algebraMap O A v * α with hx
  have hsmul : ∀ c : O, ∀ y : A, c • y = algebraMap O A c * y := fun c y => Algebra.smul_def c y
  have hx0 : x * quadBasis a 0 = u • quadBasis a 0 + v • quadBasis a 1 := by
    rw [quadBasis_zero, quadBasis_one, hsmul, hsmul, hx]; ring
  have hx1 : x * quadBasis a 1
      = (-(v * a 0)) • quadBasis a 0 + (u - v * a 1) • quadBasis a 1 := by
    rw [quadBasis_zero, quadBasis_one, hsmul, hsmul, hx]
    have hsq : α ^ 2 = -(algebraMap O A (a 1)) * α - algebraMap O A (a 0) := root_sq a
    have hexp : (algebraMap O A u + algebraMap O A v * α) * α
        = algebraMap O A u * α + algebraMap O A v * α ^ 2 := by ring
    rw [hexp, hsq, map_neg, map_mul, map_sub, map_mul]
    ring
  rw [Algebra.norm_eq_matrix_det (quadBasis a), Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, hx0, hx1, repr_comb]
  norm_num
  ring

theorem norm_zero_quad (a : Fin 2 → O) : Algebra.norm O (0 : AdjoinRoot (monicPoly a)) = 0 := by
  have h := norm_quad a 0 0
  simpa using h

theorem norm_root_quad (a : Fin 2 → O) :
    Algebra.norm O (AdjoinRoot.root (monicPoly a)) = a 0 := by
  have h := norm_quad a 0 1
  simpa using h

/-- Every element of `O[x]/(f)` is `u + vα`. -/
theorem exists_quad_repr (a : Fin 2 → O) (x : AdjoinRoot (monicPoly a)) :
    ∃ u v : O, x = algebraMap O _ u + algebraMap O _ v * AdjoinRoot.root (monicPoly a) := by
  refine ⟨(quadBasis a).repr x 0, (quadBasis a).repr x 1, ?_⟩
  have h := (quadBasis a).sum_repr x
  rw [Fin.sum_univ_two, quadBasis_zero, quadBasis_one] at h
  calc x = (quadBasis a).repr x 0 • (1 : AdjoinRoot (monicPoly a))
            + (quadBasis a).repr x 1 • AdjoinRoot.root (monicPoly a) := h.symm
    _ = _ := by rw [Algebra.smul_def, Algebra.smul_def, mul_one]

end Quad

/-! ## 2. Reducible monic quadratics have two roots -/

section Reducible

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- A reducible monic quadratic is `(X - r)(X - s)`: `a₁ = -(r+s)`, `a₀ = rs`. -/
theorem exists_roots_of_not_irreducible {a : Fin 2 → O} (h : ¬ Irreducible (monicPoly a)) :
    ∃ r s : O, a 1 = -(r + s) ∧ a 0 = r * s := by
  have hm := monicPoly_monic a
  have hd := monicPoly_natDegree a
  rw [irreducible_iff] at h
  push_neg at h
  have hnu : ¬ IsUnit (monicPoly a) := by
    intro hu; have := natDegree_eq_zero_of_isUnit hu; omega
  obtain ⟨g, k, hgk, hg, hk⟩ := h hnu
  have hg0 : g ≠ 0 := by rintro rfl; exact hm.ne_zero (by simpa using hgk)
  have hk0 : k ≠ 0 := by rintro rfl; exact hm.ne_zero (by simpa using hgk)
  have hdeg : g.natDegree + k.natDegree = 2 := by rw [← natDegree_mul hg0 hk0, ← hgk, hd]
  have hlead : g.leadingCoeff * k.leadingCoeff = 1 := by rw [← leadingCoeff_mul, ← hgk]; exact hm
  have hgu : IsUnit g.leadingCoeff :=
    ⟨⟨g.leadingCoeff, k.leadingCoeff, hlead, by rw [mul_comm]; exact hlead⟩, rfl⟩
  have hku : IsUnit k.leadingCoeff :=
    ⟨⟨k.leadingCoeff, g.leadingCoeff, by rw [mul_comm]; exact hlead, hlead⟩, rfl⟩
  have hg1 : g.natDegree = 1 := by
    rcases Nat.eq_zero_or_pos g.natDegree with h0 | h0
    · exact absurd (isUnit_of_natDegree_zero h0 hgu) hg
    · rcases Nat.eq_zero_or_pos k.natDegree with h1 | h1
      · exact absurd (isUnit_of_natDegree_zero h1 hku) hk
      · omega
  have hk1 : k.natDegree = 1 := by omega
  -- monicize both factors
  have hgm : (monicize g).Monic := monicize_monic hgu
  have hkm : (monicize k).Monic := monicize_monic hku
  have hgd : (monicize g).natDegree = 1 := by
    rw [monicize, natDegree_C_mul (isUnit_inverse_leadingCoeff hgu).ne_zero, hg1]
  have hkd : (monicize k).natDegree = 1 := by
    rw [monicize, natDegree_C_mul (isUnit_inverse_leadingCoeff hku).ne_zero, hk1]
  obtain ⟨r, hgX⟩ : ∃ r : O, monicize g = X - C r :=
    ⟨-((monicize g).coeff 0), by rw [map_neg, sub_neg_eq_add]; exact Monic.eq_X_add_C hgm hgd⟩
  obtain ⟨s, hkX⟩ : ∃ s : O, monicize k = X - C s :=
    ⟨-((monicize k).coeff 0), by rw [map_neg, sub_neg_eq_add]; exact Monic.eq_X_add_C hkm hkd⟩
  have hinv : Ring.inverse g.leadingCoeff * Ring.inverse k.leadingCoeff = 1 := by
    calc Ring.inverse g.leadingCoeff * Ring.inverse k.leadingCoeff
        = Ring.inverse g.leadingCoeff * Ring.inverse k.leadingCoeff
            * (g.leadingCoeff * k.leadingCoeff) := by rw [hlead, mul_one]
      _ = (Ring.inverse g.leadingCoeff * g.leadingCoeff)
            * (Ring.inverse k.leadingCoeff * k.leadingCoeff) := by ring
      _ = 1 := by rw [Ring.inverse_mul_cancel _ hgu, Ring.inverse_mul_cancel _ hku, mul_one]
  have hfac : monicPoly a = (X - C r) * (X - C s) := by
    rw [← hgX, ← hkX, monicize, monicize]
    calc monicPoly a = C (1 : O) * (g * k) := by rw [map_one, one_mul, hgk]
      _ = C (Ring.inverse g.leadingCoeff * Ring.inverse k.leadingCoeff) * (g * k) := by rw [hinv]
      _ = C (Ring.inverse g.leadingCoeff) * g * (C (Ring.inverse k.leadingCoeff) * k) := by
          rw [map_mul]; ring
  have hexp : (X - C r) * (X - C s) = X ^ 2 + C (-(r + s)) * X + C (r * s) := by
    rw [map_neg, map_add, map_mul]; ring
  rw [monicPoly_two_expand, hexp] at hfac
  refine ⟨r, s, ?_, ?_⟩
  · have := congrArg (fun p => Polynomial.coeff p 1) hfac
    simpa using this
  · have := congrArg (fun p => Polynomial.coeff p 0) hfac
    simpa using this

end Reducible

/-! ## 3. The RAMIFIED (Eisenstein) certificate -/

section Ram

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- An Eisenstein monic quadratic is irreducible: if it split, both roots would lie in `𝔪`
(their sum is `-a₁ ∈ 𝔪` and their product `a₀ ∈ 𝔪`, and `𝔪` is prime), forcing `a₀ ∈ 𝔪²`. -/
theorem irreducible_of_eisenstein {a : Fin 2 → O} (h0 : a 0 ∈ maximalIdeal O)
    (h0' : a 0 ∉ (maximalIdeal O) ^ 2) (h1 : a 1 ∈ maximalIdeal O) :
    Irreducible (monicPoly a) := by
  by_contra hcon
  obtain ⟨r, s, hrs1, hrs0⟩ := exists_roots_of_not_irreducible hcon
  have hprod : r * s ∈ maximalIdeal O := hrs0 ▸ h0
  have hsum : r + s ∈ maximalIdeal O := by
    have : -(r + s) ∈ maximalIdeal O := hrs1 ▸ h1
    simpa using (Ideal.neg_mem_iff _).1 this
  have hprime : (maximalIdeal O).IsPrime := (maximalIdeal.isMaximal O).isPrime
  have hboth : r ∈ maximalIdeal O ∧ s ∈ maximalIdeal O := by
    rcases hprime.mem_or_mem hprod with hr | hs
    · exact ⟨hr, by simpa [hr] using Ideal.sub_mem _ hsum hr⟩
    · exact ⟨by simpa [hs] using Ideal.sub_mem _ hsum hs, hs⟩
  exact h0' (hrs0 ▸ (by rw [pow_two]; exact Ideal.mul_mem_mul hboth.1 hboth.2))

/-- **RAM certificate.** An Eisenstein monic quadratic has splitting type `{(2,1)}`. -/
theorem typeOf_ram_of_eisenstein {a : Fin 2 → O} (h0 : a 0 ∈ maximalIdeal O)
    (h0' : a 0 ∉ (maximalIdeal O) ^ 2) (h1 : a 1 ∈ maximalIdeal O) :
    typeOf (monicPoly a) = ramType := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hm : maximalIdeal O = Ideal.span {π} := hπ.maximalIdeal_eq
  have hirr := irreducible_of_eisenstein h0 h0' h1
  -- addVal (a 0) = 1
  have hdvd : π ∣ a 0 := by rwa [hm, Ideal.mem_span_singleton] at h0
  obtain ⟨b, hb⟩ := hdvd
  have hbu : IsUnit b := by
    by_contra hbn
    refine h0' ?_
    have : π ∣ b := by
      rw [← Ideal.mem_span_singleton, ← hm]
      exact (mem_maximalIdeal _).2 (mem_nonunits_iff.2 hbn)
    obtain ⟨c, rfl⟩ := this
    rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hb]
    exact ⟨c, by ring⟩
  have hbv : IsDiscreteValuationRing.addVal O b = 0 := by
    rw [← hbu.unit_spec]; exact IsDiscreteValuationRing.addVal_eq_zero_of_unit _
  have hval : IsDiscreteValuationRing.addVal O (a 0) = 1 := by
    rw [hb, AddValuation.map_mul, IsDiscreteValuationRing.addVal_uniformizer hπ, hbv, add_zero]
  have ha0 : a 0 ≠ 0 := by
    intro h
    rw [h] at hval
    simp at hval
  -- 1 ∈ normValues, so the residue degree is 1
  have hne : (AdjoinRoot.root (monicPoly a)) ≠ 0 := by
    intro h
    have h1' := norm_root_quad a
    rw [h, norm_zero_quad] at h1'
    exact ha0 h1'.symm
  have hmem : (1 : ℕ) ∈ normValues (monicPoly a) := by
    refine ⟨one_pos, AdjoinRoot.root (monicPoly a), hne, ?_⟩
    rw [norm_root_quad, hval]
    rfl
  have hinf : inertiaDegOf (monicPoly a) = 1 := by
    have hpos : 0 < sInf (normValues (monicPoly a)) := (Nat.sInf_mem ⟨1, hmem⟩).1
    exact le_antisymm (Nat.sInf_le hmem) hpos
  -- assemble
  have hF : IsMonicFactorization (monicPoly a) {monicPoly a} :=
    ⟨by intro g hg; rw [Multiset.mem_singleton.1 hg]; exact ⟨monicPoly_monic a, hirr⟩, by simp⟩
  ext
  rw [typeOf_data, monicFactors_eq hF]
  simp [ramType, efPair, ramIndexOf, hinf, monicPoly_natDegree]

end Ram

/-! ## 4. The INERT (anisotropic) certificate -/

section Inert

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- The binary norm form of `X² + a₁X + a₀`. -/
def quadForm (a : Fin 2 → O) (u v : O) : O := u ^ 2 - a 1 * u * v + a 0 * v ^ 2

/-- **Anisotropy mod 𝔪**: the only zero of the reduced norm form is `(0,0)`. Equivalently, the
reduction of `f` has no root in the residue field. -/
def Anisotropic (a : Fin 2 → O) : Prop :=
  ∀ u v : O, quadForm a u v ∈ maximalIdeal O → u ∈ maximalIdeal O ∧ v ∈ maximalIdeal O

theorem irreducible_of_anisotropic {a : Fin 2 → O} (h : Anisotropic a) :
    Irreducible (monicPoly a) := by
  by_contra hcon
  obtain ⟨r, s, hrs1, hrs0⟩ := exists_roots_of_not_irreducible hcon
  have hzero : quadForm a (-r) 1 = 0 := by
    rw [quadForm, hrs1, hrs0]; ring
  have := (h (-r) 1 (by rw [hzero]; exact Ideal.zero_mem _)).2
  exact (maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 this)

/-- **INERT certificate.** An anisotropic monic quadratic has splitting type `{(1,2)}`: every
norm valuation is even, because a norm in `𝔪` forces both coordinates into `𝔪`, and then the
form picks up a factor `π²`. -/
theorem typeOf_inert_of_anisotropic {a : Fin 2 → O} (h : Anisotropic a) :
    typeOf (monicPoly a) = inertType := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hm : maximalIdeal O = Ideal.span {π} := hπ.maximalIdeal_eq
  have hirr := irreducible_of_anisotropic h
  -- 1 ∉ normValues
  have hnot1 : (1 : ℕ) ∉ normValues (monicPoly a) := by
    rintro ⟨-, x, -, hx⟩
    obtain ⟨u, v, rfl⟩ := exists_quad_repr a x
    rw [norm_quad] at hx
    have hQ : quadForm a u v ∈ maximalIdeal O := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have hz : IsDiscreteValuationRing.addVal O (quadForm a u v) = 0 := by
        rw [← hu.unit_spec]; exact IsDiscreteValuationRing.addVal_eq_zero_of_unit _
      rw [show quadForm a u v = u ^ 2 - a 1 * u * v + a 0 * v ^ 2 from rfl] at hz
      rw [hz] at hx
      simp at hx
    obtain ⟨hu, hv⟩ := h u v hQ
    rw [hm, Ideal.mem_span_singleton] at hu hv
    obtain ⟨u', rfl⟩ := hu
    obtain ⟨v', rfl⟩ := hv
    have hsplit : (π * u') ^ 2 - a 1 * (π * u') * (π * v') + a 0 * (π * v') ^ 2
        = π ^ 2 * (u' ^ 2 - a 1 * u' * v' + a 0 * v' ^ 2) := by ring
    rw [hsplit, AddValuation.map_mul, hπ.addVal_pow] at hx
    have hle : ((2 : ℕ) : ℕ∞) ≤ ((1 : ℕ) : ℕ∞) := by rw [← hx]; exact le_self_add
    simp at hle
  -- the residue degree is therefore 2
  have h2 : (2 : ℕ) ∈ normValues (monicPoly a) := by
    have := natDegree_mem_normValues (monicPoly_monic a) (by rw [monicPoly_natDegree]; omega) hπ
    rwa [monicPoly_natDegree] at this
  have hinf : inertiaDegOf (monicPoly a) = 2 := by
    unfold inertiaDegOf
    have hmemInf := Nat.sInf_mem (⟨2, h2⟩ : (normValues (monicPoly a)).Nonempty)
    have hpos : 0 < sInf (normValues (monicPoly a)) := hmemInf.1
    have hle : sInf (normValues (monicPoly a)) ≤ 2 := Nat.sInf_le h2
    have hne1 : sInf (normValues (monicPoly a)) ≠ 1 := by
      intro he; exact hnot1 (he ▸ hmemInf)
    omega
  have hF : IsMonicFactorization (monicPoly a) {monicPoly a} :=
    ⟨by intro g hg; rw [Multiset.mem_singleton.1 hg]; exact ⟨monicPoly_monic a, hirr⟩, by simp⟩
  ext
  rw [typeOf_data, monicFactors_eq hF]
  simp [inertType, efPair, ramIndexOf, hinf, monicPoly_natDegree]

end Inert

end Uniformity.Density
