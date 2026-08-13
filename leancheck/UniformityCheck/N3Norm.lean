import Uniformity
import UniformityCheck.N3Base

/-!
# UniformityCheck.N3Norm — the ternary norm form and the two extreme cubic certificates

The `n = 3` analogue of `Uniformity.Density.QuadCert`: the `typeOf` certificates for the two
*extreme* monic cubics over a complete DVR `O`, both resting on one explicit computation.

For a coefficient vector `b : Fin 3 → R` over any nontrivial commutative ring write
`cub3 b = X³ + b₂X² + b₁X + b₀` (`= monicPoly b` over a domain, `monicPoly_eq_cub3`), put
`A = R[x]/(cub3 b) = AdjoinRoot (cub3 b)` with root `θ`, and use the power basis `(1, θ, θ²)`
(`cubBasis`). The defining relation `θ³ = -b₂θ² - b₁θ - b₀` (`root_cube`) gives, for
`x = u₀ + u₁θ + u₂θ²` (`cubElt b u`), the multiplication matrix (`leftMulMatrix_cub`)

    ⎡ u₀ , -u₂b₀     , -u₁b₀ + u₂b₀b₂        ⎤
    ⎢ u₁ , u₀ - u₂b₁ , -u₁b₁ + u₂(b₁b₂ - b₀) ⎥      (`cubMat b u`)
    ⎣ u₂ , u₁ - u₂b₂ , u₀ - u₁b₂ + u₂(b₂² - b₁) ⎦

whose determinant is the ternary norm form `N_{A/R}(u₀ + u₁θ + u₂θ²)` (`norm_cub`). Because the
matrix is a *polynomial expression in the coefficients*, it commutes with any ring map — in
particular with `residue O : O → k`, which is what turns the residue-field hypothesis of the
inert certificate into a statement about valuations (`residue_norm_cub`).

* **RAM** (`typeOf_ram3_of_eisenstein`): if `a₀ ∈ 𝔪 \ 𝔪²` and `a₁, a₂ ∈ 𝔪` (Eisenstein) then
  `cub3 a` is irreducible (Mathlib's `Polynomial.IsEisensteinAt.irreducible`) and
  `N(θ) = -a₀` has valuation `1` (`norm_root_cub`), so the gcd of the norm valuations — the
  residue degree — is `1`, `e = 3/1 = 3`, and `typeOf (monicPoly a) = ⟨{(3,1)}⟩ = c3ram`.
* **INERT** (`typeOf_inert3_of_residue_irreducible`): if the reduction `f̄ = cub3 ā` is
  irreducible over the residue field `k` then `f` is irreducible (`irreducible_of_map_irreducible`)
  and every norm valuation is divisible by `3` (`three_dvd_of_addVal_norm`). The engine is
  `isUnit_norm_of_unit_coeff`: if some `uᵢ` is a unit then `N(x)` is a unit, because its
  reduction is the norm of the *nonzero* element `ū₀ + ū₁θ̄ + ū₂θ̄²` of the FIELD `k[x]/(f̄)`.
  Strong induction on the valuation then peels a uniformizer at a time (`N(πy) = π³N(y)`), so
  `3` is a common divisor; `3 = deg f` is itself attained (`natDegree_mem_normValues`), so the
  gcd is exactly `3`: `f(g) = 3`, `e = 1`, `typeOf (monicPoly a) = ⟨{(1,3)}⟩ = c3inert`.

The three intermediate cubic types (`c3split`, `c3linInert`, `c3linRam`) are *not* here: they
factor through a linear factor and reduce to the `n = 2` certificates via `typeOf_mul` in
`N3Base`.

## Status

Sorry-free, axiom-free (Lean core only) — see the `#print axioms` lines at the end of the file.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace UniformityCheck

open Uniformity Uniformity.Density IsLocalRing Polynomial

/-! ## 1. The monic cubic over an arbitrary base ring -/

section Gen

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- The monic cubic `X³ + b₂X² + b₁X + b₀`, over an arbitrary commutative ring. -/
noncomputable def cub3 (b : Fin 3 → R) : Polynomial R :=
  X ^ 3 + C (b 2) * X ^ 2 + C (b 1) * X + C (b 0)

theorem cub3_monic (b : Fin 3 → R) : (cub3 b).Monic := by
  unfold cub3
  monicity!

theorem cub3_natDegree (b : Fin 3 → R) : (cub3 b).natDegree = 3 := by
  unfold cub3
  compute_degree!

theorem cub3_map {S : Type*} [CommRing S] [Nontrivial S] (φ : R →+* S) (b : Fin 3 → R) :
    (cub3 b).map φ = cub3 (fun i => φ (b i)) := by
  simp [cub3, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]

/-- The power basis `(1, θ, θ²)` of `R[x]/(cub3 b)`. -/
noncomputable def cubPB (b : Fin 3 → R) : PowerBasis R (AdjoinRoot (cub3 b)) :=
  AdjoinRoot.powerBasis' (cub3_monic b)

theorem cubPB_dim (b : Fin 3 → R) : (cubPB b).dim = 3 := cub3_natDegree b

/-- `(1, θ, θ²)` as an honest `Module.Basis (Fin 3)`. -/
noncomputable def cubBasis (b : Fin 3 → R) :
    Module.Basis (Fin 3) R (AdjoinRoot (cub3 b)) :=
  (cubPB b).basis.reindex (finCongr (cubPB_dim b))

theorem cubBasis_apply (b : Fin 3 → R) (i : Fin 3) :
    cubBasis b i = AdjoinRoot.root (cub3 b) ^ (i : ℕ) := by
  rw [cubBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

theorem cubBasis_zero (b : Fin 3 → R) : cubBasis b 0 = 1 := by
  rw [cubBasis_apply]; simp

theorem cubBasis_one (b : Fin 3 → R) : cubBasis b 1 = AdjoinRoot.root (cub3 b) := by
  rw [cubBasis_apply]; simp

theorem cubBasis_two (b : Fin 3 → R) : cubBasis b 2 = AdjoinRoot.root (cub3 b) ^ 2 := by
  rw [cubBasis_apply]; rfl

/-- `eval₂` of a monic cubic, in any commutative `R`-algebra. -/
theorem eval₂_cub3 {A : Type*} [CommRing A] (φ : R →+* A) (x : A) (b : Fin 3 → R) :
    (cub3 b).eval₂ φ x = x ^ 3 + φ (b 2) * x ^ 2 + φ (b 1) * x + φ (b 0) := by
  rw [cub3]
  simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]

/-- The defining relation `θ³ = -b₂θ² - b₁θ - b₀`. -/
theorem root_cube (b : Fin 3 → R) :
    (AdjoinRoot.root (cub3 b)) ^ 3
      = -(algebraMap R _ (b 2)) * AdjoinRoot.root (cub3 b) ^ 2
        - algebraMap R _ (b 1) * AdjoinRoot.root (cub3 b) - algebraMap R _ (b 0) := by
  have h := AdjoinRoot.eval₂_root (cub3 b)
  rw [eval₂_cub3] at h
  have hof : (AdjoinRoot.of (cub3 b) : R →+* AdjoinRoot (cub3 b))
      = algebraMap R (AdjoinRoot (cub3 b)) := rfl
  rw [hof] at h
  linear_combination h

/-- The general element `u₀ + u₁θ + u₂θ²`. -/
noncomputable def cubElt (b u : Fin 3 → R) : AdjoinRoot (cub3 b) :=
  algebraMap R _ (u 0) + algebraMap R _ (u 1) * AdjoinRoot.root (cub3 b)
    + algebraMap R _ (u 2) * AdjoinRoot.root (cub3 b) ^ 2

/-- The matrix of multiplication by `u₀ + u₁θ + u₂θ²` in the basis `(1, θ, θ²)`. -/
def cubMat (b u : Fin 3 → R) : Matrix (Fin 3) (Fin 3) R :=
  !![u 0, -(u 2 * b 0), -(u 1 * b 0) + u 2 * (b 0 * b 2);
     u 1, u 0 - u 2 * b 1, -(u 1 * b 1) + u 2 * (b 1 * b 2 - b 0);
     u 2, u 1 - u 2 * b 2, u 0 - u 1 * b 2 + u 2 * (b 2 ^ 2 - b 1)]

private theorem repr_comb3 (b : Fin 3 → R) (c₀ c₁ c₂ : R) (i : Fin 3) :
    (cubBasis b).repr (c₀ • cubBasis b 0 + c₁ • cubBasis b 1 + c₂ • cubBasis b 2) i
      = if i = 0 then c₀ else if i = 1 then c₁ else c₂ := by
  rw [map_add, map_add, map_smul, map_smul, map_smul, Module.Basis.repr_self,
    Module.Basis.repr_self, Module.Basis.repr_self]
  fin_cases i <;> simp

private theorem hsmul3 (b : Fin 3 → R) (c : R) (y : AdjoinRoot (cub3 b)) :
    c • y = algebraMap R (AdjoinRoot (cub3 b)) c * y := Algebra.smul_def c y

theorem cubElt_eq_comb (b u : Fin 3 → R) :
    cubElt b u = u 0 • cubBasis b 0 + u 1 • cubBasis b 1 + u 2 • cubBasis b 2 := by
  rw [cubBasis_zero, cubBasis_one, cubBasis_two, hsmul3, hsmul3, hsmul3, cubElt]
  ring

theorem cubElt_mul_zero (b u : Fin 3 → R) :
    cubElt b u * cubBasis b 0
      = u 0 • cubBasis b 0 + u 1 • cubBasis b 1 + u 2 • cubBasis b 2 := by
  rw [← cubElt_eq_comb, cubBasis_zero, mul_one]

theorem cubElt_mul_one (b u : Fin 3 → R) :
    cubElt b u * cubBasis b 1
      = (-(u 2 * b 0)) • cubBasis b 0 + (u 0 - u 2 * b 1) • cubBasis b 1
        + (u 1 - u 2 * b 2) • cubBasis b 2 := by
  have hc := root_cube b
  rw [cubBasis_zero, cubBasis_one, cubBasis_two, hsmul3, hsmul3, hsmul3, cubElt]
  simp only [map_neg, map_mul, map_sub]
  linear_combination (algebraMap R (AdjoinRoot (cub3 b)) (u 2)) * hc

theorem cubElt_mul_two (b u : Fin 3 → R) :
    cubElt b u * cubBasis b 2
      = (-(u 1 * b 0) + u 2 * (b 0 * b 2)) • cubBasis b 0
        + (-(u 1 * b 1) + u 2 * (b 1 * b 2 - b 0)) • cubBasis b 1
        + (u 0 - u 1 * b 2 + u 2 * (b 2 ^ 2 - b 1)) • cubBasis b 2 := by
  have hc := root_cube b
  rw [cubBasis_zero, cubBasis_one, cubBasis_two, hsmul3, hsmul3, hsmul3, cubElt]
  simp only [map_neg, map_mul, map_sub, map_add, map_pow]
  linear_combination (algebraMap R (AdjoinRoot (cub3 b)) (u 1)
    + algebraMap R (AdjoinRoot (cub3 b)) (u 2)
      * (AdjoinRoot.root (cub3 b) - algebraMap R (AdjoinRoot (cub3 b)) (b 2))) * hc

theorem leftMulMatrix_cub (b u : Fin 3 → R) :
    Algebra.leftMulMatrix (cubBasis b) (cubElt b u) = cubMat b u := by
  classical
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  fin_cases j
  · rw [show ((⟨0, by omega⟩ : Fin 3)) = (0 : Fin 3) from rfl, cubElt_mul_zero, repr_comb3]
    fin_cases i <;> simp [cubMat]
  · rw [show ((⟨1, by omega⟩ : Fin 3)) = (1 : Fin 3) from rfl, cubElt_mul_one, repr_comb3]
    fin_cases i <;> simp [cubMat]
  · rw [show ((⟨2, by omega⟩ : Fin 3)) = (2 : Fin 3) from rfl, cubElt_mul_two, repr_comb3]
    fin_cases i <;> simp [cubMat]

/-- **The ternary norm form**, as a `3 × 3` determinant. -/
theorem norm_cub (b u : Fin 3 → R) :
    Algebra.norm R (cubElt b u) = (cubMat b u).det := by
  classical
  rw [Algebra.norm_eq_matrix_det (cubBasis b), leftMulMatrix_cub]

theorem repr_cubElt (b u : Fin 3 → R) (i : Fin 3) :
    (cubBasis b).repr (cubElt b u) i = u i := by
  rw [cubElt_eq_comb, repr_comb3]
  fin_cases i <;> simp

theorem cubElt_eq_zero_iff (b u : Fin 3 → R) : cubElt b u = 0 ↔ ∀ i, u i = 0 := by
  constructor
  · intro h i
    have hr := repr_cubElt b u i
    rw [h] at hr
    simpa using hr.symm
  · intro h
    rw [cubElt, h 0, h 1, h 2]
    simp

theorem cubElt_surj (b : Fin 3 → R) (x : AdjoinRoot (cub3 b)) : ∃ u : Fin 3 → R, x = cubElt b u := by
  refine ⟨fun i => (cubBasis b).repr x i, ?_⟩
  rw [cubElt_eq_comb]
  have h := (cubBasis b).sum_repr x
  rw [Fin.sum_univ_three] at h
  exact h.symm

theorem cubElt_smul (b u : Fin 3 → R) (c : R) :
    cubElt b (fun i => c * u i) = algebraMap R _ c * cubElt b u := by
  rw [cubElt, cubElt]
  simp only [map_mul]
  ring

/-- The norm of the root: `N(θ) = -b₀`. -/
theorem norm_root_cub (b : Fin 3 → R) :
    Algebra.norm R (AdjoinRoot.root (cub3 b)) = -(b 0) := by
  have he : AdjoinRoot.root (cub3 b) = cubElt b ![0, 1, 0] := by
    rw [cubElt]; simp
  rw [he, norm_cub, Matrix.det_fin_three]
  simp [cubMat]

@[simp] theorem cub3_coeff_zero (b : Fin 3 → R) : (cub3 b).coeff 0 = b 0 := by
  simp [cub3, coeff_X_pow]

@[simp] theorem cub3_coeff_one (b : Fin 3 → R) : (cub3 b).coeff 1 = b 1 := by
  simp [cub3, coeff_X_pow]

@[simp] theorem cub3_coeff_two (b : Fin 3 → R) : (cub3 b).coeff 2 = b 2 := by
  simp [cub3, coeff_X_pow]

theorem finrank_cub (b : Fin 3 → R) : Module.finrank R (AdjoinRoot (cub3 b)) = 3 := by
  haveI hfin := (cubPB b).finite
  haveI hfree : Module.Free R (AdjoinRoot (cub3 b)) := Module.Free.of_basis (cubPB b).basis
  rw [(cubPB b).finrank]
  exact cubPB_dim b

end Gen

/-! ## 2. Reduction to the residue field -/

section Res

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- Reduction of a coefficient vector mod `𝔪`. -/
noncomputable def resVec (a : Fin 3 → O) : Fin 3 → ResidueField O := fun i => residue O (a i)

theorem cubMat_map (a u : Fin 3 → O) :
    (cubMat a u).map (residue O) = cubMat (resVec a) (resVec u) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cubMat, resVec, Matrix.map_apply]

theorem residue_norm_cub (a u : Fin 3 → O) :
    residue O (Algebra.norm O (cubElt a u)) = Algebra.norm (ResidueField O) (cubElt (resVec a) (resVec u)) := by
  rw [norm_cub, norm_cub, RingHom.map_det, RingHom.mapMatrix_apply, cubMat_map]

/-- **The key lemma.** If one coordinate of `u` is a unit, the norm of `u₀ + u₁θ + u₂θ²` is a
unit — because its reduction is the norm of a *nonzero* element of the residue extension
`k[x]/(f̄)`, a field when `f̄` is irreducible. -/
theorem isUnit_norm_of_unit_coeff {a : Fin 3 → O} (hbar : Irreducible (cub3 (resVec a)))
    {u : Fin 3 → O} {i : Fin 3} (hu : u i ∉ maximalIdeal O) :
    IsUnit (Algebra.norm O (cubElt a u)) := by
  haveI : Fact (Irreducible (cub3 (resVec a))) := ⟨hbar⟩
  have hune : cubElt (resVec a) (resVec u) ≠ 0 := by
    intro hz
    have hzi := (cubElt_eq_zero_iff (resVec a) (resVec u)).1 hz i
    exact hu ((residue_eq_zero_iff (u i)).1 hzi)
  have hnz : Algebra.norm (ResidueField O) (cubElt (resVec a) (resVec u)) ≠ 0 :=
    (Algebra.norm_ne_zero_iff_of_basis (cubBasis (resVec a))).2 hune
  rw [← residue_norm_cub] at hnz
  rw [← notMem_maximalIdeal]
  intro hmem
  exact hnz ((residue_eq_zero_iff _).2 hmem)

/-- **Every norm valuation is divisible by 3.** Strong induction on the valuation: either some
coordinate is a unit (valuation `0`) or all of them are divisible by `π`, which peels off
`N(π) = π³` and drops the valuation by exactly `3`. -/
theorem three_dvd_of_addVal_norm {a : Fin 3 → O} (hbar : Irreducible (cub3 (resVec a)))
    (hdom : IsDomain (AdjoinRoot (cub3 a))) {π : O} (hπ : Irreducible π) (n : ℕ) :
    ∀ x : AdjoinRoot (cub3 a), x ≠ 0 →
      IsDiscreteValuationRing.addVal O (Algebra.norm O x) = (n : ℕ∞) → 3 ∣ n := by
  haveI := hdom
  haveI hfin : Module.Finite O (AdjoinRoot (cub3 a)) := (cubPB a).finite
  haveI hfree : Module.Free O (AdjoinRoot (cub3 a)) := Module.Free.of_basis (cubPB a).basis
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx hn
    obtain ⟨u, rfl⟩ := cubElt_surj a x
    by_cases hu : ∃ i, u i ∉ maximalIdeal O
    · obtain ⟨i, hi⟩ := hu
      have hunit := isUnit_norm_of_unit_coeff hbar hi
      have hz : IsDiscreteValuationRing.addVal O (Algebra.norm O (cubElt a u)) = 0 := by
        rw [← hunit.unit_spec]; exact IsDiscreteValuationRing.addVal_eq_zero_of_unit _
      rw [hn] at hz
      have hn0 : n = 0 := by exact_mod_cast hz
      omega
    · replace hu : ∀ i, u i ∈ maximalIdeal O := fun i => not_not.mp (not_exists.mp hu i)
      have hm : maximalIdeal O = Ideal.span {π} := hπ.maximalIdeal_eq
      have hex : ∀ i, ∃ c : O, u i = π * c := by
        intro i
        have hi := hu i
        rw [hm, Ideal.mem_span_singleton] at hi
        exact hi
      choose u' hu' using hex
      have hueq : u = fun i => π * u' i := funext hu'
      have hfac : cubElt a u = algebraMap O (AdjoinRoot (cub3 a)) π * cubElt a u' := by
        rw [hueq, cubElt_smul]
      have hxne : cubElt a u' ≠ 0 := by
        intro h0
        exact hx (by rw [hfac, h0, mul_zero])
      have hnorm : Algebra.norm O (cubElt a u) = π ^ 3 * Algebra.norm O (cubElt a u') := by
        rw [hfac, map_mul, Algebra.norm_algebraMap, finrank_cub]
      have hnnz : Algebra.norm O (cubElt a u') ≠ 0 :=
        (Algebra.norm_ne_zero_iff_of_basis (cubBasis a)).2 hxne
      obtain ⟨n', hn'⟩ := exists_addVal_eq hnnz
      have hk : IsDiscreteValuationRing.addVal O (Algebra.norm O (cubElt a u))
          = ((3 : ℕ) : ℕ∞) + ((n' : ℕ) : ℕ∞) := by
        rw [hnorm, AddValuation.map_mul, hπ.addVal_pow, hn']
      rw [hn] at hk
      have hsum : 3 + n' = n := by
        have hcast : ((3 + n' : ℕ) : ℕ∞) = ((n : ℕ) : ℕ∞) := by push_cast; exact hk.symm
        exact_mod_cast hcast
      have hdvd := ih n' (by omega) (cubElt a u') hxne hn'
      omega

end Res

/-! ## 3. The Eisenstein (totally ramified) certificate -/

section Ram

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem monicPoly_eq_cub3 (a : Fin 3 → O) : monicPoly a = cub3 a := cubic_expand a

theorem irreducible_of_eisenstein3 {a : Fin 3 → O} (h0 : a 0 ∈ maximalIdeal O)
    (h0' : a 0 ∉ (maximalIdeal O) ^ 2) (h1 : a 1 ∈ maximalIdeal O) (h2 : a 2 ∈ maximalIdeal O) :
    Irreducible (cub3 a) := by
  have hE : (cub3 a).IsEisensteinAt (maximalIdeal O) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [(cub3_monic a).leadingCoeff]
      intro hmem
      exact (maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 hmem)
    · intro n hn
      rw [cub3_natDegree] at hn
      interval_cases n
      · rw [cub3_coeff_zero]; exact h0
      · rw [cub3_coeff_one]; exact h1
      · rw [cub3_coeff_two]; exact h2
    · rw [cub3_coeff_zero]; exact h0'
  exact hE.irreducible (maximalIdeal.isMaximal O).isPrime (cub3_monic a).isPrimitive
    (by rw [cub3_natDegree]; omega)

/-- **Eisenstein cubics are totally ramified.** -/
theorem typeOf_ram3_of_eisenstein {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {a : Fin 3 → O}
    (h0 : a 0 ∈ maximalIdeal O) (h0' : a 0 ∉ (maximalIdeal O) ^ 2)
    (h1 : a 1 ∈ maximalIdeal O) (h2 : a 2 ∈ maximalIdeal O) :
    typeOf (monicPoly a) = c3ram := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hirr := irreducible_of_eisenstein3 h0 h0' h1 h2
  -- `a 0` has valuation exactly `1`
  have hm : maximalIdeal O = Ideal.span {π} := hπ.maximalIdeal_eq
  have hdvd : π ∣ a 0 := by rwa [hm, Ideal.mem_span_singleton] at h0
  obtain ⟨c, hc⟩ := hdvd
  have hcu : IsUnit c := by
    by_contra hcn
    refine h0' ?_
    have hπc : π ∣ c := by
      rw [← Ideal.mem_span_singleton, ← hm]
      exact (mem_maximalIdeal _).2 (mem_nonunits_iff.2 hcn)
    obtain ⟨d, rfl⟩ := hπc
    rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hc]
    exact ⟨d, by ring⟩
  have hcv : IsDiscreteValuationRing.addVal O c = 0 := by
    rw [← hcu.unit_spec]; exact IsDiscreteValuationRing.addVal_eq_zero_of_unit _
  have hval : IsDiscreteValuationRing.addVal O (a 0) = 1 := by
    rw [hc, AddValuation.map_mul, IsDiscreteValuationRing.addVal_uniformizer hπ, hcv, add_zero]
  -- `θ ≠ 0` and `N(θ) = -a₀` has valuation `1`
  have hroot_elt : AdjoinRoot.root (cub3 a) = cubElt a ![0, 1, 0] := by
    rw [cubElt]; simp
  have hne : (AdjoinRoot.root (cub3 a)) ≠ 0 := by
    rw [hroot_elt]
    intro hz
    have h1' := (cubElt_eq_zero_iff a ![0, 1, 0]).1 hz 1
    simp at h1'
  have hnegval : IsDiscreteValuationRing.addVal O (-(a 0))
      = IsDiscreteValuationRing.addVal O (a 0) := AddValuation.map_neg _ _
  have hmem1 : (1 : ℕ) ∈ normValues (cub3 a) := by
    refine ⟨one_pos, AdjoinRoot.root (cub3 a), hne, ?_⟩
    rw [norm_root_cub, hnegval, hval]
    rfl
  have hinf : inertiaDegOf (cub3 a) = 1 := inertiaDegOf_eq_of hmem1 (fun m _ => one_dvd m)
  have hF : IsMonicFactorization (cub3 a) {cub3 a} :=
    ⟨by intro g hg; rw [Multiset.mem_singleton.1 hg]; exact ⟨cub3_monic a, hirr⟩, by simp⟩
  rw [monicPoly_eq_cub3]
  ext
  rw [typeOf_data, monicFactors_eq hF]
  simp [c3ram, efPair, ramIndexOf, hinf, cub3_natDegree]

end Ram

/-! ## 4. The inert certificate -/

section Inert

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **A cubic whose reduction is irreducible is inert.** -/
theorem typeOf_inert3_of_residue_irreducible {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {a : Fin 3 → O}
    (h : Irreducible ((monicPoly a).map (IsLocalRing.residue O))) :
    typeOf (monicPoly a) = c3inert := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  rw [monicPoly_eq_cub3] at h
  have hbar : Irreducible (cub3 (resVec a)) := by
    rwa [cub3_map] at h
  have hirr : Irreducible (cub3 a) := irreducible_of_map_irreducible (cub3_monic a) h
  have hprime : Prime (cub3 a) := UniqueFactorizationMonoid.irreducible_iff_prime.1 hirr
  have hdom : IsDomain (AdjoinRoot (cub3 a)) := AdjoinRoot.isDomain_of_prime hprime
  have h3 : (3 : ℕ) ∈ normValues (cub3 a) := by
    have hmem := natDegree_mem_normValues (cub3_monic a) (by rw [cub3_natDegree]; omega) hπ
    rwa [cub3_natDegree] at hmem
  have hdvd3 : ∀ m ∈ normValues (cub3 a), 3 ∣ m := by
    rintro m ⟨-, x, hxne, hxv⟩
    exact three_dvd_of_addVal_norm hbar hdom hπ m x hxne hxv
  have hinf : inertiaDegOf (cub3 a) = 3 := inertiaDegOf_eq_of h3 hdvd3
  have hF : IsMonicFactorization (cub3 a) {cub3 a} :=
    ⟨by intro g hg; rw [Multiset.mem_singleton.1 hg]; exact ⟨cub3_monic a, hirr⟩, by simp⟩
  rw [monicPoly_eq_cub3]
  ext
  rw [typeOf_data, monicFactors_eq hF]
  simp [c3inert, efPair, ramIndexOf, hinf, cub3_natDegree]

end Inert

end UniformityCheck

#print axioms UniformityCheck.typeOf_ram3_of_eisenstein
#print axioms UniformityCheck.typeOf_inert3_of_residue_irreducible
