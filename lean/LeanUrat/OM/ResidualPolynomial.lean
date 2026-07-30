/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.PadicValuation
import LeanUrat.OM.NewtonPolygon

/-!
# M4 — ResidualPolynomial: the residual polynomial of a side (blueprint §"M4: the residual polynomial")

**FROZEN SIGNATURE SKELETON.** This module states the blueprint M4 nodes (`subsec:m4`, `subsec:gap1`)
with their EXACT intended signatures and `sorry` proof bodies. The point is a compiling signature
surface, not proven content.

The residual polynomial `R_S(f) = ∑_t c_t Y^t ∈ k_S[Y]` is computed from the coefficients of a monic
`f : ℤ_[p][X]` lying exactly on a side `S` of the lower Newton polygon. At order 1 the residue field
`k_S = ZMod p` is finite; at higher orders M5 supplies a finite tower field. We therefore phrase the
residual data over a general finite residue field `kS`, with the residual coefficient extracted from
the p-adic unit part via `PadicInt.toZMod`-style plumbing (recorded here as an opaque map, the genuine
M4 content being the index arithmetic `ℓ(S) = e_S · d` and the `unitCoeff/toZMod` guard).

Blueprint nodes frozen:
* `def:residual-coeff`  → `residualCoeff`
* `def:residual-poly`   → `residualPoly`
* `lem:residual-endpoints` → `residualCoeff_endpoints_ne_zero`
* `lem:residual-degree` → `residualPoly_natDegree`
* `lem:residual-monic`  → `residualPoly_monic_normalized`
* `thm:residual-sep-sqfree` → `residual_separable_iff_squarefree`
* `def:descent-trigger` → `needsDescent`
* `lem:descent-repeated-factor` → `needsDescent_iff_exists_repeated`
* `lem:residual-factorization` (GAP 1) → `residualPoly_factorization` + `ResidualFactorization`
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.M4

open Polynomial

open scoped Classical

/-! ## The residual side datum

We reuse `LeanUrat.OM.NewtonPolygon.Side` (the raw side endpoints `(i₀, v₀)–(j₀, v₁)`). The residue
field `kS` is a finite field carried as an explicit type argument: at order 1 it is `ZMod p`, at
order `r` it is the M5 tower field `F_r`. -/

/-- The number `d = ℓ(S)/e_S` of residual coefficients minus one (the residual degree). Defined from
the side's length and ramification denominator. -/
noncomputable def residualDeg (S : NewtonPolygon.Side) : ℕ := S.length / S.e

/-! ## The residual coefficient `c_t ∈ k_S` (`def:residual-coeff`)

`c_t` is the image in `k_S` of the unit part of `a_{i_t}/p^{v_{i_t}}` provided `(i_t, v_{i_t})` lies on
`S`, and `0` otherwise. In Lean: `PadicInt.toZMod (unitCoeff …)` lifted through the residue map. For
the frozen skeleton the genuine `PadicInt.unitCoeff/toZMod` plumbing is encoded as an opaque map
`coeffData : ℕ → kS` (the per-abscissa residual datum), so the downstream signatures typecheck. -/

variable {p : ℕ} [Fact p.Prime] {kS : Type*} [Field kS] [Finite kS]

/-- **The residual coefficient `c_t`** (`def:residual-coeff`, GMN Def 2.20). The image in `k_S` of the
unit part of `a_{i_t}/p^{v_{i_t}}` when `(i_t, v_{i_t})` lies on `S`, else `0`. Carried via the
per-abscissa residual datum `coeffData` (the `PadicInt.unitCoeff/toZMod` lift, opaque in the
skeleton). -/
noncomputable def residualCoeff (coeffData : ℕ → kS) (_S : NewtonPolygon.Side) (t : ℕ) : kS :=
  coeffData t

/-- **The residual polynomial `R_S(f)(Y) = ∑_{t=0}^d c_t Y^t ∈ k_S[Y]`** (`def:residual-poly`,
GMN Def 2.21). -/
noncomputable def residualPoly (coeffData : ℕ → kS) (S : NewtonPolygon.Side) : kS[X] :=
  ∑ t ∈ Finset.range (residualDeg S + 1),
    Polynomial.C (residualCoeff coeffData S t) * Polynomial.X ^ t

/-- **`residualPoly` is a PURE function of the coefficient datum** (`CERTLEVEL_DECOMP.md` Layer B,
B-res-1). `residualPoly` is a `Finset.sum (C (coeffData t) * X^t)` over `Finset.range (residualDeg S + 1)`,
depending on `coeffData`/`S` only — so equal coefficient data yields the same residual polynomial. This
is the cleanest statement of residual stability: it equals coeff-data equality. Discharged by
`subst; rfl`, unconditional, no axiom. -/
theorem residualPoly_congr (coeffData coeffData' : ℕ → kS) (S : NewtonPolygon.Side)
    (h : coeffData = coeffData') :
    residualPoly coeffData S = residualPoly coeffData' S := by
  subst h; rfl

/-! ### REVISION (BUG-M4 fix): endpoint hypotheses thread the unit-coefficient guard

The four endpoint/degree/monic lemmas below were UNPROVABLE as originally stated, because `coeffData`
is a FREE opaque parameter: with no constraint on it, `coeffData (residualDeg S)` could be `0`, forcing
`residualPoly` to have smaller degree (or be `0`), contradicting the stated `natDegree = residualDeg S`
and `≠ 0`. The genuine M4 content (`lem:residual-endpoints`, GMN Def 2.20) is that the endpoints of a
side are VERTICES of the Newton polygon, so the corresponding residual coefficients `c_0` and `c_d` are
units — i.e. NONZERO in `k_S`. We thread that as the two explicit hypotheses
`(h0 : coeffData 0 ≠ 0) (hd : coeffData (residualDeg S) ≠ 0)` on each lemma. The consumer (M7) supplies
them from the genuine vertex property. -/

/-- **Coefficient extraction.** The `j`-th coefficient of `residualPoly` is `coeffData j` when
`j ≤ residualDeg S`, else `0`. -/
theorem residualPoly_coeff (coeffData : ℕ → kS) (S : NewtonPolygon.Side) (j : ℕ) :
    (residualPoly coeffData S).coeff j =
      if j ≤ residualDeg S then coeffData j else 0 := by
  classical
  rw [residualPoly, Polynomial.finsetSum_coeff]
  simp only [residualCoeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_ite_eq (Finset.range (residualDeg S + 1)) j (fun t => coeffData t)]
  simp only [Finset.mem_range, Nat.lt_succ_iff]

/-! ### Residual multiplicativity on a shared side (`lem:residual-factorization`, GMN Thm 2.26)

For two on-a-shared-side factors `A, B` whose product is read on the side `S`, the residual
polynomial of the product is the PRODUCT of the factor residual polynomials — the F3 shape of a
product side is the multiset union of the block shapes (blueprint §W4d (d2), the (iii) obligation of
`ProductTheorem`).  The load-bearing algebraic fact, SymPy-verified with 0 violations on gate cases
B, C (`/workspace-vast/asving/tmp/phaseb_surj2/coeff_conv_check.py`, `(C1)/(C3)`), is that the
on-side residual coefficient datum of the product is the **Cauchy convolution** of the factor data:
`cd t = ∑_{s + u = t} cdA s · cdB u`.  Given that convolution identity (up to the residual degree)
and the two block data vanishing strictly above their own residual degrees, `residualPoly` multiplies
via `Polynomial.coeff_mul`.  This is a PURE polynomial-algebra lemma over the residue field `kS`. -/

/-- **`residualPoly` multiplicativity on a shared side** (`lem:residual-factorization`, GMN Thm 2.26;
`ProductTheorem` obligation (iii)).  If the residual datum of the product `cd` is the Cauchy
convolution of the factor data `cdA, cdB` up to the (additive) residual degree, and each factor datum
vanishes strictly above its own residual degree, then the residual polynomials multiply:
`residualPoly cd S = residualPoly cdA SA · residualPoly cdB SB`.  Proof: coefficient-wise via
`residualPoly_coeff` (which zeroes past the residual degree) and `Polynomial.coeff_mul`; the vanishing
hypotheses drop the per-factor guards so the antidiagonal sum matches the convolution exactly. -/
theorem residualPoly_mul (cd cdA cdB : ℕ → kS) (S SA SB : NewtonPolygon.Side)
    (hdeg : residualDeg S = residualDeg SA + residualDeg SB)
    (hAvanish : ∀ t, residualDeg SA < t → cdA t = 0)
    (hBvanish : ∀ t, residualDeg SB < t → cdB t = 0)
    (hconv : ∀ t, t ≤ residualDeg S →
      cd t = ∑ x ∈ Finset.antidiagonal t, cdA x.1 * cdB x.2) :
    residualPoly cd S = residualPoly cdA SA * residualPoly cdB SB := by
  classical
  ext j
  rw [residualPoly_coeff, Polynomial.coeff_mul]
  -- rewrite each antidiagonal factor via `residualPoly_coeff`, then drop the guards by vanishing
  have hterm : ∀ x ∈ Finset.antidiagonal j,
      (residualPoly cdA SA).coeff x.1 * (residualPoly cdB SB).coeff x.2 = cdA x.1 * cdB x.2 := by
    intro x _
    rw [residualPoly_coeff, residualPoly_coeff]
    congr 1
    · by_cases hx : x.1 ≤ residualDeg SA
      · rw [if_pos hx]
      · rw [if_neg hx, hAvanish x.1 (by omega)]
    · by_cases hx : x.2 ≤ residualDeg SB
      · rw [if_pos hx]
      · rw [if_neg hx, hBvanish x.2 (by omega)]
  rw [Finset.sum_congr rfl hterm]
  by_cases hj : j ≤ residualDeg S
  · rw [if_pos hj, hconv j hj]
  · rw [if_neg hj]
    -- j > dA + dB: every antidiagonal term has x.1 > dA or x.2 > dB, hence a vanishing factor
    refine (Finset.sum_eq_zero fun x hx => ?_).symm
    have hsum : x.1 + x.2 = j := Finset.mem_antidiagonal.mp hx
    by_cases hx1 : residualDeg SA < x.1
    · rw [hAvanish x.1 hx1, zero_mul]
    · rw [hBvanish x.2 (by omega), mul_zero]

/-- `natDegree (residualPoly) ≤ residualDeg S` (all terms have degree `≤ d`). -/
theorem residualPoly_natDegree_le (coeffData : ℕ → kS) (S : NewtonPolygon.Side) :
    (residualPoly coeffData S).natDegree ≤ residualDeg S := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun j hj => ?_
  rw [residualPoly_coeff, if_neg (by omega)]

/-- **Endpoint coefficients are units** (`lem:residual-endpoints`). The endpoints of the side are
vertices of the polygon, so `c_0 ≠ 0` and `c_d ≠ 0` in `k_S`. REVISED: threads the vertex hypotheses
`h0 : coeffData 0 ≠ 0`, `hd : coeffData (residualDeg S) ≠ 0`. -/
theorem residualCoeff_endpoints_ne_zero (coeffData : ℕ → kS) (S : NewtonPolygon.Side)
    (h0 : coeffData 0 ≠ 0) (hd : coeffData (residualDeg S) ≠ 0) :
    residualCoeff coeffData S 0 ≠ 0 ∧ residualCoeff coeffData S (residualDeg S) ≠ 0 :=
  ⟨h0, hd⟩

/-- **Degree formula** (`lem:residual-degree`). `deg R_S(f) = d = ℓ(S)/e_S`, and `R_S(f)` is never
divisible by `Y` (its constant term `c_0 ≠ 0`). REVISED: threads `hd : coeffData (residualDeg S) ≠ 0`
(the top coefficient is the nonzero leading vertex coefficient). -/
theorem residualPoly_natDegree (coeffData : ℕ → kS) (S : NewtonPolygon.Side)
    (hd : coeffData (residualDeg S) ≠ 0) :
    (residualPoly coeffData S).natDegree = residualDeg S := by
  refine le_antisymm (residualPoly_natDegree_le coeffData S) ?_
  -- the `d`-th coefficient is `coeffData d ≠ 0`, so the degree is at least `d`
  apply Polynomial.le_natDegree_of_ne_zero
  rw [residualPoly_coeff, if_pos (le_refl _)]
  exact hd

/-- `R_S(f) ≠ 0` (its leading coefficient `c_d ≠ 0`). Needed downstream for `normalizedFactors`.
REVISED: threads `hd : coeffData (residualDeg S) ≠ 0`. -/
theorem residualPoly_ne_zero (coeffData : ℕ → kS) (S : NewtonPolygon.Side)
    (hd : coeffData (residualDeg S) ≠ 0) :
    residualPoly coeffData S ≠ 0 := by
  intro hzero
  have := residualPoly_coeff coeffData S (residualDeg S)
  rw [hzero, Polynomial.coeff_zero, if_pos le_rfl] at this
  exact hd this.symm

/-- **Residual is monic after normalization** (`lem:residual-monic`). The normalized residual
`c_d⁻¹ • R_S` is monic of degree `d` over `k_S`. REVISED: threads `hd : coeffData (residualDeg S) ≠ 0`
(so `R_S ≠ 0` and `leadingCoeff⁻¹ · R_S` is monic by `Polynomial.monic_C_mul_of_...`). -/
theorem residualPoly_monic_normalized (coeffData : ℕ → kS) (S : NewtonPolygon.Side)
    (hd : coeffData (residualDeg S) ≠ 0) :
    (Polynomial.C (residualPoly coeffData S).leadingCoeff⁻¹ * residualPoly coeffData S).Monic := by
  have hne : residualPoly coeffData S ≠ 0 := residualPoly_ne_zero coeffData S hd
  have hlc : (residualPoly coeffData S).leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hne
  -- `C c⁻¹ * R` is monic: its leading coeff is `c⁻¹ * c = 1`
  rw [Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_C_mul (inv_ne_zero hlc),
    Polynomial.coeff_C_mul, ← Polynomial.leadingCoeff]
  exact inv_mul_cancel₀ hlc

/-- **Separable ⇔ squarefree over the residue field** (`thm:residual-sep-sqfree`). `k_S` is finite,
hence perfect: `PerfectField.separable_iff_squarefree`. -/
theorem residual_separable_iff_squarefree (R : kS[X]) :
    R.Separable ↔ Squarefree R :=
  PerfectField.separable_iff_squarefree

/-- The negated form (used by the descent trigger). -/
theorem not_residual_separable_iff_not_squarefree (R : kS[X]) :
    ¬ R.Separable ↔ ¬ Squarefree R :=
  not_congr PerfectField.separable_iff_squarefree

/-- **Descent trigger** (`def:descent-trigger`, GMN Lemma 3.11(3)). A side needs descent iff its
residual polynomial is non-separable, equivalently non-squarefree. -/
def needsDescent (coeffData : ℕ → kS) (S : NewtonPolygon.Side) : Prop :=
  ¬ Squarefree (residualPoly coeffData S)

/-- **Descent trigger localizes to a repeated factor** (`lem:descent-repeated-factor`).
`needsDescent` holds iff there is a monic irreducible `ψ ∈ k_S[Y]` and `μ ≥ 2` with `ψ^μ ∣ R_S(f)`.
Each such `(ψ, μ)` is the data of one descent child. -/
theorem needsDescent_iff_exists_repeated (coeffData : ℕ → kS) (S : NewtonPolygon.Side) :
    needsDescent coeffData S ↔
      ∃ (ψ : kS[X]) (μ : ℕ), ψ.Monic ∧ Irreducible ψ ∧ 2 ≤ μ ∧
        ψ ^ μ ∣ residualPoly coeffData S := by
  classical
  set R := residualPoly coeffData S with hR
  unfold needsDescent
  rw [← hR]
  constructor
  · -- forward: not squarefree ⇒ a repeated monic irreducible factor exists
    intro hns
    by_cases hR0 : R = 0
    · -- over a field `X` is a monic irreducible and `X^2 ∣ 0`
      exact ⟨X, 2, monic_X, irreducible_X, le_refl 2, by simp [hR0]⟩
    · -- `R ≠ 0`: use the normalized-factor multiset
      rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hR0,
        Multiset.nodup_iff_count_le_one] at hns
      push Not at hns
      obtain ⟨ψ, hψ⟩ := hns
      have hμ : 2 ≤ Multiset.count ψ (UniqueFactorizationMonoid.normalizedFactors R) := hψ
      have hmem : ψ ∈ UniqueFactorizationMonoid.normalizedFactors R :=
        Multiset.count_pos.mp (by omega)
      have hfacts := (Polynomial.mem_normalizedFactors_iff hR0).mp hmem
      obtain ⟨hirr, hmonic, _⟩ := hfacts
      refine ⟨ψ, Multiset.count ψ (UniqueFactorizationMonoid.normalizedFactors R),
        hmonic, hirr, hμ, ?_⟩
      -- `ψ^μ ∣ R` via the normalized-factor divisibility criterion
      rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
        (pow_ne_zero _ hirr.ne_zero) hR0,
        Irreducible.normalizedFactors_pow hirr, hmonic.normalize_eq_self]
      exact Multiset.le_count_iff_replicate_le.mp le_rfl
  · -- reverse: a repeated irreducible factor forbids squarefreeness
    rintro ⟨ψ, μ, _hmonic, hirr, hμ, hdvd⟩ hsq
    exact hirr.not_isUnit (hsq ψ (pow_two ψ ▸ (pow_dvd_pow ψ hμ).trans hdvd))

/-! ## GAP 1 (`lem:residual-factorization`): the complete coprime residual factorization

The full coprime factorization of `R_S(f)` as `c · ∏_j ψ_j^{a_j}` with the `ψ_j` pairwise-distinct
monic irreducibles, exposed as a single `structure ResidualFactorization` carrying the `Finset` of
distinct factors, the multiplicity function, and the structural proofs (distinctness, degree budget,
multiplicity-as-cluster-size). `def:cells-of-type` (M7) consumes it (one cell per element of the
`Finset`). -/

/-- **The complete coprime residual factorization** (`lem:residual-factorization`, GAP 1), exposed as a
structure consumed by M7: the `Finset` of distinct monic irreducible factors `ψ`, their multiplicity
`mult ψ`, and the structural clauses. -/
structure ResidualFactorization (R : kS[X]) where
  /-- The finite set of distinct monic irreducible factors `ψ_j`. -/
  factors : Finset kS[X]
  /-- The multiplicity `a_ψ = Multiset.count ψ (normalizedFactors R)`. -/
  mult : kS[X] → ℕ
  /-- Each factor is monic. -/
  factors_monic : ∀ ψ ∈ factors, ψ.Monic
  /-- Each factor is irreducible. -/
  factors_irreducible : ∀ ψ ∈ factors, Irreducible ψ
  /-- Each factor has multiplicity `≥ 1`. -/
  mult_pos : ∀ ψ ∈ factors, 1 ≤ mult ψ
  /-- **The factorization identity** `R = leadingCoeff · ∏_j ψ_j^{a_j}`. -/
  prod_eq : R = Polynomial.C R.leadingCoeff * ∏ ψ ∈ factors, ψ ^ mult ψ
  /-- **(1) pairwise coprimality** of the distinct monic irreducibles. -/
  pairwise_coprime : ∀ ψ ∈ factors, ∀ φ ∈ factors, ψ ≠ φ → IsCoprime ψ φ
  /-- **(2) degree budget** `∑_j a_j · deg ψ_j = deg R`. -/
  degree_budget : ∑ ψ ∈ factors, mult ψ * ψ.natDegree = R.natDegree

/-- **GAP 1: every residual polynomial has a complete coprime factorization**
(`lem:residual-factorization`). Over the finite (perfect) residue field `k_S`, `R := R_S(f)` factors
as `c · ∏_j ψ_j^{a_j}` with the structural data of `ResidualFactorization`. -/
theorem residualPoly_factorization (coeffData : ℕ → kS) (S : NewtonPolygon.Side) :
    Nonempty (ResidualFactorization (residualPoly coeffData S)) := by
  classical
  set R := residualPoly coeffData S with hR
  by_cases hR0 : R = 0
  · -- degenerate case: the empty factorization works for `R = 0`
    refine ⟨{
      factors := ∅
      mult := fun _ => 0
      factors_monic := by simp
      factors_irreducible := by simp
      mult_pos := by simp
      prod_eq := by simp [hR0]
      pairwise_coprime := by simp
      degree_budget := by simp [hR0] }⟩
  · -- the genuine factorization via `normalizedFactors`
    set facs := UniqueFactorizationMonoid.normalizedFactors R with hfacs
    -- each normalized factor is irreducible, monic, and divides `R`
    have hmem_iff : ∀ ψ, ψ ∈ facs ↔ Irreducible ψ ∧ ψ.Monic ∧ ψ ∣ R := fun ψ =>
      Polynomial.mem_normalizedFactors_iff hR0
    -- the product of all distinct factors raised to their multiplicities
    have hprodcount : (∏ ψ ∈ facs.toFinset, ψ ^ facs.count ψ) = facs.prod :=
      (Finset.prod_multiset_count facs).symm
    -- `facs.prod = normalize R`
    have hprodnorm : facs.prod = normalize R :=
      UniqueFactorizationMonoid.prod_normalizedFactors_eq hR0
    -- `C R.leadingCoeff * normalize R = R`
    have hlc : R.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hR0
    have hCnR : Polynomial.C R.leadingCoeff * normalize R = R := by
      rw [normalize_apply, Polynomial.coe_normUnit_of_ne_zero hR0,
        mul_left_comm, ← Polynomial.C_mul, mul_inv_cancel₀ hlc, Polynomial.C_1, mul_one]
    have hfact : R = Polynomial.C R.leadingCoeff * ∏ ψ ∈ facs.toFinset, ψ ^ facs.count ψ := by
      rw [hprodcount, hprodnorm, hCnR]
    refine ⟨{
      factors := facs.toFinset
      mult := fun ψ => facs.count ψ
      factors_monic := fun ψ hψ => ((hmem_iff ψ).mp (Multiset.mem_toFinset.mp hψ)).2.1
      factors_irreducible := fun ψ hψ => ((hmem_iff ψ).mp (Multiset.mem_toFinset.mp hψ)).1
      mult_pos := fun ψ hψ =>
        Multiset.one_le_count_iff_mem.mpr (Multiset.mem_toFinset.mp hψ)
      prod_eq := hfact
      pairwise_coprime := ?_
      degree_budget := ?_ }⟩
    · -- distinct monic irreducibles are coprime
      intro ψ hψ φ hφ hne
      obtain ⟨hψirr, hψmon, _⟩ := (hmem_iff ψ).mp (Multiset.mem_toFinset.mp hψ)
      obtain ⟨hφirr, hφmon, _⟩ := (hmem_iff φ).mp (Multiset.mem_toFinset.mp hφ)
      rw [hψirr.coprime_iff_not_dvd]
      intro hdvd
      exact hne (Polynomial.eq_of_monic_of_associated hψmon hφmon
        ((hψirr.dvd_irreducible_iff_associated hφirr).mp hdvd))
    · -- degree budget: take `natDegree` of the factorization identity
      have key : R.natDegree = ∑ ψ ∈ facs.toFinset, facs.count ψ * ψ.natDegree := by
        rw [hfact, Polynomial.natDegree_C_mul hlc, Polynomial.natDegree_prod]
        · refine Finset.sum_congr rfl (fun ψ hψ => ?_)
          rw [Polynomial.natDegree_pow]
        · intro ψ hψ
          obtain ⟨hψirr, _, _⟩ := (hmem_iff ψ).mp (Multiset.mem_toFinset.mp hψ)
          exact pow_ne_zero _ hψirr.ne_zero
      exact key.symm

/-- **GAP-1 generalization: ANY polynomial over a finite field has a complete coprime factorization**
(`def:om-cell` consumes this for `M5.cells`, which factors the arbitrary residual `T.Rr`, not only a
`residualPoly coeffData S`). Verbatim the `residualPoly_factorization` construction with `R` free.
Sorry-free. -/
theorem factorize_any (R : kS[X]) : Nonempty (ResidualFactorization R) := by
  classical
  by_cases hR0 : R = 0
  · -- degenerate case: the empty factorization works for `R = 0`
    refine ⟨{
      factors := ∅
      mult := fun _ => 0
      factors_monic := by simp
      factors_irreducible := by simp
      mult_pos := by simp
      prod_eq := by simp [hR0]
      pairwise_coprime := by simp
      degree_budget := by simp [hR0] }⟩
  · -- the genuine factorization via `normalizedFactors`
    set facs := UniqueFactorizationMonoid.normalizedFactors R with hfacs
    -- each normalized factor is irreducible, monic, and divides `R`
    have hmem_iff : ∀ ψ, ψ ∈ facs ↔ Irreducible ψ ∧ ψ.Monic ∧ ψ ∣ R := fun ψ =>
      Polynomial.mem_normalizedFactors_iff hR0
    -- the product of all distinct factors raised to their multiplicities
    have hprodcount : (∏ ψ ∈ facs.toFinset, ψ ^ facs.count ψ) = facs.prod :=
      (Finset.prod_multiset_count facs).symm
    -- `facs.prod = normalize R`
    have hprodnorm : facs.prod = normalize R :=
      UniqueFactorizationMonoid.prod_normalizedFactors_eq hR0
    -- `C R.leadingCoeff * normalize R = R`
    have hlc : R.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hR0
    have hCnR : Polynomial.C R.leadingCoeff * normalize R = R := by
      rw [normalize_apply, Polynomial.coe_normUnit_of_ne_zero hR0,
        mul_left_comm, ← Polynomial.C_mul, mul_inv_cancel₀ hlc, Polynomial.C_1, mul_one]
    have hfact : R = Polynomial.C R.leadingCoeff * ∏ ψ ∈ facs.toFinset, ψ ^ facs.count ψ := by
      rw [hprodcount, hprodnorm, hCnR]
    refine ⟨{
      factors := facs.toFinset
      mult := fun ψ => facs.count ψ
      factors_monic := fun ψ hψ => ((hmem_iff ψ).mp (Multiset.mem_toFinset.mp hψ)).2.1
      factors_irreducible := fun ψ hψ => ((hmem_iff ψ).mp (Multiset.mem_toFinset.mp hψ)).1
      mult_pos := fun ψ hψ =>
        Multiset.one_le_count_iff_mem.mpr (Multiset.mem_toFinset.mp hψ)
      prod_eq := hfact
      pairwise_coprime := ?_
      degree_budget := ?_ }⟩
    · -- distinct monic irreducibles are coprime
      intro ψ hψ φ hφ hne
      obtain ⟨hψirr, hψmon, _⟩ := (hmem_iff ψ).mp (Multiset.mem_toFinset.mp hψ)
      obtain ⟨hφirr, hφmon, _⟩ := (hmem_iff φ).mp (Multiset.mem_toFinset.mp hφ)
      rw [hψirr.coprime_iff_not_dvd]
      intro hdvd
      exact hne (Polynomial.eq_of_monic_of_associated hψmon hφmon
        ((hψirr.dvd_irreducible_iff_associated hφirr).mp hdvd))
    · -- degree budget: take `natDegree` of the factorization identity
      have key : R.natDegree = ∑ ψ ∈ facs.toFinset, facs.count ψ * ψ.natDegree := by
        rw [hfact, Polynomial.natDegree_C_mul hlc, Polynomial.natDegree_prod]
        · refine Finset.sum_congr rfl (fun ψ hψ => ?_)
          rw [Polynomial.natDegree_pow]
        · intro ψ hψ
          obtain ⟨hψirr, _, _⟩ := (hmem_iff ψ).mp (Multiset.mem_toFinset.mp hψ)
          exact pow_ne_zero _ hψirr.ne_zero
      exact key.symm

end LeanUrat.OM.M4
