/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H93
import Uniformity.Density.TypeOfAlgebra

/-!
# Uniformity.ChapH.H94 — `LEMMA GENIND-0`: closure of `(A1)`-admissibility

**Chapter H, NODE H.94** (`blueprint/CHAP-H_general_induction.md` §13; source `EFF.GENIND.30`,
`LEMMA GENIND-0`'s statement and proof). *`(A1)`-admissibility is closed under products, finite
disjoint unions, and affine reparameterization.* Three clauses:

* **(i) product.** Given `A1Cell r₁` and `A1Cell r₂` there is an `A1Cell (r₁ + r₂)` whose locus
  box is the product box (`Fin.append` on offsets and strides), whose exponent is the sum of the
  two exponents (`A1Cell.prod_exp`, positive coefficients preserved), whose coefficient is the
  product, and whose σ is the multiset sum — degree-compatible with the landed
  `FactorizationType.degree_mk_add` (`A1Cell.prod_σ_degree`).
* **(ii) union.** Nothing to prove: `A1Family` is `List`, hence closed under `++` by
  construction, and the union's cells' data are the concatenation.  Per the node's SIGNATURE
  block this clause is left definitional and carries no named declaration.
* **(iii) affine reparameterization.** For the unimodular change `(w₁, w₂) ↦ (w₁, δ)` with
  `w₂ = w₁ + 1 + δ` (the corpus's `δ`-coordinate trick, `W-12` §S3.4's 2SIDED instance), a cell
  over `(w₁, w₂)` transports to a cell over `(w₁, δ)` — `A1Cell.deltaSubst` — with the same locus
  box, an exponent still affine with positive coefficients, and the same σ; `deltaSubst_exp` is
  the signed statement that the transported exponent computes the substituted one.

**⚠ THE DOMINANCE-REGION SPLIT IS NOT FORMALIZED, AND THAT IS DECLARED.** Clause (iii) lands the
`δ`-substitution — the corpus's *mechanism* — but **not** the induction on dimension that turns
`{ν₁ ≥ ν₂} ∩ (shifted product)` into a finite union of shifted products at arbitrary `r`.  That
induction is a genuine combinatorial-geometry argument, declared OPEN by the blueprint (§16
item 6).  **Nothing here proves the general dominance split.**

**⚠ σ-STRENGTHENED PREDICATE.** `A1Cell` (H.93) carries the σ-label field (W-12's r4 clause) and
the closure proved here is closure for that *strengthened* predicate, which discharges
`EFF.GENIND.30`'s OPEN-CALL 3 **for the Lean development only** — the corpus keeps the open call
(nothing here edits a frozen note).

**REPAIR RECORD [A-H.1/D5].** The committed SIGNATURE left `prod` and `deltaSubst` BODYLESS
(`def … : A1Cell _` with no `where`, an elaboration failure).  `prod`'s body below is the PROOF
field's, verbatim in content.  `deltaSubst`'s body is the stage-0e gate's STUB-SIDE
DETERMINATION, **adjudicated and adopted** into the blueprint: `offset`, `stride`, `coeff`, `σ`
are kept and the VISIBILITY form is transported by the same substitution
(`visCoeff := ![v 0 + v 1, v 1]`, `visConst := visConst + visCoeff 1`).  This is not a free
choice — under kept offsets the signed `deltaSubst_exp` FORCES `expConst := expConst + expCoeff 1`
(the committed "`expConst + expCoeff 1 * (offset-shift + 1)`" left "offset-shift" undefined; it
resolves to `0`), and the visibility transport by the same affine map is the unique choice making
the vis form track the substituted coordinates.

DEPENDS: H.93 (`A1Cell`, `A1Cell.exp`, `A1Family`) · landed `FactorizationType.degree_mk_add`,
`Multiset.sum_add`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-! ## Clause (i) — products -/

/-- **NODE H.94 (i).** The product of two cells: the parameter boxes concatenate (`Fin.append` on
offsets, strides, and both affine forms' coefficients), the constants and the σ-multisets add, and
the `q`-independent coefficients multiply. -/
def A1Cell.prod {r₁ r₂ : ℕ} (C : A1Cell r₁) (D : A1Cell r₂) : A1Cell (r₁ + r₂) where
  offset := Fin.append C.offset D.offset
  stride := Fin.append C.stride D.stride
  stride_pos := by
    refine Fin.addCases (fun k => ?_) (fun k => ?_)
    · simpa [Fin.append_left] using C.stride_pos k
    · simpa [Fin.append_right] using D.stride_pos k
  expCoeff := Fin.append C.expCoeff D.expCoeff
  expCoeff_pos := by
    refine Fin.addCases (fun k => ?_) (fun k => ?_)
    · simpa [Fin.append_left] using C.expCoeff_pos k
    · simpa [Fin.append_right] using D.expCoeff_pos k
  expConst := C.expConst + D.expConst
  visCoeff := Fin.append C.visCoeff D.visCoeff
  visConst := C.visConst + D.visConst
  coeff := C.coeff * D.coeff
  σ := ⟨C.σ.data + D.σ.data⟩

/-- **NODE H.94 (i), the exponent.** The product cell's exponent at a parameter point is the sum
of the two factors' exponents at the point's two blocks. -/
theorem A1Cell.prod_exp {r₁ r₂ : ℕ} (C : A1Cell r₁) (D : A1Cell r₂) (p : Fin (r₁ + r₂) → ℕ) :
    (C.prod D).exp p = C.exp (fun i => p (Fin.castAdd r₂ i)) + D.exp (fun j => p (Fin.natAdd r₁ j)) := by
  simp only [A1Cell.exp, A1Cell.prod, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  ring

/-- **NODE H.94 (i), the σ-label.** The product cell's σ-degree is the sum of the two factors'
σ-degrees — the landed `FactorizationType.degree_mk_add`, i.e. the σ-strengthened half of the
closure claim. -/
theorem A1Cell.prod_σ_degree {r₁ r₂ : ℕ} (C : A1Cell r₁) (D : A1Cell r₂) :
    (C.prod D).σ.degree = C.σ.degree + D.σ.degree := by
  simpa [A1Cell.prod] using FactorizationType.degree_mk_add C.σ D.σ

/-! ## Clause (iii) — the `δ`-substitution

Clause (ii) — closure under finite disjoint unions — is definitional: `A1Family r` is
`List (A1Cell r)` (H.93), so `++` is the union and the union's cells are the concatenation.
-/

/-- **NODE H.94 (iii).** The `δ`-substitution `w₂ = w₁ + 1 + δ` of `W-12` §S3.4's 2SIDED instance:
the parameter box, the coefficient, and the σ-label are kept; both affine forms are transported by
the substitution (coefficients `(a₀ + a₁, a₁)`, constant shifted by `a₁`). -/
def A1Cell.deltaSubst (C : A1Cell 2) : A1Cell 2 where
  offset := C.offset
  stride := C.stride
  stride_pos := C.stride_pos
  expCoeff := ![C.expCoeff 0 + C.expCoeff 1, C.expCoeff 1]
  expCoeff_pos := by
    have h0 := C.expCoeff_pos 0
    have h1 := C.expCoeff_pos 1
    intro i
    fin_cases i
    · show 0 < C.expCoeff 0 + C.expCoeff 1
      omega
    · show 0 < C.expCoeff 1
      omega
  expConst := C.expConst + C.expCoeff 1
  visCoeff := ![C.visCoeff 0 + C.visCoeff 1, C.visCoeff 1]
  visConst := C.visConst + C.visCoeff 1
  coeff := C.coeff
  σ := C.σ

/-- **NODE H.94 (iii), the signed statement.** The transported exponent read at `(w, δ)` is the
original exponent read at the substituted point `(w, w + 1 + δ)`.  This is what forces
`expConst := expConst + expCoeff 1` in `deltaSubst`'s body (A-H.1/D5). -/
theorem A1Cell.deltaSubst_exp (C : A1Cell 2) (w δ : ℕ) :
    (C.deltaSubst).exp ![w, δ] = C.exp ![w, w + 1 + δ] := by
  simp only [A1Cell.exp, A1Cell.deltaSubst, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.A1Cell.prod
#print axioms Uniformity.Density.Induction.A1Cell.prod_exp
#print axioms Uniformity.Density.Induction.A1Cell.prod_σ_degree
#print axioms Uniformity.Density.Induction.A1Cell.deltaSubst
#print axioms Uniformity.Density.Induction.A1Cell.deltaSubst_exp

end AxCheck
