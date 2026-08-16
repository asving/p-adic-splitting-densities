/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D34a

/-!
# Uniformity.ChapD.D35 — `(WF-psi)`: the twist coefficients `c_t ↦ c_t·w^{f−t}`

**Chapter D, NODE D.35** [lemma] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §5, the read
bundle and the B-law; amendments A-1, A-D.1 govern — A-1 is what put the twist/`(WF-psi)` pair
in §5 rather than §8, because T1's three-reads and T3's routing consume them before T5 does).
ENV-D3 (the residue-field arena: a bare `[Field K]`, `open Polynomial`; nothing here counts).
One public declaration.

*`(WF-psi)`: the twist coefficients.* For a unit `w : Kˣ` and a monic residual
`ψ = y^f − Σ_{t<f} c_t y^t`, the w-twist of D.34 acts on the coefficient vector by a single
graded rescaling:

```
wtwist w ψ  =  y^f − Σ_{t<f} c_t·w^{f−t}·y^t .
```

This is T5's boxed computation, and it is the polynomial into which D.33's coefficient identity
assembles: the B-law residual `y^f − Σ u(β_t)·c_t^{coh-normalized} y^t` IS `wtwist w ψ` under the
multiplicative prescription. Downstream, D.58 (`(WF-realized)`) is exactly "D.33's slotwise
cancellation, then this lemma".

## Faithfulness

No definition is introduced here, so the trust boundary is thin: the only judgement is that the
Lean display says what the corpus display says. Three recasts, flagged for the chapter
cross-read:

* *`f − t` is `Nat` subtraction, and the truncation never bites.* The sum is indexed by
  `t : Fin f`, so `(t : ℕ) < f` on every summand and `f − (t : ℕ) ≥ 1`; the exponent is the
  corpus's `f − t` on the nose. (The signature is landed byte-for-byte from the blueprint, which
  is where the `Fin f` indexing comes from.)
* *the `f = 0` edge is true, not vacuous.* At `f = 0` both sides read `X^0 − 0 = 1` (the empty
  sum), and `wtwist w 1 = w^0 • 1 = 1`. Nothing is asserted about a degree-zero "residual"
  beyond that identity.
* *the `w^{natDegree}` scalar of `wtwist` is discharged, not assumed.* `wtwist` renormalizes by
  `w ^ P.natDegree` (D.34a), so the proof must know `natDegree ψ = f`. That is the private
  helper `psi_natDegree` below — no hypothesis `hψ : ψ.Monic` appears in the signature, because
  the polynomial is given by its explicit shape and the degree is computed from it.

**DEPENDS.** D.34 (`wtwist`, imported as `Uniformity.ChapD.D34a` — the definition micro-node of
the SPLIT MANDATED → 3 package). Nothing else in chapter D; mathlib supplies
`Polynomial.degree_lt_iff_coeff_zero`, `Polynomial.degree_sub_eq_left_of_degree_lt`,
`Polynomial.sum_comp`.

**PROOF.** The blueprint's recipe, executed. (1) `psiTail_degree_lt`: every coefficient of
`Σ_{t<f} C (c t)·X^t` in degree `≥ f` vanishes, so its `degree` is `< f`; (2) `psi_natDegree`:
hence `degree (X^f − Σ …) = degree (X^f) = f`, giving the `natDegree` that `wtwist`'s scalar
consumes; (3) the substitution itself — `Polynomial.sub_comp`/`sum_comp`/`mul_comp` push
`comp (C w⁻¹ * X)` through, and the two scalar identities are
`w^f·(w⁻¹)^f = 1` (the leading term) and `w^f·(w⁻¹)^t = w^{f−t}` for `t ≤ f`
(`wpow_sub`), i.e. the corpus's "`w^f((y/w)^f − Σ c_t (y/w)^t) = y^f − Σ c_t w^{f−t} y^t`".
The `w⁻¹` here is A-D.1's signed `Kˣ`-inverse reading of D-D11, inherited from `wtwist`'s body.

SOURCE: `EFF.T5.06` (the boxed `(WF-psi)` together with its `[COMPUTATION]` derivation; the r4
census's confirmation that T1's `(C3-three-reads)` boxes the same display).

**TEETH.** T5 §7 Pass 1(1)/(6) → **Lean theorem** (this node). The numeric leg is gate
**D.65 leg 4**, which evaluates a `(WF-psi)` instance at the F4-JOINT frame (`f = 2`, `w = ω`,
`(c₁,c₀) = (1,ω)`, twist exponents `(1,0)`) — *[A-D.1: the blueprint's original "gate D.72" was
a stale ID, and the instance is NOT executed at FRAME-C]*. Nothing is scored in this file; the
gate node owns the numerals.

ENVIRONMENT: ENV-D3.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

open Polynomial

section Psi

variable {K : Type*} [Field K]

/-- The tail `Σ_{t<f} c_t y^t` of a residual has degree `< f`: each summand sits in degree
`(t : ℕ) < f`, so every coefficient in degree `≥ f` vanishes. -/
private theorem psiTail_degree_lt (f : ℕ) (c : Fin f → K) :
    (∑ t : Fin f, Polynomial.C (c t) * Polynomial.X ^ (t : ℕ)).degree < (f : WithBot ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun t _ => ?_
  have ht : (t : ℕ) < f := t.isLt
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]

/-- The residual `y^f − Σ_{t<f} c_t y^t` has `natDegree` exactly `f` — the degree that
`wtwist`'s renormalizing scalar `w ^ natDegree` reads off. -/
private theorem psi_natDegree (f : ℕ) (c : Fin f → K) :
    (Polynomial.X ^ f - ∑ t : Fin f, Polynomial.C (c t) * Polynomial.X ^ (t : ℕ)).natDegree
      = f := by
  refine Polynomial.natDegree_eq_of_degree_eq_some ?_
  rw [Polynomial.degree_sub_eq_left_of_degree_lt
        (by rw [Polynomial.degree_X_pow]; exact psiTail_degree_lt f c),
      Polynomial.degree_X_pow]

/-- The graded rescaling that the substitution `y ↦ y/w` produces: `w^f·(w⁻¹)^t = w^{f−t}`
whenever `t ≤ f`, so the `Nat`-truncated exponent is the honest one. -/
private theorem wpow_sub (w : Kˣ) {f t : ℕ} (ht : t ≤ f) :
    (w : K) ^ f * (((w⁻¹ : Kˣ) : K)) ^ t = (w : K) ^ (f - t) := by
  have hw : (w : K) ≠ 0 := w.ne_zero
  rw [Units.val_inv_eq_inv_val, inv_pow, ← div_eq_mul_inv,
    div_eq_iff (pow_ne_zero _ hw), ← pow_add]
  congr 1
  omega

/-- **D.35** `(WF-psi)`: the twist coefficients (`EFF.T5.06`).  Twisting the monic residual
`ψ = y^f − Σ_{t<f} c_t y^t` by the unit `w` rescales its coefficient vector gradedly,
`c_t ↦ c_t·w^{f−t}`:

```
wtwist w (y^f − Σ_{t<f} c_t y^t) = y^f − Σ_{t<f} (c_t·w^{f−t}) y^t .
```

This is the polynomial into which D.33's coefficient identity assembles, and the target of
D.58's slotwise cancellation. -/
theorem wtwist_psi (w : Kˣ) (f : ℕ) (c : Fin f → K) :
    wtwist w (Polynomial.X ^ f - ∑ t : Fin f, Polynomial.C (c t) * Polynomial.X ^ (t : ℕ))
      = Polynomial.X ^ f
        - ∑ t : Fin f, Polynomial.C (c t * (w : K) ^ (f - (t : ℕ)))
            * Polynomial.X ^ (t : ℕ) := by
  rw [wtwist, psi_natDegree, Polynomial.sub_comp, Polynomial.X_pow_comp, smul_sub]
  congr 1
  · -- the leading term: `w^f·(w⁻¹)^f = 1`, so `y^f` comes back unchanged
    rw [mul_pow, ← Polynomial.C_pow, Polynomial.smul_eq_C_mul, ← mul_assoc, ← Polynomial.C_mul,
      wpow_sub w (le_refl f), Nat.sub_self, pow_zero, Polynomial.C_1, one_mul]
  · -- the tail: slotwise, `w^f·c_t·(w⁻¹)^t = c_t·w^{f−t}`
    rw [Polynomial.sum_comp, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have ht : (t : ℕ) ≤ f := le_of_lt t.isLt
    rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_pow_comp, mul_pow,
      ← Polynomial.C_pow, Polynomial.smul_eq_C_mul, ← mul_assoc, ← Polynomial.C_mul,
      ← mul_assoc, ← Polynomial.C_mul]
    congr 2
    rw [mul_comm ((w : K) ^ f) (c t), mul_assoc, wpow_sub w ht]

end Psi

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.wtwist_psi

end AxCheck
