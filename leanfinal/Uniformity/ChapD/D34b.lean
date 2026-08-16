/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D34a

/-!
# Uniformity.ChapD.D34b — the w-twist transports irreducibility, separability and roots

**Chapter D, NODE D.34** [def+lemma] [fresh], micro-node **D.34b**
(`blueprint/CHAP-D_gauge_tchain.md` §5; amendments A-1, A-D.1 govern). ENV-D3. The second
third of the **SPLIT MANDATED → 3** transport package of `wtwist` (D.34a):

* `wtwist_irreducible` — `Irreducible (wtwist w P) ↔ Irreducible P`.
* `wtwist_separable` — `(wtwist w P).Separable ↔ P.Separable`.
* `wtwist_eval` — the root map: `(wtwist w P).eval (w·s) = w^{deg P}·P.eval s`, so `s` is a root
  of `P` iff `w·s` is a root of `wtwist w P` (`w^{deg P}` is a unit).

## The route (the blueprint's own, executed)

The node's ⚠ route note says: `P ↦ P.comp (C w⁻¹ * X)` is substitution by a unit, hence a
`K`-algebra automorphism, and irreducibility/separability should be transported along it rather
than by hand induction. That is what happens here, in two private steps:

* `twistEquiv w : K[X] ≃ₐ[K] K[X]` — mathlib's `Polynomial.algEquivOfCompEqX` at the mutually
  inverse pair `(C w⁻¹ * X, C w * X)`. Irreducibility then transports by
  `MulEquiv.irreducible_iff`, and the leftover scalar `w^{deg P}` is stripped by
  `irreducible_isUnit_mul`.
* separability is `IsCoprime P (derivative P)` by definition, and the two facts that move it are
  `IsCoprime.map` along the substitution and `derivative_comp` (the chain rule contributes the
  extra factor `C w⁻¹`, a unit, removed by `isCoprime_mul_unit_left_right`). The scalar
  `w^{deg P}` is stripped by `Associated.separable_iff`.

Both `iff`s are proved in the strong direction as well as the weak one; nothing here needs `P`
monic, and the two `hP : P.Monic` binders of the frozen signatures are therefore inert (the
unused-variable linter is silenced at exactly those two declarations, with this as the reason).
The signatures are NOT weakened by dropping them — they are signed, and they stay.

## Faithfulness

The corpus sentence being transcribed is a preservation LIST ("transports factorizations
bijectively and preserves degrees, multiplicities, irreducibility, and a nonzero constant term",
`EFF.T1.15`; "separability + the monic factor correspondence `r(Z) = δ^m r̂(Z/δ)` and root map
`ŝ ↦ δŝ`", `EFF.T3.18`; "Unit substitution preserves monicity, degree, irreducibility, nonzero
constant term, and irreducible-factor degrees and multiplicities", `EFF.T5.08`). Its items are
distributed over the three micro-nodes: degrees/monicity/constant term at D.34a, irreducibility
/separability/roots here, factor multiplicities (via multiplicativity on monics) at D.34c.

*One recast, flagged for the cross-read.* The corpus's root clause is the assignment
`ŝ ↦ δŝ` on root SETS; the Lean form is the evaluation identity
`(wtwist w P).eval (w·s) = w^{deg P}·P.eval s`, from which the root-set bijection is immediate
(both directions, since `w` is a unit) but is not itself a signed declaration of this node — the
blueprint signs exactly the evaluation identity (`EFF.T3.18`'s "root map").

**DEPENDS.** D.34a (`wtwist`); mathlib `Polynomial.algEquivOfCompEqX`, `MulEquiv.irreducible_iff`,
`Polynomial.separable_def`, `Polynomial.derivative_comp`, `IsCoprime.map`,
`Associated.separable_iff`.

**PROOF.** As described above; the two `iff`s are `rw`-chains through the private
`twistEquiv`/`separable_comp_iff` pair, and `wtwist_eval` is `eval_smul` + `eval_comp` +
`w⁻¹·(w·s) = s`.

SOURCE: `EFF.T1.15`, `EFF.T3.18` (`(T3-ROUTE)` — D.41 is this node's two-section instance),
`EFF.T5.05`, `EFF.T5.08`.

**TEETH.** T3 §8.3(2) (HETOW clause (d), the separability/factor/root routing) → Lean theorem,
here. **Honesty fence (D-H4(3)), repeated at the node's instruction:** "Turning factor data into
a p-adic splitting type still requires the surrounding tower theorem" (`EFF.T5.08`) — unnamed in
both T1 and T3, routed to chapter I / the 0d trust boundary (D.64). This file transports factor
data and asserts nothing about splitting types.

ENVIRONMENT: ENV-D3.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

open Polynomial

section Twist

variable {K : Type*} [Field K]

/-- Substitution by the unit `w⁻¹` as a `K`-algebra automorphism of `K[X]` — the blueprint's
route note ("`P ↦ P.comp (C w⁻¹ * X)` is the `AlgEquiv` shape"), realised by mathlib's
`Polynomial.algEquivOfCompEqX` at the mutually inverse pair `(C w⁻¹ * X, C w * X)`. -/
private noncomputable def twistEquiv (w : Kˣ) : Polynomial K ≃ₐ[K] Polynomial K :=
  Polynomial.algEquivOfCompEqX
    (Polynomial.C ((w⁻¹ : Kˣ) : K) * Polynomial.X)
    (Polynomial.C ((w : K)) * Polynomial.X)
    (by
      rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp, ← mul_assoc,
        ← Polynomial.C_mul, Units.inv_mul, Polynomial.C_1, one_mul])
    (by
      rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp, ← mul_assoc,
        ← Polynomial.C_mul, Units.mul_inv, Polynomial.C_1, one_mul])

private theorem twistEquiv_apply (w : Kˣ) (P : Polynomial K) :
    twistEquiv w P = P.comp (Polynomial.C ((w⁻¹ : Kˣ) : K) * Polynomial.X) := by
  simp [twistEquiv, Polynomial.comp_eq_aeval]

/-- The round trip: substituting `w⁻¹` and then `w` is the identity. -/
private theorem comp_comp_of_mul_eq_one {a b : K} (hab : a * b = 1) (P : Polynomial K) :
    (P.comp (Polynomial.C a * Polynomial.X)).comp (Polynomial.C b * Polynomial.X) = P := by
  have h : (Polynomial.C a * Polynomial.X).comp (Polynomial.C b * Polynomial.X)
      = Polynomial.X := by
    rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp, ← mul_assoc,
      ← Polynomial.C_mul, hab, Polynomial.C_1, one_mul]
  rw [Polynomial.comp_assoc, h, Polynomial.comp_X]

/-- Coprimality is transported by substitution (a ring hom suffices in this direction). -/
private theorem isCoprime_comp (a : K) {p q : Polynomial K} (h : IsCoprime p q) :
    IsCoprime (p.comp (Polynomial.C a * Polynomial.X))
      (q.comp (Polynomial.C a * Polynomial.X)) := by
  have h' := h.map
    (Polynomial.aeval (Polynomial.C a * Polynomial.X) : Polynomial K →ₐ[K] Polynomial K).toRingHom
  simpa [Polynomial.comp_eq_aeval] using h'

/-- Separability under substitution by the unit `w⁻¹`, both directions. -/
private theorem separable_comp_iff (w : Kˣ) (P : Polynomial K) :
    (P.comp (Polynomial.C ((w⁻¹ : Kˣ) : K) * Polynomial.X)).Separable ↔ P.Separable := by
  have hu : IsUnit (Polynomial.C ((w⁻¹ : Kˣ) : K)) := Polynomial.isUnit_C.mpr (Units.isUnit _)
  have hd : Polynomial.derivative (Polynomial.C ((w⁻¹ : Kˣ) : K) * Polynomial.X)
      = Polynomial.C ((w⁻¹ : Kˣ) : K) := by simp
  rw [Polynomial.separable_def, Polynomial.separable_def, Polynomial.derivative_comp, hd,
    isCoprime_mul_unit_left_right hu]
  refine ⟨fun h => ?_, fun h => isCoprime_comp _ h⟩
  have h2 := isCoprime_comp ((w : K)) h
  rwa [comp_comp_of_mul_eq_one (Units.inv_mul w) P,
    comp_comp_of_mul_eq_one (Units.inv_mul w) (Polynomial.derivative P)] at h2

-- `hP` is signed but inert: substitution by a unit transports irreducibility for every `P`.
set_option linter.unusedVariables false in
/-- **D.34b** Irreducibility transport (`EFF.T1.15`, `EFF.T5.08`).  The `hP : P.Monic` binder is
signed but inert: substitution by a unit transports irreducibility for every `P`. -/
theorem wtwist_irreducible (w : Kˣ) {P : Polynomial K} (hP : P.Monic) :
    Irreducible (wtwist w P) ↔ Irreducible P := by
  have hc : IsUnit (Polynomial.C ((w : K) ^ P.natDegree)) :=
    Polynomial.isUnit_C.mpr ((Units.isUnit w).pow _)
  rw [wtwist, Polynomial.smul_eq_C_mul, irreducible_isUnit_mul hc, ← twistEquiv_apply w P]
  exact MulEquiv.irreducible_iff (twistEquiv w)

-- `hP` is signed but inert here too.
set_option linter.unusedVariables false in
/-- **D.34b** Separability transport (`EFF.T3.18`'s `(T3-ROUTE)`).  As with irreducibility, the
signed `hP : P.Monic` binder is inert. -/
theorem wtwist_separable (w : Kˣ) {P : Polynomial K} (hP : P.Monic) :
    (wtwist w P).Separable ↔ P.Separable := by
  have hc : IsUnit (Polynomial.C ((w : K) ^ P.natDegree)) :=
    Polynomial.isUnit_C.mpr ((Units.isUnit w).pow _)
  rw [wtwist, Polynomial.smul_eq_C_mul,
    ← (associated_unit_mul_right (P.comp (Polynomial.C ((w⁻¹ : Kˣ) : K) * Polynomial.X))
        (Polynomial.C ((w : K) ^ P.natDegree)) hc).separable_iff]
  exact separable_comp_iff w P

/-- **D.34b** The root map is `s ↦ w·s` (`EFF.T3.18`: "root map `ŝ ↦ δŝ`"), in its evaluation
form.  Since `w^{deg P}` is a unit, `s` is a root of `P` iff `w·s` is a root of `wtwist w P`. -/
theorem wtwist_eval (w : Kˣ) (P : Polynomial K) (s : K) :
    (wtwist w P).eval ((w : K) * s) = (w : K) ^ P.natDegree * P.eval s := by
  have hs : (Polynomial.C ((w⁻¹ : Kˣ) : K) * Polynomial.X).eval ((w : K) * s) = s := by
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, ← mul_assoc,
      Units.inv_mul, one_mul]
  rw [wtwist, Polynomial.eval_smul, smul_eq_mul, Polynomial.eval_comp, hs]

end Twist

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.wtwist_irreducible
#print axioms Uniformity.Density.Gauge.wtwist_separable
#print axioms Uniformity.Density.Gauge.wtwist_eval

end AxCheck
