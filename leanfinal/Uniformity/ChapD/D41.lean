/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D34b
import Uniformity.ChapD.D40

/-!
# Uniformity.ChapD.D41 — `t3_route`, `(T3-ROUTE)`: polynomial routing along the comparison

**Chapter D, NODE D.41** [lemma] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §6, T3's comparison
layer; amendments A-1, A-D.1 govern — the node carries no `[repaired: …]` / `[re-signed: …]`
tag, so the composed text plus A-D.1's `D-D11` rider is its signed text). ENV-D3 (the
residue-field arena: a bare `[Field K]`, plus one field extension `L/K` for the rationality
clause). Three signed declarations.

*`(T3-ROUTE)`.* Multiplication by the nonzero scalar `chiK H₀` and the substitution `Z ↦ Z/δ`
preserve separability and the multiset of irreducible-factor degrees and multiplicities; a monic
factor `r̂` of degree `m` of `RpolyHat` corresponds to the monic factor

```
r := wtwist δ r̂ = δ^m · r̂(Z/δ)
```

of `Rpoly` (up to the global scalar), with root correspondence `ŝ ↦ δ·ŝ`; and *"Rationality over
any field containing `K` is preserved"* — the correspondence commutes with
`Polynomial.map (algebraMap K L)` for any field extension `L/K`.

**This node is D.34's transport package INSTANTIATED at `w := δ` and re-exported under T3's
name.** The mathematical content lives in D.34 (`Uniformity.ChapD.D34a`/`D34b`, landed and
green: `wtwist`, `wtwist_monic`, `wtwist_irreducible`, `wtwist_separable`, `wtwist_eval`); the
three proofs here are one line each. The point is the T3-citable name and the rationality
clause — the row D.43's absorption-boundary table calls *"clause (d), separability/factor/root
routing | fully supplied by D.41 (`(T3-ROUTE)`)"*.

## ⚠ A-D.1 / D-D11 — clause 1 of `t3_route` is `rfl` and carries NO content

Transcribed: *"With the `Kˣ`-inverse reading signed at D.34 (`Polynomial.C ((δ⁻¹ : Kˣ) : K)`),
`(δ : K)^{deg} • r̂.comp (C δ⁻¹ * X)` **IS** `wtwist δ r̂` by definition, so the first conjunct of
`t3_route` is definitional and the informative content of this node is the **separability iff**
plus the two siblings (`t3_route_roots`, `t3_route_map`). The clause is signed as given — T3
displays it, and stating the identity under T3's own name is the point of the re-export — but a
fleet agent must not budget proof effort for it, and a reviewer must not read it as a theorem."*

Accordingly the proof term of clause 1 in this file is the literal `rfl`, which is the honest
display of that status: nothing is hidden behind a tactic block.

## Faithfulness

Three recasts against `EFF.T3.18`, flagged for the chapter cross-read (no new definition is made
here — `wtwist` is D.34's, already at the trust boundary):

* *the `hP : rhat.Monic` binders are signed but inert in two of the three statements.* D.34
  records the same fact for `wtwist_irreducible`/`wtwist_separable` ("substitution by a unit
  transports irreducibility for every `P`"), and the root clause needs no hypothesis at all. The
  binders are kept because the SIGNATURE is landed byte-for-byte and because the corpus's `r̂` is
  monic at every consumption site; `set_option linter.unusedVariables false in` marks each such
  binder rather than silently deleting it. In `t3_route_map` the hypothesis **is** used — it is
  what makes `natDegree` survive the base change.
* *"preserves the multiset of irreducible-factor degrees and multiplicities" is carried by
  D.34, not restated here.* `wtwist_irreducible` (D.34b) plus `wtwist_monic`'s degree clause
  (D.34a) are the factorwise statement; a chapter-D restatement in multiset form would be a
  second name for a landed fact. The factor correspondence `r := wtwist δ r̂` is therefore
  *notation* in this node's statements, exactly as in the corpus display.
* *the root correspondence is stated in evaluation form.* `ŝ ↦ δŝ` becomes
  `(wtwist δ r̂).eval (δ·s) = δ^{deg r̂}·r̂.eval s`; since `δ^{deg}` is a unit this says `s` is a
  root of `r̂` iff `δ·s` is a root of the twist, which is the corpus's sentence. Choosing the
  equation over an `IsRoot ↔ IsRoot` shape keeps the multiplicity information visible.
* *the rationality clause names `Units.map (algebraMap K L).toMonoidHom δ`.* The twist's scalar
  is a `Kˣ`; over `L` the corresponding scalar is the image unit, not merely the image element.
  That is the only way the statement typechecks with `wtwist`'s `Kˣ` argument, and it is
  faithful: `L/K` is a field extension, so `algebraMap` carries units to units.

**DEPENDS.** D.34 (the transport package — the mathematical content lives there; imported as
`Uniformity.ChapD.D34b`, which re-exports `D34a`), D.40 (the consumer shape — imported so the
blueprint's DAG edge is a real Lean import edge, though **no name of D.40 occurs in any of the
three statements**: the routing is applied to `compData_cmp_poly`'s comparison at the consumer
site, which is D.43's table row (d), not here).

**PROOF.** Each clause is D.34's corresponding clause at `w := δ`; the map-commutation leg:
`wtwist` commutes with `Polynomial.map` of a ring hom sending `δ ↦ algebraMap δ`
(coefficientwise) — `Polynomial.map_mul`/`map_C`/`map_comp`/`map_X` after
`Polynomial.smul_eq_C_mul`, with `Monic.natDegree_map` for the exponent and `Units.coe_map_inv`
for the substituted scalar.

SOURCE: `EFF.T3.18` (the boxed `(T3-ROUTE)`: `r(Z) = δ^m r̂(Z/δ)`, `ŝ ↦ δŝ`, the rationality
sentence; derivation "Because `δ ∈ K^×`, substitution by `Z/δ` is a `K`-algebra automorphism").

**TEETH.** T3 §8.2, §8.3(2), honesty item 10 → **Lean theorem**; the HETOW clause-(d) supply
(D.43's table row).

ENVIRONMENT: ENV-D3.

## Status

Sorry-free, axiom-free (Lean core only): all three are PROVED here, not the leanspec `axiom`
stubs.
-/

namespace Uniformity.Density.Gauge

-- The `h : rhat.Monic` binder is signed but inert: `wtwist_separable` transports separability
-- for every `rhat`, and clause 1 is definitional (A-D.1 / D-D11).
set_option linter.unusedVariables false in
/-- **D.41** `(T3-ROUTE)`: polynomial routing along the comparison — D.34's package instantiated
at `w := δ` and re-exported under T3's name (`EFF.T3.18`).

⚠ **Clause 1 is `rfl`** (A-D.1 / D-D11): with the `Kˣ`-inverse reading signed at D.34,
`(δ : K)^{deg} • r̂.comp (C δ⁻¹ * X)` IS `wtwist δ r̂` by definition. The informative content of
the node is the separability iff plus the two siblings below. -/
theorem t3_route {K : Type*} [Field K] (δ : Kˣ) {rhat : Polynomial K} (h : rhat.Monic) :
    wtwist δ rhat
      = (δ : K) ^ rhat.natDegree • rhat.comp (Polynomial.C ((δ⁻¹ : Kˣ) : K) * Polynomial.X)
    ∧ ((wtwist δ rhat).Separable ↔ rhat.Separable) :=
  ⟨rfl, wtwist_separable δ h⟩

-- Inert signed binder again: the root correspondence needs no monicity.
set_option linter.unusedVariables false in
/-- **D.41** `(T3-ROUTE)` root correspondence `ŝ ↦ δŝ` (`EFF.T3.18`), in evaluation form: since
`δ^{deg r̂}` is a unit, `s` is a root of `r̂` iff `δ·s` is a root of the twist. -/
theorem t3_route_roots {K : Type*} [Field K] (δ : Kˣ) {rhat : Polynomial K} (h : rhat.Monic)
    (s : K) :
    (wtwist δ rhat).eval ((δ : K) * s) = (δ : K) ^ rhat.natDegree * rhat.eval s :=
  wtwist_eval δ rhat s

/-- **D.41** `(T3-ROUTE)` rationality: the correspondence commutes with
`Polynomial.map (algebraMap K L)` for any field extension `L/K` (`EFF.T3.18`, "Rationality over
any field containing `K` is preserved"). The scalar travels as the image UNIT
`Units.map (algebraMap K L) δ`, and monicity of `rhat` is what keeps the exponent `natDegree`
fixed under the base change — this is the one place the signed hypothesis does work. -/
theorem t3_route_map {K L : Type*} [Field K] [Field L] [Algebra K L] (δ : Kˣ)
    {rhat : Polynomial K} (h : rhat.Monic) :
    (wtwist δ rhat).map (algebraMap K L)
      = wtwist (Units.map (algebraMap K L : K →+* L).toMonoidHom δ)
          (rhat.map (algebraMap K L)) := by
  have hdeg : (rhat.map (algebraMap K L)).natDegree = rhat.natDegree := h.natDegree_map _
  simp only [wtwist, Polynomial.smul_eq_C_mul, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_comp, Polynomial.map_X, Polynomial.map_pow, hdeg, map_pow,
    Units.coe_map_inv, Units.coe_map]
  rfl

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.t3_route
#print axioms Uniformity.Density.Gauge.t3_route_roots
#print axioms Uniformity.Density.Gauge.t3_route_map

end AxCheck
