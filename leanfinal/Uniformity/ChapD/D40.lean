/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D39

/-!
# Uniformity.ChapD.D40 — `(T3-CMP)`: the assembled comparison `R(Z) = χ(H₀)·R̂(Z/δ)`

**Chapter D, NODE D.40** [theorem] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §6, the telescope
port (T3); amendments A-1, A-D.1, A-D.2 govern — this node's SIGNATURE was **RE-SIGNED at
A-D.1/D-D3**: its schematic projections and the `(chiK-of-H₀-term)` placeholder are now SPELLED
against D.39's re-signed packaging). ENV-D2 + ENV-D3. Two signed declarations, the blueprint's own
SPLIT (coefficient leg / polynomial leg); the leanspec stub signs both as `axiom`s and both are
PROVED here.

*`(T3-CMP)`: the assembled comparison* (`EFF.T3.17`). With D.39's two-section data
`(ρ, ρ̂, δ) = compData A N̂ hN̂ H₀ q D Acoef hA`:

* **coefficient leg** `compData_cmp`: `ρ_t = ρ̂_t · χ(H₀) · δ^{−t}` for every slot `t`;
* **polynomial leg** `compData_cmp_poly`: `R(Z) = χ(H₀)·R̂(Z/δ)`, where `R` and `R̂` are the
  `∑_t C ρ_t · X^t` shapes formed HERE (D.39 gives them no public name, by design) and `Z ↦ Z/δ`
  is `Polynomial.comp` with `C δ⁻¹ * X`.

## The corpus's two-line computation, and where each factor comes from

`EFF.T3.17`: `ρ_t/ρ̂_t = res((N(q)/N̂(q))^t · (N̂(H₀)/N(H₀))) = χ(q)^{−t}·χ(H₀)`. Landed, that is
one application of `A.res` to a single kernel element: the three residues are pushed together by
`← map_mul` / `← map_pow` / `← map_inv` (`A.res` is a `MonoidHom` into `Kˣ`, and `MonoidHom.ker
A.v` is a group, so all three are available), and the resulting equation is a `Subtype.ext` of a
CommGroup identity in `G` in which `N̂(H₀)⁻¹·N̂(H₀)` and `N̂(q)^t·(N̂(q)^t)⁻¹` cancel and the
hatted section disappears entirely. The `A_t` coefficients cancel unchanged — the comparison is
insensitive to the descent data, which is exactly why it can be applied slotwise at any frame.
"Summing over `t` proves its polynomial identity": the polynomial leg is `Polynomial.sum_comp` to
distribute `comp` over the sum, `Finset.mul_sum` to distribute the scalar, and then the
coefficient leg slotwise under `Finset.sum_congr`.

⚠ **`χ` is NOT a character** (D.12's fence, with its executed witness): nothing here asserts
`χ(a)·χ(b) = χ(a+b)`, and the two values `χ(q) = δ` and `χ(H₀)` are genuinely independent inputs
— which is why D.39 packages only `δ` and this node calls `A.chiK Nhat hNhat H₀` for the other.
`EFF.T3.13`'s asymmetric packaging is the reason the `χ(H₀)` factor appears as a free global
scalar rather than as a value of the same power law that produced `δ^{−t}`.

## The two spellings of `δ⁻¹` (the D-D11 reading, signed at D.34)

The coefficient leg divides by the FIELD inverse `((δ : K))⁻¹ ^ t`, while the polynomial leg
substitutes the `Kˣ`-inverse coerced to `K`, `((δ⁻¹ : Kˣ) : K)`. They are the same element
(`Units.val_inv_eq_inv_val`) and the difference is deliberate: the substitution scalar must be a
UNIT for `Z ↦ Z/δ` to be a `K`-algebra automorphism (D.41's routing clause reads it that way,
and D.34's `wtwist` is spelled with the `Kˣ`-inverse), whereas the coefficient display is the
corpus's own `δ^{−t}` in `K`. No `δ ≠ 0` hypothesis is needed anywhere: `δ : Kˣ` by construction.

DEPENDS: D.12 (`NormSection.chi`, reaching this file through D.39) · D.39 (`compData`,
`GaugeArena.chiK`), landed under `Uniformity.ChapD` · mathlib `Polynomial.sum_comp`,
`Polynomial.mul_comp`/`C_comp`/`pow_comp`/`X_comp`, `Finset.mul_sum`, `Finset.sum_congr`,
`Units.val_inv_eq_inv_val`, `map_mul`/`map_pow`/`map_inv`.

**PROOF.** Coefficient leg: prove the identity FIRST in `Kˣ` (where `ρ_t`, `ρ̂_t`, `χ(H₀)`, `δ`
all live), by collapsing the four residues into one with `← map_mul`/`← map_pow`/`← map_inv` and
closing the `G`-level goal by AC-normalization; then coerce to `K` with `push_cast` + `ring`.
Polynomial leg: `Polynomial.sum_comp`, `Finset.mul_sum`, `Finset.sum_congr`, the coefficient leg,
and `C`-arithmetic (`C_mul`, `C_pow`, `mul_pow`).

SOURCE: `EFF.T3.17` (the boxed `(T3-CMP)` and its `[VERBATIM]` derivation, both legs).

**TEETH.** T3 §8.2 (the port frames), §8.3(2) (the HETOW-4 clause-(c) supply), §8.4(1) (the
character mutant) → **Lean theorem** (this node); gate **D.67** checks the same two displays
numerically at FRAME-C, `ρ_t = 3·ρ̂_t·2^{−t}` and `R(Z) = 3·R̂(Z/2)` in `𝔽₅[Z]`. Nothing numeric
runs in this file: `K` is an abstract field here, and the FRAME-C instance is the gate's.

ENVIRONMENT: ENV-D2 + ENV-D3 (`{G : Type*} [CommGroup G]`, `{K : Type*} [Field K]` written inline
per the B.42 binder rule — this file has no `variable` block; the A-D.1/D-D7-class spelling riders
are inherited from D.39, so `hNhat`'s and `hA`'s binders carry their types and the exponent is
cast `(t : ℕ) * q`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

/-- **D.40 — `(T3-CMP)`, the coefficient leg** (`EFF.T3.17`): `ρ_t = ρ̂_t·χ(H₀)·δ^{−t}`.

The corpus's `ρ_t/ρ̂_t = res((N(q)/N̂(q))^t·(N̂(H₀)/N(H₀))) = χ(q)^{−t}·χ(H₀)`, slotwise.  The
descent coefficients `A_t` cancel unchanged, so the comparison does not see the descent data.

⚠ `χ` is NOT a character (D.12): `χ(H₀)` and `δ = χ(q)` are independent inputs, which is why
D.39 packages only `δ` and this statement calls `A.chiK Nhat hNhat H₀` for the other. -/
theorem compData_cmp {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : GaugeArena G K N) (Nhat : NormSection G)
    (hNhat : ∀ k : ℤ, A.v (Nhat.n k) = Multiplicative.ofAdd k)
    (H₀ q : ℤ) (D : ℕ) (Acoef : Fin (D + 1) → G)
    (hA : ∀ t : Fin (D + 1), A.v (Acoef t) = Multiplicative.ofAdd (H₀ - (t : ℕ) * q))
    (t : Fin (D + 1)) :
    (((compData A Nhat hNhat H₀ q D Acoef hA).1 t : Kˣ) : K)
      = (((compData A Nhat hNhat H₀ q D Acoef hA).2.1 t : Kˣ) : K)
        * ((A.chiK Nhat hNhat H₀ : Kˣ) : K)
        * ((((compData A Nhat hNhat H₀ q D Acoef hA).2.2 : Kˣ) : K))⁻¹ ^ (t : ℕ) := by
  -- The identity lives in `Kˣ`; the `K`-display is its coercion.
  have hunits : (compData A Nhat hNhat H₀ q D Acoef hA).1 t
      = (compData A Nhat hNhat H₀ q D Acoef hA).2.1 t * A.chiK Nhat hNhat H₀
        * ((compData A Nhat hNhat H₀ q D Acoef hA).2.2)⁻¹ ^ (t : ℕ) := by
    -- one `A.res` of one kernel element, per `EFF.T3.17`'s single display
    simp only [compData, GaugeArena.chiK, ← map_inv, ← map_pow, ← map_mul]
    refine congrArg A.res (Subtype.ext ?_)
    -- the `G`-level identity: `N̂(H₀)⁻¹·N̂(H₀)` and `N̂(q)^t·(N̂(q)^t)⁻¹` cancel, `A_t` survives
    simp only [NormSection.chi, Subgroup.coe_mul, InvMemClass.coe_inv, SubmonoidClass.coe_pow]
    simp [mul_pow, inv_pow, mul_comm, mul_assoc, mul_left_comm]
  rw [hunits]
  push_cast
  ring

/-- **D.40 — `(T3-CMP)`, the polynomial leg** (`EFF.T3.17`): `R(Z) = χ(H₀)·R̂(Z/δ)`.

"Summing over `t` proves its polynomial identity."  `R` and `R̂` are the `∑_t C ρ_t·X^t` shapes
formed HERE — D.39 deliberately gives them no public name — and `Z ↦ Z/δ` is `Polynomial.comp`
with `C ((δ⁻¹ : Kˣ) : K) * X`, the `Kˣ`-inverse spelling signed at D.34 (D-D11): the substitution
scalar is a UNIT, so the substitution is a `K`-algebra automorphism (D.41's routing reads it that
way) and no `δ ≠ 0` hypothesis is incurred. -/
theorem compData_cmp_poly {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : GaugeArena G K N) (Nhat : NormSection G)
    (hNhat : ∀ k : ℤ, A.v (Nhat.n k) = Multiplicative.ofAdd k)
    (H₀ q : ℤ) (D : ℕ) (Acoef : Fin (D + 1) → G)
    (hA : ∀ t : Fin (D + 1), A.v (Acoef t) = Multiplicative.ofAdd (H₀ - (t : ℕ) * q)) :
    (∑ t : Fin (D + 1),
        Polynomial.C ((((compData A Nhat hNhat H₀ q D Acoef hA).1 t : Kˣ) : K))
          * Polynomial.X ^ (t : ℕ))
      = Polynomial.C ((A.chiK Nhat hNhat H₀ : Kˣ) : K)
        * (∑ t : Fin (D + 1),
              Polynomial.C ((((compData A Nhat hNhat H₀ q D Acoef hA).2.1 t : Kˣ) : K))
                * Polynomial.X ^ (t : ℕ)).comp
            (Polynomial.C
                ((((compData A Nhat hNhat H₀ q D Acoef hA).2.2⁻¹ : Kˣ) : K))
              * Polynomial.X) := by
  rw [Polynomial.sum_comp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [compData_cmp A Nhat hNhat H₀ q D Acoef hA t]
  simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp,
    Polynomial.C_mul, mul_pow, Polynomial.C_pow, Units.val_inv_eq_inv_val]
  ring

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.compData_cmp
#print axioms Uniformity.Density.Gauge.compData_cmp_poly

end AxCheck
