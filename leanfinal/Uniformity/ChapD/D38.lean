/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D10
import Uniformity.ChapD.D37

/-!
# Uniformity.ChapD.D38 — `(T3-BR)`, the boundary-read telescope `U = Θ·w^s`

**Chapter D, NODE D.38** [theorem] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §6, the telescope
port (T3); amendments A-1, A-D.1, A-D.2 govern — this node's SIGNATURE is unamended). ENV-D2 +
ENV-D3. One signed declaration (the leanspec stub signs it as an `axiom`; it is PROVED here).

*`(T3-BR)`: the boundary-read telescope.* For a port `P : BoundaryReadPort A q s` (D.37, the
source-local read package of `N(q)^s`),

`P.U = (A.theta q s : K) * (P.w : K) ^ s`,

i.e. the corpus's `U_i(β_s) = Θ_N(s;q)·w_i^s` under (BR1)–(BR5) alone (`EFF.T3.14`).

## The endpoint is DERIVED, never supplied — this is the whole node

`EFF.T3.14`: the two sides of the endpoint equation *"arose independently from the peeled read of
`N(q)^s` and the coherent digit of the surviving constant coefficient."* D.37's fence is landed as
the ABSENCE of a B-law field, so nothing in `BoundaryReadPort` mentions `Θ`, `w^s` or their
product: the left side of the conclusion comes out of BR4 (the constant-coefficient digit law) and
the right side out of BR1 (the peel), and they meet only through the sum collapse BR2+BR3 and the
orientation involution D.10. A port carrying the endpoint as a hypothesis would make this theorem
a tautology — that is exactly the §8.4(3) "endpoint-as-input" mutant, and it is why T3 does not
consume T1's conditional B-law (D.32) as a premise for `[GENTOW5-W(i)]` (`EFF.T3.05`): D.32
(bundle ⇒ B-law) and D.38 (port ⇒ B-law) are two derivations of the same display from two
different interfaces, and keeping them apart is what makes the GENTOW2/GENTOW5 discharges
non-circular.

## The step BR3 does NOT give you, and how `w` being a unit gives it

BR3 kills the positive-degree reads but says nothing about `0 ∈ expSupport`: D.37's `expSupport`
is DATA, not the derived support of `ctRQ`, so `0` could a priori be missing and then BR2 would
read `ct(R) = 0`. That is refuted, not assumed. If `0 ∉ expSupport` every index of the sum is
nonzero, so `Finset.sum_eq_zero` + BR3 collapse the sum to `0`, whence `w^s = 0` by BR1 — and
`w : Kˣ` is a unit of a field, so `(w : K)^s ≠ 0`. Hence `0 ∈ expSupport`, and
`Finset.sum_eq_single_of_mem` collapses the sum the other way, onto `ctRQ 0`. The peel unit's
invertibility is therefore load-bearing twice over: once here, and once in the inverse-orientation
step below.

DEPENDS: D.08 (`GaugeArena.vartheta`, `GaugeArena.theta`, reaching this file through D.10) · D.10
(`GaugeArena.theta_mul_vartheta`, the `K`-valued orientation involution) · D.37
(`BoundaryReadPort`), all landed under `Uniformity.ChapD` · mathlib `Finset.sum_eq_zero`,
`Finset.sum_eq_single_of_mem`, `Units.ne_zero`, `pow_ne_zero`, `Units.val_mul`, `Units.val_one`.

**PROOF.** T3's four displayed steps, verbatim (`EFF.T3.14`'s `[VERBATIM]` derivation).
1. `ct(R) = w^s` — BR1. 2. `ct(R) = ctRQ 0` — BR2 + BR3 collapse the sum, `0 ∈ expSupport` being
forced by `w^s ≠ 0` as above. 3. `ctRQ 0 = U·ϑ` — BR4 + BR5. 4. Therefore `w^s = U·ϑ`, and
multiplying by `Θ` through D.10's involution `Θ·ϑ = 1` gives `U = Θ·w^s`. Step 4 is a
multiplication by the involution, not a division: no `ϑ ≠ 0` side condition is incurred, because
`ϑ` is a `Kˣ` and D.10 already exhibits its inverse.

SOURCE: `EFF.T3.14` (the boxed `(T3-BR)`, its verbatim four-step proof, and the endpoint
non-supply sentence).

**ORIENTATION.** The conclusion is in the **B-law orientation** (D.06 rows 2–3): the factor is
`A.theta`, T1's `Θ_N(s;q)`, NOT `A.vartheta`. The `ϑ⁻¹` of the corpus's step 4 is the recorded
inverse orientation of T3 §8.1 check 2, landed as D.10's `theta_mul_vartheta` — so a silent swap
of the two orientations here would have to falsify D.10 to typecheck. The §8.4(2) "theta-free"
mutant is the reading that drops the factor altogether; it is refuted by the same step.

**TEETH.** T3 §8.3(1)/(3) (the GENTOW2-B″ and GENTOW5-W legs), §8.4(2) (theta-free mutant),
§8.4(3) (endpoint-as-input mutant), §8.4(4) → **Lean theorem** (this node). Gate **D.67** runs the
FRAME-C `U`/`ϑ` tables against it, and D.68 owns the inhabitation witness of D.37 whose `U` is
FORCED to `w^s·ϑ⁻¹ = Θ·w^s` — i.e. to this theorem's own conclusion — from the port axioms alone,
which is what makes D.37/D.38 non-vacuous. Nothing numeric runs in this file: the arena is
abstract over `K`.

ENVIRONMENT: ENV-D2 + ENV-D3 (`{G : Type*} [CommGroup G]`, `{K : Type*} [Field K]` written inline
per the B.42 binder rule — this file has no `variable` block).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

/-- **D.38 — `(T3-BR)`, the boundary-read telescope** (`EFF.T3.14`): under (BR1)–(BR5) alone,
`U_i(β_s) = Θ_N(s;q)·w_i^s`.

The endpoint equation is **DERIVED, never supplied**: its two sides "arose independently from the
peeled read of `N(q)^s` (BR1) and the coherent digit of the surviving constant coefficient
(BR4+BR5)", and D.37 carries no B-law field for them to be read off. ORIENTATION: the factor is
`theta` (D.06 rows 2–3), the inverse orientation of BR5's `vartheta`, mediated by D.10. -/
theorem BoundaryReadPort.t3_br {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    {A : GaugeArena G K N} {q : ℤ} {s : ℕ} (P : BoundaryReadPort A q s) :
    P.U = (A.theta q s : K) * (P.w : K) ^ s := by
  -- Step 2, first half: `0 ∈ expSupport` is FORCED — `expSupport` is data, so this is a
  -- refutation (if `0` were missing, BR2+BR3 would make the peeled read `0`, but `w` is a unit).
  have hmem : (0 : ℕ) ∈ P.expSupport := by
    by_contra h0
    have hsum : ∑ j ∈ P.expSupport, P.ctRQ j = 0 :=
      Finset.sum_eq_zero fun j hj => P.br3 j (by rintro rfl; exact h0 hj)
    have hw : ((P.w : K)) ^ s = 0 := by rw [← P.br1, P.br2, hsum]
    exact pow_ne_zero s (Units.ne_zero P.w) hw
  -- Step 2, second half: the sum collapses onto the constant read.
  have hcollapse : ∑ j ∈ P.expSupport, P.ctRQ j = P.ctRQ 0 :=
    Finset.sum_eq_single_of_mem 0 hmem fun b _ hb => P.br3 b hb
  -- Steps 1 + 3: `w^s = ct(R) = ctRQ 0 = U·ϑ`.
  have key : ((P.w : K)) ^ s = P.U * ((A.vartheta q s : Kˣ) : K) := by
    rw [← P.br1, P.br2, hcollapse, P.br4, P.br5]
  -- Step 4: multiply by `Θ` through D.10's involution (no division, no `ϑ ≠ 0` side condition).
  have hinv : ((A.theta q s : Kˣ) : K) * ((A.vartheta q s : Kˣ) : K) = 1 := by
    rw [← Units.val_mul, A.theta_mul_vartheta q s, Units.val_one]
  calc P.U = P.U * (((A.theta q s : Kˣ) : K) * ((A.vartheta q s : Kˣ) : K)) := by
        rw [hinv, mul_one]
    _ = ((A.theta q s : Kˣ) : K) * (P.U * ((A.vartheta q s : Kˣ) : K)) := by ring
    _ = ((A.theta q s : Kˣ) : K) * ((P.w : K)) ^ s := by rw [← key]

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.BoundaryReadPort.t3_br

end AxCheck
