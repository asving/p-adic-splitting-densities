/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B25

/-!
# Uniformity.ChapB.B64 — NS-6, the `⇒` direction: a repeated residual factor forces a further level

**Chapter B, NODE B.64** [lemma] (`blueprint/CHAP-B_leaf_layer.md` §9, the NS-6 layer), ENV-A.

*NS-6, the `⇒` direction.* Let `φ` be an order-1 key of degree `m`, `(u,ℓ)` a slope of `f`, and
`ψ` a monic irreducible factor of the residual polynomial with multiplicity `a ≥ 2`. The
corresponding factor `g` of `f` (B.48) has `deg g = ℓ * m * a * deg ψ`, and therefore

```
ℓ * m * deg ψ  <  deg g,
```

i.e. `g`'s degree strictly exceeds the degree `ℓ * m * deg ψ` that a single order-1 leaf with the
data `(ℓ, ψ)` would have. Consequently `g` is **not** an order-1 leaf for the pair `(u/ℓ, ψ)`, and
the order-1 datum does not determine `typeOf g`.

DEPENDS: B.25 (`resField`, for the type of `ψ`) · B.47 (the degree law that produces `hg` at the
call site) · mathlib `Nat` arithmetic only.

**PROOF.** `hg` rewrites the goal to `ℓ*m*deg ψ < ℓ*m*a*deg ψ`; `1 < a` and the positivity of
`ℓ*m` give `ℓ*m < ℓ*m*a`, and multiplying by the positive `deg ψ` is strictly monotone.

## ⚠ WHAT THIS NODE DOES **NOT** PROVE — `HE6-BOX-1` is an explicit NON-NODE

`docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` §3 F-1 gives the route verbatim: "(⇒) is [AGNPRW]
Thm 2.10's degree law `deg Q = m·e·deg R(Q)`: a residual factor `ψ` with `ord_ψ(R) = a ≥ 2` gives
`deg g_{λ,ψ} = e_λ·a·deg ψ·deg φ > e_λ·deg ψ·deg φ = deg(lift of ψ)`, so the type is not
`f`-complete and a level must be added." **That is a degree inequality and nothing more**, which
is why this node is eight lines.

What it does **not** prove — and what chapter B does not claim — is that `typeOf g` is genuinely
*undetermined* by the order-1 data. That stronger claim is **`HE6-BOX-1`**, which has a machine
certificate but no proof: `EFF.HE6.36` widens the box to `{ℓ≥2, d_r≥1} ∪ {ℓ=1, d_r≥2}` and
`EFF.HE6.37`'s tooth `HE6-T-CASEB` exhibits "3 distinct PARI σ on identical outer data — box is
real". `HE6-BOX-1` **is an explicit non-node of this chapter and must not be given one**; its
`ℓ=1` branch lives entirely in `EFF-HE6R1.md` (H-3), its disposition is
disclosure-without-promotion, and an agent who needs it must return `BLOCKED: HE6-BOX-1`.

## Faithfulness

`docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` NS-6 §3 F-1, transcribed as the bare degree
inequality it is. Note that `EFF.HE6R1.09` (`LEMMA HE6R1-1`'s jump condition `ℓ_i·deg r_i ≥ 2`) is
the *level-2* trigger and a **different** statement; it is not what is proved here.

**TEETH.** `HE6-T-CASEB` (`EFF.HE6.37`) stays an executable regression — the box is certified
real by machine and is **not** proved here; `HE6R1-T-CRACK` (`EFF.HE6R1.29`, "3 distinct σ at
identical outer data", fired at both `p=3,5`) likewise stays an executable regression.

SOURCE: `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` NS-6 §3 F-1; `EFF.HE6.36`; `EFF.HE6.37`;
`EFF.HE6R1.09`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial

-- ENV-A (blueprint §0.1): the polynomial arena. No `hπ` is needed — the statement is `Nat`
-- arithmetic over the ambient types.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

-- The signed binder `{u : ℕ}` (the slope numerator) is carried verbatim from the frozen
-- SIGNATURE even though the inequality never names it: the statement is about the abscissa
-- data `(ℓ, m, a, deg ψ)` alone.
set_option linter.unusedVariables false in
/-- **B.64 — NS-6, the `⇒` direction.** A residual factor of multiplicity `a ≥ 2` produces a
factor whose degree strictly exceeds the order-1 leaf degree `ℓ * m * deg ψ`. -/
theorem lt_natDegree_of_multiplicity_two {φ : Polynomial O} {u ℓ a : ℕ} (hℓ : 0 < ℓ)
    (hm : 0 < φ.natDegree) {ψ : Polynomial (resField φ)} (hψ : 0 < ψ.natDegree) (ha : 2 ≤ a)
    {g : Polynomial O} (hg : g.natDegree = ℓ * φ.natDegree * a * ψ.natDegree) :
    ℓ * φ.natDegree * ψ.natDegree < g.natDegree := by
  rw [hg]
  have hM : 0 < ℓ * φ.natDegree := Nat.mul_pos hℓ hm
  have h1 : ℓ * φ.natDegree < ℓ * φ.natDegree * a := (Nat.lt_mul_iff_one_lt_right hM).2 (by omega)
  exact (Nat.mul_lt_mul_right hψ).2 h1

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.lt_natDegree_of_multiplicity_two
end AxCheck
