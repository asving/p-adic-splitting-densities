/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B63
import Uniformity.ChapB.B73

/-!
# Uniformity.ChapB.B79a — the block certificate, half (a): the value

**Chapter B, NODE B.79 half (a)** [theorem] (`blueprint/CHAP-B_leaf_layer.md` §9), ENV-C, SPLIT
MANDATED → 2 (this file is `typeOf_eq_order1Type`; half (b) is `B79b.lean`). One signed
declaration.

*The statement.* For an order-1 key `φ` and a monic `g` with `ḡ = φ̄ ^ μ`, `0 < μ`,
`dev φ g 0 ≠ 0`, a **terminating** order-1 read (`hterm : ¬ NeedsDescent π φ g` — every side's
residual polynomial is separable), and the perimeter/`B-BOX-1` clause `hperim`:

```
typeOf g = order1Type π φ g
```

— B.66's order-1 datum is the actual splitting type, not merely a prediction.

## Proof — two lines, after A-F.11

1. **`hterm` is B.63's `hsep`, contrapositively.** B.73's `NeedsDescent` is the `∃`-negation of
   exactly B.63's `∀`-clause (same `sideMin` pin, same `1 < card` guard, same `H₀` binder), so
   the unfolding is a `by_contra` and one anonymous constructor.
2. **B.63's first conclusion clause IS this half's datum identity.** `FactorizationType.ext`
   closes.

**[A-F.11, §14 item 12 CLOSED.]** The committed instruction for step 2 was *"tying step 1's
existentially produced index family to the canonical finsets is this half's real work … the proof
re-reads B.63's own steps 1–2"*. That was **impossible as written**: a consumer holding only
B.63's committed conclusion cannot re-read B.63's proof, and that conclusion constrained its
existential `T` not at all (the slope numerator never occurred in it, the residual factor only
through its degree), so the term-by-term tie was underivable from ANY proof of B.63. Wave-15's
B.79 agent confirmed it in the strong form; A-F.11 re-signed B.63 at
`(typeOf f).data = (order1Type π φ f).data` and moved the tie inside B.63's own steps 1–2, where
B.42's and B.45's witnesses are in scope. This file is the downstream half of that repair, and it
is now one `FactorizationType.ext`.

DEPENDS (direct, post-A-F.11): B.63 (`typeOf_of_separable_residuals`) · B.66 (`order1Type`) ·
B.73 (`NeedsDescent`) · landed `Uniformity.FactorizationType.ext`. The blueprint's DEPENDS line
also names B.13 · B.42 · B.45 · B.58 · B.60 · B.61 · B.63a: those are true **transitive**
dependencies, inherited through B.63, and the line is kept as written so the generated §11 edges
stay valid.

**SIZE.** blueprint 60 lines; landed 8.

**TEETH.** `W12-SHAPE`, `W12-ORACLE`, `HE-SIG` → **executable regression** retained.

SOURCE: `EFF.HE3.67` clause 1; `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` NS-6 §3 F-1.

## Status

Sorry-free. **Footprint: `propext`, `Classical.choice`, `Quot.sound` plus
`Uniformity.Density.Leaf.exists_slope_factorization`**, inherited through B.63 — the 2026-08-16
owner-signed B.42 literature cite. No new axiom.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

section ENVC
-- ENV-C (blueprint §0.1): ENV-A + completeness + residue finiteness.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **B.79 half (a) — the block certificate's value.** A terminating order-1 read inside D-3's
perimeter makes B.66's order-1 datum the actual splitting type. -/
theorem typeOf_eq_order1Type (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {g : Polynomial O} (hg : g.Monic) {μ : ℕ} (hμ : 0 < μ)
    (hres : g.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ μ)
    (h0 : dev φ g 0 ≠ 0)
    (hterm : ¬ NeedsDescent π φ g)
    (hperim : ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
      ∀ gS : Polynomial O, gS.Monic → gS ∣ g → IsPure φ gS u ℓ →
        ∀ hne : (sideSet φ gS u ℓ).Nonempty, ∀ H₀ : ℕ,
          npHgt φ gS (sideMin φ gS u ℓ hne) = (H₀ : ℕ∞) →
          ∀ ψ : Polynomial (resField φ), ψ.Monic → Irreducible ψ →
            (∃ c : (resField φ)ˣ, resPoly π φ gS u ℓ hne H₀ = c • ψ) →
            -- [repaired: A-F.7] first disjunct narrowed from `ℓ = 1`
            ((ℓ = 1 ∧ φ.natDegree = 1) ∨ ψ.natDegree = 1 ∨
              ∀ g' ∈ monicFactors gS,
                φ.natDegree * ψ.natDegree ∣ inertiaDegOf g')) :
    typeOf g = order1Type π φ g := by
  -- ## step 1 — `hterm` unfolds to B.63's separability clause
  have hsep : ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ → ∀ h : (sideSet φ g u ℓ).Nonempty,
      1 < (sideSet φ g u ℓ).card → ∀ H₀ : ℕ, npHgt φ g (sideMin φ g u ℓ h) = (H₀ : ℕ∞) →
        (resPoly π φ g u ℓ h H₀).Separable := by
    intro u ℓ hℓ hcop h hcard H₀ hH₀
    by_contra hns
    exact hterm ⟨u, ℓ, h, H₀, hℓ, hcop, hcard, hH₀, hns⟩
  -- ## step 2 — B.63's first clause, through `FactorizationType.ext`
  exact FactorizationType.ext
    (typeOf_of_separable_residuals hπ hφ hg hμ hres h0 hsep hperim).1

end ENVC

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.typeOf_eq_order1Type
end AxCheck
