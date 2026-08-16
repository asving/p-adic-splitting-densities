/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B66c
import Uniformity.ChapB.B76
import Uniformity.ChapB.B79a

/-!
# Uniformity.ChapB.B79b — the block certificate, half (b): the level-`N` certificate

**Chapter B, NODE B.79 half (b)** [theorem] (`blueprint/CHAP-B_leaf_layer.md` §9), ENV-C, SPLIT
MANDATED → 2 (half (a) is `B79a.lean`; this file is `typeOf_congr_of_certificate`). One signed
declaration.

*The statement.* For an order-1 key `φ` and a monic `g` with `ḡ = φ̄ ^ μ`, `0 < μ`, a
**terminating** order-1 read (`hterm : ¬ NeedsDescent π φ g`) and a **visible** polygon
(`hvis : Visible π φ g N`): for every monic `g'` of the same degree with
`π ^ N ∣ (g - g').coeff i` at every `i`, and the perimeter/`B-BOX-1` clause `hperim` **at the
lift** `g'`,

```
typeOf g' = order1Type π φ g
```

— R8-1's two clauses on the representative certify B.66's order-1 datum as the actual splitting
type of *every* member of the level-`N` window class.

## `hperim` sits at the lift — the A-F.12 re-sign, and why

The frozen form of this signature carried `hperim` at the representative (`gS ∣ g`, ahead of the
`g'` binders) and was proved **UNPROVABLE** by the wave-16 B.79b unit: this proof applies half (a)
to `g'` (step 6), so it needs the perimeter of `g'`'s divisors, and nothing relates the two divisor
lattices. `hperim` is not a statement about the read data — it quantifies over the monic divisors
`gS` of the polynomial, and its third disjunct speaks about `inertiaDegOf` of `gS`'s monic factors.
B.73–B.77 transport `suppVal`/`sideSet`/`sideMin`/`IsPure`/`resPoly`/`Visible`/`NeedsDescent` and
mention neither `∣` nor `monicFactors` nor `inertiaDegOf`; no congruence-invariance for
`inertiaDegOf` exists in `leanfinal`; and the bridge is `B-BOX-1`-strength, i.e. circular.

Amendment **A-F.12** (2026-08-16) therefore moved the clause **after** the lift's binders and
re-pointed it at the lift (`gS ∣ g'`), renaming the third disjunct's inner binder `g''` (it would
otherwise shadow `g'`). A second clause at `g` alongside this one was REJECTED as dead weight: this
proof never dissects `g` — step 7 goes through the perimeter-free `order1Type_congr`. The corpus's
own scope for the `(e,f)` side-condition is per lift (`EFF.W12.27`'s two clauses: the window class
shares *the data the read consumes*, while the factorization with its `(e,f)` labels is asserted of
*any* lift `F`; `EFF.W12.86` step 5: "for every disc-nonzero lift").

## Proof — the banked skeleton, seven legs

1. `0 < N` from `hvis` (`Visible` at `N = 0` is `∃ i, ¬ 1 ∣ …`, false).
2. `ḡ' = ḡ = φ̄ ^ μ` — `hgg'` at every coefficient through `Ideal.Quotient.eq_zero_iff_mem` and
   `hπ.maximalIdeal_eq`, with `π ∣ π ^ N` from leg 1.
3. `Visible π φ g' N` by B.76(iv) `visible_congr`.
4. `dev φ g' 0 ≠ 0` by B.76(ii) `visible_iff_npHgt_lt` + `npHgt_eq_top_iff` — this is how half (b)
   supplies half (a)'s A-F.9 hypothesis `h0` at the lift.
5. `¬ NeedsDescent π φ g'` by B.74's `needsDescent_congr`.
6. Half (a) at `g'`: `typeOf g' = order1Type π φ g'`, consuming `hperim` **as given**.
7. `order1Type π φ g' = order1Type π φ g` by the landed `order1Type_congr` (B.66c) — the one
   non-mechanical leg, banked there at A-F.12 because it is a statement about `order1Type` alone.

DEPENDS (direct): B.79(a) (`typeOf_eq_order1Type`) · B.66c (`order1Type_congr`) · B.74
(`needsDescent_congr`) · B.75 (`Visible`) · B.76(ii) (`visible_iff_npHgt_lt`), B.76(iv)
(`visible_congr`) · B.12 (`npHgt_eq_top_iff`). B.73/B.77's transport clauses are inherited through
`needsDescent_congr` and `order1Type_congr`, which consume them by name.

**SIZE.** blueprint ≈ 30 lines (A-F.12's revision of the original 40); landed 22.

**TEETH.** `HE-SIG` (`EFF.HE3.52`, 947 PARI jobs, 0 bad) → **Lean theorem** inside D-3's
perimeter, **executable regression** retained outside it (`hperim` carried); `HE-BND`
(`EFF.HE3.55`, RE-SCOPED) → **executable regression** per D-4(c); `HE-T-CAP` (`EFF.HE3.54`) →
**Lean theorem**, discharged inside `order1Type_congr` by B.74's `H₀_lt_of_visible`.

SOURCE: `EFF.HE3.67` clauses 1–2 (R8-1's recursive certificate at order 1); `EFF.HE3.15`
(DEFINITION 2's decided leaves (a)/(b) = `hterm`/`hvis`); `EFF.W12.86` step 5; `EFF.W12.27`.

## Status

Sorry-free. **Footprint: `propext`, `Classical.choice`, `Quot.sound` plus
`Uniformity.Density.Leaf.exists_slope_factorization`**, inherited through half (a) ← B.63 — the
2026-08-16 owner-signed B.42 literature cite. No new axiom.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

section ENVC
-- ENV-C (blueprint §0.1): ENV-A + completeness + residue finiteness.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **B.79 half (b) — the level-`N` block certificate.** A terminating, visible order-1 read of
`g` inside D-3's perimeter fixes `typeOf` on the whole level-`N` window class of `g`, at B.66's
order-1 datum. `hperim` is signed **at the lift** `g'` (amendment A-F.12). -/
theorem typeOf_congr_of_certificate (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {g : Polynomial O} (hg : g.Monic) {μ : ℕ} (hμ : 0 < μ)
    (hres : g.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ μ)
    (hterm : ¬ NeedsDescent π φ g)
    {N : ℕ} (hvis : Visible π φ g N)
    {g' : Polynomial O} (hg' : g'.Monic) (hdeg : g'.natDegree = g.natDegree)
    (hgg' : ∀ i, π ^ N ∣ (g - g').coeff i)
    (hperim : ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
      ∀ gS : Polynomial O, gS.Monic → gS ∣ g' → IsPure φ gS u ℓ →
        ∀ hne : (sideSet φ gS u ℓ).Nonempty, ∀ H₀ : ℕ,
          npHgt φ gS (sideMin φ gS u ℓ hne) = (H₀ : ℕ∞) →
          ∀ ψ : Polynomial (resField φ), ψ.Monic → Irreducible ψ →
            (∃ c : (resField φ)ˣ, resPoly π φ gS u ℓ hne H₀ = c • ψ) →
            -- [repaired: A-F.7] first disjunct narrowed from `ℓ = 1`
            ((ℓ = 1 ∧ φ.natDegree = 1) ∨ ψ.natDegree = 1 ∨
              ∀ g'' ∈ monicFactors gS,
                φ.natDegree * ψ.natDegree ∣ inertiaDegOf g'')) :
    typeOf g' = order1Type π φ g := by
  -- ## step 1 — `hvis` forces `0 < N` (`Visible` at `N = 0` is `∃ i, ¬ 1 ∣ …`)
  have hN : N ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi⟩ := hvis
    exact hi (by simp)
  -- ## step 2 — the reduction is unchanged: `ḡ' = ḡ = φ̄ ^ μ`
  have hres' : g'.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ μ := by
    have hsub : (g - g').map (IsLocalRing.residue O) = 0 := by
      ext k
      rw [Polynomial.coeff_map, Polynomial.coeff_zero]
      refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
      rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton]
      exact (dvd_pow_self π hN).trans (hgg' k)
    rw [Polynomial.map_sub, sub_eq_zero] at hsub
    rw [← hsub]
    exact hres
  -- ## step 3 — the lift is visible at the same window (B.76(iv))
  have hvis' : Visible π φ g' N := (visible_congr hπ hφ.monic hφ.pos hgg').1 hvis
  -- ## step 4 — half (a)'s `h0` at the lift (B.76(ii) + `npHgt_eq_top_iff`)
  have h0' : dev φ g' 0 ≠ 0 := by
    intro hz
    have hlt := (visible_iff_npHgt_lt hπ).1 hvis'
    rw [npHgt_eq_top_iff.2 hz] at hlt
    exact not_top_lt hlt
  -- ## step 5 — the lift's read terminates too (B.74)
  have hterm' : ¬ NeedsDescent π φ g' := fun h => hterm ((needsDescent_congr hπ hφ hgg' hvis).2 h)
  -- ## steps 6–7 — half (a) at the lift, then the landed transport of the datum
  rw [typeOf_eq_order1Type hπ hφ hg' hμ hres' h0' hterm' hperim]
  exact order1Type_congr hπ hφ hg hres hvis hg' hdeg hgg'

end ENVC

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.typeOf_congr_of_certificate
end AxCheck
