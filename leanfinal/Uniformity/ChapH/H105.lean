/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H104

/-!
# Uniformity.ChapH.H105 — the per-stratum undecided count (N-1c, binary form)

**Chapter H, NODE H.105** (`blueprint/CHAP-H_general_induction.md` §17.1 — the T-1 completion
layer, dated extension 2026-08-16; provenance OM-2 §3.1 `N-1b`'s consequence display and Step
4h's bridge-b, source `EFF.GENIND.54`).  Last node of **N-1**, the level-0 class transport.

Within a coprime product stratum the SEMANTIC undecided census composes EXACTLY:

* `card_undecided_mulClass : #(undecided ∩ stratum₁₂) = T₁ · T₂ − (T₁ − u₁) · (T₂ − u₂)`,

where `Tᵢ = #(stratumᵢ)` and `uᵢ = #(undecided ∩ stratumᵢ)`.

## Why the statement is written with complements, not with `uᵢ`

`T₁T₂ − (T₁−u₁)(T₂−u₂)` is an identity in ℤ; in ℕ the inner subtractions truncate.  The frozen
signature therefore writes the two *decided-within-stratum complements* directly, as
`stratumᵢ \ undecidedSet`, so that no ℕ-subtraction appears inside a product.  The ONE remaining
subtraction is exact, because the decided rectangle
`(stratum₁ \ undec₁) ×ˢ (stratum₂ \ undec₂)` sits inside `stratum₁ ×ˢ stratum₂` — that inclusion
is what `Set.ncard_sdiff` consumes.

## The proof in one line

Transport `undecided ∩ stratum₁₂` back along H.102's bijection `bijOn_mulClass`; H.104's
predicate-level iff `UndecidedAt (mulClass c₁ c₂) ↔ UndecidedAt c₁ ∨ UndecidedAt c₂` identifies
the preimage as the complement of the decided rectangle, i.e. `not both decided`; then it is a
product-of-finite-sets complement count.  `undecided_preimage` below is the set identity, stated
separately because it is the only place where H.104 is used and it is worth reading on its own.

DEPENDS: H.104 (`undecidedAt_mulClass_iff`) · H.102 (`bijOn_mulClass`) · H.101, H.100 (through
those) · landed `undecidedSet`, `levelZeroStratum` · mathlib `Set.ncard_sdiff`,
`Set.InjOn.ncard_image`, `Set.ncard_prod`.

**ENVIRONMENT — ENV-H17** + `[Finite (ResidueField O)]` + `[IsAdicComplete (maximalIdeal O) O]`,
every binder INLINE (B.42).  `Finite` is what makes `Coeff O n N` a finite type, hence every
`Nat.card` here a genuine cardinality rather than the junk value `0`; `IsAdicComplete` arrives
with H.102's Hensel.

## What is NOT claimed here

The RATE consumer's union bound `∏ Tᵢ − ∏ (Tᵢ − uᵢ) ≤ ∑ uₗ ∏ Tⱼ` is landed as H.63 and is fired
at H.124 — this node states the EXACT binary identity only.  The `r`-factor form is H.124's peel
(H.102's count corollary composes the census; this identity composes with it), and no node is
opened for it here.

## TEETH (GC-8)

`verification/openmath/OM2_genindb_battery.py` PART 2, check
`P2(iii) stratum undecided = census*(ΠT − Π(T−u))`: exhaustive per stratum, over 12 cells × 2
rings, with the child tables computed INDEPENDENTLY at their own windows (so the identity is a
prediction, not a tautology of the enumeration).  GC-8 disposition: **Lean theorem** for the
identity itself; §3's `#guard` block re-runs the ℕ-arithmetic leg the battery's Python does with
unbounded integers — that `T₁T₂ − (T₁−u₁)(T₂−u₂)` computed with truncating ℕ-subtraction agrees
with the complement form `T₁T₂ − D₁D₂` at every `(T, u)` with `u ≤ T`, and DISAGREES off that
range (the reason the signature is written with complements).  The ring-level enumeration stays
the executable regression.

## Status

Sorry-free, axiom-free (Lean core only); footprint printed at the end of the file.
-/

namespace Uniformity.Density.Induction

open IsLocalRing Polynomial

/-! ## 1. The preimage of the undecided part -/

/-- **H.104, transported.** Under H.102's bijection the undecided part of the product stratum
pulls back to the complement of the DECIDED rectangle: a pair of factor classes multiplies to an
undecided class exactly when they are *not both* decided. -/
theorem undecided_preimage {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] {n₁ n₂ N : ℕ} (hN : 1 ≤ N)
    {g₁ g₂ : Polynomial (ResidueField O)} (hg₁ : g₁.Monic) (hg₂ : g₂.Monic)
    (hd₁ : g₁.natDegree = n₁) (hd₂ : g₂.natDegree = n₂) (hcop : IsCoprime g₁ g₂) :
    (fun p : Coeff O n₁ N × Coeff O n₂ N => mulClass p.1 p.2) ''
        (((levelZeroStratum O n₁ N g₁) ×ˢ (levelZeroStratum O n₂ N g₂)) \
          ((levelZeroStratum O n₁ N g₁ \ undecidedSet O n₁ N) ×ˢ
            (levelZeroStratum O n₂ N g₂ \ undecidedSet O n₂ N)))
      = (undecidedSet O (n₁ + n₂) N ∩ levelZeroStratum O (n₁ + n₂) N (g₁ * g₂) :
          Set (Coeff O (n₁ + n₂) N)) := by
  classical
  have hbij := bijOn_mulClass hN hg₁ hg₂ hd₁ hd₂ hcop
  apply Set.Subset.antisymm
  · rintro c ⟨p, ⟨hpA, hpB⟩, rfl⟩
    obtain ⟨hp1, hp2⟩ := hpA
    have hor : UndecidedAt O n₁ N p.1 ∨ UndecidedAt O n₂ N p.2 := by
      by_contra hcon
      rw [not_or] at hcon
      exact hpB ⟨⟨hp1, hcon.1⟩, ⟨hp2, hcon.2⟩⟩
    exact ⟨(undecidedAt_mulClass_iff hN hg₁ hg₂ hd₁ hd₂ hcop hp1 hp2).2 hor,
      hbij.mapsTo ⟨hp1, hp2⟩⟩
  · rintro c ⟨hcU, hcS⟩
    obtain ⟨p, hpA, hpc⟩ := hbij.surjOn hcS
    obtain ⟨hp1, hp2⟩ := hpA
    refine ⟨p, ⟨⟨hp1, hp2⟩, ?_⟩, hpc⟩
    intro hpB
    have hU : UndecidedAt O (n₁ + n₂) N (mulClass p.1 p.2) := by
      have h := hcU
      rw [← hpc] at h
      exact h
    rcases (undecidedAt_mulClass_iff hN hg₁ hg₂ hd₁ hd₂ hcop hp1 hp2).1 hU with h | h
    · exact hpB.1.2 h
    · exact hpB.2.2 h

/-! ## 2. The node -/

/-- **H.105.** The per-stratum undecided census composes exactly:
`#(undecided ∩ stratum₁₂) = T₁ T₂ − (T₁ − u₁)(T₂ − u₂)`, written subtraction-safely with the
decided-within-stratum complements. -/
theorem card_undecided_mulClass {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    [IsAdicComplete (maximalIdeal O) O] {n₁ n₂ N : ℕ} (hN : 1 ≤ N)
    {g₁ g₂ : Polynomial (ResidueField O)} (hg₁ : g₁.Monic) (hg₂ : g₂.Monic)
    (hd₁ : g₁.natDegree = n₁) (hd₂ : g₂.natDegree = n₂) (hcop : IsCoprime g₁ g₂) :
    Nat.card
        ((undecidedSet O (n₁ + n₂) N ∩ levelZeroStratum O (n₁ + n₂) N (g₁ * g₂) :
          Set (Coeff O (n₁ + n₂) N)))
      = Nat.card (levelZeroStratum O n₁ N g₁) * Nat.card (levelZeroStratum O n₂ N g₂)
        - Nat.card ((levelZeroStratum O n₁ N g₁ \ undecidedSet O n₁ N : Set (Coeff O n₁ N)))
          * Nat.card ((levelZeroStratum O n₂ N g₂ \ undecidedSet O n₂ N : Set (Coeff O n₂ N))) := by
  classical
  have hbij := bijOn_mulClass hN hg₁ hg₂ hd₁ hd₂ hcop
  -- the decided rectangle sits inside the stratum rectangle
  have hsub :
      ((levelZeroStratum O n₁ N g₁ \ undecidedSet O n₁ N) ×ˢ
        (levelZeroStratum O n₂ N g₂ \ undecidedSet O n₂ N))
        ⊆ ((levelZeroStratum O n₁ N g₁) ×ˢ (levelZeroStratum O n₂ N g₂)) :=
    Set.prod_mono Set.sdiff_subset Set.sdiff_subset
  -- everything below is `Set.ncard`, which IS `Nat.card` on the coercion
  show ((undecidedSet O (n₁ + n₂) N ∩ levelZeroStratum O (n₁ + n₂) N (g₁ * g₂) :
      Set (Coeff O (n₁ + n₂) N))).ncard
    = (levelZeroStratum O n₁ N g₁).ncard * (levelZeroStratum O n₂ N g₂).ncard
      - (levelZeroStratum O n₁ N g₁ \ undecidedSet O n₁ N).ncard
        * (levelZeroStratum O n₂ N g₂ \ undecidedSet O n₂ N).ncard
  rw [← undecided_preimage hN hg₁ hg₂ hd₁ hd₂ hcop,
    Set.InjOn.ncard_image (hbij.injOn.mono Set.sdiff_subset),
    Set.ncard_sdiff hsub, Set.ncard_prod, Set.ncard_prod]

end Uniformity.Density.Induction

/-! ## 3. TEETH, numeric half — why the complements, and not `T − u`

The battery evaluates `census * (∏ T − ∏ (T − u))` in Python, i.e. over ℤ, where `T − u` is
honest subtraction.  The Lean statement cannot: `Nat` subtraction truncates, and
`T₁T₂ − (T₁−u₁)(T₂−u₂)` computed in ℕ is only the intended number while `uᵢ ≤ Tᵢ` — which is
true here (`undecided ∩ stratum ⊆ stratum`) but is not visible in the arithmetic.  The frozen
signature sidesteps it by naming the complements `Dᵢ = #(stratumᵢ \ undecidedSet)` directly.
The guards below check the two facts that makes honest:

1. on the admissible range `uᵢ ≤ Tᵢ`, the ℕ-truncating formula and the complement formula agree
   (exhaustively for `T, u ≤ 6`, `2401` pairs);
2. off it they DISAGREE, so the choice of formulation is load-bearing, not cosmetic.
-/

section NumericGate

/-- The battery's ℤ-formula, transcribed with ℕ subtraction. -/
private def natFormula (T₁ u₁ T₂ u₂ : ℕ) : ℕ := T₁ * T₂ - (T₁ - u₁) * (T₂ - u₂)

/-- The Lean statement's complement formula, with `Dᵢ` the decided complement's cardinality. -/
private def complementFormula (T₁ D₁ T₂ D₂ : ℕ) : ℕ := T₁ * T₂ - D₁ * D₂

-- (1) on the admissible range the two agree: `Dᵢ = Tᵢ − uᵢ` with `uᵢ ≤ Tᵢ`
#guard (List.range 7).all fun T₁ => (List.range 7).all fun u₁ =>
  (List.range 7).all fun T₂ => (List.range 7).all fun u₂ =>
    !(decide (u₁ ≤ T₁ ∧ u₂ ≤ T₂)) ||
      decide (natFormula T₁ u₁ T₂ u₂ = complementFormula T₁ (T₁ - u₁) T₂ (T₂ - u₂))

-- (2) off the range they disagree — the formulation is load-bearing.
-- `T₁ = 1, u₁ = 3, T₂ = 2, u₂ = 0`: ℕ-truncation gives `1*2 − 0*2 = 2`; over ℤ it is
-- `1*2 − (−2)*2 = 6`.
#guard natFormula 1 3 2 0 == 2
#guard (1 * 2 - (1 - 3) * (2 - 0) : Int) == 6

-- a battery-shaped spot value: `T₁ = T₂ = 4`, `u₁ = 1`, `u₂ = 2` gives `16 − 3·2 = 10`
#guard natFormula 4 1 4 2 == 10
#guard complementFormula 4 3 4 2 == 10

end NumericGate

/-! ## 4. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.undecided_preimage
#print axioms Uniformity.Density.Induction.card_undecided_mulClass

end AxCheck
