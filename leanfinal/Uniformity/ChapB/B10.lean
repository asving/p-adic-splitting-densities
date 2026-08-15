/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B02
import Uniformity.ChapB.B08

/-!
# Uniformity.ChapB.B10 — the development is level-stable

**Chapter B, NODE B.10** [lemma] (`blueprint/CHAP-B_leaf_layer.md` §3, the development /
polygon layer), ENV-A′ (= ENV-A with `hπ : Irreducible π`, carried in the signature).

Monic division commutes with coefficient reduction: if `π ^ N` divides every coefficient of
`f - f'`, then `π ^ N` divides every coefficient of `dev φ f j - dev φ f' j`, for every `j`.
Equivalently (through B.08's `le_gaussVal_iff`), `(N : ℕ∞) ≤ gaussVal (f - f')` implies
`(N : ℕ∞) ≤ gaussVal (dev φ f j - dev φ f' j)`; that reading is recorded here as
`le_gaussVal_dev_sub`.

DEPENDS: B.02 (`dev`) · B.08 (`le_gaussVal_iff`) · mathlib `Polynomial.map_modByMonic`,
`Polynomial.map_divByMonic` (both present at the pin, for a ring hom and a monic divisor),
`Ideal.Quotient.eq`, `Ideal.mem_span_singleton`, `Polynomial.coeff_map`.

**PROOF.**
1. Reformulate as a statement about `ρ := Ideal.Quotient.mk (Ideal.span {π ^ N})`: for `a b`,
   `π ^ N ∣ (a - b).coeff i` for all `i` is equivalent to `a.map ρ = b.map ρ`, by
   `Polynomial.ext_iff`, `Polynomial.coeff_map`, `Ideal.Quotient.eq` and
   `Ideal.mem_span_singleton`.
2. The whole content is then the private helper `map_dev_congr`: for **any** ring hom
   `ρ : O →+* S`, `f.map ρ = f'.map ρ` implies `(dev φ f j).map ρ = (dev φ f' j).map ρ`.
3. `map_dev_congr` is an induction on `j`, generalising `f` and `f'`. At `j = 0` the
   development coefficient is `f %ₘ φ` by definition and `map_modByMonic` (with `hφ`) pushes
   `ρ` through the division. At `j + 1` it is `dev φ (f /ₘ φ) j` by definition, and
   `map_divByMonic` (with `hφ`) supplies the hypothesis of the induction hypothesis at the pair
   `f /ₘ φ`, `f' /ₘ φ`.
4. Combining: step 1 turns the hypothesis into `f.map ρ = f'.map ρ`, step 2 transports it to
   the development coefficients, step 1 read backwards is the conclusion.

The blueprint's fallback (re-proving `map_modByMonic` / `map_divByMonic` from
`Polynomial.modByMonic_add_div` and B.06's uniqueness) is **not needed**: both names exist at
the pin, in `Mathlib/Algebra/Polynomial/Div.lean`, with exactly the stated hypotheses.

SOURCE: `EFF.W12.23` (the development is read on `(O/π^N)[x]`, i.e. it is defined at level `N`);
`EFF.HE3.27`(c).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- The whole content of B.10, stated for an arbitrary ring hom: a ring hom that cannot tell
`f` from `f'` cannot tell their `φ`-adic development coefficients apart either. Monicity of
`φ` is what makes `%ₘ` and `/ₘ` commute with `map`. -/
private theorem map_dev_congr {S : Type*} [CommRing S] (ρ : O →+* S) {φ : Polynomial O}
    (hφ : φ.Monic) :
    ∀ (j : ℕ) (f f' : Polynomial O), f.map ρ = f'.map ρ →
      (dev φ f j).map ρ = (dev φ f' j).map ρ := by
  intro j
  induction j with
  | zero =>
    intro f f' hff
    change (f %ₘ φ).map ρ = (f' %ₘ φ).map ρ
    rw [Polynomial.map_modByMonic ρ hφ, Polynomial.map_modByMonic ρ hφ, hff]
  | succ j ih =>
    intro f f' hff
    change (dev φ (f /ₘ φ) j).map ρ = (dev φ (f' /ₘ φ) j).map ρ
    refine ih _ _ ?_
    rw [Polynomial.map_divByMonic ρ hφ, Polynomial.map_divByMonic ρ hφ, hff]

-- The signed hypothesis `hπ : Irreducible π` is kept (frozen signature) but is not needed at
-- our pin: the argument runs through the ideal `Ideal.span {π ^ N}` for a bare element `π`,
-- and never uses that this ideal is a power of the maximal ideal. Consumers hold `hπ` anyway
-- (they reach this lemma through B.08's `le_gaussVal_iff`, which does need it).
omit [IsDomain O] [IsDiscreteValuationRing O] in
set_option linter.unusedVariables false in
/-- **The development is level-stable.** If `π ^ N` divides every coefficient of `f - f'`,
then it divides every coefficient of `dev φ f j - dev φ f' j`, for every `j`. -/
theorem dev_congr (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic) {N : ℕ}
    {f f' : Polynomial O} (h : ∀ i, π ^ N ∣ (f - f').coeff i) :
    ∀ j i, π ^ N ∣ (dev φ f j - dev φ f' j).coeff i := by
  set ρ : O →+* O ⧸ (Ideal.span {π ^ N}) := Ideal.Quotient.mk (Ideal.span {π ^ N}) with hρ
  have hmap : f.map ρ = f'.map ρ := by
    refine Polynomial.ext fun i => ?_
    rw [Polynomial.coeff_map, Polynomial.coeff_map, hρ, Ideal.Quotient.eq]
    refine Ideal.mem_span_singleton.2 ?_
    simpa only [Polynomial.coeff_sub] using h i
  intro j i
  have hdev := map_dev_congr ρ hφ j f f' hmap
  have hcoeff := congrArg (fun p => Polynomial.coeff p i) hdev
  simp only [Polynomial.coeff_map] at hcoeff
  rw [Polynomial.coeff_sub]
  exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 hcoeff)

/-- The B.08 reading of `dev_congr`: level stability in terms of the Gauss valuation. -/
theorem le_gaussVal_dev_sub (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic) {N : ℕ}
    {f f' : Polynomial O} (h : (N : ℕ∞) ≤ gaussVal (f - f')) (j : ℕ) :
    (N : ℕ∞) ≤ gaussVal (dev φ f j - dev φ f' j) :=
  (le_gaussVal_iff hπ).2 (dev_congr hπ hφ ((le_gaussVal_iff hπ).1 h) j)

section AxCheck
#print axioms Uniformity.Density.Leaf.dev_congr
#print axioms Uniformity.Density.Leaf.le_gaussVal_dev_sub
end AxCheck

end Uniformity.Density.Leaf
