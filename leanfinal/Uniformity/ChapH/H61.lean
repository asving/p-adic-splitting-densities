/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H60
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Basic

/-!
# Uniformity.ChapH.H61 — constant fibres over the free slots

**Chapter H, NODE H.61** (`blueprint/CHAP-H_general_induction.md` §9). Let `Φ` be triangular with
unit pivots (H.59) on `Fin n → R` with `R` finite, and let `P : Finset (Fin n)` be the set of
*pinned* indices. Then for **every** target `t` the pinned fibre
`{v | ∀ i ∈ P, Φ v i = t i}` has cardinality `(Fintype.card R) ^ (n − P.card)` — a
**target-independent** `q`-power, the count being exactly the free slots.

DEPENDS: H.59, H.60 · mathlib `Equiv.ofBijective`, `Equiv.subtypeEquiv`, `Nat.card_congr`,
`Fintype.card_fun`, `Fintype.card_subtype_compl`, `Fintype.card_coe`.

**SOURCE.** `EFF.GENIND.156` (the fibre clause quoted at H.60); `EFF.GENH4.23` (the
onto-by-cardinality step, verbatim: *"onto by cardinality: the refine slice fixes the two pinned
digits and frees exactly the slots above `dμ` resp. `2dμ` — the same count as the node (slot
strings are key-independent, S2.3)"*).

## The proof, in three moves

1. **Transport along `Φ`.** By H.60 `Φ` is bijective, so `Equiv.ofBijective Φ T.bijective` is an
   equivalence and `Equiv.subtypeEquiv` carries the pinned fibre of `Φ` to the pinned fibre of the
   identity: `{v // ∀ i ∈ P, Φ v i = t i} ≃ {u // ∀ i ∈ P, u i = t i}` (the transport condition is
   `Iff.rfl`, since `Equiv.ofBijective Φ _ v` is `Φ v` definitionally).
2. **Free the unpinned slots.** `{u // ∀ i ∈ P, u i = t i} ≃ ({i : Fin n // i ∉ P} → R)`, by
   restriction, with inverse the dependent-`if` patch `fun i => if i ∈ P then t i else f i`. This
   is the step where target-independence happens: the target only ever appears in the *inverse*,
   never in the index set being counted.
3. **Count.** `Fintype.card_fun` gives `(card R) ^ (card {i // i ∉ P})`, and
   `Fintype.card_subtype_compl` with `Fintype.card_coe` evaluates that exponent as `n − P.card`.

**⚠ THE FULL-SLICE QUANTIFIER, AND THE MISUSE IT PREVENTS (the GENH4 GAP-1 record).**
`EFF.GENH4.09`'s CONDITIONALITY: *"Its 'ONTO the floored fresh node' quantifier is the subject of
ANNEX R2's GAP-1: the onto-statement quantifies over the FULL refine slice, and ANNEX R's R2
misapplied it to a FIXED member where only lift digits vary. **The lemma is not corrected — the
misuse is withdrawn**"*, with R2.G1 verbatim: *"GENH4-4's onto-the-fresh-node statement quantifies
over the FULL refine slice — all in-window digits free. On a FIXED member only LIFT digits vary."*
This node's signature quantifies `v` over **all** of `Fin n → R` and takes the pinned set `P` as
data, so a fixed-member application does not typecheck. **That is deliberate**: the contract makes
the withdrawn misuse un-expressible.

**Signature note (§15's fragile signature #4).** The statement deliberately mixes `Nat.card` on the
left (the fibre is a subtype with no supplied `Fintype` instance) with `Fintype.card R` on the right
(`R` carries one by hypothesis). The bridge is `Nat.card_congr` first — moving to a type that *does*
have a `Fintype` instance — and only then `Nat.card_eq_fintype_card`; going the other way would
require synthesising a `Fintype` on the fibre, which the signature does not provide.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **Constant fibres over the free slots.** For a triangular-with-unit-pivots `Φ` on `Fin n → R`
with `R` finite, and any pinned index set `P`, the fibre `{v | ∀ i ∈ P, Φ v i = t i}` has
`(Fintype.card R) ^ (n − P.card)` elements — **independently of the target `t`**. NODE H.61. -/
theorem TriangularUnitPivot.card_fibre {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    {n : ℕ} {Φ : (Fin n → R) → (Fin n → R)} (T : TriangularUnitPivot Φ) (P : Finset (Fin n))
    (t : Fin n → R) :
    Nat.card {v : Fin n → R // ∀ i ∈ P, Φ v i = t i}
      = Fintype.card R ^ (n - P.card) := by
  -- (1) Transport the fibre along the bijection `Φ` (H.60).
  have e1 : {v : Fin n → R // ∀ i ∈ P, Φ v i = t i} ≃ {u : Fin n → R // ∀ i ∈ P, u i = t i} :=
    (Equiv.ofBijective Φ T.bijective).subtypeEquiv (fun _ => Iff.rfl)
  -- (2) The pinned fibre of the identity is the free slots: restrict, and patch back with `t`.
  have e2 : {u : Fin n → R // ∀ i ∈ P, u i = t i} ≃ ({i : Fin n // i ∉ P} → R) :=
    { toFun := fun u i => u.1 i.1
      invFun := fun f => ⟨fun i => if h : i ∈ P then t i else f ⟨i, h⟩, by
        intro i hi; simp [hi]⟩
      left_inv := by
        rintro ⟨u, hu⟩
        apply Subtype.ext
        funext i
        by_cases hi : i ∈ P
        · simp [hi, (hu i hi).symm]
        · simp [hi]
      right_inv := by
        intro f
        funext i
        simp [i.2] }
  -- (3) Count the free slots: `n − #P` of them.
  have hcard : Fintype.card {i : Fin n // i ∉ P} = n - P.card := by
    simp [Fintype.card_subtype_compl, Fintype.card_coe]
  calc Nat.card {v : Fin n → R // ∀ i ∈ P, Φ v i = t i}
      = Nat.card ({i : Fin n // i ∉ P} → R) := Nat.card_congr (e1.trans e2)
    _ = Fintype.card R ^ (n - P.card) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_fun, hcard]

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.TriangularUnitPivot.card_fibre

end AxCheck
