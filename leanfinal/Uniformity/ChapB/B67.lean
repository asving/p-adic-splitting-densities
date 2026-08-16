/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B46
import Uniformity.ChapB.B63a
import Uniformity.MultiHensel

/-!
# Uniformity.ChapB.B67 — the order-0 peel at every degree

**Chapter B, NODE B.67** [theorem] (`blueprint/CHAP-B_leaf_layer.md` §8), ENV-C. One signed
declaration.

*The statement.* Let `f` be monic of positive degree over the complete local base and let its
reduction factor as `f̄ = ∏_{i ∈ s} φ̄_i ^ {a_i}` with the `φ̄_i` monic irreducible and pairwise
distinct. Then `f = ∏_{i ∈ s} f_i` with each `f_i` monic, `f̄_i = φ̄_i ^ {a_i}`, and

```
(typeOf f).data = ∑_{i ∈ s} (typeOf f_i).data.
```

This is the **weld** `spec/HYPOTHESIS_LEDGER.md` `HYP.03`'s residual-scope note asks for
(*"composing this with `typeOf_mul` … into the full order-0 leaf law at every degree is flagged
but not yet assembled"*, `spec/CERTAIN_NODES_2026-08-14.md` REJECTED R10): the `n`-fold Hensel
lift supplies the blocks, and the `Finset`-indexed peel law supplies their type bookkeeping.

## Proof

Three steps, exactly the blueprint's.

1. **Pairwise coprimality of the blocks.** For `i ≠ j` in `s`, `φ₀ i` is irreducible and does not
   divide `(φ₀ j) ^ (a j)`: were it to, primality in the PID `(ResidueField O)[Y]` would give
   `φ₀ i ∣ φ₀ j` (this also covers `a j = 0`, where the divisibility would make `φ₀ i` a unit),
   hence `Associated (φ₀ i) (φ₀ j)` between two irreducibles, hence `φ₀ i = φ₀ j` since both are
   monic — contradicting `hne`. B.46's `isCoprime_pow_of_not_dvd` then gives
   `IsCoprime ((φ₀ i) ^ (a i)) ((φ₀ j) ^ (a j))`.
   *(The blueprint's `IsCoprime.prod_right` extension is not needed: landed
   `exists_monic_factorization_finset` consumes pairwise coprimality directly and does the
   `prod_right` step itself.)*
2. **The lift.** Landed `Uniformity.Hensel.exists_monic_factorization_finset` (CN-17) at
   `g₀ i := (φ₀ i) ^ (a i)` returns the monic family `g`, the product identity `f = ∏ i ∈ s, g i`,
   the reductions `ḡ_i = φ̄_i ^ {a_i}`, and the degrees (the last clause is not part of this
   node's frozen conclusion and is discarded).
3. **The type identity.** B.63a's `typeOf_prod` — landed `typeOf_mul` iterated over a `Finset`
   product — turns `(typeOf (∏ i ∈ s, g i)).data` into `∑ i ∈ s, (typeOf (g i)).data`, and the
   product identity of step 2 rewrites `f` into the product.

The signed hypothesis `hd : 0 < f.natDegree` is not needed — the statement is true at `f = 1`
(take `g ≡ 1`), and CN-17 handles the empty `s` and the `a i = 0` blocks itself. It is retained
because the signature is frozen against the gate-verified stub.

DEPENDS: B.46 (`isCoprime_pow_of_not_dvd`) · B.63a (`typeOf_prod`) · landed
`Uniformity.Hensel.exists_monic_factorization_finset` (`MultiHensel.lean:111`) · mathlib
`Prime.dvd_of_dvd_pow`, `Irreducible.associated_of_dvd`,
`Polynomial.eq_of_monic_of_associated`, `UniqueFactorizationMonoid.irreducible_iff_prime`.

**Namespace.** `Uniformity.Density.Leaf`, the chapter's namespace, as in the frozen stub.

**SIZE.** blueprint 40 lines; landed 24.

## Type diff against the stage-0e stub — the known `axiom`-vs-`theorem` inclusion artifact

`[Finite (ResidueField O)]` is `omit`ted per §12 rule 7 — the node is a Hensel lift plus multiset
bookkeeping and never asks the residue field to be finite; the stub's `axiom` sheds it for the
same reason, so that binder agrees.

The one difference is `[IsAdicComplete (maximalIdeal O) O]`, which the landed `theorem` keeps and
the stub's `axiom` sheds (the *statement* never names it; the *proof* needs it, through CN-17).
This is B.26 row (b)'s documented artifact, and here too the instance is **not** decoration:
without completeness the statement is **false**. Take `O = ℤ_(5)` (the localization, a
non-complete DVR), `f = X ^ 2 + 1`, `s = {1, 2}`, `φ₀ = (X − 2, X + 2)`, `a ≡ 1`: the reduction
splits mod `5`, every hypothesis holds, yet `f` is irreducible over `ℚ` and so admits no
factorization into two monic degree-`1` blocks over `ℤ_(5)`. **Recorded for the 0e type diff:**
on this row the mismatch is the stub's, not the transcription's.

**TEETH.** `W12-LVL0` (`EFF.W12.54`, 0/138 violations: 5 cubic level-0 pattern censuses plus their
sum `q³`) → **executable regression** retained; `W12-BLOCK` (0/1,594,670) → **Lean theorem** (the
product identity, this declaration's second conjunct).

SOURCE: `EFF.W12.21` (`LEMMA W12-S2.1`, *"Level-0 product structure (window-exact Hensel
bijection)"*); `EFF.W12.22`; `spec/HYPOTHESIS_LEDGER.md` `HYP.03`'s residual-scope note;
`spec/CERTAIN_NODES_2026-08-14.md` REJECTED R10.

## Status

Sorry-free, axiom-free (Lean core only). The 2026-08-16 B.42 literature cite is **not** on this
file's import path — the order-0 peel never touches the slope factorization.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

section ENVC
-- ENV-C (blueprint §0.1): ENV-A + completeness + residue finiteness.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

omit [Finite (ResidueField O)] in
-- `hd : 0 < f.natDegree` is part of the frozen signature and is not used by the proof; see the
-- module docstring.
set_option linter.unusedVariables false in
/-- **B.67 — the order-0 peel at every degree.** A monic `f` whose reduction is
`∏_{i ∈ s} φ̄_i ^ {a_i}`, with the `φ̄_i` monic irreducible and pairwise distinct, factors as a
matching product of monic blocks, and its type data is the sum of the blocks' type data.

Residue finiteness is `omit`ted (§12 rule 7): the node is `n`-fold Hensel plus the `Finset`-indexed
`typeOf` bookkeeping, and neither asks the residue field to be finite. -/
theorem exists_order0_peel {f : Polynomial O} (hf : f.Monic) (hd : 0 < f.natDegree)
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {φ₀ : ι → Polynomial (ResidueField O)}
    {a : ι → ℕ} (hmon : ∀ i ∈ s, (φ₀ i).Monic) (hirr : ∀ i ∈ s, Irreducible (φ₀ i))
    (hne : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → φ₀ i ≠ φ₀ j)
    (hres : f.map (IsLocalRing.residue O) = ∏ i ∈ s, (φ₀ i) ^ (a i)) :
    ∃ g : ι → Polynomial O, (∀ i ∈ s, (g i).Monic) ∧ f = ∏ i ∈ s, g i ∧
      (∀ i ∈ s, (g i).map (IsLocalRing.residue O) = (φ₀ i) ^ (a i)) ∧
      (typeOf f).data = ∑ i ∈ s, (typeOf (g i)).data := by
  classical
  -- ## step 1 — the blocks are pairwise coprime
  have hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime ((φ₀ i) ^ (a i)) ((φ₀ j) ^ (a j)) := by
    intro i hi j hj hij
    refine isCoprime_pow_of_not_dvd (hirr i hi) (fun hdvd => hne i hi j hj hij ?_)
    have hprime : Prime (φ₀ i) := (hirr i hi).prime
    exact Polynomial.eq_of_monic_of_associated (hmon i hi) (hmon j hj)
      ((hirr i hi).associated_of_dvd (hirr j hj) (hprime.dvd_of_dvd_pow hdvd))
  -- ## step 2 — the `n`-fold Hensel lift
  obtain ⟨g, hgm, hgprod, hgres, -⟩ :=
    Uniformity.Hensel.exists_monic_factorization_finset s hf (fun i => (φ₀ i) ^ (a i))
      (fun i hi => (hmon i hi).pow _) hcop hres
  -- ## step 3 — the `Finset`-indexed peel law
  exact ⟨g, hgm, hgprod, hgres, by rw [hgprod]; exact typeOf_prod hgm⟩

end ENVC

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.exists_order0_peel
end AxCheck
