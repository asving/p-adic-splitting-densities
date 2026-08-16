/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B26
import Uniformity.ChapB.B27
import Uniformity.ChapB.B29

/-!
# Uniformity.ChapB.B65 — NS-6, the biconditional (ledger `HYP.14`, at order 1)

**Chapter B, NODE B.65** [theorem] (`blueprint/CHAP-B_leaf_layer.md` §8), ENV-C. One signed
declaration.

*The statement.* Over the complete bundle, with `φ` an order-1 key and `f` monic with
`f̄ = φ̄ ^ μ`, `0 < μ`, the blueprint's clause 1 and clause 2 are equivalent:

1. every residual polynomial of every slope of `f` is **separable**;
2. no monic irreducible `ψ ∈ (resField φ)[Y]` has `ψ ^ 2` dividing any of those residual
   polynomials.

Both clauses carry the *same* quantifier prefix — the one written out at amendment A-F.1 (PA-1),
pinned at the side's left endpoint `sideMin φ f u ℓ h` and never at abscissa `0` — so the node is
a pointwise fact about a single polynomial over a finite field, quantified.

## Which form of clause 2 is signed, and why

The blueprint's prose clause 2 reads *"every `(slope, monic irreducible residual factor)` pair has
multiplicity `1`"*. That is **not** a closed Lean statement: "multiplicity" is B.45's
existentially-produced exponent function `a ψ`, which no closed statement can name (stub-gate
defect **B-D5**). The signed clause 2 is therefore the **multiplicity-free reading**
`¬ (ψ ^ 2 ∣ resPoly …)`, re-signed by the blueprint owner at amendment **A-F.3 / B-D5**, where
its equivalence to B.45's `a ψ = 1` clause is adjudicated and proved. This file transcribes the
re-signed form verbatim from the frozen stub (`leanspec/Leanspec/ChapB.lean`, **B.65**): binder
names, order, implicitness and both sides of the `↔` unchanged.

*Scope.* The SIGNATURE freezes the `1 ↔ 2` half only. Clause 3 (*"`f` factors as a product of
order-1 leaves, one per pair, with degrees `ℓ_S · m · ψ.natDegree`"*) is B.63's conclusion and is
stated as a separate `iff` in that node's file; `2 → 3` is B.63 and `3 → 2` is B.64's degree
count. Neither is needed for — nor implied by — the declaration below, which is why this file
does not import B.63/B.64 (B.63 has not landed at the time of writing; the signed statement does
not depend on it).

## Proof

The whole content is one pointwise lemma over a finite field `K`, with **no** hypothesis on `R`:

```
R.Separable  ↔  ∀ ψ : K[Y], ψ.Monic → Irreducible ψ → ¬ (ψ ^ 2 ∣ R)
```

* `R = 0`. Both sides are **false**, so the `iff` holds. `Separable 0` is `IsCoprime 0 0`, i.e.
  `IsUnit (0 : K[Y])`, which fails; and `X ^ 2 ∣ 0`, with `X` monic irreducible, refutes the
  right-hand side. (This degenerate branch is the reason the lemma needs no `R ≠ 0`: the
  quantified statement of the node supplies none.)
* `R ≠ 0`. B.27's `separable_iff_squarefree` (the finite field is perfect) turns the left side
  into `Squarefree R`; mathlib's `squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible`
  (its `∃ x, Irreducible x` is witnessed by `X`) turns that into `∀ x, Irreducible x → ¬ x * x ∣ R`.
  Dropping monicity is `sq`; restoring it is `normalize`: an irreducible `x` is associated to the
  monic `normalize x`, which is again irreducible and whose square divides whatever `x * x` does.

The node's own hypotheses `hπ`, `hf`, `hμ`, `hres` are inert for this half — the equivalence is
true of *any* family of polynomials over the residual field. They are retained because the
signature is frozen against the gate-verified stub.

DEPENDS: B.27 (`separable_iff_squarefree`) · B.25/B.26 (`resField`, `instFieldResField`,
`instFiniteResField`) · B.29 (`resPoly`) · mathlib
`squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible`, `Polynomial.irreducible_X`,
`Polynomial.monic_normalize`, `normalize_associated`, `Associated.irreducible`.
*(The blueprint's DEPENDS also lists B.45; under the re-signed clause 2 the route no longer goes
through B.45's existential factorization data — B.27 plus the squarefree characterisation is the
shorter and A-F.3/B-D5-sanctioned path. B.63/B.64 serve clause 3 only; see the scope note above.)*

**Namespace.** `Uniformity.Density.Leaf`, the chapter's namespace, as in the frozen stub.

## Type diff against the stage-0e stub — the known `axiom`-vs-`theorem` inclusion artifact

The stub's `axiom` sheds `[IsAdicComplete (maximalIdeal O) O]` and `[Finite (ResidueField O)]`,
because the *statement* never names them; the landed `theorem` keeps both, because the *proof*
does (through `instFiniteResField`). This is exactly B.26 row (b)'s documented artifact, and on
this row too the instance is **not** decoration: without residue finiteness the statement is
**false**. Over an imperfect residual field the polynomial `Y ^ p − t` (with `t` a
non-`p`-th-power, `p = char`) is irreducible, hence divisible by no square of a monic
irreducible, yet inseparable (its derivative vanishes) — the right-hand side holds and the
left-hand side fails. Finiteness ⟹ perfect is the only thing that rules this out, and it is the
ENV-C hypothesis the blueprint already carries.

**SIZE.** blueprint 20 lines; landed 21 (the signed theorem) + 24 (the private field lemma).

**⚠ LEDGER `HYP.14` IS DISCHARGED AT ORDER 1 ONLY.** `spec/HYPOTHESIS_LEDGER.md` `HYP.14` states
the stopping criterion at every order `r`; this node is the base case `r = 1`, and the order-`r`
statement is chapter C's. The DAG edge `BP.B.65 → HYP.14` in §11 is a **partial** discharge.

**TEETH.** `W12-SHAPE` (both directions) → **Lean theorem** (this declaration).

SOURCE: `spec/HYPOTHESIS_LEDGER.md` `HYP.14`; `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` NS-6 and
§3 F-1; `docs/GMN_citations.md` Lemma 3.11(3); `docs/BLUEPRINT_PHASE_DESIGN_2026-08-13.md` §4.

## Status

Sorry-free, axiom-free (Lean core only). The 2026-08-16 B.42 literature cite is **not** on this
file's import path — B.65's signed half never touches the slope factorization.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

/-! ## 1. The pointwise fact over a finite field -/

/-- **The pointwise content of B.65.** Over a finite field, a polynomial is separable exactly
when no square of a monic irreducible divides it.

No hypothesis on `R`: at `R = 0` both sides are false (`Separable 0` is `IsUnit (0 : K[Y])`, and
`X ^ 2 ∣ 0`), which is what lets the node's quantified statement carry no positivity or monicity
side condition on the residual polynomials. -/
private theorem separable_iff_no_monic_irreducible_sq_dvd {K : Type*} [Field K] [Finite K]
    (R : Polynomial K) :
    R.Separable ↔ ∀ ψ : Polynomial K, ψ.Monic → Irreducible ψ → ¬ (ψ ^ 2 ∣ R) := by
  classical
  rcases eq_or_ne R 0 with rfl | hR0
  · -- both sides are false
    constructor
    · intro hs
      rw [Polynomial.Separable, Polynomial.derivative_zero, isCoprime_zero_left] at hs
      simp at hs
    · intro h
      exact absurd (dvd_zero _) (h Polynomial.X Polynomial.monic_X Polynomial.irreducible_X)
  · rw [separable_iff_squarefree hR0,
      squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible
        (⟨Polynomial.X, Polynomial.irreducible_X⟩ : ∃ x : Polynomial K, Irreducible x)]
    constructor
    · intro h ψ _ hirr hdvd
      exact h ψ hirr (by rwa [← sq])
    · intro h x hirr hdvd
      have hassoc : Associated (normalize x) x := normalize_associated x
      refine h (normalize x) (Polynomial.monic_normalize hirr.ne_zero)
        (hassoc.symm.irreducible hirr) ?_
      rw [sq]
      exact (mul_dvd_mul hassoc.dvd hassoc.dvd).trans hdvd

/-! ## 2. NODE B.65 — the signed contract -/

section ENVC
-- ENV-C (blueprint §0.1): ENV-A + completeness + residue finiteness.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

-- `hπ`, `hf`, `hμ`, `hres` are part of the frozen signature and are inert for the `1 ↔ 2` half;
-- see the module docstring.
set_option linter.unusedVariables false in
/-- **B.65 — NS-6, the biconditional at order 1** (ledger `HYP.14`, partial discharge).
Every residual polynomial of every slope of `f` is separable **iff** no monic irreducible `ψ` has
`ψ ^ 2` dividing one of them.

Clause 2 is the multiplicity-free reading re-signed at amendment A-F.3 / B-D5; clause 3 of the
blueprint statement lives with B.63/B.64. -/
theorem ns6_biconditional (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {f : Polynomial O} (hf : f.Monic) {μ : ℕ} (hμ : 0 < μ)
    (hres : f.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ μ) :
    (∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ → ∀ h : (sideSet φ f u ℓ).Nonempty,
        1 < (sideSet φ f u ℓ).card → ∀ H₀ : ℕ, npHgt φ f (sideMin φ f u ℓ h) = (H₀ : ℕ∞) →
          (resPoly π φ f u ℓ h H₀).Separable)
      ↔ (∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ → ∀ h : (sideSet φ f u ℓ).Nonempty,
          1 < (sideSet φ f u ℓ).card → ∀ H₀ : ℕ, npHgt φ f (sideMin φ f u ℓ h) = (H₀ : ℕ∞) →
            ∀ ψ : Polynomial (resField φ), ψ.Monic → Irreducible ψ →
              ¬ (ψ ^ 2 ∣ resPoly π φ f u ℓ h H₀)) := by
  letI : Field (resField φ) := instFieldResField hφ
  haveI : Finite (resField φ) := instFiniteResField hφ
  constructor
  · intro hsep u ℓ hℓ hcop h hcard H₀ hH₀
    exact (separable_iff_no_monic_irreducible_sq_dvd _).1 (hsep u ℓ hℓ hcop h hcard H₀ hH₀)
  · intro hsq u ℓ hℓ hcop h hcard H₀ hH₀
    exact (separable_iff_no_monic_irreducible_sq_dvd _).2 (hsq u ℓ hℓ hcop h hcard H₀ hH₀)

end ENVC

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.ns6_biconditional
end AxCheck
