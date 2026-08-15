/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H02
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Uniformity.ChapH.H54 — `stageLift'`, the exact-height stage lift `L_M`

**Chapter H, NODE H.54** (`blueprint/CHAP-H_general_induction.md` §8). `LEMMA GENHN-LIFT`'s lift
of a residue-field element to an exact-`dv`-height polynomial over the ambient ring: for a genre
datum `G`, a uniformizer-like `π : O`, exponents `i a : ℕ` and a coefficient lift
`lift : ℕ → O`,

`stageLift' G π i a lift = Σ_{s < f₁} (lift s · π^(a − s·h)) · X^(i + e₁·s)`.

Definitional, no proof obligation. The three properties the corpus states about `L_M`
(integrality `s·h ≤ a`, degree `< D′`, exact height `e₁(a − s·h) + (i + e₁ s)h = M`) are H.55's,
and the quotient identity is H.56's; none of them is stated here.

## The withdrawn `normIdx` form, and why this signature is the signed one

The blueprint's SIGNATURE block also displays a `GenreDatum.normIdx` (`M ↦ (i(M), a(M))` via
`Exists.choose` on H.10's occupancy witness) and a `stageLift` phrased through it. **Neither is
landed**, per §15 rule 2 of the chapter's leanspec contract: the displayed `normIdx` body is not
even syntactically complete (it reads `(G.occupied_of_keyDeg_mul_h_lt hM).choose ...`, with an
ellipsis), and an `Exists.choose`-valued index is opaque — every consumer would have to reason
through `Exists.choose_spec` instead of through an equation. H.54's own ⚠ SIGNATURE NOTE supplies
the replacement and calls it the contract form: **take `i` and `a` as explicit arguments**, and let
H.55/H.56 carry the defining equation `i * G.h + G.e₁ * a = M` (and `i < G.e₁`,
`G.keyDeg * G.h < M`) as hypotheses. That is the declaration below, verbatim from the note; the
corpus's functional notation `i(M)`, `a(M)` survives only as prose.

Consequence for consumers, stated once so it is not rediscovered: `stageLift'` knows nothing about
`M`. A statement about the height-`M` lift must supply `i`, `a` **and** the equation relating them
to `M`; a statement that omits the equation is about a different polynomial.

DEPENDS: H.01 (`GenreDatum`), H.02 (`GenreDatum.keyDeg`, for the degree bound stated at H.55),
H.10 (the occupancy witness that produces an `(i, a)` in the first place — a *consumer-side*
dependency here, since this node takes them as arguments) · landed `Polynomial.C`, `Polynomial.X`.

SOURCE: `EFF.GENHN.81` (`LEMMA GENHN-LIFT`, verbatim: *"Write `λ∈K` uniquely as
`λ=Σ_{s=0}^{f_1-1} λ_s η^s`, `λ_s ∈ F_Q`, and define
`L_M(λ) := Σ_{s=0}^{f_1-1} λ̃_s x^{i+e_1 s} π^{a-sh}`"*).

TEETH: **PROOF-ONLY** (`EFF.GENHN.81`: *"No machine leg exercises `L_M` at `f₁ ≥ 2` inside
GENHN"*, disposition `accepted-with-decorrelation-supplied` — the algebra was hand-re-derived by
the 0a compiler before transcription) → the chapter supplies the proof at H.55/H.56. The three
unfolding checks at the bottom of this file (`f₁ = 0, 1, 2`) are the local substitute: they pin
the summand shape at the two arities the corpus writes out, so a transposed `i ↔ a` or a
`s * G.e₁` / `s * G.h` swap cannot survive silently.

**⚠ `noncomputable`, and why.** `Polynomial.C` and `Polynomial.X` are noncomputable in mathlib
(`Polynomial` is a structure over `AddMonoidAlgebra`, whose support arithmetic needs classical
decidability), so the definition carries `noncomputable` exactly as the blueprint's note writes
it. Nothing in the chapter evaluates `stageLift'`; every consumer reasons with it symbolically.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- `L_M(λ)` — the exact-height `K`-lift of `LEMMA GENHN-LIFT`, as a polynomial over the ambient
ring: `L_M(λ) = Σ_{s < f₁} λ̃_s · x^{i + e₁ s} · π^{a − s h}`.

**The signed form** (H.54's ⚠ SIGNATURE NOTE): `i` and `a` are explicit arguments, so there is no
`Exists.choose`; the relation `i * G.h + G.e₁ * a = M` to the target height `M` is a hypothesis of
the consuming lemmas (H.55, H.56), not part of this definition. -/
noncomputable def stageLift' {O : Type*} [CommRing O] (G : GenreDatum) (π : O)
    (i a : ℕ) (lift : ℕ → O) : Polynomial O :=
  ∑ s ∈ Finset.range G.f₁,
    Polynomial.C (lift s * π ^ (a - s * G.h)) * Polynomial.X ^ (i + G.e₁ * s)

end Uniformity.Density.Induction

/-! ## Unfolding checks — the summand shape at `f₁ = 0, 1, 2`.
These are `example`s, not declarations: they add nothing to the node's contract and exist so that
the exponent bookkeeping (`π`'s exponent is `a − s·h`, `X`'s exponent is `i + e₁·s`) is pinned by
the elaborator at the two arities `EFF.GENHN.81` and `EFF.GENH4.19`(F) write out. -/

section UnfoldingChecks

open Uniformity.Density.Induction

/-- `f₁ = 0` (excluded by `GenreDatum.hkey` in practice, kept as the empty-sum edge): the lift is
the zero polynomial. -/
example {O : Type*} [CommRing O] (G : GenreDatum) (π : O) (i a : ℕ) (lift : ℕ → O)
    (hf : G.f₁ = 0) : stageLift' G π i a lift = 0 := by
  rw [stageLift', hf, Finset.range_zero, Finset.sum_empty]

/-- `f₁ = 1` (the split-residual case): a single term `λ̃₀ π^a x^i` — the `π`-exponent is the bare
`a` and the `X`-exponent the bare `i`, i.e. the normalizer `x^i π^a` itself. -/
example {O : Type*} [CommRing O] (G : GenreDatum) (π : O) (i a : ℕ) (lift : ℕ → O)
    (hf : G.f₁ = 1) :
    stageLift' G π i a lift = Polynomial.C (lift 0 * π ^ a) * Polynomial.X ^ i := by
  rw [stageLift', hf, Finset.sum_range_one]
  simp

/-- `f₁ = 2` (`EFF.GENH4.19`(F)'s instance, `res(a)·η + res(b)`): the second summand drops the
`π`-exponent by exactly `h` and raises the `X`-exponent by exactly `e₁` — the two moves that
together preserve the `dv`-height, which is H.55(iii). -/
example {O : Type*} [CommRing O] (G : GenreDatum) (π : O) (i a : ℕ) (lift : ℕ → O)
    (hf : G.f₁ = 2) :
    stageLift' G π i a lift
      = Polynomial.C (lift 0 * π ^ a) * Polynomial.X ^ i
        + Polynomial.C (lift 1 * π ^ (a - G.h)) * Polynomial.X ^ (i + G.e₁) := by
  rw [stageLift', hf, Finset.sum_range_succ, Finset.sum_range_one]
  simp

end UnfoldingChecks

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.stageLift'

end AxCheck
