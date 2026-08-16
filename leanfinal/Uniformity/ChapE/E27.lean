/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E26
import Uniformity.ChapH.H53

/-!
# Uniformity.ChapE.E27 — the twisted seam kill (no cancellation)

**Chapter E, NODE E.27** (`blueprint/CHAP-E_sigma_ladder.md` §5), ENV-E3. The single lemma the
whole slot machinery rests on: an assembled seam residue cannot cancel to zero.

With the stage extension `F → K`, a stage generator `η : K` integral over `F` whose minimal
polynomial has degree `[K : F] = g`, a coefficient vector `γ : Fin g → F` with **some** entry
nonzero, and a twist `ϑ : Fin g → F` with **every** entry nonzero, the twisted seam sum
(E.26's `seamSumT γ ϑ η = Σ_{t<g} algebraMap F K (γ t * ϑ t) * η ^ t`) is nonzero.

R1-b Step 3's closing argument, verbatim: *"the coefficients `γ_t·ϑ_t` lie in `K_i` and vanish
iff `γ_t` does (`ϑ_t` is a unit), and at least one attaining `γ_t ≠ 0` — so the sum is
NONZERO."* At `ϑ ≡ 1` this is `(SLOT₂)` Step 3's `K`-basis independence.

## Why the twist costs nothing

The proof is two moves. The twisted family is presented to H.53 as the SINGLE `F`-coefficient
family `t ↦ γ t * ϑ t` — this is exactly why E.26 multiplies the twist in *before* the transport
(`algebraMap F K (γ t * ϑ t)`, not a product of two transports): the sum is then literally
`Σ_t algebraMap F K (l t) * η ^ t` at `l := γ * ϑ`, the shape `eta_independent` consumes, with
no rewriting. H.53 then forces `γ t * ϑ t = 0` for **every** `t`; `F` is a field, so the
nonvanishing twist cancels and `γ t = 0` for every `t`, contradicting `hγ`.

Note the direction of the two quantifiers, which is where a slip would hide: `hγ` is
existential (`∃ t, γ t ≠ 0` — *some* attaining slot has a nonzero digit) and `hϑ` is universal
(`∀ t, ϑ t ≠ 0` — *every* twist entry is a unit). Weakening `hϑ` to an existential is false:
with `g = 2`, `γ = (1, 0)`, `ϑ = (0, 1)` the sum is `0` while `γ ≠ 0` and `ϑ 1 ≠ 0`.

## The `ϑ_t, t ≥ 1` disclosure (honesty, transcribed)

`EFF.HE7.110` discloses that the level-3 instance family has `g₂ = 1` throughout, so the twist
entries at `t ≥ 1` are *structurally invisible* to the numeric battery: `he7rannex_supp.py` P3
(18/79 σ flips when the deep letter is dropped) certifies that the twist is load-bearing in the
kill's INPUTS, but no instance exercises `t ≥ 1`. The Lean proof covers every `t` at once — the
same move by which H.53 discharged GENHN's `f₁ ≥ 2` vacuity — so the machine-invisible range is
covered by the theorem even though it is not covered by the battery.

DEPENDS: E.26 (`seamSumT`), **H.53** (`Uniformity.Density.Induction.eta_independent`, the
sanctioned chapter-H §8 slice — consumed by the committed signature).

SOURCE: `EFF.HE7.110` (R1-b Step 3, quoted above); `EFF.HE7.11` (Step 3: *"r is irreducible
over K of degree d_r, so {1, β, …, β^{d_r−1}} is a K-basis of K₂; since the γ_t lie in K and at
least one attaining γ_t is nonzero, the sum is nonzero"*); `EFF.GENHN.27` (the level-1 base:
within-class residue-field independence — H.53's own source).

ENVIRONMENT: ENV-E3.

## Status

Sorry-free. Footprint `[propext, Classical.choice, Quot.sound]` — Lean core only (the
`Classical.choice` enters through H.53's `classical`/mathlib `minpoly` route). No chapter
axiom, in particular not B.42.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- **E.27** The twisted seam kill: with `η` generating `K` over `F` in the minimal-polynomial
sense (`(minpoly F η).natDegree = [K : F] = g`), a coefficient vector with some nonzero entry
and a twist with every entry nonzero assemble to a NONZERO seam residue. -/
theorem seamSumT_ne_zero {F K : Type*} [Field F] [Field K] [Algebra F K] {η : K}
    (hgen : (minpoly F η).natDegree = Module.finrank F K) (hint : IsIntegral F η)
    {g : ℕ} (hg : g = Module.finrank F K) (γ ϑ : Fin g → F)
    (hγ : ∃ t, γ t ≠ 0) (hϑ : ∀ t, ϑ t ≠ 0) :
    seamSumT γ ϑ η ≠ 0 := by
  intro hzero
  -- The twisted family, as ONE `F`-coefficient family — the shape H.53 consumes.
  have hvanish : ∀ t, γ t * ϑ t = 0 :=
    Induction.eta_independent hgen hint hg (fun t => γ t * ϑ t) hzero
  obtain ⟨t, ht⟩ := hγ
  -- A field has no zero divisors, and the twist entry is a unit.
  exact ht ((mul_eq_zero.1 (hvanish t)).resolve_right (hϑ t))

end Uniformity.Density.Ladder

/-! ## Gate

`seamSumT` is field-valued, so the kill is not `decide`-able in general. Three checks instead:
an evaluation check on the imported `seamSumT` (guarding against E.26 drift), the kill executed
at `g = 1` — the corpus's own machine-visible range, `EFF.HE7.110`'s `g₂ = 1` family — and a
**model-independent falsifier** for the weakened hypothesis. -/

section Gate

open Uniformity.Density.Ladder

/-- Evaluation check: at `g = 1` the seam sum is the single twisted coefficient
(`η ^ 0 = 1`), for any `η`. Guards the imported E.26 body. -/
example {F K : Type*} [Field F] [Field K] [Algebra F K] (γ ϑ : Fin 1 → F) (η : K) :
    seamSumT γ ϑ η = algebraMap F K (γ 0 * ϑ 0) := by
  simp [seamSumT]

/-- All of `ZMod 5`, as a list. -/
private def zmod5 : List (ZMod 5) := (List.range 5).map (fun i => (i : ZMod 5))

#guard zmod5.length == 5

-- The kill EXECUTED at `g = 1` over `F = K = ZMod 5` (`η` immaterial, `η ^ 0 = 1`): the
-- twisted coefficient `γ₀ * ϑ₀` is nonzero whenever `γ₀ ≠ 0` and `ϑ₀ ≠ 0`. This is the whole
-- theorem on the `g₂ = 1` stratum the battery can see.
#guard zmod5.all fun g0 => zmod5.all fun t0 =>
  !(decide (g0 ≠ 0) && decide (t0 ≠ 0)) || decide (g0 * t0 ≠ 0)

-- NEGATIVE control, and it holds in EVERY stage extension: weakening `hϑ` from
-- `∀ t, ϑ t ≠ 0` to `∃ t, ϑ t ≠ 0` makes the kill FALSE at `g = 2`. So the universal
-- quantifier on the twist is load-bearing, not a transcription choice.
example {F K : Type*} [Field F] [Field K] [Algebra F K] (η : K) :
    ∃ γ ϑ : Fin 2 → F, (∃ t, γ t ≠ 0) ∧ (∃ t, ϑ t ≠ 0) ∧ seamSumT γ ϑ η = 0 :=
  ⟨![1, 0], ![0, 1], ⟨0, by simp⟩, ⟨1, by simp⟩, by
    simp [seamSumT, Fin.sum_univ_two]⟩

end Gate

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.seamSumT_ne_zero

end AxCheck
