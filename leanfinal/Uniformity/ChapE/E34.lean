/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.ZMod.Basic

/-!
# Uniformity.ChapE.E34 — `(IDX-TWIST)`'s bijection layer

**Chapter E, NODE E.34** [lemma] (`blueprint/CHAP-E_sigma_ladder.md` §6), ENV-E3 (the
stage-field arena: pure finite-field algebra, no local base `O`; here the field is left
abstract per GC-7's abstract-then-instantiate rule).

The `(IDX-TWIST)` relabelling — the print/coherent frame conversion multiplies every label of a
stage family by ONE fixed element `η^{q(κ)}` of `K^×` — is **lossless**. Its whole Lean content
is a two-line fact about a field: multiplication by a unit `w : Kˣ` is a bijection of `K`
fixing `0`, hence a bijection of `K \ {0}` onto itself. `EFF.T2.70` states exactly this and
then draws the consequence the chapter needs: the relabelled family covers every element
*"member for member; what it does not do is match them at equal index names"* — the family's
labels at `(ℓ, d) = (1, 1)` run over exactly `K^×`, the master's digits at a full height run
over all of `K`, and `L_κ(0) = 0` is the empty recentering, so the two ranges match after the
twist even though the index NAMES do not.

## The two qualifiers — RECORDED READING DIRECTIVES, not Lean content

`EFF.T2.20` boxes `(IDX-TWIST)` with two riders. Both are statements about the INSTANCE's lift
choices (carrier content, supplied by E.22's instance row), NOT propositions this node proves;
they are transcribed here verbatim in force so that no consumer silently upgrades the bijection
into more than it is:

1. **Compatible-lift equality.** The polynomial equality of the twisted and untwisted reads
   holds *exactly at the COMPATIBLE lift choice*; at an arbitrary permitted lift it holds only
   modulo height-`> κ` increments.
2. **Covering direction.** The covering claim is asserted at `κ > D′h` — it is a statement
   about the reachable range at heights above the key-degree height, not mere fullness of the
   digit set.

Honesty note (E-5): this node adjudicates NOTHING about frame orientation. The print↔coherent
frame conversion itself is E.22's instance row; the four-way `ϑ`/`Θ` orientation reconciliation
is chapter D's GC-14 table, cited by anchor and never restated here.

DEPENDS: none (mathlib only — `Set.BijOn`, `Units.ne_zero`, `mul_left_cancel₀`).

SOURCE: `EFF.T2.70` (the bijection argument, verbatim: *"`η^{q(κ)}` is ONE fixed element of
`K^×` … Multiplication by it is a bijection of K fixing 0, and of K^× onto itself. The family's
labels at `(ℓ,d) = (1,1)` run over exactly `K^×` … this master's digits at a full height run
over all of K … with `L_κ(0) = 0` the empty recentering"*); `EFF.T2.20` (`(IDX-TWIST)` boxed
plus the two qualifiers transcribed above).

TEETH: the print/coherent-frame mutant — its cure is exactly this bijection together with
E.29's coherent read. Disposition: **Lean theorem** for the bijection layer (this file); the
frame conversion itself stays E.22's instance row. The numeric gate below re-executes the
bijection concretely on `𝔽₅` and `𝔽₇`, where it is `decide`-able.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- **NODE E.34.** *`(IDX-TWIST)`'s bijection layer.* For a fixed unit `w : Kˣ` of a field `K`,
left multiplication by `w` restricts to a bijection of `K \ {0}` onto itself: it maps nonzero to
nonzero (`w` is a unit), it is injective (cancellation by `w ≠ 0`), and it is onto (`w⁻¹ * y` is
the preimage of a nonzero `y`, and is itself nonzero). -/
theorem unit_mul_bijOn {K : Type*} [Field K] (w : Kˣ) :
    Set.BijOn (fun x : K => (w : K) * x) {x | x ≠ 0} {x | x ≠ 0} := by
  have hw : (w : K) ≠ 0 := w.ne_zero
  refine ⟨fun x hx => mul_ne_zero hw hx, fun x _ y _ h => mul_left_cancel₀ hw h, fun y hy => ?_⟩
  refine ⟨((w⁻¹ : Kˣ) : K) * y, mul_ne_zero (w⁻¹).ne_zero hy, ?_⟩
  simp

/-- **NODE E.34.** *The relabelling fixes `0`* — `L_κ(0) = 0`, the empty recentering of
`EFF.T2.70`. Together with `unit_mul_bijOn` this is the whole of the twist's losslessness: `0`
is carried to `0` and `K^×` is carried onto `K^×`. -/
theorem unit_mul_zero {K : Type*} [Field K] (w : Kˣ) : (w : K) * 0 = 0 := mul_zero _

end Uniformity.Density.Ladder

/-! ## Numeric gate — the twist, brute-forced on two stage fields

`Set.BijOn` over an abstract field is not decidable, but at a concrete residue field it is: the
nonzero elements form a finite list, and "multiplication by `w` is a bijection of `K^×`" is the
statement that the image list is a permutation of the source list. `#guard` fails elaboration
when the checked `Bool` is `false`, so these run at build time. Both stage fields the chapter's
§10 gates use (`q = 2` extends to `𝔽₅`/`𝔽₇` here only to get a nontrivial unit group) are swept
over EVERY unit `w`, not a sample. -/

section NumericGate

/-- The nonzero elements of `ZMod n`, as a list. -/
private def nonzeroList (n : ℕ) : List (ZMod n) :=
  ((List.range n).map (fun i => (i : ZMod n))).filter (fun x => decide (x ≠ 0))

-- Sanity: the list really is `K^×` (four elements at `q = 5`, six at `q = 7`).
#guard (nonzeroList 5).length == 4
#guard (nonzeroList 7).length == 6

-- The bijection of `K^×` onto itself, at every unit `w` of `𝔽₅` and of `𝔽₇`.
#guard (nonzeroList 5).all fun w => ((nonzeroList 5).map (fun x => w * x)).isPerm (nonzeroList 5)
#guard (nonzeroList 7).all fun w => ((nonzeroList 7).map (fun x => w * x)).isPerm (nonzeroList 7)

-- `L_κ(0) = 0`: the twist fixes the empty recentering, at every unit.
#guard (nonzeroList 5).all fun w => w * (0 : ZMod 5) == 0
#guard (nonzeroList 7).all fun w => w * (0 : ZMod 7) == 0

-- NEGATIVE control: the same map by the NON-unit `0` collapses `K^×`, so "unit" is
-- load-bearing in the hypothesis and not decorative.
#guard !((nonzeroList 5).map (fun x => (0 : ZMod 5) * x)).isPerm (nonzeroList 5)

end NumericGate

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.unit_mul_bijOn
#print axioms Uniformity.Density.Ladder.unit_mul_zero

end AxCheck
