/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E16

/-!
# Uniformity.ChapE.E41 — the scope theorem: clauses 1–2 fire without `(LB1)`

**Chapter E, NODE E.41** [lemma] (`blueprint/CHAP-E_sigma_ladder.md` §6 — the Display-A
dispositions), ENV-E2 (the carrier arena: a slot carrier `C : SlotCarrier O K` from E.10, a block
`B : BlockData C` from E.11, the interface `I : RungInterface C B` from E.12, separability in
E.14's numerical-shadow sense).

`EFF.T2.18` scopes the level-one conditionality with one sentence: *"Clauses 1 and 2 are not
[conditional]: their proofs run on the unsplit hull of F itself."* This node machine-checks that
sentence. THEOREM HE7.A's clause-(2) conclusions — the pinned class counts `D·ℓ` per linear
residual factor and `D·ℓ·deg r′` per higher one — are produced at a ONE-side state with separable
shadow from `RungInterface` data ALONE: no `LB1Carrier` (E.39), no `MP1Carrier` (E.40), no block
suite of any kind.

## Why this is a REGRESSION-shaped theorem, and what would break it

In Lean the check is **definitional**: E.16's `he7a_clause12` has no block-suite argument, so its
conclusion is already unconditional and this node is one application. The node's value is that
the check is *nailed down as a compiled obligation* — if a future re-sign of E.16 ever routed
clause (2) through `(LB1)`/`(MP1)` (the two OPEN Display-A conjuncts), or through a `BlockSuite`
field, THIS file stops compiling, because its statement mentions neither carrier and its proof
term may not manufacture one. That is the whole content: an unconditional perimeter, fenced by a
type.

## The two hypotheses are perimeter, not fuel — and the file says which

`hone` (`I.sides.card = 1`) and `hsep` (every side separable) delimit `EFF.T2.18`'s perimeter:
the one-side separable state is exactly where the source claims the read is decided by clauses
1–2 plus E.17's terminal case. Of the two, **only `hsep` is consumed** — clause (2) is stated
per-side under separability. `hone` is consumed by NOTHING, and gate (a) proves it by re-deriving
the conclusion with `hone` deleted. Keeping it in the signed statement is deliberate (it names
the source's state), and the gate is what keeps the naming honest.

Dually, gate (b) records the other half of the scoping claim: at this very state `(LB1)`'s
TRIGGER is false, so the carrier could not have supplied anything here even if a consumer had it
in hand. The trigger is transcribed inline (`1 < I.sides.card ∨ ∃ p ∈ I.sides, ¬ I.SepSide p`,
E.39's `LB1Carrier` premise verbatim) rather than imported, so that this file's import graph
matches its DEPENDS; the honest residue is that a re-spelling of E.39's trigger would need this
transcription re-checked by hand — E.39's own gate (a) is the linked copy of the same check.

## What is NOT claimed

Nothing about clauses 3–5. `EFF.T2.33`/`.34` attach the level-one fences to the clause-4 and
clause-5 routes ONLY, and those routes are E.39/E.40's OPEN carriers. This node does not weaken,
discharge or comment on them; it fences off the part of THEOREM HE7.A that never needed them.
Nor is anything claimed about the orbit/irreducible-factor reading of a class — that stays
`(FUND)` + `HYP.01` carrier content at the instance rows (E.16's own fence, inherited here).

DEPENDS: E.16 (`he7a_clause12`) · through it E.10–E.12 (the arena) and E.14 (`SepSide`).

SOURCE: `EFF.T2.18` (the scoping paragraph: *"Clauses 1 and 2 are not [conditional]: their
proofs run on the unsplit hull of F itself"*); `EFF.T2.33`/`.34` CONDITIONALITY (the level-one
fences attach to the clause-4/clause-5 routes only).

TEETH: signed source non-applicability at level one (`EFF.T2.18` TEETH) → upgraded here to a
**Lean theorem** documenting the unconditional perimeter.

ENVIRONMENT: ENV-E2.

## Status

Sorry-free, Lean-core axioms only.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

-- `hone` is an INERT signed binder: it names `EFF.T2.18`'s perimeter (the one-side state) and
-- the application does not read it — which IS this node's content, so it is KEPT per the
-- statement fence and the linter is disabled for this declaration only. Gate (a) re-derives the
-- conclusion with the binder deleted, so the inertness is checked, not merely asserted.
set_option linter.unusedVariables false in
/-- **NODE E.41.** *The scope theorem: clauses 1–2 fire without `(LB1)`.* At a one-side state
with separable numerical shadow, THEOREM HE7.A's clause-(2) conclusions hold with hypotheses
drawn from `RungInterface` alone — no `LB1Carrier` (E.39), no `MP1Carrier` (E.40), no block
suite. This is `EFF.T2.18`'s scoping sentence as a compiled obligation: the statement mentions
neither open carrier, so a future re-sign that routed clause (2) through one would break this
file. `hone` and `hsep` name the source's perimeter; only `hsep` is used (gate (a)). -/
theorem clause12_lb1_free {O : Type*} [CommRing O] {K : Type*} [Field K]
    {C : SlotCarrier O K} {B : BlockData C} (I : RungInterface C B)
    (hone : I.sides.card = 1) (hsep : ∀ p ∈ I.sides, I.SepSide p) :
    ∀ p ∈ I.sides, (∀ q ∈ I.linFac p, I.classCount p q = C.D * p.2) ∧
      (∀ q ∈ I.hiFac p, I.classCountHi p q = C.D * p.2 * q.1) :=
  -- E.16's clause (2), applied at each side with its separability witness. Nothing else is
  -- available and nothing else is needed: no block suite, no `(LB1)`, no `(MP1)`.
  fun p hp => (he7a_clause12 I).2 p hp (hsep p hp)

/-! ## Gate (executed `example`s, not blueprint declarations)

Three checks, all of them about SCOPE rather than about the counts (the counts are E.16's).

**(a) `hone` is not fuel.** The signed conclusion is re-derived with the card-one hypothesis
deleted outright. If some later edit made clause (2) depend on the side count, the signature
would still typecheck and only this example would fail — which is the point of keeping it.

**(b) `(LB1)`'s trigger is FALSE at this state.** E.39's `LB1Carrier` fires only on
`1 < I.sides.card ∨ ∃ p ∈ I.sides, ¬ I.SepSide p`; both disjuncts fail here. So the carrier
supplies nothing at a one-side separable state, and the conclusion above provably did not come
from it. (Trigger transcribed, not imported — see the header note.)

**(c) Clause (1) is unconditional too, with no perimeter at all.** `EFF.T2.18` says clauses 1
AND 2; clause (1) needs neither `hone` nor `hsep`, and the example takes neither. -/

section Gate

-- (a) the conclusion, with `hone` deleted from the binder list.
example {O : Type*} [CommRing O] {K : Type*} [Field K] {C : SlotCarrier O K}
    {B : BlockData C} (I : RungInterface C B) (hsep : ∀ p ∈ I.sides, I.SepSide p) :
    ∀ p ∈ I.sides, (∀ q ∈ I.linFac p, I.classCount p q = C.D * p.2) ∧
      (∀ q ∈ I.hiFac p, I.classCountHi p q = C.D * p.2 * q.1) :=
  fun p hp => (he7a_clause12 I).2 p hp (hsep p hp)

-- (b) the `(LB1)` trigger (E.39's premise, transcribed) is false at the node's state.
example {O : Type*} [CommRing O] {K : Type*} [Field K] {C : SlotCarrier O K}
    {B : BlockData C} (I : RungInterface C B) (hone : I.sides.card = 1)
    (hsep : ∀ p ∈ I.sides, I.SepSide p) :
    ¬ (1 < I.sides.card ∨ ∃ p ∈ I.sides, ¬ I.SepSide p) := by
  rintro (hcard | ⟨p, hp, hnp⟩)
  · omega
  · exact hnp (hsep p hp)

-- (c) clause (1): no perimeter hypotheses whatsoever.
example {O : Type*} [CommRing O] {K : Type*} [Field K] {C : SlotCarrier O K}
    {B : BlockData C} (I : RungInterface C B) :
    (∀ p ∈ I.sides, p.2 * B.T < p.1) ∧ ∑ p ∈ I.sides, I.len p = B.μ :=
  (he7a_clause12 I).1

end Gate

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.clause12_lb1_free

end AxCheck
