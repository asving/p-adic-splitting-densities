/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E12

/-!
# Uniformity.ChapE.E19 — the `(RANK)` state, its lexicographic well-founded relation, and descent

**Chapter E, NODE E.19** [def+lemma] (`blueprint/CHAP-E_sigma_ladder.md` §4, **as REPAIRED by
amendment A-E.1/E-D5 and by this file's two further repairs, recorded below**), ENV-E1.

`EFF.T2.27`'s `(RANK)` is the lexicographic triple `rank(S) = (deg F_S, μ_S, σ_𝒞(S))`: the
recursive read's state carries a polynomial degree, a mass, and a secondary rank in a carrier
`W` that `EFF.T2.26` requires to be *merely* well-founded ("an instance may discharge it either
way" — hence `W` abstract, never `ℕ`). This node lands

* `LadderState W := ℕ ×ₗ (ℕ ×ₗ W)` — the state type, lexicographically ordered;
* `ladderState_wf r` — the well-founded relation on it, built from `<` on ℕ twice and the
  supplied `r` on `W`;
* the three descent lemmas, one per component, which is the interface E.20's engine consumes.

The node exports **rank descent only**. Root preservation/partition is a separate input to E.20
(`EFF.T2.27`: *"Every transition must also preserve or partition roots and transport its
polynomial product; rank descent alone is insufficient"*), so the S7 well-founded-but-root-losing
mutant cannot be expressed as a use of this node alone.

## REPAIR 1 — the amendment's body is REFUTED: `inferInstance` finds the EMPTY relation

A-E.1/E-D5 displays the body

```lean
letI := r; (inferInstance : WellFoundedRelation (ℕ ×ₗ (ℕ ×ₗ W)))
```

and asserts that "mathlib's `×ₗ` `WellFoundedRelation` instance is found twice". **It is not.**
At our pin `#synth WellFoundedRelation (ℕ ×ₗ (ℕ ×ₗ W))` returns `sizeOfWFRel`, the
`SizeOf`-based relation — and `SizeOf (ℕ ×ₗ (ℕ ×ₗ W))` itself resolves to `instSizeOfDefault`
(the type is a `Lex` synonym, so no structural `SizeOf` applies), whose `sizeOf` is the constant
`0`. So the amendment's body defines the relation `fun _ _ => 0 < 0` — **the empty relation**.
That is machine-checked in the gate below: against the amendment's body, `¬ rel s' s` holds for
*every* pair of states, by `Nat.lt_irrefl 0`.

The consequence is worse than the defect A-E.1/E-D5 itself diagnosed. An `axiom`-stubbed relation
makes the three lemmas *unprovable*; the displayed `inferInstance` body makes them **false** —
each asserts `rel s' s` for pairs the empty relation does not relate — while still being
"well-founded" (vacuously), so E.20's engine would elaborate and be vacuous. This is exactly the
failure mode the amendment was written to prevent, reproduced by its own repair.

**The repair** is the alternative the blueprint's own SIGNATURE NOTE licenses: *"A fleet agent may
instead write the `Prod.Lex`/`Prod.lex_wf` pair explicitly — but the relation must be TRANSPARENT
enough for the three lemmas below to be provable."* The landed body is
`rel := Prod.Lex (· < ·) (Prod.Lex (· < ·) r.rel)` with `wf` from `WellFounded.prod_lex` twice
(`Prod.lex_wf` is not a constant at our pin; the core name is `WellFounded.prod_lex`). Name,
type and the three consumers' spelling `(ladderState_wf r).rel` are unchanged, and the relation
is now the intended lexicographic one — the three descent lemmas are one `Prod.lex_def` each.

## REPAIR 2 — `instance` → `def`: an uninferable explicit argument is a HARD ERROR

The signed declaration keyword is `instance`. At our pin that is rejected outright:

> This instance has 1 argument that cannot be inferred using typeclass synthesis. Specifically
> argument 2: `(r : WellFoundedRelation W)`. These arguments are not instance-implicit and appear
> neither in another instance-implicit argument nor the return type, so they cannot be inferred.

`r` cannot be made instance-implicit without breaking every consumer, which applies the relation
as `(ladderState_wf r).rel` with `r` EXPLICIT (E.19's own three lemmas; E.20's `hdec` field).
So the declaration lands as `@[reducible] def` — same name, same type, same body, same call shape
at every use site; the only thing lost is registration in the instance database, which no signed
consumer uses. `@[reducible]` is required (Lean warns that a definition of class type must be
reducible) and is also what the blueprint's transparency demand asks for.

Both repairs are deviations from the committed SIGNATURE text and are flagged for the
orchestrator: the mathematical content is the blueprint's, but A-E.1/E-D5's displayed body is
wrong and its keyword does not elaborate.

## The three descent lemmas

Each takes the kind's numeric fact as a hypothesis, one per transition kind of `EFF.T2.27`'s
derivation: split and boundary-residual (degree strictly down) use `rank_decreases_of_deg_lt`;
peel (E.18(i)) and child jump (E.17(ii), degree non-increasing, mass strictly down) use
`rank_decreases_of_mass_lt`; product-1 recentering (degree and mass preserved, `W` strictly down)
uses `rank_decreases_of_sec`. No lemma here knows which transition it serves — that binding is
E.20's and the instance records'.

DEPENDS: E.12 (the `W`/`wf` fields whose shape this mirrors) · mathlib/core `Prod.Lex`,
`Prod.lex_def`, `WellFounded.prod_lex`, `Nat.lt_wfRel`.

SOURCE: `EFF.T2.27` (`(RANK)`'s boxed display; "Every permitted nonterminal transition therefore
strictly decreases `(RANK)`, and no transition increases a component earlier than the one it
decreases"; the six transition checks; the CONDITIONALITY sentence that keeps root preservation
out of this node); `EFF.T2.26` (`(SEC-RANK)`: `W_𝒞` merely well-founded).

TEETH: S7 Pass 2 well-founded-but-root-losing mutant → closed structurally (this node exports
only rank descent; exhaustion is E.20's separate input). The gate adds the mutant this file's own
repair history produced: a vacuously well-founded EMPTY relation, refuted by exhibiting states
the landed relation does relate.

ENVIRONMENT: ENV-E1.

## Status

Sorry-free. All four declarations report at most the Lean-core triple
`{propext, Classical.choice, Quot.sound}`. Types checked against the signed SIGNATURE
declaration by declaration (binder names, order and explicitness unchanged); the two deviations
from the signed text are the declaration KEYWORD (`instance` → `@[reducible] def`) and the BODY
of `ladderState_wf` (the amendment's `inferInstance` body is refuted above), both recorded here
and in the landing commit.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- **E.19** [def] The `(RANK)` state `(deg F_S, μ_S, σ_𝒞(S))` of `EFF.T2.27`, ordered
lexicographically: `ℕ` twice, then the rung's abstract secondary-rank carrier `W`. -/
def LadderState (W : Type*) := ℕ ×ₗ (ℕ ×ₗ W)

/-- **E.19** The lexicographic well-founded relation on `LadderState W`: `<` on the degree, then
`<` on the mass, then the supplied relation `r` on the secondary carrier.

Landed as a `@[reducible] def`, not an `instance` (REPAIR 2 — an instance cannot carry the
uninferable explicit argument `r`), and with an EXPLICIT `Prod.Lex` body, not `inferInstance`
(REPAIR 1 — `inferInstance` finds `sizeOfWFRel` over `instSizeOfDefault`, i.e. the empty
relation; see the gate). -/
@[reducible] def ladderState_wf {W : Type*} (r : WellFoundedRelation W) :
    WellFoundedRelation (LadderState W) where
  rel := Prod.Lex (· < ·) (Prod.Lex (· < ·) r.rel)
  wf := WellFounded.prod_lex Nat.lt_wfRel.wf (WellFounded.prod_lex Nat.lt_wfRel.wf r.wf)

/-- **E.19** Rank descent, first component: a strictly smaller degree decreases `(RANK)`
regardless of the other two components (split, boundary residual). -/
theorem rank_decreases_of_deg_lt {W : Type*} (r : WellFoundedRelation W)
    {s s' : LadderState W} (h : s'.1 < s.1) : (ladderState_wf r).rel s' s :=
  Prod.lex_def.mpr (Or.inl h)

/-- **E.19** Rank descent, second component: equal degree and strictly smaller mass decreases
`(RANK)` (peel — E.18(i); child jump — E.17(ii)). -/
theorem rank_decreases_of_mass_lt {W : Type*} (r : WellFoundedRelation W)
    {s s' : LadderState W} (h1 : s'.1 = s.1) (h2 : s'.2.1 < s.2.1) :
    (ladderState_wf r).rel s' s :=
  Prod.lex_def.mpr (Or.inr ⟨h1, Prod.lex_def.mpr (Or.inl h2)⟩)

/-- **E.19** Rank descent, third component: equal degree and mass, with an `r`-descent in the
secondary carrier (product-1 recentering). -/
theorem rank_decreases_of_sec {W : Type*} (r : WellFoundedRelation W)
    {s s' : LadderState W} (h1 : s'.1 = s.1) (h2 : s'.2.1 = s.2.1)
    (h3 : r.rel s'.2.2 s.2.2) : (ladderState_wf r).rel s' s :=
  Prod.lex_def.mpr (Or.inr ⟨h1, Prod.lex_def.mpr (Or.inr ⟨h2, h3⟩)⟩)

/-! ## Gate (executed `example`s, not blueprint declarations)

The first block is the **refutation record** for REPAIR 1: the amendment's displayed body is
reproduced verbatim under a private name and shown to define the EMPTY relation. The second
block is the positive check that the landed relation is not empty and is genuinely
lexicographic — it relates a state whose degree drops while its mass RISES (which no
size-based or empty relation can do), and it does not relate that pair in reverse. -/

section Gate

/-- A-E.1/E-D5's displayed body, verbatim, for refutation only. -/
@[reducible] private def ladderState_wf_inferInstance {W : Type*} (r : WellFoundedRelation W) :
    WellFoundedRelation (LadderState W) :=
  letI := r; (inferInstance : WellFoundedRelation (ℕ ×ₗ (ℕ ×ₗ W)))

-- REFUTATION. `inferInstance` yields `sizeOfWFRel` over `instSizeOfDefault` (constant `0`), so
-- the amendment's relation relates NO pair of states whatsoever: it is the empty relation, and
-- all three `rank_decreases_*` lemmas are FALSE against it (not merely unprovable).
example {W : Type*} (r : WellFoundedRelation W) (s s' : LadderState W) :
    ¬ (ladderState_wf_inferInstance r).rel s' s := by
  intro h
  exact Nat.lt_irrefl 0 h

-- POSITIVE. The landed relation relates `(0, (5, ()))` below `(1, (0, ()))`: the degree drops
-- from `1` to `0` while the mass RISES from `0` to `5`. This is precisely the descent the empty
-- relation above cannot certify, and it is `rank_decreases_of_deg_lt`'s content.
example : (ladderState_wf (emptyWf (α := Unit))).rel
    ((0, (5, ())) : LadderState Unit) ((1, (0, ())) : LadderState Unit) :=
  rank_decreases_of_deg_lt _ (by decide)

-- LEXICOGRAPHIC, not symmetric: the same pair in reverse is NOT related, because the first
-- component dominates (a mass drop cannot buy a degree rise).
example : ¬ (ladderState_wf (emptyWf (α := Unit))).rel
    ((1, (0, ())) : LadderState Unit) ((0, (5, ())) : LadderState Unit) := by
  intro h
  rcases Prod.lex_def.mp h with h1 | ⟨h1, -⟩
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)

end Gate

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.LadderState
#print axioms Uniformity.Density.Ladder.ladderState_wf
#print axioms Uniformity.Density.Ladder.rank_decreases_of_deg_lt
#print axioms Uniformity.Density.Ladder.rank_decreases_of_mass_lt
#print axioms Uniformity.Density.Ladder.rank_decreases_of_sec

end AxCheck
