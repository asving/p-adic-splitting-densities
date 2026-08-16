/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E19
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Uniformity.ChapE.E20 — the read's induction engine: termination and exhaustion

**Chapter E, NODE E.20** [theorem] (`blueprint/CHAP-E_sigma_ladder.md` §4), ENV-E1.

`EFF.T2.31` clause 6 says the recursive read of a key-free block terminates and exhausts: "Each
transition preserves or partitions roots and transports products, so induction gives exhaustion
as well as termination". This node lands the **induction engine** behind that clause, abstractly:
a transition system on E.19's `(RANK)` states in which

* every non-terminal state steps to a FINITE set of successors (`step s : Finset _`),
* each successor has strictly smaller rank (`hdec`, E.19's relation — the six transition checks
  of `EFF.T2.27` are the instances' job), and
* a **conserved weight** `wt` satisfies `Σ_{s' ∈ step s} wt s' = wt s` at every non-terminal
  state (`hcons` — the root-partition bookkeeping, `EFF.T2.27`'s "preserve or partition roots",
  which the rank-descent node E.19 deliberately does NOT supply),

produces from any `s₀` a multiset of terminal states whose total weight is `wt s₀`.

## ⚠ WHAT THE SIGNED TYPE DOES AND DOES NOT CARRY (honesty disclosure)

The blueprint STATEMENT names three clauses. The signed SIGNATURE — transcribed here
byte-for-byte from `leanspec/Leanspec/ChapE.lean` — carries **(i) and (ii) fused**: the produced
`leaves` is a `Multiset`, i.e. a finite object, and that IS the formal content of "every read
tree from `s₀` is FINITE" at this abstraction (the tree itself is not modelled — only its leaf
multiset); `(leaves.map wt).sum = wt s₀` is clause (ii), exhaustion. **Clause (iii)** ("at every
terminal the `(e, f)`-increments multiply along the path, via E.06") is **NOT in the signed type
and is NOT proved here** — it is E.06's composition law, applied by consumers at their own
instantiation. A consumer that cites E.20 for a multiplicativity fact is citing something this
file does not contain.

Two further honest readings of the type:

* `hcons` is demanded at EVERY non-terminal state, not merely at states reachable from `s₀`.
  That is the signed (stronger) hypothesis; it is what instances supply anyway.
* Nothing here says `leaves` is nonempty, that the read tree is unique, or that distinct leaves
  are distinct states. `Multiset` is the right target precisely because repeated leaves are
  expected.

## ⚠ SCHEMA HONESTY (transcribed from the blueprint)

This node is the INDUCTION ENGINE, not the full clause 6. Instantiating `step` with the actual
four-case read requires, per state, that transition's input suite — `(LB1)` at level-one clause-4
states (E.39), `(MP1)` at level-one recentered-key peels (E.40), the S1.8B/S1.8C discharges at
level two (E.42/E.43), `(RISE)`/`(REF-HT)` at recenterings (E.55/E.56 layer), and the α-refine
finiteness folded into `W`'s well-foundedness (`EFF.T2.26`'s instance table). The instantiation
map is E.22/E.23's obligation tables. The conditionality is exactly `EFF.T2.31`'s: "Full carrier
suite, including `(SEC-RANK)` and `(RISE)`; `(LB1)` when level-one clause 4 constructs blocks;
`(MP1)` for a level-one clause-5 peel at a recentered key."

## ⚠ ORDERING NOTE (A-E.1/E-D5) — DISCHARGED

The blueprint forbids landing E.20 against an `axiom`-stubbed `ladderState_wf`: with an opaque
relation the statement is about an unspecified relation and is unprovable. This file imports
`Uniformity.ChapE.E19`, where `ladderState_wf` carries its real `Prod.Lex` body (and where the
amendment's own `inferInstance` body is machine-refuted as the EMPTY relation). So the ordering
condition is met, and `hdec` here is a hypothesis about the genuine lexicographic order — the
gate below exhibits states it actually relates.

## Proof

Well-founded induction on `s₀` along `(ladderState_wf r).wf`. At a terminal state take
`leaves := {s₀}`. At a non-terminal state, `hdec` puts every `s' ∈ step s` below `s`, so the
inductive hypothesis chooses a leaf multiset `L s'` per successor (`choose!`); the answer is
`(step s).val.bind L`. Membership is `Multiset.mem_bind`; the weight telescopes by
`Multiset.map_bind` + `Multiset.sum_bind`, after `Multiset.map_congr` rewrites each
`((L s').map wt).sum` to `wt s'`, leaving exactly `hcons`.

DEPENDS: E.19 (`LadderState`, `ladderState_wf`, and — in the gate — `rank_decreases_of_deg_lt`)
· mathlib `WellFounded.induction`, `Multiset.mem_bind`, `Multiset.map_bind`,
`Multiset.sum_bind`, `Multiset.map_congr`.

SOURCE: `EFF.T2.31` clause 6 + DERIVATION ("Each transition preserves or partitions roots and
transports products, so induction gives exhaustion as well as termination"); `EFF.T2.27` (the
well-founded induction and its insufficiency caveat — here `hcons` is the extra input);
`EFF.T2.44` (the S-6 GO's shape: master = induction over the six transitions).

TEETH: S7 finite-refinement/root-preservation attacks → **Lean theorem** (the engine); Q1's
"1,587/1,587 members decided" is the instance evidence at `n = 8` (E.23). The gate below adds the
vacuity teeth this abstraction invites: a CONCRETE branching system (weight genuinely
partitioned, two successors, both of strictly smaller rank) at which the engine returns a
nontrivial exhaustion identity, and a machine-checked demonstration that `hcons` is load-bearing
— the all-empty-`step` system satisfies `hdec` vacuously and the conclusion is FALSE for it.

ENVIRONMENT: ENV-E1.

## Status

Sorry-free. `read_terminates_exhausts` reports the Lean-core triple only. The signature was
transcribed from the signed stub with binder names, order and explicitness unchanged.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

-- The signed SIGNATURE carries `[DecidablePred terminal]`, and the landed proof does not need
-- it (`by_cases` uses `Classical`). The instance is KEPT — the statement-fence forbids trimming
-- a signed binder — and the linter that would ask for its removal is switched off here only.
set_option linter.unusedDecidableInType false in
/-- **E.20** Termination and exhaustion of the recursive read (`EFF.T2.31` clause 6, schema
form): a rank-decreasing, weight-conserving transition system on `(RANK)` states yields, from any
start, a finite multiset of terminal states of total weight `wt s₀`. -/
theorem read_terminates_exhausts {W : Type*} (r : WellFoundedRelation W)
    (step : LadderState W → Finset (LadderState W))
    (terminal : LadderState W → Prop) [DecidablePred terminal]
    (wt : LadderState W → ℕ)
    (hdec : ∀ s, ¬ terminal s → ∀ s' ∈ step s, (ladderState_wf r).rel s' s)
    (hcons : ∀ s, ¬ terminal s → ∑ s' ∈ step s, wt s' = wt s) :
    ∀ s₀, ∃ leaves : Multiset (LadderState W),
      (∀ l ∈ leaves, terminal l) ∧ (leaves.map wt).sum = wt s₀ := by
  intro s₀
  refine (ladderState_wf r).wf.induction
    (C := fun s => ∃ leaves : Multiset (LadderState W),
      (∀ l ∈ leaves, terminal l) ∧ (leaves.map wt).sum = wt s) s₀ ?_
  intro s ih
  by_cases h : terminal s
  · -- terminal: the state is its own single leaf
    exact ⟨{s}, by simpa using h, by simp⟩
  · -- non-terminal: recurse into every successor, then concatenate the leaf multisets
    have key : ∀ s' ∈ step s, ∃ L : Multiset (LadderState W),
        (∀ l ∈ L, terminal l) ∧ (L.map wt).sum = wt s' :=
      fun s' hs' => ih s' (hdec s h s' hs')
    choose! L hL1 hL2 using key
    refine ⟨(step s).val.bind L, ?_, ?_⟩
    · intro l hl
      obtain ⟨s', hs', hl'⟩ := Multiset.mem_bind.mp hl
      exact hL1 s' hs' l hl'
    · rw [Multiset.map_bind, Multiset.sum_bind]
      have hmap : Multiset.map (fun a => (Multiset.map wt (L a)).sum) (step s).val
          = Multiset.map wt (step s).val :=
        Multiset.map_congr rfl (fun x hx => hL2 x hx)
      rw [hmap]
      exact hcons s h

/-! ## Gate (executed `example`s, not blueprint declarations)

A concrete branching read over `W = Unit`. States are `gSt d m = (d, (m, ()))`; the weight is the
degree `d`; a state is terminal when `d ≤ 1`; a state of degree `d ≥ 2` splits into the two
successors `gSt 1 0` and `gSt (d-1) 1`, whose degrees `1 + (d-1) = d` PARTITION the parent's
weight and whose second components `0 ≠ 1` keep them distinct in the `Finset` (a partition into
two equal halves collapsed by `Finset` dedup would silently break conservation — that is why the
mass component is used to separate them).

The three checks are: the system satisfies `hcons` (weight genuinely partitioned, not merely
transported); it satisfies `hdec` against E.19's real relation; and the engine applied to it
delivers an exhaustion identity at total weight `5`. The fourth check refutes the engine minus
`hcons`. -/

section Gate

private instance instDecEqGateState : DecidableEq (LadderState Unit) :=
  inferInstanceAs (DecidableEq (ℕ × ℕ × Unit))

/-- Gate state constructor: degree `a`, mass `b`, trivial secondary rank. -/
private def gSt (a b : ℕ) : LadderState Unit := toLex (a, toLex (b, ()))

/-- Gate weight: the degree component. -/
private def gWt : LadderState Unit → ℕ := fun s => s.1

/-- Gate terminal predicate: degree `≤ 1`. -/
private def gTerminal : LadderState Unit → Prop := fun s => s.1 ≤ 1

private instance : DecidablePred gTerminal := fun s => inferInstanceAs (Decidable (s.1 ≤ 1))

/-- Gate transition: a degree-`d` state with `d ≥ 2` splits into degrees `1` and `d - 1`. -/
private def gStep : LadderState Unit → Finset (LadderState Unit) := fun s =>
  if 2 ≤ s.1 then ({gSt 1 0, gSt (s.1 - 1) 1} : Finset (LadderState Unit)) else ∅

private theorem gStep_ne {s : LadderState Unit} : gSt 1 0 ≠ gSt (s.1 - 1) 1 := by
  intro hEq
  have h0 : (0 : ℕ) = 1 := congrArg (fun z : LadderState Unit => (Prod.snd z).1) hEq
  exact absurd h0 (by decide)

private theorem gCons (s : LadderState Unit) (h : ¬ gTerminal s) :
    ∑ s' ∈ gStep s, gWt s' = gWt s := by
  have h2 : 2 ≤ s.1 := by
    have h1 : ¬ (s.1 ≤ 1) := h
    omega
  rw [gStep, if_pos h2, Finset.sum_pair gStep_ne]
  change (1 : ℕ) + (s.1 - 1) = s.1
  omega

private theorem gDec (s : LadderState Unit) (h : ¬ gTerminal s) :
    ∀ s' ∈ gStep s, (ladderState_wf (emptyWf (α := Unit))).rel s' s := by
  have h2 : 2 ≤ s.1 := by
    have h1 : ¬ (s.1 ≤ 1) := h
    omega
  intro s' hs'
  rw [gStep, if_pos h2] at hs'
  refine rank_decreases_of_deg_lt _ ?_
  rcases Finset.mem_insert.mp hs' with rfl | hs'
  · change (1 : ℕ) < s.1
    omega
  · rw [Finset.mem_singleton.mp hs']
    change (s.1 - 1 : ℕ) < s.1
    omega

-- POSITIVE. The engine at the concrete branching system, started at degree `5`: it returns
-- leaves that are all terminal and whose degrees sum to `5`. Non-vacuous — the start state is
-- NOT terminal, and the successors' weights are genuinely partitioned by `gCons`.
example : ∃ leaves : Multiset (LadderState Unit),
    (∀ l ∈ leaves, gTerminal l) ∧ (leaves.map gWt).sum = 5 :=
  read_terminates_exhausts (emptyWf (α := Unit)) gStep gTerminal gWt gDec gCons (gSt 5 0)

-- The start state really is non-terminal (so the positive check is not the terminal branch).
example : ¬ gTerminal (gSt 5 0) := by
  change ¬ ((5 : ℕ) ≤ 1)
  decide

-- SHARPNESS. `hcons` is load-bearing. The all-empty-`step` system satisfies `hdec` vacuously
-- (nothing to check), and for it the engine's CONCLUSION is false at `gSt 5 0`: every terminal
-- state of that system has weight `0`, so no multiset of them can weigh `5`.
example (s : LadderState Unit) (_h : ¬ (s.1 = 0)) :
    ∀ s' ∈ (∅ : Finset (LadderState Unit)), (ladderState_wf (emptyWf (α := Unit))).rel s' s := by
  simp

example : ¬ ∃ leaves : Multiset (LadderState Unit),
    (∀ l ∈ leaves, l.1 = 0) ∧ (leaves.map gWt).sum = gWt (gSt 5 0) := by
  rintro ⟨leaves, h1, h2⟩
  have hz : (leaves.map gWt).sum = 0 := by
    refine Multiset.sum_eq_zero ?_
    intro x hx
    obtain ⟨l, hl, rfl⟩ := Multiset.mem_map.mp hx
    exact h1 l hl
  rw [hz] at h2
  have h5 : (0 : ℕ) = 5 := h2
  omega

end Gate

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.read_terminates_exhausts

end AxCheck
