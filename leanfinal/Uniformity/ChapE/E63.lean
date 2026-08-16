/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E05
import Uniformity.ChapE.E61
import Uniformity.ChapE.E62

/-!
# Uniformity.ChapE.E63 — `DeepTwistConjunct`, the packaged Display-A conjunct, and its
shallow-ladder vacuity

**Chapter E, NODE E.63** [lemma] [fresh] (`blueprint/CHAP-E_sigma_ladder.md` §9 — the
`(H-VARTHETA-RES)_i ∧ 𝒲_(≤i)` indexed carriers). ENV-E1 (plus chapter D's arena, imported
through E.61/E.62).

Two declarations, per the signed SIGNATURE:

* `DeepTwistConjunct` — Display A's `∀ i ≥ 3, (H-VARTHETA-RES)_i ∧ 𝒲_(≤i)` as ONE named `Prop`,
  so that chapter I's Display-A block (through E.24's `LadderSupply`) consumes a name rather
  than an inline quantifier;
* `deepTwist_vacuous_shallow` — the vacuity shadow: on a ladder of depth `≤ 2` (base plus at
  most one rung) EVERY index the conjunct quantifies over lies strictly above the ladder's top
  level, so the conjunct constrains nothing there.

## What the conjunct says, and at which data

E.61's `VarthetaRes` and E.62's `WFrame` were TYPED at the GC-13/GC-14 resolution (both landed
2026-08-16) against chapter D's landed carriers, so both now carry level-indexed instantiation
data. This node discharges the consumer obligation those two files flagged: it THREADS THE SAME
DATA through both legs, in D.63's own spelling and argument order

```
DeepTwistConjunct v ρ q A R w   ↔   ∀ i ≥ 3, HVarthetaRes … (v i) (ρ i) (q i)
                                              ∧ ⋀_{3 ≤ j ≤ i} GentowW (A j) (q j) (R j) (w j)
```

— checked below as a term, not asserted in a comment. In particular **one `q` family serves both
legs**: `q j` is the level-`j` fixed use-height `u_{j+1}` in D.62 and in D.44 alike, and chapter
D's own intended-instantiation unit test (`ChapD/D63.lean`, the example under
`VarthetaWConjunct`) shares it exactly this way. Splitting it into two independent families here
would let a consumer satisfy the HVR leg at one set of use-heights and the `𝒲` leg at another,
which is not the corpus's conjunct.

**Nothing here discharges anything.** `[GENTOW5-W(i)]` is OPEN at `i ≥ 3` (chapter C's C.89) and
`(H-VARTHETA-RES)_i` is a CARRY row (ledger HYP.57/HYP.63); this file contains no theorem
concluding `DeepTwistConjunct …`. Its terminal disposition is chapter I's (DISCHARGE NODE or
LITERATURE CITE), per the Part V owner ruling.

## The signature delta against the committed stub (honest record)

Committed stub (`leanspec/Leanspec/ChapE.lean` §9):

```lean
def DeepTwistConjunct : Prop := ∀ i, 3 ≤ i → VarthetaRes i ∧ WFrame i
axiom deepTwist_vacuous_shallow (Λ : LadderData) (h : Λ.rungs.length ≤ 1) :
    ∀ i, 3 ≤ i → Λ.rungs.length + 1 < i ∨ True
```

Two deltas, both flagged in the blueprint itself:

1. **the level data is threaded** (parameters `v ρ q A R w`), forced by E.61/E.62's typing — the
   stub's argument-free spelling refers to the `supplied : True` sockets that no longer exist.
   Frozen and preserved: the NAME, the `∀ i, 3 ≤ i → _ ∧ _` shape, the order of the two legs.
2. **the `∨ True` is dropped from the theorem's conclusion.** The blueprint's ⚠ NODE-KIND NOTE
   authorises this in terms — *"The stub stage may tighten the statement to the honest consumer
   form"* — and this repo's honesty invariant demands it: a landed theorem whose conclusion is
   `_ ∨ True` is satisfied by `Or.inr trivial` and records nothing. The tightened statement
   `∀ i, 3 ≤ i → Λ.rungs.length + 1 < i` is TRUE (`length + 1 ≤ 2 < 3 ≤ i`), strictly stronger
   than the signed one, and the signed one is re-derived from it immediately below, so any
   consumer written against the signed type is still served.

## Faithfulness

**⚠ Mandatory, trust-boundary definition** (parent CLAUDE.md trust boundary; one definition,
`DeepTwistConjunct`). Three recasts to check on the chapter cross-read:

* *the two legs are indexed differently ON PURPOSE.* The HVR leg is read at the single level `i`;
  the `𝒲` leg is CUMULATIVE inside E.62 (`Wle`, `3 ≤ j ≤ i`). Flattening either into the other is
  the conflation `EFF.T5.10` forbids, and D.63's fence repeats it. The packaging here changes
  neither.
* *`Λ.rungs.length + 1` is the ladder's TOP LEVEL, not its rung count.* E.05's `LadderData` is a
  base rung (levels 1 → 2 in corpus letters, threshold `0`) plus `rungs`; a ladder with
  `rungs.length ≤ 1` therefore reaches level `≤ 2`. That is the arithmetic content of the
  vacuity clause, and it is why the bound is `length + 1` and not `length`.
* *the vacuity clause is about INDICES, not about truth.* It says the conjunct's quantifier never
  reaches a shallow ladder's levels; it does NOT say `DeepTwistConjunct` holds, and it says
  nothing whatever at depth `≥ 3`, which is exactly where the carried hypothesis lives. The
  `n`-reading — depth `≥ 3` unreachable below `n = 16` — is E.64's, not this node's.

## DEPENDS

E.61 (`VarthetaRes`, typed against D.62's A-D.2 sitewise carrier), E.62 (`WFrame`, typed against
D.55's `Wle` at D.44's `GentowW`), E.05 (`LadderData`) — all imported, so every binding below is
a checked term. E.60's `μ₂ ≤ 3` gate and E.64's `n ≥ 16` arithmetic are the two other halves of
the same record; they are cited, not imported, and nothing here restates them.

## SOURCE

`EFF.HE7.114` (R1-d's level-3 sentence: "the first level at which any new symbol (a `ϑ_t ≠ 1` …)
can appear is level 3, unreachable below `n = 16` (THEOREM HE7.C)"); `EFF.HE7.108`(iv); ledger
Display A (the `∀ i ≥ 3` indexing, degree-indexed per CHAP-H H-7's precedent); CHAP-I NODE I.10's
dated note (the A-D.2 consumption fence, inherited through E.61).

**TEETH.** none (packaging). The RECORD this node carries is that consumers at `n ≤ 15` never
instantiate the conjunct (E.64 + E.60's `μ₂ ≤ 3` gate).

**ENVIRONMENT.** ENV-E1.

## Status

Sorry-free, axiom-free (Lean core only). No theorem here concludes `DeepTwistConjunct` at any
data: the conjunct is carried, not discharged.
-/

namespace Uniformity.Density.Ladder

open Uniformity.Density.Gauge

/-- **NODE E.63** — Display A's deep-twist conjunct, packaged under one name:
`∀ i ≥ 3, (H-VARTHETA-RES)_i ∧ 𝒲_(≤i)`, at the level-indexed data `(v, ρ, q)` of E.61 and
`(A, q, R, w)` of E.62 — ONE use-height family `q` serving both legs, as in chapter D's own
intended instantiation (D.63).

A CARRIER: `[GENTOW5-W(i)]` is open at `i ≥ 3` (C.89) and `(H-VARTHETA-RES)_i` is a ledger CARRY
row (HYP.57/HYP.63); nothing in this chapter discharges it, and its terminal disposition is
chapter I's. -/
def DeepTwistConjunct {G : Type*} [CommGroup G] {K : Type*} [Field K] {L : Type*} [Field L]
    [Algebra K L] {N : NormSection G} (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
    (A : ℕ → GaugeArena G K N) (R : ℕ → G → K) (w : ℕ → Kˣ) : Prop :=
  ∀ i, 3 ≤ i → VarthetaRes G K L N v ρ q i ∧ WFrame A q R w i

/-- The unfolding, as a unit test rather than a comment: the packaged conjunct IS, level by
level, chapter D's sitewise `(H-VARTHETA-RES)` at the level-`i` data together with the cumulative
w-frame through level `i`. Nothing is discharged — this is a shape statement at arbitrary
supplied data. -/
example {G : Type*} [CommGroup G] {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]
    {N : NormSection G} {v : ℕ → (G →* Multiplicative ℤ)}
    {ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ} {q : ℕ → ℤ} {A : ℕ → GaugeArena G K N}
    {R : ℕ → G → K} {w : ℕ → Kˣ} :
    DeepTwistConjunct v ρ q A R w ↔
      ∀ i, 3 ≤ i → HVarthetaRes G K L N (v i) (ρ i) (q i)
        ∧ ∀ j, 3 ≤ j → j ≤ i → GentowW (A j) (q j) (R j) (w j) :=
  ⟨fun H i hi => ⟨(H i hi).1.supplied, (H i hi).2.supplied⟩,
   fun H i hi => ⟨⟨(H i hi).1⟩, ⟨(H i hi).2⟩⟩⟩

/-- The consumption route, as a unit test: the packaged conjunct is exactly `∀ i ≥ 3` of D.63's
`VarthetaWConjunct` at the intended families — the shape chapter I's Display-A block consumes
(through E.24). It asserts neither leg. -/
example {G : Type*} [CommGroup G] {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]
    {N : NormSection G} {v : ℕ → (G →* Multiplicative ℤ)}
    {ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ} {q : ℕ → ℤ} {A : ℕ → GaugeArena G K N}
    {R : ℕ → G → K} {w : ℕ → Kˣ} :
    DeepTwistConjunct v ρ q A R w ↔
      ∀ i, 3 ≤ i → VarthetaWConjunct (fun j => HVarthetaRes G K L N (v j) (ρ j) (q j))
        (fun j => GentowW (A j) (q j) (R j) (w j)) i :=
  ⟨fun H i hi => ⟨(H i hi).1.supplied, (H i hi).2.supplied⟩,
   fun H i hi => ⟨⟨(H i hi).1⟩, ⟨(H i hi).2⟩⟩⟩

/-- **NODE E.63, the vacuity shadow.** On a ladder with at most one rung above the base — i.e.
of depth `≤ 2`, the levels `1, 2` that E.29/E.33's level-2 machinery already carries WITHOUT this
conjunct (E.61's `τ₁ ≡ 1` note) — every index the Display-A conjunct quantifies over lies
strictly above the ladder's top level `rungs.length + 1`. So `DeepTwistConjunct` imposes no
condition readable on such a ladder.

⚠ This is an INDEX statement: it does not assert `DeepTwistConjunct`, and it says nothing at
depth `≥ 3`, where the conjunct is live and undischarged. *[Tightened from the signed
`… < i ∨ True`, as the blueprint's ⚠ NODE-KIND NOTE authorises; the signed form is re-derived
immediately below.]* -/
theorem deepTwist_vacuous_shallow (Λ : LadderData) (h : Λ.rungs.length ≤ 1) :
    ∀ i, 3 ≤ i → Λ.rungs.length + 1 < i := by
  intro i hi
  omega

/-- The signed stub statement, re-derived from the tightened theorem: any consumer written
against the blueprint's literal `… ∨ True` conclusion is served. -/
example (Λ : LadderData) (h : Λ.rungs.length ≤ 1) :
    ∀ i, 3 ≤ i → Λ.rungs.length + 1 < i ∨ True :=
  fun i hi => Or.inl (deepTwist_vacuous_shallow Λ h i hi)

/-- The hypothesis class is INHABITED (so the vacuity clause is not a statement about nothing):
the `n = 8` frame's ladder — base `(e₁, f₁, h, 0) = (2, 1, 1, 0)` plus the single level-2 rung
`(ℓ, d_r, u, T₂) = (2, 1, 5, 2)`, chained by `T₂ = base.nextT = 2` — has `rungs.length = 1`. -/
example : ∃ Λ : LadderData, Λ.rungs.length ≤ 1 ∧ Λ.rungs.length = 1 :=
  ⟨{ base := RungDatum.mk 2 1 1 0 (by norm_num) (by norm_num) (by decide) (by norm_num)
     rungs := [RungDatum.mk 2 1 5 2 (by norm_num) (by norm_num) (by decide) (by norm_num)]
     hbase := rfl
     hchain := List.IsChain.cons_cons rfl (List.IsChain.singleton _) },
   ⟨le_refl 1, rfl⟩⟩

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.DeepTwistConjunct
#print axioms Uniformity.Density.Ladder.deepTwist_vacuous_shallow

end AxCheck
