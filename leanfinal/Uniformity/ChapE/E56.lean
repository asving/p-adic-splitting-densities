/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E10
import Uniformity.ChapE.E38

/-!
# Uniformity.ChapE.E56 — LEMMA HE7-13: the same-residue kill, and the chain invariant

**Chapter E, NODE E.56** [theorem] [fresh] (`blueprint/CHAP-E_sigma_ladder.md` §8), ENV-E2. Two
signed declarations, both landed here:

* **(i) `same_digit_rises`** — the per-step jump: two values at the SAME finite height with the
  SAME digit have a difference of STRICTLY greater height. This is LEMMA HE7-13's own mechanism
  per root (`EFF.HE7.96`(b): *"a difference of two elements of the same dv₂ and the SAME residue"*),
  and HE7-13′(b) at the class level.
* **(ii) `chain_invariant`** — the packaging that RESOLVES HE7's OPEN-CALL 3. Along a refine chain
  whose step `j` increases the slope (clause (i) applied at the refined read), the slope sequence
  is globally strictly monotone AND the increments' heights are pairwise distinct.

## Why (ii) is the resolution of the mutual induction, and not a restatement of it

`EFF.HE7.44`(d)'s `[r3]` rider and LEMMA HE7-13 (`EFF.HE7.45`, `[r2]`) are stated in the corpus as
inducting TOGETHER along the chain — the spec's RESOLUTION TRACE flags this as OPEN-CALL 3,
*"Flagged, not repaired"*. The Lean resolution is structural, and it is a DAG statement rather than
a new mathematical step:

* E.56 (this node) takes the STEP-LOCAL increase `hstep : lam j < lam (j+1)` — which is what the
  re-read at the refined key supplies, through clause (i) at every root plus the polygon re-read
  (the instances' E.23 row, licensed by E.38(iii)/E.42) — and produces the two GLOBAL facts;
* E.38 (`slot_fold`) consumes pairwise distinctness as a hypothesis (`hdist`);
* E.55 (`refine_chain_finite_of_key`, `E55.lean`) consumes strict monotonicity as a hypothesis
  (`hmono`).

No cycle survives: the induction hypothesis is ONE invariant, discharged here once
(`strictMono_nat_of_lt_succ`), and the two consumers only read it off. ⚠ What this node does NOT
do is derive `hstep`: the per-step increase is instance content (the refined read), and a fleet
agent proving `hstep` from the carrier alone has left the chapter.

## The carrier law `hsame` is a HYPOTHESIS, deliberately

`hsame` is E.10's missing residue law — the same protocol as E.35's `hneg` (see `E35.lean`'s note):
the corpus uses it silently, `SlotCarrier` does not carry it as a field, and the RE-PLAN rule
(GC-5) promotes it to an E.10 field only once three or more consumers thread it. Consumers so far:
E.56 (here), E.58 (`refine_quartet`, the per-class quartet), E.35's sibling clause. Threading, not
promoting: a field addition to a landed structure is amendment-level.

Clause (i) is therefore, honestly, a NAMING node: its proof is `exact hsame …`. That is the whole
point — the law gets a name, a promotion count, and a citation, and every consumer of "the
same-residue kill" points at one declaration instead of re-stating the law inline.

## Faithfulness

Three recasts to check on the chapter cross-read:

* *(i) is stated at EQUAL finite heights, at the level of the carrier's exact height and digit* —
  not per root. The corpus's mechanism is per root (`EFF.HE7.96`(b)); the carrier level is where
  the ladder's `hgt`/`dig` live, and `hsame` is exactly the transported form. No root, no
  valuation of a residue field, and no completion appears in the statement.
* *(ii)'s distinctness is `C.hgt (w i) ≠ C.hgt (w j)`, an inequality of `WithTop ℤ` values*, which
  is what E.38's `hdist` wants — NOT `lam i ≠ lam j`. The two are equivalent under `hh`, and the
  proof goes through the cast's injectivity; stating it in `lam` would force every consumer to
  re-derive the transport.
* *no finiteness is claimed here.* (ii) says the slopes increase and the heights differ; that an
  infinite such chain is impossible is E.55's theorem, and it needs the completeness hypothesis
  which this node does not take. Reading (ii) as termination is the error the §14 cross-read
  entry warns about.

**DEPENDS.** E.10 (`SlotCarrier`: `hgt`, `dig`), E.38 (`slot_fold` — the consumer of clause (ii)'s
distinctness; imported here only so the bridge lemma below can be stated against its exact
`hdist` shape). E.35 is the sibling forcing node (`hneg`'s protocol); it is cited, not imported.

**SOURCE.** `EFF.HE7.45` (LEMMA HE7-13 `[r2]`: *"the strict slope increase along the refine chain —
DERIVED, not assumed"*); `EFF.HE7.44`(d) (the `[r3]` rider: *"the values dv₂(w_i) are pairwise
DISTINCT (they are the strictly increasing slopes … the two lemmas induct together along the
chain)"*, with the OPEN-CALL 3 flag); `EFF.HE7.96`(b) (the per-root mechanism).

**TEETH.** PE2's 2-step chains (634/634 members, independent instrument) and `he7annex_supp.py` P3
(0 floor violations across 148 refines) — machine evidence; the Lean leg is the PACKAGING, and the
per-step supply stays instance content.

## Status

Sorry-free, axiom-free (Lean core only: `propext`, `Classical.choice`, `Quot.sound`).
-/

namespace Uniformity.Density.Ladder

/-- **E.56 (i) — the per-step jump / same-residue kill** (LEMMA HE7-13's own mechanism,
`EFF.HE7.96`(b); HE7-13′(b)). At a shared finite height, equal digits force the difference strictly
higher.

`hsame` is the carrier law, taken as a hypothesis (E.35's `hneg` protocol; promotion is RE-PLAN's
call, not this node's). -/
theorem same_digit_rises {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K)
    (hsame : ∀ (a b : Polynomial O) (k : ℤ), C.hgt a = (k : WithTop ℤ) →
      C.hgt b = (k : WithTop ℤ) → C.dig a = C.dig b → (k : WithTop ℤ) < C.hgt (a - b))
    {a b : Polynomial O} {k : ℤ} (ha : C.hgt a = (k : WithTop ℤ))
    (hb : C.hgt b = (k : WithTop ℤ)) (hd : C.dig a = C.dig b) :
    (k : WithTop ℤ) < C.hgt (a - b) :=
  hsame a b k ha hb hd

/-- **E.56 (ii) — the chain invariant** (HE7-12(d)'s `[r3]` rider and HE7-13, inducting together:
`EFF.HE7.44`(d)/`EFF.HE7.45`, OPEN-CALL 3 resolved structurally).

From the STEP-LOCAL slope increase — what the re-read at the refined key supplies — the chain's
slopes are globally strictly monotone and the increments' heights are pairwise distinct. E.55
consumes the first, E.38 the second; the induction happens once, here. -/
theorem chain_invariant {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K) (w : ℕ → Polynomial O) (lam : ℕ → ℤ)
    (hh : ∀ j, C.hgt (w j) = (lam j : WithTop ℤ))
    (hstep : ∀ j, lam j < lam (j + 1)) :
    StrictMono lam ∧ ∀ i j, i < j → C.hgt (w i) ≠ C.hgt (w j) := by
  have hmono : StrictMono lam := strictMono_nat_of_lt_succ hstep
  refine ⟨hmono, ?_⟩
  intro i j hij hcon
  rw [hh i, hh j] at hcon
  exact absurd (WithTop.coe_injective hcon) (hmono hij).ne

/-- **Helper (not a blueprint node): the bridge to E.38.** The first `n` increments of a chain,
listed in order, are pairwise distinct in height — the exact `hdist` hypothesis of `slot_fold`
(`E38.lean`). This is what clause (ii) is FOR; keeping the bridge here means no consumer re-derives
the list form. -/
theorem chain_invariant_pairwise {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K) (w : ℕ → Polynomial O)
    (hdist : ∀ i j, i < j → C.hgt (w i) ≠ C.hgt (w j)) (n : ℕ) :
    ((List.range n).map w).Pairwise fun a b => C.hgt a ≠ C.hgt b :=
  (List.pairwise_lt_range (n := n)).map w fun a b hab => hdist a b hab

end Uniformity.Density.Ladder

/-! ## Gate: the invariant on a concrete chain, and the E.38 hand-off

Small unit tests (not blueprint nodes). They fire the two clauses at data, so that a later edit
that silently changes a statement's shape breaks the build. -/

section Gate

open Uniformity.Density.Ladder

/-- The arithmetic chain `lam j = j` satisfies the step hypothesis, so the invariant fires: the
slopes are strictly monotone and, at any carrier realising them, the heights are pairwise
distinct. -/
example {O : Type} [CommRing O] {K : Type} [Field K] (C : SlotCarrier O K)
    (w : ℕ → Polynomial O) (hh : ∀ j, C.hgt (w j) = ((j : ℤ) : WithTop ℤ)) :
    StrictMono (fun j : ℕ => (j : ℤ)) ∧ ∀ i j, i < j → C.hgt (w i) ≠ C.hgt (w j) :=
  chain_invariant C w (fun j => (j : ℤ)) hh (fun j => by push_cast; omega)

/-- The hand-off shape: clause (ii)'s conclusion, listed, IS `slot_fold`'s `hdist`. -/
example {O : Type} [CommRing O] {K : Type} [Field K] (C : SlotCarrier O K)
    (w : ℕ → Polynomial O) (lam : ℕ → ℤ)
    (hh : ∀ j, C.hgt (w j) = (lam j : WithTop ℤ)) (hstep : ∀ j, lam j < lam (j + 1)) (n : ℕ) :
    ((List.range n).map w).Pairwise fun a b => C.hgt a ≠ C.hgt b :=
  chain_invariant_pairwise C w (chain_invariant C w lam hh hstep).2 n

/-- Clause (i) is the carrier law under its own name: supplied `hsame`, it fires at any equal
height and digit. -/
example {O : Type} [CommRing O] {K : Type} [Field K] (C : SlotCarrier O K)
    (hsame : ∀ (a b : Polynomial O) (k : ℤ), C.hgt a = (k : WithTop ℤ) →
      C.hgt b = (k : WithTop ℤ) → C.dig a = C.dig b → (k : WithTop ℤ) < C.hgt (a - b))
    (a : Polynomial O) (k : ℤ) (ha : C.hgt a = (k : WithTop ℤ)) :
    (k : WithTop ℤ) < C.hgt (a - a) :=
  same_digit_rises C hsame ha ha rfl

end Gate

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.same_digit_rises
#print axioms Uniformity.Density.Ladder.chain_invariant
#print axioms Uniformity.Density.Ladder.chain_invariant_pairwise

end AxCheck
