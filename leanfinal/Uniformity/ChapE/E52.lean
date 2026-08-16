/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E50

/-!
# Uniformity.ChapE.E52 — `he7a_prime_schema`: THEOREM HE7.A′ (the n = 8 bite decided)

**Chapter E, NODE E.52** [theorem] (`blueprint/CHAP-E_sigma_ladder.md` §7 — the σ dictionary and
the transport laws), ENV-E1.

At the n = 8 frame (`D″ = 4`, `K₂ = K = F_q`, `T₂ = 2u`, `μ₂ = 2`) the read of a member is a
trajectory through E.49's six-row dictionary: rows 1–4 and row 6 decide on the spot, row 5 is the
α-refine pointer, which re-reads at the refined key `Ψ − w`. THEOREM HE7.A′ says the bite IS
decided — the loop cannot spin forever, and whatever it exits on emits one of the three σ-letters
`⟨{(8,1)}⟩`, `⟨{(4,2)}⟩`, `⟨{(4,1),(4,1)}⟩`. This node is that statement in schema form: the
trajectory is a function `read : ℕ → Mu2Row`, its termination is the hypothesis `hterm`, and the
conclusion is the decided σ-value in the three-letter alphabet.

## Where each ingredient comes from (and which of them this file does NOT contain)

* **the refined-key licence** — row 5's re-read is legitimate because the transported §S5 package
  applies at `Ψ − w`: E.38(iii)'s obligation discharged at this frame, folded once by E.42
  (`s18b_fold`). Composed increments stay a single admissible increment, so the re-read is at a
  DEFINITION-HE6-1 key;
* **the termination supply** — the re-read lands at a STRICTLY larger slope (E.56's
  `chain_invariant`) and an infinite strictly-increasing chain is impossible (E.55, at `μ₂ = 2`
  with E.07's bounds). Those two are what a consumer discharges to produce `hterm`; **this file
  takes `hterm` as a hypothesis and proves nothing about the trajectory's dynamics**;
* **the row values** — E.49's `mu2Sigma`, and the alphabet is E.50's `mu2Sigma_alphabet`.

## ⚠ WHY THIS NODE IS NOT BLOCKED, THOUGH E.51 IS

E.51 (the peel-row law, row 6) is BLOCKED-until-resolution: its `hpeel : True` placeholder waits
on chapter C's HE6R1-3 emission record (GC-13), and proving it now would be vacuous. E.52 does
NOT consume E.51's theorem. It reads row 6 through `mu2Sigma .peelRow` — the *dictionary entry*,
landed in E.49 — and through nothing else; the letter that row 6 emits is table content, not a
consequence of E.51. Hence the blueprint's §12 ruling (*"E.52 is explicitly NOT blocked"*), and
hence this file imports E.50/E.49 and NOT E.51. If a later re-sign made the schema depend on the
peel LAW rather than on the peel ROW, that ruling would have to be revisited.

## ⚠ WHAT THE SCHEMA DOES AND DOES NOT PROMISE

The blueprint deliberately does not promise a member-level Lean theorem at n = 8. The trajectory
`read` is an INPUT: nothing here computes a Newton polygon, factors a residual, or identifies
which row an actual member falls in. The member-level HE7.A′ — actual polygon reads producing
`read`, over the E.23 instance suite with gates E.65 — is the certificate layer's job (the
B.79–B.82 pattern at level 2), a POST-blueprint target recorded in §14. What the schema DOES
supply is the composition law the certificate layer needs: *given* a terminating trajectory, the
decided value exists and lies in the three-letter alphabet.

Conditionality, transcribed from `EFF.HE7.62`: "unconditionally" is scoped to the n = 8 box
configuration with `disc f ≠ 0`; the peel leg rests on HE6R1-3 (a chapter-C placeholder); and the
source's three "no …" clauses stand — **no base change, no irreducibility of `Ψ` as a
hypothesis, no order-≥2 citation**. None of the three appears in this statement, which is the
cheapest way to keep them true. The source's own "five-row dictionary" off-by-one (the table has
six rows) is HE7 source defect 6, recorded in §13 and not reproduced here.

## The deciding index is the FIRST exit

The proof takes `Nat.find hterm`, not an arbitrary witness: the decided row is the one the loop
actually stops at, and gate (a) records the minimality — every earlier step is row 5. With an
arbitrary witness the statement would still be true but would describe a different (later) read,
which is not what "the loop terminates, then a decided row" says.

DEPENDS: E.49 (`Mu2Row`, `mu2Sigma`), E.50 (`mu2Sigma_alphabet`) · E.51 (row 6's LAW — cited, and
deliberately NOT consumed: see the not-blocked note) · E.55/E.56 (the termination supply the
hypothesis `hterm` stands for — forward references, cited not imported) · E.38/E.42 (the
refined-key licence — cited not imported; the schema does not re-derive it).

SOURCE: `EFF.HE7.62` (THEOREM HE7.A′, incl. the three "no …" clauses and the
conclusion-not-assumption sentence about the peel stratum); `EFF.HE7.59` (row 5's displayed
upgrade: *"read AT THE REFINED KEY, which LEMMA HE7-12 licenses … strictly larger slope by LEMMA
HE7-13, so the loop terminates (LEMMA HE7-8)"*).

TEETH: Q1 + `he7r1_supp.py` + `he7r2_supp.py` jointly (*"1,587/1,587 members decided … 0
mis-decisions"*) → instance evidence; the schema is a **Lean theorem**.

ENVIRONMENT: ENV-E1.

## Status

Sorry-free, Lean-core axioms only.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- **Helper (not a blueprint node): totality off row 5.** Every row of E.49's dictionary except
the α-refine pointer emits a value. This is the exhaustiveness of `EFF.HE7.58`'s table WITH row 6
(the source's own caveat: *"the exhaustiveness claim holds only WITH row 6"*) in the one form the
schema needs — `mu2Sigma` is `none` exactly at `.refineRow`. -/
private theorem decided_of_ne_refineRow {r : Mu2Row} (hr : r ≠ .refineRow) :
    ∃ v, mu2Sigma r = some v := by
  cases r
  case oneSideHalf => exact ⟨_, rfl⟩
  case oneSideInert => exact ⟨_, rfl⟩
  case oneSideSplit => exact ⟨_, rfl⟩
  case twoSides => exact ⟨_, rfl⟩
  case refineRow => exact absurd rfl hr
  case peelRow => exact ⟨_, rfl⟩

/-- **NODE E.52.** *THEOREM HE7.A′ schema: the n = 8 bite is decided, refine loop included.* The
read trajectory `read` walks E.49's six-row dictionary; `hterm` is the termination supply
(E.55's finiteness + E.56's strict slope increase, at `μ₂ = 2`), and the refined-key re-read is
licensed by E.38(iii)/E.42. Then the loop's FIRST exit (`Nat.find hterm`) is a decided row whose
σ-value lies in the three-letter alphabet (E.50). Row 6 enters through the dictionary ENTRY
`mu2Sigma .peelRow`, never through E.51's blocked law. -/
theorem he7a_prime_schema
    -- the row at refine-step i
    (read : ℕ → Mu2Row)
    -- termination supply (E.55/E.56 at μ₂ = 2)
    (hterm : ∃ i, read i ≠ .refineRow)
    : ∃ i v, mu2Sigma (read i) = some v ∧
        (v = ⟨{(8, 1)}⟩ ∨ v = ⟨{(4, 2)}⟩ ∨ v = ⟨{(4, 1), (4, 1)}⟩) := by
  -- the loop's first exit, not an arbitrary later one
  obtain ⟨v, hv⟩ := decided_of_ne_refineRow (Nat.find_spec hterm)
  exact ⟨Nat.find hterm, v, hv, mu2Sigma_alphabet _ _ hv⟩

/-! ## Gate (executed `example`s, not blueprint declarations)

**(a) The exit index is minimal — the trajectory really is a LOOP.** Before `Nat.find hterm`
every step is row 5, the α-refine pointer. This is the content the `Nat.find` in the proof buys
over an arbitrary witness, and it is the only place the "loop" in the node's name is visible.

**(b) `hterm` is doing work — the statement is FALSE without it.** For the never-exiting
trajectory (constantly row 5) the hypothesis is unsatisfiable AND the conclusion fails: `mu2Sigma
.refineRow = none`, so no step emits anything. So termination is not decoration bolted onto a
theorem that would hold anyway; E.55/E.56 are load-bearing suppliers.

**(c) The emitted value is at the frame's degree.** Composing with E.49's `mu2Sigma_degree`, the
decided σ-value has degree 8 — the n = 8 bite, not some other frame's. A dictionary edit that
kept the alphabet but broke the degree law would pass (a) and (b) and fail here. -/

section Gate

-- (a) every step strictly before the exit is the α-refine row.
example (read : ℕ → Mu2Row) (hterm : ∃ i, read i ≠ .refineRow) :
    ∀ j < Nat.find hterm, read j = .refineRow := by
  intro j hj
  by_contra h
  exact Nat.find_min hterm hj h

-- (b) the never-exiting trajectory: no termination supply, and nothing decided anywhere.
example : ¬ ∃ i, (fun _ : ℕ => Mu2Row.refineRow) i ≠ .refineRow := by
  rintro ⟨i, hi⟩
  exact hi rfl

example : ¬ ∃ i v, mu2Sigma ((fun _ : ℕ => Mu2Row.refineRow) i) = some v ∧
    (v = ⟨{(8, 1)}⟩ ∨ v = ⟨{(4, 2)}⟩ ∨ v = ⟨{(4, 1), (4, 1)}⟩) := by
  rintro ⟨i, v, hv, -⟩
  exact absurd hv (by simp [mu2Sigma])

-- (c) the decided value carries the frame's degree (E.49's degree law, composed).
example (read : ℕ → Mu2Row) (hterm : ∃ i, read i ≠ .refineRow) :
    ∃ i v, mu2Sigma (read i) = some v ∧ v.degree = 8 := by
  obtain ⟨i, v, hv, -⟩ := he7a_prime_schema read hterm
  exact ⟨i, v, hv, mu2Sigma_degree _ _ hv⟩

end Gate

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.he7a_prime_schema

end AxCheck
