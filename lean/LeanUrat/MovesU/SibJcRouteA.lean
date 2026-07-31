import Mathlib

/-!
# SIBJC ROUTE-(a) COUNTERMODEL GATE — the correlation-cell counting core, COMPILED
(fence-event-27 evidence completion; post-wave unit 3, 2026-07-31; per
BRIDGE_ADJUDICATIONS_2026-07-30.md item 27: "countermodel gates should compile the
(a)-route first".  NO statement is changed anywhere; this is a leaf.)

## What the row asserts and what this gate compiles

`BK.sibjc` (`MovesU/DefsLedger.SibJcRows` at the pinned `TreePin` instance) asserts
`MovesT.SibCount` for EVERY lawful `CellAssign` CA at the pinned tree models.  The M07
attempt (notes/openmath/M07-sibjc_fable.md §2, route 1 = route (a)) argues all three
fields are FALSE AS TYPED because `CellData` has no adaptedness law: a lawful CA may
key cells on the sibling branches' joint digits, and at the CORRELATION CELL
`{v₁ = v₂}` the (SIB) product law fails by exactly a factor p — with the sealed F1
census integers (p = 5: 5¹³ ≠ 5¹²).

THIS LEAF COMPILES THE COUNTING MECHANISM, at full abstraction and at the F1 numbers:

* `sib_diag_break` — for ANY pair of digit forms `v₁, v₂ : X → Fin p` JOINTLY UNIFORM
  on a finite carrier (the gate's censused P2 finding, as a hypothesis: every pair
  value is hit exactly `U` times, `U ≠ 0`), (SIB)'s m = 2 count-face equation
  `#(Σc ∩ S₁ ∩ S₂) · #Σc = #(Σc ∩ S₁) · #(Σc ∩ S₂)`
  FAILS at the correlation cell `Σc := {v₁ = v₂}` with the single-digit continuation
  events `S_r := {v_r = a}` — the two sides differ by exactly the factor p.
* `sib_diag_break_F1` — the F1 census instance: p = 5, per-pair count U = 15 625
  (= 5⁶; #Σ* = 5⁸): LHS = 15 625 · 78 125 = 5¹³ ≠ 5¹² = 15 625² = RHS.

## What this gate does NOT establish (the honest residual, recorded)

This is the (a)-route's COUNTING CORE, not an at-instance refutation of the typed row:
* the abstract carrier X stands in for the F1 window cell Σ*; tying it to the PINNED
  `TreePin` models needs (i) OL-2 (a lawful `CellAssign` at the pinned instance —
  open; if uninhabited the rows are VACUOUS, itself the recorded defect), (ii) the
  §2.4 refinement-lawfulness of the diagonal-refined CA in the `CellData` vocabulary
  (checked field-by-field in prose in M07 §2; not compiled here), (iii) the F1 events
  transcribed as `ContFiber` sets and the census P2-uniformity imported at the model.
* Until those land, the row's status stays PLAUSIBLY-FALSE-AS-TYPED — now with the
  arithmetic mechanism COMPILED (this file), upgrading the item-27 evidence from
  prose+numerics to prose+numerics+Lean-core counting gate.
* The repair menu is item 27's (adaptedness law on `CellData` / carrier
  parameterization / the R3 ledger re-key of M07 §2.4) — adjudication, not executed.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 400000

namespace LeanUrat.MovesU.SibRouteA

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Joint uniformity of a digit-form pair (the F1 gate's censused P2 finding, as a
hypothesis): every value pair is attained exactly `U` times. -/
def JointlyUniform (p : ℕ) (v₁ v₂ : X → Fin p) (U : ℕ) : Prop :=
  ∀ a b : Fin p, (univ.filter (fun x => v₁ x = a ∧ v₂ x = b)).card = U

/-- The correlation cell `{v₁ = v₂}` splits as the disjoint union of the diagonal
pair fibers, so its cardinality is `p · U`. -/
lemma corrCell_card {p : ℕ} [NeZero p] {v₁ v₂ : X → Fin p} {U : ℕ}
    (h : JointlyUniform p v₁ v₂ U) :
    (univ.filter (fun x => v₁ x = v₂ x)).card = p * U := by
  classical
  have hsplit : (univ.filter (fun x => v₁ x = v₂ x))
      = univ.biUnion (fun a : Fin p => univ.filter (fun x => v₁ x = a ∧ v₂ x = a)) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_biUnion]
    constructor
    · intro hx
      exact ⟨v₂ x, hx, rfl⟩
    · rintro ⟨a, h1, h2⟩
      rw [h1, h2]
  rw [hsplit, card_biUnion]
  · rw [Finset.sum_congr rfl (fun a _ => h a a)]
    simp [Finset.sum_const, Finset.card_univ]
  · intro a _ b _ hab
    refine disjoint_left.mpr ?_
    intro x hx hx'
    simp only [mem_filter] at hx hx'
    exact hab (hx.2.1.symm.trans hx'.2.1)

/-- On the correlation cell, the single-branch event `{v₁ = a}` collapses to the
diagonal pair fiber `{v₁ = a ∧ v₂ = a}`. -/
lemma corrCell_inter_left {p : ℕ} (v₁ v₂ : X → Fin p) (a : Fin p) :
    (univ.filter (fun x => v₁ x = v₂ x)) ∩ (univ.filter (fun x => v₁ x = a))
      = univ.filter (fun x => v₁ x = a ∧ v₂ x = a) := by
  ext x
  simp only [mem_inter, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hd, h1⟩
    exact ⟨h1, hd ▸ h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1.trans h2.symm, h1⟩

/-- Same collapse for the second branch. -/
lemma corrCell_inter_right {p : ℕ} (v₁ v₂ : X → Fin p) (a : Fin p) :
    (univ.filter (fun x => v₁ x = v₂ x)) ∩ (univ.filter (fun x => v₂ x = a))
      = univ.filter (fun x => v₁ x = a ∧ v₂ x = a) := by
  ext x
  simp only [mem_inter, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hd, h2⟩
    exact ⟨hd.trans h2, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1.trans h2.symm, h2⟩

/-- Both branches at once: the triple intersection is the same diagonal fiber. -/
lemma corrCell_inter_both {p : ℕ} (v₁ v₂ : X → Fin p) (a : Fin p) :
    ((univ.filter (fun x => v₁ x = v₂ x)) ∩ (univ.filter (fun x => v₁ x = a)))
        ∩ (univ.filter (fun x => v₂ x = a))
      = univ.filter (fun x => v₁ x = a ∧ v₂ x = a) := by
  rw [corrCell_inter_left]
  ext x
  simp only [mem_inter, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨⟨h1, h2⟩, -⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, h2⟩, h1.trans h2.symm ▸ h2⟩

/-- **THE ROUTE-(a) COUNTING GATE** (the M07 §2 mechanism, compiled): at a jointly
uniform digit-form pair with nonzero fiber count and `2 ≤ p`, (SIB)'s m = 2 count-face
identity FAILS at the correlation cell with the single-digit continuation events —
`#(Σc ∩ S₁ ∩ S₂) · #Σc = p · (#(Σc ∩ S₁) · #(Σc ∩ S₂)) ≠ #(Σc ∩ S₁) · #(Σc ∩ S₂)`.
Conditioning on the (lawful-but-unadapted) event `{v₁ = v₂}` destroys the sibling
product law by exactly the factor p. -/
theorem sib_diag_break {p : ℕ} [NeZero p] (hp : 2 ≤ p) {v₁ v₂ : X → Fin p} {U : ℕ}
    (hU : U ≠ 0) (h : JointlyUniform p v₁ v₂ U) (a : Fin p) :
    ((univ.filter (fun x => v₁ x = v₂ x)) ∩ (univ.filter (fun x => v₁ x = a))
          ∩ (univ.filter (fun x => v₂ x = a))).card
        * (univ.filter (fun x => v₁ x = v₂ x)).card
      ≠ ((univ.filter (fun x => v₁ x = v₂ x)) ∩ (univ.filter (fun x => v₁ x = a))).card
        * ((univ.filter (fun x => v₁ x = v₂ x)) ∩ (univ.filter (fun x => v₂ x = a))).card := by
  rw [corrCell_inter_both, corrCell_inter_left, corrCell_inter_right, corrCell_card h,
    h a a]
  -- U · (p·U) ≠ U · U, since U ≠ 0 and p ≥ 2
  intro hcontra
  have hU1 : 1 ≤ U := Nat.one_le_iff_ne_zero.mpr hU
  nlinarith [hU1, hp, hcontra]

/-- **The F1 census instance** (p = 5, per-pair fiber 15 625 = 5⁶ on the 5⁸-member
14-pin cell Σ*, the sealed CASE_SIB P2 finding): the two sides of (SIB)'s identity at
the correlation cell are 5¹³ and 5¹² — off by exactly 5.  (The abstract carrier stands
in for Σ*; the pinned-instance transcription residual is recorded in the header.) -/
theorem sib_diag_break_F1 {v₁ v₂ : X → Fin 5}
    (h : JointlyUniform 5 v₁ v₂ 15625) (a : Fin 5) :
    ((univ.filter (fun x => v₁ x = v₂ x)) ∩ (univ.filter (fun x => v₁ x = a))
          ∩ (univ.filter (fun x => v₂ x = a))).card
        * (univ.filter (fun x => v₁ x = v₂ x)).card
      ≠ ((univ.filter (fun x => v₁ x = v₂ x)) ∩ (univ.filter (fun x => v₁ x = a))).card
        * ((univ.filter (fun x => v₁ x = v₂ x)) ∩ (univ.filter (fun x => v₂ x = a))).card :=
  sib_diag_break (by norm_num) (by norm_num) h a

/-- The pinned F1 integers, displayed: LHS = 15 625 · 78 125 = 5¹³ ≠ 5¹² = 15 625². -/
example : 15625 * 78125 = 5 ^ 13 ∧ 15625 * 15625 = 5 ^ 12 ∧ (5:ℕ) ^ 13 ≠ 5 ^ 12 := by
  norm_num

end LeanUrat.MovesU.SibRouteA

#print axioms LeanUrat.MovesU.SibRouteA.sib_diag_break
#print axioms LeanUrat.MovesU.SibRouteA.sib_diag_break_F1
