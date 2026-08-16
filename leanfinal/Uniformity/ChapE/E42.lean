/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E38

/-!
# Uniformity.ChapE.E42 — `s18b_fold`: the level-two discharge S1.8B (the composed-key entry)

**Chapter E, NODE E.42** [theorem] (`blueprint/CHAP-E_sigma_ladder.md` §6 — the Display-A
dispositions), ENV-E2 (the carrier arena: a slot carrier `C : SlotCarrier O K` from E.10; the
threshold `T` is the frame's `T₂`).

S1.8B is the LEVEL-TWO discharge. The chain base is `Ψ − w` with either `w = 0` (the base already
IS a DEFINITION-HE6-1-shape key, so the §S5 package applies literally) or `w ≠ 0` of degree
`< D″` and slot value `> T₂`; the refine increments `w₁, …, w_j` each have degree `< D″` and slot
value `> T₂`, pairwise distinct. This node is the **fold**: `w + w₁ + ⋯ + w_j` is again either
the trivial base or a single admissible increment `W′` — degree `< D″`, finite slot value
`> T₂`. That is what lets the whole §S5 package transport ONCE, so that

> *"the chain is read at `Ψ_{κ₂, r̃}`, a DEFINITION HE6-1 key, and not at `Φ₂`"* (`EFF.T2.62`),

and items 2–5 of the `(MID-PEEL)` suite at the level-two state follow from the transported
package. Consequence for the chapter's bookkeeping (`EFF.T2.24`): `(MP1)` (E.40) is scoped to
LEVEL ONE only — the level-two analogue is discharged here, and E.40's file says so.

## The two legs are independent, and the file keeps them apart

* **the height leg** is E.38's `slot_fold` (LEMMA HE7-12(d), the `[r3]` rider): pairwise-distinct
  finite heights above `T` fold to a nonzero sum whose height is the MIN of the summands' — the
  ultrametric step is an equality exactly because the heights differ;
* **the degree leg** is master-side arithmetic — E.38's `natDegree_list_sum_lt`, iterated
  `Polynomial.natDegree_add_le`. It consumes no slot law at all (gate (b) proves it with `hdist`
  deleted). This is the r12 accumulated-degree tooth: after HETOW C-A withdrew the source
  licence for `deg w < D″`, the degree conjunct is re-derived master-side, and the match is that
  it is pure degree arithmetic on both sides.

## ⚠ THE WITHDRAWN ROUTE, TRANSCRIBED SO IT CANNOT RECUR (`EFF.T2.53`)

S1.8B's discharge runs through **HE7-12(c)'s transport** — the package moved to the refined key
— and NOT through HE7-8's interleaving clause, which *"supplies no item of the input suite"*.
That `[r3]`-clause route was WITHDRAWN at the source. Anything in this chapter that reaches for
HE7-8 (E.55) to discharge an input-suite item is resurrecting the withdrawn route; E.55 supplies
TERMINATION (well-foundedness), which is a different obligation, consumed by E.52 and by nothing
here. This file imports E.38 and nothing else for exactly that reason.

## Why `hdist` is guarded, and why it cannot be dropped

The signed distinctness is `a = 0 ∨ b = 0 ∨ C.hgt a ≠ C.hgt b`, guarded — weaker than E.38's
plain `C.hgt a ≠ C.hgt b` — because the base increment `w` is allowed to be `0`, and `C.hgt 0 =
⊤` collides with nothing but itself. Inside the proof the guards evaporate: every element with a
finite height is nonzero (`hgt_zero`), so on the list actually handed to `slot_fold` the guarded
relation IS plain distinctness.

Dropping the hypothesis altogether would make the theorem FALSE, and gate (a) is the witness:
for the pair `(w, [−w])` — same degrees, same heights, admissible in every other respect — the
sum is `0`, so the right disjunct fails (`hgt 0 = ⊤` is not finite) and the left disjunct fails
(`[−w] ≠ []`). The gate checks all three facts, including that `hdist` is the ONLY hypothesis
that fails, so it is a genuine necessity witness rather than a vacuous one.

## What is NOT claimed

No item of the `(MID-PEEL)` suite is proved here, at level two or anywhere else. This is the
arithmetic that licenses ONE application of the transport; the transport itself is `EFF.T2.62`'s
package, and its instance content is chapter-C/E.23 material. Nothing about level one is touched:
`(MP1)` stays OPEN (E.40).

DEPENDS: E.38 (`slot_fold`, `natDegree_list_sum_lt`) · E.35 (the increments' heights at
instances — the supplier of `hws`, cited not imported) · E.56 (`chain_invariant`, the
pairwise-distinctness supply — forward reference, DAG-ordered, cited not imported).

SOURCE: `EFF.T2.62` (S1.8B's composed-key scope clause: the `w = 0` / `dv₂(w) > T₂` disjunct,
*"LEMMA HE7-12(d) folds the whole sum … covered by ONE instance of clauses (a)–(c) at
`Ψ_{κ₂,r̃}` … Step 2 then runs unchanged"*); `EFF.T2.24` (S1.8B: *"This is a level-two discharge.
The level-one recentered-key peel remains `(MP1)`-conditional"*); `EFF.T2.53` (the withdrawn
`[r3]`-clause route, transcribed above); `EFF.HE7.44`(d).

TEETH: the composed-key transport tooth; the accumulated-degree tooth (r12) → **Lean theorem**.

ENVIRONMENT: ENV-E2.

## Status

Sorry-free, Lean-core axioms only.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- **Helper (not a blueprint node).** A finite slot height forces nonvanishing: `C.hgt 0 = ⊤`
(E.10's `hgt_zero`), so anything with an integer height is nonzero. This is what turns the
GUARDED distinctness of the signature into the plain distinctness `slot_fold` wants. -/
private theorem ne_zero_of_hgt_eq {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K) {A : Polynomial O} {v : ℤ} (hA : C.hgt A = (v : WithTop ℤ)) : A ≠ 0 := by
  intro h0
  rw [h0, C.hgt_zero] at hA
  exact absurd hA (by simp)

/-- **Helper (not a blueprint node).** On a list of NONZERO polynomials the guarded distinctness
`a = 0 ∨ b = 0 ∨ C.hgt a ≠ C.hgt b` collapses to plain distinctness — E.38's `hdist` shape. -/
private theorem pairwise_hgt_ne_of_ne_zero {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K) :
    ∀ l : List (Polynomial O), (∀ x ∈ l, x ≠ 0) →
      (l.Pairwise fun a b => a = 0 ∨ b = 0 ∨ C.hgt a ≠ C.hgt b) →
      l.Pairwise fun a b => C.hgt a ≠ C.hgt b := by
  intro l
  induction l with
  | nil => intro _ _; exact List.Pairwise.nil
  | cons a t ih =>
    intro h0 h
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp h
    refine List.pairwise_cons.mpr
      ⟨?_, ih (fun x hx => h0 x (List.mem_cons_of_mem _ hx)) htail⟩
    intro b hb
    rcases hhead b hb with h1 | h1 | h1
    · exact absurd h1 (h0 a (by simp))
    · exact absurd h1 (h0 b (List.mem_cons_of_mem _ hb))
    · exact h1

/-- **NODE E.42.** *The level-two discharge S1.8B (the composed-key entry), schema form over
E.38's fold.* Base increment `w` — either `0` (the literal DEFINITION-HE6-1 base) or admissible:
degree `< C.D`, finite slot value `> T`. Refine increments `ws` all admissible, all heights
pairwise distinct (guarded, since `w` may vanish). Then the composed increment `w + Σ wᵢ` is
either the trivial base again or ONE admissible increment: `EFF.T2.62`'s *"covered by ONE
instance of clauses (a)–(c)"*, which is what lets the §S5 package transport once and leaves
`(MP1)` scoped to level one (`EFF.T2.24`). -/
theorem s18b_fold {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K) {T : ℤ}
    (w : Polynomial O) (ws : List (Polynomial O))
    (hw : w = 0 ∨ (w.natDegree < C.D ∧ ∃ v : ℤ, C.hgt w = (v : WithTop ℤ) ∧ T < v))
    (hws : ∀ x ∈ ws, x.natDegree < C.D ∧ ∃ v : ℤ, C.hgt x = (v : WithTop ℤ) ∧ T < v)
    (hdist : (w :: ws).Pairwise fun a b => a = 0 ∨ b = 0 ∨ C.hgt a ≠ C.hgt b) :
    (w + ws.sum = 0 ∧ ws = [] ∧ w = 0) ∨
    ((w + ws.sum).natDegree < C.D ∧
      ∃ v : ℤ, C.hgt (w + ws.sum) = (v : WithTop ℤ) ∧ T < v) := by
  -- the increments are admissible one by one; the two projections are used throughout
  have hdegs : ∀ x ∈ ws, x.natDegree < C.D := fun x hx => (hws x hx).1
  have hvals : ∀ x ∈ ws, ∃ v : ℤ, C.hgt x = (v : WithTop ℤ) ∧ T < v := fun x hx => (hws x hx).2
  have hws0 : ∀ x ∈ ws, x ≠ 0 := by
    intro x hx
    obtain ⟨v, hv, -⟩ := hvals x hx
    exact ne_zero_of_hgt_eq C hv
  rcases hw with rfl | ⟨hwdeg, vw, hvw, hTw⟩
  · -- the base vanishes: the fold runs on the refine increments alone
    rcases eq_or_ne ws [] with rfl | hne
    · -- nothing at all to fold: `EFF.T2.62`'s literal `w = 0` base
      exact Or.inl ⟨by simp, rfl, rfl⟩
    · right
      have hd : ws.Pairwise fun a b => C.hgt a ≠ C.hgt b :=
        pairwise_hgt_ne_of_ne_zero C ws hws0 (List.pairwise_cons.mp hdist).2
      obtain ⟨-, hvsum, -⟩ := slot_fold C ws hne hdegs hvals hd
      exact ⟨by simpa using natDegree_list_sum_lt C.hD ws hdegs, by simpa using hvsum⟩
  · -- the base is a genuine increment: fold the whole list `w :: ws` in one call
    right
    have hdegs' : ∀ x ∈ (w :: ws), x.natDegree < C.D := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hwdeg
      · exact hdegs x hx'
    have hvals' : ∀ x ∈ (w :: ws), ∃ v : ℤ, C.hgt x = (v : WithTop ℤ) ∧ T < v := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨vw, hvw, hTw⟩
      · exact hvals x hx'
    have h0' : ∀ x ∈ (w :: ws), x ≠ 0 := by
      intro x hx
      obtain ⟨v, hv, -⟩ := hvals' x hx
      exact ne_zero_of_hgt_eq C hv
    have hd' : (w :: ws).Pairwise fun a b => C.hgt a ≠ C.hgt b :=
      pairwise_hgt_ne_of_ne_zero C (w :: ws) h0' hdist
    obtain ⟨-, hvsum, -⟩ :=
      slot_fold C (w :: ws) (List.cons_ne_nil _ _) hdegs' hvals' hd'
    exact ⟨by simpa using natDegree_list_sum_lt C.hD (w :: ws) hdegs',
      by simpa using hvsum⟩

/-! ## Gate (executed `example`s, not blueprint declarations)

**(a) `hdist` IS NECESSARY — the witness, machine-checked.** Take the pair `(w, [−w])` at any
carrier, with `w` admissible and `C.hgt (−w) = C.hgt w` (true at every instance; the abstract
`SlotCarrier` does not impose it, so the gate takes it as a hypothesis — and that is precisely
the point, since it makes the witness available at every carrier that does satisfy it). Then
every hypothesis of `s18b_fold` holds EXCEPT `hdist`, which fails, and BOTH disjuncts of the
conclusion fail: the sum is `0`, whose height is `⊤`. So the theorem without `hdist` is false,
not merely unproved.

**(b) The degree leg needs no slot law.** The same degree conjunct, derived with `hdist` and
every height hypothesis deleted — the r12 accumulated-degree tooth as master-side arithmetic.

**(c) Both disjuncts are reachable.** `w = 0, ws = []` returns the LEFT disjunct (the literal
base); an admissible `w` with `ws = []` returns the RIGHT one (the singleton fold — "the package
applies literally"). A conclusion whose disjuncts were not both attainable would be a shape
error, and the second half also checks that the left disjunct's triple is not silently
satisfiable at a nonzero base. -/

section Gate

-- (a) necessity of `hdist`: the cancelling pair `(w, [−w])`.
example {O : Type*} [CommRing O] {K : Type*} [Field K] (C : SlotCarrier O K) {T : ℤ}
    (w : Polynomial O) (hdeg : w.natDegree < C.D) (v : ℤ) (hv : C.hgt w = (v : WithTop ℤ))
    (hT : T < v) (hneg : C.hgt (-w) = C.hgt w) :
    -- the base and the increment list are admissible …
    (w = 0 ∨ (w.natDegree < C.D ∧ ∃ u : ℤ, C.hgt w = (u : WithTop ℤ) ∧ T < u)) ∧
    (∀ x ∈ [-w], x.natDegree < C.D ∧ ∃ u : ℤ, C.hgt x = (u : WithTop ℤ) ∧ T < u) ∧
    -- … `hdist` is the one hypothesis that fails …
    ¬ ((w :: [-w]).Pairwise fun a b => a = 0 ∨ b = 0 ∨ C.hgt a ≠ C.hgt b) ∧
    -- … and the conclusion fails outright.
    ¬ ((w + ([-w] : List (Polynomial O)).sum = 0 ∧ ([-w] : List (Polynomial O)) = [] ∧ w = 0) ∨
      ((w + ([-w] : List (Polynomial O)).sum).natDegree < C.D ∧
        ∃ u : ℤ, C.hgt (w + ([-w] : List (Polynomial O)).sum) = (u : WithTop ℤ) ∧ T < u)) := by
  have hw0 : w ≠ 0 := ne_zero_of_hgt_eq C hv
  have hsum : w + ([-w] : List (Polynomial O)).sum = 0 := by simp
  refine ⟨Or.inr ⟨hdeg, v, hv, hT⟩, ?_, ?_, ?_⟩
  · intro x hx
    obtain rfl : x = -w := by simpa using hx
    exact ⟨by simpa using hdeg, v, by rw [hneg, hv], hT⟩
  · intro hd
    rcases (List.pairwise_cons.mp hd).1 (-w) (by simp) with h | h | h
    · exact hw0 h
    · exact hw0 (by simpa using h)
    · exact h hneg.symm
  · rintro (⟨-, hnil, -⟩ | ⟨-, u, hu, -⟩)
    · exact absurd hnil (by simp)
    · rw [hsum, C.hgt_zero] at hu
      exact absurd hu (by simp)

-- (b) the degree leg alone: no distinctness, no heights, no threshold.
example {O : Type*} [CommRing O] {K : Type*} [Field K] (C : SlotCarrier O K)
    (w : Polynomial O) (ws : List (Polynomial O)) (hwdeg : w.natDegree < C.D)
    (hdeg : ∀ x ∈ ws, x.natDegree < C.D) : (w + ws.sum).natDegree < C.D := by
  have := natDegree_list_sum_lt C.hD (w :: ws) (by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hwdeg
    · exact hdeg x hx')
  simpa using this

-- (c) the LEFT disjunct is reached by the literal base `w = 0`, `ws = []`.
example {O : Type*} [CommRing O] {K : Type*} [Field K] (C : SlotCarrier O K) {T : ℤ} :
    ((0 : Polynomial O) + ([] : List (Polynomial O)).sum = 0 ∧
        ([] : List (Polynomial O)) = [] ∧ (0 : Polynomial O) = 0) ∨
      (((0 : Polynomial O) + ([] : List (Polynomial O)).sum).natDegree < C.D ∧
        ∃ v : ℤ, C.hgt ((0 : Polynomial O) + ([] : List (Polynomial O)).sum)
          = (v : WithTop ℤ) ∧ T < v) :=
  s18b_fold C 0 [] (Or.inl rfl) (by simp) (by simp)

-- (c′) the RIGHT disjunct is reached by a single admissible increment, and the left one is NOT
-- available there (a nonzero base cannot satisfy the left triple).
example {O : Type*} [CommRing O] {K : Type*} [Field K] (C : SlotCarrier O K) {T : ℤ}
    (w : Polynomial O) (hdeg : w.natDegree < C.D) (v : ℤ) (hv : C.hgt w = (v : WithTop ℤ))
    (hT : T < v) :
    (w + ([] : List (Polynomial O)).sum).natDegree < C.D ∧
      ∃ u : ℤ, C.hgt (w + ([] : List (Polynomial O)).sum) = (u : WithTop ℤ) ∧ T < u := by
  rcases s18b_fold C w [] (Or.inr ⟨hdeg, v, hv, hT⟩) (by simp) (by simp) with ⟨-, -, h0⟩ | h
  · exact absurd h0 (ne_zero_of_hgt_eq C hv)
  · exact h

end Gate

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.s18b_fold

end AxCheck
