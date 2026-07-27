/-
Unit D14a.emptyShape_law  (MovesD campaign, E-phase)  (final-audit finding 6)
[REV 5: `Pref_empty_shape`'s History-level display now sits UNDER the F3 bridge.]
moves_ref: "Pref(∅) = {∅} … its fiber is the FULL BOX, level-N count p^{nN} =
C_∅·p^{nN − A(∅)} (C_∅ = 1, A(∅) = 0), by L5's normalized full-box display — NOT by
Theorem C(b)". CONNECTED IN CORPUS VOCABULARY: `emptyFiber` IS the defined S(∅,⊤), `P.CD`
IS the corpus C (its `if` branch is the note's own definition-level dispatch — the
History type has no empty chain, which is WHY CD carries the dispatch; `Pref_empty_shape`
displays that the History-level set is empty, so 1 is the η = ∅ class and nothing else),
`P.A'` IS the corpus A.
deps: Defs.  sketch: if_pos; card univ = p^m; empty sum.  difficulty: easy.
hypothesis_fields: `hm`, `hN` explicit (L12's empty-case N(P̂) := 1 convention; the box
shape — no jet available).
[E-PHASE NOTE: `A'_nil`'s bound variable is `n'` — the blueprint's `∀ n` shadows the
binder of `P : Shape n`; recorded in MANIFEST deviations.]
-/
import Mathlib
import LeanUrat.MovesD.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n N m : ℕ}
  {pol : CanonPolicy p F} {P : Shape n}

/-- The History-level honesty display: the literal PrefSet of ∅ is empty, and CD's 1 is
exactly the η = ∅ class. -/
theorem Pref_empty_shape (hP : (P : ShapePrefix).reads = []) :
    PrefSet n pol P = ∅ ∧ P.CD pol = 1 := by
  refine ⟨?_, ?_⟩
  · -- The History type has no empty chain: MatchesHist forces `H.nodes.length = 0`,
    -- contradicting `H.nonempty`.
    ext H
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨hlen, -⟩, -⟩
    have : H.nodes = [] := by
      rw [hP] at hlen
      simpa using hlen
    exact H.nonempty this
  · -- CD's `if` branch IS the note's definition-level dispatch Pref(∅) = {∅}.
    rw [Shape.CD, if_pos hP]

/-- A(∅) = 0 (empty read sum), at every degree. -/
theorem A'_nil (hP : (P : ShapePrefix).reads = []) :
    ∀ n' : ℕ, (P : ShapePrefix).A' n' = 0 := by
  intro n'
  -- Empty read list ⇒ the per-read fresh-band sum ranges over `Finset.range 0 = ∅`.
  simp only [ShapePrefix.A', ShapePrefix.A, hP, List.length_nil, Finset.range_zero,
    Finset.sum_empty]

/-- The η = ∅ mass law on the corpus objects: full box = C_∅·p^{nN − A(∅)}. -/
theorem emptyShape_law (hm : m = n * N) (hN : 1 ≤ N) (hP : (P : ShapePrefix).reads = []) :
    Nat.card ↥(emptyFiber p m) * p ^ ((P : ShapePrefix).A' n)
      = P.CD pol * p ^ (n * N) := by
  have hA : (P : ShapePrefix).A' n = 0 := A'_nil hP n
  have hCD : P.CD pol = 1 := (Pref_empty_shape hP).2
  -- The fiber is the FULL BOX: `Nat.card (Fin m → ZMod p) = p^m`.
  have hcard : Nat.card ↥(emptyFiber p m) = p ^ m := by
    haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
    have e : ↥(emptyFiber p m) ≃ (Fin m → ZMod p) := Equiv.Set.univ (Fin m → ZMod p)
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
      Fintype.card_fin]
  rw [hA, hCD, pow_zero, mul_one, one_mul, hcard, hm]

end LeanUrat.MovesD
