/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-C1 `tbcap_hen` — CAP N_V = 1, uniform per class (MOVES 7155–7159): the class
IS a finite union of level-0 cells. PROVED-IN-NOTE status: unconditional. The locality
face is PROVED here; the finite-union face carries the E-phase sorry. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

/-- `redPoly χ x` is a function of x ∘ χ. -/
theorem redPoly_congr (χ : Fin n → Fin m) (x x' : Box p m)
    (hxx : ∀ b : Fin n, x (χ b) = x' (χ b)) :
    redPoly χ x = redPoly (p := p) χ x' := by
  unfold redPoly
  congr 1
  exact Finset.sum_congr rfl fun b _ => by rw [hxx b]

theorem tbcap_hen (χ : Fin n → Fin m) (hχ : Function.Injective χ)
    (x x' : Box p m) (hxx : ∀ b : Fin n, x (χ b) = x' (χ b)) :
    henPayload χ x = henPayload χ x' := by
  unfold henPayload henDegrees
  rw [redPoly_congr χ x x' hxx]

theorem tbcap_hen_cells (χ : Fin n → Fin m) (hχ : Function.Injective χ)
    (v₀ : Multiset Vd) :
    ∃ G : Finset (Fin n → ZMod p),
      {x : Box p m | henPayload χ x = v₀} = ⋃ g ∈ G, rootCell χ g := by
  classical
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  -- a total extension of a level-0 datum `g` to a box, agreeing with `g` on the χ-image
  set E : (Fin n → ZMod p) → Box p m :=
    (fun g j => if h : ∃ b, χ b = j then g h.choose else 0) with hE
  have hE_eq : ∀ (g : Fin n → ZMod p) (b : Fin n), E g (χ b) = g b := by
    intro g b
    have hcond : ∃ b', χ b' = χ b := ⟨b, rfl⟩
    simp only [hE]
    rw [dif_pos hcond]
    exact congrArg g (hχ hcond.choose_spec)
  refine ⟨Finset.univ.filter (fun g => henPayload χ (E g) = v₀), ?_⟩
  ext x
  constructor
  · intro hx
    rw [Set.mem_setOf_eq] at hx
    refine Set.mem_iUnion₂.mpr ⟨fun b => x (χ b), ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [tbcap_hen χ hχ (E (fun b => x (χ b))) x (fun b => hE_eq (fun b => x (χ b)) b)]
      exact hx
    · intro b; rfl
  · intro hx
    obtain ⟨g, hg, hcell⟩ := Set.mem_iUnion₂.mp hx
    rw [Finset.mem_filter] at hg
    have hcell' : ∀ b, x (χ b) = g b := hcell
    rw [Set.mem_setOf_eq, ← hg.2]
    exact tbcap_hen χ hχ x (E g) (fun b => by rw [hcell', hE_eq])

end LeanUrat.MovesT
