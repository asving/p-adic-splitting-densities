/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsTower
import LeanUrat.Moves.L1_baseResidual_R4
import LeanUrat.Moves.L1_baseWeight_R3

/-!
# HC1.T1_baseStage — the base package CONSTRUCTED at the Gauss valuation

moves_ref: MOVES 1992–2015 (the base stage, (S1)–(S6) item by item). deps: Moves
`L1_gaussVal`, `L1_baseResidual_R4`, `L1_baseWeight_R3` (ALL clean — §4.1 CLOSED).
difficulty: HARD (pre-split: T1a fields through hS5; T1b the (S6) legs).
hyp: none beyond bdata.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- **The §A base read pins** (T1's input; MOVES 1992–2015): a monic key φ of degree
d ≥ 1 whose mod-p reduction φ̄ is irreducible over F_p, a residue chart `res` of the
prime field into the ambient F with a root z₀ of φ̄ (F_Q := the splitting subfield
F_p(z₀) = `Subfield.closure {z0}`), and a read index (e, h) in lowest terms. The
base w := min_i(e·v(aᵢ) + i·h) is the construction's business (unit body). -/
structure BaseReadData (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F]
    (e h : ℕ) where
  φ : Polynomial ℤ_[p]
  hmonic : φ.Monic
  hdeg : 1 ≤ φ.natDegree
  hirr : Irreducible (φ.map (PadicInt.toZMod (p := p)))
  res : ZMod p →+* F
  z0 : F
  hz0 : Polynomial.eval₂ res z0 (φ.map (PadicInt.toZMod (p := p))) = 0
  he : 1 ≤ e
  hh : 1 ≤ h
  hcop : Nat.gcd e h = 1

/-- The base residue field F_Q: the splitting subfield F_p(z₀) inside F. -/
def BaseReadData.FQ {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {e h : ℕ} (bd : BaseReadData p F e h) : Subfield F :=
  Subfield.closure {bd.z0}

/-- Unit T1: for every legal base read there is a faithfully-based stage with the
full round-5 core, at the read's index (blueprint display verbatim). -/
theorem T1_baseStage {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (e h : ℕ) (bdata : BaseReadData p F e h) :
    ∃ σ : Stage p F, IsBaseStage σ ∧ StageCoreL σ ∧ σ.e = e ∧ σ.h = h := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.T1_baseStage
