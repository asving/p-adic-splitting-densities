/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# HC1.G4_caseKGate — the Case-K F₉ conditioned-digit gate (decide gate)

moves_ref: MOVES 3017–3045 (CASE-K v2 SEALED GATE RECORD, Q1–Q6; Q4 at 3030–3032).
**PREDICATE CORRECTED (audit C-3): the both-rise cell law is `d₀ = d₁²`** — the
seal's own algebra: both-rise ⟺ R₂ = X² + d₁X + d₀ has the double root τ ⟺
τ = −d₁/2 = d₁ (char 3) and d₀ = τ² = d₁² (rev 1's d₀ = d₁³ was the wrong algebra;
script ground truth `verification/case_k_gate_v2_p3.py` :396 `d0 = f9mul(d1, d1)`).
**ALL legs CONTENT-pinned: finite-set EQUALITY against explicit element lists,
never bare cardinalities** (the campaign order-discipline precedent; the v1-seal
adjudication at MOVES 2934 is the warrant). EDITORIAL FOLD (E-phase charge): leg
(ii)'s clause order fixed to the seal tuple pairing — `R₂(τ) = 0` with 56,
`2τ + d₁ = 0` with 64 (both: 8). Element lists machine-transcribed from the script
at E-phase; the NORMATIVE predicates are the displayed ones (d₀ = d₁², τ = d₁).
deps: none (self-contained F9 arithmetic; the gate re-checks the ALGEBRAIC layer
of the seal, not the p-adic census). difficulty: medium. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

/-- F₉ as `ZMod 3 × ZMod 3` carrying the X²+1 multiplication through `f9mul`
(componentwise Prod addition IS the F₉ addition; the Prod `*` is never used). -/
abbrev F9 : Type := ZMod 3 × ZMod 3

/-- the X²+1 multiplication `(a,b)·(c,d) = (ac − bd, ad + bc)` — fully decidable. -/
def f9mul (x y : F9) : F9 := (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1)

/-- `R₂(τ) = τ² + d₁·τ + d₀` over F₉ (the conditioned quadratic of the seal). -/
def caseKR2 (d0 d1 t : F9) : F9 := f9mul t t + f9mul d1 t + d0

/-- the CORRECTED both-rise predicate (audit C-3): Frobenius-matched
`d₀ = d₁² ∧ τ = d₁` on nonzero cells. -/
def caseKBothRise (x : F9 × F9 × F9) : Prop :=
  x.1 ≠ 0 ∧ x.2.1 ≠ 0 ∧ x.1 = f9mul x.2.1 x.2.1 ∧ x.2.2 = x.2.1

instance : DecidablePred caseKBothRise := fun x => by
  unfold caseKBothRise; infer_instance

/-- Unit G4 leg (i): the Frobenius-matched both-rise set IS the explicit 8-triple
list {(d₁², d₁, d₁) : d₁ ∈ F9ˣ}; 8-of-512 as a Nat.card COROLLARY (Q4). -/
theorem G4_caseKGate_i :
    (Finset.univ.filter caseKBothRise
      = ({((2, 0), (0, 1), (0, 1)), ((2, 0), (0, 2), (0, 2)),
      ((1, 0), (1, 0), (1, 0)), ((0, 2), (1, 1), (1, 1)),
      ((0, 1), (1, 2), (1, 2)), ((1, 0), (2, 0), (2, 0)),
      ((0, 1), (2, 1), (2, 1)), ((0, 2), (2, 2), (2, 2))} : Finset (F9 × F9 × F9))) ∧
    (Finset.univ.filter caseKBothRise).card = 8 := by
  decide

set_option maxRecDepth 100000 in
/-- Unit G4 leg (ii): the char-3 edge clauses, solution SETS pinned as explicit
element lists, with Q2's sealed cardinalities as corollaries — THE SEAL TUPLE
PAIRING (editorial fold): `R₂(τ) = 0` ↦ 56, `2τ + d₁ = 0` ↦ 64, both ↦ 8 (= the
leg-(i) both-rise list). -/
theorem G4_caseKGate_ii :
    (Finset.univ.filter (fun x : F9 × F9 × F9 =>
        x.1 ≠ 0 ∧ x.2.1 ≠ 0 ∧ caseKR2 x.1 x.2.1 x.2.2 = 0)
      = ({((0, 1), (1, 1), (0, 2)), ((0, 1), (1, 1), (2, 0)),
      ((0, 1), (1, 2), (1, 2)), ((0, 1), (2, 1), (2, 1)),
      ((0, 1), (2, 2), (0, 1)), ((0, 1), (2, 2), (1, 0)),
      ((0, 2), (1, 1), (1, 1)), ((0, 2), (1, 2), (0, 1)),
      ((0, 2), (1, 2), (2, 0)), ((0, 2), (2, 1), (0, 2)),
      ((0, 2), (2, 1), (1, 0)), ((0, 2), (2, 2), (2, 2)),
      ((1, 0), (0, 1), (1, 1)), ((1, 0), (0, 1), (2, 1)),
      ((1, 0), (0, 2), (1, 2)), ((1, 0), (0, 2), (2, 2)),
      ((1, 0), (1, 0), (1, 0)), ((1, 0), (2, 0), (2, 0)),
      ((1, 1), (1, 0), (0, 2)), ((1, 1), (1, 0), (2, 1)),
      ((1, 1), (1, 2), (1, 0)), ((1, 1), (1, 2), (1, 1)),
      ((1, 1), (2, 0), (0, 1)), ((1, 1), (2, 0), (1, 2)),
      ((1, 1), (2, 1), (2, 0)), ((1, 1), (2, 1), (2, 2)),
      ((1, 2), (1, 0), (0, 1)), ((1, 2), (1, 0), (2, 2)),
      ((1, 2), (1, 1), (1, 0)), ((1, 2), (1, 1), (1, 2)),
      ((1, 2), (2, 0), (0, 2)), ((1, 2), (2, 0), (1, 1)),
      ((1, 2), (2, 2), (2, 0)), ((1, 2), (2, 2), (2, 1)),
      ((2, 0), (0, 1), (0, 1)), ((2, 0), (0, 2), (0, 2)),
      ((2, 0), (1, 0), (1, 1)), ((2, 0), (1, 0), (1, 2)),
      ((2, 0), (2, 0), (2, 1)), ((2, 0), (2, 0), (2, 2)),
      ((2, 1), (0, 1), (1, 2)), ((2, 1), (0, 1), (2, 0)),
      ((2, 1), (0, 2), (1, 0)), ((2, 1), (0, 2), (2, 1)),
      ((2, 1), (1, 2), (0, 2)), ((2, 1), (1, 2), (2, 2)),
      ((2, 1), (2, 1), (0, 1)), ((2, 1), (2, 1), (1, 1)),
      ((2, 2), (0, 1), (1, 0)), ((2, 2), (0, 1), (2, 2)),
      ((2, 2), (0, 2), (1, 1)), ((2, 2), (0, 2), (2, 0)),
      ((2, 2), (1, 1), (0, 1)), ((2, 2), (1, 1), (2, 1)),
      ((2, 2), (2, 2), (0, 2)), ((2, 2), (2, 2), (1, 2))} : Finset (F9 × F9 × F9))) ∧
    (Finset.univ.filter (fun x : F9 × F9 × F9 =>
        x.1 ≠ 0 ∧ x.2.1 ≠ 0 ∧ x.2.2 + x.2.2 + x.2.1 = 0)
      = ({((0, 1), (0, 1), (0, 1)), ((0, 1), (0, 2), (0, 2)),
      ((0, 1), (1, 0), (1, 0)), ((0, 1), (1, 1), (1, 1)),
      ((0, 1), (1, 2), (1, 2)), ((0, 1), (2, 0), (2, 0)),
      ((0, 1), (2, 1), (2, 1)), ((0, 1), (2, 2), (2, 2)),
      ((0, 2), (0, 1), (0, 1)), ((0, 2), (0, 2), (0, 2)),
      ((0, 2), (1, 0), (1, 0)), ((0, 2), (1, 1), (1, 1)),
      ((0, 2), (1, 2), (1, 2)), ((0, 2), (2, 0), (2, 0)),
      ((0, 2), (2, 1), (2, 1)), ((0, 2), (2, 2), (2, 2)),
      ((1, 0), (0, 1), (0, 1)), ((1, 0), (0, 2), (0, 2)),
      ((1, 0), (1, 0), (1, 0)), ((1, 0), (1, 1), (1, 1)),
      ((1, 0), (1, 2), (1, 2)), ((1, 0), (2, 0), (2, 0)),
      ((1, 0), (2, 1), (2, 1)), ((1, 0), (2, 2), (2, 2)),
      ((1, 1), (0, 1), (0, 1)), ((1, 1), (0, 2), (0, 2)),
      ((1, 1), (1, 0), (1, 0)), ((1, 1), (1, 1), (1, 1)),
      ((1, 1), (1, 2), (1, 2)), ((1, 1), (2, 0), (2, 0)),
      ((1, 1), (2, 1), (2, 1)), ((1, 1), (2, 2), (2, 2)),
      ((1, 2), (0, 1), (0, 1)), ((1, 2), (0, 2), (0, 2)),
      ((1, 2), (1, 0), (1, 0)), ((1, 2), (1, 1), (1, 1)),
      ((1, 2), (1, 2), (1, 2)), ((1, 2), (2, 0), (2, 0)),
      ((1, 2), (2, 1), (2, 1)), ((1, 2), (2, 2), (2, 2)),
      ((2, 0), (0, 1), (0, 1)), ((2, 0), (0, 2), (0, 2)),
      ((2, 0), (1, 0), (1, 0)), ((2, 0), (1, 1), (1, 1)),
      ((2, 0), (1, 2), (1, 2)), ((2, 0), (2, 0), (2, 0)),
      ((2, 0), (2, 1), (2, 1)), ((2, 0), (2, 2), (2, 2)),
      ((2, 1), (0, 1), (0, 1)), ((2, 1), (0, 2), (0, 2)),
      ((2, 1), (1, 0), (1, 0)), ((2, 1), (1, 1), (1, 1)),
      ((2, 1), (1, 2), (1, 2)), ((2, 1), (2, 0), (2, 0)),
      ((2, 1), (2, 1), (2, 1)), ((2, 1), (2, 2), (2, 2)),
      ((2, 2), (0, 1), (0, 1)), ((2, 2), (0, 2), (0, 2)),
      ((2, 2), (1, 0), (1, 0)), ((2, 2), (1, 1), (1, 1)),
      ((2, 2), (1, 2), (1, 2)), ((2, 2), (2, 0), (2, 0)),
      ((2, 2), (2, 1), (2, 1)), ((2, 2), (2, 2), (2, 2))} : Finset (F9 × F9 × F9))) ∧
    (Finset.univ.filter (fun x : F9 × F9 × F9 =>
        x.1 ≠ 0 ∧ x.2.1 ≠ 0 ∧ caseKR2 x.1 x.2.1 x.2.2 = 0)).card = 56 ∧
    (Finset.univ.filter (fun x : F9 × F9 × F9 =>
        x.1 ≠ 0 ∧ x.2.1 ≠ 0 ∧ x.2.2 + x.2.2 + x.2.1 = 0)).card = 64 ∧
    (Finset.univ.filter (fun x : F9 × F9 × F9 =>
        x.1 ≠ 0 ∧ x.2.1 ≠ 0 ∧ caseKR2 x.1 x.2.1 x.2.2 = 0 ∧
        x.2.2 + x.2.2 + x.2.1 = 0)).card = 8 := by
  decide

end LeanUrat.HC1

#print axioms LeanUrat.HC1.G4_caseKGate_i
#print axioms LeanUrat.HC1.G4_caseKGate_ii
