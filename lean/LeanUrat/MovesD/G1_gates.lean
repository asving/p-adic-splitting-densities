/-
Unit G1.gateBlock  (MovesD campaign, E-phase)  [ADDENDUM unit — not among the 48
blueprint ids; built per the E-phase charge: "the ∅ bridge (F3) and the gate block are
units too". Content = the blueprint's MANDATORY GATE CHECK (§0.6) + adversary block
(§3.1), restricted to what is STATABLE on shape data at E-phase.]
moves_ref: §0.6 (P̂* data, REV-6 subtype addendum: P̂* ∈ Shape 3; W = 7, M = 1,
Nshape = 5, A = 11, NPband = 5) + §3.1 (P̂₀ ∈ Shape 4, A(P̂₀) = 14 — Fable#6's unclaimed
cross-check; adversaries A-i/A-ii/A-vi — the BUILDABLE ones; A-iii/A-iv are unbuildable
records, excluded by `ShapeRead`'s own Prop fields, and need no statement).
NOTE: the classifier-side gate numbers (C_P̂*(2) = 3, C_P̂*(3) = 48, mult ≡ 1) are
class-count semantics over PrefSet — owned by the P-phase/menu wave, not statable as
closed shape arithmetic here.
deps: Defs.  difficulty: easy (decide/norm_num arithmetic at P-phase).
hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

/-- P̂* read 0 (§D4-R.6): root, (e,h,g,μ,a) = (1,1,2,1,0), span [0,3], u*₀ = 0, γ₀ = 3,
w₀ = 1, monicTop = true (slot 3 = the monic lead). -/
def readStar0 : ShapeRead where
  species := ReadSpecies.root
  e := 1; h := 1; g := 2; μ := 1; a := 0
  s0 := 0; wSide := 3; Dwidth := 1
  ustar := 0; gam := 3; w := 1; monicTop := true
  he := by decide
  hg := by decide
  hμ := by decide
  hw := by decide
  hDw := by decide
  hh := by decide
  hcop := by decide
  hspecInc := by decide
  hspecRec := by decide
  hmonicRoot := by decide

/-- P̂* read 1 (§D4-R.6): recentering, (1,3,1,1,0), span [0,1], u*₁ = 1, γ₁ = 4, w₁ = 2,
monicTop = false. -/
def readStar1 : ShapeRead where
  species := ReadSpecies.recentering
  e := 1; h := 3; g := 1; μ := 1; a := 0
  s0 := 0; wSide := 1; Dwidth := 2
  ustar := 1; gam := 4; w := 2; monicTop := false
  he := by decide
  hg := by decide
  hμ := by decide
  hw := by decide
  hDw := by decide
  hh := by decide
  hcop := by decide
  hspecInc := by decide
  hspecRec := by decide
  hmonicRoot := by decide

/-- The sealed gate shape P̂* (§D4-R.6, n = 3). -/
def PhatStar : ShapePrefix := ⟨[readStar0, readStar1]⟩

/-- P̂₀ (§3.1, n = 4): root-only (1,1,1,2,0), full span, u* = 0, γ = 4, w = 1. -/
def read0Phat0 : ShapeRead where
  species := ReadSpecies.root
  e := 1; h := 1; g := 1; μ := 2; a := 0
  s0 := 0; wSide := 4; Dwidth := 1
  ustar := 0; gam := 4; w := 1; monicTop := true
  he := by decide
  hg := by decide
  hμ := by decide
  hw := by decide
  hDw := by decide
  hh := by decide
  hcop := by decide
  hspecInc := by decide
  hspecRec := by decide
  hmonicRoot := by decide

/-- The second positive gate shape P̂₀ (n = 4). -/
def Phat0 : ShapePrefix := ⟨[read0Phat0]⟩

/-- Adversary A-i (§3.1): root wSide = 10 against n = 3 (must fail `root_box`). -/
def advI : ShapeRead where
  species := ReadSpecies.root
  e := 1; h := 1; g := 1; μ := 1; a := 0
  s0 := 0; wSide := 10; Dwidth := 1
  ustar := 0; gam := 10; w := 1; monicTop := false
  he := by decide
  hg := by decide
  hμ := by decide
  hw := by decide
  hDw := by decide
  hh := by decide
  hcop := by decide
  hspecInc := by decide
  hspecRec := by decide
  hmonicRoot := by decide

/-- Adversary A-ii (§3.1): monicTop faker — s0 + wSide = 2 ≠ 3 (must fail `MonicTie`). -/
def advII : ShapeRead where
  species := ReadSpecies.root
  e := 1; h := 1; g := 1; μ := 1; a := 0
  s0 := 0; wSide := 2; Dwidth := 1
  ustar := 0; gam := 2; w := 1; monicTop := true
  he := by decide
  hg := by decide
  hμ := by decide
  hw := by decide
  hDw := by decide
  hh := by decide
  hcop := by decide
  hspecInc := by decide
  hspecRec := by decide
  hmonicRoot := by decide

/-- Adversary A-vi (§3.1, REV 8): root-only record with w = 2 (must fail `ShapeWF.w0`). -/
def advVI : ShapeRead where
  species := ReadSpecies.root
  e := 1; h := 1; g := 1; μ := 1; a := 0
  s0 := 0; wSide := 4; Dwidth := 1
  ustar := 0; gam := 4; w := 2; monicTop := true
  he := by decide
  hg := by decide
  hμ := by decide
  hw := by decide
  hDw := by decide
  hh := by decide
  hcop := by decide
  hspecInc := by decide
  hspecRec := by decide
  hmonicRoot := by decide

/-! ### The gate statements (P-phase: decide/norm_num against the definitions) -/

/-- GATE (positive): P̂* carries the certificate — P̂* ∈ Shape 3, clause by clause. -/
theorem PhatStar_wf : ShapeWF 3 PhatStar := by
  sorry

/-- GATE (positive): P̂₀ carries the certificate — P̂₀ ∈ Shape 4. -/
theorem Phat0_wf : ShapeWF 4 Phat0 := by
  sorry

/-- GATE: W(P̂*) = 1·3 + 2·2 = 7. -/
theorem PhatStar_W : PhatStar.W = 7 := by
  sorry

/-- GATE: M(P̂*) = 1·1 = 1. -/
theorem PhatStar_Mfac : PhatStar.Mfac = 1 := by
  sorry

/-- GATE: Nshape(P̂*) = 1 + max(⌈3⌉, ⌈4⌉) = 5. -/
theorem PhatStar_Nshape : PhatStar.Nshape = 5 := by
  sorry

/-- GATE: A(P̂*) = 9 + 2 = 11 (at n = 3, N = Nshape = 5). -/
theorem PhatStar_A' : PhatStar.A' 3 = 11 := by
  sorry

/-- GATE: NPband(P̂*) = 1 + 4 = 5 (the inhabited-branch NP value — the note's own
"N(P̂*) = 1 + (largest pinned base level = 4, at c₀) = 5"). -/
theorem PhatStar_NPband : PhatStar.NPband 3 = 5 := by
  sorry

/-- GATE: A(P̂₀) = 14 (Fable#6's unclaimed cross-check against the note). -/
theorem Phat0_A' : Phat0.A' 4 = 14 := by
  sorry

/-- ADVERSARY A-i: fails `root_box` at n = 3. -/
theorem advI_not_wf : ¬ ShapeWF 3 ⟨[advI]⟩ := by
  sorry

/-- ADVERSARY A-ii: fails `MonicTie` at n = 3. -/
theorem advII_not_wf : ¬ ShapeWF 3 ⟨[advII]⟩ := by
  sorry

/-- ADVERSARY A-vi: fails `w0` at n = 4. -/
theorem advVI_not_wf : ¬ ShapeWF 4 ⟨[advVI]⟩ := by
  sorry

end LeanUrat.MovesD
