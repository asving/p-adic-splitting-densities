/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesSp.DefsEnum

/-!
# MovesSp/DefsN3 — the SEALED n = 3 data (SP.6's hand catalogue, exhaustive)

E-phase transcription of `lean/notes/MOVESSP_LEAN_BLUEPRINT_2026-07-28.md` §4 (rev 5);
row content from `lean/notes/MOVES_2026-07-24.md` §M-SPECIES SP.6 ("The hand catalogue
at n = 3"). Definitions only, no `sorry`. Species field order everywhere:
tag, D, w, W, e, s0, ell, a, d, slots, lam, sel, lflank, rflank.

ORDER DISCIPLINE [REV 3, C1]: every literal list that a unit equates with a
`catalogue3.filter …` (or `groupX.filter …`) lists its members in catalogue3 order —
groups R → Q3 → Q2 → Q1 → I, and within a group in the displayed row order — because
`List.filter` preserves order and Nodup pins one occurrence each.

N*₃ values are gate-censused DATA (M-n3-V2) + a SEALED PREDICTION, never theorems;
field-size pass is "NECESSARY for realization, NOT sufficient"; realizability
semantics stays out of scope (blueprint §0).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

/-! ### GROUP R — ROOT, stage (D, w, W) = (1, 1, 3): 21 letters (rows R1–R8). -/

/-- R1  e=1, ℓ=1, a=0 | {(1,1)}▸(1,1) | right span 2: flanks (2) or (1,1) — 2. -/
def groupR : List Species :=
  [-- R1: right flank (2), then (1,1)
   ⟨.root, 1, 1, 3, 1, 0, 1, 0, 2, Finset.Icc 0 1, {(1,1)}, some (1,1), [], [2]⟩,
   ⟨.root, 1, 1, 3, 1, 0, 1, 0, 2, Finset.Icc 0 1, {(1,1)}, some (1,1), [], [1,1]⟩,
   -- R2: e=1, ℓ=1, a=1 | flanks (1)|(1)
   ⟨.root, 1, 1, 3, 1, 1, 1, 1, 2, Finset.Icc 1 2, {(1,1)}, some (1,1), [1], [1]⟩,
   -- R3: e=1, ℓ=1, a=2 | left span 2: (2) or (1,1)
   ⟨.root, 1, 1, 3, 1, 2, 1, 2, 2, Finset.Icc 2 3, {(1,1)}, some (1,1), [2], []⟩,
   ⟨.root, 1, 1, 3, 1, 2, 1, 2, 2, Finset.Icc 2 3, {(1,1)}, some (1,1), [1,1], []⟩,
   -- R4: e=1, ℓ=2, a=0 | {(2,1)}▸(2,1); {(1,2)}▸(1,2); {(1,1)²}▸(1,1) | right flank (1)
   ⟨.root, 1, 1, 3, 1, 0, 2, 0, 3, Finset.Icc 0 2, {(2,1)}, some (2,1), [], [1]⟩,
   ⟨.root, 1, 1, 3, 1, 0, 2, 0, 3, Finset.Icc 0 2, {(1,2)}, some (1,2), [], [1]⟩,
   ⟨.root, 1, 1, 3, 1, 0, 2, 0, 3, Finset.Icc 0 2, {(1,1),(1,1)}, some (1,1), [], [1]⟩,
   -- R5: e=1, ℓ=2, a=1 | same three λ▸sel | left flank (1)
   ⟨.root, 1, 1, 3, 1, 1, 2, 1, 3, Finset.Icc 1 3, {(2,1)}, some (2,1), [1], []⟩,
   ⟨.root, 1, 1, 3, 1, 1, 2, 1, 3, Finset.Icc 1 3, {(1,2)}, some (1,2), [1], []⟩,
   ⟨.root, 1, 1, 3, 1, 1, 2, 1, 3, Finset.Icc 1 3, {(1,1),(1,1)}, some (1,1), [1], []⟩,
   -- R6: e=1, ℓ=3, a=0 | {(3,1)}▸(3,1); {(2,1),(1,1)}▸(2,1) and ▸(1,1); {(1,3)}▸(1,3);
   --     {(1,2),(1,1)}▸(1,2) and ▸(1,1); {(1,1)³}▸(1,1)
   ⟨.root, 1, 1, 3, 1, 0, 3, 0, 4, Finset.Icc 0 3, {(3,1)}, some (3,1), [], []⟩,
   ⟨.root, 1, 1, 3, 1, 0, 3, 0, 4, Finset.Icc 0 3, {(2,1),(1,1)}, some (2,1), [], []⟩,
   ⟨.root, 1, 1, 3, 1, 0, 3, 0, 4, Finset.Icc 0 3, {(2,1),(1,1)}, some (1,1), [], []⟩,
   ⟨.root, 1, 1, 3, 1, 0, 3, 0, 4, Finset.Icc 0 3, {(1,3)}, some (1,3), [], []⟩,
   ⟨.root, 1, 1, 3, 1, 0, 3, 0, 4, Finset.Icc 0 3, {(1,2),(1,1)}, some (1,2), [], []⟩,
   ⟨.root, 1, 1, 3, 1, 0, 3, 0, 4, Finset.Icc 0 3, {(1,2),(1,1)}, some (1,1), [], []⟩,
   ⟨.root, 1, 1, 3, 1, 0, 3, 0, 4, Finset.Icc 0 3, {(1,1),(1,1),(1,1)}, some (1,1), [], []⟩,
   -- R7: e=2, ℓ=1, a=0 | {(1,1)}▸(1,1) | s₀′ ∈ {0, 1}
   ⟨.root, 1, 1, 3, 2, 0, 1, 0, 2, Finset.Icc 0 1, {(1,1)}, some (1,1), [], [1]⟩,
   ⟨.root, 1, 1, 3, 2, 1, 1, 0, 2, Finset.Icc 0 1, {(1,1)}, some (1,1), [1], []⟩,
   -- R8: e=3, ℓ=1, a=0 | {(1,1)}▸(1,1) | full span
   ⟨.root, 1, 1, 3, 3, 0, 1, 0, 2, Finset.Icc 0 1, {(1,1)}, some (1,1), [], []⟩]

/-- GROUP Q3 — POST-REC, stage (1, 1, 3): the same 21 rows as R1–R8 (retagged). -/
def groupQ3 : List Species :=
  groupR.map fun s =>
    { s with tag := Tag.postRec }

/-- GROUP Q2 — POST-REC, stage (1, 1, 2): 6 letters
(Q2.1 · Q2.2 · Q2.3's three λ▸sel rows as R4 · Q2.4). -/
def groupQ2 : List Species :=
  [-- Q2.1: e=1, ℓ=1, a=0 (right flank (1))
   ⟨.postRec, 1, 1, 2, 1, 0, 1, 0, 2, Finset.Icc 0 1, {(1,1)}, some (1,1), [], [1]⟩,
   -- Q2.2: e=1, ℓ=1, a=1 (left (1))
   ⟨.postRec, 1, 1, 2, 1, 1, 1, 1, 2, Finset.Icc 1 2, {(1,1)}, some (1,1), [1], []⟩,
   -- Q2.3: e=1, ℓ=2, a=0: three λ▸sel as R4
   ⟨.postRec, 1, 1, 2, 1, 0, 2, 0, 3, Finset.Icc 0 2, {(2,1)}, some (2,1), [], []⟩,
   ⟨.postRec, 1, 1, 2, 1, 0, 2, 0, 3, Finset.Icc 0 2, {(1,2)}, some (1,2), [], []⟩,
   ⟨.postRec, 1, 1, 2, 1, 0, 2, 0, 3, Finset.Icc 0 2, {(1,1),(1,1)}, some (1,1), [], []⟩,
   -- Q2.4: e=2, ℓ=1, a=0, s₀′=0
   ⟨.postRec, 1, 1, 2, 2, 0, 1, 0, 2, Finset.Icc 0 1, {(1,1)}, some (1,1), [], []⟩]

/-- GROUP Q1 — POST-REC, stage (1, 1, 1): 1 letter (confirming; ⊥). -/
def groupQ1 : List Species :=
  [⟨.postRec, 1, 1, 1, 1, 0, 1, 0, 2, Finset.Icc 0 1, {(1,1)}, none, [], []⟩]

/-- GROUP I — POST-INC, W = 1, confirming TERMINAL (⊥) letters, one per landing
stage (D, w) ∈ {(2,1), (2,2), (3,1), (3,3)} [(2,1) via e=2 sides; (2,2) via ▸(2,1);
(3,1) via e=3; (3,3) via ▸(3,1)]. -/
def groupI : List Species :=
  [⟨.postInc, 2, 1, 1, 1, 0, 1, 0, 2, Finset.Icc 0 1, {(1,1)}, none, [], []⟩,
   ⟨.postInc, 2, 2, 1, 1, 0, 1, 0, 2, Finset.Icc 0 1, {(1,1)}, none, [], []⟩,
   ⟨.postInc, 3, 1, 1, 1, 0, 1, 0, 2, Finset.Icc 0 1, {(1,1)}, none, [], []⟩,
   ⟨.postInc, 3, 3, 1, 1, 0, 1, 0, 2, Finset.Icc 0 1, {(1,1)}, none, [], []⟩]

/-- |𝒮₃^raw| = 21 + 21 + 6 + 1 + 4 = 53, in the PINNED order R ++ Q3 ++ Q2 ++ Q1 ++ I. -/
def catalogue3 : List Species := groupR ++ groupQ3 ++ groupQ2 ++ groupQ1 ++ groupI

/-! ### NAMED LETTERS consumed by unit statements [REV 2, F5/F6/F17]. -/

/-- Q2.3's {(1,2)}▸(1,2) row (the μ = 2 loop). -/
def loopQ23 : Species :=
  ⟨.postRec, 1, 1, 2, 1, 0, 2, 0, 3, Finset.Icc 0 2, {(1,2)}, some (1,2), [], []⟩

/-- Q3(R6)'s {(1,3)}▸(1,3) row (the μ = 3 loop). -/
def loopQ3 : Species :=
  ⟨.postRec, 1, 1, 3, 1, 0, 3, 0, 4, Finset.Icc 0 3, {(1,3)}, some (1,3), [], []⟩

/-- R3, left flank [2]  [F6: BOTH variants]. -/
def R3letterA : Species :=
  ⟨.root, 1, 1, 3, 1, 2, 1, 2, 2, Finset.Icc 2 3, {(1,1)}, some (1,1), [2], []⟩

/-- R3, left flank [1, 1]  [F6]. -/
def R3letterB : Species :=
  ⟨.root, 1, 1, 3, 1, 2, 1, 2, 2, Finset.Icc 2 3, {(1,1)}, some (1,1), [1,1], []⟩

/-- R4's {(1,2)}▸(1,2) row. -/
def rootR4sel12 : Species :=
  ⟨.root, 1, 1, 3, 1, 0, 2, 0, 3, Finset.Icc 0 2, {(1,2)}, some (1,2), [], [1]⟩

/-- R5's {(1,2)}▸(1,2) row. -/
def rootR5sel12 : Species :=
  ⟨.root, 1, 1, 3, 1, 1, 2, 1, 3, Finset.Icc 1 3, {(1,2)}, some (1,2), [1], []⟩

/-- R6's {(1,2),(1,1)}▸(1,2) row [REV 3, C2/§9]. -/
def rootR6sel12 : Species :=
  ⟨.root, 1, 1, 3, 1, 0, 3, 0, 4, Finset.Icc 0 3, {(1,2),(1,1)}, some (1,2), [], []⟩

/-- R6's {(1,3)}▸(1,3) row. -/
def rootR6sel13 : Species :=
  ⟨.root, 1, 1, 3, 1, 0, 3, 0, 4, Finset.Icc 0 3, {(1,3)}, some (1,3), [], []⟩

/-- I, stage (D,w) = (2,1)  (via e = 2 sides). -/
def letterI21 : Species :=
  ⟨.postInc, 2, 1, 1, 1, 0, 1, 0, 2, Finset.Icc 0 1, {(1,1)}, none, [], []⟩

/-- I, stage (2,2)  (via ▸(2,1)). -/
def letterI22 : Species :=
  ⟨.postInc, 2, 2, 1, 1, 0, 1, 0, 2, Finset.Icc 0 1, {(1,1)}, none, [], []⟩

/-- I, stage (3,1)  (via e = 3). -/
def letterI31 : Species :=
  ⟨.postInc, 3, 1, 1, 1, 0, 1, 0, 2, Finset.Icc 0 1, {(1,1)}, none, [], []⟩

/-- I, stage (3,3)  (via ▸(3,1)). -/
def letterI33 : Species :=
  ⟨.postInc, 3, 3, 1, 1, 0, 1, 0, 2, Finset.Icc 0 1, {(1,1)}, none, [], []⟩

/-- The n = 3 menu map (Out, sealed; stage laws of SP.4): ▸(1,1)→Q1; ▸(1,2)→Q2;
▸(1,3)→Q3; ▸(2,1)→I(2,2); ▸(3,1)→I(3,3); e=2→I(2,1); e=3→I(3,1); terminal→[].
By selection/stride match (stride first: e = 2/3 letters carry sel (1,1)). -/
def menuMap3 (s : Species) : List Species :=
  match s.sel with
  | none => []
  | some gm =>
      if s.e = 2 then [letterI21]
      else if s.e = 3 then [letterI31]
      else if gm = (1, 1) then groupQ1
      else if gm = (1, 2) then groupQ2
      else if gm = (1, 3) then groupQ3
      else if gm = (2, 1) then [letterI22]
      else if gm = (3, 1) then [letterI33]
      else []

/-! ### The six multi-side μ = 3 letters (SP.6's SIX COMPUTATIONS), BY NAME:
"Q3(R1, right flank (1,1)), Q3(R2), Q3(R3, left flank (1,1)), and the three
Q3(R4) λ-rows". -/

/-- Q3(R1)-copy, right flank [1, 1];  N*₃ = 7. -/
def msQ3R1 : Species :=
  ⟨.postRec, 1, 1, 3, 1, 0, 1, 0, 2, Finset.Icc 0 1, {(1,1)}, some (1,1), [], [1,1]⟩

/-- Q3(R2)-copy;  N*₃ = 6. -/
def msQ3R2 : Species :=
  ⟨.postRec, 1, 1, 3, 1, 1, 1, 1, 2, Finset.Icc 1 2, {(1,1)}, some (1,1), [1], [1]⟩

/-- Q3(R3)-copy, left flank [1, 1];  N*₃ = 6. -/
def msQ3R3 : Species :=
  ⟨.postRec, 1, 1, 3, 1, 2, 1, 2, 2, Finset.Icc 2 3, {(1,1)}, some (1,1), [1,1], []⟩

/-- Q3(R4), λ = {(2,1)} ▸ (2,1);  N*₃ = 6. -/
def msQ3R4a : Species :=
  ⟨.postRec, 1, 1, 3, 1, 0, 2, 0, 3, Finset.Icc 0 2, {(2,1)}, some (2,1), [], [1]⟩

/-- Q3(R4), λ = {(1,2)} ▸ (1,2);  N*₃ = 6. -/
def msQ3R4b : Species :=
  ⟨.postRec, 1, 1, 3, 1, 0, 2, 0, 3, Finset.Icc 0 2, {(1,2)}, some (1,2), [], [1]⟩

/-- Q3(R4), λ = {(1,1)²} ▸ (1,1);  N*₃ = 6. -/
def msQ3R4c : Species :=
  ⟨.postRec, 1, 1, 3, 1, 0, 2, 0, 3, Finset.Icc 0 2, {(1,1),(1,1)}, some (1,1), [], [1]⟩

def multiSide6 : List Species := [msQ3R1, msQ3R2, msQ3R3, msQ3R4a, msQ3R4b, msQ3R4c]

/-- λ's demand for distinct nonzero roots (the field-size criterion): the number
of monic-linear factors, WITH multiset multiplicity ("nonzero by the endpoint
convention: a is split off, so z ∤ R_anch"). -/
def linCount (s : Species) : ℕ := Multiset.card (s.lam.filter fun gm => gm.1 = 1)

/-! ### Field-size exclusion lists as LITERAL lists of named letters [F5]; λ-content
PINNED by Sp.n3exclusionLists' filter identities (q = 2: ≥ 2 distinct linears,
q = 3: ≥ 3), not by cardinality. [REV 4, Codex-9/12] literal bodies + row-named
letters (order = catalogue3). -/

/-- R4 {(1,1)²}▸(1,1) row          (groupR). -/
def exR4c : Species :=
  ⟨.root, 1, 1, 3, 1, 0, 2, 0, 3, Finset.Icc 0 2, {(1,1),(1,1)}, some (1,1), [], [1]⟩

/-- R5 {(1,1)²}▸(1,1) row          (groupR). -/
def exR5c : Species :=
  ⟨.root, 1, 1, 3, 1, 1, 2, 1, 3, Finset.Icc 1 3, {(1,1),(1,1)}, some (1,1), [1], []⟩

/-- R6 {(1,2),(1,1)}▸(1,2) row (= rootR6sel12). -/
def exR6b12 : Species := rootR6sel12

/-- R6 {(1,2),(1,1)}▸(1,1) row. -/
def exR6b11 : Species :=
  ⟨.root, 1, 1, 3, 1, 0, 3, 0, 4, Finset.Icc 0 3, {(1,2),(1,1)}, some (1,1), [], []⟩

/-- R6 {(1,1)³}▸(1,1) row. -/
def exR6t : Species :=
  ⟨.root, 1, 1, 3, 1, 0, 3, 0, 4, Finset.Icc 0 3, {(1,1),(1,1),(1,1)}, some (1,1), [], []⟩

/-- Q3 copy of exR4c. -/
def exQ3R4c : Species := { exR4c with tag := Tag.postRec }
/-- Q3 copy of exR5c. -/
def exQ3R5c : Species := { exR5c with tag := Tag.postRec }
/-- Q3 copy of exR6b12. -/
def exQ3R6b12 : Species := { exR6b12 with tag := Tag.postRec }
/-- Q3 copy of exR6b11. -/
def exQ3R6b11 : Species := { exR6b11 with tag := Tag.postRec }
/-- Q3 copy of exR6t. -/
def exQ3R6t : Species := { exR6t with tag := Tag.postRec }

/-- Q2.3 {(1,1)²}▸(1,1) row        (groupQ2). -/
def exQ23c : Species :=
  ⟨.postRec, 1, 1, 2, 1, 0, 2, 0, 3, Finset.Icc 0 2, {(1,1),(1,1)}, some (1,1), [], []⟩

/-- p = 2 field-size exclusion: the 11 letters with λ ⊇ two distinct linears
(catalogue3 order). -/
def fieldSizeExcluded2 : List Species :=
  [exR4c, exR5c, exR6b12, exR6b11, exR6t,
   exQ3R4c, exQ3R5c, exQ3R6b12, exQ3R6b11, exQ3R6t, exQ23c]   -- 11

/-- p = 3 field-size exclusion: exactly the 2 letters with λ = {(1,1)³}
(catalogue3 order). -/
def fieldSizeExcluded3 : List Species := [exR6t, exQ3R6t]     -- 2

/-- [REV 4, Codex-12] the n = 1 letter: the single confirming ROOT letter at stage
(1,1,1) (W = n = 1, selection ⊥ — (G6)'s degenerate degree). -/
def confirmingRoot1 : Species :=
  ⟨.root, 1, 1, 1, 1, 0, 1, 0, 2, Finset.Icc 0 1, {(1,1)}, none, [], []⟩

/-- N*₃ on the six (SP.6): per-NAME table, `none` off multiSide6. Gate-censused
DATA (M-n3-V2), never a theorem; the other 45 p = 3-admissible letters carry only
the censused N*₃ ≤ 5 remark, deliberately not a def. -/
def Nstar3six (s : Species) : Option ℕ :=
  if s = msQ3R1 then some 7
  else if s = msQ3R2 then some 6
  else if s = msQ3R3 then some 6
  else if s = msQ3R4a then some 6
  else if s = msQ3R4b then some 6
  else if s = msQ3R4c then some 6
  else none

end LeanUrat.MovesSp
