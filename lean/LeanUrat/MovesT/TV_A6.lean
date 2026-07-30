/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.MovesU.U10_theoremU

/-! # TV-A6 — the campaign-endpoint boundary deliverable for the E5 hoist:
`theoremU` byte-stability + footprint census + consumer-grep record

BRIDGE CAMPAIGN unit **TV-A6** (area BP3, cluster A; blueprint
`lean/notes/BRIDGE_BP3_TV_2026-07-30.md` §4 [REV 2, finding 8]). E-PHASE
SKELETON + the E-phase half of the record (the greps below were RUN at HEAD,
2026-07-30); the post-A4 half is an execution-phase re-run.

CHARGE (converts G-a's promise from a grep-and-sweep into a checked artifact):
after TV-A4's ripple lands in place,
(i)   `MovesU.theoremU` (U10_theoremU.lean:107) re-type-checks BYTE-UNCHANGED
      and its axiom footprint is re-verified via the AxChk census — plain
      `lake build`, then `lake env lean LeanUrat/AxChk_baseline.lean` (the
      census print is the one standing `lake env lean` exception; it is not a
      green record);
(ii)  the boundary DOCUMENTATION (U10's docstring + PROJECT_STATE) is updated
      to NAME the new premise rows — `TrackUniqOn`/`TrackRepOn` (TV-A1, the
      wave-4 parameter genre, owner HC-2/D4R0K) and the `ReadLocality` row
      from TV-B7 (owner HC-2/D4R0K, MOVES 7566–7570; SYN-C2: the ONE
      level-locality kernel, MovesT/ReadLocality.lean — `StableInputs` is its
      derived bundle, TV_B2.lean) — an existing-file edit, execution phase;
(iii) the consumer-grep transcript is attached (below, and re-run post-A4).

E-PHASE GREP TRANSCRIPT (run at HEAD 2026-07-30, recorded per the unit spec):
* `grep -rn "TrackUniqOn\|TrackRepOn\|TreeExpFin\|TreeNStmt\|TreeNStableStmt\|
  RS1GivenPackage" LeanUrat/MovesU/` → ZERO hits: no MovesU code consumes any
  row the A/B hoists change (the blueprint's claim, re-verified).
* `grep -rn "fiber_root_split\|treeExp\|perShape_law\|treeN" LeanUrat/MovesU/`
  → MANIFEST.json (2 prose entries) + DefsLedger.lean:43/:227/:342/:375 — ALL
  docstring/record mentions of `MovesT.treeN` as the count_tie DISCHARGE
  CANDIDATE; no code dependence. So `theoremU`'s statement cannot move under
  TV-A2/A3/A4; the deliverable certifies this STAYS true post-execution (or
  enumerates what changed).
* the three ∀-closure names live in exactly five MovesT files (Defs,
  E8_treeExp, E11_treeN, D12_packages, D15_w3Rekey) — the blueprint's census,
  re-confirmed; TV-A4's sweep list is complete.

THE COMPILED PIN (this file's build-time content): the definition below forces
`theoremU` to re-elaborate in this module — the type-check half of deliverable
(i) rides every `lake build` from now on. It adds NO axiom surface (a
definitional re-reference; `#print axioms` of the pin = theoremU's own).

deps: A4 (execution ordering), B7 (the ReadLocality row named in (ii) —
SYN-C2 retype record there); the E-phase transcript above has no deps.
difficulty: routine-opus, ~20 lines + records. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace LeanUrat.MovesT

/-- **TV-A6 `tv_a6_theoremU_pin`** — the boundary pin: a definitional
re-reference to `LeanUrat.MovesU.theoremU` (U10_theoremU.lean:107). Its
elaboration at every build IS deliverable (i)'s type-check half: if the A/B
hoist ripple ever moved theoremU's statement or broke its elaboration, THIS
module goes red. The footprint half (AxChk census) and the byte-diff record
are the executing prover's post-A4 duties (module docstring). -/
def tv_a6_theoremU_pin := @LeanUrat.MovesU.theoremU

end LeanUrat.MovesT
