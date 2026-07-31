# O13 Lean follow-up record — `skeleton_finite` (Skeleton finiteness at every n)

*(2026-07-31, Lean unit from the VERIFIED O-13 leaf
`O13_phaseB_attempt_rev2.md` (2-pass accepted). This is the "Lean
formalization of the encoding injection = natural follow-up" that the leaf's
§5 consumer line named. New module + this record ONLY; zero existing files
touched; zero statement changes.)*

## What landed

`lean/LeanUrat/MovesV/SkeletonFinite.lean` (new module, compiled green,
Lean-core `{propext, Classical.choice, Quot.sound}` on all five
declarations, checked 2026-07-31):

- `skeletonEquivSnRaw (n) : Skeleton n ≃ ↥(MovesSp.SnRaw n)` — the
  definitional bridge (a `Skeleton n` IS a catalogue-membered species,
  MovesV/Defs:181); both directions `rfl`.
- `inCatalogue_zero_elim : InCatalogue 0 s → False` — the n = 0 corner
  O13/SP-FIN never needed: `RootStage 0` pins W = 0 against `WellTyped`'s
  1 ≤ W; `SuccStep` extends only existing members.
- `instance : IsEmpty (Skeleton 0)`.
- **`skeleton_finite (n) : Finite (Skeleton n)`** — THE unit theorem
  (O13 rev-2 Theorem 1 = T-4 SP-FIN, Lean side, now at EVERY n): n = 0 by
  emptiness, n ≥ 1 by `MovesSp.SP_FIN` (the already-formalized
  catalogue-encoding injection into `Code n = Fin (n²+3n+12) → Fin (n+2)`,
  `SP2_encodeInj`/`SP2_encodeCard`/`SP2_finThm`) transported across the
  equivalence. Also registered as a global `Finite` instance.
- `skeletonFintype (n) : Fintype (Skeleton n)` — noncomputable
  `@[reducible]` def (NOT an instance; mathlib practice).
- `skeleton_card_le (n) : Nat.card (Skeleton n) ≤ (n+2)^(n²+3n+12)` —
  SP-FIN's explicit p-free crude bound transported.

Gates run: `lake env lean LeanUrat/MovesV/SkeletonFinite.lean` clean;
`lake build LeanUrat.MovesV.SkeletonFinite` green (8571 jobs);
`#print axioms` on all five = Lean-core; `lake env lean
LeanUrat/AxChk_baseline.lean` re-run as belt-and-braces — capstone
`OM.RealInstanceV2.montes_unconditional` footprint UNCHANGED (Lean-core
only; the new module is imported by nothing, so no regression was possible).

## Consumer wiring — PARKED, by the statement fence (nothing wired here)

The `hfin : Finite (Skeleton n)` hypothesis-row census (2026-07-31):
`tableShape_inst` (V7_ts:70, the row's origin), TV_E1
(ctsTable/ctsTable_pins/measuredOf chain), TV_E3, TV_E4, TV_E5a, TV_F2b,
TV_G3:447, and `ledgerIV_inst_assembly` (TV_E7:56). Every such row is now
mathematically dischargeable at every n by `skeleton_finite n` /
`inferInstance` — **but no consumer was re-pointed**:

- The one live sorry waiting on exactly this, `ledgerIV_inst`
  (V7_livC:71–83), stands. Whether its row gains `hfin` or the instance
  discharges it is the TV-E7-header EXECUTION-TIME RATIFICATION ITEM (the
  hfin row was a TV_E7-header escalation; statement change = parked under
  the math-first regime). Note also its in-place fill is import-blocked
  independently of hfin (TV_E6/TV_E7 import V7_livC), so an
  adjudicated fill will need the assembly proof restated upstream or the
  import graph re-cut — recorded, not attempted.
- Once un-parked, the instance route needs NO row change: with
  `import LeanUrat.MovesV.SkeletonFinite`, `skeleton_finite n` supplies
  every `hfin` argument at call sites verbatim.

## Subsumption note (files untouched by design)

`skeleton1_finite` (TV_E8:32, via V1_witnessC's Subsingleton) and
`skeleton3_finite` (V2_skeleton:15, SP_FIN at n = 3) are SUBSUMED by
`skeleton_finite`; they stand as compiled historical witnesses, nothing
re-pointed, files byte-identical.

## M1 hygiene check — no countermodel scope change

Grep over quarantine + `*negWitness*`/`*counter*` files: no compiled
countermodel or negation witness concerns `Finite (Skeleton n)` (the only
"skeleton" hits, HC2/U10d_negWitness:53 and HC2/HK05_countermodelGate:93,
use the word informally for E-phase sorried statements). The new global
`Finite (Skeleton n)` instance is visible only to importers of the new
module — none at HEAD — and in any case only ADDS derivability of a Prop
class; no leaf countermodel's scope changes. No M1 notes owed elsewhere.

## Not done here (out of charge)

- MovesV/MANIFEST.json unit-count update (shared curated file — orchestrator
  fold-in), docs/PROJECT_STATE.md line (same).
- The V7_livC sorry fill / hfin-row adjudication (parked, see above).
- Tree-level Sk(n) finiteness (O13 Theorem 3 / Lemma T′): NOT formalized —
  the Lean `Skeleton n` is the LETTER type (O13 Theorem 1 exactly); the
  tree-shape menu has no Lean carrier yet.
