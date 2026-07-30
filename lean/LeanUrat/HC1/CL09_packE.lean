/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.R1_LSTStmt
import LeanUrat.HC1.CL08_latticeExp

/-!
# HC1.CL09_packE — packE + the Gr-pin (BP5 CL-09)

**Unit CL-09** (blueprint `lean/notes/BRIDGE_BP5_CLEANUP_2026-07-30.md` §4; §3.2
display (8)).

**Informal statement.** The graded-expansion carrier pack `packE T rl :
CarrierPackR p` (display (8)): `G := gradedExpCarrier T` (CL-08), trivial history,
the tower's real coordinates/heights/blocks/level sets, digits in the base residue
field `F_Q`, `slotCoeff` = the per-level display `γ ↦ inGr γ (T.slotCoeff b
(y↾lvl b γ))` (the MOVES 3795–3807 display itself), `mono := monoE` (the per-level
expansion of the basis monomial), lines/interiors/floor from the realizability data
`rl` with the `i > K` guard `interiorEnd := 0`, `window ≡ True`. Plus THE
non-vacuity clause: `packE_gr_pin : ∀ γ, (packE T rl).G.Gr γ = T.grQ γ := fun _ =>
rfl`.

**Proof obligations left as sorries (the unit's proof work).**
* the lattice-support leg of `packE.slotCoeff`: each component lives at
  `γ = n/strTop` — LAT (CL-07) at any level-set member + levelSet-emptiness ⇒ zero
  component elsewhere (empty restriction gives the zero polynomial, `inGr` of 0 is
  0; off-lattice γ has `inGr = 0` by the DefsCar dif-convention).
* the lattice-support leg of `monoE`: nonzero only at `γ = ht c` (T3 + `mono_ne`,
  CL-27(a)), which is on the lattice by CL-07.

**E-phase resolutions recorded.**
* **UNIVERSE PIN (flagged for the orchestrator).** `CarrierPackR` fixes
  `Digit : Type` (universe 0), and display (8) sets `Digit := ↥(T.stg 0).FQ`, a
  subtype of the ambient `F`. This file therefore pins `F : Type` (universe 0) —
  `↥FQ : Type u` cannot inhabit `Digit : Type` for `u > 0`, and `CarrierPackR` is an
  EXISTING file (new-files-only discipline: not re-keyed here). CONSUMER IMPLICATION
  (CL-14…CL-19, other cluster): `R6_carrierInstance` is stated over `{F : Type*}`;
  the CL-19 assembly via `packE` discharges it at universe-0 instances only — either
  the R6 statement's universe is ratified down to `Type`, or a `Digit` shrink is
  added, at CL-19. Every planned gate instance (`GaloisField 2 2`) lives in `Type`.
* `packE.slotCoeff`'s restriction is transcribed with `if c ∈ T.levelSet b γ then
  y c else 0` (classical `if` on Set membership) — display (8) verbatim.
* `interiorEnd`'s guard is transcribed `if i ≤ T.K then rl.interiorEnd i else 0`
  (display (8); makes DOM's `i > K` leg vacuous — CL-18).
* `Hist := Unit` (display (8)); all `Hist`-indexed fields discard the argument.

**Deps.** CL-07, CL-08 (+ R1's `CarrierPackR`; statement-only — independent of the
CL-06 (i-b) repair, which edits `LSTStmt'`, not the pack shape). difficulty:
routine-opus. Size: ~80. hyp: `TowerRealizable T` (the `rl` argument).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open scoped Classical

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F]

/-- **monoE** (display (8)): the graded expansion of a basis monomial — the class of
`T.mono c` in every piece (nonzero only at `γ = ht c`, on the lattice by CL-07). -/
noncomputable def monoE (T : Tower p F) (c : T.Coord) : LatticeExp T :=
  ⟨fun γ => T.inGr γ (T.mono c), by sorry⟩

/-- **Display (8), packE**: the graded-expansion carrier pack over the real tower
data — `G := gradedExpCarrier T` (so `Gr = T.grQ`, the non-vacuity pin), real
coordinates/heights/blocks/level sets, `F_Q`-digits, the per-level `slotCoeff`
display, `monoE` monomials, `rl`-lines with the `i > K` interior guard, and the
trivial window. -/
noncomputable def packE (T : Tower p F) (rl : TowerRealizable T) : CarrierPackR p where
  G := gradedExpCarrier T
  Hist := Unit
  Coord := T.Coord
  Digit := ↥(T.stg 0).FQ
  kIdx _ := T.K
  ht _ := T.ht
  blk _ := T.blk
  lvl _ b γ := T.levelSet b γ
  slotCoeff _ b y :=
    (⟨fun γ => T.inGr γ (T.slotCoeff b (fun c => if c ∈ T.levelSet b γ then y c else 0)),
      by sorry⟩ : LatticeExp T)
  aDim _ := T.aDim
  lines _ := rl.line
  blockEdge _ := T.blockEdge
  interiorEnd _ i := if i ≤ T.K then rl.interiorEnd i else 0
  window _ _ := True
  mono _ := monoE T
  floorB _ := rl.floorB

/-- **The Gr-pin** (the non-vacuity clause of R6, display (8)): packE's graded pieces
ARE the tower's real pieces, definitionally. -/
theorem packE_gr_pin (T : Tower p F) (rl : TowerRealizable T) :
    ∀ γ : ℚ, (packE T rl).G.Gr γ = T.grQ γ := fun _ => rfl

end LeanUrat.HC1

#print axioms LeanUrat.HC1.packE
#print axioms LeanUrat.HC1.packE_gr_pin
