/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E57p

/-!
# Uniformity.ChapE.E57i2 — DEC1-N2: the split row's SECOND child (`pureBlock₂`/`pureIface₂`)

**Node DEC1-N2** of the GC-13 bridge plan
(`docs/in-progress/GC13_BRIDGE_PLAN_2026-08-25.md`, §3). Produces the second of the two
linear-class children the SPLIT row's leg (`DEC1-N3`–`N5`, sibling files) assembles from:
the block/interface pair for the factor `X − 1` (label `−1`) of the SPLIT row's parent
`F = X² − 1 = (X + 1)(X − 1)` (`DEC1-N1`'s `mixBlock`/`mixIface`, a sibling file, not
needed here). The label-`1` child is NOT rebuilt: the landed `E57pCert.pureBlock`/
`pureIface` (`Uniformity/ChapE/E57p.lean:535–591`) is reused as-is by `N3`–`N5`.

Template: `E57pCert.pureBlock`/`pureIface` verbatim, `1 → -1` in `A`, `F`, and the label
(exactly the plan's transcription instruction). This is a pure TRANSCRIPTION node: no new
mathematical content beyond the sign flip and its two `F`-touching proof adjustments
(`hkeyfree`'s Bézout witness, `hA0`).

DEPENDS: `Uniformity.ChapE.E57p` (`BlockData`, `RungInterface`, `E57pCert.flatCarrier`).

STATUS: sorry-free, axiom-free, `unsafe`-free — `#print axioms` reports at most the
Lean-core triple `{propext, Classical.choice, Quot.sound}` (census at end of file).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

open Polynomial E57pCert

namespace E57iCert

/-! ## The split row's second child: block for the factor `X − 1` (label `−1`) -/

/-- Block for the split row's second linear child: key `X`, `F = X − 1`, mass `1`
(`E57pCert.pureBlock` with the sign flipped: `A := fun _ => -1`, `F := X - 1`). -/
noncomputable def pureBlock₂ : BlockData flatCarrier where
  Φ := X
  F := X - 1
  μ := 1
  hμ := le_rfl
  hΦ := monic_X
  hΦdeg := by simp [flatCarrier]
  A := fun _ => -1
  hdev := by simp; ring
  hdegA := by intro j hj; simp [flatCarrier]
  hkeyfree := by
    refine ⟨-1, 1, ?_⟩
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one]
    ring
  hA0 := by norm_num
  T := 0

/-- Interface for the split row's second linear child: one side `(1,1)`, one linear class
of weight `1` at label `−1` (`E57pCert.pureIface` with the label flipped). -/
noncomputable def pureIface₂ : RungInterface.{0, 0, 0} flatCarrier pureBlock₂ where
  sides := {(1, 1)}
  hside_cop := by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact ⟨Nat.coprime_one_left 1, le_rfl⟩
  hside_node := by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    simp [pureBlock₂]
  len := fun _ => 1
  hlen_pos := fun _ _ => le_rfl
  hlen_sum := by simp [pureBlock₂]
  linFac := fun _ => {((-1 : ℚ), 1)}
  hiFac := fun _ => 0
  hresdeg := by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    simp
  rootCount := fun _ => 1
  haccount := by intro p hp; simp [flatCarrier]
  classCount := fun _ _ => 1
  classCountHi := fun _ _ => 1
  hnonempty := by
    intro p hp
    exact ⟨fun q _ => le_rfl, fun q hq => by simp at hq⟩
  hforce := by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact ⟨fun q _ => by simp [flatCarrier], fun q hq => by simp at hq⟩
  hexhaust := by intro p hp; simp
  W := Unit
  wf := ⟨fun _ _ => False, ⟨fun a => ⟨a, fun _ h => h.elim⟩⟩⟩
  σRank := ()

/-- **DEC1-N2 target, discharged** — byte-copied from `scratch/DEC1_check.lean`'s
`DEC1Check.N2_target` (the check file is scratch and not importable, so this is the
anti-drift pin: the statement below is byte-identical to the pinned target's body). -/
example :
    ∃ (B : BlockData flatCarrier) (J : RungInterface.{0, 0, 0} flatCarrier B),
      B.Φ = X ∧ B.F = X - 1 ∧ B.μ = 1 ∧ B.T = 0 ∧
      J.sides = {(1, 1)} ∧ J.linFac (1, 1) = {((-1 : ℚ), 1)} ∧ J.hiFac (1, 1) = 0 :=
  ⟨pureBlock₂, pureIface₂, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end E57iCert

end Uniformity.Density.Ladder

/-! ## Axiom footprint (Lean core only — no repo axiom, no stub axiom enters) -/

section AxCheck

#print axioms Uniformity.Density.Ladder.E57iCert.pureBlock₂
#print axioms Uniformity.Density.Ladder.E57iCert.pureIface₂

end AxCheck
