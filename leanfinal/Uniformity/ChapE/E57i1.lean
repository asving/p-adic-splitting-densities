/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E57p

/-!
# Uniformity.ChapE.E57i1 — DEC1-N1: the split row's PARENT (`mixBlock`, `mixIface`)

**Node DEC1-N1** of the GC-13 bridge plan
(`docs/in-progress/GC13_BRIDGE_PLAN_2026-08-25.md`, §3). Produces the SPLIT row's PARENT
block/interface pair: `F = X² − 1 = (X + 1)(X − 1)`, one side `(1,1)`, TWO unit-weight
linear classes (labels `1`, `−1` — the two factors' digits). This is the A-E.6
countermodel's interface SHAPE (`E57pCert.dupBlock`/`dupIface`, `F = X²`, the exact shape
where `hpart : True` made re-signed E.57 FALSE) realized at a LEGAL, separable polynomial
instead. Sibling nodes assemble the leg over this parent: `N2` (`E57i2.lean`, landed) the
second child `pureBlock₂`/`pureIface₂`; `N3`–`N5` (`E57i.lean`) the ledger, product,
disjointness, degree/purity field-groups and the assembly, consuming `mixBlock`/`mixIface`
from this file plus the landed `E57pCert.pureBlock`/`pureIface` (the label-`1` child, not
rebuilt).

TEMPLATE: `E57pCert.dupBlock`/`dupIface` (`Uniformity/ChapE/E57p.lean:633–700`), copied
field by field, changing `F`, `A`, the two labels, and the `F`-touching proofs. `Φ = X`
here (not `dupBlock`'s `X + 1`), so `hΦdeg` is the simpler `pureBlock` shape
(`by simp [flatCarrier]`). The interface's numeric laws (`hresdeg`, `haccount`,
`hnonempty`, `hforce`, `hexhaust`, `hlen_sum`) are label-independent and reuse `dupIface`'s
proofs verbatim (only the carrier-def name under `simp` changes).

DEPENDS: `Uniformity.ChapE.E57p` (`BlockData`, `RungInterface`, `E57pCert.flatCarrier`).

Closing `example`: `DEC1Check.N1_target`'s body, byte-copied from
`leanfinal/scratch/DEC1_check.lean` (the anti-drift pin — that file is scratch, not
importable, so the check target cannot be referenced by name).

## Status

Sorry-free, axiom-free, `unsafe`-free: `mixBlock` and `mixIface` report at most the
Lean-core triple `{propext, Classical.choice, Quot.sound}` (census at end of file).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

open Polynomial E57pCert

namespace E57iCert

/-! ## The split row's parent: block for `F = X² − 1 = (X + 1)(X − 1)` -/

/-- **DEC1-N1** — the split row's parent block: key `X`, `F = X² − 1`, mass `2`
(`E57pCert.dupBlock`'s countermodel SHAPE — `F = X²` — realized at a legal separable
polynomial: `A := fun j => if j = 0 then -1 else 0`). -/
noncomputable def mixBlock : BlockData flatCarrier where
  Φ := X
  F := X ^ 2 - 1
  μ := 2
  hμ := by norm_num
  hΦ := monic_X
  hΦdeg := by simp [flatCarrier]
  A := fun j => if j = 0 then -1 else 0
  hdev := by
    show (X ^ 2 - 1 : Polynomial ℤ) = X ^ 2 + ∑ j ∈ Finset.range 2, _ * X ^ j
    simp
    ring
  hdegA := by
    intro j hj
    rcases j with _ | _ | j
    · simp [flatCarrier]
    · simp [flatCarrier]
    · omega
  hkeyfree := by
    refine ⟨-1, X, ?_⟩
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
    ring
  hA0 := by norm_num
  T := 0

/-- **DEC1-N1** — the split row's parent interface: one side `(1,1)`, TWO unit-weight
linear classes, labels `1` and `−1` (the two factors' digits). Numeric laws identical in
shape to `dupIface`'s — only the labels differ, and none of the five clause families read
the labels themselves. -/
noncomputable def mixIface : RungInterface.{0, 0, 0} flatCarrier mixBlock where
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
    simp [mixBlock]
  len := fun _ => 2
  hlen_pos := fun _ _ => by norm_num
  hlen_sum := by simp [mixBlock]
  linFac := fun _ => {((1 : ℚ), 1), ((-1 : ℚ), 1)}
  hiFac := fun _ => 0
  hresdeg := by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    simp
  rootCount := fun _ => 2
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

/-- **DEC1-N1 target, discharged** — byte-copied from `scratch/DEC1_check.lean`'s
`DEC1Check.N1_target` (the check file is scratch and not importable, so this is the
anti-drift pin: the statement below is byte-identical to the pinned target's body). -/
example :
    ∃ (B : BlockData flatCarrier) (I : RungInterface.{0, 0, 0} flatCarrier B),
      B.Φ = X ∧ B.F = X ^ 2 - 1 ∧ B.μ = 2 ∧ B.T = 0 ∧
      I.sides = {(1, 1)} ∧ I.len (1, 1) = 2 ∧
      I.linFac (1, 1) = {((1 : ℚ), 1), ((-1 : ℚ), 1)} ∧ I.hiFac (1, 1) = 0 ∧
      I.classCount (1, 1) ((1 : ℚ), 1) = 1 ∧ I.classCount (1, 1) ((-1 : ℚ), 1) = 1 :=
  ⟨mixBlock, mixIface, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end E57iCert

end Uniformity.Density.Ladder

/-! ## Axiom footprint (Lean core only — no repo axiom, no stub axiom enters) -/

section AxCheck

#print axioms Uniformity.Density.Ladder.E57iCert.mixBlock
#print axioms Uniformity.Density.Ladder.E57iCert.mixIface

end AxCheck
