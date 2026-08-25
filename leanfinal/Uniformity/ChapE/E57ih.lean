/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E57p

/-!
# Uniformity.ChapE.E57ih — DEC1-N6 (+ N7, a wave-2 sibling section not yet landed): the HI row

**Node DEC1-N6** of the GC-13 bridge plan
(`docs/in-progress/GC13_BRIDGE_PLAN_2026-08-25.md`, §3). Produces the HI row's parent
block/interface pair: `F = X² + X + 1` over the landed flat carrier
(`Uniformity.ChapE.E57p`'s `E57pCert.flatCarrier`), one side `(1,1)`, ONE higher residual
class of degree `2` and multiplicity `1` (the inert shape — no linear residual at all).
This is the branch `hclsHi`/`hpureHi`/`dvd_classCount_hi` that no landed gate exercises
(`E57pCert.pure` is lin-only; `E57pCert.dup`'s countermodel is lin-only too).

This file is **PART 1 only** (node N6): `hiBlock`, `hiIface`, and the closing byte-copied
target check. Node **DEC1-N7** (assembly + firing `block_split_of_partitionLeg` at this row)
is a wave-2 sibling that EXTENDS this same file — it is deliberately NOT attempted here.
N6's content is complete and self-verifying on its own: the file compiles standalone.

Template: `E57pCert.dupBlock`/`dupIface` (`Uniformity/ChapE/E57p.lean:633–700`), same
interface *shape* (one side, flat carrier, `T = 0`), but now with the hi-side laws live
instead of two linear labels — the genuinely new proof content is `hkeyfree`'s Bézout
witness and the hi-branch reads of `hresdeg`/`haccount`/`hnonempty`/`hforce`/`hexhaust`.

DEPENDS: `Uniformity.ChapE.E57p` (`BlockData`, `RungInterface`, `E57pCert.flatCarrier`).

STATUS (N6 only): sorry-free, axiom-free, `unsafe`-free — `#print axioms` reports at most
the Lean-core triple `{propext, Classical.choice, Quot.sound}` (census at end of file).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

open Polynomial E57pCert

namespace E57iCert

/-! ## The HI row's parent: block for `F = X² + X + 1` (the inert shape) -/

/-- Block for the HI row: key `X`, `F = X² + X + 1`, mass `2`. The development coefficients
`A 0 = A 1 = 1` (`F = X² + 1·X + 1·1`), matching the inert parent's shape. -/
noncomputable def hiBlock : BlockData flatCarrier where
  Φ := X
  F := X ^ 2 + X + 1
  μ := 2
  hμ := by norm_num
  hΦ := monic_X
  hΦdeg := by simp [flatCarrier]
  A := fun j => if j = 0 then 1 else if j = 1 then 1 else 0
  hdev := by simp [Finset.sum_range_succ]; ring
  hdegA := by
    intro j hj
    rcases j with _ | _ | j
    · simp [flatCarrier]
    · simp [flatCarrier]
    · omega
  hkeyfree := by
    refine ⟨1, -(X + 1), ?_⟩
    simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
    ring
  hA0 := by simp
  T := 0

/-- Interface for the HI row: one side `(1,1)`, ONE higher residual class of degree `2`,
multiplicity `1` (`hiFac ≡ {(2,1)}`), no linear residual at all (`linFac ≡ 0`). The class
weight `classCountHi (1,1) (2,1) = 2` saturates `hforce`'s hi lower bound
`D·ℓ·deg = 1·1·2 = 2` exactly (the inert shape has no slack). -/
noncomputable def hiIface : RungInterface.{0, 0, 0} flatCarrier hiBlock where
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
    simp [hiBlock]
  len := fun _ => 2
  hlen_pos := fun _ _ => by norm_num
  hlen_sum := by simp [hiBlock]
  linFac := fun _ => 0
  hiFac := fun _ => {(2, 1)}
  hresdeg := by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    simp
  rootCount := fun _ => 2
  haccount := by intro p hp; simp [flatCarrier]
  classCount := fun _ _ => 1
  classCountHi := fun _ _ => 2
  hnonempty := by
    intro p hp
    exact ⟨fun q hq => by simp at hq, fun q _ => by norm_num⟩
  hforce := by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    refine ⟨fun q hq => by simp at hq, fun q hq => ?_⟩
    have hq2 : q = (2, 1) := by simpa using hq
    subst hq2
    simp [flatCarrier]
  hexhaust := by intro p hp; simp
  W := Unit
  wf := ⟨fun _ _ => False, ⟨fun a => ⟨a, fun _ h => h.elim⟩⟩⟩
  σRank := ()

/-- **DEC1-N6 target, discharged** — byte-copied from `scratch/DEC1_check.lean`'s
`DEC1Check.N6_target` (the check file is scratch and not importable, so this is the
anti-drift pin: the statement below is byte-identical to the pinned target's body). -/
example :
    ∃ (B : BlockData flatCarrier) (I : RungInterface.{0, 0, 0} flatCarrier B),
      B.Φ = X ∧ B.F = X ^ 2 + X + 1 ∧ B.μ = 2 ∧ B.T = 0 ∧
      I.sides = {(1, 1)} ∧ I.linFac (1, 1) = 0 ∧ I.hiFac (1, 1) = {(2, 1)} ∧
      I.classCountHi (1, 1) (2, 1) = 2 :=
  ⟨hiBlock, hiIface, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end E57iCert

end Uniformity.Density.Ladder

/-! ## Axiom footprint (Lean core only — no repo axiom, no stub axiom enters), N6 only -/

section AxCheck

#print axioms Uniformity.Density.Ladder.E57iCert.hiBlock
#print axioms Uniformity.Density.Ladder.E57iCert.hiIface

end AxCheck
