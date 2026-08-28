/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C136t
import Uniformity.ChapC.C130tr
import Uniformity.ChapC.C130ln

/-!
# Uniformity.ChapC.C136r0 — the depth-four terminal receiver and Laurent normalizer [R0]

**Node R0** of `docs/in-progress/DEEP_WITNESS_CAMPAIGN_2026-08-28.md` §6.4 (row R0: *"Build
depth-four `TerminalReceiver` and `LaurentNormalizer`; pin level maps and exact heights"*).
Inputs: the landed generic `DeepTower.terminalReceiver` (C130tr, CC-3) and
`DeepTower.laurentNormalizer` (C130ln, CC-4), instantiated at the campaign's T3 tower datum
`s2WitnessFour`/`s2DepthFour` (`C136t`, landed, zero `sorry`).  Blocker: none.

## The instantiation

Both generic constructions are already unconditional at ANY `DeepTower`; this node only
supplies the depth-four witness and pins the resulting level maps / exact-height law,
mirroring the depth-two precedent (`C130s17.s2TerminalReceiver`,
`(S2DepthTwo h2 hq).laurentNormalizer`) one level up in `r`.

* `s2TerminalReceiverFour` — `(s2DepthFour h2 hq).terminalReceiver junk` with the SAME
  trivial junk filler the depth-two occurrence uses (`fun _ _ _ => RingHom.id _`): C.97's
  witness (extended by T3 to depth four) still uses one constant stage field at every
  index, so every off-range hom type is literally `Kt →+* Kt` and `RingHom.id` fills it.
* `s2LaurentNormalizerFour` — `(s2DepthFour h2 hq).laurentNormalizer`, unconditional since
  the C.130f one-token repair (`levelExponentHeight` now carries `T.ehat`, not `T.e`, at
  the Φ-weight denominator) is already landed.
* Level-map pins: `topEquiv = RingEquiv.refl`, the terminal-level field
  (`levelHom 4 = topEquiv.toRingHom`), the live-range step-composite identity at each of
  the four live levels (`terminalReceiver_levelHom_live`, specialized), and injectivity at
  every level.
* Exact-height pins: `norm = laurentNormAt` and `norm_zero` (both direct field/def
  unfoldings), the universal live-range exact-height law specialized to this tower
  (`exact_height`), and its instances at the campaign's own numerals — `u_2 = 5`,
  `u_3 = 21`, the T4 operator height `85`, and the T5 refinement height `171` — so every
  height the D3/D4 stacks will consume is pinned as a literal equation, not merely
  asserted to exist.

Per the TSTK fleet lesson (no bare `rfl` through internals gated by an `ite`/`dite`): the
level-map live-range pin is discharged by `show`-ing the definitional unfolding of
`s2TerminalReceiverFour` before invoking the landed `terminalReceiver_levelHom_live`
theorem, never by a bare `rfl` against the `dite`-branched `receiverLevelHom`.

GCW-6 fence: this file is DATA (a `TerminalReceiver` and a `LaurentNormalizer` instance
plus pins), not a wired witness — no `SplitNodePointSource`, `ChainRealization`, or
`RealizedInput` is touched; that is R6/R7/R9.

## Status

Zero `sorry`; no new axiom; axiom footprint Lean-core only (AxCheck footer).  No landed
statement is touched.  Verdict: `runs/wave-c/verdict_R0.md`.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C136r0

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C136t

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## The depth-four canonical terminal receiver -/

/-- **R0 — the depth-four canonical terminal receiver.**  Exactly the depth-two pattern
(`C130s17.s2TerminalReceiver`) one level up: the campaign's `s2DepthFour` still uses one
constant stage field at every index, so the off-range `junk` filler is literally
`RingHom.id`. -/
noncomputable def s2TerminalReceiverFour :
    TerminalReceiver (s2Frame h2 hq) 1 (s2Frame_pin h2 hq) 4
      (s2DepthFour h2 hq) ((s2DepthFour h2 hq).fld 4) :=
  (s2DepthFour h2 hq).terminalReceiver (fun _ _ _ => RingHom.id _)

/-- **R0 — the depth-four Laurent normalizer.**  Unconditional: post the C.130f one-token
repair, `laurentNormalizerOfAgree`'s agreement hypothesis is `fun _ _ _ => rfl`. -/
noncomputable def s2LaurentNormalizerFour : LaurentNormalizer (s2DepthFour h2 hq) :=
  (s2DepthFour h2 hq).laurentNormalizer

/-! ## Level-map pins -/

/-- The terminal equivalence is `RingEquiv.refl`, exactly as at depth two — a direct
unfolding, no `dite` branch is crossed. -/
theorem s2TerminalReceiverFour_topEquiv :
    (s2TerminalReceiverFour h2 hq).topEquiv = RingEquiv.refl ((s2DepthFour h2 hq).fld 4) := by
  show ((s2DepthFour h2 hq).terminalReceiver (fun _ _ _ => RingHom.id _)).topEquiv =
    RingEquiv.refl ((s2DepthFour h2 hq).fld 4)
  exact DeepTower.terminalReceiver_topEquiv _ _

/-- ★ **R0 — the live-range level-map pin.**  On the live range `1 ≤ j ≤ 4`, the receiver's
level map is the telescope's step composite `towerHom j` — it never reads the (here
trivial) junk filler.  Discharged by `show`-ing the definitional unfolding of
`s2TerminalReceiverFour` before invoking the landed CC-3 theorem, per the TSTK discipline:
no bare `rfl` is attempted against the `dite`-branched `receiverLevelHom`. -/
theorem s2TerminalReceiverFour_levelHom_live {j : ℕ} (hj : StageLive 4 j) :
    (s2TerminalReceiverFour h2 hq).levelHom j =
      (s2DepthFour h2 hq).towerHom j hj.1 hj.2 := by
  show ((s2DepthFour h2 hq).terminalReceiver (fun _ _ _ => RingHom.id _)).levelHom j =
    (s2DepthFour h2 hq).towerHom j hj.1 hj.2
  exact DeepTower.terminalReceiver_levelHom_live _ _ hj

/-- The terminal-level field, restated at the depth-four instance: `levelHom 4` IS
`topEquiv.toRingHom` — a direct structure-field read, no unfolding needed. -/
theorem s2TerminalReceiverFour_levelHom_terminal :
    (s2TerminalReceiverFour h2 hq).levelHom 4 =
      (s2TerminalReceiverFour h2 hq).topEquiv.toRingHom :=
  (s2TerminalReceiverFour h2 hq).levelHom_terminal

/-- Explicit pin, level `1`. -/
theorem s2TerminalReceiverFour_levelHom_one :
    (s2TerminalReceiverFour h2 hq).levelHom 1 =
      (s2DepthFour h2 hq).towerHom 1 (by decide) (by decide) :=
  s2TerminalReceiverFour_levelHom_live h2 hq (by decide)

/-- Explicit pin, level `2`. -/
theorem s2TerminalReceiverFour_levelHom_two :
    (s2TerminalReceiverFour h2 hq).levelHom 2 =
      (s2DepthFour h2 hq).towerHom 2 (by decide) (by decide) :=
  s2TerminalReceiverFour_levelHom_live h2 hq (by decide)

/-- Explicit pin, level `3`. -/
theorem s2TerminalReceiverFour_levelHom_three :
    (s2TerminalReceiverFour h2 hq).levelHom 3 =
      (s2DepthFour h2 hq).towerHom 3 (by decide) (by decide) :=
  s2TerminalReceiverFour_levelHom_live h2 hq (by decide)

/-- Explicit pin, level `4` (the terminal level, via the terminal field). -/
theorem s2TerminalReceiverFour_levelHom_four :
    (s2TerminalReceiverFour h2 hq).levelHom 4 =
      (s2TerminalReceiverFour h2 hq).topEquiv.toRingHom :=
  s2TerminalReceiverFour_levelHom_terminal h2 hq

/-- Injectivity at every level (including junk levels — none occur here since the tower is
constant, but the pin is stated at full CC-3 generality). -/
theorem s2TerminalReceiverFour_levelHom_injective (j : ℕ) :
    Function.Injective ((s2TerminalReceiverFour h2 hq).levelHom j) :=
  TerminalReceiver.levelHom_injective (s2TerminalReceiverFour h2 hq) j

/-! ## Exact-height pins -/

/-- The normalizer's raw section IS the Laurent solve section — a direct unfolding through
two plain `def`s, no `ite`/`dite` crossed. -/
theorem s2LaurentNormalizerFour_norm_eq :
    (s2LaurentNormalizerFour h2 hq).norm = (s2DepthFour h2 hq).laurentNormAt := rfl

/-- `n(0) = 1` at every level, restated at the depth-four instance — a direct field read. -/
theorem s2LaurentNormalizerFour_norm_zero (i : ℕ) :
    (s2LaurentNormalizerFour h2 hq).norm i 0 = 1 :=
  (s2LaurentNormalizerFour h2 hq).norm_zero i

/-- ★ **R0 — the live-range exact-height pin.**  On the live range `1 ≤ j ≤ 4`, the
depth-four normalizer hits every integer height `k` exactly, against the landed
(post-repair) `levelExponentHeight` — a direct field read, no unfolding needed since the
field's value at this instance is exactly this law. -/
theorem s2LaurentNormalizerFour_exact_height {j : ℕ} (hj : StageLive 4 j) (k : ℤ) :
    levelExponentHeight (s2DepthFour h2 hq) j ((s2LaurentNormalizerFour h2 hq).norm j k) =
      Multiplicative.ofAdd k :=
  (s2LaurentNormalizerFour h2 hq).exact_height j hj k

/-- Exact height at level `2`, height `u_2 = 5`. -/
theorem s2LaurentNormalizerFour_exact_height_five :
    levelExponentHeight (s2DepthFour h2 hq) 2
        ((s2LaurentNormalizerFour h2 hq).norm 2 (5 : ℤ)) =
      Multiplicative.ofAdd (5 : ℤ) :=
  s2LaurentNormalizerFour_exact_height h2 hq (by decide) 5

/-- Exact height at level `3`, height `u_3 = 21`. -/
theorem s2LaurentNormalizerFour_exact_height_twentyone :
    levelExponentHeight (s2DepthFour h2 hq) 3
        ((s2LaurentNormalizerFour h2 hq).norm 3 (21 : ℤ)) =
      Multiplicative.ofAdd (21 : ℤ) :=
  s2LaurentNormalizerFour_exact_height h2 hq (by decide) 21

/-- Exact height at level `3`, the T4 operator height `85` (the depth-three `(2,1,85)`
calculus's own rung value). -/
theorem s2LaurentNormalizerFour_exact_height_eightyfive :
    levelExponentHeight (s2DepthFour h2 hq) 3
        ((s2LaurentNormalizerFour h2 hq).norm 3 (85 : ℤ)) =
      Multiplicative.ofAdd (85 : ℤ) :=
  s2LaurentNormalizerFour_exact_height h2 hq (by decide) 85

/-- Exact height at level `4`, the T5 refinement height `171` (the `(1,1,171)` normalizer's
own rung value — the height whose polynomial value is T5's `s2Mu5Lambda`). -/
theorem s2LaurentNormalizerFour_exact_height_oneseventyone :
    levelExponentHeight (s2DepthFour h2 hq) 4
        ((s2LaurentNormalizerFour h2 hq).norm 4 (171 : ℤ)) =
      Multiplicative.ofAdd (171 : ℤ) :=
  s2LaurentNormalizerFour_exact_height h2 hq (by decide) 171

end Uniformity.Density.Tower.C136r0

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C136r0.s2TerminalReceiverFour
#print axioms Uniformity.Density.Tower.C136r0.s2LaurentNormalizerFour
#print axioms Uniformity.Density.Tower.C136r0.s2TerminalReceiverFour_topEquiv
#print axioms Uniformity.Density.Tower.C136r0.s2TerminalReceiverFour_levelHom_live
#print axioms Uniformity.Density.Tower.C136r0.s2TerminalReceiverFour_levelHom_terminal
#print axioms Uniformity.Density.Tower.C136r0.s2TerminalReceiverFour_levelHom_one
#print axioms Uniformity.Density.Tower.C136r0.s2TerminalReceiverFour_levelHom_two
#print axioms Uniformity.Density.Tower.C136r0.s2TerminalReceiverFour_levelHom_three
#print axioms Uniformity.Density.Tower.C136r0.s2TerminalReceiverFour_levelHom_four
#print axioms Uniformity.Density.Tower.C136r0.s2TerminalReceiverFour_levelHom_injective
#print axioms Uniformity.Density.Tower.C136r0.s2LaurentNormalizerFour_norm_eq
#print axioms Uniformity.Density.Tower.C136r0.s2LaurentNormalizerFour_norm_zero
#print axioms Uniformity.Density.Tower.C136r0.s2LaurentNormalizerFour_exact_height
#print axioms Uniformity.Density.Tower.C136r0.s2LaurentNormalizerFour_exact_height_five
#print axioms Uniformity.Density.Tower.C136r0.s2LaurentNormalizerFour_exact_height_twentyone
#print axioms Uniformity.Density.Tower.C136r0.s2LaurentNormalizerFour_exact_height_eightyfive
#print axioms Uniformity.Density.Tower.C136r0.s2LaurentNormalizerFour_exact_height_oneseventyone

end AxCheck
