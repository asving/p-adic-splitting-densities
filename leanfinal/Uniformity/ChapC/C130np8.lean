/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130ar
import Uniformity.ChapC.C130s17

/-!
# Uniformity.ChapC.C130np8 — S2-source plan node NP-8

**S2-source plan node NP-8** (`docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §6, row NP-8:
"Construct `arenaRead`, `towerRead`, and `peelUnit`; lint that no canonical/arena equality was
introduced"): the concrete terminal-field arena data for the S2 depth-two tower
`S2DepthTwo h2 hq`, in the exact field shapes of C130k's `NodePointSource` / C130s17's
`SplitNodePointSource` (`.arenaRead`/`.towerRead`/`.peelUnit` are byte-parallel between the
two structures — the ambient split touches only the four evaluation fields), together with
the instantiation of CC-11's (`C130ar`) GENERAL arena-family layer at these concrete values.

## Why `arenaRead`/`peelUnit` collapse to the trivial value, and `towerRead` does not

The terminal field is `Kt := (S2DepthTwo h2 hq).fld 2`, the 2-element field pinned by
`s2Fld₂_card` (CC-6, `C130s6`).  Two of the three W-leg fields land in `Ktˣ`, whose
cardinality a 2-element field forces to exactly **one**:

* **`arenaRead`/`peelUnit`** (codomain `Ktˣ`): `Ktˣ` is a `Subsingleton` — UNCONDITIONALLY,
  with no nonzero/live-index hypothesis needed at all (contrast `C130np6`'s `s2Letter`, which
  needs the `letter_ne_zero` hypothesis before the 2-element FIELD `Kt` collapses a candidate
  to `1`).  Here there is only one unit to begin with, so EVERY candidate value of either
  field, at EVERY index whatsoever (live or junk), is FORCED to equal the trivial choice
  (`s2ArenaRead_forced`/`s2PeelUnit_forced` below) — this is stronger than a computation: it
  is the only admissible term, full stop.
* **`towerRead`** (codomain `Kt` itself, not `Ktˣ`): `Kt` has TWO elements, so no such
  collapse applies; the field is genuinely free — D.44 faithfulness item 2 licenses exactly
  this ("the read is an arbitrary function... evaluated only at ladder points"), and no B-law
  instance is claimed at any level (`C130ar`'s design fence).  The concrete choice
  `s2TowerRead := 0` is a convenience, not a forced value; `s2Kt_zero_ne_one` records that `0`
  and `1` remain genuinely distinct candidates, and `s2Kt_eq_zero_or_one` records the honest
  "small values" fact that IS forced here: every element of `Kt` is one of exactly the two
  numerals `0`/`1`.

## What this node does NOT deliver (named per plan row)

No `SplitNodePointSource` (or `NodePointSource`) instance is assembled or claimed inhabited —
that needs NP-0..NP-7 and the RP-*/KP-* residual cores (and, for the un-split `NodePointSource`,
is in fact impossible at this receiver/key pair, U13).  No `ambientLetter`/`psi_root`/
`letter_ne_zero` (NP-6, `C130np8`'s sibling `C130np6`) and no residue-ambient read (NP-7, in
flight elsewhere).  This node supplies exactly the three named field values, their live-index
computation, and the CC-11 arena-family instantiation, ready for the later `FD-0`/`SG-0`
assembly.

## Instantiating CC-11 directly, not through `NodePointSource`

CC-11's family constructors (`NodePointSource.gaugeArenaAt`/`.arenaRead0`/`.gaugeArena0At`/
`.gaugeArenaFamily0`/`.towerReadFamily0`/`.peelUnitFamily`, `C130ar`) are methods of a
`NodePointSource` instance.  That structure's node source is uninhabitable at the S2
repository realization's receiver/keys for ANY choice of its fields whatsoever (U13's
char-two argument bites on `coeffHom`/`pointHgt_eval`, entirely independently of
`arenaRead`/`towerRead`/`peelUnit`).  So this file reconstructs CC-11's arena/family
BODIES directly against the concrete fields, exactly byte-parallel to the general
constructors but with no `NodePointSource` wrapper — the standalone helpers CC-11 exports
(`arenaKerProj`, `LaurentNormalizer.arenaNormSectionAt`/`.arenaNormSection0`,
`gaugeLive_exists_iff`) are reused verbatim, never duplicated.

**DEPENDS.** `C130ar` (CC-11: `arenaKerProj`, `LaurentNormalizer.arenaNormSectionAt`/
`.arenaNormSection0`, `gaugeLive_exists_iff` — reused verbatim) · `C130s17` (`S2DepthTwo`,
`SplitNodePointSource`'s field shapes) · `C130s2` (CC-2: `S2DepthTwo`'s literal tower,
transitively) · `C130s6` (CC-6: `s2Fld₂_card`) · `C130k` (`NodePointSource`'s byte-parallel
field shapes, read only — no instance of it is claimed here).

## Status

Zero `sorry`; no new axiom; no `unsafe`; no `True` body; axiom footprint Lean-core only
(AxCheck footer).  No cite.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C130np8

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower Uniformity.Density.Gauge
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C130s17

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## 1. `Ktˣ` collapses to a single point -/

/-- private copy of the campaign's card-forcing pattern (`C130s6.fld₂_eq_one_of_ne_zero` /
`C130np6.np6_fld₂_eq_one_of_ne_zero`: `private` does not export), aimed at the UNIT GROUP
`Ktˣ` rather than the field `Kt` — `|Kt| = 2` forces `|Ktˣ| = 1` unconditionally. -/
private theorem np8_units_subsingleton :
    Subsingleton ((S2DepthTwo h2 hq).fld 2)ˣ := by
  haveI : Finite ((S2DepthTwo h2 hq).fld 2) :=
    Nat.finite_of_card_ne_zero (by rw [s2Fld₂_card h2 hq]; norm_num)
  have hu : Nat.card ((S2DepthTwo h2 hq).fld 2)ˣ = 1 := by
    rw [Nat.card_units, s2Fld₂_card h2 hq]
  exact (Nat.card_eq_one_iff_unique.mp hu).1

/-- ★ The forcing fact itself, named for reuse: EVERY unit of the S2 terminal field is `1` —
unconditionally, no nonzero hypothesis needed (there is only one unit to begin with). -/
theorem s2Unit_eq_one (u : ((S2DepthTwo h2 hq).fld 2)ˣ) : u = 1 :=
  @Subsingleton.elim _ (np8_units_subsingleton h2 hq) u 1

/-- private copy of the field-side collapse (mirrors `C130np6.np6_fld₂_eq_one_of_ne_zero`,
rebuilt here from `s2Unit_eq_one` rather than duplicating the `Nat.card` computation). -/
private theorem np8_fld_eq_one_of_ne_zero {c : (S2DepthTwo h2 hq).fld 2} (hc : c ≠ 0) :
    c = 1 := by
  have h1 : hc.isUnit.unit = 1 := s2Unit_eq_one h2 hq hc.isUnit.unit
  calc c = ((hc.isUnit.unit : ((S2DepthTwo h2 hq).fld 2)ˣ) : (S2DepthTwo h2 hq).fld 2) :=
        (hc.isUnit.unit_spec).symm
    _ = 1 := by rw [h1]; rfl

/-- ★ The honest "small values" fact for the FIELD (not just the unit group): every element
of `Kt` is one of exactly the two numerals `0`/`1` — the collapse `towerRead`'s codomain
genuinely admits, contrasted with `Ktˣ`'s single point above. -/
theorem s2Kt_eq_zero_or_one (c : (S2DepthTwo h2 hq).fld 2) : c = 0 ∨ c = 1 := by
  rcases eq_or_ne c 0 with h | h
  · exact Or.inl h
  · exact Or.inr (np8_fld_eq_one_of_ne_zero h2 hq h)

/-- Contrast fact: unlike `Ktˣ` (forced to a single point by `s2Unit_eq_one`), the codomain
`Kt` of `towerRead` has (at least) two DISTINCT elements — `0` and `1` — so no cardinality
argument forces a unique value there; `s2TowerRead`'s concrete choice below is a genuine
convenience, not a forced term. -/
theorem s2Kt_zero_ne_one : (0 : (S2DepthTwo h2 hq).fld 2) ≠ 1 := zero_ne_one

/-! ## 2. The three W-leg field values, live-index computation -/

/-- ★ **the `arenaRead` field, live-index construction**: the trivial monoid hom, at every
index — the unique admissible value (`s2ArenaRead_forced` below), since `Ktˣ` has exactly
one element. -/
noncomputable def s2ArenaRead (i : ℕ) :
    MonoidHom.ker (levelExponentHeight (S2DepthTwo h2 hq) i) →*
      ((S2DepthTwo h2 hq).fld 2)ˣ where
  toFun := fun _ => 1
  map_one' := rfl
  map_mul' := fun _ _ => (mul_one (1 : ((S2DepthTwo h2 hq).fld 2)ˣ)).symm

/-- Anti-drift pin: the arena read's `Kt`-value is the numeral `1`, at every index and every
kernel element. -/
theorem s2ArenaRead_apply {i : ℕ}
    (x : MonoidHom.ker (levelExponentHeight (S2DepthTwo h2 hq) i)) :
    (s2ArenaRead h2 hq i x : (S2DepthTwo h2 hq).fld 2) = 1 := rfl

/-- ★ **the "free arena" defense, no hypothesis needed**: ANY candidate `arenaRead`-shaped
monoid hom, at ANY index, agrees with `s2ArenaRead` — the value is FORCED, not chosen, and
unlike `C130np6.s2Letter_forced` no liveness or nonzero hypothesis is required (`Ktˣ` has
only one element to begin with). -/
theorem s2ArenaRead_forced (i : ℕ)
    (f : MonoidHom.ker (levelExponentHeight (S2DepthTwo h2 hq) i) →*
      ((S2DepthTwo h2 hq).fld 2)ˣ) :
    f = s2ArenaRead h2 hq i :=
  MonoidHom.ext fun x => (s2Unit_eq_one h2 hq (f x)).trans (s2Unit_eq_one h2 hq _).symm

/-- ★ **the `peelUnit` field, live-index construction**: the constant `1`, at every index —
forced, by the same subsingleton argument. -/
noncomputable def s2PeelUnit : ℕ → ((S2DepthTwo h2 hq).fld 2)ˣ := fun _ => 1

/-- Anti-drift pin: the peel unit's `Kt`-value is the numeral `1`, at every index. -/
theorem s2PeelUnit_apply (i : ℕ) :
    (s2PeelUnit h2 hq i : (S2DepthTwo h2 hq).fld 2) = 1 := rfl

/-- ★ the "free peel" defense, no hypothesis needed: ANY candidate `peelUnit` function agrees
with `s2PeelUnit` everywhere — forced, not chosen. -/
theorem s2PeelUnit_forced (w : ℕ → ((S2DepthTwo h2 hq).fld 2)ˣ) :
    w = s2PeelUnit h2 hq :=
  funext fun i => (s2Unit_eq_one h2 hq (w i)).trans (s2Unit_eq_one h2 hq _).symm

/-- ★ **the `towerRead` field, live-index construction**: the constant `0`, at every index —
a FREE choice (see `s2Kt_zero_ne_one`/`s2Kt_eq_zero_or_one` above), never forced; nothing in
the carrier reads this field except through the ladder-point evaluations D.44 licenses. -/
noncomputable def s2TowerRead : (i : ℕ) → LevelExponentLattice i → (S2DepthTwo h2 hq).fld 2 :=
  fun _ _ => 0

/-- Anti-drift pin: the tower read's value is the numeral `0`, at every index and every
lattice point. -/
theorem s2TowerRead_apply (i : ℕ) (g : LevelExponentLattice i) :
    s2TowerRead h2 hq i g = 0 := rfl

/-! ## 3. Instantiating CC-11's arena constructions directly at these concrete values

`CC-11`'s minimality check applies verbatim at `r = 2`: the family hypothesis `1 < r` is
exactly satisfied, with no slack. -/

example : ∃ j, GaugeLive 2 j := (gaugeLive_exists_iff 2).mpr (by omega)

/-- ★ **CC-11 at S2, the level arena**: byte-parallel to `NodePointSource.gaugeArenaAt`, fed
`s2ArenaRead` directly (no `NodePointSource` wrapper — see the module docstring for why one
cannot exist here). -/
noncomputable def s2GaugeArenaAt {i : ℕ} (hi : StageLive 2 i) :
    GaugeArena (LevelExponentLattice i) ((S2DepthTwo h2 hq).fld 2)
      ((S2DepthTwo h2 hq).laurentNormalizer.arenaNormSectionAt i) where
  v := levelExponentHeight (S2DepthTwo h2 hq) i
  exact_height := (S2DepthTwo h2 hq).laurentNormalizer.exact_height i hi
  res := s2ArenaRead h2 hq i

/-- Anti-drift pin (the separateness audit, mechanized): the level arena's residue read IS
`s2ArenaRead`, definitionally. -/
theorem s2GaugeArenaAt_res {i : ℕ} (hi : StageLive 2 i) :
    (s2GaugeArenaAt h2 hq hi).res = s2ArenaRead h2 hq i := rfl

/-- The concrete arena read, restricted to the synchronized product at a live level —
byte-parallel to `NodePointSource.arenaRead0`, reusing CC-11's `arenaKerProj` verbatim. -/
noncomputable def s2ArenaRead0 (j : LiveLevel 2) :
    MonoidHom.ker (levelHeight0 (S2DepthTwo h2 hq) j) →* ((S2DepthTwo h2 hq).fld 2)ˣ :=
  (s2ArenaRead h2 hq j.1).comp (arenaKerProj (S2DepthTwo h2 hq) j)

/-- Anti-drift pin: the synchronized arena read is the componentwise restriction of
`s2ArenaRead`, nothing else. -/
theorem s2ArenaRead0_apply (j : LiveLevel 2)
    (x : MonoidHom.ker (levelHeight0 (S2DepthTwo h2 hq) j)) :
    s2ArenaRead0 h2 hq j x = s2ArenaRead h2 hq j.1 (arenaKerProj (S2DepthTwo h2 hq) j x) := rfl

/-- ★ **CC-11 at S2, the synchronized arena** — byte-parallel to `NodePointSource.gaugeArena0At`,
fed the concrete restriction. -/
noncomputable def s2GaugeArena0At {j : ℕ} (hj : GaugeLive 2 j) :
    GaugeArena (GaugeLattice0 2) ((S2DepthTwo h2 hq).fld 2)
      (S2DepthTwo h2 hq).laurentNormalizer.arenaNormSection0 where
  v := levelHeight0 (S2DepthTwo h2 hq) ⟨j, hj⟩
  exact_height := fun k => (S2DepthTwo h2 hq).laurentNormalizer.exact_height j hj.stageLive k
  res := s2ArenaRead0 h2 hq ⟨j, hj⟩

/-- Anti-drift pin (the separateness audit on the product): the synchronized arena's residue
read is the restricted `s2ArenaRead`, definitionally. -/
theorem s2GaugeArena0At_res {j : ℕ} (hj : GaugeLive 2 j) :
    (s2GaugeArena0At h2 hq hj).res = s2ArenaRead0 h2 hq ⟨j, hj⟩ := rfl

/-- ★ **CC-11 at S2, the arena family** — byte-parallel to
`NodePointSource.gaugeArenaFamily0`; the S2 tower's unique gauge-live index is `j = 1`
(`C130np6.gaugeLive_two_iff`), so the family is genuine there and junk (the same level-1
arena) everywhere else. -/
noncomputable def s2GaugeArenaFamily0 : ℕ →
    GaugeArena (GaugeLattice0 2) ((S2DepthTwo h2 hq).fld 2)
      (S2DepthTwo h2 hq).laurentNormalizer.arenaNormSection0 := fun j =>
  if hj : GaugeLive 2 j then s2GaugeArena0At h2 hq hj
  else s2GaugeArena0At h2 hq (show GaugeLive 2 1 from ⟨le_rfl, by omega⟩)

/-- The non-swallowing audit for the family: on the gauge-live range (`j = 1` at S2) the
family slot is the genuine synchronized arena — the junk filler is never read there. -/
theorem s2GaugeArenaFamily0_live {j : ℕ} (hj : GaugeLive 2 j) :
    s2GaugeArenaFamily0 h2 hq j = s2GaugeArena0At h2 hq hj :=
  dif_pos hj

/-- Off the gauge-live range the family slot holds exactly the level-1 arena (documented
junk, mirroring `NodePointSource.gaugeArenaFamily0_junk`). -/
theorem s2GaugeArenaFamily0_junk {j : ℕ} (hj : ¬ GaugeLive 2 j) :
    s2GaugeArenaFamily0 h2 hq j =
      s2GaugeArena0At h2 hq (show GaugeLive 2 1 from ⟨le_rfl, by omega⟩) :=
  dif_neg hj

/-- ★ **CC-11 at S2, the tower-read family**, D.44's shape — byte-parallel to
`NodePointSource.towerReadFamily0`, fed `s2TowerRead` directly. -/
noncomputable def s2TowerReadFamily0 : ℕ → GaugeLattice0 2 → (S2DepthTwo h2 hq).fld 2 :=
  fun j g => if hj : GaugeLive 2 j then s2TowerRead h2 hq j (g ⟨j, hj⟩) else 0

/-- The non-swallowing audit for the tower read: on the gauge-live range the family reads
`s2TowerRead` at the projected component, nothing else. -/
theorem s2TowerReadFamily0_live {j : ℕ} (hj : GaugeLive 2 j) (g : GaugeLattice0 2) :
    s2TowerReadFamily0 h2 hq j g = s2TowerRead h2 hq j (g ⟨j, hj⟩) :=
  dif_pos hj

/-- Off the gauge-live range the tower-read family is the junk value `0`. -/
theorem s2TowerReadFamily0_junk {j : ℕ} (hj : ¬ GaugeLive 2 j) (g : GaugeLattice0 2) :
    s2TowerReadFamily0 h2 hq j g = 0 :=
  dif_neg hj

/-- ★ **CC-11 at S2, the peel-unit family** — `s2PeelUnit`, verbatim. -/
noncomputable def s2PeelUnitFamily : ℕ → ((S2DepthTwo h2 hq).fld 2)ˣ := s2PeelUnit h2 hq

/-- Anti-drift pin: the peel-unit family is `s2PeelUnit`, nothing else. -/
theorem s2PeelUnitFamily_eq : s2PeelUnitFamily h2 hq = s2PeelUnit h2 hq := rfl

/-! ## 4. The live-index numerals (S2's unique gauge-live level `j = 1`) -/

/-- The tower-read family at the S2 tower's unique gauge-live index, spelled out at the
numeral `j = 1`. -/
example (g : GaugeLattice0 2) :
    s2TowerReadFamily0 h2 hq 1 g = s2TowerRead h2 hq 1 (g ⟨1, ⟨le_rfl, by omega⟩⟩) :=
  s2TowerReadFamily0_live h2 hq ⟨le_rfl, by omega⟩ g

/-- The peel unit at every index, spelled out at the S2 live indices `i = 1, 2`. -/
example : s2PeelUnit h2 hq 1 = 1 ∧ s2PeelUnit h2 hq 2 = 1 := ⟨rfl, rfl⟩

end Uniformity.Density.Tower.C130np8

/-! ## AUDIT — no canonical/arena equality (the NP-8 exit condition, CC-11's audit pattern)

Every declaration above is `Kt`-sided: `Kt := (S2DepthTwo h2 hq).fld 2` occurs only as the
terminal field and its unit group; nothing here mentions an `Lˣ`-valued residue datum, the
`Kt → L` coefficient embedding, the residue-ambient read (NP-7), or the sitewise carrier.
No declaration states an agreement equation between an arena-side quantity and anything
outside `Kt`, and no `NodePointSource`/`SplitNodePointSource` instance is constructed at all
(the module docstring explains why the former is impossible here), so unpacking any later
socket still leaves exactly the descent/agreement goal open, per freeze v2 §8.

Grep-tooth (mechanical; the character classes keep this audit text itself out of the match —
run from the repo root):

  rg -n "canonical[R]ead|[H]VarthetaRes|hvartheta[R]es|algebra[M]ap" \
    leanfinal/Uniformity/ChapC/C130np8.lean

MUST return no output (exit 1): the residue-ambient read's name, the two D.62/D62w trap-lemma
names, the sitewise carrier's name, and the coefficient-embedding function never occur
anywhere in this file — not in a declaration, a docstring, or (by the bracket trick) this
audit text. -/

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C130np8.s2Unit_eq_one
#print axioms Uniformity.Density.Tower.C130np8.s2Kt_eq_zero_or_one
#print axioms Uniformity.Density.Tower.C130np8.s2Kt_zero_ne_one
#print axioms Uniformity.Density.Tower.C130np8.s2ArenaRead
#print axioms Uniformity.Density.Tower.C130np8.s2ArenaRead_apply
#print axioms Uniformity.Density.Tower.C130np8.s2ArenaRead_forced
#print axioms Uniformity.Density.Tower.C130np8.s2PeelUnit
#print axioms Uniformity.Density.Tower.C130np8.s2PeelUnit_apply
#print axioms Uniformity.Density.Tower.C130np8.s2PeelUnit_forced
#print axioms Uniformity.Density.Tower.C130np8.s2TowerRead
#print axioms Uniformity.Density.Tower.C130np8.s2TowerRead_apply
#print axioms Uniformity.Density.Tower.C130np8.s2GaugeArenaAt
#print axioms Uniformity.Density.Tower.C130np8.s2GaugeArenaAt_res
#print axioms Uniformity.Density.Tower.C130np8.s2ArenaRead0
#print axioms Uniformity.Density.Tower.C130np8.s2ArenaRead0_apply
#print axioms Uniformity.Density.Tower.C130np8.s2GaugeArena0At
#print axioms Uniformity.Density.Tower.C130np8.s2GaugeArena0At_res
#print axioms Uniformity.Density.Tower.C130np8.s2GaugeArenaFamily0
#print axioms Uniformity.Density.Tower.C130np8.s2GaugeArenaFamily0_live
#print axioms Uniformity.Density.Tower.C130np8.s2GaugeArenaFamily0_junk
#print axioms Uniformity.Density.Tower.C130np8.s2TowerReadFamily0
#print axioms Uniformity.Density.Tower.C130np8.s2TowerReadFamily0_live
#print axioms Uniformity.Density.Tower.C130np8.s2TowerReadFamily0_junk
#print axioms Uniformity.Density.Tower.C130np8.s2PeelUnitFamily
#print axioms Uniformity.Density.Tower.C130np8.s2PeelUnitFamily_eq

end AxCheck
