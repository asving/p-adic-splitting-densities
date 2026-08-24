/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130ln
import Uniformity.ChapC.C130s2

/-!
# Uniformity.ChapC.C130ar — the separate Kt-valued arena layer (chain-carrier node CC-11)

**Chain-carrier node CC-11** (`docs/in-progress/CHAIN_CARRIER_DESIGN_2026-08-24.md` §4.2, §8
row C.130i, §10 row CC-11: *"Construct `arenaRead`, `GaugeArena`, `towerRead`, and `peelUnit`;
audit that no canonical/arena agreement is present"*).  The three Kt-valued W-leg SOURCE
fields were landed with the CC-1 skeleton (`NodePointSource.arenaRead/towerRead/peelUnit`,
C130k); this file lands the LAYER on top of them — freeze-v2 layer C.130i: it combines
`LaurentNormalizer.exact_height` (CC-4's carrier) with the separate `arenaRead` field to build
the `Gauge.GaugeArena` family, and exports `towerRead`/`peelUnit` in the socket family shapes
(`R : ℕ → G → Kt`, `w : ℕ → Ktˣ`).

## The construction

* `LaurentNormalizer.arenaNormSectionAt i` — the level-`i` D.01 `NormSection` of the arena
  leg, on the level's Laurent exponent lattice: the normalizer word family `norm i` with its
  `norm_zero` normalization.  `LaurentNormalizer.arenaNormSection0` is the same section
  assembled componentwise on D-TIF-2's synchronized product `GaugeLattice0 r`.
* `NodePointSource.gaugeArenaAt` — the level-`i` arena (stage-live `i`): height `v` is
  C.130f's lattice height, `exact_height` is EXACTLY the normalizer's exact-height law
  (`EFF.T1.01`'s exponent identity at general depth — the field C130B proved impossible for
  C.83's truncated `towerNorm` and CC-4 solved over `ℤ`), and `res` is the carrier's SEPARATE
  Kt-valued `arenaRead` field, unchanged (`rfl`-pinned at `gaugeArenaAt_res`).
* `arenaLiveProj`/`arenaKerProj`/`NodePointSource.arenaRead0` — the synchronized-product
  restriction: the live-level projection is a monoid hom, it maps the level-height kernel into
  the lattice-height kernel, and the arena read composes through it.
* `NodePointSource.gaugeArena0At` — the arena over the synchronized product at a gauge-live
  level (the one-`(G, N)` form the frozen I.10 binders quantify over).
* `NodePointSource.gaugeArenaFamily0` — the total family `ℕ → GaugeArena (GaugeLattice0 r) Kt
  (NL.arenaNormSection0)` under the minimal hypothesis `1 < r` (PROVED minimal:
  `gaugeLive_exists_iff` — the gauge range is nonempty iff `1 < r`).  Off-range slots hold the
  level-1 arena as documented junk (freeze v2 §6: "Off-range `v,ρ,q,A,R,w` remain
  unconstrained"); `gaugeArenaFamily0_live` proves the junk is never read on the live range,
  and `gaugeArenaFamily0_junk` says exactly what the off-range slots hold.
* `NodePointSource.towerReadFamily0`/`NodePointSource.peelUnitFamily` — the D.44-shaped
  exports of the remaining two W-leg source fields (`R j` reads the `j`-component of the
  synchronized word through the carrier's `towerRead`; `w` is `peelUnit` verbatim), with
  live/junk pins.

## Sources (design §9's "source obligations" for this layer)

`EFF.T1.01`–`.03` (the level-1 arena carrier this abstracts, packaged per DECISION D-1 at
D.07), D.07/D.08 (the arena interface and its kernel arithmetic), D.44 (`R`/`w`'s consumption
shape — an arbitrary read `R : G → K` evaluated at ladder points and a peel unit `w : Kˣ`;
nothing here claims any B-law instance), `EFF.T3.21` (the telescope-port row those shapes
transcribe).  The arena data themselves stay SOURCE FIELDS of `NodePointSource`: nothing in
this file inhabits them or derives them from a bare tower.

## Deliberately NOT here (the design's fences)

* **No canonical/arena agreement** (design §4.2; §10 row CC-11's audit clause; freeze v2 §7
  row C.130i: "No theorem equates" the two reads).  See the AUDIT section before the axiom
  footer: no declaration mentions the ambient L-valued read (CC-10's layer), the `Kt → L`
  coefficient embedding, or any Kt-preimage/descent datum; the two discharge traps at
  D.62/D62w stay inapplicable.  Unpacking a socket still leaves exactly the descent/agreement
  goal, as freeze v2 §8 requires.
* The canonical L-read on level kernels and its generator views (CC-10), the four live-only
  view equalities including `ArenaFamilyViewEq` and the cross-universe `ULift` transport of
  arenas (CC-12), the use-height family `q` (CC-12's export), `RealizedInput` (CC-8), and the
  actual S2 arena-read instance (CC-17).  Every theorem here consumes a `NodePointSource`/
  `LaurentNormalizer` instance; none is constructed.

DEPENDS: C130k (CC-1 skeleton: `NodePointSource`, `LaurentNormalizer`, live lint) · C130f
(`LevelExponentLattice`, `GaugeLattice0`, `levelExponentHeight`, `levelHeight0`) · C130ln
(CC-4: the literal `DeepTower.laurentNormalizer` — teeth) · C130s2 (CC-2: `s2DepthTwo`,
`s2DepthTwoKeyChain` — teeth) · D.01/D.07 (`NormSection`, `GaugeArena`).

## Status

Zero `sorry`; no new axiom; no `unsafe`; no `True` body; axiom footprint Lean-core only
(AxCheck footer).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf
open Uniformity.Density.Gauge

universe uKt uL

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O} {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}

/-! ## 1. Lattice plumbing on the synchronized product

The live-level projection out of D-TIF-2's synchronized product, as a monoid hom, and the
minimality of the family hypothesis `1 < r`.  These need no tower and no carrier. -/

/-- The projection of the synchronized Laurent product onto a live level, as a monoid hom
(the anonymous hom inside C.130f's `levelHeight0`, named). -/
def arenaLiveProj (j : LiveLevel r) : GaugeLattice0 r →* LevelExponentLattice j.1 where
  toFun g := g j
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Anti-drift pin: the live projection is evaluation at the level, nothing else. -/
theorem arenaLiveProj_apply (j : LiveLevel r) (g : GaugeLattice0 r) :
    arenaLiveProj j g = g j := rfl

/-- The gauge range is nonempty exactly when `1 < r` — so `1 < r` is the MINIMAL hypothesis
for any total arena family over the synchronized product (nothing is smuggled in by the
family constructor below). -/
theorem gaugeLive_exists_iff (r : ℕ) : (∃ j, GaugeLive r j) ↔ 1 < r :=
  ⟨fun ⟨_, hj⟩ => Nat.lt_of_le_of_lt hj.1 hj.2, fun hr => ⟨1, le_rfl, hr⟩⟩

variable {W : DeepTower.{0, uKt} F H₀ hpin r}

/-- C.130f's level height on the synchronized product IS the lattice height composed with the
named live projection (byte-level agreement of the two anonymous homs). -/
theorem levelHeight0_comp_arenaLiveProj (j : LiveLevel r) :
    levelHeight0 W j = (levelExponentHeight W j.1).comp (arenaLiveProj j) := rfl

/-- The live projection maps the synchronized-height kernel into the level lattice-height
kernel: `levelHeight0` reads exactly the projected component. -/
def arenaKerProj (W : DeepTower.{0, uKt} F H₀ hpin r) (j : LiveLevel r) :
    MonoidHom.ker (levelHeight0 W j) →* MonoidHom.ker (levelExponentHeight W j.1) where
  toFun x := ⟨x.1 j, x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Anti-drift pin: the kernel projection is componentwise, nothing else. -/
theorem arenaKerProj_coe (j : LiveLevel r) (x : MonoidHom.ker (levelHeight0 W j)) :
    ((arenaKerProj W j x : MonoidHom.ker (levelExponentHeight W j.1)) :
      LevelExponentLattice j.1) = x.1 j := rfl

/-! ## 2. The arena-leg normalizer sections

D.01's `NormSection` carrier, inhabited by CC-4's Laurent normalizer: per level, and
componentwise on the synchronized product.  These are the `N` every arena below is over —
the exact-height law (the arena's second field) is precisely what C130B proved C.83's
truncated `towerNorm` CANNOT satisfy, which is why the arena leg must ride the Laurent
carrier and not C.130f's `normSection`. -/

namespace LaurentNormalizer

/-- The level-`i` normalizer section of the arena leg: the Laurent word family at level `i`
with its zero normalization (`(C2-zero-normalizer)`, via `LaurentNormalizer.norm_zero`). -/
def arenaNormSectionAt (NL : LaurentNormalizer W) (i : ℕ) :
    NormSection (LevelExponentLattice i) where
  n := NL.norm i
  n_zero := NL.norm_zero i

/-- Anti-drift pin: the level section is the normalizer's word family, nothing else. -/
theorem arenaNormSectionAt_n (NL : LaurentNormalizer W) (i : ℕ) :
    (NL.arenaNormSectionAt i).n = NL.norm i := rfl

/-- The synchronized normalizer section of the arena leg: componentwise Laurent words on
D-TIF-2's product over the live gauge levels. -/
def arenaNormSection0 (NL : LaurentNormalizer W) : NormSection (GaugeLattice0 r) where
  n k j := NL.norm j.1 k
  n_zero := by funext j; exact NL.norm_zero j.1

/-- Anti-drift pin: the synchronized section is componentwise, nothing else. -/
theorem arenaNormSection0_n (NL : LaurentNormalizer W) (k : ℤ) (j : LiveLevel r) :
    NL.arenaNormSection0.n k j = NL.norm j.1 k := rfl

end LaurentNormalizer

/-! ## 3. The gauge arenas (freeze-v2 layer C.130i)

`GaugeArena` = height hom + exact height + Kt-valued residue read (D.07, DECISION D-1).  The
height is C.130f's lattice height, exact height is the CC-4 normalizer law, and the residue
read is the carrier's SEPARATE `arenaRead` source field — consumed verbatim, related to
nothing else (the CC-11 fence). -/

namespace NodePointSource

variable {Kt : Type uKt} [Field Kt] {L : Type uL} [Field L] [Algebra Kt L]
variable {receiver : TerminalReceiver F H₀ hpin r W Kt} {K : KeyChain W}

/-- ★ **NODE CC-11, the level arena**: at a stage-live level `i`, the lattice height, the
Laurent exact-height law, and the separate Kt-valued `arenaRead` field assemble into D.07's
`GaugeArena` over the level normalizer section.  This is design §8 row C.130i's "combine
`LaurentNormalizer.exact_height` with the separate `arenaRead`" — the arena's `res` is the
source field UNCHANGED (see the `rfl` pin `gaugeArenaAt_res`), and no clause relates it to
any ambient read. -/
def gaugeArenaAt (S : NodePointSource (L := L) W receiver K) (NL : LaurentNormalizer W)
    {i : ℕ} (hi : StageLive r i) :
    GaugeArena (LevelExponentLattice i) Kt (NL.arenaNormSectionAt i) where
  v := levelExponentHeight W i
  exact_height := NL.exact_height i hi
  res := S.arenaRead i

/-- Anti-drift pin: the level arena's height is C.130f's lattice height, nothing else. -/
theorem gaugeArenaAt_v (S : NodePointSource (L := L) W receiver K)
    (NL : LaurentNormalizer W) {i : ℕ} (hi : StageLive r i) :
    (S.gaugeArenaAt NL hi).v = levelExponentHeight W i := rfl

/-- ★ Anti-drift pin (the separateness audit, mechanized): the level arena's residue read IS
the carrier's `arenaRead` source field, definitionally — not a composite through any ambient
read, embedding, or descent datum. -/
theorem gaugeArenaAt_res (S : NodePointSource (L := L) W receiver K)
    (NL : LaurentNormalizer W) {i : ℕ} (hi : StageLive r i) :
    (S.gaugeArenaAt NL hi).res = S.arenaRead i := rfl

/-- The separate arena read, restricted to the synchronized product: compose the carrier's
`arenaRead` with the kernel projection at a live level. -/
def arenaRead0 (S : NodePointSource (L := L) W receiver K) (j : LiveLevel r) :
    MonoidHom.ker (levelHeight0 W j) →* Ktˣ :=
  (S.arenaRead j.1).comp (arenaKerProj W j)

/-- Anti-drift pin: the synchronized arena read is the componentwise restriction of the
`arenaRead` source field, nothing else. -/
theorem arenaRead0_apply (S : NodePointSource (L := L) W receiver K) (j : LiveLevel r)
    (x : MonoidHom.ker (levelHeight0 W j)) :
    S.arenaRead0 j x = S.arenaRead j.1 (arenaKerProj W j x) := rfl

/-- ★ CC-11, the synchronized arena: the arena over D-TIF-2's product at a gauge-live level —
the one-`(G, N)` form the frozen I.10b binders (`A : ℕ → Gauge.GaugeArena G Kt N`) quantify
over.  Height = the projected lattice height; exact height = the CC-4 law at the component;
residue read = the restricted `arenaRead`. -/
def gaugeArena0At (S : NodePointSource (L := L) W receiver K) (NL : LaurentNormalizer W)
    {j : ℕ} (hj : GaugeLive r j) :
    GaugeArena (GaugeLattice0 r) Kt NL.arenaNormSection0 where
  v := levelHeight0 W ⟨j, hj⟩
  exact_height := fun k => NL.exact_height j hj.stageLive k
  res := S.arenaRead0 ⟨j, hj⟩

/-- Anti-drift pin: the synchronized arena's height is C.130f's `levelHeight0`. -/
theorem gaugeArena0At_v (S : NodePointSource (L := L) W receiver K)
    (NL : LaurentNormalizer W) {j : ℕ} (hj : GaugeLive r j) :
    (S.gaugeArena0At NL hj).v = levelHeight0 W ⟨j, hj⟩ := rfl

/-- ★ Anti-drift pin (the separateness audit on the product): the synchronized arena's
residue read is the restricted `arenaRead` source field, definitionally. -/
theorem gaugeArena0At_res (S : NodePointSource (L := L) W receiver K)
    (NL : LaurentNormalizer W) {j : ℕ} (hj : GaugeLive r j) :
    (S.gaugeArena0At NL hj).res = S.arenaRead0 ⟨j, hj⟩ := rfl

/-- ★ **The CC-11 arena family** in the socket shape `ℕ → GaugeArena G Kt N`, total over `ℕ`
under the MINIMAL hypothesis `1 < r` (`gaugeLive_exists_iff`).  Live indices carry the
genuine synchronized arena; off-range indices hold the level-1 arena as documented junk —
freeze v2 §6 pins arena projections only under gauge-liveness, and `gaugeArenaFamily0_live`
proves the junk is never read there. -/
def gaugeArenaFamily0 (S : NodePointSource (L := L) W receiver K)
    (NL : LaurentNormalizer W) (hr : 1 < r) :
    ℕ → GaugeArena (GaugeLattice0 r) Kt NL.arenaNormSection0 := fun j =>
  if hj : GaugeLive r j then S.gaugeArena0At NL hj
  else S.gaugeArena0At NL ⟨le_rfl, hr⟩

/-- ★ The non-swallowing audit for the family: on the gauge-live range the family slot is
the genuine synchronized arena at that level — the junk filler is never read. -/
theorem gaugeArenaFamily0_live (S : NodePointSource (L := L) W receiver K)
    (NL : LaurentNormalizer W) (hr : 1 < r) {j : ℕ} (hj : GaugeLive r j) :
    S.gaugeArenaFamily0 NL hr j = S.gaugeArena0At NL hj :=
  dif_pos hj

/-- Off the gauge-live range the family slot holds exactly the level-1 arena (documented
junk; freeze v2 §6 leaves off-range arena slots unconstrained). -/
theorem gaugeArenaFamily0_junk (S : NodePointSource (L := L) W receiver K)
    (NL : LaurentNormalizer W) (hr : 1 < r) {j : ℕ} (hj : ¬ GaugeLive r j) :
    S.gaugeArenaFamily0 NL hr j = S.gaugeArena0At NL ⟨le_rfl, hr⟩ :=
  dif_neg hj

/-! ## 4. The remaining W-leg exports: `towerRead` and `peelUnit` families

D.44's consumption shapes (`R : ℕ → G → Kt`, `w : ℕ → Ktˣ`), filled by the carrier's two
remaining separate source fields.  D.44 faithfulness item 2 licences the junk: "The read is
an arbitrary function `R : G → K`, evaluated only at the ladder points"; nothing constrains
`R` off the ladder or off the live range.  NO B-law instance is claimed at any level — that
is the instantiating supplier's obligation, and at depth it is exactly the open
conditionality. -/

/-- ★ CC-11, the tower-read family in D.44's shape: at a gauge-live level, read the
`j`-component of the synchronized word through the carrier's separate `towerRead` source
field; off-range, the junk value `0` (never consumed — D.44 evaluates `R` only at ladder
points of live levels). -/
def towerReadFamily0 (S : NodePointSource (L := L) W receiver K) :
    ℕ → GaugeLattice0 r → Kt := fun j g =>
  if hj : GaugeLive r j then S.towerRead j (g ⟨j, hj⟩) else 0

/-- The non-swallowing audit for the tower read: on the gauge-live range the family reads
the `towerRead` source field at the projected component, nothing else. -/
theorem towerReadFamily0_live (S : NodePointSource (L := L) W receiver K)
    {j : ℕ} (hj : GaugeLive r j) (g : GaugeLattice0 r) :
    S.towerReadFamily0 j g = S.towerRead j (g ⟨j, hj⟩) :=
  dif_pos hj

/-- Off the gauge-live range the tower-read family is the junk value `0`. -/
theorem towerReadFamily0_junk (S : NodePointSource (L := L) W receiver K)
    {j : ℕ} (hj : ¬ GaugeLive r j) (g : GaugeLattice0 r) :
    S.towerReadFamily0 j g = 0 :=
  dif_neg hj

/-- ★ CC-11, the peel-unit family in D.44's shape (`w : ℕ → Ktˣ`): the carrier's separate
`peelUnit` source field, verbatim. -/
def peelUnitFamily (S : NodePointSource (L := L) W receiver K) : ℕ → Ktˣ :=
  S.peelUnit

/-- Anti-drift pin: the peel-unit family is the `peelUnit` source field, nothing else. -/
theorem peelUnitFamily_eq (S : NodePointSource (L := L) W receiver K) :
    S.peelUnitFamily = S.peelUnit := rfl

end NodePointSource

end Uniformity.Density.Tower

/-! ## Teeth — instantiation and consumability regressions

Statements about ANY carrier instance: (i) the literal CC-4 normalizer feeds every arena
constructor, so the layer is inhabitable the moment a `NodePointSource` instance exists
(design §6's sense — no type/universe/index obstruction; the instance itself is CC-17's);
(ii) the arenas are consumable by the landed D-layer kernel arithmetic; (iii) the S2
depth-two specialization elaborates at the CC-2 occurrence. -/

section Teeth

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Gauge Uniformity.Density.Tower
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C80
open Uniformity.Density.Tower.C130s2

universe uKt uL

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O} {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
variable {W : DeepTower.{0, uKt} F H₀ hpin r}
variable {Kt : Type uKt} [Field Kt] {L : Type uL} [Field L] [Algebra Kt L]
variable {receiver : TerminalReceiver F H₀ hpin r W Kt} {K : KeyChain W}
variable (S : NodePointSource (L := L) W receiver K)

-- (i) the literal CC-4 Laurent normalizer feeds the level arena at every stage-live level
example {i : ℕ} (hi : StageLive r i) :
    GaugeArena (LevelExponentLattice i) Kt (W.laurentNormalizer.arenaNormSectionAt i) :=
  S.gaugeArenaAt W.laurentNormalizer hi

-- (i) the arena's exact-height law fires at a concrete integer height, straight off CC-4
example (NL : LaurentNormalizer W) {i : ℕ} (hi : StageLive r i) :
    (S.gaugeArenaAt NL hi).v (NL.norm i 7) = Multiplicative.ofAdd (7 : ℤ) :=
  (S.gaugeArenaAt NL hi).exact_height 7

-- (ii) D-layer consumability: every ϑ-element of the level section lies in the arena's
-- kernel (D.62's `varthetaEl_mem_ker` — pure exact-height arithmetic, NO residue claim)
example (NL : LaurentNormalizer W) {i : ℕ} (hi : StageLive r i) (q : ℤ) (s : ℕ) :
    (NL.arenaNormSectionAt i).varthetaEl q s ∈ MonoidHom.ker (S.gaugeArenaAt NL hi).v :=
  (S.gaugeArenaAt NL hi).varthetaEl_mem_ker q s

end Teeth

section TeethS2

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Gauge Uniformity.Density.Tower
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C80
open Uniformity.Density.Tower.C130s2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)
variable {Kt : Type} [Field Kt] {L : Type} [Field L] [Algebra Kt L]
variable (R : TerminalReceiver (s2Frame h2 hq) 1 (s2Frame_pin h2 hq) 2 (s2DepthTwo h2 hq) Kt)
variable (S : NodePointSource (L := L) (s2DepthTwo h2 hq) R (s2DepthTwoKeyChain h2 hq))

-- (iii) at the CC-2 depth-two occurrence (r = 2) the FULL socket-shaped family elaborates,
-- over the literal CC-4 normalizer of the landed S2 tower
noncomputable example : ℕ → GaugeArena (GaugeLattice0 2) Kt
    ((s2DepthTwo h2 hq).laurentNormalizer.arenaNormSection0) :=
  S.gaugeArenaFamily0 (s2DepthTwo h2 hq).laurentNormalizer (by omega)

-- (iii) the family's one gauge-live slot (j = 1) is the genuine synchronized arena
example :
    S.gaugeArenaFamily0 (s2DepthTwo h2 hq).laurentNormalizer (by omega) 1 =
      S.gaugeArena0At (s2DepthTwo h2 hq).laurentNormalizer ⟨le_rfl, by omega⟩ :=
  S.gaugeArenaFamily0_live _ _ ⟨le_rfl, by omega⟩

-- (iii) the tower-read and peel-unit exports specialize with no obstruction
noncomputable example : ℕ → GaugeLattice0 2 → Kt := S.towerReadFamily0
noncomputable example : ℕ → Ktˣ := S.peelUnitFamily

end TeethS2

/-! ## AUDIT — no canonical/arena agreement (the CC-11 exit condition)

Design §4.2 keeps TWO deliberately different residue reads on the carrier: the ambient
L-valued read (CC-10's layer) and the terminal-field Kt-valued read consumed here (the
`NodePointSource` source fields `arenaRead`/`towerRead`/`peelUnit`).  Identifying them is the
discharge trap the I.10a docstring warns about: the two landed lemmas at D.62/D62w discharge
the sitewise ϑ-carrier from (a) an arena whose residue read AGREES with a GIVEN ambient
L-valued datum through the `Kt → L` coefficient embedding (the arena-agreement trap), or
(b) an ambient datum whose τ-letter values are embedded Kt-units (the τ-letter trap).
Nothing landed in this file can feed either trap:

1. every declaration is Kt-sided — no declaration produces, consumes, or mentions an
   `Lˣ`-valued residue datum; `L` occurs only as an instance binder of `NodePointSource`;
2. the arenas' residue field is BY CONSTRUCTION the separate source field, `rfl`-pinned at
   `gaugeArenaAt_res`/`gaugeArena0At_res`/`arenaRead0_apply`, and NO theorem relates that
   field to the L-valued read field of `NodePointSource` (C130k), to the coefficient
   embedding, or to any Kt-preimage/descent datum;
3. no declaration states the agreement equation (ambient read = embedding ∘ arena read) in
   any form, and no D.44 B-law instance is claimed at any level — the W-leg data are
   exported as raw family shapes only, so unpacking a socket still leaves exactly the
   descent/agreement goal open, as freeze v2 §8 requires.

Grep-tooth (mechanical; the character classes keep this audit text itself out of the match —
run from the repo root):

  rg -n "canonical[R]ead|[H]VarthetaRes|hvartheta[R]es|algebra[M]ap" \
    leanfinal/Uniformity/ChapC/C130ar.lean

MUST return no output (exit 1): the two trap-lemma names, the sitewise carrier's name, the
ambient read's field name, and the coefficient-embedding function never occur anywhere in
this file — not in a declaration, a docstring, or (by the bracket trick) this audit text. -/

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.arenaLiveProj
#print axioms Uniformity.Density.Tower.arenaLiveProj_apply
#print axioms Uniformity.Density.Tower.gaugeLive_exists_iff
#print axioms Uniformity.Density.Tower.levelHeight0_comp_arenaLiveProj
#print axioms Uniformity.Density.Tower.arenaKerProj
#print axioms Uniformity.Density.Tower.arenaKerProj_coe
#print axioms Uniformity.Density.Tower.LaurentNormalizer.arenaNormSectionAt
#print axioms Uniformity.Density.Tower.LaurentNormalizer.arenaNormSectionAt_n
#print axioms Uniformity.Density.Tower.LaurentNormalizer.arenaNormSection0
#print axioms Uniformity.Density.Tower.LaurentNormalizer.arenaNormSection0_n
#print axioms Uniformity.Density.Tower.NodePointSource.gaugeArenaAt
#print axioms Uniformity.Density.Tower.NodePointSource.gaugeArenaAt_v
#print axioms Uniformity.Density.Tower.NodePointSource.gaugeArenaAt_res
#print axioms Uniformity.Density.Tower.NodePointSource.arenaRead0
#print axioms Uniformity.Density.Tower.NodePointSource.arenaRead0_apply
#print axioms Uniformity.Density.Tower.NodePointSource.gaugeArena0At
#print axioms Uniformity.Density.Tower.NodePointSource.gaugeArena0At_v
#print axioms Uniformity.Density.Tower.NodePointSource.gaugeArena0At_res
#print axioms Uniformity.Density.Tower.NodePointSource.gaugeArenaFamily0
#print axioms Uniformity.Density.Tower.NodePointSource.gaugeArenaFamily0_live
#print axioms Uniformity.Density.Tower.NodePointSource.gaugeArenaFamily0_junk
#print axioms Uniformity.Density.Tower.NodePointSource.towerReadFamily0
#print axioms Uniformity.Density.Tower.NodePointSource.towerReadFamily0_live
#print axioms Uniformity.Density.Tower.NodePointSource.towerReadFamily0_junk
#print axioms Uniformity.Density.Tower.NodePointSource.peelUnitFamily
#print axioms Uniformity.Density.Tower.NodePointSource.peelUnitFamily_eq

end AxCheck
