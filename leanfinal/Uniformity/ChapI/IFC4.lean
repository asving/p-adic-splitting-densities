/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.IFC3

/-!
# Uniformity.ChapI.IFC4 — the S2 witness RE-ASSEMBLED with the law-satisfying read, and
the first `GentowWWindow` at an arising witness's OWN exports

**[GCW-3, 2026-08-27]** — node GCW-3 of `docs/in-progress/GC13_WIRING_2026-08-27.md`,
enacted AFTER GCW-0 (the F1/F2/F3 decision record) and GCW-1 (the signing round, IFC3):
the fence "only after GCW-0/GCW-1 (else cooked)" is satisfied — `GC13Wiring` is SIGNED
(leanspec AMENDMENT A-I.5, NODE I.10c) before any read is chosen here.

## The P3 licence (quoted, and its exact scope respected)

NP-8 landed `towerRead` as a genuinely FREE node field ("a FREE choice … never forced;
nothing in the carrier reads this field except through the ladder-point evaluations D.44
licenses") and picked the convenience value `0`; IFC2 proved the signed law FALSE at that
choice, and IFC3's `s2_wiring_refuted_at_landed_exports` keeps it refuted.  This file
exercises the OTHER admissible value at the only licensed site.  The GCW-0 record (F3):

> "P3 is honest only at a witness-construction site after signing: defining that
> witness's `towerRead` to satisfy this law realizes the source definition.  It is not
> an alternative placement and supplies nothing by itself."

and IFC3's module fence:

> "The P3 (definitional) route is licensed ONLY at witness-construction sites AFTER this
> signing — GCW-3's assembly, not this file."

This file IS that witness-construction site: `s2SplitNodeWired` re-assembles the landed
`C130sg.s2SplitNode` with `towerRead := 1` — the value the signed law FORCES at S2
(`IFC3.s2_wiring_forces_read_one`) — and every other field byte-inherited (structure
update; anti-drift pins below).  The choice is made ONCE, at construction; everything
downstream is PROVED at the resulting exports, never assumed.

## The D-D12 fence on `IFC2.s2_gentowW_of_read_one` (blueprint falsifier 3, respected)

That theorem is the adjudication's freedom half — a hypothetical read, NO witness — and
is hard-fenced NOT-supply.  It is consumed here in the ONE position the blueprint's own
GCW-3 row sanctions ("the constant-1 read satisfies it and, by `s2_gentowW_of_read_one`,
the FULL D.44 identity"): as an algebra lemma applied to the exported read of the NOW
CONSTRUCTED law-satisfying witness.  The supply claim of this file rests on the witness
`s2FrontierWired` + the proved `GC13Wiring` instance at its own exports — never on the
freedom half alone.

## What lands (the GCW-3 tooth + the GCW-5 residue)

* §1 the wired witness: `s2TowerReadWired`/`s2SplitNodeWired`/`s2FrontierWired`, and the
  SG-1 funnel re-fired at it (`toCarrier` → realized input → BOTH socket applications) —
  same exact conditionality as C130sg: `wT : S2LevelOneThreshold` + `IsAdicComplete`.
* §2 the exports compute: the exported read is `1` on the gauge-live range and the CC-11
  junk `0` off it (both disclosed — no swallowing).
* §3 ★★ `s2Wired_gc13Wiring` — the SIGNED law HOLDS at the wired witness's own exported
  read, every norm section, height, receiver (live levels); and the non-swallowing tooth:
  off the live range the law is still FALSE (the junk read is `0`).
* §4 ★★ `s2Wired_gentowWWindow_at_own_exports` — **the first `GentowWWindow` at an
  arising witness's OWN exports**: the law + C132sg3's UNCONDITIONAL `GENTOW5WCleared`
  (inside `IFC3.s2Mu3_gentowWWindow_of_wiring`) fire at the witness's own arena family,
  use height, and read.  Plus the GCW-5 residue (D.44's `s = 0` clause and `s > f'` tail
  both fall to the constant-1 read: `s2Wired_gcw5_residue`), the FULL D.44 identity at
  the own exports, and the signed I.10d demand `WiredGentowDemand` fired at the first
  honest site.
* §5 the depth-vacuity honesty pin, RESTATED: the wired witness has `r = 2`, so it
  supplies NO level of the depth-`≥ 4` per-level demand (`3 ≤ j < r` is empty) — the μ₃
  tooth here is at the witness's own live level `j = 1`, and the deep SHAPE tooth
  (`DeepGentowSupplier`-ward, `r ≥ 4`) remains OPEN, exactly as before this file.  GCW-6
  standing: this file is the S2 rehearsal of the mechanism GCW-6 demands before any
  depth-`≥ 4` witness lands (law-satisfying reads at construction).

## Honesty scope

Conditionality unchanged from C130sg: every S2 statement carries `wT` (the one open
level-1 threshold source datum) + `IsAdicComplete`.  Nothing here touches IFC0/IFC1/IFC2/
IFC3, C130sg's landed witness (which stays, read `0`, as the refutation half), leanspec,
or any roll-up.  All statements below are NEW (review-flagged, standing queue).  Zero
`sorry`, zero new axiom; AxChk footer expects Lean core only.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.IFC4

open Uniformity.Density Uniformity.Density.Gauge Uniformity.Density.Tower

universe uT uG uL

section S2

open IsLocalRing
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s17
open Uniformity.Density.Tower.C130s18 Uniformity.Density.Tower.C130sg
open Uniformity.Density.Tower.C130np8 Uniformity.Density.Tower.C132sg2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## §1 The wired witness — P3 enacted at the construction site (see module fence) -/

/-- ★ **the law-satisfying read** (P3, at the licensed site): the constant `1` — the value
the SIGNED law forces at the S2 ladder points (`IFC3.s2_wiring_forces_read_one`), equally
admissible with NP-8's convenience `0` (`s2Kt_zero_ne_one`); chosen HERE, once, at witness
construction, to realize the source definition `w_i = R_{i+1,κ̄_i}(n̂_i(u_{i+1}))`
(EFF.T3.21, "Define").  NEW STATEMENT (review). -/
def s2TowerReadWired : (i : ℕ) → LevelExponentLattice i → (S2DepthTwo h2 hq).fld 2 :=
  fun _ _ => 1

/-- Anti-drift pin: the wired read's value is the numeral `1`, at every index and every
lattice point. -/
theorem s2TowerReadWired_apply (i : ℕ) (g : LevelExponentLattice i) :
    s2TowerReadWired h2 hq i g = 1 := rfl

variable (L : Type uL) [Field L] [Algebra ((S2DepthTwo h2 hq).fld 2) L]

/-- ★★ **the re-assembled S2 split node** — `C130sg.s2SplitNode` with EXACTLY ONE field
changed: `towerRead := s2TowerReadWired` (the structure update reuses every other field
byte-identically — `s2SplitNodeWired_inherits` pins it).  NP-8's freedom parameterizes
precisely this field (no node law reads it), so the update is admissible node data by the
same licence as the landed choice.  NEW STATEMENT (review). -/
def s2SplitNodeWired (w : S2LevelOneThreshold) :
    SplitNodePointSource (L := L) (S2DepthTwo h2 hq) (FractionRing (Polynomial O))
      (s2RepositoryRealization h2 hq).receiver (s2RepositoryRealization h2 hq).keys :=
  { s2SplitNode h2 hq L w with towerRead := s2TowerReadWired h2 hq }

/-- Anti-drift pin: the wired node's read IS the wired read, definitionally. -/
theorem s2SplitNodeWired_towerRead (w : S2LevelOneThreshold) :
    (s2SplitNodeWired h2 hq L w).towerRead = s2TowerReadWired h2 hq := rfl

/-- Anti-drift pin (the ONE-field audit): every W-leg and stage-table field OTHER than
`towerRead` is byte-inherited from the landed `s2SplitNode` — representative `rfl` pins
across the field genres (stage tables, point reads, thresholds, arena legs). -/
theorem s2SplitNodeWired_inherits (w : S2LevelOneThreshold) :
    (s2SplitNodeWired h2 hq L w).hgt = (s2SplitNode h2 hq L w).hgt ∧
      (s2SplitNodeWired h2 hq L w).pointHgt = (s2SplitNode h2 hq L w).pointHgt ∧
      (s2SplitNodeWired h2 hq L w).thresholdZ = (s2SplitNode h2 hq L w).thresholdZ ∧
      (s2SplitNodeWired h2 hq L w).arenaRead = (s2SplitNode h2 hq L w).arenaRead ∧
      (s2SplitNodeWired h2 hq L w).peelUnit = (s2SplitNode h2 hq L w).peelUnit :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- ★ **the re-assembled S2 frontier** — `C130sg.s2Frontier` with the wired node; the
level-two ties, FGMN legs, and compat proofs carry over unchanged (the update leaves them
byte-identical: only `towerRead` moved, which no frontier field reads).  Same exact
conditionality as SG-0: the one open source datum `w`.  NEW STATEMENT (review). -/
def s2FrontierWired (w : S2LevelOneThreshold) :
    S2SourceFrontier h2 hq (FractionRing (Polynomial O)) L :=
  { s2Frontier h2 hq L w with node := s2SplitNodeWired h2 hq L w }

/-- Anti-drift pin: the wired frontier's node IS the wired node, definitionally. -/
theorem s2FrontierWired_node (w : S2LevelOneThreshold) :
    (s2FrontierWired h2 hq L w).node = s2SplitNodeWired h2 hq L w := rfl

/-- Anti-drift pin: the wired frontier's FGMN legs are the landed frontier's,
definitionally (FD-0's `r = 1` records, untouched). -/
theorem s2FrontierWired_fgmn (w : S2LevelOneThreshold) :
    (s2FrontierWired h2 hq L w).fgmn = (s2Frontier h2 hq L w).fgmn := rfl

/-! ### The SG-1 funnel, re-fired at the wired frontier

The funnel stages are GENERIC in the frontier (C130s17/C130s18), so they re-run verbatim:
nothing below is a new construction — it is C130sg's Part 7 applied at `s2FrontierWired`.
Stage 2 (the class discharge `s2_calculus_discharge`) is witness-independent and already
unconditional; it is not restated. -/

/-- ★ funnel stage 1 at the wired frontier: the PK-1 carrier packaging fires,
conditional on exactly `w`. -/
def s2FrontierWiredChainRealization (w : S2LevelOneThreshold) :
    ChainRealization (S2DepthTwo h2 hq) ((S2DepthTwo h2 hq).fld 2)
      (FractionRing (Polynomial O)) L :=
  (s2FrontierWired h2 hq L w).toCarrier

/-- ★ funnel stage 3 at the wired frontier: the realized input fires (the concrete
`keyAt 2 + 1` arising occurrence at degree 4), conditional on `w` + `IsAdicComplete`. -/
def s2FrontierWiredRealizedInput [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (w : S2LevelOneThreshold) :
    RealizedInput (s2ArisingCore h2 hq L)
      (s2FrontierWired h2 hq L w).toCarrier :=
  (s2FrontierWired h2 hq L w).s2RealizedInput

/-- ★ funnel stage 4a at the wired frontier: the S2 I.10a socket application —
byte-parallel to `C130sg.s2Frontier_ladder_socket`, same exact conditionality. -/
theorem s2FrontierWired_ladder_socket [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (w : S2LevelOneThreshold) :
    CanonicalLadderConfigData.{0, uG, 0, uL}
      ((s2FrontierWired h2 hq L w).s2RealizedInput.stageCarrierTransport
        (RingEquiv.refl ((S2DepthTwo h2 hq).fld 2)))
      ((s2FrontierWired h2 hq L w).s2RealizedInput.inputBlockTransport
        (RingEquiv.refl ((S2DepthTwo h2 hq).fld 2)))
      (GaugeLattice.{uG} 2) ((S2DepthTwo h2 hq).fld 2) L
      ((s2FrontierWired h2 hq L w).toCarrier.normalizer.arenaNormSection0.transport
        (gaugeLatticeEquiv 2).symm)
      (gaugeHeightFamily (s2FrontierWired h2 hq L w).s2RealizedInput)
      (canonicalResFamily (s2FrontierWired h2 hq L w).s2RealizedInput)
      (useHeightFamily (s2FrontierWired h2 hq L w).s2RealizedInput) 4 :=
  s2_ladder_socket_application h2 hq (s2FrontierWired h2 hq L w)

/-- ★ funnel stage 4b at the wired frontier: the S2 I.10b socket application, depth
pinned to the witness's own `r = 2` — byte-parallel to
`C130sg.s2Frontier_deepTwist_socket`.  Its exported read family is now the WIRED one. -/
theorem s2FrontierWired_deepTwist_socket [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (w : S2LevelOneThreshold) :
    CanonicalDeepTwistConfigData.{0, uG, 0, uL}
      ((s2FrontierWired h2 hq L w).s2RealizedInput.stageCarrierTransport
        (RingEquiv.refl ((S2DepthTwo h2 hq).fld 2)))
      ((s2FrontierWired h2 hq L w).s2RealizedInput.inputBlockTransport
        (RingEquiv.refl ((S2DepthTwo h2 hq).fld 2)))
      (GaugeLattice.{uG} 2) ((S2DepthTwo h2 hq).fld 2) L
      ((s2FrontierWired h2 hq L w).toCarrier.normalizer.arenaNormSection0.transport
        (gaugeLatticeEquiv 2).symm)
      (gaugeHeightFamily (s2FrontierWired h2 hq L w).s2RealizedInput)
      (canonicalResFamily (s2FrontierWired h2 hq L w).s2RealizedInput)
      (useHeightFamily (s2FrontierWired h2 hq L w).s2RealizedInput)
      (arenaFamily (s2FrontierWired h2 hq L w).s2RealizedInput Nat.one_lt_two)
      (towerReadFamily (s2FrontierWired h2 hq L w).s2RealizedInput)
      (s2FrontierWired h2 hq L w).toCarrier.node.peelUnitFamily 2 4 :=
  s2_deepTwist_socket_application h2 hq (s2FrontierWired h2 hq L w)

/-! ## §2 The wired witness's exports compute — both ranges disclosed (no swallowing) -/

/-- ★ **the wired export read is `1` on the gauge-live range**: `towerReadFamily` at the
wired realized input reads `s2TowerReadWired ≡ 1` at the projected component of every
live level — the exact clause the signed law forces (`IFC3.s2_wiring_forces_read_one`),
now REALIZED by construction. -/
theorem s2Wired_towerReadFamily_live [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (wT : S2LevelOneThreshold) {j : ℕ} (hj : GaugeLive 2 j) (g : GaugeLattice.{uG} 2) :
    towerReadFamily (s2FrontierWiredRealizedInput h2 hq L wT) j g = 1 := by
  show (s2FrontierWired h2 hq L wT).toCarrier.node.towerReadFamily0 j
    (gaugeLatticeEquiv 2 g) = 1
  rw [SplitNodePointSource.towerReadFamily0_live _ hj]
  rfl

/-- DISCLOSURE (no swallowing): OFF the gauge-live range the exported family is still the
CC-11 junk `0` — the family constructor's off-range branch, NOT the node read.  The wired
read is `1` only where D.44 evaluates it (ladder points of live levels); nobody may quote
this witness as "read ≡ 1 at every level". -/
theorem s2Wired_towerReadFamily_junk [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (wT : S2LevelOneThreshold) {j : ℕ} (hj : ¬ GaugeLive 2 j) (g : GaugeLattice.{uG} 2) :
    towerReadFamily (s2FrontierWiredRealizedInput h2 hq L wT) j g = 0 := by
  show (s2FrontierWired h2 hq L wT).toCarrier.node.towerReadFamily0 j
    (gaugeLatticeEquiv 2 g) = 0
  exact SplitNodePointSource.towerReadFamily0_junk _ hj _

/-! ## §3 The SIGNED law holds at the wired witness's OWN exports -/

/-- ★★ **`GC13Wiring` at the wired witness's own exported read** (the GCW-3 discharge):
at every gauge-live level, for EVERY norm section, height `q`, and receiver `φ`, the
signed law holds at `towerReadFamily` of the wired realized input and the μ₃ calculus —
the read is `1` by construction (§2) and the μ₃ FGMN read is the unit `1`
(`IFC2.s2Mu3_read_eq_one`), which every receiver preserves.  Universal in `(N, q, φ)`,
hence in particular at the witness's own exported norm section and use height — the
D-D12 anti-cook guard is met at its own terms (nothing about the gauge side is cooked;
only the licensed free field was chosen, per the module fence).  Blueprint falsifier 1 is
respected: this discharge is at a witness whose read SATISFIES the signed law — the
landed zero-read witness stays refuted (`IFC3.s2_wiring_refuted_at_landed_exports`). -/
theorem s2Wired_gc13Wiring [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (wT : S2LevelOneThreshold) {j : ℕ} (hj : GaugeLive 2 j)
    (N : NormSection (GaugeLattice.{uG} 2)) (q : ℤ)
    (φ : (s2DepthTwo h2 hq).fld 2 →+* (s2DepthTwo h2 hq).fld 2) :
    IFC3.GC13Wiring N q (towerReadFamily (s2FrontierWiredRealizedInput h2 hq L wT) j)
      (s2Mu3Calculus h2 hq) φ :=
  ⟨fun s hs1 hsf => by
    have hs : s = 1 := by omega
    subst hs
    rw [s2Wired_towerReadFamily_live h2 hq L wT hj,
      IFC2.s2Mu3_read_eq_one h2 hq, map_one]⟩

/-- Non-swallowing tooth: OFF the gauge-live range the signed law is still FALSE at the
wired witness's exports (the junk read is `0`, the μ₃ read is the unit `1`) — the
discharge above is genuinely live-range content, not a vacuous family fact. -/
theorem s2Wired_gc13Wiring_junk_refuted [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (wT : S2LevelOneThreshold) {j : ℕ} (hj : ¬ GaugeLive 2 j)
    (N : NormSection (GaugeLattice.{uG} 2)) (q : ℤ)
    (φ : (s2DepthTwo h2 hq).fld 2 →+* (s2DepthTwo h2 hq).fld 2) :
    ¬ IFC3.GC13Wiring N q (towerReadFamily (s2FrontierWiredRealizedInput h2 hq L wT) j)
        (s2Mu3Calculus h2 hq) φ := by
  intro hwire
  have h := hwire.read_norm 1 le_rfl le_rfl
  rw [IFC2.s2Mu3_read_eq_one h2 hq, map_one,
    s2Wired_towerReadFamily_junk h2 hq L wT hj] at h
  exact zero_ne_one h

/-! ## §4 The tooth fires: `GentowWWindow` at the wired witness's OWN exports, and the
GCW-5 residue -/

/-- ★ the tooth, general gauge side: the law instance (§3) + C132sg3's UNCONDITIONAL
`GENTOW5WCleared` (consumed inside `IFC3.s2Mu3_gentowWWindow_of_wiring`) yield the D.44
window at the wired witness's exported read, for every arena over the terminal field. -/
theorem s2Wired_gentowWWindow [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (wT : S2LevelOneThreshold) {j : ℕ} (hj : GaugeLive 2 j)
    {N : NormSection (GaugeLattice.{uG} 2)}
    (A : GaugeArena (GaugeLattice.{uG} 2) ((s2DepthTwo h2 hq).fld 2) N) (q : ℤ) :
    ∃ w : ((s2DepthTwo h2 hq).fld 2)ˣ,
      IFC1.GentowWWindow A q
        (towerReadFamily (s2FrontierWiredRealizedInput h2 hq L wT) j) w 1 :=
  IFC3.s2Mu3_gentowWWindow_of_wiring h2 hq A q
    (towerReadFamily (s2FrontierWiredRealizedInput h2 hq L wT) j) (RingHom.id _)
    (s2Wired_gc13Wiring h2 hq L wT hj N q (RingHom.id _))

/-- ★★ **the GCW-3 tooth: the FIRST `GentowWWindow` at an arising witness's OWN exports**
— the arena family, use height, and read below are EXACTLY the wired witness's socket
exports (the literal arguments of `s2FrontierWired_deepTwist_socket`), at any of its
gauge-live levels (at S2: `j = 1`).  Until this file every window statement was either
conditional on an undischarged wiring binder (IFC1/IFC2/IFC3) or at cooked gauge data
(the hard-fenced freedom half); this one is unconditional modulo the witness's own
standing conditionality (`wT` + `IsAdicComplete`). -/
theorem s2Wired_gentowWWindow_at_own_exports
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (wT : S2LevelOneThreshold) {j : ℕ} (hj : GaugeLive 2 j) :
    ∃ w : ((s2DepthTwo h2 hq).fld 2)ˣ,
      IFC1.GentowWWindow
        (arenaFamily (s2FrontierWiredRealizedInput h2 hq L wT) Nat.one_lt_two j)
        (useHeightFamily (s2FrontierWiredRealizedInput h2 hq L wT) j)
        (towerReadFamily (s2FrontierWiredRealizedInput h2 hq L wT) j) w 1 :=
  s2Wired_gentowWWindow h2 hq L wT hj _ _

/-- ★ the FULL D.44 identity at the wired exports (every arena, height, peel unit): the
constant-1 read satisfies every exponent over the S2 terminal field.  FENCE HANDLING (see
module doc): `IFC2.s2_gentowW_of_read_one` enters HERE, applied to the exported read of
the CONSTRUCTED law-satisfying witness — the position the blueprint's GCW-3 row itself
sanctions; the supply is the witness + §3's law instance, not the freedom half alone. -/
theorem s2Wired_gentowW [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (wT : S2LevelOneThreshold) {j : ℕ} (hj : GaugeLive 2 j)
    {N : NormSection (GaugeLattice.{uG} 2)}
    (A : GaugeArena (GaugeLattice.{uG} 2) ((s2DepthTwo h2 hq).fld 2) N) (q : ℤ)
    (u : ((s2DepthTwo h2 hq).fld 2)ˣ) :
    GentowW A q (towerReadFamily (s2FrontierWiredRealizedInput h2 hq L wT) j) u :=
  IFC2.s2_gentowW_of_read_one h2 hq A q
    (fun g => s2Wired_towerReadFamily_live h2 hq L wT hj g) u

/-- ★★ the full identity at the OWN exports — arena family, use height, read, and peel
unit all the wired witness's socket exports: D.44 holds outright at the first honest
site. -/
theorem s2Wired_gentowW_at_own_exports [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (wT : S2LevelOneThreshold) {j : ℕ} (hj : GaugeLive 2 j) :
    GentowW (arenaFamily (s2FrontierWiredRealizedInput h2 hq L wT) Nat.one_lt_two j)
      (useHeightFamily (s2FrontierWiredRealizedInput h2 hq L wT) j)
      (towerReadFamily (s2FrontierWiredRealizedInput h2 hq L wT) j)
      ((s2FrontierWired h2 hq L wT).toCarrier.node.peelUnitFamily j) :=
  s2Wired_gentowW h2 hq L wT hj _ _ _

/-- ★ **the GCW-5 residue, discharged at S2**: D.44's `s = 0` clause AND its `s > f' = 1`
tail both hold at the wired exports (every arena, height, peel unit) — projections of the
full identity through `IFC1.gentowW_iff_zero_window_tail`, exactly as the blueprint
predicted ("at S2 both fall to the GCW-3 assembly with the constant-1 read").  At general
instances these remain supply obligations of the signed law record. -/
theorem s2Wired_gcw5_residue [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (wT : S2LevelOneThreshold) {j : ℕ} (hj : GaugeLive 2 j)
    {N : NormSection (GaugeLattice.{uG} 2)}
    (A : GaugeArena (GaugeLattice.{uG} 2) ((s2DepthTwo h2 hq).fld 2) N) (q : ℤ)
    (u : ((s2DepthTwo h2 hq).fld 2)ˣ) :
    towerReadFamily (s2FrontierWiredRealizedInput h2 hq L wT) j (N.n 0) =
        (A.theta q 0 : (s2DepthTwo h2 hq).fld 2) ∧
      ∀ s : ℕ, 1 < s →
        towerReadFamily (s2FrontierWiredRealizedInput h2 hq L wT) j (N.n (s * q)) =
          (A.theta q s : (s2DepthTwo h2 hq).fld 2)
            * ((u : (s2DepthTwo h2 hq).fld 2)) ^ s := by
  have h := (IFC1.gentowW_iff_zero_window_tail A q
    (towerReadFamily (s2FrontierWiredRealizedInput h2 hq L wT) j) u 1).mp
    (s2Wired_gentowW h2 hq L wT hj A q u)
  exact ⟨h.1, h.2.2⟩

/-- ★★ **the signed I.10d demand, fired at the first honest site**: IFC3's
`WiredGentowDemand` (leanspec NODE I.10d — the law AND the identity at one site, same
read) holds at the wired witness's own exports with the canonical receiver `id` — the
supplier-shaped conclusion the wiring campaign was decomposed to reach. -/
theorem s2Wired_wiredGentowDemand_at_own_exports
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (wT : S2LevelOneThreshold) {j : ℕ} (hj : GaugeLive 2 j) :
    IFC3.WiredGentowDemand
      (arenaFamily (s2FrontierWiredRealizedInput h2 hq L wT) Nat.one_lt_two j)
      (useHeightFamily (s2FrontierWiredRealizedInput h2 hq L wT) j)
      (towerReadFamily (s2FrontierWiredRealizedInput h2 hq L wT) j)
      ((s2FrontierWired h2 hq L wT).toCarrier.node.peelUnitFamily j)
      (s2Mu3Calculus h2 hq) (RingHom.id _) :=
  ⟨s2Wired_gc13Wiring h2 hq L wT hj _ _ (RingHom.id _),
    s2Wired_gentowW_at_own_exports h2 hq L wT hj⟩

/-! ## §5 The depth-vacuity honesty pin, RESTATED (the shape-tooth status is unchanged) -/

/-- HONESTY (the standing depth vacuity, restated at THIS witness): the wired witness has
`r = 2`, so the depth-`≥ 4` per-level demand range `3 ≤ j < r` is EMPTY — this file
supplies the μ₃ tooth at the witness's own live level `j = 1` and NO level of the deep
supplier's flat family.  The deep SHAPE tooth (`DeepGentowSupplier`-ward content at
`r ≥ 4`) remains OPEN exactly as before; per GCW-6, any future depth-`≥ 4` witness must
be assembled with a law-satisfying read AT CONSTRUCTION — the mechanism this file
rehearses at S2. -/
theorem s2Wired_deep_demand_still_vacuous
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (wT : S2LevelOneThreshold) :
    ∀ j, 3 ≤ j → j < 2 →
      GentowW (arenaFamily (s2FrontierWiredRealizedInput h2 hq L wT) Nat.one_lt_two j)
        (useHeightFamily (s2FrontierWiredRealizedInput h2 hq L wT) j)
        (towerReadFamily (s2FrontierWiredRealizedInput h2 hq L wT) j)
        ((s2FrontierWired h2 hq L wT).toCarrier.node.peelUnitFamily j) :=
  IFC1.deepGentow_demand_vacuous_of_shallow _ _ _ _ (by omega)

end S2

end Uniformity.Density.IFC4

end

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` only.
Consumes the landed NP/SG construction chain (C130sg, cite-free), the UNCONDITIONAL μ₃
package (C132sg2/sg3, cite-free), and the IFC1–IFC3 corpus; nothing here may add to the
trusted base. -/

#print axioms Uniformity.Density.IFC4.s2TowerReadWired
#print axioms Uniformity.Density.IFC4.s2TowerReadWired_apply
#print axioms Uniformity.Density.IFC4.s2SplitNodeWired
#print axioms Uniformity.Density.IFC4.s2SplitNodeWired_towerRead
#print axioms Uniformity.Density.IFC4.s2SplitNodeWired_inherits
#print axioms Uniformity.Density.IFC4.s2FrontierWired
#print axioms Uniformity.Density.IFC4.s2FrontierWired_node
#print axioms Uniformity.Density.IFC4.s2FrontierWired_fgmn
#print axioms Uniformity.Density.IFC4.s2FrontierWiredChainRealization
#print axioms Uniformity.Density.IFC4.s2FrontierWiredRealizedInput
#print axioms Uniformity.Density.IFC4.s2FrontierWired_ladder_socket
#print axioms Uniformity.Density.IFC4.s2FrontierWired_deepTwist_socket
#print axioms Uniformity.Density.IFC4.s2Wired_towerReadFamily_live
#print axioms Uniformity.Density.IFC4.s2Wired_towerReadFamily_junk
#print axioms Uniformity.Density.IFC4.s2Wired_gc13Wiring
#print axioms Uniformity.Density.IFC4.s2Wired_gc13Wiring_junk_refuted
#print axioms Uniformity.Density.IFC4.s2Wired_gentowWWindow
#print axioms Uniformity.Density.IFC4.s2Wired_gentowWWindow_at_own_exports
#print axioms Uniformity.Density.IFC4.s2Wired_gentowW
#print axioms Uniformity.Density.IFC4.s2Wired_gentowW_at_own_exports
#print axioms Uniformity.Density.IFC4.s2Wired_gcw5_residue
#print axioms Uniformity.Density.IFC4.s2Wired_wiredGentowDemand_at_own_exports
#print axioms Uniformity.Density.IFC4.s2Wired_deep_demand_still_vacuous
