/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.IFC2

/-!
# Uniformity.ChapI.IFC3 — the SIGNED GC-13 wiring law (`GC13Wiring`), the wired DT0
demand, and the IFC1/IFC2 translation upgraded from `hread` to the law

**[GCW1, 2026-08-27]** — the GCW-1 signing round of
`docs/in-progress/GC13_WIRING_2026-08-27.md` (read WITH its `[GCW-0]` decision record and
the orchestrator's F2=P2 adjudication; print-read `runs/wave-b/verdict_GCW0.md`; probe
`scratch/GCW0_probe.lean`).  Leanspec signing: **AMENDMENT A-I.5**
(`leanspec/Leanspec/ChapI.lean`, NODES I.10c/I.10d) — the binder blocks here are
byte-identical to the signed ones.

**⚠ TRUST BOUNDARY — `GC13Wiring` and `WiredGentowDemand` are NEW statements**, flagged
for the standing review (`docs/REVIEW_QUEUE_2026-08-26.md`, GCW1 rows).  Zero `sorry`,
zero new axiom; AxChk footer expects Lean core only.

## The decisions enacted (GCW-0's record + the orchestrator's P2)

* **F1 — relational scalar-read bridge at the abstract D.44 surface.**  No equality of a
  `GaugeLattice` element with a `Polynomial O` is asserted; the dictionary equates the two
  SCALAR READS through the level receiver `φ`.  D.44's abstract `(N, q, R)` binders are
  retained (C130vw's `GaugeFamilyViewEq`/`ArenaFamilyViewEq` already pin them to an
  arising witness's exports).  Grade `e' * (s * u')` (OPEN-DICT-2 full-current clearing,
  NOT `s * u'`); normalizer `chainNormBelow r` (the decided `n̂_i`, NOT the current key).
* **F2 = P2 (orchestrator, 2026-08-27 21:57).**  A standalone `Prop` record demanded by
  the chapter-I suppliers at arising witnesses.  PK-1's split node and the signed socket
  `CanonicalDeepTwistConfig` are BYTE-UNCHANGED — the guard-extension fork is REJECTED
  (it would couple the law into chapter C's signed socket: a gate-(a) statement change,
  and the P1 genre P2 was adopted against).
* **F3 — the source DEFINES the read; Lean signs a LAW.**  `EFF.T3.21` says "Define" and
  sets `w_i = R_{i+1,κ̄_i}(n̂_i(u_{i+1}))`; `GENTOW2_PROOF_2026-08-09.md` S5.1 defines
  `u(β) := R_{3,β}(n̂₂(β̂))` and S5.2 takes `w := u(κ̄)`.  Lean's `towerRead` is a FREE
  node field (NP-8), so the source definition is NOT a theorem of the landed structures;
  it enters as this signed law.  The P3 (definitional) route is licensed ONLY at
  witness-construction sites AFTER this signing — GCW-3's assembly, not this file.

## The underdetermination basis (why a LAW, not a proof) — FGCW's certificates

`IFC2.s2_hread_refuted_at_landed_exports`: at the landed S2 witness's OWN exports the
read identification is FALSE at every level, receiver, and lattice point (NP-8's free
convenience choice `towerRead ≡ 0`).  `IFC2.s2_gentowW_of_read_one`: ⚠ the D-D12-FENCED
freedom half — the equally admissible read `≡ 1` satisfies FULL `GentowW` — **NOT
SUPPLY, never citable as teeth**; it is cited here only as the freedom half of the
adjudication that both truth values are realized by admissible node data.

## The amended DT0 demand (GCW-1 row), and what is BLOCKED-BECAUSE

Enacted: **the supplier gains the wiring leg, SITEWISE** (`WiredGentowDemand`, §3) — at
one consumed live level, at the guard's own `(N, q j, R j)` exports and the supplied
calculus/receiver, exactly how the law itself is signed.  IFC0's `DeepGentowSupplier` is
byte-untouched and RETIRED AS A CAMPAIGN TARGET: it remains the tension record (GCW-6 —
any depth-`≥ 4` witness assembled with a zero read refutes it outright, via
`IFC2.gentowW_false_of_read_zero`; stop-the-line for the deep-witness campaign, which
inherits P2's non-vacuity tooth obligation per the orchestrator's adjudication).

**BLOCKED-BECAUSE — no UNIVERSAL wired supplier twin is landed, and none is statable
honestly today.**  The missing mechanism is a per-level calculus/receiver EXPORT from the
arising witness (the `WleCleared` truncation exporter — blueprint §4, FIELDLIST §8; the
DT0 analogue of W0's missing weld-site exporter, same house precedent).  Until it lands,
every quantifier placement for the level sites is defective, machine-anchored on
`gc13Wiring_vacuous_of_f'_zero` below: (i) wiring as a guard-side hypothesis with the
site ∀/∃-bound inside collapses to the refutable unwired supplier through an `f' = 0`
junk site (the law leg discharges vacuously); (ii) wiring demanded at EVERY site is false
at wrong calculi; (iii) a def-parameter site family has the wrong dependency shape for
the future exporter (the canonical sites depend on the witness hidden in the guard's
existential, not on the surface data).  The universal form is owed at the exporter, as a
later recorded amendment.

## VAUD coordination note (parallel IFC0 finding — NOTED, not enacted)

`runs/wave-b/verdict_VAUD.md`: L0's `LadderVarthetaSupplier` (IFC0 §1, `∀ i ≥ 3`
unbounded) is NOT guard-derivable — at the landed depth-2 socket the first demanded index
`3` is not gauge-live — and the repair must range-restrict the target to live indices
bound to the SAME witness (`CanonicalLadderLiveAt`/`LadderVarthetaSupplierLive`,
`scratch/VAUD_probe.lean` — PROPOSED, owner-gated: it rebinds a capstone-field range).
DT0's `DeepVarthetaSupplier` is already live-restricted.  Per the GCW1 coordination rule
neither unit edits `IFC0.lean`; corrected shapes route through supersession twins in this
file's genre.

## Consumers / next

§2 is GCW-2: the `hread` binder of IFC1/IFC2 is superseded by the `GC13Wiring` leg at the
plug point (`s2Mu3_gentowWWindow_of_wiring`); the law forces the S2 read normalization
(`s2_wiring_forces_read_one` — GCW-3's assembly datum) and REJECTS the landed zero-read
witness (`s2_wiring_refuted_at_landed_exports` — falsifier 1 of the blueprint: "it's rfl"
is false at the landed witness).  GCW-3 (open, NOT this file): re-assemble the S2 node
with a law-satisfying read and prove `GC13Wiring` at that witness's own exports.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.IFC3

open Uniformity.Density Uniformity.Density.Gauge Uniformity.Density.Tower

universe uT uG uL

/-! ## §1 The signed law (leanspec AMENDMENT A-I.5, NODE I.10c — byte-identical) -/

/-- **The GC-13 wiring law** — GC-13's read/normalizer dictionary at one D.44 site: the
exported tower read at the `s`-th ladder point IS the receiver image of the FGMN
normalizer read at the cleared full-current grade.  Signed at AMENDMENT A-I.5 per
GCW-0's print-read (`EFF.T3.21`'s "Define `w_i = R_{i+1,κ̄_i}(n̂_i(u_{i+1}))`"; GENTOW2
S5.1/S5.2; OPEN-DICT-2's grade + below-current-normalizer pins) and FGCW's
underdetermination certificates (`IFC2.s2_hread_refuted_at_landed_exports`;
`IFC2.s2_gentowW_of_read_one` — the latter D-D12-FENCED, NOT SUPPLY).  A chapter-I
supplier must demand an instance at each consumed live level using the arising witness's
OWN exported `(N, q j, R j)` and the corresponding calculus/receiver — the D-D12
anti-cook guard.  NEW STATEMENT (review). -/
structure GC13Wiring {G : Type*} [CommGroup G] {Kt : Type*} [Field Kt]
    (N : NormSection G) (q : ℤ) (R : G → Kt)
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    {W : DeepTower.{0, uT} F H₀ hpin r} {e' f' u' : ℕ}
    (I : FGMNCalculus W e' f' u') (φ : W.fld r →+* Kt) : Prop where
  read_norm : ∀ s : ℕ, 1 ≤ s → s ≤ f' →
    R (N.n (s * q)) =
      φ (I.Rgr (e' * (s * u')) (I.chainNormBelow r (s * u')))

/-- ★ FABRICABILITY DISCLOSURE (the module fence's anchor): at `f' = 0` the law is
VACUOUS at ANY read and any receiver — which is exactly why no landed statement may
quantify the level site existentially or hypothesis-side (a junk `f' = 0` site would
discharge the law leg and collapse the wired demand to the refutable unwired one).  The
level sites must be pinned by the future per-level exporter, never left free. -/
theorem gc13Wiring_vacuous_of_f'_zero {G : Type*} [CommGroup G] {Kt : Type*} [Field Kt]
    (N : NormSection G) (q : ℤ) (R : G → Kt)
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    {W : DeepTower.{0, uT} F H₀ hpin r} {e' u' : ℕ}
    (I : FGMNCalculus W e' 0 u') (φ : W.fld r →+* Kt) :
    GC13Wiring N q R I φ :=
  ⟨fun _ hs1 hs0 => absurd (hs1.trans hs0) (by omega)⟩

/-! ## §2 GCW-2 — the translation upgraded: the `hread` binder superseded by the law

The record's `read_norm` projection has BYTE-EXACTLY the `hread` type IFC1 displayed
(machine fact: the terms below apply it with no rewrite, cast, or repackaging — the
GCW-0 probe's consumer-shape check, landed).  `htheta` was already discharged at the μ₃
point by IFC2, so the μ₃ tooth is now conditional on the SIGNED LAW alone. -/

/-- ★ the general translation at the law: `GENTOW5WCleared` + `GC13Wiring` + the theta
identification yield D.44's window through the receiver — IFC1's
`gentowWWindow_of_gentow5wCleared` with its `hread` binder superseded by the law's
projection. -/
theorem gentowWWindow_of_wiring {G : Type*} [CommGroup G] {Kt : Type*} [Field Kt]
    {N : NormSection G} (A : GaugeArena G Kt N) (q : ℤ) (R : G → Kt)
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    {W : DeepTower.{0, uT} F H₀ hpin r} {e' f' u' : ℕ} (I : FGMNCalculus W e' f' u')
    (hC : GENTOW5WCleared W e' f' u' I) (φ : W.fld r →+* Kt)
    (hwire : GC13Wiring N q R I φ)
    (htheta : ∀ s, 1 ≤ s → s ≤ f' →
      (A.theta q s : Kt) * φ (I.thetaRatioCleared s) = 1) :
    ∃ w : Ktˣ, IFC1.GentowWWindow A q R w f' :=
  IFC1.gentowWWindow_of_gentow5wCleared A q R I hC φ hwire.read_norm htheta

section S2

open IsLocalRing Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C132sg2
open Uniformity.Density.Tower.C130np8 Uniformity.Density.Tower.C130sg

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-- ★★ **the μ₃ tooth at the SIGNED LAW** (GCW-2's plug point, enacted): a `GC13Wiring`
instance at the μ₃ calculus fires IFC2's `s2Mu3_gentowWWindow_of_hread` directly —
`hwire.read_norm 1 le_rfl le_rfl` IS the `hread` argument, byte-shape. -/
theorem s2Mu3_gentowWWindow_of_wiring {G : Type*} [CommGroup G] {Kt : Type*} [Field Kt]
    {N : NormSection G} (A : GaugeArena G Kt N) (q : ℤ) (R : G → Kt)
    (φ : (s2DepthTwo h2 hq).fld 2 →+* Kt)
    (hwire : GC13Wiring N q R (s2Mu3Calculus h2 hq) φ) :
    ∃ w : Ktˣ, IFC1.GentowWWindow A q R w 1 :=
  IFC2.s2Mu3_gentowWWindow_of_hread h2 hq A q R φ
    (hwire.read_norm 1 le_rfl le_rfl)

/-- ★ **what the law FORCES at S2** (GCW-3's assembly datum): through any receiver the
μ₃ read is the unit `1` (`IFC2.s2Mu3_read_eq_one`), so a law-satisfying read takes the
value `1` at the level-2 ladder point — `s2Mu3_hread_iff`'s normalization, now read off
a `GC13Wiring` instance. -/
theorem s2_wiring_forces_read_one {G : Type*} [CommGroup G] {Kt : Type*} [Field Kt]
    {N : NormSection G} (q : ℤ) (R : G → Kt)
    (φ : (s2DepthTwo h2 hq).fld 2 →+* Kt)
    (hwire : GC13Wiring N q R (s2Mu3Calculus h2 hq) φ) :
    R (N.n ((1 : ℕ) * q)) = 1 :=
  (IFC2.s2Mu3_hread_iff h2 hq φ _).mp (hwire.read_norm 1 le_rfl le_rfl)

/-- ★★ **the anti-cook tooth (blueprint falsifier 1)**: the SIGNED law is FALSE at the
landed S2 witness's OWN exported read (NP-8's free `towerRead ≡ 0`), at every level,
receiver, and gauge norm-section — the law correctly REJECTS the zero-read witness, so
"the wiring is rfl at the landed data" stays refuted after the signing.  This is the
GCW-6 mechanism in machine form: a witness must be RE-assembled with a law-satisfying
read (GCW-3) before any tooth fires at its exports. -/
theorem s2_wiring_refuted_at_landed_exports
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (L : Type uL) [Field L] [Algebra ((s2DepthTwo h2 hq).fld 2) L]
    (wT : S2LevelOneThreshold) (j : ℕ)
    (N : NormSection (GaugeLattice.{uG} 2)) (q : ℤ)
    (φ : (s2DepthTwo h2 hq).fld 2 →+* (s2DepthTwo h2 hq).fld 2) :
    ¬ GC13Wiring N q (towerReadFamily (s2FrontierRealizedInput h2 hq L wT) j)
        (s2Mu3Calculus h2 hq) φ :=
  fun hwire =>
    IFC2.s2_hread_refuted_at_landed_exports h2 hq L wT j (N.n ((1 : ℕ) * q)) φ
      (hwire.read_norm 1 le_rfl le_rfl)

end S2

/-! ## §3 The amended DT0 demand (GCW-1 row): the wired per-level demand, SITEWISE

Enacted per GCW-0's record + P2: the supplier gains the wiring leg; the signed socket
`CanonicalDeepTwistConfig` is byte-unchanged.  The demand is signed SITEWISE — one
consumed live level, every datum explicit — because the per-level calculus/receiver
correspondence has no landed exporter (module fence: the universal twin is
BLOCKED-BECAUSE).  At a consumed live level `j` of an arising witness, the instance is
demanded at the guard's own exports `(N, q j, R j, A j, w j)` and the supplied level
calculus/receiver — never at cooked gauge data (D-D12). -/

/-- **The wired per-level DT0 demand** (leanspec AMENDMENT A-I.5, NODE I.10d —
byte-identical): at one D.44 site, the SIGNED GC-13 law AND D.44's `[GENTOW5-W(j)]`
identity, at the same read.  STRENGTHENS the unwired per-level conclusion (the `gentowW`
projection below), and supersedes IFC0's `DeepGentowSupplier` as the campaign target —
that unwired form is byte-untouched in IFC0 and retained as GCW-6's tension record.
NEW STATEMENT (review). -/
def WiredGentowDemand {G : Type*} [CommGroup G] {Kt : Type*} [Field Kt]
    {N : NormSection G} (A : GaugeArena G Kt N) (q : ℤ) (R : G → Kt) (w : Ktˣ)
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    {W : DeepTower.{0, uT} F H₀ hpin r} {e' f' u' : ℕ}
    (I : FGMNCalculus W e' f' u') (φ : W.fld r →+* Kt) : Prop :=
  GC13Wiring N q R I φ ∧ GentowW A q R w

/-- The law leg. -/
theorem WiredGentowDemand.wiring {G : Type*} [CommGroup G] {Kt : Type*} [Field Kt]
    {N : NormSection G} {A : GaugeArena G Kt N} {q : ℤ} {R : G → Kt} {w : Ktˣ}
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    {W : DeepTower.{0, uT} F H₀ hpin r} {e' f' u' : ℕ}
    {I : FGMNCalculus W e' f' u'} {φ : W.fld r →+* Kt}
    (h : WiredGentowDemand A q R w I φ) : GC13Wiring N q R I φ := h.1

/-- The identity leg: the wired demand implies the unwired per-level conclusion —
the supersession is a STRENGTHENING, machine-visible (nothing is weakened). -/
theorem WiredGentowDemand.gentowW {G : Type*} [CommGroup G] {Kt : Type*} [Field Kt]
    {N : NormSection G} {A : GaugeArena G Kt N} {q : ℤ} {R : G → Kt} {w : Ktˣ}
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    {W : DeepTower.{0, uT} F H₀ hpin r} {e' f' u' : ℕ}
    {I : FGMNCalculus W e' f' u'} {φ : W.fld r →+* Kt}
    (h : WiredGentowDemand A q R w I φ) : GentowW A q R w := h.2

/-- ★ the junk-site collapse, MACHINE-PINNED: at an `f' = 0` site the wired demand IS
the unwired identity — the reason no site-quantified universal supplier is landed
(module fence, defect (i)); the level sites must come from the future per-level
exporter. -/
theorem wiredGentowDemand_iff_of_f'_zero {G : Type*} [CommGroup G] {Kt : Type*}
    [Field Kt] {N : NormSection G} (A : GaugeArena G Kt N) (q : ℤ) (R : G → Kt)
    (w : Ktˣ)
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    {W : DeepTower.{0, uT} F H₀ hpin r} {e' u' : ℕ}
    (I : FGMNCalculus W e' 0 u') (φ : W.fld r →+* Kt) :
    WiredGentowDemand A q R w I φ ↔ GentowW A q R w :=
  ⟨And.right, fun h => ⟨gc13Wiring_vacuous_of_f'_zero N q R I φ, h⟩⟩

end Uniformity.Density.IFC3

end

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` only.
Statement carriers + decomposition/fence bookkeeping over the landed IFC1/IFC2 corpus
(cite-free); nothing here may add to the trusted base. -/

#print axioms Uniformity.Density.IFC3.GC13Wiring
#print axioms Uniformity.Density.IFC3.gc13Wiring_vacuous_of_f'_zero
#print axioms Uniformity.Density.IFC3.gentowWWindow_of_wiring
#print axioms Uniformity.Density.IFC3.s2Mu3_gentowWWindow_of_wiring
#print axioms Uniformity.Density.IFC3.s2_wiring_forces_read_one
#print axioms Uniformity.Density.IFC3.s2_wiring_refuted_at_landed_exports
#print axioms Uniformity.Density.IFC3.WiredGentowDemand
#print axioms Uniformity.Density.IFC3.WiredGentowDemand.wiring
#print axioms Uniformity.Density.IFC3.WiredGentowDemand.gentowW
#print axioms Uniformity.Density.IFC3.wiredGentowDemand_iff_of_f'_zero
