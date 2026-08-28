/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.IFC4

/-!
# Uniformity.ChapI.I10DeepExport — G3/G4: the per-level WLE site package and the ONE
shared deep-level export record

**[G345, 2026-08-28]** — campaign rows **G3** (the WLE per-level amendment) and **G4**
(the shared deep-level export) of `docs/in-progress/DEEP_WITNESS_CAMPAIGN_2026-08-28.md`
§4.2/§4.3 + §6.1, enacted as a signing/review-grade promotion of the probe-validated
shapes into production.  Scratch statement authorities (both compile, zero `sorry`):

* `leanfinal/scratch/WLE_probe.lean` (`WLEProbe.*`) — the witness-dependent `WleCleared`
  exporter surface ([WLE] section of `docs/in-progress/GC13_WIRING_2026-08-27.md`);
* `leanfinal/scratch/TAU_probe.lean` (`TAUProbe.*`) — the canonical-generator descent
  dictionary (`CanonicalGeneratorDescent`).

## G3 — the fixed-triple total family SUPERSEDED by a true site package

The probe's `WleClearedLevelExport` demanded, inside ONE level's export,
`calculus : ∀ i, (hi : i ≤ core.r) → FGMNCalculus (core.T.trunc i hi) e' f' u'` — a
TOTAL calculus family at one fixed `(e',f',u')` — plus the cumulative
`WleCleared core.T e' f' u' calculus j`, of which only the top `j` member was ever
consumed (`top_cleared`).  That shape cannot honestly combine this campaign's
depth-three `(2,1,85)` and depth-four `(1,1,171)` calculi (DWC §2), and it demands
off-site calculi merely to inhabit the `j = 3` export.  Per gate G3 the production
`WleClearedLevelExport` below carries exactly ONE `(e',f',u')`, ONE calculus on
`core.T.trunc j hjr`, and ONE top `GENTOW5WCleared` law, with the same own-export
`GC13Wiring` leg and `f_pos`.  RETYPE DIFF against the probe (machine-diffable):

* field `calculus` : total family `∀ i, (hi : i ≤ core.r) → …` → the single site
  calculus `FGMNCalculus (core.T.trunc j hjr) e' f' u'`;
* field `cleared` : `WleCleared core.T e' f' u' calculus j` → the top law
  `GENTOW5WCleared (core.T.trunc j hjr) e' f' u' calculus`;
* every consumer occurrence `S.calculus j hjr` / `S.calculus j hj.2.le` → `S.calculus`;
* everything else (binders, universes, wiring/receiver/normalizer data, `f_pos`,
  quantifier discipline) is byte-identical to the probe.

`ThetaCompatibleAt`, `PeelCompatibleAt`, `RangeCompleteAt`, and
`wiredDemand_of_level_export` are retyped against the site package in this same
amendment (gate G3's one-amendment rule); the indexed cumulative wrapper
`WleClearedIndexed` (parameters AND calculus indexed by the level) is provided for any
consumer that still wants a cumulative carrier, with the landed fixed-triple
`WleCleared` recovered exactly at constant index families.

## G4 — ONE shared owner record, not separate TAU and WLE dictionaries

`DeepLevelExport X j hj` packages, at one deep-live level of one explicit arising
witness:

1. the corrected G3 calculus/wiring site package (`site` — the WLE dictionary
   projection);
2. TAU's `CanonicalGeneratorDescent` (`descent` — the TAU dictionary projection;
   promoted from `TAUProbe.CanonicalGeneratorDescent` BYTE-IDENTICALLY, together with
   its `unitAlgebraMap` abbreviation);
3. the receiver/letter equality (`letter_receiver`) tying the calculus letters
   `site.calculus.letterZ` — through the SAME receiver `Aℛ.receiver.levelHom j` used by
   the wiring leg and the SAME terminal embedding `algebraMap Kt L` used by the descent
   dictionary — to the canonical generator values
   `Aℛ.node.letterValue Aℛ.normalizer _ a`.  Letter indexing NOTE (review): the letter
   generator `Λ_a` is the normalized key power `Φ_{a+1}^{e_{a+2}}·n̂⁻¹` (C130cr
   `letterClass`), whose exponent/height data live at tower stage `a+2`; the equality
   therefore pairs `Λ_a`'s canonical value with the FGMN letter `z_{a+2}`
   (`letterZ (a.1 + 2)`), the same stage pairing as the landed S2 template
   `C130s17.S2SourceFrontier.letter_compat`.  Inhabiting this field is campaign row R5
   (OPEN-LETTERS); it is a statement here, not a claim.

Per the gate: the tau-word spanning theorem stays OUTSIDE this dictionary (TAU's
`tau_word` remains a field of the separate consumer record in scratch/future C3), and
the WLE theta/peel/range proofs remain consumer laws (hypotheses of
`wiredDemand_of_level_export`, not fields).  What the shared record makes FREE is
recorded: `letter_descent_of_receiver_eq` shows the receiver/letter equality forces
TAU's letter-descent clause, so `DeepLevelExport.ofLetterEq` builds the whole record
from the site package, the wrap descent, and the letter equality alone.
`DeepLevelPerWitnessExporter` is DWR §11.4's per-witness exporter shape (its deep
inhabitants are rows C0/G10, OPEN).

## Vacuity/nonvacuity teeth carried over

`no_s2_deep_level` and `wleCleared_two_vacuous` are promoted byte-identically from the
WLE probe (the machine pins that IFC4's S2 theorem is a base/shape tooth, NOT a deep
exporter instance); `wleClearedIndexed_two_vacuous` and
`deepLevelPerWitnessExporter_of_shallow` are their indexed/shared-record twins.  The
GCW-6/D-D12 fences are inherited: no field here quantifies a site existentially, the
receiver is pinned to `Aℛ.receiver.levelHom j`, `f_pos` blocks the `f' = 0` junk-site
collapse (`IFC3.gc13Wiring_vacuous_of_f'_zero`), and IFC3's
`s2_wiring_refuted_at_landed_exports` remains the standing zero-read counterexample.

## Import acyclicity (recorded per the supersession discipline)

This module imports ONLY `Uniformity.ChapI.IFC4` (exactly the WLE probe's import).  Its
closure reaches IFC3 → IFC2 → IFC1 → {IFC0, C132sg3} and, through IFC2's C130sg leg,
C130vw → C130cr — supplying `GC13Wiring`/`WiredGentowDemand`, the `GENTOW5WCleared`/
`WleCleared` carriers, the view families, and `wrapValue`/`letterValue`.  Nothing
imports this module except the chapter aggregator `Uniformity/ChapI.lean` (extended this
unit); no ChapC/ChapD module imports ChapI, so the graph stays acyclic.  The landed
IFC1–IFC4/I10* files are byte-frozen; the scratch probes remain in place as the design
record.

## leanspec finding (gate: default NO signed change — CONFIRMED)

The deepTwist signed surface is untouched: NODES I.10c (`GC13Wiring`) and I.10d
(`WiredGentowDemand`) of `leanspec/Leanspec/ChapI.lean` are CONSUMED here byte-unchanged
(as record-field/conclusion types), `CanonicalDeepTwistConfig`/`CapstoneHypotheses` are
not mentioned, and no name landed here occurs in leanspec.  Indeed A-I.5's own
BLOCKED-BECAUSE note marks the universal wired supplier as waiting on exactly this
supplier-side "`WleCleared` truncation exporter"; these are supplier-side interfaces
BELOW the signed surface.  No A-I.9 amendment is forced.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.DeepExport

open Uniformity.Density Uniformity.Density.Gauge Uniformity.Density.Tower

universe uE uG uKt uL

/-! ## §1 [G3] The per-level site package (the probe's fixed-triple family SUPERSEDED) -/

/-- **[G3] The witness-dependent per-level `WleCleared` site package.**  A positive,
owner-attached `GENTOW5WCleared` site at level `j`: ONE `(e',f',u')`, ONE calculus on the
truncated tower `core.T.trunc j hjr`, the TOP cleared law at that same calculus, and the
own-export `GC13Wiring` leg — all after the explicit realized witness `X`, so no site
family exists outside the arising-witness binder and no off-site calculus is demanded.
Supersedes the probe's fixed-triple total family (`WLEProbe.WleClearedLevelExport`; see
the module header's retype diff).  Its receiver is definitionally the witness's own
`Aℛ.receiver.levelHom j`; its gauge data are the witness's own `normalizer`,
`useHeightFamily`, and `towerReadFamily`; `f_pos` blocks the machine-certified `f' = 0`
collapse.  NEW STATEMENT (review). -/
structure WleClearedLevelExport
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type uE} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : ArisingCore (O := O) Kt L n}
    {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L}
    (X : RealizedInput core Aℛ) (j : ℕ) (hjr : j ≤ core.r) : Type (max uE uG uKt uL) where
  e' : ℕ
  f' : ℕ
  u' : ℕ
  f_pos : 0 < f'
  calculus : FGMNCalculus (core.T.trunc j hjr) e' f' u'
  cleared : GENTOW5WCleared (core.T.trunc j hjr) e' f' u' calculus
  wiring : IFC3.GC13Wiring
    (Aℛ.normalizer.arenaNormSection0.transport
      (show GaugeLattice.{uG} core.r ≃* GaugeLattice0 core.r from
        gaugeLatticeEquiv core.r).symm)
    (useHeightFamily X j) (towerReadFamily X j) calculus
    (Aℛ.receiver.levelHom j)

/-- The exported site datum supplies its top `GENTOW5WCleared` instance at a deep level —
the probe's `top_cleared` interface, now a field projection (the retype made the top law
primitive instead of extracting it from an off-site cumulative family). -/
theorem WleClearedLevelExport.top_cleared
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type uE} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : ArisingCore (O := O) Kt L n}
    {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L}
    {X : RealizedInput core Aℛ} {j : ℕ} (hj : DeepLive core.r j)
    (S : WleClearedLevelExport.{uE, uG, uKt, uL} X j hj.2.le) :
    GENTOW5WCleared (core.T.trunc j hj.2.le) S.e' S.f' S.u' S.calculus :=
  S.cleared

/-- **[G3] The adapter from the old fixed-triple shape** (the direction that holds): any
probe-shaped datum — a fixed-triple TOTAL calculus family, its cumulative
`WleCleared … j`, positivity, and the own-export wiring at the top member — yields the
retyped site package at a deep-live level, by evaluating the family at the site and
extracting the top cleared law.  The converse direction is FALSE by design: the site
package deliberately does not determine off-site calculi. -/
def WleClearedLevelExport.ofFixedTriple
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type uE} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : ArisingCore (O := O) Kt L n}
    {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L}
    {X : RealizedInput core Aℛ} {j : ℕ} (hj : DeepLive core.r j)
    {e' f' u' : ℕ} (f_pos : 0 < f')
    (I : ∀ i, (hi : i ≤ core.r) → FGMNCalculus (core.T.trunc i hi) e' f' u')
    (hcleared : WleCleared core.T e' f' u' I j)
    (hwiring : IFC3.GC13Wiring
      (Aℛ.normalizer.arenaNormSection0.transport
        (show GaugeLattice.{uG} core.r ≃* GaugeLattice0 core.r from
          gaugeLatticeEquiv core.r).symm)
      (useHeightFamily X j) (towerReadFamily X j) (I j hj.2.le)
      (Aℛ.receiver.levelHom j)) :
    WleClearedLevelExport.{uE, uG, uKt, uL} X j hj.2.le where
  e' := e'
  f' := f'
  u' := u'
  f_pos := f_pos
  calculus := I j hj.2.le
  cleared := hcleared j hj.1 le_rfl hj.2.le
  wiring := hwiring

/-- The missing per-level exporter at the retyped site package: after the witness is
explicit, every deep-live level exports a positive, canonical `WleCleared` site.  Deep
inhabitants are OPEN (campaign rows C0–C2; the r ≥ 4 wall recorded in the [WLE] section
of `GC13_WIRING_2026-08-27.md` stands). -/
def WleClearedPerLevelExporter
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type uE} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : ArisingCore (O := O) Kt L n}
    {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L}
    (X : RealizedInput core Aℛ) : Prop :=
  ∀ j, (hj : DeepLive core.r j) →
    Nonempty (WleClearedLevelExport.{uE, uG, uKt, uL} X j hj.2.le)

/-! ## §2 [G3] The indexed cumulative wrapper (retained, with level-indexed parameters) -/

/-- **[G3] The indexed cumulative `𝒲_{≤n}` wrapper**: the cumulative cleared carrier with
the triple AND the calculus indexed by the level — the honest cumulative form when
different levels carry different refinement data (DWC §2: depth-three `(2,1,85)` and
depth-four `(1,1,171)` cannot share one triple).  The landed fixed-triple `WleCleared`
is recovered exactly at constant index families (`wleClearedIndexed_of_fixed` /
`wleCleared_of_indexed_const` below).  NEW STATEMENT (review). -/
def WleClearedIndexed
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower.{0, uKt} F H₀ hpin r) (e' f' u' : ℕ → ℕ)
    (I : ∀ i, (hi : i ≤ r) → FGMNCalculus (W.trunc i hi) (e' i) (f' i) (u' i))
    (n : ℕ) : Prop :=
  ∀ i, 3 ≤ i → i ≤ n → ∀ hi : i ≤ r,
    GENTOW5WCleared (W.trunc i hi) (e' i) (f' i) (u' i) (I i hi)

/-- The landed fixed-triple cumulative carrier is an instance of the indexed wrapper at
constant index families (the supersession is a strict generalization; nothing weakened). -/
theorem wleClearedIndexed_of_fixed
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    {W : DeepTower.{0, uKt} F H₀ hpin r} {e' f' u' : ℕ}
    {I : ∀ i, (hi : i ≤ r) → FGMNCalculus (W.trunc i hi) e' f' u'} {n : ℕ}
    (h : WleCleared W e' f' u' I n) :
    WleClearedIndexed W (fun _ => e') (fun _ => f') (fun _ => u') I n :=
  h

/-- Converse at constant families: the two carriers agree exactly there (anti-drift pin
for the supersession). -/
theorem wleCleared_of_indexed_const
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    {W : DeepTower.{0, uKt} F H₀ hpin r} {e' f' u' : ℕ}
    {I : ∀ i, (hi : i ≤ r) → FGMNCalculus (W.trunc i hi) e' f' u'} {n : ℕ}
    (h : WleClearedIndexed W (fun _ => e') (fun _ => f') (fun _ => u') I n) :
    WleCleared W e' f' u' I n :=
  h

/-- Level extraction from the indexed wrapper (the analogue of the probe's cumulative
`top_cleared` route, now honestly per-level). -/
theorem WleClearedIndexed.at_level
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    {W : DeepTower.{0, uKt} F H₀ hpin r} {e' f' u' : ℕ → ℕ}
    {I : ∀ i, (hi : i ≤ r) → FGMNCalculus (W.trunc i hi) (e' i) (f' i) (u' i)} {n : ℕ}
    (h : WleClearedIndexed W e' f' u' I n) {i : ℕ} (hi3 : 3 ≤ i) (hin : i ≤ n)
    (hir : i ≤ r) :
    GENTOW5WCleared (W.trunc i hir) (e' i) (f' i) (u' i) (I i hir) :=
  h i hi3 hin hir

/-! ## §3 [G3] The three consumer dictionaries, retyped against the site package

These remain CONSUMER LAWS (open-lemma obligations of campaign rows C1/C2 = GCW-4/GCW-5
at general depth), never fields of the export records. -/

/-- OPEN-MATH consumer law: the general theta dictionary at the exported site (GCW-4 at
every cleared exponent), retyped against the site package. -/
def ThetaCompatibleAt
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type uE} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : ArisingCore (O := O) Kt L n}
    {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L}
    (X : RealizedInput core Aℛ) (hr : 1 < core.r) {j : ℕ} {hjr : j ≤ core.r}
    (S : WleClearedLevelExport.{uE, uG, uKt, uL} X j hjr) : Prop :=
  ∀ s, 1 ≤ s → s ≤ S.f' →
    ((arenaFamily.{uE, uG, uKt, uL} X hr j).theta (useHeightFamily X j) s : Kt) *
      Aℛ.receiver.levelHom j (S.calculus.thetaRatioCleared s) = 1

/-- OPEN-MATH consumer law: the cleared witness is the witness's own exported peel unit
(the single-`w` tie), retyped against the site package. -/
def PeelCompatibleAt
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type uE} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : ArisingCore (O := O) Kt L n}
    {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L}
    (X : RealizedInput core Aℛ) {j : ℕ} {hjr : j ≤ core.r}
    (S : WleClearedLevelExport.{uE, uG, uKt, uL} X j hjr) : Prop :=
  ∃ wC : (core.T.trunc j hjr).fld j, wC ≠ 0 ∧
    (∀ t, t < S.f' →
      S.calculus.Rgr (S.e' * ((S.f' - t) * S.u'))
          (S.calculus.chainNormBelow j ((S.f' - t) * S.u')) *
          S.calculus.thetaRatioCleared (S.f' - t) = wC ^ (S.f' - t)) ∧
    ((Aℛ.node.peelUnitFamily j : Ktˣ) : Kt) = Aℛ.receiver.levelHom j wC

/-- OPEN-MATH consumer law: D.44's clauses outside the cleared exponent window (the
`s = 0` normalization and the `s > f'` tail — GCW-5 at general depth), retyped against
the site package (calculus-free; the retype is the `S`-type alone). -/
def RangeCompleteAt
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type uE} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : ArisingCore (O := O) Kt L n}
    {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L}
    (X : RealizedInput core Aℛ) (hr : 1 < core.r) {j : ℕ} {hjr : j ≤ core.r}
    (S : WleClearedLevelExport.{uE, uG, uKt, uL} X j hjr) : Prop :=
  towerReadFamily.{uE, uG, uKt, uL} X j
      ((Aℛ.normalizer.arenaNormSection0.transport
        (show GaugeLattice.{uG} core.r ≃* GaugeLattice0 core.r from
          gaugeLatticeEquiv core.r).symm).n 0) =
      ((arenaFamily.{uE, uG, uKt, uL} X hr j).theta (useHeightFamily X j) 0 : Kt) ∧
    ∀ s : ℕ, S.f' < s →
      towerReadFamily.{uE, uG, uKt, uL} X j
          ((Aℛ.normalizer.arenaNormSection0.transport
            (show GaugeLattice.{uG} core.r ≃* GaugeLattice0 core.r from
              gaugeLatticeEquiv core.r).symm).n
            ((s : ℤ) * useHeightFamily X j)) =
        ((arenaFamily.{uE, uG, uKt, uL} X hr j).theta (useHeightFamily X j) s : Kt) *
          (((Aℛ.node.peelUnitFamily j : Ktˣ) : Kt) ^ s)

/-! ## §4 [G3] The wired assembly at production types -/

/-- ★ **The wired assembly from the four genuinely distinct ingredients**, at the
production site package: the site's own cleared law + wiring leg, plus the three
consumer dictionaries, yield the SIGNED sitewise `IFC3.WiredGentowDemand` at the
witness's own exports.  Ported from the probe (`WLEProbe.wiredDemand_of_level_export`)
with `S.calculus j hj.2.le → S.calculus` the only change; the engine is
`IFC1.gentowWWindow_of_cleared_law` + `IFC1.gentowW_iff_zero_window_tail`, and the
receiver identification enters ONLY through `S.wiring.read_norm`. -/
theorem wiredDemand_of_level_export
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type uE} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : ArisingCore (O := O) Kt L n}
    {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L}
    {X : RealizedInput core Aℛ} {j : ℕ} (hj : DeepLive core.r j)
    (S : WleClearedLevelExport.{uE, uG, uKt, uL} X j hj.2.le)
    (hθ : ThetaCompatibleAt X (by rcases hj with ⟨hj3, hjr⟩; omega) S)
    (hw : PeelCompatibleAt X S)
    (hrange : RangeCompleteAt X (by rcases hj with ⟨hj3, hjr⟩; omega) S) :
    IFC3.WiredGentowDemand
      (arenaFamily.{uE, uG, uKt, uL} X
        (by rcases hj with ⟨hj3, hjr⟩; omega) j)
      (useHeightFamily X j) (towerReadFamily X j) (Aℛ.node.peelUnitFamily j)
      S.calculus (Aℛ.receiver.levelHom j) := by
  rcases hw with ⟨wC, hwC, hlaw, hunit⟩
  have hwin : IFC1.GentowWWindow
      (arenaFamily.{uE, uG, uKt, uL} X
        (by rcases hj with ⟨hj3, hjr⟩; omega) j)
      (useHeightFamily X j) (towerReadFamily X j) (Aℛ.node.peelUnitFamily j) S.f' :=
    IFC1.gentowWWindow_of_cleared_law
      (arenaFamily.{uE, uG, uKt, uL} X
        (by rcases hj with ⟨hj3, hjr⟩; omega) j)
      (useHeightFamily X j) (towerReadFamily X j) S.calculus
      (Aℛ.receiver.levelHom j) wC (Aℛ.node.peelUnitFamily j) hlaw hunit
      S.wiring.read_norm hθ
  refine ⟨S.wiring, ?_⟩
  exact (IFC1.gentowW_iff_zero_window_tail
    (arenaFamily.{uE, uG, uKt, uL} X
      (by rcases hj with ⟨hj3, hjr⟩; omega) j)
    (useHeightFamily X j) (towerReadFamily X j) (Aℛ.node.peelUnitFamily j) S.f').mpr
      ⟨hrange.1, hwin, hrange.2⟩

/-- The universal wired supplier at explicit arising witnesses, retyped against the site
package.  Its conclusion is evaluated only at `X`'s own arena/use-height/read/peel-unit
exports, and its calculus/receiver are the ones in the level export.  Target definition
only — its proof from the per-level exporter needs the three consumer dictionaries
(rows C1/C2), and its deep inhabitants are the campaign's r ≥ 4 wall. -/
def UniversalWiredDeepGentowSupplier (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Kt : Type uKt) [Field Kt] (E : Type uE) [Field E]
    (L : Type uL) [Field L] [Algebra Kt L]
    (core : ArisingCore (O := O) Kt L n)
    (Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L)
    (X : RealizedInput core Aℛ),
    WleClearedPerLevelExporter.{uE, uG, uKt, uL} X →
      ∀ j, (hj : DeepLive core.r j) →
        ∃ S : WleClearedLevelExport.{uE, uG, uKt, uL} X j hj.2.le,
          IFC3.WiredGentowDemand
            (arenaFamily.{uE, uG, uKt, uL} X
              (by rcases hj with ⟨hj3, hjr⟩; omega) j)
            (useHeightFamily X j) (towerReadFamily X j)
            (Aℛ.node.peelUnitFamily j) S.calculus
            (Aℛ.receiver.levelHom j)

/-! ## §5 The machine pins: why IFC4's S2 theorem is a base/shape tooth, not a deep
exporter instance (promoted byte-identically from the probe) -/

/-- Machine pin: no level is deep-live at depth two — `DeepLive 2 j` is empty, so the S2
witness cannot inhabit any deep exporter statement.  (Byte-identical probe promotion.) -/
theorem no_s2_deep_level (j : ℕ) : ¬ DeepLive 2 j := by
  rintro ⟨h3, hj2⟩
  omega

/-- Machine pin: the landed cumulative `WleCleared … 2` is vacuous — its definition
begins at `3` — so "level-2 instance" claims are index drift.  (Byte-identical probe
promotion.) -/
theorem wleCleared_two_vacuous
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    {W : DeepTower.{0, uKt} F H₀ hpin r} {e' f' u' : ℕ}
    (I : ∀ i, (hi : i ≤ r) → FGMNCalculus (W.trunc i hi) e' f' u') :
    WleCleared W e' f' u' I 2 := by
  intro i hi3 hi2
  omega

/-- The indexed twin of `wleCleared_two_vacuous`. -/
theorem wleClearedIndexed_two_vacuous
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    {W : DeepTower.{0, uKt} F H₀ hpin r} {e' f' u' : ℕ → ℕ}
    (I : ∀ i, (hi : i ≤ r) → FGMNCalculus (W.trunc i hi) (e' i) (f' i) (u' i)) :
    WleClearedIndexed W e' f' u' I 2 := by
  intro i hi3 hi2
  omega

/-! ## §6 [G4] The TAU dictionary (byte-identical probe promotions) -/

/-- The unit-group map induced by the specified terminal-field embedding.
(Byte-identical promotion of `TAUProbe.unitAlgebraMap`.) -/
abbrev unitAlgebraMap {Kt : Type uKt} [Field Kt] {L : Type uL} [Field L]
    [Algebra Kt L] : Ktˣ →* Lˣ :=
  Units.map (algebraMap Kt L)

/-- The minimal genuinely new source field.  It identifies the values of the already-landed
canonical generators with units of the specified terminal field.  The generators themselves
and their canonical values are not copied: they are C130cr's `wrapValue`/`letterValue` from
the realization's own node and normalizer.  (Byte-identical promotion of
`TAUProbe.CanonicalGeneratorDescent`; campaign gate G4's TAU dictionary component.)
NEW STATEMENT (review). -/
structure CanonicalGeneratorDescent
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : ArisingCore (O := O) Kt L n}
    (Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L)
    (j : ℕ) (hj : GaugeLive core.r j) : Prop where
  wrap : ∃ u : Ktˣ,
    Aℛ.node.wrapValue hj.stageLive = unitAlgebraMap u
  letter : ∀ a : Fin (j - 1), ∃ u : Ktˣ,
    Aℛ.node.letterValue Aℛ.normalizer hj.stageLive a = unitAlgebraMap u

/-! ## §7 [G4] The ONE shared deep-level export record -/

/-- What the shared record makes FREE: an embedded-unit value forced by a `Kt`-point
through the terminal embedding descends as a `Ktˣ` unit — so a receiver/letter equality
implies the corresponding `CanonicalGeneratorDescent` letter clause.  (Fields only:
`Units.mk0` at the nonzero preimage.) -/
theorem letter_descent_of_receiver_eq {Kt : Type uKt} [Field Kt] {L : Type uL} [Field L]
    [Algebra Kt L] {w : Lˣ} {x : Kt} (h : algebraMap Kt L x = (w : L)) :
    ∃ u : Ktˣ, w = unitAlgebraMap u := by
  have hx : x ≠ 0 := by
    intro h0
    exact w.ne_zero (by rw [← h, h0, map_zero])
  refine ⟨Units.mk0 x hx, Units.ext ?_⟩
  simpa using h.symm

/-- **[G4] The ONE shared deep-level export record** at an explicit arising witness and a
deep-live level: the corrected G3 calculus/wiring site package, TAU's canonical-generator
descent dictionary, and the receiver/letter equality tying the calculus letters — through
the SAME receiver `Aℛ.receiver.levelHom j` used by the wiring leg and the SAME embedding
`algebraMap Kt L` used by the descent — to the canonical generator values.  This is gate
G4's single owner record: the TAU dictionary and the WLE exporter are NOT designed
separately and merged later.  The tau-word spanning theorem stays outside (a consumer
field of the future C3 record); the theta/peel/range proofs stay consumer laws (§3).

Letter indexing (review flag): `Λ_a = Φ_{a+1}^{e_{a+2}}·n̂⁻¹` carries stage-`(a+2)` data
(C130cr `letterClass`), so its FGMN twin is the letter `z_{a+2} = letterZ (a.1 + 2)` —
the same stage pairing as the landed S2 template `C130s17.S2SourceFrontier.letter_compat`.
Inhabiting `letter_receiver` at deep levels is campaign row R5 (OPEN-LETTERS).
NEW STATEMENT (review). -/
structure DeepLevelExport
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : ArisingCore (O := O) Kt L n}
    {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L}
    (X : RealizedInput core Aℛ) (j : ℕ) (hj : DeepLive core.r j) :
    Type (max uG uKt uL) where
  site : WleClearedLevelExport.{0, uG, uKt, uL} X j hj.2.le
  descent : CanonicalGeneratorDescent Aℛ j hj.gaugeLive
  letter_receiver : ∀ a : Fin (j - 1),
    algebraMap Kt L (Aℛ.receiver.levelHom j (site.calculus.letterZ (a.1 + 2))) =
      ((Aℛ.node.letterValue Aℛ.normalizer hj.gaugeLive.stageLive a : Lˣ) : L)

namespace DeepLevelExport

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {Kt : Type uKt} [Field Kt] {E : Type} [Field E]
  {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
  {core : ArisingCore (O := O) Kt L n}
  {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
    (hpin := core.hpin) core.T Kt E L}
  {X : RealizedInput core Aℛ} {j : ℕ} {hj : DeepLive core.r j}

/-- [G4] The WLE dictionary projection: the shared record supplies the G3 site package. -/
def wleExport (D : DeepLevelExport.{uG, uKt, uL} X j hj) :
    WleClearedLevelExport.{0, uG, uKt, uL} X j hj.2.le :=
  D.site

/-- [G4] The TAU dictionary projection: the shared record supplies the canonical-generator
descent. -/
theorem tauDictionary (D : DeepLevelExport.{uG, uKt, uL} X j hj) :
    CanonicalGeneratorDescent Aℛ j hj.gaugeLive :=
  D.descent

/-- The shared record's top cleared law (through the WLE projection). -/
theorem top_cleared (D : DeepLevelExport.{uG, uKt, uL} X j hj) :
    GENTOW5WCleared (core.T.trunc j hj.2.le) D.site.e' D.site.f' D.site.u'
      D.site.calculus :=
  D.site.cleared

/-- The shared record's own-export GC-13 wiring leg (through the WLE projection). -/
theorem wiring (D : DeepLevelExport.{uG, uKt, uL} X j hj) :
    IFC3.GC13Wiring
      (Aℛ.normalizer.arenaNormSection0.transport
        (show GaugeLattice.{uG} core.r ≃* GaugeLattice0 core.r from
          gaugeLatticeEquiv core.r).symm)
      (useHeightFamily X j) (towerReadFamily X j) D.site.calculus
      (Aℛ.receiver.levelHom j) :=
  D.site.wiring

/-- The wired sitewise demand at the shared record's own site, given the three consumer
dictionaries (they remain consumer laws — hypotheses, not fields). -/
theorem wiredDemand (D : DeepLevelExport.{uG, uKt, uL} X j hj)
    (hθ : ThetaCompatibleAt X (by rcases hj with ⟨hj3, hjr⟩; omega) D.site)
    (hw : PeelCompatibleAt X D.site)
    (hrange : RangeCompleteAt X (by rcases hj with ⟨hj3, hjr⟩; omega) D.site) :
    IFC3.WiredGentowDemand
      (arenaFamily.{0, uG, uKt, uL} X (by rcases hj with ⟨hj3, hjr⟩; omega) j)
      (useHeightFamily X j) (towerReadFamily X j) (Aℛ.node.peelUnitFamily j)
      D.site.calculus (Aℛ.receiver.levelHom j) :=
  wiredDemand_of_level_export hj D.site hθ hw hrange

/-- **[G4] The shared-record constructor from the letter equality**: the site package,
the wrap descent, and the receiver/letter equality suffice — TAU's letter-descent clause
is DERIVED (`letter_descent_of_receiver_eq`), which is exactly why the two dictionaries
belong in one record: the WLE-side receiver equality already carries the TAU-side
descent content. -/
def ofLetterEq (site : WleClearedLevelExport.{0, uG, uKt, uL} X j hj.2.le)
    (wrap : ∃ u : Ktˣ, Aℛ.node.wrapValue hj.gaugeLive.stageLive = unitAlgebraMap u)
    (hletters : ∀ a : Fin (j - 1),
      algebraMap Kt L (Aℛ.receiver.levelHom j (site.calculus.letterZ (a.1 + 2))) =
        ((Aℛ.node.letterValue Aℛ.normalizer hj.gaugeLive.stageLive a : Lˣ) : L)) :
    DeepLevelExport.{uG, uKt, uL} X j hj where
  site := site
  descent :=
    { wrap := wrap
      letter := fun a => letter_descent_of_receiver_eq (hletters a) }
  letter_receiver := hletters

end DeepLevelExport

/-! ## §8 [G4/DWR §11.4] The per-witness exporter shape and its teeth -/

/-- **The per-witness deep-level exporter** (DWR §11.4's exact quantifier discipline —
the same shape as `WleClearedPerLevelExporter`, at the shared record): after the witness
is explicit, every deep-live level exports the ONE shared record.  Deep inhabitants are
campaign rows C0 (the `j = 3` occurrence) and G10 (the universal theorem); at `r = 4`
the exporter reduces to the constructed `j = 3` case only after `DeepLive 4 j → j = 3`. -/
def DeepLevelPerWitnessExporter
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : ArisingCore (O := O) Kt L n}
    {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L}
    (X : RealizedInput core Aℛ) : Prop :=
  ∀ j, (hj : DeepLive core.r j) → Nonempty (DeepLevelExport.{uG, uKt, uL} X j hj)

/-- The shared exporter supplies the WLE per-level exporter (projection, quantifier for
quantifier — no owner or view is swapped). -/
theorem wleClearedPerLevelExporter_of_deep
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : ArisingCore (O := O) Kt L n}
    {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L}
    {X : RealizedInput core Aℛ}
    (h : DeepLevelPerWitnessExporter.{uG, uKt, uL} X) :
    WleClearedPerLevelExporter.{0, uG, uKt, uL} X :=
  fun j hj => (h j hj).elim fun D => ⟨D.site⟩

/-- Vacuity tooth: at depth `r ≤ 3` there is no deep-live level, so the per-witness
exporter holds vacuously — the shared record is only meaningful at `r ≥ 4`, and shallow
witnesses (the landed S2 chain in particular) supply NO deep evidence. -/
theorem deepLevelPerWitnessExporter_of_shallow
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : ArisingCore (O := O) Kt L n}
    {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L}
    (X : RealizedInput core Aℛ) (hr : core.r ≤ 3) :
    DeepLevelPerWitnessExporter.{uG, uKt, uL} X := by
  intro j hj
  rcases hj with ⟨hj3, hjr⟩
  omega

end Uniformity.Density.DeepExport

end

/-! ## Axiom audit — expect Lean core `{propext, Classical.choice, Quot.sound}` only.
Statement carriers + probe-promotion algebra over the landed IFC1–IFC4/C130/C132 corpus
(cite-free); nothing here may add to the trusted base. -/

#print axioms Uniformity.Density.DeepExport.WleClearedLevelExport
#print axioms Uniformity.Density.DeepExport.WleClearedLevelExport.top_cleared
#print axioms Uniformity.Density.DeepExport.WleClearedLevelExport.ofFixedTriple
#print axioms Uniformity.Density.DeepExport.WleClearedPerLevelExporter
#print axioms Uniformity.Density.DeepExport.WleClearedIndexed
#print axioms Uniformity.Density.DeepExport.wleClearedIndexed_of_fixed
#print axioms Uniformity.Density.DeepExport.wleCleared_of_indexed_const
#print axioms Uniformity.Density.DeepExport.WleClearedIndexed.at_level
#print axioms Uniformity.Density.DeepExport.ThetaCompatibleAt
#print axioms Uniformity.Density.DeepExport.PeelCompatibleAt
#print axioms Uniformity.Density.DeepExport.RangeCompleteAt
#print axioms Uniformity.Density.DeepExport.wiredDemand_of_level_export
#print axioms Uniformity.Density.DeepExport.UniversalWiredDeepGentowSupplier
#print axioms Uniformity.Density.DeepExport.no_s2_deep_level
#print axioms Uniformity.Density.DeepExport.wleCleared_two_vacuous
#print axioms Uniformity.Density.DeepExport.wleClearedIndexed_two_vacuous
#print axioms Uniformity.Density.DeepExport.unitAlgebraMap
#print axioms Uniformity.Density.DeepExport.CanonicalGeneratorDescent
#print axioms Uniformity.Density.DeepExport.letter_descent_of_receiver_eq
#print axioms Uniformity.Density.DeepExport.DeepLevelExport
#print axioms Uniformity.Density.DeepExport.DeepLevelExport.wleExport
#print axioms Uniformity.Density.DeepExport.DeepLevelExport.tauDictionary
#print axioms Uniformity.Density.DeepExport.DeepLevelExport.top_cleared
#print axioms Uniformity.Density.DeepExport.DeepLevelExport.wiring
#print axioms Uniformity.Density.DeepExport.DeepLevelExport.wiredDemand
#print axioms Uniformity.Density.DeepExport.DeepLevelExport.ofLetterEq
#print axioms Uniformity.Density.DeepExport.DeepLevelPerWitnessExporter
#print axioms Uniformity.Density.DeepExport.wleClearedPerLevelExporter_of_deep
#print axioms Uniformity.Density.DeepExport.deepLevelPerWitnessExporter_of_shallow
