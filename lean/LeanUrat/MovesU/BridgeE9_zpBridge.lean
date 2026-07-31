/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.BridgeE567_zfLaws
import LeanUrat.MovesU.BridgeD9b_liftTrue
import LeanUrat.MovesU.BridgeD11_classifierSpec

/-!
# BridgeE9 — `bridgeZpBridge` ASSEMBLY (bridge campaign BP1, Group E, IB-E9)

THE LAST MISSING `UInstance` FIELD CONSTRUCTION (census
`lean/notes/REMAINING_CENSUS_2026-07-31.md` §2.2: `bridge : ZpBridge` was the one
"DOES NOT EXIST AT HEAD" row).  Per the blueprint
(`lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §4 Group E, IB-E9):
`zfType := bridgeZfType` (IB-E11) · `zf_pos := bridge_zf_pos` (IB-E5) ·
`zf_factor := bridge_zf_factor` (IB-E7) · `lift_exists := bridge_lift_exists`
(IB-E8) · `lift_true := bridgeTrueType_lift_true` (IB-D9b).  The executable order
E1 → E11 → D9a → D10 → (E8, E10) → D9b → E9 is complete at this file; the zpDmass
laws (`ZpBridge.zpCount_eq_trueCount`/`zpDmass_eq_trueDmass`) come free from
DefsLedger.

TRANSCRIPTION RESOLUTIONS (statement fence; E-phase rule):
1. The classifier binder: `ZpBridge` is indexed by a `ClassifierSpec`, whose
   `canonical`/`canonical_stable` legs are OTHER clusters' constructions (IB-D7/D8,
   themselves over the IB-A11 `boxeq` dictionary).  Per the BridgeD9a/D11 precedent
   this file takes them as BINDERS with the verbatim field types and assembles the
   bridge AT `bridgeClassifierSpec n p canonical canonical_stable bridgeZfType`
   (IB-D11's construction, whose `trueType` is IB-D9a's `bridgeTrueType` at
   `bridgeZfType` definitionally) — so `mkUInstance`'s wiring
   (`BridgeMk.lean` header: `bridge := IB-E9's bridgeZpBridge assembly`) consumes
   this def at the same instantiation it consumes D11's.
2. No new law is stated here: every field is a landed theorem consumed verbatim
   (the IB-E9 blueprint row is R ~10 — assembly only).

CONDITIONALITY: the record literal's `zf_pos`/`zf_factor` legs carry the ONE
declared literature axiom `LeanUrat.SerreLocalFields.AX_integralClosure_dvr`
(Serre, *Local Fields* GTM 67, Ch. II §2, Prop. 3 — Codex guardian audit PASSED
2026-07-31, `docs/AXIOM_FAITHFULNESS.md` AX-SERRE-DVR); everything else is
Lean-core.  Census at the bottom.
Build: `lake env lean LeanUrat/MovesU/BridgeE9_zpBridge.lean`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU
open Polynomial

/-- IB-E9 — `bridgeZpBridge`: THE `ZpBridge` instance at the constructed
    classifier (IB-D11's `bridgeClassifierSpec` at `zf := bridgeZfType`), from
    the five landed suppliers (file header).  This closes the `UInstance` field
    table's last missing construction (census §2.2).  [Footprint:
    `AX_integralClosure_dvr` + core, through the E5/E7 legs.] -/
noncomputable def bridgeZpBridge (n p : ℕ) [Fact p.Prime]
    (canonical : ∀ N : ℕ, Box p n N → Option (SplittingType n))
    (canonical_stable : ∀ {N N' : ℕ} (h : N ≤ N') (f : Box p n N')
      (σ : SplittingType n),
      canonical N (boxProj p n h f) = some σ → canonical N' f = some σ) :
    ZpBridge n p (bridgeClassifierSpec n p canonical canonical_stable
      (bridgeZfType (p := p))) where
  zfType := bridgeZfType
  zf_pos := bridge_zf_pos n
  zf_factor := bridge_zf_factor n
  lift_exists := fun N f => bridge_lift_exists n N f
  lift_true := fun N f σ =>
    bridgeTrueType_lift_true (bridgeZfType (p := p))
      (fun N f => bridge_lift_exists n N f) N f σ

/-- Definitional display: the assembled bridge's reading IS IB-E11's
    `bridgeZfType` (the (†8u)/(†11) vocabulary seam is `rfl`). -/
theorem bridgeZpBridge_zfType (n p : ℕ) [Fact p.Prime]
    (canonical : ∀ N : ℕ, Box p n N → Option (SplittingType n))
    (canonical_stable : ∀ {N N' : ℕ} (h : N ≤ N') (f : Box p n N')
      (σ : SplittingType n),
      canonical N (boxProj p n h f) = some σ → canonical N' f = some σ) :
    (bridgeZpBridge n p canonical canonical_stable).zfType
      = bridgeZfType (p := p) := rfl

/-! ## Census (expected: `bridgeZpBridge` prints `AX_integralClosure_dvr` + core —
the M16 single-axiom conditionality through the E5/E7 legs; the display is core). -/

section AxCheck

#print axioms LeanUrat.MovesU.bridgeZpBridge
#print axioms LeanUrat.MovesU.bridgeZpBridge_zfType

end AxCheck

end LeanUrat.MovesU
