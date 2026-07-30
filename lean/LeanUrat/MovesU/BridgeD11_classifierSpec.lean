/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.BridgeD9a_trueTypeDef

/-!
# IB-D11 — `bridgeClassifierSpec` ASSEMBLY (bridge campaign BP1, cluster c9)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.4
(†7)/(†8), Architecture B (adjudication Q1, RATIFIED) / §4 group D (IB-D11).

INFORMAL STATEMENT: assemble the per-(n, p) `ClassifierSpec` of the bridge:
`canonical` := the VTree-fibering verdict (IB-D7's `bridgeCanonical`),
`trueType` := IB-D9a's `bridgeTrueType` (through `ZpReads`), `canonical_stable`
:= IB-D8's TransferRow consequence, `baseSection := .teichmuller` — with the
`o3_teichmuller` rfl display (`CapstoneLedger.o3_teichmuller`'s supply).

DEPS: D7, D8, D9a/D9b, D10.  TRANSCRIPTION RESOLUTION (recorded): IB-D7
(`bridgeCanonical`) and IB-D8 (`canonical_stable`) are another cluster's units,
not landed — the canonical map and its stability law are BINDERS with the
`ClassifierSpec` fields' verbatim types (Defs.lean:62–67); the ℤ_p reading `zf`
is a binder per IB-D9a's recorded resolution (instantiated at IB-E11's
`zfType`).  IB-F4 (`mkUInstance`) instantiates all three.

PROOF SKETCH: assembly-only unit (R, ~10) — record literal + rfl lemmas; no
sorry needed (the mathematics lives in the binders' suppliers).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

/-- (†7)/(†8) THE BRIDGE CLASSIFIER: Architecture B's `ClassifierSpec` assembly.
    `canonical`/`canonical_stable` = IB-D7/IB-D8's constructions (binders here —
    file header); `trueType` = IB-D9a's `bridgeTrueType` at `zf` (= IB-E11's
    `zfType` at consumption); `baseSection` = Teichmüller (the O3 pin, (†7)). -/
noncomputable def bridgeClassifierSpec (n p : ℕ) [Fact p.Prime]
    (canonical : ∀ N : ℕ, Box p n N → Option (SplittingType n))
    (canonical_stable : ∀ {N N' : ℕ} (h : N ≤ N') (f : Box p n N')
      (σ : SplittingType n),
      canonical N (boxProj p n h f) = some σ → canonical N' f = some σ)
    (zf : Polynomial ℤ_[p] → Multiset (ℕ × ℕ)) :
    ClassifierSpec n p where
  canonical := canonical
  trueType := bridgeTrueType n p zf
  canonical_stable := canonical_stable
  baseSection := .teichmuller

/-- The canonical map reads through (definitional display). -/
theorem bridgeClassifierSpec_canonical (n p : ℕ) [Fact p.Prime]
    (canonical : ∀ N : ℕ, Box p n N → Option (SplittingType n))
    (canonical_stable : ∀ {N N' : ℕ} (h : N ≤ N') (f : Box p n N')
      (σ : SplittingType n),
      canonical N (boxProj p n h f) = some σ → canonical N' f = some σ)
    (zf : Polynomial ℤ_[p] → Multiset (ℕ × ℕ)) :
    (bridgeClassifierSpec n p canonical canonical_stable zf).canonical
      = canonical := rfl

/-- The true-type map IS IB-D9a's `bridgeTrueType` (definitional display). -/
theorem bridgeClassifierSpec_trueType (n p : ℕ) [Fact p.Prime]
    (canonical : ∀ N : ℕ, Box p n N → Option (SplittingType n))
    (canonical_stable : ∀ {N N' : ℕ} (h : N ≤ N') (f : Box p n N')
      (σ : SplittingType n),
      canonical N (boxProj p n h f) = some σ → canonical N' f = some σ)
    (zf : Polynomial ℤ_[p] → Multiset (ℕ × ℕ)) :
    (bridgeClassifierSpec n p canonical canonical_stable zf).trueType
      = bridgeTrueType n p zf := rfl

/-- `o3_teichmuller` — the `CapstoneLedger.o3_teichmuller` field's supply at the
    constructed classifier, by `rfl` (†7's `baseSection := .teichmuller`). -/
theorem bridgeClassifierSpec_teichmuller (n p : ℕ) [Fact p.Prime]
    (canonical : ∀ N : ℕ, Box p n N → Option (SplittingType n))
    (canonical_stable : ∀ {N N' : ℕ} (h : N ≤ N') (f : Box p n N')
      (σ : SplittingType n),
      canonical N (boxProj p n h f) = some σ → canonical N' f = some σ)
    (zf : Polynomial ℤ_[p] → Multiset (ℕ × ℕ)) :
    (bridgeClassifierSpec n p canonical canonical_stable zf).baseSection
      = BaseSection.teichmuller := rfl

end LeanUrat.MovesU
