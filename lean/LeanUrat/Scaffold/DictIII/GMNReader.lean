/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.DictIII.Carriers

/-!
# Scaffold/DictIII/GMNReader — the ι-interface (BP_III §1.2, partial landing)

Transcribed VERBATIM from `lean/blueprints/BP_III.md` §1.2 (source: O-2a rev-5
(C4)).  This file lands `SideDatum`, `GMNData`, the requested-slope lookup, and
the reader-law structure `GMNReader` — the III-C8 dependencies of unit III-H1
(`DictIII/Hyps.lean`).  `ConsF` (which additionally needs `EHist`/`Theta` from
the full Carriers landing) is left to its owning unit.
-/

namespace LeanUrat.Scaffold.DictIII

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- One polygon side's (c1)-shape datum: (e,h,ℓ,s,u) + the −∞ marker. -/
structure SideDatum where
  e h ℓ : ℕ
  s u : ℕ
  isNegInfty : Bool          -- the slope-−∞ side (length-1, j₀ = 1 corner)

/-- Semantic polygon/residual data. At order ≤ 1 III-A6 constructs this from the
    corpus polygon API; at higher orders `OL1` supplies it. -/
structure GMNData (f : Polynomial ℤ_[p]) (c : ChainData p F) where
  principalSides : ℕ → List SideDatum
  residualOrder : ℕ → ℕ
  residualDegree : ℕ → ℕ
  rootOrder : ℕ

def requestedSlope (c : ChainData p F) (i : ℕ) : Option (ℕ × ℕ) :=
  c.slopes.get? i

def HasRequestedSlope (c : ChainData p F) (i : ℕ) (S : SideDatum) : Prop :=
  requestedSlope c i = some (S.e, S.h)

/-- Reader laws explicitly connect lookup to polygon sides and residual data. -/
structure GMNReader (f : Polynomial ℤ_[p]) (c : ChainData p F)
    (D : GMNData f c) where
  side : ℕ → Option SideDatum
  side_spec : ∀ i S,
    side i = some S ↔ S ∈ D.principalSides i ∧ HasRequestedSlope c i S
  side_unique : ∀ i S T,
    S ∈ D.principalSides i → T ∈ D.principalSides i →
    HasRequestedSlope c i S → HasRequestedSlope c i T → S = T
  resOrd : ℕ → ℕ
  resOrd_spec : ∀ i, resOrd i = D.residualOrder i
  rootOrd : ℕ
  rootOrd_spec : rootOrd = D.rootOrder
  resDeg_eq_sideDeg : ∀ i S,
    side i = some S → D.residualDegree i = S.ℓ

end LeanUrat.Scaffold.DictIII
