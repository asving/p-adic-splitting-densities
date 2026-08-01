/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.DictIII.Carriers

/-!
# Scaffold/DictIII/GMNReader — the ι-interface + Cons_f (BP_III §1.2)

Transcribed VERBATIM from `lean/blueprints/BP_III.md` §1.2 (source: O-2a rev-5
(C4)).  This file lands `SideDatum`, `GMNData`, the requested-slope lookup, and
the reader-law structure `GMNReader` (unit III-C8, the dependencies of unit
III-H1 in `DictIII/Hyps.lean`), plus `ConsF` (unit III-C9) — the §1.2 display
is the COMPLETE `ConsF` declaration; no second signature or implicit reader
semantics is permitted.

Display adjustments (same two sanctioned conventions as the Carriers.lean
headers; propositions unchanged, no other token differs from the display):
(1) the §1.2 display writes the ℕ field lines bare (`e h ℓ : ℕ`), which Lean
4.31 parses as untyped binders — parenthesized as `(e h ℓ : ℕ)`, declaring the
SAME fields; (2) the display's `c.slopes.get? i` (in `requestedSlope`) and
`H.continuingPart.nodes.get? i` (in `ConsF`) use `List.get?`, REMOVED from
the pinned environment — the surviving spelling of the SAME function is
`c.slopes[i]?` / `H.continuingPart.nodes[i]?` (`getElem?`).
-/

namespace LeanUrat.Scaffold.DictIII

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- One polygon side's (c1)-shape datum: (e,h,ℓ,s,u) + the −∞ marker. -/
structure SideDatum where
  (e h ℓ : ℕ)                -- binder parens: the III-C2a Lean-4.31 field-group repair
  (s u : ℕ)
  isNegInfty : Bool          -- the slope-−∞ side (length-1, j₀ = 1 corner)

/-- Semantic polygon/residual data. At order ≤ 1 III-A6 constructs this from the
    corpus polygon API; at higher orders `OL1` supplies it. -/
structure GMNData (f : Polynomial ℤ_[p]) (c : ChainData p F) where
  principalSides : ℕ → List SideDatum
  residualOrder : ℕ → ℕ
  residualDegree : ℕ → ℕ
  rootOrder : ℕ

def requestedSlope (c : ChainData p F) (i : ℕ) : Option (ℕ × ℕ) :=
  c.slopes[i]?   -- `List.get?` removed in this toolchain; `[i]?` is the same function (Carriers header note)

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

/-- (C4) Cons_f, over semantic data and its reader. -/
def ConsF (f : Polynomial ℤ_[p]) (H : EHist p F)
    (D : GMNData f (Theta H)) (R : GMNReader f (Theta H) D) : Prop :=
  R.rootOrd = H.a0 ∧
  ∀ i ν, H.continuingPart.nodes[i]? = some ν →   -- `.get?` → `[i]?`: header note (2)
    ∃ S, R.side i = some S ∧
      (S.e, S.h, S.ℓ, S.s, S.u) = (ν.e, ν.h, ν.ℓ, ν.s, ν.u) ∧
      ∀ g μ, ν.sel = some (g, μ) → R.resOrd i = μ

end LeanUrat.Scaffold.DictIII
