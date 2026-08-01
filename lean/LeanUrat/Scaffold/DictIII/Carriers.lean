/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Scaffold/DictIII/Carriers — 𝔈 carriers (BP_III §1.1)

E-phase transcription of `lean/blueprints/BP_III.md` §1.1 (Carriers block).
This file currently holds unit III-C1 (`ENodeData`), transcribed VERBATIM.
Source of record: O2a r5 §2 (C1).
-/

namespace LeanUrat.Scaffold.DictIII

/-- O-2a (C1): one node record ν = (e,h,ℓ,s,u,sel,inc). `sel = none` ⇔ terminal. -/
structure ENodeData where
  e h ℓ : ℕ
  s u : ℕ                      -- (C1) REV 2: declared domains ℤ≥0
  sel : Option (ℕ × ℕ)         -- some (g, μ)
  inc : Bool
  he : 1 ≤ e
  hh : 1 ≤ h
  hcop : Nat.gcd e h = 1
  hl : 1 ≤ ℓ
  hsel : ∀ gμ ∈ sel, 1 ≤ gμ.1 ∧ 1 ≤ gμ.2 ∧ gμ.2 * gμ.1 ≤ ℓ

end LeanUrat.Scaffold.DictIII
