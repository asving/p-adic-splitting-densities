/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-V2 `vd_deg_ns` — the (τ-ns) verdict degree (MOVES 7083): degree = cluster
degree μ·deg Φ̂. PROVED (E-phase prove-now set). -/

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

theorem vd_deg_ns (μ E F : ℕ) (hE : 1 ≤ E) (hF : 1 ≤ F) :
    (nsVerdict μ E F hE hF).deg = μ * (E * F) := by
  simp [Vd.deg, nsVerdict, Multiset.map_replicate, Multiset.sum_replicate]

end LeanUrat.MovesT
