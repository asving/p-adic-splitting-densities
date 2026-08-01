/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.OM.UniformCapstone

/-!
# Scaffold/AnchorN2 — the numerics/instance anchors [wave VI-2]

E-phase transcription of `lean/blueprints/BP_VI.md` §1.4, unit VI-N1.
Anchors are FLAGS, never substitutes (tree §0 discipline): each re-fires a
machine-checked instance in scaffold shape so a regression anywhere in the
spine's import cone breaks a visible gate. Per blueprint fix #13, this unit
imports only its actual OM source (`LeanUrat.OM.UniformCapstone`).
-/

namespace LeanUrat.Scaffold.AnchorN2

open LeanUrat LeanUrat.OM.UniformCapstone

/-- VI-N1 is the exact capstone proposition, not a hand-reconstructed partial
    record. This preserves pole-freeness, the common rational family, value tie,
    and bracket uniqueness together, with the prime instance explicit. -/
def AnchorN2 (p : ℕ) [Fact p.Prime] (σ : FactorizationType)
    (hσ : σ.degree = 2) : Prop :=
  Nonempty (montes_uniform_n2 σ hσ)

theorem anchor_n2 (p : ℕ) [Fact p.Prime] (σ : FactorizationType)
    (hσ : σ.degree = 2) : AnchorN2 p σ :=
  ⟨montes_uniform_n2 σ hσ⟩

end LeanUrat.Scaffold.AnchorN2
