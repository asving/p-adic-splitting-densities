/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.Field.Basic

/-!
# Uniformity.ChapF.F01 — `gaugeCobdry`, `slotScale`: the unit-character gauge action

**Chapter F, NODE F.01** [def] (`blueprint/CHAP-F_weld_layer.md` §4), ENV-F1 + `[Field K]`.
The carry gauge's documented action, `EFF.JD0.05` lines 1–2 (the four-line perimeter display):

* ledger: `c(γ,γ′) ↦ c(γ,γ′) · u_γ u_{γ′} u_{γ+γ′}^{−1}` (= `c·∂u`) — `gaugeCobdry`;
* slot:   `v ↦ u·v` (unit character, per read slot) — `slotScale`.

The residual line of the display is F.03's `resTwist`; positions, δ, `D_j` and grid abscissas
are UNCHANGED by the action and get no carrier. The LAW that the weld's value dictionary acts
this way is F.04's carried perimeter (`JD0Box2`, HYP.74) — never this node's claim.

Signatures byte-identical to the stage-0e gate (`leanspec/Leanspec/ChapF.lean`, LeanspecF).
Landed by unit OM-9 (2026-08-16).
-/

namespace Uniformity.Density.Weld

/-- The coboundary transform of a `Kˣ`-valued 2-cochain by a 1-cochain `u`
(`EFF.JD0.05` line 1: `c ↦ c·∂u`). -/
def gaugeCobdry {Γ : Type*} [AddCommGroup Γ] {K : Type*} [Field K]
    (u : Γ → Kˣ) (c : Γ → Γ → Kˣ) : Γ → Γ → Kˣ :=
  fun γ γ' => c γ γ' * u γ * u γ' * (u (γ + γ'))⁻¹

/-- The slot-wise unit action (`EFF.JD0.05` line 2): coordinatewise unit scaling of a
slot family. -/
def slotScale {Γ : Type*} {K : Type*} [Field K] (u : Γ → Kˣ) (v : Γ → K) : Γ → K :=
  fun γ => (u γ : K) * v γ

end Uniformity.Density.Weld
