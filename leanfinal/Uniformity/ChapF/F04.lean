/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapF.F01

/-!
# Uniformity.ChapF.F04 — `ValueDictSite`, `JD0Box2`: the gauge-form perimeter (HYP.74)

**Chapter F, NODE F.04** [interface-carrier] (`blueprint/CHAP-F_weld_layer.md` §4), ENV-F1.
**Display-A supply node (1 of 2).** `JD0-BOX-2` at EXACTLY ledger strength (HYP.74;
`EFF.JD0.22` BOX-2 verbatim): "That the weld's ENTIRE conditional value dictionary acts by
slot-wise unit characters is the synthesis §3.2 reading of JA-RES [GRTJA, 1/2], the (ξ,w)
covariance family [GRTW2, ACCEPTED], and the ℓ-orbit rescalings ORB-RES [J-A]. J-D0's proof
covers unit-character gauges; any value layer NOT of that form is outside the perimeter."

**This is synthesis, not a theorem** (HYP.74: "JD0 unit-character warrant is synthesis, not
proved theorem"); the carrier is instantiated per site by the fold route, never proved in
general. The grade bar is SIGNED (HYP.39, Q6). The residual leg is deliberately NOT a third
conjunct: the sites consume it through the JA-RES form whose grade cap (GRTJA 1/2) must stay
visible at chapter I (carrier F.19).

Signatures byte-identical to the stage-0e gate. Landed by unit OM-9 (2026-08-16).
-/

namespace Uniformity.Density.Weld

/-- A weld VALUE-DICTIONARY site: an indexed action on slot families, with its residual and
ledger legs. Abstract — instances are the seven cone sites' in-note data. -/
structure ValueDictSite (Γ K : Type*) [AddCommGroup Γ] [Field K] where
  slotAct : (Γ → K) → (Γ → K)
  ledgerAct : (Γ → Γ → Kˣ) → (Γ → Γ → Kˣ)

/-- `JD0-BOX-2` at ledger strength (HYP.74): the site's dictionary is realized by a
slot-wise unit character — a carry gauge in the `EFF.JD0.05` class. CARRIED, not proved;
chapter I's conjunct field. -/
def JD0Box2 {Γ K : Type*} [AddCommGroup Γ] [Field K] (site : ValueDictSite Γ K) : Prop :=
  ∃ u : Γ → Kˣ, site.slotAct = slotScale u ∧ site.ledgerAct = gaugeCobdry u

end Uniformity.Density.Weld
