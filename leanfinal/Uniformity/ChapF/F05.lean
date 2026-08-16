/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapF.F04

/-!
# Uniformity.ChapF.F05 — `JD0SiteStrike`: the per-site strike ledger (HYP.74's fold route)

**Chapter F, NODE F.05** [def] (`blueprint/CHAP-F_weld_layer.md` §4), ENV-F1. HYP.74's
discharge route is a FOLD: "record per site that the gauge consumed there is an explicit
z-power unit character verified in-note, which strikes the inheritance." This node lands the
witness shape. The SEVEN strike obligations (W11, W12, HMENU3, HEX3, GENIND, GENH4, GENHN)
are INSTANCE-ROWS, not nodes — instantiable only when the corresponding chapters' Lean site
objects exist (GC-13). That a strike witnesses `JD0Box2` is `F04w.lean`'s
`JD0SiteStrike.jd0Box2` (the fold route's site-independent half, unit OM-9).

Signatures byte-identical to the stage-0e gate. Landed by unit OM-9 (2026-08-16).
-/

namespace Uniformity.Density.Weld

/-- A per-site STRIKE (HYP.74's fold route): the site's gauge exhibited as an explicit
z-power unit character. One instance per audited cone site. -/
structure JD0SiteStrike (Γ K : Type*) [AddCommGroup Γ] [Field K] where
  site : ValueDictSite Γ K
  z : Kˣ
  a : Γ → ℤ
  strike : site.slotAct = slotScale (fun γ => z ^ a γ)

end Uniformity.Density.Weld
