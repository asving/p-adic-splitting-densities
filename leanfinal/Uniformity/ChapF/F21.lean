/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapF.F03

/-!
# Uniformity.ChapF.F21 — `XiWSatisfies`: the `(ξ, w)` covariance family, at satisfaction strength

**Chapter F, NODE F.21** [interface-carrier] (`blueprint/CHAP-F_weld_layer.md` §7), ENV-F1.
The `(ξ, w)` covariance family at its ACCEPTED fenced scope (`JD0-BOX-2`'s GRTW2 leg). From
`EFF.GRTW2.19` — the closed form: THE DISPLAYED PAIR SATISFIES the orbit equations,
deliberately NOT "is the pair" — and `EFF.GRTJA.11` (the orbit action; the ORB legs are
PROVED/machine, ORB-EPS 1,744 / ORB-RES 444 / TW-INST 1,452). Consumed by J-D0 as part of
the gauge dictionary (BOX-2): "anchor re-choice legitimacy rides the accepted lift
covariance, with LIFTCORNER as its corner cap" (`EFF.JD0.25`; the corner cap is provenance
on F.04, not a Lean dependency here).

**SATISFACTION, NEVER UNIQUENESS — the source's own deliberate weakening** (`EFF.GRTW2.21`,
remark 2: the support-stabilizer non-uniqueness). Distinct satisfying characters exist on
sparse supports — the invisible-twist genre, machine-recorded at I4B `r = 4` with `ξ = −1`
invisible on `supp = {0, 2}` over `F₃` (the spec's stabilizer arithmetic `ξ² = 1 ⟹ ξ ∈ {±1}`;
F.30 exhibits the instance numerically). **A consumer that adds a uniqueness clause has left
the source.**

**What is NOT carried:** `EFF.GRTJA.11`'s chamber half (consumed at split grade, riding
W2-OPEN-2) is out-of-cone value mass (§3 row 10) and appears nowhere in this file.

**DEPENDS F.03** (`BP.F.21 → BP.F.03`, proof-dep): F.03's `resTwist ξ R` is the
monic-normalized special case of this covariance shape — the overall unit `w` is the degree
factor `ξ^{−deg R}` there, which is why "the (ξ,w) overall unit dies in monic form". The
carrier itself keeps `w` free, so no monicity is presupposed here.

Signature byte-identical to the stage-0e gate (`leanspec/Leanspec/ChapF.lean`).
-/

namespace Uniformity.Density.Weld

open Polynomial

/-- The (ξ,w) orbit-equation predicate (`EFF.GRTW2.19`): the displayed pair SATISFIES the
covariance equations — an existence/satisfaction form, never uniqueness (`EFF.GRTW2.21`). -/
def XiWSatisfies {K : Type*} [Field K] (ξ w : Kˣ) (R ψ : K[X]) : Prop :=
  R = (w : K) • ψ.comp (C (ξ : K) * X)

end Uniformity.Density.Weld
