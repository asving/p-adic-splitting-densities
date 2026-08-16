/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Logic.Basic

/-!
# Uniformity.ChapF.F24 — `WeldMPkg`: the anchored five-face transport package

**Chapter F, NODE F.24** [def] (`blueprint/CHAP-F_weld_layer.md` §7), ENV-F1. `WELD-M-PKG`
transcribed from `EFF.WELDMASTER.22` (the C6 F-1 annex, the charge unit): for a tower on the
frozen S1 perimeter there is ONE NAMED PACKAGE `𝐓 = (𝐓_{M0}, …, 𝐓_{M4})` whose fields are
exactly the frozen clauses —

* **M0** the division-chain identity;
* **M1** `w_m = v_{m+1}` together with the affine shear and its fences (F.22's shape);
* **M2** the per-slot read/operator character transport;
* **M3** the multiplication transport to `K^c[ℤ/E]` on the scored stratum (a `CarryCocycle`
  realization, F.07/F.08's shape);
* **M4** the representative/lift covariance at W2-C3's accepted fenced scope (F.21's shape).

**"One" means one named five-field package — not uniqueness, and not a further common-map
coherence theorem.** The RECORD-ASSEMBLY LEMMA is the product constructor ("Choose the five
cited witnesses and apply the product/record constructor"), so it is the anonymous
constructor here and gets no separate node; the η-twist non-uniqueness witness
(`∂(Ẽη) = ∂Ẽ`) is F.25's content.

**The F-1 lesson, honoured structurally: there is NO cross-face compatibility field.** The
five faces are `Prop` PARAMETERS, which makes the record exactly the "product of five
propositions" the source says it is; typing the faces concretely would assert the cross-face
tie the source explicitly declines ("No compatibility beyond those displayed ties is
asserted"), and T1's own consumption at L13/L1074 honours exactly this scope. For the same
reason the module imports none of F.07/F.08/F.21/F.22: their shapes are the intended
*instantiations* of the parameters, not Lean dependencies of the package.

Chapter D cites this node for its (C7) anchor as "an interface map and scope fence". M4's
W2-C3 instance is **BLOCKED: GC-13** (`EFF.GRTW2.29 [supplied-by: chapter C]`) and is NOT
stubbed. `EFF.WELDMASTER.03` (the superseded frozen S1 "ONE transport" wording) is NOT
transcribed — the annex's package form governs.

Teeth: the frozen face table's per-field batteries, RECORDED at WELDMASTER; the package's
Lean content is definitional. Signature byte-identical to the stage-0e gate
(`leanspec/Leanspec/ChapF.lean`, LeanspecF).
-/

namespace Uniformity.Density.Weld

/-- WELD-M-PKG (`EFF.WELDMASTER.22`): the five-face transport package as a record of five
Props. Existence-only; NO cross-face coherence field. Chapter D's (C7) consumption anchor;
the field contents are per-face site data (M3 = a `CarryCocycle` realization; M4 at W2-C3's
fenced scope via GC-13). -/
structure WeldMPkg (M0 M1 M2 M3 M4 : Prop) : Prop where
  m0 : M0
  m1 : M1
  m2 : M2
  m3 : M3
  m4 : M4

end Uniformity.Density.Weld
