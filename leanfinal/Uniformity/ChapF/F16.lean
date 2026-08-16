/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.Field.Basic

/-!
# Uniformity.ChapF.F16 — SL-C2's core: strict ⟹ unit-trivial

**Chapter F, NODE F.16** [lemma] (`blueprint/CHAP-F_weld_layer.md` §6), ENV-F1 +
`[Field K]`. COROLLARY SL-C2 = THEOREM OPEN-2a-Σ's Σ-leg (`EFF.SIGMALAW.09`), transcribed
on the source's own **weaker** hypotheses: `Σ` is only assumed INJECTIVE with `Σ 1 = 1`
("Σ_m is a K₀-linear coordinate BIJECTION fixing 1 … no automorphism property needed,
OA-M1 not consumed"). Chain: `Σ ρ = 1 = Σ 1` ⟹ `ρ = 1` by injectivity. This is what made
OPEN-2a-Σ "unconditional on its Σ-leg".

Scope fences carried from the source:

* the CONVERSE (the note's N-1) is UNPROVED and is stated by no F node;
* the OA-L3 / OA-L4 legs (strictness ⟹ `δ_j = ρ_j` on supp; unit-trivial ⟹ byte-equal) are
  OPEN2ATTACK content with no effective spec — they stay at their consuming instances
  (F.17), cited and never transcribed (GC-10). This node is the middle link only.

*[repaired: A-W.1/F-D1]* the implicit binder is `sigmaMap` (the signed `Σmap` is not a legal
Lean identifier); a binder name, so no type content moves, but named-argument call sites use
this spelling.

Was an `axiom` stub at stage 0e; PROVED here (2026-08-16). Signature byte-identical to the
stage-0e gate (`leanspec/Leanspec/ChapF.lean`, LeanspecF).
-/

namespace Uniformity.Density.Weld

theorem unit_eq_one_of_sigma_eq_one {K : Type*} [Field K]
    {sigmaMap : K → K} (hinj : Function.Injective sigmaMap) (h1 : sigmaMap 1 = 1)
    (ρ : Kˣ) (hρ : sigmaMap (ρ : K) = 1) : (ρ : K) = 1 :=
  hinj (hρ.trans h1.symm)

end Uniformity.Density.Weld
