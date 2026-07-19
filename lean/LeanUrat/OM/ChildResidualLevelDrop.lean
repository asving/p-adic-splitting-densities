/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.LevelDropResidue

/-!
# `ChildResidualLevelDrop` — the concrete `childResidualExt` reduce-stability, GIVEN the read cutoffs
(P9, WAVE 5, piece 3)

The **CITE-FREE glue**: instantiate the wave-2 abstract transport
`ChildResidualExt.childResidualExt_transport` at the concrete level-drop hom `θ = levelDropHom` (#70)
and residue hom `φ = levelDropResHom`, discharging its per-digit compatibility hypothesis `hcompat`
via the level-drop stability lemma `LevelDropResidue.resUnitResidue_levelDrop` (#71, piece 2a) applied
to each develop-digit.

The one remaining input is the **per-digit read cutoffs** `hcuts : ∀ t, pval_{N+1}(digitₜ) < N`. This is
exactly the content the order-≥2 CITE (piece 2b, `childResidualExt_reduce_stable_fkeyed`) will supply
for ARISING keys under `hbulk : v_p(disc f) < N` (the GMN theorem-of-the-index bound). Everything OTHER
than those cutoffs is now PROVED — so this file reduces the order-≥2 reduce-stability to precisely the
single imported scalar fact, with no other assumption. Nothing here is a citation.

Additive leaf: imports `LevelDropResidue` only (transitively `LevelDrop` + `ChildResidualExt` +
`DevelopmentExt` + `UnramifiedBase`); edits no existing file; core-only (no `sorry`/`axiom`).
-/

set_option linter.style.longLine false

open Polynomial LeanUrat.OM LeanUrat.OM.UnramifiedBase LeanUrat.OM.LevelDrop
open LeanUrat.OM.ChildResidualExt LeanUrat.OM.DevelopmentExt LeanUrat.OM.LevelDropResidue

namespace LeanUrat.OM.ChildResidualLevelDrop

noncomputable section

variable (p N : ℕ) [hp : Fact p.Prime]

/-- **`childResidualExt` is stable under the level drop, GIVEN the per-digit read cutoffs.**
For an arising extension key `Φ` (monic) and box element `h` over `O'' = Oring(p,N+1,g')`, if every
`φ`-adic develop-digit constant term has `pval_{N+1} < N` (the cutoff `hcuts`), then transporting the
child residual along the level-drop hom `θ = levelDropHom` agrees with reducing the level-`N+1` child
residual along the residue hom `φ = levelDropResHom`:

`childResidualExt N (Φ.map θ) μ (h.map θ) = (childResidualExt (N+1) Φ μ h).map φ`.

Proof: a direct instance of `ChildResidualExt.childResidualExt_transport` whose per-digit `hcompat` is
discharged termwise by `LevelDropResidue.resUnitResidue_levelDrop` (#71) at the cutoff `hcuts t`. -/
theorem childResidualExt_reduce_stable_of_cuts
    (g' : (ZMod (p ^ (N + 1)))[X]) (g : (ZMod (p ^ N))[X])
    (hgm' : g'.Monic) (hgm : g.Monic) (h1 : 0 < N + 1) (h2 : 0 < N)
    (hm' : 0 < g'.natDegree) (hgirr : Irreducible (gbar p (N + 1) g' h1))
    [IsLocalRing (Oring p (N + 1) g')] [IsLocalRing (Oring p N g)]
    (hgg : g'.map (levelDropCoeff p N) = g)
    (Φ : (Oring p (N + 1) g')[X]) (hΦ : Φ.Monic) (μ : ℕ)
    (h : (Oring p (N + 1) g')[X])
    (hcuts : ∀ t : Fin μ,
      pval_Oring p (N + 1) g' ((developExt p (N + 1) g' Φ μ h t).coeff 0) < N) :
    childResidualExt p N g hgm h2 (Φ.map (levelDropHom p N g' g hgg)) μ
        (h.map (levelDropHom p N g' g hgg))
      = (childResidualExt p (N + 1) g' hgm' h1 Φ μ h).map
          (levelDropResHom p N g' g h1 h2 hgg) := by
  apply childResidualExt_transport p (N + 1) N g' g hgm' h1 hgm h2
    (levelDropHom p N g' g hgg) (levelDropResHom p N g' g h1 h2 hgg) Φ hΦ μ h
  intro t
  exact resUnitResidue_levelDrop p N g' g hgm' hgm h1 h2 hm' hgirr hgg _ (hcuts t)

end

end LeanUrat.OM.ChildResidualLevelDrop

/-! ## Axiom audit — must be ⊆ [propext, Classical.choice, Quot.sound]. -/

#print axioms LeanUrat.OM.ChildResidualLevelDrop.childResidualExt_reduce_stable_of_cuts
