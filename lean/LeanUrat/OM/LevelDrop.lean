/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.UnramifiedBase

/-!
# Level-drop homomorphism for the unramified base ring (`LevelDrop`)

Additive leaf over `LeanUrat.OM.UnramifiedBase`. This file connects the level-`N+1` unramified
base ring `AdjoinRoot g'` (over `ZMod (p^(N+1))`) with the level-`N` ring `AdjoinRoot g`
(over `ZMod (p^N)`), where `g` is the coefficientwise reduction `g'.map (levelDropCoeff p N)`.

The payoff is `resHom_natural_levelDrop`: residue reduction commutes with the level drop, i.e.
the square
```
  AdjoinRoot g'  --levelDropHom-->  AdjoinRoot g
       |                                 |
   resHom (N+1)                     resHom N
       v                                 v
  resField (N+1) --levelDropResHom-->  resField N
```
commutes. This is the CITE-FREE naturality statement (no external references), and the
prerequisite for a later reduce-stability lemma.

## Contents
1. `levelDropCoeff` — the single-step coefficient reduction `ZMod (p^(N+1)) →+* ZMod (p^N)`.
2. `levelDropHom` — the induced ring hom `AdjoinRoot g' →+* AdjoinRoot g` (`t' ↦ t`, base reduced).
3. `levelDropHom_mk`, `levelDropHom_root` — its action on `mk`-generators and on the adjoined root.
4. `gbar_levelDrop` — the two mod-`p` reductions agree: `ḡ' = ḡ` (both are `g' mod p`).
5. `levelDropResHom` — the residue-field hom `resField (N+1) →+* resField N`.
6. `resHom_natural_levelDrop` — the naturality square commutes.

Discipline: no `sorry`/`axiom`/`native_decide`; `Mathlib`-only + `LeanUrat.OM.UnramifiedBase`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.LevelDrop

open Polynomial LeanUrat.OM.UnramifiedBase

variable (p N : ℕ) [hp : Fact p.Prime]

noncomputable section

/-! ## 1. The level-drop coefficient reduction `ZMod (p^(N+1)) →+* ZMod (p^N)` -/

/-- **Single-step coefficient reduction** `ZMod (p^(N+1)) →+* ZMod (p^N)` (`p^N ∣ p^(N+1)`).
Same idiom as `Classifier.coeffReduce` and `UnramifiedBase.redHom`. -/
def levelDropCoeff : ZMod (p ^ (N + 1)) →+* ZMod (p ^ N) :=
  ZMod.castHom (pow_dvd_pow p (Nat.le_succ N)) (ZMod (p ^ N))

/-! ## 2. The level-drop ring hom `AdjoinRoot g' →+* AdjoinRoot g` -/

variable (g' : (ZMod (p ^ (N + 1)))[X]) (g : (ZMod (p ^ N))[X])

/-- The eval-condition witnessing that `levelDropHom` is well-defined: evaluating `g'` along the
composed coefficient hom `(AdjoinRoot.of g).comp (levelDropCoeff)` at `root g` vanishes, because
`g'.map (levelDropCoeff) = g` and `root g` is a root of `g`. Mirror of
`UnramifiedBase.eval₂_g_root_gbar`. -/
theorem eval₂_g'_root_g (hgg : g'.map (levelDropCoeff p N) = g) :
    g'.eval₂ ((AdjoinRoot.of g).comp (levelDropCoeff p N)) (AdjoinRoot.root g) = 0 := by
  have h1 : g'.eval₂ ((AdjoinRoot.of g).comp (levelDropCoeff p N)) (AdjoinRoot.root g)
      = (g'.map (levelDropCoeff p N)).eval₂ (AdjoinRoot.of g) (AdjoinRoot.root g) := by
    rw [Polynomial.eval₂_map]
  rw [h1, hgg, AdjoinRoot.eval₂_root]

/-- **The level-drop ring hom** `AdjoinRoot g' →+* AdjoinRoot g`, sending the adjoined root `t'` to
`t` and reducing the base along `levelDropCoeff : ZMod (p^(N+1)) →+* ZMod (p^N)`. Requires
`g = g'.map (levelDropCoeff)`. Mirror of `UnramifiedBase.resHom`. -/
def levelDropHom (hgg : g'.map (levelDropCoeff p N) = g) :
    AdjoinRoot g' →+* AdjoinRoot g :=
  AdjoinRoot.lift ((AdjoinRoot.of g).comp (levelDropCoeff p N)) (AdjoinRoot.root g)
    (eval₂_g'_root_g p N g' g hgg)

/-! ## 3. Action on generators -/

/-- `levelDropHom (mk g' q) = mk g (q.map levelDropCoeff)` — the hom intertwines the two quotient
maps along coefficientwise reduction. Mirror of `UnramifiedBase.resHom_mk`. -/
theorem levelDropHom_mk (hgg : g'.map (levelDropCoeff p N) = g) (q : (ZMod (p ^ (N + 1)))[X]) :
    levelDropHom p N g' g hgg (AdjoinRoot.mk g' q)
      = AdjoinRoot.mk g (q.map (levelDropCoeff p N)) := by
  rw [levelDropHom, AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← AdjoinRoot.aeval_eq,
    Polynomial.aeval_def, AdjoinRoot.algebraMap_eq]

/-- `levelDropHom (root g') = root g`. Mirror of `UnramifiedBase.resHom_troot`. -/
theorem levelDropHom_root (hgg : g'.map (levelDropCoeff p N) = g) :
    levelDropHom p N g' g hgg (AdjoinRoot.root g') = AdjoinRoot.root g := by
  rw [levelDropHom, AdjoinRoot.lift_root]

/-! ## 4. The two mod-`p` reductions agree -/

/-- **`gbar` agreement**: `ḡ' = ḡ` as polynomials over `ZMod p`. Both equal `g' mod p`, since the
level-`N+1 → N` reduction followed by the mod-`p` reduction equals the direct mod-`p` reduction
(composition of `ZMod.castHom`s). Uses `hgg : g'.map (levelDropCoeff) = g`. -/
theorem gbar_levelDrop (h1 : 0 < N + 1) (h2 : 0 < N)
    (hgg : g'.map (levelDropCoeff p N) = g) :
    gbar p (N + 1) g' h1 = gbar p N g h2 := by
  -- both sides are `g'.map (something : ZMod (p^(N+1)) →+* ZMod p)`
  rw [gbar, gbar, ← hgg, Polynomial.map_map]
  congr 1
  -- goal: `redHom p (N+1) h1 = (redHom p N h2).comp (levelDropCoeff p N)`
  rw [redHom, redHom, levelDropCoeff,
    ZMod.castHom_comp (dvd_pow_self p h2.ne') (pow_dvd_pow p (Nat.le_succ N))]

/-! ## 5. The residue-field level-drop hom -/

/-- The eval-condition for `levelDropResHom`: `ḡ'` (evaluated along `of ḡ` at `root ḡ`) vanishes,
because `ḡ' = ḡ` (step 4) and `root ḡ` is a root of `ḡ`. -/
theorem eval₂_gbar'_root_gbar (h1 : 0 < N + 1) (h2 : 0 < N)
    (hgg : g'.map (levelDropCoeff p N) = g) :
    (gbar p (N + 1) g' h1).eval₂ (AdjoinRoot.of (gbar p N g h2))
        (AdjoinRoot.root (gbar p N g h2)) = 0 := by
  rw [gbar_levelDrop p N g' g h1 h2 hgg, AdjoinRoot.eval₂_root]

/-- **The residue-field level-drop hom** `resField (N+1) →+* resField N`, i.e.
`AdjoinRoot ḡ' →+* AdjoinRoot ḡ`. Since `ḡ' = ḡ` (step 4), it is (definitionally) the identity-flavoured
lift `root ḡ' ↦ root ḡ` with base `id : ZMod p → ZMod p`. -/
def levelDropResHom (h1 : 0 < N + 1) (h2 : 0 < N)
    (hgg : g'.map (levelDropCoeff p N) = g) :
    resField p (N + 1) g' h1 →+* resField p N g h2 :=
  AdjoinRoot.lift (AdjoinRoot.of (gbar p N g h2)) (AdjoinRoot.root (gbar p N g h2))
    (eval₂_gbar'_root_gbar p N g' g h1 h2 hgg)

/-- `levelDropResHom (mk ḡ' r) = mk ḡ r` (the base map is the identity on `ZMod p`). -/
theorem levelDropResHom_mk (h1 : 0 < N + 1) (h2 : 0 < N)
    (hgg : g'.map (levelDropCoeff p N) = g) (r : (ZMod p)[X]) :
    levelDropResHom p N g' g h1 h2 hgg (AdjoinRoot.mk (gbar p (N + 1) g' h1) r)
      = AdjoinRoot.mk (gbar p N g h2) r := by
  rw [levelDropResHom, AdjoinRoot.lift_mk, ← AdjoinRoot.aeval_eq, Polynomial.aeval_def,
    AdjoinRoot.algebraMap_eq]

/-! ## 6. The naturality square commutes -/

/-- **Naturality (CITE-FREE)**: residue reduction commutes with the level drop, i.e. the square
`resHom N ∘ levelDropHom = levelDropResHom ∘ resHom (N+1)` commutes. Proof by `RingHom.ext`,
reducing both sides on the `AdjoinRoot.mk`-generators using the `_mk` lemmas and `gbar` agreement. -/
theorem resHom_natural_levelDrop (h1 : 0 < N + 1) (h2 : 0 < N)
    (hgm' : g'.Monic) (hgm : g.Monic) (hgg : g'.map (levelDropCoeff p N) = g) :
    (resHom p N g hgm h2).comp (levelDropHom p N g' g hgg)
      = (levelDropResHom p N g' g h1 h2 hgg).comp (resHom p (N + 1) g' hgm' h1) := by
  apply RingHom.ext
  intro x
  -- write `x = mk g' q`
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
  rw [RingHom.comp_apply, RingHom.comp_apply]
  -- LHS: resHom N (levelDropHom (mk g' q)) = resHom N (mk g (q.map levelDropCoeff))
  rw [levelDropHom_mk, resHom_mk]
  -- RHS: levelDropResHom (resHom (N+1) (mk g' q)) = levelDropResHom (mk ḡ' (q.map redHom))
  rw [resHom_mk, levelDropResHom_mk]
  -- both are `mk ḡ (q.map (redHom p N h2) ∘ (levelDropCoeff p N))`-ish; reconcile the coeff maps.
  congr 1
  -- `(q.map (levelDropCoeff p N)).map (redHom p N h2) = q.map (redHom p (N+1) h1)`
  rw [Polynomial.map_map]
  congr 1
  rw [redHom, redHom, levelDropCoeff,
    ZMod.castHom_comp (dvd_pow_self p h2.ne') (pow_dvd_pow p (Nat.le_succ N))]

end

end LeanUrat.OM.LevelDrop

/-! ## Axiom audit — every main def/theorem must be core-only. -/

#print axioms LeanUrat.OM.LevelDrop.levelDropCoeff
#print axioms LeanUrat.OM.LevelDrop.levelDropHom
#print axioms LeanUrat.OM.LevelDrop.levelDropHom_mk
#print axioms LeanUrat.OM.LevelDrop.levelDropHom_root
#print axioms LeanUrat.OM.LevelDrop.gbar_levelDrop
#print axioms LeanUrat.OM.LevelDrop.levelDropResHom
#print axioms LeanUrat.OM.LevelDrop.levelDropResHom_mk
#print axioms LeanUrat.OM.LevelDrop.resHom_natural_levelDrop
