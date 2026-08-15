/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.QuadCert

/-!
# Uniformity.ChapG.G52 — the five degree-3 splitting types

**Chapter G, NODE G.52** (`blueprint/CHAP-G_base_cases_menus.md` §8). The five degree-3
splitting types, with their degrees and pairwise distinctness.

DEPENDS: landed `Uniformity.Density.FactorizationType`,
`Uniformity.Density.FactorizationType.degree`.

⚠ **BLUEPRINT DEFECT D3, carried forward (not introduced here).** The blueprint's own SIGNATURE
for the ten pairwise inequalities is the literal placeholder `theorem c3_pairwise_ne :
/- the ten inequalities -/ True`, already recorded as a signature defect at the stage-0e
leanspec gate (`leanspec/Leanspec/ChapG.lean` D3) and landed there verbatim, i.e. vacuous. Per
blueprint §12 rule 3 ("elaboration failures / signature defects go back to the blueprint, never
patched here"), this file lands the SIGNATURE exactly as contracted — the ten inequalities
themselves are not stated and are not proved by this node.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

/-- `{(1,1),(1,1),(1,1)}` — three unramified linear factors. -/
def c3split : FactorizationType := ⟨{(1, 1), (1, 1), (1, 1)}⟩

/-- `{(1,1),(1,2)}` — a linear factor and an unramified quadratic. -/
def c3linInert : FactorizationType := ⟨{(1, 1), (1, 2)}⟩

/-- `{(1,3)}` — one unramified cubic factor. -/
def c3inert : FactorizationType := ⟨{(1, 3)}⟩

/-- `{(1,1),(2,1)}` — a linear factor and a ramified quadratic. -/
def c3linRam : FactorizationType := ⟨{(1, 1), (2, 1)}⟩

/-- `{(3,1)}` — one totally ramified cubic factor. -/
def c3ram : FactorizationType := ⟨{(3, 1)}⟩

theorem c3_degrees :
    c3split.degree = 3 ∧ c3linInert.degree = 3 ∧ c3inert.degree = 3
      ∧ c3linRam.degree = 3 ∧ c3ram.degree = 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [c3split, c3linInert, c3inert, c3linRam, c3ram, FactorizationType.degree]

/-- ⚠ TRANSCRIBED VERBATIM (blueprint defect D3): the blueprint's SIGNATURE for the ten pairwise
inequalities is the placeholder `True`. Landed as contracted. -/
theorem c3_pairwise_ne : True := trivial

section AxCheck
#print axioms Uniformity.Density.c3_degrees
#print axioms Uniformity.Density.c3_pairwise_ne
end AxCheck

end Uniformity.Density
