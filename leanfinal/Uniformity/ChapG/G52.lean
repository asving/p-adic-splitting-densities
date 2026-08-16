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

DEPENDS: landed `Uniformity.FactorizationType`, `Uniformity.FactorizationType.degree`.
(Docstring FQN corrected 2026-08-16, CHAP-E amendment A-E.1/E-D8: the carrier lives in
`Uniformity`, not `Uniformity.Density` — `Uniformity/Density/LocalData.lean:43`. Comment only;
no statement, proof or import is touched.)

✅ **BLUEPRINT DEFECT D3 CURED** (AMENDMENT 2026-08-15 §A-6). The blueprint's original SIGNATURE
for the ten pairwise inequalities was the literal placeholder `theorem c3_pairwise_ne :
/- the ten inequalities -/ True` — recorded as a signature defect at the stage-0e leanspec gate
(`leanspec/Leanspec/ChapG.lean` D3) and landed there and here verbatim, i.e. vacuous. Per
blueprint §12 rule 3 the repair went back to the blueprint: the intended statement was recovered
from G.52's own STATEMENT ("the five degree-3 splitting types, with their degrees and **pairwise
distinctness**"; the five constants are `EFF.HMENU3.17`'s COROLLARY HM3.D rows) and from the
declared consumer G.72, whose PROOF step 3 expands the 5-element menu with "the four distinctness
side conditions from G.52's `c3_pairwise_ne`". `C(5,2) = 10`, so "the ten inequalities" are the
five constants pairwise distinct as `FactorizationType`s; the blueprint was amended with that
signature, and this file now lands it. The order is `leancheck/UniformityCheck/N3Base.lean`'s (the
node's ⚠ RE-DERIVATION TARGET, which lands the same ten as ten separate `decide`-backed lemmas);
the proof is the blueprint's own PROOF line, "`decide` after reducing to multiset inequality".

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

/-- The ten pairwise inequalities: the five degree-3 splitting types are pairwise distinct as
`FactorizationType`s. Signature per blueprint AMENDMENT 2026-08-15 §A-6 (defect D3 cured; it was
the placeholder `True`).

`DecidableEq FactorizationType` is `Classical.decEq` (`LocalData.lean`), so each goal is
transported along the `data` projection first — where `Multiset (ℕ × ℕ)` has a genuine decidable
equality — exactly as the blueprint's PROOF line prescribes. -/
theorem c3_pairwise_ne :
    c3split ≠ c3linInert ∧ c3split ≠ c3inert ∧ c3split ≠ c3linRam ∧ c3split ≠ c3ram
      ∧ c3linInert ≠ c3inert ∧ c3linInert ≠ c3linRam ∧ c3linInert ≠ c3ram
      ∧ c3inert ≠ c3linRam ∧ c3inert ≠ c3ram
      ∧ c3linRam ≠ c3ram := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact mt (congrArg FactorizationType.data) (by decide)

section AxCheck
#print axioms Uniformity.Density.c3_degrees
#print axioms Uniformity.Density.c3_pairwise_ne
end AxCheck

end Uniformity.Density
