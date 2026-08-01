/-
BP_IV §1.2 — Step 14, the (ADM)-FULL and level-1 census layers (`Census.lean`).
Units in this file: SKEL (module skeleton) · C3 (the `Decidable (ADMFull D)`
instance).  Later waves add
C1 (`admFull_of_r_eq_zero`), C2a/C2 (`r1Bound` + `admFull_r1_iff`),
C4a/C4b/C4c (`Stratum1` / vertex-chain telescope / `censusW` + `census_r0_law`),
C6, C7, and the wave-4 HARD units C5/C5′ (CEN-W r ≥ 1 / CEN-J).
Import graph (BP_IV §1.0): `CensusCore → Hyps` and `{CensusCore, Hyps} →
Census`, never a cycle — this module imports both and is imported by no
value-side module.
-/
import Mathlib
import LeanUrat.Scaffold.ValueSide.CensusCore
import LeanUrat.Scaffold.ValueSide.Hyps

/-!
# The order-r census layers [BP_IV division, unit SKEL]

**PROVENANCE (unit SKEL; BP_IV §1.2, module map §0).**

* Blueprint: `lean/blueprints/BP_IV.md` §1.2 (statement layer) and §0
  (module map row `Census.lean` | step 14 | "imports `CensusCore.lean` and
  `Hyps.lean`; proves the (ADM)-FULL and level-1 census layers").
* Math source of record: `O9_phaseB_verifybrief_rev5.md` + M08
  (`M08-cl6-general_fable.md` §2), per BP_IV §0 step-14 row.
* Imports: `Mathlib` + the two value-side roots (`CensusCore`, `Hyps`).
-/

namespace LeanUrat.Scaffold

/-!
**PROVENANCE (unit C3; BP_IV §1.2, unit table §2 row C3).**

* Blueprint: `lean/blueprints/BP_IV.md` §1.2 (statement transcribed VERBATIM;
  unit-table row C3 "Finset.decidableBAll over onLineSlots").
* Math source of record: ROOT §3.1, the (ADM) row's "per-datum DECIDABLE"
  clause ("finite lattice check").
* Deps: C0 (the `CensusData` carriers, `CensusCore.lean`) and H1 (`ADMFull`,
  `CensusCore.lean`).
* Mechanism: `ADMFull D` is a one-field structure over the bounded-∀
  proposition `∀ β ∈ D.onLineSlots, D.attainDim β = D.d`; `decidable_of_iff`
  transports the `Finset.decidableBAll` instance on that proposition across
  the (constructor ↔ field) equivalence.  `noncomputable` because `wt` (hence
  `onLineSlots`/`attainDim`) is declared `noncomputable` upstream per the
  blueprint's verbatim signatures — the decidability is at type level, exactly
  as the C3 docstring states; no `Classical.dec` is used.
-/

/-- C3: (ADM)-FULL is per-datum decidable — the ROOT §3.1 row's "finite lattice
    check" clause, machine-checked at type level. -/
noncomputable instance : ∀ D : CensusData, Decidable (ADMFull D) := fun D =>
  decidable_of_iff (∀ β ∈ D.onLineSlots, D.attainDim β = D.d)
    ⟨fun h => ⟨h⟩, fun h => h.full_attained⟩

end LeanUrat.Scaffold
