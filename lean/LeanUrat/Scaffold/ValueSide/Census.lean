/-
BP_IV §1.2 — Step 14, the (ADM)-FULL and level-1 census layers (`Census.lean`).
Units in this file: SKEL (module skeleton, this unit).  Later waves add
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

end LeanUrat.Scaffold
