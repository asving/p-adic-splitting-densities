/-
BP_IV §1.1 — Step 13, the drainage-transfer layer (`Transfer.lean`).
Units in this file: SKEL (module skeleton, this unit).  Later waves add
T0 (`card_boxProj_fiber`), T1 (`env_antitone`), T2 (FLOOR), T3 (TR-Q skeleton),
T4a/T4 (`discV` + `DrainageImports`), T5, T6 (`env_tendsto_zero_of_imports`),
and the wave-4 HARD constructors T7 (CEIL) and T8 (tail).
Import graph (BP_IV §0/§1.0): no value-side module is imported here; the
counting vocabulary (`ClassifierSpec.decided/undec/env/dmass`, `Box`,
`boxProj`, `canonical_stable`) is reused BY IMPORT from the corpus
(`LeanUrat/MovesU/Defs.lean`), never redefined.
-/
import Mathlib
import LeanUrat.MovesU.Defs

/-!
# The abstract drainage-transfer layer [BP_IV division, unit SKEL]

**PROVENANCE (unit SKEL; BP_IV §1.1, module map §0).**

* Blueprint: `lean/blueprints/BP_IV.md` §1.1 (statement layer) and §0
  (module map row `Transfer.lean` | step 13 | "abstract drainage transfer
  over `ClassifierSpec`").
* Math source of record: the O4T brief (drainage transfer; M05 core), per
  BP_IV §0 step-13 row.
* Imports: `Mathlib` + `LeanUrat.MovesU.Defs` (corpus `ClassifierSpec`
  vocabulary, §3 corpus-reuse map). No value-side module.
-/

namespace LeanUrat.Scaffold

end LeanUrat.Scaffold
