/-
BP_IV §1.5 — Step 18, the resummation core + the tie assembly
(`SeriesTie.lean`).
Units in this file: SKEL (module skeleton, this unit).  Later waves add
S1a/S1b (Neumann sum + leastness), S0 (seriesSum = ⨆ of slice sums — located
HERE so this file never depends on `DensityTie.lean`), S2a/S2b
(`seriesSum_eq_lfp`), S3a/S3b (Bekić), S4a–S4c (margin/summability/solve
agreement), and S5 (`seriesTie_of_kernels`, targeting the corpus row
`BridgeKernels.series_tie`).
Import graph (BP_IV §1.0/§4): this module NEVER imports `DensityTie.lean`;
`DensityTie.lean` imports the completed `SeriesTie.lean`.
-/
import Mathlib
import LeanUrat.MovesU.BridgeKernels

/-!
# The resummation core + the series tie [BP_IV division, unit SKEL]

**PROVENANCE (unit SKEL; BP_IV §1.5, module map §0).**

* Blueprint: `lean/blueprints/BP_IV.md` §1.5 (statement layer) and §0
  (module map row `SeriesTie.lean` | step 18 | "resummation core +
  `seriesTie_of_kernels`").
* Math source of record: M04 (abstract resummation: lfp/Bekić/Neumann) +
  the O-11 r3 brief, per BP_IV §0 step-18 row.
* Imports: `Mathlib` + `LeanUrat.MovesU.BridgeKernels` (THE TARGET ROW
  `BridgeKernels.series_tie`, §3 corpus-reuse map; transitively supplies
  `FiberSeries`, `SolveSeam`, `TreeSeam` from `DefsLedger`).
-/

namespace LeanUrat.Scaffold

end LeanUrat.Scaffold
