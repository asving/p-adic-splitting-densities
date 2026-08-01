/-
BP_IV §1.6 — Step 18b, density = series (the squeeze) + the movement
capstone (`DensityTie.lean`).
Units in this file: SKEL (module skeleton, this unit).  Later waves add
D0a (`dmass` monotone), D0 (`cylDensity`), D1 (`dmass_eq_sliceSum`, cast of
the PROVED corpus `TreeSeam.finiteness_stack`), D2 (`sum_cylDensity_eq_one`),
D3 (`cylDensity_eq_seriesSum`), D5 (`renewal_unique_of_margin`), and D4
(`valueSide_massTie`, the movement CAPSTONE).
Import graph (BP_IV §1.0/§4): this module imports the completed
`SeriesTie.lean`; `SeriesTie.lean` never imports this module.
-/
import Mathlib
import LeanUrat.Scaffold.ValueSide.SeriesTie

/-!
# Density = series + the value-side capstone [BP_IV division, unit SKEL]

**PROVENANCE (unit SKEL; BP_IV §1.6, module map §0).**

* Blueprint: `lean/blueprints/BP_IV.md` §1.6 (statement layer) and §0
  (module map row `DensityTie.lean` | step 18b | "squeeze +
  `valueSide_massTie`").
* Math source of record: the D-11 second tranche (MASS-ID M2, monic scope),
  per BP_IV §0 step-18b row.
* Imports: `Mathlib` + `LeanUrat.Scaffold.ValueSide.SeriesTie` (the §1.0
  acyclicity edge: DensityTie imports SeriesTie, never conversely;
  `BridgeKernels`/`DefsLedger` corpus vocabulary arrives transitively).
-/

namespace LeanUrat.Scaffold

end LeanUrat.Scaffold
