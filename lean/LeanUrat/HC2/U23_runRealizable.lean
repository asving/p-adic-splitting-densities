/-
Unit U23.readsOf_realizable  (HC-2 campaign, E-phase — blueprint §5 Layer D)
moves_ref: MovesC `Realizable` ("the FULL three-condition class").
deps: U20–U22, assembly over the per-step dichotomy (`s0+w < μ` | `= μ`; the `> μ` case
excluded by coherence's window containment).  difficulty: easy given U20–U22.
hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.HC2.Defs
import LeanUrat.HC2.U20_NA
import LeanUrat.HC2.U21_HV
import LeanUrat.HC2.U22_SAE

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- A classifier run is realizable — (NA)+(HV)+(SAE) at every appended read.

QUEUE ITEM 21 RE-POINT (2026-07-31, Asvin sign-off — U21's named-hypothesis hoist):
this assembly gains the matching named hypothesis row `hpin` (the `RunVertexPin`
residue at every recorded non-recentering transition — U21's certified-underivable
(HV) content, hoisted rather than sorried; see U21's header record) and threads it
into `readsOf_HV`. Discharge routes for `hpin` at concrete runs: the Wall A↔B seam
(HC1-constructed histories carry it by `v8Rc_S5'`/`VertexPin`).

⚠ VACUITY CAVEAT (2026-07-30 verify-2 fold-in; task #44 / A16+A39): this assembly
INHERITS the K1-kernel perimeter through U20 (NA) and U22 (SAE): the kernel's
non-recentering legs at `e·g ≥ 2` close via the V10 INCONSISTENCY finding (`ReadsOf`
admits NO such instances; the `HistoryCoherent` read-pair keying is a flagged
FAITHFULNESS BUG, pending sign-off task #44), so this theorem is currently VACUOUS
at that steep perimeter. Never cite it as machine-checked transport mathematics
there. -/
theorem readsOf_realizable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H)
    (hpin : ∀ (i : ℕ) (hi1 : i + 1 < H.nodes.length),
      (H.nodes[i]'(by omega : i < H.nodes.length)).species
          ≠ ReadSpecies.recentering →
      RunVertexPin (H.nodes[i]'(by omega)).σ (H.nodes[i+1]'hi1).σ
        (H.nodes[i+1]'hi1).σ.Φ (H.nodes[i]'(by omega)).zbar) : Realizable H := by
  -- `Realizable H` = at every appended read `ν_{i+1}`, `TransitionAdmissible ν_i ν_{i+1}`;
  -- `TransitionAdmissible` is the (NA)∧(HV)∧(SAE₁)∧(SAE₂) four-tuple.  Assemble it from
  -- U20 (NA), U21 (HV, through the hoisted pin), U22 (SAE, both conjuncts) over the
  -- standing pair (blueprint §5 D).
  intro i hi
  exact ⟨readsOf_NA h i hi, readsOf_HV h i hi (hpin i hi),
    (readsOf_SAE h i hi).1, (readsOf_SAE h i hi).2⟩

end LeanUrat.MovesJ
