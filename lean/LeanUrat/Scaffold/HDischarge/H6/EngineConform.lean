/-
HDISCHARGE_H6 §4 Wave B — `H6/EngineConform.lean`: unit B0 (EASY, statement-only).
Statement transcribed VERBATIM from `lean/blueprints/HDISCHARGE_H6.md` §4 B0.

Engine-tie canonicity: what "the engine's emission" means — every reached seam
and every emitted irr verdict is realized by a coherent machine history M that
is a classifier run on f (`MovesJ.ReadsOf`) whose projected 𝔈-history's
continuing part is the seam. Deliberately does NOT tie ν's shape fields —
(T-READ)'s machine home is owed (blueprint §3.3(a)); the C0 upgrade is where
tREAD becomes provable.

FOOTPRINT RULE (blueprint §4 B0): binds `machineEHist` (CU1's certificate-free
projected value, = `machineProj_val`), NOT `machineProj` — the latter bundles
the `EWF` certificate whose W3 row is CU1's one recorded honest sorry, so any
statement binding it would inherit `sorryAx`. Coherence rides as the explicit
`MovesC.HistoryCoherent M` conjunct instead.

Deps: A2 (`DecIrrSeam`), A6 (`TerminalEmission`) in `H6/Emission.lean`;
corpus `machineEHist` (DictIII/CU1), `MovesJ.ReadsOf` (HC2/Defs),
`MovesT.IrrHalts`/`accE`/`accF` (MovesT/Defs).
-/
import Mathlib
import LeanUrat.Scaffold.DictIII.CU1
import LeanUrat.Scaffold.HDischarge.H6.Emission

namespace LeanUrat.Scaffold.HDischarge.H6

open LeanUrat.Scaffold.DictIII

/-- H6-B0 (VERBATIM from `lean/blueprints/HDISCHARGE_H6.md` §4 unit B0):
engine-tie canonicity. `reaches_engine`: every reached seam is the continuing
part of a coherent, `ReadsOf`-lawful machine history's projection.
`emits_irr_verdict`: every emitted verdict pair at a decided irr seam is THE
machine accumulator pair `(accE M, accF M)` of an `IrrHalts` run realizing the
seam. Shape fields of ν are NOT tied here (§3.3(a) — owed at C0). -/
structure EngineTied (n p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] (E : TerminalEmission p F) : Prop where
  reaches_engine : ∀ f H, E.reaches f H →
    ∃ M : MovesC.History p F, MovesC.HistoryCoherent M ∧
      LeanUrat.MovesJ.ReadsOf p F n f M ∧
      (machineEHist M).continuingPart = H
  emits_irr_verdict : ∀ f H ν EF, E.emits f H ν EF → DecIrrSeam H →
    ∃ M : MovesC.History p F, MovesC.HistoryCoherent M ∧
      LeanUrat.MovesJ.ReadsOf p F n f M ∧
      (machineEHist M).continuingPart = H ∧
      MovesT.IrrHalts M ∧
      EF = (MovesT.accE M, MovesT.accF M)

end LeanUrat.Scaffold.HDischarge.H6
