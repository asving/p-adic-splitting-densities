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

/-! ## Unit B1 — the canonical site/verdict emission `engineEmissionSV`

Relational body transcribed VERBATIM from `lean/blueprints/HDISCHARGE_H6.md` §4
unit B1 (the EXACT displayed body — fold round 1, Codex finding 10: probe
GREEN). The four interface laws are proved below the `where`; the engine tie is
`engineEmissionSV_engineTied`.

HONESTY DISPLAY (blueprint §4 B1, unchanged in substance): ν's SHAPE fields are
UNCONSTRAINED in this SV body — every `sel = none` ν is admitted at a decided
irr seam. Consequences, displayed: `tREAD` at `engineEmissionSV` is REFUTABLE
(junk shapes) — the trio is NOT claimed at SV; SV exists to discharge
tDECdec/tDECcor/tVERD-shaped work early. The C0 upgrade `engineEmission`
(ν := the TRM record) is where tREAD becomes provable. -/

/-- H6-B1 (body VERBATIM from `lean/blueprints/HDISCHARGE_H6.md` §4 unit B1):
the canonical site/verdict emission. `reaches` = realization by a coherent
`ReadsOf`-lawful machine history projecting (certificate-free, via
`machineEHist`) onto the seam; `emits` = the sel-none ν admission at a decided
irr seam realized by an `IrrHalts` run whose accumulator pair is the verdict;
`emitsHen` = the base-seam machine-record booking channel at `(1, f₀)`.
Shape fields of ν are deliberately NOT constrained (see the honesty display
in the section header). -/
noncomputable def engineEmissionSV (n p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] : TerminalEmission p F where
  reaches f H := ∃ M : MovesC.History p F, MovesC.HistoryCoherent M ∧
      LeanUrat.MovesJ.ReadsOf p F n f M ∧ (machineEHist M).continuingPart = H
  emits f H ν EF := ν.sel = none ∧ DecIrrSeam H ∧
      (∀ ν' ∈ H.nodes, ν'.sel ≠ none) ∧
      ∃ M : MovesC.History p F, MovesC.HistoryCoherent M ∧
        LeanUrat.MovesJ.ReadsOf p F n f M ∧
        (machineEHist M).continuingPart = H ∧
        MovesT.IrrHalts M ∧ EF = (MovesT.accE M, MovesT.accF M)
  emitsHen f H EF := H.nodes = [] ∧ EF = (1, H.psi0.natDegree) ∧
      ∃ M : MovesC.History p F, MovesC.HistoryCoherent M ∧
        LeanUrat.MovesJ.ReadsOf p F n f M ∧
        (machineEHist M).continuingPart = H
  emits_terminal := fun _ _ _ _ h => h.1
  emits_reaches := fun _ _ _ _ h => by
    obtain ⟨-, -, -, M, hcoh, hread, hpart, -, -⟩ := h
    exact ⟨M, hcoh, hread, hpart⟩
  emitsHen_reaches := fun _ _ _ h => h.2.2
  reaches_continuing := fun _ H h ν hν => by
    obtain ⟨M, -, -, rfl⟩ := h
    have hmem : ν ∈ (machineEHist M).nodes.takeWhile
        (fun ν' => ν'.sel.isSome) := hν
    have hsome := List.mem_takeWhile_imp
      (p := fun ν' : ENodeData => ν'.sel.isSome) hmem
    exact Option.isSome_iff_ne_none.mp hsome

/-- H6-B1: the canonical emission IS engine-tied — `reaches` and `emits` are
definitionally the realization clauses `EngineTied` demands (the `emits` case
projects away the sel-none/decidedness/continuing conjuncts). -/
theorem engineEmissionSV_engineTied (n p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] :
    EngineTied n p F (engineEmissionSV n p F) where
  reaches_engine := fun _ _ h => h
  emits_irr_verdict := fun _ _ _ _ h _ => h.2.2.2

end LeanUrat.Scaffold.HDischarge.H6
