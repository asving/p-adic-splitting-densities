/-
HDISCHARGE_H6 §4 Wave D — `H6/RowsK4.lean`: unit D1a (EASY) — THE SEMANTIC (H6)
CORE ROW. `EngineCovers` + `TerminalSeamCore` transcribed VERBATIM from
`lean/blueprints/HDISCHARGE_H6.md` §4 unit D1a (the ∃-WITH-COVERING form — fold
round 1 restructure per Codex finding 7 + the D1-keying recommendation: the
semantic row carries NO phantom keys; the K4 binder is a SEPARATE, explicitly
PROVISIONAL syntactic unblocker, unit D1b).

The first-draft ∀-over-EngineTied form was REFUTABLE (self-caught pre-review as
defect D-9; independently found as Codex finding 5 on the pre-patch text —
`EngineTied` deliberately leaves shape fields untied, and also admits
no-emission interfaces): the closed faithful form is EXISTENTIAL-WITH-COVERING.
The all-False emission fails covering wherever a realized seam exists — U31's
`gate_readsOf_inert2` anchors non-vacuity (the G2 gate consumes it);
adversarial junk emissions are not demanded to conform, only the WITNESS is.
Discharge shape: C0's TRM + waves B/C construct the witness — NOT this unit's
duty. `TerminalSeamCore` is a NAMED statement here (never an axiom, never
discharged by fiat).

Plus the RC tie lemma `rc_of_rows` (the §9.4 tie — the repaired III-S8):
emits + DecSeam + the A7 rows (tREAD + tVERD) + the A6 interface law
(`emits_terminal`) ⇒ `RCConsistentD`.

Deps: A7 (`TerminalSeamHypsE`, `H6/Emission.lean`), B0 (`EngineTied`,
`H6/EngineConform.lean`); corpus `machineEHist` (DictIII/CU1, the
certificate-free projected value — B0's FOOTPRINT RULE rides: `machineProj`
would inherit `sorryAx`), `MovesJ.ReadsOf` (HC2/Defs).
-/
import Mathlib
import LeanUrat.Scaffold.HDischarge.H6.EngineConform

namespace LeanUrat.Scaffold.HDischarge.H6

open LeanUrat.Scaffold.DictIII

/-- H6-D1a (VERBATIM from `lean/blueprints/HDISCHARGE_H6.md` §4 unit D1a):
the covering half of the semantic core row — every seam realized by a coherent,
`ReadsOf`-lawful machine history (projected certificate-free via `machineEHist`)
is reached by `E`. The all-False emission fails this wherever a realized seam
exists, which is exactly how the ∃-form escapes the D-9/finding-5 refutation
without demanding conformance of adversarial junk emissions. -/
def EngineCovers (n p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] (E : TerminalEmission p F) : Prop :=
  ∀ (f : Polynomial ℤ_[p]) (H : EHist p F),
    (∃ M : MovesC.History p F, MovesC.HistoryCoherent M ∧
      LeanUrat.MovesJ.ReadsOf p F n f M ∧
      (machineEHist M).continuingPart = H) →
    E.reaches f H

/-- H6-D1a (VERBATIM from `lean/blueprints/HDISCHARGE_H6.md` §4 unit D1a):
THE SEMANTIC (H6) CORE ROW — for every coefficient field there EXISTS a
terminal emission that is engine-tied (B0), covering (`EngineCovers`), and
satisfies the repaired CUC §9.4 row trio + tVERDhen (A7). NO phantom keys:
the K4-facing (X, FF)-keyed binder is unit D1b, a separate, explicitly
PROVISIONAL syntactic unblocker. Discharge shape (owed elsewhere): C0's TRM +
waves B/C construct the witness. -/
def TerminalSeamCore (n p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (F' : Type) [Field F'] [Finite F'],
    ∃ E : TerminalEmission p F',
      EngineTied n p F' E ∧ EngineCovers n p F' E ∧ TerminalSeamHypsE p F' E

/-- H6-D1a, the RC tie lemma (the §9.4 tie — the repaired III-S8; statement
shape displayed at `lean/blueprints/HDISCHARGE_H6.md` §4 unit D1a): at a
decided seam, under the standing antecedents (`ReadThroughIota` + `ConsF`),
any emission of an interface satisfying the A7 rows is `RCConsistentD` —
clause 1 (`sel = none`) is the A6 interface law `emits_terminal`, clause 2
(the NONEMPTY + ∀-SIDES read) is `tREAD`, clause 3 (the forced verdict) is
`tVERD`. -/
theorem rc_of_rows {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {E : TerminalEmission p F} (hrows : TerminalSeamHypsE p F E)
    {f : Polynomial ℤ_[p]} {H : EHist p F}
    {D : GMNData f (Theta H)} {R : GMNReader f (Theta H) D}
    {ν : ENodeData} {EF : ℕ × ℕ}
    (hread : ReadThroughIota f H D) (hcons : ConsF f H D R)
    (hemit : E.emits f H ν EF) (hdec : DecSeam f H D) :
    RCConsistentD f H D ν EF :=
  ⟨E.emits_terminal f H ν EF hemit,
    hrows.tREAD f H ν EF D R hread hcons hemit hdec,
    hrows.tVERD f H ν EF D R hread hcons hemit hdec⟩

end LeanUrat.Scaffold.HDischarge.H6
