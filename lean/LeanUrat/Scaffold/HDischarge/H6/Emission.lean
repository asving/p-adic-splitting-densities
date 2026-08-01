/-
HDISCHARGE_H6 §4 Wave A — `H6/Emission.lean`: E-side accumulators (unit A1, MECH).
Statement transcribed VERBATIM from `lean/blueprints/HDISCHARGE_H6.md` §4 A1
(probe-verified 2026-08-05). Cures defect D-6 (the architect-ruling proposal the
III-H9 BLOCKED block requested); also the answer to `DictIII/CU2t.lean`'s
BLOCKED(III-S2)/(III-S3) records, which hit the same accE/accF carrier seam
(BP_III wave-5 resume record defers that mop-up to this lead).

Reading: `eAccE H = ∏ ν.e` over the node list; `eAccF H = f₀ · ∏ (sel g's)`
with f₀ := deg ψ̂₀ (the root residue factor) and each selection-carrying node
contributing its g (terminal `sel = none` contributes 1 via `Option.elim`).
Gate (CUC §9.2 k′ = 0 boundary): at `H.nodes = []` the pair reduces to
`(accE₀, accF₀) = (1, f₀)` by `simp` — the `example` below.

Definitional risk on record (blueprint §3.4, fold round 1 Codex finding 12):
the reconciliation of this f₀-included `eAccF` with the machine's
`accF = ∏ ν.g` through the root-datum split is unit B2's content, NOT assumed
here.
-/
import Mathlib
import LeanUrat.Scaffold.DictIII.CU2t
import LeanUrat.MovesU.DefsLedger

namespace LeanUrat.Scaffold.HDischarge.H6

open LeanUrat.Scaffold.DictIII
open LeanUrat.MovesU

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- H6-A1 — E-side ramification accumulator: `accE_{k′} = ∏_{ν ∈ nodes} ν.e`. -/
def eAccE (H : EHist p F) : ℕ := (H.nodes.map fun ν => ν.e).prod

/-- H6-A1 — E-side residue-degree accumulator:
`accF_{k′} = f₀ · ∏_{ν ∈ nodes} (sel g)`, f₀-included form (CUC §9.2). -/
def eAccF (H : EHist p F) : ℕ :=
  H.psi0.natDegree * (H.nodes.map fun ν => (ν.sel.elim 1 Prod.fst)).prod

/-- A1 gate: the CUC §9.2 k′ = 0 boundary `(accE₀, accF₀) = (1, f₀)`. -/
example (H : EHist p F) (h : H.nodes = []) :
    (eAccE H, eAccF H) = (1, H.psi0.natDegree) := by
  simp [eAccE, eAccF, h]

/-! ## Unit A2 — seam decidedness, repaired (cures D-7/D-8)

Statements transcribed VERBATIM from `lean/blueprints/HDISCHARGE_H6.md` §4 A2
(probe-verified 2026-08-05). NEW names alongside the landed `DecIrr`/`DecHen`
pair in `DictIII/CU2t.lean` — the fenced pair is UNTOUCHED.

Reading (displayed at A2): `H` is 𝐇° (the seam continuing part; all nodes
selection-carrying — enforced at consumption via
`TerminalEmission.reaches_continuing`, unit A6). -/

/-- H6-A2 — seam decidedness, τ-irr leg: 𝐇° is nonempty and its last node
carries a saturated selection `sel = some (g, 1)` (μ_last = 1). Repaired NEW
name alongside the landed `DecIrr` (cures D-7). -/
def DecIrrSeam (H : EHist p F) : Prop :=
  H.nodes ≠ [] ∧
    (H.nodes.getLast?.elim False fun ν => ∃ g, ν.sel = some (g, 1))

/-- H6-A2 — seam decidedness, τ-hen leg: the base read — 𝐇° has no nodes, and
either `a₀ = 1` (Hensel booking) or the level-0 read has a slope-−∞ side.
Repaired NEW name alongside the landed `DecHen` (cures D-8). -/
def DecHenSeam (f : Polynomial ℤ_[p]) (H : EHist p F)
    (D : GMNData f (Theta H)) : Prop :=
  H.nodes = [] ∧
    (H.a0 = 1 ∨ ∃ S ∈ D.principalSides 0, S.isNegInfty = true)

/-- H6-A2 — seam decidedness, disjunction: a DEC seam is a τ-irr or a τ-hen
configuration. -/
def DecSeam (f : Polynomial ℤ_[p]) (H : EHist p F)
    (D : GMNData f (Theta H)) : Prop :=
  DecIrrSeam H ∨ DecHenSeam f H D

/-- H6-A3 — the deep exact-key corner (CUC §9.4 (T-DEC-cor) shape): the seam is
nonempty, its last node carries an exact selection key `some (g, μ)` with `2 ≤ μ`,
and the polygon read at index `H.nodes.length` exhibits a slope-−∞ side.

LEVEL CONVENTION (displayed, per blueprint §4 A3): `D.principalSides i` at
0-indexed `i` = the paper's level-(i+1) read; `H.nodes.length = k′` ⇒ index `k′`
= level `k′+1` — the same convention as BP_III §1.9's `cu2t_readForcing`. -/
def DeepCorner (f : Polynomial ℤ_[p]) (H : EHist p F)
    (D : GMNData f (Theta H)) : Prop :=
  H.nodes ≠ [] ∧
    (H.nodes.getLast?.elim False fun ν => ∃ g μ, ν.sel = some (g, μ) ∧ 2 ≤ μ) ∧
    ∃ S ∈ D.principalSides H.nodes.length, S.isNegInfty = true

/-- H6-A6 (VERBATIM from `lean/blueprints/HDISCHARGE_H6.md` §4 unit A6): the
terminal-emission interface — the quantifier domain the CUC §9.4 rows need and
the BP_III display lacked (the root cause of defects D-1..D-4).

`emitsHen` = the verdict-pair-only machine-record booking channel — the fold
round 1 repair of Codex finding 1; see HDISCHARGE_H6 §3.1. -/
structure TerminalEmission (p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] where
  reaches : Polynomial ℤ_[p] → EHist p F → Prop
  emits : Polynomial ℤ_[p] → EHist p F → ENodeData → (ℕ × ℕ) → Prop
  emitsHen : Polynomial ℤ_[p] → EHist p F → (ℕ × ℕ) → Prop
  emits_terminal : ∀ f H ν EF, emits f H ν EF → ν.sel = none
  emits_reaches : ∀ f H ν EF, emits f H ν EF → reaches f H
  emitsHen_reaches : ∀ f H EF, emitsHen f H EF → reaches f H
  reaches_continuing : ∀ f H, reaches f H → ∀ ν ∈ H.nodes, ν.sel ≠ none

end LeanUrat.Scaffold.HDischarge.H6
