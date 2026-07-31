/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesS.Defs

/-!
# IB-B18 — the VerdictDeg / DegConsDelta additive sibling laws (queue item 9(ii)+(iii))

SIGN-OFF QUEUE ITEM 9(ii)+(iii), EXECUTED (2026-07-31; grant recorded at
`notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` §ASVIN SIGN-OFF; form adjudicated by
the item-9 note read, work-record wf_b933dcd7-877, ledger lines 98–105).

THE NOTE WARRANT (VP-1, §T-ASSEMBLY / MOVES 7061–7063 via
`MOVEST_LEAN_BLUEPRINT_2026-07-28.md` §2.1 and `ASSEMBLY_PLAN_2026-07-26.md`
VP): "a τ-halted leaf of a degree-d cluster carries v with Σ_{(E,F) ∈ v} E·F
= d" — the displayed equality sum E·F = d.  In the §S-RESUM roster vocabulary
(`MovesS.TableShape`): a halted member μ of an outcome (status `Sum.inl v`)
carries ONE verdict type v with `vdeg v = E·F` through the R20 structural pin
`vEquiv`/`vdeg_spec`; the member's cluster degree is its `size`, δ-weighted by
the base-change factor `μ.δ` (CONVENTION DELTA-ABS, `Member`'s docstring).

WHY THESE LAWS EXIST (the compiled evidence, `BridgeB15a_r2Neg.lean`): the
IB-B15a countermodel's two RECORDED CHEATS are exactly the two missing laws —
(1) the t₂ exit carries the degree-2 verdict (1,2) on a SIZE-1 member ("NO
carried law ties a halted member's verdict degree to its size — `DegCons`
constrains sizes only"); (2) the block-2 split outcome's δ-weighted size sum
1·1 + 1·2 = 3 exceeds e = 2, invisible to the as-built `DegCons.size_sum`
(the reader's SECOND independent cheat, ledger item 9(iii)).  Both cheats are
EXCLUDED by the two Props below; `cmT` is their compiled violation witness
(`BridgeVerdictDegGate.lean`).  NOTE the adjudicated scope limit (item 9(i)):
the degree law alone CANNOT rescue the unsplit (r2) statement (per-component
poles at same-degree distinct verdicts survive at n ≥ 3), so these laws are
ADDITIVE — they gate nothing in IB-B15a's re-scoped statements.

DESIGN (boundary-safe, per the adjudication): NEW additive SIBLING Props of
`MovesS.DegCons` — new file, no field on any frozen structure (`DegCons`,
`UCarriers`, `TableShape` untouched; every existing instance, including the
adversarial `cmT`, remains legal).  Threading = the gate file's compiled
witnesses + the IB-B16 record update (BridgeRosterPins.lean) + the r2Neg
dated note; consumers adopt them as NAMED HYPOTHESIS ROWS (the hdom-row
genre), never as trivial fills.

OPEN-DISPOSITION RESOLUTION (halted δ > 1; ledger flag "note silent"): the
note read record wf_b933dcd7-877 is a work-record id, NOT a notes/ file
(verified by repo grep, 2026-07-31), so per the assignment's silence rule the
WEAKER law lands: `vdeg v = μ.size * μ.δ` (the δ-weighted equality).  It is
strictly weaker than the alternative package (halted ⇒ δ = 1, plus
vdeg = size): that package implies this law, not conversely, and this form is
TRUE in BOTH candidate worlds (if halted members always have δ = 1 it reduces
to the sketch's `vdeg v = μ.size`; if they can carry δ > 1 it reads the
member's ABSOLUTE degree per DELTA-ABS).  Adding `halted ⇒ δ = 1` would
constrain tables beyond what the silent note warrants.  GUARD DECISION (same
silence rule): both laws carry the `e ∈ Finset.Icc 1 n` guard, mirroring
`DegCons.size_sum` — VP-1 speaks of realized clusters (1 ≤ e ≤ n); a law over
the Lean-artifact padding rows is beyond the note.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

/-- IB-B18 (item 9(ii)): THE VERDICT-DEGREE LAW — VP-1's displayed equality
    Σ_{(E,F) ∈ v} E·F = d read at the single-verdict roster member: every
    HALTED member's verdict degree equals its δ-weighted size (the weaker
    halted-δ disposition; see the file header).  Additive sibling of
    `MovesS.DegCons`; a NAMED hypothesis row for consumers, never a field. -/
structure VerdictDeg {n : ℕ} (T : MovesS.TableShape n) : Prop where
  vdeg_size : ∀ e ∈ Finset.Icc 1 n, ∀ (τ : T.State e) (o : T.Out e τ),
    ∀ μ ∈ (T.odata e τ o).mem, ∀ v : T.VType,
      μ.status = Sum.inl v → (T.vdeg v : ℕ) = μ.size * (μ.δ : ℕ)

/-- IB-B18 (item 9(iii)): THE δ-WEIGHTED DEG-CONS STRENGTHENING — the
    outcome's members' δ-weighted sizes sum to at most the block degree.
    Strictly stronger than `DegCons.size_sum` (see `DegConsDelta.size_sum`
    below); kills the reader's second recorded cheat (1·1 + 1·2 = 3 > 2 at
    the countermodel's split outcome). -/
structure DegConsDelta {n : ℕ} (T : MovesS.TableShape n) : Prop where
  size_sum_delta : ∀ e ∈ Finset.Icc 1 n, ∀ (τ : T.State e) (o : T.Out e τ),
    ((T.odata e τ o).mem.map fun μ => μ.size * (μ.δ : ℕ)).sum ≤ e

/-- VP-1's displayed equality, in the (E, F) coordinates of the R20 structural
    pin: for a halted member, E·F = size·δ (through `vdeg_spec`). -/
theorem VerdictDeg.EF_eq {n : ℕ} {T : MovesS.TableShape n} (h : VerdictDeg T)
    {e : ℕ} (he : e ∈ Finset.Icc 1 n) (τ : T.State e) (o : T.Out e τ)
    {μ : MovesS.Member T.VType T.State} (hμ : μ ∈ (T.odata e τ o).mem)
    {v : T.VType} (hv : μ.status = Sum.inl v) :
    ((T.vEquiv v).1.1 : ℕ) * ((T.vEquiv v).1.2 : ℕ) = μ.size * (μ.δ : ℕ) :=
  (T.vdeg_spec v).symm.trans (h.vdeg_size e he τ o μ hμ v hv)

/-- The strengthening display: `DegConsDelta` implies `DegCons.size_sum`'s
    sentence (member sizes are ≥ their unweighted selves under δ ≥ 1), so the
    new law strictly refines the carried one — never a competing fork. -/
theorem DegConsDelta.size_sum {n : ℕ} {T : MovesS.TableShape n}
    (h : DegConsDelta T) :
    ∀ e ∈ Finset.Icc 1 n, ∀ (τ : T.State e) (o : T.Out e τ),
      ((T.odata e τ o).mem.map MovesS.Member.size).sum ≤ e := fun e he τ o =>
  le_trans
    (List.sum_le_sum fun μ _ => Nat.le_mul_of_pos_right μ.size μ.δ.pos)
    (h.size_sum_delta e he τ o)

end LeanUrat.MovesU
