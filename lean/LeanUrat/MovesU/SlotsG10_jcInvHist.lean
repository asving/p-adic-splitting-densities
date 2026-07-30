/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-!
# IB-G10 — `Slot_jcInvHist` (bridge campaign BP1, cluster c12; E-phase statement unit)

Blueprint: `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.8 (row `jcInvHist`) +
§4 group G (IB-G10); adjudications: `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`
(BP1 Q5: proceed NOW, statement-only, Codex audit before any consumer).

THE SLOT (U10_theoremU.lean docstring lines 84–85): `jcInvHist` — "CL-19's
h_ent/history-invariance residue beyond the typed `cl19_rep` face" (owner [2b]).
CL-19's ledger display (MOVES_2026-07-24.md 13345–13361, (JC-INV)): "per read,
the JOINT digit-cell conditional law given the entrance (all cells of the read
jointly, branching cells INCLUDED — hence the branching-cell selection law) is
ONE function of the retained state — invariant across representatives and
admissible histories, h_ent included."

THE COMPLEMENT SPLIT (the G10 duty: no overlap, and the conjunction must equal
CL-19's display):
* `CapstoneLedger.cl19_rep` (DefsLedger.lean:802) is the REPRESENTATIVE face,
  over the MovesS measured carrier: `μcell e τ x c q₀` is one function of the
  retained state τ across representatives x, x' : `C.MS.Rep e τ`.
* THIS slot is the HISTORY face, over MovesT entrance vocabulary (`EntSt`,
  `MovesC.History`): the joint digit-cell conditional law given a HISTORY
  entrance is invariant across admissible histories retaining the same state,
  entrance heights (h_ent) INCLUDED.  It never mentions `μcell`/`Rep` — no
  overlap.  CONJUNCTION CAVEAT (recorded for the Codex audit): the two faces
  transcribe CL-19's single display on the two sides of the tree/classifier
  seam; reading their conjunction AS the display goes through the carried
  `UInstance.Tpin`/`sibjc` identification of the two cell vocabularies — the
  seam is Tpin's row, not this slot's content.

DEPS: none (built MovesT/MovesC/MovesD vocabulary only).

RECORDED RESOLUTIONS (minimal, against the as-built corpus):
* (r1) "the joint digit-cell conditional law given the entrance" is rendered
  DIVISION-FREE by cross-multiplied cardinalities of the built joint-cell
  fibers: `cellEventE T CA χ es c` (the entrance-keyed joint read `CA.cellOf es`
  restricted to the entrance event) against `entEvent T χ es` — the corpus's
  division-free counting-law style (`CtsMeasured.ent_card`,
  `TreeSeam.count_tie`).  Branching cells are INCLUDED because `CA.cellOf` is
  the FULL joint read (its fibers refine every branch stratum —
  `CellData.branch_cell_joint`).
* (r2) "the retained state" is the L3-dictionary retained roster of the
  entrance history's LAST node (`MovesT.readOf`'s components,
  MovesT/Defs.lean:268) with the HEIGHT-AXIS DATA ERASED — h, ustar, gam are
  excluded (that is exactly "h_ent included"); the Bézout pair (s, t) is a
  function of (e, h) (`Node.hbezCanon`) and is excluded with h; the recorded
  frame data (σ, zbar, center, lift, ψ, pat, Ranch, line) enter only through
  the residue-weight source `Nat.card ↥ν.σ.K` (readOf's `w`).  RETAINED KEY :=
  (species, e, g, μ, a, s0, wSide, Dwidth, card σ.K) — `NodeRetainedKeyEq`
  below.  FLAGGED for the formulation audit: this roster is the load-bearing
  resolution of an ambiguous sketch (ADJ→H unit); a wrong roster is a
  faithfulness/falsifier failure, never a silent one.
* (r3) "admissible histories" is resolved as REALIZEDNESS in the pinned model
  (nonempty entrance events).  The stronger keying (H, H' chains of a carried
  canonical `MovesT.VTree`) is recorded as the alternative the adjudicator may
  substitute; realizedness is the weaker guard, hence the STRONGER slot.

STATEMENT-FENCE FLAG: a NEW named Prop (wave-D discharges it by proof or
carries it visibly); per Q5 it gates nothing on the construction path and must
pass the Codex formulation audit + the IB-G11c falsifier before any consumer
lands.  Non-vacuity duty: IB-G11c.  Closure manifest: IB-G12.
-/

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesU

/-- THE RETAINED-STATE KEY (resolution (r2)): equality of the L3-dictionary
    retained components of two nodes, HEIGHT-AXIS DATA ERASED — h, ustar, gam
    (and the (e,h)-determined Bézout pair) do NOT key, so key-equal entrances at
    DIFFERENT entrance heights fall under the invariance ("h_ent included").
    The σ-recorded frame data key only through the residue-weight source
    `Nat.card ↥σ.K` (`MovesT.readOf`'s `w` component, junk-guard-free form). -/
def NodeRetainedKeyEq {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (ν ν' : MovesC.Node p F) : Prop :=
  ν.species = ν'.species ∧ ν.e = ν'.e ∧ ν.g = ν'.g ∧ ν.μ = ν'.μ ∧
    ν.a = ν'.a ∧ ν.s0 = ν'.s0 ∧ ν.wSide = ν'.wSide ∧ ν.Dwidth = ν'.Dwidth ∧
    Nat.card ↥ν.σ.K = Nat.card ↥ν'.σ.K

/-- IB-G10 / CL-19 residue (`theoremU`'s `jcInvHist` parameter): HISTORY
    INVARIANCE of the joint digit-cell conditional law.  In every level-N tree
    model with joint-cell data: for two REALIZED history entrances (resolution
    (r3)) whose retained states agree (`NodeRetainedKeyEq` of the last nodes —
    h_ent erased, resolution (r2)), the joint digit-cell conditional law given
    the entrance is EQUAL, division-free (resolution (r1)): for every joint
    cell c,  |Ψ⁻¹(c) ∩ Σ| · |Σ'| = |Ψ'⁻¹(c) ∩ Σ'| · |Σ|  where Σ, Σ' are the
    two entrance events and Ψ, Ψ' the two entrance-keyed joint reads.  The
    representative face is `cl19_rep` (DefsLedger.lean:802) — disjoint by
    construction; conjunction duty recorded in the file header. -/
def Slot_jcInvHist (n : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∀ (N m : ℕ) (pol : MovesD.CanonPolicy p (ZMod p))
    (T : MovesD.TreeModel p (ZMod p) n N m pol)
    (CA : MovesT.CellData p (ZMod p) n N m pol T)
    (χ : Fin n → Fin m) (H H' : MovesC.History p (ZMod p)),
    (MovesT.entEvent T χ (MovesT.EntSt.st H)).Nonempty →
    (MovesT.entEvent T χ (MovesT.EntSt.st H')).Nonempty →
    NodeRetainedKeyEq H.lastNode H'.lastNode →
    ∀ c : CA.Cell,
      Nat.card ↥(MovesT.cellEventE T CA χ (MovesT.EntSt.st H) c)
          * Nat.card ↥(MovesT.entEvent T χ (MovesT.EntSt.st H'))
        = Nat.card ↥(MovesT.cellEventE T CA χ (MovesT.EntSt.st H') c)
          * Nat.card ↥(MovesT.entEvent T χ (MovesT.EntSt.st H))

end LeanUrat.MovesU
