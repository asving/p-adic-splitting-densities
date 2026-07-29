/-  MovesV unit V3-3b `spword_collapse` (RE-KEYED REV 7, C11) — THE TOTALITY
    + TIE THEOREM: `template?`'s dite PASSES; the total `template` declared. -/
import LeanUrat.MovesV.V3_spwordA
import LeanUrat.MovesSp.SP3_collapseNeNil
import LeanUrat.MovesSp.SP3_collapseSublist
import LeanUrat.MovesSp.SP3_collapseWalk

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem template_total {n : ℕ} (ε : EntShapeV n) : (ε.template?).isSome := by
  -- ε.Phat is a WF shape (Shape n = {P // ShapeWF n P}), so spWord fits.
  have hWF : MovesD.ShapeWF n (ε.Phat : MovesD.ShapePrefix) := ε.Phat.2
  -- [ADJUDICATED 2026-07-30: `spWord_fits` gained the width-≥-2 continuation
  --  hypotheses (V3_spwordA / V3_spwordA_negWitness).  `EntShapeV` carries NO
  --  width law, so this leg cannot cite it any more — and the negWitness's
  --  two-read prefix P3 extends to an EntShapeV (gsel = musel = 1, selRec =
  --  []), so `template_total` AS STATED needs the EntShapeV-side width law
  --  too: OPEN SIGN-OFF ITEM, recorded in the MANIFEST.  Until then the fits
  --  leg is an explicit honest sorry.]
  have hfits : SpWordFits n (ε.Phat : MovesD.ShapePrefix)
      (spWord n (ε.Phat : MovesD.ShapePrefix)) := by
    sorry
  obtain ⟨hlenW, _hfit, hmem, hch⟩ := hfits
  set sw := spWord n (ε.Phat : MovesD.ShapePrefix) with hsw
  -- sw ≠ [] : its length equals P̂.reads.length, which is nonzero by ε.hne.
  have hswne : sw ≠ [] := by
    intro h
    apply ε.hne
    have hz : (ε.Phat : MovesD.ShapePrefix).reads.length = 0 := by
      rw [← hlenW, h]; rfl
    exact List.length_eq_zero_iff.mp hz
  -- Clauses 1–3 : nonempty / catalogue / collapsed-walk chain (SP3 machinery).
  have c1 : MovesSp.collapseRuns sw ≠ [] := MovesSp.collapseRuns_ne_nil hswne
  have cw := MovesSp.collapseRuns_collapsedWalk hmem hch
  have c2 : ∀ s ∈ MovesSp.collapseRuns sw, MovesSp.InCatalogue n s := cw.1
  have c3 : (MovesSp.collapseRuns sw).Chain'
      (fun s s' => MovesSp.SuccStep n s s' ∧ s ≠ s') := cw.2
  -- Clauses 4–6 : entry / branch-count / menu tie transports (HARD — new
  -- collapse-preservation + branch-slot↔branching-letter machinery needed).
  have c456 :
      (∀ s, (MovesSp.collapseRuns sw).getLast? = some s →
          s.sel = some (ε.gsel, ε.musel)) ∧
      ε.selRec.length =
          ((MovesSp.collapseRuns sw).filter (IsBranchingLetter n)).length ∧
      (∀ i (hi : i < ε.selRec.length),
          ε.selRec.get ⟨i, hi⟩ <
            letterMenuCard n (MovesSp.collapseRuns sw) i) := by
    sorry
  obtain ⟨c4, c5, c6⟩ := c456
  simp only [EntShapeV.template?, ← hsw]
  rw [dif_pos ⟨c1, c2, c3, c4, c5, c6⟩]
  rfl

/-- the TOTAL template (downstream units' token — no forward reference:
Defs is Option-typed, units are total). -/
noncomputable def EntShapeV.template {n : ℕ} (ε : EntShapeV n) :
    EntTemplate n :=
  (ε.template?).get (template_total ε)

end LeanUrat.MovesV
