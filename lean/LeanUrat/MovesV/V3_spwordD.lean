/-  MovesV unit V3-3d `spword_faithful` · HARD — the Codex-6 reconstruction
    bridge (the corpus's pre-declared E-phase RISK; escalation hatch at §2.D).
    ROSTER (3): readFits_unique, writeHeights_total (+ the TOTAL writeHeights),
    spWord_faithful. -/
import LeanUrat.MovesV.V3_spwordA

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem readFits_unique (n : ℕ) (P : MovesD.ShapePrefix)
    (s : MovesSp.Species) (hslot uslot : ℕ) (R R' : MovesD.ShapeRead)
    (h : ReadFits n P s hslot uslot R) (h' : ReadFits n P s hslot uslot R') :
    R = R' := by
  sorry

theorem writeHeights_total {n : ℕ} (εT : EntTemplate n) (h : Hpt εT.entDim) :
    (writeHeights? εT h).isSome := by
  sorry

/-- the TOTAL instantiation map — the token every V3–V7 statement uses. -/
noncomputable def writeHeights {n : ℕ} (εT : EntTemplate n)
    (h : Hpt εT.entDim) : EntShapeV n :=
  (writeHeights? εT h).get (writeHeights_total εT h)

/-- SP.1 genuinely forgets ONLY heights: equal species words + equal retained
height/u*-code slot data determine the WF prefix.  [E-PHASE FORM: stated at
the uncollapsed word + the (h, zig γ) slot lists — MANIFEST deviations.] -/
theorem spWord_faithful {n : ℕ} (P P' : MovesD.Shape n)
    (hw : spWord n (P : MovesD.ShapePrefix) = spWord n (P' : MovesD.ShapePrefix))
    (hs : (P : MovesD.ShapePrefix).reads.map (fun R => (R.h, zig R.gam))
        = (P' : MovesD.ShapePrefix).reads.map (fun R => (R.h, zig R.gam))) :
    P = P' := by
  sorry

end LeanUrat.MovesV
