/-  MovesV unit V3-5b `inst_bij_surj` — SURJECTIVITY onto the realizable
    concrete ε with template ε̊, GIVEN the entrance exactness face (XHDdEnt);
    SCOPED SELF-LOOP-FREE (ADJ-3, 2026-07-31).

    STATEMENT REPAIR (adjudicated; Codex-confirmed mechanism — the depth-slot
    zip truncation, quoted in full in `V3_instbijA.lean`'s header): the
    unscoped surjectivity is NOT ONTO on self-loop templates — once any
    self-loop depth ≥ 1, `shapeOfSlots?`'s zip truncates past `word.length`,
    so no slot point can write a shape whose expanded run exceeds the
    pair-slot budget; concrete realizable ε over such templates have no
    preimage.  Ledger warrant (LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md,
    wave-A record): "instbij self-loop-free scoping (the depth-slot zip
    truncation, Codex-confirmed)" — "MIRRORS the capstone's order-0
    perimeter."  Scope hypothesis: `εT.word.filter (SelfLoopLetter n) = []`
    (all depth slots vanish; the zip is exact — A's mechanism lemmas). -/
import LeanUrat.MovesV.V3_instbijA
import LeanUrat.MovesV.V3_tfin

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem inst_bij_surj {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (DE : XHDdEnt n S V)
    (εT : EntTemplate n) (hSLF : εT.word.filter (SelfLoopLetter n) = [])
    (β₀ : S.Cell) (ε : EntShapeV n)
    (hT : ε.template? = some εT) (hR : Realizable V ε β₀) :
    ∃ h : Hpt εT.entDim, (V.entDom εT).Mem h ∧ writeHeights εT h = ε := by
  -- The inverse construction: extract the height/depth slots from ε and show
  -- that writing them back into the template's slots recovers ε (template-
  -- matching through readOfLetter, uniqueness by V3-3d's readFits_unique).
  obtain ⟨h, hwh⟩ : ∃ h : Hpt εT.entDim, writeHeights εT h = ε := by
    -- [ADJ-3 RESIDUE, exact: the candidate point is the slot read-off
    --  h⟨2i⟩ := reads[i].h, h⟨2i+1⟩ := zig reads[i].gam (no depth slots by
    --  hSLF; entDim = 2·word.length).  What remains is the RECONSTRUCTION
    --  fold: (1) hT forces ∃ ws, SpWordFits n ε.Phat ws (else spWord = junk
    --  [] and template?'s dite fails), with εT.word = collapseRuns ws; under
    --  hSLF, collapseRuns ws = ws (collapse strikes only self-loop copies —
    --  V3-3b apparatus), so εT.word IS the fitting word, length = reads
    --  count; (2) per letter, ReadFits existence at the actual read R_i
    --  needs the SpFitsRead ↔ ReadFits clause bridge (w/Dwidth chaining +
    --  gamTie + aTie from ShapeWF; e/s0/species/monicTop from SpFitsRead;
    --  the wSide = wraw leg is the V3-3a WIDTH LAW seam) + readFits_unique
    --  (sel.isSome from SpFitsRead clause 5) to pin the fold's choice to
    --  R_i; (3) the WF+EntTiesAt dite passes from ε's own fields; EntShapeV
    --  ext closes.  Legs (1)-(2) are the V3-3d/spword-family dependency —
    --  ADJ-2 (the spwordD writeHeights_total admissible-domain rescope +
    --  spWord_faithful re-key) LANDED 2026-07-31: the scoped forms are
    --  proved (order-0 stratum; consumers ride the recorded shim
    --  writeHeights_total_unscoped), but the multi-letter leg-(1)/(2)
    --  bridge is Phase B, so this stays the honest open core of V3-5b.]
    sorry
  refine ⟨h, ?_, hwh⟩
  -- Membership: ε realizes the template at h (Realizable = hR), so the XHD-d
  -- entrance face's no_orphanE places h in the semilinear domain.
  apply DE.no_orphanE εT h β₀
  -- instRealizable εT h β₀ := ∃ ε' ∈ writeHeights? εT h, Realizable V ε' β₀.
  have hsome : writeHeights? εT h = some ε := by
    rw [← hwh]
    exact (Option.some_get (writeHeights_total_unscoped εT h)).symm
  exact ⟨ε, hsome, hR⟩

end LeanUrat.MovesV
