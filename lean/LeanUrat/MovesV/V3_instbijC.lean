/-  MovesV unit V3-5c `inst_bij_eq` — THE ASSEMBLED EQUIV + computation law
    (incl. the zig/gamTie roundtrip check); SCOPED SELF-LOOP-FREE (ADJ-3,
    2026-07-31).

    STATEMENT REPAIR (adjudicated; Codex-confirmed mechanism — the depth-slot
    zip truncation, quoted in full in `V3_instbijA.lean`'s header): the
    assembled equiv consumes A (injectivity) and B (surjectivity), both FALSE/
    not-onto unscoped on self-loop templates, so the equiv inherits the
    SELF-LOOP-FREE scope `εT.word.filter (SelfLoopLetter n) = []`.  Ledger
    warrant (LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md, wave-A record):
    "instbij self-loop-free scoping (the depth-slot zip truncation,
    Codex-confirmed)" — "MIRRORS the capstone's order-0 perimeter." -/
import LeanUrat.MovesV.V3_instbijB

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem inst_bij_eq {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (DE : XHDdEnt n S V)
    (εT : EntTemplate n) (hSLF : εT.word.filter (SelfLoopLetter n) = [])
    (β₀ : S.Cell) (hl : V.entLands εT β₀) :
    ∃ e : {h : Hpt εT.entDim // (V.entDom εT).Mem h} ≃
        {ε : EntShapeV n // ε.template? = some εT ∧ Realizable V ε β₀},
      ∀ h, (e h).1 = writeHeights εT h.1 := by
  classical
  -- THE ROUNDTRIP CHECK (the zig/gamTie leg): the instantiated concrete shape
  -- reads back to its own template.
  have hround : ∀ h : Hpt εT.entDim, (writeHeights εT h).template? = some εT := by
    -- [ADJ-3 RESIDUE, exact: `template?` recomputes the word as
    --  `collapseRuns (spWord n (writeHeights εT h).Phat)`, and `spWord` is a
    --  CLASSICAL CHOICE over `SpWordFits` (junk [] when none fits).  Even
    --  with hSLF and A's exact-zip read-off, closing this needs (a) a
    --  fitting-word EXISTENCE certificate for the constructed prefix (its
    --  reads satisfy ReadFits, whence SpFitsRead at εT.word — the V3-3a
    --  width-law seam again), and (b) a CHOICE-PINNING law (any fitting word
    --  collapses to εT.word) — exactly V3-3d `spWord_faithful`'s re-keyed
    --  content, REFUTED AS STATED (junk-[] collision witness
    --  `SpFaithNeg.spWord_faithful_false`) and owned by ADJ-2/B3.  Not yet
    --  landed; this is the honest open core of V3-5c.]
    sorry
  -- realizability of every dom point, via the XHD-d no-stray face + the landing
  -- hypothesis.
  have hreal : ∀ h : Hpt εT.entDim, (V.entDom εT).Mem h →
      Realizable V (writeHeights εT h) β₀ := by
    intro h hMem
    obtain ⟨ε, hεmem, hεR⟩ := DE.no_strayE εT h β₀ hl hMem
    have hmem2 : writeHeights εT h ∈ writeHeights? εT h :=
      Option.get_mem (writeHeights_total_unscoped εT h)
    obtain rfl := Option.mem_unique hεmem hmem2
    exact hεR
  refine ⟨Equiv.ofBijective
      (fun a : {h : Hpt εT.entDim // (V.entDom εT).Mem h} =>
        (⟨writeHeights εT a.1, hround a.1, hreal a.1 a.2⟩ :
          {ε : EntShapeV n // ε.template? = some εT ∧ Realizable V ε β₀}))
      ⟨?_, ?_⟩, fun h => rfl⟩
  · -- injectivity, from V3-5a's `inst_bij_inj` (ADJ-3 scoped)
    intro a a' hEq
    have hv : writeHeights εT a.1 = writeHeights εT a'.1 := congrArg Subtype.val hEq
    exact Subtype.ext (inst_bij_inj εT hSLF hv)
  · -- surjectivity, from V3-5b's `inst_bij_surj` (ADJ-3 scoped)
    rintro ⟨ε, hT, hR⟩
    obtain ⟨h, hMem, hwrite⟩ := inst_bij_surj V DE εT hSLF β₀ ε hT hR
    exact ⟨⟨h, hMem⟩, Subtype.ext hwrite⟩

end LeanUrat.MovesV
