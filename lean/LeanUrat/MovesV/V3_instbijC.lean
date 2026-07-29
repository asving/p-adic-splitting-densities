/-  MovesV unit V3-5c `inst_bij_eq` — THE ASSEMBLED EQUIV + computation law
    (incl. the zig/gamTie roundtrip check). -/
import LeanUrat.MovesV.V3_instbijB

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem inst_bij_eq {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (DE : XHDdEnt n S V)
    (εT : EntTemplate n) (β₀ : S.Cell) (hl : V.entLands εT β₀) :
    ∃ e : {h : Hpt εT.entDim // (V.entDom εT).Mem h} ≃
        {ε : EntShapeV n // ε.template? = some εT ∧ Realizable V ε β₀},
      ∀ h, (e h).1 = writeHeights εT h.1 := by
  classical
  -- THE ROUNDTRIP CHECK (the zig/gamTie leg): the instantiated concrete shape
  -- reads back to its own template.  No supporting lemma exists in the corpus;
  -- this is the hard core standing open (see notes).
  have hround : ∀ h : Hpt εT.entDim, (writeHeights εT h).template? = some εT := by
    sorry
  -- realizability of every dom point, via the XHD-d no-stray face + the landing
  -- hypothesis.
  have hreal : ∀ h : Hpt εT.entDim, (V.entDom εT).Mem h →
      Realizable V (writeHeights εT h) β₀ := by
    intro h hMem
    obtain ⟨ε, hεmem, hεR⟩ := DE.no_strayE εT h β₀ hl hMem
    have hmem2 : writeHeights εT h ∈ writeHeights? εT h :=
      Option.get_mem (writeHeights_total εT h)
    obtain rfl := Option.mem_unique hεmem hmem2
    exact hεR
  refine ⟨Equiv.ofBijective
      (fun a : {h : Hpt εT.entDim // (V.entDom εT).Mem h} =>
        (⟨writeHeights εT a.1, hround a.1, hreal a.1 a.2⟩ :
          {ε : EntShapeV n // ε.template? = some εT ∧ Realizable V ε β₀}))
      ⟨?_, ?_⟩, fun h => rfl⟩
  · -- injectivity, from V3-5a's `inst_bij_inj`
    intro a a' hEq
    have hv : writeHeights εT a.1 = writeHeights εT a'.1 := congrArg Subtype.val hEq
    exact Subtype.ext (inst_bij_inj εT hv)
  · -- surjectivity, from V3-5b's `inst_bij_surj`
    rintro ⟨ε, hT, hR⟩
    obtain ⟨h, hMem, hwrite⟩ := inst_bij_surj V DE εT β₀ ε hT hR
    exact ⟨⟨h, hMem⟩, Subtype.ext hwrite⟩

end LeanUrat.MovesV
