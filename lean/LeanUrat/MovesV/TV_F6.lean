/-  TV-F6 (BRIDGE BP3, cluster c5; E-phase skeleton; REV 2, finding 7 — NEW)
    — THE COMBINED SEAM PRODUCER `measured_seam`: ONE ∃ (T, M) carrying
    TablePins + the guarded |Box| card tie + Nonempty (LedgerIV T M) +
    Nonempty (RatBurdens T M).
    Blueprint: lean/notes/BRIDGE_BP3_TV_2026-07-30.md §3.E (REV 2 display)
    + §4 (TV-F6).  deps: TV-E7 (the LedgerIV bundle at measuredOf), TV-F5
    (the RatBurdens bundle).  FLAGGED FOR RATIFICATION AS ADDITIVE (the
    blueprint's own instruction; no existing statement changes).

    WHY THIS THEOREM EXISTS (the consumer-facing record, verified):
    `ledgerIV_inst` (V7_livC.lean:54) and `ratBurdens_exists` (V7_rbC.lean:42)
    are SEPARATE `∃ T M` theorems — eliminating them separately yields two
    unrelated (T, M) pairs, while `RS4Chain` (MovesS/Interfaces.lean:129)
    takes `L : LedgerIV T M` AND `RB : RatBurdens T M` over ONE (T, M).
    "Proved over the SAME witness" must therefore be a THEOREM, not a
    construction convention: THIS declaration is the supply seam future
    wiring must eliminate — separate elimination of the two ∃s does NOT
    compose.  Premise row = the UNION of the two duties' rows (verbatim:
    ledgerIV_inst's V X cp hVA hHMC hb hc hd hEC hEU ∪ ratBurdens_exists's
    V X cp hVA hTie J hEU hEC hA).  Both existing conclusions re-derive from
    it byte-identically (the two PROVED corollaries below — union row, since
    a corollary of the union-row theorem cannot shrink the row; the EXISTING
    two statements stay untouched as the row-minimal forms).
    Sketch: T := tableShape_inst's witness, M := the shared measuredOf;
    LedgerIV from the E-cluster bundles (E3-E6 at E7's assembly), RatBurdens
    from `ratBurdens_of_seam` at the SAME (T, M, K) (TV-F5); the box tie is
    rfl-genre at Box := V.Box. -/
import LeanUrat.MovesV.V7_livC

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.MovesV

/-- TV-F6 THE COMBINED SEAM PRODUCER (blueprint §3.E REV 2 display,
transcribed): one witness pair carries BOTH premise structures — the shape
`RS4Chain` (MovesS/Interfaces.lean:129) actually consumes. -/
theorem measured_seam {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hHMC : HMC TE X.d)
    (hb : P1CtblAdd V X.w) (hc : P1NullRem V X.w)
    (hd : P1FixedHeightExact V X.w)
    (hTie : MDomTie V TE X.d) (J : JCells n C S V)
    (hEU : EntU V) (hEC : EntCount V) (hA : AffEnt n) :
    ∃ (T : MovesS.TableShape n) (M : MovesS.MeasuredSide T),
      TablePins C T ∧
      (∀ q₀ ∈ V.Pools, ∀ N : ℕ, Nonempty (V.Box q₀ N) →
        Fintype.card (M.Box q₀ N) = @Fintype.card _ (V.finB q₀ N)) ∧
      Nonempty (MovesS.LedgerIV T M) ∧
      Nonempty (MovesS.RatBurdens T M) := by
  sorry

/-- TV-F6 re-derivation, ledger leg (PROVED from the producer): the
`ledgerIV_inst` CONCLUSION, byte-identical, at the union row. -/
theorem ledgerIV_inst_of_seam {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hHMC : HMC TE X.d)
    (hb : P1CtblAdd V X.w) (hc : P1NullRem V X.w)
    (hd : P1FixedHeightExact V X.w)
    (hTie : MDomTie V TE X.d) (J : JCells n C S V)
    (hEU : EntU V) (hEC : EntCount V) (hA : AffEnt n) :
    ∃ (T : MovesS.TableShape n) (M : MovesS.MeasuredSide T),
      TablePins C T ∧
      (∀ q₀ ∈ V.Pools, ∀ N : ℕ, Nonempty (V.Box q₀ N) →
        Fintype.card (M.Box q₀ N) = @Fintype.card _ (V.finB q₀ N)) ∧
      Nonempty (MovesS.LedgerIV T M) := by
  obtain ⟨T, M, h1, h2, h3, _⟩ :=
    measured_seam V X cp hVA hHMC hb hc hd hTie J hEU hEC hA
  exact ⟨T, M, h1, h2, h3⟩

/-- TV-F6 re-derivation, burdens leg (PROVED from the producer): the
`ratBurdens_exists` CONCLUSION, byte-identical, at the union row. -/
theorem ratBurdens_exists_of_seam {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hHMC : HMC TE X.d)
    (hb : P1CtblAdd V X.w) (hc : P1NullRem V X.w)
    (hd : P1FixedHeightExact V X.w)
    (hTie : MDomTie V TE X.d) (J : JCells n C S V)
    (hEU : EntU V) (hEC : EntCount V) (hA : AffEnt n) :
    ∃ (T : MovesS.TableShape n) (M : MovesS.MeasuredSide T),
      TablePins C T ∧
      (∀ q₀ ∈ V.Pools, ∀ N : ℕ, Nonempty (V.Box q₀ N) →
        Fintype.card (M.Box q₀ N) = @Fintype.card _ (V.finB q₀ N)) ∧
      Nonempty (MovesS.RatBurdens T M) := by
  obtain ⟨T, M, h1, h2, _, h4⟩ :=
    measured_seam V X cp hVA hHMC hb hc hd hTie J hEU hEC hA
  exact ⟨T, M, h1, h2, h4⟩

end LeanUrat.MovesV
