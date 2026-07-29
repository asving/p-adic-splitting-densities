/-  MovesV unit V4-9 `rep_indep` — (iv)-REP GIVEN (U-A) + (u-R) + ObsCheck:
    the WEIGHTED measured row is representative-constant.
    `measuredRow` (NAME→HOME) DISPLAYED.
    STATEMENT REPAIR 2026-07-29 (adjudicated; machine-verified refutation from
    the prover fleet): the E-phase signature was UNDER-HYPOTHESIZED — (u-R)
    equalizes only the RAW counts, and a Bool-fiber counterexample splits them
    x-dependently across cells. The needed bridge is `CellPolyPack.count`
    (Defs.lean §2.H: cntc = polynomial eval — x-FREE), added as the premise
    `cp`. Blueprint row (MOVESV_LEAN_BLUEPRINT_2026-07-28.md V4-9): "(iv)-REP
    GIVEN (U-A) + (u-R), as the checkable row-level clause: theorem rep_row
    (P : C15Pack) (U : XHDu) (hobs : ObsCheck (C.bd s)) : ∀ (x x' : reps of α)
    …, measuredRow x = measuredRow x' — the WEIGHTED (T·G)-row"; moves_ref
    "(iv)-REP … the row is cell-constant PROVIDED the species' evaluation maps
    mention no observable outside the (a)/(b) generator list".
    [REPAIR NOTE, off-domain leg: `cp.count` pins cntc only at listed heights
    (h ∈ cdom); the off-domain terms of the row are killed by the XHD-d CELL
    FACE's `no_orphanC` (0 < cntc → h ∈ cdom, contrapositive), so the premise
    `DC : XHDdC n S V` (§2.H's displayed companion row, F-3) rides with cp —
    without it the fleet's Bool-fiber refutation relocates to an unlisted
    height. Recorded as the deviation on this repair.] -/
import LeanUrat.MovesV.V4_part1A
import LeanUrat.MovesV.V1_UA

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

noncomputable def measuredRow {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (X : XHDw n S) {τ : S.Cell} {q₀ : ℚ}
    (x : S.Hist q₀ τ) : ℝ :=
  ∑' ch : Σ c : DCellAll V τ, Σ D : ℕ, Hpt D, μcellH V X x ch.1 ch.2

theorem rep_row {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} (X : XHDw n S) (P : C15Pack n S) (U : XHDu n S)
    (cp : CellPolyPack n C S V) (DC : XHDdC n S V)
    (hobs : ∀ s : Skeleton n, ObsCheck (C.bd s)) {τ : S.Cell} {q₀ : ℚ}
    (hq : q₀ ∈ V.Pools) (x x' : S.Hist q₀ τ) (hzc : S.zc x) (hzc' : S.zc x') :
    measuredRow V X x = measuredRow V X x' := by
  classical
  unfold measuredRow
  refine tsum_congr (fun ch => ?_)
  obtain ⟨c, D, h⟩ := ch
  cases c with
  | inl dc =>
    obtain ⟨⟨d, hd⟩, c⟩ := dc
    subst hd
    simp only [μcellH]
    split
    · next e =>
      rw [eq_of_heq (cast_heq _ x), eq_of_heq (cast_heq _ x')]
      have hcnt : V.cntc d x c (castHpt e h) = V.cntc d x' c (castHpt e h) := by
        by_cases hmem : (V.cdom d c).Mem (castHpt e h)
        · have hq1 := cp.count d c x hzc hq (castHpt e h) hmem
          have hq2 := cp.count d c x' hzc' hq (castHpt e h) hmem
          exact_mod_cast hq1.symm.trans hq2
        · have hz : V.cntc d x c (castHpt e h) = 0 :=
            Nat.eq_zero_of_not_pos
              (fun hpos => hmem (DC.no_orphanC d x c _ hq hzc hpos))
          have hz' : V.cntc d x' c (castHpt e h) = 0 :=
            Nat.eq_zero_of_not_pos
              (fun hpos => hmem (DC.no_orphanC d x' c _ hq hzc' hpos))
          rw [hz, hz']
      rw [hcnt]
    · rfl
  | inr vdc =>
    obtain ⟨v, ⟨d, hd⟩, c⟩ := vdc
    subst hd
    simp only [μcellH]
    split
    · next e =>
      rw [eq_of_heq (cast_heq _ x), eq_of_heq (cast_heq _ x')]
      have hcnt : V.cntcT d x c (castHpt e h) = V.cntcT d x' c (castHpt e h) := by
        by_cases hmem : (V.cdomT d c).Mem (castHpt e h)
        · have hq1 := cp.countT d c x hzc hq (castHpt e h) hmem
          have hq2 := cp.countT d c x' hzc' hq (castHpt e h) hmem
          exact_mod_cast hq1.symm.trans hq2
        · have hz : V.cntcT d x c (castHpt e h) = 0 :=
            Nat.eq_zero_of_not_pos
              (fun hpos => hmem (DC.no_orphanCT d x c _ hq hzc hpos))
          have hz' : V.cntcT d x' c (castHpt e h) = 0 :=
            Nat.eq_zero_of_not_pos
              (fun hpos => hmem (DC.no_orphanCT d x' c _ hq hzc' hpos))
          rw [hz, hz']
      rw [hcnt]
    · rfl

end LeanUrat.MovesV
