/-  MovesV unit V1-3c `counting_tie_last` (REV 9, M-2 split) — tgam_last(+T) +
    marks_chains (the DERIVED bound; the rev-7 FIELD's name survives here). -/
import LeanUrat.MovesV.V1_chains

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem tgam_last {n} {S : StepSys n} (TE : TmplEvents n S) {α β}
    (m : S.Move α β) {q₀} (x : S.Hist q₀ α) (h : Hpt (S.dim m))
    (hq : q₀ ∈ S.Pools) (hzc : S.zc x) :
    Tgam TE (.last m) x h = S.cntraw m x h := by
  have hinj := TE.tmark_inj (.last m) x h hq hzc
  have hsurj := TE.tmark_last_surj m x h hq hzc
  rw [Tgam, ← Fintype.card_coe (TE.tinst (.last m) x h (TE.tmplLvl (.last m))),
      show S.cntraw m x h = chainCount S (.last m) x h from rfl,
      ← chains_card S (.last m) x h]
  exact Fintype.card_congr (Equiv.ofBijective (TE.tmark (.last m) x h) ⟨hinj, hsurj⟩)

theorem tgam_lastT {n} {S : StepSys n} (TE : TmplEvents n S) {α v}
    (m : S.MoveT α v) {q₀} (x : S.Hist q₀ α) (h : Hpt (S.dimT m))
    (hq : q₀ ∈ S.Pools) (hzc : S.zc x) :
    Tgam TE (.lastT m) x h = S.cntrawT m x h := by
  have hinj := TE.tmark_inj (.lastT m) x h hq hzc
  have hsurj := TE.tmark_lastT_surj m x h hq hzc
  rw [Tgam, ← Fintype.card_coe (TE.tinst (.lastT m) x h (TE.tmplLvl (.lastT m))),
      show S.cntrawT m x h = chainCount S (.lastT m) x h from rfl,
      ← chains_card S (.lastT m) x h]
  exact Fintype.card_congr (Equiv.ofBijective (TE.tmark (.lastT m) x h) ⟨hinj, hsurj⟩)

theorem marks_chains {n} {S : StepSys n} (TE : TmplEvents n S) {α}
    (γ : Template n S α) {q₀} (x : S.Hist q₀ α) (h : Hpt γ.D)
    (hq : q₀ ∈ S.Pools) (hzc : S.zc x) :
    Tgam TE γ x h ≤ chainCount S γ x h := by
  have hinj := TE.tmark_inj γ x h hq hzc
  rw [Tgam, ← chains_card S γ x h, ← Fintype.card_coe (TE.tinst γ x h (TE.tmplLvl γ))]
  exact Fintype.card_le_of_injective (TE.tmark γ x h) hinj

end LeanUrat.MovesV
