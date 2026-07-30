/-  MovesV unit V1-3a `xhdd_exact_supp` (RE-KEYED REV 7 C6; SPLIT REV 9 M-2) —
    ROSTER (3): xhdd_exact, mem_chainCount_pos (the ONE-WAY count supply),
    treal_iff_tgam (the REV-7 demotion lemma). -/
import LeanUrat.MovesV.V1_lastTie

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem xhdd_exact {n} {S : StepSys n} {TE : TmplEvents n S} (D : XHDd n S TE)
    {α} (γ : Template n S α) (h : Hpt γ.D) :
    (D.dom γ).Mem h ↔
      ∀ q₀ ∈ S.Pools, ∀ x : S.Hist q₀ α, S.zc x → 0 < Tgam TE γ x h := by
  constructor
  · exact fun hm q₀ hq x hzc => D.no_stray γ h hm hq x hzc
  · intro hall
    obtain ⟨q₀, hq⟩ := S.pools_ne
    obtain ⟨x, hzc⟩ := S.zc_ne q₀ hq α
    exact D.no_orphan γ x h hq hzc (hall q₀ hq x hzc)

theorem mem_chainCount_pos {n} {S : StepSys n} {TE : TmplEvents n S}
    (D : XHDd n S TE) {α} (γ : Template n S α) (h : Hpt γ.D)
    (hm : (D.dom γ).Mem h) {q₀} (hq : q₀ ∈ S.Pools) (x : S.Hist q₀ α)
    (hzc : S.zc x) : 0 < chainCount S γ x h :=
  lt_of_lt_of_le (D.no_stray γ h hm hq x hzc) (marks_chains TE γ x h hq hzc)

theorem treal_iff_tgam {n} {S : StepSys n} (TE : TmplEvents n S)
    {α} (γ : Template n S α) {q₀} (x : S.Hist q₀ α) (h : Hpt γ.D)
    (hq : q₀ ∈ S.Pools) (hzc : S.zc x) :
    TReal TE γ x h ↔ 0 < Tgam TE γ x h :=
  ⟨fun hr => TE.real_marks γ x h hq hzc hr,
   fun hp => TE.marks_realize γ x h hq hzc hp⟩

end LeanUrat.MovesV
