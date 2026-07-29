/-  MovesV unit V5-1 `marked_event_census` (RE-KEYED REV 4, N-1 ripple) —
    the (vi) marked event typed at the PROCESS carrier; the census lemma AT
    REALIZED POINTS rides the GUARDED `MarkFiberTie` (the guard is
    load-bearing: any unguarded version would re-prove HMC through no_stray). -/
import LeanUrat.MovesV.V1_xhdd

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV
open Classical

/-- the note-DEFINITIONAL mark-fiber structure of the (vi) display, typed as
a GUARDED premise (tevt is free data): at REALIZED composite points the
event fibers over the mark census. -/
def MarkFiberTie {n : ℕ} {S : StepSys n} (TE : TmplEvents n S) : Prop :=
  ∀ {α} (γ : Template n S α) {q₀} (x : S.Hist q₀ α) (h : Hpt γ.D),
    q₀ ∈ S.Pools → S.zc x → TReal TE γ x h → ∀ N ≥ TE.tmplLvl γ,
    ∃ fib : TE.Box q₀ N → {b // b ∈ TE.tinst γ x h (TE.tmplLvl γ)},
      (TE.tevt γ x h N).card
        = ∑ b ∈ (TE.tinst γ x h (TE.tmplLvl γ)).attach,
            ((TE.tevt γ x h N).filter (fun z => fib z = b)).card

/-- the census lemma at realized points (double counting under the tie). -/
theorem marked_event_census {n : ℕ} {S : StepSys n} (TE : TmplEvents n S)
    (hTie : MarkFiberTie TE) {α} (γ : Template n S α) {q₀}
    (x : S.Hist q₀ α) (h : Hpt γ.D) (hq : q₀ ∈ S.Pools) (hzc : S.zc x)
    (hr : TReal TE γ x h) (N : ℕ) (hN : N ≥ TE.tmplLvl γ) :
    ∃ fib : TE.Box q₀ N → {b // b ∈ TE.tinst γ x h (TE.tmplLvl γ)},
      (TE.tevt γ x h N).card
        = ∑ b ∈ (TE.tinst γ x h (TE.tmplLvl γ)).attach,
            ((TE.tevt γ x h N).filter (fun z => fib z = b)).card :=
  hTie γ x h hq hzc hr N hN

end LeanUrat.MovesV
