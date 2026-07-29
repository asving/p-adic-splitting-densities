/-  MovesV unit V1-3b `counting_tie_chains` (REV 9, M-2 split) — chains_card +
    tgam_eq_chains: Tgam IS the direct chain-set card BY LAW (MOVES 7921–7923). -/
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

noncomputable instance chainsFintype {n} (S : StepSys n) :
    ∀ {α} (γ : Template n S α) {q₀} (x : S.Hist q₀ α) (h : Hpt γ.D),
    Fintype (Chains S γ x h)
  | _, .last m, _, x, h => S.finA m x h
  | _, .lastT m, _, x, h => S.finAT m x h
  | _, .cons m γ, _, x, h =>
      letI := S.finA m x (Hpt.take h)
      letI := fun a : S.Assign m x (Hpt.take h) =>
        chainsFintype S γ (S.ext m x (Hpt.take h) a) (Hpt.drop h)
      Sigma.instFintype

theorem chains_card {n} (S : StepSys n) :
    ∀ {α} (γ : Template n S α) {q₀} (x : S.Hist q₀ α) (h : Hpt γ.D),
    Fintype.card (Chains S γ x h) = chainCount S γ x h := by
  sorry

theorem tgam_eq_chains {n} {S : StepSys n} (TE : TmplEvents n S) {α}
    (γ : Template n S α) {q₀} (x : S.Hist q₀ α) (h : Hpt γ.D)
    (hq : q₀ ∈ S.Pools) (hzc : S.zc x) :
    Tgam TE γ x h = Nat.card {c : Chains S γ x h // RealizesC TE γ x h c} := by
  sorry

end LeanUrat.MovesV
