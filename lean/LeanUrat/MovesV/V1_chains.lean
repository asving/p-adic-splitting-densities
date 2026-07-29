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
  intro α γ
  induction γ with
  | last m => intro q₀ x h; rfl
  | lastT m => intro q₀ x h; rfl
  | cons m γ ih =>
    intro q₀ x h
    letI : Fintype (S.Assign m x (Hpt.take h)) := S.finA m x (Hpt.take h)
    letI : ∀ a : S.Assign m x (Hpt.take h),
        Fintype (Chains S γ (S.ext m x (Hpt.take h) a) (Hpt.drop h)) :=
      fun a => chainsFintype S γ (S.ext m x (Hpt.take h) a) (Hpt.drop h)
    have hcard :
        Fintype.card (Chains S (Template.cons m γ) x h)
          = ∑ a : S.Assign m x (Hpt.take h),
              Fintype.card (Chains S γ (S.ext m x (Hpt.take h) a) (Hpt.drop h)) :=
      Fintype.card_sigma
    rw [hcard, chainCount]
    exact Finset.sum_congr rfl
      (fun a _ => ih (S.ext m x (Hpt.take h) a) (Hpt.drop h))

theorem tgam_eq_chains {n} {S : StepSys n} (TE : TmplEvents n S) {α}
    (γ : Template n S α) {q₀} (x : S.Hist q₀ α) (h : Hpt γ.D)
    (hq : q₀ ∈ S.Pools) (hzc : S.zc x) :
    Tgam TE γ x h = Nat.card {c : Chains S γ x h // RealizesC TE γ x h c} := by
  have hinj := TE.tmark_inj γ x h hq hzc
  rw [Tgam, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.ofInjective (TE.tmark γ x h) hinj)

end LeanUrat.MovesV
