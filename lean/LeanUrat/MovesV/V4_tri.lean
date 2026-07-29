/-  MovesV unit V4-2 `act_triangular` — (ii-b): the evaluated kernel matrix at
    q₀ is block-triangular; stated on MovesS.Kmat at evaluation (matrix zeros
    only — no stochastic reading). -/
import LeanUrat.MovesV.V4_act
import LeanUrat.MovesS.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV
open LeanUrat.MovesS (OKat evalAt)

theorem act_triangular {n : ℕ} {T : MovesS.TableShape n}
    {M : MovesS.MeasuredSide T} (RB : MovesS.RatBurdens T M) {e : ℕ}
    (hK : MovesS.KmatHyp T e) (q₀ : ℚ) (hq : q₀ ∈ M.Pools)
    (τ β : T.State e) (hact : M.activeState q₀ e τ)
    (hin : ¬ M.activeState q₀ e β)
    (hrow : ∀ (o : T.Out e τ) (hk : MovesS.routeOf (T.odata e τ o) = .kcol),
      MovesS.kTarget T e τ o hk (hK τ o hk) = β →
      ∀ hok : RB.TG e τ o ∈ OKat q₀,
        (evalAt q₀ ⟨RB.TG e τ o, hok⟩ : ℚ) = 0)
    (hok : MovesS.Kmat T RB e hK τ β ∈ OKat q₀) :
    (evalAt q₀ ⟨MovesS.Kmat T RB e hK τ β, hok⟩ : ℚ) = 0 := by
  classical
  set S : T.Out e τ → OKat q₀ := fun o =>
    if hk : MovesS.routeOf (T.odata e τ o) = .kcol then
      (if MovesS.kTarget T e τ o hk (hK τ o hk) = β then
        (⟨RB.TG e τ o, RB.tg_ok e τ o q₀ hq⟩ : OKat q₀) else 0)
    else 0 with hS
  have key : (⟨MovesS.Kmat T RB e hK τ β, hok⟩ : OKat q₀) = ∑ o : T.Out e τ, S o := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    show MovesS.Kmat T RB e hK τ β = ∑ o : T.Out e τ, ((S o : MovesS.Qq))
    unfold MovesS.Kmat
    refine Finset.sum_congr rfl (fun o _ => ?_)
    simp only [hS]
    split_ifs with hk hkt <;> simp
  rw [key, map_sum]
  refine Finset.sum_eq_zero (fun o _ => ?_)
  simp only [hS]
  split_ifs with hk hkt
  · exact hrow o hk hkt (RB.tg_ok e τ o q₀ hq)
  · exact map_zero _
  · exact map_zero _

end LeanUrat.MovesV
