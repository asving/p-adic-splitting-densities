/-
Unit U-4 `scs_flank` (medium) — hypotheses now SUFFICIENT (R2-1, R2-2).
moves_ref: "m = 1 forces NO flank side (the read side spans the window: e·ℓ = W)
and a SINGLETON residual shape λ = {(g, μ)}".  sketch: m = 1 ⟹ member positions =
Fin 1 ⟹ selIdx is the only position; memberOf avoids it (memberOf_ne_sel) yet is
injective into it ⟹ its domain is EMPTY ⟹ flankCount = 0 AND no non-selected
residual factor (sel_mem makes resFactors the singleton); flank_zero gives
flankWidth = 0; window_comp gives W = e·ℓ; res_sum on the singleton gives g·μ = ℓ.
-/
import LeanUrat.MovesS.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

variable {n : ℕ}

theorem scs_flank {T : TableShape n} (S : SCSData T) {e : ℕ}
    {τ : T.State e} {o : T.Out e τ} (hm : (T.odata e τ o).m = 1) :
    S.flankCount e τ o = 0 ∧
    S.resFactors e τ o = {(S.g e τ o, S.μsel e τ o)} ∧
    S.W e τ o = e * S.ℓ e τ o ∧
    S.g e τ o * S.μsel e τ o = S.ℓ e τ o := by
  -- m = 1 ⟹ the member positions are a subsingleton (`Fin 1`).
  have hlen : (T.odata e τ o).mem.length = 1 := hm
  have key : ∀ (a b : Fin (T.odata e τ o).mem.length), a = b := by
    intro a b
    have ha := a.isLt
    have hb := b.isLt
    apply Fin.ext
    omega
  -- `memberOf` avoids `selIdx` yet lands in a subsingleton ⟹ its domain is empty.
  have part1 : S.flankCount e τ o = 0 := by
    by_contra h
    have hpos : 0 < S.flankCount e τ o := Nat.pos_of_ne_zero h
    exact S.memberOf_ne_sel e τ o (Sum.inl ⟨0, hpos⟩) (key _ _)
  have herase : ((S.resFactors e τ o).erase (S.g e τ o, S.μsel e τ o)).card = 0 := by
    by_contra h
    have hpos : 0 < ((S.resFactors e τ o).erase (S.g e τ o, S.μsel e τ o)).card :=
      Nat.pos_of_ne_zero h
    exact S.memberOf_ne_sel e τ o (Sum.inr ⟨0, hpos⟩) (key _ _)
  -- Empty erase + `sel_mem` ⟹ the residual shape is the selected singleton.
  have part2 : S.resFactors e τ o = {(S.g e τ o, S.μsel e τ o)} := by
    have hz : (S.resFactors e τ o).erase (S.g e τ o, S.μsel e τ o) = 0 :=
      Multiset.card_eq_zero.mp herase
    have hce := Multiset.cons_erase (S.sel_mem e τ o)
    rw [hz] at hce
    rw [← hce]
    rfl
  -- flankCount = 0 ⟹ flankWidth = 0 ⟹ window_comp collapses to W = e·ℓ.
  have part3 : S.W e τ o = e * S.ℓ e τ o := by
    have hfw : S.flankWidth e τ o = 0 := S.flank_zero e τ o part1
    rw [S.window_comp e τ o, hfw, Nat.add_zero]
  -- res_sum on the singleton gives g·μ = ℓ.
  have part4 : S.g e τ o * S.μsel e τ o = S.ℓ e τ o := by
    have hrs := S.res_sum e τ o
    rw [part2] at hrs
    simpa using hrs
  exact ⟨part1, part2, part3, part4⟩

end LeanUrat.MovesS
