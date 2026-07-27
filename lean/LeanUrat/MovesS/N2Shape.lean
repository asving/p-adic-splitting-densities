/-
Unit `n2_shape` (medium; S5 construction batch) — TableShape DATA at n = 2:
block-1 layer (one state, one terminal outcome (1,1), Kmat 1 = 0) + the
THREE-outcome block-2 roster + vEquiv + Wloc/Wstate.  R44: the roster and the
numerators are a CONSISTENCY DEVICE, NOT note displays; note-displayed and
reproduced: the 1×1 block shape, the solve denominator q² + q + 1, the p = 2
ratio-1/8 shadow (`msW_eighth_le`), the checksum shadows.
  o_K   (c=1, m=1, member size 2)          — kcol
  o_spl (c=0, m=2, verdicts (1,1)+(1,1))   — termFin
  o_in  (c=0, m=1, verdict (1,2))          — termFin
-/
import LeanUrat.MovesS.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

noncomputable def n2T : TableShape 2 := sorry

/-- THE block-2 state τ★. -/
noncomputable def n2τ : n2T.State 2 := sorry
/-- The kcol outcome (rowVal q₀⁻³; the 1/8 shadow at q₀ = 2). -/
noncomputable def n2oK : n2T.Out 2 n2τ := sorry
/-- The termFin outcome with verdicts (1,1) + (1,1) (rowVal 1 − q₀⁻¹). -/
noncomputable def n2oSpl : n2T.Out 2 n2τ := sorry
/-- The termFin outcome with verdict (1,2) (rowVal q₀⁻¹ − q₀⁻³). -/
noncomputable def n2oIn : n2T.Out 2 n2τ := sorry

/-- The verdict labels, named through the R20 structural pin vEquiv. -/
noncomputable def n2v11 : n2T.VType := n2T.vEquiv.symm ⟨(1, 1), by decide⟩
noncomputable def n2v12 : n2T.VType := n2T.vEquiv.symm ⟨(1, 2), by decide⟩
noncomputable def n2v21 : n2T.VType := n2T.vEquiv.symm ⟨(2, 1), by decide⟩

/-- The data pins: routes, verdicts, roster exhaustiveness, one state per block,
the block-1 layer's single terminal (1,1) outcome. -/
theorem n2_shape :
    routeOf (n2T.odata 2 n2τ n2oK) = .kcol ∧
    routeOf (n2T.odata 2 n2τ n2oSpl) = .termFin ∧
    routeOf (n2T.odata 2 n2τ n2oIn) = .termFin ∧
    (n2T.odata 2 n2τ n2oSpl).verdicts = {n2v11, n2v11} ∧
    (n2T.odata 2 n2τ n2oIn).verdicts = {n2v12} ∧
    (n2T.odata 2 n2τ n2oK).m = 1 ∧
    (∀ μ ∈ (n2T.odata 2 n2τ n2oK).mem, μ.size = 2 ∧ μ.δ = 1) ∧
    (∀ o : n2T.Out 2 n2τ, o = n2oK ∨ o = n2oSpl ∨ o = n2oIn) ∧
    (n2oK ≠ n2oSpl ∧ n2oK ≠ n2oIn ∧ n2oSpl ≠ n2oIn) ∧
    (∀ τ : n2T.State 2, τ = n2τ) ∧
    (∀ τ τ' : n2T.State 1, τ = τ') ∧
    (∀ (τ : n2T.State 1) (o : n2T.Out 1 τ),
      routeOf (n2T.odata 1 τ o) = .termFin ∧ (n2T.odata 1 τ o).verdicts = {n2v11}) :=
  sorry

end LeanUrat.MovesS
