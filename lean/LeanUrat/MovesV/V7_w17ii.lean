/-  MovesV unit V7-8 `w17ii_wave4` (NEW at REV 7, C14 = Fable CRIT-1;
    W4-SYNC delta 2) — the SCHEDULED W17ii proof duty AT EXACTLY the built
    projection-def type (`RS4Chain.wsh17_pin` = `W17ii T M F C.WshP C.WshVal
    C.shDom C.shWeightH`, built MovesS/Interfaces.lean 103–109 + 187–190).
    Clause (i) is rfl-level at the chain's own wsh_ok/wsh_interp; clause (ii)
    (the XHD-s shallow-height-sum face over the per-shape Ŝ layer) is the
    [3t]-owned half — THE ONE BANKED SORRY (C14), its type the whole content;
    NO unconditional marking while it lives. -/
import LeanUrat.MovesS.Interfaces
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV
open LeanUrat.MovesS

theorem w17ii_wave4 {n : ℕ} {T : TableShape n} {M : MeasuredSide T}
    {RB : RatBurdens T M} {hdc : DegCons T}
    {hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e} {F : ShapeFam T}
    (C : RS4Chain T M RB hdc hK F) :
    W17ii T M F C.WshP C.WshVal C.shDom C.shWeightH := by
  intro Ŝ hŜ q₀ hq
  constructor
  · -- clause (i): the W-presentation evaluates to the W-value — the chain's
    -- own wsh_ok/wsh_interp fields, rfl-level at the instance
    exact ⟨C.wsh_ok Ŝ hŜ q₀ hq, C.wsh_interp Ŝ hŜ q₀ hq⟩
  · -- clause (ii): WshVal IS the shDom height-sum of shWeightH — the
    -- [3t]-owned per-shape assembly half (V7-4b's per-ε̊ ingredients over
    -- the shape layer).  THE ONE BANKED SORRY (C14).
    sorry

/-- the pin-level restatement: the chain's `wsh17_pin` at its own carriers. -/
theorem w17ii_pin {n : ℕ} {T : TableShape n} {M : MeasuredSide T}
    {RB : RatBurdens T M} {hdc : DegCons T}
    {hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e} {F : ShapeFam T}
    (C : RS4Chain T M RB hdc hK F) : C.wsh17_pin :=
  w17ii_wave4 C

end LeanUrat.MovesV
