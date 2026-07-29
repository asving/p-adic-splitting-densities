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
    -- FENCE-RULE RECORD (final-ratification V repairs, 2026-07-29): negation
    -- attempted at the in-corpus witness `n2Chain` (N2Sigmas) — clause (ii)
    -- HOLDS there (shDom = {0}, shWeightH ≡ 1, WshVal ≡ 1: singleton HasSum),
    -- so no compiled countermodel exists.  PLAUSIBILITY FLAG for the [3t]
    -- owner: the chain laws tie shWeightH/WshVal to level censuses
    -- (shweight_card/wshval_card/shevt_grouping) but nothing forces
    -- summability over an INFINITE shDom — a from-scratch chain with
    -- shDom infinite, shWeightH ≡ 1, visH ≡ ∅ (so shEvt = ∅, WshVal → 0)
    -- appears to satisfy every card law while breaking the HasSum; if such
    -- a chain is constructible the statement needs a domain-census guard
    -- (sign-off adjudication, queued).
    sorry

/-- the pin-level restatement: the chain's `wsh17_pin` at its own carriers. -/
theorem w17ii_pin {n : ℕ} {T : TableShape n} {M : MeasuredSide T}
    {RB : RatBurdens T M} {hdc : DegCons T}
    {hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e} {F : ShapeFam T}
    (C : RS4Chain T M RB hdc hK F) : C.wsh17_pin :=
  w17ii_wave4 C

end LeanUrat.MovesV
