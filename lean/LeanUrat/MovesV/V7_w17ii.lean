/-  MovesV unit V7-8 `w17ii_wave4` (NEW at REV 7, C14 = Fable CRIT-1;
    W4-SYNC delta 2) — the SCHEDULED W17ii proof duty AT EXACTLY the built
    projection-def type (`RS4Chain.wsh17_pin` = `W17ii T M F C.WshP C.WshVal
    C.shDom C.shWeightH`, built MovesS/Interfaces.lean).
    Clause (i) is rfl-level at the chain's own wsh_ok/wsh_interp; clause (ii)
    (the XHD-s shallow-height-sum face over the per-shape Ŝ layer) was the
    [3t]-owned half — THE ONE BANKED SORRY (C14).

    QUEUE ITEM 4 EXECUTED (Asvin sign-off 2026-07-31; TV-H3 of
    BRIDGE_BP3_TV_2026-07-30.md §3.G REV 2, menu (b′)): clause (ii) as
    previously stated was FALSE — the TV-H1b COMPILED countermodel
    (quarantine/TV_H1b_w17iiNeg_2026-07-30.lean.txt; infinite shDom,
    shWeightH ≡ 1, every pre-repair chain law satisfied, the HasSum
    impossible).  The repair: RS4Chain gained the five census fields
    `shdom_fin` (the Q4-preferred guard, finiteness form) + `shdom_no_stray` +
    `vis_sub_shdom` + `shevt_off_vis` + `shevt_disj` (E-1, ratified in the
    same grant), and clause (ii) is now PROVED below by the COUNTING SQUEEZE:
    at a fixed pool and every large enough level N,
      WshVal·|Box| = |shEvt|                (wshval_card)
                   = Σ_{h ∈ visH} |shEvtH h|  (shevt_grouping + shevt_disj)
                   = Σ_{h ∈ shDom} |shEvtH h| (vis_sub_shdom + shevt_off_vis)
                   = (Σ_{h ∈ shDom} shWeightH h)·|Box|   (shweight_card),
    |Box| > 0 cancels (boxpos), and `shdom_fin` turns the finite-domain sum
    into the HasSum.  The banked C14 sorry is RETIRED; the MovesV census is
    updated in MANIFEST.json.  U-28's premise `h17 : C.wsh17_pin` is
    byte-identical (W17ii and the pin's def are untouched). -/
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
  · -- clause (ii): WshVal IS the shDom height-sum of shWeightH.
    -- HISTORY: banked (C14) 2026-07-29 with the infinite-shDom countermodel
    -- candidate flagged; the candidate COMPILED at TV-H1b (2026-07-30,
    -- quarantined) — clause (ii) was FALSE at the pre-repair chain.  PROVED
    -- 2026-07-31 (queue item 4) by the counting squeeze over the repair
    -- census fields; see the file header.
    classical
    have hfin : (C.shDom Ŝ).Finite := C.shdom_fin Ŝ hŜ
    set D : Finset M.Hgt := hfin.toFinset with hD
    -- per-height thresholds from the census fields
    have hw : ∀ h ∈ D, ∃ N₀, ∀ N ≥ N₀,
        C.shWeightH Ŝ h q₀ * (Fintype.card (M.Box q₀ N) : ℝ)
          = ((C.shEvtH Ŝ h q₀ N).card : ℝ) :=
      fun h hh => C.shweight_card Ŝ hŜ h (hfin.mem_toFinset.mp hh) q₀ hq
    have hoff : ∀ h ∈ D, ∃ N₀, ∀ N ≥ N₀,
        h ∉ C.visH Ŝ q₀ N → C.shEvtH Ŝ h q₀ N = ∅ :=
      fun h hh => C.shevt_off_vis Ŝ hŜ h (hfin.mem_toFinset.mp hh) q₀ hq
    choose Nw hNw using hw
    choose No hNo using hoff
    obtain ⟨Nv, hNv⟩ := C.vis_sub_shdom Ŝ hŜ q₀ hq
    obtain ⟨Nc, hNc⟩ := C.wshval_card Ŝ hŜ q₀ hq
    -- one uniform level N above every threshold
    set N : ℕ := max (max Nv Nc)
      (D.attach.sup fun h => max (Nw h.1 h.2) (No h.1 h.2)) with hN
    have hNv' : Nv ≤ N := le_trans (le_max_left _ _) (le_max_left _ _)
    have hNc' : Nc ≤ N := le_trans (le_max_right _ _) (le_max_left _ _)
    have hsupN : ∀ h (hh : h ∈ D), max (Nw h hh) (No h hh) ≤ N := by
      intro h hh
      have h1 : max (Nw h hh) (No h hh)
          ≤ D.attach.sup (fun x => max (Nw x.1 x.2) (No x.1 x.2)) := by
        have h2 := Finset.le_sup
          (f := fun x : {x // x ∈ D} => max (Nw x.1 x.2) (No x.1 x.2))
          (Finset.mem_attach D ⟨h, hh⟩)
        simpa using h2
      exact le_trans h1 (le_max_right _ _)
    -- the box cardinality is positive at every level
    have hbox : ((Fintype.card (M.Box q₀ N) : ℝ)) ≠ 0 := by
      haveI := M.boxpos q₀ N
      exact_mod_cast (Fintype.card_pos).ne'
    -- THE SQUEEZE at level N
    have hgroup := C.shevt_grouping Ŝ q₀ N
    have hbi : ((C.visH Ŝ q₀ N).biUnion fun h => C.shEvtH Ŝ h q₀ N).card
        = ∑ h ∈ C.visH Ŝ q₀ N, (C.shEvtH Ŝ h q₀ N).card :=
      Finset.card_biUnion (fun h hh h' hh' hne => C.shevt_disj Ŝ q₀ N h hh h' hh' hne)
    have hsub : C.visH Ŝ q₀ N ⊆ D :=
      fun h hh => hfin.mem_toFinset.mpr (hNv N hNv' h hh)
    have hext : ∑ h ∈ C.visH Ŝ q₀ N, (C.shEvtH Ŝ h q₀ N).card
        = ∑ h ∈ D, (C.shEvtH Ŝ h q₀ N).card := by
      refine Finset.sum_subset hsub (fun h hhD hhnot => ?_)
      rw [hNo h hhD N (le_trans (le_max_right _ _) (hsupN h hhD)) hhnot,
        Finset.card_empty]
    have key : C.WshVal Ŝ q₀ * (Fintype.card (M.Box q₀ N) : ℝ)
        = (∑ h ∈ D, C.shWeightH Ŝ h q₀) * (Fintype.card (M.Box q₀ N) : ℝ) := by
      rw [hNc N hNc', hgroup, hbi, hext, Finset.sum_mul, Nat.cast_sum]
      exact Finset.sum_congr rfl fun h hh =>
        (hNw h hh N (le_trans (le_max_left _ _) (hsupN h hh))).symm
    have hval : C.WshVal Ŝ q₀ = ∑ h ∈ D, C.shWeightH Ŝ h q₀ :=
      mul_right_cancel₀ hbox key
    -- the finite-domain sum IS the HasSum (the guard)
    have hind : HasSum (Set.indicator (C.shDom Ŝ) fun h => C.shWeightH Ŝ h q₀)
        (∑ h ∈ D, Set.indicator (C.shDom Ŝ) (fun h => C.shWeightH Ŝ h q₀) h) :=
      hasSum_sum_of_ne_finset_zero fun b hb =>
        Set.indicator_of_notMem (fun hmem => hb (hfin.mem_toFinset.mpr hmem)) _
    have hindsum : (∑ h ∈ D, Set.indicator (C.shDom Ŝ)
        (fun h => C.shWeightH Ŝ h q₀) h) = ∑ h ∈ D, C.shWeightH Ŝ h q₀ :=
      Finset.sum_congr rfl fun h hh =>
        Set.indicator_of_mem (hfin.mem_toFinset.mp hh) _
    rw [hindsum, ← hval] at hind
    exact hasSum_subtype_iff_indicator.mpr hind

/-- the pin-level restatement: the chain's `wsh17_pin` at its own carriers. -/
theorem w17ii_pin {n : ℕ} {T : TableShape n} {M : MeasuredSide T}
    {RB : RatBurdens T M} {hdc : DegCons T}
    {hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e} {F : ShapeFam T}
    (C : RS4Chain T M RB hdc hK F) : C.wsh17_pin :=
  w17ii_wave4 C

end LeanUrat.MovesV
