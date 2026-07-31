/-  TV-E8 (BRIDGE BP3, cluster c4; E-phase skeleton) — THE NON-VACUITY GATE
    AUDIT on the measuredOf witness.
    Blueprint: lean/notes/BRIDGE_BP3_TV_2026-07-30.md §4 (TV-E8):
    "grep for a compiled in-corpus `CtsMeasured` instance; if one exists,
    fire `measuredOf` at it and display one non-zero μcell value; else
    record 'no compiled CTS instance — witness genericity disclosed'."
    deps: TV-E7 (scheduling; the gate audits E7's as-built witness).
    CENSUS (the unit's grep duty, EXECUTED at E-phase 2026-07-30):
    compiled `CtsMeasured` instances in-corpus:
      (1) `mcV : CtsMeasured 1 Ctoy mcS` (V1_witnessC:272) — WITH the full
          XHD bundle `mcXHD : XHD 1 mcS mcTE mcV` (:500);
      (2) `epV : CtsMeasured 1 Ctoy epS` (V4_meas:192) — no XHD bundle.
    NO compiled `CellPolyPack` instance exists anywhere in-corpus — the cp
    leg is the ONE missing firing ingredient.  Resolution (recorded): the
    gate therefore carries `mcCP` below as its own probe-carrier duty (the
    one-cell toy's count-polynomial pack; plausibly constructible — the toy
    has one skeleton, one letter, subsingleton cells).  If the prover finds
    mcCP unbuildable, the unit's else-branch fires instead: retire both
    declarations to a "witness genericity disclosed" record at the
    measuredOf docstring (adjudication outcome, never a forced proof). -/
import LeanUrat.MovesV.TV_E7
import LeanUrat.MovesV.V1_witnessC

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.MovesV

/-- TV-E8 [firing ingredient]: Skeleton 1 is finite (from V1_witnessC's
Subsingleton instance; feeds ctsTable/measuredOf's hfin at the toy). -/
theorem skeleton1_finite : Finite (Skeleton 1) :=
  Finite.of_subsingleton

/-- TV-E8 [probe carrier]: a count-polynomial pack over the compiled toy
`mcV` — the one firing ingredient the census found missing (see file
header).  Sketch: the toy has one skeleton/letter/outcome roster and
subsingleton cell indices; `P := ` the constant polynomial matching mcV's
`cntc`/`cntcT` at the pow2 pools (the V1_witnessC counting laws).
PROBE DUTY: build, or fire the else-branch record. -/
noncomputable def mcCP : CellPolyPack 1 Ctoy mcS mcV where
  P := fun _ _ _ _ _ => 1
  deg := fun _ _ _ _ _ => by simp
  count := fun d => d.hc.elim
  countT := by
    classical
    intro v d c q₀ x hzc hq h hmem
    letI : Fintype (mcS.AssignT (mcV.moveOfT d) x h) := mcS.finAT (mcV.moveOfT d) x h
    show ((1 : Polynomial ℚ).eval q₀ : ℚ) = (mcV.cntcT d x c h : ℚ)
    rw [Polynomial.eval_one]
    have hc1 : mcV.cntcT d x c h = 1 := by
      simp only [CtsMeasured.cntcT]
      refine le_antisymm (le_trans (Finset.card_filter_le _ _) ?_)
        (Finset.card_pos.mpr ⟨(() : mcS.AssignT (mcV.moveOfT d) x h),
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            @Subsingleton.elim (mcV.DCellO d.s d.m d.o d.α)
              (inferInstanceAs (Subsingleton Unit)) _ c⟩⟩)
      simp
    rw [hc1]; norm_num

/-- TV-E8 [the gate]: the fired witness is NOT the degenerate A28 core —
one non-zero μcell value displayed at a pool point of the compiled toy
(blueprint: "fire measuredOf at it and display one non-zero μcell value").
deps: TV-E7's witness, mcCP, skeleton1_finite. -/
theorem measuredOf_nonvacuity_gate :
    ∃ (e : ℕ) (τ : (ctsTable Ctoy skeleton1_finite).State e)
      (x : (measuredOf mcV mcXHD mcCP skeleton1_finite).Rep e τ)
      (c : (measuredOf mcV mcXHD mcCP skeleton1_finite).Cell e τ)
      (q₀ : ℚ),
      q₀ ∈ mcV.Pools ∧
      (measuredOf mcV mcXHD mcCP skeleton1_finite).μcell e τ x c q₀ ≠ 0 := by
  sorry

end LeanUrat.MovesV
