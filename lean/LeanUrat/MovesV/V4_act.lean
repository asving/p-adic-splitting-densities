/-  MovesV unit V4-1 `act_no_entry` (GUARD RESTORED C15; REV 4 Codex-9;
    REV 5 M-1 ripple) — (ii-a) NO-ENTRY GIVEN ValA, active-source-guarded. -/
import LeanUrat.MovesV.V2_valA
import LeanUrat.MovesV.V3_aggfullB

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem no_entry {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} (hVA : ValA n C S V) (d : MoveData n C) {q₀ : ℚ}
    (hq : q₀ ∈ V.Pools) (hne : (V.mdom d).comps ≠ [])
    (hact : V.activeState q₀ (V.toStepCells.symm d.src))
    (hin : ¬ V.activeState q₀ (V.toStepCells.symm d.tgt)) :
    ((C.T d.s d.m d.o d.α d.tix).eval q₀ : ℚ) = 0 := by
  obtain ⟨x, hzc⟩ := S.zc_ne q₀ (V.pools_sub hq) (V.toStepCells.symm d.src)
  have hpos : 0 < (V.mdom d).comps.length := List.length_pos_of_ne_nil hne
  rw [hVA.tbl_count d x hzc hq ⟨0, hpos⟩,
    hVA.tgt_supported d x hzc (((V.mdom d).comps.get ⟨0, hpos⟩).base) hq hact hin]
  simp

theorem iota_supp {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} (XsEnt : XHDsEnt n S V) (hVA : ValA n C S V)
    (β₀ : S.Cell) {q₀ : ℚ} (hq : q₀ ∈ V.Pools)
    (hin : ¬ V.activeState q₀ β₀) : iotaValV V XsEnt β₀ q₀ = 0 := by
  unfold iotaValV
  apply Finset.sum_eq_zero
  intro i _
  unfold iotaShV
  rw [dif_pos hq]
  have hc : V.entCount i q₀ = 0 := by
    unfold CtsMeasured.entCount CtsMeasured.instCensus
    cases hwh : writeHeights? i.1.1 ((V.entDom i.1.1).comps.get i.1.2).base with
    | none => simp [hwh]
    | some ε =>
        simp only [hwh, Option.map_some, Option.getD_some]
        exact hVA.ent_supported ε β₀ q₀ hq hin
  rw [hc]
  simp

end LeanUrat.MovesV
