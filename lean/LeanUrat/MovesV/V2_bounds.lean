/-  MovesV unit V2-10 `wloc_wstate_split` (RESTATED C11) — the SPLIT-bound
    fence: gate degree records + the Wstate > Wloc consistency witness. -/
import LeanUrat.MovesV.DefsGate
import LeanUrat.MovesSp.SP6_n1singleton

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- (a) the gate data's degree records (root Wloc = 3; s_blk2 Wloc = 2). -/
theorem gate_bounds : TH3.natDegree = 3 ∧ Tsplit.natDegree = 2 ∧
    Tdbl.natDegree = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold TH3; compute_degree!
  · unfold Tsplit; compute_degree!
  · unfold Tdbl; compute_degree!

/-- (b) an explicit SYNTHETIC family witnessing `Wstate s > Wloc s m`. -/
theorem wstate_gt_wloc_consistent :
    ∃ (C : CtsFamily 1) (s : Skeleton 1) (m : (C.bd s).Letter),
      C.Wloc s m < (C.bd s).Wstate := by
  classical
  refine ⟨{
    bd := fun _ => {
      Carrier := fun _ => PUnit
      finCar := fun _ => inferInstance
      Letter := PUnit
      finL := inferInstance
      letterSp := fun _ => Sum.inr MovesSp.Verdict.z
      letter_menu := fun _ => Or.inr ⟨_, Set.mem_univ _, rfl⟩
      Obs := fun _ _ => PUnit
      evalObs := fun _ _ _ => PUnit.unit
      Gen := Empty
      finG := inferInstance
      gen := fun g => g.elim
      Wstate := 1
      sizeP := fun _ => 1
      size_deg := fun _ => by simp
      size_count := fun _ q₀ _ => by
        simp only [Polynomial.eval_one]
        rw [Finset.filter_true_of_mem (fun x _ g => g.elim)]
        simp
      Outc := fun _ => PUnit
      finO := fun _ => inferInstance
      omem := fun _ _ => [⟨0, 1, Sum.inl ⟨(1, 1), by decide⟩⟩]
      omem_ne := fun _ _ => by simp
      omem_size := fun _ _ mu hmu sk hst => by
        simp only [List.mem_singleton] at hmu
        subst hmu
        simp at hst
      cont := fun _ _ => False
      decCont := fun _ _ => .isFalse id
      cont_iff := fun _ _ => by simp [Sum.isRight]
      tgtSk := fun _ _ h => h.elim
      tgt_sp := fun _ _ h => h.elim
      omem_sel := fun _ _ h => h.elim
    }
    tcell := fun _ _ _ h => h.elim
    tcellM := fun _ _ _ i sk hst => by
      exfalso
      obtain ⟨j, hj⟩ := i
      simp only [List.length_cons, List.length_nil] at hj
      interval_cases j
      simp [List.get] at hst
    tcellM_sel := fun _ _ _ h => h.elim
    Wloc := fun _ _ => 0
    T := fun _ _ _ _ _ => 1
    T_deg := fun _ _ _ _ _ => by simp
    vlabOf := fun _ _ _ _ => ⟨(1, 1), by decide⟩
  }, ⟨MovesSp.confirmingRoot1, (MovesSp.SnRaw1_eq _).mpr rfl⟩, PUnit.unit, ?_⟩
  decide

end LeanUrat.MovesV
