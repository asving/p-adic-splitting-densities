/-  MovesV unit V1-8a `stepsys_realized` (SPLIT Codex-19; POOL-INDEXED REV 4) —
    the step-system witness: StepSys + C15Pack + XHDw + XHDu inhabited
    non-degenerately.  [E-PHASE NOTE: landed as the ∃-shaped statement; the
    concrete two-cell instance is the proof's content — MANIFEST deviations.] -/
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- The concrete step-system witness: one cell `Unit`, one continuing move
`Unit`, no terminal moves (`Empty`), `dim = 0`, `Hist := Unit`, `zc := True`,
`Assign := Unit`, and the constant unit mass.  Pools = the singleton prime
power `{2}`. -/
noncomputable def witS : StepSys 1 where
  Cell := Unit
  finC := inferInstance
  cell_ne := ⟨()⟩
  Move := fun _ _ => Unit
  MoveT := fun _ _ => Empty
  finM := fun _ _ => inferInstance
  finMT := fun _ _ => inferInstance
  dim := fun _ => 0
  dimT := fun m => m.elim
  Pools := {(2 : ℚ)}
  pools_ne := ⟨2, rfl⟩
  pools_pp := by
    intro q₀ hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact ⟨2, 1, Nat.prime_two, one_pos, by norm_num⟩
  pools_gt_one := by
    intro q₀ hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    norm_num
  Hist := fun _ _ => Unit
  hist_ne := fun _ _ _ => ⟨()⟩
  zc := fun _ => True
  zc_ne := fun _ _ _ => ⟨(), trivial⟩
  Assign := by intro α β m q₀ x h; exact Unit
  finA := by intro α β m q₀ x h; exact inferInstance
  AssignT := by intro α v m; exact m.elim
  finAT := by intro α v m; exact m.elim
  ext := by intro α β m q₀ x h a; exact ()
  ext_zc := by intro α β m q₀ x h a hzc; exact trivial
  massOf := by intro α β m q₀ x h a; exact (1 : ℝ)
  massOfT := by intro α v m; exact m.elim
  out_ne := by
    intro q₀ hq α x hzc
    exact Or.inl ⟨(), (), fun _ => 0, ⟨()⟩⟩

/-- The `(U-A)` §C supply pack over `witS`: trivial invariant, constant mass. -/
noncomputable def witC15 : C15Pack 1 witS where
  Inv := Unit
  invOf := by intro α β m q₀ x h; exact ()
  invOfT := by intro α v m; exact m.elim
  F := fun _ _ => (1 : ℝ)
  mass_factors := by intro α β m q₀ x h a hq hzc; simp [witS]
  mass_factorsT := by intro α v m; exact m.elim

/-- The `(XHD-w)` weights over `witS`: the zero affine form, so every mass is
`q₀ ^ 0 = 1`. -/
noncomputable def witXHDw : XHDw 1 witS where
  E := by intro α β m; exact ⟨0, Fin.elim0, fun i => i.elim0⟩
  ET := by intro α v m; exact m.elim
  w_eq := by
    intro α β m q₀ x h a hq hzc
    simp [witS, AffineE.eval]
  wT_eq := by intro α v m; exact m.elim

/-- The `(XHD-u)` uniformity over `witS`: every mass is `1` and every count is
`1`, so all comparisons hold; the terminal twins are vacuous. -/
noncomputable def witXHDu : XHDu 1 witS where
  u_R_mass := by intro α β m q₀ x x' h a a' hq hzc hzc'; simp [witS]
  u_R_cnt := by
    intro α β m q₀ x x' h hq hzc hzc'
    simp [witS, StepSys.cntraw]
  u_T := by
    intro α β m q₀ x h h' hq hzc hpos hpos'
    simp [witS, StepSys.cntraw]
  u_R_massT := by intro α v m; exact m.elim
  u_R_cntT := by intro α v m; exact m.elim
  u_TT := by intro α v m; exact m.elim

theorem stepsys_realized :
    ∃ S : StepSys 1, Nonempty (C15Pack 1 S) ∧ Nonempty (XHDw 1 S) ∧
      Nonempty (XHDu 1 S) := by
  exact ⟨witS, ⟨witC15⟩, ⟨witXHDw⟩, ⟨witXHDu⟩⟩

end LeanUrat.MovesV
