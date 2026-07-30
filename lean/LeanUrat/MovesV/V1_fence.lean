/-  MovesV unit V1-7 `ua_split_fence` — THE HONEST-SPLIT WITNESS (A-7 form):
    (XHD-u) is NOT a consequence of the pack (inverse-defect discipline). -/
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- The fence's two-history toy step system: at one pool (q₀ = 2), one cell, one
continuing move, `Hist := Fin 2` (the two histories), and `massOf` reads the history
index `x.val` — so the two histories carry DIFFERENT masses.  This is the inverse-defect
discipline made concrete: mass factors through `invOf` (the history itself), so the pack
holds, yet cross-history uniformity (u-R) FAILS. -/
private def fenceS : StepSys 1 where
  Cell := Fin 1
  finC := inferInstance
  cell_ne := ⟨0⟩
  Move _ _ := Fin 1
  MoveT _ _ := Fin 1
  finM _ _ := inferInstance
  finMT _ _ := inferInstance
  dim := fun _ => 1
  dimT := fun _ => 1
  Pools := {2}
  pools_ne := ⟨2, rfl⟩
  pools_pp := by
    rintro q₀ rfl
    exact ⟨2, 1, Nat.prime_two, one_pos, by norm_num⟩
  pools_gt_one := by
    rintro q₀ rfl; norm_num
  Hist _ _ := Fin 2
  hist_ne _ _ _ := ⟨0⟩
  zc := fun _ => True
  zc_ne _ _ _ := ⟨0, trivial⟩
  Assign := fun _ _ _ _ => Fin 2
  finA := fun _ _ _ _ => inferInstance
  AssignT := fun _ _ _ _ => Fin 2
  finAT := fun _ _ _ _ => inferInstance
  ext := fun _ _ _ _ a => a
  ext_zc := fun _ _ _ _ _ _ => trivial
  massOf := fun _ _ x _ _ => ((x.val : ℝ))
  massOfT := fun _ _ x _ _ => ((x.val : ℝ))
  out_ne := fun _ _ _ _ _ => Or.inl ⟨0, 0, fun _ => 0, ⟨0⟩⟩

/-- The §C supply pack over `fenceS`: mass factors through the invariant `invOf := the
history`, valued by `F i := i.val`.  So `mass_factors`/`mass_factorsT` hold by `rfl` —
the pack is satisfied even though the two histories give unequal masses. -/
private def fenceP : C15Pack 1 fenceS where
  Inv := Fin 2
  invOf := fun _ _ x _ => x
  invOfT := fun _ _ x _ => x
  F := fun i _ => ((i.val : ℝ))
  mass_factors := by intros; rfl
  mass_factorsT := by intros; rfl

theorem ua_fence : ∃ S : StepSys 1, ∃ _P : C15Pack 1 S,
    ¬ (∀ {α β} (m : S.Move α β) {q₀} (_ : q₀ ∈ S.Pools)
        (x x' : S.Hist q₀ α) (h : Hpt (S.dim m)) (a : S.Assign m x h)
        (a' : S.Assign m x' h), S.massOf m x h a = S.massOf m x' h a') := by
  refine ⟨fenceS, fenceP, ?_⟩
  intro H
  have h2 := H (α := (0 : Fin 1)) (β := (0 : Fin 1)) (0 : Fin 1) (q₀ := 2) rfl
    (0 : Fin 2) (1 : Fin 2) (fun _ => 0) (0 : Fin 2) (0 : Fin 2)
  simp [fenceS] at h2

end LeanUrat.MovesV
