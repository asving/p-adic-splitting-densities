/-
Unit `n2_scs_data` (easy; S5 construction batch) — DegCons/SCSData DATA (the
corrected R35 windows: at o_K, ℓ = g = μ = 1, W = 2, D = 1); the LAWS display is
U-29b3 (`N2DegScs.lean`).  Also carries `n2hdc`/`n2hK` — the DegCons term and the
U-6-produced Kmat hypothesis every gate consumer takes.
-/
import LeanUrat.MovesS.N2Shape

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

/-! ### Reduction helpers for the concrete `n2T` roster.

`n2T` (from `N2Shape.lean`) has `State e = Unit`, `Out e τ = Fin 3` for every `e`, and
`odata e τ o = n2outT11` whenever `e ≠ 2` (the private block-1 outcome), with the three
block-2 outcomes at `e = 2`.  The outcome carriers are `private` there, so these helpers
reduce `odata` at `e ≠ 2` to the (name-free) canonical level-0 representative
`n2T.odata 0 () 0`, after which every remaining goal is a closed decidable proposition. -/

/-- Every roster member has size ≥ 1 (the DegCons floor), read off the concrete data. -/
private lemma n2odata_const {e : ℕ} (he : e ≠ 2) (τ : n2T.State e) (o : n2T.Out e τ) :
    n2T.odata e τ o
      = n2T.odata 0 (() : n2T.State 0) ((0 : Fin 3) : n2T.Out 0 (() : n2T.State 0)) := by
  show (if e = 2 then _ else _) = _
  rw [if_neg he]
  rfl

private lemma n2len_pos {e : ℕ} (τ : n2T.State e) (o : n2T.Out e τ) :
    0 < (n2T.odata e τ o).mem.length := by
  rcases h : (n2T.odata e τ o).mem with _ | ⟨a, l⟩
  · exact absurd h (n2T.odata e τ o).hm
  · simp

/-- At `e ≠ 2` no roster member is continuing (the only continuing member is o_K's, at
`e = 2`). -/
private lemma n2_not_cont {e : ℕ} (he : e ≠ 2) (τ : n2T.State e) (o : n2T.Out e τ)
    (μ : Member n2T.VType n2T.State) (hμ : μ ∈ (n2T.odata e τ o).mem) :
    μ.status.isRight = false := by
  rw [n2odata_const he] at hμ
  revert hμ; revert μ; decide

/-! ### The SCS supply at the n = 2 instance (the R35-corrected windows). -/

/-- SCSData DATA: at o_K, `ℓ = g = μsel = 1`, `W = e = 2`, `D = 1`, `W' = 1`, `D' = e = 2`
(so `W'·D' = 2 =` the kcol member's size); no flank, a one-element residue multiset. -/
noncomputable def n2SCS : SCSData n2T where
  W := fun e _ _ => e
  D := fun _ _ _ => 1
  ℓ := fun _ _ _ => 1
  g := fun _ _ _ => 1
  μsel := fun _ _ _ => 1
  W' := fun _ _ _ => 1
  D' := fun e _ _ => e
  flankCount := fun _ _ _ => 0
  flankWidth := fun _ _ _ => 0
  resFactors := fun _ _ _ => ({((1 : ℕ), (1 : ℕ))} : Multiset (ℕ × ℕ))
  selIdx := fun e τ o => ⟨0, n2len_pos τ o⟩
  memberOf := fun _ _ _ => fun x => x.elim (fun a => a.elim0) (fun b => b.elim0)
  ℓpos := fun _ _ _ => le_refl 1
  window_comp := fun _ _ _ => by simp
  flank_zero := fun _ _ _ _ => rfl
  sel_mem := fun _ _ _ => by decide
  res_sum := fun _ _ _ => by decide
  memberOf_inj := fun _ _ _ => by
    intro a b _
    rcases a with x | x <;> exact x.elim0
  memberOf_ne_sel := fun _ _ _ => by
    intro i
    rcases i with x | x <;> exact x.elim0
  sel_continuing := by
    intro e τ o hk
    rcases eq_or_ne e 2 with he | he
    · subst he
      revert hk; revert o; revert τ
      simp only [Member.continuing]
      decide
    · rw [n2odata_const he] at hk
      exact absurd hk (by decide)
  stage_D := fun _ _ _ => by simp
  stage_W := fun _ _ _ => rfl
  cluster_parent := fun _ _ _ => by simp
  cluster_child := by
    intro e τ o i hcont hi
    rcases eq_or_ne e 2 with he | he
    · subst he
      revert hi; revert hcont; revert i; revert o; revert τ
      simp only [Member.continuing]
      decide
    · exfalso
      have hmem : (n2T.odata e τ o).mem.get i ∈ (n2T.odata e τ o).mem := List.get_mem _ i
      have hnc := n2_not_cont he τ o _ hmem
      unfold Member.continuing at hcont
      rw [hnc] at hcont
      exact absurd hcont (by decide)

/-! ### DegCons at the instance: every member size ≥ 1, and Σ size ≤ e for e ∈ {1,2}. -/

theorem n2hdc : DegCons n2T where
  size_pos := by
    intro e τ o μ hμ
    rcases eq_or_ne e 2 with he | he
    · subst he; revert hμ; revert μ; revert o; revert τ; decide
    · rw [n2odata_const he] at hμ; revert hμ; revert μ; decide
  size_sum := by
    intro e he τ o
    rcases eq_or_ne e 2 with he2 | he2
    · subst he2; revert o; revert τ; decide
    · have h1 : e = 1 := by rw [Finset.mem_Icc] at he; omega
      subst h1
      rw [n2odata_const (by decide : (1 : ℕ) ≠ 2)]
      decide

/-- U-6's hK at the instance (kcol members have full block size). -/
theorem n2hK : ∀ e, e ∈ Finset.Icc 1 2 → KmatHyp n2T e := by
  intro e he τ o hk
  rcases eq_or_ne e 2 with he2 | he2
  · subst he2
    revert hk; revert o; revert τ
    decide
  · have h1 : e = 1 := by rw [Finset.mem_Icc] at he; omega
    subst h1
    rw [n2odata_const (by decide : (1 : ℕ) ≠ 2)] at hk
    exact absurd hk (by decide)

end LeanUrat.MovesS
