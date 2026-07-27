/-
Unit U-29d-i `n2_beta` (medium) — the RS1Bundle instance: βmeas := the evaluated
solve values (β_bdd from the explicit [0,1] bounds).  The pinned values are the
note-displayed reduced solve: β_{(1,2)} = (q+1)/(q²+q+1), β_{(1,1)²} =
q²/(q²+q+1).
-/
import LeanUrat.MovesS.Interfaces
import LeanUrat.MovesS.N2PolyGeom
import LeanUrat.MovesS.N2ScsData

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

/-! ### Pool facts -/

private lemma n2pools_one_le {q₀ : ℚ} (hq : q₀ ∈ n2M.Pools) : 1 ≤ q₀ := by
  obtain ⟨p, hp, δ, rfl⟩ := n2M.pools_prime_pow q₀ hq
  have h1 : (1 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.one_lt.le
  exact one_le_pow₀ h1

/-! ### The measured β family: the evaluated reduced solve values -/

/-- The evaluated solve values (the note-displayed reduced solve): at the block-2
layer, `β_{(1,2)} = (q₀+1)/(q₀²+q₀+1)` and `β_{(1,1)²} = q₀²/(q₀²+q₀+1)` keyed by
the verdict multiset (0 on every other key); at the block-1 layer, the single
terminal mass (1 on the (1,1)-verdict key, 0 elsewhere). -/
noncomputable def n2βval (e : ℕ) (σ' : Multiset n2T.VType) (q₀ : ℚ) : ℝ :=
  if e = 2 then
    if σ' = {n2v12} then (((q₀ + 1) / (q₀ ^ 2 + q₀ + 1) : ℚ) : ℝ)
    else if σ' = {n2v11, n2v11} then ((q₀ ^ 2 / (q₀ ^ 2 + q₀ + 1) : ℚ) : ℝ)
    else 0
  else if σ' = {n2v11} then 1 else 0

/-! ### Multiset key disequalities (card 1 vs card 2) -/

private lemma n2mult_ne_1211 : ({n2v12} : Multiset n2T.VType) ≠ {n2v11, n2v11} := by
  intro h
  simpa using congrArg Multiset.card h

private lemma n2mult_ne_1112 : ({n2v11, n2v11} : Multiset n2T.VType) ≠ {n2v12} := by
  intro h
  simpa using congrArg Multiset.card h

/-! ### The n2βval evaluation lemmas -/

private lemma n2βval_12 (q₀ : ℚ) :
    n2βval 2 {n2v12} q₀ = (((q₀ + 1) / (q₀ ^ 2 + q₀ + 1) : ℚ) : ℝ) := by
  simp [n2βval]

private lemma n2βval_11 (q₀ : ℚ) :
    n2βval 2 {n2v11, n2v11} q₀ = ((q₀ ^ 2 / (q₀ ^ 2 + q₀ + 1) : ℚ) : ℝ) := by
  unfold n2βval
  rw [if_pos (rfl : (2 : ℕ) = 2), if_neg n2mult_ne_1112, if_pos rfl]

private lemma n2βval_2other (σ' : Multiset n2T.VType) (q₀ : ℚ)
    (h12 : σ' ≠ {n2v12}) (h11 : σ' ≠ {n2v11, n2v11}) : n2βval 2 σ' q₀ = 0 := by
  unfold n2βval
  rw [if_pos (rfl : (2 : ℕ) = 2), if_neg h12, if_neg h11]

private lemma n2βval_1of (σ' : Multiset n2T.VType) (q₀ : ℚ) :
    n2βval 1 σ' q₀ = if σ' = {n2v11} then 1 else 0 := by
  simp only [n2βval]
  rw [if_neg (by norm_num : ¬(1 : ℕ) = 2)]

/-! ### Route facts: no split outcome anywhere in the n = 2 table -/

private lemma n2route_ne_split (e : ℕ) (τ : n2T.State e) (o : n2T.Out e τ) :
    routeOf (n2T.odata e τ o) ≠ Route.split := by
  by_cases he : e = 2
  · subst he
    obtain ⟨hrK, hrSpl, hrIn, _, _, _, _, hexh, _, hstate2, _, _⟩ := n2_shape
    have hτ := hstate2 τ
    subst hτ
    rcases hexh o with rfl | rfl | rfl
    · rw [hrK]; exact fun h => Route.noConfusion h
    · rw [hrSpl]; exact fun h => Route.noConfusion h
    · rw [hrIn]; exact fun h => Route.noConfusion h
  · simp only [n2T]
    rw [if_neg he]
    exact fun h => Route.noConfusion h

private lemma n2splitOuts_empty (e : ℕ) (τ : n2T.State e) :
    splitOuts n2T e τ = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro o
  simp only [splitOuts, Set.mem_toFinset, Set.mem_setOf_eq]
  exact n2route_ne_split e τ o

private lemma n2bSplitMeas_zero (e : ℕ) (σ' : Multiset n2T.VType) (q₀ : ℚ)
    (βhat : ∀ e', e' ∈ Finset.Icc 1 2 → n2T.State e' → Multiset n2T.VType → ℚ → ℝ)
    (τ : n2T.State e) :
    bSplitMeas n2T n2M e σ' q₀ βhat τ = 0 := by
  simp only [bSplitMeas]
  rw [n2splitOuts_empty e τ, Finset.sum_empty]

/-! ### The kernel-step values (the concrete n2M.kstep at k = 1) -/

private lemma n2kstep_e1 (τ β : n2T.State 1) (q₀ : ℚ) :
    n2M.kstep 1 1 τ β q₀ = 0 := by
  change ((if (1 : ℕ) = 2 then ((q₀ : ℝ))⁻¹ ^ 3 else 0) ^ 1 : ℝ) = 0
  norm_num

private lemma n2kstep_e2 (τ β : n2T.State 2) (q₀ : ℚ) :
    n2M.kstep 1 2 τ β q₀ = ((q₀ : ℝ))⁻¹ ^ 3 := by
  change ((if (2 : ℕ) = 2 then ((q₀ : ℝ))⁻¹ ^ 3 else 0) ^ 1 : ℝ) = ((q₀ : ℝ))⁻¹ ^ 3
  norm_num

/-! ### The measured terminal exit masses (bTermMeas at the concrete instance) -/

private lemma n2bTermMeas_e1 (τ : n2T.State 1) (σ' : Multiset n2T.VType) (q₀ : ℚ) :
    bTermMeas n2T n2M 1 σ' q₀ τ = if σ' = {n2v11} then 1 else 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h1⟩ := n2_shape
  simp only [bTermMeas]
  change (∑ o : Fin 3, if routeOf (n2T.odata 1 τ o) = Route.termFin ∧
      (n2T.odata 1 τ o).verdicts = σ' then n2M.rowVal 1 τ o q₀ else 0)
      = if σ' = {n2v11} then 1 else 0
  rw [Fin.sum_univ_three]
  have r0 : n2M.rowVal 1 τ (0 : Fin 3) q₀ = 1 := rfl
  have r1 : n2M.rowVal 1 τ (1 : Fin 3) q₀ = 0 := rfl
  have r2 : n2M.rowVal 1 τ (2 : Fin 3) q₀ = 0 := rfl
  have cAll : ∀ o : Fin 3, routeOf (n2T.odata 1 τ o) = Route.termFin ∧
      (n2T.odata 1 τ o).verdicts = {n2v11} := fun o => h1 τ o
  by_cases hσ : σ' = {n2v11}
  · subst hσ
    rw [if_pos (cAll 0), if_pos (cAll 1), if_pos (cAll 2), r0, r1, r2, if_pos rfl]
    norm_num
  · have hc : ∀ o : Fin 3, ¬(routeOf (n2T.odata 1 τ o) = Route.termFin ∧
        (n2T.odata 1 τ o).verdicts = σ') := by
      intro o
      rintro ⟨_, hv⟩
      exact hσ (hv.symm.trans (h1 τ o).2)
    rw [if_neg (hc 0), if_neg (hc 1), if_neg (hc 2), if_neg hσ]
    norm_num

private lemma n2bTermMeas_e2 (τ : n2T.State 2) (σ' : Multiset n2T.VType) (q₀ : ℚ) :
    bTermMeas n2T n2M 2 σ' q₀ τ
      = (if σ' = {n2v11, n2v11} then 1 - ((q₀ : ℝ))⁻¹ else 0)
        + (if σ' = {n2v12} then ((q₀ : ℝ))⁻¹ - ((q₀ : ℝ))⁻¹ ^ 3 else 0) := by
  obtain ⟨hrK, hrSpl, hrIn, hvSpl, hvIn, _, _, _, _, hstate2, _, _⟩ := n2_shape
  have hτ := hstate2 τ
  subst hτ
  -- the n2_shape facts, defeq-cast to the Fin-3 outcome coordinates
  have h0 : routeOf (n2T.odata 2 n2τ (0 : Fin 3)) = Route.kcol := hrK
  have h1r : routeOf (n2T.odata 2 n2τ (1 : Fin 3)) = Route.termFin := hrSpl
  have v1 : (n2T.odata 2 n2τ (1 : Fin 3)).verdicts = {n2v11, n2v11} := hvSpl
  have h2r : routeOf (n2T.odata 2 n2τ (2 : Fin 3)) = Route.termFin := hrIn
  have v2 : (n2T.odata 2 n2τ (2 : Fin 3)).verdicts = {n2v12} := hvIn
  have r1 : n2M.rowVal 2 n2τ (1 : Fin 3) q₀ = 1 - ((q₀ : ℝ))⁻¹ := rfl
  have r2 : n2M.rowVal 2 n2τ (2 : Fin 3) q₀ = ((q₀ : ℝ))⁻¹ - ((q₀ : ℝ))⁻¹ ^ 3 := rfl
  simp only [bTermMeas]
  change (∑ o : Fin 3, if routeOf (n2T.odata 2 n2τ o) = Route.termFin ∧
      (n2T.odata 2 n2τ o).verdicts = σ' then n2M.rowVal 2 n2τ o q₀ else 0) = _
  rw [Fin.sum_univ_three]
  have c0 : ¬(routeOf (n2T.odata 2 n2τ (0 : Fin 3)) = Route.termFin ∧
      (n2T.odata 2 n2τ (0 : Fin 3)).verdicts = σ') := by
    rintro ⟨hc, _⟩
    rw [h0] at hc
    exact Route.noConfusion hc
  rw [if_neg c0]
  by_cases h11 : σ' = {n2v11, n2v11}
  · subst h11
    have p1 : routeOf (n2T.odata 2 n2τ (1 : Fin 3)) = Route.termFin ∧
        (n2T.odata 2 n2τ (1 : Fin 3)).verdicts = {n2v11, n2v11} := ⟨h1r, v1⟩
    have c2 : ¬(routeOf (n2T.odata 2 n2τ (2 : Fin 3)) = Route.termFin ∧
        (n2T.odata 2 n2τ (2 : Fin 3)).verdicts = {n2v11, n2v11}) := by
      rintro ⟨_, hv⟩
      exact n2mult_ne_1211 (v2.symm.trans hv)
    rw [if_pos p1, if_neg c2, r1, if_pos rfl, if_neg n2mult_ne_1112]
    ring
  · by_cases h12 : σ' = {n2v12}
    · subst h12
      have c1 : ¬(routeOf (n2T.odata 2 n2τ (1 : Fin 3)) = Route.termFin ∧
          (n2T.odata 2 n2τ (1 : Fin 3)).verdicts = {n2v12}) := by
        rintro ⟨_, hv⟩
        exact n2mult_ne_1112 (v1.symm.trans hv)
      have p2 : routeOf (n2T.odata 2 n2τ (2 : Fin 3)) = Route.termFin ∧
          (n2T.odata 2 n2τ (2 : Fin 3)).verdicts = {n2v12} := ⟨h2r, v2⟩
      rw [if_neg c1, if_pos p2, r2, if_neg n2mult_ne_1211, if_pos rfl]
      ring
    · have c1 : ¬(routeOf (n2T.odata 2 n2τ (1 : Fin 3)) = Route.termFin ∧
          (n2T.odata 2 n2τ (1 : Fin 3)).verdicts = σ') := by
        rintro ⟨_, hv⟩
        exact h11 (hv.symm.trans v1)
      have c2 : ¬(routeOf (n2T.odata 2 n2τ (2 : Fin 3)) = Route.termFin ∧
          (n2T.odata 2 n2τ (2 : Fin 3)).verdicts = σ') := by
        rintro ⟨_, hv⟩
        exact h12 (hv.symm.trans v2)
      rw [if_neg c1, if_neg c2, if_neg h11, if_neg h12]
      ring

/-! ### The measured recursion (R_e-lump) at the instance -/

private lemma n2recursion_core (e : ℕ) (he : e ∈ Finset.Icc 1 2) (τ : n2T.State e)
    (σ' : Multiset n2T.VType) (q₀ : ℚ) (hq : q₀ ∈ n2M.Pools) :
    n2βval e σ' q₀ = evalRe n2T n2M n2RB n2hdc e he τ σ' q₀
      (fun e' _ _ σ'' q₀' => n2βval e' σ'' q₀') := by
  have hcase : e = 1 ∨ e = 2 := by
    have h := Finset.mem_Icc.mp he
    omega
  haveI : Unique (n2T.State e) := ⟨⟨τ⟩, fun _ => rfl⟩
  simp only [evalRe, n2bSplitMeas_zero, add_zero, Fintype.sum_unique]
  rcases hcase with rfl | rfl
  · -- block 1: no continuation (kstep = 0), the single terminal mass
    rw [n2kstep_e1, zero_mul, zero_add, n2bTermMeas_e1, n2βval_1of]
  · -- block 2: the 1×1 measured fixpoint β = q₀⁻³·β + (exit masses)
    have hx : (1 : ℝ) ≤ (q₀ : ℝ) := by exact_mod_cast n2pools_one_le hq
    have hxpos : (0 : ℝ) < (q₀ : ℝ) := lt_of_lt_of_le one_pos hx
    have hx0 : (q₀ : ℝ) ≠ 0 := hxpos.ne'
    have hdenpos : (0 : ℝ) < (q₀ : ℝ) ^ 2 + (q₀ : ℝ) + 1 := by
      nlinarith [sq_nonneg (q₀ : ℝ)]
    have hden : ((q₀ : ℝ) ^ 2 + (q₀ : ℝ) + 1) ≠ 0 := hdenpos.ne'
    rw [n2kstep_e2, n2bTermMeas_e2]
    by_cases h12 : σ' = {n2v12}
    · subst h12
      rw [n2βval_12, if_neg n2mult_ne_1211, if_pos rfl]
      push_cast
      field_simp
      ring
    · by_cases h11 : σ' = {n2v11, n2v11}
      · subst h11
        rw [n2βval_11, if_pos rfl, if_neg n2mult_ne_1112]
        push_cast
        field_simp
        ring
      · rw [n2βval_2other σ' q₀ h12 h11, if_neg h11, if_neg h12]
        ring

/-! ### The bundle -/

noncomputable def n2B : RS1Bundle n2T n2M n2RB n2hdc n2hK where
  βmeas := fun e _ _ _ σ' q₀ => n2βval e σ' q₀
  β_bdd := fun e he h_ent τ σ' q₀ hq => by
    have h1 : (1 : ℚ) ≤ q₀ := n2pools_one_le hq
    have hden : (0 : ℚ) < q₀ ^ 2 + q₀ + 1 := by nlinarith [sq_nonneg q₀]
    change n2βval e σ' q₀ ∈ Set.Icc (0 : ℝ) 1
    refine Set.mem_Icc.mpr ?_
    simp only [n2βval]
    split_ifs
    · -- β_{(1,2)} = (q₀+1)/(q₀²+q₀+1) ∈ [0,1]
      constructor
      · have h0 : (0 : ℚ) ≤ (q₀ + 1) / (q₀ ^ 2 + q₀ + 1) :=
          div_nonneg (by linarith) hden.le
        exact_mod_cast h0
      · have hle : (q₀ + 1) / (q₀ ^ 2 + q₀ + 1) ≤ 1 := by
          rw [div_le_one hden]
          nlinarith [sq_nonneg q₀]
        exact_mod_cast hle
    · -- β_{(1,1)²} = q₀²/(q₀²+q₀+1) ∈ [0,1]
      constructor
      · have h0 : (0 : ℚ) ≤ q₀ ^ 2 / (q₀ ^ 2 + q₀ + 1) :=
          div_nonneg (sq_nonneg q₀) hden.le
        exact_mod_cast h0
      · have hle : q₀ ^ 2 / (q₀ ^ 2 + q₀ + 1) ≤ 1 := by
          rw [div_le_one hden]
          linarith
        exact_mod_cast hle
    · norm_num
    · norm_num
    · norm_num
  βfull := fun e _ _ _ σ' q₀ => n2βval e σ' q₀
  xrb := fun _ _ _ _ _ _ _ _ => rfl
  recursion_meas := fun e he τ σ' q₀ hq _ h_ent => n2recursion_core e he τ σ' q₀ hq
  nsNull := True
  rexact := fun _ _ _ _ _ _ _ _ => rfl

/-! ### The pinned solve values (the note-displayed reduced solve) -/

theorem n2_beta : ∀ (he : 2 ∈ Finset.Icc 1 2) (h_ent : ℕ) (q₀ : ℚ),
    q₀ ∈ n2M.Pools →
    n2B.βmeas 2 he h_ent n2τ {n2v12} q₀ = (((q₀ + 1) / (q₀ ^ 2 + q₀ + 1) : ℚ) : ℝ) ∧
    n2B.βmeas 2 he h_ent n2τ {n2v11, n2v11} q₀ = ((q₀ ^ 2 / (q₀ ^ 2 + q₀ + 1) : ℚ) : ℝ) := by
  intro he h_ent q₀ hq
  exact ⟨n2βval_12 q₀, n2βval_11 q₀⟩

end LeanUrat.MovesS
