/-  MovesV unit V3-8a `ent_agg_conv` (SPLIT REV 4, Codex-7; PREMISE RE-KEYED
    REV 7, Codex6-C7) — THE NOTE-EXACT AGGREGATION: convergence GIVEN XHD-s
    on the shallow layer ALONE (summability DERIVED via box_card). NO (ENT-U). -/
import LeanUrat.MovesV.V3_instbijC
import LeanUrat.MovesV.V3_aggfin
import LeanUrat.MovesV.V0_partition

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem ent_agg_conv {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (XsEnt : XHDsEnt n S V) (DE : XHDdEnt n S V)
    (β₀ : S.Cell) (q₀ : ℚ) (hq : q₀ ∈ V.Pools) :
    ∃ v : ℝ, HasSum
      (fun p : Σ i : V.EntIx β₀,
          {h // ((V.entDom i.1.1).comps.get i.1.2).Mem h} =>
        ιshH V p.1.1.1 p.2.1 β₀ q₀) v := by
  classical
  haveI : Finite (EntTemplate n) := template_finite n
  haveI : Finite (V.EntIx β₀) := by unfold CtsMeasured.EntIx; exact Subtype.finite
  haveI : Fintype (V.EntIx β₀) := Fintype.ofFinite _
  haveI : Fintype (EntTemplate n) := Fintype.ofFinite _
  -- pool positivity
  have hq1 : (1 : ℚ) < q₀ := S.pools_gt_one q₀ (V.pools_sub hq)
  have hq0 : (0 : ℝ) ≤ (q₀ : ℝ) := by
    have : (0 : ℚ) ≤ q₀ := le_of_lt (lt_trans one_pos hq1)
    exact_mod_cast this
  have hq1' : (1 : ℝ) ≤ (q₀ : ℝ) := by exact_mod_cast le_of_lt hq1
  -- the uniform defining-level bound M (finitely many templates)
  set M : ℕ := Finset.univ.sup (fun εT : EntTemplate n => V.entLvl εT) with hM
  have hlvl : ∀ ε : EntShapeV n, (ε.template?).elim 0 V.entLvl ≤ M := by
    intro ε
    cases htp : ε.template? with
    | none => exact Nat.zero_le _
    | some εT =>
      simpa using Finset.le_sup (f := fun εT : EntTemplate n => V.entLvl εT)
        (Finset.mem_univ εT)
  -- THE CENSUS BOUND (blueprint sketch): instCensus ≤ |Box(q₀, lvl)| = q₀^{n·lvl} ≤ q₀^{n·M}
  have hcb : ∀ (εT : EntTemplate n) (h : Hpt εT.entDim),
      (V.instCensus εT h β₀ q₀ : ℝ) ≤ (q₀ : ℝ) ^ (n * M) := by
    intro εT h
    have hpow : (0 : ℝ) ≤ (q₀ : ℝ) ^ (n * M) := pow_nonneg hq0 _
    unfold CtsMeasured.instCensus
    cases hwh : writeHeights? εT h with
    | none => simpa using hpow
    | some ε =>
      simp only [Option.map_some, Option.getD_some]
      unfold CtsMeasured.entCensus
      set Nε : ℕ := (ε.template?).elim 0 V.entLvl with hNε
      have h1 : (V.entInst ε β₀ q₀ Nε).card
          ≤ @Fintype.card (V.Box q₀ Nε) (V.finB q₀ Nε) :=
        @Finset.card_le_univ _ (V.finB q₀ Nε) _
      have h2 : ((@Fintype.card (V.Box q₀ Nε) (V.finB q₀ Nε) : ℚ)) = q₀ ^ (n * Nε) :=
        V.box_card q₀ hq Nε
      exact calc
          ((V.entInst ε β₀ q₀ Nε).card : ℝ)
              ≤ (@Fintype.card (V.Box q₀ Nε) (V.finB q₀ Nε) : ℝ) := by exact_mod_cast h1
          _ = ((q₀ ^ (n * Nε) : ℚ) : ℝ) := by exact_mod_cast h2
          _ = (q₀ : ℝ) ^ (n * Nε) := by push_cast; ring
          _ ≤ (q₀ : ℝ) ^ (n * M) := by
              apply pow_le_pow_right₀ hq1'
              exact Nat.mul_le_mul_left n (hlvl ε)
  -- the sigma summand and its nonnegativity
  set f : (Σ i : V.EntIx β₀,
      {h // ((V.entDom i.1.1).comps.get i.1.2).Mem h}) → ℝ :=
    fun p => ιshH V p.1.1.1 p.2.1 β₀ q₀ with hf_def
  have hnn : ∀ p, 0 ≤ f p := by
    intro p
    show 0 ≤ ιshH V p.1.1.1 p.2.1 β₀ q₀
    unfold ιshH
    exact mul_nonneg (Nat.cast_nonneg _) (zpow_nonneg hq0 _)
  -- PER FIBER: comparison against the q₀^{n·M}-scaled weight-only Gent sum
  have hfib : ∀ i : V.EntIx β₀,
      Summable (fun x : {h // ((V.entDom i.1.1).comps.get i.1.2).Mem h} =>
        f ⟨i, x⟩) := by
    intro i
    have hg : Summable
        (fun x : {h // ((V.entDom i.1.1).comps.get i.1.2).Mem h} =>
          (q₀ : ℝ) ^ (n * M) * (q₀ : ℝ) ^ (-((instA i.1.1 x.1 : ℕ) : ℤ))) :=
      ((XsEnt.Gent_hasSum β₀ i q₀ hq).mul_left ((q₀ : ℝ) ^ (n * M))).summable
    refine Summable.of_nonneg_of_le (fun x => hnn ⟨i, x⟩) (fun x => ?_) hg
    show ιshH V i.1.1 x.1 β₀ q₀ ≤ _
    unfold ιshH
    exact mul_le_mul_of_nonneg_right (hcb i.1.1 x.1) (zpow_nonneg hq0 _)
  -- SIGMA over the FINITE EntIx: nonneg criterion; the outer sum is a finite sum
  have hf : Summable f := by
    rw [summable_sigma_of_nonneg hnn]
    exact ⟨hfib, (hasSum_fintype _).summable⟩
  exact hf

end LeanUrat.MovesV
