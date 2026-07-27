/-
Unit U-24a1 `active_solve_meas` (medium) — REDESIGNED (Fable C1; R14): the
measured value IS the active-subsystem solve, PER POOL, guards consumed.
moves_ref: "(RS.1-DEEP) per block (e, τ): β_{e,τ}(σ′) = ((I − K_e)^{−1} b_e)_τ(σ′)"
+ "Every probabilistic claim in S.4/SQ.2 is about K_e restricted per CTS-M(ii) to
the ACTIVE block".  hyp: B.recursion_meas (W-3) + B.xrb + P (E0 inside) + L
(act_target + inactive_vanish give SUBSYSTEM CLOSURE).  sketch: β̂ := (βmeas ·)_Act
satisfies β̂ = Â β̂ + b̂ by recursion_meas restricted along the closure; (1 − Â)
invertible by U-21c on P.e0 (empty Act: trivial); uniqueness of the evaluated
solution.  NO induction, NO leg evaluation, NO hok claim — the legs enter b̂ as
measured values (D11: ℚ-matrix mapped ONCE through Aℝ, everything else ℝ).
CLOSES from the note's own display.
-/
import LeanUrat.MovesS.Interfaces
import LeanUrat.MovesS.SolveIff
import LeanUrat.MovesS.SolveExistsUnique
import LeanUrat.MovesS.E0DetNeZero

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Matrix

variable {n : ℕ}

/-- Under a kcol dispatch the outcome has exactly one member (c ≥ 1, m = 1). -/
private theorem kcol_m_one {V : Type*} {St : ℕ → Type*} (o : Outcome V St)
    (hk : routeOf o = .kcol) : o.mem.length = 1 := by
  unfold routeOf at hk
  by_cases h1 : o.c = 0
  · rw [if_pos h1] at hk; exact absurd hk (by decide)
  · rw [if_neg h1] at hk
    by_cases h2 : o.m = 1
    · exact h2
    · rw [if_neg h2] at hk; exact absurd hk (by decide)

/-- On a kcol outcome the hK-free existential of `kstep_one` (a continuing member of
block size `e` landing in `β`) is exactly the `kTarget = β` predicate of `Kmat`. -/
private theorem kcol_mem_iff {T : TableShape n} {e : ℕ} {τ : T.State e} {o : T.Out e τ}
    (hk : routeOf (T.odata e τ o) = .kcol)
    (hKmem : ∀ μ ∈ (T.odata e τ o).mem, μ.size = e) (β : T.State e) :
    (∃ μ ∈ (T.odata e τ o).mem, ∃ h : μ.size = e, h ▸ μ.status = Sum.inr β)
      ↔ kTarget T e τ o hk hKmem = β := by
  have hne : (T.odata e τ o).mem ≠ [] := (T.odata e τ o).hm
  have hlen : (T.odata e τ o).mem.length = 1 := kcol_m_one _ hk
  set head := (T.odata e τ o).mem.head hne with hhead
  have hhsz : head.size = e := hKmem head (List.head_mem hne)
  have kt_iff : kTarget T e τ o hk hKmem = β ↔ (hhsz ▸ head.status = Sum.inr β) := by
    rw [Sum.eq_right_iff_getRight_eq]; unfold kTarget
    constructor
    · intro h; exact ⟨_, h⟩
    · rintro ⟨h', hh'⟩; rw [← hh']
  rw [kt_iff]
  constructor
  · rintro ⟨μ, hμmem, h, hstat⟩
    obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp hlen
    have e1 : μ = b := by rw [hb, List.mem_singleton] at hμmem; exact hμmem
    have e2 : head = b := by rw [hhead]; simp [hb]
    have hμhead : μ = head := by rw [e1, e2]
    subst hμhead; rw [proof_irrel h hhsz] at hstat; exact hstat
  · intro hstat; exact ⟨head, List.head_mem hne, hhsz, hstat⟩

/-- The (K-COL) tie: at an active source `τ`, the measured one-step in-block mass to
`β` equals the evaluated symbolic kernel entry `K_e(τ, β)` (via `kstep_one`, the
`Kmat`/`kTarget` agreement above, and `tg_interp` per non-split column). -/
private theorem kstep_eq_evalKmat {T : TableShape n} {M : MeasuredSide T}
    (RB : RatBurdens T M) (L : LedgerIV T M) {e : ℕ} (hK : KmatHyp T e)
    (τ β : T.State e) {q₀ : ℚ} (hq : q₀ ∈ M.Pools) (hact : M.activeState q₀ e τ)
    (hok : Kmat T RB e hK τ β ∈ OKat q₀) :
    M.kstep 1 e τ β q₀ = ((evalAt q₀ ⟨Kmat T RB e hK τ β, hok⟩ : ℚ) : ℝ) := by
  classical
  set term : T.Out e τ → Qq := fun o =>
    if hk : routeOf (T.odata e τ o) = .kcol then
      (if kTarget T e τ o hk (hK τ o hk) = β then RB.TG e τ o else 0) else 0 with hterm
  have hKmat : Kmat T RB e hK τ β = ∑ o : T.Out e τ, term o := rfl
  have hmem : ∀ o : T.Out e τ, term o ∈ OKat q₀ := by
    intro o; simp only [hterm]
    split
    · split
      · exact RB.tg_ok e τ o q₀ hq
      · exact zero_mem _
    · exact zero_mem _
  have hsum : (⟨Kmat T RB e hK τ β, hok⟩ : OKat q₀)
      = ∑ o : T.Out e τ, (⟨term o, hmem o⟩ : OKat q₀) := by
    apply Subtype.ext; simp only [AddSubmonoidClass.coe_finsetSum]; exact hKmat
  rw [hsum, map_sum]; push_cast
  rw [L.kstep_one e τ β q₀ hq hact, Set.toFinset_setOf, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro o _
  by_cases hk : routeOf (T.odata e τ o) = .kcol
  · by_cases hkt : kTarget T e τ o hk (hK τ o hk) = β
    · have ht : term o = RB.TG e τ o := by simp only [hterm, dif_pos hk, if_pos hkt]
      have hval : (⟨term o, hmem o⟩ : OKat q₀) = ⟨(RB.tgP e τ o).val, RB.tg_ok e τ o q₀ hq⟩ :=
        Subtype.ext ht
      rw [if_pos ⟨hk, (kcol_mem_iff hk (hK τ o hk) β).mpr hkt⟩, hval]
      exact (RB.tg_interp e τ o q₀ hq (by rw [hk]; decide)).symm
    · have ht : term o = 0 := by simp only [hterm, dif_pos hk, if_neg hkt]
      have hval : (⟨term o, hmem o⟩ : OKat q₀) = 0 := Subtype.ext ht
      rw [hval, map_zero, Rat.cast_zero, if_neg]
      rintro ⟨_, hex⟩; exact hkt ((kcol_mem_iff hk (hK τ o hk) β).mp hex)
  · have ht : term o = 0 := by simp only [hterm, dif_neg hk]
    have hval : (⟨term o, hmem o⟩ : OKat q₀) = 0 := Subtype.ext ht
    rw [hval, map_zero, Rat.cast_zero, if_neg]
    rintro ⟨hk', _⟩; exact hk hk'

/-- The D11 det transport (R19: `RingHom.map_det` + `Rat.cast_injective`). -/
theorem Aℝ_det_iff {T : TableShape n} {M : MeasuredSide T} {RB : RatBurdens T M}
    {e : ℕ} {hK : KmatHyp T e} {q₀ : ℚ} (P : PoolHyp T M RB e hK q₀) :
    (1 - Aℝ P).det ≠ 0 ↔ (1 - P.A).det ≠ 0 := by
  have hmap : (1 - P.A).map (algebraMap ℚ ℝ) = 1 - Aℝ P := by
    rw [← RingHom.mapMatrix_apply, map_sub, map_one, RingHom.mapMatrix_apply, Aℝ]
  rw [← hmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ne_eq, ne_eq,
    map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective ℚ ℝ)]

theorem active_solve_meas {T : TableShape n} {M : MeasuredSide T}
    {RB : RatBurdens T M} {hdc : DegCons T}
    {hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e}
    (B : RS1Bundle T M RB hdc hK) (L : LedgerIV T M)
    {e : ℕ} (he : e ∈ Finset.Icc 1 n) {q₀ : ℚ}
    (P : PoolHyp T M RB e (hK e he) q₀)
    (σ' : Multiset T.VType) (h_ent : ℕ) (τA : P.Act) :
    B.βmeas e he h_ent (↑τA) σ' q₀
      = ((1 - Aℝ P)⁻¹ *ᵥ bhatMeas P (fun e' he' => B.βmeas e' he' h_ent) σ') τA := by
  classical
  -- (1 − Â) is nonsingular over ℝ: U-21c on P.e0, transported by D11's det bridge.
  have hdetℝ : (1 - Aℝ P).det ≠ 0 := (Aℝ_det_iff P).mpr (e0_det_ne_zero P.e0)
  -- β̂ := the Act-restricted measured vector; b̂ := the evaluated exit vector.
  set βvec : P.Act → ℝ := fun γ => B.βmeas e he h_ent γ.1 σ' q₀ with hβvecdef
  set bvec : P.Act → ℝ := bhatMeas P (fun e' he' => B.βmeas e' he' h_ent) σ' with hbvecdef
  -- SUBSYSTEM CLOSURE: recursion_meas at each active τ becomes β̂ = Â β̂ + b̂.
  have hfix : βvec = Aℝ P *ᵥ βvec + bvec := by
    funext τ
    have hactτ : M.activeState q₀ e τ.1 := (P.act_spec τ.1).mp τ.2
    have hrec := B.recursion_meas e he τ.1 σ' q₀ P.pool_mem hactτ h_ent
    -- the measured K-row sum (over ALL states) is the Â-row sum (over Act): inactive
    -- columns carry no mass (act_target), active ones match K_e (kstep_eq_evalKmat).
    have hsumeq : (∑ β : T.State e, M.kstep 1 e τ.1 β q₀ * B.βmeas e he h_ent β σ' q₀)
        = (Aℝ P *ᵥ βvec) τ := by
      set f : T.State e → ℝ := fun β => M.kstep 1 e τ.1 β q₀ * B.βmeas e he h_ent β σ' q₀
        with hf
      have hR : (Aℝ P *ᵥ βvec) τ = ∑ γ : P.Act, f (γ : T.State e) := by
        change (∑ γ : P.Act, Aℝ P τ γ * βvec γ) = ∑ γ : P.Act, f (γ : T.State e)
        refine Finset.sum_congr rfl (fun γ _ => ?_)
        simp only [hf]
        congr 1
        rw [Aℝ, Matrix.map_apply, P.A_eval, eq_ratCast]
        exact (kstep_eq_evalKmat RB L (hK e he) τ.1 γ.1 P.pool_mem hactτ
          (P.entry_ok τ.1 γ.1 τ.2 γ.2)).symm
      rw [hR, Finset.sum_coe_sort P.Act f]
      refine (Finset.sum_subset (Finset.subset_univ P.Act) ?_).symm
      intro x _ hxnotAct
      have hxn : ¬ M.activeState q₀ e x := fun h => hxnotAct ((P.act_spec x).mpr h)
      simp only [L.act_target e τ.1 x q₀ P.pool_mem hxn, zero_mul]
    have hstep : βvec τ
        = evalRe T M RB hdc e he τ.1 σ' q₀ (fun e' he' => B.βmeas e' he' h_ent) := hrec
    change βvec τ = (Aℝ P *ᵥ βvec) τ + bvec τ
    rw [hstep, show evalRe T M RB hdc e he τ.1 σ' q₀ (fun e' he' => B.βmeas e' he' h_ent)
        = (∑ β : T.State e, M.kstep 1 e τ.1 β q₀ * B.βmeas e he h_ent β σ' q₀)
          + bTermMeas T M e σ' q₀ τ.1
          + bSplitMeas T M e σ' q₀ (fun e' he' => B.βmeas e' he' h_ent) τ.1 from rfl,
      hsumeq,
      show bvec τ = bTermMeas T M e σ' q₀ τ.1
          + bSplitMeas T M e σ' q₀ (fun e' he' => B.βmeas e' he' h_ent) τ.1 from rfl]
    ring
  -- solve: β̂ = Â β̂ + b̂ ⟺ (1 − Â) β̂ = b̂ ⟹ β̂ = (1 − Â)⁻¹ b̂ (nonsingular).
  have hlin : (1 - Aℝ P) *ᵥ βvec = bvec := (solve_iff (Aℝ P) bvec βvec).mp hfix
  have hdetU : IsUnit (1 - Aℝ P).det := isUnit_iff_ne_zero.mpr hdetℝ
  have hsol : βvec = (1 - Aℝ P)⁻¹ *ᵥ bvec := by
    calc βvec = (1 - Aℝ P)⁻¹ *ᵥ ((1 - Aℝ P) *ᵥ βvec) := by
              rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ hdetU, one_mulVec]
      _ = (1 - Aℝ P)⁻¹ *ᵥ bvec := by rw [hlin]
  exact congrFun hsol τA

end LeanUrat.MovesS
