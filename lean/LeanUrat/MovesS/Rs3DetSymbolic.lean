/-
Unit U-22 `rs3_det_symbolic` (medium) — E0 RE-SCOPED to all-active BASE pools
(R51, Codex#8-2): the note demands E0 at base pools + consumed legs (legs_reg),
NEVER at every prime-power pool.  moves_ref: "at all-active primes (cofinitely
many …) K_e(p) = A and ρ(A) < 1 gives det(I − A) ≠ 0; a rational function
vanishing at infinitely many prime evaluations is 0".  deps: U-19, U-20, U-21c,
U-22b, U-22c, U-27 (R58).  sketch: at an all-active base pool Act = univ
(act_spec + the locus); if det = 0 in Qq its evaluation vanishes there (U-20),
contradicting U-21c; U-22b/U-22c + prime infinitude give infinitely many
all-active base pools.
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.EvalDet
import LeanUrat.MovesS.E0DetNeZero
import LeanUrat.MovesS.AllActivePrimes
import LeanUrat.MovesS.RatfuncEvalInfinite

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

variable {n : ℕ}

theorem rs3_det_symbolic {T : TableShape n} {M : MeasuredSide T}
    (RB : RatBurdens T M) (hdc : DegCons T)
    (hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e)
    (PP : Set ℚ) (hsub : PP ⊆ M.Pools)
    (hbase : ∀ q₀, q₀ ∈ PP ↔ ∃ p : ℕ, p.Prime ∧ q₀ = (p : ℚ))
    (hact : ∀ e (he : e ∈ Finset.Icc 1 n), ∀ q₀ ∈ PP ∩ allActivePools M,
      Nonempty (PoolHyp T M RB e (hK e he) q₀)) :
    ∀ e (he : e ∈ Finset.Icc 1 n), (1 - Kmat T RB e (hK e he)).det ≠ 0 := by
  -- The base-prime pools PP are infinite (there are infinitely many primes).
  have hPPinf : PP.Infinite := by
    have hPP_eq : PP = (Nat.cast : ℕ → ℚ) '' {p : ℕ | p.Prime} := by
      ext q
      simp only [hbase q, Set.mem_image, Set.mem_setOf_eq, eq_comm]
    rw [hPP_eq]
    exact Nat.infinite_setOf_prime.image (Set.injOn_of_injective Nat.cast_injective)
  -- Only finitely many base primes fail to be all-active (U-22c).
  have hFin : {q₀ ∈ PP | q₀ ∉ allActivePools M}.Finite :=
    allActive_cofinite_primes RB PP hsub hbase
  -- Hence there is at least one all-active base pool.
  have hsubset :
      PP \ {q₀ ∈ PP | q₀ ∉ allActivePools M} ⊆ PP ∩ allActivePools M := by
    rintro q ⟨hqPP, hbad⟩
    refine ⟨hqPP, ?_⟩
    by_contra hc
    exact hbad ⟨hqPP, hc⟩
  obtain ⟨q₀, hq₀⟩ := (Set.Infinite.mono hsubset (hPPinf.sdiff hFin)).nonempty
  -- Fix the block and assume the symbolic determinant vanishes.
  intro e he hDet
  obtain ⟨P⟩ := hact e he q₀ hq₀
  -- At the all-active pool every state is active, so `P.Act` is everything.
  have hallτ : ∀ τ : T.State e, M.activeState q₀ e τ := by
    have h2 : q₀ ∈ allActivePools M := hq₀.2
    simp only [allActivePools, Set.mem_setOf_eq] at h2
    exact fun τ => h2.2 e he τ
  have hAct : ∀ τ : T.State e, τ ∈ P.Act := fun τ => (P.act_spec τ).mpr (hallτ τ)
  have hEntry : ∀ τ β : T.State e, Kmat T RB e (hK e he) τ β ∈ OKat q₀ :=
    fun τ β => P.entry_ok τ β (hAct τ) (hAct β)
  -- The kernel lifted to the evaluation-regular subring at q₀.
  set K' : Matrix (T.State e) (T.State e) (OKat q₀) :=
    Matrix.of (fun τ β => (⟨Kmat T RB e (hK e he) τ β, hEntry τ β⟩ : OKat q₀)) with hK'
  -- The lifted determinant vanishes too (the subring inclusion is injective).
  have hdet0 : (1 - K').det = 0 := by
    have hmd := RingHom.map_det (Subring.subtype (OKat q₀)) (1 - K')
    rw [map_sub, map_one] at hmd
    have hKK : (Subring.subtype (OKat q₀)).mapMatrix K' = Kmat T RB e (hK e he) := by
      ext τ β
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hK', Matrix.of_apply,
        Subring.coe_subtype]
    rw [hKK, hDet] at hmd
    have hinj : Function.Injective ⇑(Subring.subtype (OKat q₀)) := by
      rw [Subring.coe_subtype]; exact Subtype.val_injective
    exact (map_eq_zero_iff _ hinj).mp hmd
  -- Evaluate at q₀: the evaluated determinant is the determinant of the evaluated matrix.
  have hED : evalAt q₀ ((1 - K').det) = ((1 - K').map (evalAt q₀)).det :=
    eval_det (1 - K')
  have hBdet : ((1 - K').map (evalAt q₀)).det = 0 := by
    rw [← hED, hdet0, map_zero]
  -- Reindex the evaluated matrix onto the active block, where it coincides with `P.A`.
  set ε : (↥P.Act) ≃ T.State e := Equiv.subtypeUnivEquiv hAct with hεdef
  have hBsub : ((1 - K').map (evalAt q₀)).submatrix ε ε = 1 - P.A := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.map_apply, Matrix.sub_apply, map_sub]
    congr 1
    · rw [Matrix.one_apply, Matrix.one_apply]
      by_cases h : i = j
      · subst h; rw [if_pos rfl, if_pos rfl, map_one]
      · have hne : ε i ≠ ε j := fun hc => h (ε.injective hc)
        rw [if_neg hne, if_neg h, map_zero]
    · rw [P.A_eval, hεdef]
      simp only [Equiv.subtypeUnivEquiv_apply, hK', Matrix.of_apply]
  -- But over ℝ the escaping active block is nonsingular (U-21c) — contradiction.
  have hchain : (1 - P.A).det = 0 := by
    rw [← hBsub, Matrix.det_submatrix_equiv_self ε]
    exact hBdet
  exact (e0_det_ne_zero P.e0) hchain

end LeanUrat.MovesS
