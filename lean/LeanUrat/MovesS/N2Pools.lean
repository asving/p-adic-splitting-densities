/-
Unit U-29d2 `n2_pools_all` (medium) — legs_reg/pools_e0 at EVERY base prime:
1×1 packages, entry q₀⁻³ < 1 uniformly at q₀ ≥ 2.  consumedDeltas = {1} at this
instance (n2_shapefam), so RegP reduces to the base pools themselves.

Construction: at each prime p and block e ∈ {1,2} the state space is a singleton
(`n2T.State e = Unit`), so the active kernel is 1×1.  At e = 1 there is no kcol
outcome, so the kernel entry is 0; at e = 2 the single kcol outcome (o_K)
evaluates to q₀⁻³ (via `tg_interp` + `n2_events`).  Both entries lie in [0, 1),
so ESCAPE(E0) holds by geometric decay of a subsingleton matrix's diagonal power.
-/
import LeanUrat.MovesS.N2Pool
import LeanUrat.MovesS.N2ShapeFam
import LeanUrat.MovesS.N2Activity
import LeanUrat.MovesS.N2Events
import LeanUrat.MovesS.N2PoolsData

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Matrix

/-- ESCAPE(E0) for a subsingleton-indexed matrix: with all entries `≥ 0` and every
diagonal entry `< 1`, the powers `Aᵏ *ᵥ 1` decay to `0` (geometric, since on a
subsingleton index `(Aᵏ) i i = (A i i)ᵏ`). -/
private lemma escapeE0_subsingleton {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hss : Subsingleton ι) (A : Matrix ι ι ℚ) (hnn : ∀ i j, 0 ≤ A i j)
    (hlt : ∀ i, A i i < 1) : EscapeE0 A := by
  haveI := hss
  refine ⟨hnn, ?_⟩
  rw [tendsto_pi_nhds]
  intro i
  have hdiag : ∀ k, (A ^ k) i i = (A i i) ^ k := by
    intro k
    induction k with
    | zero => simp [Matrix.one_apply_eq]
    | succ m ih =>
        rw [pow_succ, Matrix.mul_apply, Fintype.sum_subsingleton _ i, ih]
        ring
  have hmv : ∀ k, ((A ^ k) *ᵥ (fun _ => (1 : ℚ))) i = (A i i) ^ k := by
    intro k
    have h1 : ((A ^ k) *ᵥ (fun _ => (1 : ℚ))) i = ∑ j, (A ^ k) i j := by
      simp [Matrix.mulVec, dotProduct]
    rw [h1, Fintype.sum_subsingleton _ i, hdiag k]
  simp only [Pi.zero_apply]
  refine Filter.Tendsto.congr (fun k => (hmv k).symm) ?_
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (hnn i i) (hlt i)

/-- The uniform per-pool package builder: given the pool membership, all-active data,
the singleton-state fact and the diagonal-entry bound `0 ≤ · < 1`, assemble the
`PoolHyp` (active locus = everything, kernel evaluated at the prime, ESCAPE via
`escapeE0_subsingleton`). -/
private noncomputable def mkPool (p : ℕ) (e : ℕ) (he : e ∈ Finset.Icc 1 2)
    (hmem_pool : (p : ℚ) ∈ n2M.Pools)
    (hact : ∀ (τ : n2T.State e), n2M.activeState (p : ℚ) e τ)
    (hss : Subsingleton (n2T.State e))
    (hbound : ∀ (s : n2T.State e) (h : Kmat n2T n2RB e (n2hK e he) s s ∈ OKat (p : ℚ)),
        0 ≤ (evalAt (p : ℚ) ⟨_, h⟩ : ℚ) ∧ (evalAt (p : ℚ) ⟨_, h⟩ : ℚ) < 1) :
    PoolHyp n2T n2M n2RB e (n2hK e he) (p : ℚ) := by
  haveI := hss
  have hok : ∀ (τ β : n2T.State e), Kmat n2T n2RB e (n2hK e he) τ β ∈ OKat (p : ℚ) := by
    intro τ β
    simp only [Kmat]
    refine Subring.sum_mem _ (fun o _ => ?_)
    by_cases hk : routeOf (n2T.odata e τ o) = .kcol
    · rw [dif_pos hk]
      by_cases hb : kTarget n2T e τ o hk (n2hK e he τ o hk) = β
      · rw [if_pos hb]; exact n2RB.tg_ok e τ o (p : ℚ) hmem_pool
      · rw [if_neg hb]; exact Subring.zero_mem _
    · rw [dif_neg hk]; exact Subring.zero_mem _
  refine
    { pool_mem := hmem_pool
      Act := Finset.univ
      act_spec := fun τ => ⟨fun _ => hact τ, fun _ => Finset.mem_univ τ⟩
      entry_ok := fun τ β _ _ => hok τ β
      A := fun τ β => evalAt (p : ℚ) ⟨Kmat n2T n2RB e (n2hK e he) τ.1 β.1, hok τ.1 β.1⟩
      A_eval := fun τ β => rfl
      inactive_vanish := fun τ β _ _ hβ => absurd (Finset.mem_univ β) hβ
      e0 := ?_ }
  haveI hsub : Subsingleton ↥(Finset.univ : Finset (n2T.State e)) :=
    ⟨fun a b => Subtype.ext (Subsingleton.elim a.1 b.1)⟩
  refine escapeE0_subsingleton hsub _ ?_ ?_
  · intro i j
    have hji : j = i := Subsingleton.elim j i
    rw [hji]
    exact (hbound i.1 (hok i.1 i.1)).1
  · intro i
    exact (hbound i.1 (hok i.1 i.1)).2

/-- The per-prime, per-block package: a `PoolHyp` at `q₀ = p` for every prime `p`
and every `e ∈ {1,2}`.  Both conjuncts of `n2_pools_all` are read off this. -/
private lemma n2_pool_at (p : ℕ) (hp : p.Prime) (e : ℕ) (he : e ∈ Finset.Icc 1 2) :
    Nonempty (PoolHyp n2T n2M n2RB e (n2hK e he) (p : ℚ)) := by
  obtain ⟨hrK, hrSpl, hrIn, _, _, _, _, hexh, _, hstate2, hstate1, hlayer1⟩ := n2_shape
  have hp1 : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have hmem_pool : (p : ℚ) ∈ n2M.Pools := by
    rw [n2_pools]; exact ⟨p, hp, 1, by rw [PNat.one_coe, pow_one]⟩
  obtain ⟨-, -, hactAll⟩ := n2_activity
  obtain ⟨hb1, hb2⟩ := Finset.mem_Icc.mp he
  interval_cases e
  · -- e = 1: the block-1 layer has no kcol outcome, so the kernel entry is 0.
    refine ⟨mkPool p 1 he hmem_pool (fun τ => hactAll (p : ℚ) 1 τ)
      ⟨fun a b => hstate1 a b⟩ ?_⟩
    intro s h
    have hKval : Kmat n2T n2RB 1 (n2hK 1 he) s s = 0 := by
      simp only [Kmat]
      apply Finset.sum_eq_zero
      intro o _
      rw [dif_neg (show ¬ (routeOf (n2T.odata 1 s o) = Route.kcol) from by
        rw [(hlayer1 s o).1]; decide)]
    have hsub : (⟨Kmat n2T n2RB 1 (n2hK 1 he) s s, h⟩ : OKat (p : ℚ)) = 0 :=
      Subtype.ext hKval
    rw [hsub, map_zero]
    exact ⟨le_refl 0, by norm_num⟩
  · -- e = 2: the single kcol outcome o_K evaluates to q₀⁻³ < 1.
    haveI hss2 : Subsingleton (n2T.State 2) :=
      ⟨fun a b => (hstate2 a).trans (hstate2 b).symm⟩
    refine ⟨mkPool p 2 he hmem_pool (fun τ => hactAll (p : ℚ) 2 τ) hss2 ?_⟩
    intro s h
    have hs : s = n2τ := hstate2 s
    subst hs
    have hKval : Kmat n2T n2RB 2 (n2hK 2 he) n2τ n2τ = (n2RB.tgP 2 n2τ n2oK).val := by
      simp only [Kmat]
      rw [Finset.sum_eq_single n2oK]
      · rw [dif_pos hrK, if_pos (Subsingleton.elim _ _)]
      · intro b _ hbne
        rcases hexh b with hh | hh | hh
        · exact absurd hh hbne
        · subst hh; rw [dif_neg (show ¬ (routeOf (n2T.odata 2 n2τ n2oSpl) = Route.kcol) from by
            rw [hrSpl]; decide)]
        · subst hh; rw [dif_neg (show ¬ (routeOf (n2T.odata 2 n2τ n2oIn) = Route.kcol) from by
            rw [hrIn]; decide)]
      · intro hh; exact absurd (Finset.mem_univ n2oK) hh
    have hsub : (⟨Kmat n2T n2RB 2 (n2hK 2 he) n2τ n2τ, h⟩ : OKat (p : ℚ))
        = ⟨(n2RB.tgP 2 n2τ n2oK).val, n2RB.tg_ok 2 n2τ n2oK (p : ℚ) hmem_pool⟩ :=
      Subtype.ext hKval
    rw [hsub]
    have hns : routeOf (n2T.odata 2 n2τ n2oK) ≠ Route.split := by rw [hrK]; decide
    have htg := n2RB.tg_interp 2 n2τ n2oK (p : ℚ) hmem_pool hns
    have hev := (n2_events (p : ℚ) hmem_pool).1
    have ha : evalAt (p : ℚ) ⟨(n2RB.tgP 2 n2τ n2oK).val, n2RB.tg_ok 2 n2τ n2oK (p : ℚ) hmem_pool⟩
        = (p : ℚ)⁻¹ ^ 3 := by
      have hcast :
          ((evalAt (p : ℚ) ⟨(n2RB.tgP 2 n2τ n2oK).val,
              n2RB.tg_ok 2 n2τ n2oK (p : ℚ) hmem_pool⟩ : ℚ) : ℝ)
            = (((p : ℚ)⁻¹ ^ 3 : ℚ) : ℝ) := by
        rw [htg, hev]; push_cast; ring
      exact_mod_cast hcast
    rw [ha]
    refine ⟨by positivity, ?_⟩
    have hpinv_pos : (0 : ℚ) < (p : ℚ)⁻¹ := by positivity
    exact pow_lt_one₀ (le_of_lt hpinv_pos) (inv_lt_one_of_one_lt₀ hp1) (by norm_num)

theorem n2_pools_all :
    (∀ p : ℕ, p.Prime → RegP n2T n2M n2RB p n2hK n2F) ∧
    (∀ e (he : e ∈ Finset.Icc 1 2), ∀ q₀ : ℚ, (∃ p : ℕ, p.Prime ∧ q₀ = (p : ℚ)) →
      Nonempty (PoolHyp n2T n2M n2RB e (n2hK e he) q₀)) := by
  refine ⟨?_, ?_⟩
  · intro p hp e he δ hδ
    have hδ1 : δ = 1 := by
      have hcd := n2_shapefam.2.2
      rw [hcd] at hδ
      exact Finset.mem_singleton.mp hδ
    subst hδ1
    rw [PNat.one_coe, pow_one]
    exact n2_pool_at p hp e he
  · rintro e he q₀ ⟨p, hp, rfl⟩
    exact n2_pool_at p hp e he

end LeanUrat.MovesS
