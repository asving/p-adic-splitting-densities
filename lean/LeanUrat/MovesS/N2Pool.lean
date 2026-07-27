/-
Unit U-29c `n2_pool` (easy) — PoolHyp at q₀ = 2; EscapeE0 for A = [1/8]:
geometric decay (`tendsto_pow_atTop_nhds_zero_of_lt_one`).  The 1/8 entry is
`msW_eighth_le`'s p = 2 ratio shadow.

The 1×1 block at e = 2, q₀ = 2: `n2T.State 2 = Unit`, so `Act = univ` is a
singleton; the kernel entry is `Kmat n2τ n2τ = (n2RB.tgP 2 n2τ n2oK).val = qX⁻¹^3`
(only o_K is kcol, `n2_polygeom_data`), whose value at q₀ = 2 is `2⁻³ = 1/8`.  The
escape leg is the scalar geometric decay `(1/8)^k → 0` transported through the
1×1 matrix power by a `Unique`-index induction.
-/
import LeanUrat.MovesS.N2PolyGeom
import LeanUrat.MovesS.N2ScsData
import LeanUrat.MovesS.N2PoolsData
import LeanUrat.MovesS.N2Activity

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

open Polynomial

/-! ### Scalar facts about the symbolic variable `qX` and its evaluation at 2. -/

private lemma qX_ne : qX ≠ 0 := by unfold qX; simp [RatFunc.X_ne_zero]

private lemma qX_mem : qX ∈ OKat 2 := by rw [mem_OKat_iff]; unfold qX; simp

private lemma eval_qX : evalAt 2 ⟨qX, qX_mem⟩ = 2 := by
  change RatFunc.eval (RingHom.id ℚ) 2 qX = 2
  unfold qX; simp

private lemma two_mem_pools : (2 : ℚ) ∈ n2M.Pools := by
  rw [n2_pools]; exact ⟨2, by norm_num, 1, by norm_num⟩

private lemma hqcube_mem : qX⁻¹ ^ 3 ∈ OKat 2 := by
  have h := n2RB.tg_ok 2 n2τ n2oK 2 two_mem_pools
  rwa [n2_polygeom_data.1] at h

/-- `evalAt 2 (q⁻³) = 1/8`: the ring-hom collapse `8 · e = e(q³·q⁻³) = e(1) = 1`. -/
private lemma eval_qX_inv_cube (h : qX⁻¹ ^ 3 ∈ OKat 2) :
    evalAt 2 ⟨qX⁻¹ ^ 3, h⟩ = 1 / 8 := by
  have hmul : (⟨qX, qX_mem⟩ : OKat 2) ^ 3 * ⟨qX⁻¹ ^ 3, h⟩ = 1 := by
    apply Subtype.ext; push_cast
    rw [← mul_pow, mul_inv_cancel₀ qX_ne, one_pow]
  have happ := congrArg (evalAt 2) hmul
  rw [map_mul, map_pow, map_one, eval_qX] at happ
  have h8 : (8 : ℚ) * evalAt 2 ⟨qX⁻¹ ^ 3, h⟩ = 1 := by rw [← happ]; norm_num
  linarith

/-! ### The 1×1 kernel entry and its value. -/

variable (hK : KmatHyp n2T 2)

/-- Only o_K is kcol, and its target is the single state, so the whole kernel column
collapses to the o_K burden `(n2RB.tgP 2 n2τ n2oK).val`. -/
private lemma kmat_val :
    Kmat n2T n2RB 2 hK n2τ n2τ = (n2RB.tgP 2 n2τ n2oK).val := by
  obtain ⟨hrK, hrSpl, hrIn, -, -, -, -, hroster, -, hstate2, -, -⟩ := n2_shape
  unfold Kmat
  rw [Finset.sum_eq_single n2oK]
  · rw [dif_pos hrK, if_pos (hstate2 _)]
  · intro b _ hb
    rcases hroster b with h | h | h
    · exact absurd h hb
    · subst h; exact dif_neg (by rw [hrSpl]; decide)
    · subst h; exact dif_neg (by rw [hrIn]; decide)
  · intro h; exact absurd (Finset.mem_univ n2oK) h

private lemma kmat_qX : Kmat n2T n2RB 2 hK n2τ n2τ = qX⁻¹ ^ 3 := by
  rw [kmat_val hK, n2_polygeom_data.1]

private lemma kmat_mem : Kmat n2T n2RB 2 hK n2τ n2τ ∈ OKat 2 := by
  rw [kmat_val hK]; exact n2RB.tg_ok 2 n2τ n2oK 2 two_mem_pools

private lemma eval_kmat (hmem : Kmat n2T n2RB 2 hK n2τ n2τ ∈ OKat 2) :
    evalAt 2 ⟨Kmat n2T n2RB 2 hK n2τ n2τ, hmem⟩ = 1 / 8 := by
  have heq : (⟨Kmat n2T n2RB 2 hK n2τ n2τ, hmem⟩ : OKat 2) = ⟨qX⁻¹ ^ 3, hqcube_mem⟩ :=
    Subtype.ext (kmat_qX hK)
  rw [heq, eval_qX_inv_cube]

/-! ### The active subsystem: `Act = univ`, the evaluated 1×1 matrix, its escape. -/

/-- Every `Act`-indexed kernel entry is regular at q₀ = 2 (`State 2 = Unit`, so all
indices are `n2τ`). -/
private def n2entry_ok :
    ∀ (τ β : n2T.State 2), τ ∈ (Finset.univ : Finset (n2T.State 2)) → β ∈ Finset.univ →
      Kmat n2T n2RB 2 hK τ β ∈ OKat 2 :=
  fun _ _ _ _ => kmat_mem hK

/-- The active matrix `Aℚ`, pinned to the `evalAt`-of-kernel shape `A_eval` demands. -/
noncomputable def n2A :
    Matrix ↥(Finset.univ : Finset (n2T.State 2)) ↥(Finset.univ : Finset (n2T.State 2)) ℚ :=
  fun τ β => evalAt 2 ⟨Kmat n2T n2RB 2 hK τ.1 β.1, n2entry_ok hK τ.1 β.1 τ.2 β.2⟩

private lemma n2A_val (i j) : n2A hK i j = 1 / 8 := eval_kmat hK _

open scoped Matrix in
/-- ESCAPE(E0) for the 1×1 matrix `[1/8]`: nonneg is `0 ≤ 1/8`; escape is the scalar
`(1/8)^k → 0` carried through matrix powers by a `Unique`-index induction. -/
private lemma n2escape : EscapeE0 (n2A hK) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hstate2, _, _⟩ := n2_shape
  haveI huniq : Unique ↥(Finset.univ : Finset (n2T.State 2)) :=
    ⟨⟨⟨n2τ, Finset.mem_univ _⟩⟩, fun x => Subtype.ext (hstate2 x.1)⟩
  refine ⟨?_, ?_⟩
  · intro i j; rw [n2A_val]; norm_num
  · have haux : ∀ k (i : ↥(Finset.univ : Finset (n2T.State 2))),
        (n2A hK ^ k *ᵥ (fun _ => (1 : ℚ))) i = (1 / 8) ^ k := by
      intro k
      induction k with
      | zero => intro i; simp
      | succ n ih =>
        intro i
        have hstep : (n2A hK ^ (n + 1) *ᵥ (fun _ => (1 : ℚ))) i
                   = ∑ j, n2A hK i j * (n2A hK ^ n *ᵥ (fun _ => (1 : ℚ))) j := by
          rw [pow_succ', ← Matrix.mulVec_mulVec]; rfl
        rw [hstep]; simp only [n2A_val, ih]
        rw [Fintype.sum_unique, ← pow_succ']
    rw [tendsto_pi_nhds]; intro i; simp only [Pi.zero_apply]
    have hfun : (fun k => (n2A hK ^ k *ᵥ (fun _ => (1 : ℚ))) i) = (fun k => ((1 : ℚ) / 8) ^ k) := by
      funext k; exact haux k i
    rw [hfun]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- The per-pool package at q₀ = 2, e = 2: the all-active singleton subsystem carrying
the evaluated 1×1 kernel `[1/8]` and its ESCAPE(E0) leg. -/
noncomputable def n2P2 : PoolHyp n2T n2M n2RB 2 (n2hK 2 (by decide)) 2 where
  pool_mem := two_mem_pools
  Act := Finset.univ
  act_spec := fun τ => ⟨fun _ => n2_activity.2.2 2 2 τ, fun _ => Finset.mem_univ τ⟩
  entry_ok := n2entry_ok (n2hK 2 (by decide))
  A := n2A (n2hK 2 (by decide))
  A_eval := fun τ β => rfl
  inactive_vanish := fun τ β hok _ hβ => absurd (Finset.mem_univ β) hβ
  e0 := n2escape (n2hK 2 (by decide))

theorem n2_pool :
    (∀ τA βA : n2P2.Act, n2P2.A τA βA = 1 / 8) ∧ n2P2.Act = Finset.univ :=
  ⟨fun τA βA => n2A_val (n2hK 2 (by decide)) τA βA, rfl⟩

end LeanUrat.MovesS
