/-
Unit `n2_rsh` (medium; S5 chain batch) — rsh_interp at the explicit values:
eval β_{(1,2)} = (q₀+1)/(q₀²+q₀+1) etc., with the DEVICE WshP from
n2_wshp_device (the R44 scope contradiction is GONE: R46).  Also carries the
gate's discharge of `wsh17_pin` (:= the device W17ii height-sum instance —
NONTRIVIALLY discharged by n2_sh_laws' shweight_card at the singleton height;
at wave 4 the field is re-keyed to W17ii's real statement, R57).

P-phase notes (deviations recorded):
· `wsh17_pin`'s VALUE is the named Prop `n2Wsh17Device` (N2Sigmas.lean, owned by
  this unit): the §2.E W17ii display's conclusion at the device carriers.  Its
  height-sum face is discharged here DIRECTLY from the device data (shWeightH ≡ 1
  over shDom ≡ {0} sums to WshVal ≡ 1) — the R55 restatement of the
  shweight_card-at-the-singleton-height route named above.
· Clause 3 rides `rsh_interp` (clause 2's projection) + the explicit reduced solve
  value `n2_solve_vals` (import added for it): Rsh {(1,2)} collapses over the
  single root shape (k = 1, σ₀ = 0, δ = 1, WshP-value 1) to the blockSolve entry
  (q+1)/(q²+q+1), evaluated at p with denominator p²+p+1 > 0.
-/
import LeanUrat.MovesS.N2WshpDevice
import LeanUrat.MovesS.N2ShEvents
import LeanUrat.MovesS.N2ShLaws
import LeanUrat.MovesS.N2SolveVals

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Polynomial

-- Mirror N2Sigmas' instance discipline (the σ-roster Finset lives under it):
attribute [local instance 0] Classical.decEq

/-- `powSubst δ` on a polynomial image is the polynomial base-change `p ↦ p ∘ X^δ`
(local copy of PowSubstOK's private lemma). -/
private lemma powSubst_algebraMap' (δ : ℕ+) (p : Polynomial ℚ) :
    powSubst δ (algebraMap (Polynomial ℚ) Qq p)
      = algebraMap (Polynomial ℚ) Qq (p.comp (X ^ (δ : ℕ))) := by
  have hFG : (powSubst δ).comp (algebraMap (Polynomial ℚ) Qq)
      = (algebraMap (Polynomial ℚ) Qq).comp
          (Polynomial.eval₂RingHom Polynomial.C (X ^ (δ : ℕ))) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
        RatFunc.algebraMap_C, powSubst_C]
    · simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
        powSubst_X]
  have h := RingHom.congr_fun hFG p
  simpa only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.comp] using h

/-- δ = 1 substitution is the identity (the root shape's δ ≡ 1 leg). -/
private theorem powSubst_one (f : Qq) : powSubst 1 f = f := by
  conv_lhs => rw [← RatFunc.num_div_denom f]
  rw [map_div₀, powSubst_algebraMap', powSubst_algebraMap']
  simp [RatFunc.num_div_denom]

/-- Evaluation of a polynomial fraction `p/q` at `x` is `p.eval x / q.eval x`
whenever `q.eval x ≠ 0` (local copy of PowSubstOK's private lemma). -/
private lemma eval_algebraMap_div' (x : ℚ) (p q : Polynomial ℚ) (hq : q.eval x ≠ 0) :
    RatFunc.eval (RingHom.id ℚ) x
        (algebraMap (Polynomial ℚ) Qq p / algebraMap (Polynomial ℚ) Qq q)
      = p.eval x / q.eval x := by
  have hq0 : q ≠ 0 := fun h0 => hq (by rw [h0]; simp)
  have hqne : algebraMap (Polynomial ℚ) Qq q ≠ 0 := RatFunc.algebraMap_ne_zero hq0
  have hdvd : (algebraMap (Polynomial ℚ) Qq p
      / algebraMap (Polynomial ℚ) Qq q).denom ∣ q :=
    (RatFunc.denom_dvd hq0).mpr ⟨p, rfl⟩
  have hgden : Polynomial.eval₂ (RingHom.id ℚ) x
      (algebraMap (Polynomial ℚ) Qq p / algebraMap (Polynomial ℚ) Qq q).denom ≠ 0 := by
    rw [Polynomial.eval₂_id]
    obtain ⟨c, hc⟩ := hdvd
    intro hz
    exact hq (by rw [hc, Polynomial.eval_mul, hz, zero_mul])
  have hden_q : Polynomial.eval₂ (RingHom.id ℚ) x
      (algebraMap (Polynomial ℚ) Qq q).denom ≠ 0 := by
    rw [RatFunc.denom_algebraMap]; simp
  have epq : RatFunc.eval (RingHom.id ℚ) x (algebraMap (Polynomial ℚ) Qq p) = p.eval x := by
    rw [RatFunc.eval_algebraMap]; simp [Polynomial.eval₂_id]
  have eqq : RatFunc.eval (RingHom.id ℚ) x (algebraMap (Polynomial ℚ) Qq q) = q.eval x := by
    rw [RatFunc.eval_algebraMap]; simp [Polynomial.eval₂_id]
  have hmul : (algebraMap (Polynomial ℚ) Qq p / algebraMap (Polynomial ℚ) Qq q)
      * algebraMap (Polynomial ℚ) Qq q = algebraMap (Polynomial ℚ) Qq p :=
    div_mul_cancel₀ _ hqne
  have key := congrArg (RatFunc.eval (RingHom.id ℚ) x) hmul
  rw [RatFunc.eval_mul (RingHom.id ℚ) x hgden hden_q, epq, eqq] at key
  rw [eq_div_iff hq]
  exact key

/-- The shallow convolution at the root shape (k = 1, σ₀ = 0, δ = 1) collapses to
the single δ = 1 blockSolve leg at σ = {(1,2)}. -/
private theorem n2_shconv (hdet : DetHyp n2T n2RB n2hK) (he2 : 2 ∈ Finset.Icc 1 2) :
    shConv n2T n2M n2RB n2hdc n2hK hdet n2RootShape {n2v12}
      = powSubst 1 (blockSolve n2T n2RB n2hdc n2hK n2hdet 2 he2 n2τ {n2v12}) := by
  unfold shConv
  have hsumF : ∀ F : Fin n2RootShape.k → Multiset n2T.VType, (∑ i, F i) = F (0 : Fin 1) :=
    fun F => Fin.sum_univ_one F
  have hprop : ({n2v12} : Multiset n2T.VType)
      = n2RootShape.σ0 + ∑ i : Fin n2RootShape.k,
          (fun _ => ({n2v12} : Multiset n2T.VType)) i := by
    rw [hsumF]
    show ({n2v12} : Multiset n2T.VType) = 0 + {n2v12}
    rw [zero_add]
  refine Eq.trans (Fintype.sum_eq_single ⟨fun _ => {n2v12}, hprop⟩ ?_) ?_
  · rintro ⟨g, hg⟩ hne
    exfalso
    apply hne
    have hg0 : g (0 : Fin 1) = ({n2v12} : Multiset n2T.VType) := by
      have h2 := hg
      rw [hsumF] at h2
      have h3 : ({n2v12} : Multiset n2T.VType) = 0 + g (0 : Fin 1) := h2
      rw [zero_add] at h3
      exact h3.symm
    apply Subtype.ext
    funext i
    have hi : i = ((0 : Fin 1) : Fin n2RootShape.k) := by
      haveI hs : Subsingleton (Fin n2RootShape.k) := by
        have hk : n2RootShape.k = 1 := rfl
        rw [hk]; infer_instance
      exact Subsingleton.elim i _
    rw [hi]
    exact hg0
  · have hprodF : ∀ F : Fin n2RootShape.k → Qq, (∏ i, F i) = F (0 : Fin 1) :=
      fun F => Fin.prod_univ_one F
    rw [hprodF]
    rfl

theorem n2_rsh (hdet : DetHyp n2T n2RB n2hK) :
    n2Chain.wsh17_pin ∧
    (∀ σ ∈ n2Chain.Sigmas, ∀ p ∈ n2Chain.PrimePools,
      ∃ hok : Rsh n2T n2M n2RB n2hdc n2hK hdet n2F n2Chain.WshP σ ∈ OKat p,
        ((evalAt p ⟨Rsh n2T n2M n2RB n2hdc n2hK hdet n2F n2Chain.WshP σ, hok⟩ : ℚ) : ℝ)
          = n2Chain.Rval σ p) ∧
    (∀ p ∈ n2Chain.PrimePools,
      n2Chain.Rval {n2v12} p = (((p + 1) / (p ^ 2 + p + 1) : ℚ) : ℝ)) := by
  have he2 : (2 : ℕ) ∈ Finset.Icc 1 2 := by decide
  refine ⟨?_, fun σ hσ p hp => n2Chain.rsh_interp σ hσ p hp hdet, ?_⟩
  · -- clause 1: wsh17_pin = the device W17ii height-sum instance (n2Wsh17Device)
    show n2Wsh17Device
    intro Ŝ hŜ q₀ hq
    refine ⟨⟨n2OnePG_val_mem q₀, ?_⟩, ?_⟩
    · rw [n2OnePG_evalAt]; norm_num
    · exact hasSum_single (⟨0, rfl⟩ : ({0} : Set ℕ))
        (fun b hb => absurd (Subtype.ext (Set.mem_singleton_iff.mp b.2)) hb)
  · -- clause 3: the explicit value at σ = {(1,2)}
    intro p hp
    have hσ : ({n2v12} : Multiset n2T.VType) ∈ n2Chain.Sigmas := by
      rw [n2_sigmas]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    obtain ⟨hok, heval⟩ := n2Chain.rsh_interp {n2v12} hσ p hp hdet
    have hRsh : Rsh n2T n2M n2RB n2hdc n2hK hdet n2F n2Chain.WshP {n2v12}
        = blockSolve n2T n2RB n2hdc n2hK n2hdet 2 he2 n2τ {n2v12} := by
      unfold Rsh
      rw [show n2F.Sh = {n2RootShape} from rfl, Finset.sum_singleton,
        n2_shconv hdet he2, powSubst_one,
        show (n2Chain.WshP n2RootShape).val = n2OnePG.val from rfl, n2OnePG_val, one_mul]
    have hbden : ((X : Polynomial ℚ) ^ 2 + X + 1).eval p ≠ 0 := by
      simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_one]
      intro h0
      nlinarith [sq_nonneg (2 * p + 1)]
    have hbpoly : ((X : Polynomial ℚ) ^ 2 + X + 1) ≠ 0 := fun h0 => hbden (by rw [h0]; simp)
    have hB : blockSolve n2T n2RB n2hdc n2hK n2hdet 2 he2 n2τ {n2v12} ∈ OKat p := by
      rw [(n2_solve_vals he2).1, mem_OKat_iff]
      have hdvd : (algebraMap (Polynomial ℚ) Qq (X + 1)
          / algebraMap (Polynomial ℚ) Qq (X ^ 2 + X + 1)).denom ∣ (X ^ 2 + X + 1) :=
        (RatFunc.denom_dvd hbpoly).mpr ⟨X + 1, rfl⟩
      obtain ⟨c, hc⟩ := hdvd
      intro h0
      exact hbden (by rw [hc, Polynomial.eval_mul, h0, zero_mul])
    have key : evalAt p ⟨blockSolve n2T n2RB n2hdc n2hK n2hdet 2 he2 n2τ {n2v12}, hB⟩
        = (p + 1) / (p ^ 2 + p + 1) := by
      have h1 : evalAt p ⟨blockSolve n2T n2RB n2hdc n2hK n2hdet 2 he2 n2τ {n2v12}, hB⟩
          = RatFunc.eval (RingHom.id ℚ) p
              (blockSolve n2T n2RB n2hdc n2hK n2hdet 2 he2 n2τ {n2v12}) := rfl
      rw [h1, (n2_solve_vals he2).1, eval_algebraMap_div' p (X + 1) (X ^ 2 + X + 1) hbden]
      simp
    have hsub : (⟨Rsh n2T n2M n2RB n2hdc n2hK hdet n2F n2Chain.WshP {n2v12}, hok⟩ : OKat p)
        = ⟨blockSolve n2T n2RB n2hdc n2hK n2hdet 2 he2 n2τ {n2v12}, hB⟩ :=
      Subtype.ext hRsh
    rw [← heval, hsub, key]

end LeanUrat.MovesS
