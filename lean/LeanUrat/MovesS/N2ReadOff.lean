/-
Unit U-29d5 `n2_readoff` (medium) — inhabits `ReadOffBundle` with S := the
BASE-PRIME pools (scope CORRECTED, Codex#4-10) — exactly what U-29d2's legs_reg
packages cover (consumedDeltas = {1} at this instance), infinite, ⊆
allActivePools; the per-(e, q₀) packages are READ OFF U-29d2's construction
(cited, not rebuilt); AVAgree from the explicit reduced denominators (q²+q+1 and
q³ nonvanishing at every q₀ ≥ 2 supply hok; the active solve = the explicit
values; no split legs).

PROOF ROUTE (escalation rev): the n = 2 table has NO split outcome at ANY layer
(`splitOuts = ∅` everywhere), so `bhatMeas` collapses to `bTermMeas` — the
measured β-family never enters and AVAgree closes WITHOUT the read-off gate:
both sides of the pin are the same nonsingular 1×1 solve.  Symbolically
`blockSolve = (1 − k)⁻¹ · bTerm` (Cramer on the subsingleton state space);
`hok` comes from the OKat-inverse lemma below (eval(1 − k) ≠ 0 is the package's
own `e0` determinant, transported by `A_eval`), and the evaluated value matches
`(1 − Aℝ)⁻¹ *ᵥ b̂` entry-for-entry via `tg_interp` on the terminal columns.
-/
import LeanUrat.MovesS.N2Beta
import LeanUrat.MovesS.N2Det
import LeanUrat.MovesS.N2Pools
import LeanUrat.MovesS.BlockSolve
import LeanUrat.MovesS.SolveCramer
import LeanUrat.MovesS.EvalAtCoe
import LeanUrat.MovesS.ActiveSolve

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Matrix Polynomial

def n2BasePrimes : Set ℚ := {q₀ | ∃ p : ℕ, p.Prime ∧ q₀ = (p : ℚ)}

theorem n2_base_sub : n2BasePrimes ⊆ allActivePools n2M := by
  rintro q₀ ⟨p, hp, rfl⟩
  exact ⟨⟨p, hp, 1, by rw [PNat.one_coe, pow_one]⟩, fun e _ τ => trivial⟩

theorem n2_base_infinite : n2BasePrimes.Infinite :=
  Set.infinite_of_injective_forall_mem
    (f := fun p : Nat.Primes => ((p : ℕ) : ℚ))
    (fun _ _ h => Subtype.ext (Nat.cast_injective h))
    (fun p => ⟨p, p.prop, rfl⟩)

/-! ### The route fact: the n = 2 table has no split outcome at any layer. -/

private theorem n2_route_ne_split (e : ℕ) (τ : n2T.State e) (o : n2T.Out e τ) :
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

private theorem n2_splitOuts_empty (e : ℕ) (τ : n2T.State e) :
    splitOuts n2T e τ = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro o
  simp only [splitOuts, Set.mem_toFinset, Set.mem_setOf_eq]
  exact n2_route_ne_split e τ o

/-! ### OKat inverse: a regular element with nonvanishing value has a regular
inverse, and `evalAt` inverts it. -/

private theorem evalAt_algebraMap (q₀ : ℚ) (p : Polynomial ℚ)
    (h : algebraMap (Polynomial ℚ) Qq p ∈ OKat q₀) :
    evalAt q₀ ⟨algebraMap (Polynomial ℚ) Qq p, h⟩ = p.eval q₀ := by
  rw [evalAt_coe]
  show RatFunc.eval (RingHom.id ℚ) q₀ (algebraMap (Polynomial ℚ) Qq p) = p.eval q₀
  rw [RatFunc.eval_algebraMap]
  simp [Polynomial.eval₂_id]

private theorem okat_inv {q₀ : ℚ} {f : Qq} (hf : f ∈ OKat q₀)
    (hne : evalAt q₀ ⟨f, hf⟩ ≠ 0) :
    ∃ hinv : f⁻¹ ∈ OKat q₀, evalAt q₀ ⟨f⁻¹, hinv⟩ = (evalAt q₀ ⟨f, hf⟩)⁻¹ := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hne (by rw [show (⟨(0 : Qq), hf⟩ : OKat q₀) = 0 from Subtype.ext rfl]
                  exact map_zero _)
  have hdmem : algebraMap (Polynomial ℚ) Qq f.denom ∈ OKat q₀ := by
    rw [mem_OKat_iff, RatFunc.denom_algebraMap]
    simp
  have hnmem : algebraMap (Polynomial ℚ) Qq f.num ∈ OKat q₀ := by
    rw [mem_OKat_iff, RatFunc.denom_algebraMap]
    simp
  have hd0 : algebraMap (Polynomial ℚ) Qq f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero f)
  have hmul : f * algebraMap (Polynomial ℚ) Qq f.denom
      = algebraMap (Polynomial ℚ) Qq f.num :=
    (eq_div_iff hd0).mp (RatFunc.num_div_denom f).symm
  have hnum0 : f.num.eval q₀ ≠ 0 := by
    have hp : (⟨f, hf⟩ : OKat q₀) * ⟨_, hdmem⟩ = ⟨_, hnmem⟩ := Subtype.ext hmul
    have hev := congrArg (evalAt q₀) hp
    rw [map_mul, evalAt_algebraMap, evalAt_algebraMap] at hev
    rw [← hev]
    exact mul_ne_zero hne hf
  have hform : f⁻¹ = algebraMap (Polynomial ℚ) Qq f.denom
      / algebraMap (Polynomial ℚ) Qq f.num := by
    conv_lhs => rw [← RatFunc.num_div_denom f]
    rw [inv_div]
  have hinv : f⁻¹ ∈ OKat q₀ := by
    rw [hform, mem_OKat_iff]
    intro h0
    obtain ⟨c, hc⟩ := RatFunc.denom_div_dvd f.denom f.num
    rw [hc, Polynomial.eval_mul, h0, zero_mul] at hnum0
    exact hnum0 rfl
  refine ⟨hinv, ?_⟩
  have hp1 : (⟨f, hf⟩ : OKat q₀) * ⟨f⁻¹, hinv⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hf0)
  have hev := congrArg (evalAt q₀) hp1
  rw [map_mul, map_one] at hev
  exact (inv_eq_of_mul_eq_one_right hev).symm

/-! ### The 1×1 Cramer point solve (both carriers are subsingleton-indexed). -/

private theorem cramer_point {ι F : Type*} [Fintype ι] [DecidableEq ι]
    [Subsingleton ι] [Field F] (K : Matrix ι ι F) (b : ι → F)
    (hdet : (1 - K).det ≠ 0) (i : ι) :
    ((1 - K)⁻¹ *ᵥ b) i = (1 - K i i)⁻¹ * b i := by
  have h := congrFun (solve_cramer K b hdet) i
  rw [h, Matrix.adjugate_subsingleton, Matrix.one_mulVec,
    Matrix.det_eq_elem_of_subsingleton _ i, Matrix.sub_apply, Matrix.one_apply_eq]

/-! ### The terminal-column tie: `bTermMeas` is the evaluated `bTerm` (per
column via `tg_interp`; termFin is never split). -/

private theorem bTermMeas_eq_eval {e : ℕ} (τ : n2T.State e)
    (σ' : Multiset n2T.VType) {q₀ : ℚ} (hq : q₀ ∈ n2M.Pools)
    (hok : bTerm n2T n2RB e σ' τ ∈ OKat q₀) :
    bTermMeas n2T n2M e σ' q₀ τ = ((evalAt q₀ ⟨bTerm n2T n2RB e σ' τ, hok⟩ : ℚ) : ℝ) := by
  classical
  set term : n2T.Out e τ → Qq := fun o =>
    if routeOf (n2T.odata e τ o) = .termFin ∧ (n2T.odata e τ o).verdicts = σ'
    then n2RB.TG e τ o else 0 with hterm
  have hmem : ∀ o : n2T.Out e τ, term o ∈ OKat q₀ := by
    intro o
    simp only [hterm]
    split_ifs
    · exact n2RB.tg_ok e τ o q₀ hq
    · exact zero_mem _
  have hsum : (⟨bTerm n2T n2RB e σ' τ, hok⟩ : OKat q₀)
      = ∑ o : n2T.Out e τ, (⟨term o, hmem o⟩ : OKat q₀) := by
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum]
    rfl
  rw [hsum, map_sum]
  push_cast
  simp only [bTermMeas]
  refine Finset.sum_congr rfl fun o _ => ?_
  by_cases hc : routeOf (n2T.odata e τ o) = .termFin ∧ (n2T.odata e τ o).verdicts = σ'
  · rw [if_pos hc]
    have hval : (⟨term o, hmem o⟩ : OKat q₀)
        = ⟨(n2RB.tgP e τ o).val, n2RB.tg_ok e τ o q₀ hq⟩ := by
      apply Subtype.ext
      simp only [hterm, if_pos hc]
    rw [hval]
    exact (n2RB.tg_interp e τ o q₀ hq (by rw [hc.1]; decide)).symm
  · rw [if_neg hc]
    have hval : (⟨term o, hmem o⟩ : OKat q₀) = 0 := by
      apply Subtype.ext
      simp only [hterm, if_neg hc]
      rfl
    rw [hval, map_zero, Rat.cast_zero]

/-! ### The AVAgree core, generic in the per-pool package and the measured
β-family (the split legs are empty, so the family never enters). -/

private theorem n2_avagree {e : ℕ} (he : e ∈ Finset.Icc 1 2) {q₀ : ℚ}
    (P : PoolHyp n2T n2M n2RB e (n2hK e he) q₀)
    (βfam : ∀ e', e' ∈ Finset.Icc 1 2 → n2T.State e' → Multiset n2T.VType → ℚ → ℝ)
    (σ' : Multiset n2T.VType) (τA : P.Act) :
    AVAgree P (blockSolve n2T n2RB n2hdc n2hK n2hdet e he (↑τA) σ')
      (bhatMeas P βfam σ') τA := by
  classical
  haveI hssU : Subsingleton (n2T.State e) := inferInstanceAs (Subsingleton Unit)
  haveI hssA : Subsingleton P.Act := ⟨fun a b => Subtype.ext (Subsingleton.elim a.1 b.1)⟩
  -- (1) no split legs anywhere:
  have hsplit : splitOuts n2T e (↑τA : n2T.State e) = ∅ := n2_splitOuts_empty e _
  have hbsplit0 : bSplit n2T n2RB n2hdc e he
      (fun e' _ τ' σ'' =>
        if he' : e' ∈ Finset.Icc 1 2 then
          blockSolve n2T n2RB n2hdc n2hK n2hdet e' he' τ' σ''
        else 0) σ' (↑τA) = 0 := by
    rw [bSplit_def, hsplit, Finset.sum_empty]
  -- (2) the closed 1×1 form of the symbolic solve:
  have hbs : blockSolve n2T n2RB n2hdc n2hK n2hdet e he (↑τA) σ'
      = (1 - Kmat n2T n2RB e (n2hK e he) (↑τA) (↑τA))⁻¹ * bTerm n2T n2RB e σ' (↑τA) := by
    rw [blockSolve_eq, cramer_point _ _ (n2hdet e he), Pi.add_apply, hbsplit0, add_zero]
  -- (3) memberships (every state is active at every pool at this instance):
  have hact : ∀ s : n2T.State e, s ∈ P.Act := fun s => (P.act_spec s).mpr trivial
  have hkok : Kmat n2T n2RB e (n2hK e he) (↑τA) (↑τA) ∈ OKat q₀ :=
    P.entry_ok _ _ (hact _) (hact _)
  have h1k : 1 - Kmat n2T n2RB e (n2hK e he) (↑τA) (↑τA) ∈ OKat q₀ :=
    sub_mem (one_mem _) hkok
  have hbok : bTerm n2T n2RB e σ' (↑τA) ∈ OKat q₀ := by
    simp only [bTerm]
    refine Subring.sum_mem _ fun o _ => ?_
    split_ifs
    · exact n2RB.tg_ok e _ o q₀ P.pool_mem
    · exact zero_mem _
  -- (4) the evaluated diagonal is the package's own nonzero determinant:
  have hsubk : (⟨1 - Kmat n2T n2RB e (n2hK e he) (↑τA) (↑τA), h1k⟩ : OKat q₀)
      = 1 - ⟨Kmat n2T n2RB e (n2hK e he) (↑τA) (↑τA),
          P.entry_ok τA.1 τA.1 τA.2 τA.2⟩ := Subtype.ext rfl
  have hdetq : evalAt q₀ ⟨1 - Kmat n2T n2RB e (n2hK e he) (↑τA) (↑τA), h1k⟩ ≠ 0 := by
    have hd := e0_det_ne_zero P.e0
    rw [Matrix.det_eq_elem_of_subsingleton _ τA, Matrix.sub_apply, Matrix.one_apply_eq,
      P.A_eval] at hd
    rw [hsubk, map_sub, map_one]
    exact hd
  obtain ⟨hinvok, hinvval⟩ := okat_inv h1k hdetq
  -- (5) `hok` and the evaluated value of the solve:
  have hok : blockSolve n2T n2RB n2hdc n2hK n2hdet e he (↑τA) σ' ∈ OKat q₀ := by
    rw [hbs]
    exact mul_mem hinvok hbok
  refine ⟨hok, ?_⟩
  have hLHS : evalAt q₀ ⟨blockSolve n2T n2RB n2hdc n2hK n2hdet e he (↑τA) σ', hok⟩
      = (evalAt q₀ ⟨1 - Kmat n2T n2RB e (n2hK e he) (↑τA) (↑τA), h1k⟩)⁻¹
        * evalAt q₀ ⟨bTerm n2T n2RB e σ' (↑τA), hbok⟩ := by
    rw [show (⟨blockSolve n2T n2RB n2hdc n2hK n2hdet e he (↑τA) σ', hok⟩ : OKat q₀)
        = ⟨(1 - Kmat n2T n2RB e (n2hK e he) (↑τA) (↑τA))⁻¹, hinvok⟩
          * ⟨bTerm n2T n2RB e σ' (↑τA), hbok⟩ from Subtype.ext hbs]
    rw [map_mul, hinvval]
  -- (6) the measured side is the same 1×1 solve:
  have hdetℝ : (1 - Aℝ P).det ≠ 0 := (Aℝ_det_iff P).mpr (e0_det_ne_zero P.e0)
  rw [cramer_point _ _ hdetℝ τA]
  have hbhat : bhatMeas P βfam σ' τA = bTermMeas n2T n2M e σ' q₀ (↑τA) := by
    simp only [bhatMeas, bSplitMeas]
    rw [hsplit, Finset.sum_empty, add_zero]
  have hAℝ : 1 - Aℝ P τA τA
      = ((evalAt q₀ ⟨1 - Kmat n2T n2RB e (n2hK e he) (↑τA) (↑τA), h1k⟩ : ℚ) : ℝ) := by
    rw [Aℝ, Matrix.map_apply, P.A_eval, eq_ratCast, hsubk, map_sub, map_one]
    push_cast
    ring
  rw [hbhat, bTermMeas_eq_eval _ σ' P.pool_mem hbok, hAℝ, hLHS]
  push_cast
  ring

noncomputable def n2_readoff : ReadOffBundle n2BasePrimes n2_base_sub n2B n2hdet where
  pkg := fun q₀ hq e he => (n2_pools_all.2 e he q₀ hq).some
  read := fun q₀ hq e he τA σ' h_ent =>
    n2_avagree he ((n2_pools_all.2 e he q₀ hq).some)
      (fun e' he' => n2B.βmeas e' he' h_ent) σ' τA

end LeanUrat.MovesS
