/-
Unit XG.3 x3Density — the density limit, DERIVED (finding 11: no detectInter, no
MassLink)  [E-phase: PROVED, body complete]
moves_ref: "(X.3) … μ(Undec(N)) → 0 (N → ∞)" + CONDITIONALITY SUMMARY "X.3 = [routes] +
(ns-null, closed, tag displayed) + accepted perimeter".
sketch: ⋂Undec ⊆ InfTree ∪ ⋃ns (XG.2c); InfTree ⊆ discZero (XG.2d contrapositive);
frac(discZero) = 0 (XF.10); frac(⋃ns) = 0 (NS + nsCountable + frac_iUnion_null);
frac_mono/union_le ⟹ frac(⋂) = 0; frac_inter_tendsto + undec_antitone close the limit.
deps: XG.2c, XG.2d, XF.10, XD.1. difficulty: HARD (MEDIUM-HARD band).
hyp_fields: X3aRouteP, NsNullP (tag) — NOTHING else beyond XCtx's audited inputs.
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XD1
import LeanUrat.MovesX.XF10
import LeanUrat.MovesX.XG2c
import LeanUrat.MovesX.XG2d

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem x3Density {n : ℕ} (X : XFamily n) (K : XConsts n) (hn : 2 ≤ n)
    (R : X3aRouteP n X K) (NS : NsNullP n X) (p : ℕ) [Fact p.Prime] :
    Filter.Tendsto (fun N => (X.ctx p).frac ((X.ctx p).Undec N)) Filter.atTop (nhds 0) := by
  set C := X.ctx p with hC
  -- `frac (discZero) = 0` (XF.10).
  have hdz : C.frac (discZero n p) = 0 := discZeroNull n p hn C
  -- `frac ∅ = 0` (monotone into the null `discZero`).
  have hEmpty : C.frac (∅ : Set (MonicBox n p)) = 0 :=
    le_antisymm (by simpa [hdz] using C.frac_mono ∅ (discZero n p) (Set.empty_subset _))
      (C.frac_nonneg _)
  -- `frac (⋃ i, nsFiber i) = 0` (NS + countability of `nsIdx` + `frac_iUnion_null`).
  have hns : C.frac (⋃ i, C.nsFiber i) = 0 := by
    haveI : Countable C.nsIdx := C.nsCountable
    -- reindex the countable union over `Option C.nsIdx` (always nonempty) by ℕ.
    obtain ⟨e, he⟩ :
        ∃ e : ℕ → Option C.nsIdx, Function.Surjective e :=
      exists_surjective_nat _
    set g : Option C.nsIdx → Set (MonicBox n p) :=
      fun o => o.elim ∅ C.nsFiber with hg
    have hgnull : ∀ o, C.frac (g o) = 0 := by
      intro o
      cases o with
      | none => simpa [hg] using hEmpty
      | some i => simpa [hg] using NS p i
    have hunion : (⋃ i, C.nsFiber i) = ⋃ k, g (e k) := by
      rw [he.iUnion_comp g]
      simp [hg, Set.iUnion_option]
    rw [hunion]
    exact C.frac_iUnion_null (fun k => g (e k)) (fun k => hgnull (e k))
  -- Inclusion chain: `⋂ Undec ⊆ discZero ∪ ⋃ nsFiber`.
  have hsub : (⋂ N, C.Undec N) ⊆ discZero n p ∪ (⋃ i, C.nsFiber i) := by
    intro f hf
    rcases interTrichotomy C hf with hInf | hns'
    · -- `InfTree ⊆ discZero` (XG.2d treeFinite, contrapositive).
      refine Or.inl ?_
      by_contra hd
      exact hInf (treeFinite X K R p (by omega) f hd)
    · exact Or.inr hns'
  -- Combine: `frac (⋂ Undec) = 0`.
  have hInterNull : C.frac (⋂ N, C.Undec N) = 0 := by
    refine le_antisymm ?_ (C.frac_nonneg _)
    calc C.frac (⋂ N, C.Undec N)
        ≤ C.frac (discZero n p ∪ ⋃ i, C.nsFiber i) := C.frac_mono _ _ hsub
      _ ≤ C.frac (discZero n p) + C.frac (⋃ i, C.nsFiber i) := C.frac_union_le _ _
      _ = 0 := by rw [hdz, hns]; ring
  -- The limit: monotone convergence of the box content targets `frac (⋂ Undec) = 0`.
  have htends := C.frac_inter_tendsto
  rw [hInterNull] at htends
  exact htends

end LeanUrat.MovesX
