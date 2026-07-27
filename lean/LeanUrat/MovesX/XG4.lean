/-
Unit XG.4 x3Series — the per-σ series identity, DERIVED (finding 12: `hσ` deleted;
`densityOf` DEFINED)  [PROVED, fleet 2026-07-28]
moves_ref: "for each type σ the tree-fiber series sums the full density … [(ns-null)
tag displayed]" + "(3e)-style regrouping (Tonelli, positive terms) yields the per-σ
series identity"; VP-SOUND consumed exactly at the typemult identification (note
finding 13).
sketch: E_σ := {f | S.splitType f = σ} ∖ (⋂Undec ∪ discZero); `decided_covered` +
`fiber_disjoint` + VP show E_σ is exactly the union of the σ-typemult fibers minus null
sets; ADD gives HasSum to frac E_σ; frac(⋂Undec) = 0 (XG.3's chain) and
frac(discZero) = 0 (XF.10) + union_le/mono give frac E_σ = densityOf S σ.
deps: XG.3, XF.10. difficulty: HARD.
hyp_fields: VPSoundP, CountableFiberAdditive (Tonelli, owed), SeriesData's three
coverage fields (blueprint §4) + the XG.3 riders.
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XF10
import LeanUrat.MovesX.XG3

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem x3Series {n : ℕ} (X : XFamily n) (K : XConsts n) (hn : 2 ≤ n)
    (R : X3aRouteP n X K) (NS : NsNullP n X)
    (p : ℕ) [Fact p.Prime] (S : SeriesData n p (X.ctx p))
    (VP : VPSoundP S) (ADD : CountableFiberAdditive S) (σ : SplitType n) :
    HasSum (fun T : { T // S.typemult T = σ } => (X.ctx p).frac (S.fiber T))
      (densityOf S σ) := by
  -- The union event of the σ-typemult fibers.
  set E : Set (MonicBox n p) := {f | ∃ T, S.typemult T = σ ∧ f ∈ S.fiber T} with hE
  -- ADD's two coverage hypotheses for I := σ-typemult trees against E.
  have hcov : ∀ f ∈ E, ∃ T ∈ {T | S.typemult T = σ}, f ∈ S.fiber T := by
    intro f hf
    rw [hE] at hf
    obtain ⟨T, hT, hfT⟩ := hf
    exact ⟨T, hT, hfT⟩
  have hsub : ∀ T ∈ {T | S.typemult T = σ}, S.fiber T ⊆ E := by
    intro T hT f hfT
    rw [hE]
    exact ⟨T, hT, hfT⟩
  -- Countable additivity of the box content over the disjoint σ-fiber family.
  have hHasSum := ADD {T | S.typemult T = σ} E hcov hsub
  -- The two null legs: μ(⋂Undec) = 0 (XG.3) and μ(discZero) = 0 (XF.10).
  have hInter : (X.ctx p).frac (⋂ N, (X.ctx p).Undec N) = 0 :=
    tendsto_nhds_unique (X.ctx p).frac_inter_tendsto (x3Density X K hn R NS p)
  have hDisc : (X.ctx p).frac (discZero n p) = 0 := discZeroNull n p hn (X.ctx p)
  -- E ⊆ true-type event (VP-SOUND: fiber membership pins the true type).
  have hEA : E ⊆ {f | S.splitType f = σ} := by
    intro f hf
    rw [hE] at hf
    obtain ⟨T, hT, hfT⟩ := hf
    show S.splitType f = σ
    rw [VP T f hfT]; exact hT
  -- true-type event ⊆ E ∪ (⋂Undec ∪ discZero) (decided coverage off the null sets).
  have hAE : {f | S.splitType f = σ} ⊆ E ∪ ((⋂ N, (X.ctx p).Undec N) ∪ discZero n p) := by
    intro f hf
    have hfσ : S.splitType f = σ := hf
    by_cases h1 : f ∈ ⋂ N, (X.ctx p).Undec N
    · exact Or.inr (Or.inl h1)
    · by_cases h2 : f ∈ discZero n p
      · exact Or.inr (Or.inr h2)
      · obtain ⟨T, hfT⟩ := S.decided_covered f h1 h2
        have hTσ : S.typemult T = σ := (VP T f hfT).symm.trans hfσ
        refine Or.inl ?_
        rw [hE]
        exact ⟨T, hTσ, hfT⟩
  -- frac E = densityOf S σ by the squeeze.
  have hfracEq : (X.ctx p).frac E = densityOf S σ := by
    have h1 : (X.ctx p).frac E ≤ (X.ctx p).frac {f | S.splitType f = σ} :=
      (X.ctx p).frac_mono _ _ hEA
    have h2 : (X.ctx p).frac {f | S.splitType f = σ} ≤ (X.ctx p).frac E := by
      calc (X.ctx p).frac {f | S.splitType f = σ}
          ≤ (X.ctx p).frac (E ∪ ((⋂ N, (X.ctx p).Undec N) ∪ discZero n p)) :=
            (X.ctx p).frac_mono _ _ hAE
        _ ≤ (X.ctx p).frac E + (X.ctx p).frac ((⋂ N, (X.ctx p).Undec N) ∪ discZero n p) :=
            (X.ctx p).frac_union_le _ _
        _ ≤ (X.ctx p).frac E
              + ((X.ctx p).frac (⋂ N, (X.ctx p).Undec N) + (X.ctx p).frac (discZero n p)) := by
            have := (X.ctx p).frac_union_le (⋂ N, (X.ctx p).Undec N) (discZero n p)
            linarith
        _ = (X.ctx p).frac E := by rw [hInter, hDisc]; ring
    have hEq : (X.ctx p).frac E = (X.ctx p).frac {f | S.splitType f = σ} := le_antisymm h1 h2
    rw [hEq]; rfl
  rw [hfracEq] at hHasSum
  exact hHasSum

end LeanUrat.MovesX
