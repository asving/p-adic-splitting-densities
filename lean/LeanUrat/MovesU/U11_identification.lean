/-
Unit U11.identification  (MovesU campaign)  [derived; inputs explicit]
moves_ref: "and ρ_σ(p) IS the splitting density of type σ over ℤ_p — the undecided
           complement has mass 0 and the classifier verdicts are the true
           factorization types (X.3/CL-4 + [3t] VP, with VP-SOUND's citation duty)"
deps: U7 (DefsLedger in the import chain for the ledger-facing consumption at U10;
      `VPSound` itself lives in Defs).
sketch: sandwich `decided σ N ≤ trueCount σ N ≤ decided σ N + undec N`. Left: `hvs`
        injects {f // canonical = some σ} ⊆ {f // trueType = some σ}
        (`Nat.card_le_card_of_injective` on subtype inclusion). Right: a true-σ
        class is decided-σ or undecided — if `canonical N f = some τ` then `hvs`
        gives `trueType = some τ = some σ`, so `τ = σ` (`Option.some.inj`; trueType
        is single-valued); else `canonical N f = none` (undec). So {true-σ} ⊆
        {decided-σ} ⊎ {undec}, card ≤. Divide by p^{nN}: `dmass ≤ trueDmass ≤
        dmass + env`; squeeze (`tendsto_of_tendsto_of_tendsto_of_le_of_le`, upper
        leg `hd.add henv` + `add_zero`).
hypothesis_fields: none as stated (`VPSound X` explicit — instantiated at U10 from
        `cl10_vpsound`); the derivation itself is unconditional arithmetic +
        counting, NOT a fifth tag-free note-step (the note carries this clause
        inside Theorem U's conditional sentence, and it rides VP-SOUND/CL-4's tags
        at U10).
-/
import Mathlib
import LeanUrat.MovesU.U7_squeeze
import LeanUrat.MovesU.DefsLedger

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU
open Filter Topology

/-- Clause (ii), the identification corollary (D10, ruling (B)): under VP-SOUND and
    env → 0, the TRUE-type density is the same limit — the second squeeze. -/
theorem identification {n p : ℕ} (X : ClassifierSpec n p) [NeZero p] (hp : 1 < p)
    (r : ℝ) (σ : SplittingType n) (hvs : VPSound X)
    (hd : Tendsto (X.dmass σ) atTop (𝓝 r))
    (henv : Tendsto X.env atTop (𝓝 0)) :
    Tendsto (X.trueDmass σ) atTop (𝓝 r) := by
  -- Count-level sandwich: decided_σ(N) ≤ trueCount_σ(N) ≤ decided_σ(N) + undec(N).
  -- Left leg: VP-SOUND injects the decided-σ classes into the true-σ classes.
  have hle1 : ∀ N, X.decided σ N ≤ X.trueCount σ N := by
    intro N
    haveI : NeZero (p ^ N) := ⟨pow_ne_zero N (NeZero.ne p)⟩
    change Nat.card {f : Box p n N // X.canonical N f = some σ} ≤
         Nat.card {f : Box p n N // X.trueType N f = some σ}
    refine Nat.card_le_card_of_injective (fun x => ⟨x.1, hvs N x.1 σ x.2⟩) ?_
    intro a b hab
    simp only [Subtype.mk.injEq] at hab
    exact Subtype.ext hab
  -- Right leg: a true-σ class is decided-σ or undecided (VP-SOUND single-valuedness).
  have hle2 : ∀ N, X.trueCount σ N ≤ X.decided σ N + X.undec N := by
    intro N
    haveI : NeZero (p ^ N) := ⟨pow_ne_zero N (NeZero.ne p)⟩
    change Nat.card {f : Box p n N // X.trueType N f = some σ} ≤
         Nat.card {f : Box p n N // X.canonical N f = some σ} +
         Nat.card {f : Box p n N // X.canonical N f = none}
    rw [← Nat.card_sum]
    refine Nat.card_le_card_of_injective
      (fun x => if h : X.canonical N x.1 = none then
          (Sum.inr ⟨x.1, h⟩ : {f : Box p n N // X.canonical N f = some σ} ⊕
            {f : Box p n N // X.canonical N f = none})
        else
          Sum.inl ⟨x.1, by
            obtain ⟨τ, hτ⟩ := Option.ne_none_iff_exists'.mp h
            exact hτ.trans (x.2.symm.trans (hvs N x.1 τ hτ)).symm⟩) ?_
    intro a b hab
    simp only at hab
    apply Subtype.ext
    by_cases ha : X.canonical N a.1 = none <;> by_cases hb : X.canonical N b.1 = none
    · rw [dif_pos ha, dif_pos hb] at hab
      simp only [Sum.inr.injEq, Subtype.mk.injEq] at hab
      exact hab
    · rw [dif_pos ha, dif_neg hb] at hab
      nomatch hab
    · rw [dif_neg ha, dif_pos hb] at hab
      nomatch hab
    · rw [dif_neg ha, dif_neg hb] at hab
      simp only [Sum.inl.injEq, Subtype.mk.injEq] at hab
      exact hab
  -- Divide by p^{nN} > 0 to pass to densities.
  have hgf : X.dmass σ ≤ X.trueDmass σ := by
    intro N
    simp only [ClassifierSpec.dmass, ClassifierSpec.trueDmass]
    gcongr
    exact_mod_cast hle1 N
  have hfh : X.trueDmass σ ≤ fun N => X.dmass σ N + X.env N := by
    intro N
    simp only [ClassifierSpec.dmass, ClassifierSpec.trueDmass, ClassifierSpec.env]
    rw [← add_div]
    gcongr
    exact_mod_cast hle2 N
  -- Upper comparison limit dmass + env → r + 0 = r; squeeze.
  have hh : Tendsto (fun N => X.dmass σ N + X.env N) atTop (𝓝 r) := by
    simpa using hd.add henv
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hd hh hgf hfh

end LeanUrat.MovesU
