/-
Unit Sp.rankStrict — moves_ref: "(ii) The rank ρ(s) := (D, tagord, n − W,
1 − [s is full]) … STRICTLY increases lexicographically along every non-self-loop
SUCC edge s → s′".
deps: Sp.rankStepInc, Sp.rankStepRec, Sp.rankRadix. sketch: e·g = 1 ∨ e·g ≥ 2
(WellTyped positivity); dispatch. difficulty: easy.
-/
import LeanUrat.MovesSp.Defs
import LeanUrat.MovesSp.SP0_memCoherent
import LeanUrat.MovesSp.SP4_rankStepInc
import LeanUrat.MovesSp.SP4_rankStepRec
import LeanUrat.MovesSp.SP4_rankRadix

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem rank_strict {n} {s s'} (hin : InCatalogue n s)
    (hin' : InCatalogue n s') (h : SuccStep n s s') (hne : s ≠ s') :
    rankNat n s < rankNat n s' := by
  -- coherence/budget of both endpoints (needed by rank_step_inc / rankNat_lt_of_lex)
  obtain ⟨hcs, hbs⟩ := hin.coherent_budget
  obtain ⟨hcs', hbs'⟩ := hin'.coherent_budget
  -- the stage laws force `s.sel = some (g, μ)` (the `none` branch is `False`)
  have hstage := h.1
  rcases hsel : s.sel with _ | ⟨g, μ⟩
  · simp only [StageLaws, hsel] at hstage
  · -- WellTyped positivity: e ≥ 1 and (via G4 selection ∈ λ) g ≥ 1, so e·g ≥ 1
    have he : 1 ≤ s.e := hcs.1.2.2.2.1
    have hmem : (g, μ) ∈ s.lam := hcs.2.2.2.2.1.2 (g, μ) hsel
    have hg1 : 1 ≤ g := (hcs.1.2.2.2.2.2 (g, μ) hmem).1
    have heg1 : 1 ≤ s.e * g := Nat.mul_pos he hg1
    by_cases hge2 : 2 ≤ s.e * g
    · -- e·g ≥ 2: D strictly increases, so the rank rises via the first lex coordinate
      have hD : s.D < s'.D :=
        rank_step_inc h ⟨hcs, hbs⟩ (by
          rintro g' μ' h'
          rw [hsel, Option.some.injEq, Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          exact hge2)
      exact rankNat_lt_of_lex hcs hbs hcs' hbs' (Or.inl hD)
    · -- e·g = 1: recursive step; the lower lex coordinates strictly increase
      have heg : s.e * g = 1 := by omega
      exact rank_step_rec h hne hin hin' (by
        rintro g' μ' h'
        rw [hsel, Option.some.injEq, Prod.mk.injEq] at h'
        obtain ⟨rfl, rfl⟩ := h'
        exact heg)

end LeanUrat.MovesSp
