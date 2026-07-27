/-
Unit Sp.rankStepRec — moves_ref: "· e = g = 1, μ < W(s): D′ = D; tagord′ = 2 ≥
tagord; if tagord < 2 done, else n − W′ = n − μ > n − W(s). · e = g = 1, μ = W(s):
s is full …; if tagord(s) = 2, then s is THE full POST-REC letter at its stage, so
s′ ≠ s … is non-full by (i)'s uniqueness: the last coordinate rises 0 → 1."
deps: Sp.fullForcing, Sp.fullUnique, Sp.rankRadix, Sp.memCoherent. sketch: the
displayed three-way split on (μ vs W, tagord); the μ = W ∧ tagord = 2 branch:
s full; if s' full too then full_unique forces s' = s, contra hne; so fullBit
rises. difficulty: medium-hard (the subtle case; keep the three branches as
`have`s).
-/
import LeanUrat.MovesSp.Defs
import LeanUrat.MovesSp.SP0_memCoherent
import LeanUrat.MovesSp.SP4_fullUnique
import LeanUrat.MovesSp.SP4_rankRadix

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem rank_step_rec {n} {s s'} (h : SuccStep n s s') (hne : s ≠ s')
    (hin : InCatalogue n s) (hin' : InCatalogue n s')
    (he1 : ∀ g μ, s.sel = some (g,μ) → s.e * g = 1) :
    rankNat n s < rankNat n s' := by
  -- Unpack the SUCC edge and the source's coherence/budget.
  obtain ⟨hSt, hc', hb'⟩ := h
  obtain ⟨hc, hb⟩ := hin.coherent_budget
  -- The source has a selection (else `StageLaws` is `False`).
  cases hsel : s.sel with
  | none => simp only [StageLaws, hsel] at hSt
  | some p =>
    obtain ⟨g, μ⟩ := p
    simp only [StageLaws, hsel] at hSt
    obtain ⟨hD', hw', hW', htagI, htagR⟩ := hSt
    -- `e·g = 1` forces `e = 1` and `g = 1`.
    have heg : s.e * g = 1 := he1 g μ hsel
    obtain ⟨he, hg⟩ := mul_eq_one.mp heg
    subst hg
    -- Consequences of the stage laws in the recursive (e = g = 1) case.
    have hDeq : s'.D = s.D := by rw [hD', he]; ring
    have hweq : s'.w = s.w := by rw [hw', one_mul]
    have htag' : s'.tag = Tag.postRec := htagR.mpr ⟨he, rfl⟩
    -- Source budget facts we will need.
    have hWpos : 1 ≤ s.W := hc.1.2.2.1
    have hb32 : s.a + s.ell ≤ s.W := hb.2.2.1.2.1
    have hb5W : s.W ≤ n := hb.2.2.2.2.2.2.2.2.1
    have hb4 : ∀ gm, s.sel = some gm → gm.1 * gm.2 ≤ s.ell := hb.2.2.2.1
    -- `μ ≤ W(s)`: `μ = 1·μ ≤ ℓ ≤ W`.
    have hμell : (1 : ℕ) * μ ≤ s.ell := hb4 (1, μ) hsel
    rw [one_mul] at hμell
    have hμW : μ ≤ s.W := by omega
    -- Three-way lex split, discharged through `rankNat_lt_of_lex`.
    have htagd : tagord s.tag < 2 ∨ s.tag = Tag.postRec := by
      cases s.tag <;> simp [tagord]
    rcases htagd with hlt | hpr
    · -- tagord(s) < 2 = tagord(s'): the tagord digit strictly rises.
      exact rankNat_lt_of_lex hc hb hc' hb'
        (Or.inr (Or.inl ⟨hDeq.symm, by rw [htag']; exact hlt⟩))
    · -- s is POST-REC; split on μ vs W(s).
      rcases lt_or_eq_of_le hμW with hμlt | hμeq
      · -- μ < W(s): the (n − W) digit strictly rises.
        exact rankNat_lt_of_lex hc hb hc' hb'
          (Or.inr (Or.inr (Or.inl ⟨hDeq.symm, by rw [hpr, htag'], by rw [hW']; omega⟩)))
      · -- μ = W(s): s is full; s' cannot be (else full_unique ⇒ s = s'), so fullBit rises.
        have hfull_s : s.sel = some (1, s.W) := by rw [hsel, hμeq]
        have hfs : fullBit s = 0 := by unfold fullBit; exact if_pos hfull_s
        have hnf' : ¬ (s'.sel = some (1, s'.W)) := by
          intro hfull_s'
          exact hne (full_unique hc hb hc' hb' hfull_s hfull_s'
            (by rw [hpr, htag']) hDeq.symm hweq.symm (by rw [hW', hμeq]))
        have hfs' : fullBit s' = 1 := by unfold fullBit; exact if_neg hnf'
        exact rankNat_lt_of_lex hc hb hc' hb'
          (Or.inr (Or.inr (Or.inr ⟨hDeq.symm, by rw [hpr, htag'], by rw [hW', hμeq], by omega⟩)))

end LeanUrat.MovesSp
