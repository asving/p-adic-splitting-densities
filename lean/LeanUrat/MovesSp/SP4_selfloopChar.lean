/-
Unit Sp.selfloopChar [REV 4, Codex-4 FIXED — the note's SUCC is
catalogue-restricted ("SUCC(s) := { s′ ∈ 𝒮_n^raw : … }"), so the characterized
relation is Succ-MEMBERSHIP for a catalogue letter, not bare SuccStep] —
moves_ref: "SELF-LOOPS, syntactically. s has a self-loop edge iff s ∈ SUCC(s):
necessarily e = g = 1 (else D grows strictly, (B1)) with W(s) = μ(s) — the
POST-REC species whose window equals their own selection multiplicity."
deps: Sp.memCoherent. sketch: Succ-membership = InCatalogue s ∧ SuccStep s s; the
helper: (→) D = e·g·D with D ≥ 1 forces e·g = 1; W = μ; the tag iff gives postRec.
(←) instantiate StageLaws' match; laws reflexive at e = g = 1, μ = W. loops3's
Bool filter reflects the helper. difficulty: medium.
-/
import LeanUrat.MovesSp.Defs
import LeanUrat.MovesSp.SP0_memCoherent

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

/-- the StageLaws computation both directions use. -/
theorem selfloop_succStep_iff {n : ℕ} {s : Species}
    (hc : Coherent s) (hb : Budget n s) : SuccStep n s s ↔ (s.tag = .postRec ∧
    s.e = 1 ∧ s.sel = some (1, s.W)) := by
  -- WellTyped positivity facts used in both directions.
  obtain ⟨hDpos, _hwpos, _hWpos, _hepos, _hellpos, hlampos⟩ := hc.1
  -- (G4) selection-membership: any selected pair lies in λ (positive parts).
  have hselmem : ∀ gm, s.sel = some gm → gm ∈ s.lam := hc.2.2.2.2.1.2
  constructor
  · rintro ⟨hstage, -, -⟩
    -- hstage : StageLaws s s (a match on s.sel).
    rcases hsel : s.sel with _ | ⟨g, μ⟩
    · -- selection ⊥: StageLaws is False.
      simp only [StageLaws, hsel] at hstage
    · -- selection some (g, μ): read off the raw stage laws.
      simp only [StageLaws, hsel] at hstage
      obtain ⟨hD, _hw, hW, _hInc, hRec⟩ := hstage
      -- g ≥ 1 from (G4)-membership + WellTyped positivity.
      have _hg1 : 1 ≤ g := (hlampos (g, μ) (hselmem (g, μ) hsel)).1
      -- s.D = (s.e * g) * s.D with s.D ≥ 1 forces s.e * g = 1.
      have heg : s.e * g = 1 :=
        Nat.eq_of_mul_eq_mul_right hDpos (by rw [one_mul, ← hD])
      -- both factors are 1.
      have he1 : s.e = 1 := Nat.eq_one_of_mul_eq_one_right heg
      have hg1' : g = 1 := Nat.eq_one_of_mul_eq_one_left heg
      -- tag = postRec from the (G5) tag-iff at e = g = 1; W = μ closes the selection.
      refine ⟨hRec.mpr ⟨he1, hg1'⟩, he1, ?_⟩
      rw [hg1', hW]
  · rintro ⟨htag, he1, hsel⟩
    -- Coherence and budget are the hypotheses; only StageLaws s s remains.
    refine ⟨?_, hc, hb⟩
    show StageLaws s s
    unfold StageLaws
    rw [hsel]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [he1]; ring
    · rw [one_mul]
    · rfl
    · -- tag = postInc ↔ 2 ≤ s.e · 1; RHS false (e = 1), LHS false (tag = postRec).
      rw [he1, mul_one]
      simp only [htag]
      decide
    · -- tag = postRec ↔ (s.e = 1 ∧ 1 = 1); both sides true.
      simp [htag, he1]

theorem selfloop_iff {n : ℕ} {s : Species} (hs : InCatalogue n s) :
    s ∈ Succ n s ↔ (s.tag = .postRec ∧ s.e = 1 ∧ s.sel = some (1, s.W)) := by
  obtain ⟨hc, hb⟩ := hs.coherent_budget
  constructor
  · rintro ⟨-, hstep⟩
    exact (selfloop_succStep_iff hc hb).mp hstep
  · intro h
    exact ⟨hs, (selfloop_succStep_iff hc hb).mpr h⟩

end LeanUrat.MovesSp
