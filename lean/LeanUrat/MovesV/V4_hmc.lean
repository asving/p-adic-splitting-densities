/-  MovesV unit V4-11 `hmc_typing` (REWRITTEN REV 9: THE CENSUS-LEVEL
    COUPLING) — leg (i): the false-HMC toy (¬HMC at the coupled census);
    leg (ii) = V1-8b (HMC true there); leg (iii) WITHDRAWN (verdict (A),
    HMCAUG_ESCALATION_ADJUDICATION_2026-07-29: no separation obligation).
    The terminal-final signature check is the `example` below. -/
import LeanUrat.MovesV.V1_witnessB

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- leg (i): THE COUPLED TOY — ¬HMC witnessed at carrier level (the §8
decide gate; the coupled composite census is empty at (0,0) while both
one-step factors are full). -/
theorem hmc_false_witness :
    ∃ (S : StepSys 1) (TE : TmplEvents 1 S) (D : XHDd 1 S TE), ¬ HMC TE D := by
  sorry

/-- the coupling signature (marks_chains-consistent): at the coupled point
the combinatorial chains exist while the census is empty — recorded as the
∃-shaped check rider on leg (i). -/
theorem coupling_signature :
    ∃ (S : StepSys 1) (TE : TmplEvents 1 S) (α β : S.Cell)
      (m₁ : S.Move α β) (γ : Template 1 S β) (q₀ : ℚ) (x : S.Hist q₀ α)
      (h : Hpt (Template.cons m₁ γ).D),
      0 < chainCount S (.cons m₁ γ) x h ∧ Tgam TE (.cons m₁ γ) x h = 0 := by
  sorry

/-- the terminal-final signature check: `Template.lastT` instances TYPE
against HMC's quantifier (the probe's step 2 is a literal instance BY TYPE). -/
example {n : ℕ} {S : StepSys n} (TE : TmplEvents n S) (D : XHDd n S TE)
    (hHMC : HMC TE D) {α β : S.Cell} {v : VLabel n} (m : S.Move α β)
    (mT : S.MoveT β v) (h₁ : Hpt (S.dim m)) (h₂ : Hpt (Template.lastT (n := n) (S := S) mT).D) :
    (D.dom (.cons m (.lastT mT))).Mem (Hpt.append h₁ h₂) ↔
      (D.dom (.last m)).Mem h₁ ∧ (D.dom (.lastT mT)).Mem h₂ :=
  hHMC m (.lastT mT) h₁ h₂

end LeanUrat.MovesV
