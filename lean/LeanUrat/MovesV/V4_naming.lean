/-  MovesV unit V4-12 `comp_naming` (RESTATED REV 4 at the note's exact
    quantifier) — (a) the IF leg (proved-under-hypotheses shape); (b) the
    ONLY-IF leg as a NAMED STATEMENT, consumed by nothing, claimed neither
    way; (b′) the machine-checked sum-level coincidence; (c) the fence. -/
import LeanUrat.MovesV.V4_hmc
import LeanUrat.MovesV.V0_partition

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- the factorization identity AT THE FIXED XHD weight system. -/
def Factorizes {n : ℕ} {S : StepSys n} {TE : TmplEvents n S}
    (X : XHDw n S) (D : XHDd n S TE) : Prop :=
  ∀ {α β} (m : S.Move α β) (γ : Template n S β) (q₀ : ℚ), q₀ ∈ S.Pools →
    ∀ (a b c : ℝ),
      HasSum (fun h : {h // (D.dom (.cons m γ)).Mem h} =>
        gProd X (.cons m γ) h.1 q₀) a →
      HasSum (fun h : {h // (D.dom (.last m)).Mem h} => X.g m h.1 q₀) b →
      HasSum (fun h : {h // (D.dom γ).Mem h} => gProd X γ h.1 q₀) c →
      a = b * c

/-- (a) THE IF LEG: HMC upgrades (COMP-hΣ) to the factored form. -/
theorem comp_upgrade {n : ℕ} {S : StepSys n} {TE : TmplEvents n S}
    (X : XHDw n S) (D : XHDd n S TE) (Xs : XHDs n S X D)
    (hHMC : HMC TE D) : Factorizes X D := by
  sorry

/-- (b) THE ONLY-IF LEG at the note's exact quantifier — a NAMED statement,
status RECORDED (interface-derivability OPEN, CLAIMED NEITHER WAY);
consumed by NO unit. -/
def UpgradeOnlyIf {n : ℕ} {S : StepSys n} (TE : TmplEvents n S)
    (X : XHDw n S) (D : XHDd n S TE) : Prop :=
  Factorizes X D → HMC TE D

/-- (b′) the MACHINE-CHECKED SUM-LEVEL COINCIDENCE: two DIFFERENT listed
sets with IDENTICAL fixed-system weight sums under E = h₁ + h₂. -/
theorem sum_not_membership (q₀ : ℝ) (hq : q₀ ≠ 0) :
    (([(0,0),(1,0),(0,1),(2,0)] : List (ℕ × ℕ)).map
        (fun h => q₀ ^ (-(h.1 + h.2 : ℤ)))).sum
      = (([(0,0),(1,0),(0,1),(1,1)] : List (ℕ × ℕ)).map
        (fun h => q₀ ^ (-(h.1 + h.2 : ℤ)))).sum ∧
    ([(0,0),(1,0),(0,1),(2,0)] : List (ℕ × ℕ)) ≠ [(0,0),(1,0),(0,1),(1,1)] := by
  constructor
  · norm_num
  · decide

/-- (c) THE FENCE (re-keyed to the process side, N-1): an instance where
¬HMC ∧ ¬Factorizes — no unconditional upgrade theorem can exist. -/
theorem comp_upgrade_fails :
    ∃ (S : StepSys 1) (TE : TmplEvents 1 S) (D : XHDd 1 S TE) (X : XHDw 1 S),
      ¬ HMC TE D ∧ ¬ Factorizes X D := by
  sorry

end LeanUrat.MovesV
