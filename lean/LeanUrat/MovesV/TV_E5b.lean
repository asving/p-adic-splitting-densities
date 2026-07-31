/-  TV-E5b (BRIDGE BP3, cluster c4; E-phase skeleton) — LedgerIV GROUPS
    (6)-(7) at the measuredOf witness: kstep_one / hmc / act_target.
    Blueprint: lean/notes/BRIDGE_BP3_TV_2026-07-30.md §3.E + §4 (TV-E5b).
    deps: TV-E2, TV-E5a (the probe MUST have run first — scheduling
    constraint §4).  Consumer: TV-E7 (assembly).
    Statements = the `MovesS.LedgerIV` fields (MovesS/Defs:238-247)
    transcribed VERBATIM at M := measuredOf V X cp hfin.
    Sketch: kstep_one rfl-genre at TV-E2's recursive kstep (the co-design
    pin measuredOf_kstep_one_def); hmc's k = 0 case by
    `Finset.sum_eq_single` at the Kronecker kstep 0 (§3.E REV 2 — NOT
    rfl), k ≥ 1 cases rfl-genre through the (k+2)-case pin; act_target
    from TV-E5a's bridge.  [REV 2, finding 4] if E5a records a gap, do NOT
    flip kstep definitions and retry — the fallback activity-guarded kstep
    relocates the same bridge into kstep_one's inactive-β case; ESCALATE
    directly (named hypothesis on ledgerIV_inst; risk R5).
    HYPOTHESIS-ROW RESOLUTION: ledgerIV_inst's own row verbatim + hfin
    (see the TV-E3 header record). -/
import LeanUrat.MovesV.TV_E5a

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.style.openClassical false

namespace LeanUrat.MovesV
open scoped Classical

/-- TV-E5b(a) [LedgerIV group (6), kstep_one]: the guarded one-step law —
kstep 1 is the β-targeting kcol rowVal sum (verbatim
`MovesS.LedgerIV.kstep_one` at measuredOf; rfl-genre at the TV-E2 pin). -/
theorem measuredOf_kstep_one {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hHMC : HMC TE X.d)
    (hb : P1CtblAdd V X.w) (hc : P1NullRem V X.w)
    (hd : P1FixedHeightExact V X.w)
    (hEC : EntCount V) (hEU : EntU V) (hfin : Finite (Skeleton n)) :
    ∀ (e : ℕ) (τ β : (ctsTable C hfin).State e) (q₀ : ℚ),
      q₀ ∈ (measuredOf V X cp hfin).Pools →
      (measuredOf V X cp hfin).activeState q₀ e τ →
      (measuredOf V X cp hfin).kstep 1 e τ β q₀
        = ∑ o ∈ {o : (ctsTable C hfin).Out e τ |
              MovesS.routeOf ((ctsTable C hfin).odata e τ o) = .kcol ∧
              ∃ μ ∈ ((ctsTable C hfin).odata e τ o).mem,
                ∃ h : μ.size = e, h ▸ μ.status = Sum.inr β
            }.toFinset,
            (measuredOf V X cp hfin).rowVal e τ o q₀ := by
  intro e τ β q₀ hq hact
  show kstepOne V X.w cp hfin e τ β q₀ = _
  unfold kstepOne
  split
  · rfl
  · next hβin =>
      symm
      exact measuredOf_act_bridge V X cp hVA hfin e τ β q₀ hq hact hβin

/-- TV-E5b(b) [LedgerIV group (6), hmc]: the guarded Chapman-Kolmogorov
factorization at every k (verbatim `MovesS.LedgerIV.hmc` at measuredOf;
k = 0 by `Finset.sum_eq_single` at the Kronecker kstep 0, k ≥ 1 rfl-genre
at the recursion pin). -/
theorem measuredOf_hmc {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hHMC : HMC TE X.d)
    (hb : P1CtblAdd V X.w) (hc : P1NullRem V X.w)
    (hd : P1FixedHeightExact V X.w)
    (hEC : EntCount V) (hEU : EntU V) (hfin : Finite (Skeleton n)) :
    ∀ (k : ℕ) (e : ℕ) (τ β : (ctsTable C hfin).State e) (q₀ : ℚ),
      q₀ ∈ (measuredOf V X cp hfin).Pools →
      (measuredOf V X cp hfin).activeState q₀ e τ →
      (measuredOf V X cp hfin).kstep (k + 1) e τ β q₀
        = ∑ γ : (ctsTable C hfin).State e,
            (measuredOf V X cp hfin).kstep k e τ γ q₀
              * (measuredOf V X cp hfin).kstep 1 e γ β q₀ := by
  intro k e τ β q₀ hq hact
  cases k with
  | zero =>
      symm
      rw [Finset.sum_eq_single τ (fun γ _ hγ => by
          show (if τ = γ then (1 : ℝ) else 0)
              * (measuredOf V X cp hfin).kstep 1 e γ β q₀ = 0
          rw [if_neg (fun h => hγ h.symm), zero_mul])
        (fun habs => absurd (Finset.mem_univ τ) habs)]
      show (if τ = τ then (1 : ℝ) else 0)
          * (measuredOf V X cp hfin).kstep 1 e τ β q₀ = _
      rw [if_pos rfl, one_mul]
  | succ k => rfl

/-- TV-E5b(c) [LedgerIV group (7), act_target]: one-step mass into an
inactive target vanishes (verbatim `MovesS.LedgerIV.act_target` at
measuredOf; from TV-E5a's bridge — note act_target carries NO source-
activity guard: the inactive-source residual is resolved at the kstep-1
co-design pin, escalation R5 if neither reading closes). -/
theorem measuredOf_act_target {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hHMC : HMC TE X.d)
    (hb : P1CtblAdd V X.w) (hc : P1NullRem V X.w)
    (hd : P1FixedHeightExact V X.w)
    (hEC : EntCount V) (hEU : EntU V) (hfin : Finite (Skeleton n)) :
    ∀ (e : ℕ) (τ β : (ctsTable C hfin).State e) (q₀ : ℚ),
      q₀ ∈ (measuredOf V X cp hfin).Pools →
      ¬ (measuredOf V X cp hfin).activeState q₀ e β →
      (measuredOf V X cp hfin).kstep 1 e τ β q₀ = 0 := by
  intro e τ β q₀ hq hin
  show kstepOne V X.w cp hfin e τ β q₀ = 0
  unfold kstepOne
  rw [if_neg (show ¬ V.activeState q₀ (V.toStepCells.symm β.1) from hin)]

end LeanUrat.MovesV
