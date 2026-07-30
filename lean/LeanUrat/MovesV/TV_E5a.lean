/-  TV-E5a (BRIDGE BP3, cluster c4; E-phase skeleton) — THE no_entry/rowVal
    VOCABULARY-BRIDGE PROBE GATE (runs BEFORE the TV-E5b prover).
    Blueprint: lean/notes/BRIDGE_BP3_TV_2026-07-30.md §3.E + §4 (TV-E5a);
    [REV 2, finding 10 — NEW probe gate]; risk R5.
    deps: TV-E1, TV-E2, TV-F1 (cp packs — the F1 pack layer is the
    vocabulary the bridge crosses; the statement below needs only cp).
    Consumer: TV-E5b (act_target).
    THE PROBE'S CHARGE (blueprint, verbatim): "state (as a standalone lemma
    attempt, no LedgerIV assembly) the bridge `Σ_{o targeting β, kcol}
    (μcell-sum rowVal) = (the no_entry T-poly evaluation)` at inactive β,
    via cp's count laws + rep_indep, and either PROVE it or record the
    exact vocabulary gap (which cp law is missing, at which route case)."
    E-PHASE RESOLUTION (recorded): at inactive β the RHS T-poly evaluations
    vanish by `no_entry` (V4_act:11 — ValA.tbl_count + ValA.tgt_supported),
    so the bridge's Lean face is the VANISHING of the β-targeting rowVal
    sum — exactly what act_target's discharge consumes; the intermediate
    "rowVal = count-poly × geometry" identification is the proof route
    (μcellH = cntc·q₀^(−E) pointwise; cp.count reads cntc as cp.P eval;
    tgt_supported kills the counts at an inactive target), not a separate
    typed claim.  GUARDS (recorded): source-activity (hact) IS carried —
    it is no_entry's own guard AND the guard kstep_one supplies in the
    guarded-kstep fallback; the bridge stated here is the COMMON content
    both kstep definitions need (finding 4: the fallback relocates, never
    avoids, this bridge).  The inactive-SOURCE case of act_target is NOT
    probed here — it is the residual the E5b prover resolves via the
    kstep-1 co-design pin (TV-E2), escalating per R5 if neither definition
    closes.  no_entry's `hne : (V.mdom d).comps ≠ []` premise is NOT
    pre-added: if the probe needs it, THAT is a recordable vocabulary gap
    (named-hypothesis escalation, never a silent statement weakening). -/
import LeanUrat.MovesV.TV_E2
import LeanUrat.MovesV.TV_F1
import LeanUrat.MovesV.V7_livC

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.style.openClassical false

namespace LeanUrat.MovesV
open scoped Classical

/-- TV-E5a [the bridge probe]: at a pool point with ACTIVE source τ and
INACTIVE target β (V-side activity, standalone — no dependence on the E2
activity pin), the β-targeting kcol rowVal sum vanishes.  PROBE DISCIPLINE:
prove OR record the exact vocabulary gap; if the gap survives both kstep
readings, TV-E5b escalates (named hypothesis on ledgerIV_inst, risk R5) —
never weaken LedgerIV. -/
theorem measuredOf_act_bridge {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hfin : Finite (Skeleton n)) :
    ∀ (e : ℕ) (τ β : (ctsTable C hfin).State e) (q₀ : ℚ),
      q₀ ∈ V.Pools →
      V.activeState q₀ (V.toStepCells.symm τ.1) →
      ¬ V.activeState q₀ (V.toStepCells.symm β.1) →
      ∑ o ∈ {o : (ctsTable C hfin).Out e τ |
            MovesS.routeOf ((ctsTable C hfin).odata e τ o) = .kcol ∧
            ∃ μ ∈ ((ctsTable C hfin).odata e τ o).mem,
              ∃ h : μ.size = e, h ▸ μ.status = Sum.inr β
          }.toFinset,
          (measuredOf V X cp hfin).rowVal e τ o q₀ = 0 := by
  sorry

end LeanUrat.MovesV
