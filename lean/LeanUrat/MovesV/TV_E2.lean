/-  TV-E2 (BRIDGE BP3, cluster c4; E-phase skeleton) — `measuredOf` DATA
    BLOCK 2: entrance block + activeState + rowVal + THE THREE-CASE kstep
    RECURSION, pinned on TV-E1's shared def.
    Blueprint: lean/notes/BRIDGE_BP3_TV_2026-07-30.md §3.E + §4 (TV-E2).
    deps: TV-E1.  Consumers: TV-E3/E4/E5a/E5b/E6, TV-E7; cluster F (F2).
    FIELD MAP (block 2, recorded here; the def itself lives in TV-E1 —
    resolution (2) of the TV-E1 header):
    - `EntShape e τ` := the V-side entrance index `V.EntIx β₀` at
      β₀ := toStepCells.symm τ.1 (EntIx-based; finiteness is DERIVABLE —
      the `iotaValV` def's own haveI chain `template_finite n` +
      `Subtype.finite`, V3_aggfullB, supplies `finE`);
    - entInst/entEvt(H)/entLvl/entCount/hent/Went from V's census fields;
      `ιshH`/`ιsh`/`ιval` := ιshH (Defs:1160) / iotaShV / iotaValV
      (V3_aggfullB) — the per-EntIx pins need the cast across the EntShape
      pin and are the E-fleet's transport deliverable (finding 13); the
      cast-free `ιval` pin is typed below;
    - `activeState` := V.activeState ∘ toStepCells.symm (decA classical);
    - `rowVal` := the per-outcome μcell sum over the outcome's cell fiber
      at the E1 representative ("FORCED up to rep_indep; define it as that
      sum so rep_indep is near-rfl" — §3.E).  NO unguarded ∀-Rep pin is
      typed: μcellH reads the representative's history, so the x-free form
      holds only under rep_indep's own guards — the guarded law IS TV-E4's
      `measuredOf_rep_indep`, not a definitional pin (recorded resolution);
    - `kstep` := the three-case recursion AS DISPLAYED in §3.E [REV 2,
      finding 4]: kstep 0 = Kronecker delta (FORCED by hmc at k = 0),
      kstep 1 = kstep_one's RHS transcribed, kstep (k+2) = the γ-sum
      recursion.  The kstep-1 pin is a CO-DESIGN PIN adjustable ONLY per
      the TV-E5a probe's outcome (the activity-guarded fallback — kstep 1
      := if activeState β then Σ… else 0 — relocates the same bridge into
      kstep_one's inactive-β case; NOT an exit, finding 4);
    - markedVal/gwt residue fields: docstring-recorded, prover-typed. -/
import LeanUrat.MovesV.TV_E1
import LeanUrat.MovesV.V3_aggfullB

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.MovesV
open scoped Classical

/-- TV-E2 CO-DESIGN PIN [entrance carrier]: `EntShape e τ = V.EntIx
(toStepCells.symm τ.1)` — the V-side entrance index at the state's own CTS
cell (blueprint §3.E "EntShape e τ := the V-side entrance index at β₀ :=
toStepCells.symm ⟨s, α⟩ (EntIx-based)").  finE at this carrier: derivable
(see file header). -/
theorem measuredOf_entShape {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V)
    (hfin : Finite (Skeleton n)) :
    ∀ (e : ℕ) (τ : (ctsTable C hfin).State e),
      (measuredOf V X cp hfin).EntShape e τ
        = V.EntIx (V.toStepCells.symm τ.1) := by
  sorry

/-- TV-E2 CO-DESIGN PIN [activity]: `activeState := V.activeState ∘
toStepCells.symm` (decA classical), read through the literal table's state
carrier τ = ⟨⟨s, α⟩, hblk⟩. -/
theorem measuredOf_activeState {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V)
    (hfin : Finite (Skeleton n)) :
    ∀ (q₀ : ℚ) (e : ℕ) (τ : (ctsTable C hfin).State e),
      (measuredOf V X cp hfin).activeState q₀ e τ
        ↔ V.activeState q₀ (V.toStepCells.symm τ.1) := by
  sorry

/-- TV-E2 CO-DESIGN PIN [kstep, case 0]: the Kronecker delta — FORCED by
`hmc` at k = 0 ("it reads kstep 1 = Σ_γ kstep 0 τ γ · kstep 1 γ β — so
kstep 0 is FORCED to be the Kronecker delta, and hmc's k = 0 case is
`Finset.sum_eq_single`, NOT rfl", §3.E REV 2). -/
theorem measuredOf_kstep_zero {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V)
    (hfin : Finite (Skeleton n)) :
    ∀ (e : ℕ) (τ β : (ctsTable C hfin).State e) (q₀ : ℚ),
      (measuredOf V X cp hfin).kstep 0 e τ β q₀
        = if τ = β then 1 else 0 := by
  sorry

/-- TV-E2 CO-DESIGN PIN [kstep, case 1]: kstep_one's RHS, transcribed
verbatim from `MovesS.LedgerIV.kstep_one` (MovesS/Defs:238-242) — the sum
of rowVal over the β-targeting kcol outcomes.  ADJUSTABLE ONLY per the
TV-E5a probe outcome (finding 4: the activity-guarded fallback relocates
the same no_entry/rowVal bridge; if the E5a probe records a gap, do NOT
flip definitions — escalate, risk R5). -/
theorem measuredOf_kstep_one_def {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V)
    (hfin : Finite (Skeleton n)) :
    ∀ (e : ℕ) (τ β : (ctsTable C hfin).State e) (q₀ : ℚ),
      (measuredOf V X cp hfin).kstep 1 e τ β q₀
        = ∑ o ∈ {o : (ctsTable C hfin).Out e τ |
              MovesS.routeOf ((ctsTable C hfin).odata e τ o) = .kcol ∧
              ∃ μ ∈ ((ctsTable C hfin).odata e τ o).mem,
                ∃ h : μ.size = e, h ▸ μ.status = Sum.inr β
            }.toFinset,
            (measuredOf V X cp hfin).rowVal e τ o q₀ := by
  sorry

/-- TV-E2 CO-DESIGN PIN [kstep, case k+2]: the γ-sum recursion (the γ-sum is
finite via `T.fin`; equality via `T.deq` — §3.E REV 2 display, transcribed). -/
theorem measuredOf_kstep_succ {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V)
    (hfin : Finite (Skeleton n)) :
    ∀ (k : ℕ) (e : ℕ) (τ β : (ctsTable C hfin).State e) (q₀ : ℚ),
      (measuredOf V X cp hfin).kstep (k + 2) e τ β q₀
        = ∑ γ : (ctsTable C hfin).State e,
            (measuredOf V X cp hfin).kstep (k + 1) e τ γ q₀
              * (measuredOf V X cp hfin).kstep 1 e γ β q₀ := by
  sorry

/-- TV-E2 CO-DESIGN PIN [ιval]: the state-level entrance value is the V-side
EntIx aggregate `iotaValV` at the state's own CTS cell (the cast-free member
of the ι-family pins; ιshH/ιsh per-EntIx pins ride the EntShape cast —
transport layer, finding 13). -/
theorem measuredOf_ival {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V)
    (hfin : Finite (Skeleton n)) :
    ∀ (e : ℕ) (τ : (ctsTable C hfin).State e) (q₀ : ℚ),
      (measuredOf V X cp hfin).ιval e τ q₀
        = iotaValV V X.sEnt (V.toStepCells.symm τ.1) q₀ := by
  sorry

end LeanUrat.MovesV
