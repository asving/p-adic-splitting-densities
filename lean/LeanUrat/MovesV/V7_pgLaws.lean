/-  MovesV unit V7-9 `polygeom_count_laws` (REDESIGNED CARD-SIDE at REV 8,
    Codex7 N8; repD DISPLAYED at REV 9, N-5) — supplies the built
    `MovesS.PolyGeomLaws T M RB`: the ℕ-valued TOTAL tCount via the
    representative wrapper `repD` + the THREE explicit dispatches (pool dite,
    the e ∈ Icc junk-total dite, the continuing/terminal dispatch).  The
    tCount identification duty (tbl_count base points + u_T across domains
    (MDomTie) + evt_card) is theorem-under-burdens, never self-supplied;
    `hEmptyT` is the displayed [1v] table-build clause. -/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesV.V2_valA
import LeanUrat.MovesV.V2_valB

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV
open Classical

/-- THE REPRESENTATIVE WRAPPER (REV 9, N-5 — slot 12's recorded choice
step, now a decl). -/
noncomputable def repD {n : ℕ} {T : MovesS.TableShape n}
    (M : MovesS.MeasuredSide T) (e : ℕ) (he : e ∈ Finset.Icc 1 n)
    (τ : T.State e) : M.Rep e τ :=
  (M.rep_ne e he τ).some

/-- THE hEmptyT CLAUSE (VAL(a) at a domain-empty row — a [1v] table-build
clause, owner-tagged; decide at the gate rosters). -/
def HEmptyT {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) : Prop :=
  ∀ (d : MoveData n C), (V.mdom d).comps = [] →
    ∀ q₀ ∈ V.Pools, ((C.T d.s d.m d.o d.α d.tix).eval q₀ : ℚ) = 0

open Classical in
/-- THE ℕ-VALUED TOTAL COUNT (the three dispatches displayed; the outcome
dispatch keyed by a continuing-datum selector at the abstract layer —
`dOf`/`dTOf` are V7-4a's outcome→datum one-liners at the instance).  Junk
branches carry NO law (every built law is `∀ q₀ ∈ M.Pools` at e ∈ Icc 1 n). -/
noncomputable def tCountV {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {T : MovesS.TableShape n}
    (M : MovesS.MeasuredSide T)
    (dOf : ∀ (e : ℕ) (τ : T.State e), T.Out e τ → Option (MoveData n C))
    (dTOf : ∀ (e : ℕ) (τ : T.State e), T.Out e τ →
      Option (Σ v : VLabel n, TermData n C v))
    (xOf : ∀ (d : MoveData n C) (q₀ : ℚ), q₀ ∈ V.Pools →
      {x : S.Hist q₀ (V.toStepCells.symm d.src) // S.zc x})
    (xTOf : ∀ {v : VLabel n} (d : TermData n C v) (q₀ : ℚ), q₀ ∈ V.Pools →
      {x : S.Hist q₀ (V.toStepCells.symm ⟨d.s, d.α⟩) // S.zc x})
    (e : ℕ) (τ : T.State e) (o : T.Out e τ) (q₀ : ℚ) : ℕ :=
  if hq : q₀ ∈ V.Pools then
    if he : e ∈ Finset.Icc 1 n then
      match dOf e τ o with
      | some d =>
          (match (V.mdom d).comps with
           | [] => 0
           | comp :: _ => S.cntraw (V.moveOf d) (xOf d q₀ hq).1 comp.base)
      | none =>
          match dTOf e τ o with
          | some ⟨v, d⟩ =>
              (match (V.mdomT d).comps with
               | [] => 0
               | comp :: _ =>
                   S.cntrawT (V.moveOfT d) (xTOf d q₀ hq).1 comp.base)
          | none => 0
    else 0
  else 0

/-- THE SUPPLY (theorem-under-burdens): GIVEN ValA + (XHD-u) + MDomTie +
hEmptyT and the instance wiring, the built `PolyGeomLaws` is inhabited. -/
theorem polygeom_count_laws {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {T : MovesS.TableShape n}
    {M : MovesS.MeasuredSide T} (RB : MovesS.RatBurdens T M)
    {TE : TmplEvents n S} {D : XHDd n S TE}
    (hVA : ValA n C S V) (U : XHDu n S) (hTie : MDomTie V TE D)
    (hE : HEmptyT V) :
    Nonempty (MovesS.PolyGeomLaws T M RB) := by
  sorry

end LeanUrat.MovesV
