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
hEmptyT + the ADJUDICATED count-tie premises and the instance wiring, the
built `PolyGeomLaws` is inhabited.

ADJ-4 (the wave-A2 record in
`lean/notes/LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md`: "pgLaws count-tie
premises (scount_val REFUTABLE via the scaling freedom — the ValA tbl_count
tie typed as premises)").  At arbitrary-RB generality nothing ties RB.tgP's
countT/countS factors to anything (prover fleet batch 2 + B6 re-verified):
(1) `tcount_val` needs countT INTEGER-VALUED at pools — RatBurdens pins only
the PRODUCT via tg_interp + degrees, so no choice of tCount can close it;
(2) `scount_val` is REFUTABLE — rescale countS ↦ 2·countS, geom ↦ geom/2:
val, degrees, and all RatBurdens laws survive while the cell-census equality
breaks.  The adjudicated repair types the V-side COUNT SEMANTICS as premises
of THIS statement, per the blueprint's §2.F warrant: "the COUNT SEMANTICS is
ValA's field content (§2.F note + V2-4 — the rev-1 `tbl_count` field moved
there, resolving design-freedom slot (3))" (MOVESV_LEAN_BLUEPRINT REV 9,
CTS-T block):
- `hTCount` — the T-count integer-valuedness law: countT.eval ∈ ℕ at every
  pool (the ValA.tbl_count/hEmptyT semantics read at the built burden);
- `hSCount` — the cell-census tie: countS.eval = the outcome fiber's
  cell-instance census sum at active states (killing the scaling freedom).
The identification of these premises against the BUILT V7-5a burden stays
theorem-under-burdens on the instance side, never self-supplied here. -/
theorem polygeom_count_laws {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {T : MovesS.TableShape n}
    {M : MovesS.MeasuredSide T} (RB : MovesS.RatBurdens T M)
    {TE : TmplEvents n S} {D : XHDd n S TE}
    (hVA : ValA n C S V) (U : XHDu n S) (hTie : MDomTie V TE D)
    (hE : HEmptyT V)
    (hTCount : ∀ (e : ℕ) (τ : T.State e) (o : T.Out e τ), ∀ q₀ ∈ M.Pools,
      ∃ k : ℕ, (RB.tgP e τ o).countT.eval q₀ = (k : ℚ))
    (hSCount : ∀ (e : ℕ) (τ : T.State e) (o : T.Out e τ), ∀ q₀ ∈ M.Pools,
      M.activeState q₀ e τ →
      (RB.tgP e τ o).countS.eval q₀
        = ∑ c ∈ M.cells e τ o,
            ((M.cellInst e τ c q₀ (M.cellLvl e τ c)).card : ℚ)) :
    Nonempty (MovesS.PolyGeomLaws T M RB) := by
  refine ⟨{
    tCount := fun e τ o q₀ => ((RB.tgP e τ o).countT.eval q₀).num.toNat
    tcount_val := ?_
    scount_val := hSCount
    tcount_deg := fun e τ o => (RB.tgP e τ o).degT_le.trans_eq (RB.tg_degT e τ o)
    scount_deg := fun e τ o => (RB.tgP e τ o).degS_le.trans_eq (RB.tg_degS e τ o) }⟩
  intro e τ o q₀ hq
  obtain ⟨k, hk⟩ := hTCount e τ o q₀ hq
  rw [hk]
  simp

end LeanUrat.MovesV
