/-  MovesV unit V7-5c `ratBurdens_inst` leg (d) + assembly — cellP REVERTED
    to the sizeP wiring (F-5); the nonemptiness step `cell_ne_inst`
    displayed; the assembled Nonempty (RatBurdens T M) under the stated
    premises. -/
import LeanUrat.MovesV.V7_rbB
import LeanUrat.MovesV.V7_ts

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- the roster lemma (REV 4, G-1's displayed nonemptiness step): pick a zc
history (zc_ne), apply productivity (out_ne), classify (cellOfA/cellOfAT). -/
theorem cell_ne_inst {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (αc : S.Cell) {q₀ : ℚ} (hq : q₀ ∈ S.Pools) :
    Nonempty (V.CellOf αc) := by
  obtain ⟨x, hzc⟩ := S.zc_ne q₀ hq αc
  rcases S.out_ne q₀ hq αc x hzc with ⟨β, m, h, ha⟩ | ⟨v, m, h, ha⟩
  · exact ⟨(V.toCtsCells.stepKey (Sum.inl ⟨β, m, h, ha.some⟩)).1⟩
  · exact ⟨(V.toCtsCells.stepKey (Sum.inr ⟨v, m, h, ha.some⟩)).1⟩

/-- NAMED OPEN INSTANTIATION DUTY (M4 soundness repair, ratification
verdict 2026-07-29; WITNESS-PINNED at the final-ratification M-seam repair
— the verdict: "the existential conclusions do not state that their
witnesses are the table and measured system constructed from the supplied
`C`, `V`, or `X`"): the E-phase `∨ True` escape is DELETED; the ∃-duty now
pins the TABLE side to the CTS carriers (`VType ≃ VLabel n`, per-block
`State e ≃ StateOf n e` — `tableShape_inst` satisfies them) and the
measured side's box cardinalities to V's (guarded card tie, as in
`ledgerIV_inst`).  INSTANTIATION ATTEMPT (recorded): the RatBurdens data
(countS/geom polynomial packs) must come from `cellPolyPack`'s sizeP/count
wiring + the V3 initrat `PolyGeom` packs — the V7-4 field-map unit; stays
the named sorried duty.  Quantifier record as before: `Nonempty (RatBurdens
T M)` at ARBITRARY (T, M) would be FALSE (the M1 failure mode); hard
M-side structure ties would risk the same (fence-rule record). -/
theorem ratBurdens_exists {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hTie : MDomTie V TE X.d) (J : JCells n C S V) (hEU : EntU V)
    (hEC : EntCount V) (hA : AffEnt n) :
    ∃ (T : MovesS.TableShape n) (M : MovesS.MeasuredSide T),
      Nonempty (T.VType ≃ VLabel n) ∧
      (∀ e, Nonempty (T.State e ≃ StateOf n e)) ∧
      (∀ q₀ ∈ V.Pools, ∀ N : ℕ, Nonempty (V.Box q₀ N) →
        Fintype.card (M.Box q₀ N) = @Fintype.card _ (V.finB q₀ N)) ∧
      Nonempty (MovesS.RatBurdens T M) := by
  sorry

end LeanUrat.MovesV
