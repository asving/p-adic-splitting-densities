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

/-- NAMED OPEN INSTANTIATION DUTY (M4 soundness repair; pins RESTATED at
the ROUND-4 M1 repair, 2026-07-29 — the old record claimed the pins
"exclude every degenerate unrelated witness"; they did not).
EXACT PIN INVENTORY (boundary-record rule):
TIED, table side (option (a), STRENGTHENED): `TablePins C T` — VType/State
(CellIdx-carrying)/Out equivs, real `Wloc`/`Wstate` bounds, odata rosters
in (size, δ, status-with-target-skeleton); proved at `tableShape_inst`'s
compiled witness.  TIED, measured side: ONLY the guarded |Box| card tie at
V's pools (as in `ledgerIV_inst`).
NOT TIED (option (b), SCOPED): `M.Pools`, cells, events, masses, rows,
entrances, marked values, the RatBurdens polynomial data themselves, and
the witness's identity with `tableShape_inst`'s result — a pin-satisfying
witness can still carry degenerate measured-side data; the pins CONSTRAIN,
they do not determine.  FENCE-RULE RECORD: hard M-side structure ties
could make the ∃ FALSE for adversarial V (the M1 failure mode).
INSTANTIATION ATTEMPT (recorded): the RatBurdens data (countS/geom
polynomial packs) must come from `cellPolyPack`'s sizeP/count wiring + the
V3 initrat `PolyGeom` packs — the V7-4 field-map unit; stays the named
sorried duty. -/
theorem ratBurdens_exists {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hTie : MDomTie V TE X.d) (J : JCells n C S V) (hEU : EntU V)
    (hEC : EntCount V) (hA : AffEnt n) :
    ∃ (T : MovesS.TableShape n) (M : MovesS.MeasuredSide T),
      TablePins C T ∧
      (∀ q₀ ∈ V.Pools, ∀ N : ℕ, Nonempty (V.Box q₀ N) →
        Fintype.card (M.Box q₀ N) = @Fintype.card _ (V.finB q₀ N)) ∧
      Nonempty (MovesS.RatBurdens T M) := by
  sorry

end LeanUrat.MovesV
