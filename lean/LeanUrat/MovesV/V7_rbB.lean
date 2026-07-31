/-  MovesV unit V7-5b `ratBurdens_inst` leg (c) — ιP from V3-9c(a)'s
    per-component PolyGeoms under V7-4b's EntIx keying.
    QUEUE ITEM 14 EXECUTED (Asvin sign-off 2026-07-31; ledger
    lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md item 14): the ∃ below is
    RE-POINTED at `initRat_comp`'s FULL 4-conjunct existential — the old
    2-conjunct form (countS/geom only) DISCARDED conjuncts 3-4 (the countT
    census-interpolation clause and the evalAt value clause), which made the
    `SeamCoherent.iota_val`/`iota_count` legs (TV_F2) undischargeable from
    the choice-extracted pack (`iotaPGof`, TV_F1).  Conclusion now BYTE-
    IDENTICAL to `initRat_comp`'s (V3_initrat:41-48) at XsEnt := X.sEnt;
    consumers read the new conjuncts through the TV_F1 spec projections
    (`iotaPGof_census`/`iotaPGof_val`). -/
import LeanUrat.MovesV.V7_rbA
import LeanUrat.MovesV.V3_initrat

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem ratBurdens_iota {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (hEU : EntU V) (hEC : EntCount V) (hA : AffEnt n)
    (hdom : EntDomOrder0 V) (β₀ : S.Cell) (i : V.EntIx β₀) :
    ∃ P : MovesS.PolyGeom,
      P.countS = 1 ∧ P.geom = X.sEnt.Gent β₀ i ∧
      (∀ h : Hpt i.1.1.entDim, ((V.entDom i.1.1).comps.get i.1.2).Mem h →
        ∀ (hs : Order0Perimeter i.1.1 h), ∀ q₀ ∈ V.Pools,
        (P.countT.eval q₀ : ℚ)
          = V.entCensus (writeHeights i.1.1 h hs) β₀ q₀) ∧
      ∀ q₀ (hq : q₀ ∈ V.Pools), ∃ hok : P.val ∈ MovesS.OKat q₀,
        ((MovesS.evalAt q₀ ⟨P.val, hok⟩ : ℚ) : ℝ) = iotaShV V X.sEnt i q₀ :=
  initRat_comp V X.sEnt hEU hEC hA hdom β₀ i

end LeanUrat.MovesV
