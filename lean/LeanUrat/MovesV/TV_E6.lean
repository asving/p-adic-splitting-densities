/-  TV-E6 (BRIDGE BP3, cluster c4; E-phase skeleton) — LedgerIV GROUPS
    (8)-(9) at the measuredOf witness: init_agg / init_count /
    ent_count_card / comp_once.
    Blueprint: lean/notes/BRIDGE_BP3_TV_2026-07-30.md §3.E + §4 (TV-E6).
    deps: TV-E1, TV-E2.  Consumer: TV-E7 (assembly).
    Statements = the `MovesS.LedgerIV` fields (MovesS/Defs:249-262)
    transcribed VERBATIM at M := measuredOf V X cp hfin.
    Sketch: init_agg from hEU + semilin_sum_exact + the finite EntIx
    re-index (the V5-6 comp_agg machinery, V5_compagg); init_count from
    V.ent_card (division-free form → the card form via V.box_card);
    ent_count_card rfl-genre (the V7-6a2 / V7_livA2 precedent) at the
    TV-E2 entrance-block field map; comp_once via the V7_livB
    HasSum.mul_left pattern at the ιshH weights.
    HYPOTHESIS-ROW RESOLUTION: ledgerIV_inst's own row verbatim + hfin
    (see the TV-E3 header record).  If the ιsh legs turn out to need
    AffEnt/EntDomOrder0 (the V7_rbB iota route's premises, NOT in
    ledgerIV_inst's row), that is a named-hypothesis fence event to
    surface, not to improvise. -/
import LeanUrat.MovesV.TV_E2
import LeanUrat.MovesV.V7_livC

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.MovesV

/-- TV-E6(a) [LedgerIV group (8), init_agg]: the state entrance value is the
finite entrance-shape aggregate (verbatim `MovesS.LedgerIV.init_agg` at
measuredOf). -/
theorem measuredOf_init_agg {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hHMC : HMC TE X.d)
    (hb : P1CtblAdd V X.w) (hc : P1NullRem V X.w)
    (hd : P1FixedHeightExact V X.w)
    (hEC : EntCount V) (hEU : EntU V) (hfin : Finite (Skeleton n)) :
    ∀ (e : ℕ) (τ : (ctsTable C hfin).State e) (q₀ : ℚ),
      q₀ ∈ (measuredOf V X cp hfin).Pools →
      (measuredOf V X cp hfin).activeState q₀ e τ →
      (measuredOf V X cp hfin).ιval e τ q₀
        = ∑ ε : (measuredOf V X cp hfin).EntShape e τ,
            (measuredOf V X cp hfin).ιsh e τ ε q₀ := by
  sorry

/-- TV-E6(b) [LedgerIV group (8), init_count]: the fixed-height entrance
weight counts its event, eventually (verbatim `MovesS.LedgerIV.init_count`
at measuredOf; V.ent_card → card form via box_card). -/
theorem measuredOf_init_count {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hHMC : HMC TE X.d)
    (hb : P1CtblAdd V X.w) (hc : P1NullRem V X.w)
    (hd : P1FixedHeightExact V X.w)
    (hEC : EntCount V) (hEU : EntU V) (hfin : Finite (Skeleton n)) :
    ∀ (e : ℕ) (τ : (ctsTable C hfin).State e)
      (ε : (measuredOf V X cp hfin).EntShape e τ)
      (h : (measuredOf V X cp hfin).Hgt),
      h ∈ (measuredOf V X cp hfin).ιDom e τ ε →
      ∀ q₀ ∈ (measuredOf V X cp hfin).Pools,
      (measuredOf V X cp hfin).activeState q₀ e τ → ∃ N₀, ∀ N ≥ N₀,
      (measuredOf V X cp hfin).ιshH e τ ε h q₀
          * (Fintype.card ((measuredOf V X cp hfin).Box q₀ N) : ℝ)
        = (((measuredOf V X cp hfin).entEvtH e τ ε h q₀ N).card : ℝ) := by
  sorry

/-- TV-E6(c) [LedgerIV group (8), ent_count_card]: the entrance census at its
own level IS the entrance count (verbatim `MovesS.LedgerIV.ent_count_card`
at measuredOf; rfl-genre at the TV-E2 field map — the V7_livA2 precedent). -/
theorem measuredOf_ent_count_card {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hHMC : HMC TE X.d)
    (hb : P1CtblAdd V X.w) (hc : P1NullRem V X.w)
    (hd : P1FixedHeightExact V X.w)
    (hEC : EntCount V) (hEU : EntU V) (hfin : Finite (Skeleton n)) :
    ∀ (e : ℕ) (τ : (ctsTable C hfin).State e)
      (ε : (measuredOf V X cp hfin).EntShape e τ) (q₀ : ℚ),
      q₀ ∈ (measuredOf V X cp hfin).Pools →
      (measuredOf V X cp hfin).activeState q₀ e τ →
      ((measuredOf V X cp hfin).entInst e τ ε q₀
          ((measuredOf V X cp hfin).entLvl e τ ε)).card
        = (measuredOf V X cp hfin).entCount e τ ε q₀ := by
  sorry

/-- TV-E6(d) [LedgerIV group (9), comp_once]: THE one entrance height sum
(verbatim `MovesS.LedgerIV.comp_once` at measuredOf; the V7_livB
HasSum.mul_left pattern). -/
theorem measuredOf_comp_once {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hHMC : HMC TE X.d)
    (hb : P1CtblAdd V X.w) (hc : P1NullRem V X.w)
    (hd : P1FixedHeightExact V X.w)
    (hEC : EntCount V) (hEU : EntU V) (hfin : Finite (Skeleton n)) :
    ∀ (e : ℕ) (τ : (ctsTable C hfin).State e)
      (ε : (measuredOf V X cp hfin).EntShape e τ) (q₀ : ℚ),
      q₀ ∈ (measuredOf V X cp hfin).Pools →
      (measuredOf V X cp hfin).activeState q₀ e τ →
      HasSum (fun h : (measuredOf V X cp hfin).ιDom e τ ε =>
          (measuredOf V X cp hfin).ιshH e τ ε h q₀)
        ((measuredOf V X cp hfin).ιsh e τ ε q₀) := by
  sorry

end LeanUrat.MovesV
