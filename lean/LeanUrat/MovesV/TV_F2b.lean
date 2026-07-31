/-  TV-F2b (QUEUE ITEM 14 EXECUTION UNIT, 2026-07-31; Asvin sign-off — ledger
    lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md item 14) — the SeamCoherent
    ι-LEGS PROVED at the shared measuredOf witness.
    deps: TV-F2 (the seam carrier + packs), TV-E2 (the measuredOf field map).
    Consumers: the TV-F2 prover (`seam_coherence_exists` instantiates its
    iota_ok/iota_val/iota_count fields from these three theorems).

    WHAT ITEM 14 OPENED: `ratBurdens_iota` (V7_rbB) now carries
    `initRat_comp`'s FULL 4-conjunct existential; the TV-F1 spec projections
    `iotaPGof_census`/`iotaPGof_val` expose conjuncts 3-4 — exactly the
    content of `SeamCoherent.iota_count` and `SeamCoherent.iota_val` at the
    measuredOf witness, which the old 2-conjunct choice discarded.

    KEYING SCOPE (recorded): the legs hold for ANY `SeamKeys` whose `entKey`
    is the canonical projection (the `hK` pin below) — at the intended
    literal witness entKey IS this projection (E2 installs `EntShape e τ :=
    V.EntIx (V.toStepCells.symm τ.1)`), so the pin is `fun _ _ _ => rfl`
    there.  The datum/cellKey fields do not enter the ι-legs.

    REMAINING TV-F2 BLOCKS (record, per the item-14 charge): the `tg_val`
    leg stays open — rowVal at non-split routes ties the tgP pack (C.T ·
    Σⱼ Gc, the V2-5 table reading) to E2's μcell-sum `rowVal`, and that
    bridge is `val_b`'s content, gated on the named Phase-B row
    `RealizationComplete` (V2_valB:272; the V7_ctsm/V7_ledger `hRC` field —
    NOT dischargeable in-corpus).  `j_val`/`jcell_val`/`jcell_sum` remain
    with the F-prover (the μcellH re-index).  `seam_coherence_exists` keeps
    its ONE honest sorry covering those legs. -/
import LeanUrat.MovesV.TV_F2
import LeanUrat.MovesV.TV_E2

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.MovesV

/-- [item-14 helper] `evalAt` only reads the value of the packed subtype. -/
private theorem evalAt_val_congr {q₀ : ℚ} {a b : MovesS.Qq} (h : a = b)
    (ha : a ∈ MovesS.OKat q₀) (hb : b ∈ MovesS.OKat q₀) :
    MovesS.evalAt q₀ ⟨a, ha⟩ = MovesS.evalAt q₀ ⟨b, hb⟩ := by
  cases h; rfl

/-- [item-14 helper] the seam ι-pack at an entKey-canonical keying IS the
TV-F1 `iotaPGof` pack at the measured entrance index. -/
private theorem seamIotaP_canonical {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S} (X : XHD n S TE V)
    (cp : CellPolyPack n C S V) (hfin : Finite (Skeleton n))
    (hEU : EntU V) (hEC : EntCount V) (hA : AffEnt n) (hdom : EntDomOrder0 V)
    (K : SeamKeys V (ctsTable C hfin) (measuredOf V X cp hfin))
    (hK : ∀ e (τ : (ctsTable C hfin).State e)
      (ε : (measuredOf V X cp hfin).EntShape e τ),
      K.entKey e τ ε = ⟨V.toStepCells.symm τ.1, ε⟩)
    (e : ℕ) (τ : (ctsTable C hfin).State e)
    (ε : (measuredOf V X cp hfin).EntShape e τ) :
    seamIotaP V X hEU hEC hA hdom K e τ ε
      = iotaPGof V X hEU hEC hA hdom (V.toStepCells.symm τ.1) ε := by
  unfold seamIotaP
  rw [hK e τ ε]

/-- TV-F2b (ι-leg 1, `SeamCoherent.iota_ok` at measuredOf): the seam ι-pack
value is evaluation-regular at every pool point. -/
theorem measuredOf_iota_ok {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S} (X : XHD n S TE V)
    (cp : CellPolyPack n C S V) (hfin : Finite (Skeleton n))
    (hEU : EntU V) (hEC : EntCount V) (hA : AffEnt n) (hdom : EntDomOrder0 V)
    (K : SeamKeys V (ctsTable C hfin) (measuredOf V X cp hfin))
    (hK : ∀ e (τ : (ctsTable C hfin).State e)
      (ε : (measuredOf V X cp hfin).EntShape e τ),
      K.entKey e τ ε = ⟨V.toStepCells.symm τ.1, ε⟩) :
    ∀ (e : ℕ) (τ : (ctsTable C hfin).State e)
      (ε : (measuredOf V X cp hfin).EntShape e τ) (q₀ : ℚ),
      q₀ ∈ (measuredOf V X cp hfin).Pools →
      (seamIotaP V X hEU hEC hA hdom K e τ ε).val ∈ MovesS.OKat q₀ := by
  intro e τ ε q₀ hq
  rw [seamIotaP_canonical V X cp hfin hEU hEC hA hdom K hK e τ ε]
  exact (iotaPGof_val V X hEU hEC hA hdom (V.toStepCells.symm τ.1) ε q₀
    hq).choose

/-- TV-F2b (ι-leg 2, `SeamCoherent.iota_val` at measuredOf, ANY regularity
certificate): the seam ι-pack evaluates to the measured per-shape entrance
mass `ιsh` — conjunct 4 of the item-14 re-pointed `ratBurdens_iota`. -/
theorem measuredOf_iota_val {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S} (X : XHD n S TE V)
    (cp : CellPolyPack n C S V) (hfin : Finite (Skeleton n))
    (hEU : EntU V) (hEC : EntCount V) (hA : AffEnt n) (hdom : EntDomOrder0 V)
    (K : SeamKeys V (ctsTable C hfin) (measuredOf V X cp hfin))
    (hK : ∀ e (τ : (ctsTable C hfin).State e)
      (ε : (measuredOf V X cp hfin).EntShape e τ),
      K.entKey e τ ε = ⟨V.toStepCells.symm τ.1, ε⟩) :
    ∀ (e : ℕ) (τ : (ctsTable C hfin).State e)
      (ε : (measuredOf V X cp hfin).EntShape e τ) (q₀ : ℚ)
      (hq : q₀ ∈ (measuredOf V X cp hfin).Pools)
      (hok : (seamIotaP V X hEU hEC hA hdom K e τ ε).val ∈ MovesS.OKat q₀),
      ((MovesS.evalAt q₀
          ⟨(seamIotaP V X hEU hEC hA hdom K e τ ε).val, hok⟩ : ℚ) : ℝ)
        = (measuredOf V X cp hfin).ιsh e τ ε q₀ := by
  intro e τ ε q₀ hq hok
  obtain ⟨hok', hval⟩ :=
    iotaPGof_val V X hEU hEC hA hdom (V.toStepCells.symm τ.1) ε q₀ hq
  rw [evalAt_val_congr
    (congrArg MovesS.PolyGeom.val
      (seamIotaP_canonical V X cp hfin hEU hEC hA hdom K hK e τ ε))
    hok hok']
  exact hval

/-- TV-F2b (ι-leg 3, `SeamCoherent.iota_count` at measuredOf): the seam
ι-pack's countT interpolates the measured entrance count — conjunct 3 of the
item-14 re-pointed `ratBurdens_iota`, read at the component BASE point whose
order-0 perimeter certificate `hdom` mints (the item-11 genre). -/
theorem measuredOf_iota_count {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S} (X : XHD n S TE V)
    (cp : CellPolyPack n C S V) (hfin : Finite (Skeleton n))
    (hEU : EntU V) (hEC : EntCount V) (hA : AffEnt n) (hdom : EntDomOrder0 V)
    (K : SeamKeys V (ctsTable C hfin) (measuredOf V X cp hfin))
    (hK : ∀ e (τ : (ctsTable C hfin).State e)
      (ε : (measuredOf V X cp hfin).EntShape e τ),
      K.entKey e τ ε = ⟨V.toStepCells.symm τ.1, ε⟩) :
    ∀ (e : ℕ) (τ : (ctsTable C hfin).State e)
      (ε : (measuredOf V X cp hfin).EntShape e τ) (q₀ : ℚ),
      q₀ ∈ (measuredOf V X cp hfin).Pools →
      ((seamIotaP V X hEU hEC hA hdom K e τ ε).countT.eval q₀ : ℚ)
        = ((measuredOf V X cp hfin).entCount e τ ε q₀ : ℚ) := by
  intro e τ ε q₀ hq
  rw [seamIotaP_canonical V X cp hfin hEU hEC hA hdom K hK e τ ε]
  -- the component base point and its order-0 perimeter certificate
  have hbase := linset_base_mem ((V.entDom ε.1.1).comps.get ε.1.2)
  have hs : Order0Perimeter ε.1.1 ((V.entDom ε.1.1).comps.get ε.1.2).base :=
    hdom.comp ε.1.1 ε.1.2 hbase
  -- conjunct 3 at the base point
  have h1 := iotaPGof_census V X hEU hEC hA hdom (V.toStepCells.symm τ.1) ε
    ((V.entDom ε.1.1).comps.get ε.1.2).base hbase hs q₀ hq
  rw [h1]
  -- entCount IS the base-point instCensus (rfl), = the scoped census
  have hsome : writeHeights? ε.1.1 ((V.entDom ε.1.1).comps.get ε.1.2).base
      = some (writeHeights ε.1.1 ((V.entDom ε.1.1).comps.get ε.1.2).base hs) :=
    (Option.some_get (writeHeights_total_of_perimeter ε.1.1 _ hs)).symm
  have h2 : V.entCount ε q₀
      = V.entCensus
          (writeHeights ε.1.1 ((V.entDom ε.1.1).comps.get ε.1.2).base hs)
          (V.toStepCells.symm τ.1) q₀ := by
    show V.instCensus ε.1.1 ((V.entDom ε.1.1).comps.get ε.1.2).base
        (V.toStepCells.symm τ.1) q₀ = _
    unfold CtsMeasured.instCensus
    rw [hsome]
    rfl
  show (V.entCensus
      (writeHeights ε.1.1 ((V.entDom ε.1.1).comps.get ε.1.2).base hs)
      (V.toStepCells.symm τ.1) q₀ : ℚ) = ((V.entCount ε q₀ : ℕ) : ℚ)
  exact_mod_cast congrArg (Nat.cast (R := ℚ)) h2.symm

end LeanUrat.MovesV
