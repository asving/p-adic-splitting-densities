/-  MovesV unit V5-6 `comp_agg` — (COMP-AGG) GIVEN (COMP-Σ) + (iii) +
    (iv)-REP: summing over instantiations then templates — entrance heights
    EXACTLY ONCE; the common continuation factor pulled out by (iv)-REP;
    counts do NOT aggregate.  `aggMass` (NAME→HOME).
    PROVED 2026-07-30 after the ADJUDICATED lands-leakage repair: the E-phase
    `aggMass` sums ALL εT over the full `entDom`-membership while `iotaValV`
    is `entLands`-filtered (blueprint V5-6 row, MOVESV_LEAN_BLUEPRINT_
    2026-07-28.md: "(COMP-AGG) summing (COMP-Σ) over entrance heights (via
    the instantiation bijection) then over templates ε̊ via ENT-AGG …
    = ι_{e,β₀} · ∏ (T·G) — masses aggregate, counts do NOT").  Of the two
    adjudicated forms, the ADD-THE-LAW form is landed (it keeps `aggMass`'s
    all-ε̊ display faithful to the note): `CompCarrier.ιN_lands`
    (V5_comphA) — non-landing templates contribute 0.  The proof runs the
    recorded derivable legs: the iotaEps–ιshH BRIDGE (`ιN_card` + `ent_card`
    + `box_card` at the defining level), (ENT-U) census constancy per listed
    component (`hEU`, the V3-8b fiber idiom), and the V0-3 partition sum
    (`semilin_sum_exact`); the finite ε̊-aggregate then re-indexes to the
    `entLands`-filtered `EntIx` index. -/
import LeanUrat.MovesV.V5_compsig
import LeanUrat.MovesV.V3_aggfullB
import LeanUrat.MovesV.V4_rep

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV
open LeanUrat.MovesS (Qq OKat evalAt)

/-- the ε̊-and-height double aggregate ((COMP-Σ)-shaped summands).
M1 SOUNDNESS REPAIR (2026-07-29): the false unscoped-totality shim is
DELETED, so the aggregate carries the threaded domain-scoping hypothesis
`hdom : EntDomOrder0 V` (the order-0 perimeter family) certifying every
summand's `writeHeights` value — statements gaining hypotheses is the
honest cost. -/
noncomputable def aggMass {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {TE : TmplEvents n S} (cc : CompCarrier V TE)
    {X : XHDw n S} {D : XHDd n S TE} (Xs : XHDs n S X D)
    (hdom : EntDomOrder0 V)
    (β₀ : S.Cell) {α} (γ : Template n S α) (q₀ : ℚ) : ℝ :=
  ∑' εT : EntTemplate n, ∑' h : {h // (V.entDom εT).Mem h},
    iotaEps cc (writeHeights εT h.1 (hdom εT h.1 h.2)) β₀ q₀
      * stepProdVal V Xs γ q₀

/-- THE iotaEps–ιshH BRIDGE (the adjudication's recorded derivable leg):
at the defining level the carrier's normalized entrance value IS the
census-per-`q^A` shallow mass — `ιN_card` (the |Box| normalization) +
`ent_card` (F-1's division-free entrance counting law) + `box_card`. -/
theorem iotaEps_iotashH_bridge {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {TE : TmplEvents n S} (cc : CompCarrier V TE)
    (εT : EntTemplate n) (h : Hpt εT.entDim) (hs : Order0Perimeter εT h)
    (β₀ : S.Cell) {q₀ : ℚ} (hq : q₀ ∈ V.Pools) :
    iotaEps cc (writeHeights εT h hs) β₀ q₀ = ιshH V εT h β₀ q₀ := by
  classical
  set ε := writeHeights εT h hs with hε
  set L := (ε.template?).elim 0 V.entLvl with hL
  have hsome : writeHeights? εT h = some ε :=
    (Option.some_get (writeHeights_total_of_perimeter εT h hs)).symm
  have hq1 : (1 : ℚ) < q₀ := S.pools_gt_one q₀ (V.pools_sub hq)
  have hq0 : (0 : ℝ) < (q₀ : ℝ) := by exact_mod_cast lt_trans one_pos hq1
  -- the three counting laws at the defining level
  have hcard := cc.ιN_card ε β₀ q₀ hq L (le_refl L)
  have hent := V.ent_card ε β₀ q₀ hq L (le_refl L)
  have hboxR : ((@Fintype.card _ (V.finB q₀ L)) : ℝ) = (q₀ : ℝ) ^ (n * L) := by
    exact_mod_cast V.box_card q₀ hq L
  have hentR : ((V.entEvt ε β₀ q₀ L).card : ℝ) * (q₀ : ℝ) ^ (ε.A : ℕ)
      = ((V.entInst ε β₀ q₀ L).card : ℝ) * (q₀ : ℝ) ^ (n * L) := by
    exact_mod_cast hent
  -- unfold the two §2.F wrappers through writeHeights? = some
  have hIC : V.instCensus εT h β₀ q₀ = V.entCensus ε β₀ q₀ := by
    unfold CtsMeasured.instCensus; rw [hsome]; simp
  have hIA : instA εT h = ε.A := by
    unfold instA; rw [hsome]; simp
  -- assemble
  have hA0 : (0 : ℝ) < (q₀ : ℝ) ^ (ε.A : ℕ) := pow_pos hq0 _
  have hP0 : (0 : ℝ) < (q₀ : ℝ) ^ (n * L) := pow_pos hq0 _
  rw [hboxR] at hcard
  unfold ιshH
  rw [hIC, hIA]
  unfold CtsMeasured.entCensus
  show cc.ιN ε β₀ q₀ L
      = ((V.entInst ε β₀ q₀ ((ε.template?).elim 0 V.entLvl)).card : ℝ)
        * (q₀ : ℝ) ^ (-((ε.A : ℕ) : ℤ))
  rw [← hL, zpow_neg, zpow_natCast, eq_mul_inv_iff_mul_eq₀ (ne_of_gt hA0)]
  refine mul_right_cancel₀ (ne_of_gt hP0) ?_
  calc cc.ιN ε β₀ q₀ L * (q₀ : ℝ) ^ (ε.A : ℕ) * (q₀ : ℝ) ^ (n * L)
      = cc.ιN ε β₀ q₀ L * (q₀ : ℝ) ^ (n * L) * (q₀ : ℝ) ^ (ε.A : ℕ) := by ring
    _ = ((V.entEvt ε β₀ q₀ L).card : ℝ) * (q₀ : ℝ) ^ (ε.A : ℕ) := by rw [hcard]
    _ = ((V.entInst ε β₀ q₀ L).card : ℝ) * (q₀ : ℝ) ^ (n * L) := hentR

theorem comp_agg {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {TE : TmplEvents n S} {D : XHDd n S TE}
    (cc : CompCarrier V TE) (P : C15Pack n S) (X : XHDw n S) (U : XHDu n S)
    (Xs : XHDs n S X D) (XsEnt : XHDsEnt n S V) (DE : XHDdEnt n S V)
    (hTie : MarkFiberTie TE) (hHMC : HMC TE D) (hdom : EntDomOrder0 V)
    (hEU : EntU V)
    (hobs : ∀ s : Skeleton n, ObsCheck (C.bd s))
    (β₀ : S.Cell) {α} (γ : Template n S α) {q₀ : ℚ} (hq : q₀ ∈ V.Pools) :
    aggMass cc Xs hdom β₀ γ q₀
      = iotaValV V XsEnt β₀ q₀ * stepProdVal V Xs γ q₀ := by
  classical
  letI : Finite (EntTemplate n) := template_finite n
  letI : Fintype (EntTemplate n) := Fintype.ofFinite _
  letI : Finite (V.EntIx β₀) := by
    unfold CtsMeasured.EntIx; exact Subtype.finite
  letI : Fintype (V.EntIx β₀) := Fintype.ofFinite _
  have hq1 : (1 : ℚ) < q₀ := S.pools_gt_one q₀ (V.pools_sub hq)
  have hq0 : (0 : ℝ) < (q₀ : ℝ) := by exact_mod_cast lt_trans one_pos hq1
  -- ── the (ENT-U) fiber leg: per landing (εT, j) the component sums to ιsh
  have hfiber : ∀ (εT : EntTemplate n) (hl : V.entLands εT β₀)
      (j : Fin (V.entDom εT).comps.length),
      HasSum (fun x : {h // ((V.entDom εT).comps.get j).Mem h} =>
          ιshH V εT x.1 β₀ q₀)
        (iotaShV V XsEnt ⟨⟨εT, j⟩, hl⟩ q₀) := by
    intro εT hl j
    set i : V.EntIx β₀ := ⟨⟨εT, j⟩, hl⟩ with hi
    have hIC : ∀ (h : Hpt εT.entDim) (hs : Order0Perimeter εT h),
        V.instCensus εT h β₀ q₀ = V.entCensus (writeHeights εT h hs) β₀ q₀ := by
      intro h hs
      have hsome : writeHeights? εT h = some (writeHeights εT h hs) :=
        (Option.some_get (writeHeights_total_of_perimeter εT h hs)).symm
      unfold CtsMeasured.instCensus
      rw [hsome]
      simp
    obtain ⟨P', _, hP'⟩ := hEU β₀ i
    have hconst : ∀ x : {h // ((V.entDom εT).comps.get j).Mem h},
        (V.instCensus εT x.1 β₀ q₀ : ℝ) = (V.entCount i q₀ : ℝ) := by
      intro x
      have hsx : Order0Perimeter εT x.1 := hdom.comp εT j x.2
      have hsb : Order0Perimeter εT ((V.entDom εT).comps.get j).base :=
        hdom.comp εT j (linset_base_mem ((V.entDom εT).comps.get j))
      have e1 := hP' x.1 x.2 hsx q₀ hq
      have e2 := hP' _ (linset_base_mem ((V.entDom εT).comps.get j)) hsb q₀ hq
      have hqq : (V.entCensus (writeHeights εT x.1 hsx) β₀ q₀ : ℚ)
          = (V.entCensus (writeHeights εT
              ((V.entDom εT).comps.get j).base hsb) β₀ q₀ : ℚ) :=
        e1.symm.trans e2
      rw [hIC x.1 hsx,
        show V.entCount i q₀
            = V.instCensus εT ((V.entDom εT).comps.get j).base β₀ q₀ from rfl,
        hIC ((V.entDom εT).comps.get j).base hsb]
      exact_mod_cast hqq
    have hfun : (fun x : {h // ((V.entDom εT).comps.get j).Mem h} =>
          ιshH V εT x.1 β₀ q₀)
        = (fun x => (V.entCount i q₀ : ℝ)
            * (q₀ : ℝ) ^ (-((instA εT x.1 : ℕ) : ℤ))) := by
      funext x; unfold ιshH; rw [hconst x]
    have hval : iotaShV V XsEnt i q₀
        = (V.entCount i q₀ : ℝ)
          * ((evalAt q₀ ⟨XsEnt.Gent β₀ i, XsEnt.Gent_ok β₀ i q₀ hq⟩ : ℚ) : ℝ) := by
      unfold iotaShV; rw [dif_pos hq]
    rw [hfun, hval]
    exact (XsEnt.Gent_hasSum β₀ i q₀ hq).mul_left (V.entCount i q₀ : ℝ)
  -- ── the per-ε̊ inner sum: landing templates give the component ιsh sums
  --    (bridge + V0-3), non-landing templates give 0 (the ADJUDICATED law)
  have hinner : ∀ εT : EntTemplate n,
      (∑' hh : {h // (V.entDom εT).Mem h},
        iotaEps cc (writeHeights εT hh.1 (hdom εT hh.1 hh.2)) β₀ q₀)
      = if hl : V.entLands εT β₀
        then ∑ j, iotaShV V XsEnt ⟨⟨εT, j⟩, hl⟩ q₀ else 0 := by
    intro εT
    by_cases hl : V.entLands εT β₀
    · rw [dif_pos hl]
      have hbr : ∀ hh : {h // (V.entDom εT).Mem h},
          iotaEps cc (writeHeights εT hh.1 (hdom εT hh.1 hh.2)) β₀ q₀
            = ιshH V εT hh.1 β₀ q₀ :=
        fun hh => iotaEps_iotashH_bridge cc εT hh.1 (hdom εT hh.1 hh.2) β₀ hq
      rw [tsum_congr hbr]
      have hng : ∀ h : Hpt εT.entDim, 0 ≤ ιshH V εT h β₀ q₀ := fun h =>
        mul_nonneg (Nat.cast_nonneg _) (zpow_nonneg hq0.le _)
      exact (semilin_sum_exact (V.entDom εT)
        (fun h => ιshH V εT h β₀ q₀) hng
        (fun j => iotaShV V XsEnt ⟨⟨εT, j⟩, hl⟩ q₀)
        (fun j => hfiber εT hl j)).tsum_eq
    · rw [dif_neg hl]
      have hz : ∀ hh : {h // (V.entDom εT).Mem h},
          iotaEps cc (writeHeights εT hh.1 (hdom εT hh.1 hh.2)) β₀ q₀ = 0 := by
        intro hh
        exact cc.ιN_lands εT hh.1 β₀ hq hl
          (writeHeights εT hh.1 (hdom εT hh.1 hh.2))
          (Option.get_mem (writeHeights_total_of_perimeter εT hh.1
            (hdom εT hh.1 hh.2))) _
      rw [tsum_congr hz]
      exact tsum_zero
  -- ── the finite ε̊-aggregate re-indexes to the entLands-filtered EntIx
  letI : Fintype {p : Σ εT : EntTemplate n,
      Fin (V.entDom εT).comps.length // V.entLands p.1 β₀} := Fintype.ofFinite _
  have hKEY : (∑' εT : EntTemplate n, ∑' hh : {h // (V.entDom εT).Mem h},
      iotaEps cc (writeHeights εT hh.1 (hdom εT hh.1 hh.2)) β₀ q₀)
        = iotaValV V XsEnt β₀ q₀ := by
    rw [tsum_congr hinner, tsum_fintype]
    -- the ambient dite-extension of ιsh over the sigma index
    set G : (Σ εT : EntTemplate n, Fin (V.entDom εT).comps.length) → ℝ :=
      fun p => if hl : V.entLands p.1 β₀
        then iotaShV V XsEnt ⟨p, hl⟩ q₀ else 0 with hG
    have h4 : (∑ εT : EntTemplate n, if hl : V.entLands εT β₀
          then ∑ j, iotaShV V XsEnt ⟨⟨εT, j⟩, hl⟩ q₀ else 0)
        = ∑ εT : EntTemplate n, ∑ j, G ⟨εT, j⟩ := by
      refine Finset.sum_congr rfl fun εT _ => ?_
      by_cases hl : V.entLands εT β₀
      · rw [dif_pos hl]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hG]
        rw [dif_pos hl]
      · rw [dif_neg hl]
        symm
        refine Finset.sum_eq_zero fun j _ => ?_
        simp only [hG]
        rw [dif_neg hl]
    have h5 : (∑ εT : EntTemplate n, ∑ j, G ⟨εT, j⟩)
        = ∑ p : (Σ εT : EntTemplate n, Fin (V.entDom εT).comps.length), G p := by
      rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
    have h6 : (∑ p : (Σ εT : EntTemplate n, Fin (V.entDom εT).comps.length), G p)
        = ∑ p ∈ Finset.univ.filter
            (fun p : (Σ εT : EntTemplate n, Fin (V.entDom εT).comps.length) =>
              V.entLands p.1 β₀), G p := by
      symm
      refine Finset.sum_filter_of_ne fun p _ hne => ?_
      by_contra hnl
      exact hne (by simp only [hG]; rw [dif_neg hnl])
    have h7 : (∑ p ∈ Finset.univ.filter
          (fun p : (Σ εT : EntTemplate n, Fin (V.entDom εT).comps.length) =>
            V.entLands p.1 β₀), G p)
        = ∑ i : {p : Σ εT : EntTemplate n,
            Fin (V.entDom εT).comps.length // V.entLands p.1 β₀}, G i.1 :=
      Finset.sum_subtype
        (Finset.univ.filter
          (fun p : (Σ εT : EntTemplate n, Fin (V.entDom εT).comps.length) =>
            V.entLands p.1 β₀))
        (fun x => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
        G
    have h8 : (∑ i : {p : Σ εT : EntTemplate n,
          Fin (V.entDom εT).comps.length // V.entLands p.1 β₀}, G i.1)
        = iotaValV V XsEnt β₀ q₀ := by
      unfold iotaValV
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [hG]
      rw [dif_pos i.2]
    rw [h4, h5, h6, h7, h8]
  -- ── assemble: pull the constant continuation factor, apply the key
  have hpull : aggMass cc Xs hdom β₀ γ q₀
      = (∑' εT : EntTemplate n, ∑' hh : {h // (V.entDom εT).Mem h},
          iotaEps cc (writeHeights εT hh.1 (hdom εT hh.1 hh.2)) β₀ q₀)
        * stepProdVal V Xs γ q₀ := by
    unfold aggMass
    rw [← tsum_mul_right]
    exact tsum_congr fun εT => tsum_mul_right
  rw [hpull, hKEY]

end LeanUrat.MovesV
