/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapB.B39a
import Uniformity.ChapI.IFCG16
import Uniformity.ChapI.IFCG30
import Uniformity.ChapI.IFCG35

/-!
# Uniformity.ChapI.IFCG38 — [SSL 2026-08-30] the split-sector convolution:
the coprime refinement map, the smaller-mass majorant, and the sector law
re-based on the convolution defect

Stage SSL of the cone census (design record `runs/wave-c/verdict_SSL.md`).  RECUR
(`IFCG35`) partitioned the ramified remainder carrier into the three recursion sectors
and left `SplitSectorLaw m σ` — the coprime-reducible-residual arm — as one of the three
endgame families.  This file lands the split sector's DESCENT structure:

* **§1 the monic coprime split of the class residual.**  On the minimal face the class
  residual is MONIC (`classResidualPoly_monic` — the general-face `resPoly_coeff` at the
  attained monic point, B.39a; no purity), so §2c's dichotomy upgrades from `Associated`
  to an EQUALITY `classResidualPoly π c h e' = G * H` with `G, H` monic coprime
  nonconstant (`splitSector_coprime_split`) — XHS's literal input shape.
* **§2 ★ THE REFINEMENT MAP.**  Every split-sector class with VISIBLE corner refines:
  `splitSector_refines` — EVERY lift factors `monicPoly a = g · h' · R` with `g, h'`
  monic `(h,e')`-pure of pinned degrees `e'·deg G / e'·deg H` carrying residuals EXACTLY
  `G, H` (XHS §4 fired at the minimal face); `splitSector_refines_decided` — the class
  IS a `mulClass` of two DECIDED classes of strictly smaller masses `n₁ + n₂ = m`,
  `n₁ = e'·deg G`, at types summing to `σ` (IFCG17's decided-refinement).  This is the
  class-level bijection onto its image: the pair determines the cell (`mulClass`).
* **§3 ★ THE COUNT MAJORANT.**  The visible-corner split count injects into the
  convolution table: `card_splitSectorVis_le` — at every finite level,
  `#(vis split cells) ≤ convCount = Σ_{0<n₁<m} Σ_{s ≤ σ.data} decidedCount n₁ ⟨s⟩ ·
  decidedCount (m−n₁) ⟨σ.data−s⟩` (the injection recovers the cell from the pair).  The
  invisible-corner part is boxed: `card_splitSectorInv_le ≤ q^((m−1)(M+m))` (the corner
  coefficient is pinned to the zero window).
* **§4 the limit layer.**  `zcURLim_mul` (the product combinator IFCG24 lacked);
  `zcURLim_inv` — the invisible-corner family is a `ZcURLim` with value 0 (squeeze
  against the box); ★ `zcURLim_conv` — under the `< m` decided value laws the
  convolution family IS a `ZcURLim` (each pair term is `decidedSeq · decidedSeq` at the
  diverging level `M + m`; `tendsto_decidedSeq_comp` + the value laws pin the limit to
  ONE rational function of `q`; degree-mismatched table entries vanish identically).
* **§5 ★★ THE RE-BASE.**  `SplitConvolutionDefectLaw m σ` — the ONE named remaining
  Prop: the normalized OVERCOUNT `(convCount − #vis)/q^(m(M+m))` (pointwise ≥ 0 by §3)
  is a `ZcURLim` family.  Then `splitSectorLaw_of_defectLaw`:
  defect law + the `< m` value laws ⟹ `SplitSectorLaw m σ` — the split-sector arm of
  the endgame trichotomy rests on exactly the defect law (whose discharge territory is
  the CONVERSE of §2's map: which decided pairs multiply INTO the split sector — the
  polygon-block Hensel-uniqueness/Minkowski genre, not this unit's).

## Honest scope

The full charge (fire `SplitSectorLaw m σ` outright) needs the refinement map's
SURJECTIVITY leg — the exact description of the image of §2's injection — which is a
finite-precision Newton-polygon factorization-uniqueness statement not in the corpus.
What is landed here: the map, the majorant, the invisible-corner vanishing, the
convolution family's uniform rational limit, and the exact conditional assembly.
Nothing weakened; `SplitSectorLaw`'s statement is IFCG35's, byte-untouched.

## Axiom fence

§1 is Lean-core.  §2 consumes exactly the owner-signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42) through XHS's
`wideFace_refinement_of_stratum`; §3's majorant and §5's assembly inherit it.  The C.33
cites must NOT occur.  Zero sorries at landing.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG38

open IsLocalRing Polynomial
open Uniformity.Density.Induction
open Uniformity.Density.Leaf
open Uniformity.Density.IFCG22 (classCoeffVal npHeight classNPSupport NPAttains
  ClassNPFace NPVisibleAt classNPSupport_le_apply)
open Uniformity.Density.IFCG24 (ZcURLim ZcURLim_zero ZcURLim_sum shallowSet
  mem_stratum_X_pow_iff pureFaceSet coneRemainderCount ConeRemainderLaw npHeight_coe)
open Uniformity.Density.IFCG14 (DecidedValueLaw)
open Uniformity.Density.IFCG26 (onSide_monicPoly_of_npAttains)
open Uniformity.Density.IFCG28 (onSide_monicPoly_iff sideSet_monicPoly_eq
  sideMin_monicPoly_eq sideMax_monicPoly_eq resPoly_monicPoly_eq)
open Uniformity.Density.IFCG23 (npHgt_monicPoly_eq npHgt_monicPoly_top)
open Uniformity.Density.IFCG30 (wideFace_refinement_of_stratum)
open Uniformity.Density.IFCG17 (exists_decided_factors monicPoly_coeff_eq_self)
open Uniformity.Density.IFCG16 (tendsto_decidedSeq_comp)
open Uniformity.Density.IFCG35 (MinFaceAt minFaceAt_support minFaceAt_min
  minFaceAt_attained_lt minFaceAt_unique classResidualPoly classResidualPoly_eq
  classResidualPoly_natDegree_pos exists_coprime_split_of_not_primary
  splitSector splitSectorCount SplitSectorLaw remainderCarrier)

/-! ## §0 — supply -/

section Supply

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by rw [Polynomial.map_X]; exact Polynomial.irreducible_X

/-- B83Kit's membership unfolding for the Classical `sideSet` filter (private copy). -/
private theorem mem_sideSet_iff' {φ f : Polynomial O} {u ℓ j : ℕ} :
    j ∈ sideSet φ f u ℓ ↔ (j < f.natDegree + 1 ∧ OnSide φ f u ℓ j) := by
  classical
  constructor
  · intro hj
    have hj' : j ∈ Finset.filter (OnSide φ f u ℓ) (Finset.range (f.natDegree + 1)) := hj
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hj'
    exact ⟨Finset.mem_range.mp h1, h2⟩
  · rintro ⟨h1, h2⟩
    have : j ∈ Finset.filter (OnSide φ f u ℓ) (Finset.range (f.natDegree + 1)) :=
      Finset.mem_filter.2 ⟨Finset.mem_range.2 h1, h2⟩
    exact this

end Supply

/-! ## §1 — the MONIC coprime split of the minimal-face class residual -/

section MonicSplit

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **The representation supply**: on a minimal face, the canonical class residual IS
every lift's side residual, with the side set, finite support and height data exported
(the honesty lemma's setup block, packaged for reuse; WFR §3 through
`classResidualPoly_eq`). -/
private theorem resPoly_rep {π : O} (hπ : Irreducible π) {m K h e' : ℕ}
    {c : Coeff O m K} (hF : MinFaceAt c h e')
    {a : Fin m → O} (ha : proj O m K a = c) :
    ∃ (hne : (sideSet X (monicPoly a) h e').Nonempty) (H₀ : ℕ),
      npHgt X (monicPoly a) (sideMin X (monicPoly a) h e' hne) = (H₀ : ℕ∞)
      ∧ suppVal X (monicPoly a) h e' ≠ ⊤
      ∧ classResidualPoly π c h e' = resPoly π X (monicPoly a) h e' hne H₀ := by
  obtain ⟨hh1, hhe, hcop, hface, hAm, hvis⟩ := hF
  have he' : 0 < e' := by omega
  obtain ⟨i, j, hij, hAi, hAj⟩ := hface
  have hilt : i < m := lt_of_lt_of_le hij hAj.1
  obtain ⟨hOni, hsupp⟩ := onSide_monicPoly_of_npAttains hπ he' hvis hAi ha
  have hdegm : (monicPoly a).natDegree = m := monicPoly_natDegree a
  have himem : i ∈ sideSet X (monicPoly a) h e' :=
    mem_sideSet_iff'.mpr ⟨by omega, hOni⟩
  have hne : (sideSet X (monicPoly a) h e').Nonempty := ⟨i, himem⟩
  have htop : suppVal X (monicPoly a) h e' ≠ ⊤ := by
    rw [hsupp]
    exact ENat.coe_ne_top _
  have hntop : npHgt X (monicPoly a) (sideMin X (monicPoly a) h e' hne) ≠ ⊤ :=
    npHgt_ne_top_of_onSide he' htop (onSide_of_mem_sideSet (Finset.min'_mem _ hne))
  obtain ⟨w, hw⟩ := WithTop.ne_top_iff_exists.mp hntop
  have hw' : ((w : ℕ) : ℕ∞)
      = npHgt X (monicPoly a) (sideMin X (monicPoly a) h e' hne) := hw
  exact ⟨hne, w, hw'.symm, htop,
    classResidualPoly_eq hπ he' hvis ha hne hw'.symm⟩

/-- ★ **The class residual is MONIC on the minimal face** (the general-face
`resPoly_coeff` at the attained monic point: `sideMax = m`, `H₀ = h·sideDeg`, and the
deviator at the top abscissa of a monic lift is `1`). -/
theorem classResidualPoly_monic {π : O} (hπ : Irreducible π) {m K h e' : ℕ}
    {c : Coeff O m K} (hF : MinFaceAt c h e') :
    (classResidualPoly π c h e').Monic := by
  obtain ⟨a, ha⟩ := proj_surjective O m K c
  obtain ⟨hne, H₀, hH₀, htop, hcrp⟩ := resPoly_rep hπ hF ha
  obtain ⟨hh1, hhe, hcop, hface, hAm, hvis⟩ := hF
  have he' : 0 < e' := by omega
  have hdegm : (monicPoly a).natDegree = m := monicPoly_natDegree a
  -- `sideMax = m` (the monic point is on the side and caps the abscissae)
  obtain ⟨hOnm, -⟩ := onSide_monicPoly_of_npAttains hπ he' hvis hAm ha
  have hmmem : m ∈ sideSet X (monicPoly a) h e' :=
    mem_sideSet_iff'.mpr ⟨by omega, hOnm⟩
  have hmax : sideMax X (monicPoly a) h e' hne = m := by
    unfold sideMax
    refine le_antisymm ?_ (Finset.le_max' _ m hmmem)
    have h2 := Finset.max'_mem (sideSet X (monicPoly a) h e') hne
    obtain ⟨h3, -⟩ := mem_sideSet_iff'.mp h2
    omega
  have hminle : sideMin X (monicPoly a) h e' hne ≤ m := by
    unfold sideMin
    have h2 := Finset.min'_mem (sideSet X (monicPoly a) h e') hne
    obtain ⟨h3, -⟩ := mem_sideSet_iff'.mp h2
    omega
  -- the on-side equation at the monic point pins `suppVal = h·m`
  have hsupp_m : suppVal X (monicPoly a) h e' = ((h * m : ℕ) : ℕ∞) := by
    have h6 : e' • npHgt X (monicPoly a) m + ((h * m : ℕ) : ℕ∞)
        = suppVal X (monicPoly a) h e' := hOnm
    rw [npHgt_monicPoly_top, smul_zero, zero_add] at h6
    exact h6.symm
  -- the on-side equation at `sideMin`, extracted to ℕ
  have hOnmin : OnSide X (monicPoly a) h e' (sideMin X (monicPoly a) h e' hne) :=
    onSide_of_mem_sideSet (Finset.min'_mem _ hne)
  have h7 : e' • npHgt X (monicPoly a) (sideMin X (monicPoly a) h e' hne)
      + ((h * sideMin X (monicPoly a) h e' hne : ℕ) : ℕ∞) = ((h * m : ℕ) : ℕ∞) := by
    rw [← hsupp_m]
    exact hOnmin
  rw [hH₀] at h7
  have h8 : e' * H₀ + h * sideMin X (monicPoly a) h e' hne = h * m := by
    have h9 : ((e' * H₀ + h * sideMin X (monicPoly a) h e' hne : ℕ) : ℕ∞)
        = ((h * m : ℕ) : ℕ∞) := by
      rw [← h7, nsmul_eq_mul, ← Nat.cast_mul, ← Nat.cast_add]
    exact Nat.cast_inj.mp h9
  -- coprimality forces `e' ∣ m − sideMin`; write `m − sideMin = e'·t`
  have hdvd : e' ∣ h * (m - sideMin X (monicPoly a) h e' hne) := by
    refine ⟨H₀, ?_⟩
    have hsplit : h * (m - sideMin X (monicPoly a) h e' hne)
        + h * sideMin X (monicPoly a) h e' hne = h * m := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hminle]
    have h10 := hsplit.trans h8.symm
    exact Nat.add_right_cancel h10
  obtain ⟨t, ht⟩ : e' ∣ (m - sideMin X (monicPoly a) h e' hne) :=
    hcop.symm.dvd_of_dvd_mul_left hdvd
  -- `sideDeg = t` and `H₀ = h·t`
  have hD : sideDeg X (monicPoly a) h e' hne = t := by
    unfold sideDeg
    rw [hmax, ht, Nat.mul_div_cancel_left t he']
  have hH₀t : H₀ = h * t := by
    have h11 : h * (m - sideMin X (monicPoly a) h e' hne)
        + h * sideMin X (monicPoly a) h e' hne = h * m := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hminle]
    have h12 : e' * H₀ = h * (m - sideMin X (monicPoly a) h e' hne) :=
      Nat.add_right_cancel (h8.trans h11.symm)
    rw [ht] at h12
    have h13 : e' * H₀ = e' * (h * t) := by
      rw [h12]
      ring
    exact Nat.eq_of_mul_eq_mul_left he' h13
  -- the leading coefficient: `resMk π X 0 (dev X (monicPoly a) m) = 1`
  have hnd := natDegree_resPoly hπ isKey_X he' hcop htop hne hH₀
  rw [hcrp]
  show (resPoly π X (monicPoly a) h e' hne H₀).coeff
      (resPoly π X (monicPoly a) h e' hne H₀).natDegree = 1
  have hsm : sideMin X (monicPoly a) h e' hne + e' * t = m := by
    rw [← ht, Nat.add_sub_cancel' hminle]
  have h0 : H₀ - h * t = 0 := by
    rw [hH₀t]
    exact Nat.sub_self _
  have hdegX : (monicPoly a).natDegree = m * (X : Polynomial O).natDegree := by
    rw [hdegm, Polynomial.natDegree_X, Nat.mul_one]
  rw [hnd.1, hD]
  rw [resPoly_coeff hne H₀ t]
  rw [if_pos (show t < sideDeg X (monicPoly a) h e' hne + 1 by rw [hD]; omega)]
  rw [resCoeff]
  rw [hsm, h0]
  rw [dev_top Polynomial.monic_X (by simp) (monicPoly_monic a) hdegX]
  exact resMk_one hπ _

/-- ★ **The monic coprime split of a split-sector class residual** (§2c upgraded to an
equality through monicity): at the class's minimal face, `classResidualPoly = G · H`
with `G, H` monic coprime nonconstant — XHS's literal input shape. -/
theorem splitSector_coprime_split {π : O} (hπ : Irreducible π) {m : ℕ}
    {σ : FactorizationType} {M : ℕ} {c : Coeff O m (M + m)}
    (hc : c ∈ splitSector O π m σ M) {h e' : ℕ} (hF : MinFaceAt c h e') :
    ∃ G H : Polynomial (resField (X : Polynomial O)),
      G.Monic ∧ H.Monic ∧ 0 < G.natDegree ∧ 0 < H.natDegree ∧ IsCoprime G H ∧
        classResidualPoly π c h e' = G * H := by
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  obtain ⟨-, h₀, e₀, hF₀, hni₀, hnp₀⟩ := hc
  obtain ⟨hh, he⟩ := minFaceAt_unique hF₀ hF
  subst hh
  subst he
  have hpos := classResidualPoly_natDegree_pos hπ hF
  obtain ⟨G, H, hG, hH, hGd, hHd, hcopGH, hassoc⟩ :=
    exists_coprime_split_of_not_primary hpos.1 hni₀ hnp₀
  exact ⟨G, H, hG, hH, hGd, hHd, hcopGH,
    Polynomial.eq_of_monic_of_associated (classResidualPoly_monic hπ hF)
      (hG.mul hH) hassoc⟩

end MonicSplit

/-! ## §2 — ★ THE REFINEMENT MAP -/

section Refinement

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **Corner visibility** of a class (the wide-face gate, XHS's honest fence item 2):
the constant-coefficient window sees a genuine valuation. -/
def CornerVisible {m K : ℕ} (c : Coeff O m K) : Prop :=
  ∀ i : Fin m, (i : ℕ) = 0 → classCoeffVal c i < K

/-- ★ **THE REFINEMENT MAP (lift level)** — XHS §4 fired at the split sector's minimal
face: a visible-corner split-sector class carries a monic coprime residual split
`G · H`, and EVERY lift factors `monicPoly a = g · h' · R` with `g, h'` monic
`(h,e')`-pure of degrees `e'·deg G / e'·deg H` carrying residuals EXACTLY `G, H`, and
`R` monic (the lower slopes' block).  Consumes B.42 through
`wideFace_refinement_of_stratum`. -/
theorem splitSector_refines {π : O} (hπ : Irreducible π) {m : ℕ} (hm : 0 < m)
    {σ : FactorizationType} {M : ℕ} {c : Coeff O m (M + m)}
    (hc : c ∈ splitSector O π m σ M) (hvis0 : CornerVisible c) :
    ∃ (h e' : ℕ) (G H : Polynomial (resField (X : Polynomial O))),
      MinFaceAt c h e' ∧ G.Monic ∧ H.Monic ∧ 0 < G.natDegree ∧ 0 < H.natDegree ∧
      IsCoprime G H ∧ classResidualPoly π c h e' = G * H ∧
      ∀ a : Fin m → O, proj O m (M + m) a = c →
        ∃ g h' R : Polynomial O, g.Monic ∧ h'.Monic ∧ R.Monic ∧
          monicPoly a = g * h' * R ∧
          g.natDegree = e' * G.natDegree ∧ h'.natDegree = e' * H.natDegree ∧
          IsPure X g h e' ∧ IsPure X h' h e' ∧
          (∀ hg' : (sideSet X g h e').Nonempty,
            resPoly π X g h e' hg' (h * G.natDegree) = G) ∧
          (∀ hh' : (sideSet X h' h e').Nonempty,
            resPoly π X h' h e' hh' (h * H.natDegree) = H) := by
  obtain ⟨h, e', hF, -, -⟩ := hc.2
  obtain ⟨G, H, hG, hH, hGd, hHd, hcopGH, heq⟩ := splitSector_coprime_split hπ hc hF
  refine ⟨h, e', G, H, hF, hG, hH, hGd, hHd, hcopGH, heq, ?_⟩
  intro a ha
  obtain ⟨⟨⟨-, hstr⟩, -⟩, -⟩ := hc.1
  have hu : 0 < h := hF.1
  have hhe : h < e' := hF.2.1
  have he' : 0 < e' := by omega
  have hcop : Nat.Coprime h e' := hF.2.2.1
  have hface : ClassNPFace c h e' := hF.2.2.2.1
  have hvis : NPVisibleAt c h e' := hF.2.2.2.2.2
  have hcorner : classCoeffVal c ⟨0, hm⟩ < M + m := hvis0 ⟨0, hm⟩ rfl
  obtain ⟨a₀, ha₀⟩ := proj_surjective O m (M + m) c
  obtain ⟨hne₀, H₀, hH₀, -, hcrp₀⟩ := resPoly_rep hπ hF ha₀
  have hres : resPoly π X (monicPoly a₀) h e' hne₀ H₀ = G * H := by
    rw [← hcrp₀]
    exact heq
  obtain ⟨g, h', R, hg, hh', hR, heqf, hgd, hhd, hgp, hhp, -, -, hgres, hhres⟩ :=
    wideFace_refinement_of_stratum hπ hm hu he' hcop hstr hcorner hface hvis ha₀
      hne₀ hH₀ hG hH hcopGH hres ha
  exact ⟨g, h', R, hg, hh', hR, heqf, hgd, hhd, hgp, hhp, hgres, hhres⟩

/-- ★ **THE REFINEMENT MAP (class level, decided)** — the census shape: a
visible-corner split-sector class IS a `mulClass` of two DECIDED classes of strictly
smaller masses, at types summing to `σ` (IFCG17's decided-refinement fired through the
lift-level split).  The pair determines the class (`mulClass c₁ c₂` recovers it), so
this is a bijection onto its image. -/
theorem splitSector_refines_decided {π : O} (hπ : Irreducible π) {m : ℕ} (hm : 0 < m)
    {σ : FactorizationType} {M : ℕ} {c : Coeff O m (M + m)}
    (hc : c ∈ splitSector O π m σ M) (hvis0 : CornerVisible c) :
    ∃ (n₁ n₂ : ℕ) (_ : 0 < n₁) (_ : 0 < n₂) (hsum : n₁ + n₂ = m)
      (σ₁ σ₂ : FactorizationType)
      (c₁ : Coeff O n₁ (M + m)) (c₂ : Coeff O n₂ (M + m)),
      DecidedAt O n₁ σ₁ (M + m) c₁ ∧ DecidedAt O n₂ σ₂ (M + m) c₂ ∧
      σ₁.data + σ₂.data = σ.data ∧ mulClass c₁ c₂ = hsum.symm ▸ c := by
  obtain ⟨h, e', G, H, hF, hG, hH, hGd, hHd, hcopGH, heq, hlift⟩ :=
    splitSector_refines hπ hm hc hvis0
  have he' : 0 < e' := by
    have h1 := hF.1
    have h2 := hF.2.1
    omega
  have hdecc : DecidedAt O m σ (M + m) c := hc.1.1.1.1
  obtain ⟨a, ha⟩ := proj_surjective O m (M + m) c
  obtain ⟨g, h', R, hg, hh', hR, heqf, hgd, hhd, -, -, -, -⟩ := hlift a ha
  have hg₂m : (h' * R).Monic := hh'.mul hR
  have hn₁ : 0 < g.natDegree := by
    rw [hgd]
    exact Nat.mul_pos he' hGd
  have hn₂ : 0 < (h' * R).natDegree := by
    rw [hh'.natDegree_mul hR]
    have h3 : 0 < h'.natDegree := by
      rw [hhd]
      exact Nat.mul_pos he' hHd
    omega
  have hsum : g.natDegree + (h' * R).natDegree = m := by
    have h1 : (monicPoly a).natDegree = m := monicPoly_natDegree a
    rw [heqf, mul_assoc, hg.natDegree_mul hg₂m] at h1
    exact h1
  subst hsum
  have hmp₁ : monicPoly (fun i : Fin g.natDegree => g.coeff (i : ℕ)) = g :=
    monicPoly_coeff_eq_self hg rfl
  have hmp₂ : monicPoly (fun i : Fin (h' * R).natDegree => (h' * R).coeff (i : ℕ))
      = h' * R :=
    monicPoly_coeff_eq_self hg₂m rfl
  have hkey : mulClass
      (proj O g.natDegree (M + (g.natDegree + (h' * R).natDegree))
        (fun i => g.coeff (i : ℕ)))
      (proj O (h' * R).natDegree (M + (g.natDegree + (h' * R).natDegree))
        (fun i => (h' * R).coeff (i : ℕ)))
      = c := by
    rw [← mulClass_proj, hmp₁, hmp₂, ← mul_assoc, ← heqf, ← ha]
    congr 1
    funext i
    exact monicPoly_coeff_lt a i.isLt
  rw [← hkey] at hdecc
  obtain ⟨σ₁, σ₂, hσ₁, hσ₂, hsumty⟩ := exists_decided_factors hdecc
  exact ⟨g.natDegree, (h' * R).natDegree, hn₁, hn₂, rfl, σ₁, σ₂, _, _, hσ₁, hσ₂,
    hsumty, hkey⟩

end Refinement

/-! ## §3 — ★ THE COUNT MAJORANT (the convolution table bounds the sector) -/

section Majorant

/-- The visible-corner part of the split sector. -/
def splitSectorVis (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ) :
    Set (Coeff O m (M + m)) :=
  splitSector O π m σ M ∩ {c | CornerVisible c}

/-- The invisible-corner part of the split sector (the boxed remainder). -/
def splitSectorInv (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ) :
    Set (Coeff O m (M + m)) :=
  splitSector O π m σ M ∩ {c | ¬ CornerVisible c}

/-- **The convolution index**: the split mass pairs `(n₁, n₂)` with `n₁ + n₂ = m`, both
positive (the second mass is forced to `m − n₁`; carrying it explicitly keeps every
downstream transport cast-free), times the sub-multisets `s ≤ σ.data`. -/
noncomputable def convPairs (m : ℕ) (σ : FactorizationType) :
    Finset ((ℕ × ℕ) × Multiset (ℕ × ℕ)) :=
  ((Finset.range (m + 1) ×ˢ Finset.range (m + 1)).filter
      (fun q => q.1 + q.2 = m ∧ 0 < q.1 ∧ 0 < q.2)) ×ˢ σ.data.powerset.toFinset

/-- **The convolution table**: the sum, over the split mass pair and the sub-multiset,
of the products of the smaller-mass decided counts at level `M + m`.  (No uniformizer:
the decided census is π-free.) -/
noncomputable def convCount (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (m : ℕ) (σ : FactorizationType) (M : ℕ) : ℕ :=
  ∑ p ∈ convPairs m σ,
    decidedCount O p.1.1 ⟨p.2⟩ (M + m) * decidedCount O p.1.2 ⟨σ.data - p.2⟩ (M + m)

/-- `mulClass`, transported to a pinned total mass (the level `N` is a separate
variable, so the transport touches ONLY the mass coordinate). -/
noncomputable def mulClassAt {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {n₁ n₂ N m : ℕ} (h : n₁ + n₂ = m)
    (c₁ : Coeff O n₁ N) (c₂ : Coeff O n₂ N) : Coeff O m N :=
  h ▸ mulClass c₁ c₂

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- The split count partitions along corner visibility (exact at every level). -/
theorem splitSectorCount_eq_vis_add_inv (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ) :
    splitSectorCount O π m σ M
      = Nat.card (splitSectorVis O π m σ M) + Nat.card (splitSectorInv O π m σ M) := by
  classical
  haveI : Fintype (Coeff O m (M + m)) := Fintype.ofFinite _
  have hd : Disjoint (splitSectorVis O π m σ M) (splitSectorInv O π m σ M) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hv⟩ ⟨-, hnv⟩
    exact hnv hv
  have hu : splitSector O π m σ M
      = splitSectorVis O π m σ M ∪ splitSectorInv O π m σ M :=
    (Set.inter_union_compl (splitSector O π m σ M) {c | CornerVisible c}).symm
  show Nat.card (splitSector O π m σ M : Set (Coeff O m (M + m)))
      = Nat.card (splitSectorVis O π m σ M) + Nat.card (splitSectorInv O π m σ M)
  rw [hu, Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
    Set.ncard_union_eq hd (Set.toFinite _) (Set.toFinite _)]

/-- ★ **THE MAJORANT**: the visible-corner split-sector count injects into the
convolution table — at every finite level, every mass, every type, every uniformizer.
(The injection: §2's refinement map; the recovery: `mulClass`.) -/
theorem card_splitSectorVis_le {π : O} (hπ : Irreducible π) {m : ℕ} (hm : 0 < m)
    (σ : FactorizationType) (M : ℕ) :
    Nat.card (splitSectorVis O π m σ M) ≤ convCount O m σ M := by
  classical
  -- the per-pair product image, transported to mass `m` through the filter's equation
  set T : (ℕ × ℕ) × Multiset (ℕ × ℕ) → Set (Coeff O m (M + m)) := fun p =>
    if h : p.1.1 + p.1.2 = m then
      (fun q : Coeff O p.1.1 (M + m) × Coeff O p.1.2 (M + m) =>
          mulClassAt h q.1 q.2) ''
        ((decidedSet O p.1.1 ⟨p.2⟩ (M + m)) ×ˢ (decidedSet O p.1.2 ⟨σ.data - p.2⟩ (M + m)))
    else ∅ with hT
  -- §2's refinement map is the injection: every visible cell lies in its pair's image
  have hsub : splitSectorVis O π m σ M ⊆ ⋃ p ∈ convPairs m σ, T p := by
    intro c hc
    obtain ⟨hcs, hcv⟩ := hc
    obtain ⟨n₁, n₂, hn₁, hn₂, hsum, σ₁, σ₂, c₁, c₂, hd₁, hd₂, hsumty, hkey⟩ :=
      splitSector_refines_decided hπ hm hcs hcv
    subst hsum
    refine Set.mem_biUnion
      (show ((n₁, n₂), σ₁.data) ∈ convPairs (n₁ + n₂) σ from ?_) ?_
    · rw [convPairs, Finset.mem_product, Finset.mem_filter, Finset.mem_product]
      dsimp only
      refine ⟨⟨⟨Finset.mem_range.2 (by omega), Finset.mem_range.2 (by omega)⟩,
        rfl, hn₁, hn₂⟩, ?_⟩
      rw [Multiset.mem_toFinset, Multiset.mem_powerset]
      exact Multiset.le_iff_exists_add.mpr ⟨σ₂.data, hsumty.symm⟩
    · show c ∈ T ((n₁, n₂), σ₁.data)
      rw [hT]
      dsimp only
      rw [dif_pos rfl]
      refine ⟨(c₁, c₂), ⟨?_, ?_⟩, ?_⟩
      · exact (show (⟨σ₁.data⟩ : FactorizationType) = σ₁ from rfl) ▸ hd₁
      · have h6 : σ.data - σ₁.data = σ₂.data := by
          rw [← hsumty, add_tsub_cancel_left]
        rw [show (⟨σ.data - σ₁.data⟩ : FactorizationType) = σ₂ from
          FactorizationType.ext h6]
        exact hd₂
      · exact hkey
  -- count the union against the table
  calc Nat.card (splitSectorVis O π m σ M)
      = (splitSectorVis O π m σ M).ncard := Nat.card_coe_set_eq _
    _ ≤ (⋃ p ∈ convPairs m σ, T p).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ ∑ p ∈ convPairs m σ, (T p).ncard := Finset.set_ncard_biUnion_le _ _
    _ ≤ ∑ p ∈ convPairs m σ,
          decidedCount O p.1.1 ⟨p.2⟩ (M + m)
            * decidedCount O p.1.2 ⟨σ.data - p.2⟩ (M + m) := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hpm : p.1.1 + p.1.2 = m := by
          rw [convPairs, Finset.mem_product, Finset.mem_filter] at hp
          exact hp.1.2.1
        rw [hT]
        dsimp only
        rw [dif_pos hpm]
        calc ((fun q : Coeff O p.1.1 (M + m) × Coeff O p.1.2 (M + m) =>
                mulClassAt hpm q.1 q.2) ''
              ((decidedSet O p.1.1 ⟨p.2⟩ (M + m))
                ×ˢ (decidedSet O p.1.2 ⟨σ.data - p.2⟩ (M + m)))).ncard
            ≤ ((decidedSet O p.1.1 ⟨p.2⟩ (M + m))
                ×ˢ (decidedSet O p.1.2 ⟨σ.data - p.2⟩ (M + m))).ncard :=
              Set.ncard_image_le (Set.toFinite _)
          _ = (decidedSet O p.1.1 ⟨p.2⟩ (M + m)).ncard
                * (decidedSet O p.1.2 ⟨σ.data - p.2⟩ (M + m)).ncard := Set.ncard_prod
          _ = decidedCount O p.1.1 ⟨p.2⟩ (M + m)
                * decidedCount O p.1.2 ⟨σ.data - p.2⟩ (M + m) := by
              rw [decidedCount, decidedCount, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    _ = convCount O m σ M := rfl

/-- **The invisible-corner box**: an invisible corner pins the constant coefficient to
the zero window, so the invisible part injects into the remaining `m − 1` coordinates. -/
theorem card_splitSectorInv_le (π : O) {m : ℕ} (hm : 0 < m) (σ : FactorizationType)
    (M : ℕ) :
    Nat.card (splitSectorInv O π m σ M) ≤ residueCard O ^ ((m - 1) * (M + m)) := by
  classical
  -- the corner coefficient of an invisible-corner cell is pinned to `0`
  have hzero : ∀ c ∈ splitSectorInv O π m σ M, c ⟨0, hm⟩ = 0 := by
    intro c hc
    obtain ⟨-, hnv⟩ := hc
    have hge : M + m ≤ resOrd (c ⟨0, hm⟩) := by
      by_contra hlt
      refine hnv fun i hi => ?_
      have h5 : i = ⟨0, hm⟩ := Fin.ext hi
      rw [h5]
      exact Nat.lt_of_not_le hlt
    have heq : resOrd (c ⟨0, hm⟩) = M + m :=
      le_antisymm (resOrd_le (c ⟨0, hm⟩)) hge
    exact (resOrd_eq_iff (c ⟨0, hm⟩)).mp heq
  -- drop the pinned coordinate: an injection into the `m − 1` remaining coordinates
  have hinj : Function.Injective (fun c : splitSectorInv O π m σ M =>
      (fun j : Fin (m - 1) => c.1 ⟨(j : ℕ) + 1, by omega⟩ : Coeff O (m - 1) (M + m))) := by
    intro c c' hcc
    apply Subtype.ext
    funext j
    rcases j with ⟨jv, hj⟩
    cases jv with
    | zero =>
        exact (hzero c.1 c.2).trans (hzero c'.1 c'.2).symm
    | succ k =>
        have hk : k < m - 1 := by omega
        have := congrFun hcc ⟨k, hk⟩
        simpa using this
  calc Nat.card (splitSectorInv O π m σ M)
      ≤ Nat.card (Coeff O (m - 1) (M + m)) := Nat.card_le_card_of_injective _ hinj
    _ = residueCard O ^ ((m - 1) * (M + m)) := card_coeff (m - 1) (M + m)

end Majorant

/-! ## §4 — the limit layer -/

section Limits

/-- The product combinator for `ZcURLim` (IFCG24 has `add`/`sum`; the convolution needs
the product). -/
theorem zcURLim_mul
    {F G : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], O → ℕ → ℝ}
    (hF : ZcURLim F) (hG : ZcURLim G) :
    ZcURLim (fun O _ _ _ _ _ π M => F O π M * G O π M) := by
  obtain ⟨n₁, d₁, hd₁, hval₁⟩ := hF
  obtain ⟨n₂, d₂, hd₂, hval₂⟩ := hG
  refine ⟨n₁ * n₂, d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
  intro O _ _ _ _ _
  obtain ⟨hne₁, hlim₁⟩ := hval₁ O
  obtain ⟨hne₂, hlim₂⟩ := hval₂ O
  refine ⟨by rw [Polynomial.eval_mul]; exact mul_ne_zero hne₁ hne₂, ?_⟩
  intro π hπ
  have hq : (n₁.eval ((residueCard O : ℕ) : ℚ) / d₁.eval ((residueCard O : ℕ) : ℚ)
        * (n₂.eval ((residueCard O : ℕ) : ℚ) / d₂.eval ((residueCard O : ℕ) : ℚ)) : ℚ)
      = ((n₁ * n₂).eval ((residueCard O : ℕ) : ℚ)
          / (d₁ * d₂).eval ((residueCard O : ℕ) : ℚ) : ℚ) := by
    rw [Polynomial.eval_mul, Polynomial.eval_mul]
    exact div_mul_div_comm _ _ _ _
  have hlim := (hlim₁ π hπ).mul (hlim₂ π hπ)
  rw [← Rat.cast_mul, hq] at hlim
  exact hlim

/-- The difference combinator for `ZcURLim` (the assembly consumes the defect by
subtraction). -/
theorem zcURLim_sub
    {F G : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], O → ℕ → ℝ}
    (hF : ZcURLim F) (hG : ZcURLim G) :
    ZcURLim (fun O _ _ _ _ _ π M => F O π M - G O π M) := by
  obtain ⟨n₁, d₁, hd₁, hval₁⟩ := hF
  obtain ⟨n₂, d₂, hd₂, hval₂⟩ := hG
  refine ⟨n₁ * d₂ - d₁ * n₂, d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
  intro O _ _ _ _ _
  obtain ⟨hne₁, hlim₁⟩ := hval₁ O
  obtain ⟨hne₂, hlim₂⟩ := hval₂ O
  refine ⟨by rw [Polynomial.eval_mul]; exact mul_ne_zero hne₁ hne₂, ?_⟩
  intro π hπ
  have hq : (n₁.eval ((residueCard O : ℕ) : ℚ) / d₁.eval ((residueCard O : ℕ) : ℚ)
        - n₂.eval ((residueCard O : ℕ) : ℚ) / d₂.eval ((residueCard O : ℕ) : ℚ) : ℚ)
      = ((n₁ * d₂ - d₁ * n₂).eval ((residueCard O : ℕ) : ℚ)
          / (d₁ * d₂).eval ((residueCard O : ℕ) : ℚ) : ℚ) := by
    rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul,
      Polynomial.eval_mul, div_sub_div _ _ hne₁ hne₂]
  have hlim := (hlim₁ π hπ).sub (hlim₂ π hπ)
  rw [← Rat.cast_sub, hq] at hlim
  exact hlim

/-- **The invisible-corner family vanishes**: squeezed against the §3 box, the
normalized invisible-corner split count is a `ZcURLim` family with value `0`. -/
theorem zcURLim_inv {m : ℕ} (hm : 0 < m) (σ : FactorizationType) :
    ZcURLim (fun O _ _ _ _ _ π M =>
      (Nat.card (splitSectorInv O π m σ M) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))) := by
  refine ⟨0, 1, one_ne_zero, ?_⟩
  intro O _ _ _ _ _
  refine ⟨by simp, ?_⟩
  intro π hπ
  have hval : (((0 : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ)
      / (1 : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ) = 0 := by simp
  rw [hval]
  have hq2 : 2 ≤ residueCard O := two_le_residueCard O
  have hq1 : (1 : ℝ) < ((residueCard O : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 < residueCard O)
  have hq0 : (0 : ℝ) < ((residueCard O : ℕ) : ℝ) := lt_trans one_pos hq1
  have h1 : Filter.Tendsto (fun k : ℕ => (1 / ((residueCard O : ℕ) : ℝ)) ^ k)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ((div_lt_one hq0).mpr hq1)
  refine squeeze_zero (g := fun M => (1 / ((residueCard O : ℕ) : ℝ)) ^ (M + m))
    (fun M => by positivity) (fun M => ?_) (h1.comp (Filter.tendsto_add_atTop_nat m))
  have hb : (Nat.card (splitSectorInv O π m σ M) : ℝ)
      ≤ ((residueCard O : ℕ) : ℝ) ^ ((m - 1) * (M + m)) := by
    exact_mod_cast card_splitSectorInv_le π hm σ M
  have hpow : ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
      = ((residueCard O : ℕ) : ℝ) ^ ((m - 1) * (M + m))
        * ((residueCard O : ℕ) : ℝ) ^ (M + m) := by
    rw [← pow_add]
    congr 1
    have h5 : m - 1 + 1 = m := Nat.succ_pred_eq_of_pos hm
    calc m * (M + m) = ((m - 1) + 1) * (M + m) := by rw [h5]
      _ = (m - 1) * (M + m) + (M + m) := by ring
  calc (Nat.card (splitSectorInv O π m σ M) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
      ≤ ((residueCard O : ℕ) : ℝ) ^ ((m - 1) * (M + m))
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)) := by gcongr
    _ = (1 / ((residueCard O : ℕ) : ℝ)) ^ (M + m) := by
        rw [hpow, one_div, inv_pow]
        exact div_mul_cancel_left₀
          ((by positivity : (0 : ℝ) < ((residueCard O : ℕ) : ℝ) ^ ((m - 1) * (M + m))).ne') _

/-- ★ **The convolution family is a uniform rational limit** under the `< m` decided
value laws: each table entry is `decidedSeq · decidedSeq` read at the diverging level
`M + m`, its limit the product of the two premised rational values (degree-mismatched
entries vanish identically). -/
theorem zcURLim_conv {m : ℕ} (σ : FactorizationType)
    (hDV : ∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') :
    ZcURLim (fun O _ _ _ _ _ _ M =>
      (convCount O m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))) := by
  classical
  -- the one-mass decided-sequence family, at the diverging level `M + m`
  have hfac : ∀ k : ℕ, k < m → ∀ τ : FactorizationType,
      ZcURLim (fun O _ _ _ _ _ π M => decidedSeq O k τ (M + m)) := by
    intro k hkm τ
    by_cases hdeg : τ.degree = k
    · obtain ⟨num, den, hden, hval⟩ := hDV k hkm τ hdeg
      refine ⟨num, den, hden, ?_⟩
      intro O _ _ _ _ _
      obtain ⟨hne, hdd⟩ := hval O
      refine ⟨hne, ?_⟩
      intro π hπ
      have ht := tendsto_decidedSeq_comp (O := O) (Filter.tendsto_add_atTop_nat m) k τ
      rw [hdd] at ht
      exact ht
    · refine ZcURLim_zero.congr ?_
      intro O _ _ _ _ _ π hπ M
      have hempty : decidedSet O k τ (M + m) = ∅ := by
        ext c
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hc
        obtain ⟨a, ha⟩ := proj_surjective O k (M + m) c
        have h2 := typeOf_degree (monicPoly_monic a)
        rw [hc a ha, monicPoly_natDegree] at h2
        exact hdeg h2
      have hcount : decidedCount O k τ (M + m) = 0 := by
        unfold decidedCount
        rw [hempty, Nat.card_coe_set_eq, Set.ncard_empty]
      show (0 : ℝ) = decidedSeq O k τ (M + m)
      unfold decidedSeq
      rw [hcount]
      simp
  -- each table entry is a product of two premised families
  have hterm : ∀ p ∈ convPairs m σ, ZcURLim (fun O _ _ _ _ _ π M =>
      decidedSeq O p.1.1 ⟨p.2⟩ (M + m) * decidedSeq O p.1.2 ⟨σ.data - p.2⟩ (M + m)) := by
    intro p hp
    have hpm : p.1.1 + p.1.2 = m ∧ 0 < p.1.1 ∧ 0 < p.1.2 := by
      rw [convPairs, Finset.mem_product, Finset.mem_filter] at hp
      exact hp.1.2
    exact zcURLim_mul (hfac p.1.1 (by omega) ⟨p.2⟩) (hfac p.1.2 (by omega) ⟨σ.data - p.2⟩)
  -- sum the table and renormalize
  refine (ZcURLim_sum (convPairs m σ) _ hterm).congr ?_
  intro O _ _ _ _ _ π hπ M
  show ∑ p ∈ convPairs m σ,
      decidedSeq O p.1.1 ⟨p.2⟩ (M + m) * decidedSeq O p.1.2 ⟨σ.data - p.2⟩ (M + m)
    = (convCount O m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
  rw [convCount, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpm : p.1.1 + p.1.2 = m := by
    rw [convPairs, Finset.mem_product, Finset.mem_filter] at hp
    exact hp.1.2.1
  unfold decidedSeq
  push_cast
  rw [div_mul_div_comm, ← pow_add, ← add_mul, hpm]

end Limits

/-! ## §5 — ★★ the re-base: the split-sector law rests on the convolution defect -/

section ReBase

/-- **THE CONVOLUTION DEFECT LAW at `(m, σ)`** — the ONE named remaining Prop of the
split sector: the normalized overcount of the convolution table over the visible-corner
split cells (pointwise `≥ 0` by §3's majorant) is a uniform rational limit.  Its
discharge territory is the CONVERSE of §2's refinement map — the exact description of
which decided pairs multiply into the split sector (finite-precision Newton-polygon
factorization uniqueness; the `stratDecCount_mul` genre at polygon blocks). -/
def SplitConvolutionDefectLaw (m : ℕ) (σ : FactorizationType) : Prop :=
  ZcURLim (fun O _ _ _ _ _ π M =>
    ((convCount O m σ M : ℝ) - (Nat.card (splitSectorVis O π m σ M) : ℝ))
      / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)))

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- The defect is pointwise nonnegative (§3's majorant — the defect Prop is a genuine
overcount, never a signed fudge). -/
theorem defect_nonneg {π : O} (hπ : Irreducible π) {m : ℕ} (hm : 0 < m)
    (σ : FactorizationType) (M : ℕ) :
    (0 : ℝ) ≤ ((convCount O m σ M : ℝ) - (Nat.card (splitSectorVis O π m σ M) : ℝ))
      / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)) := by
  apply div_nonneg
  · rw [sub_nonneg]
    exact_mod_cast card_splitSectorVis_le hπ hm σ M
  · positivity

/-- ★ **Nonvacuity of the defect-law family — the unramified instances fire** under
the same supply: at every unramified type the split sector is EMPTY on the shallow
stratum (UZL's forcing, exactly as IFCG35's `sectorLaws_unramified`), so the defect is
the full convolution table and its law is §4's. -/
theorem defectLaw_unramified {m : ℕ} (σ : FactorizationType)
    (hunr : ∀ p ∈ σ.data, p.1 = 1)
    (hDV : ∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') :
    SplitConvolutionDefectLaw m σ := by
  refine (zcURLim_conv σ hDV).congr ?_
  intro O _ _ _ _ _ π hπ M
  have hcar : splitSectorVis O π m σ M = ∅ := by
    ext c
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨hcarr, -⟩, -⟩
    obtain ⟨⟨⟨hdec, hstr⟩, hsh⟩, -⟩ := hcarr
    exact Uniformity.Density.IFCG33.not_decidedAt_unramified_of_shallow
      (by omega : m ≤ M + m) hstr hsh hunr hdec
  have h0 : Nat.card (splitSectorVis O π m σ M) = 0 := by
    rw [hcar, Nat.card_coe_set_eq, Set.ncard_empty]
  show (convCount O m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
      = ((convCount O m σ M : ℝ) - (Nat.card (splitSectorVis O π m σ M) : ℝ))
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
  rw [h0]
  simp

/-- ★★ **THE RE-BASE**: the split-sector law at `(m, σ)` rests on exactly the
convolution defect law, under the recursion's own supply (the `< m` decided value
laws): `#split = (conv − defect) + #inv`, the convolution family is a `ZcURLim` (§4),
the invisible part vanishes (§4), and the defect is the named Prop. -/
theorem splitSectorLaw_of_defectLaw {m : ℕ} (hm : 0 < m) (σ : FactorizationType)
    (hDV : ∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ')
    (hD : SplitConvolutionDefectLaw m σ) :
    SplitSectorLaw m σ := by
  have hconv := zcURLim_conv σ hDV
  have hvis : ZcURLim (fun O _ _ _ _ _ π M =>
      (Nat.card (splitSectorVis O π m σ M) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))) := by
    refine (zcURLim_sub hconv hD).congr ?_
    intro O _ _ _ _ _ π hπ M
    ring
  refine ((hvis.add (zcURLim_inv hm σ)).congr ?_)
  intro O _ _ _ _ _ π hπ M
  show (Nat.card (splitSectorVis O π m σ M) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
      + (Nat.card (splitSectorInv O π m σ M) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
    = (splitSectorCount O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
  rw [splitSectorCount_eq_vis_add_inv π m σ M]
  push_cast
  ring

end ReBase

end Uniformity.Density.IFCG38

end

/-! ## AXCHECK FOOTER — §1 and §3's box expect Lean core
`{propext, Classical.choice, Quot.sound}`; §2, §3's majorant, and §5's assembly expect
Lean core + the owner-signed B.42 cite
`Uniformity.Density.Leaf.exists_slope_factorization` (through XHS).  C.33 must NOT
occur. -/
#print axioms Uniformity.Density.IFCG38.classResidualPoly_monic
#print axioms Uniformity.Density.IFCG38.splitSector_coprime_split
#print axioms Uniformity.Density.IFCG38.splitSector_refines
#print axioms Uniformity.Density.IFCG38.splitSector_refines_decided
#print axioms Uniformity.Density.IFCG38.splitSectorCount_eq_vis_add_inv
#print axioms Uniformity.Density.IFCG38.card_splitSectorVis_le
#print axioms Uniformity.Density.IFCG38.card_splitSectorInv_le
#print axioms Uniformity.Density.IFCG38.zcURLim_mul
#print axioms Uniformity.Density.IFCG38.zcURLim_sub
#print axioms Uniformity.Density.IFCG38.zcURLim_inv
#print axioms Uniformity.Density.IFCG38.zcURLim_conv
#print axioms Uniformity.Density.IFCG38.defect_nonneg
#print axioms Uniformity.Density.IFCG38.defectLaw_unramified
#print axioms Uniformity.Density.IFCG38.splitSectorLaw_of_defectLaw
