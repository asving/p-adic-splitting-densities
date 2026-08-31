/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG25
import Uniformity.ChapI.IFCG34
import Uniformity.ChapI.IFCG48

/-!
# Uniformity.ChapI.IFCG51 — [ASM 2026-08-30] the full-span/dd assembly: composite-mass
`PowerFullSpanLaw` on the correspondence family, and ER4's dd limits at `m = 4`

The designated bookkeeping assembly over the landed instruments (IFCG44's face/centre
supply, IFCG47's decision transport, IFCG48's correspondence sockets, IFCG25's deep
recursion, IFCG34's dd families).  Contents:

* **§1 W1 — the class-side pins**: lattice + exact corner reconstruct the minimal face
  (landed `minFaceAt_of_lattice`) AND pin the residual degree (`lattice_pins`) — the
  missing degree read of the cell description's `⟸` half.
* **§2 W2 — the reconstruction**: an `alphaBox` member's inverse transport satisfies
  the raw lattice with EXACT corner (`boxLattice`), hence lies in the Eisenstein
  full-span cell (`mem_eisCell_symm`) — the image characterization
  `cellTransport '' (cell) = alphaBox ∩ decidedSet` both ways.
* **§3 L2 — the deep-box decided limit**: the mixed-window two-sided squeeze
  converting `#(alphaBox ∩ decided σ')` to the mass-`D` STRATUM census limit over the
  recentring ring — `tendsto_stratDecCount_of_laws` (IFCG25's cone + deep partition at
  the zero centre) + the `q^{−e'T_D}` squeeze (`tendsto_boxDec`).
* **§4 the partition**: `powerSectorFull` = Eisenstein-frame cells (faces `(1, e')`,
  linear-power residuals) ⊔ the named remainder; per-cell/per-face counts and limits.
* **§5 the fires**: `EisFullSpanRemainderLaw` (THE named remainder),
  `powerFullSpanLaw_of_correspondence` (composite mass, conditional), and the
  prime/composite wrapper.
* **§6 the `m = 4` instance**: the remainder is PROVED EMPTY
  (`eisFullSpanRemainderLaw_four`), so `PowerFullSpanLaw 4 σ` fires on
  `FactorCorrespondenceAt 2` ALONE (`powerFullSpanLaw_four`) — the `D = 2` supplies
  (`decidedSliceAt_two`, `zeroConeClause_two`) are closed.
* **§7 the dd assembly**: `dec_e1DdBox_eq_eisFace` (the E1-frame conversion) fires
  `ZcURLim (e1DdDecFam σ)` for EVERY `σ` from `FactorCorrespondenceAt 2`, and ER4's
  ramPair/type22/type41 rows land in minimal conditional form (type41: the leaf + the
  correspondence ONLY).

## Axiom fence

Lean core everywhere except what the consumed fronts already carry (B.42 through
IFCG34/35's counts); the C.33 cites must NOT occur.  Zero sorries at landing.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG51

open IsLocalRing Polynomial Filter Topology
open Uniformity.Density.Induction
open Uniformity.Density.Leaf
open Uniformity.Density.IFCG14 (DecidedValueLaw Witnessed)
open Uniformity.Density.IFCG16 (tendsto_decidedSeq_comp)
open Uniformity.Density.IFCG17 (stratDecCount decidedAt_unique monicPoly_coeff_eq_self)
open Uniformity.Density.IFCG21 (coneCellCount)
open Uniformity.Density.IFCG22 (classCoeffVal npHeight classNPSupport NPAttains
  ClassNPFace NPVisibleAt classNPSupport_le_apply le_classNPSupport classNPSupport_le)
open Uniformity.Density.IFCG23 (npHgt_monicPoly_top)
open Uniformity.Density.IFCG24 (ZcURLim ZcURLim_zero ZcURLim_sum ZcURLim_qmonomial
  shallowSet mem_stratum_X_pow_iff pureFaceSet coneRemainderCount ConeRemainderLaw
  npHeight_coe card_setOf_le_resOrd card_pi_set ZeroConeClause coneFamily
  zeroConeClause_two)
open Uniformity.Density.IFCG25 (stratDecCount_eq_cone_add_deep tendsto_deepDecCount
  deepDecCount)
open Uniformity.Density.IFCG26 (onSide_monicPoly_of_npAttains)
open Uniformity.Density.IFCG31 (ramPairType mixedType4)
open Uniformity.Density.IFCG34 (e1Box e1DdBox mem_e1Box_iff e1DdDecFam type22 type41
  E1IrrLeafDecision e1SplitFam e1IrrFam e2DecFam
  coneRemainderLaw_four_ramPair_of_sectors coneRemainderLaw_four_type22_of_sectors
  coneRemainderLaw_four_type41_of_sectors)
open Uniformity.Density.IFCG35 (MinFaceAt minFaceAt_support minFaceAt_min
  minFaceAt_unique classResidualPoly classResidualPoly_eq
  classResidualPoly_natDegree_pos powerSector remainderCarrier)
open Uniformity.Density.IFCG38 (classResidualPoly_monic)
open Uniformity.Density.IFCG39 (powerSector_data powerSector_mass_drop
  eisKey eisKey_monic eisKey_natDegree eis_root_pow_dvd_mk_iff
  devT devT_coeff devT_monic eis_residueCard)
open Uniformity.Density.IFCG43 (eis_root_irreducible devVec reassVec cellTransport
  cellTransport_apply cellTransport_symm_apply cellTransport_card_image card_coeff_eis
  eis_recentring_stack)
open Uniformity.Density.IFCG44 (alphaBox cellTransport_mem_alphaBox_iff card_alphaBox
  fullSpan_resPoly_iff_box fullSpan_raw_dvd fullSpan_corner minFaceAt_of_lattice
  fullSpan_pins powerSectorFull powerSectorProper PowerFullSpanLaw
  powerSector_eq_full_union_proper full_proper_disjoint PowerConvolutionDefectLaw)
open Uniformity.Density.IFCG47 (scaleType scaleType_data scaleType_degree
  scaleType_injective CellTypeScalingAt transport_decidedAt_iff
  powerFullSpanLaw_of_prime powerSectorFull_eq_empty_of_prime cellTypeScalingAt_one)
open Uniformity.Density.IFCG48 (FactorCorrespondenceAt
  cellTypeScalingAt_of_factorCorrespondence)
open Uniformity.Density.IFCG3 (scaleVecN monicPoly_scaleVecN_eq_scaleRoots bigTLoop)

attribute [local instance] Classical.propDecidable

/-! ## §0 — kit (private replicas of the established supply) -/

section Kit

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
  · intro ⟨h1, h2⟩
    have : j ∈ Finset.filter (OnSide φ f u ℓ) (Finset.range (f.natDegree + 1)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h1, h2⟩
    exact this

variable [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- IFCG39/44's representation supply (private replica): on a minimal face the
canonical class residual IS every lift's side residual, with the side set, finite
support and height data exported. -/
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

end Kit

/-! ## §1 — W1: the class-side pins (lattice + exact corner ⟹ face AND residual
degree) -/

section W1

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- ★ **W1 — THE CLASS-SIDE PINS**: at the Eisenstein frame `(1, e')`, the raw lattice
(`m − j ≤ e'·v_j`) with EXACT corner (`v_0 = D`, `e'·D = m`) reconstructs the minimal
face (landed `minFaceAt_of_lattice`) AND pins the residual degree to `D` — the side of
any lift spans exactly `[0, m]`.  This is the missing degree read of the cell
description's `⟸` half. -/
theorem lattice_pins {π : O} (hπ : Irreducible π) {m K e' D : ℕ} (he' : 2 ≤ e')
    (hfull : e' * D = m) (hmK : m ≤ K) (hm0 : 0 < m)
    {c : Coeff O m K}
    (hlat : ∀ j : Fin m, m - (j : ℕ) ≤ e' * resOrd (c j))
    (hcorner : resOrd (c ⟨0, hm0⟩) = D) :
    MinFaceAt c 1 e' ∧ (classResidualPoly π c 1 e').natDegree = D := by
  have he'' : 0 < e' := by omega
  have hcop : Nat.Coprime 1 e' := Nat.coprime_one_left e'
  have hlat1 : ∀ j : Fin m, 1 * (m - (j : ℕ)) ≤ e' * resOrd (c j) := by
    intro j
    rw [Nat.one_mul]
    exact hlat j
  have hcorner1 : resOrd (c ⟨0, hm0⟩) = 1 * D := by
    rw [Nat.one_mul]
    exact hcorner
  have hF : MinFaceAt c 1 e' :=
    minFaceAt_of_lattice (le_refl 1) (by omega) hcop hfull hmK hm0 hlat1 hcorner1
  refine ⟨hF, ?_⟩
  -- the residual degree via the side pins of an arbitrary lift
  obtain ⟨a, ha⟩ := proj_surjective O m K c
  obtain ⟨hne, H₀, hH₀, htop, hcrp⟩ := resPoly_rep hπ hF ha
  have hnd := natDegree_resPoly hπ isKey_X he'' hcop htop hne hH₀
  rw [hcrp, hnd.1]
  obtain ⟨hh1, hhe, hcop', hface, hAm, hvis⟩ := hF
  have hdegm : (monicPoly a).natDegree = m := monicPoly_natDegree a
  -- sideMax = m (the monic attainment, transported to the lift)
  obtain ⟨hOnm, hsuppm⟩ := onSide_monicPoly_of_npAttains hπ he'' hvis hAm ha
  have hmmem : m ∈ sideSet X (monicPoly a) 1 e' :=
    mem_sideSet_iff'.mpr ⟨by omega, hOnm⟩
  have hmax : sideMax X (monicPoly a) 1 e' hne = m := by
    unfold sideMax
    refine le_antisymm ?_ (Finset.le_max' _ m hmmem)
    have h2 := Finset.max'_mem (sideSet X (monicPoly a) 1 e') hne
    obtain ⟨h3, -⟩ := mem_sideSet_iff'.mp h2
    omega
  -- the class attains at 0 (lattice + exact corner)
  have hnpm : npHeight c m = 0 := by
    unfold npHeight
    rw [dif_neg (lt_irrefl m)]
  have hkey : ∀ i, i ≤ m → 1 * m ≤ e' * npHeight c i + 1 * i := by
    intro i him
    rcases Nat.lt_or_ge i m with hlt | hge
    · have hnp : npHeight c i = resOrd (c ⟨i, hlt⟩) := by
        have h5 := npHeight_coe c ⟨i, hlt⟩
        simpa using h5
      rw [hnp]
      have h8 := hlat ⟨i, hlt⟩
      simp only at h8
      generalize hX : e' * resOrd (c ⟨i, hlt⟩) = A at h8 ⊢
      omega
    · have him' : i = m := le_antisymm him hge
      subst him'
      rw [hnpm, Nat.mul_zero, Nat.zero_add]
  have hsup : classNPSupport c 1 e' = 1 * m :=
    le_antisymm (classNPSupport_le c 1 e') (le_classNPSupport hkey)
  have hnp0 : npHeight c 0 = D := by
    have h5 : npHeight c 0 = resOrd (c ⟨0, hm0⟩) := by
      simpa using npHeight_coe c ⟨0, hm0⟩
    rw [h5, hcorner]
  have hA0 : NPAttains c 1 e' 0 := by
    refine ⟨Nat.zero_le m, ?_⟩
    rw [hsup, hnp0, hfull]
    omega
  obtain ⟨hOn0, -⟩ := onSide_monicPoly_of_npAttains hπ he'' hvis hA0 ha
  have h0mem : (0 : ℕ) ∈ sideSet X (monicPoly a) 1 e' :=
    mem_sideSet_iff'.mpr ⟨by omega, hOn0⟩
  have hmin0 : sideMin X (monicPoly a) 1 e' hne = 0 :=
    Nat.le_zero.mp (Finset.min'_le _ 0 h0mem)
  -- sideDeg = (m − 0)/e' = D
  unfold sideDeg
  rw [hmax, hmin0, Nat.sub_zero, ← hfull, Nat.mul_div_cancel_left D he'']

end W1

/-! ## §2 — W2: the reconstruction (deep box ⟹ lattice + exact corner on the lift,
hence the face, the residual degree, and the residual power) -/

section W2

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- Coefficientwise valuation of the Eisenstein key powers:
`π^(t − ⌊l/e'⌋) ∣ (eisKey^t).coeff l`. -/
private theorem eisKey_pow_coeff_dvd {π w : O} {e' : ℕ} (he'' : 0 < e') :
    ∀ t l : ℕ, π ^ (t - l / e') ∣ (eisKey π w e' ^ t).coeff l := by
  intro t
  induction t with
  | zero =>
      intro l
      simp
  | succ t ih =>
      intro l
      have hsplit : eisKey π w e' ^ (t + 1)
          = eisKey π w e' ^ t * Polynomial.X ^ e'
            + eisKey π w e' ^ t * Polynomial.C (w * π) := by
        rw [pow_succ, eisKey, mul_add]
      rw [hsplit, Polynomial.coeff_add]
      refine dvd_add ?_ ?_
      · rw [Polynomial.coeff_mul_X_pow']
        by_cases hle : e' ≤ l
        · rw [if_pos hle]
          refine dvd_trans (pow_dvd_pow π ?_) (ih (l - e'))
          have h3 : l / e' = (l - e') / e' + 1 := by
            conv_lhs => rw [show l = (l - e') + e' by omega]
            exact Nat.add_div_right _ he''
          omega
        · rw [if_neg hle]
          exact dvd_zero _
      · rw [Polynomial.coeff_mul_C]
        have h5 : π ^ (t - l / e') * π ∣ (eisKey π w e' ^ t).coeff l * (w * π) :=
          mul_dvd_mul (ih l) (dvd_mul_left π w)
        have h6 : π ^ (t - l / e' + 1) ∣ (eisKey π w e' ^ t).coeff l * (w * π) := by
          rwa [← pow_succ] at h5
        exact dvd_trans (pow_dvd_pow π (by omega)) h6

variable [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- ★ **W2 (lift half) — THE DIGIT LATTICE READ**: a monic block of degree `e'·D`
whose `eisKey`-adic digits lie in the deep box satisfies the raw purity lattice
`π^⌈(m−j)/e'⌉ ∣ coeff j` with EXACT corner valuation `D` — the `⟸` of the cell
description at the lift level.  (The `+1` of the box is exactly the corner's
strictness: the top digit is `1`, so the constant term is `(wπ)^D` plus a
`π^(D+1)`-divisible tail.) -/
private theorem coeff_lattice_of_dev_box {π w : O} (hπ : Irreducible π)
    (hw : IsLocalRing.residue O w ≠ 0) {e' D : ℕ} (he' : 2 ≤ e')
    {g : Polynomial O} (hg : g.Monic) (hdeg : g.natDegree = e' * D)
    (hbox : ∀ t, t < D → (AdjoinRoot.root (eisKey π w e')) ^ (e' * (D - t) + 1)
        ∣ AdjoinRoot.mk (eisKey π w e') (dev (eisKey π w e') g t)) :
    (∀ j, j < e' * D → π ^ ((e' * D - j + (e' - 1)) / e') ∣ g.coeff j)
      ∧ π ^ D ∣ g.coeff 0 ∧ ¬ π ^ (D + 1) ∣ g.coeff 0 := by
  have he'' : 0 < e' := by omega
  set φ := eisKey π w e' with hφdef
  have hφm : φ.Monic := eisKey_monic he''
  have hφd : φ.natDegree = e' := eisKey_natDegree he''
  have hφd0 : 0 < φ.natDegree := by omega
  -- the development identity
  have hsum : ∑ t ∈ Finset.range (D + 1), dev φ g t * φ ^ t = g := by
    refine sum_dev_eq hφm hφd0 g ?_
    rw [hdeg, hφd]
    have h1 : (D + 1) * e' = e' * D + e' := by ring
    omega
  -- digit degree bounds
  have hdevdeg : ∀ t, (dev φ g t).degree < ((e' : ℕ) : WithBot ℕ) := by
    intro t
    have h := degree_dev_lt hφm hφd0 g t
    rwa [Polynomial.degree_eq_natDegree hφm.ne_zero, hφd] at h
  -- the top digit is exactly 1
  have hdevD : dev φ g D = 1 := by
    have hmkD : AdjoinRoot.mk φ (dev φ g D) = 1 := by
      have h1 := devT_coeff (φ := φ) (k := D) g (le_refl D)
      have h2 := devT_monic hφm hφd0 hg (by rw [hφd]; exact hdeg)
      have h3 : (devT φ D g).coeff D = 1 := by
        have h4 := h2.1.coeff_natDegree
        rwa [h2.2] at h4
      rw [h1] at h3
      exact h3
    have hdvd : φ ∣ (dev φ g D - 1) := by
      rw [← AdjoinRoot.mk_eq_zero, map_sub, hmkD, map_one, sub_self]
    have hdeglt : (dev φ g D - 1).degree < φ.degree := by
      refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) ?_
      rw [Polynomial.degree_eq_natDegree hφm.ne_zero, hφd]
      refine max_lt (hdevdeg D) ?_
      rw [Polynomial.degree_one]
      exact_mod_cast he''
    have h5 := Polynomial.eq_zero_of_dvd_of_degree_lt hdvd hdeglt
    have h6 : dev φ g D - 1 + 1 = 0 + 1 := by rw [h5]
    rwa [sub_add_cancel, zero_add] at h6
  -- the digit coefficient bounds from the box
  have hdig : ∀ t, t < D → ∀ i, i < e' →
      π ^ ((e' * (D - t) + 1 + e' - 1 - i) / e') ∣ (dev φ g t).coeff i := by
    intro t ht
    exact (eis_root_pow_dvd_mk_iff hπ hw he'' (hdevdeg t) (e' * (D - t) + 1)).mp
      (hbox t ht)
  -- the uniform weakening π^(D−t) on every digit (t = D included via dev_D = 1)
  have hdig' : ∀ t, t ≤ D → ∀ i, i < e' → π ^ (D - t) ∣ (dev φ g t).coeff i := by
    intro t ht i hi
    rcases Nat.lt_or_ge t D with htD | htD
    · refine dvd_trans (pow_dvd_pow π ?_) (hdig t htD i hi)
      rw [Nat.le_div_iff_mul_le he'']
      have h1 : (D - t) * e' = e' * (D - t) := Nat.mul_comm _ _
      generalize hA : e' * (D - t) = A at h1 ⊢
      omega
    · have htD' : t = D := le_antisymm ht htD
      subst htD'
      simp
  -- the coefficient read of the development sum
  have hcoeff : ∀ j, g.coeff j
      = ∑ t ∈ Finset.range (D + 1), (dev φ g t * φ ^ t).coeff j := by
    intro j
    conv_lhs => rw [← hsum]
    exact Polynomial.finsetSum_coeff _ _ _
  -- the corner decomposition: coeff 0 = (π^{D+1}-divisible tail) + (wπ)^D
  have hc0 : g.coeff 0
      = (∑ t ∈ Finset.range D, (dev φ g t * φ ^ t).coeff 0) + (w * π) ^ D := by
    rw [hcoeff 0, Finset.sum_range_succ]
    congr 1
    rw [hdevD, one_mul]
    have h1 : (φ ^ D).coeff 0 = (φ.coeff 0) ^ D := by
      rw [← Polynomial.constantCoeff_apply, map_pow, Polynomial.constantCoeff_apply]
    rw [h1]
    congr 1
    rw [hφdef, eisKey, Polynomial.coeff_add, Polynomial.coeff_X_pow,
      if_neg (by omega : ¬ (0 = e')), Polynomial.coeff_C_zero, zero_add]
  have htail : π ^ (D + 1) ∣ ∑ t ∈ Finset.range D, (dev φ g t * φ ^ t).coeff 0 := by
    refine Finset.dvd_sum ?_
    intro t ht
    rw [Finset.mem_range] at ht
    rw [Polynomial.mul_coeff_zero]
    have h1 : π ^ (D - t + 1) ∣ (dev φ g t).coeff 0 := by
      refine dvd_trans (pow_dvd_pow π ?_) (hdig t ht 0 he'')
      rw [Nat.le_div_iff_mul_le he'']
      have h2 : (D - t + 1) * e' = e' * (D - t) + e' := by ring
      generalize hA : e' * (D - t) = A at h2 ⊢
      omega
    have h2 : π ^ t ∣ (φ ^ t).coeff 0 := by
      have h3 : (φ ^ t).coeff 0 = (φ.coeff 0) ^ t := by
        rw [← Polynomial.constantCoeff_apply, map_pow, Polynomial.constantCoeff_apply]
      have h4 : φ.coeff 0 = w * π := by
        rw [hφdef, eisKey, Polynomial.coeff_add, Polynomial.coeff_X_pow,
          if_neg (by omega : ¬ (0 = e')), Polynomial.coeff_C_zero, zero_add]
      rw [h3, h4, mul_pow]
      exact dvd_mul_left _ _
    have h5 : π ^ (D - t + 1 + t) ∣ (dev φ g t).coeff 0 * (φ ^ t).coeff 0 := by
      rw [pow_add]
      exact mul_dvd_mul h1 h2
    refine dvd_trans (pow_dvd_pow π (by omega)) h5
  refine ⟨?_, ?_, ?_⟩
  · -- the raw lattice
    intro j hj
    rw [hcoeff j]
    refine Finset.dvd_sum ?_
    intro t ht
    rw [Finset.mem_range] at ht
    rw [Polynomial.coeff_mul]
    refine Finset.dvd_sum ?_
    rintro ⟨i, l⟩ hil
    rw [Finset.mem_antidiagonal] at hil
    by_cases hie : i < e'
    · have h1 : π ^ (D - t) ∣ (dev φ g t).coeff i := hdig' t (by omega) i hie
      have h2 : π ^ (t - l / e') ∣ (φ ^ t).coeff l := eisKey_pow_coeff_dvd he'' t l
      have h3 : π ^ (D - t + (t - l / e')) ∣ (dev φ g t).coeff i * (φ ^ t).coeff l := by
        rw [pow_add]
        exact mul_dvd_mul h1 h2
      refine dvd_trans (pow_dvd_pow π ?_) h3
      -- (e'·D − j + (e'−1))/e' ≤ (D − t) + (t − l/e')
      have hkey : (e' * D - j + (e' - 1)) / e' + l / e' < D + 1 := by
        have hmul : e' * ((e' * D - j + (e' - 1)) / e' + l / e') < e' * (D + 1) := by
          rw [Nat.mul_add]
          have hG : e' * ((e' * D - j + (e' - 1)) / e') ≤ e' * D - j + (e' - 1) :=
            Nat.mul_div_le _ e'
          have hl : e' * (l / e') ≤ l := Nat.mul_div_le l e'
          have hDe : e' * (D + 1) = e' * D + e' := by ring
          generalize hA : e' * ((e' * D - j + (e' - 1)) / e') = A at hG ⊢
          generalize hB : e' * (l / e') = B at hl ⊢
          generalize hC : e' * D = C at hG hj hDe ⊢
          omega
        exact Nat.lt_of_mul_lt_mul_left hmul
      generalize hq : l / e' = q at hkey ⊢
      omega
    · have h0 : (dev φ g t).coeff i = 0 := by
        refine Polynomial.coeff_eq_zero_of_degree_lt ?_
        refine lt_of_lt_of_le (hdevdeg t) ?_
        exact_mod_cast Nat.le_of_not_lt hie
      rw [h0, zero_mul]
      exact dvd_zero _
  · -- π^D divides the corner
    rw [hc0]
    refine dvd_add (dvd_trans (pow_dvd_pow π (by omega)) htail) ?_
    rw [mul_pow]
    exact dvd_mul_left _ _
  · -- π^(D+1) does not divide the corner
    intro hcon
    rw [hc0] at hcon
    have h7 : π ^ (D + 1) ∣ (w * π) ^ D := (dvd_add_right htail).mp hcon
    rw [mul_pow] at h7
    have h9 : π ^ D * π ∣ π ^ D * w ^ D := by
      rw [← pow_succ]
      refine dvd_trans h7 ?_
      rw [mul_comm]
    have h8 : π ∣ w ^ D :=
      (mul_dvd_mul_iff_left (pow_ne_zero D hπ.ne_zero)).mp h9
    have h10 : π ∣ w := hπ.prime.dvd_of_dvd_pow h8
    obtain ⟨u, rfl⟩ := h10
    have h11 : IsLocalRing.residue O π = 0 := by
      have h12 : π ∈ maximalIdeal O := by
        rw [IsLocalRing.mem_maximalIdeal]
        exact hπ.not_isUnit
      exact (IsLocalRing.residue_eq_zero_iff π).mpr h12
    exact hw (by rw [map_mul, h11, zero_mul])

/-- ★★ **W2 — THE RECONSTRUCTION**: a class of mass `e'·D` whose transport lies in the
`α`-lattice box IS an Eisenstein full-span cell member — minimal face `(1, e')`,
residual degree `D`, residual `(X − z̄)^D`.  This is the `⊇` half of the image
characterization `cellTransport '' cell = alphaBox ∩ decidedSet` (the `⊆` half is the
landed forward chain `fullSpan_raw_dvd`/`fullSpan_resPoly_iff_box`). -/
theorem cell_of_box {π z : O} (hπ : Irreducible π) (hz : IsLocalRing.residue O z ≠ 0)
    (hw : IsLocalRing.residue O (-z) ≠ 0) {e' D : ℕ} (he' : 2 ≤ e') (hD0 : 0 < D)
    {N : ℕ} (hDN : D < N) (hmN : e' * D ≤ N)
    [IsDomain (AdjoinRoot (eisKey π (-z) e'))]
    [IsDiscreteValuationRing (AdjoinRoot (eisKey π (-z) e'))]
    [Finite (ResidueField (AdjoinRoot (eisKey π (-z) e')))]
    {c : Coeff O (e' * D) N}
    (hbox : cellTransport hπ hw he' D N c ∈ alphaBox π (-z) e' D (e' * N)) :
    MinFaceAt c 1 e' ∧ (classResidualPoly π c 1 e').natDegree = D
      ∧ classResidualPoly π c 1 e'
          = (Polynomial.X - Polynomial.C
              (resFieldXEquiv O (IsLocalRing.residue O z))) ^ D := by
  have he'' : 0 < e' := by omega
  have hm0 : 0 < e' * D := Nat.mul_pos he'' hD0
  obtain ⟨a, ha⟩ := proj_surjective O (e' * D) N c
  have hbox' : cellTransport hπ hw he' D N (proj O (e' * D) N a)
      ∈ alphaBox π (-z) e' D (e' * N) := by
    rw [ha]
    exact hbox
  have hdev := (cellTransport_mem_alphaBox_iff hπ hw he' hDN a).mp hbox'
  obtain ⟨hlat_lift, hcor1, hcor2⟩ :=
    coeff_lattice_of_dev_box hπ hw he' (monicPoly_monic a) (monicPoly_natDegree a) hdev
  -- the class lattice
  have hlatC : ∀ j : Fin (e' * D), (e' * D) - (j : ℕ) ≤ e' * resOrd (c j) := by
    rintro ⟨jn, hjn⟩
    show e' * D - jn ≤ e' * resOrd (c ⟨jn, hjn⟩)
    have hk_le : (e' * D - jn + (e' - 1)) / e' ≤ N := by
      have h2 : e' * (D + 1) = e' * D + e' := by ring
      have h3 : (e' * D - jn + (e' - 1)) / e' < D + 1 := by
        rw [Nat.div_lt_iff_lt_mul he'']
        have h4 : (D + 1) * e' = e' * (D + 1) := Nat.mul_comm _ _
        generalize hC : e' * D = C at h2 hjn ⊢
        omega
      have h5 : D ≤ e' * D := Nat.le_mul_of_pos_left D he''
      omega
    have hcj : c ⟨jn, hjn⟩ = Ideal.Quotient.mk ((maximalIdeal O) ^ N) (a ⟨jn, hjn⟩) := by
      rw [← ha]
      rfl
    have hdvd : π ^ ((e' * D - jn + (e' - 1)) / e') ∣ a ⟨jn, hjn⟩ := by
      have h6 := hlat_lift jn hjn
      rwa [monicPoly_coeff_lt a hjn] at h6
    have hge : (e' * D - jn + (e' - 1)) / e' ≤ resOrd (c ⟨jn, hjn⟩) := by
      rw [hcj]
      exact (resOrd_ge_iff hπ hk_le _).mpr hdvd
    have h7 := Nat.div_add_mod (e' * D - jn + (e' - 1)) e'
    have h8 : (e' * D - jn + (e' - 1)) % e' < e' := Nat.mod_lt _ he''
    have h9 : e' * ((e' * D - jn + (e' - 1)) / e') ≤ e' * resOrd (c ⟨jn, hjn⟩) :=
      Nat.mul_le_mul (le_refl e') hge
    have hjm : jn < e' * D := hjn
    clear hge hdvd hcj hk_le
    generalize hB : e' * resOrd (c ⟨jn, hjn⟩) = B at h9 ⊢
    generalize hA : e' * ((e' * D - jn + (e' - 1)) / e') = A at h7 h9
    generalize hC : e' * D = C at h7 h8 hjm ⊢
    omega
  -- the exact corner
  have hcornerC : resOrd (c ⟨0, hm0⟩) = D := by
    have hc0eq : c ⟨0, hm0⟩ = Ideal.Quotient.mk ((maximalIdeal O) ^ N) (a ⟨0, hm0⟩) := by
      rw [← ha]
      rfl
    have ha0 : (monicPoly a).coeff 0 = a ⟨0, hm0⟩ := monicPoly_coeff_lt a hm0
    have hge : D ≤ resOrd (c ⟨0, hm0⟩) := by
      rw [hc0eq]
      refine (resOrd_ge_iff hπ (by omega) _).mpr ?_
      rwa [ha0] at hcor1
    have hlt : ¬ (D + 1 ≤ resOrd (c ⟨0, hm0⟩)) := by
      intro hcon
      rw [hc0eq] at hcon
      have h10 := (resOrd_ge_iff hπ (by omega : D + 1 ≤ N) _).mp hcon
      rw [ha0] at hcor2
      exact hcor2 h10
    omega
  obtain ⟨hF, hdeg⟩ := lattice_pins hπ he' rfl hmN hm0 hlatC hcornerC
  exact ⟨hF, hdeg, (fullSpan_resPoly_iff_box hπ hz he' hF hdeg rfl ha).mpr hdev⟩

end W2

/-! ## §3 — L2: the deep-box decided limit.  First the stratum-census limit from the
two law inputs (IFCG25's cone + deep partition, consumed at the zero centre), then the
`q^(−e'·T_D)` squeeze converting `#(alphaBox ∩ decided)` to it. -/

section StratLimit

/-- ★ **THE STRATUM-CENSUS LIMIT**: `DecidedValueLaw D σ'` + `ZeroConeClause D σ'`
produce ONE rational pair with
`stratDecCount O D σ' L (X^D) / q^(D·L) → value` at every complete DVR — IFCG25's
exact partition `stratum = cone + deep` at the centre `0`, its deep limit
`q^(−T_D)·decidedDensity`, and the two value inputs, summed.  (The `∀ O` clause is
the instantiation point for the recentring rings.) -/
theorem tendsto_stratDec_of_laws {D : ℕ} (hD : 1 ≤ D) {σ' : FactorizationType}
    (hDV : DecidedValueLaw D σ') (hZC : ZeroConeClause D σ') :
    ∃ n d : Polynomial ℚ, d ≠ 0 ∧
      ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
        d.eval ((residueCard O : ℕ) : ℚ) ≠ 0 ∧
          Filter.Tendsto
            (fun L => (stratDecCount O D σ' L (Polynomial.X ^ D) : ℝ)
              / ((residueCard O : ℕ) : ℝ) ^ (D * L))
            Filter.atTop
            (nhds (((n.eval ((residueCard O : ℕ) : ℚ)
              / d.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ))) := by
  obtain ⟨nc, dc, hdc, hvalc⟩ := hZC
  obtain ⟨nv, dv, hdv, hvalv⟩ := hDV
  refine ⟨nc * (Polynomial.X ^ bigTLoop D * dv) + dc * nv,
    dc * (Polynomial.X ^ bigTLoop D * dv),
    mul_ne_zero hdc (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hdv), ?_⟩
  intro O _ _ _ _ _
  obtain ⟨hnec, hlimc⟩ := hvalc O
  obtain ⟨hnev, hdens⟩ := hvalv O
  have hq2 : 2 ≤ residueCard O := two_le_residueCard O
  have hqQ : ((residueCard O : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hTQ : ((residueCard O : ℕ) : ℚ) ^ bigTLoop D ≠ 0 := pow_ne_zero _ hqQ
  have hden : (dc * (Polynomial.X ^ bigTLoop D * dv)).eval
      ((residueCard O : ℕ) : ℚ) ≠ 0 := by
    rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    exact mul_ne_zero hnec (mul_ne_zero hTQ hnev)
  refine ⟨hden, ?_⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  -- the value identity in ℚ: cone value + q^(−T)·decided value = the composed pair
  have hvalQ : (nc.eval ((residueCard O : ℕ) : ℚ) / dc.eval ((residueCard O : ℕ) : ℚ) : ℚ)
      + (((residueCard O : ℕ) : ℚ) ^ bigTLoop D)⁻¹
        * (nv.eval ((residueCard O : ℕ) : ℚ) / dv.eval ((residueCard O : ℕ) : ℚ))
      = ((nc * (Polynomial.X ^ bigTLoop D * dv) + dc * nv).eval ((residueCard O : ℕ) : ℚ)
          / (dc * (Polynomial.X ^ bigTLoop D * dv)).eval ((residueCard O : ℕ) : ℚ) : ℚ) := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X]
    field_simp
  have hlim_deep := tendsto_deepDecCount (m := D) hπ σ' (0 : ResidueField O)
  rw [hdens] at hlim_deep
  have hsum := (hlimc π hπ).add hlim_deep
  have hvalR : (((nc.eval ((residueCard O : ℕ) : ℚ)
        / dc.eval ((residueCard O : ℕ) : ℚ) : ℚ)) : ℝ)
      + ((residueCard O : ℝ) ^ bigTLoop D)⁻¹
        * (((nv.eval ((residueCard O : ℕ) : ℚ)
            / dv.eval ((residueCard O : ℕ) : ℚ) : ℚ)) : ℝ)
      = ((((nc * (Polynomial.X ^ bigTLoop D * dv) + dc * nv).eval
            ((residueCard O : ℕ) : ℚ)
          / (dc * (Polynomial.X ^ bigTLoop D * dv)).eval
            ((residueCard O : ℕ) : ℚ) : ℚ)) : ℝ) := by
    rw [← hvalQ]
    push_cast
    ring
  rw [hvalR] at hsum
  -- the exact partition at every finite level, at the zero centre
  have hshift : ∀ M : ℕ,
      coneFamily D σ' O π M
        + (deepDecCount π D σ' M 0 : ℝ) / (residueCard O : ℝ) ^ (D * (M + D))
      = (stratDecCount O D σ' (M + D) (Polynomial.X ^ D) : ℝ)
          / (residueCard O : ℝ) ^ (D * (M + D)) := by
    intro M
    have h0 : ((Polynomial.X + Polynomial.C (0 : ResidueField O)) ^ D)
        = (Polynomial.X ^ D : Polynomial (ResidueField O)) := by
      rw [Polynomial.C_0, add_zero]
    rw [← h0, stratDecCount_eq_cone_add_deep hπ (by omega : 0 < D) σ' M 0]
    push_cast
    rw [add_div]
    rfl
  refine (Filter.tendsto_add_atTop_iff_nat D).mp ?_
  exact hsum.congr fun M => hshift M

end StratLimit

section Squeeze

/-- Fibered preimage count over the image: for an additive hom and a subset of its
range, `#f⁻¹(S) = #ker · #S` (the range-restriction of `card_preimage_of_surjective`). -/
private theorem card_preimage_of_subset_range {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] [Finite A] (f : A →+ B) (S : Set B) (hS : S ⊆ Set.range f) :
    Nat.card (f ⁻¹' S) = Nat.card f.ker * Nat.card S := by
  classical
  have hpre : f ⁻¹' S = f.rangeRestrict ⁻¹' (Subtype.val ⁻¹' S) := rfl
  have hcard : Nat.card (Subtype.val ⁻¹' S : Set f.range) = Nat.card S := by
    have hsub : S ⊆ Set.range (Subtype.val : f.range → B) := by
      rw [Subtype.range_coe]
      exact fun x hx => hS hx
    have h1 : Subtype.val '' (Subtype.val ⁻¹' S : Set f.range) = S :=
      Set.image_preimage_eq_of_subset hsub
    calc Nat.card (Subtype.val ⁻¹' S : Set f.range)
        = Nat.card (Subtype.val '' (Subtype.val ⁻¹' S : Set f.range)) :=
          (Nat.card_image_of_injective Subtype.val_injective _).symm
      _ = Nat.card S := by rw [h1]
  have h2 := card_preimage_of_surjective f.rangeRestrict f.rangeRestrict_surjective
    (Subtype.val ⁻¹' S)
  rw [hpre, h2, hcard]
  congr 1
  rw [AddMonoidHom.ker_rangeRestrict]

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Finite (ResidueField R)]

/-- The same-window coordinate scaling `u_t ↦ α^{κ t}·u_t` (additive hom on the
level-`K` coefficient box). -/
private def scaledHom (α : R) {D : ℕ} (K : ℕ) (κ : Fin D → ℕ) :
    Coeff R D K →+ Coeff R D K where
  toFun u := fun t => Ideal.Quotient.mk ((maximalIdeal R) ^ K) (α ^ κ t) * u t
  map_zero' := by
    funext t
    simp
  map_add' u v := by
    funext t
    simp [mul_add]

private theorem scaledHom_apply (α : R) {D : ℕ} (K : ℕ) (κ : Fin D → ℕ)
    (u : Coeff R D K) (t : Fin D) :
    scaledHom α K κ u t
      = Ideal.Quotient.mk ((maximalIdeal R) ^ K) (α ^ κ t) * u t := rfl

/-- Scale by `α` then truncate to a lower window (additive hom `Coeff K → Coeff L`). -/
private def stratHom (α : R) {D K L : ℕ} (hL : L ≤ K) :
    Coeff R D K →+ Coeff R D L where
  toFun u := fun t => resFactor hL (Ideal.Quotient.mk ((maximalIdeal R) ^ K) α * u t)
  map_zero' := by
    funext t
    simp
  map_add' u v := by
    funext t
    simp [mul_add]

private theorem stratHom_apply (α : R) {D K L : ℕ} (hL : L ≤ K)
    (u : Coeff R D K) (t : Fin D) :
    stratHom α hL u t
      = resFactor hL (Ideal.Quotient.mk ((maximalIdeal R) ^ K) α * u t) := rfl

/-- The scaled image's range is exactly the `κ`-divisibility box. -/
private theorem mem_range_scaledHom {α : R} (hα : Irreducible α) {D K : ℕ}
    (κ : Fin D → ℕ) (hκ : ∀ t, κ t ≤ K) (b : Coeff R D K) :
    b ∈ Set.range (scaledHom α K κ) ↔ ∀ t, κ t ≤ resOrd (b t) := by
  constructor
  · rintro ⟨u, rfl⟩ t
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (u t)
    rw [scaledHom_apply, ← hy, ← map_mul]
    exact (resOrd_ge_iff hα (hκ t) _).mpr (dvd_mul_right _ _)
  · intro hb
    have hx : ∀ t, ∃ x : R,
        Ideal.Quotient.mk ((maximalIdeal R) ^ K) (α ^ κ t * x) = b t := by
      intro t
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (b t)
      have hdvd : α ^ κ t ∣ y :=
        (resOrd_ge_iff hα (hκ t) y).mp (by rw [hy]; exact hb t)
      obtain ⟨x, hxeq⟩ := hdvd
      exact ⟨x, by rw [← hxeq, hy]⟩
    choose x hx using hx
    refine ⟨proj R D K x, ?_⟩
    funext t
    rw [scaledHom_apply]
    show Ideal.Quotient.mk ((maximalIdeal R) ^ K) (α ^ κ t)
        * Ideal.Quotient.mk ((maximalIdeal R) ^ K) (x t) = b t
    rw [← map_mul]
    exact hx t

/-- The scaled map's kernel count: `q^(Σ κ)`. -/
private theorem card_ker_scaledHom {α : R} (hα : Irreducible α) {D K : ℕ}
    (κ : Fin D → ℕ) (hκ : ∀ t, κ t ≤ K) :
    Nat.card (scaledHom (R := R) α K κ).ker = residueCard R ^ (∑ t, κ t) := by
  classical
  have hα0 : α ≠ 0 := hα.ne_zero
  have hset : ((scaledHom (R := R) α K κ).ker : Set (Coeff R D K))
      = {u : Coeff R D K | ∀ t, u t ∈ {x : Res R K | K - κ t ≤ resOrd x}} := by
    ext u
    simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, Set.mem_setOf_eq]
    constructor
    · intro h t
      have h1 : scaledHom α K κ u t = 0 := by rw [h]; rfl
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (u t)
      rw [scaledHom_apply, ← hy, ← map_mul] at h1
      have h2 : α ^ K ∣ α ^ κ t * y := by
        rw [← mem_maximalIdeal_pow_iff_dvd_of_irr hα]
        exact (Ideal.Quotient.eq_zero_iff_mem).mp h1
      have h3 : α ^ (κ t) * α ^ (K - κ t) ∣ α ^ (κ t) * y := by
        rw [← pow_add]
        have h4 : κ t + (K - κ t) = K := by
          have := hκ t
          omega
        rw [h4]
        exact h2
      have h5 : α ^ (K - κ t) ∣ y :=
        (mul_dvd_mul_iff_left (pow_ne_zero (κ t) hα0)).mp h3
      rw [← hy]
      exact (resOrd_ge_iff (N := K) hα (by omega) y).mpr h5
    · intro h
      funext t
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (u t)
      have h5 : α ^ (K - κ t) ∣ y :=
        (resOrd_ge_iff (N := K) hα (by have := hκ t; omega) y).mp (by rw [hy]; exact h t)
      obtain ⟨x, hxeq⟩ := h5
      show scaledHom α K κ u t = 0
      rw [scaledHom_apply, ← hy, ← map_mul, hxeq]
      rw [Ideal.Quotient.eq_zero_iff_mem, mem_maximalIdeal_pow_iff_dvd_of_irr hα]
      refine ⟨x, ?_⟩
      rw [← mul_assoc, ← pow_add]
      congr 2
      have := hκ t
      omega
  have hcong : Nat.card (scaledHom (R := R) α K κ).ker
      = Nat.card {u : Coeff R D K | ∀ t, u t ∈ {x : Res R K | K - κ t ≤ resOrd x}} :=
    Nat.card_congr (Equiv.setCongr hset)
  rw [hcong, card_pi_set]
  have hfac : ∀ t : Fin D,
      Nat.card ({x : Res R K | K - κ t ≤ resOrd x} : Set (Res R K))
        = residueCard R ^ (K - (K - κ t)) := fun t =>
    card_setOf_le_resOrd (by omega)
  rw [Finset.prod_congr rfl (fun t _ => hfac t), Finset.prod_pow_eq_pow_sum]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  have := hκ t
  omega

/-- The strat map's range is exactly the level-`L` stratum condition. -/
private theorem mem_range_stratHom {α : R} (hα : Irreducible α) {D K L : ℕ}
    (hL1 : 1 ≤ L) (hL : L ≤ K) (w : Coeff R D L) :
    w ∈ Set.range (stratHom (D := D) α hL) ↔ ∀ t, 1 ≤ resOrd (w t) := by
  constructor
  · rintro ⟨u, rfl⟩ t
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (u t)
    rw [stratHom_apply, ← hy, ← map_mul, resFactor_mk]
    refine (resOrd_ge_iff (N := L) hα hL1 _).mpr ?_
    rw [pow_one]
    exact dvd_mul_right _ _
  · intro hw
    have hx : ∀ t, ∃ x : R,
        Ideal.Quotient.mk ((maximalIdeal R) ^ L) (α * x) = w t := by
      intro t
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (w t)
      have hdvd : α ^ 1 ∣ y :=
        (resOrd_ge_iff hα hL1 y).mp (by rw [hy]; exact hw t)
      rw [pow_one] at hdvd
      obtain ⟨x, hxeq⟩ := hdvd
      exact ⟨x, by rw [← hxeq, hy]⟩
    choose x hx using hx
    refine ⟨proj R D K x, ?_⟩
    funext t
    rw [stratHom_apply]
    show resFactor hL (Ideal.Quotient.mk ((maximalIdeal R) ^ K) α
        * Ideal.Quotient.mk ((maximalIdeal R) ^ K) (x t)) = w t
    rw [← map_mul, resFactor_mk]
    exact hx t

/-- The strat map's kernel count: `q^(D·(K − L + 1))`. -/
private theorem card_ker_stratHom {α : R} (hα : Irreducible α) {D K L : ℕ}
    (hL1 : 1 ≤ L) (hL : L ≤ K) :
    Nat.card (stratHom (R := R) (D := D) α hL).ker
      = residueCard R ^ (D * (K - L + 1)) := by
  classical
  have hα0 : α ≠ 0 := hα.ne_zero
  have hset : ((stratHom (R := R) (D := D) α hL).ker : Set (Coeff R D K))
      = {u : Coeff R D K | ∀ t, u t ∈ {x : Res R K | L - 1 ≤ resOrd x}} := by
    ext u
    simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, Set.mem_setOf_eq]
    constructor
    · intro h t
      have h1 : stratHom α hL u t = 0 := by rw [h]; rfl
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (u t)
      rw [stratHom_apply, ← hy, ← map_mul, resFactor_mk] at h1
      have h2 : α ^ L ∣ α * y := by
        rw [← mem_maximalIdeal_pow_iff_dvd_of_irr hα]
        exact (Ideal.Quotient.eq_zero_iff_mem).mp h1
      have h3 : α ^ 1 * α ^ (L - 1) ∣ α ^ 1 * y := by
        rw [← pow_add, show 1 + (L - 1) = L by omega, pow_one]
        exact h2
      have h5 : α ^ (L - 1) ∣ y :=
        (mul_dvd_mul_iff_left (pow_ne_zero 1 hα0)).mp h3
      rw [← hy]
      exact (resOrd_ge_iff (N := K) hα (by omega) y).mpr h5
    · intro h
      funext t
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (u t)
      have h5 : α ^ (L - 1) ∣ y :=
        (resOrd_ge_iff (N := K) hα (by omega) y).mp (by rw [hy]; exact h t)
      obtain ⟨x, hxeq⟩ := h5
      show stratHom α hL u t = 0
      rw [stratHom_apply, ← hy, ← map_mul, resFactor_mk, hxeq]
      rw [Ideal.Quotient.eq_zero_iff_mem, mem_maximalIdeal_pow_iff_dvd_of_irr hα]
      refine ⟨x, ?_⟩
      rw [← mul_assoc, ← pow_succ']
      congr 2
      omega
  have hcong : Nat.card (stratHom (R := R) (D := D) α hL).ker
      = Nat.card {u : Coeff R D K | ∀ t, u t ∈ {x : Res R K | L - 1 ≤ resOrd x}} :=
    Nat.card_congr (Equiv.setCongr hset)
  rw [hcong, card_pi_set]
  have hfac : ∀ t : Fin D,
      Nat.card ({x : Res R K | L - 1 ≤ resOrd x} : Set (Res R K))
        = residueCard R ^ (K - (L - 1)) := fun _ =>
    card_setOf_le_resOrd (by omega)
  rw [Finset.prod_congr rfl (fun t _ => hfac t), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← pow_mul]
  congr 1
  have h1 : K - (L - 1) = K - L + 1 := by omega
  rw [h1, Nat.mul_comm]

/-- ★ **T1 — the lower transfer**: if the scale-truncated class is decided at the low
window `L`, the scaled class is decided at `K` — every lift of the scaled class is the
`α^{e'}`-root-scaling of a lift of the low class (`typeOf_scaleRoots`). -/
private theorem decided_scaled_of_strat {α : R} (hα : Irreducible α) {e' D K L : ℕ}
    (hLK : L ≤ K) {σ' : FactorizationType} (u : Coeff R D K)
    (hwin : ∀ t : Fin D, L + (e' * (D - (t : ℕ)) + 1) ≤ K + 1)
    (hpow : ∀ t : Fin D, e' * (D - (t : ℕ)) + 1 ≤ K)
    (hdec : DecidedAt R D σ' L (stratHom α hLK u)) :
    DecidedAt R D σ' K (scaledHom α K (fun t => e' * (D - (t : ℕ)) + 1) u) := by
  intro B hB
  obtain ⟨U, hU⟩ := proj_surjective R D K u
  have hBt : ∀ t : Fin D, ∃ c : R,
      B t = α ^ (e' * (D - (t : ℕ)) + 1) * U t + α ^ K * c := by
    intro t
    have h2 := congrFun hB t
    rw [scaledHom_apply, ← hU] at h2
    have h2' : Ideal.Quotient.mk ((maximalIdeal R) ^ K) (B t)
        = Ideal.Quotient.mk ((maximalIdeal R) ^ K)
            (α ^ (e' * (D - (t : ℕ)) + 1) * U t) := by
      refine h2.trans ?_
      exact (map_mul (Ideal.Quotient.mk ((maximalIdeal R) ^ K))
        (α ^ (e' * (D - (t : ℕ)) + 1)) (U t)).symm
    have h3 : α ^ K ∣ (B t - α ^ (e' * (D - (t : ℕ)) + 1) * U t) := by
      rw [← mem_maximalIdeal_pow_iff_dvd_of_irr hα]
      exact (Ideal.Quotient.eq).mp h2'
    obtain ⟨c, hc⟩ := h3
    refine ⟨c, ?_⟩
    have h4 := sub_eq_iff_eq_add.mp hc
    rw [h4]
    ring
  choose cvec hcvec using hBt
  set V : Fin D → R :=
    fun t => α * (U t + α ^ (K - (e' * (D - (t : ℕ)) + 1)) * cvec t) with hVdef
  have hBV : B = scaleVecN (α ^ e') V := by
    funext t
    show B t = (α ^ e') ^ (D - (t : ℕ))
        * (α * (U t + α ^ (K - (e' * (D - (t : ℕ)) + 1)) * cvec t))
    have hκK : (e' * (D - (t : ℕ)) + 1) + (K - (e' * (D - (t : ℕ)) + 1)) = K := by
      have := hpow t
      omega
    have hsplit : α ^ K
        = α ^ (e' * (D - (t : ℕ)) + 1) * α ^ (K - (e' * (D - (t : ℕ)) + 1)) := by
      rw [← pow_add, hκK]
    calc B t = α ^ (e' * (D - (t : ℕ)) + 1) * U t + α ^ K * cvec t := hcvec t
      _ = (α ^ e') ^ (D - (t : ℕ))
          * (α * (U t + α ^ (K - (e' * (D - (t : ℕ)) + 1)) * cvec t)) := by
        rw [hsplit, ← pow_mul]
        ring
  have hmono : monicPoly B = (monicPoly V).scaleRoots (α ^ e') := by
    rw [hBV, monicPoly_scaleVecN_eq_scaleRoots]
  have hty : typeOf (monicPoly B) = typeOf (monicPoly V) := by
    rw [hmono]
    exact typeOf_scaleRoots hα (monicPoly_monic V) e'
  have hV : proj R D L V = stratHom α hLK u := by
    funext t
    rw [stratHom_apply, ← hU]
    have hmk : resFactor hLK (Ideal.Quotient.mk ((maximalIdeal R) ^ K) α
        * proj R D K U t)
        = Ideal.Quotient.mk ((maximalIdeal R) ^ L) (α * U t) := by
      have h5 : Ideal.Quotient.mk ((maximalIdeal R) ^ K) α * proj R D K U t
          = Ideal.Quotient.mk ((maximalIdeal R) ^ K) (α * U t) :=
        (map_mul (Ideal.Quotient.mk ((maximalIdeal R) ^ K)) α (U t)).symm
      rw [h5, resFactor_mk]
    rw [hmk]
    show Ideal.Quotient.mk ((maximalIdeal R) ^ L) (V t) = _
    refine (Ideal.Quotient.eq).mpr ?_
    rw [mem_maximalIdeal_pow_iff_dvd_of_irr hα]
    have h6 : V t - α * U t
        = α ^ (1 + (K - (e' * (D - (t : ℕ)) + 1))) * cvec t := by
      rw [hVdef, pow_add, pow_one]
      ring
    rw [h6]
    refine dvd_mul_of_dvd_left (pow_dvd_pow α ?_) _
    have h1 := hwin t
    have h2 := hpow t
    omega
  rw [hty]
  exact hdec V hV

/-- ★ **T2 — the upper transfer**: if the scaled class is decided at `K`, the
scale-truncated class is decided at any window `L` deep enough that the truncation
loses only digits above the scaling exponents. -/
private theorem decided_strat_of_scaled {α : R} (hα : Irreducible α) {e' D K L : ℕ}
    (hLK : L ≤ K) {σ' : FactorizationType} (u : Coeff R D K)
    (hwin : ∀ t : Fin D, K ≤ (e' * (D - (t : ℕ)) + 1) + (L - 1)) (hL1 : 1 ≤ L)
    (hdec : DecidedAt R D σ' K (scaledHom α K (fun t => e' * (D - (t : ℕ)) + 1) u)) :
    DecidedAt R D σ' L (stratHom α hLK u) := by
  intro V hV
  obtain ⟨U, hU⟩ := proj_surjective R D K u
  have hVt : ∀ t : Fin D, ∃ d : R, V t = α * U t + α ^ L * d := by
    intro t
    have h2 := congrFun hV t
    rw [stratHom_apply, ← hU] at h2
    have hmk : resFactor hLK (Ideal.Quotient.mk ((maximalIdeal R) ^ K) α
        * proj R D K U t)
        = Ideal.Quotient.mk ((maximalIdeal R) ^ L) (α * U t) := by
      have h5 : Ideal.Quotient.mk ((maximalIdeal R) ^ K) α * proj R D K U t
          = Ideal.Quotient.mk ((maximalIdeal R) ^ K) (α * U t) :=
        (map_mul (Ideal.Quotient.mk ((maximalIdeal R) ^ K)) α (U t)).symm
      rw [h5, resFactor_mk]
    rw [hmk] at h2
    have h3 : α ^ L ∣ (V t - α * U t) := by
      rw [← mem_maximalIdeal_pow_iff_dvd_of_irr hα]
      exact (Ideal.Quotient.eq).mp h2
    obtain ⟨d, hd⟩ := h3
    refine ⟨d, ?_⟩
    have h4 := sub_eq_iff_eq_add.mp hd
    rw [h4]
    ring
  choose dvec hdvec using hVt
  set B : Fin D → R := scaleVecN (α ^ e') V with hBdef
  have hB : proj R D K B
      = scaledHom α K (fun t => e' * (D - (t : ℕ)) + 1) u := by
    funext t
    rw [scaledHom_apply, ← hU]
    have h5 : Ideal.Quotient.mk ((maximalIdeal R) ^ K) (α ^ (e' * (D - (t : ℕ)) + 1))
        * proj R D K U t
        = Ideal.Quotient.mk ((maximalIdeal R) ^ K)
            (α ^ (e' * (D - (t : ℕ)) + 1) * U t) :=
      (map_mul (Ideal.Quotient.mk ((maximalIdeal R) ^ K)) _ (U t)).symm
    rw [h5]
    show Ideal.Quotient.mk ((maximalIdeal R) ^ K) ((α ^ e') ^ (D - (t : ℕ)) * V t) = _
    refine (Ideal.Quotient.eq).mpr ?_
    rw [mem_maximalIdeal_pow_iff_dvd_of_irr hα]
    have h1 : (α ^ e') ^ (D - (t : ℕ)) * V t - α ^ (e' * (D - (t : ℕ)) + 1) * U t
        = α ^ (e' * (D - (t : ℕ)) + L) * dvec t := by
      rw [← pow_mul, hdvec t, pow_add]
      ring
    rw [h1]
    refine dvd_mul_of_dvd_left (pow_dvd_pow α ?_) _
    have h2 := hwin t
    omega
  have hdecB := hdec B hB
  have hmono : monicPoly B = (monicPoly V).scaleRoots (α ^ e') := by
    rw [hBdef, monicPoly_scaleVecN_eq_scaleRoots]
  have hty := typeOf_scaleRoots hα (monicPoly_monic V) e'
  rw [← hmono] at hty
  rw [← hty]
  exact hdecB

/-- ★★ **THE LOWER COUNT BOUND**: `q^(D·(K−P+1))·stratDecCount(P) ≤ q^(Σκ)·#(box ∩ dec)`
(`K = e'N`, `P = e'(N−D)`): every decided stratum class at the low window fills its
whole scaled fibre with decided box classes. -/
private theorem card_boxDec_lower {α : R} (hα : Irreducible α) {e' D N : ℕ}
    (he' : 1 ≤ e') (hD1 : 1 ≤ D) (hDN : D < N) (σ' : FactorizationType) :
    residueCard R ^ (D * (e' * N - e' * (N - D) + 1))
        * stratDecCount R D σ' (e' * (N - D)) (Polynomial.X ^ D)
      ≤ residueCard R ^ (∑ t : Fin D, (e' * (D - (t : ℕ)) + 1))
        * Nat.card {b : Coeff R D (e' * N) |
            (∀ t : Fin D, e' * (D - (t : ℕ)) + 1 ≤ resOrd (b t))
              ∧ DecidedAt R D σ' (e' * N) b} := by
  classical
  have hPK : e' * (N - D) ≤ e' * N := Nat.mul_le_mul (le_refl e') (by omega)
  have hP1 : 1 ≤ e' * (N - D) := by
    have h1 : 1 * 1 ≤ e' * (N - D) := Nat.mul_le_mul he' (by omega)
    omega
  have hκK : ∀ t : Fin D, e' * (D - (t : ℕ)) + 1 ≤ e' * N := by
    intro t
    have h1 : e' * (D - (t : ℕ)) + e' ≤ e' * N := by
      rw [← Nat.mul_succ]
      refine Nat.mul_le_mul (le_refl e') ?_
      omega
    omega
  have hwin1 : ∀ t : Fin D,
      e' * (N - D) + (e' * (D - (t : ℕ)) + 1) ≤ e' * N + 1 := by
    intro t
    have h1 : e' * (N - D) + e' * (D - (t : ℕ)) = e' * ((N - D) + (D - (t : ℕ))) :=
      (Nat.mul_add e' _ _).symm
    have h2 : e' * ((N - D) + (D - (t : ℕ))) ≤ e' * N := by
      refine Nat.mul_le_mul (le_refl e') ?_
      have := t.isLt
      omega
    omega
  -- the two preimage sets and the inclusion via T1
  have hsub1 : (stratHom (D := D) α hPK) ⁻¹'
        (decidedSet R D σ' (e' * (N - D))
          ∩ levelZeroStratum R D (e' * (N - D)) (Polynomial.X ^ D))
      ⊆ (scaledHom α (e' * N) (fun t => e' * (D - (t : ℕ)) + 1)) ⁻¹'
          {b : Coeff R D (e' * N) |
            (∀ t : Fin D, e' * (D - (t : ℕ)) + 1 ≤ resOrd (b t))
              ∧ DecidedAt R D σ' (e' * N) b} := by
    intro u hu
    obtain ⟨hdec, -⟩ := hu
    refine Set.mem_preimage.mpr ⟨?_, ?_⟩
    · exact (mem_range_scaledHom hα _ hκK _).mp ⟨u, rfl⟩
    · exact decided_scaled_of_strat hα hPK u hwin1 hκK hdec
  -- the range inclusions
  have hSPrange : (decidedSet R D σ' (e' * (N - D))
        ∩ levelZeroStratum R D (e' * (N - D)) (Polynomial.X ^ D))
      ⊆ Set.range (stratHom (D := D) α hPK) := by
    rintro w ⟨-, hstr⟩
    exact (mem_range_stratHom hα hP1 hPK w).mpr
      ((mem_stratum_X_pow_iff hP1 w).mp hstr)
  have hBoxRange : {b : Coeff R D (e' * N) |
        (∀ t : Fin D, e' * (D - (t : ℕ)) + 1 ≤ resOrd (b t))
          ∧ DecidedAt R D σ' (e' * N) b}
      ⊆ Set.range (scaledHom α (e' * N) (fun t => e' * (D - (t : ℕ)) + 1)) := by
    rintro b ⟨hb, -⟩
    exact (mem_range_scaledHom hα _ hκK b).mpr hb
  -- the two exact counts
  have hc1 := card_preimage_of_subset_range (stratHom (D := D) α hPK) _ hSPrange
  have hc2 := card_preimage_of_subset_range
    (scaledHom α (e' * N) (fun t => e' * (D - (t : ℕ)) + 1)) _ hBoxRange
  rw [card_ker_stratHom hα hP1 hPK] at hc1
  rw [card_ker_scaledHom hα _ hκK] at hc2
  have hmono := Nat.card_mono (Set.toFinite _) hsub1
  rw [hc1, hc2] at hmono
  exact hmono

/-- ★★ **THE UPPER COUNT BOUND**: `q^(Σκ)·#(box ∩ dec) ≤ q^(D·(K−Q+1))·stratDecCount(Q)`
(`Q = e'(N−1)`): each decided box class owns its full fibre of decided stratum classes
at the high window. -/
private theorem card_boxDec_upper {α : R} (hα : Irreducible α) {e' D N : ℕ}
    (he' : 1 ≤ e') (hD1 : 1 ≤ D) (hDN : D < N) (σ' : FactorizationType) :
    residueCard R ^ (∑ t : Fin D, (e' * (D - (t : ℕ)) + 1))
        * Nat.card {b : Coeff R D (e' * N) |
            (∀ t : Fin D, e' * (D - (t : ℕ)) + 1 ≤ resOrd (b t))
              ∧ DecidedAt R D σ' (e' * N) b}
      ≤ residueCard R ^ (D * (e' * N - e' * (N - 1) + 1))
          * stratDecCount R D σ' (e' * (N - 1)) (Polynomial.X ^ D) := by
  classical
  have hQK : e' * (N - 1) ≤ e' * N := Nat.mul_le_mul (le_refl e') (by omega)
  have hQ1 : 1 ≤ e' * (N - 1) := by
    have h1 : 1 * 1 ≤ e' * (N - 1) := Nat.mul_le_mul he' (by omega)
    omega
  have hκK : ∀ t : Fin D, e' * (D - (t : ℕ)) + 1 ≤ e' * N := by
    intro t
    have h1 : e' * (D - (t : ℕ)) + e' ≤ e' * N := by
      rw [← Nat.mul_succ]
      refine Nat.mul_le_mul (le_refl e') ?_
      omega
    omega
  have hwin2 : ∀ t : Fin D,
      e' * N ≤ (e' * (D - (t : ℕ)) + 1) + (e' * (N - 1) - 1) := by
    intro t
    have ht := t.isLt
    have h1 : e' * (D - (t : ℕ)) + e' * (N - 1) = e' * ((D - (t : ℕ)) + (N - 1)) :=
      (Nat.mul_add e' _ _).symm
    have h2 : e' * N ≤ e' * ((D - (t : ℕ)) + (N - 1)) := by
      refine Nat.mul_le_mul (le_refl e') ?_
      omega
    omega
  -- the inclusion via T2
  have hsub2 : (scaledHom α (e' * N) (fun t => e' * (D - (t : ℕ)) + 1)) ⁻¹'
        {b : Coeff R D (e' * N) |
          (∀ t : Fin D, e' * (D - (t : ℕ)) + 1 ≤ resOrd (b t))
            ∧ DecidedAt R D σ' (e' * N) b}
      ⊆ (stratHom (D := D) α hQK) ⁻¹'
          (decidedSet R D σ' (e' * (N - 1))
            ∩ levelZeroStratum R D (e' * (N - 1)) (Polynomial.X ^ D)) := by
    intro u hu
    obtain ⟨-, hdec⟩ := hu
    refine Set.mem_preimage.mpr ⟨?_, ?_⟩
    · exact decided_strat_of_scaled hα hQK u hwin2 hQ1 hdec
    · refine (mem_stratum_X_pow_iff hQ1 _).mpr ?_
      exact (mem_range_stratHom hα hQ1 hQK _).mp ⟨u, rfl⟩
  -- the range inclusions
  have hSQrange : (decidedSet R D σ' (e' * (N - 1))
        ∩ levelZeroStratum R D (e' * (N - 1)) (Polynomial.X ^ D))
      ⊆ Set.range (stratHom (D := D) α hQK) := by
    rintro w ⟨-, hstr⟩
    exact (mem_range_stratHom hα hQ1 hQK w).mpr
      ((mem_stratum_X_pow_iff hQ1 w).mp hstr)
  have hBoxRange : {b : Coeff R D (e' * N) |
        (∀ t : Fin D, e' * (D - (t : ℕ)) + 1 ≤ resOrd (b t))
          ∧ DecidedAt R D σ' (e' * N) b}
      ⊆ Set.range (scaledHom α (e' * N) (fun t => e' * (D - (t : ℕ)) + 1)) := by
    rintro b ⟨hb, -⟩
    exact (mem_range_scaledHom hα _ hκK b).mpr hb
  have hc1 := card_preimage_of_subset_range (stratHom (D := D) α hQK) _ hSQrange
  have hc2 := card_preimage_of_subset_range
    (scaledHom α (e' * N) (fun t => e' * (D - (t : ℕ)) + 1)) _ hBoxRange
  rw [card_ker_stratHom hα hQ1 hQK] at hc1
  rw [card_ker_scaledHom hα _ hκK] at hc2
  have hmono := Nat.card_mono (Set.toFinite _) hsub2
  rw [hc1, hc2] at hmono
  exact hmono

/-- ★★★ **THE DEEP-BOX DECIDED LIMIT** (the squeeze): given the stratum-census limit
`V` at mass `D`, the normalized decided `α`-box count at levels `e'·(M+m)` converges to
`q^(−e'·T_D)·V`, `T_D = Σ_{t<D} (D−t)` — squeezed between the two count bounds at the
windows `P = e'(M+m−D)` and `Q = e'(M+m−1)`, both riding the SAME limit. -/
private theorem tendsto_boxDec {α : R} (hα : Irreducible α) {e' D : ℕ}
    (he' : 2 ≤ e') (hD1 : 1 ≤ D) {σ' : FactorizationType} {V : ℝ}
    (hV : Filter.Tendsto (fun L => (stratDecCount R D σ' L (Polynomial.X ^ D) : ℝ)
        / ((residueCard R : ℕ) : ℝ) ^ (D * L)) Filter.atTop (nhds V))
    (m : ℕ) (hm : m = e' * D) :
    Filter.Tendsto (fun M => (Nat.card {b : Coeff R D (e' * (M + m)) |
        (∀ t : Fin D, e' * (D - (t : ℕ)) + 1 ≤ resOrd (b t))
          ∧ DecidedAt R D σ' (e' * (M + m)) b} : ℝ)
        / ((residueCard R : ℕ) : ℝ) ^ (m * (M + m)))
      Filter.atTop
      (nhds ((((residueCard R : ℕ) : ℝ)
        ^ (e' * ∑ t ∈ Finset.range D, (D - t)))⁻¹ * V)) := by
  have hq0 : (0 : ℝ) < ((residueCard R : ℕ) : ℝ) := by
    exact_mod_cast residueCard_pos R
  have hqN : 0 < residueCard R := residueCard_pos R
  set T : ℕ := ∑ t ∈ Finset.range D, (D - t) with hT
  have hA : (∑ t : Fin D, (e' * (D - (t : ℕ)) + 1)) = e' * T + D := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one]
    congr 1
    rw [← Finset.mul_sum]
    congr 1
    exact Fin.sum_univ_eq_sum_range (fun t => D - t) D
  have hDm : D ≤ m := by
    rw [hm]
    have h1 : 1 * D ≤ e' * D := Nat.mul_le_mul (by omega) (le_refl D)
    omega
  have hm1 : 1 ≤ m := by omega
  -- the two squeeze arms, per M
  have hDN : ∀ M : ℕ, D < M + m := by
    intro M
    rw [hm]
    have h1 : 2 * D ≤ e' * D := Nat.mul_le_mul he' (le_refl D)
    omega
  -- the normalized box family, denominator in the D·(e'·N) form
  set F : ℕ → ℝ := fun M => (Nat.card {b : Coeff R D (e' * (M + m)) |
      (∀ t : Fin D, e' * (D - (t : ℕ)) + 1 ≤ resOrd (b t))
        ∧ DecidedAt R D σ' (e' * (M + m)) b} : ℝ)
      / ((residueCard R : ℕ) : ℝ) ^ (D * (e' * (M + m))) with hF
  have harm_lo : ∀ M : ℕ, (((residueCard R : ℕ) : ℝ) ^ (e' * T))⁻¹
      * ((stratDecCount R D σ' (e' * (M + m - D)) (Polynomial.X ^ D) : ℝ)
          / ((residueCard R : ℕ) : ℝ) ^ (D * (e' * (M + m - D)))) ≤ F M := by
    intro M
    have hnat := card_boxDec_lower (R := R) hα (by omega : 1 ≤ e') hD1 (hDN M) σ'
    rw [hA] at hnat
    -- exponent bookkeeping: K−P = e'D, D(K−P+1) + DP = DK + D
    have hKP : e' * (M + m) - e' * (M + m - D) = e' * D := by
      have h1 : e' * (M + m - D) + e' * D = e' * (M + m) := by
        rw [← Nat.mul_add]
        congr 1
        omega
      omega
    rw [hKP] at hnat
    -- fold to: q^(D·K + D) · SDC ≤ q^(e'T + D + D·P) · #Box
    have hstep : residueCard R ^ (D * (e' * (M + m)) + D)
        * stratDecCount R D σ' (e' * (M + m - D)) (Polynomial.X ^ D)
        ≤ residueCard R ^ (e' * T + D + D * (e' * (M + m - D)))
          * Nat.card {b : Coeff R D (e' * (M + m)) |
              (∀ t : Fin D, e' * (D - (t : ℕ)) + 1 ≤ resOrd (b t))
                ∧ DecidedAt R D σ' (e' * (M + m)) b} := by
      have hexp1 : D * (e' * (M + m)) + D
          = D * (e' * D + 1) + D * (e' * (M + m - D)) := by
        have h1 : e' * (M + m - D) + e' * D = e' * (M + m) := by
          rw [← Nat.mul_add]
          congr 1
          omega
        calc D * (e' * (M + m)) + D
            = D * (e' * (M + m - D) + e' * D) + D := by rw [h1]
          _ = D * (e' * D + 1) + D * (e' * (M + m - D)) := by ring
      calc residueCard R ^ (D * (e' * (M + m)) + D)
            * stratDecCount R D σ' (e' * (M + m - D)) (Polynomial.X ^ D)
          = residueCard R ^ (D * (e' * (M + m - D)))
            * (residueCard R ^ (D * (e' * D + 1))
              * stratDecCount R D σ' (e' * (M + m - D)) (Polynomial.X ^ D)) := by
            rw [hexp1, pow_add]
            ring
        _ ≤ residueCard R ^ (D * (e' * (M + m - D)))
            * (residueCard R ^ (e' * T + D)
              * Nat.card {b : Coeff R D (e' * (M + m)) |
                  (∀ t : Fin D, e' * (D - (t : ℕ)) + 1 ≤ resOrd (b t))
                    ∧ DecidedAt R D σ' (e' * (M + m)) b}) :=
            Nat.mul_le_mul_left _ hnat
        _ = residueCard R ^ (e' * T + D + D * (e' * (M + m - D)))
            * Nat.card {b : Coeff R D (e' * (M + m)) |
                (∀ t : Fin D, e' * (D - (t : ℕ)) + 1 ≤ resOrd (b t))
                  ∧ DecidedAt R D σ' (e' * (M + m)) b} := by
            rw [pow_add]
            ring
    -- cancel q^D
    have hfin : residueCard R ^ (D * (e' * (M + m)))
        * stratDecCount R D σ' (e' * (M + m - D)) (Polynomial.X ^ D)
        ≤ residueCard R ^ (e' * T + D * (e' * (M + m - D)))
          * Nat.card {b : Coeff R D (e' * (M + m)) |
              (∀ t : Fin D, e' * (D - (t : ℕ)) + 1 ≤ resOrd (b t))
                ∧ DecidedAt R D σ' (e' * (M + m)) b} := by
      refine Nat.le_of_mul_le_mul_left ?_ (pow_pos hqN D)
      calc residueCard R ^ D * (residueCard R ^ (D * (e' * (M + m)))
              * stratDecCount R D σ' (e' * (M + m - D)) (Polynomial.X ^ D))
          = residueCard R ^ (D * (e' * (M + m)) + D)
              * stratDecCount R D σ' (e' * (M + m - D)) (Polynomial.X ^ D) := by
            rw [pow_add]
            ring
        _ ≤ residueCard R ^ (e' * T + D + D * (e' * (M + m - D)))
              * Nat.card _ := hstep
        _ = residueCard R ^ D * (residueCard R ^ (e' * T + D * (e' * (M + m - D)))
              * Nat.card _) := by
            rw [pow_add, pow_add]
            ring
    -- to ℝ, divided form
    rw [hF]
    rw [inv_mul_eq_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hcast : (residueCard R ^ (D * (e' * (M + m)))
          * stratDecCount R D σ' (e' * (M + m - D)) (Polynomial.X ^ D) : ℝ)
        ≤ (residueCard R ^ (e' * T + D * (e' * (M + m - D)))
          * Nat.card {b : Coeff R D (e' * (M + m)) |
              (∀ t : Fin D, e' * (D - (t : ℕ)) + 1 ≤ resOrd (b t))
                ∧ DecidedAt R D σ' (e' * (M + m)) b} : ℝ) := by
      exact_mod_cast hfin
    rw [pow_add] at hcast
    calc (stratDecCount R D σ' (e' * (M + m - D)) (Polynomial.X ^ D) : ℝ)
          * ((residueCard R : ℕ) : ℝ) ^ (D * (e' * (M + m)))
        = ((residueCard R : ℕ) : ℝ) ^ (D * (e' * (M + m)))
          * (stratDecCount R D σ' (e' * (M + m - D)) (Polynomial.X ^ D) : ℝ) := by ring
      _ ≤ ((residueCard R : ℕ) : ℝ) ^ (e' * T)
          * ((residueCard R : ℕ) : ℝ) ^ (D * (e' * (M + m - D)))
          * (Nat.card {b : Coeff R D (e' * (M + m)) |
              (∀ t : Fin D, e' * (D - (t : ℕ)) + 1 ≤ resOrd (b t))
                ∧ DecidedAt R D σ' (e' * (M + m)) b} : ℝ) := hcast
      _ = (Nat.card {b : Coeff R D (e' * (M + m)) |
              (∀ t : Fin D, e' * (D - (t : ℕ)) + 1 ≤ resOrd (b t))
                ∧ DecidedAt R D σ' (e' * (M + m)) b} : ℝ)
          * (((residueCard R : ℕ) : ℝ) ^ (D * (e' * (M + m - D)))
            * ((residueCard R : ℕ) : ℝ) ^ (e' * T)) := by ring
  have harm_hi : ∀ M : ℕ, F M ≤ (((residueCard R : ℕ) : ℝ) ^ (e' * T))⁻¹
      * ((stratDecCount R D σ' (e' * (M + m - 1)) (Polynomial.X ^ D) : ℝ)
          / ((residueCard R : ℕ) : ℝ) ^ (D * (e' * (M + m - 1)))) := by
    intro M
    have hnat := card_boxDec_upper (R := R) hα (by omega : 1 ≤ e') hD1 (hDN M) σ'
    rw [hA] at hnat
    have hKQ : e' * (M + m) - e' * (M + m - 1) = e' := by
      have h1 : e' * (M + m - 1) + e' * 1 = e' * (M + m) := by
        rw [← Nat.mul_add]
        congr 1
        omega
      omega
    rw [hKQ] at hnat
    -- fold to: q^(e'T + D + D·Q) · #Box ≤ q^(D·K + D) · SDC(Q)
    have hstep : residueCard R ^ (e' * T + D + D * (e' * (M + m - 1)))
        * Nat.card {b : Coeff R D (e' * (M + m)) |
            (∀ t : Fin D, e' * (D - (t : ℕ)) + 1 ≤ resOrd (b t))
              ∧ DecidedAt R D σ' (e' * (M + m)) b}
        ≤ residueCard R ^ (D * (e' * (M + m)) + D)
          * stratDecCount R D σ' (e' * (M + m - 1)) (Polynomial.X ^ D) := by
      have hexp1 : D * (e' * (M + m)) + D
          = D * (e' + 1) + D * (e' * (M + m - 1)) := by
        have h1 : e' * (M + m - 1) + e' * 1 = e' * (M + m) := by
          rw [← Nat.mul_add]
          congr 1
          omega
        rw [Nat.mul_one] at h1
        calc D * (e' * (M + m)) + D
            = D * (e' * (M + m - 1) + e') + D := by rw [h1]
          _ = D * (e' + 1) + D * (e' * (M + m - 1)) := by ring
      calc residueCard R ^ (e' * T + D + D * (e' * (M + m - 1)))
            * Nat.card {b : Coeff R D (e' * (M + m)) |
                (∀ t : Fin D, e' * (D - (t : ℕ)) + 1 ≤ resOrd (b t))
                  ∧ DecidedAt R D σ' (e' * (M + m)) b}
          = residueCard R ^ (D * (e' * (M + m - 1)))
            * (residueCard R ^ (e' * T + D)
              * Nat.card {b : Coeff R D (e' * (M + m)) |
                  (∀ t : Fin D, e' * (D - (t : ℕ)) + 1 ≤ resOrd (b t))
                    ∧ DecidedAt R D σ' (e' * (M + m)) b}) := by
            rw [pow_add]
            ring
        _ ≤ residueCard R ^ (D * (e' * (M + m - 1)))
            * (residueCard R ^ (D * (e' + 1))
              * stratDecCount R D σ' (e' * (M + m - 1)) (Polynomial.X ^ D)) :=
            Nat.mul_le_mul_left _ hnat
        _ = residueCard R ^ (D * (e' * (M + m)) + D)
            * stratDecCount R D σ' (e' * (M + m - 1)) (Polynomial.X ^ D) := by
            rw [hexp1, pow_add]
            ring
    have hfin : residueCard R ^ (e' * T + D * (e' * (M + m - 1)))
        * Nat.card {b : Coeff R D (e' * (M + m)) |
            (∀ t : Fin D, e' * (D - (t : ℕ)) + 1 ≤ resOrd (b t))
              ∧ DecidedAt R D σ' (e' * (M + m)) b}
        ≤ residueCard R ^ (D * (e' * (M + m)))
          * stratDecCount R D σ' (e' * (M + m - 1)) (Polynomial.X ^ D) := by
      refine Nat.le_of_mul_le_mul_left ?_ (pow_pos hqN D)
      calc residueCard R ^ D * (residueCard R ^ (e' * T + D * (e' * (M + m - 1)))
              * Nat.card _)
          = residueCard R ^ (e' * T + D + D * (e' * (M + m - 1))) * Nat.card _ := by
            rw [pow_add, pow_add]
            ring
        _ ≤ residueCard R ^ (D * (e' * (M + m)) + D)
              * stratDecCount R D σ' (e' * (M + m - 1)) (Polynomial.X ^ D) := hstep
        _ = residueCard R ^ D * (residueCard R ^ (D * (e' * (M + m)))
              * stratDecCount R D σ' (e' * (M + m - 1)) (Polynomial.X ^ D)) := by
            rw [pow_add]
            ring
    rw [hF]
    rw [inv_mul_eq_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hcast : ((residueCard R ^ (e' * T + D * (e' * (M + m - 1)))
          * Nat.card {b : Coeff R D (e' * (M + m)) |
              (∀ t : Fin D, e' * (D - (t : ℕ)) + 1 ≤ resOrd (b t))
                ∧ DecidedAt R D σ' (e' * (M + m)) b} : ℕ) : ℝ)
        ≤ ((residueCard R ^ (D * (e' * (M + m)))
          * stratDecCount R D σ' (e' * (M + m - 1)) (Polynomial.X ^ D) : ℕ) : ℝ) := by
      exact_mod_cast hfin
    push_cast at hcast
    rw [pow_add] at hcast
    calc (Nat.card {b : Coeff R D (e' * (M + m)) |
            (∀ t : Fin D, e' * (D - (t : ℕ)) + 1 ≤ resOrd (b t))
              ∧ DecidedAt R D σ' (e' * (M + m)) b} : ℝ)
          * (((residueCard R : ℕ) : ℝ) ^ (D * (e' * (M + m - 1)))
            * ((residueCard R : ℕ) : ℝ) ^ (e' * T))
        = ((residueCard R : ℕ) : ℝ) ^ (e' * T)
          * ((residueCard R : ℕ) : ℝ) ^ (D * (e' * (M + m - 1)))
          * (Nat.card {b : Coeff R D (e' * (M + m)) |
              (∀ t : Fin D, e' * (D - (t : ℕ)) + 1 ≤ resOrd (b t))
                ∧ DecidedAt R D σ' (e' * (M + m)) b} : ℝ) := by ring
      _ ≤ ((residueCard R : ℕ) : ℝ) ^ (D * (e' * (M + m)))
          * (stratDecCount R D σ' (e' * (M + m - 1)) (Polynomial.X ^ D) : ℝ) := hcast
      _ = (stratDecCount R D σ' (e' * (M + m - 1)) (Polynomial.X ^ D) : ℝ)
          * ((residueCard R : ℕ) : ℝ) ^ (D * (e' * (M + m))) := by ring
  -- the two arms converge to q^(−e'T)·V
  have hφlo : Filter.Tendsto (fun M => e' * (M + m - D)) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono (fun M => ?_) Filter.tendsto_id
    show M ≤ e' * (M + m - D)
    have h1 : 1 * M ≤ e' * (M + m - D) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hφhi : Filter.Tendsto (fun M => e' * (M + m - 1)) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono (fun M => ?_) Filter.tendsto_id
    show M ≤ e' * (M + m - 1)
    have h1 : 1 * M ≤ e' * (M + m - 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hlim_lo : Filter.Tendsto (fun M => (((residueCard R : ℕ) : ℝ) ^ (e' * T))⁻¹
      * ((stratDecCount R D σ' (e' * (M + m - D)) (Polynomial.X ^ D) : ℝ)
          / ((residueCard R : ℕ) : ℝ) ^ (D * (e' * (M + m - D)))))
      Filter.atTop (nhds ((((residueCard R : ℕ) : ℝ) ^ (e' * T))⁻¹ * V)) :=
    (hV.comp hφlo).const_mul _
  have hlim_hi : Filter.Tendsto (fun M => (((residueCard R : ℕ) : ℝ) ^ (e' * T))⁻¹
      * ((stratDecCount R D σ' (e' * (M + m - 1)) (Polynomial.X ^ D) : ℝ)
          / ((residueCard R : ℕ) : ℝ) ^ (D * (e' * (M + m - 1)))))
      Filter.atTop (nhds ((((residueCard R : ℕ) : ℝ) ^ (e' * T))⁻¹ * V)) :=
    (hV.comp hφhi).const_mul _
  have hFlim : Filter.Tendsto F Filter.atTop
      (nhds ((((residueCard R : ℕ) : ℝ) ^ (e' * T))⁻¹ * V)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlim_lo hlim_hi harm_lo harm_hi
  refine hFlim.congr fun M => ?_
  rw [hF]
  rw [hm]
  ring

end Squeeze

/-! ## §4 — the face/centre partition of the full-span power sector at the Eisenstein
frame, and the per-cell transport -/

section Cells

/-- Exact disjoint-union count over a finite index set. -/
private theorem ncard_biUnion_eq {α ι : Type*} [Finite α] (s : Finset ι)
    (f : ι → Set α)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (f i) (f j)) :
    (⋃ i ∈ s, f i).ncard = ∑ i ∈ s, (f i).ncard := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      have hcons : (⋃ i ∈ Finset.cons a s ha, f i) = f a ∪ ⋃ i ∈ s, f i := by
        rw [Finset.cons_eq_insert, Finset.set_biUnion_insert]
      rw [hcons, Finset.sum_cons]
      have hd : Disjoint (f a) (⋃ i ∈ s, f i) := by
        rw [Set.disjoint_iUnion_right]
        intro i
        rw [Set.disjoint_iUnion_right]
        intro hi
        exact hdisj a (Finset.mem_cons_self a s) i
          (Finset.mem_cons_of_mem hi) (by rintro rfl; exact ha hi)
      rw [Set.ncard_union_eq hd (Set.toFinite _) (Set.toFinite _)]
      congr 1
      exact ih fun i hi j hj hij =>
        hdisj i (Finset.mem_cons_of_mem hi) j (Finset.mem_cons_of_mem hj) hij

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- **The σ-decided Eisenstein full-span cell** at face `(1, e')`, residual centre `ζ`:
minimal face `(1, e')`, residual the `D`-th power of `X − ζ`, decided at `σ`. -/
def eisCellDec (π : O) (m e' D N : ℕ) (ζ : resField (X : Polynomial O))
    (σ : FactorizationType) : Set (Coeff O m N) :=
  {c | MinFaceAt c 1 e'
    ∧ classResidualPoly π c 1 e' = (Polynomial.X - Polynomial.C ζ) ^ D
    ∧ DecidedAt O m σ N c}

/-- The residual centre is pinned by the cell (distinct centres give disjoint cells). -/
private theorem residual_pow_inj {ζ ζ' : resField (X : Polynomial O)} {D : ℕ}
    (hD : 1 ≤ D)
    (h : (Polynomial.X - Polynomial.C ζ) ^ D = (Polynomial.X - Polynomial.C ζ') ^ D) :
    ζ = ζ' := by
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  have h1 := congrArg (Polynomial.eval ζ) h
  rw [Polynomial.eval_pow, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_C, sub_self,
    zero_pow (by omega : D ≠ 0)] at h1
  have h2 : ζ - ζ' = 0 := pow_eq_zero_iff (by omega : D ≠ 0) |>.mp h1.symm
  have h3 : ζ - ζ' + ζ' = 0 + ζ' := by rw [h2]
  rwa [sub_add_cancel, zero_add] at h3

/-- A proper power of a monic linear is never irreducible. -/
private theorem not_irreducible_linear_pow {ζ : resField (X : Polynomial O)} {D : ℕ}
    (hD : 2 ≤ D) :
    ¬ Irreducible ((Polynomial.X - Polynomial.C ζ) ^ D) := by
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  intro hirr
  have hsplit : (Polynomial.X - Polynomial.C ζ) ^ D
      = (Polynomial.X - Polynomial.C ζ) * (Polynomial.X - Polynomial.C ζ) ^ (D - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rcases hirr.isUnit_or_isUnit hsplit with hu | hu
  · have hdeg := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [Polynomial.natDegree_X_sub_C] at hdeg
    omega
  · have hdeg := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, Nat.mul_one] at hdeg
    omega

/-- ★ **The cell sits in the full-span power sector**: a decided Eisenstein cell member
satisfies EVERY `powerSectorFull` clause — decided, stratum, shallow, outside every
pure-face box (face uniqueness), proper-power residual, full span. -/
theorem eisCellDec_subset_psf {π : O} (hπ : Irreducible π) {m e' D : ℕ}
    (hm : m = e' * D) (he' : 2 ≤ e') (hD : 2 ≤ D)
    {ζ : resField (X : Polynomial O)} (σ : FactorizationType) (M : ℕ) :
    eisCellDec π m e' D (M + m) ζ σ ⊆ powerSectorFull O π m σ M := by
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  rintro c ⟨hF, hres, hdec⟩
  have hm0 : 0 < m := by
    rw [hm]
    positivity
  have hmK : m ≤ M + m := by omega
  have hdegres : (classResidualPoly π c 1 e').natDegree = D := by
    rw [hres, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, Nat.mul_one]
  have hfull : e' * (classResidualPoly π c 1 e').natDegree = m := by
    rw [hdegres, hm]
  -- the exact corner (for the shallow clause)
  have hcorner := fullSpan_corner hπ hF hfull hmK hm0
  rw [hdegres, Nat.one_mul] at hcorner
  -- stratum
  have hstrat : c ∈ levelZeroStratum O m (M + m) (Polynomial.X ^ m) := by
    refine (mem_stratum_X_pow_iff (by omega) c).mpr fun i => ?_
    have h1 := minFaceAt_min hF i
    rw [Nat.one_mul] at h1
    have h2 := i.isLt
    generalize hA : e' * resOrd (c i) = A at h1
    rcases Nat.eq_zero_or_pos (resOrd (c i)) with h0 | h3
    · rw [h0, Nat.mul_zero] at hA
      omega
    · exact h3
  -- shallow
  have hsh : c ∈ shallowSet O m (M + m) := by
    refine ⟨⟨0, hm0⟩, ?_⟩
    have hDlt : D < m := by
      rw [hm]
      have h1 : 2 * D ≤ e' * D := Nat.mul_le_mul he' (le_refl D)
      omega
    show resOrd (c ⟨0, hm0⟩) < m - ((⟨0, hm0⟩ : Fin m) : ℕ)
    rw [hcorner]
    show D < m - 0
    omega
  -- outside every pure-face box
  have hpf : c ∉ pureFaceSet O m (M + m) := by
    rintro ⟨h, hhmem, hbox⟩
    obtain ⟨hcorner', hlat'⟩ := hbox
    have hmemfilter := hhmem
    rw [Uniformity.Density.IFCG24.faceH, Finset.mem_filter, Finset.mem_range] at hmemfilter
    obtain ⟨hhm, hh1, hcop⟩ := hmemfilter
    -- reconstruct the (h, m) face and contradict uniqueness
    have hlat'' : ∀ j : Fin m, h * (m - (j : ℕ)) ≤ m * resOrd (c j) := by
      intro j
      have h1 := hlat' j
      rwa [npHeight_coe] at h1
    have hcorner'' : resOrd (c ⟨0, hm0⟩) = h * 1 := by
      have h2 : npHeight c 0 = resOrd (c ⟨0, hm0⟩) := by
        simpa using npHeight_coe c ⟨0, hm0⟩
      rw [← h2, hcorner', Nat.mul_one]
    have hFm : MinFaceAt c h m :=
      minFaceAt_of_lattice hh1 hhm hcop (Nat.mul_one m) hmK hm0 hlat'' hcorner''
    obtain ⟨-, hem⟩ := minFaceAt_unique hF hFm
    have hDlt : e' < m := by
      rw [hm]
      have h1 : e' * 2 ≤ e' * D := Nat.mul_le_mul (le_refl e') hD
      omega
    omega
  -- assemble
  refine ⟨⟨⟨⟨⟨hdec, hstrat⟩, hsh⟩, hpf⟩, 1, e', hF, ?_, ?_⟩, 1, e', hF, hfull⟩
  · rw [hres]
    exact not_irreducible_linear_pow hD
  · exact ⟨Polynomial.X - Polynomial.C ζ, D, Polynomial.irreducible_X_sub_C ζ, hD,
      by rw [hres]⟩

end Cells

section CellCount

-- the universe fence: `transport_decidedAt_iff` and `CellTypeScalingAt` quantify
-- `O : Type`, so the transport consumers live here.
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]
variable {π z : O} {e' D : ℕ}
variable [IsDomain (AdjoinRoot (eisKey π (-z) e'))]
  [IsDiscreteValuationRing (AdjoinRoot (eisKey π (-z) e'))]
  [Finite (ResidueField (AdjoinRoot (eisKey π (-z) e')))]

/-- ★★ **THE PER-CELL IMAGE CHARACTERIZATION**: at `σ = scaleType e' σ'`, the cell
transport carries the decided Eisenstein cell EXACTLY onto `alphaBox ∩ decidedSet`
over the recentring ring — forward by the landed reading + outbound transport,
backward by W2's reconstruction + inbound transport. -/
theorem cellTransport_image_eisCellDec (hπ : Irreducible π)
    (hz : IsLocalRing.residue O z ≠ 0) (hw : IsLocalRing.residue O (-z) ≠ 0)
    (he' : 2 ≤ e') (hD : 1 ≤ D) {N : ℕ} (hDN : D < N) (hmN : e' * D ≤ N)
    (hCTS : CellTypeScalingAt D) (σ' : FactorizationType) :
    (cellTransport hπ hw he' D N) ''
        (eisCellDec π (e' * D) e' D N (resFieldXEquiv O (IsLocalRing.residue O z))
          (scaleType e' σ'))
      = alphaBox π (-z) e' D (e' * N)
        ∩ decidedSet (AdjoinRoot (eisKey π (-z) e')) D σ' (e' * N) := by
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  ext b
  constructor
  · rintro ⟨c, ⟨hF, hres, hdec⟩, rfl⟩
    obtain ⟨a, ha⟩ := proj_surjective O (e' * D) N c
    have hdegres : (classResidualPoly π c 1 e').natDegree = D := by
      rw [hres, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, Nat.mul_one]
    have hdevdvd := (fullSpan_resPoly_iff_box hπ hz he' hF hdegres rfl ha).mp hres
    have hbox : cellTransport hπ hw he' D N c ∈ alphaBox π (-z) e' D (e' * N) := by
      rw [← ha]
      exact (cellTransport_mem_alphaBox_iff hπ hw he' hDN a).mpr hdevdvd
    exact ⟨hbox, (transport_decidedAt_iff hCTS hπ hw he' hDN hF hbox σ').mpr hdec⟩
  · rintro ⟨hbox, hdec⟩
    refine ⟨(cellTransport hπ hw he' D N).symm b, ?_, Equiv.apply_symm_apply _ b⟩
    have hbox' : cellTransport hπ hw he' D N ((cellTransport hπ hw he' D N).symm b)
        ∈ alphaBox π (-z) e' D (e' * N) := by
      rw [Equiv.apply_symm_apply]
      exact hbox
    obtain ⟨hF, hdeg, hres⟩ := cell_of_box hπ hz hw he' (by omega) hDN hmN hbox'
    refine ⟨hF, hres, ?_⟩
    have hdec' : DecidedAt (AdjoinRoot (eisKey π (-z) e')) D σ' (e' * N)
        (cellTransport hπ hw he' D N ((cellTransport hπ hw he' D N).symm b)) := by
      rw [Equiv.apply_symm_apply]
      exact hdec
    exact (transport_decidedAt_iff hCTS hπ hw he' hDN hF hbox' σ').mp hdec'

/-- ★★ **THE PER-CELL COUNT**: the decided cell count equals the decided `α`-box
count over the recentring ring. -/
theorem card_eisCellDec (hπ : Irreducible π)
    (hz : IsLocalRing.residue O z ≠ 0) (hw : IsLocalRing.residue O (-z) ≠ 0)
    (he' : 2 ≤ e') (hD : 1 ≤ D) {N : ℕ} (hDN : D < N) (hmN : e' * D ≤ N)
    (hCTS : CellTypeScalingAt D) (σ' : FactorizationType) :
    Nat.card (eisCellDec π (e' * D) e' D N
        (resFieldXEquiv O (IsLocalRing.residue O z)) (scaleType e' σ'))
      = Nat.card (alphaBox π (-z) e' D (e' * N)
          ∩ decidedSet (AdjoinRoot (eisKey π (-z) e')) D σ' (e' * N)
          : Set (Coeff (AdjoinRoot (eisKey π (-z) e')) D (e' * N))) := by
  calc Nat.card (eisCellDec π (e' * D) e' D N
          (resFieldXEquiv O (IsLocalRing.residue O z)) (scaleType e' σ'))
      = Nat.card ((cellTransport hπ hw he' D N) ''
          (eisCellDec π (e' * D) e' D N
            (resFieldXEquiv O (IsLocalRing.residue O z)) (scaleType e' σ'))) :=
        (cellTransport_card_image hπ hw he' D N _).symm
    _ = _ := by
        rw [cellTransport_image_eisCellDec hπ hz hw he' hD hDN hmN hCTS σ']

/-- ★ **The off-range emptiness**: at a type outside `scaleType e'`'s range the decided
Eisenstein cell is EMPTY — the pointwise law types every lift inside the range. -/
theorem eisCellDec_eq_empty_of_not_range (hπ : Irreducible π)
    (hz : IsLocalRing.residue O z ≠ 0) (hw : IsLocalRing.residue O (-z) ≠ 0)
    (he' : 2 ≤ e') {N : ℕ}
    (hCTS : CellTypeScalingAt D) {σ : FactorizationType}
    (hσ : σ ∉ Set.range (scaleType e')) :
    eisCellDec π (e' * D) e' D N (resFieldXEquiv O (IsLocalRing.residue O z)) σ
      = ∅ := by
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  ext c
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hF, hres, hdec⟩
  obtain ⟨a, ha⟩ := proj_surjective O (e' * D) N c
  have hdegres : (classResidualPoly π c 1 e').natDegree = D := by
    rw [hres, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, Nat.mul_one]
  have hdevdvd := (fullSpan_resPoly_iff_box hπ hz he' hF hdegres rfl ha).mp hres
  have hlat := fullSpan_raw_dvd hπ hF ha
  have hscale := hCTS O π (-z) hπ hw e' he' (monicPoly a) (monicPoly_monic a)
    (monicPoly_natDegree a)
    (fun j hj => by
      have h1 := hlat j hj
      rwa [one_mul] at h1) hdevdvd
  refine hσ ⟨typeOf (devT (eisKey π (-z) e') D (monicPoly a)), ?_⟩
  rw [← hscale]
  exact hdec a ha

end CellCount

section CellLimit

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- ★★★ **THE PER-CELL LIMIT**: with the mass-`D` stratum-limit pair `(n, d)` supplied
(from `tendsto_stratDec_of_laws`) and the pointwise scaling law at `D`, the normalized
decided-cell count at centre `z` converges to `q^(−e'·T_D)·(n(q)/d(q))` — instantiated
through the recentring stack at `q' = q`. -/
theorem tendsto_eisCellDec {π z : O} (hπ : Irreducible π)
    (hz : IsLocalRing.residue O z ≠ 0) (hw : IsLocalRing.residue O (-z) ≠ 0)
    {e' D : ℕ} (he' : 2 ≤ e') (hD : 1 ≤ D) {m : ℕ} (hm : m = e' * D)
    (hCTS : CellTypeScalingAt D) (σ' : FactorizationType) {n d : Polynomial ℚ}
    (hval : ∀ (O₁ : Type) [CommRing O₁] [IsDomain O₁] [IsDiscreteValuationRing O₁]
        [IsAdicComplete (maximalIdeal O₁) O₁] [Finite (ResidueField O₁)],
        d.eval ((residueCard O₁ : ℕ) : ℚ) ≠ 0 ∧
          Filter.Tendsto (fun L => (stratDecCount O₁ D σ' L (Polynomial.X ^ D) : ℝ)
              / ((residueCard O₁ : ℕ) : ℝ) ^ (D * L)) Filter.atTop
            (nhds (((n.eval ((residueCard O₁ : ℕ) : ℚ)
              / d.eval ((residueCard O₁ : ℕ) : ℚ) : ℚ) : ℝ)))) :
    Filter.Tendsto (fun M =>
        (Nat.card (eisCellDec π m e' D (M + m)
            (resFieldXEquiv O (IsLocalRing.residue O z)) (scaleType e' σ')) : ℝ)
          / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)))
      Filter.atTop
      (nhds ((((residueCard O : ℕ) : ℝ)
          ^ (e' * ∑ t ∈ Finset.range D, (D - t)))⁻¹
        * ((n.eval ((residueCard O : ℕ) : ℚ)
            / d.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ))) := by
  subst hm
  obtain ⟨i1, i2, i3, i4, hpack⟩ := eis_recentring_stack π (-z) hπ hw he'
  obtain ⟨iAC, hcard⟩ := hpack
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  letI := iAC
  have hα : Irreducible (AdjoinRoot.root (eisKey π (-z) e')) :=
    eis_root_irreducible hπ hw he'
  have hV' := (hval (AdjoinRoot (eisKey π (-z) e'))).2
  have hbox := tendsto_boxDec hα he' hD hV' (e' * D) rfl
  rw [hcard] at hbox
  refine hbox.congr fun M => ?_
  have hDN : D < M + e' * D := by
    have h1 : 2 * D ≤ e' * D := Nat.mul_le_mul he' (le_refl D)
    omega
  have hmN : e' * D ≤ M + e' * D := by omega
  congr 2
  rw [card_eisCellDec hπ hz hw he' hD hDN hmN hCTS σ']
  rfl

end CellLimit

section Faces

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- **The σ-decided Eisenstein face carrier** at `(1, e')` with residual a `D`-th power
of a NONZERO-centred monic linear — the union of the cells over the centres. -/
def eisFace (π : O) (m e' D N : ℕ) (σ : FactorizationType) : Set (Coeff O m N) :=
  {c | MinFaceAt c 1 e'
    ∧ (∃ ζ : resField (X : Polynomial O), ζ ≠ 0
        ∧ classResidualPoly π c 1 e' = (Polynomial.X - Polynomial.C ζ) ^ D)
    ∧ DecidedAt O m σ N c}

/-- The face carrier counts as the centre sum of the cells. -/
theorem card_eisFace_eq_sum (π : O) {m e' D N : ℕ} (hD : 1 ≤ D)
    (σ : FactorizationType) [Fintype (ResidueField O)] :
    Nat.card (eisFace π m e' D N σ)
      = ∑ y ∈ Finset.univ.filter (fun y : ResidueField O => y ≠ 0),
          Nat.card (eisCellDec π m e' D N (resFieldXEquiv O y) σ) := by
  classical
  have hunion : eisFace π m e' D N σ
      = ⋃ y ∈ Finset.univ.filter (fun y : ResidueField O => y ≠ 0),
          eisCellDec π m e' D N (resFieldXEquiv O y) σ := by
    ext c
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨hF, ⟨ζ, hζ, hres⟩, hdec⟩
      refine ⟨(resFieldXEquiv O).symm ζ,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hF, ?_, hdec⟩
      · intro h0
        apply hζ
        have h1 : resFieldXEquiv O ((resFieldXEquiv O).symm ζ) = ζ :=
          (resFieldXEquiv O).apply_symm_apply ζ
        rw [← h1, h0, map_zero]
      · rw [(resFieldXEquiv O).apply_symm_apply ζ]
        exact hres
    · rintro ⟨y, hy, hF, hres, hdec⟩
      have hy0 : y ≠ 0 := (Finset.mem_filter.mp hy).2
      refine ⟨hF, ⟨resFieldXEquiv O y, ?_, hres⟩, hdec⟩
      intro h0
      apply hy0
      refine (resFieldXEquiv O).injective ?_
      rw [map_zero]
      exact h0
  have hdisj : ∀ y ∈ Finset.univ.filter (fun y : ResidueField O => y ≠ 0),
      ∀ y' ∈ Finset.univ.filter (fun y : ResidueField O => y ≠ 0), y ≠ y' →
        Disjoint (eisCellDec π m e' D N (resFieldXEquiv O y) σ)
          (eisCellDec π m e' D N (resFieldXEquiv O y') σ) := by
    intro y _ y' _ hne
    rw [Set.disjoint_left]
    rintro c ⟨-, hres, -⟩ ⟨-, hres', -⟩
    exact hne ((resFieldXEquiv O).injective
      (residual_pow_inj hD (hres.symm.trans hres')))
  rw [hunion, Nat.card_coe_set_eq, ncard_biUnion_eq _ _ hdisj]
  exact Finset.sum_congr rfl fun y _ => (Nat.card_coe_set_eq _).symm

/-- Each admissible face carrier sits inside the full-span power sector. -/
theorem eisFace_subset_psf {π : O} (hπ : Irreducible π) {m e' D : ℕ}
    (hm : m = e' * D) (he' : 2 ≤ e') (hD : 2 ≤ D) (σ : FactorizationType) (M : ℕ) :
    eisFace π m e' D (M + m) σ ⊆ powerSectorFull O π m σ M := by
  rintro c ⟨hF, ⟨ζ, hζ, hres⟩, hdec⟩
  exact eisCellDec_subset_psf hπ hm he' hD σ M ⟨hF, hres, hdec⟩

/-- Distinct faces are disjoint (uniqueness of the minimal face). -/
theorem eisFace_disjoint (π : O) {m N : ℕ} {e₁ e₂ D₁ D₂ : ℕ} (hne : e₁ ≠ e₂)
    (σ : FactorizationType) :
    Disjoint (eisFace π m e₁ D₁ N σ) (eisFace π m e₂ D₂ N σ) := by
  rw [Set.disjoint_left]
  rintro c ⟨hF₁, -, -⟩ ⟨hF₂, -, -⟩
  obtain ⟨-, he⟩ := minFaceAt_unique hF₁ hF₂
  exact hne he

/-- ★ **THE PARTITION COUNT**: the full-span count is the divisor-face sum plus the
non-Eisenstein remainder count, exactly, at every level. -/
theorem card_psf_partition {π : O} (hπ : Irreducible π) (m : ℕ)
    (σ : FactorizationType) (M : ℕ) :
    Nat.card (powerSectorFull O π m σ M)
      = (∑ e' ∈ (m.divisors.filter fun e' => 2 ≤ e' ∧ 2 ≤ m / e'),
          Nat.card (eisFace π m e' (m / e') (M + m) σ))
        + Nat.card ((powerSectorFull O π m σ M
            \ ⋃ e' ∈ (m.divisors.filter fun e' => 2 ≤ e' ∧ 2 ≤ m / e'),
                eisFace π m e' (m / e') (M + m) σ) : Set (Coeff O m (M + m))) := by
  classical
  have hsub : (⋃ e' ∈ (m.divisors.filter fun e' => 2 ≤ e' ∧ 2 ≤ m / e'),
      eisFace (O := O) π m e' (m / e') (M + m) σ) ⊆ powerSectorFull O π m σ M := by
    refine Set.iUnion₂_subset fun e' he' => ?_
    rw [Finset.mem_filter, Nat.mem_divisors] at he'
    obtain ⟨⟨hdvd, hm0⟩, h2e, h2D⟩ := he'
    exact eisFace_subset_psf hπ (Nat.mul_div_cancel' hdvd).symm h2e h2D σ M
  have hsplit := (Set.ncard_inter_add_ncard_sdiff_eq_ncard
    (powerSectorFull O π m σ M)
    (⋃ e' ∈ (m.divisors.filter fun e' => 2 ≤ e' ∧ 2 ≤ m / e'),
      eisFace (O := O) π m e' (m / e') (M + m) σ) (Set.toFinite _)).symm
  have hinter : powerSectorFull O π m σ M
      ∩ (⋃ e' ∈ (m.divisors.filter fun e' => 2 ≤ e' ∧ 2 ≤ m / e'),
          eisFace (O := O) π m e' (m / e') (M + m) σ)
      = ⋃ e' ∈ (m.divisors.filter fun e' => 2 ≤ e' ∧ 2 ≤ m / e'),
          eisFace (O := O) π m e' (m / e') (M + m) σ :=
    Set.inter_eq_self_of_subset_right hsub
  rw [hinter] at hsplit
  have hUcard : (⋃ e' ∈ (m.divisors.filter fun e' => 2 ≤ e' ∧ 2 ≤ m / e'),
      eisFace (O := O) π m e' (m / e') (M + m) σ).ncard
      = ∑ e' ∈ (m.divisors.filter fun e' => 2 ≤ e' ∧ 2 ≤ m / e'),
          (eisFace (O := O) π m e' (m / e') (M + m) σ).ncard :=
    ncard_biUnion_eq _ _ fun i _ j _ hij => eisFace_disjoint π hij σ
  rw [Nat.card_coe_set_eq, hsplit, hUcard]
  congr 1

end Faces

section FaceLimit

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- ★★★ **THE PER-FACE LIMIT**: the normalized face-carrier count converges to
`(q − 1) · q^(−e'·T_D) · (n(q)/d(q))` — the centre sum of the per-cell limits. -/
theorem tendsto_eisFace {π : O} (hπ : Irreducible π)
    {e' D m : ℕ} (he' : 2 ≤ e') (hD : 1 ≤ D) (hm : m = e' * D)
    (hCTS : CellTypeScalingAt D) (σ' : FactorizationType) {n d : Polynomial ℚ}
    (hval : ∀ (O₁ : Type) [CommRing O₁] [IsDomain O₁] [IsDiscreteValuationRing O₁]
        [IsAdicComplete (maximalIdeal O₁) O₁] [Finite (ResidueField O₁)],
        d.eval ((residueCard O₁ : ℕ) : ℚ) ≠ 0 ∧
          Filter.Tendsto (fun L => (stratDecCount O₁ D σ' L (Polynomial.X ^ D) : ℝ)
              / ((residueCard O₁ : ℕ) : ℝ) ^ (D * L)) Filter.atTop
            (nhds (((n.eval ((residueCard O₁ : ℕ) : ℚ)
              / d.eval ((residueCard O₁ : ℕ) : ℚ) : ℚ) : ℝ)))) :
    Filter.Tendsto (fun M =>
        (Nat.card (eisFace π m e' D (M + m) (scaleType e' σ')) : ℝ)
          / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)))
      Filter.atTop
      (nhds ((((residueCard O : ℕ) : ℝ) - 1)
        * ((((residueCard O : ℕ) : ℝ) ^ (e' * ∑ t ∈ Finset.range D, (D - t)))⁻¹
          * ((n.eval ((residueCard O : ℕ) : ℚ)
              / d.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)))) := by
  classical
  haveI : Fintype (ResidueField O) := Fintype.ofFinite _
  have hcount : ∀ M, (Nat.card (eisFace π m e' D (M + m) (scaleType e' σ')) : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
      = ∑ y ∈ Finset.univ.filter (fun y : ResidueField O => y ≠ 0),
          (Nat.card (eisCellDec π m e' D (M + m) (resFieldXEquiv O y)
              (scaleType e' σ')) : ℝ)
            / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)) := by
    intro M
    rw [card_eisFace_eq_sum π hD (scaleType e' σ')]
    push_cast
    rw [Finset.sum_div]
  have hlim : ∀ y ∈ Finset.univ.filter (fun y : ResidueField O => y ≠ 0),
      Filter.Tendsto (fun M =>
        (Nat.card (eisCellDec π m e' D (M + m) (resFieldXEquiv O y)
            (scaleType e' σ')) : ℝ)
          / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))) Filter.atTop
        (nhds ((((residueCard O : ℕ) : ℝ)
            ^ (e' * ∑ t ∈ Finset.range D, (D - t)))⁻¹
          * ((n.eval ((residueCard O : ℕ) : ℚ)
              / d.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ))) := by
    intro y hy
    have hy0 : y ≠ 0 := (Finset.mem_filter.mp hy).2
    have hzres : IsLocalRing.residue O (resSect O y) = y := residue_resSect O y
    have hz0 : IsLocalRing.residue O (resSect O y) ≠ 0 := by
      rw [hzres]
      exact hy0
    have hw0 : IsLocalRing.residue O (-(resSect O y)) ≠ 0 := by
      rw [map_neg, hzres]
      exact neg_ne_zero.mpr hy0
    have h1 := tendsto_eisCellDec hπ hz0 hw0 he' hD hm hCTS σ' hval
    rw [hzres] at h1
    exact h1
  have hsum := tendsto_finsetSum
    (Finset.univ.filter (fun y : ResidueField O => y ≠ 0)) hlim
  have hcardf : (Finset.univ.filter (fun y : ResidueField O => y ≠ 0)).card
      = residueCard O - 1 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ 0),
      Finset.card_univ]
    congr 1
    rw [residueCard, Nat.card_eq_fintype_card]
  rw [Finset.sum_const, hcardf, nsmul_eq_mul] at hsum
  have hq2 : 2 ≤ residueCard O := two_le_residueCard O
  have hcast : ((residueCard O - 1 : ℕ) : ℝ) = ((residueCard O : ℕ) : ℝ) - 1 := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ residueCard O)]
    ring
  rw [hcast] at hsum
  exact hsum.congr fun M => (hcount M).symm

end FaceLimit

/-! ## §5 — the named remainder, the conditional composite-mass fire, the wrapper -/

section Fire

/-- ★ **THE NAMED REMAINDER — `EisFullSpanRemainderLaw m σ`**: the uniform rational
limit of the NON-Eisenstein-frame part of the full-span sector (the `h ≥ 2` faces and
the `deg ψ ≥ 2` residual root fields).  PSL4 §5 records the `(h ≥ 2)` ring-side
transport and the `d ≥ 2` compositum lattice as this territory's exact open
instruments; this Prop is their consumption point.  At `m = 4` it is PROVED below
(the carrier is empty). -/
def EisFullSpanRemainderLaw (m : ℕ) (σ : FactorizationType) : Prop :=
  ZcURLim (fun O _ _ _ _ _ π M =>
    (Nat.card ((powerSectorFull O π m σ M
        \ ⋃ e' ∈ (m.divisors.filter fun e' => 2 ≤ e' ∧ 2 ≤ m / e'),
            eisFace π m e' (m / e') (M + m) σ) : Set (Coeff O m (M + m))) : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)))

/-- ★★ **THE PER-FACE LAW**: at a divisor face `(e', D)`, the normalized face-carrier
family is a `ZcURLim` — conditional on `FactorCorrespondenceAt D` and the mass-`D`
decided-value and zero-cone laws.  Value: `(q−1)·q^(−e'T_D)·(n_{σ'}/d_{σ'})(q)` at the
`scaleType`-preimage `σ'`; `0` off the range or off the degree. -/
theorem zcURLim_eisFace {m e' D : ℕ} (he' : 2 ≤ e') (hD : 2 ≤ D) (hm : m = e' * D)
    (σ : FactorizationType) (hFC : FactorCorrespondenceAt D)
    (hDV : ∀ τ : FactorizationType, τ.degree = D → DecidedValueLaw D τ)
    (hZC : ∀ τ : FactorizationType, τ.degree = D → ZeroConeClause D τ) :
    ZcURLim (fun O _ _ _ _ _ π M =>
      (Nat.card (eisFace π m e' D (M + m) σ) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))) := by
  classical
  subst hm
  have hCTS : CellTypeScalingAt D := cellTypeScalingAt_of_factorCorrespondence hFC
  by_cases hdeg : σ.degree = e' * D
  · by_cases hrange : σ ∈ Set.range (scaleType e')
    · -- the live face
      obtain ⟨σ', hσ'⟩ := hrange
      have hσ'deg : σ'.degree = D := by
        have h1 := scaleType_degree e' σ'
        rw [hσ'] at h1
        have h2 : e' * σ'.degree = e' * D := by
          rw [← h1, hdeg]
        exact Nat.eq_of_mul_eq_mul_left (by omega) h2
      obtain ⟨n, d, hd, hval⟩ := tendsto_stratDec_of_laws (by omega : 1 ≤ D)
        (hDV σ' hσ'deg) (hZC σ' hσ'deg)
      refine ⟨(Polynomial.X - 1) * n,
        Polynomial.X ^ (e' * ∑ t ∈ Finset.range D, (D - t)) * d,
        mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hd, ?_⟩
      intro O _ _ _ _ _
      have hq2 : 2 ≤ residueCard O := two_le_residueCard O
      have hqQ : ((residueCard O : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hdO := (hval O).1
      have hden : (Polynomial.X ^ (e' * ∑ t ∈ Finset.range D, (D - t)) * d).eval
          ((residueCard O : ℕ) : ℚ) ≠ 0 := by
        rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
        exact mul_ne_zero (pow_ne_zero _ hqQ) hdO
      refine ⟨hden, ?_⟩
      intro π hπ
      have h1 := tendsto_eisFace hπ he' (by omega : 1 ≤ D) rfl hCTS σ' hval
      rw [hσ'] at h1
      have hqR : ((residueCard O : ℕ) : ℝ) ≠ 0 := by
        have : (0 : ℝ) < ((residueCard O : ℕ) : ℝ) := by
          exact_mod_cast residueCard_pos O
        exact this.ne'
      have hdR : ((d.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ) ≠ 0 := by
        exact_mod_cast hdO
      have hvv : (((residueCard O : ℕ) : ℝ) - 1)
          * ((((residueCard O : ℕ) : ℝ) ^ (e' * ∑ t ∈ Finset.range D, (D - t)))⁻¹
            * ((n.eval ((residueCard O : ℕ) : ℚ)
                / d.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ))
          = ((((Polynomial.X - 1) * n).eval ((residueCard O : ℕ) : ℚ)
              / ((Polynomial.X ^ (e' * ∑ t ∈ Finset.range D, (D - t)) * d).eval
                  ((residueCard O : ℕ) : ℚ)) : ℚ) : ℝ) := by
        rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one]
        push_cast
        field_simp
      rw [hvv] at h1
      exact h1
    · -- σ outside the scale range: every cell is empty
      refine ZcURLim_zero.congr ?_
      intro O _ _ _ _ _ π hπ M
      haveI : Fintype (ResidueField O) := Fintype.ofFinite _
      have hcnt := card_eisFace_eq_sum (O := O) π (by omega : 1 ≤ D) σ
        (m := e' * D) (e' := e') (N := M + e' * D)
      have hzero : ∀ y ∈ Finset.univ.filter (fun y : ResidueField O => y ≠ 0),
          Nat.card (eisCellDec π (e' * D) e' D (M + e' * D)
            (resFieldXEquiv O y) σ) = 0 := by
        intro y hy
        have hy0 : y ≠ 0 := (Finset.mem_filter.mp hy).2
        have hzres : IsLocalRing.residue O (resSect O y) = y := residue_resSect O y
        have hz0 : IsLocalRing.residue O (resSect O y) ≠ 0 := by
          rw [hzres]
          exact hy0
        have hw0 : IsLocalRing.residue O (-(resSect O y)) ≠ 0 := by
          rw [map_neg, hzres]
          exact neg_ne_zero.mpr hy0
        obtain ⟨i1, i2, i3, i4, hpack⟩ :=
          eis_recentring_stack π (-(resSect O y)) hπ hw0 he'
        obtain ⟨iAC, -⟩ := hpack
        letI := i1
        letI := i2
        letI := i3
        letI := i4
        have hempty := eisCellDec_eq_empty_of_not_range hπ hz0 hw0 he'
          (N := M + e' * D) hCTS hrange
        rw [hzres] at hempty
        rw [hempty]
        simp
      show (0 : ℝ) = _
      rw [hcnt, Finset.sum_congr rfl hzero]
      simp
  · -- σ off the degree: the face is empty (every member is decided at a degree-m type)
    refine ZcURLim_zero.congr ?_
    intro O _ _ _ _ _ π hπ M
    have hempty : eisFace π (e' * D) e' D (M + e' * D) σ = ∅ := by
      ext c
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨-, -, hdec⟩
      obtain ⟨a, ha⟩ := proj_surjective O (e' * D) (M + e' * D) c
      have hty := hdec a ha
      apply hdeg
      rw [← hty, typeOf_degree (monicPoly_monic a), monicPoly_natDegree]
    show (0 : ℝ) = _
    rw [hempty]
    simp

/-- ★★★ **THE COMPOSITE-MASS FIRE**: `PowerFullSpanLaw m σ` conditional on
{`FactorCorrespondenceAt D` : `D ∣ m`, `2 ≤ D ≤ m/2`} + the mass-`D` decided-value and
zero-cone supplies at those depths + the named non-Eisenstein remainder. -/
theorem powerFullSpanLaw_of_correspondence {m : ℕ} (σ : FactorizationType)
    (hFC : ∀ D, D ∣ m → 2 ≤ D → 2 * D ≤ m → FactorCorrespondenceAt D)
    (hDV : ∀ D, D ∣ m → 2 ≤ D → 2 * D ≤ m →
      ∀ τ : FactorizationType, τ.degree = D → DecidedValueLaw D τ)
    (hZC : ∀ D, D ∣ m → 2 ≤ D → 2 * D ≤ m →
      ∀ τ : FactorizationType, τ.degree = D → ZeroConeClause D τ)
    (hRem : EisFullSpanRemainderLaw m σ) :
    PowerFullSpanLaw m σ := by
  classical
  have hface : ∀ e' ∈ (m.divisors.filter fun e' => 2 ≤ e' ∧ 2 ≤ m / e'),
      ZcURLim (fun O _ _ _ _ _ π M =>
        (Nat.card (eisFace π m e' (m / e') (M + m) σ) : ℝ)
          / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))) := by
    intro e' he'
    rw [Finset.mem_filter, Nat.mem_divisors] at he'
    obtain ⟨⟨hdvd, -⟩, h2e, h2D⟩ := he'
    have hmm : m = e' * (m / e') := (Nat.mul_div_cancel' hdvd).symm
    have hDdvd : (m / e') ∣ m := Nat.div_dvd_of_dvd hdvd
    have h2Dm : 2 * (m / e') ≤ m := by
      conv_rhs => rw [hmm]
      exact Nat.mul_le_mul h2e (le_refl _)
    exact zcURLim_eisFace h2e h2D hmm σ (hFC _ hDdvd h2D h2Dm)
      (hDV _ hDdvd h2D h2Dm) (hZC _ hDdvd h2D h2Dm)
  refine ((ZcURLim_sum _ _ hface).add hRem).congr ?_
  intro O _ _ _ _ _ π hπ M
  show (∑ e' ∈ (m.divisors.filter fun e' => 2 ≤ e' ∧ 2 ≤ m / e'),
      (Nat.card (eisFace π m e' (m / e') (M + m) σ) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)))
    + (Nat.card ((powerSectorFull O π m σ M
        \ ⋃ e' ∈ (m.divisors.filter fun e' => 2 ≤ e' ∧ 2 ≤ m / e'),
            eisFace π m e' (m / e') (M + m) σ) : Set (Coeff O m (M + m))) : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
    = (Nat.card (powerSectorFull O π m σ M) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
  rw [card_psf_partition hπ m σ M]
  push_cast
  rw [add_div, Finset.sum_div]

/-- ★★★ **THE GENERAL WRAPPER**: prime mass (DTR's unconditional fire) OR the
correspondence family with its divisor-depth supplies. -/
theorem powerFullSpanLaw_of_prime_or_correspondence {m : ℕ} (σ : FactorizationType)
    (h : m.Prime
      ∨ ((∀ D, D ∣ m → 2 ≤ D → 2 * D ≤ m → FactorCorrespondenceAt D)
        ∧ (∀ D, D ∣ m → 2 ≤ D → 2 * D ≤ m →
            ∀ τ : FactorizationType, τ.degree = D → DecidedValueLaw D τ)
        ∧ (∀ D, D ∣ m → 2 ≤ D → 2 * D ≤ m →
            ∀ τ : FactorizationType, τ.degree = D → ZeroConeClause D τ)
        ∧ EisFullSpanRemainderLaw m σ)) :
    PowerFullSpanLaw m σ := by
  rcases h with hp | ⟨h1, h2, h3, h4⟩
  · exact powerFullSpanLaw_of_prime hp σ
  · exact powerFullSpanLaw_of_correspondence σ h1 h2 h3 h4

end Fire

/-! ## §6 — the `m = 4` instance: the remainder is EMPTY, and the law fires on
`FactorCorrespondenceAt 2` alone -/

section FourInstance

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- ★★ At `m = 4` every full-span class IS an Eisenstein-frame cell member: the face
is forced to `(1, 2)` and the residual to a nonzero-centred linear square
(`4 = e'·k·deg ψ` with `e' ≥ 2, k ≥ 2, deg ψ ≥ 1` forces `e' = k = 2, deg ψ = 1`). -/
theorem psf_four_subset_eisFace {π : O} (hπ : Irreducible π)
    (σ : FactorizationType) (M : ℕ) :
    powerSectorFull O π 4 σ M
      ⊆ ⋃ e' ∈ ((4 : ℕ).divisors.filter fun e' => 2 ≤ e' ∧ 2 ≤ 4 / e'),
          eisFace π 4 e' (4 / e') (M + 4) σ := by
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  rintro c ⟨hcp, h₁, e₁, hF₁, hfull₁⟩
  obtain ⟨h, e', k, ψ, hF, he'2, hψm, hψirr, hψ0, hk, heq, hd1, hle⟩ :=
    powerSector_data σ hπ hcp
  obtain ⟨hh, he⟩ := minFaceAt_unique hF₁ hF
  subst hh
  subst he
  -- the arithmetic forcing
  rw [heq, Polynomial.natDegree_pow] at hfull₁
  have he'4 : e₁ = 2 ∧ k = 2 ∧ ψ.natDegree = 1 := by
    have h2 : 2 * (2 * 1) ≤ e₁ * (k * ψ.natDegree) :=
      Nat.mul_le_mul he'2 (Nat.mul_le_mul hk hd1)
    have h3 : e₁ * (k * ψ.natDegree) = 4 := hfull₁
    -- e₁ ≥ 2, k ≥ 2, degψ ≥ 1, product = 4 ⟹ (2,2,1)
    rcases Nat.lt_or_ge e₁ 3 with he₁ | he₁
    · have he₁2 : e₁ = 2 := by omega
      subst he₁2
      have h4 : k * ψ.natDegree = 2 := by omega
      rcases Nat.lt_or_ge k 3 with hk3 | hk3
      · have hk2 : k = 2 := by omega
        subst hk2
        omega
      · have h5 : 3 * 1 ≤ k * ψ.natDegree := Nat.mul_le_mul hk3 hd1
        omega
    · exfalso
      have h5 : 3 * (2 * 1) ≤ e₁ * (k * ψ.natDegree) :=
        Nat.mul_le_mul he₁ (Nat.mul_le_mul hk hd1)
      omega
  obtain ⟨he₁2, hk2, hψd⟩ := he'4
  subst he₁2
  subst hk2
  -- the h-slope is forced to 1
  have hh1 : h₁ = 1 := by
    have ha := hF.1
    have hb := hF.2.1
    omega
  subst hh1
  -- the residual centre (destructured through ∃ — never rewrite `eq_X_add_C` in place)
  obtain ⟨aψ, haψ⟩ : ∃ a, ψ = Polynomial.X + Polynomial.C a :=
    ⟨ψ.coeff 0, hψm.eq_X_add_C hψd⟩
  have haψ0 : aψ ≠ 0 := by
    intro h0
    apply hψ0
    rw [haψ, h0]
    simp
  have hζ0 : -aψ ≠ 0 := neg_ne_zero.mpr haψ0
  have hres : classResidualPoly π c 1 2
      = (Polynomial.X - Polynomial.C (-aψ)) ^ 2 := by
    rw [heq]
    congr 1
    rw [haψ, map_neg, sub_neg_eq_add]
  -- membership in the (e' = 2) face
  have hmem : (2 : ℕ) ∈ ((4 : ℕ).divisors.filter fun e' => 2 ≤ e' ∧ 2 ≤ 4 / e') := by
    decide
  refine Set.mem_biUnion hmem ?_
  have hdec : DecidedAt O 4 σ (M + 4) c := hcp.1.1.1.1
  exact ⟨hF, ⟨-aψ, hζ0, hres⟩, hdec⟩

/-- ★★ **The `m = 4` remainder law, UNCONDITIONAL**: the non-Eisenstein part is empty. -/
theorem eisFullSpanRemainderLaw_four (σ : FactorizationType) :
    EisFullSpanRemainderLaw 4 σ := by
  refine ZcURLim_zero.congr ?_
  intro O _ _ _ _ _ π hπ M
  have hempty : (powerSectorFull O π 4 σ M
      \ ⋃ e' ∈ ((4 : ℕ).divisors.filter fun e' => 2 ≤ e' ∧ 2 ≤ 4 / e'),
          eisFace π 4 e' (4 / e') (M + 4) σ) = ∅ := by
    rw [Set.sdiff_eq_empty]
    exact psf_four_subset_eisFace hπ σ M
  show (0 : ℝ) = _
  rw [hempty]
  simp

/-- ★★★ **THE `m = 4` FULL-SPAN LAW ON THE CORRESPONDENCE ALONE**:
`FactorCorrespondenceAt 2` fires `PowerFullSpanLaw 4 σ` for EVERY `σ` — the `D = 2`
value laws are closed (`decidedSliceAt_two`), the `D = 2` zero-cone clauses are closed
(`zeroConeClause_two`), and the remainder is empty. -/
theorem powerFullSpanLaw_four (hFC2 : FactorCorrespondenceAt 2)
    (σ : FactorizationType) : PowerFullSpanLaw 4 σ := by
  refine powerFullSpanLaw_of_correspondence σ ?_ ?_ ?_ (eisFullSpanRemainderLaw_four σ)
  · intro D _ h2 h4
    have hD2 : D = 2 := by omega
    subst hD2
    exact hFC2
  · intro D _ h2 h4 τ hτ
    have hD2 : D = 2 := by omega
    subst hD2
    exact Uniformity.Density.decidedSliceAt_two τ hτ
  · intro D _ h2 h4 τ _
    have hD2 : D = 2 := by omega
    subst hD2
    exact zeroConeClause_two τ

end FourInstance

/-! ## §7 — the dd assembly: ER4's double-root sector IS the `(4, 2, 2)` Eisenstein
face, so its three `ZcURLim` limits fire on `FactorCorrespondenceAt 2` alone -/

section DdAssembly

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- ★★ **THE E1-FRAME CONVERSION**: ER4's σ-decided double-root box IS the σ-decided
`(4, 2, 2)` Eisenstein face carrier — the E1 lattice/corner reconstruct the face (W1),
and the pinned side residual is the class residual. -/
theorem dec_e1DdBox_eq_eisFace {π : O} (hπ : Irreducible π)
    (σ : FactorizationType) (M : ℕ) :
    (decidedSet O 4 σ (M + 4) ∩ e1DdBox π (M + 4) : Set (Coeff O 4 (M + 4)))
      = eisFace π 4 2 2 (M + 4) σ := by
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  have hm0 : (0 : ℕ) < 4 := by omega
  ext c
  constructor
  · rintro ⟨hdec, he1, a, ha, L, hLm, hLd, hres⟩
    obtain ⟨h0, h1, h2, h3⟩ :=
      (Uniformity.Density.IFCG34.mem_e1Box_iff c).mp he1
    -- the lattice and exact corner
    have hlat : ∀ j : Fin 4, 4 - (j : ℕ) ≤ 2 * resOrd (c j) := by
      rintro ⟨jn, hjn⟩
      interval_cases jn
      · have h0' : resOrd (c ⟨0, hjn⟩) = 2 := h0
        show 4 - (0 : ℕ) ≤ 2 * resOrd (c ⟨0, hjn⟩)
        omega
      · have h1' : 2 ≤ resOrd (c ⟨1, hjn⟩) := h1
        show 4 - (1 : ℕ) ≤ 2 * resOrd (c ⟨1, hjn⟩)
        omega
      · have h2' : 1 ≤ resOrd (c ⟨2, hjn⟩) := h2
        show 4 - (2 : ℕ) ≤ 2 * resOrd (c ⟨2, hjn⟩)
        omega
      · have h3' : 1 ≤ resOrd (c ⟨3, hjn⟩) := h3
        show 4 - (3 : ℕ) ≤ 2 * resOrd (c ⟨3, hjn⟩)
        omega
    have hcorner : resOrd (c ⟨0, hm0⟩) = 2 := h0
    obtain ⟨hF, hdeg2⟩ := lattice_pins hπ (le_refl 2) (by norm_num : 2 * 2 = 4)
      (by omega : 4 ≤ M + 4) hm0 hlat hcorner
    -- the class residual is the pinned side residual
    have hfull' : 2 * (classResidualPoly π c 1 2).natDegree = 4 := by
      rw [hdeg2]
    obtain ⟨hne, hmin0, hsdeg, hnpz, hcrp⟩ := fullSpan_pins hπ hF hfull' ha
    rw [hdeg2] at hcrp
    have hcL : classResidualPoly π c 1 2 = L ^ 2 := by
      rw [hcrp]
      exact hres
    -- the nonzero centre
    obtain ⟨hne₂, H₀, hH₀, htop, hcrp₂⟩ := resPoly_rep hπ hF ha
    have hnd := natDegree_resPoly hπ isKey_X (by omega : 0 < 2)
      (Nat.coprime_one_left 2) htop hne₂ hH₀
    have hc0 : (classResidualPoly π c 1 2).coeff 0 ≠ 0 := by
      rw [hcrp₂]
      exact hnd.2
    rw [hcL] at hc0
    have hL0 : L.coeff 0 ≠ 0 := by
      intro hz
      apply hc0
      rw [← Polynomial.constantCoeff_apply, map_pow, Polynomial.constantCoeff_apply, hz]
      simp
    obtain ⟨aL, haL⟩ : ∃ a, L = Polynomial.X + Polynomial.C a :=
      ⟨L.coeff 0, hLm.eq_X_add_C hLd⟩
    have haL0 : aL ≠ 0 := by
      intro hz
      apply hL0
      rw [haL, hz]
      simp
    refine ⟨hF, ⟨-aL, neg_ne_zero.mpr haL0, ?_⟩, hdec⟩
    rw [hcL]
    congr 1
    rw [haL, map_neg, sub_neg_eq_add]
  · rintro ⟨hF, ⟨ζ, hζ, hres⟩, hdec⟩
    refine ⟨hdec, ?_⟩
    have hdegres : (classResidualPoly π c 1 2).natDegree = 2 := by
      rw [hres, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, Nat.mul_one]
    have hfull' : 2 * (classResidualPoly π c 1 2).natDegree = 4 := by
      rw [hdegres]
    have hcorner := fullSpan_corner hπ hF hfull' (by omega : 4 ≤ M + 4) hm0
    rw [hdegres, Nat.one_mul] at hcorner
    obtain ⟨a, ha⟩ := proj_surjective O 4 (M + 4) c
    obtain ⟨hne, hmin0, hsdeg, hnpz, hcrp⟩ := fullSpan_pins hπ hF hfull' ha
    rw [hdegres] at hcrp
    refine ⟨?_, a, ha, Polynomial.X - Polynomial.C ζ,
      Polynomial.monic_X_sub_C ζ, Polynomial.natDegree_X_sub_C ζ, ?_⟩
    · -- the E1 box conditions from the face
      refine (Uniformity.Density.IFCG34.mem_e1Box_iff c).mpr ⟨hcorner, ?_, ?_, ?_⟩
      · have h1 := minFaceAt_min hF 1
        rw [Nat.one_mul] at h1
        have h1' : 1 * (4 - ((1 : Fin 4) : ℕ)) ≤ 2 * resOrd (c 1) := by
          rw [Nat.one_mul]
          exact h1
        omega
      · have h2 := minFaceAt_min hF 2
        rw [Nat.one_mul] at h2
        omega
      · have h3 := minFaceAt_min hF 3
        rw [Nat.one_mul] at h3
        omega
    · -- the pinned side residual is the class residual
      have hgoal : classResidualPoly π c 1 2 = (Polynomial.X - Polynomial.C ζ) ^ 2 :=
        hres
      rw [hcrp] at hgoal
      exact hgoal

/-- ★★★ **ER4's dd LIMITS ON THE CORRESPONDENCE ALONE**: `ZcURLim (e1DdDecFam σ)` for
EVERY `σ`, from `FactorCorrespondenceAt 2` — the `D = 2` value laws
(`decidedSliceAt_two`) and cone clauses (`zeroConeClause_two`) are closed. -/
theorem zcURLim_e1DdDecFam (hFC2 : FactorCorrespondenceAt 2) (σ : FactorizationType) :
    ZcURLim (e1DdDecFam σ) := by
  have hface := zcURLim_eisFace (m := 4) (e' := 2) (D := 2) (le_refl 2) (le_refl 2)
    (by norm_num) σ hFC2 (fun τ hτ => Uniformity.Density.decidedSliceAt_two τ hτ)
    (fun τ _ => zeroConeClause_two τ)
  refine hface.congr ?_
  intro O _ _ _ _ _ π hπ M
  show (Nat.card (eisFace π 4 2 2 (M + 4) σ) : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4)) = e1DdDecFam σ O π M
  rw [← dec_e1DdBox_eq_eisFace hπ σ M]
  rfl

/-- ★★ **ER4's `{(2,1),(2,1)}` row, dd premise discharged**: the law from the split-box
limit, the E2 term, and `FactorCorrespondenceAt 2`. -/
theorem coneRemainderLaw_four_ramPair_of_correspondence
    (hFC2 : FactorCorrespondenceAt 2) (h1 : ZcURLim e1SplitFam)
    (h3 : ZcURLim (e2DecFam ramPairType)) : ConeRemainderLaw 4 ramPairType :=
  coneRemainderLaw_four_ramPair_of_sectors h1 (zcURLim_e1DdDecFam hFC2 ramPairType) h3

/-- ★★ **ER4's `{(2,2)}` row, dd premise discharged**: the law from the named leaf,
the irreducible-box limit, and `FactorCorrespondenceAt 2`. -/
theorem coneRemainderLaw_four_type22_of_correspondence (hL : E1IrrLeafDecision)
    (hFC2 : FactorCorrespondenceAt 2) (h1 : ZcURLim e1IrrFam) :
    ConeRemainderLaw 4 type22 :=
  coneRemainderLaw_four_type22_of_sectors hL h1 (zcURLim_e1DdDecFam hFC2 type22)

/-- ★★★ **ER4's `{(4,1)}` row, dd premise discharged**: the wild law from EXACTLY the
named leaf and `FactorCorrespondenceAt 2` — the order-2 recursion term is closed. -/
theorem coneRemainderLaw_four_type41_of_correspondence (hL : E1IrrLeafDecision)
    (hFC2 : FactorCorrespondenceAt 2) : ConeRemainderLaw 4 type41 :=
  coneRemainderLaw_four_type41_of_sectors hL (zcURLim_e1DdDecFam hFC2 type41)

end DdAssembly

end Uniformity.Density.IFCG51

end

/-! ## AXCHECK FOOTER — the assembly layers (§1–§4, §5's fire, §6's `m = 4` instance)
expect pure Lean core `{propext, Classical.choice, Quot.sound}` wherever their inputs
are Lean-core; the `m = 4` fire inherits `decidedSliceAt_two`'s footprint; the §7 row
fires inherit IFCG34's (Lean core + exactly the owner-signed B.42
`Uniformity.Density.Leaf.exists_slope_factorization`).  The C.33 cites must NOT occur. -/

section AxCheck
#print axioms Uniformity.Density.IFCG51.lattice_pins
#print axioms Uniformity.Density.IFCG51.cell_of_box
#print axioms Uniformity.Density.IFCG51.tendsto_stratDec_of_laws
#print axioms Uniformity.Density.IFCG51.eisCellDec_subset_psf
#print axioms Uniformity.Density.IFCG51.cellTransport_image_eisCellDec
#print axioms Uniformity.Density.IFCG51.card_eisCellDec
#print axioms Uniformity.Density.IFCG51.eisCellDec_eq_empty_of_not_range
#print axioms Uniformity.Density.IFCG51.tendsto_eisCellDec
#print axioms Uniformity.Density.IFCG51.card_eisFace_eq_sum
#print axioms Uniformity.Density.IFCG51.eisFace_subset_psf
#print axioms Uniformity.Density.IFCG51.card_psf_partition
#print axioms Uniformity.Density.IFCG51.tendsto_eisFace
#print axioms Uniformity.Density.IFCG51.EisFullSpanRemainderLaw
#print axioms Uniformity.Density.IFCG51.zcURLim_eisFace
#print axioms Uniformity.Density.IFCG51.powerFullSpanLaw_of_correspondence
#print axioms Uniformity.Density.IFCG51.powerFullSpanLaw_of_prime_or_correspondence
#print axioms Uniformity.Density.IFCG51.psf_four_subset_eisFace
#print axioms Uniformity.Density.IFCG51.eisFullSpanRemainderLaw_four
#print axioms Uniformity.Density.IFCG51.powerFullSpanLaw_four
#print axioms Uniformity.Density.IFCG51.dec_e1DdBox_eq_eisFace
#print axioms Uniformity.Density.IFCG51.zcURLim_e1DdDecFam
#print axioms Uniformity.Density.IFCG51.coneRemainderLaw_four_ramPair_of_correspondence
#print axioms Uniformity.Density.IFCG51.coneRemainderLaw_four_type22_of_correspondence
#print axioms Uniformity.Density.IFCG51.coneRemainderLaw_four_type41_of_correspondence
end AxCheck
