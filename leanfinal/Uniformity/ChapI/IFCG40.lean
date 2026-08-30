/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG38

/-!
# Uniformity.ChapI.IFCG40 — [SDL 2026-08-30] the polygon-block product count:
the class-level Minkowski transfer, the exact defect decomposition, and the
low-mass firings of the convolution defect law

Stage SDL of the cone census (design record `runs/wave-c/verdict_SDL.md`).  SSL
(`IFCG38`) re-based `SplitSectorLaw m σ` onto ONE Prop, the convolution defect law
`SplitConvolutionDefectLaw m σ`, and named its discharge territory: the CONVERSE of the
refinement map — which decided smaller-mass pairs multiply INTO the visible split
sector.  This file lands that converse's ENGINE and the exact finite-level accounting:

* **§1 ★ THE CLASS-LEVEL MINKOWSKI TRANSFER.**  B.39a §7's general product law
  (`resPoly_mul_gen` and its side-data clauses — the corpus ALREADY holds the full
  polynomial-level Minkowski/Gauss transfer, purity-free) is lifted to the class level:
  `minFaceAt_mulClass` — two classes with the SAME minimal face `(h, e')` multiply to a
  class with that minimal face, and the class residual polynomial MULTIPLIES:
  `classResidualPoly π (mulClass c₁ c₂) h e' = classResidualPoly π c₁ h e' *
  classResidualPoly π c₂ h e'`.  The two-block concatenation of the charge is the
  instance: a pure block times a face-plus-steeper block reads off `G · H`.
* **§1b ★ THE SECTOR CONVERSE** (`mulClass_mem_splitSector` / `_Vis`): a coprime-residual
  pair of same-face classes multiplies INTO the split sector — the converse of SSL §2's
  refinement map — with the two honest gate legs as hypotheses: the product's
  DECIDEDNESS (the polygon-block Hensel gap, named below) and its pure-face-box
  exclusion.  With corner attainment on both factors the product lands in the VISIBLE
  sector (`CornerVisible` is derived, not assumed).
* **§2 ★ THE EXACT COUNT LAYER.**  `mulClass_cancel_left/right` — the fold is
  LEVEL-EXACT injective in each argument separately (monic polynomials are regular mod
  `𝔪^N`; no polygon needed).  `multCount` — the pair-fiber multiplicity of a product
  cell in SSL's convolution table — with the fiberwise double count
  `convCount_eq_sum_multCount` and ★ THE EXACT DEFECT DECOMPOSITION
  `convCount_eq_card_vis_add_defect`:

      convCount = #vis + [ Σ_{c ∈ vis} (multCount c − 1)  +  Σ_{c ∉ vis} multCount c ]

  — the defect IS collisions plus strays, exactly, at every finite level.
* **§3 ★ THE FIRINGS.**  `splitSector_eq_empty_of_mass_le_three` — below mass 4 the
  split sector is EMPTY (a coprime split needs residual degree ≥ 2 and `e' ≥ 2`, so
  mass ≥ 4); hence `splitConvolutionDefectLaw_of_mass_le_one` (UNCONDITIONAL — the
  first outright instances of the defect law: the table and the sector are both empty),
  `splitConvolutionDefectLaw_of_mass_le_three` (under the `< m` decided value laws),
  and `splitSectorLaw_of_mass_le_three` (the socket fires end-to-end).  ★
  `splitConvolutionDefectLaw_iff_splitSectorLaw`: under the `< m` value laws the defect
  law is EQUIVALENT to the sector law — SSL's "re-base, not a strength reduction" claim,
  machine-checked in both directions.

## THE HONEST FENCE (what this unit's charge asked that is NOT provable as stated)

The charge predicted "(decided cell₁, decided cell₂) → product cell is injective ONTO
the visible split cells" — finite-precision uniqueness at distinct slopes.  This is
FALSE at level exactness: for two blocks sharing a face (or at distinct positive
slopes), the multiplication map has fibers of size `q^{v(Res)}` where `v(Res)` is the
resultant valuation of the block pair (mixing number `> 0` whenever both blocks have
all roots of positive valuation — e.g. masses `(1,1)` at slope `1`: `(X−a)(X−b)` with
`v(a)=v(b)=1` determines `a` only mod `π^{N−1}`).  Level-exact injectivity holds ONLY
against a unit-corner cofactor (IFCG16 §6 / XHS §3's genre, residual coprimality mod
`π`) — inside the `X^m` stratum NO two-block split is level-exact.  The TRUE exact
object is §2's fiber decomposition; the surviving open content of
`SplitConvolutionDefectLaw m σ` (mass ≥ 4, σ ramified) is the rationality of the
mixing-graded census: `convCount = Σ_c multCount c` with `multCount c` a `q`-power
ladder in the cell's resultant depths.  Everything else — the transfer engine, the
sector converse, the exact decomposition, the equivalence, the low-mass firings — is
machine-checked here.

## Axiom fence

Lean-core (`propext`, `Classical.choice`, `Quot.sound`) EVERYWHERE except exactly TWO
declarations: §2's `one_le_multCount_of_vis` and `convCount_eq_card_vis_add_defect`
consume SSL's refinement map, hence Lean core + the owner-signed B.42 cite
`Uniformity.Density.Leaf.exists_slope_factorization` (through XHS).  In particular §1's
transfer, both cancellations, the double count, ALL of §3 — including the equivalence
`splitConvolutionDefectLaw_iff_splitSectorLaw` and the mass-≤-3 firings — are pure
Lean core.  The C.33 cites do NOT occur.  Zero sorries at landing.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG40

open IsLocalRing Polynomial
open Uniformity.Density.Induction
open Uniformity.Density.Leaf
open Uniformity.Density.IFCG22 (classCoeffVal classCoeffVal_le classCoeffVal_exact
  le_classCoeffVal_iff_dvd npHeight classNPSupport NPAttains ClassNPFace NPVisibleAt
  classNPSupport_le_apply le_classNPSupport classNPSupport_le exists_npAttains)
open Uniformity.Density.IFCG24 (ZcURLim ZcURLim_zero shallowSet pureFaceSet
  mem_stratum_X_pow_iff npHeight_coe)
open Uniformity.Density.IFCG14 (DecidedValueLaw)
open Uniformity.Density.IFCG23 (npHgt_monicPoly_eq npHgt_monicPoly_top)
open Uniformity.Density.IFCG26 (onSide_monicPoly_of_npAttains)
open Uniformity.Density.IFCG17 (monicPoly_coeff_eq_self exists_decided_factors)
open Uniformity.Density.IFCG35 (MinFaceAt minFaceAt_support minFaceAt_min
  minFaceAt_attained_lt minFaceAt_unique classResidualPoly classResidualPoly_eq
  classResidualPoly_natDegree_pos splitSector splitSectorCount SplitSectorLaw)
open Uniformity.Density.IFCG38 (CornerVisible splitSectorVis splitSectorInv convPairs
  convCount mulClassAt SplitConvolutionDefectLaw zcURLim_conv zcURLim_sub zcURLim_inv
  splitSectorCount_eq_vis_add_inv splitSectorLaw_of_defectLaw splitSector_refines_decided
  splitSector_coprime_split classResidualPoly_monic)

/-! ## §0 — supply (private copies of landed idioms) -/

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

variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **The representation supply** (private copy of SSL §1's): on a minimal face, the
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

end Supply

/-! ## §1 — ★ THE CLASS-LEVEL MINKOWSKI TRANSFER -/

section Transfer

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★ **The class-level Minkowski transfer at a shared minimal face** — the
concatenation law: two classes with the same minimal face `(h, e')` multiply to a class
with minimal face `(h, e')`, and the class residual polynomial MULTIPLIES.  (B.39a §7's
general polynomial-level product law, transported through the CN1 class/lift bridges;
the level bound `n₁ + n₂ ≤ N` is what keeps the product's face below the frame floor.) -/
theorem minFaceAt_mulClass {π : O} (hπ : Irreducible π) {n₁ n₂ N : ℕ}
    (hN : n₁ + n₂ ≤ N) {c₁ : Coeff O n₁ N} {c₂ : Coeff O n₂ N} {h e' : ℕ}
    (hF₁ : MinFaceAt c₁ h e') (hF₂ : MinFaceAt c₂ h e') :
    MinFaceAt (mulClass c₁ c₂) h e'
      ∧ classResidualPoly π (mulClass c₁ c₂) h e'
          = classResidualPoly π c₁ h e' * classResidualPoly π c₂ h e' := by
  have hh1 := hF₁.1
  have hhe := hF₁.2.1
  have hcop := hF₁.2.2.1
  have hface₁ := hF₁.2.2.2.1
  have hAtop₁ := hF₁.2.2.2.2.1
  have hvis₁ := hF₁.2.2.2.2.2
  have hface₂ := hF₂.2.2.2.1
  have hAtop₂ := hF₂.2.2.2.2.1
  have hvis₂ := hF₂.2.2.2.2.2
  have he' : 0 < e' := by omega
  have hu : 0 < h := by omega
  -- lifts and their side data (the resPoly_rep supply)
  obtain ⟨a₁, ha₁⟩ := proj_surjective O n₁ N c₁
  obtain ⟨a₂, ha₂⟩ := proj_surjective O n₂ N c₂
  obtain ⟨hne₁, H₁, hH₁, htop₁, hcrp₁⟩ := resPoly_rep hπ hF₁ ha₁
  obtain ⟨hne₂, H₂, hH₂, htop₂, hcrp₂⟩ := resPoly_rep hπ hF₂ ha₂
  have hdeg₁ : (monicPoly a₁).natDegree = n₁ := monicPoly_natDegree a₁
  have hdeg₂ : (monicPoly a₂).natDegree = n₂ := monicPoly_natDegree a₂
  -- the supports are the class supports `h·nᵢ`
  obtain ⟨-, hsupp₁⟩ := onSide_monicPoly_of_npAttains hπ he' hvis₁ hAtop₁ ha₁
  obtain ⟨-, hsupp₂⟩ := onSide_monicPoly_of_npAttains hπ he' hvis₂ hAtop₂ ha₂
  have hcs₁ : classNPSupport c₁ h e' = h * n₁ := minFaceAt_support hF₁
  have hcs₂ : classNPSupport c₂ h e' = h * n₂ := minFaceAt_support hF₂
  -- the left-endpoint on-side identities, in ℕ
  have hid₁ : e' * H₁ + h * sideMin X (monicPoly a₁) h e' hne₁ = h * n₁ := by
    have hOn : e' • npHgt X (monicPoly a₁) (sideMin X (monicPoly a₁) h e' hne₁)
        + ((h * sideMin X (monicPoly a₁) h e' hne₁ : ℕ) : ℕ∞)
        = suppVal X (monicPoly a₁) h e' :=
      onSide_of_mem_sideSet (Finset.min'_mem _ hne₁)
    have h7 : e' • npHgt X (monicPoly a₁) (sideMin X (monicPoly a₁) h e' hne₁)
        + ((h * sideMin X (monicPoly a₁) h e' hne₁ : ℕ) : ℕ∞) = ((h * n₁ : ℕ) : ℕ∞) := by
      rw [hOn, hsupp₁, hcs₁]
    rw [hH₁, nsmul_add_cast_gen] at h7
    exact Nat.cast_inj.mp h7
  have hid₂ : e' * H₂ + h * sideMin X (monicPoly a₂) h e' hne₂ = h * n₂ := by
    have hOn : e' • npHgt X (monicPoly a₂) (sideMin X (monicPoly a₂) h e' hne₂)
        + ((h * sideMin X (monicPoly a₂) h e' hne₂ : ℕ) : ℕ∞)
        = suppVal X (monicPoly a₂) h e' :=
      onSide_of_mem_sideSet (Finset.min'_mem _ hne₂)
    have h7 : e' • npHgt X (monicPoly a₂) (sideMin X (monicPoly a₂) h e' hne₂)
        + ((h * sideMin X (monicPoly a₂) h e' hne₂ : ℕ) : ℕ∞) = ((h * n₂ : ℕ) : ℕ∞) := by
      rw [hOn, hsupp₂, hcs₂]
    rw [hH₂, nsmul_add_cast_gen] at h7
    exact Nat.cast_inj.mp h7
  -- the left endpoints sit strictly inside (a face has an attained abscissa `< nᵢ`)
  have hj₁lt : sideMin X (monicPoly a₁) h e' hne₁ < n₁ := by
    obtain ⟨i, j, hij, hAi, hAj⟩ := hface₁
    have hilt : i < n₁ := lt_of_lt_of_le hij hAj.1
    obtain ⟨hOni, -⟩ := onSide_monicPoly_of_npAttains hπ he' hvis₁ hAi ha₁
    have himem : i ∈ sideSet X (monicPoly a₁) h e' :=
      mem_sideSet_iff'.mpr ⟨by omega, hOni⟩
    have h2 : sideMin X (monicPoly a₁) h e' hne₁ ≤ i := Finset.min'_le _ _ himem
    omega
  have hj₂lt : sideMin X (monicPoly a₂) h e' hne₂ < n₂ := by
    obtain ⟨i, j, hij, hAi, hAj⟩ := hface₂
    have hilt : i < n₂ := lt_of_lt_of_le hij hAj.1
    obtain ⟨hOni, -⟩ := onSide_monicPoly_of_npAttains hπ he' hvis₂ hAi ha₂
    have himem : i ∈ sideSet X (monicPoly a₂) h e' :=
      mem_sideSet_iff'.mpr ⟨by omega, hOni⟩
    have h2 : sideMin X (monicPoly a₂) h e' hne₂ ≤ i := Finset.min'_le _ _ himem
    omega
  -- B.39a §7: the product's side data
  have hFdeg : (monicPoly a₁ * monicPoly a₂).natDegree = n₁ + n₂ := by
    rw [(monicPoly_monic a₁).natDegree_mul (monicPoly_monic a₂), hdeg₁, hdeg₂]
  have hneF : (sideSet X (monicPoly a₁ * monicPoly a₂) h e').Nonempty :=
    sideSet_nonempty_gen X _ h e'
  have hminF : sideMin X (monicPoly a₁ * monicPoly a₂) h e' hneF
      = sideMin X (monicPoly a₁) h e' hne₁ + sideMin X (monicPoly a₂) h e' hne₂ :=
    sideMin_mul_gen hπ isKey_X hu he' hcop htop₁ htop₂ hne₁ hne₂ hH₁ hH₂ hneF
  have hnpF : npHgt X (monicPoly a₁ * monicPoly a₂)
      (sideMin X (monicPoly a₁) h e' hne₁ + sideMin X (monicPoly a₂) h e' hne₂)
      = ((H₁ + H₂ : ℕ) : ℕ∞) :=
    npHgt_mul_gen hπ isKey_X hu he' hcop htop₁ htop₂ hne₁ hne₂ hH₁ hH₂
  have hresF : resPoly π X (monicPoly a₁ * monicPoly a₂) h e' hneF (H₁ + H₂)
      = resPoly π X (monicPoly a₁) h e' hne₁ H₁ * resPoly π X (monicPoly a₂) h e' hne₂ H₂ :=
    resPoly_mul_gen hπ isKey_X hu he' hcop htop₁ htop₂ hne₁ hne₂ hH₁ hH₂ hneF
  have hsuppF : suppVal X (monicPoly a₁ * monicPoly a₂) h e'
      = ((e' * (H₁ + H₂)
          + h * (sideMin X (monicPoly a₁) h e' hne₁ + sideMin X (monicPoly a₂) h e' hne₂) : ℕ) : ℕ∞) :=
    suppVal_mul_gen hπ isKey_X hu he' hcop htop₁ htop₂ hne₁ hne₂ hH₁ hH₂
  -- numerics
  have hkey : e' * (H₁ + H₂)
      + h * (sideMin X (monicPoly a₁) h e' hne₁ + sideMin X (monicPoly a₂) h e' hne₂)
      = h * (n₁ + n₂) := by
    calc e' * (H₁ + H₂)
        + h * (sideMin X (monicPoly a₁) h e' hne₁ + sideMin X (monicPoly a₂) h e' hne₂)
        = (e' * H₁ + h * sideMin X (monicPoly a₁) h e' hne₁)
          + (e' * H₂ + h * sideMin X (monicPoly a₂) h e' hne₂) := by ring
      _ = h * n₁ + h * n₂ := by rw [hid₁, hid₂]
      _ = h * (n₁ + n₂) := by ring
  have hmlt : h * (n₁ + n₂) < e' * N := by
    calc h * (n₁ + n₂) < e' * (n₁ + n₂) := by
          exact mul_lt_mul_of_pos_right hhe (by omega)
      _ ≤ e' * N := Nat.mul_le_mul_left e' hN
  have hHsum_lt : H₁ + H₂ < N := by
    have h1 : e' * (H₁ + H₂) ≤ h * (n₁ + n₂) := by omega
    exact Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt h1 hmlt)
  -- the product's coefficient-vector lift
  have hb : proj O (n₁ + n₂) N
      (fun i : Fin (n₁ + n₂) => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))
      = mulClass c₁ c₂ := by
    rw [mulClass_proj, ha₁, ha₂]
  have hmb : monicPoly (fun i : Fin (n₁ + n₂) => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))
      = monicPoly a₁ * monicPoly a₂ :=
    monicPoly_coeff_eq_self ((monicPoly_monic a₁).mul (monicPoly_monic a₂)) hFdeg
  -- the class value at the product's left endpoint is exactly `H₁ + H₂`
  have hJlt : sideMin X (monicPoly a₁) h e' hne₁ + sideMin X (monicPoly a₂) h e' hne₂
      < n₁ + n₂ := by omega
  have hvalJ : classCoeffVal (mulClass c₁ c₂)
      ⟨sideMin X (monicPoly a₁) h e' hne₁ + sideMin X (monicPoly a₂) h e' hne₂, hJlt⟩
      = H₁ + H₂ := by
    have haddv : IsDiscreteValuationRing.addVal O
        ((monicPoly a₁ * monicPoly a₂).coeff
          (sideMin X (monicPoly a₁) h e' hne₁ + sideMin X (monicPoly a₂) h e' hne₂))
        = ((H₁ + H₂ : ℕ) : ℕ∞) := by
      rw [← npHgt_X]
      exact hnpF
    have hdvd : π ^ (H₁ + H₂) ∣ (monicPoly a₁ * monicPoly a₂).coeff
        (sideMin X (monicPoly a₁) h e' hne₁ + sideMin X (monicPoly a₂) h e' hne₂) :=
      (Uniformity.Hensel.pow_dvd_iff_le_addVal hπ).2 (by rw [haddv])
    have hndvd : ¬ π ^ (H₁ + H₂ + 1) ∣ (monicPoly a₁ * monicPoly a₂).coeff
        (sideMin X (monicPoly a₁) h e' hne₁ + sideMin X (monicPoly a₂) h e' hne₂) := by
      intro hcon
      have h2 := (Uniformity.Hensel.pow_dvd_iff_le_addVal hπ).1 hcon
      rw [haddv, Nat.cast_le] at h2
      omega
    have h1 := (le_classCoeffVal_iff_dvd hπ (by omega : H₁ + H₂ ≤ N) hb
      ⟨sideMin X (monicPoly a₁) h e' hne₁ + sideMin X (monicPoly a₂) h e' hne₂, hJlt⟩).2 hdvd
    have h2 : ¬ (H₁ + H₂ + 1 ≤ classCoeffVal (mulClass c₁ c₂)
        ⟨sideMin X (monicPoly a₁) h e' hne₁ + sideMin X (monicPoly a₂) h e' hne₂, hJlt⟩) := by
      intro hcon
      exact hndvd ((le_classCoeffVal_iff_dvd hπ (by omega : H₁ + H₂ + 1 ≤ N) hb
        ⟨sideMin X (monicPoly a₁) h e' hne₁ + sideMin X (monicPoly a₂) h e' hne₂, hJlt⟩).1 hcon)
    omega
  -- the product's class support is `h·(n₁+n₂)`
  have hcsF : classNPSupport (mulClass c₁ c₂) h e' = h * (n₁ + n₂) := by
    refine le_antisymm (classNPSupport_le _ h e') (le_classNPSupport ?_)
    intro i him
    rcases Nat.lt_or_ge i (n₁ + n₂) with hilt | hige
    · have hnp : npHeight (mulClass c₁ c₂) i
          = classCoeffVal (mulClass c₁ c₂) ⟨i, hilt⟩ := by
        unfold Uniformity.Density.IFCG22.npHeight
        rw [dif_pos hilt]
      rw [hnp]
      rcases Nat.lt_or_ge (classCoeffVal (mulClass c₁ c₂) ⟨i, hilt⟩) N with hwin | hinv
      · -- exact window: the class value is the lift's polygon height
        have hlift : npHgt X (monicPoly a₁ * monicPoly a₂) i
            = ((classCoeffVal (mulClass c₁ c₂) ⟨i, hilt⟩ : ℕ) : ℕ∞) := by
          have h5 := npHgt_monicPoly_eq hπ hb hilt hwin
          rwa [hmb] at h5
        have hwb := suppVal_le_weight Polynomial.monic_X (by simp) he' h
          (monicPoly a₁ * monicPoly a₂) i
        rw [hsuppF, hlift, nsmul_add_cast_gen, Nat.cast_le] at hwb
        omega
      · -- invisible window: the class value is the full window `N`
        have h6 : classCoeffVal (mulClass c₁ c₂) ⟨i, hilt⟩ ≤ N := classCoeffVal_le _ _
        have h7 : classCoeffVal (mulClass c₁ c₂) ⟨i, hilt⟩ = N := le_antisymm h6 hinv
        have h8 : e' * N ≤ e' * classCoeffVal (mulClass c₁ c₂) ⟨i, hilt⟩ :=
          Nat.mul_le_mul_left e' hinv
        omega
    · have hieq : i = n₁ + n₂ := le_antisymm him hige
      subst hieq
      have hnp : npHeight (mulClass c₁ c₂) (n₁ + n₂) = 0 := by
        unfold Uniformity.Density.IFCG22.npHeight
        rw [dif_neg (lt_irrefl _)]
      rw [hnp]
      omega
  -- the face data of the product
  have hAJ : NPAttains (mulClass c₁ c₂) h e'
      (sideMin X (monicPoly a₁) h e' hne₁ + sideMin X (monicPoly a₂) h e' hne₂) := by
    refine ⟨by omega, ?_⟩
    have hnp : npHeight (mulClass c₁ c₂)
        (sideMin X (monicPoly a₁) h e' hne₁ + sideMin X (monicPoly a₂) h e' hne₂)
        = classCoeffVal (mulClass c₁ c₂)
            ⟨sideMin X (monicPoly a₁) h e' hne₁ + sideMin X (monicPoly a₂) h e' hne₂, hJlt⟩ := by
      unfold Uniformity.Density.IFCG22.npHeight
      rw [dif_pos hJlt]
    rw [hnp, hvalJ, hcsF]
    exact hkey
  have hAtopF : NPAttains (mulClass c₁ c₂) h e' (n₁ + n₂) := by
    refine ⟨le_rfl, ?_⟩
    have hnp : npHeight (mulClass c₁ c₂) (n₁ + n₂) = 0 := by
      unfold Uniformity.Density.IFCG22.npHeight
      rw [dif_neg (lt_irrefl _)]
    rw [hnp, hcsF]
    omega
  have hvisF : NPVisibleAt (mulClass c₁ c₂) h e' := by
    show classNPSupport (mulClass c₁ c₂) h e' < e' * N
    rw [hcsF]
    exact hmlt
  have hFace : MinFaceAt (mulClass c₁ c₂) h e' :=
    ⟨hh1, hhe, hcop,
      ⟨sideMin X (monicPoly a₁) h e' hne₁ + sideMin X (monicPoly a₂) h e' hne₂, n₁ + n₂,
        by omega, hAJ, hAtopF⟩, hAtopF, hvisF⟩
  refine ⟨hFace, ?_⟩
  -- the residual transfer: the class residual of the product IS the lift's, which multiplies
  obtain ⟨hne_b, H₀, hH_b, -, hcrp_b⟩ := resPoly_rep hπ hFace hb
  revert hH_b hcrp_b
  revert hne_b
  rw [hmb]
  intro hne_b hH_b hcrp_b
  -- identify the left height (proof-irrelevant side data)
  have hH_b' : npHgt X (monicPoly a₁ * monicPoly a₂)
      (sideMin X (monicPoly a₁ * monicPoly a₂) h e' hneF) = ((H₀ : ℕ) : ℕ∞) := hH_b
  rw [hminF, hnpF] at hH_b'
  have hH0 : H₁ + H₂ = H₀ := Nat.cast_inj.mp hH_b'
  have hcrp_b' : classResidualPoly π (mulClass c₁ c₂) h e'
      = resPoly π X (monicPoly a₁ * monicPoly a₂) h e' hneF H₀ := hcrp_b
  rw [hcrp_b', ← hH0, hresF, hcrp₁, hcrp₂]

/-- ★ **Corner visibility transfers**: if both factors attain their minimal face at the
corner abscissa `0`, the product's corner is VISIBLE (the corner valuations add and stay
below the window). -/
theorem cornerVisible_mulClass {π : O} (hπ : Irreducible π) {n₁ n₂ N : ℕ}
    (hN : n₁ + n₂ ≤ N) {c₁ : Coeff O n₁ N} {c₂ : Coeff O n₂ N} {h e' : ℕ}
    (hF₁ : MinFaceAt c₁ h e') (hF₂ : MinFaceAt c₂ h e')
    (hA₁ : NPAttains c₁ h e' 0) (hA₂ : NPAttains c₂ h e' 0) :
    CornerVisible (mulClass c₁ c₂) := by
  have hh1 := hF₁.1
  have hhe := hF₁.2.1
  have hvis₁ := hF₁.2.2.2.2.2
  have hvis₂ := hF₂.2.2.2.2.2
  have he' : 0 < e' := by omega
  obtain ⟨a₁, ha₁⟩ := proj_surjective O n₁ N c₁
  obtain ⟨a₂, ha₂⟩ := proj_surjective O n₂ N c₂
  have hcs₁ : classNPSupport c₁ h e' = h * n₁ := minFaceAt_support hF₁
  have hcs₂ : classNPSupport c₂ h e' = h * n₂ := minFaceAt_support hF₂
  -- the corner heights of the factors: `e'·Vᵢ = h·nᵢ`
  obtain ⟨hOn₁, hsupp₁⟩ := onSide_monicPoly_of_npAttains hπ he' hvis₁ hA₁ ha₁
  obtain ⟨hOn₂, hsupp₂⟩ := onSide_monicPoly_of_npAttains hπ he' hvis₂ hA₂ ha₂
  have htop₁ : suppVal X (monicPoly a₁) h e' ≠ ⊤ := by
    rw [hsupp₁]
    exact ENat.coe_ne_top _
  have htop₂ : suppVal X (monicPoly a₂) h e' ≠ ⊤ := by
    rw [hsupp₂]
    exact ENat.coe_ne_top _
  obtain ⟨V₁, hV₁⟩ := WithTop.ne_top_iff_exists.mp (npHgt_ne_top_of_onSide he' htop₁ hOn₁)
  obtain ⟨V₂, hV₂⟩ := WithTop.ne_top_iff_exists.mp (npHgt_ne_top_of_onSide he' htop₂ hOn₂)
  have hV₁' : npHgt X (monicPoly a₁) 0 = ((V₁ : ℕ) : ℕ∞) := hV₁.symm
  have hV₂' : npHgt X (monicPoly a₂) 0 = ((V₂ : ℕ) : ℕ∞) := hV₂.symm
  have hid₁ : e' * V₁ = h * n₁ := by
    have hOn₁' : e' • npHgt X (monicPoly a₁) 0 + ((h * 0 : ℕ) : ℕ∞)
        = suppVal X (monicPoly a₁) h e' := hOn₁
    rw [hV₁', nsmul_add_cast_gen, hsupp₁, hcs₁] at hOn₁'
    have := Nat.cast_inj.mp hOn₁'
    omega
  have hid₂ : e' * V₂ = h * n₂ := by
    have hOn₂' : e' • npHgt X (monicPoly a₂) 0 + ((h * 0 : ℕ) : ℕ∞)
        = suppVal X (monicPoly a₂) h e' := hOn₂
    rw [hV₂', nsmul_add_cast_gen, hsupp₂, hcs₂] at hOn₂'
    have := Nat.cast_inj.mp hOn₂'
    omega
  -- the sum of corner heights stays below the window
  have hn₁pos : 0 < n₁ := by
    obtain ⟨i, j, hij, -, hAj⟩ := hF₁.2.2.2.1
    have := hAj.1
    omega
  have hVlt : V₁ + V₂ < N := by
    have h1 : e' * (V₁ + V₂) = h * (n₁ + n₂) := by
      calc e' * (V₁ + V₂) = e' * V₁ + e' * V₂ := by ring
        _ = h * n₁ + h * n₂ := by rw [hid₁, hid₂]
        _ = h * (n₁ + n₂) := by ring
    have h2 : h * (n₁ + n₂) < e' * N := by
      calc h * (n₁ + n₂) < e' * (n₁ + n₂) := mul_lt_mul_of_pos_right hhe (by omega)
        _ ≤ e' * N := Nat.mul_le_mul_left e' hN
    have h3 : e' * (V₁ + V₂) < e' * N := by omega
    exact Nat.lt_of_mul_lt_mul_left h3
  -- the product's corner coefficient has valuation exactly `V₁ + V₂`
  have haddv : IsDiscreteValuationRing.addVal O ((monicPoly a₁ * monicPoly a₂).coeff 0)
      = ((V₁ + V₂ : ℕ) : ℕ∞) := by
    have hnp0 : npHgt X (monicPoly a₁ * monicPoly a₂) 0 = ((V₁ + V₂ : ℕ) : ℕ∞) := by
      show gaussVal (dev X (monicPoly a₁ * monicPoly a₂) 0) = ((V₁ + V₂ : ℕ) : ℕ∞)
      rw [dev_X, Polynomial.mul_coeff_zero, map_mul, gaussVal_mul hπ]
      have h6 : gaussVal (Polynomial.C ((monicPoly a₁).coeff 0)) = ((V₁ : ℕ) : ℕ∞) := by
        rw [← hV₁']
        show gaussVal (Polynomial.C ((monicPoly a₁).coeff 0))
          = gaussVal (dev X (monicPoly a₁) 0)
        rw [dev_X]
      have h7 : gaussVal (Polynomial.C ((monicPoly a₂).coeff 0)) = ((V₂ : ℕ) : ℕ∞) := by
        rw [← hV₂']
        show gaussVal (Polynomial.C ((monicPoly a₂).coeff 0))
          = gaussVal (dev X (monicPoly a₂) 0)
        rw [dev_X]
      rw [h6, h7]
      push_cast
      ring
    rw [← npHgt_X]
    exact hnp0
  -- the class corner value is `V₁ + V₂ < N`
  have hb : proj O (n₁ + n₂) N
      (fun i : Fin (n₁ + n₂) => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))
      = mulClass c₁ c₂ := by
    rw [mulClass_proj, ha₁, ha₂]
  intro i hi0
  by_contra hcon
  have hge : V₁ + V₂ + 1 ≤ classCoeffVal (mulClass c₁ c₂) i := by omega
  have hdvd := (le_classCoeffVal_iff_dvd hπ
    (by omega : V₁ + V₂ + 1 ≤ N) hb i).1 hge
  have h8 : ((V₁ + V₂ + 1 : ℕ) : ℕ∞)
      ≤ IsDiscreteValuationRing.addVal O ((monicPoly a₁ * monicPoly a₂).coeff (i : ℕ)) :=
    (Uniformity.Hensel.pow_dvd_iff_le_addVal hπ).1 hdvd
  rw [hi0, haddv, Nat.cast_le] at h8
  omega

/-- A class with a (fractional) minimal face is SHALLOW: the attained interior abscissa
dips strictly below its Eisenstein corner (`h < e'` prices the dip). -/
theorem shallow_of_minFaceAt {m N : ℕ} {c : Coeff O m N} {h e' : ℕ}
    (hF : MinFaceAt c h e') : c ∈ shallowSet O m N := by
  obtain ⟨i, hi⟩ := minFaceAt_attained_lt hF
  refine ⟨i, ?_⟩
  have hhe := hF.2.1
  have hilt := i.isLt
  have h2 : h * (m - (i : ℕ)) < e' * (m - (i : ℕ)) :=
    mul_lt_mul_of_pos_right hhe (by omega)
  have h3 : e' * resOrd (c i) < e' * (m - (i : ℕ)) := by omega
  exact Nat.lt_of_mul_lt_mul_left h3

/-- ★ **THE SECTOR CONVERSE** (the converse of SSL §2's refinement map): a
coprime-residual pair of same-minimal-face classes multiplies INTO the split sector.
The two honest gate legs are hypotheses: the product's DECIDEDNESS (the polygon-block
Hensel gap — the exact content the defect law still owes) and the pure-face-box
exclusion (the classes the upstream census already counted). -/
theorem mulClass_mem_splitSector {π : O} (hπ : Irreducible π) {n₁ n₂ M : ℕ}
    {σ : FactorizationType}
    {c₁ : Coeff O n₁ (M + (n₁ + n₂))} {c₂ : Coeff O n₂ (M + (n₁ + n₂))} {h e' : ℕ}
    (hF₁ : MinFaceAt c₁ h e') (hF₂ : MinFaceAt c₂ h e')
    (hcop : IsCoprime (classResidualPoly π c₁ h e') (classResidualPoly π c₂ h e'))
    (hdec : DecidedAt O (n₁ + n₂) σ (M + (n₁ + n₂)) (mulClass c₁ c₂))
    (hstr : mulClass c₁ c₂
      ∈ levelZeroStratum O (n₁ + n₂) (M + (n₁ + n₂)) (X ^ (n₁ + n₂)))
    (hpf : mulClass c₁ c₂ ∉ pureFaceSet O (n₁ + n₂) (M + (n₁ + n₂))) :
    mulClass c₁ c₂ ∈ splitSector O π (n₁ + n₂) σ M := by
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  obtain ⟨hFace, hres⟩ := minFaceAt_mulClass hπ (by omega : n₁ + n₂ ≤ M + (n₁ + n₂)) hF₁ hF₂
  have hpos₁ := (classResidualPoly_natDegree_pos hπ hF₁).1
  have hpos₂ := (classResidualPoly_natDegree_pos hπ hF₂).1
  have hne₁ : classResidualPoly π c₁ h e' ≠ 0 := fun h0 => by
    rw [h0] at hpos₁
    simp at hpos₁
  have hne₂ : classResidualPoly π c₂ h e' ≠ 0 := fun h0 => by
    rw [h0] at hpos₂
    simp at hpos₂
  refine ⟨⟨⟨⟨hdec, hstr⟩, shallow_of_minFaceAt hFace⟩, hpf⟩, h, e', hFace, ?_, ?_⟩
  · -- not irreducible: it factors into two nonconstant pieces
    intro hirr
    rcases hirr.isUnit_or_isUnit hres with hu₁ | hu₂
    · have := Polynomial.natDegree_eq_zero_of_isUnit hu₁
      omega
    · have := Polynomial.natDegree_eq_zero_of_isUnit hu₂
      omega
  · -- not a proper prime power: the two coprime nonconstant factors would share `ψ`
    rintro ⟨ψ, k, hψ, hk2, hassoc⟩
    have hψp : Prime ψ := (UniqueFactorizationMonoid.irreducible_iff_prime).1 hψ
    rw [hres] at hassoc
    obtain ⟨u, hu⟩ := hassoc
    have hdvd₁ : classResidualPoly π c₁ h e' ∣ ψ ^ k :=
      ⟨classResidualPoly π c₂ h e' * u, by rw [← hu]; ring⟩
    have hdvd₂ : classResidualPoly π c₂ h e' ∣ ψ ^ k :=
      ⟨classResidualPoly π c₁ h e' * u, by rw [← hu]; ring⟩
    have hψdvd : ∀ G : Polynomial (resField (X : Polynomial O)),
        0 < G.natDegree → G ∣ ψ ^ k → ψ ∣ G := by
      intro G hGpos hGdvd
      obtain ⟨i, hik, hGi⟩ := (dvd_prime_pow hψp k).1 hGdvd
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · exfalso
        rw [pow_zero] at hGi
        have := Polynomial.natDegree_eq_zero_of_isUnit (associated_one_iff_isUnit.mp hGi)
        omega
      · exact dvd_trans (dvd_pow_self ψ (by omega)) hGi.symm.dvd
    exact hψ.not_isUnit (hcop.isUnit_of_dvd' (hψdvd _ hpos₁ hdvd₁) (hψdvd _ hpos₂ hdvd₂))

/-- ★ The visible-sector form: with corner attainment on both factors the product lands
in the VISIBLE split sector — the exact membership shape of SSL's defect accounting. -/
theorem mulClass_mem_splitSectorVis {π : O} (hπ : Irreducible π) {n₁ n₂ M : ℕ}
    {σ : FactorizationType}
    {c₁ : Coeff O n₁ (M + (n₁ + n₂))} {c₂ : Coeff O n₂ (M + (n₁ + n₂))} {h e' : ℕ}
    (hF₁ : MinFaceAt c₁ h e') (hF₂ : MinFaceAt c₂ h e')
    (hA₁ : NPAttains c₁ h e' 0) (hA₂ : NPAttains c₂ h e' 0)
    (hcop : IsCoprime (classResidualPoly π c₁ h e') (classResidualPoly π c₂ h e'))
    (hdec : DecidedAt O (n₁ + n₂) σ (M + (n₁ + n₂)) (mulClass c₁ c₂))
    (hstr : mulClass c₁ c₂
      ∈ levelZeroStratum O (n₁ + n₂) (M + (n₁ + n₂)) (X ^ (n₁ + n₂)))
    (hpf : mulClass c₁ c₂ ∉ pureFaceSet O (n₁ + n₂) (M + (n₁ + n₂))) :
    mulClass c₁ c₂ ∈ splitSectorVis O π (n₁ + n₂) σ M :=
  ⟨mulClass_mem_splitSector hπ hF₁ hF₂ hcop hdec hstr hpf,
    cornerVisible_mulClass hπ (by omega : n₁ + n₂ ≤ M + (n₁ + n₂)) hF₁ hF₂ hA₁ hA₂⟩

end Transfer

/-! ## §2 — ★ THE EXACT COUNT LAYER -/

section CountLayer

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- ★ **Level-exact left cancellation of the class fold**: monic polynomials are regular
modulo `𝔪^N`, so the pair map is injective in each argument SEPARATELY at full level
exactness — no polygon, no coprimality.  (Two-sided injectivity is FALSE level-exactly;
see the honest fence.) -/
theorem mulClass_cancel_left {n₁ n₂ N : ℕ} {c₁ : Coeff O n₁ N}
    {c₂ c₂' : Coeff O n₂ N} (heq : mulClass c₁ c₂ = mulClass c₁ c₂') : c₂ = c₂' := by
  obtain ⟨a₁, ha₁⟩ := proj_surjective O n₁ N c₁
  obtain ⟨a₂, ha₂⟩ := proj_surjective O n₂ N c₂
  obtain ⟨a₂', ha₂'⟩ := proj_surjective O n₂ N c₂'
  have hd : (monicPoly a₁ * monicPoly a₂).natDegree = n₁ + n₂ := by
    rw [(monicPoly_monic a₁).natDegree_mul (monicPoly_monic a₂),
      monicPoly_natDegree, monicPoly_natDegree]
  have hd' : (monicPoly a₁ * monicPoly a₂').natDegree = n₁ + n₂ := by
    rw [(monicPoly_monic a₁).natDegree_mul (monicPoly_monic a₂'),
      monicPoly_natDegree, monicPoly_natDegree]
  have hclass : proj O (n₁ + n₂) N (fun i => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))
      = proj O (n₁ + n₂) N (fun i => (monicPoly a₁ * monicPoly a₂').coeff (i : ℕ)) := by
    rw [mulClass_proj, mulClass_proj, ha₁, ha₂, ha₂', heq]
  -- the mapped products agree as polynomials over the truncation ring
  have hmap : (monicPoly a₁ * monicPoly a₂).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))
      = (monicPoly a₁ * monicPoly a₂').map (Ideal.Quotient.mk ((maximalIdeal O) ^ N)) := by
    refine Polynomial.ext fun i => ?_
    rw [Polynomial.coeff_map, Polynomial.coeff_map]
    rcases Nat.lt_or_ge i (n₁ + n₂) with hi | hi
    · exact congrFun hclass ⟨i, hi⟩
    · rcases eq_or_lt_of_le hi with heqi | hlt
      · have e1 : (monicPoly a₁ * monicPoly a₂).coeff i = 1 := by
          rw [← heqi, ← hd]
          exact ((monicPoly_monic a₁).mul (monicPoly_monic a₂)).coeff_natDegree
        have e2 : (monicPoly a₁ * monicPoly a₂').coeff i = 1 := by
          rw [← heqi, ← hd']
          exact ((monicPoly_monic a₁).mul (monicPoly_monic a₂')).coeff_natDegree
        rw [e1, e2]
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hlt),
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd']; exact hlt)]
  -- the mapped monic factor is regular
  have hfac : (monicPoly a₁).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))
      * ((monicPoly a₂).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))
        - (monicPoly a₂').map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))) = 0 := by
    rw [mul_sub, ← Polynomial.map_mul, ← Polynomial.map_mul, hmap, sub_self]
  have hF₂ : (monicPoly a₂).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))
      = (monicPoly a₂').map (Ideal.Quotient.mk ((maximalIdeal O) ^ N)) := by
    by_contra hne
    have hD : (monicPoly a₂).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))
        - (monicPoly a₂').map (Ideal.Quotient.mk ((maximalIdeal O) ^ N)) ≠ 0 :=
      sub_ne_zero_of_ne hne
    have hlc : ((monicPoly a₂).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))
        - (monicPoly a₂').map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))).leadingCoeff ≠ 0 :=
      fun hc => hD (Polynomial.leadingCoeff_eq_zero.mp hc)
    have hkey := Polynomial.coeff_mul_degree_add_degree
      ((monicPoly a₁).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N)))
      ((monicPoly a₂).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))
        - (monicPoly a₂').map (Ideal.Quotient.mk ((maximalIdeal O) ^ N)))
    rw [hfac, Polynomial.coeff_zero,
      Polynomial.Monic.leadingCoeff ((monicPoly_monic a₁).map _), one_mul] at hkey
    exact hlc hkey.symm
  funext i
  have h1 : c₂ i = ((monicPoly a₂).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))).coeff (i : ℕ) := by
    rw [Polynomial.coeff_map, monicPoly_coeff_lt a₂ i.isLt]
    exact (congrFun ha₂ i).symm
  have h2 : c₂' i = ((monicPoly a₂').map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))).coeff (i : ℕ) := by
    rw [Polynomial.coeff_map, monicPoly_coeff_lt a₂' i.isLt]
    exact (congrFun ha₂' i).symm
  rw [h1, h2, hF₂]

/-- Right cancellation (the mirror). -/
theorem mulClass_cancel_right {n₁ n₂ N : ℕ} {c₁ c₁' : Coeff O n₁ N}
    {c₂ : Coeff O n₂ N} (heq : mulClass c₁ c₂ = mulClass c₁' c₂) : c₁ = c₁' := by
  obtain ⟨a₁, ha₁⟩ := proj_surjective O n₁ N c₁
  obtain ⟨a₁', ha₁'⟩ := proj_surjective O n₁ N c₁'
  obtain ⟨a₂, ha₂⟩ := proj_surjective O n₂ N c₂
  have hd : (monicPoly a₁ * monicPoly a₂).natDegree = n₁ + n₂ := by
    rw [(monicPoly_monic a₁).natDegree_mul (monicPoly_monic a₂),
      monicPoly_natDegree, monicPoly_natDegree]
  have hd' : (monicPoly a₁' * monicPoly a₂).natDegree = n₁ + n₂ := by
    rw [(monicPoly_monic a₁').natDegree_mul (monicPoly_monic a₂),
      monicPoly_natDegree, monicPoly_natDegree]
  have hclass : proj O (n₁ + n₂) N (fun i => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))
      = proj O (n₁ + n₂) N (fun i => (monicPoly a₁' * monicPoly a₂).coeff (i : ℕ)) := by
    rw [mulClass_proj, mulClass_proj, ha₁, ha₁', ha₂, heq]
  have hmap : (monicPoly a₁ * monicPoly a₂).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))
      = (monicPoly a₁' * monicPoly a₂).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N)) := by
    refine Polynomial.ext fun i => ?_
    rw [Polynomial.coeff_map, Polynomial.coeff_map]
    rcases Nat.lt_or_ge i (n₁ + n₂) with hi | hi
    · exact congrFun hclass ⟨i, hi⟩
    · rcases eq_or_lt_of_le hi with heqi | hlt
      · have e1 : (monicPoly a₁ * monicPoly a₂).coeff i = 1 := by
          rw [← heqi, ← hd]
          exact ((monicPoly_monic a₁).mul (monicPoly_monic a₂)).coeff_natDegree
        have e2 : (monicPoly a₁' * monicPoly a₂).coeff i = 1 := by
          rw [← heqi, ← hd']
          exact ((monicPoly_monic a₁').mul (monicPoly_monic a₂)).coeff_natDegree
        rw [e1, e2]
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hlt),
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd']; exact hlt)]
  have hfac : (monicPoly a₂).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))
      * ((monicPoly a₁).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))
        - (monicPoly a₁').map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))) = 0 := by
    rw [mul_sub, mul_comm ((monicPoly a₂).map _) ((monicPoly a₁).map _),
      mul_comm ((monicPoly a₂).map _) ((monicPoly a₁').map _),
      ← Polynomial.map_mul, ← Polynomial.map_mul, hmap, sub_self]
  have hF₁ : (monicPoly a₁).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))
      = (monicPoly a₁').map (Ideal.Quotient.mk ((maximalIdeal O) ^ N)) := by
    by_contra hne
    have hD : (monicPoly a₁).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))
        - (monicPoly a₁').map (Ideal.Quotient.mk ((maximalIdeal O) ^ N)) ≠ 0 :=
      sub_ne_zero_of_ne hne
    have hlc : ((monicPoly a₁).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))
        - (monicPoly a₁').map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))).leadingCoeff ≠ 0 :=
      fun hc => hD (Polynomial.leadingCoeff_eq_zero.mp hc)
    have hkey := Polynomial.coeff_mul_degree_add_degree
      ((monicPoly a₂).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N)))
      ((monicPoly a₁).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))
        - (monicPoly a₁').map (Ideal.Quotient.mk ((maximalIdeal O) ^ N)))
    rw [hfac, Polynomial.coeff_zero,
      Polynomial.Monic.leadingCoeff ((monicPoly_monic a₂).map _), one_mul] at hkey
    exact hlc hkey.symm
  funext i
  have h1 : c₁ i = ((monicPoly a₁).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))).coeff (i : ℕ) := by
    rw [Polynomial.coeff_map, monicPoly_coeff_lt a₁ i.isLt]
    exact (congrFun ha₁ i).symm
  have h2 : c₁' i = ((monicPoly a₁').map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))).coeff (i : ℕ) := by
    rw [Polynomial.coeff_map, monicPoly_coeff_lt a₁' i.isLt]
    exact (congrFun ha₁' i).symm
  rw [h1, h2, hF₁]

open Classical in
/-- `Nat.card` of a set in a finite type, as a `Finset.filter` card (IFCG17's private
bridge, copied). -/
private theorem natCard_set_eq_card_filter {α : Type*} [Fintype α] (s : Set α) :
    Nat.card s = (Finset.univ.filter (fun a => a ∈ s)).card := by
  rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset (Finset.univ.filter (fun a => a ∈ s))]
  congr 1
  ext a
  simp

open Classical in
/-- Fiberwise decomposition of a set count along a map into a finite type (IFCG17's
private helper, at full-type coverage). -/
private theorem natCard_eq_sum_fiber {α β : Type*} [Fintype α] [Fintype β] (s : Set α)
    (φ : α → β) :
    Nat.card s = ∑ b : β, Nat.card ((s ∩ φ ⁻¹' {b} : Set α)) := by
  rw [natCard_set_eq_card_filter,
    Finset.card_eq_sum_card_fiberwise (f := φ) (t := Finset.univ)
      (fun a _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [natCard_set_eq_card_filter, Finset.filter_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_singleton_iff]

/-- **The pair fiber of one convolution-table entry over a product cell**: the number of
decided pairs at the entry `p = ((n₁, n₂), s)` whose `mulClass` product is `c`. -/
noncomputable def pairFiber (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    (m : ℕ) (σ : FactorizationType) (M : ℕ)
    (p : (ℕ × ℕ) × Multiset (ℕ × ℕ)) (c : Coeff O m (M + m)) : ℕ :=
  if hpm : p.1.1 + p.1.2 = m then
    Nat.card (((decidedSet O p.1.1 ⟨p.2⟩ (M + m))
        ×ˢ (decidedSet O p.1.2 ⟨σ.data - p.2⟩ (M + m)))
      ∩ (fun q : Coeff O p.1.1 (M + m) × Coeff O p.1.2 (M + m) =>
          mulClassAt hpm q.1 q.2) ⁻¹' {c} : Set _)
  else 0

/-- **The multiplicity of a product cell in SSL's convolution table**: the total number
of table pairs mapping to `c`. -/
noncomputable def multCount (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    (m : ℕ) (σ : FactorizationType) (M : ℕ) (c : Coeff O m (M + m)) : ℕ :=
  ∑ p ∈ convPairs m σ, pairFiber O m σ M p c

/-- ★ **The fiberwise double count**: SSL's convolution table counts every product cell
with its multiplicity — exactly, at every finite level. -/
theorem convCount_eq_sum_multCount (m : ℕ) (σ : FactorizationType) (M : ℕ)
    [Fintype (Coeff O m (M + m))] :
    convCount O m σ M = ∑ c : Coeff O m (M + m), multCount O m σ M c := by
  classical
  have hper : ∀ p ∈ convPairs m σ,
      decidedCount O p.1.1 ⟨p.2⟩ (M + m) * decidedCount O p.1.2 ⟨σ.data - p.2⟩ (M + m)
        = ∑ c : Coeff O m (M + m), pairFiber O m σ M p c := by
    intro p hp
    have hpm : p.1.1 + p.1.2 = m := by
      rw [convPairs, Finset.mem_product, Finset.mem_filter] at hp
      exact hp.1.2.1
    haveI : Fintype (Coeff O p.1.1 (M + m) × Coeff O p.1.2 (M + m)) := Fintype.ofFinite _
    have hprod : decidedCount O p.1.1 ⟨p.2⟩ (M + m)
          * decidedCount O p.1.2 ⟨σ.data - p.2⟩ (M + m)
        = Nat.card (((decidedSet O p.1.1 ⟨p.2⟩ (M + m))
            ×ˢ (decidedSet O p.1.2 ⟨σ.data - p.2⟩ (M + m)) : Set _)) := by
      rw [decidedCount, decidedCount, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
        Nat.card_coe_set_eq, Set.ncard_prod]
    rw [hprod, natCard_eq_sum_fiber _ (fun q : Coeff O p.1.1 (M + m) × Coeff O p.1.2 (M + m)
      => mulClassAt hpm q.1 q.2)]
    refine Finset.sum_congr rfl fun c _ => ?_
    unfold pairFiber
    rw [dif_pos hpm]
  calc convCount O m σ M
      = ∑ p ∈ convPairs m σ, decidedCount O p.1.1 ⟨p.2⟩ (M + m)
          * decidedCount O p.1.2 ⟨σ.data - p.2⟩ (M + m) := rfl
    _ = ∑ p ∈ convPairs m σ, ∑ c : Coeff O m (M + m), pairFiber O m σ M p c :=
        Finset.sum_congr rfl hper
    _ = ∑ c : Coeff O m (M + m), ∑ p ∈ convPairs m σ, pairFiber O m σ M p c :=
        Finset.sum_comm
    _ = ∑ c : Coeff O m (M + m), multCount O m σ M c := rfl

variable [IsAdicComplete (maximalIdeal O) O]

/-- Every VISIBLE split cell is hit by the table at least once (SSL's refinement map —
the B.42-citing leg). -/
theorem one_le_multCount_of_vis {π : O} (hπ : Irreducible π) {m : ℕ} (hm : 0 < m)
    {σ : FactorizationType} {M : ℕ} {c : Coeff O m (M + m)}
    (hc : c ∈ splitSectorVis O π m σ M) : 1 ≤ multCount O m σ M c := by
  classical
  obtain ⟨hcs, hcv⟩ := hc
  obtain ⟨n₁, n₂, hn₁, hn₂, hsum, σ₁, σ₂, c₁, c₂, hd₁, hd₂, hsumty, hkey⟩ :=
    splitSector_refines_decided hπ hm hcs hcv
  subst hsum
  have hpmem : ((n₁, n₂), σ₁.data) ∈ convPairs (n₁ + n₂) σ := by
    rw [convPairs, Finset.mem_product, Finset.mem_filter, Finset.mem_product]
    dsimp only
    refine ⟨⟨⟨Finset.mem_range.2 (by omega), Finset.mem_range.2 (by omega)⟩,
      rfl, hn₁, hn₂⟩, ?_⟩
    rw [Multiset.mem_toFinset, Multiset.mem_powerset]
    exact Multiset.le_iff_exists_add.mpr ⟨σ₂.data, hsumty.symm⟩
  have hfmem : ((c₁, c₂) : Coeff O n₁ (M + (n₁ + n₂)) × Coeff O n₂ (M + (n₁ + n₂)))
      ∈ ((decidedSet O n₁ ⟨σ₁.data⟩ (M + (n₁ + n₂)))
          ×ˢ (decidedSet O n₂ ⟨σ.data - σ₁.data⟩ (M + (n₁ + n₂)))
        ∩ (fun q : Coeff O n₁ (M + (n₁ + n₂)) × Coeff O n₂ (M + (n₁ + n₂)) =>
            mulClassAt rfl q.1 q.2) ⁻¹' {c} : Set _) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact (show (⟨σ₁.data⟩ : FactorizationType) = σ₁ from rfl) ▸ hd₁
    · have h6 : σ.data - σ₁.data = σ₂.data := by
        rw [← hsumty, add_tsub_cancel_left]
      rw [show (⟨σ.data - σ₁.data⟩ : FactorizationType) = σ₂ from
        FactorizationType.ext h6]
      exact hd₂
    · exact hkey
  have hfpos : 1 ≤ pairFiber O (n₁ + n₂) σ M ((n₁, n₂), σ₁.data) c := by
    unfold pairFiber
    dsimp only
    rw [dif_pos rfl]
    rw [Nat.card_coe_set_eq]
    exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨(c₁, c₂), hfmem⟩
  have hle := Finset.single_le_sum
    (f := fun p => pairFiber O (n₁ + n₂) σ M p c) (fun i _ => Nat.zero_le _) hpmem
  calc 1 ≤ pairFiber O (n₁ + n₂) σ M ((n₁, n₂), σ₁.data) c := hfpos
    _ ≤ multCount O (n₁ + n₂) σ M c := hle

open Classical in
/-- ★★ **THE EXACT DEFECT DECOMPOSITION** — at every finite level, every mass, every
type, every uniformizer:

    convCount = #vis + [ Σ_{c ∈ vis} (multCount c − 1)  +  Σ_{c ∉ vis} multCount c ]

The bracket IS SSL's defect (`convCount − #vis`), decomposed exactly into the COLLISION
excess over the visible sector plus the STRAY mass of the table (pairs whose product is
not a visible split cell). -/
theorem convCount_eq_card_vis_add_defect {π : O} (hπ : Irreducible π) {m : ℕ}
    (hm : 0 < m) (σ : FactorizationType) (M : ℕ) [Fintype (Coeff O m (M + m))] :
    convCount O m σ M
      = Nat.card (splitSectorVis O π m σ M)
        + ((∑ c ∈ Finset.univ.filter (· ∈ splitSectorVis O π m σ M),
              (multCount O m σ M c - 1))
          + ∑ c ∈ Finset.univ.filter (· ∉ splitSectorVis O π m σ M),
              multCount O m σ M c) := by
  classical
  have hsplit : ∑ c : Coeff O m (M + m), multCount O m σ M c
      = ∑ c ∈ Finset.univ.filter (· ∈ splitSectorVis O π m σ M), multCount O m σ M c
        + ∑ c ∈ Finset.univ.filter (· ∉ splitSectorVis O π m σ M), multCount O m σ M c :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ
      (· ∈ splitSectorVis O π m σ M) _).symm
  have hvis : ∑ c ∈ Finset.univ.filter (· ∈ splitSectorVis O π m σ M), multCount O m σ M c
      = (Finset.univ.filter (· ∈ splitSectorVis O π m σ M)).card
        + ∑ c ∈ Finset.univ.filter (· ∈ splitSectorVis O π m σ M),
            (multCount O m σ M c - 1) := by
    rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c hc => ?_
    have h1 : 1 ≤ multCount O m σ M c :=
      one_le_multCount_of_vis hπ hm (Finset.mem_filter.mp hc).2
    omega
  have hcard : Nat.card (splitSectorVis O π m σ M)
      = (Finset.univ.filter (· ∈ splitSectorVis O π m σ M)).card :=
    natCard_set_eq_card_filter _
  rw [convCount_eq_sum_multCount, hsplit, hvis, hcard]
  omega

end CountLayer

/-! ## §3 — ★ THE FIRINGS -/

section Firings

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★ **Below mass 4 the split sector is EMPTY**: a coprime split needs residual degree
`≥ 2` at a face of denominator `e' ≥ 2`, hence mass `≥ e' · sideDeg ≥ 4`. -/
theorem splitSector_eq_empty_of_mass_le_three {π : O} (hπ : Irreducible π) {m : ℕ}
    (hm3 : m ≤ 3) (σ : FactorizationType) (M : ℕ) :
    splitSector O π m σ M = ∅ := by
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  ext c
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hc
  obtain ⟨h, e', hF, hni, hnp⟩ := hc.2
  obtain ⟨G, H, hG, hH, hGd, hHd, hcopGH, heq⟩ := splitSector_coprime_split hπ hc hF
  -- the coprime-split residual has degree ≥ 2
  have hdeg2 : 2 ≤ (classResidualPoly π c h e').natDegree := by
    rw [heq, Polynomial.natDegree_mul hG.ne_zero hH.ne_zero]
    omega
  -- but the residual degree is the side degree, priced by `e' ≥ 2` inside mass `m`
  obtain ⟨a, ha⟩ := proj_surjective O m (M + m) c
  obtain ⟨hne, H₀, hH₀, htop, hcrp⟩ := resPoly_rep hπ hF ha
  have hh1 := hF.1
  have hhe := hF.2.1
  have hcop := hF.2.2.1
  have he' : 0 < e' := by omega
  have hnd := natDegree_resPoly hπ isKey_X he' hcop htop hne hH₀
  have hmax_eq : sideMax X (monicPoly a) h e' hne
      = sideMin X (monicPoly a) h e' hne + e' * sideDeg X (monicPoly a) h e' hne :=
    sideMax_eq he' hcop htop hne
  have hdegm : (monicPoly a).natDegree = m := monicPoly_natDegree a
  have hmax_le : sideMax X (monicPoly a) h e' hne ≤ m := by
    have h2 := Finset.max'_mem (sideSet X (monicPoly a) h e') hne
    obtain ⟨h3, -⟩ := mem_sideSet_iff'.mp h2
    unfold sideMax
    omega
  rw [hcrp, hnd.1] at hdeg2
  have hbig : 2 * 2 ≤ e' * sideDeg X (monicPoly a) h e' hne :=
    Nat.mul_le_mul (by omega) hdeg2
  omega

end Firings

section LawFirings

/-- ★ **THE UNCONDITIONAL FIRINGS** — at mass `≤ 1` the convolution table and the split
sector are both empty, so the defect family is identically zero: the first outright
(hypothesis-free) instances of `SplitConvolutionDefectLaw`. -/
theorem splitConvolutionDefectLaw_of_mass_le_one {m : ℕ} (hm1 : m ≤ 1)
    (σ : FactorizationType) : SplitConvolutionDefectLaw m σ := by
  refine Uniformity.Density.IFCG24.ZcURLim_zero.congr ?_
  intro O _ _ _ _ _ π hπ M
  have hconv : convCount O m σ M = 0 := by
    have hfilter : ((Finset.range (m + 1) ×ˢ Finset.range (m + 1)).filter
        (fun q => q.1 + q.2 = m ∧ 0 < q.1 ∧ 0 < q.2)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro q -
      rintro ⟨hq1, hq2, hq3⟩
      omega
    rw [convCount, convPairs, hfilter, Finset.empty_product, Finset.sum_empty]
  have hvis : Nat.card (splitSectorVis O π m σ M) = 0 := by
    have hemp : splitSectorVis O π m σ M = ∅ := by
      rw [← Set.subset_empty_iff,
        ← splitSector_eq_empty_of_mass_le_three hπ (by omega : m ≤ 3) σ M]
      exact Set.inter_subset_left
    rw [hemp, Nat.card_coe_set_eq, Set.ncard_empty]
  show (0 : ℝ) = ((convCount O m σ M : ℝ) - (Nat.card (splitSectorVis O π m σ M) : ℝ))
      / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
  rw [hconv, hvis]
  simp

/-- ★ **The low-mass firings**: below mass 4 the visible split sector is empty, so the
defect is the full convolution table, whose law is SSL §4's under the `< m` decided
value laws — the recursion's own supply. -/
theorem splitConvolutionDefectLaw_of_mass_le_three {m : ℕ} (hm3 : m ≤ 3)
    (σ : FactorizationType)
    (hDV : ∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') :
    SplitConvolutionDefectLaw m σ := by
  refine (zcURLim_conv σ hDV).congr ?_
  intro O _ _ _ _ _ π hπ M
  have hvis : Nat.card (splitSectorVis O π m σ M) = 0 := by
    have hemp : splitSectorVis O π m σ M = ∅ := by
      rw [← Set.subset_empty_iff, ← splitSector_eq_empty_of_mass_le_three hπ hm3 σ M]
      exact Set.inter_subset_left
    rw [hemp, Nat.card_coe_set_eq, Set.ncard_empty]
  show (convCount O m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
      = ((convCount O m σ M : ℝ) - (Nat.card (splitSectorVis O π m σ M) : ℝ))
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
  rw [hvis]
  simp

/-- The socket fires end-to-end at low mass: `SplitSectorLaw m σ` outright for
`0 < m ≤ 3` under the `< m` value laws (through SSL's assembly). -/
theorem splitSectorLaw_of_mass_le_three {m : ℕ} (hm : 0 < m) (hm3 : m ≤ 3)
    (σ : FactorizationType)
    (hDV : ∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') :
    SplitSectorLaw m σ :=
  Uniformity.Density.IFCG38.splitSectorLaw_of_defectLaw hm σ hDV
    (splitConvolutionDefectLaw_of_mass_le_three hm3 σ hDV)

/-- ★★ **THE HONEST EQUIVALENCE**: under the `< m` decided value laws the convolution
defect law at `(m, σ)` is EQUIVALENT to the split-sector law at `(m, σ)` — SSL's
"re-base, not a strength reduction" accounting, machine-checked in both directions.
The endgame's split leg is therefore EXACTLY: `SplitConvolutionDefectLaw m σ` at
`4 ≤ m`, `σ` ramified (mass `≤ 3` and unramified `σ` are landed). -/
theorem splitConvolutionDefectLaw_iff_splitSectorLaw {m : ℕ} (hm : 0 < m)
    (σ : FactorizationType)
    (hDV : ∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') :
    SplitConvolutionDefectLaw m σ ↔ SplitSectorLaw m σ := by
  constructor
  · exact fun hD => Uniformity.Density.IFCG38.splitSectorLaw_of_defectLaw hm σ hDV hD
  · intro hS
    have hvis : ZcURLim (fun O _ _ _ _ _ π M =>
        (Nat.card (splitSectorVis O π m σ M) : ℝ)
          / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))) := by
      refine (zcURLim_sub hS (zcURLim_inv hm σ)).congr ?_
      intro O _ _ _ _ _ π hπ M
      show (splitSectorCount O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
          - (Nat.card (splitSectorInv O π m σ M) : ℝ)
            / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
        = (Nat.card (splitSectorVis O π m σ M) : ℝ)
            / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
      rw [splitSectorCount_eq_vis_add_inv π m σ M]
      push_cast
      ring
    refine (zcURLim_sub (zcURLim_conv σ hDV) hvis).congr ?_
    intro O _ _ _ _ _ π hπ M
    show (convCount O m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
        - (Nat.card (splitSectorVis O π m σ M) : ℝ)
          / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
      = ((convCount O m σ M : ℝ) - (Nat.card (splitSectorVis O π m σ M) : ℝ))
          / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
    ring

end LawFirings

end Uniformity.Density.IFCG40

end

/-! ## AXCHECK FOOTER — §1, §2's cancellations/double-count, and §3 expect Lean core
`{propext, Classical.choice, Quot.sound}`; `one_le_multCount_of_vis`,
`convCount_eq_card_vis_add_defect`, and the iff expect Lean core + the owner-signed
B.42 cite `Uniformity.Density.Leaf.exists_slope_factorization` (through SSL's
refinement map).  C.33 must NOT occur. -/
#print axioms Uniformity.Density.IFCG40.minFaceAt_mulClass
#print axioms Uniformity.Density.IFCG40.cornerVisible_mulClass
#print axioms Uniformity.Density.IFCG40.mulClass_mem_splitSector
#print axioms Uniformity.Density.IFCG40.mulClass_mem_splitSectorVis
#print axioms Uniformity.Density.IFCG40.mulClass_cancel_left
#print axioms Uniformity.Density.IFCG40.mulClass_cancel_right
#print axioms Uniformity.Density.IFCG40.convCount_eq_sum_multCount
#print axioms Uniformity.Density.IFCG40.one_le_multCount_of_vis
#print axioms Uniformity.Density.IFCG40.convCount_eq_card_vis_add_defect
#print axioms Uniformity.Density.IFCG40.splitSector_eq_empty_of_mass_le_three
#print axioms Uniformity.Density.IFCG40.splitConvolutionDefectLaw_of_mass_le_one
#print axioms Uniformity.Density.IFCG40.splitConvolutionDefectLaw_of_mass_le_three
#print axioms Uniformity.Density.IFCG40.splitSectorLaw_of_mass_le_three
#print axioms Uniformity.Density.IFCG40.splitConvolutionDefectLaw_iff_splitSectorLaw
